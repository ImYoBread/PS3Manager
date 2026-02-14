using FluentFTP;
using Microsoft.Win32;
using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.ComponentModel;
using System.Diagnostics;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Net;
using System.Net.Http;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Threading;

namespace PS3Manager
{
    public partial class MainWindow : Window
    {
        private AsyncFtpClient _ftp;
        private bool _connected = false;
        private string _localPath = "";
        private string _remotePath = "/";
        private HttpClient _http = new HttpClient { Timeout = TimeSpan.FromSeconds(30) };
        private Point _dragStartPoint;
        private bool _isDragging = false;

        // Clipboard for file operations
        private List<FileItem> _clipboardFiles = new List<FileItem>();
        private bool _clipboardIsCut = false;
        private bool _clipboardIsLocal = false;

        // FTP Transfer tracking
        private CancellationTokenSource _transferCts;
        private Stopwatch _transferStopwatch = new Stopwatch();
        private double _transferSmoothSpeed = 0;
        private DateTime _transferLastUpdate = DateTime.MinValue;

        // Myrient Integration
        private MyrientScraper _myrient;
        private CancellationTokenSource _downloadCts;

        // Collections
        public ObservableCollection<GameInfo> AllGames { get; set; }
        public ObservableCollection<GameInfo> FilteredGames { get; set; }
        public ObservableCollection<FileItem> LocalFiles { get; set; }
        public ObservableCollection<FileItem> RemoteFiles { get; set; }
        public ObservableCollection<PkgInfo> PkgsList { get; set; }
        public ObservableCollection<MyrientGame> MyrientGames { get; set; }
        public ObservableCollection<DownloadTask> ActiveDownloads { get; set; }

        private string[] _gameFolders = new[]
        {
            "/dev_hdd0/game", "/dev_hdd0/GAMES", "/dev_hdd0/GAMEZ", "/dev_hdd0/GAMEI",
            "/dev_hdd0/PS3ISO", "/dev_hdd0/PS2ISO", "/dev_hdd0/PSXISO", "/dev_hdd0/PSPISO",
            "/dev_usb000/GAMES", "/dev_usb000/PS3ISO", "/dev_usb001/GAMES"
        };

        public MainWindow()
        {
            AllGames = new ObservableCollection<GameInfo>();
            FilteredGames = new ObservableCollection<GameInfo>();
            LocalFiles = new ObservableCollection<FileItem>();
            RemoteFiles = new ObservableCollection<FileItem>();
            PkgsList = new ObservableCollection<PkgInfo>();
            MyrientGames = new ObservableCollection<MyrientGame>();
            ActiveDownloads = new ObservableCollection<DownloadTask>();

            InitializeComponent();

            // Set ItemsSource after InitializeComponent
            lstGames.ItemsSource = FilteredGames;
            lstDashGames.ItemsSource = AllGames;
            lstLocal.ItemsSource = LocalFiles;
            lstRemote.ItemsSource = RemoteFiles;
            lstPKG.ItemsSource = PkgsList;
            lstMyrientGames.ItemsSource = MyrientGames;
            lstDownloads.ItemsSource = ActiveDownloads;

            // Initialize Myrient
            _myrient = new MyrientScraper();

            sliderFan.ValueChanged += (s, e) => txtFanVal.Text = $"{(int)sliderFan.Value}%";

            // Setup context menus
            SetupLocalContextMenu();
            SetupRemoteContextMenu();

            // Load drives
            LoadDrives();

            Status("Ready - Enter PS3 IP and click Connect");
        }

        // ════════════════════════════════════════════════════════════════
        //  FDM/IDM-STYLE DYNAMIC SEGMENTATION ENGINE
        //
        //  Key techniques copied from Free Download Manager / IDM:
        //
        //  1. DYNAMIC SEGMENTATION — segments are NOT fixed. When a
        //     worker finishes, it finds the largest remaining segment
        //     and splits it in half, stealing work from the slowest
        //     connection. This keeps ALL connections busy at all times.
        //
        //  2. CONNECTION REUSE — workers keep their HTTP connections
        //     alive and reuse them for the next segment without
        //     reconnecting/re-handshaking.
        //
        //  3. ADAPTIVE CONCURRENCY — starts with a few connections,
        //     ramps up to max, monitors throughput, backs off if the
        //     server starts rejecting.
        //
        //  4. PRE-ALLOCATED OUTPUT — file is allocated at full size
        //     up front so each worker writes to its exact byte offset.
        //     No merge step needed.
        //
        //  5. PERSISTENT PROGRESS — saves segment state so downloads
        //     can resume after interruption.
        // ════════════════════════════════════════════════════════════════
        // ════════════════════════════════════════════════════════════════
        //  MAXIMUM SPEED CONSTANTS - Aggressive settings to bypass limits
        // ════════════════════════════════════════════════════════════════
        private const int DL_MAX_CONNECTIONS = 32;              // Reduced for stability
        private const int DL_INITIAL_CONNECTIONS = 16;          // Start with 16
        private const int DL_RAMP_INTERVAL_MS = 1000;
        private const int DL_MIN_SEGMENT_BYTES = 256 * 1024;    // 256KB - larger segments for stability
        private const int DL_READ_BUFFER = 65536;               // 64KB - smaller buffer for more frequent updates
        private const int DL_WORKER_RETRY = 3;
        private const int DL_CONNECTION_TIMEOUT = 10000;        // 10 seconds
        private const int DL_READ_TIMEOUT = 30000;              // 30 seconds

        // User-Agent rotation
        private static readonly string[] USER_AGENTS = new[]
        {
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:127.0) Gecko/20100101 Firefox/127.0"
        };
        private static int _uaIndex = 0;

        #region Myrient Event Handlers

        private void MyrientSearch_Click(object sender, RoutedEventArgs e)
        {
            if (string.IsNullOrWhiteSpace(txtMyrientSearch.Text)) return;

            string query = txtMyrientSearch.Text.Trim();
            if (query.Length < 2)
            {
                Status("Please enter at least 2 characters to search");
                return;
            }

            // Get selected platforms from checkboxes
            var selectedPlatforms = new List<string>();
            if (chkPS1.IsChecked == true) selectedPlatforms.Add("PS1");
            if (chkPS2.IsChecked == true) selectedPlatforms.Add("PS2");
            if (chkPS3.IsChecked == true) selectedPlatforms.Add("PS3");

            if (selectedPlatforms.Count == 0)
            {
                Status("Please select at least one platform");
                return;
            }

            Status($"Searching Myrient for '{query}'...");
            MyrientGames.Clear();

            var searchBtn = sender as Button;
            if (searchBtn != null) searchBtn.IsEnabled = false;

            // Run search on background thread
            Task.Run(async () =>
            {
                try
                {
                    foreach (var platform in selectedPlatforms)
                    {
                        var results = await _myrient.SearchAsync(query, platform);

                        // Update UI on main thread
                        Dispatcher.Invoke(() =>
                        {
                            foreach (var game in results)
                            {
                                MyrientGames.Add(game);
                            }
                        });
                    }

                    Dispatcher.Invoke(() =>
                    {
                        Status($"Found {MyrientGames.Count} results");
                    });
                }
                catch (Exception ex)
                {
                    Dispatcher.Invoke(() =>
                    {
                        Status($"Search error: {ex.Message}");
                        MessageBox.Show($"Search failed: {ex.Message}", "Error", MessageBoxButton.OK, MessageBoxImage.Error);
                    });
                }
                finally
                {
                    Dispatcher.Invoke(() =>
                    {
                        if (searchBtn != null) searchBtn.IsEnabled = true;
                    });
                }
            });
        }

        private void MyrientSearch_KeyDown(object sender, KeyEventArgs e)
        {
            if (e.Key == Key.Enter)
                MyrientSearch_Click(sender, e);
        }

        private void MyrientDownload_Click(object sender, RoutedEventArgs e)
        {
            if (lstMyrientGames.SelectedItems.Count == 0) return;

            var selectedGames = lstMyrientGames.SelectedItems.Cast<MyrientGame>().ToList();

            foreach (var game in selectedGames)
            {
                StartDownload(game);
            }
        }

        private void StartDownload(MyrientGame game)
        {
            string dir = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), "Downloads", game.Platform);
            Directory.CreateDirectory(dir);

            string fn = Uri.UnescapeDataString(game.FileName);
            foreach (char c in Path.GetInvalidFileNameChars()) fn = fn.Replace(c, '_');
            string localPath = Path.Combine(dir, fn);

            if (ActiveDownloads.Any(d => d.Url == game.DownloadUrl && !IsFinished(d.Status)))
            { Status($"Already downloading: {fn}"); return; }

            if (File.Exists(localPath))
            {
                if (MessageBox.Show($"'{fn}' exists. Re-download?", "Exists", MessageBoxButton.YesNo) != MessageBoxResult.Yes) return;
                try { File.Delete(localPath); } catch { }
            }

            var task = new DownloadTask
            {
                Name = fn,
                Platform = game.Platform,
                Url = game.DownloadUrl,
                LocalPath = localPath,
                TotalSize = game.Size,
                TotalBytes = game.Size > 0 ? game.Size : null,
                Status = "Queued",
                StartTime = DateTime.Now,
                CancellationTokenSource = new CancellationTokenSource()
            };
            ActiveDownloads.Add(task);

            // Try HTTP/2 first, fallback to TCP optimized
            new Thread(() => DownloadHttp2Bypass(task))
            {
                IsBackground = true,
                Name = $"DL_H2_{fn}"
            }.Start();
        }

        // Add this alternative download method
        // ════════════════════════════════════════════════════════════════
        //  HTTP/2 MULTIPLEXING BYPASS - Uses HTTP/2 single connection
        //  with multiplexed streams to bypass per-stream throttling
        // ════════════════════════════════════════════════════════════════
        // ════════════════════════════════════════════════════════════════
        //  HTTP/2 MULTIPLEXING BYPASS - Uses HTTP/2 single connection
        //  with multiplexed streams to bypass per-stream throttling
        // ════════════════════════════════════════════════════════════════
        private void DownloadHttp2Bypass(DownloadTask task)
        {
            var sw = Stopwatch.StartNew();

            try
            {
                Dispatcher.Invoke(() => task.Status = "Initializing HTTP/2 bypass...");

                // ── STEP 1: Configure HTTP/2 handler with optimizations ─────────
                var handler = new SocketsHttpHandler
                {
                    EnableMultipleHttp2Connections = true,
                    MaxConnectionsPerServer = 4,
                    PooledConnectionIdleTimeout = TimeSpan.FromMinutes(10),
                    KeepAlivePingDelay = TimeSpan.FromSeconds(60),
                    KeepAlivePingTimeout = TimeSpan.FromSeconds(30),
                    KeepAlivePingPolicy = HttpKeepAlivePingPolicy.Always,
                    InitialHttp2StreamWindowSize = 16 * 1024 * 1024,
                    MaxResponseHeadersLength = 65536,
                    AutomaticDecompression = DecompressionMethods.None,
                    ConnectTimeout = TimeSpan.FromSeconds(30),
                    Proxy = null,
                    UseProxy = false
                };

                // ── STEP 2: Create HTTP/2 client with browser headers ───────────
                var client = new HttpClient(handler);
                client.DefaultRequestVersion = new Version(2, 0);
                client.DefaultVersionPolicy = HttpVersionPolicy.RequestVersionOrLower;
                client.Timeout = TimeSpan.FromMinutes(30);

                client.DefaultRequestHeaders.Clear();
                client.DefaultRequestHeaders.Add("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
                client.DefaultRequestHeaders.Add("Accept", "*/*");
                client.DefaultRequestHeaders.Add("Accept-Language", "en-US,en;q=0.9");
                client.DefaultRequestHeaders.Add("Accept-Encoding", "identity");
                client.DefaultRequestHeaders.Add("Referer", "https://myrient.erista.me/files/");
                client.DefaultRequestHeaders.Add("Origin", "https://myrient.erista.me");
                client.DefaultRequestHeaders.Add("DNT", "1");
                client.DefaultRequestHeaders.Add("Upgrade-Insecure-Requests", "1");
                client.DefaultRequestHeaders.Add("Sec-Fetch-Dest", "document");
                client.DefaultRequestHeaders.Add("Sec-Fetch-Mode", "navigate");
                client.DefaultRequestHeaders.Add("Sec-Fetch-Site", "same-origin");
                client.DefaultRequestHeaders.Add("Sec-Fetch-User", "?1");
                client.DefaultRequestHeaders.Add("Cache-Control", "no-cache");
                client.DefaultRequestHeaders.Add("Pragma", "no-cache");

                // ── STEP 3: Get file size with HTTP/2 ───────────────────────────
                long totalBytes = 0;

                try
                {
                    var headMsg = new HttpRequestMessage(HttpMethod.Head, task.Url);
                    headMsg.Version = new Version(2, 0);
                    var headResponse = client.SendAsync(headMsg, HttpCompletionOption.ResponseHeadersRead).Result;
                    if (headResponse.IsSuccessStatusCode)
                        totalBytes = headResponse.Content.Headers.ContentLength ?? 0;
                }
                catch { }

                if (totalBytes <= 0)
                {
                    try
                    {
                        var probeMsg = new HttpRequestMessage(HttpMethod.Get, task.Url);
                        probeMsg.Version = new Version(2, 0);
                        probeMsg.Headers.Range = new System.Net.Http.Headers.RangeHeaderValue(0, 0);
                        var probeResponse = client.SendAsync(probeMsg, HttpCompletionOption.ResponseHeadersRead).Result;
                        var contentRange = probeResponse.Content.Headers.ContentRange;
                        if (contentRange != null && contentRange.Length.HasValue)
                            totalBytes = contentRange.Length.Value;
                    }
                    catch { }
                }

                if (totalBytes <= 0)
                    totalBytes = ProbeFileSize(task.Url);

                if (totalBytes <= 0)
                    throw new Exception("Cannot determine file size with HTTP/2 or HTTP/1.1");

                task.TotalBytes = totalBytes;
                task.TotalSize = totalBytes;

                // ── STEP 4: Pre-allocate file ───────────────────────────────────
                Directory.CreateDirectory(Path.GetDirectoryName(task.LocalPath));
                if (File.Exists(task.LocalPath))
                    File.Delete(task.LocalPath);

                // ── STEP 5: HTTP/2 download with progress tracking ──────────────
                Dispatcher.Invoke(() => task.Status = "HTTP/2 downloading...");

                var requestMsg = new HttpRequestMessage(HttpMethod.Get, task.Url);
                requestMsg.Version = new Version(2, 0);
                var response = client.SendAsync(requestMsg, HttpCompletionOption.ResponseHeadersRead,
                    task.CancellationTokenSource.Token).Result;

                if (!response.IsSuccessStatusCode)
                    throw new Exception($"HTTP/2 request failed: {response.StatusCode}");

                if (response.Content.Headers.ContentLength.HasValue &&
                    response.Content.Headers.ContentLength.Value < 1024 &&
                    response.Content.Headers.ContentLength.Value != totalBytes)
                    throw new Exception("HTTP/2 throttled - falling back to TCP optimized");

                // ════════════════════════════════════════════════════════════════
                //  FIXED: Properly dispose all streams before extraction
                // ════════════════════════════════════════════════════════════════
                long downloaded = 0;
                DateTime lastUpdate = DateTime.Now;
                long lastDownloaded = 0;
                long maxSpeed = 0;
                double smoothSpeed = 0;

                using (var rawStream = response.Content.ReadAsStream())
                using (var stream = new BufferedStream(rawStream, 4 * 1024 * 1024))
                using (var fileStream = new FileStream(task.LocalPath, FileMode.Create, FileAccess.Write,
                    FileShare.None, 1024 * 1024, FileOptions.SequentialScan))
                {
                    byte[] buffer = new byte[1024 * 1024];
                    int read;
                    while ((read = stream.Read(buffer, 0, buffer.Length)) > 0)
                    {
                        if (task.CancellationTokenSource?.IsCancellationRequested == true)
                            throw new OperationCanceledException();

                        fileStream.Write(buffer, 0, read);
                        downloaded += read;

                        var now = DateTime.Now;
                        if ((now - lastUpdate).TotalMilliseconds > 500)
                        {
                            double seconds = (now - lastUpdate).TotalSeconds;
                            double instantSpeed = seconds > 0 ? (downloaded - lastDownloaded) / seconds : 0;
                            smoothSpeed = smoothSpeed < 1000 ? instantSpeed : smoothSpeed * 0.7 + instantSpeed * 0.3;
                            if (smoothSpeed > maxSpeed) maxSpeed = (long)smoothSpeed;

                            double progress = totalBytes > 0 ? (double)downloaded / totalBytes * 100 : 0;
                            long dl = downloaded;

                            string eta = "";
                            if (smoothSpeed > 1000 && downloaded < totalBytes)
                            {
                                double remaining = (totalBytes - downloaded) / smoothSpeed;
                                eta = remaining < 60 ? $" ~{remaining:F0}s" :
                                      remaining < 3600 ? $" ~{remaining / 60:F1}m" :
                                      $" ~{remaining / 3600:F1}h";
                            }

                            string statusText = $"{Sz(dl)}/{Sz(totalBytes)} | {Spd(smoothSpeed)} | HTTP/2 | {Spd(maxSpeed)} peak{eta}";
                            Dispatcher.BeginInvoke(() =>
                            {
                                task.DownloadedBytes = dl;
                                task.Progress = progress;
                                task.Status = statusText;
                            });

                            lastUpdate = now;
                            lastDownloaded = downloaded;
                        }
                    }
                    fileStream.Flush();
                } // Streams are guaranteed closed here

                // ════════════════════════════════════════════════════════════════
                //  FIXED: Force garbage collection and wait for file handle release
                // ════════════════════════════════════════════════════════════════
                GC.Collect();
                GC.WaitForPendingFinalizers();
                Thread.Sleep(100);

                // ── STEP 6: Verify ──────────────────────────────────────────────
                long actualSize = new FileInfo(task.LocalPath).Length;

                if (actualSize != totalBytes && Math.Abs(actualSize - totalBytes) > totalBytes * 0.01)
                    throw new Exception($"Size mismatch: expected {Sz(totalBytes)}, got {Sz(actualSize)}");

                double avgSpeed = sw.Elapsed.TotalSeconds > 0 ? downloaded / sw.Elapsed.TotalSeconds : 0;

                Dispatcher.Invoke(() =>
                {
                    task.DownloadedBytes = downloaded;
                    task.Progress = 100;
                    task.Status = $"✓ {Sz(downloaded)} in {sw.Elapsed:mm\\:ss} @ {Spd(avgSpeed)} HTTP/2 (peak: {Spd(maxSpeed)})";
                    Status($"HTTP/2 download complete: {task.Name} @ {Spd(avgSpeed)}");
                });

                // Auto extract + decrypt if enabled
                PostDownloadProcess(task);
            }
            catch (OperationCanceledException)
            {
                try { File.Delete(task.LocalPath); } catch { }
                Dispatcher.Invoke(() => { task.Status = "Cancelled"; Status($"Cancelled: {task.Name}"); });
            }
            catch (Exception ex)
            {
                try { File.Delete(task.LocalPath); } catch { }
                Dispatcher.Invoke(() =>
                {
                    Status($"HTTP/2 failed: {ex.Message}, falling back to TCP optimized...");
                });
                DynamicSegmentDownload(task);
            }
            finally
            {
                sw.Stop();
            }
        }
        // ════════════════════════════════════════════════════════════════
        //  MISSING METHOD: ProbeFileSize — HTTP/1.1 fallback size probe
        // ════════════════════════════════════════════════════════════════
        private long ProbeFileSize(string url)
        {
            try
            {
                var handler = new HttpClientHandler
                {
                    AllowAutoRedirect = true,
                    MaxAutomaticRedirections = 10
                };
                using var client = new HttpClient(handler) { Timeout = TimeSpan.FromSeconds(15) };
                client.DefaultRequestHeaders.Add("User-Agent", USER_AGENTS[_uaIndex % USER_AGENTS.Length]);

                // Try HEAD first
                var headReq = new HttpRequestMessage(HttpMethod.Head, url);
                var headResp = client.SendAsync(headReq, HttpCompletionOption.ResponseHeadersRead).Result;
                if (headResp.IsSuccessStatusCode && headResp.Content.Headers.ContentLength.HasValue)
                    return headResp.Content.Headers.ContentLength.Value;

                // Try Range GET probe
                var rangeReq = new HttpRequestMessage(HttpMethod.Get, url);
                rangeReq.Headers.Range = new System.Net.Http.Headers.RangeHeaderValue(0, 0);
                var rangeResp = client.SendAsync(rangeReq, HttpCompletionOption.ResponseHeadersRead).Result;
                if (rangeResp.Content.Headers.ContentRange?.Length.HasValue == true)
                    return rangeResp.Content.Headers.ContentRange.Length.Value;

                return 0;
            }
            catch { return 0; }
        }

        // ════════════════════════════════════════════════════════════════
        //  MISSING METHOD: IsFinished — check if a download is done
        // ════════════════════════════════════════════════════════════════
        private static bool IsFinished(string status)
        {
            if (string.IsNullOrEmpty(status)) return false;
            return status.StartsWith("✓") ||
                   status == "Cancelled" ||
                   status.StartsWith("Error") ||
                   status.StartsWith("Failed") ||
                   status.Contains("complete", StringComparison.OrdinalIgnoreCase);
        }

        // ════════════════════════════════════════════════════════════════
        //  DYNAMIC SEGMENT DOWNLOAD — Multi-connection IDM/FDM style
        //  Fallback when HTTP/2 single-stream fails or gets throttled
        // ════════════════════════════════════════════════════════════════
        private void DynamicSegmentDownload(DownloadTask task)
        {
            var sw = Stopwatch.StartNew();

            try
            {
                Dispatcher.Invoke(() => task.Status = "TCP multi-segment starting...");

                // ── Probe file size ──────────────────────────────────────
                long totalBytes = task.TotalSize > 0 ? task.TotalSize : ProbeFileSize(task.Url);
                if (totalBytes <= 0)
                {
                    // Last resort: do a full GET and stream it
                    SingleStreamFallback(task);
                    return;
                }

                task.TotalBytes = totalBytes;
                task.TotalSize = totalBytes;

                // ── Check range support ──────────────────────────────────
                bool supportsRange = CheckRangeSupport(task.Url);
                if (!supportsRange)
                {
                    SingleStreamFallback(task);
                    return;
                }

                // ── Pre-allocate file ────────────────────────────────────
                Directory.CreateDirectory(Path.GetDirectoryName(task.LocalPath));
                using var fs = new FileStream(task.LocalPath, FileMode.Create, FileAccess.Write, FileShare.Write, 64 * 1024);
                fs.SetLength(totalBytes);
                fs.Close();

                // ── Build initial segments ───────────────────────────────
                int numConnections = Math.Min(DL_INITIAL_CONNECTIONS, (int)(totalBytes / DL_MIN_SEGMENT_BYTES));
                if (numConnections < 1) numConnections = 1;

                long segmentSize = totalBytes / numConnections;
                var segments = new List<DownloadSegment>();
                for (int i = 0; i < numConnections; i++)
                {
                    long start = i * segmentSize;
                    long end = (i == numConnections - 1) ? totalBytes - 1 : start + segmentSize - 1;
                    segments.Add(new DownloadSegment { Start = start, End = end, Downloaded = 0 });
                }

                var segLock = new object();
                long totalDownloaded = 0;
                int activeWorkers = 0;
                int maxWorkers = numConnections;
                DateTime lastUiUpdate = DateTime.Now;
                long lastReported = 0;
                long peakSpeed = 0;
                bool cancelled = false;

                Dispatcher.Invoke(() => task.Status = $"Downloading with {numConnections} connections...");

                // ── Worker function ──────────────────────────────────────
                void WorkerLoop(int workerId)
                {
                    Interlocked.Increment(ref activeWorkers);
                    try
                    {
                        while (!cancelled && !task.CancellationTokenSource.IsCancellationRequested)
                        {
                            // Find a segment to work on
                            DownloadSegment seg = null;
                            lock (segLock)
                            {
                                // First: find an unstarted segment
                                seg = segments.FirstOrDefault(s => !s.Started && !s.Completed);
                                if (seg != null) { seg.Started = true; }
                                else
                                {
                                    // Work stealing: find the largest incomplete segment and split it
                                    var largest = segments
                                        .Where(s => s.Started && !s.Completed && s.Remaining > DL_MIN_SEGMENT_BYTES * 2)
                                        .OrderByDescending(s => s.Remaining)
                                        .FirstOrDefault();

                                    if (largest != null)
                                    {
                                        long midpoint = largest.Start + largest.Downloaded + largest.Remaining / 2;
                                        var newSeg = new DownloadSegment
                                        {
                                            Start = midpoint,
                                            End = largest.End,
                                            Downloaded = 0,
                                            Started = true
                                        };
                                        largest.End = midpoint - 1;
                                        segments.Add(newSeg);
                                        seg = newSeg;
                                    }
                                }
                            }

                            if (seg == null) break; // No more work

                            // Download the segment
                            for (int retry = 0; retry < DL_WORKER_RETRY; retry++)
                            {
                                try
                                {
                                    DownloadSegmentRange(task, seg, ref totalDownloaded, ref cancelled);
                                    break;
                                }
                                catch (OperationCanceledException) { cancelled = true; break; }
                                catch
                                {
                                    if (retry == DL_WORKER_RETRY - 1) throw;
                                    Thread.Sleep(500 * (retry + 1));
                                }
                            }

                            // Update UI
                            var now = DateTime.Now;
                            if ((now - lastUiUpdate).TotalMilliseconds > 500)
                            {
                                double elapsed = (now - lastUiUpdate).TotalSeconds;
                                double speed = elapsed > 0 ? (totalDownloaded - lastReported) / elapsed : 0;
                                if (speed > peakSpeed) peakSpeed = (long)speed;
                                double progress = totalBytes > 0 ? (double)totalDownloaded / totalBytes * 100 : 0;

                                string eta = "";
                                if (speed > 1000 && totalDownloaded < totalBytes)
                                {
                                    double remaining = (totalBytes - totalDownloaded) / speed;
                                    eta = remaining < 60 ? $" ~{remaining:F0}s" :
                                          remaining < 3600 ? $" ~{remaining / 60:F1}m" :
                                          $" ~{remaining / 3600:F1}h";
                                }

                                try
                                {
                                    long dl = totalDownloaded; // capture for closure
                                    string statusText = $"{Sz(dl)}/{Sz(totalBytes)} | {Spd(speed)} | {activeWorkers}x TCP | {Spd(peakSpeed)} peak{eta}";
                                    Dispatcher.BeginInvoke(() =>
                                    {
                                        task.DownloadedBytes = dl;
                                        task.Progress = progress;
                                        task.Status = statusText;
                                    });
                                }
                                catch { }

                                lastUiUpdate = now;
                                lastReported = totalDownloaded;
                            }
                        }
                    }
                    catch (Exception ex)
                    {
                        Debug.WriteLine($"Worker {workerId} error: {ex.Message}");
                    }
                    finally
                    {
                        Interlocked.Decrement(ref activeWorkers);
                    }
                }

                // ── Launch workers ───────────────────────────────────────
                var threads = new List<Thread>();
                for (int i = 0; i < maxWorkers; i++)
                {
                    int id = i;
                    var t = new Thread(() => WorkerLoop(id))
                    {
                        IsBackground = true,
                        Name = $"DL_Seg_{id}_{task.Name}"
                    };
                    t.Start();
                    threads.Add(t);
                    Thread.Sleep(50); // Stagger connections
                }

                // ── Ramp up: add more workers over time ──────────────────
                var rampThread = new Thread(() =>
                {
                    Thread.Sleep(DL_RAMP_INTERVAL_MS);
                    while (!cancelled && !task.CancellationTokenSource.IsCancellationRequested &&
                           maxWorkers < DL_MAX_CONNECTIONS)
                    {
                        bool hasWork;
                        lock (segLock)
                        {
                            hasWork = segments.Any(s => !s.Completed && s.Remaining > DL_MIN_SEGMENT_BYTES * 2);
                        }
                        if (!hasWork) break;

                        maxWorkers++;
                        int id = maxWorkers;
                        var t = new Thread(() => WorkerLoop(id)) { IsBackground = true, Name = $"DL_Seg_{id}_{task.Name}" };
                        t.Start();
                        threads.Add(t);

                        Thread.Sleep(DL_RAMP_INTERVAL_MS);
                    }
                })
                { IsBackground = true };
                rampThread.Start();

                // ── Wait for all workers ─────────────────────────────────
                foreach (var t in threads) t.Join();
                rampThread.Join(5000);

                if (cancelled || task.CancellationTokenSource.IsCancellationRequested)
                    throw new OperationCanceledException();

                // ── Verify ───────────────────────────────────────────────
                long actualSize = new FileInfo(task.LocalPath).Length;
                double avgSpeed = sw.Elapsed.TotalSeconds > 0 ? totalDownloaded / sw.Elapsed.TotalSeconds : 0;

                Dispatcher.Invoke(() =>
                {
                    task.DownloadedBytes = totalDownloaded;
                    task.Progress = 100;
                    task.Status = $"✓ {Sz(totalDownloaded)} in {sw.Elapsed:mm\\:ss} @ {Spd(avgSpeed)} TCP (peak: {Spd(peakSpeed)})";
                    Status($"Download complete: {task.Name} @ {Spd(avgSpeed)}");
                });

                // Auto extract + decrypt if enabled
                PostDownloadProcess(task);
            }
            catch (OperationCanceledException)
            {
                try { File.Delete(task.LocalPath); } catch { }
                Dispatcher.Invoke(() => { task.Status = "Cancelled"; Status($"Cancelled: {task.Name}"); });
            }
            catch (Exception ex)
            {
                try { File.Delete(task.LocalPath); } catch { }
                Dispatcher.Invoke(() =>
                {
                    task.Status = $"Error: {ex.Message}";
                    Status($"Download failed: {task.Name} - {ex.Message}");
                });
            }
            finally { sw.Stop(); }
        }

        private void DownloadSegmentRange(DownloadTask task, DownloadSegment seg, ref long totalDownloaded, ref bool cancelled)
        {
            long rangeStart = seg.Start + seg.Downloaded;
            long rangeEnd = seg.End;

            if (rangeStart > rangeEnd) { seg.Completed = true; return; }

            var handler = new HttpClientHandler { AllowAutoRedirect = true, MaxAutomaticRedirections = 10 };
            using var client = new HttpClient(handler) { Timeout = TimeSpan.FromMilliseconds(DL_READ_TIMEOUT) };

            // Rotate user agents
            int uaIdx = Interlocked.Increment(ref _uaIndex);
            client.DefaultRequestHeaders.Add("User-Agent", USER_AGENTS[uaIdx % USER_AGENTS.Length]);
            client.DefaultRequestHeaders.Add("Accept", "*/*");
            client.DefaultRequestHeaders.Add("Accept-Encoding", "identity");
            client.DefaultRequestHeaders.Add("Referer", "https://myrient.erista.me/files/");
            client.DefaultRequestHeaders.Add("Connection", "keep-alive");

            var request = new HttpRequestMessage(HttpMethod.Get, task.Url);
            request.Headers.Range = new System.Net.Http.Headers.RangeHeaderValue(rangeStart, rangeEnd);

            var response = client.SendAsync(request, HttpCompletionOption.ResponseHeadersRead,
                task.CancellationTokenSource.Token).Result;

            if (!response.IsSuccessStatusCode && (int)response.StatusCode != 206)
                throw new Exception($"HTTP {response.StatusCode}");

            using var stream = response.Content.ReadAsStream();
            using var fileStream = new FileStream(task.LocalPath, FileMode.Open, FileAccess.Write, FileShare.ReadWrite, 512 * 1024);
            fileStream.Seek(rangeStart, SeekOrigin.Begin);

            byte[] buffer = new byte[512 * 1024]; // 512KB read buffer
            int read;
            while ((read = stream.Read(buffer, 0, buffer.Length)) > 0)
            {
                if (task.CancellationTokenSource.IsCancellationRequested || cancelled)
                    throw new OperationCanceledException();

                fileStream.Write(buffer, 0, read);
                seg.Downloaded += read;
                Interlocked.Add(ref totalDownloaded, read);
            }

            seg.Completed = true;
        }

        private bool CheckRangeSupport(string url)
        {
            try
            {
                using var client = new HttpClient { Timeout = TimeSpan.FromSeconds(10) };
                client.DefaultRequestHeaders.Add("User-Agent", USER_AGENTS[0]);
                var req = new HttpRequestMessage(HttpMethod.Get, url);
                req.Headers.Range = new System.Net.Http.Headers.RangeHeaderValue(0, 0);
                var resp = client.SendAsync(req, HttpCompletionOption.ResponseHeadersRead).Result;
                return (int)resp.StatusCode == 206 || resp.Headers.AcceptRanges?.Contains("bytes") == true;
            }
            catch { return false; }
        }

        // ── Single stream fallback (no range support) ────────────────
        private void SingleStreamFallback(DownloadTask task)
        {
            Dispatcher.Invoke(() => task.Status = "Single-stream download...");

            var handler = new HttpClientHandler { AllowAutoRedirect = true };
            using var client = new HttpClient(handler) { Timeout = TimeSpan.FromMinutes(60) };
            client.DefaultRequestHeaders.Add("User-Agent", USER_AGENTS[0]);
            client.DefaultRequestHeaders.Add("Accept", "*/*");

            var response = client.SendAsync(new HttpRequestMessage(HttpMethod.Get, task.Url),
                HttpCompletionOption.ResponseHeadersRead, task.CancellationTokenSource.Token).Result;

            if (!response.IsSuccessStatusCode)
                throw new Exception($"HTTP {response.StatusCode}");

            long totalBytes = response.Content.Headers.ContentLength ?? task.TotalSize;
            if (totalBytes > 0) { task.TotalBytes = totalBytes; task.TotalSize = totalBytes; }

            using var stream = response.Content.ReadAsStream();
            using var fileStream = new FileStream(task.LocalPath, FileMode.Create, FileAccess.Write,
                FileShare.None, 1024 * 1024, FileOptions.SequentialScan | FileOptions.Asynchronous);

            byte[] buffer = new byte[1024 * 1024]; // 1MB buffer
            long downloaded = 0;
            var sw = Stopwatch.StartNew();
            DateTime lastUpdate = DateTime.Now;
            long lastDownloaded = 0;
            long maxSpeed = 0;

            int read;
            while ((read = stream.Read(buffer, 0, buffer.Length)) > 0)
            {
                if (task.CancellationTokenSource.IsCancellationRequested)
                    throw new OperationCanceledException();

                fileStream.Write(buffer, 0, read);
                downloaded += read;

                var now = DateTime.Now;
                if ((now - lastUpdate).TotalMilliseconds > 500)
                {
                    double seconds = (now - lastUpdate).TotalSeconds;
                    double speed = seconds > 0 ? (downloaded - lastDownloaded) / seconds : 0;
                    if (speed > maxSpeed) maxSpeed = (long)speed;
                    double progress = totalBytes > 0 ? (double)downloaded / totalBytes * 100 : 0;
                    long dl = downloaded;

                    try
                    {
                        string statusText = $"{Sz(dl)}/{Sz(totalBytes)} | {Spd(speed)} | Stream | {Spd(maxSpeed)} peak";
                        Dispatcher.BeginInvoke(() =>
                        {
                            task.DownloadedBytes = dl;
                            task.Progress = progress;
                            task.Status = statusText;
                        });
                    }
                    catch { }

                    lastUpdate = now;
                    lastDownloaded = downloaded;
                }
            }

            double avgSpeed = sw.Elapsed.TotalSeconds > 0 ? downloaded / sw.Elapsed.TotalSeconds : 0;
            Dispatcher.BeginInvoke(() =>
            {
                task.DownloadedBytes = downloaded;
                task.Progress = 100;
                task.Status = $"✓ {Sz(downloaded)} in {sw.Elapsed:mm\\:ss} @ {Spd(avgSpeed)} (peak: {Spd(maxSpeed)})";
                Status($"Download complete: {task.Name} @ {Spd(avgSpeed)}");
            });

            // Auto extract + decrypt if enabled
            PostDownloadProcess(task);
        }

        // ════════════════════════════════════════════════════════════════
        //  POST-DOWNLOAD: Extract ZIP → Find ISO → Decrypt with ps3dec
        // ════════════════════════════════════════════════════════════════

        /// Called after any successful download. Checks if auto-decrypt is
        /// enabled, extracts .zip, locates .iso inside, matches a key from
        /// the DKeys folder, and runs ps3dec.exe.
        private void PostDownloadProcess(DownloadTask task)
        {
            // Check if auto-decrypt is enabled on the UI thread
            bool autoDecrypt = false;
            Dispatcher.Invoke(() => autoDecrypt = chkAutoDecrypt.IsChecked == true);
            if (!autoDecrypt) return;

            // Only process .zip files
            if (!task.LocalPath.EndsWith(".zip", StringComparison.OrdinalIgnoreCase)) return;

            try
            {
                // ── STEP 1: Extract ZIP (ALL platforms) ──────────────────
                Dispatcher.BeginInvoke(() => { task.Status = "📦 Extracting ZIP..."; task.Progress = 0; });

                string extractDir = Path.Combine(Path.GetDirectoryName(task.LocalPath), Path.GetFileNameWithoutExtension(task.LocalPath));
                Directory.CreateDirectory(extractDir);

                // Extract with progress
                using (var archive = ZipFile.OpenRead(task.LocalPath))
                {
                    int totalEntries = archive.Entries.Count;
                    int extracted = 0;

                    foreach (var entry in archive.Entries)
                    {
                        if (task.CancellationTokenSource?.IsCancellationRequested == true)
                            throw new OperationCanceledException();

                        string destPath = Path.Combine(extractDir, entry.FullName);
                        string destDir = Path.GetDirectoryName(destPath);
                        if (!string.IsNullOrEmpty(destDir))
                            Directory.CreateDirectory(destDir);

                        if (string.IsNullOrEmpty(entry.Name)) { extracted++; continue; }

                        entry.ExtractToFile(destPath, overwrite: true);
                        extracted++;

                        double pct = (double)extracted / totalEntries * 100;
                        Dispatcher.BeginInvoke(() =>
                        {
                            task.Progress = pct;
                            task.Status = $"📦 Extracting... {extracted}/{totalEntries}";
                        });
                    }
                }

                // ════════════════════════════════════════════════════════════════
                //  ONLY DECRYPT PS3 GAMES - Skip decryption for PS1/PS2
                //  (but still extract and cleanup ZIP)
                // ════════════════════════════════════════════════════════════════
                if (task.Platform != "PS3")
                {
                    Dispatcher.BeginInvoke(() =>
                    {
                        task.Status = $"📦 Extracted ✓ ({task.Platform} - no decryption needed)";
                        Status($"Extracted {task.Platform} game: {task.Name}");
                    });

                    // Cleanup ZIP for non-PS3 games too
                    try
                    {
                        if (File.Exists(task.LocalPath))
                            File.Delete(task.LocalPath);
                    }
                    catch { }
                    return;
                }

                // ── STEP 2: Find ISO file(s) for PS3 games only ──────────
                Dispatcher.BeginInvoke(() => task.Status = "📦 Extraction complete, searching for ISO...");

                var isoFiles = Directory.GetFiles(extractDir, "*.iso", SearchOption.AllDirectories);
                if (isoFiles.Length == 0)
                    isoFiles = Directory.GetFiles(extractDir, "*.bin", SearchOption.AllDirectories);

                if (isoFiles.Length == 0)
                {
                    Dispatcher.BeginInvoke(() =>
                    {
                        task.Status = "📦 Extracted ✓ (no ISO found to decrypt)";
                        Status($"No ISO found in {Path.GetFileName(task.LocalPath)}");
                    });
                    return;
                }

                // Process each ISO found (only PS3 games reach this point)
                foreach (var isoPath in isoFiles)
                {
                    DecryptIso(task, isoPath);
                }

                // ── STEP 3: Cleanup — delete ZIP after successful decrypt ─
                try
                {
                    if (File.Exists(task.LocalPath))
                        File.Delete(task.LocalPath);
                    Dispatcher.BeginInvoke(() => Status($"Cleaned up ZIP: {task.Name}"));
                }
                catch (Exception ex)
                {
                    Debug.WriteLine($"Failed to delete ZIP: {ex.Message}");
                }
            }
            catch (OperationCanceledException)
            {
                Dispatcher.BeginInvoke(() => { task.Status = "Cancelled (during extract/decrypt)"; });
            }
            catch (Exception ex)
            {
                Dispatcher.BeginInvoke(() =>
                {
                    task.Status = $"📦 Extract/Decrypt error: {ex.Message}";
                    Status($"Post-download error: {ex.Message}");
                });
            }
        }

        /// Decrypt a single ISO using ps3dec.exe and a key from the DKeys folder.
        private void DecryptIso(DownloadTask task, string isoPath)
        {
            string isoName = Path.GetFileNameWithoutExtension(isoPath);
            Dispatcher.BeginInvoke(() =>
            {
                task.Status = $"🔑 Looking for decryption key for: {isoName}";
                task.Progress = 0;
            });

            // ── Find ps3dec.exe ──────────────────────────────────────────
            string ps3decPath = FindPs3Dec();
            if (string.IsNullOrEmpty(ps3decPath))
            {
                Dispatcher.BeginInvoke(() =>
                {
                    task.Status = $"📦 Extracted ✓ (ps3dec.exe not found — skipping decrypt)";
                    Status("ps3dec.exe not found. Place it in app folder or DKeys folder.");
                });
                return;
            }

            // ── Find matching key in DKeys folder ────────────────────────
            string dkeysPath = FindDKeysFolder();
            string decryptionKey = null;

            if (!string.IsNullOrEmpty(dkeysPath) && Directory.Exists(dkeysPath))
            {
                // Search for a key file whose name matches part of the ISO name
                decryptionKey = FindMatchingKey(dkeysPath, isoName);

                if (decryptionKey == null)
                {
                    // Try with the parent task name (ZIP filename) too
                    string zipStem = Path.GetFileNameWithoutExtension(task.Name);
                    decryptionKey = FindMatchingKey(dkeysPath, zipStem);
                }
            }
            else
            {
                Dispatcher.BeginInvoke(() =>
                {
                    task.Status = $"📦 Extracted ✓ (DKeys folder not found — skipping decrypt)";
                    Status("DKeys folder not found. Create it next to PS3 Manager.");
                });
                return;
            }

            if (string.IsNullOrEmpty(decryptionKey))
            {
                Dispatcher.BeginInvoke(() =>
                {
                    task.Status = $"📦 Extracted ✓ (no matching key found — skipping decrypt)";
                    Status($"No decryption key found for {isoName}");
                });
                return;
            }

            // ── Build ps3dec command ─────────────────────────────────────
            // Usage: PS3Dec <mode> <type> [type_op] in [out]
            // <mode>: 'd' for decrypt
            // <type>: "d1" (key before processing) or "key" (actual disc_key)
            // We'll use "key" since we have the actual 32-char hex key

            string outputDir = Path.GetDirectoryName(isoPath);
            string outputName = isoName + "_decrypted.iso";
            string outputPath = Path.Combine(outputDir, outputName);

            // Arguments: d key <32_char_key> "<input_iso>" "<output_iso>"
            string arguments = $"d key {decryptionKey} \"{isoPath}\" \"{outputPath}\"";

            Dispatcher.BeginInvoke(() =>
            {
                task.Status = $"🔓 Decrypting {isoName}...";
                task.Progress = 0;
                Status($"Running ps3dec: {Path.GetFileName(ps3decPath)} d key *** \"{isoName}\"");
            });

            // ── Run ps3dec.exe ───────────────────────────────────────────
            var psi = new ProcessStartInfo
            {
                FileName = ps3decPath,
                Arguments = arguments,
                UseShellExecute = false,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                CreateNoWindow = true,
                WorkingDirectory = Path.GetDirectoryName(ps3decPath)
            };

            var sw = Stopwatch.StartNew();

            using var proc = new Process();
            proc.StartInfo = psi;
            proc.EnableRaisingEvents = true;

            // Capture output for progress parsing
            var outputLines = new List<string>();
            proc.OutputDataReceived += (s, e) =>
            {
                if (string.IsNullOrEmpty(e.Data)) return;
                outputLines.Add(e.Data);
                Debug.WriteLine($"[ps3dec] {e.Data}");

                // Try to parse progress from ps3dec output
                var pctMatch = Regex.Match(e.Data, @"(\d+(?:\.\d+)?)%");
                if (pctMatch.Success && double.TryParse(pctMatch.Groups[1].Value, out double pct))
                {
                    Dispatcher.BeginInvoke(() =>
                    {
                        task.Progress = pct;
                        task.Status = $"🔓 Decrypting... {pct:F1}%";
                    });
                }

                // Also look for progress indicators like "123MB/456MB"
                var byteMatch = Regex.Match(e.Data, @"([\d.]+)\s*[KMGT]?B\s*/\s*([\d.]+)\s*[KMGT]?B");
                if (byteMatch.Success)
                {
                    Dispatcher.BeginInvoke(() =>
                    {
                        task.Status = $"🔓 Decrypting... {e.Data.Trim()}";
                    });
                }
            };

            proc.ErrorDataReceived += (s, e) =>
            {
                if (!string.IsNullOrEmpty(e.Data))
                {
                    Debug.WriteLine($"[ps3dec ERR] {e.Data}");
                    outputLines.Add($"ERROR: {e.Data}");
                }
            };

            proc.Start();
            proc.BeginOutputReadLine();
            proc.BeginErrorReadLine();

            // Wait for completion (non-blocking to allow cancellation)
            while (!proc.WaitForExit(1000))
            {
                if (task.CancellationTokenSource?.IsCancellationRequested == true)
                {
                    try { proc.Kill(entireProcessTree: true); } catch { }
                    throw new OperationCanceledException();
                }
            }
            proc.WaitForExit();

            sw.Stop();

            if (proc.ExitCode == 0)
            {
                // ── Success: cleanup original ISO, keep decrypted ────────
                bool decryptedExists = File.Exists(outputPath);

                // Delete the encrypted ISO to save space
                try
                {
                    if (decryptedExists && File.Exists(isoPath))
                        File.Delete(isoPath);
                }
                catch (Exception ex) { Debug.WriteLine($"Cleanup error: {ex.Message}"); }

                Dispatcher.BeginInvoke(() =>
                {
                    task.Progress = 100;
                    task.Status = $"✓ Decrypted in {sw.Elapsed:mm\\:ss} → {outputName}";
                    Status($"Decryption complete: {isoName} → {outputName}");
                });
            }
            else
            {
                string lastError = outputLines.LastOrDefault(l => l.StartsWith("ERROR:")) ?? $"Exit code {proc.ExitCode}";
                Dispatcher.BeginInvoke(() =>
                {
                    task.Status = $"⚠ Decrypt failed: {lastError}";
                    Status($"ps3dec failed for {isoName}: {lastError}");
                });
            }
        }

        // ─── Helper: Find ps3dec.exe ─────────────────────────────────────
        private string FindPs3Dec()
        {
            // Search order: app dir, DKeys folder, PATH
            string appDir = AppDomain.CurrentDomain.BaseDirectory;

            string[] searchPaths = new[]
            {
                Path.Combine(appDir, "ps3dec.exe"),
                Path.Combine(appDir, "DKeys", "ps3dec.exe"),
                Path.Combine(appDir, "tools", "ps3dec.exe"),
                "ps3dec.exe" // will find via PATH
            };

            foreach (var p in searchPaths)
            {
                if (File.Exists(p)) return Path.GetFullPath(p);
            }

            // Check PATH
            try
            {
                var which = new ProcessStartInfo
                {
                    FileName = "where",
                    Arguments = "ps3dec.exe",
                    UseShellExecute = false,
                    RedirectStandardOutput = true,
                    CreateNoWindow = true
                };
                var proc = Process.Start(which);
                string result = proc.StandardOutput.ReadToEnd().Trim();
                proc.WaitForExit();
                if (proc.ExitCode == 0 && File.Exists(result.Split('\n')[0].Trim()))
                    return result.Split('\n')[0].Trim();
            }
            catch { }

            return null;
        }

        // ─── Helper: Find DKeys folder ───────────────────────────────────
        private string FindDKeysFolder()
        {
            string appDir = AppDomain.CurrentDomain.BaseDirectory;

            string[] searchPaths = new[]
            {
                Path.Combine(appDir, "DKeys"),
                Path.Combine(appDir, "dkeys"),
                Path.Combine(appDir, "keys"),
                Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), "DKeys"),
            };

            foreach (var p in searchPaths)
            {
                if (Directory.Exists(p)) return p;
            }

            return null;
        }

        // ─── Helper: Find matching key file ──────────────────────────────
        /// Searches the DKeys folder for a file whose name matches the ISO name.
        /// Key files can be named like "GAMEID.dkey", "Game Name.key", "Game Name.txt"
        /// or just contain the game name. Returns the 32-char hex key string or null.
        private string FindMatchingKey(string dkeysFolder, string isoName)
        {
            if (string.IsNullOrEmpty(isoName) || !Directory.Exists(dkeysFolder)) return null;

            // Normalize the ISO name for matching
            string normalizedIso = isoName
                .Replace("_", " ")
                .Replace("-", " ")
                .Replace(".", " ")
                .Trim();

            try
            {
                foreach (var keyFile in Directory.GetFiles(dkeysFolder))
                {
                    string keyFileName = Path.GetFileNameWithoutExtension(keyFile);
                    string normalizedKey = keyFileName
                        .Replace("_", " ")
                        .Replace("-", " ")
                        .Replace(".", " ")
                        .Trim();

                    // Check if either name contains the other (fuzzy match)
                    bool match = normalizedIso.Contains(normalizedKey, StringComparison.OrdinalIgnoreCase) ||
                                 normalizedKey.Contains(normalizedIso, StringComparison.OrdinalIgnoreCase);

                    // Also try matching just the game ID (e.g., BLUS30443, BLES01234)
                    if (!match)
                    {
                        var gameIdPattern = Regex.Match(isoName, @"[A-Z]{4}\d{5}");
                        if (gameIdPattern.Success)
                        {
                            match = keyFileName.Contains(gameIdPattern.Value, StringComparison.OrdinalIgnoreCase);
                        }
                    }

                    if (match)
                    {
                        string keyContent = File.ReadAllText(keyFile).Trim();

                        // Clean up: remove whitespace, newlines, BOM
                        keyContent = keyContent
                            .Replace("\r", "")
                            .Replace("\n", "")
                            .Replace(" ", "")
                            .Trim();

                        // Validate it looks like a hex key (32 hex chars = 16 bytes AES-128)
                        string hexOnly = Regex.Replace(keyContent, @"[^0-9a-fA-F]", "");

                        if (hexOnly.Length == 32)
                        {
                            Debug.WriteLine($"Found key for '{isoName}' in '{Path.GetFileName(keyFile)}': {hexOnly}");
                            return hexOnly;
                        }
                        else
                        {
                            Debug.WriteLine($"Key file '{keyFile}' matched but content invalid (len={hexOnly.Length})");
                        }
                    }
                }
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"Error searching DKeys: {ex.Message}");
            }

            return null;
        }

        // ─── Helper: Setup keys folder for ps3dec --auto mode ────────────
        /// ps3dec --auto expects keys in a folder called "keys" next to the exe.
        /// This copies all DKeys into that location.
        private void SetupKeysForAuto(string ps3decPath, string dkeysFolder)
        {
            try
            {
                string ps3decDir = Path.GetDirectoryName(ps3decPath);
                string keysDir = Path.Combine(ps3decDir, "keys");
                Directory.CreateDirectory(keysDir);

                foreach (var keyFile in Directory.GetFiles(dkeysFolder))
                {
                    string dest = Path.Combine(keysDir, Path.GetFileName(keyFile));
                    File.Copy(keyFile, dest, overwrite: true);
                }
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"Error setting up keys for auto mode: {ex.Message}");
            }
        }

        // ─── Format helpers ──────────────────────────────────────────
        private static string Spd(double b)
        {
            if (b < 1024) return $"{b:F0} B/s";
            if (b < 1048576) return $"{b / 1024:F1} KB/s";
            if (b < 1073741824) return $"{b / 1048576:F2} MB/s";
            return $"{b / 1073741824:F2} GB/s";
        }

        private static string Sz(long b)
        {
            if (b <= 0) return "0 B";
            string[] u = { "B", "KB", "MB", "GB", "TB" }; int i = 0; double s = b;
            while (s >= 1024 && i < u.Length - 1) { i++; s /= 1024; }
            return $"{s:0.##} {u[i]}";
        }

        private void CancelDownload_Click(object sender, RoutedEventArgs e)
        {
            var active = ActiveDownloads.Where(d => !IsFinished(d.Status)).ToList();
            if (active.Count == 0) { Status("Nothing to cancel"); return; }
            foreach (var t in active) { try { t.CancellationTokenSource?.Cancel(); t.Status = "Cancelling..."; } catch { } }
            Status($"Cancelling {active.Count} download(s)...");
        }

        private void ClearCompletedDownloads_Click(object sender, RoutedEventArgs e)
        {
            foreach (var t in ActiveDownloads.Where(d => IsFinished(d.Status)).ToList())
            { t.CancellationTokenSource?.Dispose(); ActiveDownloads.Remove(t); }
        }

        private void OpenDownloadsFolder_Click(object sender, RoutedEventArgs e)
        {
            string p = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), "Downloads");
            Directory.CreateDirectory(p);
            Process.Start(new ProcessStartInfo("explorer.exe", p) { UseShellExecute = true });
        }

        private void OpenDKeysFolder_Click(object sender, RoutedEventArgs e)
        {
            string dkeys = FindDKeysFolder();
            if (string.IsNullOrEmpty(dkeys))
            {
                // Create it next to the app
                dkeys = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "DKeys");
                Directory.CreateDirectory(dkeys);
                Status("Created DKeys folder — place your .dkey files here");
            }
            Process.Start(new ProcessStartInfo("explorer.exe", dkeys) { UseShellExecute = true });
        }

        #endregion

        #region Context Menus Setup
        private void SetupLocalContextMenu()
        {
            var contextMenu = new ContextMenu();
            contextMenu.Style = (Style)FindResource("DarkContextMenu");

            var copyItem = new MenuItem { Header = "📋 Copy" };
            copyItem.Click += (s, e) => LocalCopy();

            var cutItem = new MenuItem { Header = "✂️ Cut" };
            cutItem.Click += (s, e) => LocalCut();

            var pasteItem = new MenuItem { Header = "📄 Paste" };
            pasteItem.Click += (s, e) => LocalPaste();

            var deleteItem = new MenuItem { Header = "🗑️ Delete" };
            deleteItem.Click += (s, e) => LocalDelete();

            var renameItem = new MenuItem { Header = "✏️ Rename" };
            renameItem.Click += (s, e) => LocalRename();

            var separator1 = new Separator();

            var refreshItem = new MenuItem { Header = "🔄 Refresh" };
            refreshItem.Click += (s, e) => LoadLocalFiles(_localPath);

            var newFolderItem = new MenuItem { Header = "📁 New Folder" };
            newFolderItem.Click += (s, e) => LocalNewFolder();

            contextMenu.Items.Add(copyItem);
            contextMenu.Items.Add(cutItem);
            contextMenu.Items.Add(pasteItem);
            contextMenu.Items.Add(separator1);
            contextMenu.Items.Add(deleteItem);
            contextMenu.Items.Add(renameItem);
            contextMenu.Items.Add(new Separator());
            contextMenu.Items.Add(newFolderItem);
            contextMenu.Items.Add(refreshItem);

            lstLocal.ContextMenu = contextMenu;

            contextMenu.Opened += (s, e) =>
            {
                pasteItem.IsEnabled = _clipboardFiles.Count > 0 && _clipboardIsLocal;
            };
        }

        private void SetupRemoteContextMenu()
        {
            var contextMenu = new ContextMenu();
            contextMenu.Style = (Style)FindResource("DarkContextMenu");

            var copyItem = new MenuItem { Header = "📋 Copy" };
            copyItem.Click += (s, e) => RemoteCopy();

            var cutItem = new MenuItem { Header = "✂️ Cut" };
            cutItem.Click += (s, e) => RemoteCut();

            var pasteItem = new MenuItem { Header = "📄 Paste" };
            pasteItem.Click += (s, e) => RemotePaste();

            var deleteItem = new MenuItem { Header = "🗑️ Delete" };
            deleteItem.Click += (s, e) => RemoteDelete();

            var renameItem = new MenuItem { Header = "✏️ Rename" };
            renameItem.Click += (s, e) => RemoteRename();

            var separator1 = new Separator();

            var refreshItem = new MenuItem { Header = "🔄 Refresh" };
            refreshItem.Click += (s, e) => _ = LoadRemoteFilesAsync(_remotePath);

            var newFolderItem = new MenuItem { Header = "📁 New Folder" };
            newFolderItem.Click += (s, e) => RemoteNewFolder();

            contextMenu.Items.Add(copyItem);
            contextMenu.Items.Add(cutItem);
            contextMenu.Items.Add(pasteItem);
            contextMenu.Items.Add(separator1);
            contextMenu.Items.Add(deleteItem);
            contextMenu.Items.Add(renameItem);
            contextMenu.Items.Add(new Separator());
            contextMenu.Items.Add(newFolderItem);
            contextMenu.Items.Add(refreshItem);

            lstRemote.ContextMenu = contextMenu;

            contextMenu.Opened += (s, e) =>
            {
                pasteItem.IsEnabled = _clipboardFiles.Count > 0 && !_clipboardIsLocal && _connected;
            };
        }
        #endregion

        #region Local File Operations
        private void LocalCopy()
        {
            if (lstLocal.SelectedItems.Count == 0) return;
            _clipboardFiles = lstLocal.SelectedItems.Cast<FileItem>().ToList();
            _clipboardIsCut = false;
            _clipboardIsLocal = true;
            Status($"Copied {_clipboardFiles.Count} item(s) to clipboard");
        }

        private void LocalCut()
        {
            if (lstLocal.SelectedItems.Count == 0) return;
            _clipboardFiles = lstLocal.SelectedItems.Cast<FileItem>().ToList();
            _clipboardIsCut = true;
            _clipboardIsLocal = true;
            Status($"Cut {_clipboardFiles.Count} item(s) - ready to move");
        }

        private void LocalPaste()
        {
            if (_clipboardFiles.Count == 0 || !_clipboardIsLocal) return;

            foreach (var file in _clipboardFiles)
            {
                try
                {
                    string destPath = Path.Combine(_localPath, file.Name);
                    destPath = GetUniqueLocalPath(destPath);

                    if (file.IsDir)
                    {
                        if (_clipboardIsCut)
                            Directory.Move(file.Path, destPath);
                        else
                            CopyDirectoryLocal(file.Path, destPath);
                    }
                    else
                    {
                        if (_clipboardIsCut)
                            File.Move(file.Path, destPath);
                        else
                            File.Copy(file.Path, destPath, true);
                    }
                }
                catch (Exception ex)
                {
                    Status($"Error: {ex.Message}");
                }
            }

            if (_clipboardIsCut)
            {
                _clipboardFiles.Clear();
                Status("Move completed");
            }
            else
            {
                Status("Copy completed");
            }

            LoadLocalFiles(_localPath);
        }

        private void LocalDelete()
        {
            if (lstLocal.SelectedItems.Count == 0) return;

            var files = lstLocal.SelectedItems.Cast<FileItem>().ToList();
            var msg = files.Count == 1 ? $"Delete '{files[0].Name}'?" : $"Delete {files.Count} items?";

            if (MessageBox.Show(msg, "Confirm Delete", MessageBoxButton.YesNo, MessageBoxImage.Warning) != MessageBoxResult.Yes)
                return;

            foreach (var file in files)
            {
                try
                {
                    if (file.IsDir)
                        Directory.Delete(file.Path, true);
                    else
                        File.Delete(file.Path);
                }
                catch (Exception ex)
                {
                    Status($"Error deleting {file.Name}: {ex.Message}");
                }
            }

            LoadLocalFiles(_localPath);
            Status($"Deleted {files.Count} item(s)");
        }

        private void LocalRename()
        {
            if (lstLocal.SelectedItem is not FileItem file) return;

            var dialog = new InputDialog("Rename", "Enter new name:", file.Name);
            if (dialog.ShowDialog() != true) return;

            try
            {
                string newPath = Path.Combine(_localPath, dialog.ResponseText);
                if (file.IsDir)
                    Directory.Move(file.Path, newPath);
                else
                    File.Move(file.Path, newPath);

                LoadLocalFiles(_localPath);
                Status("Renamed successfully");
            }
            catch (Exception ex)
            {
                Status($"Error: {ex.Message}");
            }
        }

        private void LocalNewFolder()
        {
            var dialog = new InputDialog("New Folder", "Enter folder name:", "New Folder");
            if (dialog.ShowDialog() != true) return;

            try
            {
                string newPath = Path.Combine(_localPath, dialog.ResponseText);
                Directory.CreateDirectory(newPath);
                LoadLocalFiles(_localPath);
                Status("Folder created");
            }
            catch (Exception ex)
            {
                Status($"Error: {ex.Message}");
            }
        }

        private void CopyDirectoryLocal(string sourceDir, string destDir)
        {
            Directory.CreateDirectory(destDir);

            foreach (var file in Directory.GetFiles(sourceDir))
            {
                string destFile = Path.Combine(destDir, Path.GetFileName(file));
                File.Copy(file, destFile, true);
            }

            foreach (var dir in Directory.GetDirectories(sourceDir))
            {
                string destSubDir = Path.Combine(destDir, Path.GetFileName(dir));
                CopyDirectoryLocal(dir, destSubDir);
            }
        }

        private string GetUniqueLocalPath(string path)
        {
            if (!File.Exists(path) && !Directory.Exists(path)) return path;

            string dir = Path.GetDirectoryName(path);
            string name = Path.GetFileNameWithoutExtension(path);
            string ext = Path.GetExtension(path);
            int counter = 1;

            string newPath;
            do
            {
                newPath = Path.Combine(dir, $"{name} ({counter}){ext}");
                counter++;
            } while (File.Exists(newPath) || Directory.Exists(newPath));

            return newPath;
        }
        #endregion

        #region Remote File Operations
        private void RemoteCopy()
        {
            if (lstRemote.SelectedItems.Count == 0) return;
            _clipboardFiles = lstRemote.SelectedItems.Cast<FileItem>().ToList();
            _clipboardIsCut = false;
            _clipboardIsLocal = false;
            Status($"Copied {_clipboardFiles.Count} item(s) to clipboard");
        }

        private void RemoteCut()
        {
            if (lstRemote.SelectedItems.Count == 0) return;
            _clipboardFiles = lstRemote.SelectedItems.Cast<FileItem>().ToList();
            _clipboardIsCut = true;
            _clipboardIsLocal = false;
            Status($"Cut {_clipboardFiles.Count} item(s) - ready to move");
        }

        private async void RemotePaste()
        {
            if (_clipboardFiles.Count == 0 || _clipboardIsLocal || !_connected) return;

            foreach (var file in _clipboardFiles)
            {
                try
                {
                    string destPath = $"{_remotePath}/{file.Name}";
                    destPath = await GetUniqueRemotePath(destPath);

                    if (file.IsDir)
                    {
                        if (_clipboardIsCut)
                            await _ftp.MoveDirectory(file.Path, destPath);
                        else
                            await CopyDirectoryRemote(file.Path, destPath);
                    }
                    else
                    {
                        if (_clipboardIsCut)
                            await _ftp.MoveFile(file.Path, destPath, FtpRemoteExists.Overwrite);
                        else
                        {
                            string tempFile = Path.GetTempFileName();
                            try
                            {
                                await _ftp.DownloadFile(tempFile, file.Path, FtpLocalExists.Overwrite);
                                await _ftp.UploadFile(tempFile, destPath, FtpRemoteExists.Overwrite);
                            }
                            finally
                            {
                                try { File.Delete(tempFile); } catch { }
                            }
                        }
                    }
                }
                catch (Exception ex)
                {
                    Status($"Error: {ex.Message}");
                }
            }

            if (_clipboardIsCut)
            {
                _clipboardFiles.Clear();
                Status("Move completed");
            }
            else
            {
                Status("Copy completed");
            }

            await LoadRemoteFilesAsync(_remotePath);
        }

        private async void RemoteDelete()
        {
            if (lstRemote.SelectedItems.Count == 0 || !_connected) return;

            var files = lstRemote.SelectedItems.Cast<FileItem>().ToList();
            var msg = files.Count == 1 ? $"Delete '{files[0].Name}'?" : $"Delete {files.Count} items?";

            if (MessageBox.Show(msg, "Confirm Delete", MessageBoxButton.YesNo, MessageBoxImage.Warning) != MessageBoxResult.Yes)
                return;

            foreach (var file in files)
            {
                try
                {
                    if (file.IsDir)
                        await _ftp.DeleteDirectory(file.Path);
                    else
                        await _ftp.DeleteFile(file.Path);
                }
                catch (Exception ex)
                {
                    Status($"Error deleting {file.Name}: {ex.Message}");
                }
            }

            await LoadRemoteFilesAsync(_remotePath);
            Status($"Deleted {files.Count} item(s)");
        }

        private async void RemoteRename()
        {
            if (lstRemote.SelectedItem is not FileItem file || !_connected) return;

            var dialog = new InputDialog("Rename", "Enter new name:", file.Name);
            if (dialog.ShowDialog() != true) return;

            try
            {
                string newPath = $"{_remotePath}/{dialog.ResponseText}";

                if (file.IsDir)
                    await _ftp.MoveDirectory(file.Path, newPath);
                else
                    await _ftp.MoveFile(file.Path, newPath, FtpRemoteExists.Overwrite);

                await LoadRemoteFilesAsync(_remotePath);
                Status("Renamed successfully");
            }
            catch (Exception ex)
            {
                Status($"Error: {ex.Message}");
            }
        }

        private async void RemoteNewFolder()
        {
            var dialog = new InputDialog("New Folder", "Enter folder name:", "New Folder");
            if (dialog.ShowDialog() != true) return;

            try
            {
                string newPath = $"{_remotePath}/{dialog.ResponseText}";
                await _ftp.CreateDirectory(newPath);
                await LoadRemoteFilesAsync(_remotePath);
                Status("Folder created");
            }
            catch (Exception ex)
            {
                Status($"Error: {ex.Message}");
            }
        }

        private async Task CopyDirectoryRemote(string sourceDir, string destDir)
        {
            await _ftp.CreateDirectory(destDir);

            var items = await _ftp.GetListing(sourceDir);
            foreach (var item in items)
            {
                string destItem = $"{destDir}/{item.Name}";
                if (item.Type == FtpObjectType.Directory)
                {
                    await CopyDirectoryRemote(item.FullName, destItem);
                }
                else
                {
                    string tempFile = Path.GetTempFileName();
                    try
                    {
                        await _ftp.DownloadFile(tempFile, item.FullName, FtpLocalExists.Overwrite);
                        await _ftp.UploadFile(tempFile, destItem, FtpRemoteExists.Overwrite);
                    }
                    finally
                    {
                        try { File.Delete(tempFile); } catch { }
                    }
                }
            }
        }

        private async Task<string> GetUniqueRemotePath(string path)
        {
            try
            {
                if (!await _ftp.FileExists(path) && !await _ftp.DirectoryExists(path))
                    return path;
            }
            catch { return path; }

            string dir = path.Substring(0, path.LastIndexOf('/'));
            string name = Path.GetFileNameWithoutExtension(path);
            string ext = Path.GetExtension(path);
            int counter = 1;

            string newPath;
            do
            {
                newPath = $"{dir}/{name} ({counter}){ext}";
                counter++;
                try
                {
                    if (!await _ftp.FileExists(newPath) && !await _ftp.DirectoryExists(newPath))
                        break;
                }
                catch { break; }
            } while (counter < 1000);

            return newPath;
        }
        #endregion

        private void LoadDrives()
        {
            cmbDrives.Items.Clear();
            foreach (var drive in DriveInfo.GetDrives().Where(d => d.IsReady))
            {
                cmbDrives.Items.Add($"{drive.Name} ({drive.VolumeLabel})");
            }
            if (cmbDrives.Items.Count > 0)
            {
                cmbDrives.SelectedIndex = 0;
            }
        }

        #region Window
        private void TitleBar_Drag(object s, MouseButtonEventArgs e) { if (e.ClickCount == 2) Max_Click(s, null); else DragMove(); }
        private void Min_Click(object s, RoutedEventArgs e) => WindowState = WindowState.Minimized;
        private void Max_Click(object s, RoutedEventArgs e) => WindowState = WindowState == WindowState.Maximized ? WindowState.Normal : WindowState.Maximized;
        private void Close_Click(object s, RoutedEventArgs e) { Disconnect(); Close(); }
        #endregion

        #region Navigation
        private void Nav_Click(object s, RoutedEventArgs e)
        {
            if (s is not Button btn) return;
            foreach (var b in new[] { navDash, navGames, navFiles, navPKG, navWebMAN, navTweaks, navDownloads }) b.Tag = null;
            btn.Tag = "Active";
            pageDash.Visibility = pageGames.Visibility = pageFiles.Visibility = pagePKG.Visibility = pageWebMAN.Visibility = pageTweaks.Visibility = pageDownloads.Visibility = Visibility.Collapsed;

            if (btn == navDash) pageDash.Visibility = Visibility.Visible;
            else if (btn == navGames) pageGames.Visibility = Visibility.Visible;
            else if (btn == navFiles)
            {
                pageFiles.Visibility = Visibility.Visible;
                if (LocalFiles.Count == 0 && cmbDrives.SelectedItem != null)
                    LoadLocalFiles(_localPath);
                if (_connected && RemoteFiles.Count == 0)
                    _ = LoadRemoteFilesAsync(_remotePath);
            }
            else if (btn == navPKG) pagePKG.Visibility = Visibility.Visible;
            else if (btn == navWebMAN) pageWebMAN.Visibility = Visibility.Visible;
            else if (btn == navTweaks) pageTweaks.Visibility = Visibility.Visible;
            else if (btn == navDownloads) pageDownloads.Visibility = Visibility.Visible;
        }
        #endregion

        #region Connection - FIXED
        private async void Connect_Click(object sender, RoutedEventArgs e)
        {
            if (_connected) { Disconnect(); return; }

            string ip = txtIP.Text.Trim();
            if (string.IsNullOrEmpty(ip)) { MessageBox.Show("Enter PS3 IP address!"); return; }

            Status($"Connecting to {ip}...");
            btnConnect.IsEnabled = false;
            txtStatus.Text = "Connecting...";
            statusDot.Fill = Brushes.Orange;

            try
            {
                _ftp = new AsyncFtpClient();
                _ftp.Host = ip;
                _ftp.Port = 21;
                _ftp.Credentials = new NetworkCredential("anonymous", "");

                // Optimized settings for faster connection
                _ftp.Config.EncryptionMode = FtpEncryptionMode.None;
                _ftp.Config.DataConnectionType = FtpDataConnectionType.PASV;
                _ftp.Config.ConnectTimeout = 8000;
                _ftp.Config.DataConnectionConnectTimeout = 8000;
                _ftp.Config.DataConnectionReadTimeout = 30000;
                _ftp.Config.ReadTimeout = 15000;
                _ftp.Config.SendHost = false;
                _ftp.Config.PassiveBlockedPorts = null;
                _ftp.Config.PassiveMaxAttempts = 3;
                _ftp.Config.RetryAttempts = 2;
                _ftp.Config.SocketKeepAlive = false;

                Status("Connecting via FTP...");

                // Use Task.Run to prevent UI blocking
                await Task.Run(async () => await _ftp.Connect());

                if (!_ftp.IsConnected) throw new Exception("Connection failed");

                _connected = true;
                txtStatus.Text = "Connected!";
                statusDot.Fill = (Brush)FindResource("Green");
                btnConnect.Content = "⚡ DISCONNECT";
                txtPS3Status.Text = " (Connected)";
                txtPS3Status.Foreground = (Brush)FindResource("Green");

                // Run initialization in background
                _ = Task.Run(async () =>
                {
                    try
                    {
                        await DetectFirmware();
                        await ScanGamesAsync();
                        await Dispatcher.InvokeAsync(async () =>
                        {
                            if (pageFiles.Visibility == Visibility.Visible)
                                await LoadRemoteFilesAsync(_remotePath);
                            await RefreshTemps();
                            Status($"Ready - {AllGames.Count} games found");
                        });
                    }
                    catch (Exception ex)
                    {
                        await Dispatcher.InvokeAsync(() => Status($"Init error: {ex.Message}"));
                    }
                });
            }
            catch (Exception ex)
            {
                txtStatus.Text = "Failed";
                statusDot.Fill = (Brush)FindResource("Pink");
                txtPS3Status.Text = " (Not connected)";
                txtPS3Status.Foreground = (Brush)FindResource("TextD");

                string msg = ex.Message.Contains("EPSV") || ex.Message.Contains("PASV")
                    ? $"FTP passive mode error:\n{ex.Message}"
                    : ex.Message.Contains("denied") || ex.Message.Contains("blocked")
                    ? "Windows Firewall blocking.\nRun as Admin or add Firewall exception."
                    : $"Connection failed:\n{ex.Message}\n\nMake sure PS3 is on and FTP enabled.";

                MessageBox.Show(msg, "Error", MessageBoxButton.OK, MessageBoxImage.Error);
                Disconnect();
            }
            finally { btnConnect.IsEnabled = true; }
        }

        private void Disconnect()
        {
            _connected = false;
            if (_ftp != null)
            {
                try { if (_ftp.IsConnected) _ftp.Disconnect(); } catch { }
                _ftp.Dispose();
                _ftp = null;
            }

            txtStatus.Text = "Disconnected";
            statusDot.Fill = (Brush)FindResource("TextD");
            btnConnect.Content = "⚡ CONNECT";
            txtFW.Text = "NOT CONNECTED";
            txtFW.Foreground = (Brush)FindResource("TextD");
            badgeFW.Background = (Brush)FindResource("BgHover");
            txtPS3Status.Text = " (Not connected)";
            txtPS3Status.Foreground = (Brush)FindResource("TextD");

            AllGames.Clear();
            FilteredGames.Clear();
            RemoteFiles.Clear();
            txtGameCount.Text = txtFree.Text = txtCPU.Text = txtRSX.Text = txtFan.Text = "--";
            Status("Disconnected");
        }

        private async Task DetectFirmware()
        {
            try
            {
                bool cfw = await _ftp.DirectoryExists("/dev_blind");
                bool hen = await _ftp.FileExists("/dev_hdd0/hen/hen.self");

                string type = cfw ? "CFW" : hen ? "HFW+HEN" : "HFW";
                var color = cfw ? (Brush)FindResource("Green") : hen ? (Brush)FindResource("Orange") : Brushes.Yellow;

                await Dispatcher.InvokeAsync(() =>
                {
                    txtFW.Text = type;
                    txtFW.Foreground = Brushes.Black;
                    badgeFW.Background = color;
                });
            }
            catch { }
        }
        #endregion
        #region Missing Game Methods
        private void Search_Changed(object s, TextChangedEventArgs e)
        {
            var q = txtSearch.Text.ToLower();
            FilteredGames.Clear();
            foreach (var g in AllGames)
                if (string.IsNullOrEmpty(q) || g.Title.ToLower().Contains(q) || g.TitleID.ToLower().Contains(q))
                    FilteredGames.Add(g);
        }

        private void RefreshGames_Click(object s, RoutedEventArgs e)
        {
            if (_connected)
                _ = ScanGamesAsync();
            else
                MessageBox.Show("Connect first!");
        }

        private async void MountGame_Click(object s, RoutedEventArgs e)
        {
            if (s is not Button btn || btn.Tag is not GameInfo g) return;
            try
            {
                Status($"Mounting {g.Title}...");
                await _http.GetStringAsync($"http://{txtIP.Text}/mount.ps3{g.Path}");
                Status($"Mounted: {g.Title}");
                try { await _http.GetStringAsync($"http://{txtIP.Text}/popup.ps3?Mounted:{Uri.EscapeDataString(g.Title)}"); } catch { }
            }
            catch (Exception ex) { Status($"Mount failed: {ex.Message}"); }
        }

        private async void DeleteGame_Click(object s, RoutedEventArgs e)
        {
            if (s is not Button btn || btn.Tag is not GameInfo g) return;
            if (MessageBox.Show($"Delete '{g.Title}'?", "Confirm", MessageBoxButton.YesNo, MessageBoxImage.Warning) != MessageBoxResult.Yes) return;
            try
            {
                Status($"Deleting {g.Title}...");
                if (g.IsISO)
                    await _ftp.DeleteFile(g.Path);
                else
                    await _ftp.DeleteDirectory(g.Path);
                AllGames.Remove(g);
                FilteredGames.Remove(g);
                txtGameCount.Text = AllGames.Count.ToString();
                Status($"Deleted: {g.Title}");
            }
            catch (Exception ex) { Status($"Delete failed: {ex.Message}"); }
        }

        private string GetGameType(string f) =>
            f.Contains("PS3ISO") ? "PS3 ISO" :
            f.Contains("PS2ISO") ? "PS2 ISO" :
            f.Contains("PSXISO") ? "PSX" :
            f.Contains("PSPISO") ? "PSP" :
            f.Contains("/game") ? "PSN" :
            f.Contains("usb") ? "USB" : "Folder";

        private string GetGameIcon(string f) =>
            f.Contains("PS3ISO") ? "💿" :
            f.Contains("PS2ISO") ? "📀" :
            f.Contains("PSXISO") ? "💾" :
            f.Contains("PSPISO") ? "📱" :
            f.Contains("/game") ? "🎮" :
            f.Contains("usb") ? "🔌" : "📁";

        private string CleanTitle(string n)
        {
            if (n.EndsWith(".iso", StringComparison.OrdinalIgnoreCase) || n.EndsWith(".bin", StringComparison.OrdinalIgnoreCase))
                n = Path.GetFileNameWithoutExtension(n);
            n = Regex.Replace(n, @"[\[\(].*?[\]\)]", "").Replace("_", " ").Trim();
            return n.Length > 50 ? n.Substring(0, 47) + "..." : n;
        }
        #endregion

        #region Local File Manager - SORTED BY MOST RECENT
        private void LocalDrive_Changed(object s, SelectionChangedEventArgs e)
        {
            if (cmbDrives.SelectedItem == null) return;
            string drive = cmbDrives.SelectedItem.ToString().Split(' ')[0];
            _localPath = drive;
            LoadLocalFiles(_localPath);
        }

        private void LoadLocalFiles(string path)
        {
            if (string.IsNullOrEmpty(path)) return;

            LocalFiles.Clear();
            _localPath = path;

            try
            {
                var dir = new DirectoryInfo(path);
                var items = new List<FileItem>();

                var parent = Directory.GetParent(path);
                if (parent != null)
                {
                    items.Add(new FileItem
                    {
                        Name = "..",
                        Path = parent.FullName,
                        IsDir = true,
                        Size = "",
                        Icon = "⬆",
                        ModifiedTime = "",
                        LastModified = DateTime.MaxValue
                    });
                }

                foreach (var d in dir.GetDirectories())
                {
                    try
                    {
                        items.Add(new FileItem
                        {
                            Name = d.Name,
                            Path = d.FullName,
                            IsDir = true,
                            Size = "<DIR>",
                            Icon = "📁",
                            ModifiedTime = d.LastWriteTime.ToString("MM/dd HH:mm"),
                            LastModified = d.LastWriteTime
                        });
                    }
                    catch { }
                }

                foreach (var f in dir.GetFiles())
                {
                    try
                    {
                        items.Add(new FileItem
                        {
                            Name = f.Name,
                            Path = f.FullName,
                            IsDir = false,
                            Size = FormatSize(f.Length),
                            Icon = GetFileIcon(f.Name),
                            ModifiedTime = f.LastWriteTime.ToString("MM/dd HH:mm"),
                            LastModified = f.LastWriteTime
                        });
                    }
                    catch { }
                }

                var sortedItems = items
                    .OrderBy(x => x.Name == ".." ? 0 : 1)
                    .ThenByDescending(x => x.LastModified)
                    .ToList();

                foreach (var item in sortedItems)
                {
                    LocalFiles.Add(item);
                }
            }
            catch (Exception ex)
            {
                Status($"Error loading local files: {ex.Message}");
            }
        }

        private void LocalUp_Click(object s, RoutedEventArgs e)
        {
            if (string.IsNullOrEmpty(_localPath)) return;
            var parent = Directory.GetParent(_localPath);
            if (parent != null)
            {
                _localPath = parent.FullName;
                LoadLocalFiles(_localPath);
            }
        }

        private void LocalRefresh_Click(object s, RoutedEventArgs e) => LoadLocalFiles(_localPath);

        private void Local_DblClick(object s, MouseButtonEventArgs e)
        {
            if (lstLocal.SelectedItem is FileItem f && f.IsDir)
            {
                _localPath = f.Path;
                LoadLocalFiles(_localPath);
            }
        }
        #endregion

        #region Remote File Manager
        private async Task LoadRemoteFilesAsync(string path)
        {
            if (!_connected || _ftp == null) return;

            Status($"Loading {path}...");
            _remotePath = path;
            Dispatcher.Invoke(() => { txtRemotePath.Text = path; RemoteFiles.Clear(); });

            try
            {
                var items = await _ftp.GetListing(path);
                var sorted = items.OrderByDescending(x => x.Type == FtpObjectType.Directory).ThenBy(x => x.Name).ToList();

                foreach (var item in sorted)
                {
                    bool isDir = item.Type == FtpObjectType.Directory;
                    Dispatcher.Invoke(() => RemoteFiles.Add(new FileItem
                    {
                        Name = item.Name,
                        Path = item.FullName,
                        IsDir = isDir,
                        Size = isDir ? "<DIR>" : FormatSize(item.Size),
                        Icon = isDir ? "📁" : GetFileIcon(item.Name)
                    }));
                }
                Status($"Loaded {RemoteFiles.Count} items");
            }
            catch (Exception ex) { Status($"Error: {ex.Message}"); }
        }

        private void RemoteUp_Click(object s, RoutedEventArgs e)
        {
            if (_remotePath == "/") return;
            string parent = Path.GetDirectoryName(_remotePath)?.Replace("\\", "/") ?? "/";
            if (string.IsNullOrEmpty(parent)) parent = "/";
            _ = LoadRemoteFilesAsync(parent);
        }

        private void RemoteRefresh_Click(object s, RoutedEventArgs e) => _ = LoadRemoteFilesAsync(_remotePath);
        private void RemotePath_KeyDown(object s, KeyEventArgs e) { if (e.Key == Key.Enter) _ = LoadRemoteFilesAsync(txtRemotePath.Text); }
        private void QuickNav(object s, RoutedEventArgs e) { if (s is Button btn && btn.Tag is string path) _ = LoadRemoteFilesAsync(path); }

        private void Remote_DblClick(object s, MouseButtonEventArgs e)
        {
            if (lstRemote.SelectedItem is FileItem f && f.IsDir)
                _ = LoadRemoteFilesAsync(f.Path);
        }
        #endregion

        #region Drag & Drop
        private void Local_PreviewMouseDown(object s, MouseButtonEventArgs e)
        {
            _dragStartPoint = e.GetPosition(null);
        }

        private void Local_PreviewMouseMove(object s, MouseEventArgs e)
        {
            if (e.LeftButton != MouseButtonState.Pressed) return;

            Point pos = e.GetPosition(null);
            Vector diff = _dragStartPoint - pos;

            if (Math.Abs(diff.X) > SystemParameters.MinimumHorizontalDragDistance ||
                Math.Abs(diff.Y) > SystemParameters.MinimumVerticalDragDistance)
            {
                if (lstLocal.SelectedItems.Count > 0)
                {
                    var files = lstLocal.SelectedItems.Cast<FileItem>().ToList();
                    var data = new DataObject("LocalFiles", files);
                    DragDrop.DoDragDrop(lstLocal, data, DragDropEffects.Copy);
                }
            }
        }

        private void Remote_PreviewMouseDown(object s, MouseButtonEventArgs e)
        {
            _dragStartPoint = e.GetPosition(null);
        }

        private void Remote_PreviewMouseMove(object s, MouseEventArgs e)
        {
            if (e.LeftButton != MouseButtonState.Pressed || !_connected) return;

            Point pos = e.GetPosition(null);
            Vector diff = _dragStartPoint - pos;

            if (Math.Abs(diff.X) > SystemParameters.MinimumHorizontalDragDistance ||
                Math.Abs(diff.Y) > SystemParameters.MinimumVerticalDragDistance)
            {
                if (lstRemote.SelectedItems.Count > 0)
                {
                    var files = lstRemote.SelectedItems.Cast<FileItem>().ToList();
                    var data = new DataObject("RemoteFiles", files);
                    DragDrop.DoDragDrop(lstRemote, data, DragDropEffects.Copy);
                }
            }
        }

        private async void Local_Drop(object s, DragEventArgs e)
        {
            if (e.Data.GetDataPresent("RemoteFiles"))
            {
                var files = e.Data.GetData("RemoteFiles") as List<FileItem>;
                if (files != null && _connected)
                {
                    await DownloadFilesAsync(files);
                }
            }
            else if (e.Data.GetDataPresent(DataFormats.FileDrop))
            {
                LoadLocalFiles(_localPath);
            }
        }

        private async void Remote_Drop(object s, DragEventArgs e)
        {
            if (!_connected) return;

            if (e.Data.GetDataPresent("LocalFiles"))
            {
                var files = e.Data.GetData("LocalFiles") as List<FileItem>;
                if (files != null)
                {
                    await UploadFilesAsync(files);
                }
            }
            else if (e.Data.GetDataPresent(DataFormats.FileDrop))
            {
                var paths = e.Data.GetData(DataFormats.FileDrop) as string[];
                if (paths != null)
                {
                    var files = paths.Select(p => new FileItem
                    {
                        Name = Path.GetFileName(p),
                        Path = p,
                        IsDir = Directory.Exists(p)
                    }).ToList();
                    await UploadFilesAsync(files);
                }
            }
        }

        private async Task UploadFilesAsync(List<FileItem> files)
        {
            _transferCts = new CancellationTokenSource();
            _transferStopwatch.Restart();

            Dispatcher.Invoke(() =>
            {
                transferPanel.Visibility = Visibility.Visible;
                btnCancelTransfer.Visibility = Visibility.Visible;
                transferProgress.Value = 0;
                txtTransferDirection.Text = "⬆ UPLOADING";
                txtTransferDirection.Foreground = (Brush)FindResource("Cyan");
                txtTransferSpeed.Text = "";
                txtTransferBytes.Text = "";
                txtTransferPercent.Text = "0%";
                txtTransferETA.Text = "";
            });

            int total = files.Count;
            int done = 0;

            foreach (var file in files)
            {
                if (_transferCts.IsCancellationRequested) break;

                try
                {
                    string remoteDest = $"{_remotePath}/{file.Name}";
                    long fileSize = 0;
                    if (!file.IsDir && File.Exists(file.Path))
                        fileSize = new FileInfo(file.Path).Length;

                    Dispatcher.Invoke(() =>
                    {
                        txtTransferFileName.Text = file.Name;
                        txtTransferStatus.Text = $"File {done + 1} of {total}";
                        transferProgress.Value = 0;
                        txtTransferPercent.Text = "0%";
                        txtTransferSpeed.Text = "";
                        txtTransferBytes.Text = fileSize > 0 ? $"0 B / {FormatSize(fileSize)}" : "";
                        txtTransferETA.Text = "";
                    });
                    Status($"Uploading {file.Name}...");

                    _transferSmoothSpeed = 0;
                    _transferLastUpdate = DateTime.Now;

                    if (file.IsDir)
                    {
                        await _ftp.UploadDirectory(file.Path, remoteDest, FtpFolderSyncMode.Update,
                            token: _transferCts.Token);
                    }
                    else
                    {
                        var progress = new Progress<FtpProgress>(p =>
                        {
                            UpdateTransferProgress(p, fileSize);
                        });
                        await _ftp.UploadFile(file.Path, remoteDest, FtpRemoteExists.Overwrite,
                            createRemoteDir: true, progress: progress, token: _transferCts.Token);
                    }

                    done++;
                    Dispatcher.Invoke(() =>
                    {
                        transferProgress.Value = 100;
                        txtTransferPercent.Text = "100%";
                        txtTransferETA.Text = "";
                    });
                }
                catch (OperationCanceledException)
                {
                    Status("Upload cancelled");
                    break;
                }
                catch (Exception ex)
                {
                    Status($"Upload error: {ex.Message}");
                }
            }

            _transferStopwatch.Stop();
            double avgSpeed = _transferStopwatch.Elapsed.TotalSeconds > 0
                ? files.Where(f => !f.IsDir && File.Exists(f.Path)).Sum(f => new FileInfo(f.Path).Length) / _transferStopwatch.Elapsed.TotalSeconds
                : 0;

            Dispatcher.Invoke(() =>
            {
                txtTransferFileName.Text = "";
                txtTransferSpeed.Text = "";
                txtTransferETA.Text = "";
                txtTransferBytes.Text = "";
                txtTransferPercent.Text = "";
                btnCancelTransfer.Visibility = Visibility.Collapsed;

                if (_transferCts.IsCancellationRequested)
                {
                    txtTransferStatus.Text = $"Upload cancelled — {done}/{total} file(s)";
                    transferProgress.Foreground = (Brush)FindResource("Pink");
                }
                else
                {
                    transferProgress.Value = 100;
                    transferProgress.Foreground = (Brush)FindResource("Green");
                    txtTransferStatus.Text = $"✓ Upload complete: {done} file(s) in {_transferStopwatch.Elapsed:mm\\:ss} @ {Spd(avgSpeed)}";
                }
            });
            Status(_transferCts.IsCancellationRequested ? "Upload cancelled" : $"Uploaded {done} file(s)");

            // Auto-hide after 4 seconds and reset color
            _ = Task.Delay(4000).ContinueWith(_ =>
                Dispatcher.Invoke(() =>
                {
                    if (btnCancelTransfer.Visibility == Visibility.Collapsed)
                    {
                        transferPanel.Visibility = Visibility.Collapsed;
                        transferProgress.Foreground = (Brush)FindResource("Cyan");
                    }
                }));

            await LoadRemoteFilesAsync(_remotePath);
        }

        private async Task DownloadFilesAsync(List<FileItem> files)
        {
            _transferCts = new CancellationTokenSource();
            _transferStopwatch.Restart();

            Dispatcher.Invoke(() =>
            {
                transferPanel.Visibility = Visibility.Visible;
                btnCancelTransfer.Visibility = Visibility.Visible;
                transferProgress.Value = 0;
                transferProgress.Foreground = (Brush)FindResource("Cyan");
                txtTransferDirection.Text = "⬇ DOWNLOADING";
                txtTransferDirection.Foreground = (Brush)FindResource("Green");
                txtTransferSpeed.Text = "";
                txtTransferBytes.Text = "";
                txtTransferPercent.Text = "0%";
                txtTransferETA.Text = "";
            });

            int total = files.Count;
            int done = 0;
            long totalBytesAllFiles = 0;

            foreach (var file in files)
            {
                if (_transferCts.IsCancellationRequested) break;

                try
                {
                    string localDest = Path.Combine(_localPath, file.Name);

                    // Get actual file size from FTP
                    long fileSize = 0;
                    if (!file.IsDir)
                    {
                        try { fileSize = await _ftp.GetFileSize(file.Path); }
                        catch { }
                    }

                    Dispatcher.Invoke(() =>
                    {
                        txtTransferFileName.Text = file.Name;
                        txtTransferStatus.Text = $"File {done + 1} of {total}";
                        transferProgress.Value = 0;
                        txtTransferPercent.Text = "0%";
                        txtTransferSpeed.Text = "";
                        txtTransferBytes.Text = fileSize > 0 ? $"0 B / {FormatSize(fileSize)}" : "";
                        txtTransferETA.Text = "";
                    });
                    Status($"Downloading {file.Name}...");

                    _transferSmoothSpeed = 0;
                    _transferLastUpdate = DateTime.Now;

                    if (file.IsDir)
                    {
                        await _ftp.DownloadDirectory(localDest, file.Path, FtpFolderSyncMode.Update,
                            token: _transferCts.Token);
                    }
                    else
                    {
                        var progress = new Progress<FtpProgress>(p =>
                        {
                            UpdateTransferProgress(p, fileSize);
                        });
                        await _ftp.DownloadFile(localDest, file.Path, FtpLocalExists.Overwrite,
                            FtpVerify.None, progress, _transferCts.Token);
                    }

                    done++;
                    totalBytesAllFiles += fileSize;
                    Dispatcher.Invoke(() =>
                    {
                        transferProgress.Value = 100;
                        txtTransferPercent.Text = "100%";
                        txtTransferETA.Text = "";
                    });
                }
                catch (OperationCanceledException)
                {
                    Status("Download cancelled");
                    break;
                }
                catch (Exception ex)
                {
                    Status($"Download error: {ex.Message}");
                }
            }

            _transferStopwatch.Stop();
            double avgSpeed = _transferStopwatch.Elapsed.TotalSeconds > 0 && totalBytesAllFiles > 0
                ? totalBytesAllFiles / _transferStopwatch.Elapsed.TotalSeconds
                : 0;

            Dispatcher.Invoke(() =>
            {
                txtTransferFileName.Text = "";
                txtTransferSpeed.Text = "";
                txtTransferETA.Text = "";
                txtTransferBytes.Text = "";
                txtTransferPercent.Text = "";
                btnCancelTransfer.Visibility = Visibility.Collapsed;

                if (_transferCts.IsCancellationRequested)
                {
                    txtTransferStatus.Text = $"Download cancelled — {done}/{total} file(s)";
                    transferProgress.Foreground = (Brush)FindResource("Pink");
                }
                else
                {
                    transferProgress.Value = 100;
                    transferProgress.Foreground = (Brush)FindResource("Green");
                    string speedInfo = avgSpeed > 0 ? $" @ {Spd(avgSpeed)}" : "";
                    txtTransferStatus.Text = $"✓ Download complete: {done} file(s) in {_transferStopwatch.Elapsed:mm\\:ss}{speedInfo}";
                }
            });
            Status(_transferCts.IsCancellationRequested ? "Download cancelled" : $"Downloaded {done} file(s)");

            // Auto-hide after 4 seconds and reset color
            _ = Task.Delay(4000).ContinueWith(_ =>
                Dispatcher.Invoke(() =>
                {
                    if (btnCancelTransfer.Visibility == Visibility.Collapsed)
                    {
                        transferPanel.Visibility = Visibility.Collapsed;
                        transferProgress.Foreground = (Brush)FindResource("Cyan");
                    }
                }));

            LoadLocalFiles(_localPath);
        }

        private async void TransferToPS3_Click(object s, RoutedEventArgs e)
        {
            if (!_connected || lstLocal.SelectedItems.Count == 0) return;
            var files = lstLocal.SelectedItems.Cast<FileItem>().ToList();
            await UploadFilesAsync(files);
        }

        private async void TransferToPC_Click(object s, RoutedEventArgs e)
        {
            if (!_connected || lstRemote.SelectedItems.Count == 0) return;
            var files = lstRemote.SelectedItems.Cast<FileItem>().ToList();
            await DownloadFilesAsync(files);
        }

        private void CancelTransfer_Click(object s, RoutedEventArgs e)
        {
            _transferCts?.Cancel();
            Dispatcher.Invoke(() =>
            {
                btnCancelTransfer.Visibility = Visibility.Collapsed;
                txtTransferStatus.Text = "Cancelling...";
            });
        }

        /// <summary>
        /// Handles FtpProgress callbacks from FluentFTP upload/download.
        /// Updates the transfer panel with speed, bytes, percentage, and ETA.
        /// </summary>
        private void UpdateTransferProgress(FtpProgress p, long totalSize)
        {
            var now = DateTime.Now;

            // Throttle UI updates to every 200ms
            if ((now - _transferLastUpdate).TotalMilliseconds < 200 && p.Progress < 100)
                return;

            double pct = p.Progress;
            long transferred = p.TransferredBytes;
            double speed = p.TransferSpeed;

            // Smooth the speed reading (exponential moving average)
            if (_transferSmoothSpeed < 100)
                _transferSmoothSpeed = speed;
            else
                _transferSmoothSpeed = _transferSmoothSpeed * 0.7 + speed * 0.3;

            // Calculate ETA
            string eta = "";
            if (_transferSmoothSpeed > 100 && totalSize > 0 && transferred < totalSize)
            {
                double remaining = (totalSize - transferred) / _transferSmoothSpeed;
                eta = remaining < 60 ? $"~{remaining:F0}s left" :
                      remaining < 3600 ? $"~{remaining / 60:F1}m left" :
                      $"~{remaining / 3600:F1}h left";
            }
            else if (p.ETA != TimeSpan.Zero && p.ETA.TotalSeconds > 0)
            {
                var r = p.ETA.TotalSeconds;
                eta = r < 60 ? $"~{r:F0}s left" :
                      r < 3600 ? $"~{r / 60:F1}m left" :
                      $"~{r / 3600:F1}h left";
            }

            string speedText = _transferSmoothSpeed > 0 ? Spd(_transferSmoothSpeed) : "";
            string bytesText = totalSize > 0
                ? $"{FormatSize(transferred)} / {FormatSize(totalSize)}"
                : FormatSize(transferred);

            _transferLastUpdate = now;

            Dispatcher.BeginInvoke(() =>
            {
                transferProgress.Value = Math.Min(pct, 100);
                txtTransferPercent.Text = $"{pct:F1}%";
                txtTransferSpeed.Text = speedText;
                txtTransferBytes.Text = bytesText;
                txtTransferETA.Text = eta;
            });
        }
        #endregion

        #region Games - FIXED
        private async Task ScanGamesAsync()
        {
            if (!_connected || _ftp == null) return;

            await Dispatcher.InvokeAsync(() =>
            {
                AllGames.Clear();
                FilteredGames.Clear();
            });

            int total = 0;

            foreach (var folder in _gameFolders)
            {
                try
                {
                    await Dispatcher.InvokeAsync(() => Status($"Checking {folder}..."));

                    bool exists = await _ftp.DirectoryExists(folder);
                    if (!exists) continue;

                    await Dispatcher.InvokeAsync(() => Status($"Scanning {folder}..."));
                    var items = await _ftp.GetListing(folder);

                    foreach (var item in items)
                    {
                        bool isDir = item.Type == FtpObjectType.Directory;
                        bool isISO = item.Name.EndsWith(".iso", StringComparison.OrdinalIgnoreCase) ||
                                     item.Name.EndsWith(".bin", StringComparison.OrdinalIgnoreCase);

                        if (isDir || isISO)
                        {
                            var game = new GameInfo
                            {
                                TitleID = item.Name,
                                Title = CleanTitle(item.Name),
                                Path = item.FullName,
                                Type = GetGameType(folder),
                                Icon = GetGameIcon(folder),
                                IsISO = isISO
                            };

                            await Dispatcher.InvokeAsync(() =>
                            {
                                AllGames.Add(game);
                                FilteredGames.Add(game);
                            });
                            total++;
                        }
                    }
                }
                catch (Exception ex)
                {
                    Debug.WriteLine($"Error scanning {folder}: {ex.Message}");
                }
            }

            await Dispatcher.InvokeAsync(() => txtGameCount.Text = total.ToString());
            await Dispatcher.InvokeAsync(() => Status($"Found {total} games!"));
        }
        #endregion

        #region PKG
        private void AddPKG_Click(object s, RoutedEventArgs e)
        {
            var dlg = new OpenFileDialog { Filter = "PKG|*.pkg", Multiselect = true };
            if (dlg.ShowDialog() != true) return;
            foreach (var file in dlg.FileNames)
            {
                var fi = new System.IO.FileInfo(file);
                PkgsList.Add(new PkgInfo { Name = fi.Name, Path = file, Size = FormatSize(fi.Length), Status = "Queued" });
            }
            txtPKGStatus.Text = $"{PkgsList.Count} file(s)";
        }

        private void ClearPKG_Click(object s, RoutedEventArgs e) { PkgsList.Clear(); txtPKGStatus.Text = "Ready"; }

        private async void InstallPKG_Click(object s, RoutedEventArgs e)
        {
            if (!_connected || PkgsList.Count == 0) return;
            foreach (var pkg in PkgsList)
            {
                try
                {
                    pkg.Status = "Uploading...";
                    var remote = $"/dev_hdd0/packages/{pkg.Name}";
                    await _ftp.UploadFile(pkg.Path, remote, FtpRemoteExists.Overwrite);
                    pkg.Status = "Installing...";
                    await _http.GetStringAsync($"http://{txtIP.Text}/install.ps3{remote}");
                    pkg.Status = "Done ✓";
                }
                catch { pkg.Status = "Error"; }
            }
            txtPKGStatus.Text = "Complete";
        }
        #endregion

        #region WebMAN
        private async Task WebCmd(string cmd, string msg) { if (!_connected) return; try { await _http.GetStringAsync($"http://{txtIP.Text}{cmd}"); Status(msg); } catch (Exception ex) { Status($"Failed: {ex.Message}"); } }
        private async void Restart_Click(object s, RoutedEventArgs e) => await WebCmd("/restart.ps3", "Restarting...");
        private async void Shutdown_Click(object s, RoutedEventArgs e) => await WebCmd("/shutdown.ps3", "Shutting down...");
        private async void SoftReboot_Click(object s, RoutedEventArgs e) => await WebCmd("/reboot.ps3?soft", "Soft rebooting...");
        private async void Screenshot_Click(object s, RoutedEventArgs e) => await WebCmd("/screenshot.ps3", "Screenshot!");
        private async void Eject_Click(object s, RoutedEventArgs e) => await WebCmd("/eject.ps3", "Ejected");
        private async void Beep_Click(object s, RoutedEventArgs e) => await WebCmd("/beep.ps3?1", "Beep!");
        private async void Unmount_Click(object s, RoutedEventArgs e) => await WebCmd("/mount.ps3/unmount", "Unmounted");
        private async void SetFan_Click(object s, RoutedEventArgs e) => await WebCmd($"/cpursx.ps3?fan={(int)sliderFan.Value}", $"Fan: {(int)sliderFan.Value}%");
        private async void AutoFan_Click(object s, RoutedEventArgs e) => await WebCmd("/cpursx.ps3?fan=0", "Fan: Auto");
        private async void SendPopup_Click(object s, RoutedEventArgs e) => await WebCmd($"/popup.ps3?{Uri.EscapeDataString(txtPopup.Text)}", "Sent!");
        private void OpenWebMAN_Click(object s, RoutedEventArgs e) => Process.Start(new ProcessStartInfo($"http://{txtIP.Text}") { UseShellExecute = true });

        private async void EnableSyscalls_Click(object s, RoutedEventArgs e) => await WebCmd("/syscall.ps3?enable", "Syscalls enabled");
        private async void DisableSyscalls_Click(object s, RoutedEventArgs e) => await WebCmd("/syscall.ps3?disable", "Syscalls disabled");
        private async void EnableHEN_Click(object s, RoutedEventArgs e) => await WebCmd("/hen.ps3?enable", "HEN enabled");
        private async void EnableCobra_Click(object s, RoutedEventArgs e) => await WebCmd("/cobra.ps3?enable", "Cobra enabled");
        private async void DisableCobra_Click(object s, RoutedEventArgs e) => await WebCmd("/cobra.ps3?disable", "Cobra disabled");
        #endregion

        #region System
        private async Task RefreshTemps()
        {
            if (!_connected) return;
            try
            {
                var resp = await _http.GetStringAsync($"http://{txtIP.Text}/cpursx.ps3");
                var cpu = Regex.Match(resp, @"CPU[:\s]*(\d+)", RegexOptions.IgnoreCase);
                var rsx = Regex.Match(resp, @"RSX[:\s]*(\d+)", RegexOptions.IgnoreCase);
                var fan = Regex.Match(resp, @"FAN[:\s]*(\d+)", RegexOptions.IgnoreCase);
                var free = Regex.Match(resp, @"(\d+(?:\.\d+)?)\s*GB\s*free", RegexOptions.IgnoreCase);

                Dispatcher.Invoke(() =>
                {
                    if (cpu.Success) txtCPU.Text = cpu.Groups[1].Value;
                    if (rsx.Success) txtRSX.Text = rsx.Groups[1].Value;
                    if (fan.Success) txtFan.Text = fan.Groups[1].Value;
                    if (free.Success) txtFree.Text = free.Groups[1].Value;
                });
            }
            catch { }
        }
        #endregion

        #region Helpers
        private void Status(string msg) => Dispatcher.Invoke(() => txtStatusBar.Text = msg);
        private static string FormatSize(long b) { string[] u = { "B", "KB", "MB", "GB", "TB" }; int i = 0; double s = b; while (s >= 1024 && i < u.Length - 1) { i++; s /= 1024; } return $"{s:0.##} {u[i]}"; }
        private string GetFileIcon(string n) { var e = Path.GetExtension(n).ToLower(); return e switch { ".pkg" => "📦", ".iso" or ".bin" => "💿", ".self" or ".sprx" => "⚙️", ".png" or ".jpg" => "🖼️", ".mp4" or ".mkv" => "🎬", ".txt" or ".log" => "📝", ".exe" => "⚙️", ".zip" or ".rar" or ".7z" => "📦", _ => "📄" }; }
        #endregion
    }

    #region Models
    public class GameInfo : INotifyPropertyChanged
    {
        public string TitleID { get; set; } = "";
        public string Title { get; set; } = "";
        public string Path { get; set; } = "";
        public string Type { get; set; } = "";
        public string Icon { get; set; } = "🎮";
        public bool IsISO { get; set; }
        public event PropertyChangedEventHandler PropertyChanged;
    }

    public class FileItem
    {
        public string Name { get; set; } = "";
        public string Path { get; set; } = "";
        public string Size { get; set; } = "";
        public string Icon { get; set; } = "📄";
        public bool IsDir { get; set; }
        public string ModifiedTime { get; set; } = "";
        public DateTime LastModified { get; set; }
    }

    public class PkgInfo : INotifyPropertyChanged
    {
        private string _status = "";
        public string Name { get; set; } = "";
        public string Path { get; set; } = "";
        public string Size { get; set; } = "";
        public string Status { get => _status; set { _status = value; PropertyChanged?.Invoke(this, new PropertyChangedEventArgs(nameof(Status))); } }
        public event PropertyChangedEventHandler PropertyChanged;
    }

    public class MyrientGame
    {
        public string Name { get; set; } = "";
        public string Platform { get; set; } = "";
        public string Region { get; set; } = "";
        public string DownloadUrl { get; set; } = "";
        public string FileName { get; set; } = "";
        public long Size { get; set; }
        public string SizeText { get; set; } = "";
    }

    public class DownloadTask : INotifyPropertyChanged
    {
        private double _progress;
        private string _status = "Queued";
        private long _downloadedBytes;

        public string Name { get; set; } = "";
        public string Platform { get; set; } = "";
        public string Url { get; set; } = "";
        public string LocalPath { get; set; } = "";
        public long? TotalBytes { get; set; }
        public long TotalSize { get; set; }
        public DateTime StartTime { get; set; }
        public string ErrorMessage { get; set; } = "";
        public CancellationTokenSource CancellationTokenSource { get; set; } = new CancellationTokenSource();

        public double Progress
        {
            get => _progress;
            set { _progress = value; N(nameof(Progress)); }
        }

        public string Status
        {
            get => _status;
            set { _status = value; N(nameof(Status)); }
        }

        public long DownloadedBytes
        {
            get => _downloadedBytes;
            set { _downloadedBytes = value; N(nameof(DownloadedBytes)); }
        }

        public event PropertyChangedEventHandler PropertyChanged;
        private void N(string p) => PropertyChanged?.Invoke(this, new PropertyChangedEventArgs(p));
    }

    public class DownloadSegment
    {
        public long Start { get; set; }
        public long End { get; set; }
        public long Downloaded { get; set; }
        public bool Started { get; set; }
        public bool Completed { get; set; }
        public long Remaining => End - Start - Downloaded + 1;
    }

    public class MyrientScraper
    {
        private static readonly HttpClient _http = new HttpClient { Timeout = TimeSpan.FromSeconds(30) };

        private static readonly Dictionary<string, string> _platformUrls = new()
        {
            ["PS1"] = "https://myrient.erista.me/files/Redump/Sony%20-%20PlayStation/",
            ["PS2"] = "https://myrient.erista.me/files/Redump/Sony%20-%20PlayStation%202/",
            ["PS3"] = "https://myrient.erista.me/files/Redump/Sony%20-%20PlayStation%203/"
        };

        static MyrientScraper()
        {
            _http.DefaultRequestHeaders.Add("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
            _http.DefaultRequestHeaders.Add("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8");
        }

        public async Task<List<MyrientGame>> SearchAsync(string query, string platform)
        {
            var results = new List<MyrientGame>();
            var platformsToSearch = platform == "All" ? _platformUrls.Keys.ToList() : new List<string> { platform };

            foreach (var plat in platformsToSearch)
            {
                try
                {
                    var games = await SearchPlatformAsync(query, plat);
                    results.AddRange(games);
                }
                catch (Exception ex)
                {
                    Debug.WriteLine($"Error searching {plat}: {ex.Message}");
                }
            }

            return results;
        }

        private async Task<List<MyrientGame>> SearchPlatformAsync(string query, string platform)
        {
            var results = new List<MyrientGame>();
            var url = _platformUrls[platform];

            try
            {
                Debug.WriteLine($"Fetching URL: {url}");
                var html = await _http.GetStringAsync(url);
                Debug.WriteLine($"HTML length: {html.Length}");

                // Parse nginx autoindex HTML format
                // Look for table rows with file links - nginx autoindex format
                // <tr><td><a href="filename">filename</a></td><td>date</td><td>size</td></tr>

                // Primary pattern for nginx autoindex
                var rowMatches = Regex.Matches(html, @"<tr[^>]*>.*?<td[^>]*>.*?<a\s+href=""([^""]+)""[^>]*>([^<]+)</a>.*?</td>.*?<td[^>]*>([^<]*)</td>.*?<td[^>]*>([^<]*)</td>.*?</tr>",
                    RegexOptions.Singleline | RegexOptions.IgnoreCase);

                Debug.WriteLine($"Found {rowMatches.Count} row matches with primary pattern");

                foreach (Match match in rowMatches)
                {
                    var href = match.Groups[1].Value;
                    var fileName = System.Net.WebUtility.HtmlDecode(match.Groups[2].Value.Trim());
                    var dateText = match.Groups[3].Value.Trim();
                    var sizeText = match.Groups[4].Value.Trim();

                    // Skip parent directory and non-file entries
                    if (href == "../" || href == "./" || href.StartsWith("?") || string.IsNullOrWhiteSpace(fileName))
                        continue;

                    // Skip directories (indicated by "-" in size column)
                    if (sizeText == "-" || string.IsNullOrEmpty(sizeText))
                        continue;

                    // Skip if not a game file (only .zip files for Redump)
                    var ext = Path.GetExtension(fileName).ToLower();
                    if (ext != ".zip")
                        continue;

                    // Check if matches search query
                    if (!fileName.Contains(query, StringComparison.OrdinalIgnoreCase))
                        continue;

                    var downloadUrl = url + href;

                    results.Add(new MyrientGame
                    {
                        Name = fileName,
                        Platform = platform,
                        FileName = fileName,
                        DownloadUrl = downloadUrl,
                        SizeText = sizeText,
                        Size = ParseSize(sizeText)
                    });

                    // Limit results per platform to avoid overwhelming the UI
                    if (results.Count >= 100)
                        break;
                }

                // If no results with primary pattern, try alternative parsing
                if (results.Count == 0)
                {
                    Debug.WriteLine("Trying alternative parsing...");
                    results = ParseAlternative(html, url, query, platform);
                }
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"Error in SearchPlatformAsync: {ex.Message}");
                Debug.WriteLine($"Stack trace: {ex.StackTrace}");
            }

            Debug.WriteLine($"Returning {results.Count} results for {platform}");
            return results;
        }

        private List<MyrientGame> ParseAlternative(string html, string url, string query, string platform)
        {
            var results = new List<MyrientGame>();

            // Alternative: Look for any anchor tags with .zip extension
            // Pattern: <a href="filename.zip">filename.zip</a>
            var matches = Regex.Matches(html, @"<a\s+href=""([^""]+\.zip)""[^>]*>([^<]+)</a>",
                RegexOptions.IgnoreCase | RegexOptions.Singleline);

            Debug.WriteLine($"Alternative pattern found {matches.Count} matches");

            foreach (Match match in matches)
            {
                var href = match.Groups[1].Value;
                var fileName = System.Net.WebUtility.HtmlDecode(match.Groups[2].Value.Trim());

                if (href == "../" || href == "./" || href.StartsWith("?"))
                    continue;

                if (!fileName.Contains(query, StringComparison.OrdinalIgnoreCase))
                    continue;

                var downloadUrl = url + href;

                results.Add(new MyrientGame
                {
                    Name = fileName,
                    Platform = platform,
                    FileName = fileName,
                    DownloadUrl = downloadUrl,
                    SizeText = "Unknown",
                    Size = 0
                });

                if (results.Count >= 100)
                    break;
            }

            return results;
        }

        private long ParseSize(string sizeText)
        {
            try
            {
                if (string.IsNullOrWhiteSpace(sizeText) || sizeText == "-")
                    return 0;

                // Handle formats like "1.2G", "500M", "100K" (nginx autoindex format)
                // Also handle "1.2 GiB", "500 MiB", etc.
                var match = Regex.Match(sizeText, @"([\d.]+)\s*([KMGT]?)(?:i?B)?", RegexOptions.IgnoreCase);
                if (!match.Success)
                    return 0;

                double value = double.Parse(match.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture);
                string unit = match.Groups[2].Value.ToUpper();

                return unit switch
                {
                    "" or "B" => (long)value,
                    "K" => (long)(value * 1024),
                    "M" => (long)(value * 1024 * 1024),
                    "G" => (long)(value * 1024 * 1024 * 1024),
                    "T" => (long)(value * 1024 * 1024 * 1024 * 1024),
                    _ => 0
                };
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"Error parsing size '{sizeText}': {ex.Message}");
                return 0;
            }
        }
    }

    public class RelayCommand : ICommand
    {
        private readonly Action<object> _execute;
        private readonly Func<object, bool> _canExecute;

        public RelayCommand(Action<object> execute, Func<object, bool> canExecute = null)
        {
            _execute = execute;
            _canExecute = canExecute;
        }

        public bool CanExecute(object parameter) => _canExecute?.Invoke(parameter) ?? true;
        public void Execute(object parameter) => _execute(parameter);
        public event EventHandler CanExecuteChanged
        {
            add { CommandManager.RequerySuggested += value; }
            remove { CommandManager.RequerySuggested -= value; }
        }
    }
    #endregion
}