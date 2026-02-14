using System.Windows;
using System.Windows.Controls;

namespace PS3Manager
{
    public partial class InputDialog : Window
    {
        public string ResponseText { get; private set; }

        public InputDialog(string title, string prompt, string defaultValue = "")
        {
            Title = title;
            Width = 400;
            Height = 150;
            WindowStartupLocation = WindowStartupLocation.CenterOwner;
            Background = (System.Windows.Media.Brush)Application.Current.FindResource("BgDark");

            var grid = new Grid { Margin = new Thickness(10) };
            grid.RowDefinitions.Add(new RowDefinition { Height = GridLength.Auto });
            grid.RowDefinitions.Add(new RowDefinition { Height = GridLength.Auto });
            grid.RowDefinitions.Add(new RowDefinition { Height = GridLength.Auto });

            var promptText = new TextBlock
            {
                Text = prompt,
                Foreground = System.Windows.Media.Brushes.White,
                Margin = new Thickness(0, 0, 0, 5)
            };
            Grid.SetRow(promptText, 0);

            var textBox = new TextBox
            {
                Text = defaultValue,
                Background = (System.Windows.Media.Brush)Application.Current.FindResource("BgCard"),
                Foreground = System.Windows.Media.Brushes.White,
                Padding = new Thickness(5),
                Margin = new Thickness(0, 0, 0, 10)
            };
            Grid.SetRow(textBox, 1);

            var buttonPanel = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Right };
            var okButton = new Button
            {
                Content = "OK",
                Width = 75,
                Margin = new Thickness(0, 0, 5, 0),
                Background = (System.Windows.Media.Brush)Application.Current.FindResource("Cyan"),
                Foreground = System.Windows.Media.Brushes.Black
            };
            var cancelButton = new Button
            {
                Content = "Cancel",
                Width = 75,
                Background = (System.Windows.Media.Brush)Application.Current.FindResource("BgHover"),
                Foreground = System.Windows.Media.Brushes.White
            };

            okButton.Click += (s, e) => { ResponseText = textBox.Text; DialogResult = true; Close(); };
            cancelButton.Click += (s, e) => { DialogResult = false; Close(); };

            buttonPanel.Children.Add(okButton);
            buttonPanel.Children.Add(cancelButton);
            Grid.SetRow(buttonPanel, 2);

            grid.Children.Add(promptText);
            grid.Children.Add(textBox);
            grid.Children.Add(buttonPanel);

            Content = grid;
            textBox.Focus();
            textBox.SelectAll();
        }
    }
}