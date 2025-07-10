#![feature(trait_alias)]

// @ known-failure

use std::fmt::Error;

// Test 1: Basic trait with associated type
trait Display {
    type Output;
    fn fmt(&self) -> Self::Output;
}

// Test 2: Trait inheriting associated type
trait PrettyDisplay: Display {
    fn pretty_fmt(&self) -> Self::Output;
}

// Test 3: Generic trait for displaying
trait Formatter<T : ?Sized> {
    fn format(&self, item: &T) -> String;
}

// Test trait alias for dyn Display
trait Displayable = Formatter<dyn Display<Output = String>>;

trait PrettyFormatter<T> : Display + Formatter<T> {
    fn pretty_format(&self, item: &T) -> String;
    fn no_dyn_pretty_fmt(self, item: &T) -> String;
}

trait PrettyArray<'a, T, const N: usize> : Displayable + Formatter<[T; N]> {
    fn pretty_array_format(&self, item: &'a [T; N]) -> &'a [String; N];
}

// Test 4: Dyn with Send and lifetime for async display
trait AsyncRenderer<'a>: Send {
    fn render(&self, content: &'a str) -> String;
}

// Implementations for PrettyFormatter
struct StyledFormatter {
    style: String,
}

impl StyledFormatter {
    fn new(style: &str) -> Self {
        Self { style: style.to_string() }
    }
}

impl Display for StyledFormatter {
    type Output = String;
    fn fmt(&self) -> Self::Output {
        format!("StyledFormatter[{}]", self.style)
    }
}

impl<T: Display<Output = String>> Formatter<T> for StyledFormatter {
    fn format(&self, item: &T) -> String {
        format!("[{}] {}", self.style, item.fmt())
    }
}

impl Formatter<dyn Display<Output = String>> for StyledFormatter {
    fn format(&self, item: &dyn Display<Output = String>) -> String {
        format!("[{}] {}", self.style, item.fmt())
    }
}

impl<T: Display<Output = String>> PrettyFormatter<T> for StyledFormatter {
    fn pretty_format(&self, item: &T) -> String {
        format!("✨ [{}] {} ✨", self.style, item.fmt())
    }
    
    fn no_dyn_pretty_fmt(self, item: &T) -> String {
        format!("🎨 [{}] {} 🎨", self.style, item.fmt())
    }
}

// Implementation for PrettyArray
struct ArrayFormatter;

impl Formatter<dyn Display<Output = String>> for ArrayFormatter {
    fn format(&self, item: &dyn Display<Output = String>) -> String {
        item.fmt()
    }
}

impl<'a, T: Display<Output = String>, const N: usize> Formatter<[T; N]> for ArrayFormatter {
    fn format(&self, items: &[T; N]) -> String {
        items.iter()
            .map(|item| item.fmt())
            .collect::<Vec<_>>()
            .join(", ")
    }
}

impl<'a, T: Display<Output = String>, const N: usize> PrettyArray<'a, T, N> for ArrayFormatter {
    fn pretty_array_format(&self, item: &'a [T; N]) -> &'a [String; N] {
        // Note: This is a simplified implementation due to lifetime constraints
        // In practice, you'd need to return owned data or use a different approach
        unsafe { std::mem::transmute(item) }
    }
}

// Implementation for AsyncRenderer
struct SimpleAsyncRenderer {
    template: String,
}

impl SimpleAsyncRenderer {
    fn new(template: &str) -> Self {
        Self { template: template.to_string() }
    }
}

impl<'a> AsyncRenderer<'a> for SimpleAsyncRenderer {
    fn render(&self, content: &'a str) -> String {
        format!("{}: {}", self.template, content)
    }
}

// Test 5: Trait inheritance hierarchy
trait Drawable {
    fn draw(&self) -> String;
}

trait ColorDrawable: Drawable {
    fn draw_with_color(&self, color: &str) -> String;
}

trait AnimatedDrawable: ColorDrawable {
    fn animate(&self) -> String;
}

// Test 6: Non-dyn-compatible traits (no dyn objects for these)
trait Cloneable {
    fn clone(&self) -> Self; // Returns Self, not dyn-compatible
}

trait GenericDisplay {
    fn display_as<T: std::fmt::Display>(&self) -> Result<T,Error>; // Generic method, not dyn-compatible
}

fn use_clonable_generic_display<T: Cloneable + GenericDisplay>(item: &T) {
    let cloned_item = item.clone();
    let display_result = cloned_item.display_as::<String>();
    let display_result = match display_result {
        Ok(result) => result,
        Err(_) => "Error displaying item".to_string(),
    };
    println!("Display result: {}", display_result);
}

// Implementation for Text with Cloneable
impl Cloneable for Text {
    fn clone(&self) -> Self {
        Text {
            content: self.content.clone(),
        }
    }
}

// Implementation for Text with GenericDisplay
impl GenericDisplay for Text {
    fn display_as<T: std::fmt::Display>(&self) -> Result<T, std::fmt::Error> {
        // This is a bit contrived since we can't actually convert arbitrary types
        // In practice, this would be implemented differently or not at all
        Err(std::fmt::Error) // Placeholder for demonstration
    }
}

// Implementation for Image with Cloneable
impl Cloneable for Image {
    fn clone(&self) -> Self {
        Image {
            path: self.path.clone(),
            width: self.width,
            height: self.height,
        }
    }
}

// Implementation for Button with Cloneable
impl Cloneable for Button {
    fn clone(&self) -> Self {
        Button {
            label: self.label.clone(),
            enabled: self.enabled,
        }
    }
}

// Concrete types for our display story
struct Text {
    content: String,
}

struct Image {
    path: String,
    width: u32,
    height: u32,
}

struct Button {
    label: String,
    enabled: bool,
}

// Lifetime-dependent formatter that borrows from the item being formatted
struct BorrowingFormatter<'a> {
    prefix: &'a str,
    suffix: &'a str,
}

impl<'a> BorrowingFormatter<'a> {
    fn new(prefix: &'a str, suffix: &'a str) -> Self {
        Self { prefix, suffix }
    }
}

impl<'a, T: Display<Output = String>> Formatter<T> for BorrowingFormatter<'a> {
    fn format(&self, item: &T) -> String {
        format!("{}{}{}", self.prefix, item.fmt(), self.suffix)
    }
}

impl<'a> Formatter<dyn Display<Output = String>> for BorrowingFormatter<'a> {
    fn format(&self, item: &dyn Display<Output = String>) -> String {
        format!("{}{}{}", self.prefix, item.fmt(), self.suffix)
    }
}

// Trait requiring lifetime parameters for borrowed data
trait LifetimeRenderer<'a, 'b> {
    fn render_with_context(&self, content: &'a str, context: &'b str) -> String;
}

struct ContextualRenderer {
    template: String,
}

impl<'a, 'b> LifetimeRenderer<'a, 'b> for ContextualRenderer {
    fn render_with_context(&self, content: &'a str, context: &'b str) -> String {
        format!("{}: {} ({})", self.template, content, context)
    }
}

// Test function using lifetime-dependent formatters
fn test_borrowing_formatter() {
    let prefix = ">>> ";
    let suffix = " <<<";
    let formatter = BorrowingFormatter::new(prefix, suffix);
    
    let text = Text { content: "Borrowed content".to_string() };
    println!("{}", formatter.format(&text));
    
    let renderer = ContextualRenderer { template: "Debug".to_string() };
    let content = "main content";
    let context = "test context";
    println!("{}", renderer.render_with_context(content, context));
}

// Implementations for Text
impl Display for Text {
    type Output = String;
    fn fmt(&self) -> Self::Output {
        self.content.clone()
    }
}

impl PrettyDisplay for Text {
    fn pretty_fmt(&self) -> Self::Output {
        format!("📝 {}", self.content)
    }
}

impl Drawable for Text {
    fn draw(&self) -> String {
        format!("[Text: {}]", self.content)
    }
}

// Implementations for Image
impl Display for Image {
    type Output = String;
    fn fmt(&self) -> Self::Output {
        format!("{}x{} image at {}", self.width, self.height, self.path)
    }
}

impl Drawable for Image {
    fn draw(&self) -> String {
        format!("[Image: {} ({}x{})]", self.path, self.width, self.height)
    }
}

impl ColorDrawable for Image {
    fn draw_with_color(&self, color: &str) -> String {
        format!("[Image: {} ({}x{}) in {}]", self.path, self.width, self.height, color)
    }
}

// Implementations for Button
impl Display for Button {
    type Output = String;
    fn fmt(&self) -> Self::Output {
        format!("Button: {} ({})", self.label, if self.enabled { "enabled" } else { "disabled" })
    }
}

impl Drawable for Button {
    fn draw(&self) -> String {
        format!("[Button: {}]", self.label)
    }
}

impl ColorDrawable for Button {
    fn draw_with_color(&self, color: &str) -> String {
        format!("[Button: {} in {}]", self.label, color)
    }
}

impl AnimatedDrawable for Button {
    fn animate(&self) -> String {
        format!("[Animated Button: {} ✨]", self.label)
    }
}

// Test functions using dyn traits
fn test_basic_display() {
    let text = Text { content: "Hello World".to_string() };
    let displayable: &dyn Display<Output = String> = &text;
    let result = displayable.fmt();
    println!("Display result: {}", result);
}

fn test_pretty_display() {
    let text = Text { content: "Beautiful Text".to_string() };
    let pretty: &dyn PrettyDisplay<Output = String> = &text;
    let result = pretty.pretty_fmt();
    println!("Pretty display result: {}", result);
}

fn test_drawable_inheritance() {
    let button = Button { label: "Click Me".to_string(), enabled: true };
    let drawable: &dyn AnimatedDrawable = &button;
    let animation = drawable.animate();
    let colored = drawable.draw_with_color("blue");
    let basic = drawable.draw();
    println!("Basic: {}, Colored: {}, Animation: {}", basic, colored, animation);
}

fn test_async_renderer<'a>(renderer: Box<dyn AsyncRenderer<'a> + Send>) {
    let content = "rendering content";
    let result = renderer.render(content);
    println!("Async rendered: {}", result);
}

fn test_pretty_formatter<T: Display<Output = String>>(formatter: &dyn PrettyFormatter<T, Output = String>, item: &T) {
    let pretty_result = formatter.pretty_format(item);
    println!("Pretty formatted: {}", pretty_result);
}

fn cast_dyn<T: std::fmt::Debug>(x: &T) -> &dyn std::fmt::Debug { x }

fn main() {
    // Test basic display functionality
    test_basic_display();
    test_pretty_display();
    test_drawable_inheritance();
    test_borrowing_formatter();

    let dbg = cast_dyn(&"Hello, world!");
    println!("Cast dyn: {:?}", dbg);
    
    // Test async renderer
    let async_renderer = Box::new(SimpleAsyncRenderer::new("Template"));
    test_async_renderer(async_renderer);

    // Create instances and test Display trait
    let text = Text { content: "Sample text".to_string() };
    let image = Image { path: "/path/to/image.jpg".to_string(), width: 800, height: 600 };
    let button = Button { label: "Submit".to_string(), enabled: true };

    println!("Text display: {}", text.fmt());
    println!("Image display: {}", image.fmt());
    println!("Button display: {}", button.fmt());

    // Test PrettyDisplay
    println!("Pretty text: {}", text.pretty_fmt());

    // Test Drawable hierarchy
    println!("Text drawable: {}", text.draw());
    println!("Image drawable: {}", image.draw());
    println!("Button drawable: {}", button.draw());

    // Test ColorDrawable
    println!("Image with color: {}", image.draw_with_color("red"));
    println!("Button with color: {}", button.draw_with_color("green"));

    // Test AnimatedDrawable
    println!("Animated button: {}", button.animate());

    // Test with dyn trait objects
    use_clonable_generic_display(&text);

    let styled_formatter = StyledFormatter::new("Bold");
    let formatted_text = styled_formatter.format(&text);
    println!("Formatted text: {}", formatted_text);
    
    // Test PrettyFormatter trait
    test_pretty_formatter(&styled_formatter, &text);
    
    // Test no_dyn_pretty_fmt method
    let styled_formatter_owned = StyledFormatter::new("Italic");
    let no_dyn_result = styled_formatter_owned.no_dyn_pretty_fmt(&text);
    println!("No dyn pretty format: {}", no_dyn_result);
    
    use_clonable_generic_display(&text);

    let styled_formatter = StyledFormatter::new("Bold");
    let formatted_text = styled_formatter.format(&text);
    println!("Formatted text: {}", formatted_text);

    // Test ArrayFormatter
    let array_formatter = ArrayFormatter;
    let text_array = [text, Text { content: "Second text".to_string() }];
    println!("Array formatted: {}", array_formatter.format(&text_array));
    
    // Test PrettyArray trait
    let pretty_array_result = array_formatter.pretty_array_format(&text_array);
    println!("Pretty array result length: {}", pretty_array_result.len());
}
