//! Shared utility functions for use in tests.
//!
//! This is in `util/mod.rs` instead of `util.rs` to avoid cargo treating it like a test file.
use snapbox;
use std::path::Path;

#[derive(Clone, Copy)]
pub enum Action {
    Verify,
    Overwrite,
}

/// Depending on `action`, either check that the contents of `path` matches `output`, or overwrite
/// the file with the given output.
pub fn compare_or_overwrite(action: Action, output: String, path: &Path) -> snapbox::Result<()> {
    let actual = snapbox::Data::text(output).map_text(snapbox::utils::normalize_lines);
    match action {
        Action::Verify => expect_file_contents(path, actual)?,
        Action::Overwrite => actual.write_to(path)?,
    }
    Ok(())
}

/// Compare the file contents with the provided string and error with a diff if they differ.
fn expect_file_contents(path: &Path, actual: snapbox::Data) -> snapbox::Result<()> {
    let expected = snapbox::Data::read_from(path, Some(snapbox::DataFormat::Text))?
        .map_text(snapbox::utils::normalize_lines);

    if expected != actual {
        let mut buf = String::new();
        let palette = snapbox::report::Palette::auto();
        snapbox::report::write_diff(
            &mut buf,
            &expected,
            &actual,
            Some(&path.display()),
            Some(&"charon output"),
            palette,
        )
        .map_err(|e| e.to_string())?;
        Err(buf.into())
    } else {
        Ok(())
    }
}
