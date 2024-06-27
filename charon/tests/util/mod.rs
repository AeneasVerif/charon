//! Shared utility functions for use in tests.
//!
//! This is in `util/mod.rs` instead of `util.rs` to avoid cargo treating it like a test file.
use snapbox;
use snapbox::filter::Filter;
use std::path::Path;

#[derive(Clone, Copy)]
pub enum Action {
    Verify,
    Overwrite,
}

/// Depending on `action`, either check that the contents of `path` matches `output`, or overwrite
/// the file with the given output.
pub fn compare_or_overwrite(
    action: Action,
    output: String,
    path: &Path,
) -> snapbox::assert::Result<()> {
    let actual = snapbox::Data::text(output);
    let actual = snapbox::filter::FilterNewlines.filter(actual);
    match action {
        Action::Verify => expect_file_contents(path, actual)?,
        Action::Overwrite => actual.write_to_path(path)?,
    }
    Ok(())
}

/// Compare the file contents with the provided string and error with a diff if they differ.
fn expect_file_contents(path: &Path, actual: snapbox::Data) -> snapbox::assert::Result<()> {
    let expected = snapbox::Data::read_from(path, Some(snapbox::data::DataFormat::Text));
    let expected = snapbox::filter::FilterNewlines.filter(expected);

    if expected != actual {
        let mut buf = String::new();
        snapbox::report::write_diff(
            &mut buf,
            &expected,
            &actual,
            Some(&path.display()),
            Some(&"charon output"),
            Default::default(),
        )
        .map_err(|e| e.to_string())?;
        Err(buf.into())
    } else {
        Ok(())
    }
}
