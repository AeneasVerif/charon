# Versioning

To get the version of the current Charon release, you can run:
```sh
charon version
# 0.1.259 (e4c4510d817097accb931fad0c14f357ce94066d)
```

This version number does not follow semver: our paradigm is that we increment the patch number for
every breaking change to the AST. Changes to helper functions or to the generated output are not
tracked by this version number. Once we reach `1.0` we'll be more careful with this.

In parentheses is the git commit the binary was built from.
