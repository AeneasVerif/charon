# Versioning

To get the version of the current Charon release, you can run:
```sh
charon version
# 0.1.259 (e4c4510d817097accb931fad0c14f357ce94066d)
```

The version number follows semver; though for now we are still in the `0.1.x` versions. We hope to soon start providing better stability guarantees!

In parentheses is the git commit hash of the Charon source code that was used to build the binary. This is useful for debugging, to know exactly which version of the source code is being run. The version number is always bumped when the AST changes; however we reserve the rights to modify the translation without bumping the version number, e.g. for minor bug fixes.
