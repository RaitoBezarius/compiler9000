# Compiler 9000

An formalized micro-compiler in Lean 4

## Instructions

Use Nix with Flakes support, if you want to have cache support.

```
$ cachix use compiler9000
$ nix run .#vscode-dev
```

Enjoy your VSCode development environment.

## Continuous Integrations

All commits / pull requests to `main` are rebuilt for the VSCode development environment and pushed to the cache.
