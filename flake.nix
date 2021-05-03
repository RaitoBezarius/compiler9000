{
  description = "Compiler 9000";

  inputs.nixpkgs.url = "github:nixos/nixpkgs-unstable";
  inputs.nixpkgs.follows = "lean";
  inputs.lean.url = "github:RaitoBezarius/lean4/lean-vscode-override";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, lean, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };
        leanPkgs = lean.packages.${system};
        pkg = leanPkgs.buildLeanPackage.override {
          lean-vscode = leanPkgs.lean-vscode.override {
            vscodeExtensions = with pkgs.vscode-extensions; [ vscodevim.vim ];
          };
        } {
          name =
            "Compiler9000"; # must match the name of the top-level .lean file
          src = ./.;
        };
      in {
        packages = pkg // { inherit (leanPkgs) lean; };

        defaultPackage = pkg.modRoot;
      });
}
