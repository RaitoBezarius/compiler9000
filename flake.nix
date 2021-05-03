{
  description = "Compiler 9000";

  inputs.nixpkgs-vscode.follows = "lean/nixpkgs-vscode";
  inputs.lean.url = "github:leanprover/lean4";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs-vscode, lean, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs-vscode {
          inherit system;
          config.allowUnfree = true;
        };
        leanPkgs = lean.packages.${system};
        pkg = with pkgs;
          leanPkgs.buildLeanPackage.override {
            lean-vscode = vscode-with-extensions.override {
              vscodeExtensions = with vscode-extensions; [ vscodevim.vim ];
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
