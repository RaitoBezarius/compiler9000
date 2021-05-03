{
  description = "Compiler 9000";

  inputs.nixpkgs.url = "github:nixos/nixpkgs-unstable";
  inputs.nixpkgs-vscode.url = "github:nixos/nixpkgs-unstable";
  inputs.nixpkgs.follows = "lean";
  inputs.nixpkgs-vscode.follows = "lean";
  inputs.lean.url = "github:RaitoBezarius/lean4/lean-vscode-override";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, nixpkgs-vscode, lean, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };
        pkgs-vscode = import nixpkgs-vscode {
          inherit system;
          config.allowUnfree = true;
        };
        vim-mode = pkgs-vscode.vscode-utils.extensionFromVscodeMarketplace {
          name = "vim";
          publisher = "vscodevim";
          version = "1.11.3";
          sha256 = "1smzsgcrkhghbnpy51gp28kh74l7y4s2m8pfxabb4ffb751254j0";
        };
        # TODO: Why this doesn't work?
        lean-vscode = pkgs.vscode-with-extensions.override {
          vscodeExtensions = [ vim-mode ];
        };
        leanPkgs = lean.packages.${system};
        pkg = leanPkgs.buildLeanPackage {
          name =
            "Compiler9000"; # must match the name of the top-level .lean file
          src = ./.;
        };
      in {
        packages = pkg // { inherit (leanPkgs) lean; test-vscode = lean-vscode; };

        defaultPackage = pkg.modRoot;
      });
}
