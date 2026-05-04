{
  description = "Simple Lean setup";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };
  outputs =
    {
      nixpkgs,
      flake-utils,
      lean4-nix,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
        };
      in
      {
        devShells.default =
          with pkgs;
          mkShell {
            buildInputs = [
              # lean
              lean.lean-all

              # lean proofwidgets dep
              nodejs-slim

              # nix helpers
              nix-update
            ];
          };
      }
    );
}
