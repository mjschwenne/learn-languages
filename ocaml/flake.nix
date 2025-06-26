{
  description = "A Flake for Learning OCaml";

  inputs = {
    nixpkgs.url = "nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    nixpkgs,
    flake-utils,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
      in {
        devShells.default = with pkgs;
          mkShell {
            buildInputs = with pkgs.ocaml-ng.ocamlPackages_4_14; [
              ocaml
              utop
              ocaml-lsp
              dune_3
              ocamlbuild
              findlib
              batteries
              pprint
              ppx_jane
              stdio
            ];

            shellHook = ''
            '';
          };
      }
    );
}
