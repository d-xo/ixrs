{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    hypertypes = { url = "github:lamdu/hypertypes"; flake = false; };
  };
  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed;
      imports = [ inputs.haskell-flake.flakeModule ];

      perSystem = { self', pkgs, ... }: {
        haskellProjects.default = {
          packages = {
            hypertypes.source = inputs.hypertypes;
          };
          settings = {
            parameterized-utils.broken = false;
          };
        };
        packages.default = self'.packages.hkrs;
      };
    };
}
