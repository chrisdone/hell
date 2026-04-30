{
  description = "hell";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachSystem [ "aarch64-linux" "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };

        pkgsStaticArm64 = import nixpkgs {
          localSystem  = system;
          crossSystem  = {
            config = "aarch64-unknown-linux-musl";
            isStatic = true;
          };
        };
        pkgsStaticAmd64 = import nixpkgs {
          localSystem  = system;
          crossSystem  = {
            config = "x86_64-unknown-linux-musl";
            isStatic = true;
          };
        };

        mkStaticApp = hp: hp.haskellPackages.callCabal2nix "hell" ./. {};

        app = pkgs.haskellPackages.callCabal2nix "hell" ./. {};
      in {
        devShells.default = pkgs.haskellPackages.shellFor {
          name = "hell-dev";
          packages = _: [ app ];
          withHoogle = true;
          buildInputs = with pkgs.haskellPackages; [
            cabal-install
            haskell-language-server
            fourmolu
            hlint
            pkgs.pandoc
            pkgs.zlib
          ];
        };
        checks = {
          run-script-check = pkgs.runCommand "test-hell-script" {
            buildInputs = [ app ];
          } ''
            hell ${./scripts/check.hell} --dir ${./examples} --dir ${./scripts}
            touch $out
          '';
          build = app;
        };
        packages = {
          default = app;
          static-arm64 = mkStaticApp pkgsStaticArm64;
          static-amd64 = mkStaticApp pkgsStaticAmd64;
        };
      }
    );
}
