{
  description = "Haskell app with cross-compilation";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachSystem [ "aarch64-linux", "x86_64-linux" ] (system:
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

        mkStaticApp = hp: hp.haskellPackages.callCabal2nix "my-app" ./. {};

        app = pkgs.haskellPackages.callCabal2nix "my-app" ./. {};
      in {
        devShells.default = pkgs.haskellPackages.shellFor {
          name = "my-app-dev";
          packages = _: [ app ];
          withHoogle = true;
          buildInputs = with pkgs.haskellPackages; [
            cabal-install
            haskell-language-server
            fourmolu
            hlint
            pkgs.zlib
          ];
        };
        packages = {
          default = app;
          static-arm64 = mkStaticApp pkgsStaticArm64;
          static-amd64 = mkStaticApp pkgsStaticAmd64;
        };
      }
    );
}
