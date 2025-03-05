{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        overlay = final: prev: {
          hell = prev.callCabal2nix "hell" ./. { };
        };
        haskellPackages = pkgs.haskell.packages.ghc910.extend overlay;
      in
      {
        # nix build
        packages.default = haskellPackages.hell;

        # nix develop
        devShells.default = haskellPackages.shellFor {
          packages = p: [ p.hell ];
          buildInputs = with haskellPackages; [
            stack
            cabal-install
            haskell-language-server
            pandoc-cli
          ];
        };
      }
    );
}
