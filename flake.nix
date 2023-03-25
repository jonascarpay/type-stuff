{
  description = "type-stuff";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/release-22.11";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.unify.url = "github:jonascarpay/unify";
  inputs.rebound.url = "github:jonascarpay/rebound";

  outputs = inputs:
    let
      overlay = final: prev: {
        haskell = prev.haskell // {
          packageOverrides = hfinal: hprev:
            prev.haskell.packageOverrides hfinal hprev // {
              type-stuff = hfinal.callCabal2nix "type-stuff" ./. { };
            };
        };
        type-stuff = final.haskell.lib.compose.justStaticExecutables final.haskellPackages.type-stuff;
      };
      perSystem = system:
        let
          pkgs = import inputs.nixpkgs { inherit system; overlays = [ inputs.unify.overlay inputs.rebound.overlay overlay ]; };
          hspkgs = pkgs.haskellPackages;
        in
        {
          devShell = hspkgs.shellFor {
            withHoogle = true;
            doBenchmark = true;
            packages = p: [ p.type-stuff ];
            extraDependencies = p: { benchmarkHaskellDepends = [ p.criterion ]; }; # doBenchmark does not work for whatever reason
            buildInputs = [
              hspkgs.cabal-install
              hspkgs.haskell-language-server
              hspkgs.hlint
              hspkgs.ormolu
              pkgs.bashInteractive
              pkgs.tagref
            ];
          };
          defaultPackage = pkgs.type-stuff;
        };
    in
    { inherit overlay; } // inputs.flake-utils.lib.eachDefaultSystem perSystem;
}
