{
  description = "Supplemental material to the paper \"'do' Unchained: Embracing Local Imperativity in a Purely Functional Language\"";

  inputs.lean.url = github:leanprover/lean4;
  inputs.lean-doc.url = github:leanprover/lean4?dir=doc;
  inputs.lean-doc.inputs.lean.follows = "lean";
  inputs.lean-doc.inputs.flake-utils.follows = "lean/flake-utils";
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.aesop.url = github:JLimperg/aesop;
  inputs.aesop.flake = false;

  outputs = { flake-utils, ... }@inputs: flake-utils.lib.eachDefaultSystem (system:
    let
      leanPkgs = inputs.lean.packages.${system};
      lean-doc = inputs.lean-doc.packages.${system};
      aesop = leanPkgs.buildLeanPackage {
        name = "Aesop";
        src = inputs.aesop;
        precompilePackage = true;
      };
      pkg = leanPkgs.buildLeanPackage {
        name = "Do";  # must match the name of the top-level .lean file
        src = ./.;
        deps = [ aesop ];
      };
    in with leanPkgs.nixpkgs; {
      packages = pkg // rec {
        inherit (leanPkgs) lean ciShell;

        renders = let
          mods = lean-doc.renderDir "Do" ./Do;
          mods' = map (drv: drv.overrideAttrs (_: { LEAN_PATH = pkg.modRoot; })) mods.paths;
        in symlinkJoin { name = "Do"; paths = mods'; };

        book = stdenv.mkDerivation {
          name = "do-doc";
          src = ./doc;
          buildInputs = [ lean-doc.lean-mdbook ];
          buildPhase = ''
            mkdir $out
            # necessary for `additional-css`...?
            cp -r --no-preserve=mode ${inputs.lean-doc}/doc/*.{js,css} .
            cp -r ${renders}/* .
            mdbook build -d $out
        '';
          dontInstall = true;
        };
      };

      defaultPackage = pkg.modRoot;
    });
}
