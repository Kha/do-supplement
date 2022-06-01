{
  description = "Supplemental material to the paper \"'do' Unchained: Embracing Local Imperativity in a Purely Functional Language\"";

  inputs.lean.url = github:leanprover/lean4;
  inputs.flake-utils.url = github:numtide/flake-utils;

  outputs = { self, lean, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let
      leanPkgs = lean.packages.${system};
      pkg = leanPkgs.buildLeanPackage {
        name = "Do";  # must match the name of the top-level .lean file
        src = ./.;
      };
    in {
      packages = pkg // {
        inherit (leanPkgs) lean;
      };

      defaultPackage = pkg.modRoot;
    });
}
