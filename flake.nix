{
  description = "Elan environment with direnv";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs";

  outputs = { self, nixpkgs }:
    let pkgs = import nixpkgs { system = "x86_64-linux"; };
    in {
      devShell.x86_64-linux = pkgs.mkShell { buildInputs = [ pkgs.elan ]; };
    };
}
