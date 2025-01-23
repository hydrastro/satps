{
  description = "satps";

  inputs = { nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable"; };

  outputs = { self, nixpkgs }: {
    packages = nixpkgs.lib.genAttrs [ "x86_64-linux" ] (system:
      let pkgs = import nixpkgs { inherit system; };
      in rec {
        satps = pkgs.stdenv.mkDerivation {
          pname = "satps";
          version = "0.0.0";

          src = ./.;

          buildInputs = [ pkgs.stdenv.cc pkgs.freeglut pkgs.glew ];

          buildPhase = ''
            make PREFIX=$out
          '';

          installPhase = ''
            mkdir -p $out/bin
            cp satps $out/bin/
            chmod +x $out/bin/satps
          '';

          meta = with pkgs.lib; { description = "satps"; };
        };
      });

    defaultPackage = { x86_64-linux = self.packages.x86_64-linux.satps; };
  };
}
