[
  (self: super: {
    coqPackages = super.coqPackages.overrideScope (
      f: p: {
        vscoq-language-server = p.vscoq-language-server.overrideAttrs (o: rec {
          version = "2.2.3";
          src =
            let
              fetched = self.fetchFromGitHub {
                owner = "coq-community";
                repo = "vscoq";
                rev = "v${version}";
                hash = "sha256-3utFmksoVQhhde3yRXoHBzVJmafKPuaxAWN+X5B7Trk=";
              };
            in
            "${fetched}/language-server";
          name = "ocaml${super.ocaml.version}-${o.pname}-${version}";
        });
      }
    );
  })
]
