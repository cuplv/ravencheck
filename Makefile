RAVENCHECK_VERSION=0.1.1

prep-release:
	cp release-files/support-readme.md lang/README.md
	cp release-files/support-readme.md macros/README.md
	sed -i 's|{ path = "./macros" }|"'${RAVENCHECK_VERSION}'"|g' Cargo.toml
	sed -i 's|{ path = "./lang" }|"'${RAVENCHECK_VERSION}'"|g' Cargo.toml
