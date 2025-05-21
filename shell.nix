{ pkgs ? import <nixpkgs> { } }:

let
  buildPkgs = pkgs.buildPackages;
  armToolchainCross = pkgs.pkgsCross.arm-embedded.buildPackages;

  # 1. Get the original gcc-arm-embedded package
  gccArmEmbeddedOrig = buildPkgs.gcc-arm-embedded;

  # 2. Define the name of the GDB executable to exclude
  #    (Verify this is correct for your gcc-arm-embedded version)
  gdbExeToExclude = "arm-none-eabi-gdb";

  # 3. Create a wrapper derivation that filters out the unwanted GDB
  gccArmEmbeddedFiltered = pkgs.runCommand "gcc-arm-embedded-no-gdb" {
      # Tools needed for the build script itself
      nativeBuildInputs = [ buildPkgs.coreutils ]; # Provides ln, mkdir, basename, etc.
      # Pass the original toolchain package to the script
      originalToolchain = gccArmEmbeddedOrig;
    } ''
      # Create the output bin directory
      mkdir -p $out/bin

      # === FIXES ARE HERE ===
      # Refer to the variables using shell syntax ($var or )
      echo "Filtering toolchain: $originalToolchain"
      echo "Excluding: ${gdbExeToExclude}"

      # Use shell variable expansion (braces good practice for safety)
      for tool_path in $originalToolchain/bin/*; do
        tool_name=$(basename "$tool_path")
        # Use shell variable syntax for comparison too
        if [ "$tool_name" != "${gdbExeToExclude}" ]; then
          ln -s "$tool_path" "$out/bin/$tool_name"
          echo "  Linked: $tool_name"
        else
          echo "  Skipped: $tool_name"
        fi
      done
      # === END FIXES ===
     
      # Optional linking of other directories
      # if [ -d "$originalToolchain/lib" ]; then ln -s "$originalToolchain/lib" "$out/lib"; fi
    '';

in
pkgs.mkShell {
  nativeBuildInputs = [
    buildPkgs.python313
    buildPkgs.tio
    buildPkgs.valgrind

    # 4. Use the filtered wrapper derivation
    gccArmEmbeddedFiltered

    # 5. Add the GDB you *do* want
    armToolchainCross.gdb

  ];

  packages = [
    (buildPkgs.python313.withPackages (python-pkgs: [
      python-pkgs.tqdm
      python-pkgs.pyserial
      python-pkgs.pandas
      python-pkgs.matplotlib
    ]))
  ];

  shellHook = ''
    echo "--- Nix Shell Environment ---"
    echo "Using GCC from ${gccArmEmbeddedFiltered}:"
    which arm-none-eabi-gcc
    arm-none-eabi-gcc --version | head -n 1
    echo "Using GDB from ${armToolchainCross.gdb}:"
    which ${gdbExeToExclude} # Use the variable here too
    ${gdbExeToExclude} --version | head -n 1
    echo "---------------------------"
  '';
}
