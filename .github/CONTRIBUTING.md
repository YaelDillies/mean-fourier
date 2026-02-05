We mostly follow [Mathlib's contribution guide](https://leanprover-community.github.io/contribute/index.html).

On top of Mathlib's contribution guidelines, we also enforce the following:
* Prerequisites that belong to existing Mathlib files should be put in the `MeanFourier.Mathlib` folder.
  Precisely, declarations that belong in an existing Mathlib file `Mathlib.X` will be located in `MeanFourier.Mathlib.X`.
  We aim to preserve the property that `MeanFourier.Mathlib.X` only imports `Mathlib.X` and files of the form `MeanFourier.Mathlib.Y` where `Mathlib.X` (transitively) imports `Mathlib.Y`.
  Prerequisites that do not belong in any existing Mathlib file should be located outside the `MeanFourier.Mathlib` folder.
