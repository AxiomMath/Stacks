module

public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction

/-!
# The unit of the derived extension–restriction adjunction at a localized complex

`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction` makes any model of
total derived extension of scalars left adjoint to derived restriction of scalars. Its unit at
`DerivedCategory.Q` of a complex is computed in
`StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction`, which this module re-exports:

* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app`: the unit
  at `DerivedCategory.Q.obj X`, composed with derived restriction of scalars of the comparison of
  the chosen model with degreewise extension of scalars, is `DerivedCategory.Q` of the degreewise
  unit followed by the factorization of derived restriction of scalars.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq`: the
  same solved for the unit, where the comparison is invertible at `X`, and
  `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`
  with that invertibility supplied at every K-flat complex.
-/
