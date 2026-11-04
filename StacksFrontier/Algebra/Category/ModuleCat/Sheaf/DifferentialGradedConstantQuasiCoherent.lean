module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConstantTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionQuasiCoherentSubcategory

/-!
# Quasi-coherent objects over a sheaf of differential graded algebras over a constant ring

For a sheaf `(A, d)` of differential graded algebras over the constant sheaf of rings with value
`R` on a chaotic site, the full subcategory `QC(A, d)` of `D(A, d)` is strictly full, saturated
and triangulated (Tag 0GZA). This file restates the instances of Tag 0GZA for `A` over the
constant sheaf of rings, whose sheaf of rings is that of the chaotic ringed site of the constant
sheaf of commutative rings on the nose, so that instance search finds the pretriangulated and
`R`-linear structures of `QC(A, d)`: the structures in which Remark 0H1E compares it with
`D_comp(R, I)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.Chaotic.const_qc_isTriangulated`: `QC(A, d)` is a
  triangulated subcategory, so `QC(A, d)` is pretriangulated (and `R`-linear, as a full
  subcategory of the `R`-linear category `D(A, d)`).

## References

* [Stacks Project, Lemma 24.33.3 (Tag 0GZA)](https://stacks.math.columbia.edu/tag/0GZA)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace SheafOfModules.DifferentialGradedModule.Chaotic

variable {C : Type u} [Category.{u} C] {R : Type u} [CommRing R]
  (A : SheafOfModules.DifferentialGradedAlgebra.{u, u}
    (Stacks.PresheafOfModules.constRingSheaf (C := C) R))

/-- `QC(A, d)` is closed under isomorphisms (Tag 0GZA), over the constant sheaf of rings. -/
instance const_qc_isClosedUnderIsomorphisms : (QC A).IsClosedUnderIsomorphisms :=
  qc_isClosedUnderIsomorphisms (O := Stacks.PresheafOfModules.constCommRingSheaf (C := C) R) A

/-- `QC(A, d)` is a triangulated subcategory of `D(A, d)` (Tag 0GZA), over the constant sheaf of
rings. -/
instance const_qc_isTriangulated : (QC A).IsTriangulated :=
  qc_isTriangulated (O := Stacks.PresheafOfModules.constCommRingSheaf (C := C) R) A

example : Pretriangulated (QC A).FullSubcategory := inferInstance

example : Linear R (QC A).FullSubcategory := inferInstance

example : IsTriangulated (QC A).FullSubcategory := inferInstance

end SheafOfModules.DifferentialGradedModule.Chaotic
