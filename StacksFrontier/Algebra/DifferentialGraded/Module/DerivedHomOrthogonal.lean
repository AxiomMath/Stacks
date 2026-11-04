module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHom
public import StacksCore.Tactic.StacksAttribute

/-! # Derived Hom is computed by ordinary Hom at a resolution orthogonal to the acyclics

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`, let `N`
be a differential graded `(A, B)`-bimodule, and let `RHom(N, -) : D(B, d) ⥤ D(A, d)` be the
right derived functor of Hom out of `N` (Tag 09LI). If `I` is a differential graded `B`-module
whose class in `K(B, d)` is orthogonal on the right to the acyclic modules — for instance a
module with property (I), by Tag 09KS — then the canonical comparison

`Hom_{Mod^{dg}_{(B,d)}}(N, I) ⟶ RHom(N, I)`

is an isomorphism of `D(A, d)`.

The underlying statement is about an arbitrary right derived functor: a left Kan extension along
a localization functor has invertible unit at any object into which the localization functor is
bijective on morphisms.

## Main results

* `CategoryTheory.Functor.isIso_app_of_bijective_of_isRightDerivedFunctor`: the unit of a right
  derived functor is invertible at an object into which the localization functor is bijective on
  morphisms, provided the derived functor is pointwise.
* `DifferentialGradedModule.hasPointwiseRightDerivedFunctor_of_exists_quasiIso_rightOrthogonal`:
  resolutions on the right make every right derived functor on `K(A, d)` pointwise.
* `DifferentialGradedModule.isIso_app_of_rightOrthogonal`: the unit of a right derived functor
  on `K(A, d)` is invertible at a module orthogonal on the right to the acyclic ones.
* `DifferentialGradedModule.DerivedHomData.isIso_comparison_app_of_rightOrthogonal` and
  `DifferentialGradedModule.DerivedHomData.comparisonIso`: the comparison of Tag 09LI is an
  isomorphism at such a module, and the resulting identification of derived Hom with ordinary
  differential graded Hom.

## Implementation notes

The general statement assumes `F.HasPointwiseRightDerivedFunctor W`: the bijectivity at `I`
makes the colimit computing the left Kan extension at `I` exist, but the identification of an
abstract left Kan extension with the pointwise one is global. In the differential graded case
the pointwise right derived functor is supplied by the resolutions, whose existence is Tag 09KU.

## References

* [Stacks Project, Tag 0CS5](https://stacks.math.columbia.edu/tag/0CS5); the derived functor is
  [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI), the orthogonality of property (I) modules
  is [Tag 09KS](https://stacks.math.columbia.edu/tag/09KS), and their existence is
  [Tag 09KU](https://stacks.math.columbia.edu/tag/09KU).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-- The unit of a right derived functor is invertible at an object `I` into which the
localization functor is bijective on morphisms. -/
theorem isIso_app_of_bijective_of_isRightDerivedFunctor (F : C ⥤ H) (L : C ⥤ D)
    (W : MorphismProperty C) [L.IsLocalization W] [F.HasPointwiseRightDerivedFunctor W]
    {RF : D ⥤ H} (α : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor α W] (I : C)
    (h : ∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I))) :
    IsIso (α.app I) := by
  simpa using (isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor RF α W
    (L.obj I)).isIso_ι_app_of_isTerminal _ (costructuredArrowMkIdIsTerminal L I h)

end CategoryTheory.Functor

namespace DifferentialGradedModule

variable {R : Type u₁} [CommRing R] (A : DifferentialGradedAlgebra R)
  {H : Type u₃} [Category.{v₃} H]

/-- Under resolutions on the right by modules orthogonal to the acyclic ones, every
`F : K(A, d) ⥤ ℋ` has a *pointwise* right derived functor with respect to the
quasi-isomorphisms. -/
theorem hasPointwiseRightDerivedFunctor_of_exists_quasiIso_rightOrthogonal
    (F : HomotopyCategory A ⥤ H)
    (hres : ∀ M : DifferentialGradedModule A,
      ∃ (I : DifferentialGradedModule A) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj I)) :
    F.HasPointwiseRightDerivedFunctor (quasiIsomorphisms' A) := by
  rw [← acyclic_trW_eq_quasiIsomorphisms']
  exact (acyclic' A).hasPointwiseRightDerivedFunctor_of_rightOrthogonal_resolutions F
    (exists_trW_rightOrthogonal_of_exists_quasiIso_rightOrthogonal A hres)

/-- The localization functor of `K(A, d)` at the quasi-isomorphisms is a localization functor
for the multiplicative system attached to the acyclic modules. -/
theorem quasiIsomorphismsQ_isLocalization_acyclic_trW :
    (quasiIsomorphisms' A).Q.IsLocalization ((acyclic' A).trW) := by
  rw [acyclic_trW_eq_quasiIsomorphisms']
  infer_instance

/-- The localization functor of `K(A, d)` at the quasi-isomorphisms is bijective on the
morphisms into an object orthogonal on the right to the acyclic modules. -/
theorem quasiIsomorphismsQ_map_bijective_of_rightOrthogonal {I : HomotopyCategory A}
    (hI : (acyclic' A).rightOrthogonal I) (X : HomotopyCategory A) :
    Function.Bijective ((quasiIsomorphisms' A).Q.map :
      (X ⟶ I) → ((quasiIsomorphisms' A).Q.obj X ⟶ (quasiIsomorphisms' A).Q.obj I)) :=
  have := quasiIsomorphismsQ_isLocalization_acyclic_trW A
  ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated hI (quasiIsomorphisms' A).Q X

/-- The unit of a right derived functor on `K(A, d)` is invertible at an object orthogonal on
the right to the acyclic modules, as soon as resolutions by such objects exist. -/
theorem isIso_app_of_rightOrthogonal (F : HomotopyCategory A ⥤ H)
    (hres : ∀ M : DifferentialGradedModule A,
      ∃ (I : DifferentialGradedModule A) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj I))
    {RF : (quasiIsomorphisms' A).Localization ⥤ H}
    (α : F ⟶ (quasiIsomorphisms' A).Q ⋙ RF)
    [RF.IsRightDerivedFunctor α (quasiIsomorphisms' A)]
    {I : HomotopyCategory A} (hI : (acyclic' A).rightOrthogonal I) :
    IsIso (α.app I) :=
  have := hasPointwiseRightDerivedFunctor_of_exists_quasiIso_rightOrthogonal A F hres
  Functor.isIso_app_of_bijective_of_isRightDerivedFunctor F (quasiIsomorphisms' A).Q
    (quasiIsomorphisms' A) α I (quasiIsomorphismsQ_map_bijective_of_rightOrthogonal A hI)

namespace DerivedHomData

variable {A} (B : DifferentialGradedAlgebra R) {N : DifferentialGradedModule B}

variable (A) in
/-- The comparison of Tag 09LI from ordinary differential graded Hom to derived Hom is an
isomorphism at a differential graded `B`-module orthogonal on the right to the acyclic ones, for
instance a module with property (I). -/
theorem isIso_comparison_app_of_rightOrthogonal (L : BimoduleStructure A B N)
    (D : DerivedHomData A B N L)
    (hres : ∀ M : DifferentialGradedModule B, ∃ (I : DifferentialGradedModule B) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex B).map f) ∧
        (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I))
    {I : HomotopyCategory B} (hI : (acyclic' B).rightOrthogonal I) :
    IsIso (D.comparison.app I) :=
  have := D.isRightDerived
  isIso_app_of_rightOrthogonal B (homToDerivedCategory A B N L) hres D.comparison hI

variable (A) in
/-- Derived Hom out of `N` evaluated at a module `I` orthogonal on the right to the acyclic ones
is ordinary differential graded Hom out of `N` into `I`, read in the derived category of
differential graded `A`-modules. -/
def comparisonIso (L : BimoduleStructure A B N) (D : DerivedHomData A B N L)
    (hres : ∀ M : DifferentialGradedModule B, ∃ (I : DifferentialGradedModule B) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex B).map f) ∧
        (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I))
    {I : HomotopyCategory B} (hI : (acyclic' B).rightOrthogonal I) :
    (homToDerivedCategory A B N L).obj I ≅ D.functor.obj ((quasiIsomorphisms' B).Q.obj I) :=
  have := isIso_comparison_app_of_rightOrthogonal A B L D hres hI
  asIso (D.comparison.app I)

end DerivedHomData

end DifferentialGradedModule

end
