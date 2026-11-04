module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.KInjectiveSections
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Hom complexes and extension of scalars

The Hom complex out of an extension of scalars is the Hom complex into a restriction of scalars.

## Main definitions

* `AlgebraicGeometry.AffineExt.adjHomComplexIso`: the isomorphism of Hom complexes
  `HomComplex P (resC φ J) ≅ HomComplex (extC φ P) J` induced by the extension–restriction of
  scalars adjunction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.AffineExt

attribute [local instance 10000] HasDerivedCategory.standard

section Generic

variable {C : Type*} [Category C] [Preadditive C]

/-- The degree `p` component of the morphism `K ⟶ L⟦n⟧` corresponding to a degree `n` cocycle
`z` is the component `z.v p (p + n)` followed by the identification `(L⟦n⟧).X p ≅ L.X (p + n)`. -/
lemma equivHomShift_symm_f {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) (p : ℤ) :
    (Cocycle.equivHomShift.symm z).f p =
      (z : Cochain K L n).v p (p + n) rfl ≫ (L.shiftFunctorObjXIso n p (p + n) rfl).inv :=
  rfl

end Generic

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

/-- Extension of scalars on cochain complexes. -/
abbrev extC : CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ :=
  (ModuleCat.extendScalars.{u, u, u} φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction of scalars on cochain complexes. -/
abbrev resC (φ : A ⟶ B) :
    CochainComplex (ModuleCat.{u} B) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  (ModuleCat.restrictScalars.{u} φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The Hom complex out of an extension of scalars is the Hom complex into a restriction of
scalars. -/
def adjHomComplexIso (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (J : CochainComplex (ModuleCat.{u} B) ℤ) :
    CochainComplex.HomComplex P ((resC φ).obj J) ≅ CochainComplex.HomComplex ((extC φ).obj P) J :=
  CochainComplex.HomComplex.homComplexIsoOfAddEquiv
    (fun p q => ((ModuleCat.extendRestrictScalarsAdj φ.hom).homAddEquiv (P.X p) (J.X q)).symm)
    (fun _ q q' f => (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv_naturality_right_symm
      f (J.d q q'))
    (fun p' p _ f => (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv_naturality_left_symm
      (P.d p' p) f)

end AlgebraicGeometry.AffineExt
