module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.GeneratedInDegreeOne

/-!
# The sections of `Sym^n(E)` over an affine open are `Sym^n` of the sections

`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E` is the degreewise sheafification of
the sectionwise symmetric algebra, so over a general open its sections are not the symmetric
powers of the sections of `E`: a section of the sheafification is only *locally* a sum of
products. **Over an affine open, for `E` quasi-coherent, it is**, and that is the content of this
file: the sheafification unit

`Sym^n_{Γ(X, V)}(Γ(E, V)) ⟶ Γ(V, Sym^n(E))`

is bijective. Together with the multiplication and unit laws of the sheafification unit
(`Stacks.SymGraded.symmetricAlgebra_mul_unit` and `symmetricAlgebra_one_eval`) this identifies the
graded ring of sections of `Sym(E)` over an affine open with the symmetric algebra of `Γ(E, V)`,
which is the chart-level input of relative-`Proj` base change: the chart of `𝐏(E)` over `V` is
`Proj` of that ring.

## Relation to the free case

`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/Free.lean` proves the same identification
for
a **finite free** `E`, and over *every* open rather than only the affine ones, by a different and
much cheaper route: for a free sheaf the sectionwise symmetric power is already a sheaf
(`Stacks.SymGraded.isSheaf_symPow_free`), so the sheafification unit is invertible outright and
`Stacks.SymGraded.freePieceEquiv` is `PresheafOfModules.unitAppEquiv`. That route is unavailable
here — for a general quasi-coherent `E` the sectionwise symmetric power is genuinely not a sheaf —
and the restriction to affine opens is not an artefact of the proof but a necessary hypothesis.

## Main results

* `Stacks.SymGraded.bijective_sheafifyUnit_app_of_isAffineOpen`: **the sheafification unit is
  bijective on the sections over an affine open.** This is the arbitrary-`E` counterpart of
  `Stacks.SymGraded.freePieceEquiv`.
* `Stacks.SymGraded.symPieceEquiv`: that bijection as an equivalence, with
  `symPieceEquiv_apply` identifying it with the unit, so the multiplication and unit laws of the
  unit apply to it unchanged.

## Implementation notes

The surjectivity half is `Stacks.SymGraded.surjective_sheafifyUnit_app_of_isAffineOpen`, used
for generation in degree one, and the chain below is that proof with every transfer replaced by
its bijective counterpart from
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafificationUnitSections.lean`. The two inputs,
`Stacks.AffineBaseChange.bijective_toTildeₗ_basicOpen` and
`Stacks.SymGraded.AffinePieces.bijective_toPieceₗ_basicOpen`, are bijectivity statements on basic
opens; the relevant basic open is the basic open of `1`, which is `⊤`.

**The ring is `Γ(X, V)` throughout.** The sections of
`Stacks.SymGraded.siteGradedPiece E.val n` over `V` are
`Stacks.SymGraded.gradedPiece (R := Γ(X, V)) Γ(E, V) n` by `rfl`
(`Stacks.SymGraded.siteGradedPiece_obj`), and `Stacks.SymGraded.AffinePieces.pieceAt` is that same
module over that same ring.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)

## Relation to Tag 01CG

This is the third assertion of Tag 01CG over an affine base, read on sections;
`Stacks.SymGraded.AffinePieces.sheafificationIsoTilde` is that assertion as an isomorphism of
sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PresheafOfModules
open Stacks.AlgebraicGeometry.ImmersionRestrict

namespace Stacks.SymGraded

universe u

open Stacks.SymGraded.AffinePieces

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] {V : X.Opens}
  (hV : IsAffineOpen V) (n : ℤ)

omit [E.IsQuasicoherent] hV in
/-- **The comparison with the associated sheaf is bijective on the global sections of
`Spec Γ(X, V)`**: `⊤` is the basic open of `1`. -/
theorem bijective_toTilde_app_top : Function.Bijective
    (Hom.app (Stacks.AffineBaseChange.toTilde (pieceAt E V n))
      (op (⊤ : (Spec Γ(X, V)).Opens))) := by
  have h := Stacks.AffineBaseChange.bijective_toTildeₗ_basicOpen (pieceAt E V n) (1 : Γ(X, V))
  rw [show Stacks.AffineBaseChange.specBasicOpen (1 : Γ(X, V)) =
    (⊤ : (Spec Γ(X, V)).Opens) from PrimeSpectrum.basicOpen_one] at h
  exact h

include hV in
/-- **The comparison of the base-change presheaf with the sectionwise symmetric power is bijective
on the global sections of `Spec Γ(X, V)`.** -/
theorem bijective_toPiece_app_top : Function.Bijective
    (Hom.app (toPiece E hV n) (op (⊤ : (Spec Γ(X, V)).Opens))) := by
  have h := bijective_toPieceₗ_basicOpen E hV n (1 : Γ(X, V))
  rw [show Stacks.AffineBaseChange.specBasicOpen (1 : Γ(X, V)) =
    (⊤ : (Spec Γ(X, V)).Opens) from PrimeSpectrum.basicOpen_one] at h
  exact h

omit [E.IsQuasicoherent] hV in
/-- **The sheafification unit of the base-change presheaf is bijective on the global sections of
`Spec Γ(X, V)`.** -/
theorem bijective_sheafifyUnit_app_baseChange_top :
    Function.Bijective (Hom.app (sheafifyUnit (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
      (Stacks.AffineBaseChange.presheaf (pieceAt E V n)))
      (op (⊤ : (Spec Γ(X, V)).Opens))) :=
  (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff
    (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj) (tilde (pieceAt E V n))
    (Stacks.AffineBaseChange.toTilde (pieceAt E V n))
    (Stacks.AffineBaseChange.isLocallyInjective_toTilde (pieceAt E V n))
    (Stacks.AffineBaseChange.isLocallySurjective_toTilde (pieceAt E V n))
    (op (⊤ : (Spec Γ(X, V)).Opens))).2 (bijective_toTilde_app_top E n)

include hV in
/-- **The sheafification unit of the restriction along `fromSpec` of the sectionwise degree-`n`
symmetric power is bijective on the global sections of `Spec Γ(X, V)`.** -/
theorem bijective_sheafifyUnit_app_restrict_top :
    Function.Bijective (Hom.app (sheafifyUnit (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
      ((presheafRestrict hV.fromSpec).obj (siteGradedPiece E.val n)))
      (op (⊤ : (Spec Γ(X, V)).Opens))) :=
  Stacks.PresheafOfModules.bijective_sheafifyUnit_app_of_isLocallyBijective
    (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj) (toPiece E hV n)
    (isLocallyInjective_toPiece E hV n) (isLocallySurjective_toPiece E hV n)
    (op (⊤ : (Spec Γ(X, V)).Opens)) (bijective_sheafifyUnit_app_baseChange_top E n)
    (bijective_toPiece_app_top E hV n).2

include hV in
/-- **The sheafification unit of the sectionwise degree-`n` symmetric power of a quasi-coherent
module is bijective on the sections over an affine open.**

So `Γ(V, Sym^n(E))` *is* `Sym^n_{Γ(X, V)}(Γ(E, V))` for `V` affine. This is the arbitrary-`E`
counterpart of `Stacks.SymGraded.freePieceEquiv`, which gets the same conclusion over every open
for a finite free module because there the sectionwise symmetric power is already a sheaf. -/
theorem bijective_sheafifyUnit_app_of_isAffineOpen :
    Function.Bijective (Hom.app
      (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n))
      (op V)) := by
  have h : Function.Bijective (Hom.app
      (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n))
      (op (hV.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens)))) := by
    have _hi := Stacks.AlgebraicGeometry.SheafifyRestrict.isLocallyInjective_sheafifyUnit
      (siteGradedPiece E.val n)
    have _hs := Stacks.AlgebraicGeometry.SheafifyRestrict.isLocallySurjective_sheafifyUnit
      (siteGradedPiece E.val n)
    exact (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff
      (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
      ((Scheme.Modules.restrictFunctor hV.fromSpec).obj
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
          (siteGradedPiece E.val n)))
      ((presheafRestrict hV.fromSpec).map
        (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n)))
      (isLocallyInjective_presheafRestrict_map hV.fromSpec
        (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n)))
      (isLocallySurjective_presheafRestrict_map hV.fromSpec
        (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n)))
      (op (⊤ : (Spec Γ(X, V)).Opens))).1 (bijective_sheafifyUnit_app_restrict_top E hV n)
  rw [show hV.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens) = V from
    (Scheme.Hom.image_top_eq_opensRange hV.fromSpec).trans hV.opensRange_fromSpec] at h
  exact h

include hV in
/-- **`Sym^n` of the sections of `E` over an affine open is the sections of `Sym^n(E)` there**, as
an equivalence given by the sheafification unit. -/
def symPieceEquiv : (siteGradedPiece E.val n).obj (op V) ≃
    ((Scheme.Modules.symmetricAlgebra X E).piece n).val.obj (op V) :=
  Equiv.ofBijective _ (bijective_sheafifyUnit_app_of_isAffineOpen E hV n)

include hV in
/-- The equivalence `symPieceEquiv E hV n` sends a section `x` of `Sym^n` of the sections of `E`
over `V` to its image under the sheafification unit. -/
@[simp]
theorem symPieceEquiv_apply (x : (siteGradedPiece E.val n).obj (op V)) :
    symPieceEquiv E hV n x =
      Hom.app (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
        (siteGradedPiece E.val n)) (op V) x := rfl

end Stacks.SymGraded

end
