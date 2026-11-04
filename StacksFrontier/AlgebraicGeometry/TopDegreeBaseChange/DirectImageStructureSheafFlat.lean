module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimension
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafEilenbergWatts
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafSurjectivityBaseChange

/-!
# Flatness of `f_* 𝒪_X` over the base

Let `X ⟶ Y ⟶ S` be a commutative triangle of schemes with `X ⟶ S` flat, `f : X ⟶ Y` proper,
`dim(X_y) ≤ 1` for every `y ∈ Y`, and `R¹ f_* 𝒪_X = 0`. Then `f_* 𝒪_X` is flat over `S`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.flat_of_flat_globalSections`: flatness of
  `Γ(W, ⊤)` over the base ring of `W` transported along a ring isomorphism that carries the
  structure morphism to a prescribed ring map.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.appTop_resLE_isoSpec`: the structure morphism of
  `f⁻¹U` over `Spec Γ(S, V)` reads at `⊤` as `(f ≫ q).appLE V (f⁻¹U)`, through `topIso` and the
  affine identification of `V`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isFlatOver_directImageStructureSheaf`:
  `f_* 𝒪_X` is flat over `S`.

## References

* [Stacks Project, Tag 0E7K](https://stacks.math.columbia.edu/tag/0E7K)
* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] baseSectionsAlgebra

noncomputable section

/-! ### Transporting the affine case -/

/-- The algebra map of `Stacks.Cohomology.AffineBase.baseSectionsAlgebra` is the structure
morphism read at the open `⊤`. -/
theorem algebraMap_baseSectionsAlgebra_apply {R : Type u} [CommRing R]
    (W : Over (Spec (CommRingCat.of R))) (r : R) :
    algebraMap R Γ(W.left, ⊤) r =
      (W.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
  show (W.left.presheaf.map (homOfLE (le_refl (⊤ : W.left.Opens))).op).hom
    ((W.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
  rw [show (homOfLE (le_refl (⊤ : W.left.Opens))).op = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id]
  rfl

/-- If `e : Γ(W, ⊤) ≅ B` carries the structure morphism of `W` at `⊤` to a ring map
`φ : R →+* B` and `Γ(W, ⊤)` is flat over `R`, then `B` is flat over `R` for the `R`-action through
`φ`. -/
theorem flat_of_flat_globalSections {R : Type u} [CommRing R]
    (W : Over (Spec (CommRingCat.of R))) {B : CommRingCat.{u}}
    (e : Γ(W.left, ⊤) ≅ B) (φ : R →+* B)
    (he : ∀ r : R, (e.hom).hom (algebraMap R Γ(W.left, ⊤) r) = φ r)
    (h : Module.Flat R (Γ(W.left, ⊤) : Type u)) :
    letI := Module.compHom (B : Type u) φ
    Module.Flat R (B : Type u) := by
  let := Module.compHom (B : Type u) φ
  refine Module.Flat.of_linearEquiv
    (AddEquiv.toLinearEquiv e.commRingCatIsoToRingEquiv.toAddEquiv fun r x ↦ ?_).symm
  show (e.hom).hom (algebraMap R Γ(W.left, ⊤) r * x) = φ r * (e.hom).hom x
  rw [map_mul, he]

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
  (U : Y.Opens) (V : S.Opens) (hV : IsAffineOpen V) (hP : f ⁻¹ᵁ U ≤ (f ≫ q) ⁻¹ᵁ V)

/-- Composing the restriction `(f ≫ q).resLE V (f⁻¹U)` with the affine identification of `V`
gives a morphism `(f⁻¹U).toScheme ⟶ Spec Γ(S, V)`, and through
`AlgebraicGeometry.Scheme.Opens.topIso` its effect on global sections is
`(f ≫ q).appLE V (f⁻¹U)`. -/
theorem appTop_resLE_isoSpec :
    (Scheme.ΓSpecIso Γ(S, V)).inv ≫
        ((f ≫ q).resLE V (f ⁻¹ᵁ U) hP ≫ hV.isoSpec.hom).appTop ≫ (f ⁻¹ᵁ U).topIso.hom =
      (f ≫ q).appLE V (f ⁻¹ᵁ U) hP := by
  rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end

/-! ### Flatness of the direct image of the structure sheaf -/

section Main

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- Let `X ⟶ Y ⟶ S` be a commutative triangle of schemes with `X ⟶ S` flat, let `f : X ⟶ Y` be
proper with `dim(X_y) ≤ 1` for every `y ∈ Y`, and suppose `R¹ f_* 𝒪_X = 0`. Then `f_* 𝒪_X` is
flat over `S`. -/
@[stacks 0E7K "clause (a): flatness of `f_* 𝒪_X` over the base"]
theorem isFlatOver_directImageStructureSheaf (hcoh : CohomologyVanishesAboveOne.{u})
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) [Flat (f ≫ q)] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f)) :
    IsFlatOver q.toLRSHom.toShHom (directImageStructureSheaf f) := by
  refine ((isFlatOver_tfae q (directImageStructureSheaf f)).out 2 1).mp ?_
  intro U hU V hV hUV _
  have hP : f ⁻¹ᵁ U ≤ (f ≫ q) ⁻¹ᵁ V := fun x hx ↦ hUV hx
  have _ : IsAffine U.toScheme := hU
  have hcomp : (f ≫ q).appLE V (f ⁻¹ᵁ U) hP = q.appLE V U hUV ≫ f.app U := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have _ : Flat (Over.mk ((f ≫ q).resLE V (f ⁻¹ᵁ U) hP ≫ hV.isoSpec.hom)).hom := by
    dsimp only [Over.mk_hom]
    infer_instance
  refine flat_of_flat_globalSections
    (Over.mk ((f ≫ q).resLE V (f ⁻¹ᵁ U) hP ≫ hV.isoSpec.hom))
    (f ⁻¹ᵁ U).topIso (q.appLE V U hUV ≫ f.app U).hom (fun r ↦ ?_)
    (flat_globalSections_of_isZero_firstDirectImage (Γ(S, V) : Type u)
      (Over.mk ((f ≫ q).resLE V (f ⁻¹ᵁ U) hP ≫ hV.isoSpec.hom)) hcoh (f ∣_ U)
      (topologicalKrullDim_fiber_morphismRestrict_le f U 1 fun y _ ↦ hdim y)
      (isZero_firstDirectImage_structureSheaf_restrict f U hR))
  rw [algebraMap_baseSectionsAlgebra_apply, ← hcomp]
  exact congrArg (fun k : CommRingCat.Hom _ _ ↦ k.hom r)
    (appTop_resLE_isoSpec f q U V hV hP)

end

end Main

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
