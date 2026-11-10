module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute

/-!
# Charts of a relative affine space

The relative affine space `𝔸(n; X)` of [Stacks, Tag 0G47] is covered by the parts lying over
the affine opens of `X`, and the part over an affine open `U = Spec A` is the affine open
`Spec A[xᵢ]` of `𝔸(n; X)`. This module builds that chart structure: the identification of
`𝔸(n; U)` with the preimage of `U` in `𝔸(n; X)`, the affineness of that preimage, and the ring
isomorphism of its functions with a polynomial ring.

## Main definitions

* `AlgebraicGeometry.AffineSpace.chart` is the preimage of an open `U ⊆ X` in `𝔸(n; X)`.
* `AlgebraicGeometry.AffineSpace.chartIso` identifies `𝔸(n; U)` with that preimage.

## Main results

* `AlgebraicGeometry.AffineSpace.isAffineOpen_chart`: the chart over an affine open is affine.

## Implementation notes

Everything is deduced from `AlgebraicGeometry.AffineSpace.isPullback_map`, which presents
`𝔸(n; U) → 𝔸(n; X)` as the base change of `U → X` along `𝔸(n; X) → X`: being an open immersion
is stable under base change, and the range of a base change of an open immersion is the
preimage of its range.

## References

* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.AffineSpace

variable {X : Scheme.{u}} (n : Type u)

/-- The part of the relative affine space `𝔸(n; X)` lying over an open `U` of `X`. -/
def chart (U : X.Opens) : (𝔸(n; X)).Opens := (𝔸(n; X) ↘ X) ⁻¹ᵁ U

variable {n}

/-- The projection of `𝔸(n; U)` to `𝔸(n; X)` is an open immersion: it is the base change of
the open immersion `U → X`. -/
instance isOpenImmersion_map_ι (U : X.Opens) : IsOpenImmersion (map n U.ι) :=
  MorphismProperty.of_isPullback (isPullback_map (n := n) U.ι).flip inferInstance

/-- The image of `𝔸(n; U)` in `𝔸(n; X)` is the chart over `U`. -/
theorem range_map_ι (U : X.Opens) :
    Set.range ⇑(map n U.ι) = (chart n U : Set (𝔸(n; X))) := by
  have h := isPullback_map (n := n) U.ι
  have hfst : ∀ z : 𝔸(n; U.toScheme),
      (pullback.fst (𝔸(n; X) ↘ X) U.ι) (h.isoPullback.hom z) = (map n U.ι) z := fun z =>
    congrArg (fun m : 𝔸(n; U.toScheme) ⟶ 𝔸(n; X) => m z) h.isoPullback_hom_fst
  have hsurj : Function.Surjective ⇑h.isoPullback.hom :=
    (Scheme.homeoOfIso h.isoPullback).surjective
  have hrange : Set.range ⇑(map n U.ι) =
      Set.range ⇑(pullback.fst (𝔸(n; X) ↘ X) U.ι) :=
    (congrArg Set.range (funext hfst)).symm.trans (hsurj.range_comp _)
  rw [hrange, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
  rfl

/-- **`𝔸(n; U) = 𝔸(n; X)|_U`.** The relative affine space over an open of `X` is the chart of
the relative affine space over `X` lying above that open. -/
def chartIso (U : X.Opens) : 𝔸(n; U.toScheme) ≅ (chart n U).toScheme :=
  IsOpenImmersion.isoOfRangeEq (map n U.ι) (chart n U).ι
    ((range_map_ι U).trans (Scheme.Opens.range_ι _).symm)

/-- Composing `chartIso U` with the inclusion of the chart into `𝔸(n; X)` gives the projection
`𝔸(n; U) → 𝔸(n; X)`. -/
@[reassoc (attr := simp)]
theorem chartIso_hom_ι (U : X.Opens) :
    (chartIso U).hom ≫ (chart n U).ι = map n U.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The chart over an affine open is an affine scheme. -/
instance isAffine_chart (U : X.affineOpens) : IsAffine (chart n U.1).toScheme :=
  haveI : IsAffine U.1.toScheme := U.2
  .of_isIso (chartIso (n := n) U.1).inv

/-- **The chart over an affine open is an affine open.** -/
theorem isAffineOpen_chart (U : X.affineOpens) : IsAffineOpen (chart n U.1) :=
  isAffine_chart U

/-- The chart is monotone in the open of the base. -/
theorem chart_mono {U V : X.Opens} (h : U ≤ V) : chart n U ≤ chart n V :=
  fun _ hx => h hx

variable (n) in
/-- **The charts over an open cover of the base cover the relative affine space.** -/
theorem iUnion_coe_chart {ι : Sort*} (W : ι → X.Opens) (hW : ⨆ i, W i = ⊤) :
    (⋃ i, (chart n (W i) : Set 𝔸(n; X))) = Set.univ := by
  have hpre : ∀ i, ((chart n (W i) : Set 𝔸(n; X))) =
      ⇑(𝔸(n; X) ↘ X) ⁻¹' (W i : Set X) := fun _ => rfl
  simp only [hpre, ← Set.preimage_iUnion, ← TopologicalSpace.Opens.coe_iSup, hW]
  simp

/-! ### The functions on a relative affine space over an affine base -/

section Gamma

variable (n : Type u) (S : Scheme.{u}) [IsAffine S]

/-- **The functions on `𝔸(n; S)` over an affine base.** For `S` affine the ring of global
functions of `𝔸(n; S)` is the polynomial ring `Γ(S, ⊤)[xᵢ]`. -/
def ΓIso : Γ(𝔸(n; S), ⊤) ≅ CommRingCat.of (MvPolynomial n Γ(S, ⊤)) where
  hom := (isoOfIsAffine n S).inv.appTop ≫ (Scheme.ΓSpecIso _).hom
  inv := (Scheme.ΓSpecIso _).inv ≫ (isoOfIsAffine n S).hom.appTop
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id,
      Category.id_comp, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc ((isoOfIsAffine n S).hom.appTop),
      ← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.id_comp,
      Iso.inv_hom_id]

variable {n S}

/-- The identification of `Γ(𝔸(n; S), ⊤)` with a polynomial ring sends the `i`-th coordinate
function to the `i`-th variable. -/
@[simp]
theorem ΓIso_hom_coord (i : n) :
    (ΓIso n S).hom (coord S i) = MvPolynomial.X i := by
  change (Scheme.ΓSpecIso _).hom ((isoOfIsAffine n S).inv.appTop (coord S i)) = _
  rw [isoOfIsAffine_inv_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

/-- Pulling a function back from the base and reading it in the polynomial ring is taking the
corresponding constant polynomial. -/
theorem appTop_comp_ΓIso_hom :
    (𝔸(n; S) ↘ S).appTop ≫ (ΓIso n S).hom =
      CommRingCat.ofHom (MvPolynomial.C (σ := n) (R := Γ(S, ⊤))) := by
  have hinvmor : S.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(S, ⊤)).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso Γ(S, ⊤)).hom, Iso.inv_hom_id, ← Scheme.toSpecΓ_appTop,
      ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop]
  change (𝔸(n; S) ↘ S).appTop ≫ (isoOfIsAffine n S).inv.appTop ≫ (Scheme.ΓSpecIso _).hom = _
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, isoOfIsAffine_inv_over,
    Scheme.Hom.comp_appTop, hinvmor, Category.assoc, Scheme.ΓSpecIso_naturality,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable (n) in
/-- **The projection `𝔸(n; S) → 𝔸(n; T)` pulls back a function of `T` to the corresponding
function of `S`.** This is `AlgebraicGeometry.AffineSpace.map_over`, read on global functions. -/
theorem map_appTop_over_appTop {S T : Scheme.{u}} (f : S ⟶ T) (a : Γ(T, ⊤)) :
    (map n f).appTop ((𝔸(n; T) ↘ T).appTop a) = (𝔸(n; S) ↘ S).appTop (f.appTop a) := by
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
    congrArg (fun m : 𝔸(n; S) ⟶ T => m.appTop a) (map_over (n := n) f)

/-- The identification of `Γ(𝔸(n; S), ⊤)` with a polynomial ring sends a function pulled back
from the base to the corresponding constant. -/
@[simp]
theorem ΓIso_hom_appTop (a : Γ(S, ⊤)) :
    (ΓIso n S).hom ((𝔸(n; S) ↘ S).appTop a) = MvPolynomial.C a := by
  rw [← CommRingCat.comp_apply, appTop_comp_ΓIso_hom]
  rfl

end Gamma

end AlgebraicGeometry.AffineSpace

end
