module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseProper
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackNaturalityInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductProjections
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductSymmetry
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityTestMap
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafComapMap
import all StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence

/-!
# The exterior product commutes with every cap product

Let `k` be a field, let `X` be a scheme locally of finite type over `k`, let `u : Y ⟶ Z` be a
morphism of schemes locally of finite type over `k` and let `c ∈ A^p(Y ⟶ Z)` be a bivariant
class. **Stacks 0FBY** asserts

  `α × (c ∩ β) = c ∩ (α × β)`   in   `CH_{n + (m - p)}(X ×_k Y)`

for every `α ∈ CH_n(X)` and every `β ∈ CH_m(Z)`. The equation is
`Stacks.Chow.CommutesExteriorProductCap`, and for `α` the fundamental class of an integral scheme
flat over the base it is
`Stacks.Chow.commutesExteriorProductCapAt_fundamentalChowClass_of_invertible`. This module proves
it for every `α`.

The class `α` is the class of a cycle `∑ nᵢ [Zᵢ]`, a locally finite sum over integral closed
subschemes `Zᵢ ⊆ X`. The coproduct `W = ∐ Zᵢ` is proper over `X`, and the cycle
`α' = ∑ nᵢ [Zᵢ]` on `W` pushes forward to `α`. Two facts carry the equation from the pieces to
`X`:

* **proper pushforward in the first variable**: `(π × 1)_*(α' × γ) = α × γ` for the morphism
  `π : W ⟶ X`, so that both sides of the equation for `α` are the pushforwards along `π × 1` of
  the two sides for `α'`, the right-hand side by the proper axiom of Stacks 0B76 for `c`;
* **restriction in the first variable**: `(α' × γ)|_{V ×_k Y} = α'|_V × γ` for an open
  immersion `V ⟶ W`, so that both sides of the equation for `α'` restrict to the two sides for
  the restriction of `α'` to a summand `Zᵢ`, the right-hand side by the flat axiom of Stacks 0B76
  in relative dimension zero.

Since `W ×_k Y` is the disjoint union of the open and closed pieces `Zᵢ ×_k Y`, a class on it is
determined by its restrictions to them, and on `Zᵢ` the class `α'` restricts to `nᵢ [Zᵢ]`, for
which the equation is the fundamental-class case: an integral scheme of finite type over a field
is flat over it of relative dimension its dimension.

The form with the cap product in the first variable, `(c ∩ ξ) × γ = c ∩ (ξ × γ)`, follows from
the symmetry of the exterior product.

## Main definitions

* `Stacks.Chow.exteriorProductFstMap` — the morphism `h × 1_Y : X' ×_S Y ⟶ X ×_S Y` induced by
  `h : X' ⟶ X`.
* `Stacks.Chow.exteriorCapFstIso` — the identification `Y ×_Z (Z ×_S X) ≅ Y ×_S X`.
* `Stacks.Chow.capExteriorProductFst` — the class `c ∩ (ξ × γ)` read on `Y ×_S X`.

## Main results

* `Stacks.Chow.exteriorProductWeight_fstMap_of_isOpenImmersion`,
  `Stacks.Chow.exteriorProductWeight_fstMap_of_isClosedImmersion` — the multiplicities of the
  exterior product are unchanged along `h × 1_Y` for `h` an open or a closed immersion.
* `Stacks.Chow.properPushforward_exteriorProduct_fstMap` — proper pushforward in the first
  variable of the exterior product of cycles, along a proper morphism surjective on stalks that
  preserves the multiplicities.
* `Stacks.Chow.chowGroupRestrict_chowExteriorProduct` — restriction to an open subscheme in the
  first variable of the exterior product on Chow groups.
* `Stacks.Chow.commutesExteriorProductCapAt_of_properChowPushforward`,
  `Stacks.Chow.commutesExteriorProductCapAt_of_isOpenImmersion_cover` — the equation of Stacks
  0FBY descends along a proper pushforward and along a decomposition into open and closed pieces
  in the first variable.
* `Stacks.Chow.commutesExteriorProductCap_of_field` — **Stacks 0FBY** over a field.
* `Stacks.Chow.chowExteriorProduct_capTarget_eq_capExteriorProductFst_of_field` — Stacks 0FBY
  over a field with the cap product in the first variable.

## Implementation notes

The bivariant classes are those of `Stacks.Chow.BivariantClass` stated against the Gysin system
`Stacks.Chow.gysinSystemOfInvertible`, the only Gysin system carrying the first Chern class rule
of invertible modules; this is the system at which the fundamental-class case is available with
no hypothesis.

The proper pushforward identity is proved coefficientwise, through
`Stacks.Chow.properPushforward_eq_of_support_section`: a point of `X ×_k Y` in the support of
`α × γ` lifts to a unique point of `W ×_k Y` over the corresponding generic point of a summand,
uniqueness because `π` is surjective on stalks, and the multiplicities agree because `π × 1` is
the base change of a closed immersion on the open summand `Zᵢ ×_k Y`. No general proper
naturality of the exterior product in its first variable is needed, only this case.

## References

* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The base change of a morphism in the first factor -/

section FstMap

variable {S X X' Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S) (h : X' ⟶ X)
  (hh : h ≫ f = f')

/-- The morphism `h × 1_Y : X' ×_S Y ⟶ X ×_S Y` induced by `h : X' ⟶ X` over `S`: the unique
morphism whose first projection is `h` after the first projection of `X' ×_S Y` and whose second
projection is the second projection of `X' ×_S Y`. -/
def exteriorProductFstMap : (pullback f' g : Scheme.{u}) ⟶ (pullback f g : Scheme.{u}) :=
  pullback.lift (pullback.fst f' g ≫ h) (pullback.snd f' g)
    (by rw [Category.assoc, hh]; exact pullback.condition)

/-- The first projection of `h × 1_Y` is `h` after the first projection of `X' ×_S Y`. -/
@[reassoc (attr := simp)]
theorem exteriorProductFstMap_fst :
    exteriorProductFstMap f g f' h hh ≫ pullback.fst f g = pullback.fst f' g ≫ h :=
  pullback.lift_fst _ _ _

/-- The second projection of `h × 1_Y` is the second projection of `X' ×_S Y`. -/
@[reassoc (attr := simp)]
theorem exteriorProductFstMap_snd :
    exteriorProductFstMap f g f' h hh ≫ pullback.snd f g = pullback.snd f' g :=
  pullback.lift_snd _ _ _

/-- On points, the first projection of the image of `w` under `h × 1_Y` is `h` of the first
projection of `w`. -/
@[simp]
theorem exteriorProductFstMap_base_fst (w : (pullback f' g : Scheme.{u})) :
    (pullback.fst f g).base ((exteriorProductFstMap f g f' h hh).base w) =
      h.base ((pullback.fst f' g).base w) := by
  rw [← Scheme.Hom.comp_apply, exteriorProductFstMap_fst, Scheme.Hom.comp_apply]

/-- On points, the second projection of the image of `w` under `h × 1_Y` is the second
projection of `w`. -/
@[simp]
theorem exteriorProductFstMap_base_snd (w : (pullback f' g : Scheme.{u})) :
    (pullback.snd f g).base ((exteriorProductFstMap f g f' h hh).base w) =
      (pullback.snd f' g).base w := by
  rw [← Scheme.Hom.comp_apply, exteriorProductFstMap_snd]

/-- `h × 1_Y` is a morphism over `S`. -/
theorem exteriorProductFstMap_comp_structureMorphism :
    exteriorProductFstMap f g f' h hh ≫ (pullback.fst f g ≫ f) = pullback.fst f' g ≫ f' := by
  rw [exteriorProductFstMap_fst_assoc, hh]

/-- `h × 1_Y` is the base change of `h` along the first projection of `X ×_S Y`. -/
theorem isPullback_exteriorProductFstMap :
    IsPullback (exteriorProductFstMap f g f' h hh) (pullback.fst f' g) (pullback.fst f g) h := by
  refine IsPullback.of_right ?_ (exteriorProductFstMap_fst f g f' h hh)
    (IsPullback.of_hasPullback f g).flip
  rw [exteriorProductFstMap_snd, hh]
  exact (IsPullback.of_hasPullback f' g).flip

/-- `h × 1_Y` is an open immersion when `h` is, being a base change of it. -/
instance isOpenImmersion_exteriorProductFstMap [IsOpenImmersion h] :
    IsOpenImmersion (exteriorProductFstMap f g f' h hh) :=
  MorphismProperty.of_isPullback (isPullback_exteriorProductFstMap f g f' h hh).flip inferInstance

/-- `h × 1_Y` is a closed immersion when `h` is, being a base change of it. -/
instance isClosedImmersion_exteriorProductFstMap [IsClosedImmersion h] :
    IsClosedImmersion (exteriorProductFstMap f g f' h hh) :=
  MorphismProperty.of_isPullback (isPullback_exteriorProductFstMap f g f' h hh).flip inferInstance

/-- `h × 1_Y` is proper when `h` is, being a base change of it. -/
instance isProper_exteriorProductFstMap [IsProper h] :
    IsProper (exteriorProductFstMap f g f' h hh) :=
  MorphismProperty.of_isPullback (isPullback_exteriorProductFstMap f g f' h hh).flip inferInstance

/-- `h × 1_Y` is surjective on stalks when `h` is, being a base change of it. -/
instance surjectiveOnStalks_exteriorProductFstMap [SurjectiveOnStalks h] :
    SurjectiveOnStalks (exteriorProductFstMap f g f' h hh) :=
  MorphismProperty.of_isPullback (isPullback_exteriorProductFstMap f g f' h hh).flip inferInstance

/-- The image of `h × 1_Y` is the inverse image of the image of `h`. -/
theorem range_exteriorProductFstMap :
    Set.range (exteriorProductFstMap f g f' h hh).base =
      (pullback.fst f g).base ⁻¹' Set.range h.base := by
  have hsq := isPullback_exteriorProductFstMap f g f' h hh
  have hfst : hsq.isoPullback.hom ≫ pullback.fst (pullback.fst f g) h =
      exteriorProductFstMap f g f' h hh := hsq.isoPullback_hom_fst
  have hsurj : Function.Surjective hsq.isoPullback.hom.base :=
    (Scheme.homeoOfIso hsq.isoPullback).surjective
  rw [← hfst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
    Set.image_univ]
  exact Scheme.Pullback.range_fst _ _

/-- The base change of a composite is the composite of the base changes. -/
theorem exteriorProductFstMap_comp {X'' : Scheme.{u}} (f'' : X'' ⟶ S) (h' : X'' ⟶ X')
    (hh' : h' ≫ f' = f'') :
    exteriorProductFstMap f' g f'' h' hh' ≫ exteriorProductFstMap f g f' h hh =
      exteriorProductFstMap f g f'' (h' ≫ h) (by rw [Category.assoc, hh, hh']) := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The base change `h × 1_Y` depends only on the morphism `h`. -/
theorem exteriorProductFstMap_congr {h' : X' ⟶ X} (e : h = h') (hh' : h' ≫ f = f') :
    exteriorProductFstMap f g f' h hh = exteriorProductFstMap f g f' h' hh' := by
  subst e
  rfl

/-- Over a morphism `π` that is surjective on stalks, a point of `X' ×_S Y` is determined by its
image in `X ×_S Y` and its first projection. -/
theorem exteriorProductFstMap_injective_of_fst_eq [SurjectiveOnStalks h]
    {w w' : (pullback f' g : Scheme.{u})}
    (himg : (exteriorProductFstMap f g f' h hh).base w =
      (exteriorProductFstMap f g f' h hh).base w')
    (hfst : (pullback.fst f' g).base w = (pullback.fst f' g).base w') : w = w' := by
  have hsq := isPullback_exteriorProductFstMap f g f' h hh
  have hinj := (SurjectiveOnStalks.isEmbedding_pullback (pullback.fst f g) h).injective
  have hiso : Function.Injective hsq.isoPullback.hom.base :=
    (Scheme.homeoOfIso hsq.isoPullback).injective
  refine hiso (hinj ?_)
  simp only [Prod.mk.injEq]
  constructor
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsq.isoPullback_hom_fst]
    exact himg
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsq.isoPullback_hom_snd]
    exact hfst

/-- A point of `X ×_S Y` and a point of `X'` over the same point of `X` come from a point of
`X' ×_S Y`. -/
theorem exists_exteriorProductFstMap_eq (z : (pullback f g : Scheme.{u})) (x' : X')
    (hz : (pullback.fst f g).base z = h.base x') :
    ∃ w : (pullback f' g : Scheme.{u}), (exteriorProductFstMap f g f' h hh).base w = z ∧
      (pullback.fst f' g).base w = x' := by
  have hsq := isPullback_exteriorProductFstMap f g f' h hh
  obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback z x' hz
  refine ⟨hsq.isoPullback.inv.base t, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_fst]
    exact ht1
  · rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd]
    exact ht2

end FstMap

/-! ### Multiplicities along the base change of a closed or an open immersion -/

/-- The inverse image under `h × 1_Y` of the product ideal of `h x'` and `y` is the product ideal
of `x'` and `y`, as soon as the reduced closure of `h x'` pulls back to that of `x'`. -/
private theorem comap_exteriorProductIdeal_fstMap {S X X' Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X' ⟶ S) (h : X' ⟶ X) (hh : h ≫ f = f') (x' : X') (y : Y)
    (hx : (integralComponentAt (h.base x')).comap h = integralComponentAt x') :
    (exteriorProductIdeal f g (h.base x') y).comap (exteriorProductFstMap f g f' h hh) =
      exteriorProductIdeal f' g x' y := by
  simp only [exteriorProductIdeal, Scheme.IdealSheafData.comap_sup,
    ← Scheme.IdealSheafData.comap_comp, exteriorProductFstMap_fst, exteriorProductFstMap_snd]
  rw [Scheme.IdealSheafData.comap_comp _ (pullback.fst f' g) h]
  rw [show Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({h.base x'} : Set X)) =
    integralComponentAt (h.base x') from rfl, hx]
  rfl

/-- **The exterior product multiplicity along the base change of an open immersion.** For an
open immersion `m : X' ⟶ X` over the base, the multiplicity of a point of `X' ×_S Y` in the
product of the reduced closures of `x'` and `y` is that of its image in `X ×_S Y` in the product
of the reduced closures of `m x'` and `y`: the inverse image of the second product along `m × 1`
is the first, and the coefficient of the cycle of a closed subscheme does not see an open
immersion of the ambient scheme. -/
theorem exteriorProductWeight_fstMap_of_isOpenImmersion (C : ChowSituation.{u})
    {X X' Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (f' : X' ⟶ C.S) [LocallyOfFiniteType f'] (m : X' ⟶ X)
    [IsOpenImmersion m] (hm : m ≫ f = f') (j : ℤ) (x' : X') (y : Y)
    (w : (pullback f' g : Scheme.{u})) :
    exteriorProductWeight C f g j (m.base x') y ((exteriorProductFstMap f g f' m hm).base w) =
      exteriorProductWeight C f' g j x' y w := by
  have hideal := comap_exteriorProductIdeal_fstMap f g f' m hm x' y
    (comap_integralComponentAt_of_isOpenImmersion m x')
  unfold exteriorProductWeight
  rw [← closedSubschemeCycleCoeff_congr C (pullback.fst f' g ≫ f') hideal j w]
  exact (closedSubschemeCycleCoeff_comap_of_isOpenImmersion C (pullback.fst f g ≫ f)
    (pullback.fst f' g ≫ f') _ (exteriorProductFstMap_comp_structureMorphism f g f' m hm) _ j
    w).symm

/-- The reduced closure of the image of a point under a closed immersion pulls back to the
reduced closure of the point. -/
theorem comap_integralComponentAt_of_isClosedImmersion {A B : Scheme.{u}} (j : A ⟶ B)
    [IsClosedImmersion j] (a : A) :
    (integralComponentAt (j.base a)).comap j = integralComponentAt a := by
  rw [← map_integralComponentAt, Scheme.IdealSheafData.comap_map_of_isClosedImmersion]

/-- **The exterior product multiplicity along the base change of a closed immersion.** For a
closed immersion `v : X' ⟶ X` over the base, the multiplicity of a point of `X' ×_S Y` in the
product of the reduced closures of `x'` and `y` is that of its image in `X ×_S Y` in the product
of the reduced closures of `v x'` and `y`: the second product lies in the image of `v × 1` and
pulls back to the first. -/
theorem exteriorProductWeight_fstMap_of_isClosedImmersion (C : ChowSituation.{u})
    {X X' Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (f' : X' ⟶ C.S) [LocallyOfFiniteType f'] (v : X' ⟶ X)
    [IsClosedImmersion v] (hv : v ≫ f = f') (j : ℤ) (x' : X') (y : Y)
    (w : (pullback f' g : Scheme.{u})) :
    exteriorProductWeight C f g j (v.base x') y ((exteriorProductFstMap f g f' v hv).base w) =
      exteriorProductWeight C f' g j x' y w := by
  have hideal := comap_exteriorProductIdeal_fstMap f g f' v hv x' y
    (comap_integralComponentAt_of_isClosedImmersion v x')
  have hker : (exteriorProductFstMap f g f' v hv).ker ≤ exteriorProductIdeal f g (v.base x') y := by
    have hsq := isPullback_exteriorProductFstMap f g f' v hv
    have hfst : hsq.isoPullback.hom ≫ pullback.fst (pullback.fst f g) v =
        exteriorProductFstMap f g f' v hv := hsq.isoPullback_hom_fst
    rw [← hfst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    refine le_trans (Scheme.IdealSheafData.comap_mono _ ?_) le_sup_left
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    show closure ({v.base x'} : Set X) ⊆ (v.ker.support : Set X)
    rw [Scheme.Hom.support_ker]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨x', rfl⟩)
  unfold exteriorProductWeight
  rw [← closedSubschemeCycleCoeff_congr C (pullback.fst f' g ≫ f') hideal j w]
  have key : ∀ (q : (pullback f' g : Scheme.{u}) ⟶ C.S) [LocallyOfFiniteType q],
      q = exteriorProductFstMap f g f' v hv ≫ pullback.fst f g ≫ f →
      closedSubschemeCycleCoeff C q ((exteriorProductIdeal f g (v.base x') y).comap
          (exteriorProductFstMap f g f' v hv)).subschemeι j w =
        closedSubschemeCycleCoeff C (exteriorProductFstMap f g f' v hv ≫ pullback.fst f g ≫ f)
          ((exteriorProductIdeal f g (v.base x') y).comap
            (exteriorProductFstMap f g f' v hv)).subschemeι j w := by
    intro q _ hq; subst hq; rfl
  rw [key _ (exteriorProductFstMap_comp_structureMorphism f g f' v hv).symm]
  exact closedSubschemeCycleCoeff_comap_of_isClosedImmersion C (pullback.fst f g ≫ f)
    (exteriorProductFstMap f g f' v hv) _ hker j w

/-- **The exterior product multiplicity along the morphism out of a coproduct of closed
subschemes.** For closed immersions `vᵢ : Zᵢ ⟶ X`, the multiplicities of the exterior product on
`(∐ Zᵢ) ×_S Y` are those on `X ×_S Y` at the images under `(∐ vᵢ) × 1_Y`: on the summand
`Zᵢ ×_S Y`, which is open, that morphism is the base change of the closed immersion `vᵢ`. -/
theorem exteriorProductWeight_sigmaDesc (C : ChowSituation.{u}) {X Y : Scheme.{u}} {I : Type u}
    (Z : I → Scheme.{u}) (v : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (v i)] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sW : (∐ Z : Scheme.{u}) ⟶ C.S) [LocallyOfFiniteType sW]
    (hπ : Sigma.desc v ≫ sX = sW) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (j : ℤ)
    (z : (pullback sW sY : Scheme.{u})) :
    exteriorProductWeight C sW sY j ((pullback.fst sW sY).base z) ((pullback.snd sW sY).base z)
        z =
      exteriorProductWeight C sX sY j ((Sigma.desc v).base ((pullback.fst sW sY).base z))
        ((pullback.snd sW sY).base z)
        ((exteriorProductFstMap sX sY sW (Sigma.desc v) hπ).base z) := by
  obtain ⟨i, t0, ht0⟩ := exists_mem_range_sigmaι Z ((pullback.fst sW sY).base z)
  have hv : v i ≫ sX = Sigma.ι Z i ≫ sW := by rw [← hπ, ← Category.assoc, Sigma.ι_desc]
  obtain ⟨t, rfl, htfst⟩ := exists_exteriorProductFstMap_eq sW sY (Sigma.ι Z i ≫ sW) (Sigma.ι Z i)
    rfl z t0 ht0.symm
  have hcomp : (exteriorProductFstMap sX sY sW (Sigma.desc v) hπ).base
      ((exteriorProductFstMap sW sY (Sigma.ι Z i ≫ sW) (Sigma.ι Z i) rfl).base t) =
      (exteriorProductFstMap sX sY (Sigma.ι Z i ≫ sW) (v i) hv).base t := by
    rw [← Scheme.Hom.comp_apply, exteriorProductFstMap_comp,
      exteriorProductFstMap_congr sX sY (Sigma.ι Z i ≫ sW) _ _ (Sigma.ι_desc v i) hv]
  rw [exteriorProductFstMap_base_fst, exteriorProductFstMap_base_snd, htfst, hcomp,
    exteriorProductWeight_fstMap_of_isOpenImmersion, ← Scheme.Hom.comp_apply, Sigma.ι_desc,
    exteriorProductWeight_fstMap_of_isClosedImmersion]

/-! ### Proper pushforward in the first variable of the exterior product of cycles -/

/-- **The exterior product of cycles commutes with a proper pushforward in its first variable**,
for a proper morphism `π : W ⟶ X` surjective on stalks along which the exterior product
multiplicities are unchanged, and a cycle `a'` on `W` supported on a set of points mapped
bijectively onto the support of its pushforward `a`:

  `(π × 1_Y)_*(a' × c) = a × c`.

The hypotheses are those of `Stacks.Chow.properPushforward_eq_of_support_section`, which this
reduces to: a point of `X ×_S Y` in the support of `a × c` lifts to a unique point of `W ×_S Y`
over the corresponding point of the support of `a'`, uniqueness being
`AlgebraicGeometry.SurjectiveOnStalks.isEmbedding_pullback`. -/
theorem properPushforward_exteriorProduct_fstMap (C : ChowSituation.{u}) {X W Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : W ⟶ X) [IsProper π] [SurjectiveOnStalks π]
    (hπ : π ≫ sX = sW) (n m : ℤ)
    (hweight : ∀ z : (pullback sW sY : Scheme.{u}),
      exteriorProductWeight C sW sY (n + m) ((pullback.fst sW sY).base z)
          ((pullback.snd sW sY).base z) z =
        exteriorProductWeight C sX sY (n + m) (π.base ((pullback.fst sW sY).base z))
          ((pullback.snd sW sY).base z) ((exteriorProductFstMap sX sY sW π hπ).base z))
    (a : CycleGroup C sX n) (a' : CycleGroup C sW n)
    (e : ↥(Function.support (a.1 : X → ℤ)) → W) (he : ∀ i, π.base (e i) = (i : X))
    (ha' : ∀ i, a'.1 (e i) = a.1 (i : X)) (hsupp : ∀ x : W, a'.1 x ≠ 0 → ∃ i, x = e i)
    (c : CycleGroup C sY m) :
    properPushforward C (pullback.fst sW sY ≫ sW) (pullback.fst sX sY ≫ sX)
        (exteriorProductFstMap sX sY sW π hπ)
        (exteriorProductFstMap_comp_structureMorphism sX sY sW π hπ) (n + m)
        (exteriorProduct C sW sY n m a' c) =
      exteriorProduct C sX sY n m a c := by
  classical
  set F := exteriorProductFstMap sX sY sW π hπ with hF
  -- the coefficient identity at a point over the support of `a'`
  have hcoef : ∀ (z : (pullback sW sY : Scheme.{u})) (i : ↥(Function.support (a.1 : X → ℤ))),
      (pullback.fst sW sY).base z = e i →
        (exteriorProduct C sW sY n m a' c).1 z =
          (exteriorProduct C sX sY n m a c).1 (F.base z) := by
    intro z i hz
    rw [exteriorProduct_apply, exteriorProduct_apply, hweight z, hF,
      exteriorProductFstMap_base_fst, exteriorProductFstMap_base_snd, hz, ha', he]
  have hlift : ∀ w : ↥(Function.support ((exteriorProduct C sX sY n m a c).1 :
      ↥(pullback sX sY) → ℤ)), (pullback.fst sX sY).base (w : _) ∈
        Function.support (a.1 : X → ℤ) := by
    intro w
    have hw : (exteriorProduct C sX sY n m a c).1 (w : _) ≠ 0 := w.2
    rw [exteriorProduct_apply] at hw
    exact (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 hw).1).1
  have hex : ∀ w : ↥(Function.support ((exteriorProduct C sX sY n m a c).1 :
      ↥(pullback sX sY) → ℤ)), ∃ z : (pullback sW sY : Scheme.{u}),
        F.base z = (w : _) ∧ (pullback.fst sW sY).base z = e ⟨_, hlift w⟩ := fun w ↦
    exists_exteriorProductFstMap_eq sX sY sW π hπ (w : _) (e ⟨_, hlift w⟩) (he ⟨_, hlift w⟩).symm
  choose E hE1 hE2 using hex
  have hres : ∀ x : (pullback sW sY : Scheme.{u}), Function.Bijective ((F.residueFieldMap x).hom) :=
    fun x ↦ bijective_residueFieldMap_of_surjective_stalkMap F x (F.stalkMap_surjective x)
  refine properPushforward_eq_of_support_section C (pullback.fst sX sY ≫ sX)
    (pullback.fst sW sY ≫ sW) F _ (n + m) hres _ _ E hE1 (fun w ↦ ?_) (fun z hz ↦ ?_)
  · rw [hcoef (E w) ⟨_, hlift w⟩ (hE2 w), hE1 w]
  · have hz' : a'.1 ((pullback.fst sW sY).base z) ≠ 0 := by
      rw [exteriorProduct_apply] at hz
      exact (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 hz).1).1
    obtain ⟨i, hi⟩ := hsupp _ hz'
    have hw : (exteriorProduct C sX sY n m a c).1 (F.base z) ≠ 0 := by
      rwa [← hcoef z i hi]
    refine ⟨⟨F.base z, hw⟩, ?_⟩
    have hidx : (⟨_, hlift ⟨F.base z, hw⟩⟩ : ↥(Function.support (a.1 : X → ℤ))) = i := by
      refine Subtype.ext ?_
      show (pullback.fst sX sY).base (F.base z) = (i : X)
      rw [hF, exteriorProductFstMap_base_fst, hi, he]
    refine exteriorProductFstMap_injective_of_fst_eq sX sY sW π hπ (hE1 ⟨F.base z, hw⟩).symm ?_
    rw [hE2, hidx, hi]

/-! ### Restriction to an open subscheme in the first variable -/

/-- **The exterior product of cycles commutes with restriction to an open subscheme in its first
variable**: `(α × c)|_{U ×_S Y} = α|_U × c` for an open immersion `U ⟶ X`. -/
theorem cycleGroupRestrict_exteriorProduct (C : ChowSituation.{u}) {X U Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
    (n m : ℤ) (α : CycleGroup C sX n) (c : CycleGroup C sY m) :
    cycleGroupRestrict C (pullback.fst sX sY ≫ sX) (pullback.fst sU sY ≫ sU)
        (exteriorProductFstMap sX sY sU j hj)
        (exteriorProductFstMap_comp_structureMorphism sX sY sU j hj) (n + m)
        (exteriorProduct C sX sY n m α c) =
      exteriorProduct C sU sY n m (cycleGroupRestrict C sX sU j hj n α) c := by
  refine Subtype.ext ?_
  apply Function.locallyFinsuppWithin.ext
  intro w
  rw [cycleGroupRestrict_apply, exteriorProduct_apply, exteriorProduct_apply,
    cycleGroupRestrict_apply, exteriorProductFstMap_base_fst, exteriorProductFstMap_base_snd,
    exteriorProductWeight_fstMap_of_isOpenImmersion]

/-- **The exterior product on Chow groups commutes with restriction to an open subscheme in its
first variable.** -/
theorem chowGroupRestrict_chowExteriorProduct (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X U Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) (n m : ℤ) (α : chowGroup C sX n)
    (c : chowGroup C sY m) :
    chowGroupRestrict C (pullback.fst sX sY ≫ sX) (pullback.fst sU sY ≫ sU)
        (exteriorProductFstMap sX sY sU j hj)
        (exteriorProductFstMap_comp_structureMorphism sX sY sU j hj) (n + m)
        (chowExteriorProduct C hδ sX sY n m (TensorProduct.tmul ℤ α c)) =
      chowExteriorProduct C hδ sU sY n m
        (TensorProduct.tmul ℤ (chowGroupRestrict C sX sU j hj n α) c) := by
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    induction c using QuotientAddGroup.induction_on with
    | H d =>
      rw [chowExteriorProduct_tmul_mk]
      exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sU sY ≫ sU)
        (n + m))) (cycleGroupRestrict_exteriorProduct C sX sU sY j hj n m a d)

/-! ### The two sides of Stacks 0FBY along a proper pushforward and along a restriction -/

section Transport

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  (G : GysinSystem C) {X W Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z) [LocallyOfFiniteType u]
  (hu : u ≫ sZ = sY) (p : ℤ) (c : BivariantClass C G sY sZ u hu p)

omit [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S] [LocallyOfFiniteType sX]
  [LocallyOfFiniteType sW] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
  [LocallyOfFiniteType u] in
/-- The base change `h × 1_Y` and the identifications `Y ×_Z (- ×_S Z) ≅ - ×_S Y` of
`Stacks.Chow.exteriorCapIso` commute with the base change along `u` of `h × 1_Z`. -/
theorem testBaseChangeMapOfEq_comp_exteriorCapIso_hom (h : W ⟶ X) (hh : h ≫ sX = sW) :
    testBaseChangeMapOfEq u (pullback.snd sX sZ) (exteriorProductFstMap sX sZ sW h hh)
        (pullback.snd sW sZ) (exteriorProductFstMap_snd sX sZ sW h hh) ≫
      (exteriorCapIso sX sZ u hu).hom =
    (exteriorCapIso sW sZ u hu).hom ≫ exteriorProductFstMap sX sY sW h hh := by
  refine pullback.hom_ext ?_ ?_ <;> simp

include hδ in
/-- **The right-hand side of Stacks 0FBY along a proper pushforward in the first variable.** If
the exterior product with `α` is the pushforward along `π × 1_Z` of the exterior product with
`α'`, then `c ∩ (α × β)` is the pushforward along `π × 1_Y` of `c ∩ (α' × β)`. The content is
the proper axiom of Stacks 0B76 for `c`. -/
theorem capExteriorProduct_eq_properChowPushforward (π : W ⟶ X) [IsProper π]
    (hπ : π ≫ sX = sW) (n m : ℤ) (α : chowGroup C sX n) (α' : chowGroup C sW n)
    (β : chowGroup C sZ m)
    (hZ : chowExteriorProduct C hδ sX sZ n m (TensorProduct.tmul ℤ α β) =
      properChowPushforward C (pullback.fst sW sZ ≫ sW) (pullback.fst sX sZ ≫ sX)
        (exteriorProductFstMap sX sZ sW π hπ)
        (exteriorProductFstMap_comp_structureMorphism sX sZ sW π hπ) (n + m)
        (properPushforwardDescends C _ _ _ _ _)
        (chowExteriorProduct C hδ sW sZ n m (TensorProduct.tmul ℤ α' β))) :
    capExteriorProduct C hδ G sX sY sZ u hu p c n m α β =
      properChowPushforward C (pullback.fst sW sY ≫ sW) (pullback.fst sX sY ≫ sX)
        (exteriorProductFstMap sX sY sW π hπ)
        (exteriorProductFstMap_comp_structureMorphism sX sY sW π hπ) (n + (m - p))
        (properPushforwardDescends C _ _ _ _ _)
        (capExteriorProduct C hδ G sW sY sZ u hu p c n m α' β) := by
  set PZ := exteriorProductFstMap sX sZ sW π hπ with hPZ
  set P' := testBaseChangeMapOfEq u (pullback.snd sX sZ) PZ (pullback.snd sW sZ)
    (exteriorProductFstMap_snd sX sZ sW π hπ) with hP'
  have hsq := isPullback_testBaseChangeMapOfEq u (pullback.snd sX sZ) PZ (pullback.snd sW sZ)
    (exteriorProductFstMap_snd sX sZ sW π hπ)
  have : IsProper P' := MorphismProperty.of_isPullback hsq inferInstance
  have hP'base : P' ≫ (pullback.fst u (pullback.snd sX sZ) ≫ sY) =
      pullback.fst u (pullback.snd sW sZ) ≫ sY := by
    rw [hP', testBaseChangeMapOfEq_fst_assoc]
  have hPZbase : PZ ≫ (pullback.snd sX sZ ≫ sZ) = pullback.snd sW sZ ≫ sZ := by
    rw [hPZ, exteriorProductFstMap_snd_assoc]
  -- the target class, read through `π × 1_Z`
  have htarget : exteriorProductOnTarget C hδ sX sZ n m α β =
      properChowPushforward C (pullback.snd sW sZ ≫ sZ) (pullback.snd sX sZ ≫ sZ) PZ hPZbase
        (n + m) (properPushforwardDescends C _ _ _ _ _)
        (exteriorProductOnTarget C hδ sW sZ n m α' β) := by
    rw [exteriorProductOnTarget, hZ, exteriorProductOnTarget]
    exact properChowPushforward_chowGroupCongr C _ _ PZ _ _ (n + m) _ _ _
  -- the proper axiom of Stacks 0B76
  have hnat := BivariantClass.proper_naturality_of_eq C G sY sZ u hu p c
    (pullback.snd sX sZ) PZ (pullback.snd sW sZ) (exteriorProductFstMap_snd sX sZ sW π hπ) P'
    hsq (testBaseChangeMapOfEq_fst _ _ _ _ _) (n + m) hPZbase
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (exteriorProductOnTarget C hδ sW sZ n m α' β)
  -- the comparison of the two identifications
  have hcomm := chowPushforwardOfIso_comm_properChowPushforward C
    (pullback.fst u (pullback.snd sW sZ) ≫ sY) (pullback.fst u (pullback.snd sX sZ) ≫ sY)
    (pullback.fst sW sY ≫ sW) (pullback.fst sX sY ≫ sX) (exteriorCapIso sW sZ u hu).hom
    (exteriorCapIso sX sZ u hu).hom P' (exteriorProductFstMap sX sY sW π hπ)
    (testBaseChangeMapOfEq_comp_exteriorCapIso_hom C sX sW sY sZ u hu π hπ)
    (exteriorCapIso_hom_comp_structureMorphism sW sZ u hu)
    (exteriorCapIso_hom_comp_structureMorphism sX sZ u hu) hP'base
    (exteriorProductFstMap_comp_structureMorphism sX sY sW π hπ) (n + (m - p))
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
  rw [capExteriorProduct, capExteriorProduct, ← hcomm, htarget, hnat,
    properChowPushforward_chowGroupDegreeEquiv]

include hδ in
/-- The exterior product presented on the structure morphism of the target commutes with
restriction to an open subscheme in the first variable. -/
theorem chowGroupRestrict_exteriorProductOnTarget {V : Scheme.{u}} (sV : V ⟶ C.S)
    [LocallyOfFiniteType sV] (j : V ⟶ W) [IsOpenImmersion j] (hj : j ≫ sW = sV) (n m : ℤ)
    (α : chowGroup C sW n) (β : chowGroup C sZ m) :
    chowGroupRestrict C (pullback.snd sW sZ ≫ sZ) (pullback.snd sV sZ ≫ sZ)
        (exteriorProductFstMap sW sZ sV j hj) (exteriorProductFstMap_snd_assoc _ _ _ _ _ _)
        (n + m) (exteriorProductOnTarget C hδ sW sZ n m α β) =
      exteriorProductOnTarget C hδ sV sZ n m (chowGroupRestrict C sW sV j hj n α) β := by
  rw [exteriorProductOnTarget, exteriorProductOnTarget,
    chowGroupRestrict_chowGroupCongr C (pullback.fst sW sZ ≫ sW) (pullback.snd sW sZ ≫ sZ) _ _
      (by rw [exteriorProductFstMap_fst_assoc, hj, ← pullback.condition])
      _ pullback.condition,
    ← chowGroupCongr_chowGroupRestrict C _ (pullback.fst sV sZ ≫ sV) (pullback.snd sV sZ ≫ sZ) _
      (exteriorProductFstMap_comp_structureMorphism sW sZ sV j hj) _ pullback.condition,
    chowGroupRestrict_chowExteriorProduct]

include hδ in
/-- **The right-hand side of Stacks 0FBY along a restriction to an open subscheme in the first
variable.** Restricting `c ∩ (α × β)` to `V ×_S Y` gives `c ∩ (α|_V × β)`. The content is the
flat axiom of Stacks 0B76 for `c` in relative dimension zero,
`Stacks.Chow.BivariantClass.cap_chowGroupRestrict`. -/
theorem chowGroupRestrict_capExteriorProduct {V : Scheme.{u}} (sV : V ⟶ C.S)
    [LocallyOfFiniteType sV] (j : V ⟶ W) [IsOpenImmersion j] (hj : j ≫ sW = sV) (n m : ℤ)
    (α : chowGroup C sW n) (β : chowGroup C sZ m) :
    chowGroupRestrict C (pullback.fst sW sY ≫ sW) (pullback.fst sV sY ≫ sV)
        (exteriorProductFstMap sW sY sV j hj)
        (exteriorProductFstMap_comp_structureMorphism sW sY sV j hj) (n + (m - p))
        (capExteriorProduct C hδ G sW sY sZ u hu p c n m α β) =
      capExteriorProduct C hδ G sV sY sZ u hu p c n m (chowGroupRestrict C sW sV j hj n α) β := by
  set MZ := exteriorProductFstMap sW sZ sV j hj with hMZ
  set M'' := testBaseChangeMapOfEq u (pullback.snd sW sZ) MZ (pullback.snd sV sZ)
    (exteriorProductFstMap_snd sW sZ sV j hj) with hM''
  have hsq := isPullback_testBaseChangeMapOfEq u (pullback.snd sW sZ) MZ (pullback.snd sV sZ)
    (exteriorProductFstMap_snd sW sZ sV j hj)
  have : IsOpenImmersion M'' := MorphismProperty.of_isPullback hsq inferInstance
  have hM''base : M'' ≫ (pullback.fst u (pullback.snd sW sZ) ≫ sY) =
      pullback.fst u (pullback.snd sV sZ) ≫ sY := by
    rw [hM'', testBaseChangeMapOfEq_fst_assoc]
  have hMZbase : MZ ≫ (pullback.snd sW sZ ≫ sZ) = pullback.snd sV sZ ≫ sZ := by
    rw [hMZ, exteriorProductFstMap_snd_assoc]
  have hiso : IsPullback M'' (exteriorCapIso sV sZ u hu).hom (exteriorCapIso sW sZ u hu).hom
      (exteriorProductFstMap sW sY sV j hj) :=
    IsPullback.of_vert_isIso ⟨testBaseChangeMapOfEq_comp_exteriorCapIso_hom C sW sV sY sZ u hu j hj⟩
  have hrestrict := chowGroupRestrict_properChowPushforward C
    (pullback.fst u (pullback.snd sW sZ) ≫ sY) (pullback.fst sW sY ≫ sW)
    (pullback.fst u (pullback.snd sV sZ) ≫ sY) (pullback.fst sV sY ≫ sV)
    (exteriorCapIso sW sZ u hu).hom (exteriorCapIso_hom_comp_structureMorphism sW sZ u hu)
    M'' hM''base (exteriorProductFstMap sW sY sV j hj)
    (exteriorProductFstMap_comp_structureMorphism sW sY sV j hj)
    (exteriorCapIso sV sZ u hu).hom (exteriorCapIso_hom_comp_structureMorphism sV sZ u hu) hiso
    (n + (m - p)) (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
  unfold capExteriorProduct chowPushforwardOfIso
  rw [hrestrict, chowGroupRestrict_chowGroupDegreeEquiv,
    BivariantClass.cap_chowGroupRestrict C G sY sZ u hu p c (pullback.snd sW sZ) MZ
      (pullback.snd sV sZ) (exteriorProductFstMap_snd sW sZ sV j hj) M'' hsq
      (testBaseChangeMapOfEq_fst _ _ _ _ _) (n + m) hMZbase hM''base,
    chowGroupRestrict_exteriorProductOnTarget C hδ sW sZ sV j hj n m α β]

include hδ in
/-- **Stacks 0FBY descends along a proper pushforward in the first variable.** If the exterior
product with `α` is the pushforward along `π × 1` of the exterior product with `α'`, for a proper
`π : W ⟶ X`, and the equation of Stacks 0FBY holds for `α'`, then it holds for `α`. -/
theorem commutesExteriorProductCapAt_of_properChowPushforward (π : W ⟶ X) [IsProper π]
    (hπ : π ≫ sX = sW) (n m : ℤ) (α : chowGroup C sX n) (α' : chowGroup C sW n)
    (hA : ∀ {T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ)
      (δ : chowGroup C sT k),
      chowExteriorProduct C hδ sX sT n k (TensorProduct.tmul ℤ α δ) =
        properChowPushforward C (pullback.fst sW sT ≫ sW) (pullback.fst sX sT ≫ sX)
          (exteriorProductFstMap sX sT sW π hπ)
          (exteriorProductFstMap_comp_structureMorphism sX sT sW π hπ) (n + k)
          (properPushforwardDescends C _ _ _ _ _)
          (chowExteriorProduct C hδ sW sT n k (TensorProduct.tmul ℤ α' δ)))
    (h' : CommutesExteriorProductCapAt C hδ G sW sY sZ u hu p c n m α') :
    CommutesExteriorProductCapAt C hδ G sX sY sZ u hu p c n m α := by
  intro β
  rw [capExteriorProduct_eq_properChowPushforward C hδ G sX sW sY sZ u hu p c π hπ n m α α' β
    (hA sZ m β), ← h' β]
  exact hA sY (m - p) _

include hδ in
/-- **Stacks 0FBY is local along a decomposition into open and closed pieces in the first
variable.** If `W` is the disjoint union of the open subschemes `V i`, and the equation of Stacks
0FBY holds for the restriction of `α` to every piece, then it holds for `α`: both sides restrict
to the corresponding sides for the pieces, and Chow classes are determined by their restrictions
to the pieces of such a decomposition. -/
theorem commutesExteriorProductCapAt_of_isOpenImmersion_cover {I : Type u}
    {V : I → Scheme.{u}} (sV : ∀ i, V i ⟶ C.S) [∀ i, LocallyOfFiniteType (sV i)]
    (j : ∀ i, V i ⟶ W) [∀ i, IsOpenImmersion (j i)] (hj : ∀ i, j i ≫ sW = sV i)
    (hcover : ∀ x : W, ∃ i, x ∈ Set.range (j i).base)
    (hdisjoint : Pairwise fun i l ↦ Disjoint (Set.range (j i).base) (Set.range (j l).base))
    (n m : ℤ) (α : chowGroup C sW n)
    (h : ∀ i, CommutesExteriorProductCapAt C hδ G (sV i) sY sZ u hu p c n m
      (chowGroupRestrict C sW (sV i) (j i) (hj i) n α)) :
    CommutesExteriorProductCapAt C hδ G sW sY sZ u hu p c n m α := by
  intro β
  rw [← sub_eq_zero]
  have hrange : ∀ i, Set.range (exteriorProductFstMap sW sY (sV i) (j i) (hj i)).base =
      (pullback.fst sW sY).base ⁻¹' Set.range (j i).base := fun i ↦
    range_exteriorProductFstMap sW sY (sV i) (j i) (hj i)
  refine eq_zero_of_chowGroupRestrict_eq_zero C (pullback.fst sW sY ≫ sW)
    (fun i ↦ pullback.fst (sV i) sY ≫ sV i)
    (fun i ↦ exteriorProductFstMap sW sY (sV i) (j i) (hj i))
    (fun i ↦ exteriorProductFstMap_comp_structureMorphism sW sY (sV i) (j i) (hj i))
    (isClopenDecomposition_of_isOpenImmersion_cover _ (fun x ↦ ?_) (fun i l hil ↦ ?_)) _ _
    (fun i ↦ ?_)
  · obtain ⟨i, hi⟩ := hcover ((pullback.fst sW sY).base x)
    exact ⟨i, (hrange i).symm ▸ hi⟩
  · show Disjoint _ _
    rw [hrange, hrange]
    exact (hdisjoint hil).preimage _
  · rw [map_sub, sub_eq_zero]
    have hi := h i β
    rw [exteriorProductCap, chowGroupRestrict_chowExteriorProduct,
      chowGroupRestrict_capExteriorProduct]
    exact hi

end Transport

/-- The exterior product on Chow groups commutes with a proper pushforward in its first variable,
under the hypotheses of `Stacks.Chow.properPushforward_exteriorProduct_fstMap`: this is that
identity of cycles read modulo rational equivalence in the second variable. -/
theorem chowExteriorProduct_mk_eq_properChowPushforward (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X W : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (π : W ⟶ X) [IsProper π] [SurjectiveOnStalks π]
    (hπ : π ≫ sX = sW) (n : ℤ)
    (hweight : ∀ {T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (j : ℤ)
      (z : (pullback sW sT : Scheme.{u})),
      exteriorProductWeight C sW sT j ((pullback.fst sW sT).base z)
          ((pullback.snd sW sT).base z) z =
        exteriorProductWeight C sX sT j (π.base ((pullback.fst sW sT).base z))
          ((pullback.snd sW sT).base z) ((exteriorProductFstMap sX sT sW π hπ).base z))
    (a : CycleGroup C sX n) (a' : CycleGroup C sW n)
    (e : ↥(Function.support (a.1 : X → ℤ)) → W) (he : ∀ i, π.base (e i) = (i : X))
    (ha' : ∀ i, a'.1 (e i) = a.1 (i : X)) (hsupp : ∀ x : W, a'.1 x ≠ 0 → ∃ i, x = e i)
    {T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ) (δ : chowGroup C sT k) :
    chowExteriorProduct C hδ sX sT n k
        (TensorProduct.tmul ℤ (QuotientAddGroup.mk' (rationalEquivalences C sX n) a) δ) =
      properChowPushforward C (pullback.fst sW sT ≫ sW) (pullback.fst sX sT ≫ sX)
        (exteriorProductFstMap sX sT sW π hπ)
        (exteriorProductFstMap_comp_structureMorphism sX sT sW π hπ) (n + k)
        (properPushforwardDescends C _ _ _ _ _)
        (chowExteriorProduct C hδ sW sT n k
          (TensorProduct.tmul ℤ (QuotientAddGroup.mk' (rationalEquivalences C sW n) a') δ)) := by
  induction δ using QuotientAddGroup.induction_on with
  | H d =>
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, chowExteriorProduct_tmul_mk,
      chowExteriorProduct_tmul_mk]
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX sT ≫ sX) (n + k)))
      (properPushforward_exteriorProduct_fstMap C sX sW sT π hπ n k (hweight sT (n + k)) a a' e he
        ha' hsupp d).symm

/-! ### Linearity in the first variable -/

section Linearity

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (u : Y ⟶ Z) [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ)
  (c : BivariantClass C G sY sZ u hu p) (n m : ℤ)

/-- The equation of Stacks 0FBY for an integer multiple of a class follows from the equation for
the class: both sides are additive in the first variable. -/
theorem CommutesExteriorProductCapAt.zsmul {α : chowGroup C sX n}
    (h : CommutesExteriorProductCapAt C hδ G sX sY sZ u hu p c n m α) (k : ℤ) :
    CommutesExteriorProductCapAt C hδ G sX sY sZ u hu p c n m (k • α) := by
  intro β
  have h1 : exteriorProductCap C hδ G sX sY sZ u hu p c n m (k • α) β =
      k • exteriorProductCap C hδ G sX sY sZ u hu p c n m α β := by
    simp only [exteriorProductCap, ← TensorProduct.smul_tmul', map_zsmul]
  have h2 : capExteriorProduct C hδ G sX sY sZ u hu p c n m (k • α) β =
      k • capExteriorProduct C hδ G sX sY sZ u hu p c n m α β := by
    simp only [capExteriorProduct, exteriorProductOnTarget, ← TensorProduct.smul_tmul',
      map_zsmul]
  rw [h1, h2, h β]

end Linearity

/-! ### Stacks 0FBY over a field -/

section Field

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z)
  [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ)
  (c : BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
    sY sZ u hu p)

/-- Stacks 0FBY for an integer multiple of the fundamental class of an integral scheme locally of
finite type over the field: such a scheme is flat over the field of relative dimension its
dimension, so `Stacks.Chow.commutesExteriorProductCapAt_fundamentalChowClass_of_invertible`
applies. -/
theorem commutesExteriorProductCapAt_zsmul_fundamentalChowClass {V : Scheme.{u}}
    (sV : V ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV] [IsIntegral V] (d : ℕ)
    (hd : relativeDimension (fieldChowSituation k).dimensionFunction sV (genericPoint V) = d)
    (m l : ℤ) :
    CommutesExteriorProductCapAt (fieldChowSituation k) (fun _ _ ↦ rfl)
      (gysinSystemOfInvertible (fieldChowSituation k)) sV sY sZ u hu p c (d : ℤ) m
      (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) sV (d : ℤ))
        (l • fundamentalCycle (fieldChowSituation k) sV (d : ℤ))) := by
  rw [mk_zsmul_fundamentalCycle]
  have hfr := relativeDimension_of_isIntegral_over_field k sV
  rw [hd, Int.toNat_natCast] at hfr
  exact CommutesExteriorProductCapAt.zsmul _ _ _ _ _ _ _ _ _ _ _ _
    (commutesExteriorProductCapAt_fundamentalChowClass_of_invertible (fieldChowSituation k)
      (fun _ _ ↦ rfl) sV sY sZ u hu p d m c hfr hd) l

/-- **Stacks 0FBY for the class of a cycle presented by its integral components.** Let `a` be a
cycle on `X` and let `vᵢ : Zᵢ ⟶ X` be closed immersions of integral schemes, one for each point
`i` of the support of `a`, with generic point mapping to `i` and with locally finite images. Then
the equation of Stacks 0FBY holds for the class of `a`.

The coproduct `W = ∐ Zᵢ` is proper over `X` by `Stacks.Chow.isProper_sigmaDesc_of_locallyFinite`
and carries the cycle `a' = ∑ a(i) [Zᵢ]`, whose exterior products push forward to those of `a` by
`Stacks.Chow.chowExteriorProduct_mk_eq_properChowPushforward`; so it suffices to treat `a'`, by
`Stacks.Chow.commutesExteriorProductCapAt_of_properChowPushforward`. The summands decompose `W`
into open and closed pieces, so it suffices to treat the restriction `a(i) [Zᵢ]` of `a'` to each,
by `Stacks.Chow.commutesExteriorProductCapAt_of_isOpenImmersion_cover`; and for the fundamental
class of the integral scheme `Zᵢ`, flat over the field of relative dimension its dimension, the
equation is `Stacks.Chow.commutesExteriorProductCapAt_fundamentalChowClass_of_invertible`. -/
theorem commutesExteriorProductCapAt_mk_of_integralPresentation (n m : ℤ)
    (a : CycleGroup (fieldChowSituation k) sX n)
    (Zs : ↥(Function.support (a.1 : X → ℤ)) → Scheme.{u}) [∀ i, IsIntegral (Zs i)]
    (v : ∀ i, Zs i ⟶ X) [∀ i, IsClosedImmersion (v i)]
    (hv : ∀ i, (v i).base (genericPoint (Zs i)) = (i : X))
    (hlf : LocallyFinite fun i ↦ Set.range (v i)) :
    CommutesExteriorProductCapAt (fieldChowSituation k) (fun _ _ ↦ rfl)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX sY sZ u hu p c n m
      (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) sX n) a) := by
  classical
  have : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Zs v hlf
  have : SurjectiveOnStalks (Sigma.desc v) := surjectiveOnStalks_sigmaDesc Zs v
  have hti : ∀ i, Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX) = v i ≫ sX := fun i ↦ by
    rw [← Category.assoc, Sigma.ι_desc]
  have hdim : ∀ i, relativeDimension (fieldChowSituation k).dimensionFunction
      (Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) (genericPoint (Zs i)) = n := fun i ↦ by
    rw [hti i, relativeDimension_comp_closedImmersion, hv i]
    exact (mem_cyclesOfDimension_iff_forall_point _ sX n a.1).1 a.2 _ i.2
  have hcoeff : ∀ i, ∀ z : Zs i,
      (a.1 (i : X) • fundamentalCycle (fieldChowSituation k)
        (Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) n).1 z =
        if z = genericPoint (Zs i) then a.1 (i : X) else 0 := fun i z ↦ by
    show a.1 (i : X) • (fundamentalCycle (fieldChowSituation k)
      (Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) n).1 z = _
    rw [fundamentalCycle_eq_single (fieldChowSituation k) (Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX))
      genericPoints_eq_singleton (hdim i) (Field.toIsField _)]
    simp [Function.locallyFinsuppWithin.single_apply]
  -- the cycle `∑ a(i) [Zᵢ]` on the coproduct
  obtain ⟨a', ha'⟩ := exists_cycleGroup_of_sigma (fieldChowSituation k) Zs (Sigma.desc v ≫ sX)
    (fun i ↦ Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) (fun i ↦ rfl) n
    (fun i ↦ a.1 (i : X) • fundamentalCycle (fieldChowSituation k)
      (Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) n)
  have he : ∀ i, (Sigma.desc v).base (Sigma.ι Zs i (genericPoint (Zs i))) = (i : X) := fun i ↦ by
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    exact hv i
  have hae : ∀ i, a'.1 (Sigma.ι Zs i (genericPoint (Zs i))) = a.1 (i : X) := fun i ↦ by
    rw [ha' i, hcoeff i]
    simp
  have hsupp : ∀ x : (∐ Zs : Scheme.{u}), a'.1 x ≠ 0 →
      ∃ i, x = Sigma.ι Zs i (genericPoint (Zs i)) := fun x hx ↦ by
    obtain ⟨⟨i, z⟩, rfl⟩ := (sigmaMk Zs).surjective x
    rw [sigmaMk_mk, ha' i, hcoeff i] at hx
    refine ⟨i, ?_⟩
    by_cases hz : z = genericPoint (Zs i)
    · rw [sigmaMk_mk, hz]
    · simp [hz] at hx
  -- reduce to the coproduct, then to its summands
  refine commutesExteriorProductCapAt_of_properChowPushforward (fieldChowSituation k)
    (fun _ _ ↦ rfl) _ sX (Sigma.desc v ≫ sX) sY sZ u hu p c (Sigma.desc v) rfl n m _
    (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) (Sigma.desc v ≫ sX) n) a')
    (fun sT _ l δ ↦ chowExteriorProduct_mk_eq_properChowPushforward (fieldChowSituation k)
      (fun _ _ ↦ rfl) sX (Sigma.desc v ≫ sX) (Sigma.desc v) rfl n
      (fun sT _ j z ↦ exteriorProductWeight_sigmaDesc (fieldChowSituation k) Zs v sX
        (Sigma.desc v ≫ sX) rfl sT j z) a a' _ he hae hsupp sT l δ) ?_
  refine commutesExteriorProductCapAt_of_isOpenImmersion_cover (fieldChowSituation k)
    (fun _ _ ↦ rfl) _ (Sigma.desc v ≫ sX) sY sZ u hu p c
    (fun i ↦ Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) (Sigma.ι Zs) (fun i ↦ rfl)
    (exists_mem_range_sigmaι Zs) (pairwise_disjoint_range_sigmaι Zs) n m _ fun i ↦ ?_
  -- the summand `Zᵢ`
  have hn : 0 ≤ n := hdim i ▸ relativeDimension_fieldChowSituation_nonneg k _ _
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hres : chowGroupRestrict (fieldChowSituation k) (Sigma.desc v ≫ sX)
      (Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) (Sigma.ι Zs i) rfl (d : ℤ)
      (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) (Sigma.desc v ≫ sX)
        (d : ℤ)) a') =
      QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k)
        (Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) (d : ℤ)) (a.1 (i : X) • fundamentalCycle
          (fieldChowSituation k) (Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) (d : ℤ)) := by
    have hcyc : cycleGroupRestrict (fieldChowSituation k) (Sigma.desc v ≫ sX)
        (Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) (Sigma.ι Zs i) rfl (d : ℤ) a' =
        a.1 (i : X) • fundamentalCycle (fieldChowSituation k)
          (Sigma.ι Zs i ≫ (Sigma.desc v ≫ sX)) (d : ℤ) := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
      rw [cycleGroupRestrict_apply]
      exact ha' i z
    exact (chowGroupRestrict_mk _ _ _ _ _ _ a').trans (congrArg _ hcyc)
  rw [hres]
  exact commutesExteriorProductCapAt_zsmul_fundamentalChowClass k sY sZ u hu p c _ d (hdim i) m _

/-- **Stacks 0FBY over a field, for a single class.** Let `k` be a field, `X` locally of finite
type over `k`, `u : Y ⟶ Z` a morphism of schemes locally of finite type over `k`, and
`c ∈ A^p(Y ⟶ Z)`. Then for every `α ∈ CH_n(X)` and every `β ∈ CH_m(Z)`

  `α × (c ∩ β) = c ∩ (α × β)`   in   `CH_{n + (m - p)}(X ×_k Y)`.

The class `α` is the class of a cycle, and the points of its support are the generic points of
their reduced closures, a locally finite family of integral closed subschemes; so
`Stacks.Chow.commutesExteriorProductCapAt_mk_of_integralPresentation` applies. -/
theorem commutesExteriorProductCapAt_of_field (n m : ℤ)
    (α : chowGroup (fieldChowSituation k) sX n) :
    CommutesExteriorProductCapAt (fieldChowSituation k) (fun _ _ ↦ rfl)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX sY sZ u hu p c n m α := by
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    have : ∀ i : ↥(Function.support (a.1 : X → ℤ)),
        IsIntegral (integralComponentAt (i : X)).subscheme := fun i ↦
      isIntegral_integralComponentAt (i : X)
    exact commutesExteriorProductCapAt_mk_of_integralPresentation k sX sY sZ u hu p c n m a
      (fun i ↦ (integralComponentAt (i : X)).subscheme)
      (fun i ↦ (integralComponentAt (i : X)).subschemeι)
      (fun i ↦ genericPointOf_integralComponentAt (i : X))
      (locallyFinite_range_subschemeι_support _ sX n a)

/-- **Stacks 0FBY over a field.** Let `k` be a field, `X` locally of finite type over `k`,
`u : Y ⟶ Z` a morphism of schemes locally of finite type over `k`, and `c ∈ A^p(Y ⟶ Z)`. Then

  `α × (c ∩ β) = c ∩ (α × β)`   in   `CH_{n + (m - p)}(X ×_k Y)`

for every `α ∈ CH_n(X)` and every `β ∈ CH_m(Z)`. -/
@[stacks 0FBY "the bivariant classes are those of the Gysin system of invertible modules, \
`Stacks.Chow.gysinSystemOfInvertible`"]
theorem commutesExteriorProductCap_of_field (n m : ℤ) :
    CommutesExteriorProductCap (fieldChowSituation k) (fun _ _ ↦ rfl)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX sY sZ u hu p c n m :=
  fun α ↦ commutesExteriorProductCapAt_of_field k sX sY sZ u hu p c n m α

end Field

/-! ### The form of Stacks 0FBY with the cap product in the first variable -/

section FirstVariable

/-- The identification `Y ×_Z (Z ×_S X) ≅ Y ×_S X`, for `u : Y ⟶ Z` a morphism over `S`. The
scheme on the left is where the cap operation of a bivariant class for `u`, taken at the test
morphism `pr_Z : Z ×_S X ⟶ Z`, lands. -/
def exteriorCapFstIso {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sZ : Z ⟶ S) {sY : Y ⟶ S}
    (u : Y ⟶ Z) (hu : u ≫ sZ = sY) :
    (pullback u (pullback.fst sZ sX) : Scheme.{u}) ≅ (pullback sY sX : Scheme.{u}) :=
  pullbackRightPullbackFstIso sZ sX u ≪≫ pullback.congrHom hu rfl

/-- The first projection of the identification `Y ×_Z (Z ×_S X) ≅ Y ×_S X`. -/
@[reassoc (attr := simp)]
theorem exteriorCapFstIso_hom_fst {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sZ : Z ⟶ S)
    {sY : Y ⟶ S} (u : Y ⟶ Z) (hu : u ≫ sZ = sY) :
    (exteriorCapFstIso sX sZ u hu).hom ≫ pullback.fst sY sX =
      pullback.fst u (pullback.fst sZ sX) := by
  simp [exteriorCapFstIso]

/-- The second projection of the identification `Y ×_Z (Z ×_S X) ≅ Y ×_S X`. -/
@[reassoc (attr := simp)]
theorem exteriorCapFstIso_hom_snd {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sZ : Z ⟶ S)
    {sY : Y ⟶ S} (u : Y ⟶ Z) (hu : u ≫ sZ = sY) :
    (exteriorCapFstIso sX sZ u hu).hom ≫ pullback.snd sY sX =
      pullback.snd u (pullback.fst sZ sX) ≫ pullback.snd sZ sX := by
  simp [exteriorCapFstIso]

/-- The identification `Y ×_Z (Z ×_S X) ≅ Y ×_S X` is a morphism over `S`. -/
theorem exteriorCapFstIso_hom_comp_structureMorphism {S X Y Z : Scheme.{u}} (sX : X ⟶ S)
    (sZ : Z ⟶ S) {sY : Y ⟶ S} (u : Y ⟶ Z) (hu : u ≫ sZ = sY) :
    (exteriorCapFstIso sX sZ u hu).hom ≫ (pullback.fst sY sX ≫ sY) =
      pullback.fst u (pullback.fst sZ sX) ≫ sY := by
  rw [exteriorCapFstIso_hom_fst_assoc]

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (u : Y ⟶ Z) [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ)
  (c : BivariantClass C G sY sZ u hu p)

/-- The right-hand side `c ∩ (ξ × γ)` of the first-variable form of Stacks 0FBY, read in
`CH_{(m - p) + n}(Y ×_S X)`: the cap is taken at the test morphism `pr_Z : Z ×_S X ⟶ Z`, and the
class is pushed forward along `Stacks.Chow.exteriorCapFstIso`. -/
def capExteriorProductFst (m n : ℤ) (ξ : chowGroup C sZ m) (γ : chowGroup C sX n) :
    chowGroup C (pullback.fst sY sX ≫ sY) ((m - p) + n) :=
  chowPushforwardOfIso C (pullback.fst u (pullback.fst sZ sX) ≫ sY) (pullback.fst sY sX ≫ sY)
    (exteriorCapFstIso sX sZ u hu).hom (exteriorCapFstIso_hom_comp_structureMorphism sX sZ u hu)
    ((m - p) + n)
    (chowGroupDegreeEquiv C (pullback.fst u (pullback.fst sZ sX) ≫ sY)
      (by omega : m + n - p = (m - p) + n)
      (c.cap (pullback.fst sZ sX) (m + n)
        (chowExteriorProduct C hδ sZ sX m n (TensorProduct.tmul ℤ ξ γ))))

include hδ in
/-- **Stacks 0FBY with the cap product in the first variable.** If the equation of Stacks 0FBY
holds for `γ ∈ CH_n(X)`, then for every `ξ ∈ CH_m(Z)`

  `(c ∩ ξ) × γ = c ∩ (ξ × γ)`   in   `CH_{(m - p) + n}(Y ×_S X)`.

This is the equation for `γ` transported along the symmetry of the exterior product,
`Stacks.Chow.chowPushforwardOfIso_pullbackSymmetry_chowExteriorProduct_tmul`, on `X ×_S Y` and on
`X ×_S Z`; the second transport moves past the cap product by the isomorphism case of condition
(1) of Stacks 0B76, `Stacks.Chow.BivariantClass.cap_chowPushforwardOfTestIso`. -/
theorem chowExteriorProduct_capTarget_eq_capExteriorProductFst (m n : ℤ) (γ : chowGroup C sX n)
    (h : CommutesExteriorProductCapAt C hδ G sX sY sZ u hu p c n m γ) (ξ : chowGroup C sZ m) :
    chowExteriorProduct C hδ sY sX (m - p) n
        (TensorProduct.tmul ℤ (c.capTarget C G sY sZ u hu p m ξ) γ) =
      capExteriorProductFst C hδ G sX sY sZ u hu p c m n ξ γ := by
  set σY := (pullbackSymmetry sX sY).hom
  set σZ := (pullbackSymmetry sZ sX).hom
  set E := (exteriorCapIso sX sZ u hu).hom
  set F := (exteriorCapFstIso sX sZ u hu).hom
  have hσZ : σZ ≫ pullback.snd sX sZ = pullback.fst sZ sX := pullbackSymmetry_hom_comp_snd _ _
  set B := (pullbackBaseChangeOfTestIso u σZ hσZ).hom
  have hsq : B ≫ E ≫ σY = F := by
    refine pullback.hom_ext ?_ ?_ <;> simp [σY, σZ, E, F, B]
  -- the symmetry on `X ×_S Y`
  have hsymY := chowPushforwardOfIso_pullbackSymmetry_chowExteriorProduct_tmul C hδ sX sY n
    (m - p) γ (c.capTarget C G sY sZ u hu p m ξ)
  -- the symmetry on `X ×_S Z`, read on the target class
  have hsymZ := chowPushforwardOfIso_pullbackSymmetry_chowExteriorProduct_tmul C hδ sZ sX m n ξ γ
  have htarget : exteriorProductOnTarget C hδ sX sZ n m γ ξ ≍
      chowPushforwardOfIso C (pullback.fst sZ sX ≫ sZ) (pullback.snd sX sZ ≫ sZ) σZ
        (by rw [← Category.assoc, hσZ]) (m + n)
        (chowExteriorProduct C hδ sZ sX m n (TensorProduct.tmul ℤ ξ γ)) := by
    refine (chowGroupCongr_heq C _ _ _).trans ?_
    have hcongr : chowPushforwardOfIso C (pullback.fst sZ sX ≫ sZ) (pullback.snd sX sZ ≫ sZ) σZ
        (by rw [← Category.assoc, hσZ]) (m + n)
        (chowExteriorProduct C hδ sZ sX m n (TensorProduct.tmul ℤ ξ γ)) =
        chowGroupCongr C (pullback.condition (f := sX) (g := sZ)) (m + n)
          (chowPushforwardOfIso C (pullback.fst sZ sX ≫ sZ) (pullback.fst sX sZ ≫ sX) σZ
            (Stacks.WeilCohomology.pullbackSymmetry_hom_comp_base sZ sX) (m + n)
            (chowExteriorProduct C hδ sZ sX m n (TensorProduct.tmul ℤ ξ γ))) :=
      (chowGroupCongr_chowPushforwardOfIso_target C _ _ σZ _ _ (m + n) _).symm
    rw [hcongr, hsymZ]
    exact ((chowGroupCongr_heq C _ _ _).trans (chowGroupDegreeEquiv_heq C _ _ _)).symm
  -- the cap product at the two presentations of the target class
  have hcap := heq_cap_of_heq C G sY sZ u hu p c (pullback.snd sX sZ) (add_comm n m) htarget
  rw [BivariantClass.cap_chowPushforwardOfTestIso C G sY sZ u hu p c (pullback.snd sX sZ) σZ hσZ
    (m + n)] at hcap
  -- assemble
  have hmain := h ξ
  unfold exteriorProductCap at hmain
  rw [hmain] at hsymY
  have hEσ : (E ≫ σY) ≫ (pullback.fst sY sX ≫ sY) = pullback.fst u (pullback.snd sX sZ) ≫ sY := by
    rw [Category.assoc, Stacks.WeilCohomology.pullbackSymmetry_hom_comp_base,
      exteriorCapIso_hom_comp_structureMorphism]
  have step1 : chowExteriorProduct C hδ sY sX (m - p) n
      (TensorProduct.tmul ℤ (c.capTarget C G sY sZ u hu p m ξ) γ) ≍
      chowPushforwardOfIso C (pullback.fst sX sY ≫ sX) (pullback.fst sY sX ≫ sY) σY
        (Stacks.WeilCohomology.pullbackSymmetry_hom_comp_base sX sY) (n + (m - p))
        (capExteriorProduct C hδ G sX sY sZ u hu p c n m γ ξ) := by
    rw [hsymY]
    exact (chowGroupDegreeEquiv_heq C _ _ _).symm
  have step2 : chowPushforwardOfIso C (pullback.fst sX sY ≫ sX) (pullback.fst sY sX ≫ sY) σY
        (Stacks.WeilCohomology.pullbackSymmetry_hom_comp_base sX sY) (n + (m - p))
        (capExteriorProduct C hδ G sX sY sZ u hu p c n m γ ξ) ≍
      chowPushforwardOfIso C (pullback.fst u (pullback.snd sX sZ) ≫ sY)
        (pullback.fst sY sX ≫ sY) (E ≫ σY) hEσ (n + m - p)
        (c.cap (pullback.snd sX sZ) (n + m) (exteriorProductOnTarget C hδ sX sZ n m γ ξ)) := by
    rw [capExteriorProduct, chowPushforwardOfIso_comp_apply]
    exact chowPushforwardOfIso_heq_congr C _ _ _ _ (by omega) _ _
      (chowGroupDegreeEquiv_heq C _ _ _)
  have step3 : chowPushforwardOfIso C (pullback.fst u (pullback.snd sX sZ) ≫ sY)
        (pullback.fst sY sX ≫ sY) (E ≫ σY) hEσ (n + m - p)
        (c.cap (pullback.snd sX sZ) (n + m) (exteriorProductOnTarget C hδ sX sZ n m γ ξ)) ≍
      chowPushforwardOfIso C (pullback.fst u (pullback.fst sZ sX) ≫ sY)
        (pullback.fst sY sX ≫ sY) F (exteriorCapFstIso_hom_comp_structureMorphism sX sZ u hu)
        (m + n - p)
        (c.cap (pullback.fst sZ sX) (m + n)
          (chowExteriorProduct C hδ sZ sX m n (TensorProduct.tmul ℤ ξ γ))) := by
    refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by omega) _ _ hcap).trans ?_
    rw [chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_congr_apply C _ _ (B ≫ E ≫ σY) F hsq]
  have step4 : chowPushforwardOfIso C (pullback.fst u (pullback.fst sZ sX) ≫ sY)
        (pullback.fst sY sX ≫ sY) F (exteriorCapFstIso_hom_comp_structureMorphism sX sZ u hu)
        (m + n - p)
        (c.cap (pullback.fst sZ sX) (m + n)
          (chowExteriorProduct C hδ sZ sX m n (TensorProduct.tmul ℤ ξ γ))) ≍
      capExteriorProductFst C hδ G sX sY sZ u hu p c m n ξ γ := by
    unfold capExteriorProductFst
    exact chowPushforwardOfIso_heq_congr C _ _ _ _ (by omega) _ _
      (chowGroupDegreeEquiv_heq C _ _ _).symm
  exact eq_of_heq (step1.trans (step2.trans (step3.trans step4)))

end FirstVariable

/-! ### The first-variable form over a field -/

section FieldFirstVariable

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z)
  [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ)
  (c : BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
    sY sZ u hu p)

/-- **Stacks 0FBY over a field, with the cap product in the first variable.** Let `k` be a field,
`X` locally of finite type over `k`, `u : Y ⟶ Z` a morphism of schemes locally of finite type
over `k`, and `c ∈ A^p(Y ⟶ Z)`. Then for every `ξ ∈ CH_m(Z)` and every `γ ∈ CH_n(X)`

  `(c ∩ ξ) × γ = c ∩ (ξ × γ)`   in   `CH_{(m - p) + n}(Y ×_k X)`.

This is `Stacks.Chow.chowExteriorProduct_capTarget_eq_capExteriorProductFst` for the classes for
which Stacks 0FBY holds, which over a field is all of them by
`Stacks.Chow.commutesExteriorProductCapAt_of_field`. -/
theorem chowExteriorProduct_capTarget_eq_capExteriorProductFst_of_field (m n : ℤ)
    (ξ : chowGroup (fieldChowSituation k) sZ m) (γ : chowGroup (fieldChowSituation k) sX n) :
    chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) sY sX (m - p) n
        (TensorProduct.tmul ℤ
          (c.capTarget (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
            sY sZ u hu p m ξ) γ) =
      capExteriorProductFst (fieldChowSituation k) (fun _ _ ↦ rfl)
        (gysinSystemOfInvertible (fieldChowSituation k)) sX sY sZ u hu p c m n ξ γ :=
  chowExteriorProduct_capTarget_eq_capExteriorProductFst (fieldChowSituation k) (fun _ _ ↦ rfl)
    (gysinSystemOfInvertible (fieldChowSituation k)) sX sY sZ u hu p c m n γ
    (commutesExteriorProductCapAt_of_field k sX sY sZ u hu p c n m γ) ξ

end FieldFirstVariable

end Stacks.Chow

end
