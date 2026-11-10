module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductBivariant
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.CapCommute
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductFlatPullback

/-!
# Stacks 0FBY: the exterior product commutes with capping by a bivariant class

Let `k` be a field, let `X` be a scheme locally of finite type over `k`, let `u : Y ⟶ Z` be a
morphism of schemes locally of finite type over `k` and let `c' ∈ A^q(Y ⟶ Z)`. **Stacks 0FBY**:

  `α × (c' ∩ β) = c' ∩ (α × β)`   in   `CH_*(X ×_k Y)`

for `α ∈ CH_*(X)` and `β ∈ CH_*(Z)`, where `×` is the exterior product of Stacks 0FBV.

## The proof

Write `α = ∑ₓ nₓ [closure {x}]`. Over a field the projection
`v_x : closure {x} ×_k Z ⟶ Z` is flat of relative dimension `dim closure {x}`, and `α × β` is the
locally finite sum over the points `x` of the support of `α` of the pushforwards along the closed
immersions `closure {x} ×_k Z ⟶ X ×_k Z` of the flat pullbacks `v_x^*(nₓ β)`
(`Stacks.Chow.exteriorProduct_apply_eq_finsum`). Capping with `c'` commutes with flat pullback by
the flat-pullback axiom of Stacks 0B76, the base change of `v_x` along `u` being the projection
`closure {x} ×_k Y ⟶ Y` (`Stacks.Chow.exists_cap_flatPullback_dedekindPointFibre`), and it
commutes with the locally finite sum by
`Stacks.Chow.BivariantClass.cap_chowGroupCongr_mk_eq_mk_of_locallyFinite`. The result is the same
decomposition of `α × (c' ∩ β)`.

This is the source's argument with the class `c_α` of Stacks 0FBW unwound: `c_α` is assembled
from proper pushforward, multiplication by integers and flat pullback, and `c'` commutes with each
of these (Stacks 0FBX). Only the flat-pullback and the proper-pushforward axioms of `c'` are used,
so the statement holds for bivariant classes at any Gysin system.

## Main results

* `Stacks.Chow.commutesExteriorProductCap_of_subsingleton` — **Stacks 0FBY** over a base which is
  a point with dimension function zero, for bivariant classes at any Gysin system.
* `Stacks.Chow.exteriorProductCap_eq_capExteriorProduct_field` — **Stacks 0FBY** over a field,
  for the group `A^q(Y ⟶ Z)` of Stacks 0B76.

## References

* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0FBX](https://stacks.math.columbia.edu/tag/0FBX)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The exterior product as a locally finite sum over the support of the first factor -/

section Decomposition

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g]

/-- The multiplicity of a point `ι_x w` of `closure {x} ×_S Y` in the product
`closure {x} ×_S closure {y}` is the multiplicity at `w` of the inverse image of `closure {y}`
under the projection `v_x : closure {x} ×_S Y ⟶ Y`. -/
theorem exteriorProductWeight_dedekindPointFibre (k : ℤ) (x : X) (y : Y)
    (w : (dedekindPointFibre f g x).subscheme) :
    exteriorProductWeight C f g k x y ((dedekindPointFibre f g x).subschemeι.base w) =
      closedSubschemeCycleCoeff C
        ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).comap
          ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)).subschemeι k w := by
  have hI : (dedekindPointFibre f g x).subschemeι.ker ≤
      (exteriorProductIdeal f g x y).subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι (exteriorProductIdeal f g x y)]
    exact ker_dedekindPointFibre_le f g x y
  have := isIso_pullback_snd_of_ker_le (dedekindPointFibre f g x).subschemeι
    (exteriorProductIdeal f g x y).subschemeι hI
  have hcomp : (((exteriorProductIdeal f g x y).comapIso
        (dedekindPointFibre f g x).subschemeι).trans
        (asIso (pullback.snd (dedekindPointFibre f g x).subschemeι
          (exteriorProductIdeal f g x y).subschemeι))).hom ≫
      (exteriorProductIdeal f g x y).subschemeι =
      ((exteriorProductIdeal f g x y).comap (dedekindPointFibre f g x).subschemeι).subschemeι ≫
        (dedekindPointFibre f g x).subschemeι := by
    change (((exteriorProductIdeal f g x y).comapIso (dedekindPointFibre f g x).subschemeι).hom ≫
      pullback.snd _ _) ≫ _ = _
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  rw [exteriorProductWeight,
    ← closedSubschemeCycleCoeff_eq_of_iso C (pullback.fst f g ≫ f) _ _ _ hcomp,
    closedSubschemeCycleCoeff_comp_isClosedImmersion C _ (pullback.fst f g ≫ f)
      (dedekindPointFibre f g x).subschemeι rfl,
    comap_exteriorProductIdeal_dedekindPointFibre]

variable [Subsingleton C.S] [IsIntegral C.S] (n m : ℤ)

open Classical in
/-- **The summand of `α × β` at a point `x` of `X`.** Over the spectrum of a field, the
pushforward along `ι_x : closure {x} ×_S Y ⟶ X ×_S Y` of the flat pullback of `α(x) · β` along
the flat projection `v_x : closure {x} ×_S Y ⟶ Y`, read in degree `n + m`, is the part of
`α × β` lying over `x`. -/
theorem properPushforward_flatPullback_dedekindPointFibre (α : CycleGroup C f n)
    (β : CycleGroup C g m) (x : X)
    [LocallyOfFiniteType ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)]
    [Flat ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension
      ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g) r)
    (hdeg : m + (r : ℤ) = n + m)
    (a : CycleGroup C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m))
    (ha : a.1 = (flatPullback C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
      g ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)
      (by rw [Category.assoc, ← pullback.condition]) r hr m (α.1 x • β)).1)
    (z : (pullback f g : Scheme.{u})) :
    (properPushforward C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
        (pullback.fst f g ≫ f) (dedekindPointFibre f g x).subschemeι rfl (n + m) a).1 z =
      if (pullback.fst f g).base z = x then exteriorProductCoeff C f g n m α β z else 0 := by
  by_cases hz : z ∈ Set.range (dedekindPointFibre f g x).subschemeι.base
  · obtain ⟨w, rfl⟩ := hz
    have hpt : (pullback.snd f g).base ((dedekindPointFibre f g x).subschemeι.base w) =
        ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g).base w :=
      (Scheme.Hom.comp_apply _ _ w).symm
    rw [properPushforward_apply_image_of_isClosedImmersion, ha, flatPullback_apply]
    have hsmul : ((α.1 x • β : CycleGroup C g m)).1
        (((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g).base w) =
        α.1 x * β.1 (((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g).base w) := by
      simp
    have hwt : flatPullbackWeight C
          ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
          ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g) (m + (r : ℤ)) w =
        exteriorProductWeight C f g (n + m) x
          (((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g).base w)
          ((dedekindPointFibre f g x).subschemeι.base w) := by
      rw [hdeg, exteriorProductWeight_dedekindPointFibre, flatPullbackWeight]
    rw [hsmul, hwt]
    by_cases hw : (pullback.fst f g).base ((dedekindPointFibre f g x).subschemeι.base w) = x
    · rw [ite_eq_left hw, exteriorProductCoeff, hw, hpt]
    · rw [ite_eq_right hw, exteriorProductWeight_eq_zero_of_ne C f g (n + m) x _ _ hw, mul_zero]
  · rw [properPushforward_apply_of_notMem_range C _ _ _ rfl _ _ hz]
    refine (ite_eq_right ?_).symm
    intro hzx
    refine hz ?_
    rw [(dedekindPointFibre f g x).range_subschemeι]
    have hmem : z ∈ (pullback.fst f g).base ⁻¹' closure ({x} : Set X) := by
      rw [Set.mem_preimage, hzx]
      exact subset_closure (Set.mem_singleton _)
    simpa [Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] using hmem

open Classical in
omit [Subsingleton C.S] [IsIntegral C.S] in
/-- **The exterior product is the locally finite sum of its summands over the points of the
support of the first factor.** If for each point `x` of the support of `α` the cycle `a x` on
`closure {x} ×_S Y` pushes forward to the part of `α × β` lying over `x`, then `α × β` is the
locally finite sum of these pushforwards. -/
theorem exteriorProduct_apply_eq_finsum (α : CycleGroup C f n) (β : CycleGroup C g m)
    (a : ∀ x : α.1.support,
      CycleGroup C ((dedekindPointFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m))
    (ha : ∀ (x : α.1.support) (z : (pullback f g : Scheme.{u})),
      (properPushforward C ((dedekindPointFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f))
        (pullback.fst f g ≫ f) (dedekindPointFibre f g x.1).subschemeι rfl (n + m) (a x)).1 z =
        if (pullback.fst f g).base z = x.1 then exteriorProductCoeff C f g n m α β z else 0)
    (z : (pullback f g : Scheme.{u})) :
    (exteriorProduct C f g n m α β).1 z = ∑ᶠ x : α.1.support,
      (properPushforward C ((dedekindPointFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f))
        (pullback.fst f g ≫ f) (dedekindPointFibre f g x.1).subschemeι rfl (n + m) (a x)).1 z := by
  simp_rw [ha]
  by_cases hz : α.1 ((pullback.fst f g).base z) = 0
  · have hterm : ∀ x : α.1.support,
        (if (pullback.fst f g).base z = x.1 then exteriorProductCoeff C f g n m α β z
          else 0) = 0 := by
      intro x
      by_cases hx : (pullback.fst f g).base z = x.1
      · rw [ite_eq_left hx, exteriorProductCoeff, hz, zero_mul, zero_mul]
      · rw [ite_eq_right hx]
    rw [finsum_eq_zero_of_forall_eq_zero hterm]
    change exteriorProductCoeff C f g n m α β z = 0
    rw [exteriorProductCoeff, hz, zero_mul, zero_mul]
  · rw [finsum_eq_single _ (⟨(pullback.fst f g).base z, hz⟩ : α.1.support)]
    · rw [ite_eq_left rfl]
      rfl
    · intro x hx
      exact ite_eq_right fun hxx ↦ hx (Subtype.ext hxx.symm)

end Decomposition

/-! ### The point fibres of `X ×_S Y` and of `X ×_S Z` -/

section Geometry

variable {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sZ : Z ⟶ S) (u : Y ⟶ Z) (x : X)

/-- Inside `X ×_S Y`, the subscheme `closure {x} ×_S Y` is the inverse image of
`closure {x} ×_S Z ⊆ X ×_S Z` under `1_X × u`. -/
theorem dedekindPointFibre_eq_comap_exteriorProductSndMap :
    dedekindPointFibre sX (u ≫ sZ) x =
      (dedekindPointFibre sX sZ x).comap (exteriorProductSndMap sX sZ (u ≫ sZ) u rfl) := by
  rw [dedekindPointFibre, dedekindPointFibre, ← Scheme.IdealSheafData.comap_comp,
    exteriorProductSndMap_comp_fst]

/-- The morphism `closure {x} ×_S Y ⟶ closure {x} ×_S Z` induced by `u`. -/
def pointFibreSndMap :
    (dedekindPointFibre sX (u ≫ sZ) x).subscheme ⟶ (dedekindPointFibre sX sZ x).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (exteriorProductSndMap sX sZ (u ≫ sZ) u rfl)
    (Scheme.IdealSheafData.le_map_iff_comap_le.2
      (le_of_eq (dedekindPointFibre_eq_comap_exteriorProductSndMap sX sZ u x).symm))

/-- The morphism `closure {x} ×_S Y ⟶ closure {x} ×_S Z` of `Stacks.Chow.pointFibreSndMap` is
compatible with the closed immersions into `X ×_S Y` and `X ×_S Z`: it is the restriction of
`1_X × u` to the two point fibres. -/
@[reassoc (attr := simp)]
theorem pointFibreSndMap_subschemeι :
    pointFibreSndMap sX sZ u x ≫ (dedekindPointFibre sX sZ x).subschemeι =
      (dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫
        exteriorProductSndMap sX sZ (u ≫ sZ) u rfl :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The square exhibiting `closure {x} ×_S Y` as `Y ×_Z (closure {x} ×_S Z)`. -/
theorem isPullback_pointFibreSndMap :
    IsPullback ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ pullback.snd sX (u ≫ sZ))
      (pointFibreSndMap sX sZ u x) u
      ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) :=
  (isPullback_subschemeMap_of_eq_comap (exteriorProductSndMap sX sZ (u ≫ sZ) u rfl) _ _
    (dedekindPointFibre_eq_comap_exteriorProductSndMap sX sZ u x)).paste_horiz
    (isPullback_exteriorProductSndMap sX sZ (u ≫ sZ) u rfl).flip

end Geometry

/-! ### Capping commutes with each summand -/

section Summand

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z)
  [LocallyOfFiniteType u] (p : ℤ) (c : BivariantClass C G (u ≫ sZ) sZ u rfl p) (n m : ℤ)

/-- **The summand at a point `x`.** Let `v_x : closure {x} ×_S Z ⟶ Z` and
`v'_x : closure {x} ×_S Y ⟶ Y` be the two projections, flat of relative dimension `r`, and let
`γ₀` represent `c ∩ [β₀]`. Then `c` capped with `v_x^*(e β₀)`, at the test scheme
`closure {x} ×_S Z ⟶ Z`, is represented by a cycle whose pushforward to `Y ×_Z (X ×_S Z)` is the
pushforward of `(v'_x)^*(e γ₀)` along `closure {x} ×_S Y ⟶ X ×_S Y ≅ Y ×_Z (X ×_S Z)`.

This is the flat-pullback axiom of Stacks 0B76 for `c` at `v_x`, read through the identification
`closure {x} ×_S Y ≅ Y ×_Z (closure {x} ×_S Z)` by Stacks 02RG for isomorphism legs. -/
theorem exists_cap_flatPullback_dedekindPointFibre (b₀ : CycleGroup C sZ m)
    (γ₀ : CycleGroup C (u ≫ sZ) (m - p))
    (hγ₀ : QuotientAddGroup.mk' (rationalEquivalences C (u ≫ sZ) (m - p)) γ₀ =
      c.capTarget C G (u ≫ sZ) sZ u rfl p m
        (QuotientAddGroup.mk' (rationalEquivalences C sZ m) b₀))
    (e : ℤ) (x : X) [Flat ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ)]
    [Flat ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ pullback.snd sX (u ≫ sZ))] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension
      ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) r)
    (hr' : AlgebraicGeometry.RelativeDimension
      ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ pullback.snd sX (u ≫ sZ)) r)
    (hdeg : m + (r : ℤ) = n + m) :
    ∃ b : CycleGroup C (pullback.fst u (((dedekindPointFibre sX sZ x).subschemeι ≫
        pullback.snd sX sZ) ≫ 𝟙 Z) ≫ (u ≫ sZ)) (n + m - p),
      QuotientAddGroup.mk' (rationalEquivalences C _ (n + m - p)) b =
        c.cap (((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) ≫ 𝟙 Z) (n + m)
          (chowGroupCongr C (by simp only [Category.comp_id, Category.assoc, pullback.condition])
            (n + m) (QuotientAddGroup.mk' (rationalEquivalences C _ (n + m))
              (hdeg ▸ flatPullback C ((dedekindPointFibre sX sZ x).subschemeι ≫
                (pullback.fst sX sZ ≫ sX)) sZ
                ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ)
                (by rw [Category.assoc, ← pullback.condition]) r hr m (e • b₀)))) ∧
      ∀ z, (properPushforward C (pullback.fst u (((dedekindPointFibre sX sZ x).subschemeι ≫
          pullback.snd sX sZ) ≫ 𝟙 Z) ≫ (u ≫ sZ))
          (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ))
          (testBaseChangeMapOfEq u (pullback.snd sX sZ) (dedekindPointFibre sX sZ x).subschemeι
            _ (Category.comp_id _).symm)
          (testBaseChangeMapOfEq_fst_assoc _ _ _ _ _ _) (n + m - p) b).1 z =
        (properPushforward C ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫
            (pullback.fst sX (u ≫ sZ) ≫ sX))
          (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ))
          ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ (exteriorCapIso sX sZ u rfl).inv)
          (by rw [Category.assoc, ← exteriorCapIso_hom_comp_structureMorphism sX sZ u rfl,
            Iso.inv_hom_id_assoc]) (m - p + (r : ℤ))
          (flatPullback C ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫
              (pullback.fst sX (u ≫ sZ) ≫ sX)) (u ≫ sZ)
            ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ pullback.snd sX (u ≫ sZ))
            (by rw [Category.assoc, ← pullback.condition]) r hr' (m - p) (e • γ₀))).1 z := by
  -- the identification `closure {x} ×_S Y ≅ Y ×_Z (closure {x} ×_S Z)`
  have hpb : IsPullback
      ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ pullback.snd sX (u ≫ sZ))
      (pointFibreSndMap sX sZ u x) u
      (((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) ≫ 𝟙 Z) := by
    simpa only [Category.comp_id] using isPullback_pointFibreSndMap sX sZ u x
  obtain ⟨ρ, hρiso, hρfst, hρsnd⟩ : ∃ ρ : (dedekindPointFibre sX (u ≫ sZ) x).subscheme ⟶
      pullback u (((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) ≫ 𝟙 Z),
      IsIso ρ ∧
      ρ ≫ pullback.fst u (((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) ≫ 𝟙 Z)
        = (dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ pullback.snd sX (u ≫ sZ) ∧
      ρ ≫ pullback.snd u (((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) ≫ 𝟙 Z)
        = pointFibreSndMap sX sZ u x :=
    ⟨hpb.isoPullback.hom, inferInstance, hpb.isoPullback_hom_fst, hpb.isoPullback_hom_snd⟩
  have hρbase : ρ ≫ (pullback.fst u (((dedekindPointFibre sX sZ x).subschemeι ≫
      pullback.snd sX sZ) ≫ 𝟙 Z) ≫ (u ≫ sZ)) =
      (dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ (pullback.fst sX (u ≫ sZ) ≫ sX) := by
    rw [reassoc_of% hρfst, ← pullback.condition]
  have hρtest : ρ ≫ testBaseChangeMapOfEq u (pullback.snd sX sZ)
      (dedekindPointFibre sX sZ x).subschemeι _ (Category.comp_id _).symm =
      (dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ (exteriorCapIso sX sZ u rfl).inv := by
    rw [Iso.eq_comp_inv]
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, exteriorCapIso_hom_fst, testBaseChangeMapOfEq_snd_assoc,
        reassoc_of% hρsnd, pointFibreSndMap_subschemeι_assoc, exteriorProductSndMap_comp_fst]
    · simp only [Category.assoc, exteriorCapIso_hom_snd, testBaseChangeMapOfEq_fst, hρfst]
  -- the base change of `v_x` to `Y`
  have hsqh := isPullback_bivariantBaseChangeMap u (𝟙 Z)
    ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ)
  have : LocallyOfFiniteType (bivariantBaseChangeMap u (𝟙 Z)
      ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ)) :=
    MorphismProperty.of_isPullback hsqh inferInstance
  have : Flat (bivariantBaseChangeMap u (𝟙 Z)
      ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ)) :=
    MorphismProperty.of_isPullback hsqh inferInstance
  have hrh : AlgebraicGeometry.RelativeDimension (bivariantBaseChangeMap u (𝟙 Z)
      ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ)) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hsqh hr
  have hu₀ : (pullbackIdIso u).hom ≫ (pullback.fst u (𝟙 Z) ≫ (u ≫ sZ)) = u ≫ sZ := by
    rw [pullbackIdIso_hom_fst_assoc]
  have hsq : ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ pullback.snd sX (u ≫ sZ)) ≫
      (pullbackIdIso u).hom = ρ ≫ bivariantBaseChangeMap u (𝟙 Z)
        ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullbackIdIso_hom_fst, Category.comp_id,
        bivariantBaseChangeMap_fst, hρfst]
    · simp only [Category.assoc, pullbackIdIso_hom_snd, bivariantBaseChangeMap, pullback.lift_snd,
        reassoc_of% hρsnd, pointFibreSndMap_subschemeι_assoc, exteriorProductSndMap_comp_snd]
  -- `c ∩ [β₀]` read on `Y ×_Z Z`
  have hcapβ : c.cap (𝟙 Z) m (chowGroupCongr C (Category.id_comp sZ).symm m
        (QuotientAddGroup.mk' (rationalEquivalences C sZ m) b₀)) =
      chowPushforwardOfIso C (u ≫ sZ) (pullback.fst u (𝟙 Z) ≫ (u ≫ sZ)) (pullbackIdIso u).hom
        hu₀ (m - p) (QuotientAddGroup.mk' (rationalEquivalences C (u ≫ sZ) (m - p)) γ₀) := by
    rw [hγ₀, BivariantClass.capTarget, chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_of_eq_id _ _ _ _ (Iso.inv_hom_id _)]
    rfl
  have hcap : c.cap (𝟙 Z) m (chowGroupCongr C (Category.id_comp sZ).symm m
        (QuotientAddGroup.mk' (rationalEquivalences C sZ m) (e • b₀))) =
      chowPushforwardOfIso C (u ≫ sZ) (pullback.fst u (𝟙 Z) ≫ (u ≫ sZ)) (pullbackIdIso u).hom
        hu₀ (m - p) (QuotientAddGroup.mk' (rationalEquivalences C (u ≫ sZ) (m - p))
          (e • γ₀)) := by
    rw [map_zsmul, map_zsmul, map_zsmul, hcapβ, map_zsmul, map_zsmul]
  -- the flat-pullback axiom of Stacks 0B76 at `v_x`
  have hnat := c.flat_naturality_of_relativeDimension (𝟙 Z)
    ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) r hr
    (bivariantBaseChangeMap u (𝟙 Z)
      ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ)) hsqh
    (bivariantBaseChangeMap_fst u (𝟙 Z) _) m hrh
    (chowGroupCongr C (Category.id_comp sZ).symm m
      (QuotientAddGroup.mk' (rationalEquivalences C sZ m) (e • b₀)))
  -- Stacks 02RG for the two isomorphism legs `pullbackIdIso u` and `ρ`
  have hbase' : ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ pullback.snd sX (u ≫ sZ)) ≫
      (u ≫ sZ) = (dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫
        (pullback.fst sX (u ≫ sZ) ≫ sX) := by
    rw [Category.assoc, ← pullback.condition]
  have h02RG := flatPullbackChow_chowPushforwardOfIso C (u ≫ sZ)
    ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ (pullback.fst sX (u ≫ sZ) ≫ sX))
    (pullback.fst u (𝟙 Z) ≫ (u ≫ sZ))
    (pullback.fst u (((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) ≫ 𝟙 Z) ≫
      (u ≫ sZ)) (pullbackIdIso u).hom hu₀ ρ hρbase
    ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ pullback.snd sX (u ≫ sZ)) hbase'
    (bivariantBaseChangeMap u (𝟙 Z)
      ((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ))
    (by rw [← Category.assoc, bivariantBaseChangeMap_fst]) hsq r hr' hrh (m - p)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (QuotientAddGroup.mk' (rationalEquivalences C (u ≫ sZ) (m - p)) (e • γ₀))
  have hdeg2 : m - p + (r : ℤ) = n + m - p := by omega
  refine ⟨hdeg2 ▸ properPushforward C ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫
      (pullback.fst sX (u ≫ sZ) ≫ sX))
      (pullback.fst u (((dedekindPointFibre sX sZ x).subschemeι ≫ pullback.snd sX sZ) ≫ 𝟙 Z) ≫
        (u ≫ sZ)) ρ hρbase (m - p + (r : ℤ))
      (flatPullback C ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫
          (pullback.fst sX (u ≫ sZ) ≫ sX)) (u ≫ sZ)
        ((dedekindPointFibre sX (u ≫ sZ) x).subschemeι ≫ pullback.snd sX (u ≫ sZ)) hbase' r hr'
        (m - p) (e • γ₀)), ?_, fun z ↦ ?_⟩
  · apply eq_of_heq
    refine (mk_cast_heq _ hdeg2 _).trans ?_
    rw [← chowPushforwardOfIso_mk, ← flatPullbackChow_mk C _ _ _ hbase' r hr' (m - p)
      (flatPullbackDescends C _ _ _ _ _ _ _), ← h02RG, ← hcap]
    refine hnat.symm.trans ?_
    refine BivariantClass.cap_heq c _ hdeg ?_
    refine HEq.trans ?_ (chowGroupCongr_heq C _ _ _).symm
    refine HEq.trans ?_ (mk_cast_heq _ hdeg _).symm
    refine HEq.trans ?_ (heq_of_eq (flatPullbackChow_mk C _ _ _
      (by rw [Category.assoc, ← pullback.condition]) r hr m
      (flatPullbackDescends C _ _ _ _ _ _ _) _))
    exact flatPullbackChow_heq_congr_base C
      (by simp only [Category.comp_id, Category.assoc, pullback.condition])
      (Category.id_comp sZ) rfl _ _ rfl _ _ rfl _ _ _ _ (chowGroupCongr_heq C _ _ _)
  · rw [properPushforward_val_cast, properPushforward_properPushforward,
      properPushforward_congr C _ _ _ _ hρtest]

end Summand

/-! ### Stacks 0FBY -/

section Main

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (u : Y ⟶ Z) [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ)

/-- **Stacks 0FBY over a point.** Let the base be a point with dimension function zero, for
instance the spectrum of a field, let `X` be locally of finite type over it, let `u : Y ⟶ Z` be a
morphism of schemes locally of finite type over it and let `c ∈ A^p(Y ⟶ Z)` be a bivariant class
for any Gysin system. Then for all `α ∈ CH_n(X)` and `β ∈ CH_m(Z)`

  `α × (c ∩ β) = c ∩ (α × β)`   in   `CH_{n + (m - p)}(X ×_S Y)`.

Write `α = ∑ₓ nₓ [closure {x}]`. Then `α × β` is the locally finite sum over the points `x` of the
support of `α` of the pushforwards along `closure {x} ×_S Z ⟶ X ×_S Z` of the flat pullbacks of
`nₓ β` along the flat projections `closure {x} ×_S Z ⟶ Z`. Capping with `c` commutes with each of
these flat pullbacks by the flat-pullback axiom of Stacks 0B76, and with the locally finite sum by
`Stacks.Chow.BivariantClass.cap_chowGroupCongr_mk_eq_mk_of_locallyFinite`; the result is the
corresponding decomposition of `α × (c ∩ β)`. -/
@[stacks 0FBY "α × (c ∩ β) = c ∩ (α × β) in CH_*(X ×_S Y), over a base which is a point with \
dimension function zero (in particular Spec k), for bivariant classes at any Gysin system"]
theorem commutesExteriorProductCap_of_subsingleton (c : BivariantClass C G sY sZ u hu p)
    (n m : ℤ) : CommutesExteriorProductCap C hδ G sX sY sZ u hu p c n m := by
  classical
  subst hu
  intro α β
  obtain ⟨a₀, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sX n) α
  obtain ⟨b₀, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sZ m) β
  obtain ⟨γ₀, hγ₀⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C (u ≫ sZ) (m - p))
    (c.capTarget C G (u ≫ sZ) sZ u rfl p m
      (QuotientAddGroup.mk' (rationalEquivalences C sZ m) b₀))
  -- the relative dimension of the points of the support of `α`
  have hrel : ∀ x : a₀.1.support, relativeDimension C.dimensionFunction sX x.1 = n :=
    fun x ↦ (mem_cyclesOfDimension_iff_forall_point C sX n a₀.1).1 a₀.2 x.1 x.2
  have hdeg : ∀ x : a₀.1.support, m + (n.toNat : ℤ) = n + m := fun x ↦ by
    have h := relativeDimension_nonneg C hδ sX x.1
    rw [hrel x] at h
    omega
  have hdegY : ∀ x : a₀.1.support, m - p + (n.toNat : ℤ) = n + (m - p) := fun x ↦ by
    have := hdeg x
    omega
  have : ∀ {W : Scheme.{u}} (g : W ⟶ C.S) (x : X),
      Flat ((dedekindPointFibre sX g x).subschemeι ≫ pullback.snd sX g) :=
    fun g x ↦ flat_pointClosurePullback_snd sX g x
  have hrW : ∀ {W : Scheme.{u}} (g : W ⟶ C.S) [LocallyOfFiniteType g] (x : a₀.1.support),
      AlgebraicGeometry.RelativeDimension
        ((dedekindPointFibre sX g x.1).subschemeι ≫ pullback.snd sX g) n.toNat :=
    fun g _ x ↦ relativeDimension_pointClosureFibreSnd C hδ sX g n x.1 (hrel x)
  -- the summands of `α × β` and of `α × (c ∩ β)`
  set a : ∀ x : a₀.1.support, CycleGroup C ((dedekindPointFibre sX sZ x.1).subschemeι ≫
      (pullback.fst sX sZ ≫ sX)) (n + m) := fun x ↦
    hdeg x ▸ flatPullback C ((dedekindPointFibre sX sZ x.1).subschemeι ≫
      (pullback.fst sX sZ ≫ sX)) sZ ((dedekindPointFibre sX sZ x.1).subschemeι ≫
        pullback.snd sX sZ) (by rw [Category.assoc, ← pullback.condition]) n.toNat (hrW sZ x) m
      (a₀.1 x.1 • b₀) with ha
  set a' : ∀ x : a₀.1.support, CycleGroup C ((dedekindPointFibre sX (u ≫ sZ) x.1).subschemeι ≫
      (pullback.fst sX (u ≫ sZ) ≫ sX)) (n + (m - p)) := fun x ↦
    hdegY x ▸ flatPullback C ((dedekindPointFibre sX (u ≫ sZ) x.1).subschemeι ≫
      (pullback.fst sX (u ≫ sZ) ≫ sX)) (u ≫ sZ)
      ((dedekindPointFibre sX (u ≫ sZ) x.1).subschemeι ≫ pullback.snd sX (u ≫ sZ))
      (by rw [Category.assoc, ← pullback.condition]) n.toNat (hrW (u ≫ sZ) x) (m - p)
      (a₀.1 x.1 • γ₀) with ha'
  have hP1 : ∀ (x : a₀.1.support) (z : (pullback sX sZ : Scheme.{u})),
      (properPushforward C ((dedekindPointFibre sX sZ x.1).subschemeι ≫
        (pullback.fst sX sZ ≫ sX)) (pullback.fst sX sZ ≫ sX)
        (dedekindPointFibre sX sZ x.1).subschemeι rfl (n + m) (a x)).1 z =
        if (pullback.fst sX sZ).base z = x.1 then exteriorProductCoeff C sX sZ n m a₀ b₀ z
        else 0 := fun x z ↦
    properPushforward_flatPullback_dedekindPointFibre C sX sZ n m a₀ b₀ x.1 n.toNat (hrW sZ x)
      (hdeg x) (a x) (val_cycleGroup_cast C _ (hdeg x) _) z
  have hP2 : ∀ (x : a₀.1.support) (z : (pullback sX (u ≫ sZ) : Scheme.{u})),
      (properPushforward C ((dedekindPointFibre sX (u ≫ sZ) x.1).subschemeι ≫
        (pullback.fst sX (u ≫ sZ) ≫ sX)) (pullback.fst sX (u ≫ sZ) ≫ sX)
        (dedekindPointFibre sX (u ≫ sZ) x.1).subschemeι rfl (n + (m - p)) (a' x)).1 z =
        if (pullback.fst sX (u ≫ sZ)).base z = x.1 then
          exteriorProductCoeff C sX (u ≫ sZ) n (m - p) a₀ γ₀ z
        else 0 := fun x z ↦
    properPushforward_flatPullback_dedekindPointFibre C sX (u ≫ sZ) n (m - p) a₀ γ₀ x.1 n.toNat
      (hrW (u ≫ sZ) x) (hdegY x) (a' x) (val_cycleGroup_cast C _ (hdegY x) _) z
  have hcap := fun x : a₀.1.support ↦ exists_cap_flatPullback_dedekindPointFibre sX sZ u p c n m
    b₀ γ₀ hγ₀ (a₀.1 x.1) x.1 n.toNat (hrW sZ x) (hrW (u ≫ sZ) x) (hdeg x)
  choose b hP3 hP4 using hcap
  -- the two locally finite families
  have hfin : ∀ {W : Scheme.{u}} (g : W ⟶ C.S) [LocallyOfFiniteType g],
      LocallyFinite fun x : a₀.1.support ↦ Set.range (dedekindPointFibre sX g x.1).subschemeι :=
    fun g _ ↦ (locallyFinite_dedekindPointFibre sX g a₀.1).subset fun x ↦ by
      rw [Scheme.IdealSheafData.range_subschemeι]
  have hinvbase : (exteriorCapIso sX sZ u rfl).inv ≫
      (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ)) = pullback.fst sX (u ≫ sZ) ≫ sX := by
    rw [← exteriorCapIso_hom_comp_structureMorphism sX sZ u rfl, Iso.inv_hom_id_assoc]
  have hdq : n + (m - p) = n + m - p := by ring
  set E := exteriorProduct C sX (u ≫ sZ) n (m - p) a₀ γ₀ with hE
  -- capping commutes with the locally finite sum
  have key := c.cap_chowGroupCongr_mk_eq_mk_of_locallyFinite (pullback.snd sX sZ)
    (pullback.fst sX sZ ≫ sX) (pullback.condition (f := sX) (g := sZ)).symm (n + m)
    (fun x : a₀.1.support ↦ (dedekindPointFibre sX sZ x.1).subschemeι) (hfin sZ)
    (fun x ↦ ((dedekindPointFibre sX sZ x.1).subschemeι ≫ pullback.snd sX sZ) ≫ 𝟙 Z)
    (fun x ↦ (Category.comp_id _).symm)
    (fun x ↦ (dedekindPointFibre sX sZ x.1).subschemeι ≫ (pullback.fst sX sZ ≫ sX))
    (fun _ ↦ rfl) a (exteriorProduct C sX sZ n m a₀ b₀)
    (exteriorProduct_apply_eq_finsum C sX sZ n m a₀ b₀ a hP1) b hP3
    (cycleOfDegreeEq _ hdq (properPushforward C (pullback.fst sX (u ≫ sZ) ≫ sX)
      (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ)) (exteriorCapIso sX sZ u rfl).inv
      hinvbase (n + (m - p)) E)) (fun z ↦ ?_)
  · simp only [exteriorProductCap, capExteriorProduct, exteriorProductOnTarget]
    rw [← hγ₀]
    change QuotientAddGroup.mk' _ E = _
    change _ = chowPushforwardOfIso C _ _ _ _ _ (chowGroupDegreeEquiv C _ _ (c.cap _ _
      (chowGroupCongr C _ (n + m) (QuotientAddGroup.mk' _ (exteriorProduct C sX sZ n m a₀ b₀)))))
    have hD : chowGroupDegreeEquiv C (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ))
        hdq.symm (QuotientAddGroup.mk' _ (cycleOfDegreeEq _ hdq
          (properPushforward C (pullback.fst sX (u ≫ sZ) ≫ sX)
            (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ)) (exteriorCapIso sX sZ u rfl).inv
            hinvbase (n + (m - p)) E))) =
        QuotientAddGroup.mk' _ (properPushforward C (pullback.fst sX (u ≫ sZ) ≫ sX)
          (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ)) (exteriorCapIso sX sZ u rfl).inv
          hinvbase (n + (m - p)) E) :=
      chowGroupDegreeEquiv_mk_eq_mk_of_val C _ _ _ _ rfl
    rw [key, hD, chowPushforwardOfIso_mk, properPushforward_properPushforward,
      properPushforward_congr C _ _ _ (𝟙 _) (Iso.inv_hom_id _) _ (Category.id_comp _),
      properPushforward_id]
  · -- the right hand side is the locally finite sum of the transported summands
    rw [show (cycleOfDegreeEq _ hdq (properPushforward C (pullback.fst sX (u ≫ sZ) ≫ sX)
        (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ)) (exteriorCapIso sX sZ u rfl).inv
        hinvbase (n + (m - p)) E)).1 z =
      AlgebraicCycle.map (exteriorCapIso sX sZ u rfl).inv
        (relativeDimension C.dimensionFunction (pullback.fst sX (u ≫ sZ) ≫ sX))
        (relativeDimension C.dimensionFunction
          (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ))) E.1 z from rfl]
    rw [algebraicCycle_map_finsum_apply (exteriorCapIso sX sZ u rfl).inv _ _
      (fun x : a₀.1.support ↦ Set.range (dedekindPointFibre sX (u ≫ sZ) x.1).subschemeι)
      (hfin (u ≫ sZ))
      (fun x ↦ (properPushforward C _ _ (dedekindPointFibre sX (u ≫ sZ) x.1).subschemeι rfl
        (n + (m - p)) (a' x)).1)
      (fun x ↦ support_properPushforward_subset C _ _ _ _ _ _) _
      (exteriorProduct_apply_eq_finsum C sX (u ≫ sZ) n (m - p) a₀ γ₀ a' hP2) z]
    refine finsum_congr fun x ↦ ?_
    rw [hP4 x z]
    refine (congrArg (fun c : CycleGroup C _ _ ↦ c.1 z)
      (properPushforward_properPushforward C _ _ _ _ _ rfl hinvbase _ _)).trans ?_
    rw [ha', properPushforward_val_cast]

end Main

section Field

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z) (hu : u ≫ sZ = sY)
  (q : ℤ)

/-- **Stacks 0FBY.** Let `k` be a field, let `X` be a scheme locally of finite type over `k`, let
`u : Y ⟶ Z` be a morphism of schemes locally of finite type over `k` and let
`c' ∈ A^q(Y ⟶ Z)`. Then for `α ∈ CH_n(X)` and `β ∈ CH_m(Z)`

  `α × (c' ∩ β) = c' ∩ (α × β)`   in   `CH_{n + (m - q)}(X ×_k Y)`.

Here `A^q(Y ⟶ Z)` is the group of bivariant classes of Stacks 0B76, the exterior product is that
of Stacks 0FBV, and the two sides are those of `Stacks.Chow.exteriorProductCap` and
`Stacks.Chow.capExteriorProduct`: `c' ∩ β` is read on `Y ≅ Y ×_Z Z`, and `c' ∩ (α × β)` is the
cap at the test scheme `X ×_k Z ⟶ Z`, read on `X ×_k Y ≅ Y ×_Z (X ×_k Z)`. -/
@[stacks 0FBY "α × (c' ∩ β) = c' ∩ (α × β) in CH_*(X ×_k Y), for k a field and c' ∈ A^q(Y → Z) \
of Stacks 0B76"]
theorem exteriorProductCap_eq_capExteriorProduct_field
    (c' : BivariantChowClass (fieldChowSituation k) sY sZ u hu q) (n m : ℤ)
    (α : chowGroup (fieldChowSituation k) sX n) (β : chowGroup (fieldChowSituation k) sZ m) :
    haveI := BivariantChowClass.locallyOfFiniteType_of_structure sZ u hu
    exteriorProductCap (fieldChowSituation k) (fun _ _ ↦ rfl)
        (gysinSystemOfInvertible (fieldChowSituation k)) sX sY sZ u hu q
        (BivariantChowClass.equivBivariantClass c') n m α β =
      capExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
        (gysinSystemOfInvertible (fieldChowSituation k)) sX sY sZ u hu q
        (BivariantChowClass.equivBivariantClass c') n m α β :=
  have := BivariantChowClass.locallyOfFiniteType_of_structure sZ u hu
  commutesExteriorProductCap_of_subsingleton (fieldChowSituation k) (fun _ _ ↦ rfl)
    (gysinSystemOfInvertible (fieldChowSituation k)) sX sY sZ u hu q
    (BivariantChowClass.equivBivariantClass c') n m α β

end Field

end Stacks.Chow

end
