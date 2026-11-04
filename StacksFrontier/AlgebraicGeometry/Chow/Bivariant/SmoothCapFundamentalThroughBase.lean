module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalIso
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackNaturalityInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothRelativeDimensionShift
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindBivariantIdentification
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClassCharacterized

/-!
# The map of Stacks 0FC2 through the base

Let `k` be a field, or more generally let the base `S` be as in section 42.63 of the Stacks
Project, and let `g : X ⟶ S` be flat of relative dimension `e`. The map
`c ↦ c ∩ [X]_{m+e}` of `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalIso`
factors through the base: as `c ↦ c ∘ g^*`, composition with the flat-pullback class of the
structure morphism, followed by cap product with the fundamental class `[S]_m` of the base.

## Main definitions

* `Stacks.Chow.congrHomAddHom` — `Stacks.Chow.BivariantClass.congrHom` as an additive map.
* `Stacks.Chow.compStructureFlatPullbackClass` — `c ↦ c ∘ g^*` as an additive map.

## Main results

* `Stacks.Chow.chowPushforwardOfIso_cap_comp_structureFlatPullbackClass` —
  `(c ∘ g^*) ∩ [S]_m = c ∩ [X]_{m+e}`.
* `Stacks.Chow.chowCohomologyCapFundamentalClass_eq_bivariantToBaseEval`,
  `Stacks.Chow.chowCohomologyCapFundamentalClass_bijective_of_bivariantToBaseEval` — over a field,
  the map of Stacks 0FC2 is the composite of `c ↦ c ∘ g^*` and the evaluation map of Stacks 0FBW,
  hence bijective when both are.
* `Stacks.Chow.chowCohomologyCapFundamentalClass_eq_bivariantCapBaseFundamentalClass`,
  `Stacks.Chow.chowCohomologyCapFundamentalClass_bijective_of_bivariantCapBaseFundamentalClass` —
  the same over a base as in section 42.63, through Stacks 0FC5.

Stacks 0FC2 itself, and Stacks 0FCB, are assembled from these in
`StacksFrontier.AlgebraicGeometry.Chow.SmoothChowCohomology`.

## References

* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Tag 0FCB](https://stacks.math.columbia.edu/tag/0FCB)
* [Stacks Project, Tag 0FBT](https://stacks.math.columbia.edu/tag/0FBT)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Reading a bivariant class for an equal morphism, additively -/

section CongrHom

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f f' : X ⟶ Y}
  [LocallyOfFiniteType f] [LocallyOfFiniteType f'] {hf : f ≫ sY = sX} {p : ℤ}

/-- `Stacks.Chow.BivariantClass.congrHom` as an additive map `A^p(X ⟶ Y) ⟶ A^p(X ⟶ Y)` between
the groups of two equal morphisms. -/
def congrHomAddHom (e : f = f') (hf' : f' ≫ sY = sX) :
    BivariantClass C G sX sY f hf p →+ BivariantClass C G sX sY f' hf' p where
  toFun c := c.congrHom e hf'
  map_zero' := by subst e; rfl
  map_add' _ _ := by subst e; rfl

end CongrHom

/-! ### Capping `[X]` through the base: the composite with the smooth pullback class -/

section ThroughBase

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [Flat sX] (e : ℕ) (he : AlgebraicGeometry.RelativeDimension sX e) (m p : ℤ)

/-- **The computation behind Stacks 0FC2 and 0FCB.** For `c ∈ A^p(X)` and `g : X ⟶ S` flat of
relative dimension `e`, capping the composite `c ∘ g^* ∈ A^{p-e}(X ⟶ S)` with the fundamental
class `[S]_m` of the base, `dim_δ S ≤ m`, is capping `c` with `[X]_{m+e}`:

  `(c ∘ g^*) ∩ [S]_m = c ∩ (g^* ∩ [S]_m) = c ∩ [X]_{m+e}`,

each side read on `X` through the canonical identifications of the fibre products. -/
theorem chowPushforwardOfIso_cap_comp_structureFlatPullbackClass
    (hdim : schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ (m : EInt)) (n : ℤ) (hn : n = m + e)
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    chowPushforwardOfIso C (pullback.fst (𝟙 X ≫ sX) (𝟙 C.S) ≫ sX) sX
        (pullback.fst (𝟙 X ≫ sX) (𝟙 C.S)) rfl (m - (p + -(e : ℤ)))
        ((bivariantCompositeOfInvertible C sX sX (𝟙 C.S) (𝟙 X) sX (Category.id_comp sX)
          (Category.comp_id sX) p (-(e : ℤ)) c
          (smoothShiftFlatPullbackClass C sX (𝟙 C.S) sX (Category.comp_id sX) e he)).cap
          (𝟙 C.S) m (fundamentalChowClass C (𝟙 C.S ≫ 𝟙 C.S) m)) ≍
      chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX n p c := by
  subst hn
  set h : (pullback sX (𝟙 C.S) : Scheme.{u}) ⟶ X := pullback.fst sX (𝟙 C.S) with hh
  set k : ℤ := m - -(e : ℤ) with hk
  -- `g^* ∩ [S]_m = [X ×_S S]_k`
  have hstar :
      (smoothShiftFlatPullbackClass C sX (𝟙 C.S) sX (Category.comp_id sX) e he).cap (𝟙 C.S) m
      (fundamentalChowClass C (𝟙 C.S ≫ 𝟙 C.S) m) = fundamentalChowClass C (h ≫ sX) k :=
    IsBivariantFlatPullback.cap_fundamentalChowClass
      (hdesc := flatPullbackDescends C)
        (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sX (𝟙 C.S) sX
        (Category.comp_id sX) e he) (𝟙 C.S) m hdim
  -- `h_*[X ×_S S]_k = [X]_k`, and the cap of `c` commutes with `h_*`
  have hpush : chowPushforwardOfIso C (h ≫ sX) (𝟙 X ≫ sX) h (by simp) k
      (fundamentalChowClass C (h ≫ sX) k) = fundamentalChowClass C (𝟙 X ≫ sX) k :=
    chowPushforwardOfIso_fundamentalChowClass C _ _ h _ k
  have hcap := BivariantClass.cap_chowPushforwardOfTestIso C (gysinSystemOfInvertible C) sX sX
    (𝟙 X) (Category.id_comp sX) p c (𝟙 X) h (Category.comp_id h) k
    (fundamentalChowClass C (h ≫ sX) k)
  rw [hpush] at hcap
  -- the left-hand side, unfolded
  have hL : (bivariantCompositeOfInvertible C sX sX (𝟙 C.S) (𝟙 X) sX (Category.id_comp sX)
          (Category.comp_id sX) p (-(e : ℤ)) c
          (smoothShiftFlatPullbackClass C sX (𝟙 C.S) sX (Category.comp_id sX) e he)).cap
          (𝟙 C.S) m (fundamentalChowClass C (𝟙 C.S ≫ 𝟙 C.S) m) ≍
      chowPushforwardOfIso C (pullback.fst (𝟙 X) h ≫ sX) (pullback.fst (𝟙 X ≫ sX) (𝟙 C.S) ≫ sX)
        (pullbackRightPullbackFstIso sX (𝟙 C.S) (𝟙 X)).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sX (𝟙 X) sX (𝟙 C.S)) (k - p)
        (c.cap h k (fundamentalChowClass C (h ≫ sX) k)) := by
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    rw [bivariantCompositeCap_apply, hstar]
    rfl
  refine (chowPushforwardOfIso_heq_congr C _ _ _ rfl (by ring) _ _ hL).trans ?_
  rw [chowPushforwardOfIso_comp_apply]
  -- the right-hand side, unfolded
  rw [chowCohomologyCapFundamentalClass_apply, chowGroupSelfUnitCollapse,
    chowGroupEquivOfIso_apply]
  have hR : chowPushforwardOfIso C (pullback.fst (𝟙 X) (𝟙 X) ≫ sX) sX
        (pullback.fst (𝟙 X) (𝟙 X)) rfl (k - p)
        (c.cap (𝟙 X) k (fundamentalChowClass C (𝟙 X ≫ sX) k)) ≍
      chowPushforwardOfIso C (pullback.fst (𝟙 X) (𝟙 X) ≫ sX) sX
        (pullback.fst (𝟙 X) (𝟙 X)) rfl ((m + e) - p)
        (c.cap (𝟙 X) (m + e) (selfFundamentalClass C sX (m + e))) :=
    chowPushforwardOfIso_heq_congr C _ _ _ rfl (by rw [hk]; ring) _ _
      (BivariantClass.cap_heq_congr c (𝟙 X) (by rw [hk]; ring) _ _
        (fundamentalChowClass_heq C _ (by rw [hk]; ring)))
  refine HEq.trans ?_ hR
  rw [hcap, chowPushforwardOfIso_comp_apply]
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ (k - p) _)
  simp only [hh, pullbackBaseChangeOfTestIso_hom_fst, pullbackRightPullbackFstIso_hom_fst]
  all_goals rfl

/-- The composite `c ↦ c ∘ g^*`, `A^p(X) ⟶ A^{p-e}(X ⟶ S)`, read as a class for the structure
morphism `g` itself rather than for `𝟙 X ≫ g`. This is the first arrow of the factorization of
the map of Stacks 0FC2 and Stacks 0FCB; Stacks 0FBT says it is bijective. -/
def compStructureFlatPullbackClass :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX p →+
      BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX)
        (p + -(e : ℤ)) :=
  (congrHomAddHom (Category.id_comp sX) (Category.comp_id sX)).comp
    (smoothShiftForward C sX sX (𝟙 C.S) (𝟙 X) sX (Category.id_comp sX) (Category.comp_id sX) e
      he p)

/-- `compStructureFlatPullbackClass` sends `c` to the composite of `c` with the flat-pullback
class of `g`, transported along `𝟙 X ≫ g = g` and `g ≫ 𝟙 S = g`. -/
theorem compStructureFlatPullbackClass_apply
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    compStructureFlatPullbackClass C sX e he p c =
      (bivariantCompositeOfInvertible C sX sX (𝟙 C.S) (𝟙 X) sX (Category.id_comp sX)
        (Category.comp_id sX) p (-(e : ℤ)) c
        (smoothShiftFlatPullbackClass C sX (𝟙 C.S) sX (Category.comp_id sX) e he)).congrHom
        (Category.id_comp sX) (Category.comp_id sX) :=
  rfl

/-- A map that agrees pointwise with a composite of three bijections is bijective. -/
private theorem bijective_of_eq_comp_comp {α β γ δ : Sort*} {f : α → δ} {t : α → β} {w : β → γ}
    {g : γ → δ} (h : ∀ c, f c = g (w (t c))) (ht : Function.Bijective t)
    (hw : Function.Bijective w) (hg : Function.Bijective g) : Function.Bijective f := by
  rw [show f = g ∘ w ∘ t from funext h]
  exact hg.comp (hw.comp ht)

/-- **The factorization of the map of Stacks 0FC2.** Over any base, for `g : X ⟶ S` flat of
relative dimension `e` and `dim_δ S ≤ 0`, the map `c ↦ c ∩ [X]_e` of Stacks 0FC2 is the
composite of `c ↦ c ∘ g^*` with the canonical map `c' ↦ c' ∩ [S]` of Stacks 0FBW, up to the
transport of degrees `-(p - e) = e - p`. -/
theorem chowCohomologyCapFundamentalClass_eq_bivariantToBaseEval
    (hdim : schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ ((0 : ℤ) : EInt))
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX e p c =
      chowGroupDegreeEquiv C sX (by ring)
        (bivariantToBaseEval C (gysinSystemOfInvertible C) sX (p + -(e : ℤ))
          (compStructureFlatPullbackClass C sX e he p c)) := by
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq C sX _ _).symm)
  refine HEq.symm (HEq.trans ?_
    (chowPushforwardOfIso_cap_comp_structureFlatPullbackClass C sX e he 0 p hdim e (by ring) c))
  rw [bivariantToBaseEval_apply, chowGroupBaseUnitCollapse, AddEquiv.trans_apply,
    chowGroupEquivOfIso_apply]
  refine (chowPushforwardOfIso_heq_congr C _ _ _ rfl (by ring) _ _
    (chowGroupDegreeEquiv_heq C _ _ _)).trans ?_
  rw [compStructureFlatPullbackClass_apply, BivariantClass.congrHom_cap,
    chowPushforwardOfIso_comp_apply]
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _)
  simp

/-- **Stacks 0FC2 from Stacks 0FBT and Stacks 0FBW.** Over a base with `dim_δ S ≤ 0` whose
canonical map `A^q(X ⟶ S) ⟶ CH_{-q}(X)` is bijective (Stacks 0FBW), the map `c ↦ c ∩ [X]_e` is
bijective as soon as `c ↦ c ∘ g^*` is (Stacks 0FBT). -/
theorem chowCohomologyCapFundamentalClass_bijective_of_bivariantToBaseEval
    (hdim : schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ ((0 : ℤ) : EInt))
    (hT : Function.Bijective (compStructureFlatPullbackClass C sX e he p))
    (hW : Function.Bijective
      (bivariantToBaseEval C (gysinSystemOfInvertible C) sX (p + -(e : ℤ)))) :
    Function.Bijective
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX e p) := by
  exact bijective_of_eq_comp_comp
    (chowCohomologyCapFundamentalClass_eq_bivariantToBaseEval C sX e he p hdim) hT hW
    (chowGroupDegreeEquiv C sX _).bijective

/-- **The factorization of the map of Stacks 0FCB.** Over any base, for `g : X ⟶ S` flat of
relative dimension `e` and `dim_δ S ≤ 1`, the map `c ↦ c ∩ [X]_{e+1}` of Stacks 0FCB is the
composite of `c ↦ c ∘ g^*` with the canonical map `c' ↦ c' ∩ [S]_1` of Stacks 0FC5, up to the
transport of degrees `1 - (p - e) = (e + 1) - p`. -/
theorem chowCohomologyCapFundamentalClass_eq_bivariantCapBaseFundamentalClass
    (hdim : schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ ((1 : ℤ) : EInt))
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) p c =
      chowGroupDegreeEquiv C sX (by ring)
        (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX (p + -(e : ℤ))
          (compStructureFlatPullbackClass C sX e he p c)) := by
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq C sX _ _).symm)
  refine HEq.symm (HEq.trans ?_
    (chowPushforwardOfIso_cap_comp_structureFlatPullbackClass C sX e he 1 p hdim (e + 1)
      (by ring) c))
  rw [bivariantCapBaseFundamentalClass_apply, basePullbackPushforward,
    properChowPushforward_eq_chowPushforwardOfIso, compStructureFlatPullbackClass_apply,
    baseFundamentalChowClass, BivariantClass.congrHom_cap, chowPushforwardOfIso_comp_apply]
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _)
  simp

/-- **Stacks 0FCB from Stacks 0FBT and Stacks 0FC5.** Over a base with `dim_δ S ≤ 1` whose
canonical map `A^q(X ⟶ S) ⟶ CH_{1-q}(X)` is bijective (Stacks 0FC5), the map
`c ↦ c ∩ [X]_{e+1}` is bijective as soon as `c ↦ c ∘ g^*` is (Stacks 0FBT). -/
theorem chowCohomologyCapFundamentalClass_bijective_of_bivariantCapBaseFundamentalClass
    (hdim : schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ ((1 : ℤ) : EInt))
    (hT : Function.Bijective (compStructureFlatPullbackClass C sX e he p))
    (hW : Function.Bijective
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX (p + -(e : ℤ)))) :
    Function.Bijective
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) p) := by
  exact bijective_of_eq_comp_comp
    (chowCohomologyCapFundamentalClass_eq_bivariantCapBaseFundamentalClass C sX e he p hdim) hT hW
    (chowGroupDegreeEquiv C sX _).bijective

end ThroughBase

end Stacks.Chow

end
