module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseProper
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindBivariantIdentification
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField

/-!
# Bivariant classes towards a Dedekind base commute with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `c ∈ A^p(X ⟶ S)` and let `c' ∈ A^q(Y ⟶ Z)` for a morphism
`Y ⟶ Z` of schemes locally of finite type over `S`. **Stacks 0FC6** asserts, over a base as in
section 42.63 (Tag 0FC3), that `c ∘ c' = c' ∘ c`. Its proof reads off from the proof of
Stacks 0FC5 that `c` is built from proper pushforward, integral combinations, flat pullback and
Gysin maps, and observes that `c'` commutes with each of these operations by the definition of a
bivariant class.

The first part of this file proves that every class built from those operations commutes with
every `c'`, in the sense of `Stacks.Chow.BivariantCommuteOverBase`. The operations are recorded
by the inductive predicate `Stacks.Chow.IsChowOperationClassOverBase`: flat-pullback classes of
flat structure morphisms of some relative dimension (Stacks 0B78), Gysin classes of divisors of
sections of invertible modules on the base (Stacks 0B79), flat pullback after a class already
built, proper pushforward of a class already built (Stacks 0EPK), and sums and negatives.

The second part proves Stacks 0FC6 over a base with no zero-dimensional component. A class is
*central over the base* (`Stacks.Chow.IsCentralOverBase`) when it commutes with every `c'`; the
central classes form a subgroup. By Stacks 0FC5
(`Stacks.Chow.bivariantCapBaseFundamentalClass_bijective`) `c ↦ c ∩ [S]₁` identifies
`A^p(X ⟶ S)` with `CH_{1-p}(X)`, so it suffices that the images of central classes generate
`CH_{1-p}(X)`. The generators of the proof of Stacks 0FC5 are
`g_* ∘ ξ` with `g : W = ∐_j closure{y_j} ⟶ X`. Over generic points of the base `ξ` is a flat
pullback class. Over closed points `ξ` is assembled by Stacks 0FDZ from the classes
`(p'_j)^* ∘ c_{s_j}` on the summands, `c_{s_j}` the Gysin class of the closed point `s_j`, which
is an effective Cartier divisor on the base
(`Stacks.Chow.IsDedekindChowBase.isEffectiveCartierDivisor_integralComponentAt`).
Each summand class is built by the operations, and commuting is local on a decomposition into
open and closed pieces (`Stacks.Chow.bivariantCommuteOverBase_of_forall_piece`), so the
assembled class is central.

## Main definitions

* `Stacks.Chow.IsFlatPullbackAfter` — the assertion that `c ∈ A^{p-r}(X ⟶ S)` is the composite
  `π^* ∘ b` of `b ∈ A^p(D ⟶ S)` with flat pullback along a flat `π : X ⟶ D` of relative
  dimension `r`.
* `Stacks.Chow.IsGysinOverBase` — the assertion that `b ∈ A^1(D ⟶ S)` is the Gysin class of the
  divisor `D = Z(σ)` of a section `σ` of an invertible module on the base.
* `Stacks.Chow.IsChowOperationClassOverBase` — the classes towards the base built by the
  operations above.
* `Stacks.Chow.IsCentralOverBase`, `Stacks.Chow.centralOverBaseSubgroup` — the classes towards
  the base commuting with every bivariant class, and the subgroup they form.

## Main results

* `Stacks.Chow.bivariantCommuteOverBase_of_isFlatPullbackAfter` — commuting with `c'` passes
  from `b` to `π^* ∘ b`.
* `Stacks.Chow.bivariantCommuteOverBase_of_isGysinOverBase` — the Gysin class of a divisor on the
  base commutes with every `c'`.
* `Stacks.Chow.bivariantCommuteOverBase_of_isChowOperationClassOverBase_ofInvertible` — every
  class built by the operations of chapter 42 commutes with every bivariant class over the base.
* `Stacks.Chow.bivariantCommuteOverBase_of_forall_piece` — commuting is local on a decomposition
  of the source into open and closed subschemes.
* `Stacks.Chow.exists_isChowOperationClassOverBase_cap_eq_of_closedPoint` — the vertical
  generators of the proof of Stacks 0FC5 are built by the operations of chapter 42.
* `Stacks.Chow.isCentralOverBase_of_isDedekindChowBase`,
  `Stacks.Chow.bivariantCommuteOverBase_of_isDedekindChowBase` — **Stacks 0FC6** over a base as
  in section 42.63 with no zero-dimensional component.

## Implementation notes

The commutation of the Gysin class `b` of `D = Z(σ) ⊆ S` with `c'` is the Gysin axiom of
Stacks 0B76 for `c'` at the divisor `Z(sZ^* σ)` of `Z` pulled back to a test scheme
`t : T ⟶ Z`, in the form `Stacks.Chow.BivariantClass.gysin_naturality_gysinCap` used for
Stacks 0FA3. The cap operation of `b` at `t` is the Gysin map of `σ` pulled back along `t ≫ sZ`,
whereas that axiom produces the Gysin map of `σ` pulled back first along `sZ` and then along `t`;
the two zero schemes are equal and the two Gysin maps agree by
`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward`, a theorem at the canonical
Gysin system. What remains is an identity of isomorphisms of iterated fibre products, checked
on their projections.

The source proves Stacks 0FC6 for every base as in section 42.63, which allows Dedekind domains
of the covering that are fields, that is, zero-dimensional components of the base on which `δ`
vanishes. The results here assume `Stacks.Chow.HasNoZeroDimensionalComponent`, under which
Stacks 0FC5 holds (`Stacks.Chow.bivariantCapBaseFundamentalClass_bijective`); on a
zero-dimensional component the canonical map of Stacks 0FC5 is not injective, so the argument
through it does not apply there, although the statement of Stacks 0FC6 is still true, by
Stacks 0FBX over the residue field of the component.

## Contents of this part

This first part covers the classes built by the operations of chapter 42: flat pullback after a
class towards the base, the Gysin class of a divisor on the base, the inductive predicate
`Stacks.Chow.IsChowOperationClassOverBase`, and the theorem that every class it records commutes
with every bivariant class over the base. Locality on open and closed pieces, central classes and
the vertical generators are in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseUnconditional.CentralClasses`;
the generation of the Chow groups and Stacks 0FC6 itself are in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseUnconditional.Generation`.

## References

* [Stacks Project, Tag 0FC6](https://stacks.math.columbia.edu/tag/0FC6)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FBX](https://stacks.math.columbia.edu/tag/0FBX)
* [Stacks Project, Tag 0FA3](https://stacks.math.columbia.edu/tag/0FA3)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Flat pullback after a class towards the base -/

/-- The comparison isomorphisms of the iterated fibre products of `X` and of `D` are compatible
with the two base changes of a morphism `π : X ⟶ D` over the base. -/
theorem mixedCommuteHom_comp_baseChangeMapOfEq {C : ChowSituation.{u}} {X D Y Z T : Scheme.{u}}
    (sD : D ⟶ C.S) (π : X ⟶ D) (sZ : Z ⟶ C.S) (w : Y ⟶ Z) (t : T ⟶ Z) :
    mixedCommuteHom (π ≫ sD) sZ w t ≫
        baseChangeMapOfEq w (pullback.snd sD (t ≫ sZ) ≫ t)
          (bivariantPushforwardBaseChange π sD (t ≫ sZ))
          (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t)
          (by rw [← Category.assoc, bivariantPushforwardBaseChange_snd]) =
      bivariantPushforwardBaseChange π sD (pullback.fst w t ≫ (w ≫ sZ)) ≫
        mixedCommuteHom sD sZ w t := by
  refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;>
    simp [bivariantPushforwardBaseChange]

section FlatAfter

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X D Y Z : Scheme.{u}} (sD : D ⟶ C.S)
  [LocallyOfFiniteType sD] (π : X ⟶ D) [LocallyOfFiniteType π] [Flat π] (r : ℕ)
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z) [LocallyOfFiniteType w] (p q : ℤ)

omit [Flat π] in
/-- The assertion that `c ∈ A^{p-r}(X ⟶ S)` is the composite `π^* ∘ b` of a class
`b ∈ A^p(D ⟶ S)` with flat pullback along a flat morphism `π : X ⟶ D` of relative dimension `r`:
capping with `c` at a test scheme `u : U ⟶ S` is capping with `b` followed by flat pullback along
the base change `X ×_S U ⟶ D ×_S U` of `π`. -/
def IsFlatPullbackAfter (b : BivariantClass C G sD (𝟙 C.S) sD (Category.comp_id sD) p)
    (c : BivariantClass C G (π ≫ sD) (𝟙 C.S) (π ≫ sD) (Category.comp_id (π ≫ sD))
      (p - (r : ℤ))) : Prop :=
  ∀ {U : Scheme.{u}} (u : U ⟶ C.S) [LocallyOfFiniteType u]
    [LocallyOfFiniteType (bivariantPushforwardBaseChange π sD u)]
    [Flat (bivariantPushforwardBaseChange π sD u)]
    (hr : AlgebraicGeometry.RelativeDimension (bivariantPushforwardBaseChange π sD u) r) (k : ℤ)
    (α : chowGroup C (u ≫ 𝟙 C.S) k),
    c.cap u k α ≍
      flatPullbackChow C (pullback.fst (π ≫ sD) u ≫ (π ≫ sD)) (pullback.fst sD u ≫ sD)
        (bivariantPushforwardBaseChange π sD u)
        (bivariantPushforwardBaseChange_comp_structure rfl sD u) r hr (k - p)
        (flatPullbackDescends C _ _ _ _ _ _ _) (b.cap u k α)

/-- **The flat-pullback step of the proof of Stacks 0FC6.** If `b ∈ A^p(D ⟶ S)` commutes with
`c' ∈ A^q(Y ⟶ Z)` and `π : X ⟶ D` is flat of relative dimension `r`, then the composite
`π^* ∘ b ∈ A^{p-r}(X ⟶ S)` commutes with `c'`: capping with `c'` commutes with flat pullback by
the flat axiom of Stacks 0B76, read through the comparison isomorphisms of the iterated fibre
products. -/
theorem bivariantCommuteOverBase_of_isFlatPullbackAfter
    (hr : AlgebraicGeometry.RelativeDimension π r)
    (b : BivariantClass C G sD (𝟙 C.S) sD (Category.comp_id sD) p)
    (c : BivariantClass C G (π ≫ sD) (𝟙 C.S) (π ≫ sD) (Category.comp_id (π ≫ sD))
      (p - (r : ℤ)))
    (c' : BivariantClass C G (w ≫ sZ) sZ w rfl q)
    (hb : BivariantCommuteOverBase C G sD sZ w p q b c')
    (hc : IsFlatPullbackAfter C G sD π r p b c) :
    BivariantCommuteOverBase C G (π ≫ sD) sZ w (p - (r : ℤ)) q c c' := by
  intro T t _ k α
  have bc : ∀ {U : Scheme.{u}} (u : U ⟶ C.S),
      ∃ (_ : LocallyOfFiniteType (bivariantPushforwardBaseChange π sD u))
        (_ : Flat (bivariantPushforwardBaseChange π sD u)),
        AlgebraicGeometry.RelativeDimension (bivariantPushforwardBaseChange π sD u) r :=
    fun u ↦ let sq := isPullback_bivariantPushforwardBaseChange π sD u
      ⟨MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance,
        MorphismProperty.of_isPullback sq (P := @Flat) inferInstance,
        AlgebraicGeometry.RelativeDimension.of_isPullback sq hr⟩
  obtain ⟨_, _, hrT⟩ := bc (t ≫ sZ)
  obtain ⟨_, _, hrV⟩ := bc (pullback.fst w t ≫ (w ≫ sZ))
  have hm : bivariantPushforwardBaseChange π sD (t ≫ sZ) ≫ (pullback.snd sD (t ≫ sZ) ≫ t) =
      pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t := by
    rw [← Category.assoc, bivariantPushforwardBaseChange_snd]
  have sq' := isPullback_baseChangeMapOfEq w (pullback.snd sD (t ≫ sZ) ≫ t)
    (bivariantPushforwardBaseChange π sD (t ≫ sZ)) (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) hm
  have := locallyOfFiniteType_baseChangeMapOfEq w (pullback.snd sD (t ≫ sZ) ≫ t)
    (bivariantPushforwardBaseChange π sD (t ≫ sZ)) (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) hm
  have := flat_baseChangeMapOfEq w (pullback.snd sD (t ≫ sZ) ≫ t)
    (bivariantPushforwardBaseChange π sD (t ≫ sZ)) (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) hm
  have hr' : AlgebraicGeometry.RelativeDimension (baseChangeMapOfEq w
      (pullback.snd sD (t ≫ sZ) ≫ t) (bivariantPushforwardBaseChange π sD (t ≫ sZ))
      (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) hm) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sq' hrT
  have hmb : bivariantPushforwardBaseChange π sD (t ≫ sZ) ≫
      ((pullback.snd sD (t ≫ sZ) ≫ t) ≫ sZ) = (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) ≫ sZ := by
    rw [← Category.assoc, hm]
  have eD : pullback.fst sD (t ≫ sZ) ≫ sD = (pullback.snd sD (t ≫ sZ) ≫ t) ≫ sZ := by
    rw [Category.assoc]; exact pullback.condition
  have eX : pullback.fst (π ≫ sD) (t ≫ sZ) ≫ (π ≫ sD) =
      (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) ≫ sZ := by
    rw [Category.assoc]; exact pullback.condition
  have hnat := c'.flat_naturality_of_test_eq (pullback.snd sD (t ≫ sZ) ≫ t)
    (bivariantPushforwardBaseChange π sD (t ≫ sZ)) r hrT
    (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) hm _ sq' (baseChangeMapOfEq_fst _ _ _ _ _) (k - p)
    hmb hr' (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (chowGroupCongr C eD (k - p)
      (b.cap (t ≫ sZ) k (chowGroupCongr C (Category.comp_id (t ≫ sZ)).symm k α)))
  have hcT := hc (t ≫ sZ) hrT k (chowGroupCongr C (Category.comp_id (t ≫ sZ)).symm k α)
  have hcV := hc (pullback.fst w t ≫ (w ≫ sZ)) hrV (k - q)
    (chowGroupCongr C (Category.comp_id (pullback.fst w t ≫ (w ≫ sZ))).symm (k - q)
      (c'.cap t k α))
  have hbt := hb t k α
  have h02RG := flatPullbackChow_chowPushforwardOfIso C
    (pullback.fst sD (pullback.fst w t ≫ (w ≫ sZ)) ≫ sD)
    (pullback.fst (π ≫ sD) (pullback.fst w t ≫ (w ≫ sZ)) ≫ (π ≫ sD))
    (pullback.fst w (pullback.snd sD (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
    (pullback.fst w (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
    (mixedCommuteHom sD sZ w t) (mixedCommuteHom_comp_structureMorphism sD sZ w t)
    (mixedCommuteHom (π ≫ sD) sZ w t) (mixedCommuteHom_comp_structureMorphism (π ≫ sD) sZ w t)
    (bivariantPushforwardBaseChange π sD (pullback.fst w t ≫ (w ≫ sZ)))
    (bivariantPushforwardBaseChange_comp_structure rfl sD _)
    (baseChangeMapOfEq w (pullback.snd sD (t ≫ sZ) ≫ t)
      (bivariantPushforwardBaseChange π sD (t ≫ sZ)) (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) hm)
    (baseChangeMapOfEq_comp_structure _ _ _ _ _ _)
    (mixedCommuteHom_comp_baseChangeMapOfEq sD π sZ w t).symm r hrV hr' (k - q - p)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (mixedIteratedCapBaseLast C G sD sZ w p q b c' t k α)
  rw [hbt] at h02RG
  simp only [mixedIteratedCapBaseFirst_apply, mixedIteratedCapBaseLast_apply] at h02RG ⊢
  refine eq_of_heq (HEq.trans ?_ (HEq.symm (chowGroupDegreeEquiv_heq C
    (pullback.fst w (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)) _ _)))
  refine HEq.trans (chowPushforwardOfIso_heq (mixedCommuteHom (π ≫ sD) sZ w t)
    (mixedCommuteHom_comp_structureMorphism (π ≫ sD) sZ w t)
    (mixedCommuteHom_comp_structureMorphism (π ≫ sD) sZ w t) rfl rfl (by ring) hcV) ?_
  refine HEq.trans (heq_of_eq h02RG.symm) (HEq.trans ?_ (HEq.trans hnat.symm ?_))
  · exact flatPullbackChow_heq_congr_base C rfl rfl rfl _ _ rfl _ _ (by ring) _ _ _ _
      (chowGroupDegreeEquiv_heq C _ _ _)
  refine BivariantClass.cap_heq c' (pullback.snd (π ≫ sD) (t ≫ sZ) ≫ t) (by ring) ?_
  refine HEq.trans ?_ (chowGroupCongr_heq C _ _ _).symm
  refine HEq.trans ?_ hcT.symm
  exact flatPullbackChow_heq_congr_base C eX.symm eD.symm rfl _ _ rfl _ _ rfl _ _ _ _
    (chowGroupCongr_heq C _ _ _)

end FlatAfter


/-! ### Heterogeneous congruences for the Gysin map and for composites of isomorphisms -/

section HeqCongr

variable {C : ChowSituation.{u}}

/-- The Gysin map of a Gysin system respects equality of the structure morphism over the base and
heterogeneous equality of its argument. -/
theorem GysinSystem.onChow_heq_congr_base (G : GysinSystem C) {T : Scheme.{u}}
    {q q' : T ⟶ C.S} [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q')
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) (x : chowGroup C q (k + 1)) (x' : chowGroup C q' (k + 1))
    (hx : x ≍ x') : G.onChow q L s k x ≍ G.onChow q' L s k x' := by
  subst hq
  obtain rfl := eq_of_heq hx
  rfl

/-- Pushing forward along an isomorphism `v` and then along an isomorphism `u` over the base is
pushing forward along `v ≫ u`, the intermediate structure morphism and degree being matched only
up to equality and heterogeneous equality. -/
theorem chowPushforwardOfIso_comp_heq {A B E : Scheme.{u}} {sA : A ⟶ C.S} {sB sB' : B ⟶ C.S}
    {sE : E ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] [LocallyOfFiniteType sB']
    [LocallyOfFiniteType sE] (v : A ⟶ B) [IsIso v] (u : B ⟶ E) [IsIso u] (hv : v ≫ sB = sA)
    (hu : u ≫ sE = sB') (hB : sB = sB') {k k' : ℤ} (hk : k = k')
    (x : chowGroup C sA k) (y : chowGroup C sB' k')
    (hy : y ≍ chowPushforwardOfIso C sA sB v hv k x) :
    chowPushforwardOfIso C sB' sE u hu k' y ≍
      chowPushforwardOfIso C sA sE (v ≫ u) (by rw [Category.assoc, hu, ← hB, hv]) k x := by
  subst hk
  subst hB
  obtain rfl := eq_of_heq hy
  rw [chowPushforwardOfIso_comp_apply]

end HeqCongr

/-! ### The Gysin class of a divisor on the base -/

section GysinBase

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y Z : Scheme.{u}} (L : C.S.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.S.sheaf.obj C.S.ringCatSheaf.property L]
  (σ : Γ(L, ⊤)) (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z) [LocallyOfFiniteType w]
  (q : ℤ)

/-- The assertion that `b ∈ A^1(D ⟶ S)` is the Gysin class of Stacks 0B79 of the divisor
`D = Z(σ)` of a global section `σ` of an invertible module on the base: capping with `b` at a
test scheme `u : U ⟶ S` is the Gysin map of the pulled-back section, read on `D ×_S U` through
the identification of Stacks 0B6Y. -/
def IsGysinOverBase
    (b : BivariantClass C G (gysinTripleInclusion L σ) (𝟙 C.S) (gysinTripleInclusion L σ)
      (Category.comp_id _) 1) : Prop :=
  ∀ {U : Scheme.{u}} (u : U ⟶ C.S) [LocallyOfFiniteType u] (k : ℤ)
    (α : chowGroup C (u ≫ 𝟙 C.S) k),
    b.cap u k α ≍ gysinBivariantCap C G (𝟙 C.S) L σ u k α

/-- **Stacks 0B79 towards the base.** The Gysin class of a divisor on the base exists: it is the
class `Stacks.Chow.gysinBivariantClass` of the triple on `S`, read with the structure morphism
`D ⟶ S` of its source in place of `D ⟶ S ⟶ S`. -/
theorem exists_isGysinOverBase :
    ∃ b : BivariantClass C (gysinSystemOfInvertible C) (gysinTripleInclusion L σ) (𝟙 C.S)
      (gysinTripleInclusion L σ) (Category.comp_id _) 1,
      IsGysinOverBase C (gysinSystemOfInvertible C) L σ b :=
  ⟨bivariantClassCongrBase C (gysinSystemOfInvertible C) (gysinTripleInclusion L σ)
      (Category.comp_id _) rfl (hv := rfl) (hv' := Category.comp_id _) 1
      (gysinBivariantClass C (𝟙 C.S) L σ).1,
    fun u _ k α ↦ (bivariantClassCongrBase_cap C (gysinSystemOfInvertible C)
      (gysinTripleInclusion L σ) (Category.comp_id _) rfl 1 _ u k α α HEq.rfl).trans
        (heq_of_eq ((gysinBivariantClass C (𝟙 C.S) L σ).2 u k α))⟩

/-- **The Gysin step of the proof of Stacks 0FC6.** The Gysin class `b ∈ A^1(D ⟶ S)` of a
divisor `D = Z(σ)` on the base commutes with every bivariant class `c' ∈ A^q(Y ⟶ Z)` over the
base: the identity to be proved is the Gysin axiom of Stacks 0B76 for `c'` at the divisor pulled
back to the test scheme, read through the identifications of Stacks 0B6Y. -/
theorem bivariantCommuteOverBase_of_isGysinOverBase
    (hG : G.IsNaturalUnderPullbackCompPushforward)
    (b : BivariantClass C G (gysinTripleInclusion L σ) (𝟙 C.S) (gysinTripleInclusion L σ)
      (Category.comp_id _) 1)
    (c' : BivariantClass C G (w ≫ sZ) sZ w rfl q) (hb : IsGysinOverBase C G L σ b) :
    BivariantCommuteOverBase C G (gysinTripleInclusion L σ) sZ w 1 q b c' := by
  intro T t _ k α
  -- the divisor on `T` pulled back in two steps and in one step
  have h0 := Stacks.Divisors.zeroScheme_pullback_comp_eq t sZ (t ≫ sZ) rfl L σ
  have hE1 : (eqToHom (congrArg Scheme.IdealSheafData.subscheme h0) ≫
      (gysinDivisorBaseChangeIso L σ (t ≫ sZ)).hom) ≫
        pullback.snd (gysinTripleInclusion L σ) (t ≫ sZ) =
      (gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t).subschemeι := by
    rw [Category.assoc, gysinDivisorBaseChangeIso_hom_snd, subschemeι_eqToHom h0]
  have hm : (eqToHom (congrArg Scheme.IdealSheafData.subscheme h0) ≫
      (gysinDivisorBaseChangeIso L σ (t ≫ sZ)).hom) ≫
        (pullback.snd (gysinTripleInclusion L σ) (t ≫ sZ) ≫ t) =
      (gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t).subschemeι ≫
        t := by
    rw [← Category.assoc, hE1]
  have eD : pullback.fst (gysinTripleInclusion L σ) (t ≫ sZ) ≫ gysinTripleInclusion L σ =
      (pullback.snd (gysinTripleInclusion L σ) (t ≫ sZ) ≫ t) ≫ sZ := by
    rw [Category.assoc]; exact pullback.condition
  have hmb : (eqToHom (congrArg Scheme.IdealSheafData.subscheme h0) ≫
      (gysinDivisorBaseChangeIso L σ (t ≫ sZ)).hom) ≫
        ((pullback.snd (gysinTripleInclusion L σ) (t ≫ sZ) ≫ t) ≫ sZ) =
      (gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t).subschemeι ≫
        (t ≫ sZ) := by
    rw [← Category.assoc, hm, Category.assoc]
  -- the inner Gysin class on `T`, read on `D ×_S T`
  have hin : chowGroupCongr C eD (k - 1)
      (b.cap (t ≫ sZ) k (chowGroupCongr C (Category.comp_id (t ≫ sZ)).symm k α)) =
      chowPushforwardOfIso C
        ((gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t).subschemeι ≫
          (t ≫ sZ))
        ((pullback.snd (gysinTripleInclusion L σ) (t ≫ sZ) ≫ t) ≫ sZ)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme h0) ≫
          (gysinDivisorBaseChangeIso L σ (t ≫ sZ)).hom) hmb (k - 1)
        (G.onChow (t ≫ sZ) (gysinTripleModule (gysinTripleModule L sZ) t)
          (gysinTripleSection (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t) (k - 1)
          (chowGroupDegreeEquiv C (t ≫ sZ) (show k = k - 1 + 1 by ring) α)) := by
    have hpc := G.onChow_pullbackComp hG t sZ (t ≫ sZ) rfl ((t ≫ sZ) ≫ 𝟙 C.S) L σ (k - 1)
      (chowGroupDegreeEquiv C ((t ≫ sZ) ≫ 𝟙 C.S) (show k = k - 1 + 1 by ring)
        (chowGroupCongr C (Category.comp_id (t ≫ sZ)).symm k α))
    refine eq_of_heq ((chowGroupCongr_heq C _ _ _).trans ((hb (t ≫ sZ) k _).trans ?_))
    rw [gysinBivariantCap_apply, ← hpc, chowPushforwardOfIso_comp_apply]
    refine chowPushforwardOfIso_heq _ _ _ (by simp) (by simpa using eD) rfl ?_
    exact G.onChow_heq_congr_base (Category.comp_id _) _ _ _ _ _
      ((chowGroupDegreeEquiv_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans
        (chowGroupDegreeEquiv_heq C _ _ _).symm))
  -- the Gysin axiom of `c'` at the divisor pulled back to `T`
  have h3 := c'.gysin_naturality_gysinCap C G sZ (gysinTripleModule L sZ)
    (gysinTripleSection L σ sZ) w q hG t k α
  -- the outer Gysin class on `Y ×_Z T`
  have h2 := Stacks.Divisors.zeroScheme_pullback_comp_eq (pullback.fst w t ≫ w) sZ
    (pullback.fst w t ≫ (w ≫ sZ)) (Category.assoc _ _ _) L σ
  have hpcV := G.onChow_pullbackComp hG (pullback.fst w t ≫ w) sZ (pullback.fst w t ≫ (w ≫ sZ))
    (Category.assoc _ _ _) ((pullback.fst w t ≫ (w ≫ sZ)) ≫ 𝟙 C.S) L σ (k - q - 1)
    (chowGroupDegreeEquiv C ((pullback.fst w t ≫ (w ≫ sZ)) ≫ 𝟙 C.S)
      (show k - q = k - q - 1 + 1 by ring)
      (chowGroupCongr C (Category.comp_id (pullback.fst w t ≫ (w ≫ sZ))).symm (k - q)
        (c'.cap t k α)))
  have hout := hb (pullback.fst w t ≫ (w ≫ sZ)) (k - q)
    (chowGroupCongr C (Category.comp_id (pullback.fst w t ≫ (w ≫ sZ))).symm (k - q)
      (c'.cap t k α))
  rw [gysinBivariantCap_apply, ← hpcV, chowPushforwardOfIso_comp_apply] at hout
  -- the comparison of the isomorphisms
  have hiso : ((bivariantDivisorBaseChangeIso w t
        (gysinTripleModule (gysinTripleModule L sZ) t)
        (gysinTripleSection (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t)).hom ≫
      eqToHom (congrArg Scheme.IdealSheafData.subscheme
        (Stacks.Divisors.zeroScheme_pullback_comp_eq (pullback.snd w t) t
          (pullback.fst w t ≫ w) pullback.condition.symm (gysinTripleModule L sZ)
          (gysinTripleSection L σ sZ)))) ≫
      ((eqToHom (congrArg Scheme.IdealSheafData.subscheme h2) ≫
        (gysinDivisorBaseChangeIso L σ (pullback.fst w t ≫ (w ≫ sZ))).hom) ≫
        mixedCommuteHom (gysinTripleInclusion L σ) sZ w t) =
      (testBaseChangeIso w (pullback.snd (gysinTripleInclusion L σ) (t ≫ sZ) ≫ t)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme h0) ≫
          (gysinDivisorBaseChangeIso L σ (t ≫ sZ)).hom)
        ((gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t).subschemeι ≫
          t) hm).hom := by
    have k0 := subschemeι_eqToHom h0
    have k1 := subschemeι_eqToHom h2
    have k2 := subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback_comp_eq (pullback.snd w t) t
      (pullback.fst w t ≫ w) pullback.condition.symm (gysinTripleModule L sZ)
      (gysinTripleSection L σ sZ))
    have k3 := bivariantDivisorBaseChangeIso_hom_subschemeι w t
      (gysinTripleModule (gysinTripleModule L sZ) t)
      (gysinTripleSection (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t)
    have k4 := gysinDivisorBaseChangeIso_hom_comp_test L σ (pullback.fst w t ≫ (w ≫ sZ))
    have k5 := gysinDivisorBaseChangeIso_hom_comp_test L σ (t ≫ sZ)
    have kV : (bivariantDivisorBaseChangeIso w t
        (gysinTripleModule (gysinTripleModule L sZ) t)
        (gysinTripleSection (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t)).hom ≫
        eqToHom (congrArg Scheme.IdealSheafData.subscheme
          (Stacks.Divisors.zeroScheme_pullback_comp_eq (pullback.snd w t) t
            (pullback.fst w t ≫ w) pullback.condition.symm (gysinTripleModule L sZ)
            (gysinTripleSection L σ sZ))) ≫
        eqToHom (congrArg Scheme.IdealSheafData.subscheme h2) ≫
        (gysinDivisorBaseChangeIso L σ (pullback.fst w t ≫ (w ≫ sZ))).hom ≫
        pullback.snd (gysinTripleInclusion L σ) (pullback.fst w t ≫ (w ≫ sZ)) =
        bivariantBaseChangeMap w t
          (gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t).subschemeι
          := by
      rw [gysinDivisorBaseChangeIso_hom_snd, k1, k2, k3]
    have kV' : (bivariantDivisorBaseChangeIso w t
        (gysinTripleModule (gysinTripleModule L sZ) t)
        (gysinTripleSection (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t)).hom ≫
        eqToHom (congrArg Scheme.IdealSheafData.subscheme
          (Stacks.Divisors.zeroScheme_pullback_comp_eq (pullback.snd w t) t
            (pullback.fst w t ≫ w) pullback.condition.symm (gysinTripleModule L sZ)
            (gysinTripleSection L σ sZ))) ≫
        eqToHom (congrArg Scheme.IdealSheafData.subscheme h2) ≫
        (gysinDivisorBaseChangeIso L σ (pullback.fst w t ≫ (w ≫ sZ))).hom ≫
        pullback.fst (gysinTripleInclusion L σ) (pullback.fst w t ≫ (w ≫ sZ)) ≫
          gysinTripleInclusion L σ =
        bivariantBaseChangeMap w t
          (gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t).subschemeι ≫
          (pullback.fst w t ≫ (w ≫ sZ)) := by
      rw [k4, reassoc_of% k1, reassoc_of% k2, reassoc_of% k3]
    have kT : eqToHom (congrArg Scheme.IdealSheafData.subscheme h0) ≫
        (gysinDivisorBaseChangeIso L σ (t ≫ sZ)).hom ≫
        pullback.fst (gysinTripleInclusion L σ) (t ≫ sZ) ≫ gysinTripleInclusion L σ =
        (gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t).subschemeι ≫
          (t ≫ sZ) := by
      rw [k5, reassoc_of% k0]
    have kT' : eqToHom (congrArg Scheme.IdealSheafData.subscheme h0) ≫
        (gysinDivisorBaseChangeIso L σ (t ≫ sZ)).hom ≫
        pullback.snd (gysinTripleInclusion L σ) (t ≫ sZ) =
        (gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t).subschemeι := by
      rw [gysinDivisorBaseChangeIso_hom_snd, k0]
    refine pullback.hom_ext ?_
      (pullback.hom_ext ((cancel_mono (gysinTripleInclusion L σ)).mp ?_) ?_)
    · simp only [Category.assoc, mixedCommuteHom_fst, testBaseChangeIso_hom_fst]
      rw [reassoc_of% kV]
      simp [bivariantBaseChangeMap]
    · simp only [Category.assoc, mixedCommuteHom_snd_assoc, mixedCommuteSnd_fst_assoc,
        testBaseChangeIso_hom_snd_assoc]
      rw [kV', kT]
      simp [bivariantBaseChangeMap, pullback.condition_assoc]
    · simp only [Category.assoc, mixedCommuteHom_snd_assoc, mixedCommuteSnd_snd,
        testBaseChangeIso_hom_snd_assoc]
      rw [reassoc_of% kV, kT']
      simp [bivariantBaseChangeMap]
  simp only [mixedIteratedCapBaseFirst_apply, mixedIteratedCapBaseLast_apply]
  rw [hin, c'.cap_chowPushforwardOfIso (pullback.snd (gysinTripleInclusion L σ) (t ≫ sZ) ≫ t)
    (eqToHom (congrArg Scheme.IdealSheafData.subscheme h0) ≫
      (gysinDivisorBaseChangeIso L σ (t ≫ sZ)).hom)
    ((gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ) t).subschemeι ≫ t)
    hm _ (Category.assoc _ _ _).symm (k - 1) hmb _ _ rfl]
  have hstr : ((eqToHom (congrArg Scheme.IdealSheafData.subscheme h2) ≫
      (gysinDivisorBaseChangeIso L σ (pullback.fst w t ≫ (w ≫ sZ))).hom) ≫
        mixedCommuteHom (gysinTripleInclusion L σ) sZ w t) ≫
      (pullback.fst w (pullback.snd (gysinTripleInclusion L σ) (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)) =
      (gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ)
        (pullback.fst w t ≫ w)).subschemeι ≫ ((pullback.fst w t ≫ w) ≫ sZ) := by
    rw [Category.assoc, Category.assoc, mixedCommuteHom_comp_structureMorphism,
      gysinDivisorBaseChangeIso_hom_comp_test, reassoc_of% (subschemeι_eqToHom h2)]
    simp only [Category.assoc]
  have hA := congrArg (chowPushforwardOfIso C
    ((gysinTripleDivisor (gysinTripleModule L sZ) (gysinTripleSection L σ sZ)
        (pullback.fst w t ≫ w)).subschemeι ≫ ((pullback.fst w t ≫ w) ≫ sZ))
    (pullback.fst w (pullback.snd (gysinTripleInclusion L σ) (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
    ((eqToHom (congrArg Scheme.IdealSheafData.subscheme h2) ≫
      (gysinDivisorBaseChangeIso L σ (pullback.fst w t ≫ (w ≫ sZ))).hom) ≫
        mixedCommuteHom (gysinTripleInclusion L σ) sZ w t) hstr (k - q - 1)) h3
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_congr_apply C _ _ _ _ hiso _
    (by simp)] at hA
  refine eq_of_heq ((chowPushforwardOfIso_comp_heq _ _ _ _ (by simp) rfl _ _ hout).trans
    ((chowPushforwardOfIso_heq _ _ hstr (by simp) rfl rfl
      (G.onChow_heq_congr_base (by simp) _ _ _ _ _
        ((chowGroupDegreeEquiv_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans
          ((chowGroupCongr_heq C _ _ _).symm.trans
            (chowGroupDegreeEquiv_heq C _ _ _).symm))))).trans
    ((heq_of_eq hA.symm).trans
      ((chowPushforwardOfIso_heq _ _ _ rfl rfl (by ring)
        ((chowGroupDegreeEquiv_heq C _ _ _).trans
          (BivariantClass.cap_heq c' _ rfl (chowGroupCongr_heq C _ _ _).symm))).trans
        (chowGroupDegreeEquiv_heq C _ _ _).symm))))

end GysinBase


/-! ### The classes generated by the operations of chapter 42 -/

/-- The bivariant classes towards the base built by the operations through which the proof of
Stacks 0FC5 presents a class `c ∈ A^p(X ⟶ S)`: flat-pullback classes of structure morphisms which
are flat of some relative dimension (Stacks 0B78), Gysin classes of divisors on the base
(Stacks 0B79), flat pullback after a class already built, proper pushforward of a class already
built (Stacks 0EPK), and integral combinations. -/
inductive IsChowOperationClassOverBase (C : ChowSituation.{u}) (G : GysinSystem C) :
    ∀ {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ),
      BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p → Prop
  /-- The flat-pullback class of a structure morphism flat of relative dimension `r`. -/
  | flat {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Flat sX] (r : ℕ)
      (hr : AlgebraicGeometry.RelativeDimension sX r)
      (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) (-(r : ℤ)))
      (hc : IsFlatPullbackOverBase C G sX r (-(r : ℤ)) c) :
      IsChowOperationClassOverBase C G sX (-(r : ℤ)) c
  /-- The Gysin class of the divisor of a section of an invertible module on the base. -/
  | gysin (L : C.S.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible C.S.sheaf.obj C.S.ringCatSheaf.property L]
      (σ : Γ(L, ⊤))
      (b : BivariantClass C G (gysinTripleInclusion L σ) (𝟙 C.S) (gysinTripleInclusion L σ)
        (Category.comp_id _) 1)
      (hb : IsGysinOverBase C G L σ b) :
      IsChowOperationClassOverBase C G (gysinTripleInclusion L σ) 1 b
  /-- Flat pullback along a flat morphism of relative dimension `r` after a class built. -/
  | flatComp {X D : Scheme.{u}} (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (π : X ⟶ D)
      [LocallyOfFiniteType π] [Flat π] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension π r)
      (p : ℤ) (b : BivariantClass C G sD (𝟙 C.S) sD (Category.comp_id sD) p)
      (hb : IsChowOperationClassOverBase C G sD p b)
      (c : BivariantClass C G (π ≫ sD) (𝟙 C.S) (π ≫ sD) (Category.comp_id (π ≫ sD))
        (p - (r : ℤ)))
      (hc : IsFlatPullbackAfter C G sD π r p b c) :
      IsChowOperationClassOverBase C G (π ≫ sD) (p - (r : ℤ)) c
  /-- Proper pushforward of a class built. -/
  | pushforward {X X' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (π : X' ⟶ X)
      [IsProper π] (p : ℤ)
      (ξ : BivariantClass C G (π ≫ sX) (𝟙 C.S) (π ≫ sX) (Category.comp_id (π ≫ sX)) p)
      (hξ : IsChowOperationClassOverBase C G (π ≫ sX) p ξ)
      (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p)
      (hc : IsBivariantProperPushforward C G (π ≫ sX) sX (𝟙 C.S) π sX rfl (Category.comp_id sX)
        (properPushforwardDescends C) p ξ c) :
      IsChowOperationClassOverBase C G sX p c
  /-- The zero class. -/
  | zero {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ) :
      IsChowOperationClassOverBase C G sX p 0
  /-- Sums of classes built. -/
  | add {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)
      (c d : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p)
      (hc : IsChowOperationClassOverBase C G sX p c)
      (hd : IsChowOperationClassOverBase C G sX p d) :
      IsChowOperationClassOverBase C G sX p (c + d)
  /-- Negatives of classes built. -/
  | neg {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)
      (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p)
      (hc : IsChowOperationClassOverBase C G sX p c) :
      IsChowOperationClassOverBase C G sX p (-c)

/-- The flat-pullback classes towards the base and their integral combinations are among the
classes built by the operations of chapter 42. -/
theorem isChowOperationClassOverBase_of_isChowOperationGenerated (C : ChowSituation.{u})
    (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)
    {c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p}
    (hc : IsChowOperationGenerated C G sX p c) : IsChowOperationClassOverBase C G sX p c := by
  refine AddSubgroup.closure_induction
    (p := fun x _ ↦ IsChowOperationClassOverBase C G sX p x) ?_ (.zero sX p)
    (fun x y _ _ hx hy ↦ .add sX p x y hx hy) (fun x _ hx ↦ .neg sX p x hx) hc
  rintro x ⟨r, hflat, rfl, hrX, hx⟩
  exact .flat sX r hrX x hx

/-- The subgroup of `Stacks.Chow.IsChowOperationProperGenerated`, generated by the flat-pullback
classes towards the base and their proper pushforwards, consists of classes built by the
operations of chapter 42. -/
theorem isChowOperationClassOverBase_of_isChowOperationProperGenerated (C : ChowSituation.{u})
    (G : GysinSystem C) (hpp : ProperPushforwardDescends C) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (p : ℤ)
    {c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p}
    (hc : IsChowOperationProperGenerated C G hpp sX p c) :
    IsChowOperationClassOverBase C G sX p c := by
  refine AddSubgroup.closure_induction
    (p := fun x _ ↦ IsChowOperationClassOverBase C G sX p x) ?_ (.zero sX p)
    (fun x y _ _ hx hy ↦ .add sX p x y hx hy) (fun x _ hx ↦ .neg sX p x hx) hc
  rintro x (⟨r, hflat, rfl, hrX, hx⟩ | ⟨X', π, hπ, ξ, hgenξ, hpf⟩)
  · exact .flat sX r hrX x hx
  · exact .pushforward sX π p ξ
      (isChowOperationClassOverBase_of_isChowOperationGenerated C G (π ≫ sX) p hgenξ) x hpf

section Main

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y Z : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (w : Y ⟶ Z) [LocallyOfFiniteType w] (q : ℤ)

/-- Every class built by the operations of chapter 42 commutes with every bivariant class over
the base, for a Gysin system whose Gysin maps of a section pulled back in two steps agree with
those of the section pulled back along the composite. -/
theorem bivariantCommuteOverBase_of_isChowOperationClassOverBase
    (hG : G.IsNaturalUnderPullbackCompPushforward) {X : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {p : ℤ} {c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p}
    (hc : IsChowOperationClassOverBase C G sX p c)
    (c' : BivariantClass C G (w ≫ sZ) sZ w rfl q) :
    BivariantCommuteOverBase C G sX sZ w p q c c' := by
  induction hc with
  | flat sX r hr c hc =>
    exact bivariantCommuteOverBase_of_isFlatPullbackOverBase C G sX sZ w r (-(r : ℤ)) q c c'
      (flatPullbackDescends C) rfl hr hc
  | gysin L σ b hb =>
    exact bivariantCommuteOverBase_of_isGysinOverBase C G L σ sZ w q hG b c' hb
  | flatComp sD π r hr p b _ c hc ih =>
    exact bivariantCommuteOverBase_of_isFlatPullbackAfter C G sD π r sZ w p q hr b c c' ih hc
  | pushforward sX π p ξ _ c hc ih =>
    exact bivariantCommuteOverBase_of_isBivariantProperPushforward C G sX sZ w π
      (properPushforwardDescends C) p q c ξ c' hc ih
  | zero sX p => exact bivariantCommuteOverBase_zero C G sX sZ w p q c'
  | add sX p c d _ _ ihc ihd => exact bivariantCommuteOverBase_add C G sX sZ w p q c' ihc ihd
  | neg sX p c _ ihc => exact bivariantCommuteOverBase_neg C G sX sZ w p q c' ihc

/-- Every class built by the operations of chapter 42 commutes with every bivariant class over
the base, at the Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the first Chern class rule
of invertible modules; nothing is assumed. -/
theorem bivariantCommuteOverBase_of_isChowOperationClassOverBase_ofInvertible {X : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {p : ℤ}
    {c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p}
    (hc : IsChowOperationClassOverBase C (gysinSystemOfInvertible C) sX p c)
    (c' : BivariantClass C (gysinSystemOfInvertible C) (w ≫ sZ) sZ w rfl q) :
    BivariantCommuteOverBase C (gysinSystemOfInvertible C) sX sZ w p q c c' :=
  bivariantCommuteOverBase_of_isChowOperationClassOverBase C (gysinSystemOfInvertible C) sZ w q
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) hc c'

end Main

end Stacks.Chow

end
