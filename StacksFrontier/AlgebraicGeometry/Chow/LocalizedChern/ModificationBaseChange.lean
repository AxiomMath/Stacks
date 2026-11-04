module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationComparison
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityRestrictedBaseChange

/-!
# The localized classes of a modification are compatible with base change

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z ⊆ X` be closed, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over
`𝐀¹_X`, and let `Q ∈ D(𝒪_W)` and `T ⊆ W_∞` be as in Stacks 0F9K, which builds the classes
`P'_p(Q)`, resp. `c'_p(Q)`, in `A^p(Z ⟶ X)`. **Stacks 0GUI** says that for `h : X' ⟶ X` locally of
finite type, with `Z' = Z ×_X X'`, `b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` and `Q' = (W' ⟶ W)^*Q`,
the classes built from `b'`, `Q'` and the base change of `T` are the restrictions (Remark 0F9Z)
of `P'_p(Q)`, resp. `c'_p(Q)`.

This file proves a more general statement: for any proper `b' : W' ⟶ 𝐏¹_{X'}` which is an
isomorphism over `𝐀¹_{X'}` and any morphism `k : W' ⟶ W` lying over `𝐏¹_{X'} ⟶ 𝐏¹_X`, the
localized class built from `b'`, a class `q'` operating as `q` does through `k`, and any
admissible `T' ⊆ W'_∞`, is the restriction of the one built from `b`, `q` and `T`. The proof is
the comparison of `StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationComparison` on
every test scheme `V ⟶ X'`, for the morphism `W' ×_{X'} V ⟶ W ×_X V` induced by `k`; the closed
subscheme `T'` is first replaced by `k_∞^{-1}(T)` using the first assertion of Stacks 0FAU.

## Main definitions

* `Stacks.Chow.modificationInfinityLift`, `Stacks.Chow.modificationExceptionalLift` — the
  morphisms `W'_∞ ⟶ W_∞` and `W'_∞ ×_{X'} Z' ⟶ W_∞ ×_X Z` induced by `k`.

## Main results

* `Stacks.Chow.bivariantRestriction_localizedModificationClass_of_lift` — the restriction of the
  localized class of a general class along a morphism of modifications over `h`.
* `Stacks.Chow.bivariantRestriction_localizedModificationClass` — the generic form of
  Stacks 0GUI.
* `Stacks.Chow.bivariantRestriction_modificationPowerSum`,
  `Stacks.Chow.bivariantRestriction_modificationChernClass` — **Stacks 0GUI**.

## Implementation notes

The restriction of Remark 0F9Z is `Stacks.Chow.bivariantRestriction`, which produces a class for
the chosen fibre product `Z ×_X X' ⟶ X'` whose source lies over the base through `Z`; the
localized class for `Z' = Z ×_X X'` has its source over the base through `X'`. These are equal
morphisms and not the same term, and `Stacks.Chow.bivariantClassCongrBase` reads the first class
against the second. The class `q'` is related to `q` through its operation on the test schemes
over `W'`, as in `Stacks.Chow.localizedModificationClass_cap_comparison`; for `q' = c_p(Q')` and
`q = c_p(Q)` this holds by `Stacks.Chow.res_perfectChernClass_derivedPullback_of_comp_eq`.

## References

* [Stacks Project, Tag 0GUI](https://stacks.math.columbia.edu/tag/0GUI)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
* [Stacks Project, Tag 0FAU](https://stacks.math.columbia.edu/tag/0FAU)
* [Stacks Project, Tag 0FB3](https://stacks.math.columbia.edu/tag/0FB3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open GysinAtInfinity (baseChangedModification)

/-- The morphism `𝐏¹_{X'} ⟶ 𝐏¹_X` induced by a morphism `X' ⟶ X` locally of finite type is
locally of finite type, being a base change of it. -/
instance locallyOfFiniteType_familyBaseChange {X X' S : Scheme.{u}} (f : X ⟶ S) (h : X' ⟶ X)
    [LocallyOfFiniteType h] : LocallyOfFiniteType (familyBaseChange f h) :=
  MorphismProperty.of_isPullback (isPullback_familyBaseChange f h) inferInstance

/-! ### A morphism of modifications over a base change -/

section Lift

variable {S X W X' W' Z : Scheme.{u}} {f : X ⟶ S} {b : W ⟶ projectiveLineProduct f}
  (h : X' ⟶ X) {b' : W' ⟶ projectiveLineProduct (h ≫ f)} (k : W' ⟶ W)
  (hk : k ≫ b = b' ≫ familyBaseChange f h)

include hk in
/-- A morphism `k : W' ⟶ W` over `𝐏¹_{X'} ⟶ 𝐏¹_X` lies over `h : X' ⟶ X`. -/
@[reassoc]
theorem comp_modificationProjection_of_lift :
    k ≫ modificationProjection f b = modificationProjection (h ≫ f) b' ≫ h := by
  simp only [modificationProjection, ← Category.assoc, hk]
  simp

/-- The morphism of fibres at infinity `W'_∞ ⟶ W_∞` induced by a morphism `k : W' ⟶ W` over
`𝐏¹_{X'} ⟶ 𝐏¹_X`: the inverse image of the divisor at infinity of `𝐏¹_X` in `𝐏¹_{X'}` is the
divisor at infinity of `𝐏¹_{X'}`. -/
def modificationInfinityLift :
    modificationFibreAtInfinity (h ≫ f) b' ⟶ modificationFibreAtInfinity f b :=
  pullback.lift (modificationInclusionAtInfinity (h ≫ f) b' ≫ k)
    (pullback.snd b' (infinitySection (h ≫ f)) ≫ h) (by
      rw [Category.assoc, hk, ← Category.assoc, pullback.condition, Category.assoc,
        infinitySection_comp_familyBaseChange, Category.assoc])

/-- The morphism of fibres at infinity lies over `k`. -/
@[reassoc (attr := simp)]
theorem modificationInfinityLift_comp_inclusion :
    modificationInfinityLift h k hk ≫ modificationInclusionAtInfinity f b =
      modificationInclusionAtInfinity (h ≫ f) b' ≫ k :=
  pullback.lift_fst _ _ _

/-- The morphism of fibres at infinity lies over `h`. -/
@[reassoc]
theorem modificationInfinityLift_comp_projection :
    modificationInfinityLift h k hk ≫ modificationProjectionAtInfinity f b =
      modificationProjectionAtInfinity (h ≫ f) b' ≫ h := by
  rw [modificationProjectionAtInfinity, modificationInfinityLift_comp_inclusion_assoc,
    comp_modificationProjection_of_lift h k hk]
  rfl

/-- The morphism `E' = W'_∞ ×_{X'} Z' ⟶ E = W_∞ ×_X Z` of the inverse images of `Z' = Z ×_X X'`
and of `Z` induced by `k`. -/
def modificationExceptionalLift (z : Z ⟶ X) :
    pullback (modificationProjectionAtInfinity (h ≫ f) b') (pullback.snd z h) ⟶
      pullback (modificationProjectionAtInfinity f b) z :=
  pullback.lift (pullback.fst _ _ ≫ modificationInfinityLift h k hk)
    (pullback.snd _ _ ≫ pullback.fst z h) (by
      rw [Category.assoc, modificationInfinityLift_comp_projection,
        pullback.condition_assoc, Category.assoc, pullback.condition (f := z)])

/-- The morphism `E' ⟶ E` lies over the morphism of fibres at infinity. -/
@[reassoc (attr := simp)]
theorem modificationExceptionalLift_fst (z : Z ⟶ X) :
    modificationExceptionalLift h k hk z ≫ pullback.fst (modificationProjectionAtInfinity f b) z =
      pullback.fst _ _ ≫ modificationInfinityLift h k hk :=
  pullback.lift_fst _ _ _

/-- The closed subscheme `κ⁻¹(T) ⊆ W'_∞` contains every point of `W'_∞` over `X' ∖ Z'` when `T`
contains every point of `W_∞` over `X ∖ Z`, where `κ : W'_∞ ⟶ W_∞` is induced by `k`. -/
private theorem mem_range_pullbackSnd_of_lift {T : Scheme.{u}} (z : Z ⟶ X)
    (t : T ⟶ modificationFibreAtInfinity f b)
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (w : modificationFibreAtInfinity (h ≫ f) b')
    (hw : modificationProjectionAtInfinity (h ≫ f) b' w ∉ Set.range (pullback.snd z h)) :
    w ∈ Set.range (pullback.snd t (modificationInfinityLift h k hk)) := by
  rw [Scheme.Pullback.range_snd]
  refine hT (modificationInfinityLift h k hk w) fun hz ↦ hw ?_
  rwa [Scheme.Pullback.range_snd, Set.mem_preimage, ← Scheme.Hom.comp_apply,
    ← modificationInfinityLift_comp_projection h k hk, Scheme.Hom.comp_apply]

/-- A morphism `l` is proper if its composite with a separated `s` is a proper `e`. -/
private theorem isProper_of_comp_eq {P P' B : Scheme.{u}} (l : P' ⟶ P) (s : P ⟶ B) [IsSeparated s]
    (e : P' ⟶ B) [IsProper e] (hl : l ≫ s = e) : IsProper l := by
  subst hl
  exact IsProper.of_comp l s

/-- The morphism of base changes `W' ×_{X'} V ⟶ W ×_X V` induced by `k`. -/
private def modificationBaseChangeLift {V : Scheme.{u}} (g' : V ⟶ X') :
    modificationBaseChange (h ≫ f) b' g' ⟶ modificationBaseChange f b (g' ≫ h) :=
  pullback.lift (pullback.fst _ _ ≫ k) (pullback.snd _ _) (by
    rw [Category.assoc, comp_modificationProjection_of_lift h k hk, pullback.condition_assoc])

/-- The morphism of base changes induced by `k` lies over `k`. -/
@[reassoc (attr := simp)]
private theorem modificationBaseChangeLift_fst {V : Scheme.{u}} (g' : V ⟶ X') :
    modificationBaseChangeLift h k hk g' ≫ pullback.fst (modificationProjection f b) (g' ≫ h) =
      pullback.fst (modificationProjection (h ≫ f) b') g' ≫ k :=
  pullback.lift_fst _ _ _

/-- The morphism of base changes induced by `k` lies over `V`. -/
@[reassoc (attr := simp)]
private theorem modificationBaseChangeLift_snd {V : Scheme.{u}} (g' : V ⟶ X') :
    modificationBaseChangeLift h k hk g' ≫ pullback.snd (modificationProjection f b) (g' ≫ h) =
      pullback.snd (modificationProjection (h ≫ f) b') g' :=
  pullback.lift_snd _ _ _

/-- The morphism of base changes induced by `k` lies over `𝐏¹_S`. -/
private theorem modificationBaseChangeLift_comp_toRelativeLine {V : Scheme.{u}} (g' : V ⟶ X') :
    modificationBaseChangeLift h k hk g' ≫ modificationBaseChangeToRelativeLine f b (g' ≫ h) =
      modificationBaseChangeToRelativeLine (h ≫ f) b' g' := by
  simp only [modificationBaseChangeToRelativeLine, modificationBaseChangeToLine,
    modificationBaseChangeLift, pullback.lift_fst_assoc, Category.assoc]
  rw [reassoc_of% hk, familyBaseChange_comp_snd]

/-- The morphism of base changes induced by `k` is proper when the modifications are. -/
private instance isProper_modificationBaseChangeLift [IsProper (modificationProjection f b)]
    [IsProper (modificationProjection (h ≫ f) b')] {V : Scheme.{u}} (g' : V ⟶ X') :
    IsProper (modificationBaseChangeLift h k hk g') :=
  isProper_of_comp_eq _ (pullback.snd _ _) _ (modificationBaseChangeLift_snd h k hk g')

/-- The morphism of base changes `W'_∞ ×_{X'} V ⟶ W_∞ ×_X V` of the fibres at infinity induced by
`k`. -/
private def modificationInfinityBaseChangeLift {V : Scheme.{u}} (g' : V ⟶ X') :
    pullback (modificationProjectionAtInfinity (h ≫ f) b') g' ⟶
      pullback (modificationProjectionAtInfinity f b) (g' ≫ h) :=
  pullback.lift (pullback.fst _ _ ≫ modificationInfinityLift h k hk) (pullback.snd _ _) (by
    rw [Category.assoc, modificationInfinityLift_comp_projection h k hk,
      pullback.condition_assoc])

/-- The morphism of base changes of the fibres at infinity lies over the morphism of fibres at
infinity. -/
@[reassoc (attr := simp)]
private theorem modificationInfinityBaseChangeLift_fst {V : Scheme.{u}} (g' : V ⟶ X') :
    modificationInfinityBaseChangeLift h k hk g' ≫
        pullback.fst (modificationProjectionAtInfinity f b) (g' ≫ h) =
      pullback.fst (modificationProjectionAtInfinity (h ≫ f) b') g' ≫
        modificationInfinityLift h k hk :=
  pullback.lift_fst _ _ _

/-- The morphism of base changes of the fibres at infinity lies over `V`. -/
@[reassoc (attr := simp)]
private theorem modificationInfinityBaseChangeLift_snd {V : Scheme.{u}} (g' : V ⟶ X') :
    modificationInfinityBaseChangeLift h k hk g' ≫
        pullback.snd (modificationProjectionAtInfinity f b) (g' ≫ h) =
      pullback.snd (modificationProjectionAtInfinity (h ≫ f) b') g' :=
  pullback.lift_snd _ _ _

/-- The morphism of base changes of the fibres at infinity is proper when the projections at
infinity are. -/
private instance isProper_modificationInfinityBaseChangeLift
    [IsProper (modificationProjectionAtInfinity f b)]
    [IsProper (modificationProjectionAtInfinity (h ≫ f) b')] {V : Scheme.{u}} (g' : V ⟶ X') :
    IsProper (modificationInfinityBaseChangeLift h k hk g') :=
  isProper_of_comp_eq _ (pullback.snd _ _) _ (modificationInfinityBaseChangeLift_snd h k hk g')

/-- The morphisms of base changes induced by `k` commute with the inclusions at infinity. -/
private theorem modificationInfinityBaseChangeLift_comp_infinityBaseChange {V : Scheme.{u}}
    (g' : V ⟶ X') :
    modificationInfinityBaseChangeLift h k hk g' ≫ modificationInfinityBaseChange f b (g' ≫ h) =
      modificationInfinityBaseChange (h ≫ f) b' g' ≫ modificationBaseChangeLift h k hk g' := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, modificationInfinityBaseChange_comp_fst, Category.assoc,
      modificationBaseChangeLift_fst, ← Category.assoc (modificationInfinityBaseChange _ _ _),
      modificationInfinityBaseChange_comp_fst, modificationInfinityBaseChangeLift_fst_assoc,
      Category.assoc, modificationInfinityLift_comp_inclusion]
  · rw [Category.assoc, modificationInfinityBaseChange_comp_snd,
      modificationInfinityBaseChangeLift_snd, Category.assoc, modificationBaseChangeLift_snd,
      modificationInfinityBaseChange_comp_snd]

end Lift

section BaseChange

variable {C : ChowSituation.{u}} {X W X' W' Z T T' : Scheme.{u}} {f : X ⟶ C.S}
  [LocallyOfFiniteType f] {b : W ⟶ projectiveLineProduct f} [IsProper b]
  (z : Z ⟶ X) [IsClosedImmersion z] (h : X' ⟶ X) [LocallyOfFiniteType h]
  {b' : W' ⟶ projectiveLineProduct (h ≫ f)} [IsProper b'] (k : W' ⟶ W) [LocallyOfFiniteType k]
  (hk : k ≫ b = b' ≫ familyBaseChange f h) {p : ℤ}

/-- The morphism of fibres at infinity induced by a morphism `k` locally of finite type is locally
of finite type. -/
instance locallyOfFiniteType_modificationInfinityLift (hk : k ≫ b = b' ≫ familyBaseChange f h) :
    LocallyOfFiniteType (modificationInfinityLift h k hk) := by
  have : LocallyOfFiniteType (modificationInfinityLift h k hk ≫
      modificationInclusionAtInfinity f b) := by
    rw [modificationInfinityLift_comp_inclusion]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (modificationInclusionAtInfinity f b)

/-- The morphism `E' ⟶ E` induced by a morphism `k` locally of finite type is locally of finite
type. -/
instance locallyOfFiniteType_modificationExceptionalLift
    (hk : k ≫ b = b' ≫ familyBaseChange f h) :
    LocallyOfFiniteType (modificationExceptionalLift h k hk z) := by
  have : LocallyOfFiniteType (modificationExceptionalLift h k hk z ≫
      pullback.snd (modificationProjectionAtInfinity f b) z) := by
    rw [modificationExceptionalLift, pullback.lift_snd]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (pullback.snd _ z)

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType h] [IsProper b']
  [LocallyOfFiniteType k] in
/-- `k : W' ⟶ W` is a morphism over the base. -/
theorem comp_modificationProjection_comp_of_lift (hk : k ≫ b = b' ≫ familyBaseChange f h) :
    k ≫ (modificationProjection f b ≫ f) = modificationProjection (h ≫ f) b' ≫ (h ≫ f) := by
  rw [← Category.assoc, comp_modificationProjection_of_lift h k hk, Category.assoc]

/-- If `q` vanishes over `T` and `q'` operates as `q` does through `k`, then `q'` vanishes over
`κ⁻¹(T)`, where `κ : W'_∞ ⟶ W_∞` is induced by `k`. -/
private theorem vanishesOver_pullbackSnd_of_lift (hk : k ≫ b = b' ≫ familyBaseChange f h)
    (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {q' : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjection (h ≫ f) b' ≫ (h ≫ f)) p}
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (hqq' : ∀ {Y : Scheme.{u}} (y : Y ⟶ W') [LocallyOfFiniteType y] [LocallyOfFiniteType (y ≫ k)]
      (k' : ℤ) (γ : chowGroup C (y ≫ (modificationProjection (h ≫ f) b' ≫ (h ≫ f))) k')
      (γ' : chowGroup C ((y ≫ k) ≫ (modificationProjection f b ≫ f)) k'), γ ≍ γ' →
        q'.idRule C _ (gysinSystemOfInvertible C) y k' γ ≍
          q.idRule C _ (gysinSystemOfInvertible C) (y ≫ k) k' γ') :
    BivariantClass.VanishesOver q' (pullback.snd t (modificationInfinityLift h k hk) ≫
      modificationInclusionAtInfinity (h ≫ f) b') := by
  set κ := modificationInfinityLift h k hk
  have hκf := comp_modificationProjection_comp_of_lift h k hk
  simp only [Category.assoc] at hκf
  apply BivariantClass.VanishesOver.of_idRule_eq_zero
  intro Y y _ k' x
  have hm : (y ≫ pullback.fst t κ) ≫ (t ≫ modificationInclusionAtInfinity f b) =
      (y ≫ pullback.snd t κ ≫ modificationInclusionAtInfinity (h ≫ f) b') ≫ k := by
    simp only [Category.assoc]
    rw [pullback.condition_assoc, modificationInfinityLift_comp_inclusion]
  have : LocallyOfFiniteType
      ((y ≫ pullback.snd t κ ≫ modificationInclusionAtInfinity (h ≫ f) b') ≫ k) := by
    rw [← hm]
    infer_instance
  refine chowGroup_eq_zero_of_heq_zero_of_base_eq (by simp only [Category.assoc]; rw [hκf])
    ((hqq' _ k' x (chowGroupCongr C (by simp only [Category.assoc]; rw [hκf]) k' x)
      (chowGroupCongr_heq C _ _ _).symm).trans (heq_of_eq ?_))
  exact hq.idRule_eq_zero _ _ hm k' _

/-- **The restriction of a localized class along a morphism of modifications.** In the setting
of Stacks 0F9K let `h : X' ⟶ X` be locally of finite type and `Z' = Z ×_X X'`, let
`b' : W' ⟶ 𝐏¹_{X'}` be proper and an isomorphism over `𝐀¹_{X'}`, and let `k : W' ⟶ W` lie over
`𝐏¹_{X'} ⟶ 𝐏¹_X`. Let `q ∈ A^p(W)` vanish over a closed `T ⊆ W_∞` containing every point of `W_∞`
over `X ∖ Z`, and let `q' ∈ A^p(W')` operate on every test scheme over `W'` as `q` does through
`k` (for instance `q' = k^* q`). Then for every closed `T' ⊆ W'_∞` containing every point of
`W'_∞` over `X' ∖ Z'` over which `q'` vanishes, the localized class of Stacks 0F9K built from
`b'`, `q'` and `T'` is the restriction (Remark 0F9Z) of the one built from `b`, `q` and `T`. This
contains Stacks 0GUI (`b'` the base change of `b`). -/
theorem bivariantRestriction_localizedModificationClass_of_lift
    (hk : k ≫ b = b' ≫ familyBaseChange f h)
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
    (hA' : IsIso (pullback.snd b' (projectiveLineAffineChart (h ≫ f))))
    (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
    (t' : T' ⟶ modificationFibreAtInfinity (h ≫ f) b') [IsClosedImmersion t']
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {q' : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjection (h ≫ f) b' ≫ (h ≫ f)) p}
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hT' : ∀ w, modificationProjectionAtInfinity (h ≫ f) b' w ∉ Set.range (pullback.snd z h) →
      w ∈ Set.range t')
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (hq' : BivariantClass.VanishesOver q' (t' ≫ modificationInclusionAtInfinity (h ≫ f) b'))
    (hqq' : ∀ {Y : Scheme.{u}} (y : Y ⟶ W') [LocallyOfFiniteType y] [LocallyOfFiniteType (y ≫ k)]
      (k' : ℤ) (γ : chowGroup C (y ≫ (modificationProjection (h ≫ f) b' ≫ (h ≫ f))) k')
      (γ' : chowGroup C ((y ≫ k) ≫ (modificationProjection f b ≫ f)) k'), γ ≍ γ' →
        q'.idRule C _ (gysinSystemOfInvertible C) y k' γ ≍
          q.idRule C _ (gysinSystemOfInvertible C) (y ≫ k) k' γ') :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd z h)
        (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h) (hv' := rfl) p
        (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (localizedModificationClass (gysinAtInfinityData C f b hA) z t hT hq)) =
      localizedModificationClass (gysinAtInfinityData C (h ≫ f) b' hA') (pullback.snd z h) t'
        hT' hq' := by
  have hT'' := mem_range_pullbackSnd_of_lift h k hk z t hT
  have hq'' : BivariantClass.VanishesOver q' (pullback.snd t (modificationInfinityLift h k hk) ≫
      modificationInclusionAtInfinity (h ≫ f) b') :=
    vanishesOver_pullbackSnd_of_lift h k hk t hq hqq'
  set κ := modificationInfinityLift h k hk
  rw [localizedModificationClass_eq _ (pullback.snd z h) t' (pullback.snd t κ) hT' hT'' hq' hq'']
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {V} g' _ k' α ↦ ?_
  have := (gysinAtInfinityData C (h ≫ f) b' hA').properModification
  have := (gysinAtInfinityData C f b hA).properModification
  have := (gysinAtInfinityData C (h ≫ f) b' hA').properProjectionAtInfinity
  have := (gysinAtInfinityData C f b hA).properProjectionAtInfinity
  have hψs : (pullbackLeftPullbackSndIso z h g').hom ≫ (pullback.fst z (g' ≫ h) ≫ (z ≫ f)) =
      pullback.fst (pullback.snd z h) g' ≫ (pullback.snd z h ≫ (h ≫ f)) := by
    rw [pullbackLeftPullbackSndIso_hom_fst_assoc, pullback.condition_assoc]
  have key := localizedModificationClass_cap_comparison (κW := k) (κ := κ)
    (eκ := modificationExceptionalLift h k hk z) (lT := pullback.fst t κ) hA' hA hT'' hT hq'' hq
    (modificationInfinityLift_comp_inclusion h k hk)
    (comp_modificationProjection_comp_of_lift h k hk) (modificationExceptionalLift_fst h k hk z)
    pullback.condition hqq' g' (g' ≫ h) (Category.assoc _ _ _).symm
    (modificationBaseChangeLift h k hk g') (modificationBaseChangeLift_snd h k hk g')
    (modificationBaseChangeLift_comp_toRelativeLine h k hk g')
    (modificationInfinityBaseChangeLift h k hk g')
    (modificationInfinityBaseChangeLift_comp_infinityBaseChange h k hk g')
    (modificationInfinityBaseChangeLift_fst h k hk g')
    (pullbackLeftPullbackSndIso z h g').hom (pullbackLeftPullbackSndIso_hom_snd z h g') k' α
  refine eq_of_heq ((bivariantClassCongrBase_cap C _ (pullback.snd z h) _ rfl p _ g' k' α α
    HEq.rfl).trans ?_)
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply, ← key]
  have hinv : inv (pullbackLeftPullbackSndIso z h g').hom ≫
      (pullback.fst (pullback.snd z h) g' ≫ (pullback.snd z h ≫ (h ≫ f))) =
        pullback.fst z (g' ≫ h) ≫ (z ≫ f) := by
    rw [IsIso.inv_comp_eq, hψs]
  refine (chowPushforwardOfIso_heq _ _ (by simpa using hinv) rfl
    (by rw [pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h]) rfl HEq.rfl).trans
    (heq_of_eq ?_)
  rw [chowPushforwardOfIso_congr_apply C _ _ (pullbackLeftPullbackSndIso z h g').inv
    (inv (pullbackLeftPullbackSndIso z h g').hom) (by simp) _ hinv]
  exact chowPushforwardOfIso_inv_comp C _ _ (pullbackLeftPullbackSndIso z h g').hom hψs
    (k' - p) _

/-- **Stacks 0GUI, for a general class.** In the setting of Stacks 0F9K let `h : X' ⟶ X` be
locally of finite type, and let `b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` and `Z' = Z ×_X X'` be
the base changes. Let `q ∈ A^p(W)` vanish over a closed `T ⊆ W_∞` containing every point of
`W_∞` over `X ∖ Z`, and let `q' ∈ A^p(W')` operate on every test scheme over `W'` as `q` does
through `W' ⟶ W` (for instance `q' = (W' ⟶ W)^* q`). Then for every closed `T' ⊆ W'_∞` containing
every point of `W'_∞` over `X' ∖ Z'` over which `q'` vanishes, the localized class of
Stacks 0F9K built from `b'`, `q'` and `T'` is the restriction (Remark 0F9Z) of the one built from
`b`, `q` and `T`. -/
theorem bivariantRestriction_localizedModificationClass
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
    (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
    (t' : T' ⟶ modificationFibreAtInfinity (h ≫ f) (baseChangedModification f b h))
    [IsClosedImmersion t']
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {q' : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjection (h ≫ f) (baseChangedModification f b h) ≫ (h ≫ f)) p}
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hT' : ∀ w, modificationProjectionAtInfinity (h ≫ f) (baseChangedModification f b h) w ∉
      Set.range (pullback.snd z h) → w ∈ Set.range t')
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (hq' : BivariantClass.VanishesOver q'
      (t' ≫ modificationInclusionAtInfinity (h ≫ f) (baseChangedModification f b h)))
    (hqq' : ∀ {Y : Scheme.{u}} (y : Y ⟶ pullback b (familyBaseChange f h))
      [LocallyOfFiniteType y] [LocallyOfFiniteType (y ≫ pullback.fst b (familyBaseChange f h))]
      (k : ℤ) (γ : chowGroup C
        (y ≫ (modificationProjection (h ≫ f) (baseChangedModification f b h) ≫ (h ≫ f))) k)
      (γ' : chowGroup C ((y ≫ pullback.fst b (familyBaseChange f h)) ≫
        (modificationProjection f b ≫ f)) k), γ ≍ γ' →
        q'.idRule C _ (gysinSystemOfInvertible C) y k γ ≍
          q.idRule C _ (gysinSystemOfInvertible C) (y ≫ pullback.fst b (familyBaseChange f h)) k
            γ') :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd z h)
        (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h) (hv' := rfl) p
        (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (localizedModificationClass (gysinAtInfinityData C f b hA) z t hT hq)) =
      localizedModificationClass (gysinAtInfinityData C (h ≫ f) (baseChangedModification f b h)
        (isIso_restrictedModification_affineChart f b h hA)) (pullback.snd z h) t' hT' hq' :=
  bivariantRestriction_localizedModificationClass_of_lift z h _
    (restrictedModification_comp_familyBaseChange f b h).symm hA
    (isIso_restrictedModification_affineChart f b h hA) t t' hT hT' hq hq' hqq'

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType h] in
/-- `W' ⟶ W` is a morphism over the base, for the base change `W' = W ×_{𝐏¹_X} 𝐏¹_{X'}`. -/
theorem restrictedModification_fst_comp_structure :
    pullback.fst b (familyBaseChange f h) ≫ (modificationProjection f b ≫ f) =
      modificationProjection (h ≫ f) (baseChangedModification f b h) ≫ (h ≫ f) :=
  comp_modificationProjection_comp_of_lift h _
    (restrictedModification_comp_familyBaseChange f b h).symm

end BaseChange

section PerfectBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X W X' Z T T' : Scheme.{u}} (f : X ⟶ C.S)
  [LocallyOfFiniteType f] (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (z : Z ⟶ X) [IsClosedImmersion z]
  (h : X' ⟶ X) [LocallyOfFiniteType h]
  (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
  (t' : T' ⟶ modificationFibreAtInfinity (h ≫ f) (baseChangedModification f b h))
  [IsClosedImmersion t']
  {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q) (p : ℕ)

/-- In the setting of Stacks 0F9K let `h : X' ⟶ X` be locally of finite type, let
`b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` and `Z' = Z ×_X X'` be the base changes, and set
`Q' = (W' ⟶ W)^* Q`. Then the class `P'_p(Q') ∈ A^p(Z' ⟶ X')` constructed as in Stacks 0F9K from
`b'`, `Q'` and any closed `T' ⊆ W'_∞` with the properties used there (for instance the base change
of `T`) is the restriction (Remark 0F9Z) of `P'_p(Q) ∈ A^p(Z ⟶ X)`. -/
@[stacks 0GUI "the case of P'_p: the class P'_p(Q') of Lemma 0F9K for the base change is the \
restriction of P'_p(Q)"]
theorem bivariantRestriction_modificationPowerSum
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hT' : ∀ w, modificationProjectionAtInfinity (h ≫ f) (baseChangedModification f b h) w ∉
      Set.range (pullback.snd z h) → w ∈ Set.range t')
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q))
    (hzero' : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t' ≫ modificationInclusionAtInfinity (h ≫ f)
        (baseChangedModification f b h)).toLRSHom.toShHom).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst b (familyBaseChange f h)).toLRSHom.toShHom).obj Q))) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd z h)
        (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h) (hv' := rfl) p
        (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (modificationPowerSum C f b hA z t hQ p hT hzero)) =
      modificationPowerSum C (h ≫ f) (baseChangedModification f b h)
        (isIso_restrictedModification_affineChart f b h hA) (pullback.snd z h) t'
        (hQ.derivedPullback (pullback.fst b (familyBaseChange f h))) p hT' hzero' := by
  refine bivariantRestriction_localizedModificationClass z h hA t t' hT hT'
    (vanishesOver_perfectPowerSumClass_of_isZero C _ _ hQ p hzero)
    (vanishesOver_perfectPowerSumClass_of_isZero C _ _ _ p hzero') ?_
  intro Y y _ _ k γ γ' hγ
  have hs := restrictedModification_fst_comp_structure (b := b) h
  have key := TotalChowClass.idRule_res_apply_heq _ hs (perfectPowerSum C _ hQ p) p y k γ γ' hγ
  rwa [res_perfectPowerSum_derivedPullback C _ hQ _ hs
    (hQ.derivedPullback (pullback.fst b (familyBaseChange f h))) p] at key

/-- In the setting of Stacks 0F9K let `h : X' ⟶ X` be locally of finite type, let
`b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` and `Z' = Z ×_X X'` be the base changes, and set
`Q' = (W' ⟶ W)^* Q`. Then the class `c'_p(Q') ∈ A^p(Z' ⟶ X')` constructed as in Stacks 0F9K from
`b'`, `Q'` and any closed `T' ⊆ W'_∞` with the properties used there (for instance the base change
of `T`) is the restriction (Remark 0F9Z) of `c'_p(Q) ∈ A^p(Z ⟶ X)`. -/
@[stacks 0GUI "the case of c'_p: the class c'_p(Q') of Lemma 0F9K for the base change is the \
restriction of c'_p(Q)"]
theorem bivariantRestriction_modificationChernClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hT' : ∀ w, modificationProjectionAtInfinity (h ≫ f) (baseChangedModification f b h) w ∉
      Set.range (pullback.snd z h) → w ∈ Set.range t')
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (hrank' : ∃ M : T'.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t' ≫ modificationInclusionAtInfinity (h ≫ f)
          (baseChangedModification f b h)).toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.fst b (familyBaseChange f h)).toLRSHom.toShHom).obj Q) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd z h)
        (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl h) (hv' := rfl) p
        (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (modificationChernClass C f b hA z t hQ p hT hrank)) =
      modificationChernClass C (h ≫ f) (baseChangedModification f b h)
        (isIso_restrictedModification_affineChart f b h hA) (pullback.snd z h) t'
        (hQ.derivedPullback (pullback.fst b (familyBaseChange f h))) p hT' hrank' := by
  refine bivariantRestriction_localizedModificationClass z h hA t t' hT hT'
    (vanishesOver_perfectChernClass_of_rankLT C _ _ hQ p hrank)
    (vanishesOver_perfectChernClass_of_rankLT C _ _ _ p hrank') ?_
  intro Y y _ _ k γ γ' hγ
  have hs := restrictedModification_fst_comp_structure (b := b) h
  have key := TotalChowClass.idRule_res_apply_heq _ hs (perfectChernClass C _ hQ) p y k γ γ' hγ
  rwa [res_perfectChernClass_derivedPullback_of_comp_eq C _ hQ _ hs
    (hQ.derivedPullback (pullback.fst b (familyBaseChange f h)))] at key

end PerfectBaseChange

end Stacks.Chow

end
