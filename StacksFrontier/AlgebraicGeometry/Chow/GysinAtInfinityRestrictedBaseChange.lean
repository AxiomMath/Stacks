module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FamilyFibreDifferenceExistence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityComparison
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.BaseChange

/-!
# The class at infinity of a base-changed modification

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over the affine chart
`𝐀¹_X`, and let `C ∈ A⁰(W_∞ ⟶ X)` be the class of Stacks 0F9J. **Stacks 0GUH** says that for a
morphism `q : X' ⟶ X` locally of finite type, with `b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` and
`i'_∞ : W'_∞ ⟶ W'` the base changes of `b` and `i_∞`, the class `C' ∈ A⁰(W'_∞ ⟶ X')` constructed
as in Stacks 0F9J using `b'` is the restriction of `C` in the sense of Remark 0F9Z.

The statement is for the class `Stacks.Chow.gysinAtInfinityClass` of Stacks 0F9J itself, with
the base change `b'` constructed as `Stacks.Chow.GysinAtInfinity.baseChangedModification`. The
hypotheses on `b` are preserved by the base change: `b'` is proper, and it is an isomorphism over
`𝐀¹_{X'}` because `𝐀¹_{X'}` is the inverse image of `𝐀¹_X` in `𝐏¹_{X'}`
(`Stacks.Chow.isIso_restrictedModification_affineChart`).

## Main definitions

* `Stacks.Chow.restrictedModificationIso`, `Stacks.Chow.restrictedModificationInfinityIso` — the
  canonical identifications `W ×_X X' ≅ W'` and `W_∞ ×_X X' ≅ W'_∞`.

## Main results

* `Stacks.Chow.isIso_restrictedModification_affineChart` — `b'` is an isomorphism over
  `𝐀¹_{X'}`.
* `Stacks.Chow.gysinAtInfinityClass_restrictedModification_cap` — `C' ∩ α = C ∩ α` under the
  identification of the two base-changed fibres at infinity.
* `Stacks.Chow.gysinAtInfinityClass_restrictedModification_eq_bivariantRestriction` —
  **Stacks 0GUH**: the class `C'` equals the restriction of `C` along `q`, transported along the
  identification `W_∞ ×_X X' ≅ W'_∞`.

## Implementation notes

The base change `b' : W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` is the base's
`Stacks.Chow.GysinAtInfinity.baseChangedModification`, with its properness and its cartesian
square over `q`.

The restriction of Remark 0F9Z is `Stacks.Chow.bivariantRestriction`, which produces a class for
the *chosen* fibre product `W_∞ ×_X X' ⟶ X'`; `Stacks.Chow.bivariantTransport` carries it along
the canonical identification of that fibre product with `W'_∞`, so that the two sides of the
conclusion are elements of one and the same group `A⁰(W'_∞ ⟶ X')`. Both constructions are taken
at the Gysin system `Stacks.Chow.gysinSystemOfInvertible`, whose Gysin maps are natural under
isomorphisms of base changes (`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso`).

## References

* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open GysinAtInfinity (baseChangedModification isPullback_baseChangedModification
  modificationProjectionAtInfinity_eq_snd)

/-! ### The base change of a modification -/

section Restricted

variable {X S W X' : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (q : X' ⟶ X)

/-- The morphism `𝐀¹_{X'} ⟶ 𝐀¹_X ⟶ 𝐀¹_S` is the morphism `𝐀¹_{X'} ⟶ 𝐀¹_S`. -/
theorem affineLineOverMap_comp_affineLineOverMap :
    affineLineOverMap q ≫ affineLineOverMap f = affineLineOverMap (q ≫ f) := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The affine chart of `𝐏¹_{X'}` lies over the affine chart of `𝐏¹_X`. -/
theorem projectiveLineAffineChart_comp_familyBaseChange :
    projectiveLineAffineChart (q ≫ f) ≫ familyBaseChange f q =
      affineLineOverMap q ≫ projectiveLineAffineChart f := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · rw [Category.assoc, familyBaseChange_comp_snd, projectiveLineAffineChart_snd, Category.assoc,
      projectiveLineAffineChart_snd, ← Category.assoc, affineLineOverMap_comp_affineLineOverMap]

/-- The base change of `b` lies over `b`. -/
@[reassoc]
theorem restrictedModification_comp_familyBaseChange :
    baseChangedModification f b q ≫ familyBaseChange f q =
      pullback.fst b (familyBaseChange f q) ≫ b :=
  pullback.condition.symm

/-- **The base change of a modification is an isomorphism over `𝐀¹_{X'}`.** The inverse image
of `𝐀¹_{X'}` in `W'` is the base change of the inverse image of `𝐀¹_X` in `W` along
`𝐀¹_{X'} ⟶ 𝐀¹_X`. -/
theorem isIso_restrictedModification_affineChart
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    IsIso (pullback.snd (baseChangedModification f b q) (projectiveLineAffineChart (q ≫ f))) := by
  have H := (IsPullback.of_hasPullback (baseChangedModification f b q)
    (projectiveLineAffineChart (q ≫ f))).paste_horiz
    (IsPullback.of_hasPullback b (familyBaseChange f q))
  rw [projectiveLineAffineChart_comp_familyBaseChange] at H
  let m : pullback (baseChangedModification f b q) (projectiveLineAffineChart (q ≫ f)) ⟶
      pullback b (projectiveLineAffineChart f) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst b (familyBaseChange f q))
      (pullback.snd _ _ ≫ affineLineOverMap q)
      (by rw [Category.assoc (pullback.snd _ _)]; exact H.w)
  have H' : IsPullback (m ≫ pullback.fst b (projectiveLineAffineChart f))
      (pullback.snd (baseChangedModification f b q) (projectiveLineAffineChart (q ≫ f))) b
      (affineLineOverMap q ≫ projectiveLineAffineChart f) := by
    rwa [pullback.lift_fst]
  exact (IsPullback.of_right H' (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback b (projectiveLineAffineChart f))).isIso_snd_of_isIso hA

/-- The canonical identification `W ×_X X' ≅ W' = W ×_{𝐏¹_X} 𝐏¹_{X'}`. -/
def restrictedModificationIso :
    pullback (modificationProjection f b) q ≅ pullback b (familyBaseChange f q) :=
  (IsPullback.of_hasPullback _ _).isoIsPullback _ _ (isPullback_baseChangedModification f b q)

/-- The identification `W ×_X X' ≅ W'` is compatible with the maps to `W`. -/
@[reassoc (attr := simp)]
theorem restrictedModificationIso_hom_fst :
    (restrictedModificationIso f b q).hom ≫ pullback.fst b (familyBaseChange f q) =
      pullback.fst (modificationProjection f b) q := by
  simp [restrictedModificationIso]

/-- The identification `W ×_X X' ≅ W'` lies over `X'`. -/
@[reassoc]
theorem restrictedModificationIso_hom_projection :
    (restrictedModificationIso f b q).hom ≫
        modificationProjection (q ≫ f) (baseChangedModification f b q) =
      pullback.snd (modificationProjection f b) q := by
  simp [restrictedModificationIso]

/-- The infinity section of `𝐏¹_{X'}` lies over the infinity section of `𝐏¹_X`. -/
theorem infinitySection_comp_familyBaseChange :
    infinitySection (q ≫ f) ≫ familyBaseChange f q = q ≫ infinitySection f :=
  constantSection_comp_familyBaseChange f q integralInfinitySection

/-- The canonical identification `W_∞ ×_X X' ≅ W'_∞` of the base change of the fibre at infinity
with the fibre at infinity of the base change. -/
def restrictedModificationInfinityIso :
    pullback (modificationProjectionAtInfinity f b) q ≅
      modificationFibreAtInfinity (q ≫ f) (baseChangedModification f b q) :=
  (pullback.congrHom (modificationProjectionAtInfinity_eq_snd f b) rfl).trans
    ((pullbackLeftPullbackSndIso b (infinitySection f) q).trans
      ((pullback.congrHom rfl (infinitySection_comp_familyBaseChange f q).symm).trans
        (pullbackLeftPullbackSndIso b (familyBaseChange f q) (infinitySection (q ≫ f))).symm))

/-- The identification `W_∞ ×_X X' ≅ W'_∞` is compatible with the maps to `W`. -/
@[reassoc]
theorem restrictedModificationInfinityIso_hom_fst :
    (restrictedModificationInfinityIso f b q).hom ≫
        modificationInclusionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫
          pullback.fst b (familyBaseChange f q) =
      pullback.fst (modificationProjectionAtInfinity f b) q ≫
        modificationInclusionAtInfinity f b := by
  simp [restrictedModificationInfinityIso]

/-- The identification `W_∞ ×_X X' ≅ W'_∞` lies over `X'`. -/
theorem restrictedModificationInfinityIso_hom_projection :
    (restrictedModificationInfinityIso f b q).hom ≫
        modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) =
      pullback.snd (modificationProjectionAtInfinity f b) q := by
  rw [modificationProjectionAtInfinity_eq_snd (q ≫ f) (baseChangedModification f b q)]
  simp [restrictedModificationInfinityIso]

end Restricted

/-! ### Stacks 0GUH -/

section BaseChange

variable (C : ChowSituation.{u}) {X W X' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (q : X' ⟶ X) [LocallyOfFiniteType q]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType q] in
/-- The identification `W ×_X T ≅ W' ×_{X'} T` lies over `T`. -/
@[reassoc]
theorem restrictedModificationComparison_snd {T : Scheme.{u}} (g : T ⟶ X') :
    modificationBaseChangeComparison C f b q (baseChangedModification f b q)
        (restrictedModificationIso f b q) (restrictedModificationIso_hom_projection f b q) g ≫
      pullback.snd (modificationProjection (q ≫ f) (baseChangedModification f b q)) g =
      pullback.snd (modificationProjection f b) (g ≫ q) := by
  simp [modificationBaseChangeComparison]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType q] in
/-- The identification `W ×_X T ≅ W' ×_{X'} T` is compatible with the maps to `W`. -/
@[reassoc]
theorem restrictedModificationComparison_fst {T : Scheme.{u}} (g : T ⟶ X') :
    modificationBaseChangeComparison C f b q (baseChangedModification f b q)
        (restrictedModificationIso f b q) (restrictedModificationIso_hom_projection f b q) g ≫
      pullback.fst (modificationProjection (q ≫ f) (baseChangedModification f b q)) g ≫
        pullback.fst b (familyBaseChange f q) =
      pullback.fst (modificationProjection f b) (g ≫ q) := by
  simp [modificationBaseChangeComparison]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType q] in
/-- The identification `W ×_X T ≅ W' ×_{X'} T` is compatible with the maps to `𝐏¹_S`. -/
theorem restrictedModificationComparison_toRelativeLine {T : Scheme.{u}} (g : T ⟶ X') :
    modificationBaseChangeComparison C f b q (baseChangedModification f b q)
        (restrictedModificationIso f b q) (restrictedModificationIso_hom_projection f b q) g ≫
      modificationBaseChangeToRelativeLine (q ≫ f) (baseChangedModification f b q) g =
      modificationBaseChangeToRelativeLine f b (g ≫ q) := by
  simp only [modificationBaseChangeToRelativeLine, modificationBaseChangeToLine, Category.assoc]
  rw [← familyBaseChange_comp_snd f q, restrictedModification_comp_familyBaseChange_assoc,
    restrictedModificationComparison_fst_assoc]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType q] in
/-- The identification of the base-changed fibres at infinity is compatible with the
identification of the base-changed modifications. -/
theorem restrictedModificationInfinityComparison_comp {T : Scheme.{u}} (g : T ⟶ X') :
    modificationInfinityBaseChangeComparison C f b q (baseChangedModification f b q)
        (restrictedModificationInfinityIso f b q)
        (restrictedModificationInfinityIso_hom_projection f b q) g ≫
      modificationInfinityBaseChange (q ≫ f) (baseChangedModification f b q) g =
      modificationInfinityBaseChange f b (g ≫ q) ≫
        modificationBaseChangeComparison C f b q (baseChangedModification f b q)
          (restrictedModificationIso f b q) (restrictedModificationIso_hom_projection f b q) g := by
  refine pullback.hom_ext ((isPullback_baseChangedModification f b q).hom_ext ?_ ?_) ?_
  · simp only [Category.assoc]
    rw [restrictedModificationComparison_fst,
      ← Category.assoc (modificationInfinityBaseChange (q ≫ f) _ g),
      modificationInfinityBaseChange_comp_fst,
      modificationInfinityBaseChange_comp_fst]
    simp only [Category.assoc, modificationInfinityBaseChangeComparison,
      transportPullbackIso_hom_fst_assoc, restrictedModificationInfinityIso_hom_fst,
      pullbackLeftPullbackSndIso_inv_fst_assoc]
  · simp only [Category.assoc]
    rw [pullback.condition, restrictedModificationComparison_snd_assoc,
      ← Category.assoc (modificationInfinityBaseChange (q ≫ f) _ g),
      modificationInfinityBaseChange_comp_snd,
      ← Category.assoc (modificationInfinityBaseChange _ _ _),
      modificationInfinityBaseChange_comp_snd]
    simp [modificationInfinityBaseChangeComparison]
  · simp only [Category.assoc]
    rw [restrictedModificationComparison_snd, modificationInfinityBaseChange_comp_snd,
      modificationInfinityBaseChange_comp_snd]
    simp [modificationInfinityBaseChangeComparison]

/-- For every test scheme `g : T ⟶ X'` locally of finite type, `C' ∩ α = C ∩ α` after the
canonical identification `W_∞ ×_X T ≅ W'_∞ ×_{X'} T` of the two base changes of the fibre at
infinity, where `C'` is the class of Stacks 0F9J for the base change `b'` of `b` along `q`. -/
theorem gysinAtInfinityClass_restrictedModification_cap {T : Scheme.{u}} (g : T ⟶ X')
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (q ≫ f)) k) :
    (gysinAtInfinityClass C (q ≫ f) (baseChangedModification f b q)
        (isIso_restrictedModification_affineChart f b q hA)).cap g k α =
      chowPushforwardOfIso C (modificationInfinityBaseChangeOver f b (g ≫ q))
        (modificationInfinityBaseChangeOver (q ≫ f) (baseChangedModification f b q) g)
        (modificationInfinityBaseChangeComparison C f b q (baseChangedModification f b q)
          (restrictedModificationInfinityIso f b q)
          (restrictedModificationInfinityIso_hom_projection f b q) g)
        (modificationInfinityBaseChangeComparison_comp_base C f b q (baseChangedModification f b q)
          (restrictedModificationInfinityIso f b q)
          (restrictedModificationInfinityIso_hom_projection f b q) g) (k - 0)
        ((gysinAtInfinityClass C f b hA).cap (g ≫ q) k
          (chowGroupCongr C (Category.assoc g q f).symm k α)) := by
  have key := gysinCapOfLift_comparison C
    (modificationBaseChangeComparison C f b q (baseChangedModification f b q)
      (restrictedModificationIso f b q) (restrictedModificationIso_hom_projection f b q) g)
    (modificationInfinityBaseChangeComparison C f b q (baseChangedModification f b q)
      (restrictedModificationInfinityIso f b q)
      (restrictedModificationInfinityIso_hom_projection f b q) g)
    (Category.assoc g q f) hA (isIso_restrictedModification_affineChart f b q hA)
    (restrictedModificationComparison_snd C f b q g)
    (restrictedModificationComparison_toRelativeLine C f b q g)
    (restrictedModificationInfinityComparison_comp C f b q g) k
    (chowGroupCongr C (Category.assoc g q f).symm k α)
  rw [chowGroupCongr_chowGroupCongr] at key
  change gysinCapAtInfinity C (q ≫ f) (baseChangedModification f b q)
    (isIso_restrictedModification_affineChart f b q hA) g k α = _ at key
  rw [gysinAtInfinityClass_cap, gysinAtInfinityClass_cap, key]
  exact chowGroupDegreeEquiv_chowPushforwardOfIso C _ _ _ _ _ _

/-- In the setting of Stacks 0F9J let `q : X' ⟶ X` be locally of finite type and let
`b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` and `i'_∞ : W'_∞ ⟶ W'` be the base changes of `b` and
`i_∞` (`Stacks.Chow.GysinAtInfinity.baseChangedModification`). Then the class
`C' ∈ A⁰(W'_∞ ⟶ X')` of Stacks 0F9J for `b'` is the restriction (Remark 0F9Z) of `C`: it equals
`Stacks.Chow.bivariantRestriction` of `C` along `q`, carried along the canonical identification
`W_∞ ×_X X' ≅ W'_∞` by `Stacks.Chow.bivariantTransport`. -/
@[stacks 0GUH "the class C' of Lemma 0F9J for the base change b' is the restriction of C"]
theorem gysinAtInfinityClass_restrictedModification_eq_bivariantRestriction :
    gysinAtInfinityClass C (q ≫ f) (baseChangedModification f b q)
        (isIso_restrictedModification_affineChart f b q hA) =
      bivariantTransport C (gysinSystemOfInvertible C)
        (pullback.fst (modificationProjectionAtInfinity f b) q ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫ (q ≫ f))
        (q ≫ f) (pullback.snd (modificationProjectionAtInfinity f b) q)
        (pullbackSnd_comp_structureMorphism_eq C (modificationProjectionAtInfinity f b ≫ f) f
          (modificationProjectionAtInfinity f b) rfl q)
        (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q)) rfl
        (restrictedModificationInfinityIso f b q)
        (restrictedModificationInfinityIso_hom_projection f b q) 0
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C)
          (modificationProjectionAtInfinity f b ≫ f) f (modificationProjectionAtInfinity f b) rfl
          q 0 (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (gysinAtInfinityClass C f b hA)) := by
  refine eq_of_isBivariantTransport C _ _ _ _ _ _ _ _ _ _ 0 ?_
    (isBivariantTransport_bivariantTransport C _ _ _ _ _ _ _ _ _ _ 0 _ _)
  intro T g _ k α
  rw [bivariantTransportCap_apply, bivariantRestriction_cap, bivariantRestrictionCap_apply,
    chowPushforwardOfIso_comp_eq C _ _ _ _ _ _
      (modificationInfinityBaseChangeComparison_eq C f b q (baseChangedModification f b q)
        (restrictedModificationInfinityIso f b q)
        (restrictedModificationInfinityIso_hom_projection f b q) g) _ _
      (modificationInfinityBaseChangeComparison_comp_base C f b q (baseChangedModification f b q)
        (restrictedModificationInfinityIso f b q)
        (restrictedModificationInfinityIso_hom_projection f b q) g) (k - 0)]
  exact gysinAtInfinityClass_restrictedModification_cap C f b hA q g k α

end BaseChange

end Stacks.Chow

end
