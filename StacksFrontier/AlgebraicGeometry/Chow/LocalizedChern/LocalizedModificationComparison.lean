module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseProper
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationComparison
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedModificationSituation

/-!
# The classes of Stacks 0F9K for a modification extending a pullback

Let `(S, δ)`, `X`, `i : Z ⟶ X`, `F ∈ D(𝒪_X)` and `p` be as in Situation 0GUJ. Let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with projection `π : W ⟶ X`, fibre at
infinity `i_∞ : W_∞ ⟶ W` and section at zero `i_0 : X ⟶ W`, let `Q ∈ D(𝒪_W)` be perfect with
defined Chern classes, and let `T ⊆ W_∞` be closed, contain every point of `W_∞` lying over
`X ∖ Z`, and be such that `Q|_T` is zero, resp. finite locally free of rank `< p` in degree `0`.
These are the data of Stacks 0F9K, which attaches to them the classes
`P'_p(Q) = (E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C`, resp. `c'_p(Q)`, in `A^p(Z ⟶ X)`, with `E = W_∞ ×_X Z` and
`C` the class of Stacks 0F9J.

Stacks 0FE8 computes these classes when `Q` extends the pullback of `F`: if
`Q|_{b^{-1}(𝐀¹_X)} ≅ π^* F|_{b^{-1}(𝐀¹_X)}`, `F|_{X ∖ Z}` is zero, resp. finite locally free of
rank `< p` in degree `0`, and `Q` satisfies condition (3) of Situation 0GUJ, then
`P'_p(Q) = P_p(Z ⟶ X, F)`, resp. `c'_p(Q) = c_p(Z ⟶ X, F)`.

The proof runs through the localized class `R = P_p(W_Z ⟶ W, Q)`, resp. `c_p(W_Z ⟶ W, Q)`, of
Situation 0GUJ for `W`, `W_Z = W ×_X Z` and `Q`, whose condition (2) holds by the hypotheses on
`T` and on `F`. The class `P'_p(Q|_E)` is the restriction of `R` to `W_∞` (Stacks 0FB8, 0FB7,
0FB3). Hence on a test scheme `V ⟶ X`, `P'_p(Q) ∩ α` is the pushforward of `R ∩ (C ∩ α)`, and
by proper naturality of `R` and Stacks 0F9J (`i_{∞,*}(C ∩ α) = i_{0,*} α`) that of `R ∩ α`
computed through the section at zero. The section at zero factors through the chart
`b^{-1}(𝐀¹_X)`, on which the restrictions of `R` and of the localized class of `π^* F` agree
(Stacks 0FB3, as both are localized classes of isomorphic objects); the latter is the
restriction of `P_p(Z ⟶ X, F)` along `π` (Stacks 0FB3, 0FB7), and `π ∘ i_0 = 𝟙` concludes.

## Main results

* `Stacks.Chow.LocalizedSituation.modificationPowerSum_eq_localizedPowerSum` — Stacks 0FE8
  for `P_p`.
* `Stacks.Chow.LocalizedSituation.modificationChernClass_eq_localizedChern` — Stacks 0FE8
  for `c_p`.
* `Stacks.Chow.localizedModificationClass_eq_of_isModificationInfinityRestriction` — the
  localized class of Stacks 0F9K is `c` as soon as its exceptional class is the restriction to
  `W_∞` of a class `R` on `W` which on the chart `b^{-1}(𝐀¹_X)` is the restriction of `c`.
* `Stacks.Chow.isModificationInfinityRestriction_modificationExtension_perfectPowerSumClass`,
  `Stacks.Chow.isModificationInfinityRestriction_modificationExtension_perfectChernClass` — the
  exceptional classes of Stacks 0F9K are restrictions of the localized classes on `W`.

## Implementation notes

The proof in the Stacks Project identifies `P'_p(Q)` with `P_p(Z ⟶ X, F)` by comparing both,
through Stacks 0FB8, 0FB7 and 0FB3, with the localized class of `π^* F` on `W` capped against
`C ∩ α`, and then evaluating on `W_∞`. Here the comparison of `Q` with `π^* F` is made instead on
the chart `b^{-1}(𝐀¹_X)`, after moving the cap from `W_∞` to the section at zero by
Stacks 0F9J; only the restrictions of the two localized classes to the chart are compared, so
that no comparison of `Q` with `π^* F` along `W_∞` is needed.

## References

* [Stacks Project, Tag 0FE8](https://stacks.math.columbia.edu/tag/0FE8)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0FB3](https://stacks.math.columbia.edu/tag/0FB3)
* [Stacks Project, Tag 0FB7](https://stacks.math.columbia.edu/tag/0FB7)
* [Stacks Project, Tag 0FB8](https://stacks.math.columbia.edu/tag/0FB8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Chow

/-! ### Bookkeeping -/

section Bookkeeping

variable {C : ChowSituation.{u}}

/-- Two bivariant classes whose restrictions (Remark 0F9Z) along `h : Y' ⟶ Y` agree cap alike on
every test scheme factoring through `h`. -/
theorem BivariantClass.cap_comp_eq_of_bivariantRestriction_eq {G : GysinSystem C}
    {X Y Y' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX}
    {h : Y' ⟶ Y} [LocallyOfFiniteType h] {p : ℤ} {hgys : G.IsNaturalUnderBaseChangeIso}
    {c₁ c₂ : BivariantClass C G sX sY f hf p}
    (hc : bivariantRestriction C G sX sY f hf h p hgys c₁ =
      bivariantRestriction C G sX sY f hf h p hgys c₂)
    {T : Scheme.{u}} (v : T ⟶ Y') [LocallyOfFiniteType v] [LocallyOfFiniteType (v ≫ h)] (k : ℤ)
    (β : chowGroup C ((v ≫ h) ≫ sY) k) :
    c₁.cap (v ≫ h) k β = c₂.cap (v ≫ h) k β := by
  have e := congrArg (fun c => c.cap v k (chowGroupCongr C (Category.assoc v h sY) k β)) hc
  simp only [bivariantRestriction_cap, bivariantRestrictionCap_apply,
    chowGroupCongr_chowGroupCongr] at e
  exact chowPushforwardOfIso_injective C _ _ _ _ _ e

/-- For `q : W ⟶ X`, `z : Z ⟶ X` and a test scheme `m : Y ⟶ W` lying over `v : Y ⟶ V` and
`g : V ⟶ X`, the morphism `(W ×_X Z) ×_W Y ⟶ Z ×_X V` induced by the projections. -/
def restrictionComparisonMap {W X Z Y V : Scheme.{u}} (q : W ⟶ X) (z : Z ⟶ X) (m : Y ⟶ W)
    (v : Y ⟶ V) (g : V ⟶ X) (h : m ≫ q = v ≫ g) :
    pullback (pullback.fst q z) m ⟶ pullback z g :=
  pullback.lift (pullback.fst _ m ≫ pullback.snd q z) (pullback.snd _ m ≫ v) (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, h, Category.assoc])

variable {W X Z Y V : Scheme.{u}} (q : W ⟶ X) (z : Z ⟶ X) (m : Y ⟶ W) (v : Y ⟶ V) (g : V ⟶ X)
  (h : m ≫ q = v ≫ g)

/-- The comparison morphism followed by the first projection to `Z ×_X V`. -/
@[reassoc (attr := simp)]
theorem restrictionComparisonMap_fst :
    restrictionComparisonMap q z m v g h ≫ pullback.fst z g =
      pullback.fst _ m ≫ pullback.snd q z :=
  pullback.lift_fst _ _ _

/-- The comparison morphism followed by the second projection to `Z ×_X V`. -/
@[reassoc (attr := simp)]
theorem restrictionComparisonMap_snd :
    restrictionComparisonMap q z m v g h ≫ pullback.snd z g = pullback.snd _ m ≫ v :=
  pullback.lift_snd _ _ _

/-- For `z` a closed immersion and `v` proper, the comparison morphism is proper. -/
instance isProper_restrictionComparisonMap [IsClosedImmersion z] [IsProper v] :
    IsProper (restrictionComparisonMap q z m v g h) := by
  unfold restrictionComparisonMap
  infer_instance

/-- The comparison morphism lies over the base. -/
theorem restrictionComparisonMap_comp_structure (f : X ⟶ C.S) :
    restrictionComparisonMap q z m v g h ≫ (pullback.fst z g ≫ (z ≫ f)) =
      pullback.fst (pullback.fst q z) m ≫ (pullback.fst q z ≫ (q ≫ f)) := by
  rw [restrictionComparisonMap_fst_assoc, ← pullback.condition_assoc]

end Bookkeeping

/-! ### The class at infinity and a class supported on `W ×_X Z` -/

section Generic

variable {C : ChowSituation.{u}} {X W Z : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (z : Z ⟶ X) [IsClosedImmersion z]
  {p : ℤ}
  (R : BivariantClass C (gysinSystemOfInvertible C)
    (pullback.fst (modificationProjection f b) z ≫ modificationProjection f b ≫ f)
    (modificationProjection f b ≫ f) (pullback.fst (modificationProjection f b) z) rfl p)

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The base-changed fibre at infinity over a test scheme lies over the test scheme. -/
theorem fst_comp_inclusionAtInfinity_comp {V : Scheme.{u}} (g : V ⟶ X) :
    (pullback.fst (modificationProjectionAtInfinity f b) g ≫ modificationInclusionAtInfinity f b)
        ≫ modificationProjection f b =
      pullback.snd (modificationProjectionAtInfinity f b) g ≫ g := by
  rw [Category.assoc, ← pullback.condition]

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The section at zero over a test scheme lies over the test scheme. -/
theorem comp_sectionAtZero_comp {V : Scheme.{u}} (g : V ⟶ X) :
    (g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)) ≫
        modificationProjection f b = 𝟙 V ≫ g := by
  rw [Category.assoc, modificationSectionAtZero_comp_projection f b hA, Category.comp_id,
    Category.id_comp]

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The section at zero over a test scheme lies over the base. -/
theorem comp_sectionAtZero_comp_structure {V : Scheme.{u}} (g : V ⟶ X) :
    g ≫ f = (g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))
      ≫ modificationProjection f b ≫ f := by
  rw [Category.assoc, ← Category.assoc (modificationSectionAtZero _ _ _),
    modificationSectionAtZero_comp_projection f b hA, Category.id_comp]

/-- **The class at infinity followed by a class on `W` supported on `W ×_X Z`.** Let
`R ∈ A^p(W_Z ⟶ W)` for `W_Z = W ×_X Z`. On a test scheme `g : V ⟶ X`, the pushforward to
`Z ×_X V` of `R ∩ (C ∩ α)`, computed on `W_∞ ×_X V ⟶ W`, is that of `R ∩ α`, computed on
`V ⟶ X ⟶ W` through the section at zero. By proper naturality of `R` both are pushforwards of
`R` capped with a class on `W ×_X V`, namely `i_{∞,*}(C ∩ α)` and `i_{0,*} α`, which agree by
Stacks 0F9J. -/
theorem chowPush_cap_gysinCapOfLift {V : Scheme.{u}} (g : V ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    chowPush C _ (pullback.fst z g ≫ (z ≫ f))
        (restrictionComparisonMap (modificationProjection f b) z
          (pullback.fst (modificationProjectionAtInfinity f b) g ≫
            modificationInclusionAtInfinity f b)
          (pullback.snd (modificationProjectionAtInfinity f b) g) g
          (fst_comp_inclusionAtInfinity_comp g))
        (restrictionComparisonMap_comp_structure _ _ _ _ _ _ f) (k - p)
        (R.cap (pullback.fst (modificationProjectionAtInfinity f b) g ≫
            modificationInclusionAtInfinity f b) k
          (chowGroupCongr C (by
            simp only [modificationInfinityBaseChangeOver, modificationProjectionAtInfinity,
              Category.assoc]) k (gysinCapAtInfinity C f b hA g k α))) =
      chowPush C _ (pullback.fst z g ≫ (z ≫ f))
        (restrictionComparisonMap (modificationProjection f b) z
          (g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))
          (𝟙 V) g (comp_sectionAtZero_comp hA g))
        (restrictionComparisonMap_comp_structure _ _ _ _ _ _ f) (k - p)
        (R.cap (g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))
          k (chowGroupCongr C (comp_sectionAtZero_comp_structure hA g) k α)) := by
  have := isClosedImmersion_modificationSectionAtZeroBaseChange f b g hA
  set π := modificationProjection f b
  set i₀ := modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)
  set hInf := modificationInfinityBaseChange f b g
  set h₀ := modificationSectionAtZeroBaseChange f b (isIso_modificationFibreAtZeroProjection f b hA)
    (modificationSectionAtZero_comp_projection f b hA) g
  set mInf := pullback.fst (modificationProjectionAtInfinity f b) g ≫
    modificationInclusionAtInfinity f b
  have hmInf : hInf ≫ pullback.fst π g = mInf := modificationInfinityBaseChange_comp_fst f b g
  have hm₀ : h₀ ≫ pullback.fst π g = g ≫ i₀ := pullback.lift_fst _ _ _
  set ψ := restrictionComparisonMap π z (pullback.fst π g) (pullback.snd π g) g pullback.condition
  have eInf := R.cap_properChowPushforward (properPushforwardDescends C) (pullback.fst π g) hInf
    mInf hmInf (pullback.lift (pullback.fst _ mInf) (pullback.snd _ mInf ≫ hInf) (by
      rw [pullback.condition, Category.assoc, hmInf]))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) k
    (chowGroupCongr C (by
      simp only [mInf, modificationInfinityBaseChangeOver, modificationProjectionAtInfinity,
        Category.assoc]) k (gysinCapAtInfinity C f b hA g k α))
  have e₀ := R.cap_properChowPushforward (properPushforwardDescends C) (pullback.fst π g) h₀
    (g ≫ i₀) hm₀ (pullback.lift (pullback.fst _ (g ≫ i₀)) (pullback.snd _ (g ≫ i₀) ≫ h₀) (by
      rw [pullback.condition, Category.assoc, hm₀]))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) k
    (chowGroupCongr C (comp_sectionAtZero_comp_structure hA g) k α)
  have hJ := chowPushforward_gysinCapOfLift C f b g hA k α
  have hJ' : properChowPushforward C (mInf ≫ π ≫ f) (pullback.fst π g ≫ π ≫ f) hInf
        (by rw [← Category.assoc, hmInf]) k (properPushforwardDescends C _ _ _ _ _)
        (chowGroupCongr C (by
          simp only [mInf, π, modificationInfinityBaseChangeOver,
            modificationProjectionAtInfinity, Category.assoc]) k
          (gysinCapAtInfinity C f b hA g k α)) =
      properChowPushforward C ((g ≫ i₀) ≫ π ≫ f) (pullback.fst π g ≫ π ≫ f) h₀
        (by rw [← Category.assoc, hm₀]) k (properPushforwardDescends C _ _ _ _ _)
        (chowGroupCongr C (comp_sectionAtZero_comp_structure hA g) k α) := by
    rw [← properChowPushforward_chowGroupCongr C _ rfl hInf
        (modificationInfinityBaseChange_over f b g) _ k
        (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _),
      ← properChowPushforward_chowGroupCongr C _ rfl h₀
        (modificationSectionAtZeroBaseChange_over f b g _ _) _ k
        (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
    exact congrArg (chowGroupCongr C rfl k) hJ
  have cInf : pullback.lift (pullback.fst _ mInf) (pullback.snd _ mInf ≫ hInf) (by
      rw [pullback.condition, Category.assoc, hmInf]) ≫ ψ =
      restrictionComparisonMap π z mInf (pullback.snd (modificationProjectionAtInfinity f b) g) g
        (fst_comp_inclusionAtInfinity_comp g) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [ψ, Category.assoc, restrictionComparisonMap_fst]
      rw [pullback.lift_fst_assoc]
    · simp only [ψ, Category.assoc, restrictionComparisonMap_snd, pullback.lift_snd_assoc]
      rw [modificationInfinityBaseChange_comp_snd]
  have c₀ : pullback.lift (pullback.fst _ (g ≫ i₀)) (pullback.snd _ (g ≫ i₀) ≫ h₀) (by
      rw [pullback.condition, Category.assoc, hm₀]) ≫ ψ =
      restrictionComparisonMap π z (g ≫ i₀) (𝟙 V) g (comp_sectionAtZero_comp hA g) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [ψ, Category.assoc, restrictionComparisonMap_fst]
      rw [pullback.lift_fst_assoc]
    · simp only [ψ, Category.assoc, restrictionComparisonMap_snd, pullback.lift_snd_assoc]
      rw [modificationSectionAtZeroBaseChange_comp_snd]
  rw [← chowPush_comp C _ _ _ _ ψ _ cInf _ (restrictionComparisonMap_comp_structure _ _ _ _ _ _ f),
    ← chowPush_comp C _ _ _ _ ψ _ c₀ _ (restrictionComparisonMap_comp_structure _ _ _ _ _ _ f)]
  · refine congrArg (chowPush C _ _ ψ _ (k - p)) ?_
    exact eInf.symm.trans ((congrArg (R.cap (pullback.fst π g) k) hJ').trans e₀)
  all_goals rw [← Category.assoc, pullback.lift_fst]

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion z] in
/-- The identification of `Stacks.Chow.modificationInfinityRestrictionIso` followed by the
exceptional base change map of `Stacks.Chow.localizedModificationClass_cap_heq` is the comparison
morphism `(W ×_X Z) ×_W (W_∞ ×_X V) ⟶ Z ×_X V`. -/
theorem modificationInfinityRestrictionIso_hom_comp_exceptionalBaseChangeMap {V : Scheme.{u}}
    (g : V ⟶ X) :
    (modificationInfinityRestrictionIso z
          (pullback.fst (modificationProjectionAtInfinity f b) g)).hom ≫
        exceptionalBaseChangeMap (modificationProjectionAtInfinity f b) z g =
      restrictionComparisonMap (modificationProjection f b) z
        (pullback.fst (modificationProjectionAtInfinity f b) g ≫
          modificationInclusionAtInfinity f b)
        (pullback.snd (modificationProjectionAtInfinity f b) g) g
        (fst_comp_inclusionAtInfinity_comp g) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, exceptionalBaseChangeMap_fst,
      modificationInfinityRestrictionIso_hom_fst_assoc, pullback.lift_snd,
      restrictionComparisonMap_fst]
  · rw [Category.assoc, exceptionalBaseChangeMap_snd,
      modificationInfinityRestrictionIso_hom_snd_assoc, restrictionComparisonMap_snd]

end Generic

/-! ### The restriction of a class on `X` at the section at zero -/

section ZeroSection

variable {C : ChowSituation.{u}} {X W Z : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (z : Z ⟶ X) [IsClosedImmersion z]
  {p : ℤ}

/-- **The restriction of a class on `X` to `W`, read at the section at zero.** For
`c ∈ A^p(Z ⟶ X)`, let `R ∈ A^p(W ×_X Z ⟶ W)` be the restriction (Remark 0F9Z) of `c` along
`π : W ⟶ X`, read on `W ×_X Z` through `Z ×_X W ≅ W ×_X Z` (Stacks 0EPK). On a test scheme
`g : V ⟶ X`, `R ∩ α`, computed on `V ⟶ X ⟶ W` through the section at zero `i_0` and pushed forward
to `Z ×_X V`, is `c ∩ α`, because `π ∘ i_0 = 𝟙`. -/
theorem chowPush_cap_sectionAtZero_bivariantRestriction
    (c : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p)
    {V : Scheme.{u}} (g : V ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    chowPush C _ (pullback.fst z g ≫ (z ≫ f))
        (restrictionComparisonMap (modificationProjection f b) z
          (g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))
          (𝟙 V) g (comp_sectionAtZero_comp hA g))
        (restrictionComparisonMap_comp_structure _ _ _ _ _ _ f) (k - p)
        ((bivariantProperPushforwardOfInvertible C
          (pullback.snd z (modificationProjection f b) ≫ modificationProjection f b ≫ f)
          (pullback.fst (modificationProjection f b) z ≫ modificationProjection f b ≫ f)
          (modificationProjection f b ≫ f) (pullbackSymmetry z (modificationProjection f b)).hom
          (pullback.fst (modificationProjection f b) z)
          (by rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]) rfl p
          ((bivariantClassCongrBase C (gysinSystemOfInvertible C)
            (pullback.snd z (modificationProjection f b))
            (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl
              (modificationProjection f b)).symm rfl
            (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl
              (modificationProjection f b)) (hv' := rfl) p
            (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl
              (modificationProjection f b) p
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)).congrHom
            (pullbackSymmetry_hom_comp_fst _ _).symm
            (by rw [pullbackSymmetry_hom_comp_fst]))).cap
          (g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)) k
          (chowGroupCongr C (comp_sectionAtZero_comp_structure hA g) k α)) =
      c.cap g k α := by
  set π := modificationProjection f b
  set m := g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)
  set R'' := bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd z π)
    (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl π).symm rfl
    (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl π) (hv' := rfl) p
    (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl π p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
  have e : m ≫ π = g := by
    rw [Category.assoc, modificationSectionAtZero_comp_projection f b hA, Category.comp_id]
  have hR := (bivariantClassCongrBase_cap C (gysinSystemOfInvertible C) (pullback.snd z π)
    (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl π).symm rfl
    (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl π) (hv' := rfl) p
    (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl π p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c) m k
    (chowGroupCongr C (comp_sectionAtZero_comp_structure hA g) k α)
    (chowGroupCongr C (comp_sectionAtZero_comp_structure hA g) k α) HEq.rfl).trans
    (heq_of_eq (bivariantRestrictionCap_apply C (gysinSystemOfInvertible C) (z ≫ f) f z rfl π p
      c m k (chowGroupCongr C (comp_sectionAtZero_comp_structure hA g) k α)))
  have hcomp : (pullbackLeftPullbackSndIso z π m).inv ≫
      ((pullback.congrHom (pullbackSymmetry_hom_comp_fst z π).symm rfl).hom ≫
        bivariantPushforwardBaseChange (pullbackSymmetry z π).hom (pullback.fst π z) m ≫
        restrictionComparisonMap π z m (𝟙 V) g (comp_sectionAtZero_comp hA g)) =
      (pullback.congrHom (rfl : z = z) e).hom := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, restrictionComparisonMap_fst,
        bivariantPushforwardBaseChange_fst_assoc, pullbackSymmetry_hom_comp_snd,
        pullback.congrHom_hom, pullbackMap_fst_assoc, Category.comp_id, Category.id_comp,
        pullbackLeftPullbackSndIso_inv_fst, pullbackMap_fst]
    · simp only [Category.assoc, restrictionComparisonMap_snd, Category.comp_id,
        bivariantPushforwardBaseChange_snd, pullback.congrHom_hom, pullbackMap_snd,
        pullbackLeftPullbackSndIso_inv_snd_snd]
  have hbase : (pullback.congrHom (rfl : z = z) e).hom ≫ (pullback.fst z g ≫ z ≫ f) =
      pullback.fst z (m ≫ π) ≫ z ≫ f := by
    simp
  rw [bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply,
    BivariantClass.congrHom_cap]
  have hsrc : pullback.fst (pullback.snd z π) m ≫ (pullback.snd z π ≫ π ≫ f) =
      pullback.fst (pullback.snd z π) m ≫ (pullback.fst z π ≫ (z ≫ f)) := by
    rw [pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl π]
  have hu : ((pullback.congrHom (pullbackSymmetry_hom_comp_fst z π).symm rfl).hom ≫
      bivariantPushforwardBaseChange (pullbackSymmetry z π).hom (pullback.fst π z) m ≫
      restrictionComparisonMap π z m (𝟙 V) g (comp_sectionAtZero_comp hA g)) ≫
        (pullback.fst z g ≫ z ≫ f) =
      pullback.fst (pullback.snd z π) m ≫ (pullback.snd z π ≫ π ≫ f) := by
    simp only [Category.assoc, restrictionComparisonMap_comp_structure,
      bivariantPushforwardBaseChange_fst_assoc, pullbackSymmetry_hom_comp_fst_assoc,
      pullback.congrHom_hom, pullbackMap_fst_assoc, Category.id_comp]
  have key := chowPush_heq C _ hu (hu.trans hsrc) hsrc rfl rfl hR
  rw [chowPush_chowPushforwardOfIso C _ _ _ _ _ _ _ (by rw [hcomp, hbase]),
    chowPush_congr C _ _ hcomp _ hbase, chowGroupCongr_chowGroupCongr] at key
  refine Eq.trans ?_ ((eq_of_heq key).trans (chowPushforwardOfIso_congrHom_cap C
    (gysinSystemOfInvertible C) (z ≫ f) f z rfl p c e (by simp) k α _ rfl))
  exact chowPush_comp_comp _ _ _ _ _ _ _ _ _ _ hu (k - p) _

end ZeroSection

/-! ### The localized class of Stacks 0F9K through a class on `W` -/

section ThroughW

variable {C : ChowSituation.{u}} {X W Z T : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (z : Z ⟶ X) [IsClosedImmersion z]
  {p : ℤ}

/-- The section at zero `i_0 : X ⟶ W` as a morphism into the chart `b^{-1}(𝐀¹_X)`. -/
def modificationSectionAtZeroToChart : X ⟶ pullback b (projectiveLineAffineChart f) :=
  pullback.lift (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))
    (affineLineZeroSection X) (by
      rw [modificationSectionAtZero_comp f b hA,
        affineLineZeroSection_comp_projectiveLineAffineChart])

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The section at zero into the chart, followed by the chart, is the section at zero. -/
@[reassoc (attr := simp)]
theorem modificationSectionAtZeroToChart_fst :
    modificationSectionAtZeroToChart hA ≫ pullback.fst b (projectiveLineAffineChart f) =
      modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA) :=
  pullback.lift_fst _ _ _

/-- **The localized class of Stacks 0F9K through a class on `W` supported on `W ×_X Z`.** Let
`R ∈ A^p(W_Z ⟶ W)` for `W_Z = W ×_X Z` be such that

* the class `(q|_E)' ∈ A^p(E ⟶ W_∞)` is the restriction of `R` to `W_∞`
  (`Stacks.Chow.IsModificationInfinityRestriction`), and
* on the test schemes factoring through the chart `b^{-1}(𝐀¹_X)`, `R` caps as the restriction
  (Remark 0F9Z) along `π : W ⟶ X` of a class `c ∈ A^p(Z ⟶ X)`, read on `W ×_X Z`.

Then the localized class `q' = (E ⟶ Z)_* ∘ (q|_E)' ∘ C` of Stacks 0F9K is `c`. On a test scheme
`V ⟶ X`, `q' ∩ α` is the pushforward of `(q|_E)' ∩ (C ∩ α)`, hence of `R ∩ (C ∩ α)`, which is
that of `R ∩ α` computed through the section at zero (`Stacks.Chow.chowPush_cap_gysinCapOfLift`);
the section at zero factors through the chart, where `R` is the restriction of `c`, and
`π ∘ i_0 = 𝟙` (`Stacks.Chow.chowPush_cap_sectionAtZero_bivariantRestriction`). -/
theorem localizedModificationClass_eq_of_isModificationInfinityRestriction
    (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (c : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p)
    (R : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjection f b) z ≫ modificationProjection f b ≫ f)
      (modificationProjection f b ≫ f) (pullback.fst (modificationProjection f b) z) rfl p)
    (hext : IsModificationInfinityRestriction C f b z R (modificationExtension z t hT hq))
    (hres : ∀ {Y : Scheme.{u}} (v : Y ⟶ pullback b (projectiveLineAffineChart f))
      [LocallyOfFiniteType v] (k : ℤ)
      (β : chowGroup C ((v ≫ pullback.fst b (projectiveLineAffineChart f)) ≫
        (modificationProjection f b ≫ f)) k),
      R.cap (v ≫ pullback.fst b (projectiveLineAffineChart f)) k β =
        (bivariantProperPushforwardOfInvertible C
          (pullback.snd z (modificationProjection f b) ≫ modificationProjection f b ≫ f)
          (pullback.fst (modificationProjection f b) z ≫ modificationProjection f b ≫ f)
          (modificationProjection f b ≫ f) (pullbackSymmetry z (modificationProjection f b)).hom
          (pullback.fst (modificationProjection f b) z)
          (by rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]) rfl p
          ((bivariantClassCongrBase C (gysinSystemOfInvertible C)
            (pullback.snd z (modificationProjection f b))
            (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl
              (modificationProjection f b)).symm rfl
            (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl
              (modificationProjection f b)) (hv' := rfl) p
            (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl
              (modificationProjection f b) p
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)).congrHom
            (pullbackSymmetry_hom_comp_fst _ _).symm
            (by rw [pullbackSymmetry_hom_comp_fst]))).cap
          (v ≫ pullback.fst b (projectiveLineAffineChart f)) k β) :
    localizedModificationClass (gysinAtInfinityData C f b hA) z t hT hq = c := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {V} g _ k α ↦ eq_of_heq ?_
  refine (localizedModificationClass_cap_heq (gysinAtInfinityData C f b hA) z t hT hq g k
    α).trans ?_
  rw [hext, chowPush_chowPushforwardOfIso C _ _ _ _ _ _ _ (by
      rw [modificationInfinityRestrictionIso_hom_comp_exceptionalBaseChangeMap,
        restrictionComparisonMap_comp_structure]),
    chowPush_congr C _ _ (modificationInfinityRestrictionIso_hom_comp_exceptionalBaseChangeMap z g)
      _ (restrictionComparisonMap_comp_structure _ _ _ _ _ _ f)]
  refine (chowPush_heq C _ (restrictionComparisonMap_comp_structure _ _ _ _ _ _ f)
    (restrictionComparisonMap_comp_structure _ _ _ _ _ _ f) rfl rfl (by ring : k - 0 - p = k - p)
    (R.cap_heq_congr _ (sub_zero k) _
      (chowGroupCongr C (by
        simp only [modificationInfinityBaseChangeOver, modificationProjectionAtInfinity,
          Category.assoc]) k (gysinCapAtInfinity C f b hA g k α)) ?_)).trans ?_
  · refine (chowGroupCongr_heq C _ _ _).trans (HEq.trans ?_ (chowGroupCongr_heq C _ _ _).symm)
    exact chowGroupDegreeEquiv_heq C _ _ _
  rw [chowPush_cap_gysinCapOfLift hA z R g k α]
  have hres₀ : ∀ (m : V ⟶ W) [LocallyOfFiniteType m],
      (g ≫ modificationSectionAtZeroToChart hA) ≫ pullback.fst b (projectiveLineAffineChart f) = m →
      ∀ β : chowGroup C (m ≫ (modificationProjection f b ≫ f)) k,
        R.cap m k β = (bivariantProperPushforwardOfInvertible C _ _ _
          (pullbackSymmetry z (modificationProjection f b)).hom
          (pullback.fst (modificationProjection f b) z)
          (by rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]) rfl p
          ((bivariantClassCongrBase C (gysinSystemOfInvertible C)
            (pullback.snd z (modificationProjection f b))
            (pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl
              (modificationProjection f b)).symm rfl
            (hv := pullbackSnd_comp_structureMorphism_eq C (z ≫ f) f z rfl
              (modificationProjection f b)) (hv' := rfl) p
            (bivariantRestriction C (gysinSystemOfInvertible C) (z ≫ f) f z rfl
              (modificationProjection f b) p
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)).congrHom
            (pullbackSymmetry_hom_comp_fst _ _).symm
            (by rw [pullbackSymmetry_hom_comp_fst]))).cap m k β := by
    intro m _ hm β
    subst hm
    have := locallyOfFiniteType_of_comp (g ≫ modificationSectionAtZeroToChart hA)
      (pullback.fst b (projectiveLineAffineChart f))
    exact hres _ k β
  rw [hres₀ _ (by rw [Category.assoc, modificationSectionAtZeroToChart_fst])]
  exact heq_of_eq (chowPush_cap_sectionAtZero_bivariantRestriction hA z c g k α)

end ThroughW

/-! ### The exceptional class of Stacks 0F9K as a restriction -/

section Exceptional

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X W Z T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {Q : DerivedCategory W.Modules}

/-- A class equal to the pushforward of the restriction of `κ` to `W_∞` is a restriction of `κ`. -/
private theorem isModificationInfinityRestriction_of_eq_bivariantProperPushforward
    {m : ℤ}
    (κ : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjection f b) z ≫ modificationProjection f b ≫ f)
      (modificationProjection f b ≫ f) (pullback.fst (modificationProjection f b) z) rfl m)
    (E : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl m)
    (hE : E = bivariantProperPushforwardOfInvertible C _ _ _ (modificationInfinityRestrictionMap z)
      (pullback.fst (modificationProjectionAtInfinity f b) z)
      (by rw [← Category.assoc, modificationInfinityRestrictionMap_fst]) rfl m
      ((bivariantClassCongrBase C (gysinSystemOfInvertible C)
        (pullback.snd (pullback.fst (modificationProjection f b) z)
          (modificationInclusionAtInfinity f b))
        (pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _) (hv' := rfl) m
        (bivariantRestriction C (gysinSystemOfInvertible C) _ _ _ rfl
          (modificationInclusionAtInfinity f b) m
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ)).congrHom
        (modificationInfinityRestrictionMap_fst z).symm
        (by rw [← Category.assoc, modificationInfinityRestrictionMap_fst, Category.assoc]))) :
    IsModificationInfinityRestriction C f b z κ E :=
  hE ▸ isModificationInfinityRestriction_bivariantProperPushforward C f b z κ

/-- **The exceptional class `(c_p(Q)|_E)'` of Stacks 0F9K is the restriction of `c_p(W_Z ⟶ W, Q)`
to `W_∞`**, in the sense of `Stacks.Chow.IsModificationInfinityRestriction`: by
`Stacks.Chow.modificationExtension_perfectChernClass` it is the class `c'_p(Q|_{W_{Z,∞}})` of
Stacks 0F9H, which by Stacks 0FB8, 0FB7 and 0FB3 is the restriction of the localized Chern class
`c_p(W_Z ⟶ W, Q)` of the situation `Stacks.Chow.modificationSituationOf`. -/
theorem isModificationInfinityRestriction_modificationExtension_perfectChernClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (hperf : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q)
    (hres : ∃ M : StrictlyPerfect.OXMod.{u, u, u} (W.toRingedSpace.restrict
          (modificationComplementOpens b z).isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M p ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (W.toRingedSpace.ofRestrict (modificationComplementOpens b z).isOpenEmbedding)).obj
              Q ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (hfin : LocalizedChernFiniteness C (modificationProjection f b ≫ f) Q)
    (h₀ : (modificationSituationOf C f b z p hperf (Or.inr hres) hfin)
      |>.IsFiniteLocallyFreeOfRankLTOnComplement) :
    IsModificationInfinityRestriction C f b z
      ((modificationSituationOf C f b z p hperf (Or.inr hres) hfin).localizedChern h₀)
      (modificationExtension z t hT (vanishesOver_perfectChernClass_of_rankLT C
        (modificationProjection f b ≫ f) (t ≫ modificationInclusionAtInfinity f b) hQ p
          hrank)) := by
  let S₀ := modificationSituationOf C f b z p hperf (Or.inr hres) hfin
  let S' := S₀.pullback (modificationInclusionAtInfinity f b)
  let S := S'.withLargerClosed (pullback.fst (modificationProjectionAtInfinity f b) z)
    (modificationInfinityRestrictionMap z) (modificationInfinityRestrictionMap_fst z)
  have : @IsClosedImmersion T S.X t := ‹_›
  have h8 := S.closedCoverChernClass_eq_localizedChern t
    (range_union_range_pullbackFst_eq_univ z t hT)
    (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_inclusionAtInfinity C f b hrank)
  have h7 := LocalizedSituation.localizedChern_withLargerClosed (S := S')
    (i' := pullback.fst (modificationProjectionAtInfinity f b) z)
    (j := modificationInfinityRestrictionMap z) (hj := modificationInfinityRestrictionMap_fst z)
    h₀.pullback
  have h3 := S₀.bivariantRestriction_localizedChern (modificationInclusionAtInfinity f b) h₀
  rw [← h3] at h7
  rw [modificationExtension_perfectChernClass C f b z t hT hQ p hrank]
  exact @isModificationInfinityRestriction_of_eq_bivariantProperPushforward C _ _ _ f _ b _ z _
    _ _ _ (h8.trans h7)

/-- **The exceptional class `(P_p(Q)|_E)'` of Stacks 0F9K is the restriction of
`P_p(W_Z ⟶ W, Q)` to `W_∞`**, in the sense of `Stacks.Chow.IsModificationInfinityRestriction`: by
`Stacks.Chow.modificationExtension_perfectPowerSumClass` it is the class `P'_p(Q|_{W_{Z,∞}})` of
Stacks 0F9H, which by Stacks 0FB8, 0FB7 and 0FB3 is the restriction of the localized class
`P_p(W_Z ⟶ W, Q)` of the situation `Stacks.Chow.modificationSituationOf`. -/
theorem isModificationInfinityRestriction_modificationExtension_perfectPowerSumClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q))
    (hperf : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q)
    (hres : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (W.toRingedSpace.ofRestrict (modificationComplementOpens b z).isOpenEmbedding)).obj Q))
    (hfin : LocalizedChernFiniteness C (modificationProjection f b ≫ f) Q)
    (h₀ : (modificationSituationOf C f b z p hperf (Or.inl hres) hfin).IsZeroOnComplement) :
    IsModificationInfinityRestriction C f b z
      ((modificationSituationOf C f b z p hperf (Or.inl hres) hfin).localizedPowerSum h₀ p)
      (modificationExtension z t hT (vanishesOver_perfectPowerSumClass_of_isZero C
        (modificationProjection f b ≫ f) (t ≫ modificationInclusionAtInfinity f b) hQ p
          hzero)) := by
  let S₀ := modificationSituationOf C f b z p hperf (Or.inl hres) hfin
  let S' := S₀.pullback (modificationInclusionAtInfinity f b)
  let S := S'.withLargerClosed (pullback.fst (modificationProjectionAtInfinity f b) z)
    (modificationInfinityRestrictionMap z) (modificationInfinityRestrictionMap_fst z)
  have : @IsClosedImmersion T S.X t := ‹_›
  have h8 := S.closedCoverPowerSum_eq_localizedPowerSum t
    (range_union_range_pullbackFst_eq_univ z t hT)
    (isZero_derivedPullback_inclusionAtInfinity C f b hzero) p
  have h7 := LocalizedSituation.localizedPowerSum_withLargerClosed (S := S')
    (i' := pullback.fst (modificationProjectionAtInfinity f b) z)
    (j := modificationInfinityRestrictionMap z) (hj := modificationInfinityRestrictionMap_fst z)
    h₀.pullback p
  have h3 := S₀.bivariantRestriction_localizedPowerSum (modificationInclusionAtInfinity f b) h₀ p
  rw [← h3] at h7
  rw [modificationExtension_perfectPowerSumClass C f b z t hT hQ p hzero]
  exact @isModificationInfinityRestriction_of_eq_bivariantProperPushforward C _ _ _ f _ b _ z _
    _ _ _ (h8.trans h7)

end Exceptional

/-! ### Stacks 0FE8 -/

namespace LocalizedSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : LocalizedSituation.{u}) {W T : Scheme.{u}}
  (b : W ⟶ projectiveLineProduct S.a) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart S.a)))
  (t : T ⟶ modificationFibreAtInfinity S.a b) [IsClosedImmersion t]
  {Q : DerivedCategory W.Modules}
  (hQp : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q)
  (hfin : LocalizedChernFiniteness S.base (modificationProjection S.a b ≫ S.a) Q)
  (hF : Nonempty ((derivedPullback
      (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q ≅
    (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a) ≫
      modificationProjection S.a b).toLRSHom.toShHom).obj S.E))

/-- The identification of `Q|_{b^{-1}(𝐀¹_X)}` with the pullback of `F`, as an isomorphism with the
pullback of `π^* F`. -/
def modificationChartIso :
    (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q ≅
      (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj
        ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E) :=
  hF.some ≪≫ (derivedPullbackCompIsoOfScheme _ _ S.E).symm

/-- The situation of Stacks 0GUJ for `W`, `W_Z = W ×_X Z` and `π^* F`, as
`Stacks.Chow.modificationSituationOf`: the base change of Situation 0GUJ along `π : W ⟶ X`
(`Stacks.Chow.LocalizedSituation.pullback`), with its closed subscheme `Z ×_X W` presented as
`W ×_X Z` (Stacks 0FB7, `Stacks.Chow.LocalizedSituation.withLargerClosed`). -/
abbrev modificationPullbackSituation
    (hres : IsZero ((derivedPullback
        (W.toRingedSpace.ofRestrict (modificationComplementOpens b S.i).isOpenEmbedding)).obj
          ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E)) ∨
      ∃ M : StrictlyPerfect.OXMod.{u, u, u}
          (W.toRingedSpace.restrict (modificationComplementOpens b S.i).isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M S.p ∧ Nonempty ((derivedPullback
          (W.toRingedSpace.ofRestrict (modificationComplementOpens b S.i).isOpenEmbedding)).obj
            ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E) ≅
            (DerivedCategory.singleFunctor _ 0).obj M)) :
    LocalizedSituation.{u} :=
  modificationSituationOf S.base S.a b S.i S.p (S.pullback (modificationProjection S.a b)).perfect
    hres (S.finiteness_pullback (modificationProjection S.a b))

include hF in
/-- **The localized Chern classes of `Q` and of `π^* F` agree on `b^{-1}(𝐀¹_X)`.** The restrictions
(Remark 0F9Z) to the chart of `c_p(W_Z ⟶ W, Q)` and of `c_p(W_Z ⟶ W, π^* F)` coincide: by
Stacks 0FB3 both are localized Chern classes on the chart, of `Q|_{b^{-1}(𝐀¹_X)}` and of the
pullback of `F`, which are isomorphic; the comparison of their graph constructions is that of the
proof of Stacks 0FB3. -/
theorem bivariantRestriction_modificationSituationOf_localizedChern
    (hres : ∃ M : StrictlyPerfect.OXMod.{u, u, u}
          (W.toRingedSpace.restrict (modificationComplementOpens b S.i).isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M S.p ∧ Nonempty ((derivedPullback
          (W.toRingedSpace.ofRestrict (modificationComplementOpens b S.i).isOpenEmbedding)).obj Q ≅
            (DerivedCategory.singleFunctor _ 0).obj M))
    (h₀ : (modificationSituationOf S.base S.a b S.i S.p hQp (Or.inr hres) hfin)
      |>.IsFiniteLocallyFreeOfRankLTOnComplement)
    (hresF : ∃ M : StrictlyPerfect.OXMod.{u, u, u}
          (W.toRingedSpace.restrict (modificationComplementOpens b S.i).isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M S.p ∧ Nonempty ((derivedPullback
          (W.toRingedSpace.ofRestrict (modificationComplementOpens b S.i).isOpenEmbedding)).obj
            ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E) ≅
            (DerivedCategory.singleFunctor _ 0).obj M))
    (hSP : (S.modificationPullbackSituation b (Or.inr hresF))
      |>.IsFiniteLocallyFreeOfRankLTOnComplement) :
    bivariantRestriction S.base (gysinSystemOfInvertible S.base)
        (pullback.fst (modificationProjection S.a b) S.i ≫ modificationProjection S.a b ≫ S.a)
        (modificationProjection S.a b ≫ S.a) (pullback.fst (modificationProjection S.a b) S.i) rfl
        (pullback.fst b (projectiveLineAffineChart S.a)) S.p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
        ((modificationSituationOf S.base S.a b S.i S.p hQp (Or.inr hres) hfin).localizedChern h₀) =
      bivariantRestriction S.base (gysinSystemOfInvertible S.base)
        (pullback.fst (modificationProjection S.a b) S.i ≫ modificationProjection S.a b ≫ S.a)
        (modificationProjection S.a b ≫ S.a) (pullback.fst (modificationProjection S.a b) S.i) rfl
        (pullback.fst b (projectiveLineAffineChart S.a)) S.p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
        ((S.modificationPullbackSituation b (Or.inr hresF)).localizedChern hSP) := by
  let S₀ := modificationSituationOf S.base S.a b S.i S.p hQp (Or.inr hres) hfin
  let SP := S.modificationPullbackSituation b (Or.inr hresF)
  let S₂ := S₀.pullback (pullback.fst b (projectiveLineAffineChart S.a))
  have e : (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj
      ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E) ≅
      (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q :=
    (S.modificationChartIso b hF).symm
  have hl := exists_lift_graphBlowupToBase_and_iso (modificationProjection S.a b ≫ S.a)
    (pullback.fst b (projectiveLineAffineChart S.a))
    ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E) SP.perfect
    ((derivedPullback (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q)
    S₂.perfect e
  obtain ⟨k, hk, ⟨eQ⟩⟩ := hl
  have h₁ := bivariantRestriction_graphChernClass_of_iso SP.base SP.a
    (pullback.fst b (projectiveLineAffineChart S.a)) SP.E SP.perfect S₂.E S₂.perfect SP.i k hk eQ
    SP.graphSubschemeι S₂.graphSubschemeι SP.isFiniteLocallyFree_graphObjectRestrictHomology
    S₂.isFiniteLocallyFree_graphObjectRestrictHomology SP.hasDefinedChernClasses_graphObject
    S₂.hasDefinedChernClasses_graphObject S.p SP.mem_range_graphSubschemeι
    S₂.mem_range_graphSubschemeι (SP.finiteLocallyFreeRank_graphSubscheme_lt hSP)
    (S₂.finiteLocallyFreeRank_graphSubscheme_lt h₀.pullback)
  have h₂ := bivariantRestriction_localizedChern (S := S₀)
    (pullback.fst b (projectiveLineAffineChart S.a)) h₀
  exact (bivariantClassCongrBase _ _ _ _ _ _).injective (h₂.trans h₁.symm)

omit [IsProper b] in
variable {b} in
/-- The points of `W ∖ W ×_X Z` lie over `X ∖ Z`. -/
theorem modificationProjection_notMem_range {w : W} (hw : w ∈ modificationComplementOpens b S.i) :
    modificationProjection S.a b w ∉ Set.range S.i := fun hz =>
  hw (by rw [Scheme.Pullback.range_fst]; exact hz)

include hA hQp hfin hF in
/-- In Situation 0GUJ, let `b : W ⟶ 𝐏¹_X` be proper and an
isomorphism over `𝐀¹_X`, let `Q ∈ D(𝒪_W)` be perfect, and let
`T ⊆ W_∞` be closed, contain every point of `W_∞` lying over `X ∖ Z`, and be such that `Q|_T` is
finite locally free of rank `< p` in degree `0`. Assume that `Q|_{b^{-1}(𝐀¹_X)}` is the pullback
of `F`, that `F|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0`, and that `Q` on `W`
satisfies condition (3) of Situation 0GUJ, so that the Chern classes of `Q` are defined
(`Stacks.Chow.hasDefinedChernClasses_of_localizedChernFiniteness`, assumption (A0) of
Stacks 0F9K). Then the class `c'_p(Q)` of Stacks 0F9K is the localized Chern class
`c_p(Z ⟶ X, F)` of Stacks 0FB2. -/
@[stacks 0FE8 "for c_p: c'_p(Q) = c_p(Z → X, F) when Q|_{b^{-1}(A^1_X)} is the pullback of F \
and F|_{X ∖ Z} is finite locally free of rank < p in degree 0"]
theorem modificationChernClass_eq_localizedChern
    (hT : ∀ w, modificationProjectionAtInfinity S.a b w ∉ Set.range S.i → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M S.p ∧
      Nonempty ((derivedPullback (t ≫ modificationInclusionAtInfinity S.a b).toLRSHom.toShHom).obj
        Q ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    modificationChernClass S.base S.a b hA S.i t
        (hasDefinedChernClasses_of_localizedChernFiniteness S.base _ Q hQp hfin) S.p hT hrank =
      S.localizedChern h := by
  have hQ := hasDefinedChernClasses_of_localizedChernFiniteness S.base _ Q hQp hfin
  have hres := S.modificationRestriction_of_rankLT b t (modificationComplementOpens b S.i)
    (fun _ hw => S.modificationProjection_notMem_range hw) hQp h hF hT hrank
  have hresF := S.exists_rankLT_pullback_restriction b (modificationComplementOpens b S.i)
    (fun _ hw => S.modificationProjection_notMem_range hw) h
  let S₀ := modificationSituationOf S.base S.a b S.i S.p hQp (Or.inr hres) hfin
  have h₀ : S₀.IsFiniteLocallyFreeOfRankLTOnComplement := hres
  let SP := S.modificationPullbackSituation b (Or.inr hresF)
  have hSP : SP.IsFiniteLocallyFreeOfRankLTOnComplement := hresF
  have hbr := S.bivariantRestriction_modificationSituationOf_localizedChern b hQp hfin hF hres h₀
    hresF hSP
  have h7 := localizedChern_withLargerClosed (S := S.pullback (modificationProjection S.a b))
    (i' := pullback.fst (modificationProjection S.a b) S.i)
    (j := (pullbackSymmetry S.i (modificationProjection S.a b)).hom)
    (hj := pullbackSymmetry_hom_comp_fst _ _)
    h.pullback
  have h3 := S.bivariantRestriction_localizedChern (modificationProjection S.a b) h
  unfold modificationChernClass
  refine localizedModificationClass_eq_of_isModificationInfinityRestriction hA S.i t hT _
    (S.localizedChern h) _
    (isModificationInfinityRestriction_modificationExtension_perfectChernClass S.base S.a b S.i t
      hT hQ S.p hrank hQp hres hfin h₀) ?_
  intro Y v _ k β
  rw [BivariantClass.cap_comp_eq_of_bivariantRestriction_eq hbr v k β]
  refine congrArg (fun R => BivariantClass.cap R _ k β) (h7.trans ?_)
  rw [h3]

include hF in
/-- **The localized classes `P_p` of `Q` and of `π^* F` agree on `b^{-1}(𝐀¹_X)`.** The
restrictions (Remark 0F9Z) to the chart of `P_p(W_Z ⟶ W, Q)` and of `P_p(W_Z ⟶ W, π^* F)`
coincide: by Stacks 0FB3 both are localized classes on the chart, of `Q|_{b^{-1}(𝐀¹_X)}` and of
the pullback of `F`, which are isomorphic. -/
theorem bivariantRestriction_modificationSituationOf_localizedPowerSum (p : ℕ)
    (hres : IsZero ((derivedPullback
        (W.toRingedSpace.ofRestrict (modificationComplementOpens b S.i).isOpenEmbedding)).obj Q))
    (h₀ : (modificationSituationOf S.base S.a b S.i p hQp (Or.inl hres) hfin).IsZeroOnComplement)
    (hresF : IsZero ((derivedPullback
        (W.toRingedSpace.ofRestrict (modificationComplementOpens b S.i).isOpenEmbedding)).obj
          ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E)))
    (hSP : (S.modificationPullbackSituation b (Or.inl hresF)).IsZeroOnComplement) :
    bivariantRestriction S.base (gysinSystemOfInvertible S.base)
        (pullback.fst (modificationProjection S.a b) S.i ≫ modificationProjection S.a b ≫ S.a)
        (modificationProjection S.a b ≫ S.a) (pullback.fst (modificationProjection S.a b) S.i) rfl
        (pullback.fst b (projectiveLineAffineChart S.a)) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
        ((modificationSituationOf S.base S.a b S.i p hQp (Or.inl hres) hfin).localizedPowerSum
          h₀ p) =
      bivariantRestriction S.base (gysinSystemOfInvertible S.base)
        (pullback.fst (modificationProjection S.a b) S.i ≫ modificationProjection S.a b ≫ S.a)
        (modificationProjection S.a b ≫ S.a) (pullback.fst (modificationProjection S.a b) S.i) rfl
        (pullback.fst b (projectiveLineAffineChart S.a)) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso S.base)
        ((S.modificationPullbackSituation b (Or.inl hresF)).localizedPowerSum hSP p) := by
  let S₀ := modificationSituationOf S.base S.a b S.i p hQp (Or.inl hres) hfin
  let SP := S.modificationPullbackSituation b (Or.inl hresF)
  let S₂ := S₀.pullback (pullback.fst b (projectiveLineAffineChart S.a))
  have e : (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj
      ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E) ≅
      (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q :=
    (S.modificationChartIso b hF).symm
  have hl := exists_lift_graphBlowupToBase_and_iso (modificationProjection S.a b ≫ S.a)
    (pullback.fst b (projectiveLineAffineChart S.a))
    ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E) SP.perfect
    ((derivedPullback (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q)
    S₂.perfect e
  obtain ⟨k, hk, ⟨eQ⟩⟩ := hl
  have h₁ := bivariantRestriction_graphPowerSumClass_of_iso SP.base SP.a
    (pullback.fst b (projectiveLineAffineChart S.a)) SP.E SP.perfect S₂.E S₂.perfect SP.i k hk eQ
    SP.graphSubschemeι S₂.graphSubschemeι SP.isFiniteLocallyFree_graphObjectRestrictHomology
    S₂.isFiniteLocallyFree_graphObjectRestrictHomology SP.hasDefinedChernClasses_graphObject
    S₂.hasDefinedChernClasses_graphObject p SP.mem_range_graphSubschemeι
    S₂.mem_range_graphSubschemeι (SP.finiteLocallyFreeRank_graphSubscheme_eq_zero hSP)
    (S₂.finiteLocallyFreeRank_graphSubscheme_eq_zero h₀.pullback)
  have h₂ := bivariantRestriction_localizedPowerSum (S := S₀)
    (pullback.fst b (projectiveLineAffineChart S.a)) h₀ p
  exact (bivariantClassCongrBase _ _ _ _ _ _).injective (h₂.trans h₁.symm)

include hA hQp hfin hF in
/-- In Situation 0GUJ, let `b : W ⟶ 𝐏¹_X` be proper and an
isomorphism over `𝐀¹_X`, let `Q ∈ D(𝒪_W)` be perfect, and let
`T ⊆ W_∞` be closed, contain every point of `W_∞` lying over `X ∖ Z`, and be such that `Q|_T` is
zero. Assume that `Q|_{b^{-1}(𝐀¹_X)}` is the pullback of `F`, that `F|_{X ∖ Z}` is zero, and that
`Q` on `W` satisfies condition (3) of Situation 0GUJ, so that the Chern classes of `Q` are defined
(`Stacks.Chow.hasDefinedChernClasses_of_localizedChernFiniteness`, assumption (A0) of
Stacks 0F9K). Then the class `P'_p(Q)` of Stacks 0F9K is the localized class `P_p(Z ⟶ X, F)` of
Stacks 0FB2. -/
@[stacks 0FE8 "for P_p: P'_p(Q) = P_p(Z → X, F) when Q|_{b^{-1}(A^1_X)} is the pullback of F \
and F|_{X ∖ Z} is zero"]
theorem modificationPowerSum_eq_localizedPowerSum (p : ℕ)
    (hT : ∀ w, modificationProjectionAtInfinity S.a b w ∉ Set.range S.i → w ∈ Set.range t)
    (hzero : IsZero ((derivedPullback
      (t ≫ modificationInclusionAtInfinity S.a b).toLRSHom.toShHom).obj Q))
    (h : S.IsZeroOnComplement) :
    modificationPowerSum S.base S.a b hA S.i t
        (hasDefinedChernClasses_of_localizedChernFiniteness S.base _ Q hQp hfin) p hT hzero =
      S.localizedPowerSum h p := by
  have hQ := hasDefinedChernClasses_of_localizedChernFiniteness S.base _ Q hQp hfin
  have hres := S.modificationRestriction_of_isZero b t (modificationComplementOpens b S.i)
    (fun _ hw => S.modificationProjection_notMem_range hw) hQp h hF hT hzero
  have hresF := S.isZero_pullback_restriction b (modificationComplementOpens b S.i)
    (fun _ hw => S.modificationProjection_notMem_range hw) h
  let S₀ := modificationSituationOf S.base S.a b S.i p hQp (Or.inl hres) hfin
  have h₀ : S₀.IsZeroOnComplement := hres
  let SP := S.modificationPullbackSituation b (Or.inl hresF)
  have hSP : SP.IsZeroOnComplement := hresF
  have hbr := S.bivariantRestriction_modificationSituationOf_localizedPowerSum b hQp hfin hF p
    hres h₀ hresF hSP
  have h7 := localizedPowerSum_withLargerClosed
    (S := S.pullback (modificationProjection S.a b))
    (i' := pullback.fst (modificationProjection S.a b) S.i)
    (j := (pullbackSymmetry S.i (modificationProjection S.a b)).hom)
    (hj := pullbackSymmetry_hom_comp_fst _ _)
    h.pullback p
  have h3 := S.bivariantRestriction_localizedPowerSum (modificationProjection S.a b) h p
  unfold modificationPowerSum
  refine localizedModificationClass_eq_of_isModificationInfinityRestriction hA S.i t hT _
    (S.localizedPowerSum h p) _
    (isModificationInfinityRestriction_modificationExtension_perfectPowerSumClass S.base S.a b
      S.i t hT hQ p hzero hQp hres hfin h₀) ?_
  intro Y v _ k β
  rw [BivariantClass.cap_comp_eq_of_bivariantRestriction_eq hbr v k β]
  refine congrArg (fun R => BivariantClass.cap R _ k β) (h7.trans ?_)
  rw [h3]

end LocalizedSituation

end Stacks.Chow

end
