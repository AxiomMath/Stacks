module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCyclesDescent
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FlatPullbackChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ArbitraryRankDual
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.ArbitraryRank
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of a finite locally free module under a change of base scheme

Let `B` be a flat base change of Chow situations `g : S' ⟶ S` with dimension shift `c`
([Stacks, Tag 0FVG]), let `X` be locally of finite type over `S` with base change
`X' = X ×_S S'`, and let `ℰ` be a finite locally free `𝒪_X`-module of rank `r` with base change
`ℰ'` on `X'`. [Stacks, Tag 0FVN] says that the square

  `CH_k(X)     --g^*--> CH_{k+c}(X')`
  `CH_{k-i}(X) --g^*--> CH_{k+c-i}(X')`

with vertical arrows `c_i(ℰ) ∩ -` and `c_i(ℰ') ∩ -` commutes for all `i`.

The cap products are those of the library, `Stacks.Chow.GenuineChern.chernCap`: the operations
`c_j(ℰ) ∩ -` read off the relation of [Stacks, Tag 02U6] on the genuine projective bundle
`Stacks.Chow.bundle ℰ` with its twist `𝒪(1)`.

## The proof

This is the proof of the source. The family `(c_j(ℰ) ∩ α)_j` satisfies the relation of
[Stacks, Tag 02U6] on `P = 𝐏(ℰ)`; base change carries it to a family satisfying the relation on
`P ×_S S' ⟶ X'` with the pulled-back twist (`Stacks.Chow.baseChange_isChernCapFamily`, from
[Stacks, Tag 0FVK] and [Stacks, Tag 0FVM]). The bundle `P ×_S S'` is `𝐏(ℰ')` over `X'`, with
`𝒪(1)` pulling back to `𝒪(1)` (`Stacks.Chow.GenuineChern.bundleBaseChangeHolds`), so flat pullback
along that isomorphism over the identity of `X'` carries the relation to `𝐏(ℰ')`
([Stacks, Tag 02SS] for the twists). The uniqueness of [Stacks, Tag 02U6] on `𝐏(ℰ')`, which holds
by the projective space bundle formula [Stacks, Tag 02TX], identifies the result with the family
`(c_j(ℰ') ∩ g^*α)_j`.

## Main results

* `Stacks.Chow.baseChange_chernCap_of_iso` — the square, for any `ℰ'` identified with the base
  change of `ℰ`.
* `Stacks.Chow.baseChange_chernCap` — **[Stacks, Tag 0FVN]**, for `0 ≤ i ≤ r`.
* `Stacks.Chow.baseChange_chernCap_nat` — **[Stacks, Tag 0FVN]** for every natural number `i`,
  with `c_i ∩ -` zero above the rank.

## References

* [Stacks Project, Tag 0FVN](https://stacks.math.columbia.edu/tag/0FVN)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 0FVM](https://stacks.math.columbia.edu/tag/0FVM)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The family of the cap products of [Stacks, Tag 02U6] at equal degrees and heterogeneously
equal classes. -/
theorem chernCapFamilyOfRank_heq (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] {k k' : ℤ}
    (h : k = k') {α : chowGroup C sX k} {α' : chowGroup C sX k'} (hα : α ≍ α')
    (j : Fin (r + 1)) :
    chernCapFamilyOfRank E r C sX k α j ≍ chernCapFamilyOfRank E r C sX k' α' j := by
  subst h
  cases hα
  rfl

variable (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ B.base.S)
  [LocallyOfFiniteType sX]

/-- **[Stacks, Tag 0FVN] for a module identified with the base change.** Let `ℰ` be finite
locally free of rank `r` on `X` and `ℰ'` finite locally free of rank `r` on `X' = X ×_S S'` with
`ℰ' ≅ (X' ⟶ X)^*ℰ`. Then `c_j(ℰ') ∩ g^*α = g^*(c_j(ℰ) ∩ α)` for every `α ∈ CH_k(X)` and every
`0 ≤ j ≤ r`. -/
theorem baseChange_chernCap_of_iso (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (E' : (pullback sX B.g : Scheme.{u}).Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (eE : E' ≅ (Scheme.Modules.pullback (pullback.fst sX B.g)).obj E)
    (k : ℤ) (j : Fin (r + 1)) (α : chowGroup B.base sX k) :
    GenuineChern.chernCap B.baseChange r (pullback.snd sX B.g) E' (k + B.c) j
        (baseChangeChowPullback B sX k α) =
      chowGroupCast B.baseChange (pullback.snd sX B.g)
        (show k - (j : ℤ) + B.c = k + B.c - (j : ℤ) from by omega)
        (baseChangeChowPullback B sX (k - (j : ℤ))
          (GenuineChern.chernCap B.base r sX E k j α)) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E' r
  let := flat_bundleProj_ofRank E r
  let := locallyOfFiniteType_bundleProj_ofRank E r
  let := flat_bundleProj_ofRank E' r
  let := locallyOfFiniteType_bundleProj_ofRank E' r
  have hπ := relativeDimension_bundleProj_ofRank E r
  have hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence B.base (bundleProj E ≫ sX)
      sX (bundleProj E) rfl (r - 1) hπ k :=
    fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general B.base _ sX _ rfl _ _ k
  -- the family of `α` on `𝐏(ℰ)` and its base change on `𝐏(ℰ) ×_S S'`
  set c := chernCapFamilyOfRank E r B.base sX k α
  have hc : IsChernCapFamily B.base sX (bundleProj E ≫ sX) (bundleProj E) rfl r hπ hfac
      (invertibleChernCap B.base (bundleProj E ≫ sX) (bundleTwist E)) k α c :=
    isChernCapFamilyOfRank_chernCapFamilyOfRank E r B.base sX k α
  have hc' := baseChange_isChernCapFamily B sX (bundleProj E) r hπ hfac (bundleTwist E) k α c hc
  -- `𝐏(ℰ') ≅ X' ×_X 𝐏(ℰ) ≅ 𝐏(ℰ) ×_S S'` over `X'`, with `𝒪(1)` pulling back to `𝒪(1)`
  obtain ⟨e, he, ⟨eT⟩⟩ := GenuineChern.bundleBaseChangeHolds (pullback.fst sX B.g) E E' eE
  have hP := isPullback_baseChangeMorphism B sX (bundleProj E)
  let i : (pullback (pullback.fst sX B.g) (bundleProj E) : Scheme.{u}) ≅
      pullback (bundleProj E ≫ sX) B.g :=
    (IsPullback.of_hasPullback _ _).flip.isoIsPullback _ _ hP
  have hi₁ : i.hom ≫ pullback.fst (bundleProj E ≫ sX) B.g =
      pullback.snd (pullback.fst sX B.g) (bundleProj E) :=
    IsPullback.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback _ _).flip hP
  have hi₂ : i.hom ≫ baseChangeMorphism B sX (bundleProj E) =
      pullback.fst (pullback.fst sX B.g) (bundleProj E) :=
    IsPullback.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback _ _).flip hP
  set f' : bundle E' ⟶ pullback (bundleProj E ≫ sX) B.g := e.hom ≫ i.hom with hf'def
  have hsq : f' ≫ bundleBaseChangeMorphism B sX (bundleProj E) =
      bundleProj E' ≫ 𝟙 (pullback sX B.g : Scheme.{u}) := by
    rw [Category.comp_id, hf'def, Category.assoc, bundleBaseChangeMorphism, hi₂, he]
  have hf' : f' ≫ pullback.snd (bundleProj E ≫ sX) B.g =
      bundleProj E' ≫ pullback.snd sX B.g := by
    rw [← baseChangeMorphism_comp_snd B sX (bundleProj E), ← Category.assoc, hsq,
      Category.comp_id]
  have hfst : e.hom ≫ pullback.snd (pullback.fst sX B.g) (bundleProj E) =
      f' ≫ pullback.fst (bundleProj E ≫ sX) B.g := by
    rw [hf'def, Category.assoc, hi₁]
  have hd' : AlgebraicGeometry.RelativeDimension f' 0 :=
    (AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero f').mp inferInstance
  have hfacf' : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence B.baseChange
      (bundleProj E' ≫ pullback.snd sX B.g) (pullback.snd (bundleProj E ≫ sX) B.g) f' hf' 0 hd'
      k :=
    fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general B.baseChange _ _ f' hf' 0 hd' k
  have hfacid : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence B.baseChange
      (pullback.snd sX B.g) (pullback.snd sX B.g) (𝟙 _) (Category.id_comp _) 0
      (relativeDimension_identity _) k :=
    fun k ↦ flatPullbackFactorsThroughRationalEquivalence_id B.baseChange _ k
  let eL : bundleTwist E' ≅ (Scheme.Modules.pullback f').obj
      (bundleTwistBaseChange B sX (bundleProj E) (bundleTwist E)) :=
    eT.symm ≪≫ (Scheme.Modules.pullbackCongr hfst).app (bundleTwist E) ≪≫
      ((Scheme.Modules.pullbackComp f' (pullback.fst (bundleProj E ≫ sX) B.g)).app
        (bundleTwist E)).symm
  have hcompat := chernTermsCompatibleWithFlatPullback_of_square B.baseChange
    (pullback.snd sX B.g) (pullback.snd sX B.g) (bundleProj E' ≫ pullback.snd sX B.g)
    (pullback.snd (bundleProj E ≫ sX) B.g) (bundleProj E') rfl
    (bundleBaseChangeMorphism B sX (bundleProj E)) (baseChangeMorphism_comp_snd B sX _) r
    (relativeDimension_bundleProj_ofRank E' r)
    (relativeDimension_bundleBaseChangeMorphism B sX (bundleProj E) r hπ)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general B.baseChange _ _ _ rfl _ _ k)
    (flatPullbackFactors_bundleBaseChangeMorphism B sX (bundleProj E) r hπ)
    (bundleTwistCap E' B.baseChange (pullback.snd sX B.g))
    (invertibleChernCap B.baseChange (pullback.snd (bundleProj E ≫ sX) B.g)
      (bundleTwistBaseChange B sX (bundleProj E) (bundleTwist E)))
    (𝟙 _) (Category.id_comp _) 0 (relativeDimension_identity _) hfacid f' hf' hd' hfacf' hsq
    (fun m y y' hy ↦ flatPullbackChow_firstChernClassCapChow_heq B.baseChange _ _ f' hf' 0 hd'
      hfacf' (bundleTwistBaseChange B sX (bundleProj E) (bundleTwist E)) (bundleTwist E') eL m y
      y' hy)
  have hfam := flatPullback_isChernCapFamily (hcompat := hcompat)
    (k := k + B.c) (α := baseChangeChowPullback B sX k α) (c := baseChangeChernFamily B sX r k c)
    (hc := hc') ..
  -- uniqueness on `𝐏(ℰ')`
  have hj := congrFun (eq_chernCapFamilyOfRank_of_isChernCapFamilyOfRank E' r B.baseChange
    (pullback.snd sX B.g) (k + B.c + ((0 : ℕ) : ℤ)) _ _ hfam) j
  rw [GenuineChern.chernCap_eq_chernCapFamilyOfRank, GenuineChern.chernCap_eq_chernCapFamilyOfRank]
  have hid : ∀ (m : ℤ) (x : chowGroup B.baseChange (pullback.snd sX B.g) m),
      flatPullbackChow B.baseChange (pullback.snd sX B.g) (pullback.snd sX B.g) (𝟙 _)
        (Category.id_comp _) 0 (relativeDimension_identity _) m (hfacid m) x ≍ x := fun m x ↦
    (heq_of_eq (flatPullbackChow_id B.baseChange _ m x)).trans (chowGroupCast_heq _ _ _ _)
  refine eq_of_heq ((chernCapFamilyOfRank_heq B.baseChange (pullback.snd sX B.g) E' r (by simp)
    (hid _ (baseChangeChowPullback B sX k α)).symm j).trans ((heq_of_eq hj).symm.trans ?_))
  exact (chowGroupCast_heq _ _ _ _).trans (hid _ _)


/-! ### The Chern classes of Stacks 0ESW on a scheme of constant rank -/

section ArbitraryIndex

/-- The cap product `c ∩ α` of a class `c ∈ A^p(X)` with `α ∈ A_k(X)` is the operation of `c` on
the test scheme `𝟙 X`. -/
theorem chowCohomologyCap_heq_idRule (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {p : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) (k : ℤ)
    (α : chowGroup C sX k) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sX p c k α ≍
      c.idRule C sX (gysinSystemOfInvertible C) (𝟙 X) k
        (chowGroupCongr C (Category.id_comp sX).symm k α) := by
  have hfs : pullback.fst (𝟙 X) (𝟙 X) = pullback.snd (𝟙 X) (𝟙 X) := by
    simpa using pullback.condition (f := 𝟙 X) (g := 𝟙 X)
  simp only [chowCohomologyCap, BivariantClass.idRule_apply, pullbackSndPush,
    AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, chowGroupEquivOfIso_apply]
  rw [chowPushforwardOfIso_congr C _ _ _ _ hfs rfl (by rw [← hfs])]
  exact chowPushforwardOfIso_heq _ _ _ rfl (Category.id_comp sX).symm rfl HEq.rfl

variable {X X' : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **On a test scheme along which `ℰ` has constant rank `r`, `c_i(ℰ) ∩ -` is `c_i(f^*ℰ) ∩ -`
for `i ≤ r` and zero for `i > r`**, for the Chern class `c_i(ℰ)` of [Stacks, Tag 0ESW]. The test
morphism maps into the rank-`r` locus, on which `c_i(ℰ)` restricts to `c_i(ℰ|_{X_r})` of
[Stacks, Tag 0B7H] for `i ≤ r` and to zero for `i > r`. -/
theorem idRule_chernClassOfLocallyFree_of_rank (r i : ℕ) (f : X' ⟶ X) [LocallyOfFiniteType f]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) r] (k : ℤ) (α : chowGroup C (f ≫ sX) k) :
    (SectionZeroScheme.chernClassOfLocallyFree E C sX i).idRule C sX
        (gysinSystemOfInvertible C) f k α =
      if h : i ≤ r then
        GenuineChern.chernCap C r (f ≫ sX) ((Scheme.Modules.pullback f).obj E) k
          ⟨i, Nat.lt_succ_of_le h⟩ α
      else 0 := by
  set U := rankLocus E r with hU
  have hrange : Set.range f ⊆ Set.range U.ι := by
    rintro _ ⟨x', rfl⟩
    rw [Scheme.Opens.range_ι]
    exact SectionZeroScheme.mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback E f r x'
  set f' := IsOpenImmersion.lift U.ι f hrange with hf'def
  have hf' : f' ≫ U.ι = f := IsOpenImmersion.lift_fac U.ι f hrange
  have : LocallyOfFiniteType f' := by
    have : LocallyOfFiniteType (f' ≫ U.ι) := hf' ▸ inferInstance
    exact locallyOfFiniteType_of_comp f' U.ι
  clear_value f'
  subst hf'
  have hEU := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback U.ι).obj E)) r :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ r
  set β : chowGroup C (f' ≫ (U.ι ≫ sX)) k :=
    chowGroupCongr C (Category.assoc f' U.ι sX).symm k α with hβ
  have hβα : β ≍ α := chowGroupCongr_heq C _ k α
  have h2 := BivariantClass.idRule_chowCohomologyRestriction_heq U.ι
    (SectionZeroScheme.chernClassOfLocallyFree E C sX i) f' k β α hβα
  rw [SectionZeroScheme.chowCohomologyRestriction_chernClassOfLocallyFree E C sX r i U hU] at h2
  split_ifs at h2 ⊢ with h
  · rw [GenuineChern.idRule_chernClass] at h2
    refine eq_of_heq (h2.symm.trans ?_)
    refine (heq_of_eq (GenuineChern.chernCap_congr C (f' ≫ U.ι ≫ sX)
      (E := (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback U.ι).obj E))
      (E' := (Scheme.Modules.pullback (f' ≫ U.ι)).obj E) r
      ((Scheme.Modules.pullbackComp f' U.ι).app E) k ⟨i, Nat.lt_succ_of_le h⟩ β)).trans ?_
    exact SectionZeroScheme.chernCap_heq_of_base_eq C (Category.assoc f' U.ι sX).symm _ r k _ hβα
  · rw [BivariantClass.idRule_zero] at h2
    exact eq_of_heq (h2.symm.trans (zero_heq_zero_of_eq C (Category.assoc f' U.ι sX).symm _))

/-- **The cap product with the Chern class `c_i(ℰ)` of [Stacks, Tag 0ESW] of a module of constant
rank `r`** is the cap product `c_i(ℰ) ∩ -` of [Stacks, Tag 02U6] for `i ≤ r`, and zero for
`i > r`. -/
theorem chowCohomologyCap_chernClassOfLocallyFree_of_rank (r i : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ)
    (α : chowGroup C sX k) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sX (i : ℤ)
        (SectionZeroScheme.chernClassOfLocallyFree E C sX i) k α =
      if h : i ≤ r then GenuineChern.chernCap C r sX E k ⟨i, Nat.lt_succ_of_le h⟩ α else 0 := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (𝟙 X)).obj E) r :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ r
  refine eq_of_heq ((chowCohomologyCap_heq_idRule C sX _ k α).trans ?_)
  rw [idRule_chernClassOfLocallyFree_of_rank E C sX r i (𝟙 X) k]
  split_ifs with h
  · exact chernCap_heq_of_iso C (Category.id_comp sX) (F' := E) r
      ((Scheme.Modules.pullbackId X).app E) k _ (chowGroupCongr_heq C _ k α)
  · exact zero_heq_zero_of_eq C (Category.id_comp sX) _

end ArbitraryIndex

/-! ### Stacks 0FVN -/

variable (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ B.base.S)
  [LocallyOfFiniteType sX] (E : X.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]

/-- **[Stacks, Tag 0FVN] for `0 ≤ i ≤ r`.** Let `ℰ` be finite locally free of rank `r` on `X`,
with base change `ℰ'` on `X' = X ×_S S'`. Then `c_i(ℰ') ∩ g^*α = g^*(c_i(ℰ) ∩ α)` in
`CH_{k+c-i}(X')` for every `α ∈ CH_k(X)` and every `0 ≤ i ≤ r`. -/
theorem baseChange_chernCap (k : ℤ) (i : Fin (r + 1)) (α : chowGroup B.base sX k) :
    haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.fst sX B.g) E r
    GenuineChern.chernCap B.baseChange r (pullback.snd sX B.g)
        ((Scheme.Modules.pullback (pullback.fst sX B.g)).obj E) (k + B.c) i
        (baseChangeChowPullback B sX k α) =
      chowGroupCast B.baseChange (pullback.snd sX B.g)
        (show k - (i : ℤ) + B.c = k + B.c - (i : ℤ) from by omega)
        (baseChangeChowPullback B sX (k - (i : ℤ))
          (GenuineChern.chernCap B.base r sX E k i α)) :=
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.fst sX B.g) E r
  baseChange_chernCap_of_iso B sX E r _ (Iso.refl _) k i α

/-- **[Stacks, Tag 0FVN].** Let `g : S' ⟶ S` be a flat base change of Chow situations with
dimension shift `c` ([Stacks, Tag 0FVG]), let `X` be locally of finite type over `S` with base
change `X' = X ×_S S'`, and let `ℰ` be a finite locally free `𝒪_X`-module of rank `r` with base
change `ℰ'` on `X'`. Then for every `i` the square

  `CH_k(X)     --g^*--> CH_{k+c}(X')`
  `    |c_i(ℰ) ∩ -              |c_i(ℰ') ∩ -`
  `CH_{k-i}(X) --g^*--> CH_{k+c-i}(X')`

commutes, where `c_i ∈ A^i` is the Chern class of [Stacks, Tag 0ESW], built from the classes of
[Stacks, Tag 0B7H] (zero for `i > r`), and `g^*` is the map of [Stacks, Tag 0FVJ]. For `i ≤ r`
the cap products are those of [Stacks, Tag 02U6] (`Stacks.Chow.baseChange_chernCap`). -/
@[stacks 0FVN]
theorem baseChange_chowCohomologyCap_chernClassOfLocallyFree (i : ℕ) (k : ℤ)
    (α : chowGroup B.base sX k) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.fst sX B.g) E r
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      ((Scheme.Modules.pullback (pullback.fst sX B.g)).obj E) r
    chowCohomologyCap B.baseChange (gysinSystemOfInvertible B.baseChange) (pullback.snd sX B.g)
        (i : ℤ)
        (SectionZeroScheme.chernClassOfLocallyFree
          ((Scheme.Modules.pullback (pullback.fst sX B.g)).obj E) B.baseChange
          (pullback.snd sX B.g) i) (k + B.c) (baseChangeChowPullback B sX k α) =
      chowGroupCast B.baseChange (pullback.snd sX B.g)
        (show k - (i : ℤ) + B.c = k + B.c - (i : ℤ) from by omega)
        (baseChangeChowPullback B sX (k - (i : ℤ))
          (chowCohomologyCap B.base (gysinSystemOfInvertible B.base) sX (i : ℤ)
            (SectionZeroScheme.chernClassOfLocallyFree E B.base sX i) k α)) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.fst sX B.g) E r
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    ((Scheme.Modules.pullback (pullback.fst sX B.g)).obj E) r
  rw [chowCohomologyCap_chernClassOfLocallyFree_of_rank _ _ _ r i,
    chowCohomologyCap_chernClassOfLocallyFree_of_rank _ _ _ r i]
  split_ifs with h
  · exact baseChange_chernCap B sX E r k ⟨i, Nat.lt_succ_of_le h⟩ α
  · rw [map_zero, map_zero]

end Stacks.Chow

end
