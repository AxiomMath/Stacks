module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernProductVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.LocallyFreeRemark
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleRankOne
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FormulaOfRank
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaModulesEquivalence
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite

/-!
# A module whose Chern classes are nonzero in infinitely many degrees

Stacks 0ESW observes that for a finite locally free module `ℰ` of non-constant rank it may happen
that `c_p(ℰ) ≠ 0` for infinitely many `p`. This file gives an example: over a field `k`, with
`δ = 0`, let `X = ∐_{n ≥ 0} 𝐏^{n+1}_k` and let `ℰ` be `𝒪(1)^{⊕ (n+1)}` on the summand
`𝐏^{n+1}_k`. Then `c_{n+1}(ℰ) ≠ 0` for every `n`.

On `𝐏^{n+1}_k` the Whitney sum formula gives `c_{n+1}(𝒪(1)^{⊕ (n+1)}) ∩ - = c₁(𝒪(1))^{n+1} ∩ -`
(`Stacks.Chow.chernCap_twistSum_last`), and `c₁(𝒪(1))^{n+1} ∩ π^*[Spec k] ≠ 0` because the map
of the projective bundle formula, Stacks 02TX, is injective and `[Spec k] ≠ 0` in
`A_0(Spec k) ≅ 𝐙`.

## Main results

* `Stacks.Chow.chernCap_twistSum_last` — `c_{n+1}(ℒ^{⊕ (n+1)}) ∩ - = c₁(ℒ)^{n+1} ∩ -` for an
  invertible module `ℒ`.
* `Stacks.Chow.exists_capPow_bundleTwist_ne_zero` — `c₁(𝒪(1))^{n+1} ∩ π^*[Spec k] ≠ 0` on
  `𝐏^{n+1}_k`.
* `Stacks.Chow.exists_infinite_chernClassOfLocallyFree_ne_zero` — **Stacks 0ESW**: there are a
  base situation, a scheme `X` locally of finite type over it and a finite locally free module
  `ℰ` on `X` with `c_p(ℰ) ≠ 0` for infinitely many `p`.

## References

* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The Chern classes of a sum of copies of an invertible module -/

section TwistSum

variable {P : Scheme.{u}} (L : P.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]

/-- The direct sum `ℒ^{⊕ (n+1)}` of `n + 1` copies of a module `ℒ`. -/
def twistSum : ℕ → P.Modules
  | 0 => L
  | n + 1 => twistSum n ⊞ L

/-- The split short exact sequence `0 ⟶ ℒ^{⊕ (n+1)} ⟶ ℒ^{⊕ (n+2)} ⟶ ℒ ⟶ 0`. -/
def twistSumShortComplex (n : ℕ) : ShortComplex P.Modules :=
  ShortComplex.mk (biprod.inl : twistSum L n ⟶ twistSum L n ⊞ L) (biprod.snd : _ ⟶ L) (by simp)

omit hL in
/-- The sequence `0 ⟶ ℒ^{⊕ (n+1)} ⟶ ℒ^{⊕ (n+2)} ⟶ ℒ ⟶ 0` is short exact. -/
theorem twistSumShortComplex_shortExact (n : ℕ) : (twistSumShortComplex L n).ShortExact :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact

/-- `ℒ^{⊕ (n+1)}` is finite locally free of rank `n + 1`. -/
theorem isFiniteLocallyFreeOfRank_twistSum : ∀ n : ℕ,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (twistSum L n) (n + 1)
  | 0 => hL
  | n + 1 => GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact (twistSumShortComplex L n)
      (twistSumShortComplex_shortExact L n) (n + 1) 1 (isFiniteLocallyFreeOfRank_twistSum n) hL

variable (C : ChowSituation.{u}) (sP : P ⟶ C.S) [LocallyOfFiniteType sP]

/-- **Stacks 02UI for `ℒ^{⊕ (n+2)} = ℒ^{⊕ (n+1)} ⊕ ℒ`**, on the Chern class cap products. -/
theorem chernFamily_twistSum_succ (n : ℕ) :
    haveI := isFiniteLocallyFreeOfRank_twistSum L n
    haveI := isFiniteLocallyFreeOfRank_twistSum L (n + 1)
    GenuineChern.chernFamily C sP (twistSum L (n + 1)) (n + 2) =
      GenuineChern.chernFamily C sP (twistSum L n) (n + 1) * GenuineChern.chernFamily C sP L 1 := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (twistSumShortComplex L n).X₁ (n + 1) := isFiniteLocallyFreeOfRank_twistSum L n
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (twistSumShortComplex L n).X₃ 1 := hL
  exact GenuineChern.chernFamily_eq_mul_of_shortExact C sP (twistSumShortComplex L n)
    (twistSumShortComplex_shortExact L n) (n + 1) 1

/-- **The top Chern class of `ℒ^{⊕ (n+1)}` is `c₁(ℒ)^{n+1}`**, on the Chern class cap products:
`c_{n+1}(ℒ^{⊕ (n+1)}) ∩ α = c₁(ℒ)^{n+1} ∩ α`, by the Whitney sum formula. -/
theorem chernCap_twistSum_last (n : ℕ) :
    ∀ (k : ℤ) (x : chowGroup C sP k),
      haveI := isFiniteLocallyFreeOfRank_twistSum L n
      haveI := GenuineChern.isInvertible_of_rank_one L
      GenuineChern.chernCap C (n + 1) sP (twistSum L n) k (Fin.last (n + 1)) x ≍
        capPow C sP (invCap C sP L) (n + 1) k (k - ((n + 1 : ℕ) : ℤ)) (by ring) x := by
  have := GenuineChern.isInvertible_of_rank_one L
  induction n with
  | zero =>
    intro k x
    change GenuineChern.chernCap C 1 sP L k 1 x ≍ _
    rw [GenuineChern.chernCap_one_eq_invCap, capPow_succ_apply, capPow_zero_apply]
    exact (chowGroupCast_heq C sP _ _).symm
  | succ n ih =>
    intro k x
    have := isFiniteLocallyFreeOfRank_twistSum L n
    have := isFiniteLocallyFreeOfRank_twistSum L (n + 1)
    set A := GenuineChern.chernFamily C sP (twistSum L n) (n + 1)
    set B := GenuineChern.chernFamily C sP L 1
    have hfam := chernFamily_twistSum_succ L C sP n
    have h1 : GenuineChern.chernCap C (n + 1 + 1) sP (twistSum L (n + 1)) k (Fin.last (n + 1 + 1))
        x = (A * B) k (n + 2) x := by
      rw [← hfam]
      change _ = chernCapFamilyOnChow C (GenuineChern.chernCap C) sP (twistSum L (n + 1)) (n + 2)
        k (n + 2) x
      rw [chernCapFamilyOnChow_of_le C _ sP _ _ k le_rfl]
      rfl
    rw [h1, gradedCap_mul_apply, Finset.sum_eq_single 1]
    · rw [convolveTerm_of_le _ _ _ (by omega), capTo_def]
      refine (gradedDegreeCast_heq _ _).trans ?_
      have hB : B k 1 x = (invCap C sP L).capOnChow C sP (k - 1)
          (chowGroupCast C sP (by omega) x) := by
        change chernCapFamilyOnChow C (GenuineChern.chernCap C) sP L 1 k 1 x = _
        rw [chernCapFamilyOnChow_of_le C _ sP _ _ k le_rfl]
        exact GenuineChern.chernCap_one_eq_invCap C sP L k x
      have hA : A (k - ((1 : ℕ) : ℤ)) (n + 2 - 1) = GenuineChern.chernCap C (n + 1) sP
          (twistSum L n) (k - ((1 : ℕ) : ℤ)) (Fin.last (n + 1)) := by
        change chernCapFamilyOnChow C (GenuineChern.chernCap C) sP (twistSum L n) (n + 1) _
          (n + 2 - 1) = _
        rw [chernCapFamilyOnChow_of_le C _ sP _ _ _ (by omega)]
        rfl
      rw [hA, hB]
      refine (ih _ _).trans ?_
      refine HEq.trans ?_ (heq_of_eq (capPow_succ_apply C sP (invCap C sP L) (n + 1) k _
        (by push_cast; ring) x)).symm
      exact GenuineChern.capPow_heq C sP _ _ _ rfl (by push_cast; ring) (by push_cast; ring)
        (capOnChow_heq C sP _ (by ring)
          ((chowGroupCast_heq C sP _ _).trans (chowGroupCast_heq C sP _ _).symm))
    · intro j hj hj1
      have hjm : j ≤ n + 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [convolveTerm_of_le _ _ _ hjm, capTo_def]
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · have hA0 : A (k - ((0 : ℕ) : ℤ)) (n + 2 - 0) = 0 := by
          change chernCapFamilyOnChow C (GenuineChern.chernCap C) sP (twistSum L n) (n + 1) _
            (n + 2 - 0) = 0
          exact chernCapFamilyOnChow_of_gt C _ sP _ _ _ (by omega)
        rw [hA0, AddMonoidHom.zero_apply, map_zero]
      · have hBj : B k j = 0 := by
          change chernCapFamilyOnChow C (GenuineChern.chernCap C) sP L 1 k j = 0
          exact chernCapFamilyOnChow_of_gt C _ sP _ _ _ (by omega)
        rw [hBj, AddMonoidHom.zero_apply, map_zero, map_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h

end TwistSum

/-! ### The power `c₁(𝒪(1))^{n+1}` on the projective space `𝐏^{n+1}` is nonzero -/

section ProjectiveSpace

variable (C : ChowSituation.{u})

/-- A nonzero Chow class stays nonzero under a heterogeneous equality to a class in an equal
degree. -/
theorem ne_zero_of_heq {T : Scheme.{u}} {q : T ⟶ C.S} [LocallyOfFiniteType q] {a b : ℤ}
    (h : a = b) {x : chowGroup C q a} {y : chowGroup C q b} (hxy : x ≍ y) (hx : x ≠ 0) :
    y ≠ 0 := by
  subst h
  cases hxy
  exact hx

/-- The cap operator `c₁(𝒪(1)) ∩ -` of the projective bundle is the first Chern class cap operator
of the invertible module `𝒪(1)`. -/
theorem bundleTwistCap_eq_invCap {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] :
    bundleTwistCap E C sX = invCap C (bundleProj E ≫ sX) (bundleTwist E) :=
  rfl

variable (hδ : ∀ s : C.S, C.dimensionFunction s = 0) [Subsingleton C.S]
  (F : C.S.Modules) (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 2)]

include hδ in
/-- **`c₁(𝒪(1))^{n+1} ∩ π^*[S] ≠ 0` on `𝐏(ℱ) = 𝐏^{n+1}_S`** for `ℱ` of rank `n + 2` on a
one-point base with vanishing dimension function: the map of the projective bundle formula,
Stacks 02TX, is injective and the fundamental class of the base is nonzero in `A_0(S) ≅ 𝐙`. -/
theorem exists_capPow_bundleTwistCap_ne_zero (s : C.S) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F (n + 2)
    ∃ (a : ℤ) (α : chowGroup C (bundleProj F ≫ 𝟙 C.S) a),
      capPow C (bundleProj F ≫ 𝟙 C.S) (bundleTwistCap F C (𝟙 C.S)) (n + 1) a
        (a - ((n + 1 : ℕ) : ℤ)) (by ring) α ≠ 0 := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F (n + 2)
  classical
  obtain ⟨pt, hpt⟩ : ∃ pt : chowGroup C (𝟙 C.S) 0, pt ≠ 0 := by
    refine ⟨(chowGroupBaseEquivInt C hδ s).symm 1, fun h ↦ ?_⟩
    have h' := congrArg (chowGroupBaseEquivInt C hδ s) h
    rw [AddEquiv.apply_symm_apply, map_zero] at h'
    exact one_ne_zero h'
  have hdeg : (0 : ℤ) = -((n + 1 : ℕ) : ℤ) + (((Fin.last (n + 1) : Fin (n + 2)) : ℕ) : ℤ) := by
    rw [Fin.val_last]
    ring
  obtain ⟨β, hβi, hβj⟩ :
      ∃ β : ∀ j : Fin (n + 2), chowGroup C (𝟙 C.S) (-((n + 1 : ℕ) : ℤ) + ((j : ℕ) : ℤ)),
      β (Fin.last (n + 1)) = chowGroupCast C (𝟙 C.S) hdeg pt ∧
        ∀ j, j ≠ Fin.last (n + 1) → β j = 0 :=
    ⟨Pi.single (Fin.last (n + 1)) (chowGroupCast C (𝟙 C.S) hdeg pt), Pi.single_eq_same _ _,
      fun j hj ↦ Pi.single_eq_of_ne hj _⟩
  have hβ : β ≠ 0 := by
    intro h
    have h' := congrFun h (Fin.last (n + 1))
    rw [hβi, Pi.zero_apply] at h'
    exact hpt ((AddEquiv.map_eq_zero_iff _).1 h')
  have hmap := (injective_iff_map_eq_zero _).1
    (bijective_projectiveBundleFormulaMap F (n + 2) C (𝟙 C.S) (-((n + 1 : ℕ) : ℤ))).1
  have hne : projectiveBundleFormulaMap F (n + 2) C (𝟙 C.S) (-((n + 1 : ℕ) : ℤ)) β ≠ 0 :=
    fun h ↦ hβ (hmap β h)
  have hsum : ∑ j : Fin (n + 2),
      projectiveBundleFormulaTerm F (n + 2) C (𝟙 C.S) (-((n + 1 : ℕ) : ℤ)) j (β j) =
        projectiveBundleFormulaTerm F (n + 2) C (𝟙 C.S) (-((n + 1 : ℕ) : ℤ)) (Fin.last (n + 1))
          (β (Fin.last (n + 1))) :=
    Finset.sum_eq_single _ (fun j _ hj ↦ (congrArg _ (hβj j hj)).trans (map_zero _))
      (fun h ↦ absurd (Finset.mem_univ _) h)
  rw [projectiveBundleFormulaMap_apply, hsum] at hne
  let := flat_bundleProj_ofRank F (n + 2)
  let := locallyOfFiniteType_bundleProj_ofRank F (n + 2)
  have hterm : projectiveBundleFormulaTerm F (n + 2) C (𝟙 C.S) (-((n + 1 : ℕ) : ℤ))
      (Fin.last (n + 1)) (β (Fin.last (n + 1))) =
      capPow C (bundleProj F ≫ 𝟙 C.S) (bundleTwistCap F C (𝟙 C.S))
        ((Fin.last (n + 1) : Fin (n + 2)) : ℕ)
        (-((n + 1 : ℕ) : ℤ) + (((Fin.last (n + 1) : Fin (n + 2)) : ℕ) : ℤ) + ((n + 2 - 1 : ℕ) : ℤ))
        (-((n + 1 : ℕ) : ℤ) + ((n + 2 : ℕ) : ℤ) - 1) (by rw [Fin.val_last]; push_cast; ring)
        (bundlePullback C (𝟙 C.S) (bundleProj F ≫ 𝟙 C.S) (bundleProj F) rfl (n + 2 - 1)
          (relativeDimension_bundleProj_ofRank F (n + 2))
          (-((n + 1 : ℕ) : ℤ) + (((Fin.last (n + 1) : Fin (n + 2)) : ℕ) : ℤ))
          (β (Fin.last (n + 1)))) :=
    rfl
  rw [hterm] at hne
  refine ⟨-((n + 1 : ℕ) : ℤ) + (((Fin.last (n + 1) : Fin (n + 2)) : ℕ) : ℤ) +
    ((n + 2 - 1 : ℕ) : ℤ),
    bundlePullback C (𝟙 C.S) (bundleProj F ≫ 𝟙 C.S) (bundleProj F) rfl (n + 2 - 1)
      (relativeDimension_bundleProj_ofRank F (n + 2))
      (-((n + 1 : ℕ) : ℤ) + (((Fin.last (n + 1) : Fin (n + 2)) : ℕ) : ℤ))
      (β (Fin.last (n + 1))), ne_zero_of_heq C ?_ ?_ hne⟩
  · rw [Fin.val_last]
    push_cast
    ring
  · exact GenuineChern.capPow_heq C _ _ _ _ (Fin.val_last _) rfl
      (by rw [Fin.val_last]; push_cast; ring) HEq.rfl

end ProjectiveSpace

/-! ### The example -/

section Example

/-- A Chow class vanishing heterogeneously equal to the zero class in an equal degree, for equal
structure morphisms. -/
theorem eq_zero_of_zero_heq (C : ChowSituation.{u}) {T : Scheme.{u}} {q q' : T ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q') {a b : ℤ} (h : a = b)
    {y : chowGroup C q' b} (hy : (0 : chowGroup C q a) ≍ y) : y = 0 := by
  subst hq h
  exact (eq_of_heq hy).symm

variable (C : ChowSituation.{u})

/-- The free module `𝒪^{n+2}` on the base. -/
abbrev baseFree (n : ℕ) : C.S.Modules := Scheme.Modules.free C.S (ULift.{u} (Fin (n + 2)))

/-- The free module `𝒪^{n+2}` is finite locally free of rank `n + 2`. -/
instance isFiniteLocallyFreeOfRank_baseFree (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (baseFree C n) (n + 2) :=
  isFiniteLocallyFreeOfRank_free (ULift.{u} (Fin (n + 2))) (n + 2) Equiv.ulift

/-- The free module `𝒪^{n+2}` is finite locally free. -/
instance isFiniteLocallyFree_baseFree (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (baseFree C n) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (n + 2)

/-- The twisting module `𝒪(1)` on `𝐏(𝒪^{n+2})` is finite locally free of rank `1`. -/
instance isFiniteLocallyFreeOfRank_bundleTwist_baseFree (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (bundleTwist (baseFree C n)) 1 :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible _
    (isInvertible_bundleTwist (baseFree C n))

/-- The projective spaces `𝐏^{n+1}_S = 𝐏(𝒪^{n+2})`, indexed in the universe of the schemes. -/
abbrev baseProjectiveSpace (n : ULift.{u} ℕ) : Scheme.{u} := bundle (baseFree C n.down)

/-- The structure morphism `𝐏^{n+1}_S ⟶ S`. -/
abbrev baseProjectiveSpaceStructure (n : ULift.{u} ℕ) : baseProjectiveSpace C n ⟶ C.S :=
  bundleProj (baseFree C n.down) ≫ 𝟙 C.S

/-- The structure morphism `𝐏^{n+1}_S ⟶ S` is locally of finite type. -/
instance locallyOfFiniteType_baseProjectiveSpaceStructure (n : ULift.{u} ℕ) :
    LocallyOfFiniteType (baseProjectiveSpaceStructure C n) :=
  locallyOfFiniteType_bundleProj_comp (baseFree C n.down) C (𝟙 C.S)

/-- The module `𝒪(1)^{⊕ (n+1)}` on `𝐏^{n+1}_S`. -/
abbrev baseTwistSum (n : ULift.{u} ℕ) : (baseProjectiveSpace C n).Modules :=
  twistSum (bundleTwist (baseFree C n.down)) n.down

/-- The module `𝒪(1)^{⊕ (n+1)}` on `𝐏^{n+1}_S` is finite locally free of rank `n + 1`. -/
instance isFiniteLocallyFreeOfRank_baseTwistSum (n : ULift.{u} ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (baseTwistSum C n)
      (n.down + 1) :=
  isFiniteLocallyFreeOfRank_twistSum _ n.down

/-- The morphism `∐_{n ≥ 0} 𝐏^{n+1}_S ⟶ S` induced by the structure morphisms is locally of finite
type. -/
instance locallyOfFiniteType_sigmaDesc_baseProjectiveSpaceStructure :
    LocallyOfFiniteType (Sigma.desc (baseProjectiveSpaceStructure C)) :=
  letI : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) inferInstance

/-- **The Chern classes of a module of non-constant rank can be nonzero in infinitely many
degrees.** Over a one-point base `S` with vanishing dimension function (for instance the spectrum
of a field with `δ = 0`), on `X = ∐_{n ≥ 0} 𝐏^{n+1}_S` with `ℰ = 𝒪(1)^{⊕ (n+1)}` on the summand
`𝐏^{n+1}_S`, one has `c_{n+1}(ℰ) ≠ 0` for every `n`. -/
theorem exists_infinite_chernClassOfLocallyFree_ne_zero_of_subsingleton
    (hδ : ∀ s : C.S, C.dimensionFunction s = 0) [Subsingleton C.S] (s : C.S) :
    ∃ (X : Scheme.{u}) (sX : X ⟶ C.S) (_ : LocallyOfFiniteType sX)
      (E : X.Modules) (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E),
      {p : ℕ | SectionZeroScheme.chernClassOfLocallyFree E C sX p ≠ 0}.Infinite := by
  obtain ⟨E, he⟩ := exists_restrict_iso_of_summandModules (baseProjectiveSpace C) (baseTwistSum C)
  have hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E := by
    refine (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators E).1
      (Stacks.Modules.isFiniteLocallyFree_of_openCover E
        (sigmaOpenCover (baseProjectiveSpace C)) fun n ↦ ?_)
    have := isFiniteLocallyFreeOfRank_baseTwistSum C n
    exact Stacks.Modules.isFiniteLocallyFree_of_iso
      (((Scheme.Modules.restrictFunctorIsoPullback
        (Sigma.ι (baseProjectiveSpace C) n)).app E) ≪≫ (he n).some).symm
      ((Stacks.Modules.isFiniteLocallyFree_iff_localGenerators _).2
        (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
          (baseTwistSum C n) (n.down + 1)))
  refine ⟨_, Sigma.desc (baseProjectiveSpaceStructure C), inferInstance, E, hE,
    Set.infinite_of_injective_forall_mem Nat.succ_injective fun n ↦ ?_⟩
  change SectionZeroScheme.chernClassOfLocallyFree E C
    (Sigma.desc (baseProjectiveSpaceStructure C)) (n + 1) ≠ 0
  intro h0
  have hι : Sigma.ι (baseProjectiveSpace C) (ULift.up n) ≫
      Sigma.desc (baseProjectiveSpaceStructure C) = baseProjectiveSpaceStructure C (ULift.up n) :=
    Sigma.ι_comp_desc _ _
  have : LocallyOfFiniteType (Sigma.ι (baseProjectiveSpace C) (ULift.up n)) := by
    have : LocallyOfFiniteType (Sigma.ι (baseProjectiveSpace C) (ULift.up n) ≫
        Sigma.desc (baseProjectiveSpaceStructure C)) := by
      rw [hι]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (Sigma.desc (baseProjectiveSpaceStructure C))
  have hEι : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (Sigma.ι (baseProjectiveSpace C) (ULift.up n))).obj E) (n + 1) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (he (ULift.up n)).some.symm (isFiniteLocallyFreeOfRank_baseTwistSum C (ULift.up n))
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (baseTwistSum C (ULift.up n)) (n + 1) := isFiniteLocallyFreeOfRank_baseTwistSum C (ULift.up n)
  obtain ⟨a, α, hα⟩ := exists_capPow_bundleTwistCap_ne_zero C hδ (baseFree C n) n s
  have h1 := SectionZeroScheme.idRule_chernClassOfLocallyFree_of_rank C
    (Sigma.desc (baseProjectiveSpaceStructure C)) E (n + 1) (n + 1)
    (Sigma.ι (baseProjectiveSpace C) (ULift.up n)) a (chowGroupCongr C hι.symm a α)
  rw [h0, BivariantClass.idRule_zero, dite_eq_left le_rfl,
    GenuineChern.chernCap_congr C _ (n + 1) (he (ULift.up n)).some] at h1
  have h2 := SectionZeroScheme.chernCap_heq_of_base_eq C hι (baseTwistSum C (ULift.up n)) (n + 1)
    a (Fin.last (n + 1)) (chowGroupCongr_heq C hι.symm a α)
  have h3 := chernCap_twistSum_last (bundleTwist (baseFree C n)) C
    (baseProjectiveSpaceStructure C (ULift.up n)) n a α
  have h12 := (heq_of_eq h1).trans h2
  have h4 := h12.trans h3
  have h5 := eq_zero_of_zero_heq C hι rfl h4
  rw [bundleTwistCap_eq_invCap] at hα
  exact hα h5

/-- **The example over a field.** For a field `k`, with `δ = 0`, there are a scheme `X` locally
of finite type over `Spec k` and a finite locally free `𝒪_X`-module `ℰ` with `c_p(ℰ) ≠ 0` for
infinitely many `p`. -/
theorem exists_infinite_chernClassOfLocallyFree_ne_zero_of_field (k : Type u) [Field k] :
    ∃ (X : Scheme.{u}) (sX : X ⟶ (fieldChowSituation k).S) (_ : LocallyOfFiniteType sX)
      (E : X.Modules) (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E),
      {p : ℕ | SectionZeroScheme.chernClassOfLocallyFree E (fieldChowSituation k) sX p ≠
        0}.Infinite :=
  have : Subsingleton (fieldChowSituation k).S := inferInstanceAs (Subsingleton (Spec (.of k)))
  exists_infinite_chernClassOfLocallyFree_ne_zero_of_subsingleton (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction k) (default : Spec (.of k))

/-- **The Chern classes of a module of non-constant rank can be nonzero in infinitely many
degrees.** There are a base situation `(S, δ)` of chapter 42, a scheme `X`
locally of finite type over `S` and a finite locally free `𝒪_X`-module `ℰ` such that
`c_p(ℰ) ≠ 0` for infinitely many `p`. -/
@[stacks 0ESW "it may happen that c_p(E) is nonzero for infinitely many p"]
theorem exists_infinite_chernClassOfLocallyFree_ne_zero :
    ∃ (C : ChowSituation.{u}) (X : Scheme.{u}) (sX : X ⟶ C.S) (_ : LocallyOfFiniteType sX)
      (E : X.Modules) (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E),
      {p : ℕ | SectionZeroScheme.chernClassOfLocallyFree E C sX p ≠ 0}.Infinite :=
  ⟨_, exists_infinite_chernClassOfLocallyFree_ne_zero_of_field (ULift.{u} ℚ)⟩

end Example

end Stacks.Chow

end
