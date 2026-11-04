module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSumChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumComplex
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.MappingConeChern

/-!
# The Chern classes of a direct sum of perfect objects

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E`, `F` be objects of `D(𝒪_X)` whose Chern classes are defined
(Stacks 0F9E (1)). This file proves the case of Stacks 0F9F for the split distinguished triangle
`E ⟶ E ⊕ F ⟶ F ⟶ E[1]`: the Chern classes of `E ⊕ F` are defined and `c(E ⊕ F) = c(E) c(F)`.

The proof follows the source. Choose envelope presentations `(f : Y ⟶ X, 𝓔^•)` of `E` and
`(f' : Y' ⟶ X, 𝓕^•)` of `F`. The morphism `Y ×_X Y' ⟶ X` is an envelope (Stacks 0GU6, 0GU7),
and the termwise biproduct of the pullbacks of `𝓔^•` and `𝓕^•` to `Y ×_X Y'` is a locally bounded
complex of finite locally free modules representing the derived pullback of `E ⊕ F`, derived
pullback being a left adjoint. Its total Chern class is the product of those of the two pulled
back complexes: on a piece of `Y ×_X Y'` on which both complexes have constant ranks this is the
multiplicativity of Stacks 02UI, term by term, and the total Chern classes of finite locally free
modules commute with each other. Restriction along the envelope being injective, the formula
descends to `X`. The same reduction gives the additivity of the power sums of complexes, which
the power sum half of Stacks 0F9F uses.

## Main definitions

* `Stacks.Chow.derivedPullbackBiprodIso` — `Lf^*(E ⊕ F) ≅ Lf^*E ⊕ Lf^*F`.
* `Stacks.Chow.EnvelopePresentation.biprod` — the direct sum of two envelope presentations.

## Main results

* `Stacks.Chow.isLocallyBoundedFiniteLocallyFree_biprod` — the termwise biproduct of two locally
  bounded complexes of finite locally free modules is one.
* `Stacks.Chow.complexChern_biprod` — `c(𝓔^• ⊕ 𝓕^•) = c(𝓔^•) c(𝓕^•)`.
* `Stacks.Chow.powerSumComplex_biprod` — `P_p(𝓔^• ⊕ 𝓕^•) = P_p(𝓔^•) + P_p(𝓕^•)`.
* `Stacks.Chow.hasDefinedChernClasses_biprod` — Stacks 0F9F, the direct-sum case: the Chern
  classes of `E ⊕ F` are defined.
* `Stacks.Chow.perfectChernClass_biprod` — Stacks 0F9F, the direct-sum case:
  `c(E ⊕ F) = c(E) c(F)`.

## Implementation notes

The ring of total classes is not known to be commutative, so the product of the bounded case is
rearranged with `Stacks.Chow.list_prod_map_mul_of_commute`, which only needs every factor of one
complex to commute with every factor of the other (`Stacks.Chow.totalChern_commute`).

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Ordered products of termwise products -/

/-! ### Modules -/

section Module

variable {Y : Scheme.{u}}

/-- A biproduct of finite locally free modules of ranks `r` and `s` is finite locally free of
rank `r + s`. -/
theorem isFiniteLocallyFreeOfRank_biprod (F G : Y.Modules) (r s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G s] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F ⊞ G : Y.Modules)
      (r + s) :=
  GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
    (ShortComplex.mk (biprod.inl : F ⟶ F ⊞ G) (biprod.snd : F ⊞ G ⟶ G) (by simp))
    (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact r s ‹_› ‹_›

variable (C : ChowSituation.{u}) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **The power sums of a direct sum** are the sums of the power sums:
`P_p(ℰ ⊕ ℱ) = P_p(ℰ) + P_p(ℱ)`, the split case of Stacks 0F9C. -/
theorem powerSumTotal_biprod (F G : Y.Modules) (r s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G s] (p : ℕ) :
    haveI := isFiniteLocallyFreeOfRank_biprod F G r s
    powerSumTotal C sY (F ⊞ G : Y.Modules) (r + s) p =
      powerSumTotal C sY F r p + powerSumTotal C sY G s p :=
  powerSumTotal_eq_add_of_shortExact C sY
    (ShortComplex.mk (biprod.inl : F ⟶ F ⊞ G) (biprod.snd : F ⊞ G ⟶ G) (by simp))
    (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact r s p

end Module

/-! ### Bounded complexes of constant ranks -/

section Bounded

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  {P Q R : CochainComplex Y.Modules ℤ} (e : ∀ n, R.X n ≅ (P.X n ⊞ Q.X n : Y.Modules))

include e

/-- The factor `c(R^n)^{(-1)^n}` of a complex whose terms are the biproducts of the terms of two
complexes `P` and `Q` is the product of the factors of `P` and of `Q`. -/
theorem complexChernFactor_eq_mul_of_iso_biprod (ρ σ τ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hQ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Q.X n) (σ n))
    (hR : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R.X n) (τ n))
    (hτ : ∀ n, τ n = ρ n + σ n) (n : ℤ) :
    complexChernFactor C sY R τ hR n =
      complexChernFactor C sY P ρ hP n * complexChernFactor C sY Q σ hQ n := by
  let := hP n
  let := hQ n
  let := hR n
  have := isFiniteLocallyFreeOfRank_biprod (P.X n) (Q.X n) (ρ n) (σ n)
  have hc : Commute (totalChernUnit C sY (P.X n) (ρ n)) (totalChernUnit C sY (Q.X n) (σ n)) :=
    Commute.units_val_iff.mp (totalChern_commute C sY (P.X n) (Q.X n) (ρ n) (σ n))
  have hu : totalChernUnit C sY (R.X n) (τ n) =
      totalChernUnit C sY (P.X n) (ρ n) * totalChernUnit C sY (Q.X n) (σ n) :=
    Units.ext ((totalChern_congr C sY (e n) (hτ n)).trans
      (totalChern_biprod C sY (P.X n) (Q.X n) (ρ n) (σ n)))
  rw [complexChernFactor, complexChernFactor, complexChernFactor, hu, hc.mul_zpow]

/-- The ranks of the terms of `R` are the sums of the ranks of the terms of `P` and `Q`, when `R`
is termwise isomorphic to `P ⊞ Q` and `Y` has a point. -/
private theorem rank_eq_add_of_iso_biprod (ρ σ τ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hQ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Q.X n) (σ n))
    (hR : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R.X n) (τ n))
    (y : Y) : ∀ n, τ n = ρ n + σ n := fun n ↦
  let := hP n
  let := hQ n
  Scheme.Modules.isFiniteLocallyFreeOfRank_unique (R.X n) (hR n)
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (e n).symm
      (isFiniteLocallyFreeOfRank_biprod (P.X n) (Q.X n) (ρ n) (σ n))) y

/-- **The total Chern class of a termwise biproduct of bounded complexes of constant ranks** is
the product of the total Chern classes. -/
theorem complexChernBounded_eq_mul_of_iso_biprod (ρ σ τ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hQ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Q.X n) (σ n))
    (hR : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R.X n) (τ n)) :
    complexChernBounded C sY R τ hR =
      complexChernBounded C sY P ρ hP * complexChernBounded C sY Q σ hQ := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty sY).elim _ _
  have hτ := rank_eq_add_of_iso_biprod e ρ σ τ hP hQ hR y
  have hs₁ : ∀ n ∉ ρ.support ∪ σ.support, ρ n = 0 := fun n hn ↦
    Finsupp.notMem_support_iff.1 fun h ↦ hn (Finset.mem_union_left _ h)
  have hs₂ : ∀ n ∉ ρ.support ∪ σ.support, σ n = 0 := fun n hn ↦
    Finsupp.notMem_support_iff.1 fun h ↦ hn (Finset.mem_union_right _ h)
  rw [complexChernBounded_eq_prod C sY R τ hR (ρ.support ∪ σ.support)
      (fun n hn ↦ by rw [hτ, hs₁ n hn, hs₂ n hn]),
    complexChernBounded_eq_prod C sY P ρ hP _ hs₁, complexChernBounded_eq_prod C sY Q σ hQ _ hs₂,
    ← Units.val_mul, complexChernProd, complexChernProd, complexChernProd]
  congr 1
  rw [← list_prod_map_mul_of_commute]
  · congr 1
    exact List.map_congr_left fun n _ ↦
      complexChernFactor_eq_mul_of_iso_biprod C sY e ρ σ τ hP hQ hR hτ n
  · intro n _ m _
    let := hP m
    let := hQ n
    have hc : Commute (totalChernUnit C sY (Q.X n) (σ n)) (totalChernUnit C sY (P.X m) (ρ m)) :=
      Commute.units_val_iff.mp (totalChern_commute C sY (Q.X n) (P.X m) (σ n) (ρ m))
    exact hc.zpow_zpow _ _

/-- **The power sums of a termwise biproduct of bounded complexes of constant ranks** are the
sums of the power sums. -/
theorem powerSumComplexBounded_eq_add_of_iso_biprod (ρ σ τ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hQ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Q.X n) (σ n))
    (hR : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R.X n) (τ n))
    (p : ℕ) :
    powerSumComplexBounded C sY R τ hR p =
      powerSumComplexBounded C sY P ρ hP p + powerSumComplexBounded C sY Q σ hQ p := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty sY).elim _ _
  have hτ := rank_eq_add_of_iso_biprod e ρ σ τ hP hQ hR y
  have hs₁ : ∀ n ∉ ρ.support ∪ σ.support, ρ n = 0 := fun n hn ↦
    Finsupp.notMem_support_iff.1 fun h ↦ hn (Finset.mem_union_left _ h)
  have hs₂ : ∀ n ∉ ρ.support ∪ σ.support, σ n = 0 := fun n hn ↦
    Finsupp.notMem_support_iff.1 fun h ↦ hn (Finset.mem_union_right _ h)
  rw [powerSumComplexBounded_eq_sum C sY R τ hR p (ρ.support ∪ σ.support)
      (fun n hn ↦ by rw [hτ, hs₁ n hn, hs₂ n hn]),
    powerSumComplexBounded_eq_sum C sY P ρ hP p _ hs₁,
    powerSumComplexBounded_eq_sum C sY Q σ hQ p _ hs₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  let := hP n
  let := hQ n
  let := hR n
  have := isFiniteLocallyFreeOfRank_biprod (P.X n) (Q.X n) (ρ n) (σ n)
  rw [← smul_add, powerSumTotal_congr C sY (e n) (hτ n) p,
    powerSumTotal_biprod C sY (P.X n) (Q.X n) (ρ n) (σ n) p]

end Bounded

/-! ### Locally bounded complexes -/

section LocallyBounded

variable {Y : Scheme.{u}}

/-- The terms of the termwise pullback of a biproduct of complexes are the biproducts of the
terms of the termwise pullbacks. -/
def pullbackComplexBiprodXIso {Y' : Scheme.{u}} (g : Y' ⟶ Y) (P Q : CochainComplex Y.Modules ℤ)
    (n : ℤ) :
    (pullbackComplex g (P ⊞ Q)).X n ≅
      ((pullbackComplex g P).X n ⊞ (pullbackComplex g Q).X n : Y'.Modules) :=
  haveI := preservesBinaryBiproducts_of_preservesBiproducts (Scheme.Modules.pullback g)
  (Scheme.Modules.pullback g).mapIso (HomologicalComplex.biprodXIso P Q n) ≪≫
    (Scheme.Modules.pullback g).mapBiprod (P.X n) (Q.X n)

/-- **The termwise biproduct of two locally bounded complexes of finite locally free modules is
one again**: its terms are biproducts of finite locally free modules, and near a point it vanishes
outside the union of the two ranges of degrees. -/
theorem isLocallyBoundedFiniteLocallyFree_biprod {P Q : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q) :
    IsLocallyBoundedFiniteLocallyFree (P ⊞ Q : CochainComplex Y.Modules ℤ) := by
  refine ⟨fun n ↦ ?_, fun x ↦ ?_⟩
  · let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P.X n) := hP.1 n
    let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (Q.X n) := hQ.1 n
    exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
      (HomologicalComplex.biprodXIso P Q n).symm
      (h := SheafOfModules.isFiniteLocallyFree_biprod (P.X n) (Q.X n))
  · obtain ⟨U, hxU, lo, hi, hU⟩ := hP.2 x
    obtain ⟨V, hxV, lo', hi', hV⟩ := hQ.2 x
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, min lo lo', max hi hi', fun n hn ↦ ?_⟩
    have hn₁ : n < lo ∨ hi < n := by
      rcases hn with hn | hn
      · exact Or.inl (lt_of_lt_of_le hn (min_le_left _ _))
      · exact Or.inr (lt_of_le_of_lt (le_max_left _ _) hn)
    have hn₂ : n < lo' ∨ hi' < n := by
      rcases hn with hn | hn
      · exact Or.inl (lt_of_lt_of_le hn (min_le_right _ _))
      · exact Or.inr (lt_of_le_of_lt (le_max_right _ _) hn)
    have h₁ := Stacks.BlowUpComplexes.isZero_restrictModules_of_le (V := U ⊓ V) inf_le_left _
      (hU n hn₁)
    have h₂ := Stacks.BlowUpComplexes.isZero_restrictModules_of_le (V := U ⊓ V) inf_le_right _
      (hV n hn₂)
    let W : Y.Opens := U ⊓ V
    let e : ∀ M : Y.Modules, (RingedSpace.restrictModules Y.toRingedSpace W).obj M ≅
        (Scheme.Modules.pullback W.ι).obj M := fun M ↦
      (Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Y W).app M ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M
    refine IsZero.of_iso ?_ (e _ ≪≫ pullbackComplexBiprodXIso W.ι P Q n)
    exact (biprod_isZero_iff (C := (W : Scheme.{u}).Modules) ((pullbackComplex W.ι P).X n)
      ((pullbackComplex W.ι Q).X n)).2 ⟨h₁.of_iso (e _).symm, h₂.of_iso (e _).symm⟩

variable (C : ChowSituation.{u}) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **A total class is determined on the test schemes along which two given locally bounded
complexes have constant ranks**: the decomposition of `Y` into the rank loci of `P` refines, on
each piece, to the decomposition into the rank loci of the pullback of `Q`, and Stacks 0FDZ
applies twice. -/
theorem TotalChowClass.eq_of_res_eq_of_complexRank₂ {P Q : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    {a b : TotalChowClass C sY}
    (h : ∀ {T : Scheme.{u}} {sT : T ⟶ C.S} [LocallyOfFiniteType sT] (g : T ⟶ Y)
      [LocallyOfFiniteType g] (hs : g ≫ sY = sT) (ρ σ : ℤ →₀ ℕ),
      (∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((pullbackComplex g P).X n) (ρ n)) →
      (∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((pullbackComplex g Q).X n) (σ n)) →
      TotalChowClass.res g hs a = TotalChowClass.res g hs b) : a = b := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
  set hQ' := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback
    (complexRankLoci hP ρ).ι Q hQ
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hQ') fun σ ↦ ?_
  set ιs := (complexRankLoci hQ' σ).ι
  rw [TotalChowClass.res_res, TotalChowClass.res_res]
  refine h _ _ ρ.down σ.down (fun n ↦ ?_) (fun n ↦ ?_)
  · exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.pullbackComp ιs (complexRankLoci hP ρ).ι).app (P.X n))
      (isFiniteLocallyFreeOfRank_pullbackComplex_X _ ιs ρ.down
        (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down) n)
  · exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.pullbackComp ιs (complexRankLoci hP ρ).ι).app (Q.X n))
      (isFiniteLocallyFreeOfRank_complexRankLocus hQ' σ.down n)

/-- The terms of the pullback of `P ⊞ Q` are finite locally free of rank `ρ n + σ n`, when those
of the pullbacks of `P` and `Q` have ranks `ρ n` and `σ n`. -/
private theorem isFiniteLocallyFreeOfRank_pullbackComplex_biprod_X {Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {P Q : CochainComplex Y.Modules ℤ} {ρ σ : ℤ →₀ ℕ}
    (hρ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex g P).X n) (ρ n))
    (hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex g Q).X n) (σ n)) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex g (P ⊞ Q)).X n) ((ρ + σ) n) := by
  let := hρ n
  let := hσ n
  rw [Finsupp.add_apply]
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (pullbackComplexBiprodXIso g P Q n).symm (isFiniteLocallyFreeOfRank_biprod _ _ _ _)

/-- **The total Chern class of a termwise biproduct** of locally bounded complexes of finite
locally free modules is the product of the total Chern classes: `c(P ⊕ Q) = c(P) c(Q)`. -/
theorem complexChern_biprod {P Q : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q) :
    complexChern C sY (isLocallyBoundedFiniteLocallyFree_biprod hP hQ) =
      complexChern C sY hP * complexChern C sY hQ := by
  refine TotalChowClass.eq_of_res_eq_of_complexRank₂ C sY hP hQ
    fun {T sT _} g _ hs ρ σ hρ hσ ↦ ?_
  have hτ := isFiniteLocallyFreeOfRank_pullbackComplex_biprod_X g hρ hσ
  rw [map_mul, res_complexChern_eq_complexChernBounded C sY _ g hs (ρ + σ) hτ,
    res_complexChern_eq_complexChernBounded C sY hP g hs ρ hρ,
    res_complexChern_eq_complexChernBounded C sY hQ g hs σ hσ]
  exact complexChernBounded_eq_mul_of_iso_biprod C sT (pullbackComplexBiprodXIso g P Q) ρ σ
    (ρ + σ) hρ hσ hτ

/-- **The power sums of a termwise biproduct** of locally bounded complexes of finite locally
free modules are the sums of the power sums: `P_p(P ⊕ Q) = P_p(P) + P_p(Q)`. -/
theorem powerSumComplex_biprod {P Q : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (p : ℕ) :
    powerSumComplex C sY (isLocallyBoundedFiniteLocallyFree_biprod hP hQ) p =
      powerSumComplex C sY hP p + powerSumComplex C sY hQ p := by
  refine TotalChowClass.eq_of_res_eq_of_complexRank₂ C sY hP hQ
    fun {T sT _} g _ hs ρ σ hρ hσ ↦ ?_
  have hτ := isFiniteLocallyFreeOfRank_pullbackComplex_biprod_X g hρ hσ
  rw [map_add, res_powerSumComplex_eq_powerSumComplexBounded C sY _ g hs (ρ + σ) hτ,
    res_powerSumComplex_eq_powerSumComplexBounded C sY hP g hs ρ hρ,
    res_powerSumComplex_eq_powerSumComplexBounded C sY hQ g hs σ hσ]
  exact powerSumComplexBounded_eq_add_of_iso_biprod C sT (pullbackComplexBiprodXIso g P Q) ρ σ
    (ρ + σ) hρ hσ hτ p

end LocallyBounded

/-! ### Direct sums in the derived category -/

section Derived

variable {X : Scheme.{u}}

/-- **Derived pullback commutes with direct sums**: `Lf^*(E ⊕ F) ≅ Lf^*E ⊕ Lf^*F`. The derived
pullback is a left adjoint, so it preserves binary coproducts, which in the derived category are
the biproducts. -/
def derivedPullbackBiprodIso {Y : Scheme.{u}} (f : Y ⟶ X) (E F : DerivedCategory X.Modules) :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj
        (E ⊞ F : DerivedCategory X.Modules) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj E ⊞
        (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj F :=
  haveI : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).IsLeftAdjoint :=
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f.toLRSHom.toShHom).isLeftAdjoint
  have hG : PreservesColimitsOfSize.{0, 0}
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom) :=
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      f.toLRSHom.toShHom).leftAdjoint_preservesColimits
  haveI : PreservesColimit (pair E F)
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom) :=
    (hG.preservesColimitsOfShape (J := Discrete WalkingPair)).preservesColimit
  (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).mapIso
      (biprod.isoCoprod E F) ≪≫
    (PreservesColimitPair.iso _ E F).symm ≪≫ (biprod.isoCoprod _ _).symm

variable {E F : DerivedCategory X.Modules}

/-- **The direct sum of two envelope presentations.** For presentations `(f, 𝓔^•)` of `E` and
`(f', 𝓕^•)` of `F`, the envelope `Y ×_X Y' ⟶ X` and the termwise biproduct of the pullbacks of
`𝓔^•` and `𝓕^•` to `Y ×_X Y'` present `E ⊕ F`. -/
def EnvelopePresentation.biprod (H : EnvelopePresentation E) (H' : EnvelopePresentation F) :
    EnvelopePresentation (E ⊞ F : DerivedCategory X.Modules) where
  Y := pullback H.f H'.f
  f := pullback.fst H.f H'.f ≫ H.f
  envelope := isEnvelope_comp H.f _ H.envelope
    (isEnvelope_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback H.f H'.f).flip
      H'.envelope)
  P := (pullbackComplex (pullback.fst H.f H'.f) H.P ⊞ pullbackComplex (pullback.snd H.f H'.f) H'.P :
    CochainComplex (pullback H.f H'.f).Modules ℤ)
  locallyBounded := isLocallyBoundedFiniteLocallyFree_biprod
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H.P H.locallyBounded)
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H'.P H'.locallyBounded)
  representation := ⟨derivedPullbackBiprodIso _ E F ≪≫
    biprod.mapIso (H.pullbackRepresentation (pullback.fst H.f H'.f))
      ((eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
        (congrArg (fun m : pullback H.f H'.f ⟶ X ↦ m.toLRSHom.toShHom)
          (pullback.condition (f := H.f) (g := H'.f))))).app F ≪≫
        H'.pullbackRepresentation (pullback.snd H.f H'.f)) ≪≫
    (haveI := preservesBinaryBiproducts_of_preservesBiproducts
      (DerivedCategory.Q (C := (pullback H.f H'.f).Modules))
    ((DerivedCategory.Q (C := (pullback H.f H'.f).Modules)).mapBiprod
      (pullbackComplex (pullback.fst H.f H'.f) H.P)
      (pullbackComplex (pullback.snd H.f H'.f) H'.P)).symm)⟩

/-- **Stacks 0F9F, the direct-sum case: the Chern classes of a direct sum are defined** when
those of the summands are. -/
theorem hasDefinedChernClasses_biprod (hE : HasDefinedChernClasses E)
    (hF : HasDefinedChernClasses F) : HasDefinedChernClasses (E ⊞ F : DerivedCategory X.Modules) :=
  ⟨hE.some.biprod hF.some⟩

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 0F9F, the direct-sum case: the Whitney formula** `c(E ⊕ F) = c(E) c(F)` for objects
of `D(𝒪_X)` whose Chern classes are defined. -/
theorem perfectChernClass_biprod (hE : HasDefinedChernClasses E) (hF : HasDefinedChernClasses F)
    (hEF : HasDefinedChernClasses (E ⊞ F : DerivedCategory X.Modules)) :
    perfectChernClass C sX hEF = perfectChernClass C sX hE * perfectChernClass C sX hF := by
  set H := hE.some
  set H' := hF.some
  refine (eq_perfectChernClass C sX hEF (H.biprod H') ?_).symm
  show TotalChowClass.res (pullback.fst H.f H'.f ≫ H.f) rfl
      (perfectChernClass C sX hE * perfectChernClass C sX hF) =
    complexChern C ((pullback.fst H.f H'.f ≫ H.f) ≫ sX)
      (isLocallyBoundedFiniteLocallyFree_biprod
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H.P H.locallyBounded)
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H'.P
          H'.locallyBounded))
  rw [map_mul, complexChern_biprod C _
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H.P H.locallyBounded)
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H'.P
      H'.locallyBounded)]
  congr 1
  · rw [← TotalChowClass.res_res H.f rfl (pullback.fst H.f H'.f) (Category.assoc _ _ _).symm,
      res_perfectChernClass C sX hE H, res_complexChern]
  · have hs : (pullback.snd H.f H'.f ≫ H'.f) ≫ sX = (pullback.fst H.f H'.f ≫ H.f) ≫ sX := by
      rw [pullback.condition]
    rw [TotalChowClass.res_congr (pullback.condition (f := H.f) (g := H'.f)) rfl hs,
      ← TotalChowClass.res_res H'.f rfl (pullback.snd H.f H'.f)
        ((Category.assoc _ _ _).symm.trans hs),
      res_perfectChernClass C sX hF H', res_complexChern]

/-- **Stacks 0F9F, the direct-sum case: additivity of the power sums**
`P_p(E ⊕ F) = P_p(E) + P_p(F)` for objects of `D(𝒪_X)` whose Chern classes are defined. -/
theorem perfectPowerSum_biprod (hE : HasDefinedChernClasses E) (hF : HasDefinedChernClasses F)
    (hEF : HasDefinedChernClasses (E ⊞ F : DerivedCategory X.Modules)) (p : ℕ) :
    perfectPowerSum C sX hEF p = perfectPowerSum C sX hE p + perfectPowerSum C sX hF p := by
  set H := hE.some
  set H' := hF.some
  refine (eq_perfectPowerSum C sX hEF (H.biprod H') p ?_).symm
  show TotalChowClass.res (pullback.fst H.f H'.f ≫ H.f) rfl
      (perfectPowerSum C sX hE p + perfectPowerSum C sX hF p) =
    powerSumComplex C ((pullback.fst H.f H'.f ≫ H.f) ≫ sX)
      (isLocallyBoundedFiniteLocallyFree_biprod
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H.P H.locallyBounded)
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H'.P
          H'.locallyBounded)) p
  rw [map_add, powerSumComplex_biprod C _
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H.P H.locallyBounded)
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H'.P
      H'.locallyBounded)]
  congr 1
  · rw [← TotalChowClass.res_res H.f rfl (pullback.fst H.f H'.f) (Category.assoc _ _ _).symm,
      res_perfectPowerSum_eq_powerSumComplex C sX hE H, res_powerSumComplex]
  · have hs : (pullback.snd H.f H'.f ≫ H'.f) ≫ sX = (pullback.fst H.f H'.f ≫ H.f) ≫ sX := by
      rw [pullback.condition]
    rw [TotalChowClass.res_congr (pullback.condition (f := H.f) (g := H'.f)) rfl hs,
      ← TotalChowClass.res_res H'.f rfl (pullback.snd H.f H'.f)
        ((Category.assoc _ _ _).symm.trans hs),
      res_perfectPowerSum_eq_powerSumComplex C sX hF H', res_powerSumComplex]

end Derived

end Stacks.Chow

end
