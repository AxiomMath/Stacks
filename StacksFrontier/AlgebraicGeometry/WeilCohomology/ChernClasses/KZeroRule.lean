module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ShortExactMultiplicativity

/-!
# The total Chern class on all of `K₀(Vect(X))`: Stacks Tag 0FI5

In the standing situation of Stacks Section 45.12 this file constructs the rule

`c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`

of Tag 0FI5 and proves that it is the only one with the proposition's three properties.

The two steps left after
`Stacks.WeilCohomology.ChernSituation.chernSeries_mul_of_shortExact` are the source's own: the
total Chern class of a module of **arbitrary** rank, got by patching the constant-rank classes
over the open and closed loci where the rank is constant, and the extension from the generators
`[ℰ]` to all of `K₀(Vect(X))` by the universal property of the Grothendieck group.

## Main definitions

* `Stacks.WeilCohomology.ChernSituation.chernSeriesOfModule`: **the total Chern class of an
  arbitrary finite locally free module**, the unique class whose restriction to every object over
  `X` on which `ℰ` has constant rank is the constant-rank total Chern class. A module which is not
  finite locally free gets `1`, which is the normalisation
  `AlgebraicGeometry.VectorBundleKZero.classOf` uses for the same modules.
* `Stacks.WeilCohomology.ChernSituation.totalChernClass`: **the rule `c^A` of Tag 0FI5**, as the
  family of components `c^A(α)_n ∈ A^n(X)`.

## Main results

* `Stacks.WeilCohomology.ChernSituation.chernSeriesOfModule_eq_chernSeries`: on a module of
  constant rank the arbitrary-rank class is the constant-rank one.
* `Stacks.WeilCohomology.ChernSituation.chernSeriesOfModule_mul_of_shortExact`: multiplicativity
  in short exact sequences, with **no** restriction on the ranks.
* `Stacks.WeilCohomology.ChernSituation.isTotalChernClass_totalChernClass`: **the existence half
  of Tag 0FI5** — the rule has the three properties.
* `Stacks.WeilCohomology.ChernSituation.eq_totalChernClass_of_isTotalChernClass`: **the
  uniqueness half of Tag 0FI5 on all of `K₀(Vect(X))`** — any rule with the three properties is
  this one.
* `Stacks.WeilCohomology.ChernSituation.existsUnique_isTotalChernClass`: **Tag 0FI5.**

## How the restriction to constant rank is removed

The source writes: "let `X = ⋃ X_r` be the decomposition into open and closed subschemes such
that `ℰ|_{X_r}` has constant rank `r`. Since `X` is quasi-compact, this decomposition is finite.
Hence `A(X) = ∏ A(X_r)`." That sentence is the content of the three fields
`Stacks.WeilCohomology.ChernSituation.eq_of_pull_constantRank`,
`Stacks.WeilCohomology.ChernSituation.exists_pull_eq_constantRank` and
`Stacks.WeilCohomology.ChernSituation.mem_grade_of_pull_constantRank` of the situation, which say
that `A(X)` is determined by, patched from, and graded by its restrictions along the morphisms of
`𝒞` along which `ℰ` acquires a constant rank. Everything below is proved from them; no statement
here mentions a constant rank.

## How the restriction to the generators is removed

The target of `c^A` is a *group*, `Stacks.WeilCohomology.UnitalCentralSeries`, so the universal
property of `K₀(Vect(X))` applies to `ℰ ↦ c^A(ℰ)` once it is multiplicative in short exact
sequences; that is `Stacks.WeilCohomology.kZeroSeries`. Property (1) is then automatic on all of
`K₀(Vect(X))`, property (2) follows from its value on the generators because both sides of it are
multiplicative on sums — `Stacks.WeilCohomology.eq_of_convolutive_of_eq_classOf` — and so does
uniqueness.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology

namespace ChernSituation

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
  (𝔖 : ChernSituation.{u, v, v₁, w} C S)

/-! ### Separation along the constant-rank loci -/

/-- Separation along the constant-rank loci of one module. -/
theorem eq_of_pull_one (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (a b : 𝔖.A X)
    (h : ∀ (Z : C) (g : Z ⟶ X), Flat (S.map g) → ∀ m : ℕ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj E) m → 𝔖.pull g a = 𝔖.pull g b) : a = b :=
  𝔖.eq_of_pull_constantRank X (Fin 1) inferInstance (fun _ => E) (fun _ => hE) a b
    fun Z g hg m hm => h Z g hg (m 0) (hm 0)

/-- Separation along the loci where three modules all have constant rank. -/
theorem eq_of_pull_three (X : C) (E₁ E₂ E₃ : (S.obj X).Modules)
    (h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E₁)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E₂)
    (h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E₃) (a b : 𝔖.A X)
    (h : ∀ (Z : C) (g : Z ⟶ X), Flat (S.map g) → ∀ m₁ m₂ m₃ : ℕ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map g)).obj E₁) m₁ →
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map g)).obj E₂) m₂ →
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Scheme.Modules.pullback (S.map g)).obj E₃) m₃ →
            𝔖.pull g a = 𝔖.pull g b) : a = b := by
  classical
  refine 𝔖.eq_of_pull_constantRank X (Fin 3) inferInstance
    (fun i => if i = 0 then E₁ else if i = 1 then E₂ else E₃) (fun i => ?_) a b fun Z g hg m hm =>
    h Z g hg (m 0) (m 1) (m 2) ?_ ?_ ?_
  · by_cases hi0 : i = 0
    · simpa [hi0] using h₁
    · by_cases hi1 : i = 1
      · simpa [hi0, hi1] using h₂
      · simpa [hi0, hi1] using h₃
  · simpa using hm 0
  · simpa using hm 1
  · simpa using hm 2

/-! ### The total Chern class of a module of arbitrary rank -/

/-- The components of the unit series are homogeneous. -/
private theorem coeff_one_mem_grade (X : C) (n : ℕ) :
    (1 : UnitalCentralSeries (𝔖.A X)).coeff n ∈ 𝔖.grade X n := by
  rw [UnitalCentralSeries.coeff_one]
  split_ifs with hn
  · subst hn; exact 𝔖.one_mem X
  · exact AddSubgroup.zero_mem _

/-- The components of the constant-rank total Chern class are homogeneous. -/
theorem chernSeries_coeff_mem_grade (X : C) (E : (S.obj X).Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m) (n : ℕ) :
    (𝔖.chernSeries X E m hE).coeff n ∈ 𝔖.grade X n := by
  revert hE
  cases m with
  | zero =>
      intro hE
      rw [𝔖.chernSeries_rank_zero X E hE]
      exact 𝔖.coeff_one_mem_grade X n
  | succ r =>
      intro hE
      rw [𝔖.chernSeries_coeff_succ X E r hE n]
      exact 𝔖.chernClass_mem_grade X E r hE n

/-- The family of constant-rank total Chern classes that the arbitrary-rank class patches. -/
def constantRankFamily (X : C) (E : (S.obj X).Modules) (n : ℕ) :
    ∀ (Z : C) (g : Z ⟶ X) (m : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj E) m → 𝔖.A Z :=
  fun Z g m hm => (𝔖.chernSeries Z ((Scheme.Modules.pullback (S.map g)).obj E) m hm).coeff n

/-- The family is compatible with further pullback, by
`Stacks.WeilCohomology.ChernSituation.pull_chernSeries_coeff_of_iso`: the two pullbacks
`h^*(g^*ℰ)` and `(h ≫ g)^*ℰ` are isomorphic and not equal. -/
theorem constantRankFamily_compat (X : C) (E : (S.obj X).Modules) (n : ℕ) :
    ∀ (Z Z' : C) (g : Z ⟶ X) (h : Z' ⟶ Z) (m : ℕ)
      (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj E) m)
      (hm' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map (h ≫ g))).obj E) m),
      𝔖.pull h (𝔖.constantRankFamily X E n Z g m hm) =
        𝔖.constantRankFamily X E n Z' (h ≫ g) m hm' :=
  fun Z Z' g h m hm hm' =>
    𝔖.pull_chernSeries_coeff_of_iso Z Z' h _ _ m hm hm'
      ((Scheme.Modules.pullbackComp (S.map h) (S.map g)).app E ≪≫
        (Scheme.Modules.pullbackCongr (S.map_comp h g).symm).app E) n

/-- The `n`-th component of the total Chern class of an arbitrary finite locally free module. -/
def patchedCoeff (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) : 𝔖.A X :=
  (𝔖.exists_pull_eq_constantRank X E hE (𝔖.constantRankFamily X E n)
    (𝔖.constantRankFamily_compat X E n)).choose

/-- **The defining property of the arbitrary-rank components**: along any morphism of `𝒞` making
`ℰ` of constant rank they restrict to the constant-rank total Chern class. -/
theorem pull_patchedCoeff (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) (Z : C) (g : Z ⟶ X) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map g)).obj E) m) :
    𝔖.pull g (𝔖.patchedCoeff X E hE n) =
      (𝔖.chernSeries Z ((Scheme.Modules.pullback (S.map g)).obj E) m hm).coeff n :=
  (𝔖.exists_pull_eq_constantRank X E hE (𝔖.constantRankFamily X E n)
    (𝔖.constantRankFamily_compat X E n)).choose_spec Z g m hm

/-- Each arbitrary-rank component `Stacks.WeilCohomology.ChernSituation.patchedCoeff` is central
in `A(X)`. -/
theorem patchedCoeff_mem_center (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) :
    𝔖.patchedCoeff X E hE n ∈ Subring.center (𝔖.A X) := by
  refine Subring.mem_center_iff.2 fun b => 𝔖.eq_of_pull_one X E hE _ _ fun Z g hg m hm => ?_
  rw [map_mul, map_mul, 𝔖.pull_patchedCoeff X E hE n Z g m hm]
  exact Subring.mem_center_iff.1 (UnitalCentralSeries.coeff_mem_center _ n) _

/-- The `0`-th arbitrary-rank component is `1`. -/
theorem patchedCoeff_zero (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) : 𝔖.patchedCoeff X E hE 0 = 1 := by
  refine 𝔖.eq_of_pull_one X E hE _ 1 fun Z g hg m hm => ?_
  rw [𝔖.pull_patchedCoeff X E hE 0 Z g m hm, map_one, UnitalCentralSeries.coeff_zero]

/-- The `n`-th arbitrary-rank component lies in `A^n(X)`. -/
theorem patchedCoeff_mem_grade (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) :
    𝔖.patchedCoeff X E hE n ∈ 𝔖.grade X n := by
  refine 𝔖.mem_grade_of_pull_constantRank X E hE _ n fun Z g hg m hm => ?_
  rw [𝔖.pull_patchedCoeff X E hE n Z g m hm]
  exact 𝔖.chernSeries_coeff_mem_grade Z _ m hm n

/-- **The total Chern class of an arbitrary finite locally free module.** Its `n`-th component is
the unique class of `A^n(X)` restricting to `c^A_n` on every object over `X` where `ℰ` has
constant rank; a module which is not finite locally free gets the unit series, which is the
normalisation `AlgebraicGeometry.VectorBundleKZero.classOf` uses for the same modules. -/
def chernSeriesOfModule (X : C) (E : (S.obj X).Modules) : UnitalCentralSeries (𝔖.A X) :=
  letI := Classical.propDecidable (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (R := (S.obj X).ringCatSheaf) E)
  if hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E then
    UnitalCentralSeries.ofCoeff (𝔖.patchedCoeff X E hE) (𝔖.patchedCoeff_mem_center X E hE)
      (𝔖.patchedCoeff_zero X E hE)
  else 1

/-- The total Chern class of a module which is not finite locally free is `1`. -/
theorem chernSeriesOfModule_of_not (X : C) (E : (S.obj X).Modules)
    (hE : ¬ AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) : 𝔖.chernSeriesOfModule X E = 1 :=
  dite_eq_right hE

/-- On a finite locally free module, the `n`-th coefficient of the total Chern class is the
arbitrary-rank component `Stacks.WeilCohomology.ChernSituation.patchedCoeff`. -/
theorem coeff_chernSeriesOfModule (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) :
    (𝔖.chernSeriesOfModule X E).coeff n = 𝔖.patchedCoeff X E hE n := by
  rw [chernSeriesOfModule, dite_eq_left hE, UnitalCentralSeries.coeff_ofCoeff]

/-- The `n`-th coefficient of the total Chern class of any module lies in `A^n(X)`. -/
theorem coeff_chernSeriesOfModule_mem_grade (X : C) (E : (S.obj X).Modules) (n : ℕ) :
    (𝔖.chernSeriesOfModule X E).coeff n ∈ 𝔖.grade X n := by
  by_cases hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E
  · rw [𝔖.coeff_chernSeriesOfModule X E hE n]
    exact 𝔖.patchedCoeff_mem_grade X E hE n
  · rw [𝔖.chernSeriesOfModule_of_not X E hE]
    exact 𝔖.coeff_one_mem_grade X n

/-- Along a morphism making the rank constant, the components of the arbitrary-rank total Chern
class of a finite locally free module restrict to the constant-rank ones. -/
private theorem pull_coeff_chernSeriesOfModule_of_rank (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) (Z : C) (g : Z ⟶ X) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map g)).obj E) m) :
    𝔖.pull g ((𝔖.chernSeriesOfModule X E).coeff n) =
      (𝔖.chernSeries Z ((Scheme.Modules.pullback (S.map g)).obj E) m hm).coeff n := by
  rw [𝔖.coeff_chernSeriesOfModule X E hE n]
  exact 𝔖.pull_patchedCoeff X E hE n Z g m hm

/-- **On a module of constant rank the arbitrary-rank total Chern class is the constant-rank
one.** -/
theorem chernSeriesOfModule_eq_chernSeries (X : C) (E : (S.obj X).Modules) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m) :
    𝔖.chernSeriesOfModule X E = 𝔖.chernSeries X E m hm := by
  refine UnitalCentralSeries.ext fun n => ?_
  refine 𝔖.eq_of_pull_one X E hm.isFiniteLocallyFree _ _ fun Z g hg m' hm' => ?_
  have hpm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map g)).obj E) m :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map g) E m hm
  rw [𝔖.pull_coeff_chernSeriesOfModule_of_rank X E hm.isFiniteLocallyFree n Z g m' hm',
    𝔖.pull_chernSeries_coeff X Z g E m hm hpm n,
    𝔖.chernSeries_eq_of_rank Z _ m' m hm' hpm]

/-- **The total Chern class is compatible with pullback**, which is property (2) of Tag 0FI5 at a
generator. The patching characterization holds along *every* morphism of `𝒞` making the rank
constant, so both sides restrict to the same constant-rank class. -/
theorem pull_coeff_chernSeriesOfModule (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) :
    𝔖.pull f ((𝔖.chernSeriesOfModule X E).coeff n) =
      (𝔖.chernSeriesOfModule X' ((Scheme.Modules.pullback (S.map f)).obj E)).coeff n := by
  have hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X').ringCatSheaf) ((Scheme.Modules.pullback (S.map f)).obj E) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (S.map f) E hE
  refine 𝔖.eq_of_pull_one X' _ hE' _ _ fun Z g hg m hm => ?_
  have hiso : (Scheme.Modules.pullback (S.map g)).obj
        ((Scheme.Modules.pullback (S.map f)).obj E) ≅
      (Scheme.Modules.pullback (S.map (g ≫ f))).obj E :=
    (Scheme.Modules.pullbackComp (S.map g) (S.map f)).app E ≪≫
      (Scheme.Modules.pullbackCongr (S.map_comp g f).symm).app E
  have hm2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map (g ≫ f))).obj E) m :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso hiso hm
  rw [← RingHom.comp_apply, ← 𝔖.pull_comp g f,
    𝔖.pull_coeff_chernSeriesOfModule_of_rank X E hE n Z (g ≫ f) m hm2,
    𝔖.pull_coeff_chernSeriesOfModule_of_rank X' _ hE' n Z g m hm,
    𝔖.chernSeries_eq_of_iso Z _ _ m m hm2 hm hiso.symm]

/-- **The total Chern class is multiplicative in every short exact sequence of finite locally free
modules**, with no restriction on the ranks: the loci where all three have constant rank separate
`A(X)`, the inclusions of those loci are flat, and there the sequence stays short exact and
`Stacks.WeilCohomology.ChernSituation.chernSeries_mul_of_shortExact` applies. -/
theorem chernSeriesOfModule_mul_of_shortExact (X : C) (T : ShortComplex (S.obj X).Modules)
    (hT : T.ShortExact)
    (h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) T.X₁)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) T.X₂)
    (h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) T.X₃) :
    𝔖.chernSeriesOfModule X T.X₂ =
      𝔖.chernSeriesOfModule X T.X₁ * 𝔖.chernSeriesOfModule X T.X₃ := by
  refine UnitalCentralSeries.ext fun n => ?_
  refine 𝔖.eq_of_pull_three X T.X₁ T.X₂ T.X₃ h₁ h₂ h₃ _ _ fun Z g hg m₁ m₂ m₃ hm₁ hm₂ hm₃ => ?_
  have := hg
  have key := 𝔖.chernSeries_mul_of_shortExact m₁ Z
    (T.map (Scheme.Modules.pullback (S.map g))) (shortExact_map_pullback (S.map g) T hT)
    m₂ m₃ hm₁ hm₂ hm₃
  have hr : 𝔖.pull g
        ((𝔖.chernSeriesOfModule X T.X₁ * 𝔖.chernSeriesOfModule X T.X₃).coeff n) =
      (𝔖.chernSeries Z ((Scheme.Modules.pullback (S.map g)).obj T.X₁) m₁ hm₁ *
        𝔖.chernSeries Z ((Scheme.Modules.pullback (S.map g)).obj T.X₃) m₃ hm₃).coeff n := by
    rw [UnitalCentralSeries.coeff_mul, map_sum, UnitalCentralSeries.coeff_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, 𝔖.pull_coeff_chernSeriesOfModule_of_rank X T.X₁ h₁ q.1 Z g m₁ hm₁,
      𝔖.pull_coeff_chernSeriesOfModule_of_rank X T.X₃ h₃ q.2 Z g m₃ hm₃]
  rw [𝔖.pull_coeff_chernSeriesOfModule_of_rank X T.X₂ h₂ n Z g m₂ hm₂, hr]
  exact congrArg (fun s => UnitalCentralSeries.coeff s n) key

/-! ### The rule on `K₀(Vect(X))` -/

/-- The total Chern class of a module which is not finite locally free, in the sense of
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, is `1`. -/
theorem chernSeriesOfModule_eq_one_of_not (X : C) (M : (S.obj X).Modules)
    (hM : ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) M) : 𝔖.chernSeriesOfModule X M = 1 :=
  𝔖.chernSeriesOfModule_of_not X M fun h =>
    hM ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mpr h)

/-- The class in `K₀(Vect(X))` of a module which is not finite locally free is `0`. -/
private theorem classOf_eq_zero_of_not_agFiniteLocallyFree {X : C} (M : (S.obj X).Modules)
    (hM : ¬ AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) M) : VectorBundleKZero.classOf (S.obj X) M = 0 :=
  VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M
    fun h => hM ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp h)

/-- For an exact sequence `0 ⟶ ℰ ⟶ ℱ ⟶ 𝒢 ⟶ 0` of finite locally free modules,
`c^A(ℱ) = c^A(ℰ) · c^A(𝒢)`. -/
theorem chernSeriesOfModule_mul (X : C) {E F G : (S.obj X).Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0)
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E)
    (hF : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) F)
    (hG : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) :
    𝔖.chernSeriesOfModule X F = 𝔖.chernSeriesOfModule X E * 𝔖.chernSeriesOfModule X G :=
  𝔖.chernSeriesOfModule_mul_of_shortExact X (ShortComplex.mk f g w)
    (ShortComplex.ShortExact.mk' hex hmono hepi)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry F).mp hF)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry G).mp hG)

/-- **The rule `c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` of Stacks Tag 0FI5**, as the family of its
components. On a generator it is the total Chern class of the module; the extension is the
universal property of the Grothendieck group, which applies because the target is a group and
`ℰ ↦ c^A(ℰ)` is multiplicative in short exact sequences. -/
def totalChernClass (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ) : 𝔖.A X :=
  (kZeroSeries (𝔖.chernSeriesOfModule X) (𝔖.chernSeriesOfModule_eq_one_of_not X)
    (fun f g w hE hF hG hmono hepi hex =>
      𝔖.chernSeriesOfModule_mul X f g w hE hF hG hmono hepi hex) α).coeff n

/-- On the class of a module `ℰ`, the rule is the total Chern class of `ℰ`. -/
theorem totalChernClass_classOf (X : C) (E : (S.obj X).Modules) (n : ℕ) :
    𝔖.totalChernClass X (VectorBundleKZero.classOf (S.obj X) E) n =
      (𝔖.chernSeriesOfModule X E).coeff n := by
  rw [totalChernClass, kZeroSeries_classOf]

/-- The rule is multiplicative: the `n`-th component of `c^A(α + β)` is
`∑_{p + q = n} c^A_p(α) c^A_q(β)`. -/
theorem totalChernClass_add (X : C) (α β : VectorBundleKZero (S.obj X)) (n : ℕ) :
    𝔖.totalChernClass X (α + β) n =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        𝔖.totalChernClass X α p.1 * 𝔖.totalChernClass X β p.2 := by
  rw [totalChernClass, kZeroSeries_add, UnitalCentralSeries.coeff_mul]
  rfl

/-- The rule takes the value `1` on `0 ∈ K₀(Vect(X))`. -/
theorem totalChernClass_zero (X : C) (n : ℕ) :
    𝔖.totalChernClass X 0 n = if n = 0 then 1 else 0 := by
  rw [totalChernClass, kZeroSeries_zero, UnitalCentralSeries.coeff_one]

/-- The `n`-th component of the rule lies in `A^n(X)`. -/
theorem totalChernClass_mem_grade (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ) :
    𝔖.totalChernClass X α n ∈ 𝔖.grade X n := by
  have hmulG : ∀ (i j : ℕ) {x y : 𝔖.A X}, x ∈ 𝔖.grade X i → y ∈ 𝔖.grade X j →
      x * y ∈ 𝔖.grade X (i + j) := fun i j {_ _} hx hy => 𝔖.mul_mem X i j hx hy
  exact coeff_kZeroSeries_mem _ _ _ (𝔖.grade X) (𝔖.one_mem X) hmulG
    (fun M k => 𝔖.coeff_chernSeriesOfModule_mem_grade X M k) α n

/-- **The existence half of Stacks Tag 0FI5.** The rule
`Stacks.WeilCohomology.ChernSituation.totalChernClass` has the three properties of the
proposition: it is multiplicative on sums of classes and unital, compatible with pullback, and
takes the value `1 + c₁^A(ℒ)` on an invertible module; and its `n`-th component lies in
`A^n(X)`. -/
theorem isTotalChernClass_totalChernClass :
    IsTotalChernClassOnLocallyFree 𝔖.toChernSetup 𝔖.totalChernClass where
  mem_grade X α n := 𝔖.totalChernClass_mem_grade X α n
  map_add X α β n := 𝔖.totalChernClass_add X α β n
  map_zero X n := 𝔖.totalChernClass_zero X n
  map_pull {X Y} f E hE n := by
    rw [𝔖.totalChernClass_classOf Y E n, 𝔖.totalChernClass_classOf X _ n]
    exact 𝔖.pull_coeff_chernSeriesOfModule Y X f E hE n
  map_pull_kZero {X Y} f κ hκ α n := by
    have hite : ∀ k : ℕ, 𝔖.pull f (if k = 0 then 1 else 0) = if k = 0 then 1 else 0 :=
      fun k => by split_ifs <;> simp
    refine eq_of_convolutive_of_eq_classOf
      (c := fun β k => 𝔖.pull f (𝔖.totalChernClass Y β k))
      (c' := fun β k => 𝔖.totalChernClass X (κ β) k) ?_ ?_ ?_ ?_ ?_ α n
    · intro a b k
      rw [𝔖.totalChernClass_add Y a b k, map_sum]
      exact Finset.sum_congr rfl fun q _ => map_mul _ _ _
    · intro k
      rw [𝔖.totalChernClass_zero Y k]
      exact hite k
    · intro a b k
      rw [map_add, 𝔖.totalChernClass_add X (κ a) (κ b) k]
    · intro k
      rw [map_zero, 𝔖.totalChernClass_zero X k]
    · intro M k
      by_cases hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          (R := (S.obj Y).ringCatSheaf) M
      · rw [hκ M hM, 𝔖.totalChernClass_classOf Y M k, 𝔖.totalChernClass_classOf X _ k]
        exact 𝔖.pull_coeff_chernSeriesOfModule Y X f M hM k
      · rw [classOf_eq_zero_of_not_agFiniteLocallyFree M hM, map_zero,
          𝔖.totalChernClass_zero Y k, 𝔖.totalChernClass_zero X k]
        exact hite k
  invertible X L hL n := by
    have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 := by
      have := hL
      infer_instance
    rw [𝔖.totalChernClass_classOf X L n, 𝔖.chernSeriesOfModule_eq_chernSeries X L 1 h1]
    exact 𝔖.chernSeries_coeff_invertible X L hL h1 n

/-! ### Uniqueness, and the proposition -/

/-- **The uniqueness half of Stacks Tag 0FI5, on all of `K₀(Vect(X))`.** A rule with the three
properties of the proposition is
`Stacks.WeilCohomology.ChernSituation.totalChernClass`.

Property (1) reduces this to the classes `[ℰ]` of modules, by
`Stacks.WeilCohomology.eq_of_convolutive_of_eq_classOf`; the loci where `ℰ` has constant rank
reduce it further to a module of constant rank, property (2) carrying both rules there; and there
it is `Stacks.WeilCohomology.eq_of_isTotalChernClassOnLocallyFree`, which the splitting principle
proves. -/
theorem eq_totalChernClass_of_isTotalChernClass
    {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔖.A X}
    (hc : IsTotalChernClassOnLocallyFree 𝔖.toChernSetup c) (X : C) (α : VectorBundleKZero (S.obj X))
    (n : ℕ) : c X α n = 𝔖.totalChernClass X α n := by
  refine eq_of_convolutive_of_eq_classOf (hc.map_add X) (hc.map_zero X)
    (𝔖.totalChernClass_add X) (𝔖.totalChernClass_zero X) (fun M k => ?_) α n
  by_cases hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) M
  · refine 𝔖.eq_of_pull_one X M hM _ _ fun Z g hg m hm => ?_
    rw [hc.map_pull g M hM k, 𝔖.totalChernClass_classOf X M k,
      𝔖.pull_coeff_chernSeriesOfModule X Z g M hM k, ← 𝔖.totalChernClass_classOf Z _ k]
    exact _root_.Stacks.WeilCohomology.eq_of_isTotalChernClassOnLocallyFree hc
      𝔖.isTotalChernClass_totalChernClass Z _ m hm k
  · rw [classOf_eq_zero_of_not_agFiniteLocallyFree M hM, hc.map_zero X k,
      𝔖.totalChernClass_zero X k]

/-- **Tag 0FI5 over the standing situation as a structure.** In the standing situation of
Section 45.12 there is a unique rule which assigns to every object `X` of `𝒞` a total Chern class

`c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`

such that (1) `c^A(α + β) = c^A(α) c^A(β)` and `c^A(0) = 1`, (2) `f^* ∘ c^A = c^A ∘ f^*` for a
morphism `f : X' ⟶ X` of `𝒞`, and (3) `c^A([ℒ]) = 1 + c₁^A(ℒ)` for `ℒ ∈ Pic(X)`.

The tag sits on `Stacks.WeilCohomology.existsUnique_isTotalChernClass_of_source`, which is this
statement with the three conditions of `Stacks.WeilCohomology.ChernSituation` spelled out as
hypotheses and the structure built inside the proof. -/
theorem existsUnique_isTotalChernClass :
    ∃! c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔖.A X,
      IsTotalChernClassOnLocallyFree 𝔖.toChernSetup c :=
  ⟨𝔖.totalChernClass, 𝔖.isTotalChernClass_totalChernClass, fun _c hc =>
    funext fun X => funext fun α => funext fun n =>
      𝔖.eq_totalChernClass_of_isTotalChernClass hc X α n⟩

end ChernSituation

/-! ### Tag 0FI5 in the source's own situation -/

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **Stacks Project, Tag 0FI5.** In the standing situation of Section 45.12 there is a unique
rule which assigns to every object `X` of `𝒞` a total Chern class

`c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`

such that (1) `c^A(α + β) = c^A(α) c^A(β)` and `c^A(0) = 1`, (2) `f^* ∘ c^A = c^A ∘ f^*` for a
morphism `f : X' ⟶ X` of `𝒞`, and (3) `c^A([ℒ]) = 1 + c₁^A(ℒ)` for `ℒ ∈ Pic(X)`.

**What the situation is.** `Stacks.WeilCohomology.ChernSetup` is the source's own standing
situation: the graded rings `A(X)` with the pullback ring maps and the additive
`c₁^A : Pic(X) ⟶ A¹(X)` — the data the source fixes — together with clause (1), clause (2),
clause (3)(a), condition (1), condition (2) and condition (4), and the grading
`A(X) = ⨁_{i ≥ 0} A^i(X)` as `isInternal_grade`. Every field of it is a datum or a condition the
source states; in particular `Stacks.WeilCohomology.ChernSetup.bundleDatum` — the projective
bundle with its flat projection, its invertible twist and its tautological sequence — is a
*definition*, built from clause (3)(a) by
`Stacks.WeilCohomology.BundleObject.toBundleDatum`, and not a field.

The three remaining conditions of the section are the hypotheses here:

* condition (3), `f^*c₁^A(ℒ) = c₁^A(f^*ℒ)`, at `f^*ℒ` itself;
* clause (3)(b), that the induced `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`
  (`Stacks.WeilCohomology.IsBundleCompare`), at `f^*ℰ` itself and with nothing about twists;
* clause (3)(c), that the induced closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`
  (`Stacks.WeilCohomology.IsBundleEmbedding`), together with condition (5) read at
  `c₁^A(𝒪_P(𝐏(𝓕)))` for the divisor module characterized by
  `Stacks.WeilCohomology.IsSubbundleDivisorModule`.

**No hypothesis is read more strongly than the source states it.** In particular `hcompare` is
clause (3)(b) at `f^*ℰ` itself. The invariance of the total Chern class under an isomorphism of
modules, which `K₀(Vect(X))` forces on any rule out of it and which a comparison of the
projective bundles `𝐏(ℰ)` and `𝐏(ℰ')` would get only from a stronger reading of that clause, is
instead the theorem `Stacks.WeilCohomology.ChernSituation.chernSeries_eq_of_iso`, proved from
multiplicativity in the short exact sequence `0 ⟶ ℰ ⟶ ℰ' ⟶ 0 ⟶ 0`. The pseudofunctoriality
coherence isomorphism `h^*(g^*ℰ) ≅ (h ≫ g)^*ℰ`, which the source has for free by writing `f^*`
as a strict functor, is handled by the same theorem through
`Stacks.WeilCohomology.ChernSituation.pull_chernSeries_coeff_of_iso`.

The `Stacks.WeilCohomology.ChernSituation` the development is written over is assembled from
these inside the proof, so it is not an argument of this statement. Everything the source
derives rather than assumes is a theorem: condition (3) under an isomorphism of invertible
modules (`Stacks.WeilCohomology.ChernSituation.pull_c₁`), condition (4) read with the grading
(`Stacks.WeilCohomology.SourceChernSetup.mem_grade_of_bundleFormula`), the identifications of
twists along the two induced morphisms
(`Stacks.WeilCohomology.ChernSituation.exists_bundleCompare` and
`Stacks.WeilCohomology.ChernSituation.exists_divisorDatum`), and
`𝒪_P(𝐏(𝓕)) ≅ 𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}`
(`Stacks.WeilCohomology.BundleObject.twistClass_eq_picardClassOf_add`). -/
@[stacks 0FI5 "the proposition: existence and uniqueness of the rule c^A on all of \
  K_0(Vect(X)), with its three properties, K_0(Vect(X)) being the Grothendieck group \
  AlgebraicGeometry.VectorBundleKZero of Tag 0FDK and prod_{i >= 0} A^i(X) the family of \
  components together with the clause mem_grade. NO constant rank and NO restriction to \
  generators: properties (1) and (2) are stated for every element of K_0(Vect(X)) and the \
  construction is for a module of arbitrary rank. The standing situation is the structure \
  Stacks.WeilCohomology.ChernSetup -- the data the source fixes, with clause (1), clause (2), \
  clause (3)(a), condition (1), condition (2), condition (4) and the source's grading \
  A(X) = sum of the A^i(X) as isInternal_grade -- together with the three remaining conditions \
  of the section, each in the source's own form: condition (3) at f^*L itself; clause (3)(b) as \
  the closure property IsBundleCompare at f^*E itself; and clause (3)(c) as the closure \
  property IsBundleEmbedding with condition (5) read at c_1^A(O_P(P')) for the divisor module \
  characterized divisor-theoretically by IsSubbundleDivisorModule. NO hypothesis is read more \
  strongly than the source states it: the invariance of the total Chern class under an \
  isomorphism of modules, which K_0(Vect(X)) forces on any rule out of it and which a \
  comparison of P(E) with P(E') would get only by asking clause (3)(b) at every E' isomorphic \
  to f^*E, is instead PROVED, as chernSeries_eq_of_iso, from multiplicativity in the short \
  exact sequence 0 to E to E' to 0; the pseudofunctoriality coherence isomorphism \
  h^*(g^*E) = (h . g)^*E, which the source has for free, comes from the same theorem through \
  pull_chernSeries_coeff_of_iso. The structure \
  Stacks.WeilCohomology.ChernSituation is built inside the proof and is not an argument. PROVED \
  here and in this directory, not assumed: the projective bundle with its flat projection, its \
  invertible twist and its tautological sequence of kernel rank r, from clause (3)(a) \
  (BundleObject.toBundleDatum); the rank-one case of that kernel rank \
  (isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred); condition (3) under an \
  isomorphism of invertible modules (pull_c_1); condition (4) read with the grading \
  (mem_grade_of_bundleFormula); the identification of twists along the induced morphism \
  P(f^*E) to P(E) (exists_bundleCompare) and along the induced closed immersion P(F) to P(E) \
  (exists_divisorDatum); the source's identification O_P(P') = O_P(1) tensor (p^*L)^{-1}, from \
  the description of P(F) in P(E) as the zero scheme of a regular section \
  (BundleObject.twistClass_eq_picardClassOf_add); clause (1), clause (2) and condition (2) with \
  the local constancy of the rank, in the form 'A(X) is separated by, patched from and graded by \
  its restrictions to the loci where E has constant rank' (eq_of_pull_constantRank, \
  exists_pull_eq_constantRank, mem_grade_of_pull_constantRank, subsingleton_of_isEmpty); the \
  construction of the Chern classes, equation 45.12.1.1, their centrality and homogeneity, \
  their compatibility with pullback, the Whitney formula for an invertible submodule, \
  multiplicativity in an arbitrary short exact sequence by induction on the rank, the \
  arbitrary-rank total Chern class, the extension to K_0(Vect(X)) with the formal inverse, the \
  three properties, and the uniqueness; the source's 'it suffices to check this after pulling \
  back by P(E^dual) -- thus we may assume we have an invertible submodule L of E such that both \
  E/L and F/L are finite locally free' (exists_splitInvertibleSub); the rank of the middle term \
  of the sequence of clause (3)(c), from \
  AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact; and the first Chern class of the \
  divisor class of that clause, from condition (3) with the additivity of c_1^A on Pic \
  (c_1_divisorClass)"]
theorem existsUnique_isTotalChernClass_of_source (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)
    (hpull : PullbackFirstChernCondition 𝔄) (hcompare : BundleCompareClause 𝔄)
    (hdivisor : DivisorDatumClause 𝔄) :
    ∃! c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X,
    IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c :=
  ChernSituation.existsUnique_isTotalChernClass (chernSituationOfSource 𝔄 hpull hcompare hdivisor)

end Stacks.WeilCohomology

end
