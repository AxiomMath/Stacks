module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.KZeroRule
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.ShortExactMultiplicativity

/-!
# The total Chern class on all of `K₀(Vect(X))`: Stacks Tag 0FI5, in the weak standing situation

The results of `StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.KZeroRule`, stated for
`Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation
of Stacks Section 45.12 in which the projective bundle formula, condition (4), is only asked to be
injective and to resolve the top power `c₁^A(𝒪_P(1))^{r+1}` of the twist class (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`, which explains why Tag
0FIE needs this generality). The arguments use condition (4) only through these two properties.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

namespace ChernSituation

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
  (𝔗 : ChernSituation.{u, v, v₁, w} C S)

/-! ### Separation along the constant-rank loci -/

/-- Separation along the constant-rank loci of one module. -/
theorem eq_of_pull_one (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (a b : 𝔗.A X)
    (h : ∀ (Z : C) (g : Z ⟶ X), Flat (S.map g) → ∀ m : ℕ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj E) m → 𝔗.pull g a = 𝔗.pull g b) : a = b :=
  𝔗.eq_of_pull_constantRank X (Fin 1) inferInstance (fun _ => E) (fun _ => hE) a b
    fun Z g hg m hm => h Z g hg (m 0) (hm 0)

/-- Separation along the loci where three modules all have constant rank. -/
theorem eq_of_pull_three (X : C) (E₁ E₂ E₃ : (S.obj X).Modules)
    (h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E₁)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E₂)
    (h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E₃) (a b : 𝔗.A X)
    (h : ∀ (Z : C) (g : Z ⟶ X), Flat (S.map g) → ∀ m₁ m₂ m₃ : ℕ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map g)).obj E₁) m₁ →
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map g)).obj E₂) m₂ →
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Scheme.Modules.pullback (S.map g)).obj E₃) m₃ →
            𝔗.pull g a = 𝔗.pull g b) : a = b := by
  classical
  refine 𝔗.eq_of_pull_constantRank X (Fin 3) inferInstance
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
    (1 : UnitalCentralSeries (𝔗.A X)).coeff n ∈ 𝔗.grade X n := by
  rw [UnitalCentralSeries.coeff_one]
  split_ifs with hn
  exacts [hn ▸ 𝔗.one_mem X, AddSubgroup.zero_mem _]

/-- The components of the constant-rank total Chern class are homogeneous. -/
theorem chernSeries_coeff_mem_grade (X : C) (E : (S.obj X).Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m) (n : ℕ) :
    (𝔗.chernSeries X E m hE).coeff n ∈ 𝔗.grade X n := by
  revert hE
  cases m with
  | zero =>
      intro hE
      rw [𝔗.chernSeries_rank_zero X E hE]
      exact 𝔗.coeff_one_mem_grade X n
  | succ r =>
      intro hE
      rw [𝔗.chernSeries_coeff_succ X E r hE n]
      exact 𝔗.chernClass_mem_grade X E r hE n

/-- The family of constant-rank total Chern classes that the arbitrary-rank class patches. -/
def constantRankFamily (X : C) (E : (S.obj X).Modules) (n : ℕ) :
    ∀ (Z : C) (g : Z ⟶ X) (m : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj E) m → 𝔗.A Z :=
  fun Z g m hm => (𝔗.chernSeries Z ((Scheme.Modules.pullback (S.map g)).obj E) m hm).coeff n

/-- The family is compatible with further pullback, by
`Stacks.WeilCohomology.Weak.ChernSituation.pull_chernSeries_coeff_of_iso`: the two pullbacks
`h^*(g^*ℰ)` and `(h ≫ g)^*ℰ` are isomorphic and not equal. -/
theorem constantRankFamily_compat (X : C) (E : (S.obj X).Modules) (n : ℕ) :
    ∀ (Z Z' : C) (g : Z ⟶ X) (h : Z' ⟶ Z) (m : ℕ)
      (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj E) m)
      (hm' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map (h ≫ g))).obj E) m),
      𝔗.pull h (𝔗.constantRankFamily X E n Z g m hm) =
        𝔗.constantRankFamily X E n Z' (h ≫ g) m hm' :=
  fun Z Z' g h m hm hm' =>
    𝔗.pull_chernSeries_coeff_of_iso Z Z' h _ _ m hm hm'
      ((Scheme.Modules.pullbackComp (S.map h) (S.map g)).app E ≪≫
        (Scheme.Modules.pullbackCongr (S.map_comp h g).symm).app E) n

/-- The `n`-th component of the total Chern class of an arbitrary finite locally free module. -/
def patchedCoeff (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) : 𝔗.A X :=
  (𝔗.exists_pull_eq_constantRank X E hE (𝔗.constantRankFamily X E n)
    (𝔗.constantRankFamily_compat X E n)).choose

/-- **The defining property of the arbitrary-rank components**: along any morphism of `𝒞` making
`ℰ` of constant rank they restrict to the constant-rank total Chern class. -/
theorem pull_patchedCoeff (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) (Z : C) (g : Z ⟶ X) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map g)).obj E) m) :
    𝔗.pull g (𝔗.patchedCoeff X E hE n) =
      (𝔗.chernSeries Z ((Scheme.Modules.pullback (S.map g)).obj E) m hm).coeff n :=
  (𝔗.exists_pull_eq_constantRank X E hE (𝔗.constantRankFamily X E n)
    (𝔗.constantRankFamily_compat X E n)).choose_spec Z g m hm

/-- The components of the arbitrary-rank total Chern class are central. -/
theorem patchedCoeff_mem_center (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) :
    𝔗.patchedCoeff X E hE n ∈ Subring.center (𝔗.A X) := by
  refine Subring.mem_center_iff.2 fun b => 𝔗.eq_of_pull_one X E hE _ _ fun Z g hg m hm => ?_
  rw [map_mul, map_mul, 𝔗.pull_patchedCoeff X E hE n Z g m hm]
  exact Subring.mem_center_iff.1 (UnitalCentralSeries.coeff_mem_center _ n) _

/-- The degree-zero component of the arbitrary-rank total Chern class is `1`. -/
theorem patchedCoeff_zero (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) : 𝔗.patchedCoeff X E hE 0 = 1 := by
  refine 𝔗.eq_of_pull_one X E hE _ 1 fun Z g hg m hm => ?_
  rw [𝔗.pull_patchedCoeff X E hE 0 Z g m hm, map_one, UnitalCentralSeries.coeff_zero]

/-- The `n`-th component of the arbitrary-rank total Chern class lies in `A^n(X)`. -/
theorem patchedCoeff_mem_grade (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) :
    𝔗.patchedCoeff X E hE n ∈ 𝔗.grade X n := by
  refine 𝔗.mem_grade_of_pull_constantRank X E hE _ n fun Z g hg m hm => ?_
  rw [𝔗.pull_patchedCoeff X E hE n Z g m hm]
  exact 𝔗.chernSeries_coeff_mem_grade Z _ m hm n

/-- **The total Chern class of an arbitrary finite locally free module.** Its `n`-th component is
the unique class of `A^n(X)` restricting to `c^A_n` on every object over `X` where `ℰ` has
constant rank; a module which is not finite locally free gets the unit series, which is the
normalisation `AlgebraicGeometry.VectorBundleKZero.classOf` uses for the same modules. -/
def chernSeriesOfModule (X : C) (E : (S.obj X).Modules) : UnitalCentralSeries (𝔗.A X) :=
  letI := Classical.propDecidable (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (R := (S.obj X).ringCatSheaf) E)
  if hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E then
    UnitalCentralSeries.ofCoeff (𝔗.patchedCoeff X E hE) (𝔗.patchedCoeff_mem_center X E hE)
      (𝔗.patchedCoeff_zero X E hE)
  else 1

/-- The total Chern class of a module which is not finite locally free is `1`. -/
theorem chernSeriesOfModule_of_not (X : C) (E : (S.obj X).Modules)
    (hE : ¬ AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) : 𝔗.chernSeriesOfModule X E = 1 :=
  dif_neg hE

/-- The `n`-th component of the total Chern class of a finite locally free module is
`Stacks.WeilCohomology.Weak.ChernSituation.patchedCoeff`. -/
theorem coeff_chernSeriesOfModule (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) :
    (𝔗.chernSeriesOfModule X E).coeff n = 𝔗.patchedCoeff X E hE n := by
  rw [chernSeriesOfModule, dif_pos hE, UnitalCentralSeries.coeff_ofCoeff]

/-- Along a morphism making `ℰ` of constant rank, the components of the arbitrary-rank total
Chern class restrict to those of the constant-rank one. -/
private theorem pull_coeff_chernSeriesOfModule_of_rank (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) (Z : C) (g : Z ⟶ X) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map g)).obj E) m) :
    𝔗.pull g ((𝔗.chernSeriesOfModule X E).coeff n) =
      (𝔗.chernSeries Z ((Scheme.Modules.pullback (S.map g)).obj E) m hm).coeff n := by
  rw [𝔗.coeff_chernSeriesOfModule X E hE n]
  exact 𝔗.pull_patchedCoeff X E hE n Z g m hm

/-- The `n`-th component of the total Chern class of a module lies in `A^n(X)`. -/
theorem coeff_chernSeriesOfModule_mem_grade (X : C) (E : (S.obj X).Modules) (n : ℕ) :
    (𝔗.chernSeriesOfModule X E).coeff n ∈ 𝔗.grade X n := by
  by_cases hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E
  · rw [𝔗.coeff_chernSeriesOfModule X E hE n]
    exact 𝔗.patchedCoeff_mem_grade X E hE n
  · rw [𝔗.chernSeriesOfModule_of_not X E hE]
    exact 𝔗.coeff_one_mem_grade X n

/-- **On a module of constant rank the arbitrary-rank total Chern class is the constant-rank
one.** -/
theorem chernSeriesOfModule_eq_chernSeries (X : C) (E : (S.obj X).Modules) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m) :
    𝔗.chernSeriesOfModule X E = 𝔗.chernSeries X E m hm := by
  refine UnitalCentralSeries.ext fun n => ?_
  rw [𝔗.coeff_chernSeriesOfModule X E hm.isFiniteLocallyFree n]
  refine 𝔗.eq_of_pull_one X E hm.isFiniteLocallyFree _ _ fun Z g hg m' hm' => ?_
  have hpm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map g)).obj E) m :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map g) E m hm
  rw [𝔗.pull_patchedCoeff X E hm.isFiniteLocallyFree n Z g m' hm',
    𝔗.pull_chernSeries_coeff X Z g E m hm hpm n,
    𝔗.chernSeries_eq_of_rank Z _ m' m hm' hpm]

/-- **The total Chern class is compatible with pullback**, which is property (2) of Tag 0FI5 at a
generator. The patching characterization holds along *every* morphism of `𝒞` making the rank
constant, so both sides restrict to the same constant-rank class. -/
theorem pull_coeff_chernSeriesOfModule (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) :
    𝔗.pull f ((𝔗.chernSeriesOfModule X E).coeff n) =
      (𝔗.chernSeriesOfModule X' ((Scheme.Modules.pullback (S.map f)).obj E)).coeff n := by
  have hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X').ringCatSheaf) ((Scheme.Modules.pullback (S.map f)).obj E) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (S.map f) E hE
  refine 𝔗.eq_of_pull_one X' _ hE' _ _ fun Z g hg m hm => ?_
  have hiso : (Scheme.Modules.pullback (S.map g)).obj
        ((Scheme.Modules.pullback (S.map f)).obj E) ≅
      (Scheme.Modules.pullback (S.map (g ≫ f))).obj E :=
    (Scheme.Modules.pullbackComp (S.map g) (S.map f)).app E ≪≫
      (Scheme.Modules.pullbackCongr (S.map_comp g f).symm).app E
  have hm2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map (g ≫ f))).obj E) m :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso hiso hm
  rw [← RingHom.comp_apply, ← 𝔗.pull_comp g f,
    𝔗.pull_coeff_chernSeriesOfModule_of_rank X E hE n Z (g ≫ f) m hm2,
    𝔗.pull_coeff_chernSeriesOfModule_of_rank X' _ hE' n Z g m hm,
    𝔗.chernSeries_eq_of_iso Z _ _ m m hm2 hm hiso.symm]

/-- **The total Chern class is multiplicative in every short exact sequence of finite locally free
modules**, with no restriction on the ranks: the loci where all three have constant rank separate
`A(X)`, the inclusions of those loci are flat, and there the sequence stays short exact and
`Stacks.WeilCohomology.Weak.ChernSituation.chernSeries_mul_of_shortExact` applies. -/
theorem chernSeriesOfModule_mul_of_shortExact (X : C) (T : ShortComplex (S.obj X).Modules)
    (hT : T.ShortExact)
    (h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) T.X₁)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) T.X₂)
    (h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) T.X₃) :
    𝔗.chernSeriesOfModule X T.X₂ =
      𝔗.chernSeriesOfModule X T.X₁ * 𝔗.chernSeriesOfModule X T.X₃ := by
  refine UnitalCentralSeries.ext fun n => ?_
  refine 𝔗.eq_of_pull_three X T.X₁ T.X₂ T.X₃ h₁ h₂ h₃ _ _ fun Z g hg m₁ m₂ m₃ hm₁ hm₂ hm₃ => ?_
  have := hg
  have key := 𝔗.chernSeries_mul_of_shortExact m₁ Z
    (T.map (Scheme.Modules.pullback (S.map g))) (shortExact_map_pullback (S.map g) T hT)
    m₂ m₃ hm₁ hm₂ hm₃
  have hr : 𝔗.pull g
        ((𝔗.chernSeriesOfModule X T.X₁ * 𝔗.chernSeriesOfModule X T.X₃).coeff n) =
      (𝔗.chernSeries Z ((Scheme.Modules.pullback (S.map g)).obj T.X₁) m₁ hm₁ *
        𝔗.chernSeries Z ((Scheme.Modules.pullback (S.map g)).obj T.X₃) m₃ hm₃).coeff n := by
    rw [UnitalCentralSeries.coeff_mul, map_sum, UnitalCentralSeries.coeff_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, 𝔗.pull_coeff_chernSeriesOfModule_of_rank X T.X₁ h₁ q.1 Z g m₁ hm₁,
      𝔗.pull_coeff_chernSeriesOfModule_of_rank X T.X₃ h₃ q.2 Z g m₃ hm₃]
  rw [𝔗.pull_coeff_chernSeriesOfModule_of_rank X T.X₂ h₂ n Z g m₂ hm₂, hr]
  exact congrArg (fun s => UnitalCentralSeries.coeff s n) key

/-! ### The rule on `K₀(Vect(X))` -/

/-- The total Chern class of a module which is not finite locally free, in the sense of
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, is `1`. -/
theorem chernSeriesOfModule_eq_one_of_not (X : C) (M : (S.obj X).Modules)
    (hM : ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) M) : 𝔗.chernSeriesOfModule X M = 1 :=
  𝔗.chernSeriesOfModule_of_not X M fun h =>
    hM ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mpr h)

/-- For an exact sequence `0 ⟶ ℰ ⟶ 𝓕 ⟶ 𝒢 ⟶ 0` of finite locally free modules,
`c^A(𝓕) = c^A(ℰ) c^A(𝒢)`. -/
theorem chernSeriesOfModule_mul (X : C) {E F G : (S.obj X).Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0)
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E)
    (hF : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) F)
    (hG : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) :
    𝔗.chernSeriesOfModule X F = 𝔗.chernSeriesOfModule X E * 𝔗.chernSeriesOfModule X G :=
  𝔗.chernSeriesOfModule_mul_of_shortExact X (ShortComplex.mk f g w)
    (ShortComplex.ShortExact.mk' hex hmono hepi)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry F).mp hF)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry G).mp hG)

/-- **The rule `c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` of Stacks Tag 0FI5**, as the family of its
components. On a generator it is the total Chern class of the module; the extension is the
universal property of the Grothendieck group, which applies because the target is a group and
`ℰ ↦ c^A(ℰ)` is multiplicative in short exact sequences. -/
def totalChernClass (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ) : 𝔗.A X :=
  (kZeroSeries (𝔗.chernSeriesOfModule X) (𝔗.chernSeriesOfModule_eq_one_of_not X)
    (fun f g w hE hF hG hmono hepi hex =>
      𝔗.chernSeriesOfModule_mul X f g w hE hF hG hmono hepi hex) α).coeff n

/-- On the class `[ℰ]` of a module, the rule is the total Chern class of `ℰ`. -/
theorem totalChernClass_classOf (X : C) (E : (S.obj X).Modules) (n : ℕ) :
    𝔗.totalChernClass X (VectorBundleKZero.classOf (S.obj X) E) n =
      (𝔗.chernSeriesOfModule X E).coeff n := by
  rw [totalChernClass, kZeroSeries_classOf]

/-- The rule is multiplicative: `c^A(α + β) = c^A(α) c^A(β)`, componentwise. -/
theorem totalChernClass_add (X : C) (α β : VectorBundleKZero (S.obj X)) (n : ℕ) :
    𝔗.totalChernClass X (α + β) n =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        𝔗.totalChernClass X α p.1 * 𝔗.totalChernClass X β p.2 := by
  rw [totalChernClass, kZeroSeries_add, UnitalCentralSeries.coeff_mul]
  rfl

/-- The rule is unital: `c^A(0) = 1`, componentwise. -/
theorem totalChernClass_zero (X : C) (n : ℕ) :
    𝔗.totalChernClass X 0 n = if n = 0 then 1 else 0 := by
  rw [totalChernClass, kZeroSeries_zero, UnitalCentralSeries.coeff_one]

/-- The `n`-th component of `c^A(α)` lies in `A^n(X)`. -/
theorem totalChernClass_mem_grade (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ) :
    𝔗.totalChernClass X α n ∈ 𝔗.grade X n := by
  have hmulG : ∀ (i j : ℕ) {x y : 𝔗.A X}, x ∈ 𝔗.grade X i → y ∈ 𝔗.grade X j →
      x * y ∈ 𝔗.grade X (i + j) := fun i j {_ _} hx hy => 𝔗.mul_mem X i j hx hy
  exact coeff_kZeroSeries_mem _ _ _ (𝔗.grade X) (𝔗.one_mem X) hmulG
    (fun M k => 𝔗.coeff_chernSeriesOfModule_mem_grade X M k) α n

/-- **The existence half of Stacks Tag 0FI5.** The rule
`Stacks.WeilCohomology.Weak.ChernSituation.totalChernClass` has the three properties of the
proposition: it is multiplicative on sums of classes and unital, compatible with pullback, and
takes the value `1 + c₁^A(ℒ)` on an invertible module; and its `n`-th component lies in
`A^n(X)`. -/
theorem isTotalChernClass_totalChernClass :
    IsTotalChernClass 𝔗.toChernSetup 𝔗.totalChernClass where
  mem_grade X α n := 𝔗.totalChernClass_mem_grade X α n
  map_add X α β n := 𝔗.totalChernClass_add X α β n
  map_zero X n := 𝔗.totalChernClass_zero X n
  map_pull {X Y} f E hE n := by
    rw [𝔗.totalChernClass_classOf Y E n, 𝔗.totalChernClass_classOf X _ n]
    exact 𝔗.pull_coeff_chernSeriesOfModule Y X f E hE n
  map_pull_kZero {X Y} f κ hκ α n := by
    have hz (k : ℕ) : 𝔗.pull f (if k = 0 then 1 else 0) = if k = 0 then 1 else 0 := by
      split_ifs <;> simp
    refine eq_of_convolutive_of_eq_classOf
      (c := fun β k => 𝔗.pull f (𝔗.totalChernClass Y β k))
      (c' := fun β k => 𝔗.totalChernClass X (κ β) k) ?_ ?_ ?_ ?_ ?_ α n
    · intro a b k
      rw [𝔗.totalChernClass_add Y a b k, map_sum]
      exact Finset.sum_congr rfl fun q _ => map_mul _ _ _
    · intro k
      rw [𝔗.totalChernClass_zero Y k]
      exact hz k
    · intro a b k
      rw [map_add, 𝔗.totalChernClass_add X (κ a) (κ b) k]
    · intro k
      rw [map_zero, 𝔗.totalChernClass_zero X k]
    · intro M k
      by_cases hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          (R := (S.obj Y).ringCatSheaf) M
      · rw [hκ M hM, 𝔗.totalChernClass_classOf Y M k, 𝔗.totalChernClass_classOf X _ k]
        exact 𝔗.pull_coeff_chernSeriesOfModule Y X f M hM k
      · rw [VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M
          (fun h => hM
            ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp h)),
          map_zero,
          𝔗.totalChernClass_zero Y k, 𝔗.totalChernClass_zero X k]
        exact hz k
  invertible X L hL n := by
    have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 := by
      have := hL
      infer_instance
    rw [𝔗.totalChernClass_classOf X L n, 𝔗.chernSeriesOfModule_eq_chernSeries X L 1 h1]
    exact 𝔗.chernSeries_coeff_invertible X L hL h1 n

/-! ### Uniqueness, and the proposition -/

/-- **The uniqueness half of Stacks Tag 0FI5, on all of `K₀(Vect(X))`.** A rule with the three
properties of the proposition is
`Stacks.WeilCohomology.Weak.ChernSituation.totalChernClass`.

Property (1) reduces this to the classes `[ℰ]` of modules, by
`Stacks.WeilCohomology.eq_of_convolutive_of_eq_classOf`; the loci where `ℰ` has constant rank
reduce it further to a module of constant rank, property (2) carrying both rules there; and there
it is `Stacks.WeilCohomology.eq_of_isTotalChernClassOnLocallyFree`, which the splitting principle
proves. -/
theorem eq_totalChernClass_of_isTotalChernClass
    {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔗.A X}
    (hc : IsTotalChernClass 𝔗.toChernSetup c) (X : C) (α : VectorBundleKZero (S.obj X))
    (n : ℕ) : c X α n = 𝔗.totalChernClass X α n := by
  refine eq_of_convolutive_of_eq_classOf (hc.map_add X) (hc.map_zero X)
    (𝔗.totalChernClass_add X) (𝔗.totalChernClass_zero X) (fun M k => ?_) α n
  by_cases hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) M
  · refine 𝔗.eq_of_pull_one X M hM _ _ fun Z g hg m hm => ?_
    rw [hc.map_pull g M hM k, 𝔗.totalChernClass_classOf X M k,
      𝔗.pull_coeff_chernSeriesOfModule X Z g M hM k, ← 𝔗.totalChernClass_classOf Z _ k]
    exact Stacks.WeilCohomology.Weak.eq_of_isTotalChernClass hc
      𝔗.isTotalChernClass_totalChernClass Z _ m hm k
  · rw [VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M
      (fun h => hM ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp h)),
      hc.map_zero X k, 𝔗.totalChernClass_zero X k]

/-- **Tag 0FI5 over the standing situation as a structure.** In the standing situation of
Section 45.12 there is a unique rule which assigns to every object `X` of `𝒞` a total Chern class

`c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`

such that (1) `c^A(α + β) = c^A(α) c^A(β)` and `c^A(0) = 1`, (2) `f^* ∘ c^A = c^A ∘ f^*` for a
morphism `f : X' ⟶ X` of `𝒞`, and (3) `c^A([ℒ]) = 1 + c₁^A(ℒ)` for `ℒ ∈ Pic(X)`.

The tag sits on `Stacks.WeilCohomology.existsUnique_isTotalChernClass_of_source`, which is this
statement with the three conditions of `Stacks.WeilCohomology.Weak.ChernSituation` spelled out as
hypotheses and the structure built inside the proof. -/
theorem existsUnique_isTotalChernClass :
    ∃! c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔗.A X,
      IsTotalChernClass 𝔗.toChernSetup c :=
  ⟨𝔗.totalChernClass, 𝔗.isTotalChernClass_totalChernClass, fun _c hc =>
    funext fun X => funext fun α => funext fun n =>
      𝔗.eq_totalChernClass_of_isTotalChernClass hc X α n⟩

end ChernSituation

/-! ### Tag 0FI5 in the source's own situation -/

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **Stacks Project, Tag 0FI5.** In the standing situation of Section 45.12 there is a unique
rule which assigns to every object `X` of `𝒞` a total Chern class

`c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`

such that (1) `c^A(α + β) = c^A(α) c^A(β)` and `c^A(0) = 1`, (2) `f^* ∘ c^A = c^A ∘ f^*` for a
morphism `f : X' ⟶ X` of `𝒞`, and (3) `c^A([ℒ]) = 1 + c₁^A(ℒ)` for `ℒ ∈ Pic(X)`.

**What the situation is.** `Stacks.WeilCohomology.Weak.ChernSetup` is the source's own standing
situation: the graded rings `A(X)` with the pullback ring maps and the additive
`c₁^A : Pic(X) ⟶ A¹(X)` — the data the source fixes — together with clause (1), clause (2),
clause (3)(a), condition (1), condition (2) and condition (4), and the grading
`A(X) = ⨁_{i ≥ 0} A^i(X)` as `isInternal_grade`. Every field of it is a datum or a condition the
source states; in particular `Stacks.WeilCohomology.Weak.ChernSetup.bundleDatum` — the projective
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
instead the theorem `Stacks.WeilCohomology.Weak.ChernSituation.chernSeries_eq_of_iso`, proved from
multiplicativity in the short exact sequence `0 ⟶ ℰ ⟶ ℰ' ⟶ 0 ⟶ 0`. The pseudofunctoriality
coherence isomorphism `h^*(g^*ℰ) ≅ (h ≫ g)^*ℰ`, which the source has for free by writing `f^*`
as a strict functor, is handled by the same theorem through
`Stacks.WeilCohomology.Weak.ChernSituation.pull_chernSeries_coeff_of_iso`.

The `Stacks.WeilCohomology.Weak.ChernSituation` the development is written over is assembled from
these inside the proof, so it is not an argument of this statement. Everything the source
derives rather than assumes is a theorem: condition (3) under an isomorphism of invertible
modules (`Stacks.WeilCohomology.Weak.ChernSituation.pull_c₁`), condition (4) read with the grading
(`Stacks.WeilCohomology.Weak.ChernSetup.mem_grade_of_bundleFormula`), the identifications of twists
along the two induced morphisms
(`Stacks.WeilCohomology.Weak.ChernSituation.exists_bundleCompare` and
`Stacks.WeilCohomology.Weak.ChernSituation.exists_divisorDatum`), and
`𝒪_P(𝐏(𝓕)) ≅ 𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}`
(`Stacks.WeilCohomology.BundleObject.twistClass_eq_picardClassOf_add`). -/
theorem existsUnique_isTotalChernClass_of_source (𝔚 : ChernSetup.{u, v, v₁, w} C S)
    (hpull : PullbackFirstChernCondition 𝔚) (hcompare : BundleCompareClause 𝔚)
    (hdivisor : DivisorDatumClause 𝔚) :
    ∃! c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X, IsTotalChernClass 𝔚 c :=
  ChernSituation.existsUnique_isTotalChernClass (chernSituationOfSource 𝔚 hpull hcompare hdivisor)

end Stacks.WeilCohomology.Weak

end
