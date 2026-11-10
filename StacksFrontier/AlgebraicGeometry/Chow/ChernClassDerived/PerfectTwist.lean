module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristicRank

/-!
# The Chern classes of a perfect object twisted by an invertible module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `E` be a perfect object of `D(𝒪_X)` whose Chern classes are defined and
which has constant rank `r`, and let `ℒ` be an invertible `𝒪_X`-module. Then

  `c_i(E ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j}(E) c_1(ℒ)^j`.

## Main results

* `Stacks.Chow.perfectChernClass_derivedTwist_apply` — this formula, degreewise.
* `Stacks.Chow.perfectChernClass_derivedTwist` — the same for total classes:
  `c(E ⊗ ℒ) = T_{r, c_1(ℒ)}(c(E))`, with `T_{r,x}` the twist
  `Stacks.Chow.TotalChowClass.twist`.
* `Stacks.Chow.complexChern_twistComplex` — the formula for the total Chern class of a locally
  bounded complex of finite locally free modules of alternating rank `r`.
* `Stacks.Chow.EnvelopePresentation.finsum_rank_eq` — the alternating rank of a presenting
  complex is the rank of the object.
* `Stacks.Chow.TotalChowClass.res_twist` — restriction commutes with the twist.
* `Stacks.Chow.TotalChowClass.res_firstChernTotal` — the restriction of `c_1(ℒ)` along `h` is
  `c_1(h^*ℒ)`.

## References

* [Stacks Project, Tag 0FAF](https://stacks.math.columbia.edu/tag/0FAF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']

/-- Restriction commutes with taking a homogeneous component. -/
theorem res_homComponent (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') (i : ℕ)
    (c : TotalChowClass C sY) : res h hs (homComponent i c) = homComponent i (res h hs c) := by
  subst hs
  refine ext fun p ↦ ?_
  rw [res_rfl_apply, homComponent_apply, homComponent_apply, res_rfl_apply]
  split_ifs
  · rfl
  · exact map_zero _

/-- Restriction commutes with forming a series. -/
theorem res_series (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (f : ℕ → TotalChowClass C sY) : res h hs (series f) = series fun m ↦ res h hs (f m) := by
  subst hs
  refine ext fun p ↦ ?_
  rw [res_rfl_apply, series_apply, series_apply, res_rfl_apply]

/-- The degree-`i` component of a twist:
`T_{r,x}(c)_i = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j} x^j`, with `c_{i-j}` the homogeneous
component of `c` of degree `i - j`. -/
theorem twist_apply_apply (r : ℤ) (x c : TotalChowClass C sY) (i : ℕ) :
    twist r x c i = ∑ j ∈ range (i + 1),
      Ring.choose (r - i + j) j • (homComponent (i - j) c * x ^ j) i := by
  rw [twist_apply, series_apply, sum_apply]
  rfl

/-- **Restriction commutes with the twist** `T_{r,x}`. -/
theorem res_twist (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') (r : ℤ)
    (x c : TotalChowClass C sY) :
    res h hs (twist r x c) = twist r (res h hs x) (res h hs c) := by
  rw [twist_apply, twist_apply, res_series]
  congr 1
  funext m
  simp only [map_sum, map_zsmul, map_mul, map_pow, res_homComponent]

end TotalChowClass

namespace TotalChowClass

section FirstChern

variable (C : ChowSituation.{u}) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]

/-- The first Chern class of an invertible module, as a total class, is the degree-`1` part of
its total Chern class `c(ℒ) = 1 + c_1(ℒ)`. -/
theorem firstChernTotal_eq_homComponent_totalChern :
    letI := isFiniteLocallyFreeOfRank_one_of_isInvertible L
    firstChernTotal C sY L = homComponent 1 (totalChern C sY L 1) := by
  let := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  refine ext fun p ↦ ?_
  rw [homComponent_apply]
  by_cases hp : p = 1
  · subst hp
    rw [ite_eq_left rfl, firstChernTotal_apply_one]
    exact (totalChern_apply C sY L 1 1).symm
  · rw [ite_eq_right hp, firstChernTotal_apply_of_ne C sY L hp]

/-- **Restriction of the first Chern class**: the restriction of `c_1(ℒ)` along `h : Y' ⟶ Y` is
`c_1(h^*ℒ)`. -/
theorem res_firstChernTotal {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') :
    haveI := isInvertible_pullback h L
    res h hs (firstChernTotal C sY L) =
      firstChernTotal C sY' ((Scheme.Modules.pullback h).obj L) := by
  have := isInvertible_pullback h L
  let := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  rw [firstChernTotal_eq_homComponent_totalChern, firstChernTotal_eq_homComponent_totalChern,
    res_homComponent, res_totalChern]

end FirstChern

end TotalChowClass

/-! ### The rank of a perfect object on the rank loci of a presentation -/

section Rank

variable {X : Scheme.{u}} {E : DerivedCategory X.Modules}

/-- **The alternating rank of a presentation is the rank of the object.** Let `E` be a
pseudo-coherent object of `D(𝒪_X)` of constant rank `r` (its derived-fibre Euler characteristic)
and let `(f, 𝓔^•)` be an envelope presentation of `E`. On every nonempty rank locus `Y_ρ` of
`𝓔^•` the alternating sum `∑_n (-1)^n ρ(n)` of the ranks of the terms is `r`. -/
theorem EnvelopePresentation.finsum_rank_eq (H : EnvelopePresentation E)
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (r : ℤ)
    (hr : ∀ x : X, DerivedFibreBetti.chiDerivedFibre X E hpc x = r) (ρ : ℤ →₀ ℕ)
    (hρ : (complexRankLocus H.locallyBounded ρ : Set H.Y).Nonempty) :
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ n : ℤ) = r := by
  obtain ⟨y, hy⟩ := hρ
  have : Nonempty (complexRankLocus H.locallyBounded ρ).toScheme := ⟨⟨y, hy⟩⟩
  have hrank := isFiniteLocallyFreeOfRank_complexRankLocus H.locallyBounded ρ
  refine DerivedFibreBetti.finsum_rank_eq_of_derivedPullback_iso E hpc r hr
    ((complexRankLocus H.locallyBounded ρ).ι ≫ H.f)
    (pullbackComplex (complexRankLocus H.locallyBounded ρ).ι H.P) ?_ ρ hrank
    (H.pullbackRepresentation _)
  refine ρ.support.finite_toSet.subset fun n hn ↦ ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  have := hrank n
  rw [h0] at this
  exact hn (isZero_of_isFiniteLocallyFreeOfRank_zero _)

end Rank

/-! ### The twist of the total Chern class of a locally bounded complex -/

section ComplexTwist

variable {Y : Scheme.{u}} {P : CochainComplex Y.Modules ℤ} (M : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

/-- Tensoring a finite locally free module with an invertible module preserves its rank. -/
private theorem isFiniteLocallyFreeOfRank_tensor_of_isInvertible {Z : Scheme.{u}} {F : Z.Modules}
    {n : ℕ} (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F n)
    (L : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).obj F).obj L) n := by
  simpa using isFiniteLocallyFreeOfRank_tensor hF (isFiniteLocallyFreeOfRank_one_of_isInvertible L)

/-- Twisting by an invertible module and pulling back preserve the ranks of the terms. -/
theorem isFiniteLocallyFreeOfRank_pullbackComplex_twistComplex {Y' : Scheme.{u}} (h : Y' ⟶ Y)
    (ρ : ℤ → ℕ)
    (hρ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex h P).X n) (ρ n)) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex h (twistComplex P M)).X n) (ρ n) := by
  have := isInvertible_pullback h M
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (sheafTensorPullbackIso h (P.X n) M).symm
    (isFiniteLocallyFreeOfRank_tensor_of_isInvertible (hρ n) _)

end ComplexTwist

/-- **The twist of the total Chern class of a locally bounded complex.** Let `P` be a locally
bounded complex of finite locally free `𝒪_Y`-modules whose alternating rank is `r` on every
nonempty rank locus, and let `ℳ` be invertible. Then `c(P ⊗ ℳ) = T_{r, c_1(ℳ)}(c(P))`. -/
theorem complexChern_twistComplex (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] (r : ℤ)
    (hr : ∀ ρ : ℤ →₀ ℕ, (complexRankLocus hP ρ : Set Y).Nonempty →
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ n : ℤ) = r) :
    complexChern C sY (isLocallyBoundedFiniteLocallyFree_twistComplex hP M) =
      TotalChowClass.twist r (TotalChowClass.firstChernTotal C sY M) (complexChern C sY hP) := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
  have := isInvertible_pullback (complexRankLoci hP ρ).ι M
  have hρ := isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down
  rw [res_complexChern_eq_complexChernBounded C sY _ _ rfl ρ.down
      (isFiniteLocallyFreeOfRank_pullbackComplex_twistComplex M _ ρ.down hρ),
    TotalChowClass.res_twist, TotalChowClass.res_firstChernTotal,
    res_complexChern_complexRankLocus]
  rcases (complexRankLocus hP ρ.down : Set Y).eq_empty_or_nonempty with he | hne
  · have : IsEmpty (complexRankLoci hP ρ).toScheme :=
      ⟨fun y ↦ (Set.eq_empty_iff_forall_notMem.1 he) y.1 y.2⟩
    exact (TotalChowClass.subsingleton_of_isEmpty _).elim _ _
  · have hρM : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((twistComplex (pullbackComplex (complexRankLoci hP ρ).ι P)
          ((Scheme.Modules.pullback (complexRankLoci hP ρ).ι).obj M)).X n) (ρ.down n) :=
      fun n ↦ isFiniteLocallyFreeOfRank_tensor_of_isInvertible (hρ n) _
    rw [← hr ρ.down hne, ← TotalChowClass.complexChernBounded_twistComplex C _ _ _ ρ.down hρ hρM]
    exact complexChernBounded_congr C _ _ (fun n ↦ sheafTensorPullbackIso _ (P.X n) M) _ _ _ _

/-! ### The Chern classes of a twisted perfect object -/

section Twist

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E : DerivedCategory X.Modules} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The total Chern class of a twist.** For a perfect object `E` of `D(𝒪_X)` of constant rank
`r` whose Chern classes are defined and an invertible `𝒪_X`-module `ℒ`,
`c(E ⊗ ℒ) = T_{r, c_1(ℒ)}(c(E))`. -/
theorem perfectChernClass_derivedTwist (perfect : RingedSpace.IsPerfect.{u, u + 1} E)
    (definedChernClasses : HasDefinedChernClasses E) (r : ℤ)
    (constantRank : ∀ x : X, DerivedFibreBetti.chiDerivedFibre X E
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect) x = r) :
    perfectChernClass C sX (hasDefinedChernClasses_derivedTwist definedChernClasses L) =
      TotalChowClass.twist r (TotalChowClass.firstChernTotal C sX L)
        (perfectChernClass C sX definedChernClasses) := by
  set H := definedChernClasses.some
  have := isInvertible_pullback H.f L
  refine (eq_perfectChernClass C sX _ (H.twist L) ?_).symm
  change TotalChowClass.res H.f rfl _ =
    complexChern C (H.f ≫ sX) (isLocallyBoundedFiniteLocallyFree_twistComplex H.locallyBounded _)
  rw [TotalChowClass.res_twist, TotalChowClass.res_firstChernTotal,
    res_perfectChernClass C sX definedChernClasses H]
  exact (complexChern_twistComplex C _ H.locallyBounded _ r fun ρ hρ ↦
    H.finsum_rank_eq _ r constantRank ρ hρ).symm

/-- **The Chern classes of a twist.** Let `X` be locally of finite type over the base of
chapter 42, let `E` be a perfect object of `D(𝒪_X)` whose Chern classes are defined and which has
constant rank `r`, and let `ℒ` be an invertible `𝒪_X`-module. Then

  `c_i(E ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j}(E) c_1(ℒ)^j`

in `A^i(X)`, where `c_{i-j}(E)` is the component of degree `i - j` of the total Chern class and
the product is that of Chow cohomology. -/
@[stacks 0FAF]
theorem perfectChernClass_derivedTwist_apply (perfect : RingedSpace.IsPerfect.{u, u + 1} E)
    (definedChernClasses : HasDefinedChernClasses E) (r : ℤ)
    (constantRank : ∀ x : X, DerivedFibreBetti.chiDerivedFibre X E
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect) x = r) (i : ℕ) :
    perfectChernClass C sX (hasDefinedChernClasses_derivedTwist definedChernClasses L) i =
      ∑ j ∈ range (i + 1), Ring.choose (r - i + j) j •
        (TotalChowClass.homComponent (i - j) (perfectChernClass C sX definedChernClasses) *
          TotalChowClass.firstChernTotal C sX L ^ j) i := by
  rw [perfectChernClass_derivedTwist C sX L perfect definedChernClasses r constantRank,
    TotalChowClass.twist_apply_apply]

end Twist

end Stacks.Chow

end
