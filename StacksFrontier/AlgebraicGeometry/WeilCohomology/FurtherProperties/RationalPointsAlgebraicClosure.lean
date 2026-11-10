module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FiniteFieldExtensionDivisibility
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.ProjectiveDivisorReduction
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.AlgClosedDivisiblePoints
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsSeparableDivisibility

/-!
# Stacks Tag 0FH7 through an algebraic closure

The proof of [Stacks, Tag 0FH7] reduces to a separably closed ground field and then runs a Bertini
argument there. The Bertini step of this library, namely
`Stacks.SectionsVanishingOnSubscheme.exists_projective_smooth_geometricallyIrreducible_curve_pair`,
is proved over an algebraically closed field. This file passes from the separable closure `F` to
its algebraic closure `F̄` and back, so that the Bertini step is used only where it is proved.

The way back is the push-pull formula. Divisibility of `[y] - [y']` by `n` over `F̄` descends to a
finite subextension `E/F` ([Stacks, Tag 0FH6]). Such an `E` is purely inseparable over the
separably closed `F`, so `[E : F]` is a power of the characteristic exponent, which is prime to
`n` because `n` is invertible. Then
`Stacks.Chow.exists_eq_zsmul_of_baseChangeChowPullbackOfIsPullback_eq_zsmul_of_isCoprime` gives
divisibility over `F` itself.

Over `F̄` the argument is the source's: a smooth projective curve through the two points (Bertini),
the curve case, and pushforward along the curve. Dimension zero is handled separately.

## Main results

* `Stacks.WeilCohomology.isCoprime_finrank_of_isSepClosed`: the degree of a finite extension of a
  separably closed field is prime to every integer invertible in it.
* `Stacks.WeilCohomology.rationalPointDifferenceDivisible_one_of_surjective`: the curve case over
  an algebraically closed field, from the Jacobian and a surjective `[n]`.
* `Stacks.WeilCohomology.exists_rationalPointChowClass_sub_eq_zsmul_of_isAlgClosed`: the
  divisibility over an algebraically closed field.
* `Stacks.WeilCohomology.exists_rationalPointChowClass_sub_eq_zsmul_of_isSepClosed`: the
  divisibility over a separably closed field.
* `Stacks.WeilCohomology.exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_projective`:
  the conclusion of [Stacks, Tag 0FH7], from the curve case.

## What this carries beyond the source

One hypothesis, `hcurve : Stacks.WeilCohomology.RationalPointDifferenceDivisible K n 1` for `K` the
algebraic closure of the separable closure of `k`: the curve case over an algebraically closed
field. In particular the Bertini hypothesis `Stacks.WeilCohomology.BertiniDivisorReduction` of
`Stacks.WeilCohomology.exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul` is no longer
carried, and the hypotheses on `X` are exactly the source's: projective, smooth and geometrically
irreducible.

`Stacks.WeilCohomology.rationalPointDifferenceDivisible_one_of_surjective` reduces the curve case
over an algebraically closed field to two inputs: the Jacobian of a smooth proper curve, as
`Stacks.WeilCohomology.HasJacobianParametrizations` (**Stacks Tag 0BA0**), and surjectivity of
multiplication by `n` on an abelian variety (**Stacks Tag 03RP**). Over an algebraically closed
field surjectivity is enough; étaleness is not needed
(`Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_surjective_of_isAlgClosed`).

No `@[stacks]` attribute is attached, because of the carried hypothesis.

## References

* [Stacks Project, Tag 0FH6](https://stacks.math.columbia.edu/tag/0FH6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-- **The degree of a finite extension of a separably closed field is prime to every integer
invertible in it.** Such an extension is purely inseparable, so its degree is a power of the
characteristic exponent `q`; and `q` is prime to `n`, since either `q = 1` or `q` is the
characteristic, which divides no integer invertible in the field. -/
theorem isCoprime_finrank_of_isSepClosed (F E : Type u) [Field F] [IsSepClosed F] [Field E]
    [Algebra F E] [FiniteDimensional F E] (n : ℤ) (hn : IsUnit (n : F)) :
    IsCoprime (Module.finrank F E : ℤ) n := by
  obtain ⟨m, hm⟩ := IsPurelyInseparable.finrank_eq_pow F E (ringExpChar F)
  rw [hm, Nat.cast_pow]
  refine IsCoprime.pow_left ?_
  have key : ∀ q : ℕ, ExpChar F q → IsCoprime (q : ℤ) n := by
    intro q hq
    cases hq with
    | zero => exact isCoprime_one_left
    | prime hp =>
      refine (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).2 fun hdvd => ?_
      rw [← CharP.intCast_eq_zero_iff F q n] at hdvd
      rw [hdvd] at hn
      exact not_isUnit_zero hn
  exact key _ inferInstance

open scoped CategoryTheory.MonObj in
/-- **The curve case of [Stacks, Tag 0FH7] over an algebraically closed field, from the Jacobian
and a surjective multiplication by `n`.** Let `K` be algebraically closed. If every smooth proper
curve over `K` has a Jacobian in the sense of `Stacks.WeilCohomology.HasJacobianParametrizations`,
and multiplication by `n` is surjective on every abelian variety over `K`, then the difference of
two rational points on a proper smooth geometrically irreducible curve is `n` times a class of
`CH_0`.

This is `Stacks.WeilCohomology.rationalPointDifferenceDivisible_one` with the étaleness of `[n]`
replaced by its surjectivity, which over an algebraically closed field already lifts rational
points (`Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_surjective_of_isAlgClosed`). -/
theorem rationalPointDifferenceDivisible_one_of_surjective (K : Type u) [Field K] [IsAlgClosed K]
    (n : ℤ)
    (hsurj : ∀ (A : Over (Spec (.of K))) [CategoryTheory.GrpObj A]
      [AlgebraicGeometry.IsAbelianVariety K A], Surjective ((𝟙 A : A ⟶ A) ^ n).left)
    (hJac : HasJacobianParametrizations K n) :
    RationalPointDifferenceDivisible K n 1 := by
  unfold RationalPointDifferenceDivisible
  intro X f _ _ _ hdim x x' hx hx'
  have hdimle : topologicalKrullDim X ≤ 1 := hdim.le
  have : SmoothOfRelativeDimension 1 f :=
    Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one K f hdim
  obtain ⟨c, hdeg, hc⟩ := exists_curvePicardToChowZero_eq_rationalPointChowClass_sub K f hdimle
    (curveHasOneDimensionalSections K f) x x' hx hx'
  obtain ⟨A, _, φ, hφsurj, hcompat⟩ := hJac f hdimle
  obtain ⟨g, hg, hφg⟩ := hφsurj c hdeg
  obtain ⟨g', hg'sec, hg'eq⟩ :=
    Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_surjective_of_isAlgClosed A.X n
      (hsurj A.X) g hg
  exact ⟨curvePicardToChowZero K f (φ g'), by
    rw [← hc, ← hφg, hcompat g g' hg hg'sec hg'eq, map_zsmul]⟩

/-- **The divisibility of [Stacks, Tag 0FH7] over an algebraically closed field, from the curve
case.** Let `K` be algebraically closed and `X` H-projective, smooth and geometrically irreducible
over `K` with two `K`-rational points. Then `[x] - [x']` is `n` times a class of `CH_0(X)`, granted
the curve case `hcurve`. -/
theorem exists_rationalPointChowClass_sub_eq_zsmul_of_isAlgClosed (K : Type u) [Field K]
    [IsAlgClosed K] (n : ℤ) (hcurve : RationalPointDifferenceDivisible K n 1)
    {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation K).S) [Smooth f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveMorphism f)
    (x x' : (fieldChowSituation K).S ⟶ X)
    (hx : x ≫ f = 𝟙 (fieldChowSituation K).S) (hx' : x' ≫ f = 𝟙 (fieldChowSituation K).S) :
    ∃ c : chowGroup (fieldChowSituation K) f 0,
      rationalPointChowClass K f x hx - rationalPointChowClass K f x' hx' = n • c := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  obtain ⟨d, hdim⟩ := exists_topologicalKrullDim_eq_natCast_of_isProper K f
    (Nonempty.map (fun p ↦ x.base p) inferInstance)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact rationalPointDifferenceDivisible_zero K n f hdim x x' hx hx'
  obtain ⟨C, ι, hι, hsm, hgi, hprojC, hdimC, xC, xC', hfac, hfac'⟩ :=
    Stacks.SectionsVanishingOnSubscheme.exists_projective_smooth_geometricallyIrreducible_curve_pair
      K d hd f hproj hdim x x' hx hx'
  have : IsProper (ι ≫ f) := isProper_of_isProjectiveMorphism _ hprojC
  have hxC : xC ≫ ι ≫ f = 𝟙 (fieldChowSituation K).S := by
    rwa [← Category.assoc, hfac]
  have hxC' : xC' ≫ ι ≫ f = 𝟙 (fieldChowSituation K).S := by
    rwa [← Category.assoc, hfac']
  obtain ⟨c, hc⟩ := hcurve (ι ≫ f) (by exact_mod_cast hdimC) xC xC' hxC hxC'
  exact ⟨chowPushforwardOfIsClosedImmersion (fieldChowSituation K) (ι ≫ f) f ι rfl 0 c,
    rationalPointChowClass_sub_eq_zsmul_chowPushforward K f (ι ≫ f) ι rfl xC xC' hxC hxC'
      x x' hfac hfac' hx hx' n c hc⟩

/-- A section of `f` pulls back to a section of the base change of `f` along `g`. -/
theorem exists_pullback_section_of_section {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (x : S ⟶ X) (hx : x ≫ f = 𝟙 S) :
    ∃ y : T ⟶ pullback f g, y ≫ pullback.snd f g = 𝟙 T ∧ y ≫ pullback.fst f g = g ≫ x :=
  ⟨pullback.lift (g ≫ x) (𝟙 _) (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

/-- **The divisibility of [Stacks, Tag 0FH7] over a separably closed field, from the curve case
over its algebraic closure.** -/
theorem exists_rationalPointChowClass_sub_eq_zsmul_of_isSepClosed (F : Type u) [Field F]
    [IsSepClosed F] (n : ℤ) (hn : IsUnit ((n : ℤ) : F))
    (hcurve : RationalPointDifferenceDivisible (AlgebraicClosure F) n 1)
    {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation F).S) [Smooth f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveMorphism f)
    (x x' : (fieldChowSituation F).S ⟶ X)
    (hx : x ≫ f = 𝟙 (fieldChowSituation F).S) (hx' : x' ≫ f = 𝟙 (fieldChowSituation F).S) :
    ∃ c : chowGroup (fieldChowSituation F) f 0,
      rationalPointChowClass F f x hx - rationalPointChowClass F f x' hx' = n • c := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  set K := AlgebraicClosure F
  set g := (fieldExtensionBaseChangeSituation F K).g
  obtain ⟨y, hy, hxy⟩ := exists_pullback_section_of_section f g x hx
  obtain ⟨y', hy', hxy'⟩ := exists_pullback_section_of_section f g x' hx'
  obtain ⟨γ, hγ⟩ := exists_rationalPointChowClass_sub_eq_zsmul_of_isAlgClosed K n hcurve
    (pullback.snd f g) (hproj.baseChange g) y y' hy hy'
  have hbc := baseChangeChowPullbackOfIsPullback_rationalPointChowClass_sub F K f
    (IsPullback.of_hasPullback f g) x hx x' hx' y hy hxy y' hy' hxy'
  have : QuasiCompact (Over.mk f).hom := (inferInstance : QuasiCompact f)
  have : LocallyOfFiniteType (Over.mk f).hom := (inferInstance : LocallyOfFiniteType f)
  have : CompactSpace ↥(Over.mk f).left :=
    QuasiCompact.compactSpace_of_compactSpace (Over.mk f).hom
  obtain ⟨E, δ, hδ⟩ := exists_finiteSubextension_baseChangeChowPullback_eq_zsmul F K (Over.mk f)
    0 n (rationalPointChowClass F f x hx - rationalPointChowClass F f x' hx') γ (hbc.trans hγ)
  have : FiniteDimensional F E.1 := E.2
  exact exists_eq_zsmul_of_baseChangeChowPullbackOfIsPullback_eq_zsmul_of_isCoprime F E.1 f 0 n
    (isCoprime_finrank_of_isSepClosed F E.1 n hn) _ δ hδ

/-- **The conclusion of [Stacks, Tag 0FH7], from the curve case.** Let `k` be a field, let `X` be
H-projective, smooth and geometrically irreducible over `k`, let `x, x'` be `k`-rational points
and let `n` be invertible in `k`. Then there is a finite separable extension `K/k` and a class `δ`
of `CH_0(X_K)` with the base change of `[x] - [x']` equal to `n δ`.

The carried hypothesis `hcurve` is the curve case over the algebraic closure of the separable
closure of `k`, as described in the module docstring. Stacks Tag 0FH7 is **not** registered here
because of it. -/
theorem exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_projective (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [Smooth f]
    [GeometricallyIrreducible f] (hproj : IsProjectiveMorphism f)
    (n : ℤ) (hn : IsUnit ((n : ℤ) : k))
    (hcurve : RationalPointDifferenceDivisible (AlgebraicClosure (SeparableClosure k)) n 1)
    (x x' : (fieldChowSituation k).S ⟶ X)
    (hx : x ≫ f = 𝟙 (fieldChowSituation k).S)
    (hx' : x' ≫ f = 𝟙 (fieldChowSituation k).S) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
        (_ : Algebra.IsSeparable k K)
        (δ : chowGroup (fieldChowSituation K)
          (pullback.snd f (fieldExtensionBaseChangeSituation k K).g) 0),
      baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl f
          (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k K).g) 0
          (rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx') = n • δ := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  set F := SeparableClosure k
  set g := (fieldExtensionBaseChangeSituation k F).g
  have hnF : IsUnit ((n : ℤ) : F) := by simpa using hn.map (algebraMap k F)
  obtain ⟨y, hy, hxy⟩ := exists_pullback_section_of_section f g x hx
  obtain ⟨y', hy', hxy'⟩ := exists_pullback_section_of_section f g x' hx'
  obtain ⟨γ, hγ⟩ := exists_rationalPointChowClass_sub_eq_zsmul_of_isSepClosed F n hnF hcurve
    (pullback.snd f g) (hproj.baseChange g) y y' hy hy'
  have hbc := baseChangeChowPullbackOfIsPullback_rationalPointChowClass_sub k F f
    (IsPullback.of_hasPullback f g) x hx x' hx' y hy hxy y' hy' hxy'
  have : QuasiCompact (Over.mk f).hom := (inferInstance : QuasiCompact f)
  have : LocallyOfFiniteType (Over.mk f).hom := (inferInstance : LocallyOfFiniteType f)
  have : CompactSpace ↥(Over.mk f).left :=
    QuasiCompact.compactSpace_of_compactSpace (Over.mk f).hom
  exact exists_finiteSeparable_baseChangeChowPullback_eq_zsmul k (Over.mk f) 0 n
    (rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx') γ (hbc.trans hγ)

end Stacks.WeilCohomology

end
