module

public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsAlgebraicClosure
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsCurveJacobian

/-!
# Stacks 0FH7 from the Jacobian of projective curves

`Stacks.WeilCohomology.exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_projective`
reduces [Stacks, Tag 0FH7] to the curve case over the algebraic closure of the separable closure,
for *proper* curves. The argument only ever applies the curve case to the curve produced by the
Bertini step, which is *projective*. This file records that: the curve case is needed, and is
consumed, only for projective curves, in the form
`Stacks.WeilCohomology.HasProjectiveJacobianParametrizations` of the Jacobian input.

This matters because the Jacobian of [Stacks, Tag 0BA0] is constructed for smooth *projective*
curves (the Hilbert schemes of points and the ample twists of [Stacks, Tag 0B9Y] use
projectivity), while the passage from proper to projective for curves ([Stacks, Tag 0A26]) is
not unconditional in this library.

## Main definitions

* `Stacks.WeilCohomology.HasProjectiveJacobianParametrizations` — the Jacobian input for
  projective curves.

## Main results

* `exists_rationalPointChowClass_sub_eq_zsmul_of_isAlgClosed_of_projectiveJacobian` and
  `exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_projectiveJacobian` — the
  divisibility of [Stacks, Tag 0FH7] from the projective Jacobian input.

## References

* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.WeilCohomology

/-- **The Jacobian input for projective curves**: `JacobianParametrization k n f _` for every
projective smooth geometrically irreducible `k`-scheme of dimension one. -/
def HasProjectiveJacobianParametrizations (k : Type u) [Field k] (n : ℤ) : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    [GeometricallyIrreducible f], IsProjectiveMorphism f →
    ∀ (hdim : topologicalKrullDim X = (1 : WithBot ℕ∞)), JacobianParametrization k n f hdim.le

/-- A section `x` of `f` lifts along `g` to a section of the base change `pullback.snd f g`. -/
private theorem exists_section_pullback_snd {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (x : S ⟶ X) (hx : x ≫ f = 𝟙 S) :
    ∃ y : T ⟶ pullback f g, y ≫ pullback.snd f g = 𝟙 T ∧ y ≫ pullback.fst f g = g ≫ x :=
  ⟨pullback.lift (g ≫ x) (𝟙 _) (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

/-- The curve case for a projective curve, from the projective Jacobian input and surjectivity
of `[n]`. -/
theorem exists_rationalPointChowClass_sub_eq_zsmul_curve (K : Type u) [Field K] [IsAlgClosed K]
    (n : ℤ)
    (hsurj : ∀ (A : Over (Spec (.of K))) [CategoryTheory.GrpObj A]
      [AlgebraicGeometry.IsAbelianVariety K A], Surjective ((𝟙 A : A ⟶ A) ^ n).left)
    (hJac : HasProjectiveJacobianParametrizations K n)
    {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation K).S) [IsProper f] [Smooth f]
    [GeometricallyIrreducible f] (hproj : IsProjectiveMorphism f)
    (hdim : topologicalKrullDim X = (1 : WithBot ℕ∞))
    (x x' : (fieldChowSituation K).S ⟶ X)
    (hx : x ≫ f = 𝟙 (fieldChowSituation K).S) (hx' : x' ≫ f = 𝟙 (fieldChowSituation K).S) :
    ∃ c : chowGroup (fieldChowSituation K) f 0,
      rationalPointChowClass K f x hx - rationalPointChowClass K f x' hx' = n • c := by
  have hdimle : topologicalKrullDim X ≤ 1 := by rw [hdim]
  have : SmoothOfRelativeDimension 1 f :=
    Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one K f
      (by exact_mod_cast hdim)
  obtain ⟨c, hdeg, hc⟩ := exists_curvePicardToChowZero_eq_rationalPointChowClass_sub K f hdimle
    (curveHasOneDimensionalSections K f) x x' hx hx'
  obtain ⟨A, hAV, φ, hφsurj, hcompat⟩ := hJac f hproj hdim
  have := hAV
  obtain ⟨g, hg, hφg⟩ := hφsurj c hdeg
  have : LocallyOfFiniteType A.X.hom := inferInstance
  obtain ⟨g', hg'sec, hg'eq⟩ :=
    Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_surjective_of_isAlgClosed A.X n
      (hsurj A.X) g hg
  exact ⟨curvePicardToChowZero K f (φ g'), by
    rw [← hc, ← hφg, hcompat g g' hg hg'sec hg'eq, map_zsmul]⟩

/-- **The divisibility of [Stacks, Tag 0FH7] over an algebraically closed field, from the
projective Jacobian input.** -/
theorem exists_rationalPointChowClass_sub_eq_zsmul_of_isAlgClosed_of_projectiveJacobian
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℤ)
    (hsurj : ∀ (A : Over (Spec (.of K))) [CategoryTheory.GrpObj A]
      [AlgebraicGeometry.IsAbelianVariety K A], Surjective ((𝟙 A : A ⟶ A) ^ n).left)
    (hJac : HasProjectiveJacobianParametrizations K n)
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
  obtain ⟨C, ιC, hιC, hsm, hgi, hprojC, hdimC, xC, xC', hfac, hfac'⟩ :=
    Stacks.SectionsVanishingOnSubscheme.exists_projective_smooth_geometricallyIrreducible_curve_pair
      K d hd f hproj hdim x x' hx hx'
  have : IsProper (ιC ≫ f) := isProper_of_isProjectiveMorphism _ hprojC
  have hxC : xC ≫ ιC ≫ f = 𝟙 (fieldChowSituation K).S := by
    rw [← Category.assoc, hfac]; exact hx
  have hxC' : xC' ≫ ιC ≫ f = 𝟙 (fieldChowSituation K).S := by
    rw [← Category.assoc, hfac']; exact hx'
  obtain ⟨c, hc⟩ := exists_rationalPointChowClass_sub_eq_zsmul_curve K n hsurj hJac (ιC ≫ f) hprojC
    hdimC xC xC' hxC hxC'
  exact ⟨chowPushforwardOfIsClosedImmersion (fieldChowSituation K) (ιC ≫ f) f ιC rfl 0 c,
    rationalPointChowClass_sub_eq_zsmul_chowPushforward K f (ιC ≫ f) ιC rfl xC xC' hxC hxC'
      x x' hfac hfac' hx hx' n c hc⟩

/-- **The divisibility of [Stacks, Tag 0FH7] over a separably closed field**, from the projective
Jacobian input over its algebraic closure. -/
theorem exists_rationalPointChowClass_sub_eq_zsmul_of_isSepClosed_of_projectiveJacobian
    (F : Type u) [Field F]
    [IsSepClosed F] (n : ℤ) (hn : IsUnit ((n : ℤ) : F))
    (hsurj : ∀ (A : Over (Spec (.of (AlgebraicClosure F)))) [CategoryTheory.GrpObj A]
      [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure F) A],
      Surjective ((𝟙 A : A ⟶ A) ^ n).left)
    (hJac : HasProjectiveJacobianParametrizations (AlgebraicClosure F) n)
    {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation F).S) [Smooth f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveMorphism f)
    (x x' : (fieldChowSituation F).S ⟶ X)
    (hx : x ≫ f = 𝟙 (fieldChowSituation F).S) (hx' : x' ≫ f = 𝟙 (fieldChowSituation F).S) :
    ∃ c : chowGroup (fieldChowSituation F) f 0,
      rationalPointChowClass F f x hx - rationalPointChowClass F f x' hx' = n • c := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  set K := AlgebraicClosure F
  set g := (fieldExtensionBaseChangeSituation F K).g
  obtain ⟨y, hy, hxy⟩ := exists_section_pullback_snd f g x hx
  obtain ⟨y', hy', hxy'⟩ := exists_section_pullback_snd f g x' hx'
  obtain ⟨γc, hγc⟩ :=
    exists_rationalPointChowClass_sub_eq_zsmul_of_isAlgClosed_of_projectiveJacobian K n hsurj hJac
    (pullback.snd f g) (hproj.baseChange g) y y' hy hy'
  have hbc := baseChangeChowPullbackOfIsPullback_rationalPointChowClass_sub F K f
    (IsPullback.of_hasPullback f g) x hx x' hx' y hy hxy y' hy' hxy'
  have : QuasiCompact (Over.mk f).hom := (inferInstance : QuasiCompact f)
  have : LocallyOfFiniteType (Over.mk f).hom := (inferInstance : LocallyOfFiniteType f)
  have : CompactSpace ↥(Over.mk f).left :=
    QuasiCompact.compactSpace_of_compactSpace (Over.mk f).hom
  obtain ⟨E, δ, hδ⟩ := exists_finiteSubextension_baseChangeChowPullback_eq_zsmul F K (Over.mk f)
    0 n (rationalPointChowClass F f x hx - rationalPointChowClass F f x' hx') γc (hbc.trans hγc)
  have : FiniteDimensional F E.1 := E.2
  exact exists_eq_zsmul_of_baseChangeChowPullbackOfIsPullback_eq_zsmul_of_isCoprime F E.1 f 0 n
    (isCoprime_finrank_of_isSepClosed F E.1 n hn) _ δ hδ

/-- **The conclusion of [Stacks, Tag 0FH7], from the projective Jacobian input.** Let `k` be a
field, let `X` be H-projective, smooth and geometrically irreducible over `k`, let `x, x'` be
`k`-rational points and let `n` be invertible in `k`. Then there is a finite separable extension
`K/k` and a class `δ` of `CH_0(X_K)` with the base change of `[x] - [x']` equal to `n δ`, granted
surjectivity of `[n]` on abelian varieties and the Jacobian of projective curves over the algebraic
closure of the separable closure of `k`. -/
theorem exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_projectiveJacobian
    (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [Smooth f]
    [GeometricallyIrreducible f] (hproj : IsProjectiveMorphism f)
    (n : ℤ) (hn : IsUnit ((n : ℤ) : k))
    (hsurj : ∀ (A : Over (Spec (.of (AlgebraicClosure (SeparableClosure k)))))
      [CategoryTheory.GrpObj A]
      [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure (SeparableClosure k)) A],
      Surjective ((𝟙 A : A ⟶ A) ^ n).left)
    (hJac : HasProjectiveJacobianParametrizations (AlgebraicClosure (SeparableClosure k)) n)
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
  have hnF : IsUnit ((n : ℤ) : F) := by
    rw [← map_intCast (algebraMap k F) n]
    exact hn.map _
  obtain ⟨y, hy, hxy⟩ := exists_section_pullback_snd f g x hx
  obtain ⟨y', hy', hxy'⟩ := exists_section_pullback_snd f g x' hx'
  obtain ⟨γc, hγc⟩ :=
    exists_rationalPointChowClass_sub_eq_zsmul_of_isSepClosed_of_projectiveJacobian F n hnF hsurj
      hJac (pullback.snd f g) (hproj.baseChange g) y y' hy hy'
  have hbc := baseChangeChowPullbackOfIsPullback_rationalPointChowClass_sub k F f
    (IsPullback.of_hasPullback f g) x hx x' hx' y hy hxy y' hy' hxy'
  have : QuasiCompact (Over.mk f).hom := (inferInstance : QuasiCompact f)
  have : LocallyOfFiniteType (Over.mk f).hom := (inferInstance : LocallyOfFiniteType f)
  have : CompactSpace ↥(Over.mk f).left :=
    QuasiCompact.compactSpace_of_compactSpace (Over.mk f).hom
  exact exists_finiteSeparable_baseChangeChowPullback_eq_zsmul k (Over.mk f) 0 n
    (rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx') γc (hbc.trans hγc)

end Stacks.WeilCohomology

end
