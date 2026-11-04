module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Existence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Complete dévissages of a finite type module on an algebraic space

Let `X ⟶ Y` be a finite type morphism of algebraic spaces over a scheme `S`, let `F` be a
finite type quasi-coherent `𝒪_X`-module and let `y` be a point of `Y`. Stacks 0CWJ asserts
that there are an étale morphism `(Y', y') ⟶ (Y, y)` with `Y'` an affine scheme and finitely
many étale morphisms `hᵢ : Wᵢ ⟶ X_{Y'}` whose images cover the fibre `|(X_{Y'})_{y'}|`, such
that the pullback of `F` to each `Wᵢ` has a complete dévissage over `y'`.

The source's proof is a reduction to the scheme-level statement Stacks 05HU: the question is
étale local on `Y`, so one may assume `Y` affine; then `X` is quasi-compact, so it has a
surjective étale cover by an affine scheme `X'`; and Stacks 05HU applied to `X' ⟶ Y` and the
pullback of `F` to `X'` gives the conclusion.

`AlgebraicGeometry.Space.exists_affineChart_hasCompleteDevissageCover` carries out that
reduction, from the source's hypotheses and no others. It produces, from the spaces-level data,
an affine object `Y₁` of the site with an
étale morphism `q : Y₁ ⟶ Y` through the prescribed point, an étale chart `U` of `X` whose
scheme is affine and which is *surjective* onto the base change `X ×_Y Y₁`, a morphism of the
site from `U` to `Y₁` which is of finite type and quasi-compact as a morphism of schemes, and
finally the whole conclusion of Stacks 05HU for that morphism of schemes and for the
restriction of `F` to `U`.

## Main definitions

* `AlgebraicGeometry.HasCompleteDevissageCover` names the conclusion of Stacks 05HU for a
  morphism of schemes and a module on its source: an elementary étale neighbourhood of the
  base point together with finitely many étale morphisms covering the fibre, each carrying a
  complete dévissage of the pullback of the module.

## Main results

* `AlgebraicGeometry.hasCompleteDevissageCover`: Stacks 05HU, repackaged as
  `AlgebraicGeometry.HasCompleteDevissageCover`.
* `AlgebraicGeometry.Space.exists_affineChart_hasCompleteDevissageCover`: Stacks 0CWJ,
  delivered at an affine étale chart of the base change of `X` to an affine étale chart of the
  target at the prescribed point.

## Implementation notes

**The hypotheses are the source's.** Quasi-coherence of `F` is
`SheafOfModules.IsQuasicoherentOnSite` on the small étale site of `X` and finite type of `F` is
`SheafOfModules.IsFiniteTypeOnSite` there, which are the notions Stacks 05VR applies to a module
on an algebraic space. Stacks 05HU is applied to the restriction of `F` to the affine étale chart
`U`, and the quasi-coherence and the finite type of that restriction are *derived* from those two
conditions on `F`: the first is
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart` and the second is
`AlgebraicGeometry.Space.isFiniteType_restrictToChart`, which holds at every étale scheme chart
and needs no affineness of the chart. Nothing about the chart restrictions is assumed.

**Why the conclusion is stated at the chart.** The objects of the big fppf site of `S` are
size-bounded schemes, and the schemes Stacks 05HU produces — the elementary étale neighbourhood
`Y'` of the base point and the sources `Wᵢ` of the covering étale morphisms — carry no size bound
at all. They are therefore not objects of the site, `yoneda.obj Wᵢ` is not available, and neither
the morphisms `Wᵢ ⟶ X_{Y'}` nor the inclusion `|(X_{Y'})_{y'}| ⊆ ⋃ hᵢ(Wᵢ)` of the source's
conclusion can be written down as morphisms of algebraic spaces in this development. What is
available, and what is delivered here, is the scheme-level conclusion
`AlgebraicGeometry.HasCompleteDevissageCover` for the affine chart `U` of `X ×_Y Y₁`, together
with the surjectivity of `U` onto `X ×_Y Y₁` — which is what turns the covering statement at the
chart into the covering statement of the source, once the two can be compared.

**The family of the source's conclusion is not dropped.** The morphisms `hᵢ : Wᵢ ⟶ X_{Y'}`,
`i = 1, …, n`, their complete dévissages and the inclusion of the fibre in the union of their
images are all bound inside `AlgebraicGeometry.HasCompleteDevissageCover`, which quantifies over
`n : ℕ` and over a family `W : Fin n → Scheme` of schemes. The single chart `U` of the conclusion
below is not that family with `n = 1`; it is the affine surjective étale cover `X'` of `X_{Y'}`
which the source's own proof chooses before invoking Stacks 05HU, delivered here as part of the
statement because the comparison of the chart with `X_{Y'}` is what the covering clause has to
be read through.

Everything else in the source's reduction is proved. The affine étale chart of `Y` at `y` is
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`, which is exactly the licence for
"we may assume `Y` is an affine scheme". Quasi-compactness of `X ×_Y Y₁` is read off the
quasi-compactness half of the finite type hypothesis applied to the representable presheaf of
the affine `Y₁`, and the affine surjective étale cover of a quasi-compact algebraic space is
Stacks 03H6. That the resulting morphism of schemes is locally of finite type is the
commuting square of étale charts `(U, Y₁)` fed to the finite type hypothesis in its
every-étale-chart form of Stacks 03XF part (1); that it is quasi-compact holds because both
schemes are affine.

## References

* [Stacks Project, Tag 0CWJ](https://stacks.math.columbia.edu/tag/0CWJ)
* [Stacks Project, Tag 05HU](https://stacks.math.columbia.edu/tag/05HU)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The conclusion of Stacks 05HU -/

/-- The conclusion of **Stacks Project, Tag 05HU** for a morphism of schemes `g : Z ⟶ T`, a
module `G` on `Z` and a point `t` of `T`: there are an elementary étale neighbourhood
`(T', t') ⟶ (T, t)` and finitely many étale morphisms `hᵢ : Wᵢ ⟶ Z ×_T T'` whose images cover
the fibre of `Z ×_T T'` over `t'`, such that the pullback of `G` to each `Wᵢ` has a complete
dévissage along `Wᵢ ⟶ T'` over `t'`.

No finiteness hypothesis on `g` or on `G` appears: the finiteness needed to *state* the
complete dévissages is existentially bound inside, and the finiteness needed to *produce* them
is the hypothesis of `AlgebraicGeometry.hasCompleteDevissageCover`. -/
def HasCompleteDevissageCover {Z T : Scheme.{u}} (g : Z ⟶ T) (G : Z.Modules) (t : T) : Prop :=
  ∃ (T' : EtaleNeighborhood T t) (_ : T'.IsElementary) (n : ℕ) (W : Fin n → Scheme.{u})
    (h : ∀ i, W i ⟶ Limits.pullback g T'.toBase) (_ : ∀ i, Etale (h i))
    (hl : ∀ i, LocallyOfFiniteType (h i ≫ Limits.pullback.snd g T'.toBase))
    (hq : ∀ i, ((Scheme.Modules.pullback
      (h i ≫ Limits.pullback.fst g T'.toBase)).obj G).IsQuasicoherent)
    (ht : ∀ i, ((Scheme.Modules.pullback
      (h i ≫ Limits.pullback.fst g T'.toBase)).obj G).IsFiniteType),
    (∀ i, Nonempty (@CompleteDevissage _ _ (h i ≫ Limits.pullback.snd g T'.toBase)
      ((Scheme.Modules.pullback (h i ≫ Limits.pullback.fst g T'.toBase)).obj G) T'.point
      (hl i) (hq i) (ht i))) ∧
      Limits.pullback.snd g T'.toBase ⁻¹' {T'.point} ⊆ ⋃ i, Set.range (h i)

/-- **Stacks Project, Tag 05HU**, in the packaging of
`AlgebraicGeometry.HasCompleteDevissageCover`. -/
theorem hasCompleteDevissageCover {Z T : Scheme.{u}} (g : Z ⟶ T) [LocallyOfFiniteType g]
    [QuasiCompact g] (G : Z.Modules) [G.IsQuasicoherent] [G.IsFiniteType] (t : T) :
    HasCompleteDevissageCover g G t :=
  exists_etaleNeighborhood_completeDevissage_cover g G t

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-! ### Stacks 0CWJ at an affine étale chart -/

/-- **Stacks Project, Tag 0CWJ**, delivered at an affine étale chart of the base change.

Let `X ⟶ Y` be a finite type morphism of algebraic spaces over `S`, let `F` be a finite type
quasi-coherent `𝒪_X`-module, and let `y` be a point of `Y`. Then there are

* an object `Y₁` of the site whose scheme is affine, an étale morphism `q : Y₁ ⟶ Y`, and a
  point `w` of `Y₁` above `y` — the source's `(Y', y') ⟶ (Y, y)` before the passage to an
  elementary étale neighbourhood;
* an étale chart `U` of `X` whose scheme is affine, and a morphism `ĝ : U ⟶ Y₁` of the site
  making the square over `q` commute, such that the induced morphism from `U` to the base
  change `X ×_Y Y₁` is surjective on points — the source's affine surjective étale cover `X'`
  of `X`, after the reduction to an affine base;
* the morphism of schemes underlying `ĝ` is locally of finite type and quasi-compact, and the
  conclusion of Stacks 05HU holds for it, for the restriction of `F` to `U`, and for the
  point of the scheme of `Y₁` determined by `w`.

The finitely many étale morphisms `hᵢ : Wᵢ ⟶ X_{Y'}` of the source's conclusion, their
complete dévissages and the inclusion of the fibre in the union of their images are bound
inside `AlgebraicGeometry.HasCompleteDevissageCover`. See the implementation notes of this
file for why they are delivered at the chart `U` rather than at `X_{Y'}`. -/
@[stacks 0CWJ "the elementary étale neighbourhood of the point, the covering family and its \
dévissages are delivered for the affine étale chart of the base change rather than for the base \
change as an algebraic space: the sources of the covering étale morphisms carry no size bound, \
so they are not objects of the big fppf site"]
theorem exists_affineChart_hasCompleteDevissageCover (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsFiniteType B S hS f) (F : Modules.{u, u} B S hS X hX)
    (hFq : F.IsQuasicoherentOnSite) (hFt : SheafOfModules.IsFiniteTypeOnSite F)
    (y : points B S hS Y) :
    ∃ (Y₁ : BigFppfOver B S hS) (q : yoneda.obj Y₁ ⟶ Y) (U : SmallEtale B S hS X)
      (ĝ : U.obj.left ⟶ Y₁) (hsq : yoneda.map ĝ ≫ q = U.obj.hom ≫ f)
      (w : points B S hS (yoneda.obj Y₁)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) ∧
      IsAffine (etaleChartScheme B S hS U) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      pointsMap B S hS (yoneda.obj Y₁) q w = y ∧
      IsSurjective B S hS (Limits.pullback.lift (yoneda.map ĝ) U.obj.hom hsq) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ĝ) ∧
      QuasiCompact ((BigFppfOver.toScheme B S hS).map ĝ) ∧
      HasCompleteDevissageCover ((BigFppfOver.toScheme B S hS).map ĝ)
        (restrictToChart B S hS hX F U) (pointsToScheme B S hS Y₁ w) := by
  classical
  -- The affine étale chart of `Y` at `y`: this is the source's "we may assume `Y` affine".
  obtain ⟨Y₁, q, hY₁aff, hqet, w, hw⟩ := exists_affine_etale_chart_at_point B S hS Y hY y
  have hY₁alg : IsAlgebraicSpace B S hS (yoneda.obj Y₁) := isAlgebraicSpace_yoneda B S hS Y₁
  -- `X ×_Y Y₁` is an algebraic space, and it is quasi-compact because `f` is quasi-compact
  -- and the affine `Y₁` is a quasi-compact algebraic space.
  have hPalg : IsAlgebraicSpace B S hS (Limits.pullback q f) :=
    isAlgebraicSpace_pullback B S hS q f hY₁alg hX hY
  have hPqc : IsQuasiCompactSpace B S hS (Limits.pullback q f) :=
    hf.2 (yoneda.obj Y₁) hY₁alg
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS Y₁ hY₁aff) q
  -- Stacks 03H6: an affine surjective étale cover of that quasi-compact algebraic space.
  obtain ⟨X', c, hX'aff, hcsurj, hcet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (Limits.pullback q f) hPalg).mp hPqc
  -- `c` itself is étale after every represented base change.
  have hPiso : ∀ ⦃A C : BigFppfOver B S hS⦄ (m : A ⟶ C), IsIso m →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) m := by
    intro A C m hm
    have := hm
    change Etale ((BigFppfOver.toScheme B S hS).map m)
    infer_instance
  have hcP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c := by
    have h₁ := hcet X' (𝟙 (yoneda.obj X')) (presheaf_id_of_iso B S hS _ hPiso X')
    rwa [Category.id_comp] at h₁
  -- so is the projection `X ×_Y Y₁ ⟶ X`, being a base change of `q`, and hence so is their
  -- composite, which is therefore an étale chart of `X`.
  have hsndP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (Limits.pullback.snd q f) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback q f) hqet
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have hcomp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hφP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ Limits.pullback.snd q f) :=
    hcomp.comp_mem _ _ hcP hsndP
  set U : SmallEtale B S hS X :=
    ⟨CostructuredArrow.mk (c ≫ Limits.pullback.snd q f), hφP⟩ with hU
  -- The chart maps to `Y₁` by the other projection; `yoneda` is full, so this comes from a
  -- morphism of the site.
  set ĝ : U.obj.left ⟶ Y₁ := yoneda.preimage (c ≫ Limits.pullback.fst q f) with hĝ
  have hĝmap : yoneda.map ĝ = c ≫ Limits.pullback.fst q f := yoneda.map_preimage _
  have hsq : yoneda.map ĝ ≫ q = U.obj.hom ≫ f := by
    rw [hĝmap]
    change (c ≫ Limits.pullback.fst q f) ≫ q = (c ≫ Limits.pullback.snd q f) ≫ f
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  -- Local finite type of the underlying morphism of schemes: the square of étale charts
  -- `(U, Y₁)` fed to the every-étale-chart form of the finite type hypothesis.
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ĝ) :=
    hf.1 U.obj.left Y₁ U.obj.hom q ĝ hφP hqet hsq
  -- Quasi-compactness: both schemes are affine, so the morphism is affine.
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) := hY₁aff
  have _ : IsAffine (etaleChartScheme B S hS U) := hX'aff
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map ĝ) := inferInstance
  refine ⟨Y₁, q, U, ĝ, hsq, w, hY₁aff, hX'aff, hqet, hw, ?_, hlft, hqc, ?_⟩
  · -- The induced morphism into the fibre product is `c`, which is surjective on points.
    have hlift : Limits.pullback.lift (yoneda.map ĝ) U.obj.hom hsq = c := by
      refine Limits.pullback.hom_ext ?_ ?_
      · rw [Limits.pullback.lift_fst, hĝmap]
      · rw [Limits.pullback.lift_snd]
        rfl
    rw [hlift]
    exact isSurjective_of_presheafSurjective B S hS c hcsurj
  · -- Stacks 05HU for the chart.
    have _ : (restrictToChart B S hS hX F U).IsQuasicoherent :=
      isQuasicoherent_restrictToChart B S hS ⟨X, hX⟩ F hFq U
    have _ : (restrictToChart B S hS hX F U).IsFiniteType :=
      isFiniteType_restrictToChart B S hS ⟨X, hX⟩ F hFq hFt U
    exact hasCompleteDevissageCover ((BigFppfOver.toScheme B S hS).map ĝ)
      (restrictToChart B S hS hX F U) (pointsToScheme B S hS Y₁ w)

end AlgebraicGeometry.Space

end
