module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre

/-!
# Free sections along a fibre for an algebraic space

Let `f : X ⟶ Y` be a finite type morphism of algebraic spaces over a scheme `S`, let `F` be a
finite type quasi-coherent `𝒪_X`-module and let `y` be a point of `|Y|` at which `F` is flat
over `Y` along the whole set-theoretic fibre `f^{-1}({y}) ⊆ |X|`. Stacks 0CVW asserts that
there are an étale morphism `(Y', y') ⟶ (Y, y)` with `Y'` a scheme and a commutative diagram
```
  X  ←ᵍ  X'
  ↓      ↓
  Y  ←  Spec 𝒪_{Y', y'}
```
such that `X' ⟶ X ×_Y Spec 𝒪_{Y', y'}` is étale, `|X'_{y'}| ⟶ f^{-1}({y})` is surjective,
`X'` is affine, and `Γ(X', g^*F)` is a free `𝒪_{Y', y'}`-module.

The source's proof is a reduction to the scheme-level statement Stacks 05L1: the question is
étale local on `Y`, so one may assume `Y` affine; then `X ×_Y Y'` is quasi-compact, so it has a
surjective étale cover by an affine scheme `X'`; the pullback of `F` to `X'` is flat over `Y'`
along the fibre over `y'`; and Stacks 05L1 applied to `X' ⟶ Y'` produces the elementary étale
neighbourhood `(Y'', y'')` and the affine scheme over `Spec 𝒪_{Y'', y''}` of the conclusion.

`AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre` carries out that
reduction. It produces an affine object `Y₁` of the site with an étale morphism `q : Y₁ ⟶ Y`
through the prescribed point, an affine étale chart `U` of `X` which is *surjective* onto the
base change `X ×_Y Y₁`, a morphism `ĝ : U ⟶ Y₁` of the site which is of finite type and
quasi-compact as a morphism of schemes, and the whole conclusion of Stacks 05L1 for that
morphism of schemes — including the identification of the set-theoretic fibre `f^{-1}({y})` in
`|X|` with the image of the fibre of the affine scheme that Stacks 05L1 produces.

## Main definitions

* `AlgebraicGeometry.HasFreeSectionsAlongFibreOver` names the conclusion of Stacks 05L1 for a
  morphism of schemes `g : Z ⟶ T`, a module on its source and a point of `T`, with the
  covering clause read through a prescribed map `π` out of `|Z|`: the fibre of the affine
  scheme `Z'` over the closed point is required to have prescribed image under `π ∘ c`. Taking
  `π` to be the map from a chart of an algebraic space to its point space turns that clause
  into the source's surjectivity of `|X'_{y'}| ⟶ f^{-1}({y})`.

## Main results

* `AlgebraicGeometry.hasFreeSectionsAlongFibreOver`: Stacks 05L1, repackaged as
  `AlgebraicGeometry.HasFreeSectionsAlongFibreOver`.
* `AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre`: Stacks 0CVW, reduced
  to the affine étale chart of the target at the prescribed point.

## Implementation notes

As for the sibling Stacks 0CWJ in
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/ExistenceCompleteDevissage.lean`, the size bound on
the objects of the site forces the conclusion to be stated at the chart rather than on the
algebraic space `X_{Y'}` itself.

First, the objects of the big fppf site of `S` are size-bounded schemes, whereas the schemes
Stacks 05L1 produces — the elementary étale neighbourhood `Y''` of the base point, its local
scheme `Spec 𝒪_{Y'', y''}` and the affine source `X''` — carry no size bound at all. They are
therefore not objects of the site, `yoneda.obj X''` is not available, and the commutative
diagram of *algebraic spaces* of the source's conclusion cannot be written down in this
development. What is available, and what is delivered here, is the scheme-level conclusion
`AlgebraicGeometry.HasFreeSectionsAlongFibreOver` for the affine chart `U` of `X ×_Y Y₁`,
together with the surjectivity of `U` onto `X ×_Y Y₁`. In particular the étaleness clause is
étaleness over `U ×_{Y₁} Spec 𝒪_{Y'', y''}` rather than over `X ×_Y Spec 𝒪_{Y'', y''}`; the
two differ by the base change of the étale chart `U ⟶ X`, which cannot be formed because the
local scheme is not an object of the site.

The covering clause, by contrast, *is* delivered on the algebraic space: `π` is instantiated
at `AlgebraicGeometry.Space.pointOfEtaleChart`, so the clause reads as the equality of the
set-theoretic fibre `f^{-1}({y}) ⊆ |X|` with the image in `|X|` of the fibre of `X''` over the
closed point. That is the source's "`|X'_{y'}| ⟶ F` is surjective", in the form Stacks 05L1
states it at the level of schemes.

Second, the module of the conclusion is the restriction of `F` to the chart,
`AlgebraicGeometry.Space.chartModule`. Its quasi-coherence and its finite type follow from
quasi-coherence and finite type of `F` on the small étale site of `X`, which are the source's
hypotheses on `F`: the first by `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`, the
second by `AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite`.

Everything else in the source's reduction is proved. The affine étale chart of `Y` at `y` is
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`, which is the licence for "we may
assume `Y` is an affine scheme"; quasi-compactness of `X ×_Y Y₁` is the quasi-compactness half
of the finite type hypothesis; the affine surjective étale cover of a quasi-compact algebraic
space is Stacks 03H6; and the transport of the flatness hypothesis from the point space of `X`
to the chart is Stacks 05VU in the form
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_mem_flatLocus`, which is what makes
the some-chart flat locus of Stacks 0DLR testable on the square of charts at hand.

## References

* [Stacks Project, Tag 0CVW](https://stacks.math.columbia.edu/tag/0CVW)
* [Stacks Project, Tag 05L1](https://stacks.math.columbia.edu/tag/05L1)
* [Stacks Project, Tag 0CWJ](https://stacks.math.columbia.edu/tag/0CWJ)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-! ### The conclusion of Stacks 05L1 -/

/-- The conclusion of **Stacks Project, Tag 05L1** for a morphism of schemes `g : Z ⟶ T`, a
module `G` on `Z` and a point `t` of `T`, with the covering clause read through a map
`π : Z → P`: there are an elementary étale neighbourhood `(T', t') ⟶ (T, t)` and a commutative
square with an affine scheme `Z'` over `Spec 𝒪_{T', t'}` and `c : Z' ⟶ Z` such that
`Z' ⟶ Z ×_T Spec 𝒪_{T', t'}` is étale, the prescribed set `Fib` is the image under `π ∘ c` of
the fibre of `Z'` over the closed point, and `Γ(Z', c^*G)` is a free `𝒪_{T', t'}`-module.

For `π` the identity and `Fib` the fibre `g^{-1}({t})` this is literally the conclusion of
Stacks 05L1; a general `π` lets the covering clause be stated on a space that `Z` is a chart
of. -/
def HasFreeSectionsAlongFibreOver {Z T : Scheme.{u}} (g : Z ⟶ T) (G : Z.Modules) (t : T)
    {P : Type v} (π : Z → P) (Fib : Set P) : Prop :=
  ∃ (T' : EtaleNeighborhood T t) (_ : T'.IsElementary) (Z' : Scheme.{u})
    (q : Z' ⟶ Spec (.of (T'.scheme.presheaf.stalk T'.point))) (c : Z' ⟶ Z)
    (hcomm : c ≫ g = q ≫ T'.scheme.fromSpecStalk T'.point ≫ T'.toBase)
    (_ : Etale (pullback.lift c q hcomm))
    (_ : Fib = π '' (c '' (q ⁻¹' {IsLocalRing.closedPoint _})))
    (_ : IsAffine Z'),
    letI : Module (T'.scheme.presheaf.stalk T'.point)
        Γ((Scheme.Modules.pullback c).obj G, ⊤) :=
      Module.compHom _
        ((Scheme.ΓSpecIso (.of (T'.scheme.presheaf.stalk T'.point))).inv ≫ q.appTop).hom
    Module.Free (T'.scheme.presheaf.stalk T'.point)
      Γ((Scheme.Modules.pullback c).obj G, ⊤)

/-- **Stacks Project, Tag 05L1**, in the packaging of
`AlgebraicGeometry.HasFreeSectionsAlongFibreOver`.

The flatness hypothesis is stated on the points of `Z` lying over `t` rather than on the
scheme-theoretic fibre, which is the same condition by
`AlgebraicGeometry.Scheme.Hom.range_fiberι`. -/
theorem hasFreeSectionsAlongFibreOver {Z T : Scheme.{u}} (g : Z ⟶ T) [LocallyOfFiniteType g]
    [QuasiCompact g] (G : Z.Modules) [G.IsQuasicoherent] [G.IsFiniteType] (t : T)
    {P : Type v} (π : Z → P) (Fib : Set P) (hFib : Fib = π '' (g ⁻¹' {t}))
    (hflat : ∀ z : Z, g z = t → IsFlatOverAt g.toLRSHom.toShHom G z) :
    HasFreeSectionsAlongFibreOver g G t π Fib := by
  have hfibre : ∀ z : g.fiber t, g (g.fiberι t z) = t := by
    intro z
    have hz : g.fiberι t z ∈ g ⁻¹' {t} := by
      rw [← g.range_fiberι t]
      exact Set.mem_range_self z
    exact hz
  obtain ⟨T', hT', Z', q, c, hcomm, het, hcov, haff, hfree⟩ :=
    exists_elementaryEtaleNeighborhood_free_sections_along_fibre_of_finiteType g G t
      fun z => hflat (g.fiberι t z) (hfibre z)
  refine ⟨T', hT', Z', q, c, hcomm, het, ?_, haff, hfree⟩
  rw [hFib, hcov]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-! ### Stacks 0CVW at an affine étale chart -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Project, Tag 0CVW**, reduced to the affine étale chart of the target at the
prescribed point.

Let `f : X ⟶ Y` be a finite type morphism of algebraic spaces over `S`, let `F` be a
quasi-coherent `𝒪_X`-module whose restriction to every étale chart of `X` is quasi-coherent of
finite type, and let `y` be a point of `|Y|` at which `F` is flat over `Y` along the whole
set-theoretic fibre `f^{-1}({y})`. Then there are

* an object `Y₁` of the site whose scheme is affine, an étale morphism `q : Y₁ ⟶ Y` and a
  point `w` of `Y₁` above `y` — the source's `(Y', y') ⟶ (Y, y)` before the passage to an
  elementary étale neighbourhood;
* an étale chart `U` of `X` whose scheme is affine, and a morphism `ĝ : U ⟶ Y₁` of the site
  making the square over `q` commute, such that the induced morphism from `U` to the base
  change `X ×_Y Y₁` is surjective on points — the source's affine surjective étale cover `X'`
  of `X ×_Y Y'`;
* the morphism of schemes underlying `ĝ` is locally of finite type and quasi-compact, and the
  conclusion of Stacks 05L1 holds for it, for the restriction of `F` to `U`, and for the point
  of the scheme of `Y₁` determined by `w` — with the covering clause of that conclusion read
  on the point space of `X`, where it says that the set-theoretic fibre `f^{-1}({y})` is the
  image of the fibre of the affine scheme Stacks 05L1 produces.

The hypothesis `hFt` is the source's "`F` of finite type", on the small étale site of `X`.
The chartwise finite type it gives is
`AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite`, and chartwise
quasi-coherence follows from `SheafOfModules.IsQuasicoherentOnSite` by
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`. -/
@[stacks 0CVW "the etale neighbourhood, the affine scheme and its free sections are \
delivered; reduced to the affine etale chart of the target"]
theorem exists_affineChart_hasFreeSectionsAlongFibre {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hFt : SheafOfModules.IsFiniteTypeOnSite F)
    (y : points B S hS Y.1)
    (hflat : ∀ x : points B S hS X.1, pointsMap B S hS X.1 f.hom x = y →
      x ∈ flatLocus B S hS X.2 f.hom F) :
    ∃ (Y₁ : BigFppfOver B S hS) (q : yoneda.obj Y₁ ⟶ Y.1) (U : SmallEtale B S hS X.1)
      (ĝ : U.obj.left ⟶ Y₁) (hsq : yoneda.map ĝ ≫ q = U.obj.hom ≫ f.hom)
      (w : points B S hS (yoneda.obj Y₁)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) ∧
      IsAffine (etaleChartScheme B S hS U) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      pointsMap B S hS (yoneda.obj Y₁) q w = y ∧
      IsSurjective B S hS (pullback.lift (yoneda.map ĝ) U.obj.hom hsq) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ĝ) ∧
      QuasiCompact ((BigFppfOver.toScheme B S hS).map ĝ) ∧
      HasFreeSectionsAlongFibreOver ((BigFppfOver.toScheme B S hS).map ĝ)
        (chartModule B S hS X.2 F U) (pointsToScheme B S hS Y₁ w)
        (pointOfEtaleChart B S hS U) (pointsMap B S hS X.1 f.hom ⁻¹' {y}) := by
  classical
  -- The affine étale chart of `Y` at `y`: this is the source's "we may assume `Y` affine".
  obtain ⟨Y₁, q, hY₁aff, hqet, w, hw⟩ := exists_affine_etale_chart_at_point B S hS Y.1 Y.2 y
  have hY₁alg : IsAlgebraicSpace B S hS (yoneda.obj Y₁) := isAlgebraicSpace_yoneda B S hS Y₁
  -- `X ×_Y Y₁` is an algebraic space, and it is quasi-compact because `f` is quasi-compact
  -- and the affine `Y₁` is a quasi-compact algebraic space.
  have hPalg : IsAlgebraicSpace B S hS (pullback q f.hom) :=
    isAlgebraicSpace_pullback B S hS q f.hom hY₁alg X.2 Y.2
  have hPqc : IsQuasiCompactSpace B S hS (pullback q f.hom) :=
    hf.2 (yoneda.obj Y₁) hY₁alg
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS Y₁ hY₁aff) q
  -- Stacks 03H6: an affine surjective étale cover of that quasi-compact algebraic space.
  obtain ⟨X', c, hX'aff, hcsurj, hcet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (pullback q f.hom) hPalg).mp hPqc
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
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd q f.hom) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback q f.hom) hqet
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have hcomp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hφP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ pullback.snd q f.hom) :=
    hcomp.comp_mem _ _ hcP hsndP
  set U : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (c ≫ pullback.snd q f.hom), hφP⟩ with hU
  -- The chart maps to `Y₁` by the other projection; `yoneda` is full, so this comes from a
  -- morphism of the site.
  set ĝ : U.obj.left ⟶ Y₁ := yoneda.preimage (c ≫ pullback.fst q f.hom) with hĝ
  have hĝmap : yoneda.map ĝ = c ≫ pullback.fst q f.hom := yoneda.map_preimage _
  have hsq : yoneda.map ĝ ≫ q = U.obj.hom ≫ f.hom := by
    rw [hĝmap]
    change (c ≫ pullback.fst q f.hom) ≫ q = (c ≫ pullback.snd q f.hom) ≫ f.hom
    rw [Category.assoc, Category.assoc, pullback.condition]
  -- The square of étale charts through `y`, and the point of the chart of `Y₁` below.
  set V : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk q, hqet⟩ with hV
  set d : ChartDiagram B S hS X.1 Y.1 f.hom := { U := U, V := V, g := ĝ, comm := hsq.symm }
    with hd
  set τ := (BigFppfOver.toScheme B S hS).map ĝ with hτ
  set w₀ := pointsToScheme B S hS Y₁ w with hw₀def
  have hw₀ : pointOfEtaleChart B S hS V w₀ = y := by
    change pointsMap B S hS (yoneda.obj Y₁) q
      ((pointsEquivScheme B S hS Y₁).symm w₀) = y
    rw [show (pointsEquivScheme B S hS Y₁).symm w₀ = w from
      (pointsEquivScheme B S hS Y₁).symm_apply_apply w]
    exact hw
  -- The square of charts is compatible with the maps on points.
  have hcompat : ∀ u : etaleChartScheme B S hS U,
      pointsMap B S hS X.1 f.hom (pointOfEtaleChart B S hS U u) =
        pointOfEtaleChart B S hS V (τ u) := by
    intro u
    change pointsMap B S hS X.1 f.hom (pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
      ((pointsEquivScheme B S hS U.obj.left).symm u)) = _
    rw [← pointsMap_comp_apply, ← hsq, pointsMap_comp_apply,
      pointsMap_yoneda_map_symm B S hS ĝ u]
    rfl
  have hlocft : LocallyOfFiniteType τ := hf.1 U.obj.left Y₁ U.obj.hom q ĝ hφP hqet hsq
  have hY₁affI : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) := hY₁aff
  have hUaffI : IsAffine (etaleChartScheme B S hS U) := hX'aff
  have hqcτ : QuasiCompact τ := inferInstance
  refine ⟨Y₁, q, U, ĝ, hsq, w, hY₁aff, hX'aff, hqet, hw, ?_, hlocft, hqcτ, ?_⟩
  · -- The induced morphism into the fibre product is `c`, which is surjective on points.
    have hlift : pullback.lift (yoneda.map ĝ) U.obj.hom hsq = c := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, hĝmap]
      · rw [pullback.lift_snd]
        rfl
    rw [hlift]
    exact isSurjective_of_presheafSurjective B S hS c hcsurj
  · -- The set-theoretic fibre of `f` over `y` is the image of the fibre of the chart over `w`.
    -- A point of the chart over `w₀` lies over `y`.
    have hover : ∀ u : etaleChartScheme B S hS U, τ u = w₀ →
        pointsMap B S hS X.1 f.hom (pointOfEtaleChart B S hS U u) = y := fun u hu => by
      rw [hcompat u, hu, hw₀]
    have hfibEq : (pointsMap B S hS X.1 f.hom ⁻¹' {y} : Set (points B S hS X.1)) =
        pointOfEtaleChart B S hS U '' (τ ⁻¹' {w₀}) := by
      refine Set.Subset.antisymm ?_ ?_
      · intro x hx
        have hxy : pointsMap B S hS X.1 f.hom x = y := hx
        obtain ⟨z, hz₁, hz₂⟩ := exists_points_of_isPullback B S hS
          (IsPullback.of_hasPullback q f.hom) w x (hw.trans hxy.symm)
        obtain ⟨uu, huu⟩ := (surjective_iff_surjective_pointsMap B S hS
          (pullback q f.hom) hPalg X' c).mp hcsurj z
        refine ⟨pointsEquivScheme B S hS X' uu, ?_, ?_⟩
        · -- the point of the chart lies over `w₀`
          change τ (pointsEquivScheme B S hS X' uu) ∈ ({w₀} : Set _)
          have hkey : τ (pointsToScheme B S hS X' uu) = w₀ := by
            have h : pointsToScheme B S hS Y₁
                (pointsMap B S hS (yoneda.obj X') (yoneda.map ĝ) uu) =
                τ (pointsToScheme B S hS X' uu) :=
              pointsToScheme_pointsMap_yoneda B S hS ĝ uu
            rw [hĝmap, pointsMap_comp_apply, huu, hz₁] at h
            exact h.symm
          exact hkey
        · -- and it maps to `x`
          change pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
            ((pointsEquivScheme B S hS X').symm (pointsEquivScheme B S hS X' uu)) = x
          rw [(pointsEquivScheme B S hS X').symm_apply_apply]
          change pointsMap B S hS (yoneda.obj X') (c ≫ pullback.snd q f.hom) uu = x
          rw [pointsMap_comp_apply, huu, hz₂]
      · rintro x ⟨u, hu, rfl⟩
        exact hover u hu
    -- Transport of the flatness hypothesis to the chart: Stacks 05VU.
    have hflatChart : ∀ u : etaleChartScheme B S hS U, τ u = w₀ →
        IsFlatOverAt τ.toLRSHom.toShHom (chartModule B S hS X.2 F U) u := by
      intro u hu
      exact (mem_chartFlatLocus_iff_isFlatOverAtOnChartDiagram B S hS F d u).2
        ((isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u).2 (hflat _ (hover u hu)))
    have _ : (chartModule B S hS X.2 F U).IsQuasicoherent :=
      isQuasicoherent_restrictToChart B S hS X F ‹_› U
    have _ : (chartModule B S hS X.2 F U).IsFiniteType :=
      isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS X F ‹_› hFt U
    exact hasFreeSectionsAlongFibreOver τ (chartModule B S hS X.2 F U) w₀
      (pointOfEtaleChart B S hS U) _ hfibEq hflatChart

end AlgebraicGeometry.Space

end
