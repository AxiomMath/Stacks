module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingFlatnessChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStratumRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingStratificationFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingStratumMono
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverLocalSource
public import StacksFrontier.AlgebraicGeometry.Spaces.RankDecompositionSelfChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# The flatness clause of Stacks 0CZA

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `G` be a
quasi-coherent `𝒪_X`-module of finite presentation and let `X ⊇ Z_0 ⊇ Z_1 ⊇ …` be the chain of
closed subspaces cut out by the Fitting ideal sheaves of `G`, with strata `X_r = Z_{r-1} ∖ Z_r`
and disjoint union `X' = ∐_{r ≥ 0} X_r`.  This file proves the remaining clause of
Stacks 0CZA: **`X'` represents the functor sending a test object `a : T ⟶ X` of the site to a
one-point set when `G_T` is flat over `T` and to the empty set otherwise.**

## Main results

* `AlgebraicGeometry.Space.exists_hom_lift_fittingRankStratification_of_isFiniteLocallyFreeOfRank`:
  a test object on which `G` pulls back to a module finite locally free of one rank lifts to
  `X'`.
* `AlgebraicGeometry.Space.existsUnique_hom_lift_fittingRankStratification_of_isAffine`: the
  flatness clause over an **affine** test object.
* `AlgebraicGeometry.Space.existsUnique_hom_lift_fittingRankStratification_of_isFlatOver`: the
  forward half of the flatness clause, over an arbitrary test object.
* `AlgebraicGeometry.Space.isFlatOver_of_hom_lift_fittingRankStratification`: the backward
  half.
* `AlgebraicGeometry.Space.isFlatOver_modulePullback_iff_existsUnique_hom_lift` and
  `AlgebraicGeometry.Space.isFlatOver_modulePullback_iff_exists_hom_lift`: **the flatness
  clause of Stacks 0CZA**, with unique and with mere existence of the factorisation.
* `AlgebraicGeometry.Space.exists_fittingRankStratification_flat_spec`: **Stacks 0CZA.**

## Implementation notes

The two halves run in opposite directions through the same single-stratum statement, clause (3)
of Stacks 0CZ9 in the form
`AlgebraicGeometry.Space.existsUnique_lift_fittingRankStratum_iff`, which is an *equivalence*
between factoring through `X_r` and the pullback of `G` being finite locally free of rank `r`.

Forwards, the ranks are produced one point at a time.  Over an affine test object the sections
of `G_T` over the identity chart are finite locally free (Stacks 00NX), so every point has a
basic-open neighbourhood on which the pullback has a single rank — that is
`AlgebraicGeometry.Space.exists_basicOpen_isFiniteLocallyFreeOfRank_of_isFlatOver_id`.  The
resulting basic opens are *not* disjoint, and the local lifts they produce are *not* asked to
be compatible: the structural morphism `π : X' ⟶ X` is a monomorphism
(`AlgebraicGeometry.Space.mono_fittingRankStratificationHom`), so
`AlgebraicGeometry.Space.existsUnique_lift_fittingRankStratification_of_openCover` glues them
with no further input.  A general test object is reduced to affine ones by the same gluing
statement, applied to the family of its affine open subobjects — so no covering sieve has to be
exhibited and the affine case is used exactly as the point case is.

Backwards, a lift `h : T ⟶ X'` is a section of a coproduct sheaf, and Stacks 02WO in the form
`AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan` cuts `T` into
*disjoint open* pieces on the `r`-th of which `h` factors through `X_r`.  Clause (3) read
forwards gives the rank `r` of `G` there, hence its flatness over the piece
(`AlgebraicGeometry.Space.isFlatOver_id_of_isFiniteLocallyFreeOfRank`), and flatness over the
own space is étale local on the source
(`AlgebraicGeometry.Space.isFlatOver_id_of_etale_cover_of_representable`), so it holds over
`T`.  This is why that locality is needed at the *identity*: the condition of Stacks 0CZA is
flatness of `G_T` over `T` itself.

Every comparison of a pullback along a composite with the iterated pullback is the inverse
image comparison of Stacks 03LU, `AlgebraicGeometry.Space.modulePullbackCompIso`, and both the
rank and the flatness are transported along it
(`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.of_iso` and
`AlgebraicGeometry.Space.isFlatOver_iff_of_iso`); nothing unfolds the comparison.

## References

* [Stacks Project, Tag 0CZA](https://stacks.math.columbia.edu/tag/0CZA)
* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

/-! ### Sections and morphisms out of a representable presheaf -/

/-- Factoring a morphism out of a representable presheaf through a morphism of presheaves is
the same problem as lifting the corresponding section, in the sense that the two unique
existence statements agree. -/
theorem existsUnique_hom_comp_iff_existsUnique_section {C : Type u} [Category.{v} C]
    {F H : Cᵒᵖ ⥤ Type v} (φ : F ⟶ H) {T : C} (a : yoneda.obj T ⟶ H) :
    (∃! h : yoneda.obj T ⟶ F, h ≫ φ = a) ↔
      ∃! τ : F.obj (op T), φ.app (op T) τ = yonedaEquiv a :=
  yonedaEquiv.existsUnique_congr fun h ↦ by
    rw [← yonedaEquiv_comp]
    exact (Equiv.apply_eq_iff_eq yonedaEquiv).symm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)

/-! ### Lifting a test object of constant rank -/

/-- **A test object over which `G` pulls back to a module finite locally free of one rank lifts
to the disjoint union of the strata.**  Clause (3) of Stacks 0CZ9 factors the test morphism
through the rank-`r` stratum, and composing with the `r`-th leg of the coproduct lands it in
`X' = ∐_{k ≥ 0} X_k`. -/
theorem exists_hom_lift_fittingRankStratification_of_isFiniteLocallyFreeOfRank
    (hGqc : G.IsQuasicoherentOnSite) (hGft : SheafOfModules.IsFiniteTypeOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r)
    {V : AlgebraicSpaces B S hS} (f : V ⟶ X) (r : ℕ)
    (hrank : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS V.1 V.2)
      ((modulePullback B S hS f).obj G) r) :
    ∃ h : V.1 ⟶ (fittingRankStratification B S hS X Z).1,
      h ≫ (fittingRankStratificationHom B S hS X Z).hom = f.hom := by
  obtain ⟨g, hg, -⟩ :=
    (existsUnique_lift_fittingRankStratum_iff B S hS G hGqc hGft Z hZ r f).1 hrank
  refine ⟨g ≫ (Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r).hom, ?_⟩
  have hres : (Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r).hom ≫
      (fittingRankStratificationHom B S hS X Z).hom =
      (fittingRankStratum B S hS X Z r).ι :=
    congrArg (fun k : fittingRankStratumSpace B S hS X Z r ⟶ X ↦ k.hom)
      ((isAlgebraicSpace_fittingRankStratification B S hS X Z).2 r)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t : (fittingRankStratum B S hS X Z r).toFunctor ⟶ X.1 ↦ g ≫ t) hres).trans hg)

/-! ### The comparison of a pullback along a composite -/

/-- The inverse image of `G` along a composite, compared with the iterated inverse image, by
the comparison of Stacks 03LU. -/
def modulePullbackCompIsoApp {V W : AlgebraicSpaces B S hS} (f : V ⟶ W) (g : W ⟶ X) :
    (modulePullback B S hS f).obj ((modulePullback B S hS g).obj G) ≅
      (modulePullback B S hS (f ≫ g)).obj G :=
  (modulePullbackCompIso B S hS f g).app G

/-- The square whose two vertical sides are identities is cartesian, which is what makes
Stacks 05VW applicable to a pullback along an arbitrary morphism of the source of a module
flat over its own space. -/
theorem isPullback_id_id {V W : AlgebraicSpaces B S hS} (m : V ⟶ W) :
    IsPullback m (𝟙 V) (𝟙 W) m :=
  IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

/-- **The inverse image of a module flat over its own algebraic space is flat over its own
algebraic space.**  This is Stacks 05VW read at the cartesian square of
`AlgebraicGeometry.Space.isPullback_id_id`. -/
theorem isFlatOver_id_modulePullback {V W : AlgebraicSpaces B S hS} (m : V ⟶ W)
    (H : Modules.{u, u} B S hS W.1 W.2) [H.IsQuasicoherentOnSite]
    (hH : IsFlatOver B S hS W.2 (𝟙 W : W ⟶ W).hom H) :
    IsFlatOver B S hS V.2 (𝟙 V : V ⟶ V).hom ((modulePullback B S hS m).obj H) :=
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS m H ‹_›
  isFlatOver_modulePullback B S hS (isPullback_id_id B S hS m) H hH

/-- The inverse image of `G` along a composite `m ≫ g` is flat over its own algebraic space as
soon as the inverse image along `g` is: pull back along `m` by
`AlgebraicGeometry.Space.isFlatOver_id_modulePullback` and transport along the comparison of
Stacks 03LU. -/
theorem isFlatOver_id_modulePullback_comp (hGqc : G.IsQuasicoherentOnSite)
    {V W : AlgebraicSpaces B S hS} (m : V ⟶ W) (g : W ⟶ X)
    (hflat : IsFlatOver B S hS W.2 (𝟙 W : W ⟶ W).hom ((modulePullback B S hS g).obj G)) :
    IsFlatOver B S hS V.2 (𝟙 V : V ⟶ V).hom ((modulePullback B S hS (m ≫ g)).obj G) := by
  have : ((modulePullback B S hS g).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g G hGqc
  exact (isFlatOver_iff_of_iso B S hS V.2 (𝟙 V : V ⟶ V).hom
    (modulePullbackCompIsoApp B S hS X G m g)).1
    (isFlatOver_id_modulePullback B S hS m ((modulePullback B S hS g).obj G) hflat)

/-- The section corresponding to a local factorisation through `X'`, in the form the gluing
statements of `StacksFrontier/AlgebraicGeometry/Spaces/FittingStratumMono.lean` consume. -/
theorem app_yonedaEquiv_eq_of_hom_lift (Z : ℕ → ClosedSubspaces B S hS X.1)
    {T Y : BigFppfOver B S hS} (q : Y ⟶ T) (a : yoneda.obj T ⟶ X.1)
    (h : yoneda.obj Y ⟶ (fittingRankStratification B S hS X Z).1)
    (hh : h ≫ (fittingRankStratificationHom B S hS X Z).hom = yoneda.map q ≫ a) :
    (fittingRankStratificationHom B S hS X Z).hom.app (op Y) (yonedaEquiv h) =
      X.1.map q.op (yonedaEquiv a) :=
  (congrArg (fun k : yoneda.obj Y ⟶ X.1 ↦ yonedaEquiv k) hh).trans
    (yonedaEquiv_naturality a q).symm

/-- Local lifts of a test morphism over a family of open subobjects covering `T` glue to a unique
lift over `T`. -/
private theorem existsUnique_hom_lift_fittingRankStratification_of_openCover
    (Z : ℕ → ClosedSubspaces B S hS X.1) (hanti : Antitone fun r ↦ (Z r).1)
    (T : BigFppfOver B S hS) {κ : Type u} (O : κ → ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (a : yoneda.obj T ⟶ X.1) (hcov : ∀ t, ∃ k, t ∈ O k)
    (hlocal : ∀ k, ∃ h : yoneda.obj (openSub T (O k)) ⟶ (fittingRankStratification B S hS X Z).1,
      h ≫ (fittingRankStratificationHom B S hS X Z).hom = yoneda.map (openSubHom T (O k)) ≫ a) :
    ∃! h : yoneda.obj T ⟶ (fittingRankStratification B S hS X Z).1,
      h ≫ (fittingRankStratificationHom B S hS X Z).hom = a := by
  have hrange : ∀ k, Set.range ((BigFppfOver.toScheme B S hS).map (openSubHom T (O k))) =
      (O k : Set ((BigFppfOver.toScheme B S hS).obj T)) := fun k ↦ by
    rw [toScheme_map_openSubHom B S hS T (O k)]
    exact Scheme.Opens.range_ι (O k)
  refine (existsUnique_hom_comp_iff_existsUnique_section (T := T)
    (fittingRankStratificationHom B S hS X Z).hom a).2 ?_
  refine existsUnique_lift_fittingRankStratification_of_openCover B S hS X Z hanti
    (fun k ↦ openSubHom T (O k)) (fun k ↦ ?_) (fun t ↦ ?_) _ fun k ↦ ?_
  · rw [toScheme_map_openSubHom B S hS T (O k)]
    exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (O k).ι)
  · obtain ⟨k, hk⟩ := hcov t
    exact ⟨k, (hrange k).symm ▸ hk⟩
  · obtain ⟨h, hh⟩ := hlocal k
    exact ⟨yonedaEquiv h, app_yonedaEquiv_eq_of_hom_lift B S hS X Z (openSubHom T (O k)) a h hh⟩

/-! ### The flatness clause over an affine test object -/

/-- **The flatness clause of Stacks 0CZA over an affine test object.**  Let `G` be a
quasi-coherent `𝒪_X`-module of finite presentation, let `W` be an affine object of the site and
let `f : h_W ⟶ X` be a test morphism whose pullback `G_W` is flat over `h_W` in the sense of
Stacks 05VV.  Then `f` factors uniquely through `X' = ∐_{r ≥ 0} X_r`.

Every point of `W` has a basic-open neighbourhood on which `G_W` is finite locally free of a
single rank
(`AlgebraicGeometry.Space.exists_basicOpen_isFiniteLocallyFreeOfRank_of_isFlatOver_id`), hence
on which the test morphism factors through one stratum and so through `X'`.  Those basic opens
are not disjoint and the local factorisations are not compatible by construction; they do not
have to be, because `π` is a monomorphism. -/
theorem existsUnique_hom_lift_fittingRankStratification_of_isAffine
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r)
    (W : BigFppfOver B S hS) (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (f : schemeSpace W ⟶ X)
    (hflat : IsFlatOver B S hS (schemeSpace W).2
      (𝟙 (schemeSpace W) : schemeSpace W ⟶ schemeSpace W).hom
      ((modulePullback B S hS f).obj G)) :
    ∃! h : yoneda.obj W ⟶ (fittingRankStratification B S hS X Z).1,
      h ≫ (fittingRankStratificationHom B S hS X Z).hom = f.hom := by
  have hGft : SheafOfModules.IsFiniteTypeOnSite G := by
    have := hGfp
    infer_instance
  have hanti : Antitone fun r ↦ (Z r).1 :=
    antitone_of_definingIdealSheaf_eq_fittingIdeal B S hS X G Z hZ
  have hHqc : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hGqc
  have hHfp : SheafOfModules.IsFinitePresentationOnSite ((modulePullback B S hS f).obj G) :=
    isFinitePresentationOnSite_modulePullback B S hS f G hGfp
  -- a basic open of a single rank around every point of `W`
  choose gen n hmem hrk using fun z ↦
    exists_basicOpen_isFiniteLocallyFreeOfRank_of_isFlatOver_id B S hS W
      (isAlgebraicSpace_yoneda B S hS W) ((modulePullback B S hS f).obj G) hHqc hHfp hflat hW z
  refine existsUnique_hom_lift_fittingRankStratification_of_openCover B S hS X Z hanti W
    (fun z ↦ ((BigFppfOver.toScheme B S hS).obj W).basicOpen (gen z)) f.hom
    (fun z ↦ ⟨z, hmem z⟩) fun z ↦ ?_
  exact exists_hom_lift_fittingRankStratification_of_isFiniteLocallyFreeOfRank
    B S hS X G hGqc hGft Z hZ (schemeSpaceMap (openSubHom W _) ≫ f) (n z)
    (RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
      (modulePullbackCompIsoApp B S hS X G (schemeSpaceMap (openSubHom W _)) f) (hrk z))

/-! ### The flatness clause over an arbitrary test object -/

/-- **The forward half of the flatness clause of Stacks 0CZA.**  A test morphism
`f : h_T ⟶ X` whose pullback `G_T` is flat over `h_T` factors uniquely through
`X' = ∐_{r ≥ 0} X_r`, for an arbitrary object `T` of the site.

The affine open subobjects of `T` cover it, over each of them the affine case applies — the
restriction of `G_T` stays flat over the piece by Stacks 05VW — and the local factorisations
glue by `AlgebraicGeometry.Space.existsUnique_lift_fittingRankStratification_of_openCover`,
which needs no compatibility because `π` is a monomorphism. -/
theorem existsUnique_hom_lift_fittingRankStratification_of_isFlatOver
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r)
    (T : BigFppfOver B S hS) (f : schemeSpace T ⟶ X)
    (hflat : IsFlatOver B S hS (schemeSpace T).2
      (𝟙 (schemeSpace T) : schemeSpace T ⟶ schemeSpace T).hom
      ((modulePullback B S hS f).obj G)) :
    ∃! h : yoneda.obj T ⟶ (fittingRankStratification B S hS X Z).1,
      h ≫ (fittingRankStratificationHom B S hS X Z).hom = f.hom := by
  have hanti : Antitone fun r ↦ (Z r).1 :=
    antitone_of_definingIdealSheaf_eq_fittingIdeal B S hS X G Z hZ
  refine existsUnique_hom_lift_fittingRankStratification_of_openCover B S hS X Z hanti T
    (fun V : ((BigFppfOver.toScheme B S hS).obj T).affineOpens ↦ V.1) f.hom
    (fun t ↦ ?_) fun V ↦ ?_
  · obtain ⟨V, hV, htV, -⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
        (X := (BigFppfOver.toScheme B S hS).obj T) (x := t) (U := ⊤) trivial
    exact ⟨⟨V, hV⟩, htV⟩
  · have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj (openSub T V.1)) := by
      have : IsAffine (V.1 : Scheme.{u}) := V.2
      exact this
    obtain ⟨h₀, hh₀, -⟩ := existsUnique_hom_lift_fittingRankStratification_of_isAffine B S hS X G
      hGqc hGfp Z hZ (openSub T V.1) haff (schemeSpaceMap (openSubHom T V.1) ≫ f)
      (isFlatOver_id_modulePullback_comp B S hS X G hGqc
        (schemeSpaceMap (openSubHom T V.1)) f hflat)
    exact ⟨h₀, hh₀⟩

/-! ### The backward half of the flatness clause -/

/-- **The backward half of the flatness clause of Stacks 0CZA.**  If a test morphism
`f : h_T ⟶ X` factors through `X' = ∐_{r ≥ 0} X_r`, then the pullback `G_T` is flat over `h_T`
in the sense of Stacks 05VV.

The factorisation is a section of a coproduct sheaf, so Stacks 02WO cuts `T` into disjoint open
pieces on the `r`-th of which the test morphism factors through the stratum `X_r`; clause (3) of
Stacks 0CZ9 makes `G` finite locally free of rank `r` there, hence flat over the piece, and
flatness over the own space is étale local on the source. -/
theorem isFlatOver_of_hom_lift_fittingRankStratification
    (hGqc : G.IsQuasicoherentOnSite) (hGft : SheafOfModules.IsFiniteTypeOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r)
    (T : BigFppfOver B S hS) (f : schemeSpace T ⟶ X)
    (h : yoneda.obj T ⟶ (fittingRankStratification B S hS X Z).1)
    (hh : h ≫ (fittingRankStratificationHom B S hS X Z).hom = f.hom) :
    IsFlatOver B S hS (schemeSpace T).2
      (𝟙 (schemeSpace T) : schemeSpace T ⟶ schemeSpace T).hom
      ((modulePullback B S hS f).obj G) := by
  have : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hGqc
  -- the disjoint union of the strata, read as a coproduct of sheaves
  have hsheaf : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj
      (fittingRankStratification B S hS X Z))
      fun r : ℕ ↦ (algebraicSpacesToSheaf B S hS).map
        (Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r)) :=
    isColimitCofanMkObjOfIsColimit (algebraicSpacesToSheaf B S hS) _ _ (coproductIsCoproduct _)
  -- Stacks 02WO: the open pieces of `T` on which the factorisation comes from one stratum
  obtain ⟨W, p, hoi, hpiece, -, hcov, -⟩ :=
    AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan _ hsheaf T
      (yonedaEquiv h)
  have hpiece' : ∀ r : ℕ, ∃ z : (fittingRankStratum B S hS X Z r).toFunctor.obj (op (W r)),
      ((algebraicSpacesToSheaf B S hS).map
            (Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r)).hom.app
          (op (W r)) z =
        (fittingRankStratification B S hS X Z).1.map (p r).op (yonedaEquiv h) := hpiece
  refine isFlatOver_id_of_etale_cover_of_representable B S hS p
    (fun r ↦ have := hoi r; inferInstance) hcov _ fun r ↦ ?_
  obtain ⟨z, hz⟩ := hpiece' r
  have hres : ((algebraicSpacesToSheaf B S hS).map
        (Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r)).hom ≫
      (fittingRankStratificationHom B S hS X Z).hom =
      (fittingRankStratum B S hS X Z r).ι :=
    congrArg (fun k : fittingRankStratumSpace B S hS X Z r ⟶ X ↦ k.hom)
      ((isAlgebraicSpace_fittingRankStratification B S hS X Z).2 r)
  -- the test morphism restricted to the `r`-th piece factors through the stratum `X_r`
  have hfac0 : yonedaEquiv.symm z ≫ ((algebraicSpacesToSheaf B S hS).map
        (Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r)).hom =
      yoneda.map (p r) ≫ h :=
    ((yonedaEquiv_symm_naturality_right (W r) ((algebraicSpacesToSheaf B S hS).map
          (Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r)).hom z).trans
        (congrArg (fun t : (fittingRankStratification B S hS X Z).1.obj (op (W r)) ↦
          yonedaEquiv.symm t) hz)).trans
      ((yonedaEquiv_symm_map (p r).op (yonedaEquiv h)).trans
        (congrArg (fun k : yoneda.obj T ⟶ (fittingRankStratification B S hS X Z).1 ↦
          yoneda.map (p r) ≫ k) (yonedaEquiv.symm_apply_apply h)))
  have hstep : (yonedaEquiv.symm z ≫ ((algebraicSpacesToSheaf B S hS).map
        (Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r)).hom) ≫
      (fittingRankStratificationHom B S hS X Z).hom = yoneda.map (p r) ≫ f.hom := by
    rw [hfac0]
    exact (Category.assoc _ _ _).trans
      (congrArg (fun k : yoneda.obj T ⟶ X.1 ↦ yoneda.map (p r) ≫ k) hh)
  have hfac : yonedaEquiv.symm z ≫ (fittingRankStratum B S hS X Z r).ι =
      (schemeSpaceMap (p r) ≫ f).hom := by
    rw [← hres]
    exact (Category.assoc _ _ _).symm.trans hstep
  -- clause (3) of Stacks 0CZ9 gives the rank `r` of `G` on the piece
  have hrk := (existsUnique_lift_fittingRankStratum_iff B S hS G hGqc hGft Z hZ r
    (schemeSpaceMap (p r) ≫ f)).2
      ⟨yonedaEquiv.symm z, hfac, fun y hy ↦
        (cancel_mono (fittingRankStratum B S hS X Z r).ι).1 (hy.trans hfac.symm)⟩
  exact (isFlatOver_iff_of_iso B S hS (schemeSpace (W r)).2
    (𝟙 (schemeSpace (W r)) : schemeSpace (W r) ⟶ schemeSpace (W r)).hom
    (modulePullbackCompIsoApp B S hS X G (schemeSpaceMap (p r)) f)).2
    (isFlatOver_id_of_isFiniteLocallyFreeOfRank B S hS (schemeSpace (W r))
      ((modulePullback B S hS (schemeSpaceMap (p r) ≫ f)).obj G)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ G hGqc) r hrk)

/-! ### The flatness clause, and Stacks 0CZA -/

/-- **The flatness clause of Stacks 0CZA.**  Let `X` be an algebraic space over `S`, let `G` be
a quasi-coherent `𝒪_X`-module of finite presentation and let `X ⊇ Z_0 ⊇ Z_1 ⊇ …` be the chain of
closed subspaces cut out by the Fitting ideal sheaves of `G`.  For a test object `T` of the site
and a morphism `f : h_T ⟶ X`, the pullback `G_T` is flat over `T` in the sense of Stacks 05VV
exactly when `f` factors, necessarily uniquely, through the disjoint union
`X' = ∐_{r ≥ 0} X_r` of the strata.

So `X'` represents the functor of Stacks 0CZA: the set of factorisations is a one-point set
when `G_T` is flat over `T`, and — since a factorisation is automatically unique, `π` being a
monomorphism — empty otherwise. -/
theorem isFlatOver_modulePullback_iff_existsUnique_hom_lift
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r)
    (T : BigFppfOver B S hS) (f : schemeSpace T ⟶ X) :
    IsFlatOver B S hS (schemeSpace T).2
        (𝟙 (schemeSpace T) : schemeSpace T ⟶ schemeSpace T).hom
        ((modulePullback B S hS f).obj G) ↔
      ∃! h : yoneda.obj T ⟶ (fittingRankStratification B S hS X Z).1,
        h ≫ (fittingRankStratificationHom B S hS X Z).hom = f.hom := by
  have hGft : SheafOfModules.IsFiniteTypeOnSite G := by
    have := hGfp
    infer_instance
  refine ⟨existsUnique_hom_lift_fittingRankStratification_of_isFlatOver B S hS X G hGqc hGfp
    Z hZ T f, fun hlift ↦ ?_⟩
  obtain ⟨h, hh, -⟩ := hlift
  exact isFlatOver_of_hom_lift_fittingRankStratification B S hS X G hGqc hGft Z hZ T f h hh

/-- **The flatness clause of Stacks 0CZA, with mere existence of the factorisation.**  Since
`π` is a monomorphism a factorisation through `X'` is automatically unique, so the value of the
functor of Stacks 0CZA at a test object really is empty when `G_T` is not flat over `T`. -/
theorem isFlatOver_modulePullback_iff_exists_hom_lift
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r)
    (T : BigFppfOver B S hS) (f : schemeSpace T ⟶ X) :
    IsFlatOver B S hS (schemeSpace T).2
        (𝟙 (schemeSpace T) : schemeSpace T ⟶ schemeSpace T).hom
        ((modulePullback B S hS f).obj G) ↔
      ∃ h : yoneda.obj T ⟶ (fittingRankStratification B S hS X Z).1,
        h ≫ (fittingRankStratificationHom B S hS X Z).hom = f.hom := by
  have hGft : SheafOfModules.IsFiniteTypeOnSite G := by
    have := hGfp
    infer_instance
  refine ⟨fun hflat ↦ ?_, fun ⟨h, hh⟩ ↦
    isFlatOver_of_hom_lift_fittingRankStratification B S hS X G hGqc hGft Z hZ T f h hh⟩
  obtain ⟨h, hh, -⟩ := (isFlatOver_modulePullback_iff_existsUnique_hom_lift B S hS X G hGqc
    hGfp Z hZ T f).1 hflat
  exact ⟨h, hh⟩

/-- **Stacks 0CZA.**  Let `X` be an algebraic space over a scheme `S` contained in a big fppf
site `B` and let `G` be a quasi-coherent `𝒪_X`-module of finite presentation.  Then the Fitting
ideal sheaves of `G` cut out a decreasing chain of closed subspaces
`X = Z_{-1} ⊇ Z_0 ⊇ Z_1 ⊇ …` with empty intersection, the strata `X_r = Z_{r-1} ∖ Z_r` are
pairwise disjoint locally closed subspaces of `X` and every point of `X` lies in exactly one of
them, the disjoint union `X' = ∐_{r ≥ 0} X_r` is an algebraic space over `S` whose structural
morphism restricts on the `r`-th summand to the inclusion of `X_r`, and

1. `X'` **represents the functor** sending a test object `f : h_T ⟶ X` of the site to a
   one-point set when `G_T` is flat over `T` in the sense of Stacks 05VV and to the empty set
   otherwise;
2. the pullback of `G` to `X_r` is finite locally free of rank `r`;
3. both `X_r ⟶ X` and `X' ⟶ X` are of finite presentation.

The hypotheses are exactly the ones Stacks 0CZA makes. -/
@[stacks 0CZA]
theorem exists_fittingRankStratification_flat_spec (hGqc : G.IsQuasicoherentOnSite)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite G) :
    ∃ Z : ℕ → ClosedSubspaces B S hS X.1,
      (∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) ∧
      (Antitone fun r ↦ (Z r).1) ∧
      (⨅ r : ℕ, (Z r).1) = (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS) ∧
      (∀ r : ℕ, IsLocallyClosedSubspace B S hS (fittingRankStratum B S hS X Z r)) ∧
      (∀ r s : ℕ, r ≠ s →
        fittingRankStratum B S hS X Z r ⊓ fittingRankStratum B S hS X Z s ≤
          (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS)) ∧
      (∀ x : points B S hS X.1, ∃! r : ℕ,
        x ∉ Set.range (pointsMap B S hS (Z r).1.toFunctor (Z r).1.ι) ∧
          ∀ k < r, x ∈ Set.range (pointsMap B S hS (Z k).1.toFunctor (Z k).1.ι)) ∧
      IsAlgebraicSpace B S hS (fittingRankStratification B S hS X Z).obj ∧
      (∀ r : ℕ, Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r ≫
          fittingRankStratificationHom B S hS X Z = fittingRankStratumHom B S hS X Z r) ∧
      (∀ (T : BigFppfOver B S hS) (f : schemeSpace T ⟶ X),
        IsFlatOver B S hS (schemeSpace T).2
            (𝟙 (schemeSpace T) : schemeSpace T ⟶ schemeSpace T).hom
            ((modulePullback B S hS f).obj G) ↔
          ∃! h : yoneda.obj T ⟶ (fittingRankStratification B S hS X Z).1,
            h ≫ (fittingRankStratificationHom B S hS X Z).hom = f.hom) ∧
      (∀ r : ℕ, RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite B S hS (fittingRankStratumSpace B S hS X Z r).1
          (fittingRankStratumSpace B S hS X Z r).2)
        ((modulePullback B S hS (fittingRankStratumHom B S hS X Z r)).obj G) r) ∧
      (∀ r : ℕ, IsFinitePresentation B S hS (fittingRankStratum B S hS X Z r).ι) ∧
      IsFinitePresentation B S hS (fittingRankStratificationHom B S hS X Z).hom := by
  obtain ⟨Z, hZ, hanti, hbot, hlc, hdisj, hcover, halg, hres, hrank, hfppres, hfpstrat⟩ :=
    exists_fittingRankStratification_spec B S hS X G hGqc hGfp
  exact ⟨Z, hZ, hanti, hbot, hlc, hdisj, hcover, halg, hres,
    fun T f ↦ isFlatOver_modulePullback_iff_existsUnique_hom_lift B S hS X G hGqc hGfp Z hZ T f,
    hrank, hfppres, hfpstrat⟩

end AlgebraicGeometry.Space

end
