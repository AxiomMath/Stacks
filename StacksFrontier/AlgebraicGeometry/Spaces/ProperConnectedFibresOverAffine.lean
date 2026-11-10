module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ClopenFibreSpreading
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubsetsOfStructureMapIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective

/-!
# Connected fibres of a proper morphism with `f_* 𝒪_X = 𝒪_Y` over a Noetherian affine base

Let `T` be an object of the big fppf site of `S` whose scheme is affine and locally Noetherian,
and let `f : X ⟶ T` be a proper morphism of algebraic spaces whose structure map
`𝒪_T ⟶ f_* 𝒪_X` is an isomorphism.  Then every fibre `f⁻¹(t) ⊆ |X|` is preconnected.  This is
the connectedness assertion of the Stein factorization (Stacks 0A1B, clause (1)) over an affine
base, proved without the theorem on formal functions.

## The argument

Suppose the fibre over `t` meets two closed sets `P₀, Q₀ ⊆ |X|` which cover it and are disjoint
on it.  By Chow's lemma there is a proper surjection `ρ : V ⟶ X` from a scheme; the preimages
`P, Q ⊆ V` cover the fibre of the proper morphism of schemes `V ⟶ T` and are disjoint on it, so
after an étale base change `(U, u) ⟶ (T, t)` the split of the fibre spreads to an open and closed
subset `A` of `V ×_T U`
(`Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isProper`). The images of `A`
and of its complement in `X_U = X ×_T U` are closed and cover `X_U`; they are
disjoint above `u`, hence above a neighbourhood `U'` of `u`, the set of points where they meet
being closed with closed image.  So `X_{U'}` is split by an open and closed subset, which by
`f_* 𝒪 = 𝒪` (preserved by the flat base change `U' ⟶ T`) is the preimage of a subset of `U'`
(`AlgebraicGeometry.Space.exists_preimage_eq_of_isClopen_of_isIso_fSharp`).  But the fibre over
`u` contains points of both pieces.

## Main results

* `AlgebraicGeometry.Space.iff_mem_of_isClosed_cover_of_isIso_fSharp`: the last step, for a
  closed cover of the source of a morphism with `f_* 𝒪 = 𝒪` which is disjoint above an open
  neighbourhood of a point.
* `AlgebraicGeometry.Space.isPreconnected_fibre_of_isProper_of_isIso_fSharp`: the statement above.

## References

* [Stacks Project, Tag 0A1B](https://stacks.math.columbia.edu/tag/0A1B)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 03H0](https://stacks.math.columbia.edu/tag/03H0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphism of spaces induced by an étale morphism of the site is flat. -/
private theorem isFlat_schemeSpaceMap_of_etale {T T₂ : BigFppfOver B S hS} (ν : T₂ ⟶ T)
    (hνet : Etale ((BigFppfOver.toScheme B S hS).map ν)) : IsFlat B S hS (schemeSpaceMap ν).hom :=
  isFlat_of_presheafEtale B S hS ((presheaf_yoneda_map_iff B S hS
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange ν).2 hνet)

/-- Every point of a scheme of the site lies in the image of an affine open immersion from a
scheme of the site, landing in any given open neighbourhood of it. -/
private theorem exists_siteObject_affine_isOpenImmersion_of_isOpen {T : BigFppfOver B S hS}
    (t : (BigFppfOver.toScheme B S hS).obj T) {W : Set ((BigFppfOver.toScheme B S hS).obj T)}
    (hW : IsOpen W) (ht : t ∈ W) :
    ∃ (T₂ : BigFppfOver B S hS) (ν : T₂ ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T₂) ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ν) ∧
      IsFlat B S hS (schemeSpaceMap ν).hom ∧
      (∀ y, (BigFppfOver.toScheme B S hS).map ν y ∈ W) ∧
      ∃ t₂, (BigFppfOver.toScheme B S hS).map ν t₂ = t := by
  obtain ⟨_, ⟨O₀, hO₀, rfl⟩, htO, hOW⟩ :=
    ((BigFppfOver.toScheme B S hS).obj T).isBasis_affineOpens.exists_subset_of_mem_open ht hW
  let O : ((BigFppfOver.toScheme B S hS).obj T).Opens := O₀
  have hOc : B.Contains O.toScheme := Scheme.size_lt_of_isOpenImmersion O.ι T.left.property
  obtain ⟨T₂, ν, e, hν⟩ := exists_siteObject_toScheme_map_eq B S hS hOc O.ι
  have hopen : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ν) := by
    rw [hν]; infer_instance
  have : IsAffine O.toScheme := hO₀
  let tO : O.toScheme := ⟨t, htO⟩
  refine ⟨T₂, ν, IsAffine.of_isIso e.hom, hopen, isFlat_schemeSpaceMap_of_etale ν inferInstance,
    fun y => hOW ?_, e.inv tO, ?_⟩
  · rw [hν, Scheme.Hom.comp_apply]
    exact (e.hom _).2
  · rw [hν, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.inv e.hom, Iso.inv_hom_id]
    rfl

/-- In a base change of `f` along `ν`, the two projections of a point lie over the same point. -/
private theorem pointsToScheme_pointsMap_pullback {T T₂ : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T) (ν : T₂ ⟶ T)
    (y : points B S hS (pullback f (schemeSpaceMap ν)).obj) :
    pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom
        (pointsMap B S hS _ (pullback.fst f (schemeSpaceMap ν)).hom y)) =
      (BigFppfOver.toScheme B S hS).map ν
        (pointsToScheme B S hS T₂
          (pointsMap B S hS _ (pullback.snd f (schemeSpaceMap ν)).hom y)) := by
  have hw : (pullback.fst f (schemeSpaceMap ν)).hom ≫ f.hom =
      (pullback.snd f (schemeSpaceMap ν)).hom ≫ yoneda.map ν :=
    congrArg (·.hom) (pullback.condition (f := f) (g := schemeSpaceMap ν))
  have e₁ := congrFun (pointsMap_comp B S hS _ (pullback.fst f (schemeSpaceMap ν)).hom f.hom) y
  have e₂ := congrFun (pointsMap_comp B S hS _ (pullback.snd f (schemeSpaceMap ν)).hom
    (yoneda.map ν)) y
  have h₁ := e₁.symm.trans ((congrArg (fun m => pointsMap B S hS _ m y) hw).trans e₂)
  exact (congrArg (pointsToScheme B S hS T) h₁).trans (pointsToScheme_pointsMap_yoneda B S hS ν _)

/-- A point of `X` over a point of `T` in the image of `ν` lifts to a point of the base change of
`f` along `ν` lying over any given preimage of it. -/
private theorem exists_point_pullback_of_pointsToScheme_eq {T T₂ : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T) (ν : T₂ ⟶ T)
    (t₂ : (BigFppfOver.toScheme B S hS).obj T₂) (x : points B S hS X.obj)
    (hx : pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) =
      (BigFppfOver.toScheme B S hS).map ν t₂) :
    ∃ y, pointsMap B S hS _ (pullback.fst f (schemeSpaceMap ν)).hom y = x ∧
      pointsToScheme B S hS T₂ (pointsMap B S hS _ (pullback.snd f (schemeSpaceMap ν)).hom y) =
        t₂ := by
  obtain ⟨p, hp⟩ := surjective_pointsToScheme B S hS T₂ t₂
  have hcomp : pointsMap B S hS X.obj f.hom x =
      pointsMap B S hS (schemeSpace T₂).obj (schemeSpaceMap ν).hom p := by
    refine injective_pointsToScheme B S hS T (hx.trans ?_)
    exact (congrArg _ hp).symm.trans (pointsToScheme_pointsMap_yoneda B S hS ν p).symm
  obtain ⟨y, hy₁, hy₂⟩ := exists_point_of_isPullback B S hS
    (IsPullback.of_hasPullback f (schemeSpaceMap ν)) x p hcomp
  exact ⟨y, hy₁, (congrArg _ hy₂).trans hp⟩

/-- Points of the scheme of a site object, read in a space `X` over it through a morphism `ρ`
with `ρ ≫ f = yoneda.map m`, lie over the image under `m`. -/
private theorem pointsToScheme_pointsMap_pointsEquivScheme_symm {V W : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ρ : yoneda.obj V ⟶ X) (f : X ⟶ yoneda.obj W)
    (m : V ⟶ W) (hm : ρ ≫ f = yoneda.map m) (v : (BigFppfOver.toScheme B S hS).obj V) :
    pointsToScheme B S hS W (pointsMap B S hS X f
        (pointsMap B S hS (yoneda.obj V) ρ ((pointsEquivScheme B S hS V).symm v))) =
      (BigFppfOver.toScheme B S hS).map m v := by
  have h₁ := (congrFun (pointsMap_comp B S hS _ ρ f)
    ((pointsEquivScheme B S hS V).symm v)).symm.trans
    (congrArg (fun k => pointsMap B S hS (yoneda.obj V) k
      ((pointsEquivScheme B S hS V).symm v)) hm)
  refine (congrArg (pointsToScheme B S hS W) h₁).trans ?_
  rw [pointsToScheme_pointsMap_yoneda]
  congr 1
  exact (pointsEquivScheme B S hS V).apply_symm_apply v

/-- **A closed cover of the source of a morphism with `f_* 𝒪 = 𝒪` which is disjoint above a
neighbourhood of a point does not separate the fibre over that point.**  Let `f : X ⟶ Z` be
quasi-compact and quasi-separated with `𝒪_Z ⟶ f_* 𝒪_X` an isomorphism, `Z` a scheme of the site,
and let `C₁, C₂ ⊆ |X|` be closed, covering `|X|`, and meeting only above a closed subset `E` of
`Z`.  Then two points of `X` over the same point `z ∉ E` are both in `C₁` or both outside it.

Over an affine open neighbourhood `O` of `z` missing `E` the cover is a decomposition into open
and closed pieces; `f_* 𝒪 = 𝒪` survives the flat base change to `O`, so the piece `C₁` is the
preimage of a subset of `O` there. -/
theorem iff_mem_of_isClosed_cover_of_isIso_fSharp {Z : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace Z) (hqc : IsQuasiCompact B S hS f.hom)
    (hqs : IsQuasiSeparated B S hS f.hom) [IsIso (smallEtaleRingedToposHom B S hS f).fSharp]
    (C₁ C₂ : Set (points B S hS X.obj)) (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (hcov : C₁ ∪ C₂ = Set.univ) (E : Set ((BigFppfOver.toScheme B S hS).obj Z))
    (hE : IsClosed E)
    (hD : ∀ x ∈ C₁ ∩ C₂, pointsToScheme B S hS Z (pointsMap B S hS X.obj f.hom x) ∈ E)
    (z : (BigFppfOver.toScheme B S hS).obj Z) (hz : z ∉ E) (x₁ x₂ : points B S hS X.obj)
    (hx₁ : pointsToScheme B S hS Z (pointsMap B S hS X.obj f.hom x₁) = z)
    (hx₂ : pointsToScheme B S hS Z (pointsMap B S hS X.obj f.hom x₂) = z) :
    x₁ ∈ C₁ ↔ x₂ ∈ C₁ := by
  -- an affine open neighbourhood of `z` missing `E`, as an object of the site
  obtain ⟨Z₂, ν, -, -, hflat, hνE, z₂, hz₂⟩ :=
    exists_siteObject_affine_isOpenImmersion_of_isOpen z hE.isOpen_compl hz
  -- the base change of `f` to it
  have : IsIso (smallEtaleRingedToposHom B S hS (pullback.snd f (schemeSpaceMap ν))).fSharp :=
    isIso_fSharp_of_isPullback_of_isFlat (IsPullback.of_hasPullback f (schemeSpaceMap ν)) hqc hqs
      hflat
  let j := pullback.fst f (schemeSpaceMap ν)
  let g := pullback.snd f (schemeSpaceMap ν)
  -- the preimage of `C₁` is open and closed
  let C : Set (points B S hS (pullback f (schemeSpaceMap ν)).obj) :=
    pointsMap B S hS _ j.hom ⁻¹' C₁
  have hCc : Cᶜ = pointsMap B S hS _ j.hom ⁻¹' C₂ := by
    ext y
    simp only [C, Set.mem_compl_iff, Set.mem_preimage]
    constructor
    · intro hy
      have : pointsMap B S hS _ j.hom y ∈ C₁ ∪ C₂ := hcov ▸ Set.mem_univ _
      exact this.resolve_left hy
    · intro hy hy₁
      have := hD _ ⟨hy₁, hy⟩
      rw [pointsToScheme_pointsMap_pullback] at this
      exact hνE _ this
  have hC : IsClopen C := by
    refine ⟨h₁.preimage (continuous_pointsMap B S hS _), ?_⟩
    rw [← isClosed_compl_iff, hCc]
    exact h₂.preimage (continuous_pointsMap B S hS _)
  obtain ⟨D, hD'⟩ := exists_preimage_eq_of_isClopen_of_isIso_fSharp g C hC
  -- lifts of the two points over the point of `O` above `z`
  obtain ⟨y₁, hy₁, hy₁'⟩ :=
    exists_point_pullback_of_pointsToScheme_eq f ν z₂ x₁ (hx₁.trans hz₂.symm)
  obtain ⟨y₂, hy₂, hy₂'⟩ :=
    exists_point_pullback_of_pointsToScheme_eq f ν z₂ x₂ (hx₂.trans hz₂.symm)
  have h1 : x₁ ∈ C₁ ↔ y₁ ∈ C := by rw [← hy₁]; exact Iff.rfl
  have h2 : x₂ ∈ C₁ ↔ y₂ ∈ C := by rw [← hy₂]; exact Iff.rfl
  rw [h1, h2, hD' y₁, hD' y₂, hy₁', hy₂']

/-- The comparison of the points of a scheme of the site with the points of its representable
presheaf is a homeomorphism; in particular its inverse is continuous. -/
theorem continuous_pointsEquivScheme_symm (V : BigFppfOver B S hS) :
    Continuous (pointsEquivScheme B S hS V).symm := by
  rw [continuous_def]
  intro W hW
  have h := (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS V W).1 hW
  have he : pointsToScheme B S hS V '' W = (pointsEquivScheme B S hS V).symm ⁻¹' W :=
    (pointsEquivScheme B S hS V).image_eq_preimage_symm W
  rwa [he] at h

/-- The inverse comparison of points of a scheme of the site is a closed map. -/
theorem isClosedMap_pointsEquivScheme_symm (V : BigFppfOver B S hS) :
    IsClosedMap (pointsEquivScheme B S hS V).symm := by
  intro W hW
  rw [isClosed_pointTopology_yoneda_iff_isClosed_image, Equiv.image_symm_eq_preimage]
  have : pointsToScheme B S hS V '' (pointsToScheme B S hS V ⁻¹' W) = W :=
    Set.image_preimage_eq W (surjective_pointsToScheme B S hS V)
  change IsClosed (pointsToScheme B S hS V '' (pointsToScheme B S hS V ⁻¹' W))
  rwa [this]

/-- **The fibres of a proper morphism with `f_* 𝒪_X = 𝒪_T` over a Noetherian affine scheme of
the site are preconnected.**  Let `T` be an object of the big fppf site of `S` with affine and
locally Noetherian scheme, and let `f : X ⟶ T` be proper with `𝒪_T ⟶ f_* 𝒪_X` an isomorphism.
Then for every point `t` of `T` the fibre `{x ∈ |X| : f(x) = t}` is preconnected; see the module
documentation for the argument. -/
theorem isPreconnected_fibre_of_isProper_of_isIso_fSharp {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom)
    [IsIso (smallEtaleRingedToposHom B S hS f).fSharp]
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    IsPreconnected {x : points B S hS X.obj |
      pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) = t} := by
  classical
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro P₀ Q₀ hP₀ hQ₀ hcov hdisj
  by_contra hcon
  rw [not_or, Set.not_subset, Set.not_subset] at hcon
  obtain ⟨⟨x₁, hx₁F, hx₁P⟩, ⟨x₂, hx₂F, hx₂Q⟩⟩ := hcon
  have hx₂P : x₂ ∈ P₀ := (hcov hx₂F).resolve_right hx₂Q
  let Tsch := (BigFppfOver.toScheme B S hS).obj T
  -- Chow's lemma
  obtain ⟨V, ρ, hρP, hρS⟩ := exists_properSurjective_schemeCover_of_isProper_toAffine B S hS T
    inferInstance X.property f.hom hf
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  let m : V ⟶ T := yoneda.preimage (ρ ≫ f.hom)
  have hm : yoneda.map m = ρ ≫ f.hom := yoneda.map_preimage _
  have hcompP : IsProper B S hS (ρ ≫ f.hom) :=
    isProper_comp B S hS hVsp X.property hT ρ f.hom hρP hf
  have hmProper : AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map m) := by
    have hpre : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map m) := by
      rw [hm]
      exact (presheaf_isProper_iff B S hS (ρ ≫ f.hom) hVsp hT
        (by rw [← hm]; exact Functor.relativelyRepresentable.map yoneda m)).mp hcompP
    change (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda (yoneda.map m) at hpre
    have hpm := MorphismProperty.of_relative_map hpre
    exact hpm
  -- the scheme points of `V` read in `X`
  let ψ : (BigFppfOver.toScheme B S hS).obj V → points B S hS X.obj := fun v =>
    pointsMap B S hS (yoneda.obj V) ρ ((pointsEquivScheme B S hS V).symm v)
  have hψc : Continuous ψ :=
    (continuous_pointsMap B S hS ρ).comp (continuous_pointsEquivScheme_symm V)
  have hψT : ∀ v, pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom (ψ v)) =
      (BigFppfOver.toScheme B S hS).map m v :=
    pointsToScheme_pointsMap_pointsEquivScheme_symm ρ f.hom m hm.symm
  let P : Set ((BigFppfOver.toScheme B S hS).obj V) := ψ ⁻¹' P₀
  let Q : Set ((BigFppfOver.toScheme B S hS).obj V) := ψ ⁻¹' Q₀
  have hcov' : (BigFppfOver.toScheme B S hS).map m ⁻¹' {t} ⊆ P ∪ Q := by
    intro v hv
    exact hcov (show pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom (ψ v)) = t from
      (hψT v).trans hv)
  have hdisj' : (BigFppfOver.toScheme B S hS).map m ⁻¹' {t} ∩ (P ∩ Q) = ∅ := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hv hvP hvQ
    have : ψ v ∈ {x : points B S hS X.obj |
        pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) = t} ∩ (P₀ ∩ Q₀) :=
      ⟨(hψT v).trans hv, hvP, hvQ⟩
    rw [hdisj] at this
    exact this
  -- spread the split of the fibre of `V ⟶ T` over an étale neighbourhood
  obtain ⟨U, -, A, hA, hAp⟩ :=
    Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isProper
    ((BigFppfOver.toScheme B S hS).map m) t P Q (hP₀.preimage hψc) (hQ₀.preimage hψc) hcov' hdisj'
  obtain ⟨Zu, ν, κ, u', -, hκ, hκν, hνet, hκu, hνu⟩ :=
    exists_affine_siteObject_of_etaleNeighborhood B S hS (inferInstance : IsAffine Tsch) U
  -- the base change of `f` to `Zu`
  have hflat := isFlat_schemeSpaceMap_of_etale ν hνet
  let sq := IsPullback.of_hasPullback f (schemeSpaceMap ν)
  let X' := Limits.pullback f (schemeSpaceMap ν)
  let j := pullback.fst f (schemeSpaceMap ν)
  let g := pullback.snd f (schemeSpaceMap ν)
  have hfqc : IsQuasiCompact B S hS f.hom := hf.2.1.2
  have hfqs : IsQuasiSeparated B S hS f.hom := isQuasiSeparated_of_isSeparated B S hS hf.1
  have : IsIso (smallEtaleRingedToposHom B S hS g).fSharp :=
    isIso_fSharp_of_isPullback_of_isFlat sq hfqc hfqs hflat
  have sqP : IsPullback j.hom g.hom f.hom (yoneda.map ν) := sq.map (ObjectProperty.ι _)
  have hZu := isAlgebraicSpace_yoneda B S hS Zu
  have hgqc : IsQuasiCompact B S hS g.hom := isQuasiCompact_of_isPullback B S hS sqP hfqc
  have hgqs : IsQuasiSeparated B S hS g.hom := isQuasiSeparated_of_isPullback B S hS sqP hfqs
  have hguc : UniversallyClosed B S hS g.hom :=
    universallyClosed_of_isPullback B S hS X'.property X.property hZu hT f.hom (yoneda.map ν)
      hf.2.2 sqP.flip
  -- the base change of the Chow cover, as a scheme of the site
  let hrep : yoneda.relativelyRepresentable (yoneda.map m) :=
    Functor.relativelyRepresentable.map yoneda m
  let Vp := hrep.pullback (yoneda.map ν)
  let a : Vp ⟶ V := hrep.fst' (yoneda.map ν)
  let b : Vp ⟶ Zu := hrep.snd (yoneda.map ν)
  have hab : a ≫ m = b ≫ ν := hrep.w' ν
  have hVp : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map m) (yoneda.map ν) :=
    hrep.isPullback' (yoneda.map ν)
  let ρ' : yoneda.obj Vp ⟶ X'.obj := sqP.lift (yoneda.map a ≫ ρ) (yoneda.map b)
    ((Category.assoc _ _ _).trans ((congrArg (yoneda.map a ≫ ·) hm.symm).trans
      ((yoneda.map_comp a m).symm.trans ((congrArg yoneda.map hab).trans
        (yoneda.map_comp b ν)))))
  have hρ'j : ρ' ≫ j.hom = yoneda.map a ≫ ρ := sqP.lift_fst _ _ _
  have hρ'g : ρ' ≫ g.hom = yoneda.map b := sqP.lift_snd _ _ _
  have hsqρ : IsPullback (yoneda.map a) ρ' ρ j.hom := by
    refine IsPullback.of_bot ?_ hρ'j.symm sqP
    rw [hρ'g, ← hm]
    exact hVp
  have hρ'uc : UniversallyClosed B S hS ρ' :=
    universallyClosed_of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS Vp) hVsp
      X'.property X.property ρ j.hom hρP.2.2 hsqρ.flip
  have hρ'surj : Function.Surjective (pointsMap B S hS (yoneda.obj Vp) ρ') :=
    surjective_pointsMap_of_isPullback B S hS hsqρ hρS
  -- the clopen subset of the base change of the Chow cover
  let lam : (BigFppfOver.toScheme B S hS).obj Vp ⟶
      Limits.pullback ((BigFppfOver.toScheme B S hS).map m) U.toBase :=
    pullback.lift ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b ≫ κ) (by
        rw [Category.assoc, hκν, ← Functor.map_comp, ← Functor.map_comp, hab])
  let A' : Set ((BigFppfOver.toScheme B S hS).obj Vp) := lam ⁻¹' A
  have hA' : IsClopen A' := hA.preimage lam.continuous
  have hA'p : ∀ z, (BigFppfOver.toScheme B S hS).map b z = u' →
      (z ∈ A' ↔ (BigFppfOver.toScheme B S hS).map a z ∈ P) := by
    intro z hz
    have hsnd : pullback.snd ((BigFppfOver.toScheme B S hS).map m) U.toBase (lam z) = U.point := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply, hz, hκu]
    have hfst : pullback.fst ((BigFppfOver.toScheme B S hS).map m) U.toBase (lam z) =
        (BigFppfOver.toScheme B S hS).map a z := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    change lam z ∈ A ↔ _
    rw [hAp (lam z) hsnd, hfst]
  -- the points of the base change of the Chow cover, read in `X'`
  let ψ' : (BigFppfOver.toScheme B S hS).obj Vp → points B S hS X'.obj := fun z =>
    pointsMap B S hS (yoneda.obj Vp) ρ' ((pointsEquivScheme B S hS Vp).symm z)
  have hψ'j : ∀ z, pointsMap B S hS X'.obj j.hom (ψ' z) =
      ψ ((BigFppfOver.toScheme B S hS).map a z) := by
    intro z
    have h₁ := (congrFun (pointsMap_comp B S hS _ ρ' j.hom)
      ((pointsEquivScheme B S hS Vp).symm z)).symm.trans
      ((congrArg (fun k => pointsMap B S hS (yoneda.obj Vp) k
        ((pointsEquivScheme B S hS Vp).symm z)) hρ'j).trans
      (congrFun (pointsMap_comp B S hS _ (yoneda.map a) ρ) ((pointsEquivScheme B S hS Vp).symm z)))
    refine h₁.trans (congrArg (pointsMap B S hS (yoneda.obj V) ρ) ?_)
    apply injective_pointsToScheme B S hS V
    rw [pointsToScheme_pointsMap_yoneda]
    change (BigFppfOver.toScheme B S hS).map a (pointsEquivScheme B S hS Vp
      ((pointsEquivScheme B S hS Vp).symm z)) = pointsEquivScheme B S hS V
        ((pointsEquivScheme B S hS V).symm _)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hψ'g : ∀ z, pointsToScheme B S hS Zu (pointsMap B S hS X'.obj g.hom (ψ' z)) =
      (BigFppfOver.toScheme B S hS).map b z :=
    pointsToScheme_pointsMap_pointsEquivScheme_symm ρ' g.hom b hρ'g
  have hψ'surj : Function.Surjective ψ' :=
    hρ'surj.comp (pointsEquivScheme B S hS Vp).symm.surjective
  have hcl : ∀ K : Set ((BigFppfOver.toScheme B S hS).obj Vp), IsClosed K → IsClosed (ψ' '' K) := by
    intro K hK
    rw [show ψ' '' K = pointsMap B S hS (yoneda.obj Vp) ρ' ''
      ((pointsEquivScheme B S hS Vp).symm '' K) from (Set.image_image _ _ _).symm]
    exact isClosedMap_pointsMap_of_pullback_fst_id B S hS ρ'
      (hρ'uc X'.obj X'.property (𝟙 _)) _ (isClosedMap_pointsEquivScheme_symm Vp _ hK)
  let C₁ := ψ' '' A'
  let C₂ := ψ' '' A'ᶜ
  have hC₁ : IsClosed C₁ := hcl _ hA'.1
  have hC₂ : IsClosed C₂ := hcl _ hA'.2.isClosed_compl
  have hcovC : C₁ ∪ C₂ = Set.univ := by
    rw [← Set.image_union, Set.union_compl_self, Set.image_univ, hψ'surj.range_eq]
  let E : Set ((BigFppfOver.toScheme B S hS).obj Zu) :=
    pointsToScheme B S hS Zu '' (pointsMap B S hS X'.obj g.hom '' (C₁ ∩ C₂))
  have hE : IsClosed E := by
    have := isClosedMap_pointsMap_of_pullback_fst_id B S hS g.hom
      (hguc (schemeSpace Zu).obj (schemeSpace Zu).property (𝟙 _)) _ (hC₁.inter hC₂)
    exact (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS Zu _).1 this
  have hD : ∀ x ∈ C₁ ∩ C₂,
      pointsToScheme B S hS Zu (pointsMap B S hS X'.obj g.hom x) ∈ E :=
    fun x hx => ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  -- the key property of the pieces over `u'`
  have hkey : ∀ x : points B S hS X'.obj,
      pointsToScheme B S hS Zu (pointsMap B S hS X'.obj g.hom x) = u' →
      ∀ z, ψ' z = x → (z ∈ A' ↔ pointsMap B S hS X'.obj j.hom x ∈ P₀) := by
    intro x hx z hz
    have hbz : (BigFppfOver.toScheme B S hS).map b z = u' := by rw [← hψ'g, hz, hx]
    rw [hA'p z hbz, ← hz, hψ'j]
    exact Iff.rfl
  have hu' : u' ∉ E := by
    rintro ⟨_, ⟨x, ⟨⟨z₁, hz₁, hz₁x⟩, ⟨z₂, hz₂, hz₂x⟩⟩, rfl⟩, hxu⟩
    exact hz₂ ((hkey x hxu z₂ hz₂x).2
      ((hkey x hxu z₁ hz₁x).1 hz₁))
  -- the two points over `u'`
  obtain ⟨pu, hpu⟩ := surjective_pointsToScheme B S hS Zu u'
  obtain ⟨x₁', hx₁j, hx₁g⟩ :=
    exists_point_pullback_of_pointsToScheme_eq f ν u' x₁ (Eq.trans hx₁F hνu.symm)
  obtain ⟨x₂', hx₂j, hx₂g⟩ :=
    exists_point_pullback_of_pointsToScheme_eq f ν u' x₂ (Eq.trans hx₂F hνu.symm)
  have h₂ : x₂' ∈ C₁ := by
    obtain ⟨z, hz⟩ := hψ'surj x₂'
    exact ⟨z, (hkey x₂' hx₂g z hz).2 (hx₂j ▸ hx₂P), hz⟩
  have h₁ : x₁' ∉ C₁ := by
    intro h
    obtain ⟨z, hz⟩ := hψ'surj x₁'
    have hz₂ : z ∈ A'ᶜ := fun hzA => hx₁P (hx₁j ▸ (hkey x₁' hx₁g z hz).1 hzA)
    exact hu' (hx₁g ▸ hD x₁' ⟨h, z, hz₂, hz⟩)
  exact h₁ ((iff_mem_of_isClosed_cover_of_isIso_fSharp g hgqc hgqs C₁ C₂ hC₁ hC₂ hcovC E hE hD
    u' hu' x₁' x₂' hx₁g hx₂g).2 h₂)

/-- **The fibres of a proper morphism with `f_* 𝒪_X = 𝒪_T` over a locally Noetherian scheme of
the site are preconnected.**  The fibre over `t` is the image of the fibre of the base change to
an affine open neighbourhood of `t`, which is preconnected by
`AlgebraicGeometry.Space.isPreconnected_fibre_of_isProper_of_isIso_fSharp`: the base change of
`f` to the open neighbourhood is proper, with `f_* 𝒪 = 𝒪` by flat base change. -/
theorem isPreconnected_fibre_of_isProper_of_isIso_fSharp' {T : BigFppfOver B S hS}
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom)
    [IsIso (smallEtaleRingedToposHom B S hS f).fSharp]
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    IsPreconnected {x : points B S hS X.obj |
      pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) = t} := by
  obtain ⟨T₂, ν, haff, hopen, hflat, -, t₂, ht₂⟩ :=
    exists_siteObject_affine_isOpenImmersion_of_isOpen t isOpen_univ (Set.mem_univ t)
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T₂) :=
    isLocallyNoetherian_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map ν)
  let j := pullback.fst f (schemeSpaceMap ν)
  let g := pullback.snd f (schemeSpaceMap ν)
  have hfqc : IsQuasiCompact B S hS f.hom := hf.2.1.2
  have hfqs : IsQuasiSeparated B S hS f.hom := isQuasiSeparated_of_isSeparated B S hS hf.1
  have : IsIso (smallEtaleRingedToposHom B S hS g).fSharp :=
    isIso_fSharp_of_isPullback_of_isFlat (IsPullback.of_hasPullback f (schemeSpaceMap ν))
      hfqc hfqs hflat
  have hg : IsProper B S hS g.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback
      (IsPullback.of_hasPullback f (schemeSpaceMap ν)) hf
  have hpre := isPreconnected_fibre_of_isProper_of_isIso_fSharp g hg t₂
  have heq : {x : points B S hS X.obj |
      pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) = t} =
      pointsMap B S hS _ j.hom '' {y | pointsToScheme B S hS T₂
        (pointsMap B S hS _ g.hom y) = t₂} := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy₁, hy₂⟩ :=
        exists_point_pullback_of_pointsToScheme_eq f ν t₂ x (hx.trans ht₂.symm)
      exact ⟨y, hy₂, hy₁⟩
    · rintro ⟨y, hy, rfl⟩
      change pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom (pointsMap B S hS _ j.hom y)) = t
      rw [pointsToScheme_pointsMap_pullback, hy, ht₂]
  rw [heq]
  exact hpre.image _ (continuous_pointsMap B S hS j.hom).continuousOn

end AlgebraicGeometry.Space

end
