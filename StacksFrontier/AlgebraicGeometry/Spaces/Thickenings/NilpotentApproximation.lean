module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Comap
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# A closed subspace with all the points of a separated space, as a limit of finite-order ones

Let `W` be an algebraic space over `S` and let `Z ⊆ W` be a closed subspace with the same points
as `W`. Let `φ : V ⟶ W` be a surjective étale chart with `V` affine, and suppose the relation
`R = V ×_W V` is affine (this holds as soon as `W` is separated,
`AlgebraicGeometry.Space.isAffine_of_isAbsolutelySeparated`). Let `I` be the chart ideal of `Z`,
an ideal of `Γ(V, 𝒪)` consisting of nilpotent functions. This file writes `Z` as the intersection
of a directed family of closed subspaces `Z_G ⊇ Z` of `W`, each of which has a **nilpotent** chart
ideal. Here `G` runs through the finite subsets of `I`.

The stage `Z_G` is the scheme-theoretic image in `W` of the closed subscheme `V(G) ⊆ V` under
`φ`. No invariant ideal has to be produced by hand, and no Noetherian approximation is used. Its
chart ideal `K_G` is the kernel of `Γ(V, 𝒪) → Γ(V(G) ×_W V, 𝒪)`, by Stacks 082Z part (2),
and this has two properties:
* `K_G ⊆ (G)`, because `V(G)` maps into `V(G) ×_W V` by its two inclusions into `V`. So `K_G`
  is nilpotent, `(G)` being a finitely generated ideal of nilpotents;
* every `f ∈ I` lies in some `K_G`. Indeed, the extensions of `I` along the two projections
  `s, t : R ⟶ V` agree, so `s^♯ f = Σ cᵢ t^♯ gᵢ` with `gᵢ ∈ I`; take `G = {gᵢ}`. Then `f` dies
  on `V(G) ×_W V`, which maps to `R` with target projection through `V(G)`.

This replaces, for the nil ideal of a thickening, the use of Stacks 0829 (and through it of
Noetherian approximation, Stacks 07SU) in Stacks 0A0U: the stages need not be of finite
presentation, but each of them is of finite order. That is what the thickening case of Stacks 07VT
needs.

## Main definitions

* `AlgebraicGeometry.Space.idealChart`, `AlgebraicGeometry.Space.idealChartι`: the closed subscheme
  `V(J)` of an affine object `V` of the site, as an object of the site over `V`.
* `AlgebraicGeometry.Space.idealImage`: the scheme-theoretic image in `W` of `V(J) ⟶ V ⟶ W`.
* `AlgebraicGeometry.Space.ApproxIndex`, `AlgebraicGeometry.Space.approxStage`: the index set
  (finite subsets of the chart ideal of `Z`) and the stages `Z_G`.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_idealImage`: the chart ideal of the image of `V(J)` is
  the kernel of pullback to `V(J) ×_W V`.
* `AlgebraicGeometry.Space.definingIdealAt_idealImage_le`: it is contained in `J`.
* `AlgebraicGeometry.Space.map_definingIdealAt_atlasRelationTarget_eq`: invariance of the chart
  ideal of a closed subspace under the relation `R`.
* `AlgebraicGeometry.Space.exists_finset_mem_definingIdealAt_idealImage`: every function in the
  chart ideal of `Z` lies in the chart ideal of some stage.
* `AlgebraicGeometry.Space.le_approxStage`, `AlgebraicGeometry.Space.approxStage_antitone` and
  `AlgebraicGeometry.Space.eq_iInf_approxStage`: `Z` is the intersection of the directed family of
  stages, each of which contains it.
* `AlgebraicGeometry.Space.chartIdealAt_le_nilradical` and
  `AlgebraicGeometry.Space.exists_chartKer_approxStage_pow_eq_bot`: when `Z` has all the points of
  `W`, the chart ideal of every stage is nilpotent.

## References

* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chart

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

/-- The closed subscheme `V(J)` cut out by an ideal of global functions on the affine object `V`,
as a subobject of the underlying scheme of `V`. -/
noncomputable abbrev idealSubobject (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    Subobject ((BigFppfOver.toScheme B S hS).obj V) :=
  Subobject.mk (Scheme.IdealSheafData.ofIdealTop J).subschemeι

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The subscheme `V(J)` is immersed in `V`. -/
theorem isImmersion_idealSubobject_arrow (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    AlgebraicGeometry.IsImmersion (idealSubobject B S hS J).arrow := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

/-- The closed subscheme `V(J)` as an object of the site. -/
noncomputable abbrev idealChart (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    BigFppfOver B S hS :=
  subschemeObject B S hS (idealSubobject B S hS J) (isImmersion_idealSubobject_arrow B S hS J)

/-- The inclusion of `V(J)` into `V`, as a morphism of the site. -/
noncomputable abbrev idealChartι (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    idealChart B S hS J ⟶ V :=
  subschemeι B S hS (idealSubobject B S hS J) (isImmersion_idealSubobject_arrow B S hS J)

/-- Pullback of regular functions along a morphism of schemes is unchanged, as to its kernel, by
precomposing with an isomorphism. -/
theorem ker_Γ_map_of_eq_iso_comp {X X' Y : Scheme.{u}} (e : X' ≅ X) (g : X ⟶ Y) (h : X' ⟶ Y)
    (he : h = e.hom ≫ g) :
    RingHom.ker (Scheme.Γ.map h.op).hom = RingHom.ker (Scheme.Γ.map g.op).hom := by
  subst he
  rw [op_comp, Functor.map_comp, CommRingCat.hom_comp]
  exact RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso (Scheme.Γ.map e.hom.op)).1

/-- Pullback of regular functions along `V(J) ⟶ V` has kernel `J`. -/
theorem ker_Γ_idealChartι (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (idealChartι B S hS J)).op).hom
      = J :=
  (ker_Γ_map_of_eq_iso_comp (Subobject.underlyingIso
      (Scheme.IdealSheafData.ofIdealTop J).subschemeι)
    (Scheme.IdealSheafData.ofIdealTop J).subschemeι
    ((BigFppfOver.toScheme B S hS).map (idealChartι B S hS J))
    (Subobject.underlyingIso_hom_comp_eq_mk _).symm).trans
    (Scheme.IdealSheafData.ker_appTop_subschemeι_ofIdealTop J)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The inclusion `V(J) ⟶ V` is a closed immersion of schemes. -/
theorem isClosedImmersion_toScheme_map_idealChartι
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (idealChartι B S hS J)) := by
  change AlgebraicGeometry.IsClosedImmersion (idealSubobject B S hS J).arrow
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

/-- The closed subscheme `V(J)` of the affine scheme `V` is affine. -/
instance isAffine_idealChart (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (idealChart B S hS J)) :=
  have := isClosedImmersion_toScheme_map_idealChartι B S hS J
  isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (idealChartι B S hS J))

/-- On an affine scheme, the ideal sheaf generated by an ideal of global functions is monotone
in the ideal. -/
theorem ofIdealTop_mono {J J' : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (h : J ≤ J') :
    Scheme.IdealSheafData.ofIdealTop J ≤ Scheme.IdealSheafData.ofIdealTop J' :=
  (Scheme.IdealSheafData.equivOfIsAffine
    (X := (BigFppfOver.toScheme B S hS).obj V)).symm.toOrderIso.monotone h

/-- A larger ideal cuts out a smaller closed subscheme. -/
theorem idealSubobject_le {J J' : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (h : J ≤ J') : idealSubobject B S hS J' ≤ idealSubobject B S hS J :=
  Subobject.mk_le_mk_of_comm (Scheme.IdealSheafData.inclusion (ofIdealTop_mono B S hS h))
    (by simp)

/-- For `J ≤ J'` the closed subscheme `V(J')` lies in `V(J)`, as a morphism of the site over
`V`. -/
noncomputable def idealChartMap {J J' : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (h : J ≤ J') : idealChart B S hS J' ⟶ idealChart B S hS J :=
  Over.homMk ⟨Subobject.ofLE _ _ (idealSubobject_le B S hS h)⟩
    (by ext; exact Subobject.ofLE_arrow_assoc _ _)

/-- The inclusion `V(J') ⟶ V(J)` lies over `V`. -/
@[reassoc (attr := simp)]
theorem idealChartMap_ι {J J' : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (h : J ≤ J') : idealChartMap B S hS h ≫ idealChartι B S hS J = idealChartι B S hS J' := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp]
  exact Subobject.ofLE_arrow _

end Chart

section Image

variable (W : AlgebraicSpaces B S hS) {V : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (φ : yoneda.obj V ⟶ W.1)

/-- The composite `V(J) ⟶ V ⟶ W` of the inclusion of the closed subscheme cut out by `J` with
the chart. -/
noncomputable abbrev idealChartToSpace (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    yoneda.obj (idealChart B S hS J) ⟶ W.1 :=
  yoneda.map (idealChartι B S hS J) ≫ φ

/-- The scheme-theoretic image in `W` of `V(J) ⟶ V ⟶ W`. -/
noncomputable abbrev idealImage (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    ClosedSubspaces B S hS W.1 :=
  schemeTheoreticImage B S hS (idealChartToSpace B S hS W φ J) W.2

/-- The morphism `V(J) ⟶ W` is quasi-compact, `V(J)` being affine and `W` quasi-separated
(Stacks 073B, part (1)). -/
theorem isQuasiCompact_idealChartToSpace
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    IsQuasiCompact B S hS (idealChartToSpace B S hS W φ J) :=
  isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal W.2 hqs
    (isQuasiCompact_yoneda_of_compact B S hS _ inferInstance) _

variable {φ} (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

/-- The defining ideal of a closed subspace of `W` on the chart `V`, as an ideal of the global
functions on the affine scheme `V`. -/
noncomputable abbrev chartIdealAt (Z : ClosedSubspaces B S hS W.1) :
    Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  definingIdealAt B S hS W Z (op (chartOfSurjectiveEtale B S hS W he))

/-- **The defining ideal of the image on the chart.** On the chart `V` itself, the defining
ideal of the scheme-theoretic image of `V(J) ⟶ W` is the kernel of pullback of regular
functions along the projection `V(J) ×_W V ⟶ V`: Stacks 082Z, part (2), for this
quasi-compact morphism. -/
theorem definingIdealAt_idealImage
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    definingIdealAt B S hS W (idealImage B S hS W φ J)
        (op (chartOfSurjectiveEtale B S hS W he)) =
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS W.2
          (idealChartToSpace B S hS W φ J)).snd φ)).op).hom := by
  have h := congrArg (fun N => N.obj (op (chartOfSurjectiveEtale B S hS W he)))
    (definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf B S hS
      (ObjectProperty.homMk (idealChartToSpace B S hS W φ J) :
        (⟨_, isAlgebraicSpace_yoneda B S hS (idealChart B S hS J)⟩ : AlgebraicSpaces B S hS) ⟶
          W)
      (isQuasiCompact_idealChartToSpace B S hS W φ hqs J))
  refine h.trans ?_
  rw [kernelIdealSheaf_obj, ker_structureSharp_eq B S hS _
    (relativelyRepresentable_of_isAlgebraicSpace B S hS W.2 (idealChartToSpace B S hS W φ J)),
    chartPullbackRingHom_chartBaseChangeArrow]
  rfl

/-- A function killed by pullback along `b` is killed by pullback along `a ≫ b`. -/
private theorem ker_Γ_map_toScheme_le_comp {X Y T : BigFppfOver B S hS} (a : X ⟶ Y) (b : Y ⟶ T) :
    RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map b).op).hom ≤
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (a ≫ b)).op).hom := by
  intro x hx
  rw [RingHom.mem_ker, Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp,
    RingHom.comp_apply, RingHom.mem_ker.1 hx, map_zero]

/-- **The image of `V(J)` cuts out on the chart an ideal contained in `J`.** The closed subscheme
`V(J)` maps into `V(J) ×_W V` by its two inclusions into `V`, so a function on `V` vanishing on
`V(J) ×_W V` vanishes on `V(J)`. -/
theorem definingIdealAt_idealImage_le
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    definingIdealAt B S hS W (idealImage B S hS W φ J)
        (op (chartOfSurjectiveEtale B S hS W he)) ≤ J := by
  rw [definingIdealAt_idealImage B S hS W he hqs J]
  set hr := relativelyRepresentable_of_isAlgebraicSpace B S hS W.2
    (idealChartToSpace B S hS W φ J)
  have hδ : idealChartι B S hS J = hr.lift' (𝟙 _) (idealChartι B S hS J) (by simp) ≫ hr.snd φ :=
    (hr.lift'_snd _ _ _).symm
  exact ((ker_Γ_map_toScheme_le_comp B S hS (hr.lift' (𝟙 _) (idealChartι B S hS J) (by simp))
    (hr.snd φ)).trans_eq (by rw [← hδ])).trans (ker_Γ_idealChartι B S hS J).le

variable {W} (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

/-- **The chart ideal of a closed subspace is invariant.** Its extensions along the two
projections of `R = V ×_W V` agree, as ideals of the global functions of the affine scheme `R`. -/
theorem map_definingIdealAt_atlasRelationTarget_eq
    (Z : ClosedSubspaces B S hS W.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs))] :
    (chartIdealAt B S hS W he Z).map
        ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).appTop.hom =
      (chartIdealAt B S hS W he Z).map
        ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).appTop.hom := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (chartOfSurjectiveEtale B S hS W he).1.left) :=
    ‹IsAffine ((BigFppfOver.toScheme B S hS).obj V)›
  have hI : ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)).ker =
      Scheme.IdealSheafData.ofIdealTop
        (definingIdealAt B S hS W Z (op (chartOfSurjectiveEtale B S hS W he))) :=
    ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS W Z (chartOfSurjectiveEtale B S hS W he)
  have ht := schemeKer_snd_comp B S hS (X := W) Z φ (atlasRelationTarget B S hS hs)
  have hs' := schemeKer_snd_comp B S hS (X := W) Z φ (atlasRelationSource B S hS hs)
  rw [(isPullback_yoneda_map_atlasRelation B S hS hs).w] at ht
  rw [ht, hI] at hs'
  exact Scheme.IdealSheafData.equivOfIsAffine.symm.injective
    ((Stacks.AlgebraicGeometry.comap_ofIdealTop _ _).symm.trans
    (hs'.trans (Stacks.AlgebraicGeometry.comap_ofIdealTop _ _)))

/-- Pullback of regular functions along a composite of morphisms of the site, evaluated. -/
theorem Γ_map_toScheme_comp_apply {X Y T : BigFppfOver B S hS} (a : X ⟶ Y) (b : Y ⟶ T)
    (x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (a ≫ b)).op).hom x =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map a).op).hom
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map b).op).hom x) := by
  rw [Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp]
  rfl

/-- **Every function in the ideal of a closed subspace lies in the ideal cut out by the image of
some `V(J)`, `J` finitely generated inside that ideal.** If `f` lies in the ideal `I` of `Z` on
the chart, then its pullback along the source projection of `R = V ×_W V` lies in the extension
of `I` along the target projection (invariance), hence in the extension of a finitely generated
`J = (g₁, …, gₙ) ⊆ I`; and then `f` vanishes on `V(J) ×_W V`, which maps to `R` with target
projection through `V(J)`. -/
theorem exists_finset_mem_definingIdealAt_idealImage
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (Z : ClosedSubspaces B S hS W.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs))]
    {f : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hf : f ∈ chartIdealAt B S hS W he Z) :
    ∃ G : Finset Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
      (↑G : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ⊆ chartIdealAt B S hS W he Z ∧
      f ∈ chartIdealAt B S hS W he (idealImage B S hS W φ (Ideal.span ↑G)) := by
  classical
  set I₀ := chartIdealAt B S hS W he Z with hI₀
  set t := atlasRelationTarget B S hS hs
  set s := atlasRelationSource B S hS hs
  have hmem : ((BigFppfOver.toScheme B S hS).map s).appTop.hom f ∈
      Ideal.span (((BigFppfOver.toScheme B S hS).map t).appTop.hom '' I₀) := by
    rw [← Ideal.map, map_definingIdealAt_atlasRelationTarget_eq B S hS he hs Z]
    exact Ideal.mem_map_of_mem _ hf
  obtain ⟨T, hT, hxT⟩ := Submodule.mem_span_finite_of_mem_span hmem
  obtain ⟨G, hG, rfl⟩ := Finset.subset_set_image_iff.1 hT
  refine ⟨G, hG, ?_⟩
  set J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) := Ideal.span ↑G
  set hr := relativelyRepresentable_of_isAlgebraicSpace B S hS W.2
    (idealChartToSpace B S hS W φ J)
  have hw : yoneda.map (hr.fst' φ ≫ idealChartι B S hS J) ≫ φ = yoneda.map (hr.snd φ) ≫ φ := by
    rw [Functor.map_comp, Category.assoc, Functor.map_preimage]
    exact hr.w φ
  set κ : hr.pullback φ ⟶ atlasRelation B S hS hs :=
    hs.rep.lift' (hr.fst' φ ≫ idealChartι B S hS J) (hr.snd φ) hw
  have hκt : κ ≫ t = hr.fst' φ ≫ idealChartι B S hS J := hs.rep.lift'_fst _ _ _
  have hκs : κ ≫ s = hr.snd φ := hs.rep.lift'_snd _ _ _
  have hle : ∀ x ∈ (↑(G.image ((BigFppfOver.toScheme B S hS).map t).appTop.hom) :
      Set Γ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs), ⊤)),
      x ∈ RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map κ).op).hom := by
    intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hgJ : g ∈ RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (κ ≫ t)).op).hom := by
      rw [hκt]
      refine ker_Γ_map_toScheme_le_comp B S hS _ _ ?_
      rw [ker_Γ_idealChartι B S hS J]
      exact Ideal.subset_span hg
    exact (Γ_map_toScheme_comp_apply B S hS κ t g).symm.trans (RingHom.mem_ker.1 hgJ)
  have key : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hr.snd φ)).op).hom f = 0 := by
    rw [← hκs, Γ_map_toScheme_comp_apply]
    exact RingHom.mem_ker.1 (Ideal.span_le.2 hle hxT)
  exact (definingIdealAt_idealImage B S hS W he hqs J).ge (RingHom.mem_ker.2 key)

end Image

section System

variable {W : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] {φ : yoneda.obj V ⟶ W.1}
  (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  (Z : ClosedSubspaces B S hS W.1)

/-- **The image stages shrink as the ideal grows.** For `J ≤ J'`, `V(J') ⟶ W` factors through
`V(J) ⟶ W`, so its scheme-theoretic image is contained in that of `V(J)`. -/
theorem idealImage_antitone {J J' : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (h : J ≤ J') : (idealImage B S hS W φ J').1 ≤ (idealImage B S hS W φ J).1 := by
  have hfac : idealChartToSpace B S hS W φ J' =
      yoneda.map (idealChartMap B S hS h) ≫ idealChartToSpace B S hS W φ J := by
    rw [idealChartToSpace, idealChartToSpace, ← Category.assoc, ← Functor.map_comp,
      idealChartMap_ι]
  refine schemeTheoreticImageSubfunctor_le B S hS _ (idealImage B S hS W φ J).2 ?_
  rw [hfac]
  exact (Subfunctor.range_comp_le _ _).trans
    (range_le_schemeTheoreticImageSubfunctor B S hS _)

/-- The chart ideal sheaf of a closed subspace at the chart `V` is cut out by its chart ideal. -/
theorem etaleChartKer_chart (Z' : ClosedSubspaces B S hS W.1) :
    etaleChartKer B S hS W Z' (chartOfSurjectiveEtale B S hS W he) =
      Scheme.IdealSheafData.ofIdealTop (chartIdealAt B S hS W he Z') :=
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (chartOfSurjectiveEtale B S hS W he).1.left) :=
    ‹IsAffine ((BigFppfOver.toScheme B S hS).obj V)›
  ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS W Z' (chartOfSurjectiveEtale B S hS W he)

/-- The index of the approximating system: the finite subsets of the chart ideal of `Z`. -/
abbrev ApproxIndex : Type u :=
  {G : Finset Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) //
    (↑G : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ⊆ chartIdealAt B S hS W he Z}

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The finite subsets of the chart ideal form a directed set. -/
theorem isDirected_approxIndex : IsDirected (ApproxIndex B S hS he Z) (· ≤ ·) := by
  classical
  exact ⟨fun G G' => ⟨⟨G.1 ∪ G'.1, by
    rw [Finset.coe_union]; exact Set.union_subset G.2 G'.2⟩,
    Finset.subset_union_left, Finset.subset_union_right⟩⟩

/-- The stage of the approximating system at a finite subset `G` of the chart ideal of `Z`: the
scheme-theoretic image of `V((G)) ⟶ W`. -/
noncomputable abbrev approxStage (G : ApproxIndex B S hS he Z) : ClosedSubspaces B S hS W.1 :=
  idealImage B S hS W φ (Ideal.span (↑G.1 : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))

/-- The stages form an inverse system of closed subspaces. -/
theorem approxStage_antitone ⦃G G' : ApproxIndex B S hS he Z⦄ (h : G ≤ G') :
    (approxStage B S hS he Z G').1 ≤ (approxStage B S hS he Z G).1 :=
  idealImage_antitone B S hS (Ideal.span_mono (Finset.coe_subset.2 h))

variable (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)

include hqs in
/-- The chart ideal of the stage at `G` is contained in the ideal generated by `G`. -/
theorem chartIdealAt_approxStage_le (G : ApproxIndex B S hS he Z) :
    chartIdealAt B S hS W he (approxStage B S hS he Z G) ≤
      Ideal.span (↑G.1 : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :=
  definingIdealAt_idealImage_le B S hS W he hqs _

include hs hqs in
/-- Every stage contains `Z`: its chart ideal is contained in the ideal generated by a subset of
the chart ideal of `Z`. -/
theorem le_approxStage (G : ApproxIndex B S hS he Z) :
    Z.1 ≤ (approxStage B S hS he Z G).1 := by
  refine le_of_etaleChartKer_le_of_chart B S hS W Z (approxStage B S hS he Z G)
    (chartOfSurjectiveEtale B S hS W he) hs ?_
  rw [etaleChartKer_chart B S hS he, etaleChartKer_chart B S hS he]
  exact ofIdealTop_mono B S hS ((chartIdealAt_approxStage_le B S hS he Z hqs G).trans
    (Ideal.span_le.2 G.2))

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs))]

include hs hqs in
/-- The chart ideal of `Z` is the union of the chart ideals of the stages. -/
theorem chartIdealAt_eq_iSup :
    chartIdealAt B S hS W he Z =
      ⨆ G : ApproxIndex B S hS he Z, chartIdealAt B S hS W he (approxStage B S hS he Z G) := by
  refine le_antisymm (fun f hf => ?_) (iSup_le fun G =>
    (chartIdealAt_approxStage_le B S hS he Z hqs G).trans (Ideal.span_le.2 G.2))
  obtain ⟨G, hG, hfG⟩ := exists_finset_mem_definingIdealAt_idealImage B S hS he hs hqs Z hf
  exact Ideal.mem_iSup_of_mem (⟨G, hG⟩ : ApproxIndex B S hS he Z) hfG

include hs hqs in
/-- **`Z` is the intersection of the stages.** -/
theorem eq_iInf_approxStage :
    Z.1 = ⨅ G : ApproxIndex B S hS he Z, (approxStage B S hS he Z G).1 := by
  refine subfunctor_eq_iInf_of_etaleChartKer_eq_iSup_of_chart B S hS W
    (approxStage B S hS he Z) Z (chartOfSurjectiveEtale B S hS W he) hs ?_
  rw [etaleChartKer_chart B S hS he, chartIdealAt_eq_iSup B S hS hs he Z hqs]
  simp only [etaleChartKer_chart B S hS he]
  exact (Scheme.IdealSheafData.equivOfIsAffine
    (X := (BigFppfOver.toScheme B S hS).obj V)).symm.toOrderIso.map_iSup _

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs))] in
/-- **The chart ideal of a closed subspace with all the points of `W` consists of nilpotents.** The
base change `Z ×_W V ⟶ V` is a surjective closed immersion, so a function on `V` killed by it has
empty basic open, hence is nilpotent, `V` being quasi-compact. -/
theorem chartIdealAt_le_nilradical (hsurj : IsSurjective B S hS Z.1.ι) :
    chartIdealAt B S hS W he Z ≤ nilradical Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) := by
  have hps := presheafSurjective_of_isSurjective B S hS Z.1.ι Z.2.2.rep hsurj
  have hq : Surjective ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)) :=
    hps.property φ _ _ (Z.2.2.rep.isPullback φ)
  intro f hf
  have hf' : f ∈ RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (Z.2.2.rep.snd φ)).op).hom := by
    have h := definingIdealAt_eq_ker B S hS W Z (chartOfSurjectiveEtale B S hS W he)
    exact h ▸ hf
  have h0 : ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)).appTop.hom f = 0 :=
    RingHom.mem_ker.1 hf'
  have hbot : ((BigFppfOver.toScheme B S hS).obj V).basicOpen f = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := hq.surj x
    have hy : y ∈ ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)) ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).obj V).basicOpen f := hx
    rw [Scheme.preimage_basicOpen_top, h0, Scheme.basicOpen_zero] at hy
    exact hy.elim
  exact (Scheme.isNilpotent_iff_basicOpen_eq_bot f).2 hbot

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs))] in
include hqs in
/-- **Every stage is a finite-order thickening on the chart.** The chart ideal of the stage at
`G` lies in the ideal generated by `G`, a finitely generated ideal of nilpotents, hence
nilpotent. -/
theorem exists_chartKer_approxStage_pow_eq_bot (hsurj : IsSurjective B S hS Z.1.ι)
    (G : ApproxIndex B S hS he Z) :
    ∃ n : ℕ, chartKer B S hS W (approxStage B S hS he Z G) φ ^ n = ⊥ := by
  have hG : Ideal.span (↑G.1 : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ≤
      nilradical Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    Ideal.span_le.2 (G.2.trans (chartIdealAt_le_nilradical B S hS he Z hsurj))
  obtain ⟨n, hn⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical ⟨G.1, rfl⟩).2 hG
  refine ⟨n, ?_⟩
  have hK : chartIdealAt B S hS W he (approxStage B S hS he Z G) ^ n = ⊥ :=
    le_bot_iff.1 ((Ideal.pow_right_mono
      (chartIdealAt_approxStage_le B S hS he Z hqs G) n).trans hn.le)
  have h := etaleChartKer_chart B S hS he (approxStage B S hS he Z G)
  change chartKer B S hS W (approxStage B S hS he Z G) φ =
    Scheme.IdealSheafData.ofIdealTop _ at h
  rw [h, ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, ← map_pow, hK, map_bot]

end System

end AlgebraicGeometry.Space

end
