module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge

/-!
# Étale morphisms of algebraic spaces are smooth, and the smooth atlas

Let `S` be a scheme contained in a big fppf site `B`. An étale morphism of algebraic spaces
over `S` in the sense of Stacks 03FR is smooth, flat and locally of finite presentation
(Stacks 04XX, 0467, 0468): in a commuting square of étale charts of an étale morphism `f`, the
composite of the chart of the source with `f` is étale by Stacks 03FT, so both sides of the
square over the target chart are étale, and Stacks 03FV makes the morphism of schemes
underlying the square étale; an étale morphism of schemes is smooth, flat and locally of
finite presentation.

The consequence this file is written for is that the scheme atlas an algebraic space has by
definition (Stacks 025Y) is a *smooth* surjective covering of it, not merely an fppf one: a
surjective étale scheme atlas is a smooth covering in the sense of Stacks 041C and an étale
covering in the sense of Stacks 041E, so every algebraic space over `S` admits a surjective
smooth morphism from a scheme. That is the shape in which the presentation clause of an
algebraic stack (Stacks 026O) consumes an algebraic-space presentation, and it is the
smooth-topology counterpart of `AlgebraicGeometry.Space.isFppfCovering_atlas`.

## Main results

* `AlgebraicGeometry.Space.isSmooth_of_isEtale`: **Stacks 04XX**.
* `AlgebraicGeometry.Space.isFlat_of_isEtale`: **Stacks 0467**.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isEtale`: **Stacks 0468**.
* `AlgebraicGeometry.Space.isSmoothCovering_atlas` and
  `AlgebraicGeometry.Space.isEtaleCovering_atlas`: a surjective étale scheme atlas is a smooth
  covering and an étale covering, in the senses of Stacks 041C and 041E.
* `AlgebraicGeometry.Space.exists_isSurjective_isSmooth_atlas`: every algebraic space over `S`
  admits a surjective smooth morphism from a representable presheaf.
* `AlgebraicGeometry.Space.ofArrows_atlas_mem_precoverage` and
  `AlgebraicGeometry.Space.prop_iff_pullbackSnd_of_atlas_covering`: a one-member atlas family
  which covers for a topology `τ` of Stacks 03YH, read as a member of the precoverage of `τ`,
  and the resulting test of a property local on the base for `τ` on the base change to that
  atlas.

## Implementation notes

`AlgebraicGeometry.Space.etale_of_etaleChart_square_of_isEtale` is the chart-square step for an
arbitrary étale morphism of algebraic spaces; the existing
`AlgebraicGeometry.Space.etale_of_etaleChart_square` is its special case in which the étale
morphism goes out of a representable presheaf and the chart of the source factors through it.
Only algebraicity of the *target* is needed, since the sources of the two charts are
representable and hence algebraic spaces.

`AlgebraicGeometry.Space.prop_iff_pullbackSnd_of_atlas_covering` is stated for a variable
topology with the covering property as a hypothesis, so it serves the smooth and étale
topologies as well as the fppf one; the fppf case is
`AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas`.

As in `AlgebraicGeometry.Space.isFppfCovering_atlas`, the index universe of a covering family
of `AlgebraicGeometry.Space.Topology.precoverage` is independent of the universe of the site,
so the one-member family is indexed by `PUnit` in a free universe and a consumer instantiates
it at the universe its locality hypothesis was stated at.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 041C](https://stacks.math.columbia.edu/tag/041C)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
* [Stacks Project, Tag 0468](https://stacks.math.columbia.edu/tag/0468)
* [Stacks Project, Tag 04XX](https://stacks.math.columbia.edu/tag/04XX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- In a commuting square of étale charts of an étale morphism `f` of algebraic spaces over
`S`, the morphism of schemes underlying the square is étale.

The chart `a` of the source composed with `f` is étale by Stacks 03FT, so both `h ≫ b` and `b`
are étale; Stacks 03FV then makes `h` étale. Only the target of `f` is required to be an
algebraic space: the sources of the two charts are representable. -/
theorem etale_of_etaleChart_square_of_isEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    {f : F ⟶ G} (hf : IsEtale B S hS f)
    {U V : BigFppfOver B S hS} {a : yoneda.obj U ⟶ F} {b : yoneda.obj V ⟶ G} {h : U ⟶ V}
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hsq : yoneda.map h ≫ b = a ≫ f) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h) := by
  have ha' : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).2 ha
  have hb' : IsEtale B S hS b := (isEtale_iff_presheaf_of_yoneda B S hS b).2 hb
  have hcomp : IsEtale B S hS (yoneda.map h ≫ b) := by
    rw [hsq]
    exact isEtale_comp B S hS ha' hf
  have hmap : IsEtale B S hS (yoneda.map h) :=
    isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) hG (yoneda.map h) (yoneda.map h ≫ b) b hcomp hb' rfl
  exact (presheaf_yoneda_map_etale_iff B S hS h).1
    ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map h)).1 hmap)

/-- A property of morphisms of schemes implied by étaleness holds on every étale chart of an
étale morphism of algebraic spaces over `S`. -/
theorem holdsOnEveryEtaleChart_of_isEtale_hom
    (Q : MorphismProperty Scheme.{u})
    (hQ : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), AlgebraicGeometry.Etale g → Q g)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    {f : F ⟶ G} (hf : IsEtale B S hS f) :
    HoldsOnEveryEtaleChart B S hS Q f := fun _ _ _ _ _ ha hb hsq =>
  hQ _ (etale_of_etaleChart_square_of_isEtale B S hS hG hf ha hb hsq)

/-- **Stacks 04XX.** An étale morphism of algebraic spaces over `S` is smooth: an étale
morphism of schemes is smooth. -/
@[stacks 04XX]
theorem isSmooth_of_isEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    {f : F ⟶ G} (hf : IsEtale B S hS f) :
    IsSmooth B S hS f :=
  holdsOnEveryEtaleChart_of_isEtale_hom B S hS
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
    (fun _ hg => have := hg; inferInstance) hG hf

/-- **Stacks 0467.** An étale morphism of algebraic spaces over `S` is flat: in every commuting
square of étale charts the chart morphism of schemes is étale, by cancellation
(`AlgebraicGeometry.Space.etale_of_comp_etale_chart`), and an étale morphism of schemes is
flat.

Nothing is asked of the target. -/
@[stacks 0467]
theorem isFlat_of_isEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsEtale B S hS f) : IsFlat B S hS f := by
  intro U V a b h ha hb hcomm
  have : Etale ((BigFppfOver.toScheme B S hS).map h) :=
    etale_of_comp_etale_chart B S hS (hf U a ha) hb hcomm
  infer_instance

/-- **Stacks 0468.** An étale morphism of algebraic spaces over `S` is locally of finite
presentation: the chart morphism of schemes in every commuting square of étale charts is étale,
hence locally of finite presentation.

Nothing is asked of the target. -/
@[stacks 0468]
theorem isLocallyOfFinitePresentation_of_isEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} (hf : IsEtale B S hS f) :
    IsLocallyOfFinitePresentation B S hS f := by
  intro U V a b h ha hb hcomm
  have : Etale ((BigFppfOver.toScheme B S hS).map h) :=
    etale_of_comp_etale_chart B S hS (hf U a ha) hb hcomm
  infer_instance

/-- The points of a surjective scheme atlas cover the points of the algebraic space. -/
private theorem iUnion_range_pointsMap_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    (⋃ _ : PUnit.{v + 1}, Set.range (pointsMap B S hS (yoneda.obj T) a)) = Set.univ := by
  rw [Set.iUnion_const]
  exact ((surjective_iff_surjective_pointsMap B S hS F hF T a).1 hsurj).range_eq

/-- A scheme atlas of an algebraic space over `S` which is surjective and étale after every
representable base change is a smooth covering of it in the sense of Stacks 041C, as a family
indexed by a one-element type. -/
theorem isSmoothCovering_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    IsSmoothCovering B S hS (fun _ : PUnit.{v + 1} => yoneda.obj T) (fun _ => a) := by
  have ha : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).2 hetale
  exact ⟨hF, fun _ => isAlgebraicSpace_yoneda B S hS T,
    fun _ => isSmooth_of_isEtale B S hS hF ha,
    iUnion_range_pointsMap_atlas.{u, v} B S hS hF hsurj⟩

/-- A scheme atlas of an algebraic space over `S` which is surjective and étale after every
representable base change is an étale covering of it in the sense of Stacks 041E, as a family
indexed by a one-element type. -/
theorem isEtaleCovering_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    IsEtaleCovering B S hS (fun _ : PUnit.{v + 1} => yoneda.obj T) (fun _ => a) := by
  have ha : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).2 hetale
  exact ⟨hF, fun _ => isAlgebraicSpace_yoneda B S hS T, fun _ => ha,
    iUnion_range_pointsMap_atlas.{u, v} B S hS hF hsurj⟩

/-- The one-member family of a surjective étale scheme atlas is a covering family for the
smooth topology of Stacks 03YH. -/
theorem smooth_isCovering_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Topology.smooth.IsCovering B S hS
      (fun _ : PUnit.{v + 1} => yoneda.obj T) (fun _ => a) :=
  ⟨hF, fun _ => isAlgebraicSpace_yoneda B S hS T,
    isSmoothCovering_atlas.{u, v} B S hS hF hsurj hetale⟩

/-- The one-member family of a surjective étale scheme atlas is a covering family for the étale
topology of Stacks 03YH. -/
theorem etale_isCovering_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Topology.etale.IsCovering B S hS
      (fun _ : PUnit.{v + 1} => yoneda.obj T) (fun _ => a) :=
  ⟨hF, fun _ => isAlgebraicSpace_yoneda B S hS T,
    isEtaleCovering_atlas.{u, v} B S hS hF hsurj hetale⟩

/-- Every algebraic space over `S` admits a surjective smooth morphism from a representable
presheaf: its scheme atlas, which exists by Stacks 025Y, is surjective and étale, hence
surjective and smooth by Stacks 04XX. -/
theorem exists_isSurjective_isSmooth_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    ∃ (T : BigFppfOver B S hS) (a : yoneda.obj T ⟶ F),
      IsSurjective B S hS a ∧ IsSmooth B S hS a := by
  obtain ⟨T, a, hsurj, hetale⟩ := hF.exists_atlas
  exact ⟨T, a, (surjective_iff_surjective_pointsMap B S hS F hF T a).1 hsurj,
    isSmooth_of_isEtale B S hS hF ((isEtale_iff_presheaf_of_yoneda B S hS a).2 hetale)⟩

/-- A one-member family out of a representable presheaf which covers an algebraic space for a
topology `τ` of Stacks 03YH is a covering family of the precoverage of `τ`. -/
theorem ofArrows_atlas_mem_precoverage (τ : Topology)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F}
    (hcov : τ.IsCovering B S hS (fun _ : PUnit.{v + 1} => yoneda.obj T) (fun _ => a)) :
    Presieve.ofArrows
        (fun _ : PUnit.{v + 1} =>
          (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS))
        (fun _ => ObjectProperty.homMk a) ∈
      (Topology.precoverage.{u, v} τ B S hS).coverings ⟨F, hF⟩ :=
  ⟨PUnit.{v + 1}, fun _ => ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩,
    fun _ => ObjectProperty.homMk a, rfl, hcov⟩

/-- A property of morphisms of algebraic spaces over `S` which is local on the base for a
topology `τ` of Stacks 03YH may be tested on the base change of the morphism to any scheme
atlas of its target which covers for `τ`. For `τ` the fppf topology this is
`AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas`; the smooth and étale cases are the ones
supplied by `AlgebraicGeometry.Space.smooth_isCovering_atlas` and
`AlgebraicGeometry.Space.etale_isCovering_atlas`. -/
theorem prop_iff_pullbackSnd_of_atlas_covering (τ : Topology)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, v} τ B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ Y.obj}
    (hcov : τ.IsCovering B S hS (fun _ : PUnit.{v + 1} => yoneda.obj T) (fun _ => a)) :
    P f ↔ P (Limits.pullback.snd f (ObjectProperty.homMk a :
      (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)) := by
  have key := MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := P) (K := Topology.precoverage.{u, v} τ B S hS)
    (ofArrows_atlas_mem_precoverage.{u, v} B S hS τ Y.property hcov) (f := f)
  refine key.trans
    ⟨fun h => h _ (Presieve.ofArrows.mk PUnit.unit), ?_⟩
  intro h U g hpb hg
  cases hg
  exact h

end AlgebraicGeometry.Space

end
