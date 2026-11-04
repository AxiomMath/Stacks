module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.NoetherianSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.SmoothComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.Topology.Sober.Generization

/-!
# The multiplicity of a component of an algebraic stack is chart-independent (Stacks 0DR7)

Let `f₁ : U₁ → 𝒳` and `f₂ : U₂ → 𝒳` be smooth 1-morphisms to a locally Noetherian algebraic
stack over `S` from the algebraic stacks of two schemes `U₁`, `U₂` of the site, and let `T₁` and
`T₂` be irreducible components of `U₁` and `U₂` whose images in the space of points of `𝒳` have
the same irreducible component `T` as closure. Then `T₁` and `T₂` have the same multiplicity,
that is, the local rings of `U₁` at the generic point of `T₁` and of `U₂` at the generic point of
`T₂` have the same length.

The proof is the source's. Shrink each chart to a nonempty open subscheme `V_i ⊆ T_i`, which
exists because `U_i` is locally Noetherian; the resulting 1-morphism `V_i → 𝒳` is still smooth,
so its image on points is a nonempty open subset of `T`. Two nonempty open subsets of an
irreducible set meet, so there are a point of `|V₁|` and a point of `|V₂|` with the same image in
`|𝒳|`; the map `|V₁ ×_𝒳 V₂| → |V₁| ×_{|𝒳|} |V₂|` is surjective (Stacks 04XH), so the 2-fibre
product is nonempty on points, and a smooth surjective scheme chart `W` of it is therefore a
nonempty scheme carrying smooth morphisms `W → V₁ → U₁` and `W → V₂ → U₂`. Every point of `W`
maps into `T₁` and into `T₂`, and a smooth — hence flat — morphism carries the generic point of
an irreducible component to a generic point, so the closure of the image of any irreducible
component of `W` is `T₁` on one side and `T₂` on the other. Stacks 0DR6 applied twice to that one
component of `W` identifies the two multiplicities.

## Main results

* `AlgebraicGeometry.Stack.componentMultiplicity_eq_of_closure_image_eq`: **Stacks 0DR7**.

## Implementation notes

"`𝒳` is locally Noetherian" is the existential smooth-atlas condition of Stacks 04YF and
Stacks 04YG at the property `AlgebraicGeometry.IsLocallyNoetherian` of schemes, spelled
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas`; no named predicate "locally Noetherian
algebraic stack" is used, because Stacks 04YG has no library site of its own. The hypothesis is
consumed through the universal scheme criterion of Stacks 04YF, which is what makes each of the
two charts `U₁`, `U₂` locally Noetherian.

The image of a component of a chart in the space of points of Stacks 04XL is taken along
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap` of the chart, read on the scheme through
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`, the identification of the points of the
algebraic stack of a scheme of the site with the scheme itself. The two spellings of the
fibred-in-groupoids witness of the point space — the one read off the algebraic-stack condition
with `Classical.choose` and the one bundled in the underlying
`CategoryTheory.CatFiberedInGroupoids` — are proofs of the same `Prop`, so definitional proof
irrelevance identifies them and the choice is immaterial.

The multiplicity of an irreducible component `T'` of a scheme `U` is
`Stacks.Chow.componentMultiplicity (𝟙 U) (TopologicalSpace.genericPoints.ofComponent T')`, the
length of the local ring of `U` at the generic point of `T'` read as the multiplicity of
Stacks 02QU of `U` as a closed subscheme of itself.

The two applications of Stacks 0DR6 are to the *same* irreducible component of the common
refinement `W`, read along its two smooth morphisms to `U₁` and to `U₂`. That both closures of
images are full components is not an extra hypothesis: it is automatic, because every point of `W`
lands in `T₁` on one side and in `T₂` on the other, and a flat morphism is generalizing.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0DR6](https://stacks.math.columbia.edu/tag/0DR6)
* [Stacks Project, Tag 0DR7](https://stacks.math.columbia.edu/tag/0DR7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

open TopologicalSpace

attribute [local instance] pointTopology

universe u w

/-! ### Irreducible components under a flat morphism of schemes -/

/-- **The closure of the image of an irreducible component under a flat morphism all of whose
points land in one irreducible component of the target is that component.** A flat morphism is
generalizing, so no point of the target properly generalizes the image of the generic point of
the component; that image is therefore the generic point of an irreducible component, and the
component it generates is contained in — hence equal to — the given one. -/
private theorem closure_image_component_eq_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (Z : irreducibleComponents X) (T : irreducibleComponents Y)
    (hfT : ∀ x : X, f.base x ∈ (T : Set Y)) :
    closure (f.base '' (Z : Set X)) = (T : Set Y) := by
  have hη : f.base (genericPoints.ofComponent Z : X) ∈ genericPoints Y := by
    refine mem_genericPoints_of_forall_specializes_eq fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Flat.generalizingMap f hy
    exact congrArg f.base
      (forall_specializes_eq_of_mem_genericPoints (genericPoints.ofComponent Z).2 x hx)
  have hgen := (genericPoints.isGenericPoint_ofComponent Z).image f.continuous
  have hcomp : closure (f.base '' (Z : Set X)) ∈ irreducibleComponents Y := by
    rwa [← hgen]
  have hsub : closure (f.base '' (Z : Set X)) ⊆ (T : Set Y) :=
    closure_minimal (Set.image_subset_iff.2 fun x _ => hfT x)
      (isClosed_of_mem_irreducibleComponents _ T.2)
  exact hsub.antisymm (hcomp.2 T.2.1 hsub)

/-! ### Shrinking a chart to an irreducible component -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An irreducible component of a locally Noetherian scheme contains a nonempty open
subscheme.** A Noetherian open neighbourhood of a point of the component meets it in an
irreducible component of the neighbourhood, and a Noetherian space has only finitely many
irreducible components, so that intersection contains a nonempty open set. -/
private theorem exists_opens_nonempty_subset_component {X : Scheme.{u}}
    [IsLocallyNoetherian X] (T : irreducibleComponents X) :
    ∃ V : X.Opens, (V : Set X).Nonempty ∧ (V : Set X) ⊆ (T : Set X) := by
  obtain ⟨x, hx⟩ := T.2.1.nonempty
  obtain ⟨W, hW, hxW, hWN⟩ := isLocallyNoetherianSpace_of_isLocallyNoetherian X x
  have hcomp : (Subtype.val : W → X) ⁻¹' (T : Set X) ∈ irreducibleComponents W :=
    preimage_mem_irreducibleComponents T.2 hW.isOpenEmbedding_subtypeVal
      ⟨x, hx, ⟨⟨x, hxW⟩, rfl⟩⟩
  obtain ⟨O, hO, hOne, hOT⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hcomp
  refine ⟨⟨Subtype.val '' O, hW.isOpenEmbedding_subtypeVal.isOpenMap _ hO⟩, hOne.image _, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hOT hz

/-- **A locally Noetherian scheme of the site has, inside any irreducible component, a nonempty
open subscheme which again belongs to the site.** An open subscheme is no larger than the scheme
it sits in, so it satisfies the size bound defining the site, and the open immersion is
smooth. -/
private theorem exists_smooth_chart_in_component (U : BigFppfOver B S hS)
    (hU : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U))
    (T : irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃ (V : BigFppfOver B S hS) (j : V ⟶ U),
      Smooth ((BigFppfOver.toScheme B S hS).map j) ∧
        Nonempty ((BigFppfOver.toScheme B S hS).obj V) ∧
          ∀ x, ((BigFppfOver.toScheme B S hS).map j).base x ∈ (T : Set _) := by
  obtain ⟨O, hOne, hOT⟩ := exists_opens_nonempty_subset_component T
  have hsize : B.Contains (O : Scheme.{u}) :=
    (Scheme.size_coe_opens_le ((BigFppfOver.toScheme B S hS).obj U) O).trans_lt U.left.property
  let Vobj : B.Schemes := B.obj hsize
  let v : Vobj ⟶ U.left := B.inclusion.preimage (X := Vobj) (Y := U.left) O.ι
  let V : BigFppfOver B S hS := Over.mk (v ≫ U.hom)
  let j : V ⟶ U := Over.homMk v
  have hj : (BigFppfOver.toScheme B S hS).map j = O.ι :=
    B.inclusion.map_preimage (X := Vobj) (Y := U.left) O.ι
  refine ⟨V, j, ?_, ?_, ?_⟩
  · rw [hj]
    infer_instance
  · exact hOne.to_subtype
  · intro x
    rw [hj]
    exact hOT x.2

/-! ### The 1-morphism induced by a smooth morphism of the site -/

/-- **The image on points of a chart precomposed with a morphism of the site all of whose points
land in a subset `T` of the chart lies in the image of `T`.** This is naturality of
`AlgebraicGeometry.Stack.pointsHomeomorphScheme` together with functoriality of the map on
points. -/
private theorem range_pointsMap_schemeStackMap_comp_subset
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U V : BigFppfOver B S hS)
    (f : schemeStack.{u, w} B S hS U ⟶ 𝒳) (j : V ⟶ U)
    (T : Set ((BigFppfOver.toScheme B S hS).obj U))
    (hj : ∀ x, ((BigFppfOver.toScheme B S hS).map j).base x ∈ T) :
    letI := pointTopology B S hS (schemeStack.{u, w} B S hS U).val
    Set.range (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS j ≫ f)) ⊆
      AlgebraicStacks.pointsMap B S hS f '' ((pointsHomeomorphScheme B S hS U).symm '' T) := by
  let _ := pointTopology B S hS (schemeStack.{u, w} B S hS U).val
  let _ := pointTopology B S hS (schemeStack.{u, w} B S hS V).val
  rintro _ ⟨q, rfl⟩
  refine ⟨AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS j) q, ?_, ?_⟩
  · refine ⟨pointsHomeomorphScheme B S hS U
      (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS j) q), ?_, ?_⟩
    · have hnat : pointsHomeomorphScheme B S hS U
          (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS j) q) =
          ((BigFppfOver.toScheme B S hS).map j).base
            (pointsHomeomorphScheme B S hS V q) :=
        pointsHomeomorphScheme_naturality B S hS j q
      rw [hnat]
      exact hj _
    · exact (pointsHomeomorphScheme B S hS U).symm_apply_apply _
  · exact (congrFun (AlgebraicStacks.pointsMap_comp B S hS
      (schemeStackMap.{u, w} B S hS j) f) q).symm

/-! ### Stacks 0DR7 -/

/-- **Stacks 0DR7.** Let `f₁ : U₁ → 𝒳` and `f₂ : U₂ → 𝒳` be smooth 1-morphisms to a locally
Noetherian algebraic stack over `S` from the algebraic stacks of two schemes `U₁`, `U₂` of the
site, and let `T₁`, `T₂` be irreducible components of `U₁`, `U₂`. If the closures of the images of
`T₁` and `T₂` in the space of points of Stacks 04XL of `𝒳` are the same irreducible component `T`,
then `T₁` and `T₂` have the same multiplicity.

Together with Stacks 0DR5 this makes the multiplicity of an irreducible component of `|𝒳|` well
defined: it may be computed on any smooth scheme chart, by any component lying over it. -/
@[stacks 0DR7]
theorem componentMultiplicity_eq_of_closure_image_eq
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hN : HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    (U₁ U₂ : BigFppfOver B S hS)
    (f₁ : schemeStack.{u, w} B S hS U₁ ⟶ 𝒳) (f₂ : schemeStack.{u, w} B S hS U₂ ⟶ 𝒳)
    (hf₁ : AlgebraicStacks.IsSmooth B S hS f₁) (hf₂ : AlgebraicStacks.IsSmooth B S hS f₂)
    (T₁ : irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U₁))
    (T₂ : irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U₂)) :
    letI := pointTopology B S hS (schemeStack.{u, w} B S hS U₁).val
    letI := pointTopology B S hS (schemeStack.{u, w} B S hS U₂).val
    ∀ T ∈ irreducibleComponents (AlgebraicStacks.points B S hS 𝒳),
      closure (AlgebraicStacks.pointsMap B S hS f₁ ''
          ((pointsHomeomorphScheme B S hS U₁).symm '' (T₁ : Set _))) = T →
        closure (AlgebraicStacks.pointsMap B S hS f₂ ''
            ((pointsHomeomorphScheme B S hS U₂).symm '' (T₂ : Set _))) = T →
          _root_.Stacks.Chow.componentMultiplicity
                (𝟙 ((BigFppfOver.toScheme B S hS).obj U₁)) (genericPoints.ofComponent T₁) =
            _root_.Stacks.Chow.componentMultiplicity
                (𝟙 ((BigFppfOver.toScheme B S hS).obj U₂)) (genericPoints.ofComponent T₂) := by
  let _ := pointTopology B S hS (schemeStack.{u, w} B S hS U₁).val
  let _ := pointTopology B S hS (schemeStack.{u, w} B S hS U₂).val
  intro T hT h₁ h₂
  let _ : ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocallyNoetherian X)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hEvery := (exists_scheme_atlas_iff_forall_scheme B S hS
    (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳).1 hN
  have hLN₁ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U₁) := hEvery U₁ f₁ hf₁
  have hLN₂ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U₂) := hEvery U₂ f₂ hf₂
  obtain ⟨V₁, j₁, hj₁, ⟨x₁⟩, hjT₁⟩ := exists_smooth_chart_in_component B S hS U₁ hLN₁ T₁
  obtain ⟨V₂, j₂, hj₂, ⟨x₂⟩, hjT₂⟩ := exists_smooth_chart_in_component B S hS U₂ hLN₂ T₂
  -- the two shrunken charts, still smooth
  have ha₁ : AlgebraicStacks.IsSmooth B S hS (schemeStackMap.{u, w} B S hS j₁ ≫ f₁) :=
    AlgebraicStacks.isSmooth_comp B S hS _ _ (isSmooth_schemeStackMap.{u, w} B S hS j₁ hj₁) hf₁
  have ha₂ : AlgebraicStacks.IsSmooth B S hS (schemeStackMap.{u, w} B S hS j₂ ≫ f₂) :=
    AlgebraicStacks.isSmooth_comp B S hS _ _ (isSmooth_schemeStackMap.{u, w} B S hS j₂ hj₂) hf₂
  let _ := pointTopology B S hS (schemeStack.{u, w} B S hS V₁).val
  let _ := pointTopology B S hS (schemeStack.{u, w} B S hS V₂).val
  -- their images on points are open subsets of `T`
  have hAT₁ : Set.range (AlgebraicStacks.pointsMap B S hS
      (schemeStackMap.{u, w} B S hS j₁ ≫ f₁)) ⊆ T := by
    rw [← h₁]
    exact (range_pointsMap_schemeStackMap_comp_subset B S hS 𝒳 U₁ V₁ f₁ j₁ _ hjT₁).trans
      subset_closure
  have hAT₂ : Set.range (AlgebraicStacks.pointsMap B S hS
      (schemeStackMap.{u, w} B S hS j₂ ≫ f₂)) ⊆ T := by
    rw [← h₂]
    exact (range_pointsMap_schemeStackMap_comp_subset B S hS 𝒳 U₂ V₂ f₂ j₂ _ hjT₂).trans
      subset_closure
  -- both are nonempty, so by irreducibility of `T` they share a point
  obtain ⟨z, -, ⟨p₁, hp₁⟩, p₂, hp₂⟩ := hT.1.2 _ _
    (AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS _ ha₁).isOpen_range
    (AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS _ ha₂).isOpen_range
    ⟨_, hAT₁ ⟨(pointsHomeomorphScheme B S hS V₁).symm x₁, rfl⟩, ⟨_, rfl⟩⟩
    ⟨_, hAT₂ ⟨(pointsHomeomorphScheme B S hS V₂).symm x₂, rfl⟩, ⟨_, rfl⟩⟩
  -- Stacks 04XH: the 2-fibre product of the two shrunken charts has a point
  have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
    (schemeStackMap.{u, w} B S hS j₁ ≫ f₁) (schemeStackMap.{u, w} B S hS j₂ ≫ f₂)
  obtain ⟨p, -, -⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS _ hP p₁ p₂
    (hp₁.trans hp₂.symm)
  -- a smooth surjective scheme chart of that 2-fibre product
  obtain ⟨W, c, hcSmooth, hcSurj⟩ := exists_smooth_surjective_schemeStack B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS (schemeStackMap.{u, w} B S hS j₁ ≫ f₁)
      (schemeStackMap.{u, w} B S hS j₂ ≫ f₂)).pt
  have hrep : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS (schemeStackMap.{u, w} B S hS j₁ ≫ f₁)
        (schemeStackMap.{u, w} B S hS j₂ ≫ f₂)).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
      (schemeStack.{u, w} B S hS V₁).val (schemeStack.{u, w} B S hS V₂).val _ _
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V₂)
        (schemeStackMap.{u, w} B S hS j₂ ≫ f₂).hom)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V₁)
  obtain ⟨g₁, hg₁, -⟩ := exists_schemeMap_of_representable B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) hrep c _ hcSmooth
    (AlgebraicStacks.isSmooth_baseChange B S hS (schemeStackMap.{u, w} B S hS j₂ ≫ f₂)
      (schemeStackMap.{u, w} B S hS j₁ ≫ f₁) _ hP ha₂)
  obtain ⟨g₂, hg₂, -⟩ := exists_schemeMap_of_representable B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) hrep c _ hcSmooth
    (AlgebraicStacks.isSmooth_baseChange B S hS (schemeStackMap.{u, w} B S hS j₁ ≫ f₁)
      (schemeStackMap.{u, w} B S hS j₂ ≫ f₂) _ (Bicategory.isTwoFibreProduct_swap hP) ha₁)
  -- `W` is nonempty, and any of its irreducible components does the job
  obtain ⟨q, -⟩ := hcSurj p
  let _ := pointTopology B S hS (schemeStack.{u, w} B S hS W).val
  let y : (BigFppfOver.toScheme B S hS).obj W := pointsHomeomorphScheme B S hS W q
  let Z : irreducibleComponents ((BigFppfOver.toScheme B S hS).obj W) :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  have : Smooth ((BigFppfOver.toScheme B S hS).map (g₁ ≫ j₁)) := by
    rw [Functor.map_comp]
    infer_instance
  have : Smooth ((BigFppfOver.toScheme B S hS).map (g₂ ≫ j₂)) := by
    rw [Functor.map_comp]
    infer_instance
  refine (_root_.Stacks.Chow.componentMultiplicity_id_eq_of_smooth
    ((BigFppfOver.toScheme B S hS).map (g₁ ≫ j₁)) Z T₁
    (closure_image_component_eq_of_flat _ Z T₁ fun x => ?_)).symm.trans
    (_root_.Stacks.Chow.componentMultiplicity_id_eq_of_smooth
      ((BigFppfOver.toScheme B S hS).map (g₂ ≫ j₂)) Z T₂
      (closure_image_component_eq_of_flat _ Z T₂ fun x => ?_))
  · rw [Functor.map_comp]
    simpa using hjT₁ (((BigFppfOver.toScheme B S hS).map g₁).base x)
  · rw [Functor.map_comp]
    simpa using hjT₂ (((BigFppfOver.toScheme B S hS).map g₂).base x)

end AlgebraicGeometry.Stack

end
