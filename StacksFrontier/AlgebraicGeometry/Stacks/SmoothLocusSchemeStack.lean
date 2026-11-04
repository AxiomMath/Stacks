module

public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothObject
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingLocus

/-!
# The smooth locus of the stack of a scheme

For an object `V` of the big fppf site of `S`, the structure morphism of the algebraic stack
`(Sch/V)` represented by `V` is smooth exactly when `V ⟶ S` is smooth, and the smooth locus of that
structure morphism (Stacks 0DZR) is cut out by the smooth locus of `V ⟶ S` as a morphism of
schemes: an object of `(Sch/V)` lies in it exactly when its structure morphism to `V` lands in the
set of points at which `V ⟶ S` is smooth.

## Main results

* `AlgebraicGeometry.Stack.isSmooth_structureMorphism_schemeStack_iff`: smoothness of the
  structure morphism of `(Sch/V)` is smoothness of `V ⟶ S`.
* `AlgebraicGeometry.Stack.IsSmoothLocus.property_schemeStack_iff`: membership in the smooth
  locus of the structure morphism of `(Sch/V)` is read on the smooth locus of `V ⟶ S`.

## Implementation notes

The structure morphism of `(Sch/V)` is the 1-morphism named by the object `V ⟶ S` of the final
algebraic stack `(Sch/S)`, because every 1-morphism to the final algebraic stack is the structure
morphism (`AlgebraicGeometry.Stack.eq_structureMorphism`); this is what lets
`AlgebraicGeometry.Stack.smoothObject_schemeStack_iff` and
`AlgebraicGeometry.Stack.exists_isRelativelySmooth_restrict_of_openSubstackOfPoints` be applied to
it. One inclusion of the second result uses the open image of the inclusion of the smooth locus
(`AlgebraicGeometry.Stack.isSmooth_openImage_inclusion_comp`), so that no identification of an
open substack with the open substack cut out by its points is needed.

## References

* [Stacks Project, Tag 0DZR](https://stacks.math.columbia.edu/tag/0DZR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The object of the final algebraic stack `(Sch/S)` named by an object `V` of the site: the
morphism `V ⟶ S`, read in the slice over the identity of `S`. -/
abbrev finalStackObject (V : BigFppfOver B S hS) :
    (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val.val.obj :=
  Over.mk (Over.homMk V.hom : V ⟶ Over.mk (𝟙 (B.obj hS)))

/-- The 1-morphism named by `finalStackObject` is the structure morphism of `(Sch/V)`. -/
theorem objectStackMap_finalStackObject (V : BigFppfOver B S hS) :
    objectStackMap B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))
        (finalStackObject.{u, w} B S hS V) =
      structureMorphism B S hS (schemeStack.{u, w} B S hS V) :=
  eq_structureMorphism B S hS (schemeStack.{u, w} B S hS V) _

/-- The composite of an open subscheme inclusion with `f` is smooth exactly when the preimage of
the smooth locus of `f` is everything. -/
private theorem smooth_ι_comp_iff_preimage_smoothLocus_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (U : X.Opens) :
    Smooth (U.ι ≫ f) ↔ U.ι ⁻¹ᵁ f.smoothLocus = ⊤ := by
  rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top_iff]

/-- **The structure morphism of the stack of a scheme is smooth exactly when the scheme is
smooth over `S`.** -/
theorem isSmooth_structureMorphism_schemeStack_iff (V : BigFppfOver B S hS) :
    AlgebraicStacks.IsSmooth B S hS (structureMorphism B S hS (schemeStack.{u, w} B S hS V)) ↔
      Smooth (B.inclusion.map V.hom) := by
  rw [← objectStackMap_finalStackObject.{u, w} B S hS V]
  exact smoothObject_schemeStack_iff.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))
    (finalStackObject.{u, w} B S hS V)

/-- **Membership in the smooth locus of the structure morphism of the stack of a scheme.** Let
`V` be an object of the site with `V ⟶ S` locally of finite presentation, and let `W` be the
smooth locus (Stacks 0DZR) of the structure morphism of `(Sch/V)`. An object `z` of `(Sch/V)`
lies in `W` exactly when every point of its underlying scheme maps into the smooth locus of
`V ⟶ S`. -/
theorem IsSmoothLocus.property_schemeStack_iff (V : BigFppfOver B S hS)
    [LocallyOfFinitePresentation (B.inclusion.map V.hom)]
    {W : OpenSubstack (schemeStack.{u, w} B S hS V)}
    (hW : IsSmoothLocus B S hS (structureMorphism B S hS (schemeStack.{u, w} B S hS V)) W)
    (z : Over V) :
    W.property z ↔ ∀ t : (BigFppfOver.toScheme B S hS).obj z.left,
      (BigFppfOver.toScheme B S hS).map z.hom t ∈ (B.inclusion.map V.hom).smoothLocus := by
  constructor
  · intro hz t
    -- the open image of the inclusion of `W` is an open substack on which `V ⟶ S` is smooth
    have hZ := isSmooth_openImage_inclusion_comp B S hS W.inclusion
      (structureMorphism B S hS (schemeStack.{u, w} B S hS V))
      (AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS W.inclusion W.isOpenImmersion) hW.1
    rw [← objectStackMap_finalStackObject.{u, w} B S hS V] at hZ
    -- the point of `(Sch/V)` of `z` at `t` lies in the point set of `W`
    let := pointTopology B S hS (schemeFibredCategory B S hS z.left)
    let := pointTopology B S hS (schemeFibredCategory B S hS V)
    have hnat := pointsHomeomorphScheme_naturality B S hS z.hom
      ((pointsHomeomorphScheme B S hS z.left).symm t)
    rw [Homeomorph.apply_symm_apply] at hnat
    have hmem : (pointsHomeomorphScheme B S hS V).symm
        ((BigFppfOver.toScheme B S hS).map z.hom t) ∈
          Set.range (AlgebraicStacks.pointsMap B S hS W.inclusion) := by
      rw [← hnat, Homeomorph.symm_apply_apply]
      obtain ⟨r, hr⟩ := Quotient.exists_rep ((pointsHomeomorphScheme B S hS z.left).symm t)
      rw [← hr]
      refine (OpenSubstack.mem_pointSet_iff B S hS W _).2
        ⟨fieldValuedPointMap B S hS _ (schemeFibredCategoryMap B S hS z.hom).hom r, ?_, rfl⟩
      exact OpenSubstack.prop_of_hom B S hS W
        (Over.homMk r.obj.hom : Over.mk (r.obj.hom ≫ z.hom) ⟶ z) hz
    obtain ⟨V', hv, hV'⟩ := exists_isRelativelySmooth_restrict_of_openSubstackOfPoints B S hS
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))) (finalStackObject.{u, w} B S hS V)
      _ _ hZ _ hmem
    -- read the relative smoothness on the open subscheme as smoothness over `S`
    have hsm : AlgebraicStacks.IsSmooth B S hS
        (Bicategory.InducedBicategory.mkHom
          (schemeFibredCategoryMap B S hS (BigFppfOver.openSubHom B S hS V V') ≫
            objectMorphism B S hS
              (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
              (Functor.Fiber.mk (a := finalStackObject.{u, w} B S hS V) rfl)) :
          schemeStack.{u, w} B S hS (BigFppfOver.openSubObj B S hS V V') ⟶
            schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))) :=
      hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
        (fun _ _ h => Space.IsSmooth B S hS h)
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).property _ hV'.1 hV'.2
    rw [eq_structureMorphism B S hS _ (Bicategory.InducedBicategory.mkHom _),
      isSmooth_structureMorphism_schemeStack_iff] at hsm
    let V'' : (B.inclusion.obj V.left).Opens := V'
    change Smooth (V''.ι ≫ B.inclusion.map V.hom) at hsm
    have htop := (smooth_ι_comp_iff_preimage_smoothLocus_eq_top _ V'').1 hsm
    exact (htop ▸ trivial : (⟨_, hv⟩ : V'') ∈ V''.ι ⁻¹ᵁ (B.inclusion.map V.hom).smoothLocus)
  · intro H
    set O := (B.inclusion.map V.hom).smoothLocus
    let g := BigFppfOver.openSubHom B S hS V O
    have hc : AlgebraicStacks.IsSmooth B S hS (schemeStackMap.{u, w} B S hS g) :=
      isSmooth_schemeStackMap.{u, w} B S hS g (by change Smooth O.ι; infer_instance)
    have hcf : AlgebraicStacks.IsSmooth B S hS (schemeStackMap.{u, w} B S hS g ≫
        structureMorphism B S hS (schemeStack.{u, w} B S hS V)) := by
      rw [comp_structureMorphism, isSmooth_structureMorphism_schemeStack_iff]
      show Smooth (O.ι ≫ B.inclusion.map V.hom)
      exact (smooth_ι_comp_iff_preimage_smoothLocus_eq_top _ O).2 (Scheme.Opens.ι_preimage_self O)
    have hle := hW.2 _ (isSmooth_openImage_inclusion_comp B S hS _ _ hc hcf)
    have hrange : Set.range (B.inclusion.map z.hom.left).base ⊆ Set.range O.ι.base := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact H t
    let k : z.left ⟶ BigFppfOver.openSubObj B S hS V O := Over.homMk (ObjectProperty.homMk
      (IsOpenImmersion.lift O.ι (B.inclusion.map z.hom.left) hrange)) (by
        apply ObjectProperty.hom_ext
        show IsOpenImmersion.lift O.ι (B.inclusion.map z.hom.left) hrange ≫
          (O.ι ≫ B.inclusion.map V.hom) = B.inclusion.map z.left.hom
        rw [← Category.assoc, IsOpenImmersion.lift_fac, ← Functor.map_comp, Over.w])
    have hk : k ≫ g = z.hom := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact IsOpenImmersion.lift_fac _ _ _
    have := W.strictlyFull
    refine W.property.prop_of_iso ?_
      (hle _ (property_openImage_obj B S hS (schemeStackMap.{u, w} B S hS g) hc (Over.mk k)))
    exact Over.isoMk (Iso.refl _) ((Category.id_comp _).trans hk.symm)

end AlgebraicGeometry.Stack

end
