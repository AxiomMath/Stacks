module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategorySiteKind
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardAmbientSite

/-!
# The primed 2-fibre product is a subsite of the 2-fibre product

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S`, let `y` be a smooth
(respectively flat) object of `𝒴` lying over a scheme `V`, and let `(V ×_{y, 𝒴} 𝒳)'` be the full
subcategory of the 2-fibre product `V ×_{y, 𝒴} 𝒳` cut out by smoothness (respectively flatness)
of the `𝒳`-component. This file verifies the closure condition of **Stacks 07AK** (1) for that
full subcategory, with no hypothesis: a morphism of the 2-fibre product lying over a smooth
(respectively flat) morphism of schemes has its `𝒳`-component lying over the same morphism of
schemes, so smoothness (respectively flatness) of the `𝒳`-component is inherited by
`AlgebraicGeometry.Stack.LisseEtale.smoothObject_of_smooth` (respectively
`AlgebraicGeometry.Stack.flatObject_of_flat`).

Together with the fibredness in groupoids of the 2-fibre product it follows that the inclusion of
`(V ×_{y, 𝒴} 𝒳)'` is continuous and cocontinuous, which is what makes `(V ×_{y, 𝒴} 𝒳)'` a subsite
of `V ×_{y, 𝒴} 𝒳` at all, and which feeds
`AlgebraicGeometry.Stack.inclusionToposMorphism` and
`AlgebraicGeometry.Stack.inclusionToposMorphism_inverseImageIso` to give the morphism of topoi
`g` and the identification of `g^{-1}` with restriction.

The remaining assertion of Stacks 07AK — that the comparison is an isomorphism on cohomology in
every degree — is not available in this repository; see the module documentation of
`StacksFrontier.AlgebraicGeometry.Stacks.SubcategorySiteKind`.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isClosedUnderSitePullback_primedObjectProperty` and
  `AlgebraicGeometry.Stack.FlatFppf.isClosedUnderSitePullback_primedObjectProperty`:
  **Stacks 07AK** (1) for the primed 2-fibre product, in the smooth and in the flat case.
* `AlgebraicGeometry.Stack.LisseEtale.isContinuous_primedInclusion`,
  `AlgebraicGeometry.Stack.LisseEtale.isCocontinuous_primedInclusion` and their flat
  counterparts: the inclusion of the primed 2-fibre product is continuous and cocontinuous.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of a category over the big fppf category of `S` which lies over a smooth morphism
of the base lies over a smooth morphism of schemes itself. -/
private theorem smooth_map_of_isHomLift {C : Type*} [Category C]
    (p : C ⥤ BigFppfOver B S hS) {U V : BigFppfOver B S hS} {x y : C}
    (k : U ⟶ V) (a : x ⟶ y) [p.IsHomLift k a]
    [Smooth ((BigFppfOver.toScheme B S hS).map k)] :
    Smooth ((BigFppfOver.toScheme B S hS).map (p.map a)) := by
  rw [IsHomLift.fac' p k a]
  simp only [Functor.map_comp]
  infer_instance

/-- A morphism of a category over the big fppf category of `S` which lies over a flat morphism of
the base lies over a flat morphism of schemes itself. -/
private theorem flat_map_of_isHomLift {C : Type*} [Category C]
    (p : C ⥤ BigFppfOver B S hS) {U V : BigFppfOver B S hS} {x y : C}
    (k : U ⟶ V) (a : x ⟶ y) [p.IsHomLift k a]
    [Flat ((BigFppfOver.toScheme B S hS).map k)] :
    Flat ((BigFppfOver.toScheme B S hS).map (p.map a)) := by
  rw [IsHomLift.fac' p k a]
  simp only [Functor.map_comp]
  infer_instance

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

namespace LisseEtale

/-- **Stacks 07AK (1) for the primed 2-fibre product, the smooth case.** The full subcategory of
`V ×_{y, 𝒴} 𝒳` cut out by smoothness of the `𝒳`-component is closed under the morphisms of the
2-fibre product lying over a smooth morphism of schemes. -/
theorem isClosedUnderSitePullback_primedObjectProperty (y : LisseEtale.{u, w} B S hS 𝒴) :
    IsClosedUnderSitePullback B S hS
      (SubsitePushforward.ambientStructureFunctor 𝒳.val.val.p 𝒴.val.val.p
        f.hom.hom.toFunctor (ambientChoiceOfPullbacks B S hS 𝒴) y)
      (primedObjectProperty B S hS f y) .etale := by
  refine Or.inl ⟨rfl, ?_⟩
  intro a b k hk hb
  refine smoothObject_of_smooth B S hS 𝒳 k.b ?_ hb
  let : Smooth ((BigFppfOver.toScheme B S hS).map k.hbase) := hk
  let := k.hb
  exact smooth_map_of_isHomLift B S hS 𝒳.val.val.p k.hbase k.b

/-- **Stacks 07AK, continuity, for the primed 2-fibre product in the smooth case.** -/
theorem isContinuous_primedInclusion (y : LisseEtale.{u, w} B S hS 𝒴) :
    (primedObjectProperty B S hS f y).ι.IsContinuous
      ((primedObjectProperty B S hS f y).ι.inheritedTopology
        (ambientTwoFibreProductTopology B S hS f y .etale))
      (ambientTwoFibreProductTopology B S hS f y .etale) :=
  isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS _ _ .etale
    (SubsitePushforward.isFiberedInGroupoids_ambientStructureFunctor _ _ _ _ _
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.w)
    (isClosedUnderSitePullback_primedObjectProperty B S hS f y)

/-- **Stacks 07AK, cocontinuity, for the primed 2-fibre product in the smooth case.** -/
theorem isCocontinuous_primedInclusion (y : LisseEtale.{u, w} B S hS 𝒴) :
    (primedObjectProperty B S hS f y).ι.IsCocontinuous
      ((primedObjectProperty B S hS f y).ι.inheritedTopology
        (ambientTwoFibreProductTopology B S hS f y .etale))
      (ambientTwoFibreProductTopology B S hS f y .etale) :=
  isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS _ _ .etale
    (SubsitePushforward.isFiberedInGroupoids_ambientStructureFunctor _ _ _ _ _
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.w)
    (isClosedUnderSitePullback_primedObjectProperty B S hS f y)

end LisseEtale

namespace FlatFppf

/-- **Stacks 07AK (1) for the primed 2-fibre product, the flat case.** The full subcategory of
`V ×_{y, 𝒴} 𝒳` cut out by flatness of the `𝒳`-component is closed under the morphisms of the
2-fibre product lying over a flat morphism of schemes; the locally-finite-presentation hypothesis
of the source is not needed. -/
theorem isClosedUnderSitePullback_primedObjectProperty (y : FlatFppf B S hS 𝒴) :
    IsClosedUnderSitePullback B S hS
      (SubsitePushforward.ambientStructureFunctor 𝒳.val.val.p 𝒴.val.val.p
        f.hom.hom.toFunctor (ambientChoiceOfPullbacks B S hS 𝒴) y)
      (primedObjectProperty B S hS f y) .fppf := by
  refine Or.inr ⟨rfl, ?_⟩
  intro a b k hk _ hb
  refine flatObject_of_flat B S hS 𝒳 k.b ?_ hb
  let : Flat ((BigFppfOver.toScheme B S hS).map k.hbase) := hk
  let := k.hb
  exact flat_map_of_isHomLift B S hS 𝒳.val.val.p k.hbase k.b

/-- **Stacks 07AK, continuity, for the primed 2-fibre product in the flat case.** -/
theorem isContinuous_primedInclusion (y : FlatFppf B S hS 𝒴) :
    (primedObjectProperty B S hS f y).ι.IsContinuous
      ((primedObjectProperty B S hS f y).ι.inheritedTopology
        (ambientTwoFibreProductTopology B S hS f y .fppf))
      (ambientTwoFibreProductTopology B S hS f y .fppf) :=
  isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS _ _ .fppf
    (SubsitePushforward.isFiberedInGroupoids_ambientStructureFunctor _ _ _ _ _
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.w)
    (isClosedUnderSitePullback_primedObjectProperty B S hS f y)

/-- **Stacks 07AK, cocontinuity, for the primed 2-fibre product in the flat case.** -/
theorem isCocontinuous_primedInclusion (y : FlatFppf B S hS 𝒴) :
    (primedObjectProperty B S hS f y).ι.IsCocontinuous
      ((primedObjectProperty B S hS f y).ι.inheritedTopology
        (ambientTwoFibreProductTopology B S hS f y .fppf))
      (ambientTwoFibreProductTopology B S hS f y .fppf) :=
  isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS _ _ .fppf
    (SubsitePushforward.isFiberedInGroupoids_ambientStructureFunctor _ _ _ _ _
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.w)
    (isClosedUnderSitePullback_primedObjectProperty B S hS f y)

end FlatFppf

end AlgebraicGeometry.Stack

end
