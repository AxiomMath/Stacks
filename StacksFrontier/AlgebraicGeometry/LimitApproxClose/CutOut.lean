module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StageColimit

/-!
# A diagram cut out by the images of a natural transformation is that transformation's source

Let `ν : E ⟶ D` be a natural transformation of diagrams of schemes whose components are open
immersions, and let `V` be a compatible family of opens of `D` with `V j` the image of `ν.app j`
for every `j`. Then the subdiagram of `D` cut out by `V` is naturally isomorphic to `E`.

Applied to the glueing `AlgebraicGeometry.gluePairFunctor` of two diagrams along a common open
subdiagram, this identifies the subdiagrams cut out by the images of the two legs, and by their
intersection, with the two diagrams and with the common diagram respectively.

## Main definitions

* `AlgebraicGeometry.compatibleOpensDiagramIso`: the natural isomorphism between `E` and the
  subdiagram of `D` cut out by a compatible family of opens equal to the images of `ν`.
* `AlgebraicGeometry.gluePairFunctorInlIso`, `AlgebraicGeometry.gluePairFunctorInrIso`: the
  subdiagram of the glued diagram cut out by the images of the first, respectively second, leg is
  the first, respectively second, diagram.
* `AlgebraicGeometry.gluePairFunctorInterIso`: the subdiagram of the glued diagram cut out by the
  intersection of the images of the two legs is the common diagram.

## Main results

* `AlgebraicGeometry.Scheme.gluePair_opensRange_inf`: inside a glueing, the images of the two
  legs meet exactly in the image of the common open subscheme.
* `AlgebraicGeometry.compatibleOpens_gluePairFunctorInl`,
  `AlgebraicGeometry.compatibleOpens_gluePairFunctorInr`,
  `AlgebraicGeometry.compatibleOpens_gluePairFunctorInter`: the images of the first leg, of the
  second leg, and their intersections, are compatible families of opens of the glued diagram.

## Implementation notes

The family of opens is an argument of `AlgebraicGeometry.compatibleOpensDiagramIso`, together
with a pointwise identification of it with the images, so that it may be taken to be an
intersection of two families of images. Stagewise the isomorphism is
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`, and its naturality uses only the naturality of
`ν`.

## What is NOT done here

Nothing here produces a cone, a limit, or an inhabitant of
`AlgebraicGeometry.Scheme.FiniteTypeApproximation`: the cone of step (iii) and the three limiting
restricted cones it feeds are not built.  Tag 07RN is not proved and no tag attribute is attached
to anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v w u

namespace AlgebraicGeometry

/-- **A diagram cut out by the images of a natural transformation is that transformation's
source.** Here `V` is a compatible family of opens of `D` equal stagewise to the images
of `ν`. -/
noncomputable def compatibleOpensDiagramIso {J : Type w} [Category.{v} J]
    {D E : J ⥤ Scheme.{u}} (ν : E ⟶ D) [∀ j, IsOpenImmersion (ν.app j)]
    (V : ∀ j, (D.obj j).Opens) (hV : ∀ ⦃j k : J⦄ (u : j ⟶ k), D.map u ⁻¹ᵁ V k = V j)
    (hνV : ∀ j, (ν.app j).opensRange = V j) :
    E ≅ compatibleOpensDiagram D V hV :=
  NatIso.ofComponents
    (fun j ↦ IsOpenImmersion.isoOfRangeEq (ν.app j) (V j).ι (by
      rw [Scheme.Opens.range_ι, ← hνV j, Scheme.Hom.coe_opensRange]))
    fun {j k} u ↦ by
      refine (cancel_mono (Scheme.Opens.ι (V k))).mp ?_
      rw [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Category.assoc,
        Scheme.Hom.resLE_comp_ι, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        ν.naturality u]

/-- The defining equation of the components of
`AlgebraicGeometry.compatibleOpensDiagramIso`. -/
@[simp]
lemma compatibleOpensDiagramIso_hom_app_ι {J : Type w} [Category.{v} J]
    {D E : J ⥤ Scheme.{u}} (ν : E ⟶ D) [∀ j, IsOpenImmersion (ν.app j)]
    (V : ∀ j, (D.obj j).Opens) (hV : ∀ ⦃j k : J⦄ (u : j ⟶ k), D.map u ⁻¹ᵁ V k = V j)
    (hνV : ∀ j, (ν.app j).opensRange = V j) (j : J) :
    (compatibleOpensDiagramIso ν V hV hνV).hom.app j ≫ (V j).ι = ν.app j :=
  IsOpenImmersion.isoOfRangeEq_hom_fac (ν.app j) ((V j).ι)
    (by rw [Scheme.Opens.range_ι, ← hνV j, Scheme.Hom.coe_opensRange])

namespace Scheme

variable {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]

/-- **Inside a glueing the two legs meet exactly in the image of the common open subscheme.** -/
lemma gluePair_opensRange_inf :
    (gluePairInl f g).opensRange ⊓ (gluePairInr f g).opensRange =
      (f ≫ gluePairInl f g).opensRange := by
  refine le_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨p, hp⟩ := ht.1
    obtain ⟨q, hq⟩ := ht.2
    obtain ⟨z, hzp, -⟩ := (gluePairInl_eq_gluePairInr_iff f g).mp (hp.trans hq.symm)
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hzp, hp]⟩
  · obtain ⟨z, rfl⟩ := ht
    refine ⟨⟨f z, (Scheme.Hom.comp_apply _ _ _).symm⟩, ⟨g z, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, ← gluePair_condition f g, Scheme.Hom.comp_apply]

end Scheme

section Functor

variable {J : Type w} [Category.{v} J] {Dw Dx Dy : J ⥤ Scheme.{u}} (α : Dw ⟶ Dx) (β : Dw ⟶ Dy)
  [∀ j, IsOpenImmersion (α.app j)] [∀ j, IsOpenImmersion (β.app j)]
  (hα : ∀ ⦃j k : J⦄ (u : j ⟶ k), Dx.map u ⁻¹ᵁ (α.app k).opensRange = (α.app j).opensRange)
  (hβ : ∀ ⦃j k : J⦄ (u : j ⟶ k), Dy.map u ⁻¹ᵁ (β.app k).opensRange = (β.app j).opensRange)

include hβ in
/-- The images of the first leg of the glued stages are a compatible family of opens. -/
lemma compatibleOpens_gluePairFunctorInl ⦃j k : J⦄ (u : j ⟶ k) :
    (gluePairFunctor α β).map u ⁻¹ᵁ ((gluePairFunctorInl α β).app k).opensRange =
      ((gluePairFunctorInl α β).app j).opensRange :=
  preimage_opensRange_of_isPullback (isPullback_gluePairFunctorInl_app α β hβ u).flip

include hα in
/-- The images of the second leg of the glued stages are a compatible family of opens. -/
lemma compatibleOpens_gluePairFunctorInr ⦃j k : J⦄ (u : j ⟶ k) :
    (gluePairFunctor α β).map u ⁻¹ᵁ ((gluePairFunctorInr α β).app k).opensRange =
      ((gluePairFunctorInr α β).app j).opensRange :=
  preimage_opensRange_of_isPullback (isPullback_gluePairFunctorInr_app α β hα u).flip

include hα hβ in
/-- The intersections of the images of the two legs are a compatible family of opens. -/
lemma compatibleOpens_gluePairFunctorInter ⦃j k : J⦄ (u : j ⟶ k) :
    (gluePairFunctor α β).map u ⁻¹ᵁ
        (((gluePairFunctorInl α β).app k).opensRange ⊓
          ((gluePairFunctorInr α β).app k).opensRange) =
      ((gluePairFunctorInl α β).app j).opensRange ⊓
        ((gluePairFunctorInr α β).app j).opensRange :=
  CompatibleOpensPair.preimage_inf_compatible (compatibleOpens_gluePairFunctorInl α β hβ)
    (compatibleOpens_gluePairFunctorInr α β hα) u

/-- **The subdiagram of the glued stages cut out by the first leg is the first diagram.** -/
noncomputable def gluePairFunctorInlIso :
    Dx ≅ compatibleOpensDiagram (gluePairFunctor α β)
      (fun j ↦ ((gluePairFunctorInl α β).app j).opensRange)
      (compatibleOpens_gluePairFunctorInl α β hβ) :=
  compatibleOpensDiagramIso (gluePairFunctorInl α β) _ _ fun _ ↦ rfl

/-- **The subdiagram of the glued stages cut out by the second leg is the second diagram.** -/
noncomputable def gluePairFunctorInrIso :
    Dy ≅ compatibleOpensDiagram (gluePairFunctor α β)
      (fun j ↦ ((gluePairFunctorInr α β).app j).opensRange)
      (compatibleOpens_gluePairFunctorInr α β hα) :=
  compatibleOpensDiagramIso (gluePairFunctorInr α β) _ _ fun _ ↦ rfl

/-- Each component of the composite of `α` with the first leg of the glued diagram is an open
immersion. -/
instance isOpenImmersion_comp_gluePairFunctorInl_app (j : J) :
    IsOpenImmersion ((α ≫ gluePairFunctorInl α β).app j) :=
  inferInstanceAs (IsOpenImmersion (α.app j ≫ (gluePairFunctorInl α β).app j))

/-- **The subdiagram of the glued stages cut out by the intersection of the two legs is the
common diagram.** -/
noncomputable def gluePairFunctorInterIso :
    Dw ≅ compatibleOpensDiagram (gluePairFunctor α β)
      (fun j ↦ ((gluePairFunctorInl α β).app j).opensRange ⊓
        ((gluePairFunctorInr α β).app j).opensRange)
      (compatibleOpens_gluePairFunctorInter α β hα hβ) :=
  compatibleOpensDiagramIso (α ≫ gluePairFunctorInl α β) _ _ fun j ↦
    (Scheme.gluePair_opensRange_inf (α.app j) (β.app j)).symm

end Functor

end AlgebraicGeometry
