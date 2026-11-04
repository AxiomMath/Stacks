module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismFlatCover

/-!
# A representable étale morphism of fppf sheaves is flat and locally of finite type

Let `S` be a scheme contained in a big fppf site `B`. A morphism of fppf sheaves which is
representable by algebraic spaces and étale is also flat, locally of finite presentation and
locally of finite type, in the sense that the morphism of schemes underlying every commuting
square of étale scheme charts of each of its represented base changes has those properties.

Flatness and being locally of finite presentation are two of the three hypotheses of
**Stacks 05VM** in the form
`AlgebraicGeometry.FormalSpace.isLocallySurjective_of_surjective_flat`, which turns a
representable surjective flat cover into a surjection of fppf sheaves. The third, surjectivity,
is not implied by étaleness and has to come from elsewhere.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyULift_flat_of_isEtale`,
  `AlgebraicGeometry.FormalSpace.hasPropertyULift_locallyOfFinitePresentation_of_isEtale` and
  `AlgebraicGeometry.FormalSpace.hasPropertyULift_locallyOfFiniteType_of_isEtale`: a
  morphism of presheaves representable by algebraic spaces and étale is flat, locally of
  finite presentation and locally of finite type after every represented base change.
* `AlgebraicGeometry.FormalSpace.IsRepresentableEtale.hasPropertyULift_flat` and
  `AlgebraicGeometry.FormalSpace.IsRepresentableEtale.hasPropertyULift_locallyOfFinitePresentation`
  state the same for a morphism of fppf sheaves which is representable étale in the sense of
  Definition 0AIM.
* `AlgebraicGeometry.FormalSpace.IsRepresentableEtale.isLocallyOfFiniteType`: a morphism of
  fppf sheaves which is representable étale in the sense of Definition 0AIM is locally of
  finite type in the sense of part (1) of **Stacks 0AM4**.

## Implementation notes

All three are
`AlgebraicGeometry.FormalSpace.holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site` at the
property in question, which asks of that property only that it hold for an étale morphism of
schemes: no locality statement has to be supplied to it, and no hypothesis on the source
either. Being locally of finite type is the property in which
`AlgebraicGeometry.Space.IsLocallyOfFiniteTypeULift` and so part (1) of Stacks 0AM4 is
phrased, so the last of the three is that condition itself and not only a consequence of it.
This is the same argument
`AlgebraicGeometry.FormalSpace.hasPropertyULift_smooth_of_isRepresentableEtale` makes for
smoothness, read at two further properties; what differs between the three is only the
property.

## References

* [Stacks Project, Tag 03ZF](https://stacks.math.columbia.edu/tag/03ZF)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of presheaves representable by algebraic spaces and étale is flat after every
represented base change.** Flatness is étale local on the source and the target and holds for
an étale morphism of schemes, so it may be read off a single étale chart of the base change,
which its own étaleness supplies. -/
theorem hasPropertyULift_flat_of_isEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (c : F ⟶ G)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c)
    (hetale : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) c hrep) :
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsFlatULift.{u + 1} B S hS g.hom) c hrep := fun U ξ ↦
  holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS
    (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
    (fun _ _ ↦ inferInstance) _ (hetale U ξ)

/-- **A morphism of presheaves representable by algebraic spaces and étale is locally of finite
presentation after every represented base change.** Being locally of finite presentation is
étale local on the source and the target and holds for an étale morphism of schemes. -/
theorem hasPropertyULift_locallyOfFinitePresentation_of_isEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (c : F ⟶ G)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c)
    (hetale : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) c hrep) :
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsLocallyOfFinitePresentationULift.{u + 1} B S hS g.hom)
      c hrep := fun U ξ ↦
  holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    (fun _ _ ↦ inferInstance) _ (hetale U ξ)

/-- **A morphism of presheaves representable by algebraic spaces and étale is locally of finite
type after every represented base change.** Being locally of finite type is étale local on the
source and the target and holds for an étale morphism of schemes. -/
theorem hasPropertyULift_locallyOfFiniteType_of_isEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (c : F ⟶ G)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c)
    (hetale : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) c hrep) :
    Space.HasPropertyULift.{u + 1} B S hS
      (Space.locallyOfFiniteTypePropertyULift.{u + 1} B S hS) c hrep := fun U ξ ↦
  holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    (fun _ _ ↦ inferInstance) _ (hetale U ξ)

/-- A representable étale morphism of fppf sheaves, in the sense of Definition 0AIM, is flat
after every represented base change. -/
theorem IsRepresentableEtale.hasPropertyULift_flat {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hf : IsRepresentableEtale B S hS f) :
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsFlatULift.{u + 1} B S hS g.hom) f.hom hf.1 :=
  hasPropertyULift_flat_of_isEtale B S hS f.hom hf.1 hf.2

/-- A representable étale morphism of fppf sheaves, in the sense of Definition 0AIM, is locally
of finite presentation after every represented base change. -/
theorem IsRepresentableEtale.hasPropertyULift_locallyOfFinitePresentation
    {X Y : FppfSheaf B S hS} {f : X ⟶ Y} (hf : IsRepresentableEtale B S hS f) :
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsLocallyOfFinitePresentationULift.{u + 1} B S hS g.hom)
      f.hom hf.1 :=
  hasPropertyULift_locallyOfFinitePresentation_of_isEtale B S hS f.hom hf.1 hf.2

/-- **A representable étale morphism of fppf sheaves is locally of finite type.** The
representability witness is the one étaleness carries, and the condition on each represented
base change is `hasPropertyULift_locallyOfFiniteType_of_isEtale`. -/
theorem IsRepresentableEtale.isLocallyOfFiniteType {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hf : IsRepresentableEtale B S hS f) : IsLocallyOfFiniteType B S hS f :=
  ⟨hf.1, hasPropertyULift_locallyOfFiniteType_of_isEtale B S hS f.hom hf.1 hf.2⟩

end AlgebraicGeometry.FormalSpace

end
