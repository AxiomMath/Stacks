module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.InverseImage

/-!
# The canonical morphism to a ringed topos from its inverse image

Given a morphism of topoi `f : Sh(C) ⟶ Sh(D)` and a ringed topos `Y = (Sh(D), O_Y)`, the source
topos carries the inverse-image structure sheaf `f⁻¹O_Y`, and the resulting ringed topos has a
canonical morphism to `Y`: the underlying morphism of topoi is `f`, and the structure map is the
unit of the ring-level adjunction `f⁻¹ ⊣ f_*`, whose inverse-image form is therefore the
identity.

## Main definitions

* `AlgebraicGeometry.inverseImageRingedTopos`: the source topos with the inverse-image structure
  sheaf.
* `AlgebraicGeometry.inverseImageRingedToposHom`: its canonical morphism to the target.

## Implementation notes

The four `GrothendieckTopology.HasSheafCompose` hypotheses are those of
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, which is what makes
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor` and
`.pushforwardCommRingFunctor` — and hence `AlgebraicGeometry.RingedToposHom` — available. They
are assumed rather than derived, for the reason recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposRingImageAdjunction.lean`; they are
automatic when the universes of the site and of the sections coincide.

## References

* [Stacks Project, Tag 04KR](https://stacks.math.columbia.edu/tag/04KR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry

universe w v u w' v' u'

section

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  (Y : RingedTopos.{v', u', w'})
  (f : MorphismOfTopoi (Sheaf J (Type w)) Y.Topos)
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- The source topos of a morphism of topoi, equipped with the inverse image of the structure
sheaf of a ringed topos on the target. -/
noncomputable abbrev inverseImageRingedTopos : RingedTopos.{v, u, w} :=
  { C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O }

/-- The canonical morphism of ringed topoi from the inverse-image ringed topos: its underlying
morphism of topoi is the given one, and its structure map is the unit of the adjunction between
the inverse image and the direct image of sheaves of commutative rings. -/
noncomputable def inverseImageRingedToposHom :
    RingedToposHom (inverseImageRingedTopos C J Y f) Y where
  toToposHom := f
  fSharp := (commRingImageAdjunction f).unit.app Y.O

@[simp]
lemma inverseImageRingedToposHom_toToposHom :
    (inverseImageRingedToposHom C J Y f).toToposHom = f := rfl

@[simp]
lemma inverseImageRingedToposHom_fSharp :
    (inverseImageRingedToposHom C J Y f).fSharp =
      (commRingImageAdjunction f).unit.app Y.O := rfl

/-- The inverse-image form of the structure map of the canonical morphism is the identity. -/
lemma inverseImageRingedToposHom_fSharpInverseImage :
    (inverseImageRingedToposHom C J Y f).fSharpInverseImage =
      𝟙 ((inverseImageCommRingFunctor f).obj Y.O) :=
  (commRingImageAdjunction f).homEquiv_symm_unit Y.O

end

end AlgebraicGeometry

end
