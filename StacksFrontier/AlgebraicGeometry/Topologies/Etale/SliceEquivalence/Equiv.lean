module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization

/-!
# The small étale site of an étale object is the slice of the small étale site

Let `B` be a big étale site, let `X` be a scheme in it and let `j : U ⟶ X` be an object of the
small étale site of `X`. An étale scheme `V ⟶ U` over `U` is étale over `X` through `V ⟶ U ⟶ X`,
and it comes with its original arrow to `U`; this is an object of the slice of the small étale
site of `X` over `U`. Conversely an object of that slice is a scheme over `X` étale over `X`
together with a map to `U` over `X`, and that map is étale because `U ⟶ X` is, so the object is
an étale scheme over `U`. The two constructions are mutually inverse up to canonical
isomorphism, so the small étale site of `U` is the slice `(X_ét)/U`.

This file constructs the equivalence of categories and pins it down: it is determined on
objects and on morphisms, and composing it with the forgetful functor of the slice gives back
composition with `j`, before any étale condition is forgotten. The identification of the two
Grothendieck topologies is proved separately, in
`StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence`.

## Main definitions

* `AlgebraicGeometry.smallEtaleOverObject` — the object of the slice attached to an étale
  scheme over `U`.
* `AlgebraicGeometry.smallEtaleEquivalenceOver` — the equivalence of categories.

## Main results

* `AlgebraicGeometry.smallEtaleEquivalenceOver_obj` and
  `AlgebraicGeometry.smallEtaleEquivalenceOver_map` — the action of the equivalence on objects
  and on morphisms.
* `AlgebraicGeometry.smallEtaleEquivalenceOver_restriction` — composing with the slice
  forgetful functor recovers `AlgebraicGeometry.smallEtalePostcompose`.

## Implementation notes

The functor is `CategoryTheory.Over.lift` of composition with `j`, along the natural
transformation whose component at `V` is the original arrow `V ⟶ U`; its inverse is the
`CategoryTheory.ObjectProperty.lift` of `CategoryTheory.Over.post` along the structure functor
of the small étale site, the étale condition being supplied by cancelling `U ⟶ X` on the right.
Both unit and counit are identities on underlying schemes, which is why the three
characterizing statements hold by `rfl`. The statement about morphisms is a `HEq`, since the
source and target of the transported morphism are only definitionally, not syntactically, the
ones of the original.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- The object of the slice `(X_ét)/U` attached to an étale scheme `V` over `U`: compose its
structure morphism with `U ⟶ X`, and retain its morphism to `U`. -/
public def smallEtaleOverObject (V : SmallEtale B U.obj.left.1 U.obj.left.property) : Over U :=
  let W : SmallEtale B X hX :=
    ⟨(Over.map U.obj.hom).obj V.obj,
      B.etale_map_comp V.obj.hom U.obj.hom V.property U.property⟩
  Over.mk (ObjectProperty.homMk (Over.homMk V.obj.hom (by rfl)) : W ⟶ U)

/-- **The small étale site of `U` is the localization of the small étale site of `X` at `U`.**
The equivalence of categories between the small étale site of an object `U` of the small étale
site of `X` and the slice of the latter over `U`. -/
public noncomputable def smallEtaleEquivalenceOver :
    SmallEtale B U.obj.left.1 U.obj.left.property ≌ Over U := by
  let F := Over.lift (smallEtalePostcompose B X hX U) {
    app := fun V => ObjectProperty.homMk (Over.homMk V.obj.hom (by cat_disch))
    naturality V W f := by
      ext
      exact congrArg (fun g => g.hom) f.hom.w }
  let GBase := Over.post (X := U)
    (SmallEtale.inclusion B X hX ⋙ BigEtaleOver.forget B X hX)
  let G := (BigEtaleOver.IsEtaleOver B U.obj.left.1 U.obj.left.property).lift GBase fun V =>
    B.etale_map_of_postcomp (GBase.obj V).hom U.obj.hom V.left.obj.hom
      V.left.property U.property (by simp [GBase, Over.post])
  exact
    { functor := F
      inverse := G
      unitIso := NatIso.ofComponents fun V =>
        ObjectProperty.isoMk (BigEtaleOver.IsEtaleOver B U.obj.left.1 U.obj.left.property)
          (Over.isoMk (Iso.refl V.obj.left) (by rfl))
      counitIso := NatIso.ofComponents fun V =>
        Over.isoMk
          (ObjectProperty.isoMk (BigEtaleOver.IsEtaleOver B X hX)
            (Over.isoMk (Iso.refl V.left.obj.left) (by
              change 𝟙 V.left.obj.left ≫ V.left.obj.hom = V.hom.hom.left ≫ U.obj.hom
              simp)))
          (by ext; rfl)
      functor_unitIso_comp V := by ext; rfl }

/-- The equivalence sends an étale scheme `V` over `U` to the composite `V ⟶ U ⟶ X` equipped
with the original arrow `V ⟶ U`. -/
public theorem smallEtaleEquivalenceOver_obj
    (V : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (smallEtaleEquivalenceOver B X hX U).functor.obj V = smallEtaleOverObject B X hX U V :=
  rfl

/-- On morphisms the equivalence retains the original morphism of schemes. -/
public theorem smallEtaleEquivalenceOver_map
    {V W : SmallEtale B U.obj.left.1 U.obj.left.property} (f : V ⟶ W) :
    HEq ((smallEtaleEquivalenceOver B X hX U).functor.map f).left.hom.left f.hom.left :=
  HEq.rfl

/-- Forgetting the structure morphism to `U` turns the equivalence into composition with
`U ⟶ X`. The equality holds in the small étale site of `X`, before the étale condition is
forgotten. -/
public theorem smallEtaleEquivalenceOver_restriction :
    (smallEtaleEquivalenceOver B X hX U).functor ⋙ Over.forget U =
      smallEtalePostcompose B X hX U :=
  rfl

end AlgebraicGeometry
