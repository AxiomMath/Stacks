module

public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceSections
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceEtale

/-!
# The morphism of algebraic spaces determined by a 1-morphism (Stacks 04SW)

Let `𝒳` and `𝒴` be categories fibred in groupoids over the big fppf site of `S` which are
representable by algebraic spaces `F` and `G` through chosen equivalences over the site, and let
`f : 𝒳 ⥤ 𝒴` be a 1-morphism over the site. The equation of Stacks 04SW identifies 1-morphisms
`𝒳 ⟶ 𝒴` modulo 2-isomorphism with morphisms `F ⟶ G` of algebraic spaces. This file says *which*
morphism of algebraic spaces a given 1-morphism is identified with, and pins it down by a
property it alone has.

The morphism itself is already constructed, as
`AlgebraicGeometry.Space.inducedSpaceMap` — a section of `F` over `U` is an object of `𝒳` over
`U`, its image under `f` is an object of `𝒴` over `U`, hence a section of `G` over `U` — and that
recipe is exactly the characterisation proved here: the induced morphism carries the section of
`F` named by an object `z` of `𝒳` to the section of `G` named by `f z`, and it is the only
morphism of presheaves that does. Naming a section is
`CategoryTheory.PresheafOfCategories.sectionOfObj`.

Two consequences are the point of the file. First, a morphism of algebraic spaces `F ⟶ G` is the
one determined by `f` *if and only if* it carries each named section to the named image section:
this is the compatibility that pins a free morphism-of-spaces parameter against a 1-morphism
parameter, and it is what a statement about "the induced morphism of algebraic spaces" — such as
Stacks 073N and hence Stacks 075N — needs in order to be well posed. Second, the bijection of
Stacks 04SW itself, `AlgebraicGeometry.Stack.morphismSpaceEquiv`, takes the class of `f` to that
same constructed morphism, so the abstract identification and the explicit recipe agree.

## Main results

* `AlgebraicGeometry.Space.inducedSpaceMap_app_sectionOfObj`: the induced morphism of
  representing presheaves carries the section named by `z` to the section named by `f z`.
* `AlgebraicGeometry.Space.eq_inducedSpaceMap_of_app_sectionOfObj`: conversely, a morphism of the
  representing presheaves with that property *is* the induced one.
* `AlgebraicGeometry.Space.eq_inducedSpacesHom_iff_forall_sectionOfObj`: **Stacks 04SW**, the
  morphism of algebraic spaces determined by a 1-morphism, characterised on named sections.
* `AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_inducedSpaceMap`: **Stacks 04SW**, the bijection
  of morphism spaces takes the class of a 1-morphism to the constructed induced morphism of
  representing presheaves.

## Implementation notes

The universes of the two characterisations differ, and that difference is the reason both are
stated. Everything in the `AlgebraicGeometry.Space` namespace below leaves the total categories
of `𝒳` and `𝒴` at four independent universes, as `AlgebraicGeometry.Space.inducedSpaceMap` does,
because the construction and its characterisation use only the verticality `f ⋙ q = p` and the
two chosen equivalences. `AlgebraicGeometry.Stack.morphismSpaceEquiv` is stated for bundled
objects of the 2-category `CategoryTheory.CatFiberedInGroupoids`, whose morphism universe is tied
to that of the site, so the identification with the bijection is only available there. A consumer
that has to stay universe-polymorphic — a square of ringed topoi over the two small étale sites,
say — therefore expresses the compatibility by
`AlgebraicGeometry.Space.eq_inducedSpacesHom_iff_forall_sectionOfObj`, and reads
`AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_inducedSpaceMap` as the certificate that this is
the 04SW identification and not merely some construction.

Both proofs go through the one-object statement rather than through any unfolding of
`AlgebraicGeometry.Stack.morphismSpaceEquiv`: the first transports
`AlgebraicGeometry.Space.inducedSpaceMap_app`, an equality of objects of the category of
elements of `G`, along `CategoryTheory.PresheafOfCategories.sectionOfObj_eq_of_obj_eq`, and then
replaces the canonical object naming the section by the given `z`, which is isomorphic to it in
the fibre; the second is surjectivity of naming,
`CategoryTheory.PresheafOfCategories.exists_sectionOfObj`.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)

/-- **The induced morphism of representing presheaves, on a named section.** The morphism
`F ⟶ G` determined by a 1-morphism `f : 𝒳 ⥤ 𝒴` over the site carries the section of `F` over `W`
named by an object `z` of `𝒳` lying over `W` to the section of `G` over `W` named by `f z`.

This is the defining recipe of `AlgebraicGeometry.Space.inducedSpaceMap` read through the naming
of sections: `AlgebraicGeometry.Space.inducedSpaceMap_app` says it for the *canonical* object
attached to a section, and the canonical object naming `sectionOfObj eF z h` is isomorphic to
`z` in the fibre of `p` over `W`, an isomorphism which `f` carries to the fibre of `q`. -/
theorem inducedSpaceMap_app_sectionOfObj
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (z : 𝒳) {W : BigFppfOver B S hS} (h : p.obj z = W) :
    (inducedSpaceMap B S hS F G p q eF eG f hf).app (op W)
        (PresheafOfCategories.sectionOfObj eF z h) =
      PresheafOfCategories.sectionOfObj eG (f.obj z)
        ((Functor.congr_obj hf z).trans h) := by
  set x := PresheafOfCategories.sectionOfObj eF z h
  -- the canonical object of `𝒳` over `W` attached to the section `x`
  set xa : 𝒳 := eF.inv.functor.obj ⟨W, Discrete.mk x⟩
  have hxaW : p.obj xa = W :=
    Functor.congr_obj eF.inv.w (⟨W, Discrete.mk x⟩ :
      (presheafOfCategories (F ⋙ typeToCat)).obj)
  -- for the canonical object the statement is `inducedSpaceMap_app`, transported along
  -- `sectionOfObj_eq_of_obj_eq` for the identity equivalence on the category of elements of `G`
  have key : (inducedSpaceMap B S hS F G p q eF eG f hf).app (op W) x =
      PresheafOfCategories.sectionOfObj eG (f.obj xa)
        ((Functor.congr_obj hf xa).trans hxaW) :=
    PresheafOfCategories.sectionOfObj_eq_of_obj_eq
      (StacksRepresentableCFG.EquivalenceOver.refl _) eG
      (⟨W, Discrete.mk ((inducedSpaceMap B S hS F G p q eF eG f hf).app (op W) x)⟩ :
        (presheafOfCategories (G ⋙ typeToCat)).obj)
      (f.obj xa) rfl ((Functor.congr_obj hf xa).trans hxaW)
      (inducedSpaceMap_app B S hS F G p q eF eG f hf W x)
  refine key.trans ?_
  -- `z` and the canonical object name the same section, hence are isomorphic in the fibre
  have hinv : PresheafOfCategories.sectionOfObj eF xa hxaW = x :=
    PresheafOfCategories.sectionOfObj_inv_obj eF (⟨W, Discrete.mk x⟩ :
      (presheafOfCategories (F ⋙ typeToCat)).obj)
  have izx : (Functor.Fiber.mk h : p.Fiber W) ≅ Functor.Fiber.mk hxaW :=
    PresheafOfCategories.fiberIsoOfSectionOfObj_eq eF h hxaW hinv.symm
  -- push that isomorphism through `f` and name the section at both ends
  have iyz : (Functor.Fiber.mk ((Functor.congr_obj hf z).trans h) : q.Fiber W) ≅
      Functor.Fiber.mk ((Functor.congr_obj hf xa).trans hxaW) :=
    (Functor.fiberFunctorOfCompEq hf W).mapIso izx
  exact (PresheafOfCategories.sectionOfObj_eq_of_fiberIso eG _ _ iyz).symm

/-- **The induced morphism of representing presheaves is the only one computed by naming
sections.** A morphism `m : F ⟶ G` which carries the section named by every object `z` of `𝒳` to
the section named by `f z` is the morphism induced by `f`.

Every section of `F` is named by some object
(`CategoryTheory.PresheafOfCategories.exists_sectionOfObj`), so the hypothesis prescribes `m` at
every section, and `AlgebraicGeometry.Space.inducedSpaceMap_app_sectionOfObj` says the induced
morphism takes those prescribed values. -/
theorem eq_inducedSpaceMap_of_app_sectionOfObj
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (m : F ⟶ G)
    (hm : ∀ (z : 𝒳) (W : BigFppfOver B S hS) (h : p.obj z = W),
      m.app (op W) (PresheafOfCategories.sectionOfObj eF z h) =
        PresheafOfCategories.sectionOfObj eG (f.obj z)
          ((Functor.congr_obj hf z).trans h)) :
    m = inducedSpaceMap B S hS F G p q eF eG f hf := by
  ext W s
  obtain ⟨W⟩ := W
  obtain ⟨z, h, rfl⟩ := PresheafOfCategories.exists_sectionOfObj eF (W := W) s
  exact (hm z W h).trans
    (inducedSpaceMap_app_sectionOfObj B S hS F G p q eF eG f hf z h).symm

section Spaces

variable {X Y : AlgebraicSpaces B S hS}

/-- **The induced morphism of algebraic spaces, on a named section.** The morphism `X ⟶ Y` of
algebraic spaces determined by a 1-morphism `f : 𝒳 ⥤ 𝒴` over the site carries the section of `X`
named by an object `z` of `𝒳` to the section of `Y` named by `f z`. -/
theorem inducedSpacesHom_hom_app_sectionOfObj
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (X.1 ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (z : 𝒳) {W : BigFppfOver B S hS} (h : p.obj z = W) :
    (inducedSpacesHom B S hS p q eF eG f hf).hom.app (op W)
        (PresheafOfCategories.sectionOfObj eF z h) =
      PresheafOfCategories.sectionOfObj eG (f.obj z)
        ((Functor.congr_obj hf z).trans h) :=
  inducedSpaceMap_app_sectionOfObj B S hS X.1 Y.1 p q eF eG f hf z h

/-- **Stacks 04SW.** A morphism `g : X ⟶ Y` of algebraic spaces is the one determined by a
1-morphism `f : 𝒳 ⥤ 𝒴` over the site if and only if it carries the section of `X` named by every
object `z` of `𝒳` to the section of `Y` named by `f z`.

This is the identification of Stacks 04SW stated as a property of a *given* morphism of algebraic
spaces: it is what pins a morphism of algebraic spaces appearing as a free parameter against a
1-morphism appearing as another, which is the compatibility a statement about "the induced
morphism of algebraic spaces" presupposes. The right-hand condition is the recipe of the source —
an object of `𝒳` over `U` is a section of `X` over `U`, and `f` of it is a section of `Y` over
`U` — and the left-hand side is
`AlgebraicGeometry.Space.inducedSpacesHom`, the morphism of algebraic spaces that recipe
defines.

The hypotheses are those of the source: `X` and `Y` are algebraic spaces, and `eF`, `eG` are the
equivalences over the site exhibiting `𝒳` and `𝒴` as representable by them. Being equivalent
over the site to a category of elements already makes `p` and `q` fibred in groupoids, so no
such hypothesis is carried. -/
@[stacks 04SW "the morphism of algebraic spaces determined by a 1-morphism, characterised on
  named sections"]
theorem eq_inducedSpacesHom_iff_forall_sectionOfObj
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (X.1 ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (g : X ⟶ Y) :
    g = inducedSpacesHom B S hS p q eF eG f hf ↔
      ∀ (z : 𝒳) (W : BigFppfOver B S hS) (h : p.obj z = W),
        g.hom.app (op W) (PresheafOfCategories.sectionOfObj eF z h) =
          PresheafOfCategories.sectionOfObj eG (f.obj z)
            ((Functor.congr_obj hf z).trans h) := by
  constructor
  · rintro rfl z W h
    exact inducedSpacesHom_hom_app_sectionOfObj B S hS p q eF eG f hf z h
  · exact fun hg => ObjectProperty.hom_ext _
      (eq_inducedSpaceMap_of_app_sectionOfObj B S hS X.1 Y.1 p q eF eG f hf g.hom hg)

end Spaces

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

/-- **Stacks 04SW.** The bijection of morphism spaces takes the 2-isomorphism class of a
1-morphism `Φ : 𝒳 ⥤ 𝒴` over the site to the morphism of representing presheaves that `Φ`
induces: the section of `G` attached to a section of `F` is the one named by the image under `Φ`
of the object naming it.

So the abstract identification `AlgebraicGeometry.Stack.morphismSpaceEquiv` and the explicit
construction `AlgebraicGeometry.Space.inducedSpaceMap` of Stacks 0GQA are the same map, and a
compatibility expressed through the latter — as
`AlgebraicGeometry.Space.eq_inducedSpacesHom_iff_forall_sectionOfObj` expresses it — is a
compatibility with the former.

Both sides are computed on named sections: the left by
`AlgebraicGeometry.Stack.morphismSpaceEquiv_app_sectionOfObj`, the right by
`AlgebraicGeometry.Space.inducedSpaceMap_app_sectionOfObj`, and a morphism of representing
presheaves is determined by those values. -/
@[stacks 04SW "the bijection is the morphism of representing presheaves induced by the
  1-morphism"]
theorem morphismSpaceEquiv_eq_inducedSpaceMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, w} (BigFppfOver B S hS))
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (Φ : {H : 𝒳.val.obj ⥤ 𝒴.val.obj // H ⋙ 𝒴.val.p = 𝒳.val.p}) :
    morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ Φ) =
      Space.inducedSpaceMap B S hS F G 𝒳.val.p 𝒴.val.p eX eY Φ.1 Φ.2 :=
  Space.eq_inducedSpaceMap_of_app_sectionOfObj B S hS F G 𝒳.val.p 𝒴.val.p eX eY Φ.1 Φ.2 _
    (fun z _W h => morphismSpaceEquiv_app_sectionOfObj B S hS 𝒳 𝒴 F G eX eY Φ z h)

end AlgebraicGeometry.Stack

end
