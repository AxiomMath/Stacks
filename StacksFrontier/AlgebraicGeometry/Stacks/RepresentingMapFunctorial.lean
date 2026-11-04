module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProduct

/-!
# Functoriality of the morphism of representing presheaves (Stacks 04SW)

Stacks 04SW identifies 1-morphisms of categories fibred in groupoids represented by presheaves
`F` and `G`, modulo 2-isomorphism, with morphisms `F ⟶ G` of the representing presheaves. This
module records that the identification is functorial: it is constant on 2-isomorphism classes,
it takes a composite of 1-morphisms to the composite of the induced morphisms, and it takes the
1-morphism attached to a morphism of presheaves by **Stacks 0458** back to that morphism.

Together these turn a 2-commutative square of 1-morphisms between represented categories into a
commuting square of morphisms of representing presheaves, which is the step the proof of
Stacks 06FM needs in order to read a diagram of algebraic spaces over a pair of represented
stacks as a diagram of morphisms of algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.representingMap_congr_twoIso`: 2-isomorphic 1-morphisms induce the
  same morphism of representing presheaves.
* `AlgebraicGeometry.Stack.representingMap_id` and
  `AlgebraicGeometry.Stack.representingMap_comp`: functoriality.
* `AlgebraicGeometry.Stack.representingMap_congr_equivalenceOver` and
  `AlgebraicGeometry.Stack.representingMap_comparison_square`: how the induced morphism of
  representing presheaves changes when the two comparison equivalences are replaced by others —
  it is conjugated by the comparison morphism on each side.
* `AlgebraicGeometry.Stack.representingMap_associatedMap`: the induced morphism of the
  1-morphism of Stacks 0458 attached to `h : F ⟶ G`, read through the identity comparisons, is
  `h` itself.
* `AlgebraicGeometry.Stack.representingMap_square_comm`: the three combined — a 2-commutative
  square of 1-morphisms between represented categories induces a commuting square of morphisms
  of representing presheaves.
* `AlgebraicGeometry.Stack.existsUnique_twoIso_of_representingMap_eq`: two 1-morphisms with the
  same induced morphism of representing presheaves admit a unique isomorphism of underlying
  functors with all components over identities.
* `AlgebraicGeometry.Stack.nonempty_unique_twoIso_of_representingMap_eq`: the same read in the
  2-category of categories fibred in groupoids — there is exactly one 2-isomorphism between
  them.

## Implementation notes

No declaration carries a `@[stacks]` attribute: the identification itself is already tagged as
`AlgebraicGeometry.Stack.morphismSpaceEquiv` (**Stacks 04SW**), whose covering set includes the
computation rules these proofs run on, and the source states no functoriality lemma separately.

The last two results are the uniqueness clause of Stacks 04SW phrased over
`AlgebraicGeometry.Stack.representingMap`, which is the shape every consumer of this file holds
an equality in: `AlgebraicGeometry.Stack.existsUnique_twoIso_of_morphismSpaceEquiv_eq` takes its
two 1-morphisms as elements of the subtype `{G // G ⋙ p' = p}`, so applying it to an equality of
`representingMap`s means rebuilding that subtype at the call site. They carry no tag of their
own; the part key *uniqueness up to unique two-isomorphism* stays on the tagged theorem they
call. The 2-category form is the source's own wording — *"unique up to unique 2-isomorphism"* —
and is obtained from the underlying-functor form by `CategoryTheory.BasedNatIso.mkNatIso`
together with `CategoryTheory.CatFiberedInGroupoids.underlyingIso`, which is injective by
`CategoryTheory.Bicategory.InducedBicategory.hom₂_ext`; it is `Nonempty (Unique _)` rather than
`Unique _` because the witness is extracted from an `ExistsUnique`, which eliminates only into
`Prop`.

`AlgebraicGeometry.Stack.representingMap` is `AlgebraicGeometry.Stack.morphismSpaceEquiv`
evaluated at the 2-isomorphism class of a 1-morphism, so being well defined on 2-isomorphism
classes is `Quotient.sound` applied to `CategoryTheory.Functor.twoIsoSetoid`; the witness is
`CategoryTheory.CatFiberedInGroupoids.underlyingIso` of the 2-cell, whose components lie over
identities. Composition and the identity go through
`AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_sectionOfObj` and
`AlgebraicGeometry.Stack.morphismSpaceEquiv_app_sectionOfObj`: a morphism of representing
presheaves is determined by its values on named sections, and on a named section each side names
the section belonging to the image object.

## References

* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two 2-isomorphic 1-morphisms of categories fibred in groupoids over the big fppf site of `S`
induce the same morphism of representing presheaves: the identification of Stacks 04SW is defined
on 2-isomorphism classes, and a 2-cell of the 2-category of categories fibred in groupoids has
all its components over identities. -/
theorem representingMap_congr_twoIso
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    {a a' : 𝒜 ⟶ 𝒞} (η : a ≅ a') :
    representingMap B S hS 𝒜 𝒞 F G eF eG a = representingMap B S hS 𝒜 𝒞 F G eF eG a' := by
  refine congrArg (morphismSpaceEquiv B S hS 𝒜 𝒞 F G eF eG) (Quotient.sound ?_)
  exact ⟨CatFiberedInGroupoids.underlyingIso η, fun x => η.hom.hom.isHomLift' x⟩

/-- The identity 1-morphism induces the identity morphism of the representing presheaf. -/
theorem representingMap_id
    (𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p) :
    representingMap B S hS 𝒜 𝒜 F F eF eF (𝟙 𝒜) = 𝟙 F :=
  morphismSpaceEquiv_eq_of_sectionOfObj B S hS 𝒜 𝒜 F F eF eF _ (𝟙 F) (fun _ _ _ => rfl)

/-- A composite of 1-morphisms induces the composite of the morphisms of representing
presheaves. -/
theorem representingMap_comp
    {𝒜 ℬ 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      ℬ.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    (a : 𝒜 ⟶ ℬ) (c : ℬ ⟶ 𝒞) :
    representingMap B S hS 𝒜 𝒞 F H eF eH (a ≫ c) =
      representingMap B S hS 𝒜 ℬ F G eF eG a ≫ representingMap B S hS ℬ 𝒞 G H eG eH c := by
  refine morphismSpaceEquiv_eq_of_sectionOfObj B S hS 𝒜 𝒞 F H eF eH
    ⟨CatFiberedInGroupoids.homFunctor (a ≫ c),
      CatFiberedInGroupoids.homFunctor_comp_p (a ≫ c)⟩ _ (fun z W hz => ?_)
  have h1 := morphismSpaceEquiv_app_sectionOfObj B S hS 𝒜 ℬ F G eF eG
    ⟨CatFiberedInGroupoids.homFunctor a, CatFiberedInGroupoids.homFunctor_comp_p a⟩ z hz
  have h2 := morphismSpaceEquiv_app_sectionOfObj B S hS ℬ 𝒞 G H eG eH
    ⟨CatFiberedInGroupoids.homFunctor c, CatFiberedInGroupoids.homFunctor_comp_p c⟩
    ((CatFiberedInGroupoids.homFunctor a).obj z)
    ((Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a) z).trans hz)
  rw [NatTrans.comp_app, types_comp_apply, h1, h2]
  rfl

section ChangeOfEquivalence

variable {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (F F' G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eF' : StacksRepresentableCFG.EquivalenceOver
    𝒜.val.p (presheafOfCategories (F' ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver
    𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
  (eG' : StacksRepresentableCFG.EquivalenceOver
    𝒞.val.p (presheafOfCategories (G' ⋙ typeToCat)).p)
  (a : 𝒜 ⟶ 𝒞)

/-- **Changing the comparison equivalences conjugates the morphism of representing presheaves.**
Let `a : 𝒜 ⟶ 𝒞` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`,
let `𝒜` be exhibited as the category of elements of `F` by `eF` and of `F'` by `eF'`, and let `𝒞`
be exhibited as that of `G` by `eG` and of `G'` by `eG'`. Then the morphism of representing
presheaves read off the primed comparisons is the one read off the unprimed comparisons,
precomposed with the comparison morphism `F' ⟶ F` and postcomposed with the comparison morphism
`G ⟶ G'`.

The two comparison morphisms are themselves instances of Stacks 04SW: the morphism of
representing presheaves induced by the *identity* 1-morphism, read through one comparison on the
source and the other on the target. They are isomorphisms — automorphisms when `F = F'` and
`G = G'` — and in that form they are `AlgebraicGeometry.Stack.representingIso`, whose `hom` and
`inv` fields are by definition the very terms appearing here:
`(representingIso B S hS F F' eF eF').inv = representingMap B S hS 𝒜 𝒜 F' F eF' eF (𝟙 𝒜)` and
`(representingIso B S hS G G' eG eG').hom = representingMap B S hS 𝒞 𝒞 G G' eG eG' (𝟙 𝒞)` both
hold by `rfl`, so a consumer needing invertibility passes through that isomorphism with no
further lemma.

This is the statement that a transport of a predicate along a change of comparison equivalences
consumes. There is no invariance at a fixed morphism to be had: changing `eF` already changes
which morphism of presheaves `a` is sent to, so the law relates composites, with a comparison
isomorphism on each side. -/
theorem representingMap_congr_equivalenceOver :
    representingMap B S hS 𝒜 𝒞 F' G' eF' eG' a =
      representingMap B S hS 𝒜 𝒜 F' F eF' eF (𝟙 𝒜) ≫
        representingMap B S hS 𝒜 𝒞 F G eF eG a ≫
          representingMap B S hS 𝒞 𝒞 G G' eG eG' (𝟙 𝒞) := by
  rw [← Category.assoc,
    ← representingMap_comp B S hS F' F G eF' eF eG (𝟙 𝒜) a,
    ← representingMap_comp B S hS F' G G' eF' eG eG' (𝟙 𝒜 ≫ a) (𝟙 𝒞),
    Category.comp_id, Category.id_comp]

/-- **The change-of-comparison law as a commuting square**, with no inverse taken: the comparison
morphism `F ⟶ F'` followed by the morphism of representing presheaves read off the primed
comparisons is the morphism read off the unprimed comparisons followed by the comparison morphism
`G ⟶ G'`.

Both composites are the morphism of representing presheaves induced by `a` read through `eF` on
the source and `eG'` on the target, so this is naturality of the identification of Stacks 04SW in
the comparison equivalence. It is the form to use when only the forward comparison morphisms are
at hand; `AlgebraicGeometry.Stack.representingMap_congr_equivalenceOver` is the same law solved
for the primed morphism. -/
theorem representingMap_comparison_square :
    representingMap B S hS 𝒜 𝒜 F F' eF eF' (𝟙 𝒜) ≫
        representingMap B S hS 𝒜 𝒞 F' G' eF' eG' a =
      representingMap B S hS 𝒜 𝒞 F G eF eG a ≫
        representingMap B S hS 𝒞 𝒞 G G' eG eG' (𝟙 𝒞) := by
  rw [← representingMap_comp B S hS F F' G' eF eF' eG' (𝟙 𝒜) a,
    ← representingMap_comp B S hS F G G' eF eG eG' a (𝟙 𝒞),
    Category.id_comp, Category.comp_id]

end ChangeOfEquivalence

/-- **Stacks 0458 against Stacks 04SW.** The 1-morphism attached to a morphism `h : F ⟶ G` of
presheaves on the big fppf site of `S` induces, through the identity comparisons of the two
categories of elements, the morphism `h` itself. -/
theorem representingMap_associatedMap
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (h : F ⟶ G) :
    representingMap B S hS (fibredCategory B S hS F) (fibredCategory B S hS G) F G
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (associatedMap B S hS h).1 = h :=
  morphismSpaceEquiv_eq_of_comp_eq B S hS _ _ F G _ _ _ h rfl

/-- **A 2-commutative square of 1-morphisms between represented categories is a commuting square
of morphisms of representing presheaves.** Given a 1-morphism `f : 𝒳 ⟶ 𝒴` between categories
represented by `F` and `G`, two 1-morphisms `a`, `b` out of the categories of elements of
presheaves `U` and `V`, a morphism `h : U ⟶ V`, and an invertible 2-cell exhibiting the square as
2-commutative, the induced morphisms of representing presheaves commute on the nose.

This is the form in which the hypothesis of a diagram of Stacks 06FM is fed to the criteria of
Stacks 06FA, which ask for an equation of morphisms of algebraic spaces rather than a 2-cell. -/
theorem representingMap_square_comm
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : fibredCategory B S hS U ⟶ 𝒳)
    (b : fibredCategory B S hS V ⟶ 𝒴)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b ≅ a ≫ f) :
    h ≫ representingMap B S hS (fibredCategory B S hS V) 𝒴 V G
          (StacksRepresentableCFG.EquivalenceOver.refl _) eY b =
      representingMap B S hS (fibredCategory B S hS U) 𝒳 U F
          (StacksRepresentableCFG.EquivalenceOver.refl _) eX a ≫
        representingMap B S hS 𝒳 𝒴 F G eX eY f := by
  have e1 : representingMap B S hS (fibredCategory B S hS U) 𝒴 U G
        (StacksRepresentableCFG.EquivalenceOver.refl _) eY
        ((associatedMap B S hS h).1 ≫ b) =
      h ≫ representingMap B S hS (fibredCategory B S hS V) 𝒴 V G
        (StacksRepresentableCFG.EquivalenceOver.refl _) eY b := by
    rw [representingMap_comp (𝒜 := fibredCategory B S hS U) (ℬ := fibredCategory B S hS V)
      (𝒞 := 𝒴) B S hS U V G (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) eY, representingMap_associatedMap]
  exact e1.symm.trans <|
    (representingMap_congr_twoIso (𝒜 := fibredCategory B S hS U) (𝒞 := 𝒴) B S hS U G
      (StacksRepresentableCFG.EquivalenceOver.refl _) eY η).trans <|
    representingMap_comp (𝒜 := fibredCategory B S hS U) (ℬ := 𝒳) (𝒞 := 𝒴) B S hS U F G
      (StacksRepresentableCFG.EquivalenceOver.refl _) eX eY a f

section Uniqueness

universe w

variable (𝒳 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, w} (BigFppfOver B S hS))
  (F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eH : StacksRepresentableCFG.EquivalenceOver
    𝒵.val.p (presheafOfCategories (H ⋙ typeToCat)).p)

/-- **The uniqueness clause of Stacks 04SW, over `AlgebraicGeometry.Stack.representingMap`.**
Two 1-morphisms `f, g : 𝒳 ⟶ 𝒵` of categories fibred in groupoids represented by `F` and `H`
which induce the same morphism `F ⟶ H` of representing presheaves admit a unique isomorphism of
their underlying functors all of whose components lie over identities of the site. -/
theorem existsUnique_twoIso_of_representingMap_eq {f g : 𝒳 ⟶ 𝒵}
    (h : representingMap B S hS 𝒳 𝒵 F H eF eH f =
      representingMap B S hS 𝒳 𝒵 F H eF eH g) :
    ∃! α : CatFiberedInGroupoids.homFunctor f ≅ CatFiberedInGroupoids.homFunctor g,
      ∀ x : 𝒳.val.obj, 𝒵.val.p.IsHomLift (𝟙 (𝒳.val.p.obj x)) (α.hom.app x) :=
  existsUnique_twoIso_of_morphismSpaceEquiv_eq B S hS 𝒳 𝒵 F H eF eH
    ⟨CatFiberedInGroupoids.homFunctor f, CatFiberedInGroupoids.homFunctor_comp_p f⟩
    ⟨CatFiberedInGroupoids.homFunctor g, CatFiberedInGroupoids.homFunctor_comp_p g⟩ h

/-- **The uniqueness clause of Stacks 04SW in the source's own wording.** Two 1-morphisms
`f, g : 𝒳 ⟶ 𝒵` which induce the same morphism of representing presheaves are related by exactly
one 2-isomorphism of the 2-category of categories fibred in groupoids over the site. -/
theorem nonempty_unique_twoIso_of_representingMap_eq {f g : 𝒳 ⟶ 𝒵}
    (h : representingMap B S hS 𝒳 𝒵 F H eF eH f =
      representingMap B S hS 𝒳 𝒵 F H eF eH g) :
    Nonempty (Unique (f ≅ g)) := by
  obtain ⟨α, hα, huniq⟩ :=
    existsUnique_twoIso_of_representingMap_eq B S hS 𝒳 𝒵 F H eF eH h
  refine ⟨⟨⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso α hα)⟩, fun η =>
    Iso.ext <| Bicategory.InducedBicategory.hom₂_ext ?_⟩⟩
  apply BasedNatTrans.ext
  exact congrArg Iso.hom
    (huniq (CatFiberedInGroupoids.underlyingIso η) (fun x => η.hom.hom.isHomLift' x))

end Uniqueness

end AlgebraicGeometry.Stack

end
