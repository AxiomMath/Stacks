module

public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceIsoClass
public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# The 2-fibre product of represented stacks is represented by the fibre product (Stacks 04SD)

Let `𝒳`, `𝒴` and `𝒵` be categories fibred in groupoids over the big fppf site of `S`, represented
by presheaves `F`, `G` and `H` through chosen equivalences over the site, and let `f : 𝒳 ⟶ 𝒵` and
`g : 𝒴 ⟶ 𝒵` be 1-morphisms over the site. Stacks 04SW turns `f` and `g` into morphisms
`F ⟶ H` and `G ⟶ H` of presheaves (`AlgebraicGeometry.Stack.representingMap`). This file shows
that the presheaf of isomorphism classes of the 2-fibre product `𝒳 ×_𝒵 𝒴` over the site is the
fibre product `F ×_H G` of presheaves.

This is Stacks 04SD (`CategoryTheory.Functor.twoFibreProductIsoClassEquiv`: the presheaf of
isomorphism classes of a 2-fibre product is the fibre product of the presheaves of isomorphism
classes) composed, in each of the three corners, with the identification of the presheaf of
isomorphism classes of a represented stack with its representing presheaf
(`CategoryTheory.PresheafOfCategories.isoClassSectionEquiv`). The compatibility of those three
identifications with the two morphisms is `AlgebraicGeometry.Stack` 's
`morphismSpaceEquiv_app_isoClassSection`.

Its purpose is to recognise the representing presheaf of a base change: a 2-fibre product square
whose apex is represented by some presheaf has that presheaf isomorphic to `F ×_H G`, hence to
the pullback of `F ⟶ H` and `G ⟶ H`.

## Main definitions

* `AlgebraicGeometry.Stack.representingMap`: the morphism of representing presheaves induced by
  a 1-morphism over the site, Stacks 04SW.
* `AlgebraicGeometry.Stack.twoFibreProductIsoClassSectionEquiv`: the isomorphism classes in the
  fibre of the 2-fibre product over `U` are the sections of `F ×_H G` over `U`.
* `AlgebraicGeometry.Stack.fibreProductIsoRepresenting`: that bijection read as an isomorphism of
  presheaves, comparing `F ×_H G` with any presheaf representing the 2-fibre product.

## Implementation notes

The 2-fibre product section is stated at the universes Stacks 04SD and 04XC are used at,
`CatFiberedInGroupoids.{u, u, u + 1, u + 1}`: Stacks 04SD
(`CategoryTheory.Functor.twoFibreProductIsoClassEquiv`) needs the three factors and the 2-fibre
product itself to lie in one universe, which forces the object universe to absorb that of the
site.

## References

* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section RepresentingMap

variable (𝒳 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, w} (BigFppfOver B S hS))
  (F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eH : StacksRepresentableCFG.EquivalenceOver
    𝒵.val.p (presheafOfCategories (H ⋙ typeToCat)).p)

/-- **Stacks 04SW**, as a map of representing presheaves: the morphism `F ⟶ H` of representing
presheaves induced by a 1-morphism `f : 𝒳 ⟶ 𝒵` over the site. -/
noncomputable abbrev representingMap (f : 𝒳 ⟶ 𝒵) : F ⟶ H :=
  morphismSpaceEquiv B S hS 𝒳 𝒵 F H eF eH
    (Quotient.mk _ ⟨CatFiberedInGroupoids.homFunctor f,
      CatFiberedInGroupoids.homFunctor_comp_p f⟩)

end RepresentingMap

variable (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
variable (F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (eF : StacksRepresentableCFG.EquivalenceOver
    𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver
    𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
  (eH : StacksRepresentableCFG.EquivalenceOver
    𝒵.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
variable (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵)

/-- The structure functor of the 2-fibre product of `f` and `g` taken in the categories over the
site. -/
abbrev twoFibreProductStructureFunctor :
    TwoFibreProductOver 𝒳.val.p 𝒴.val.p 𝒵.val.p
        (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor g) ⥤
      BigFppfOver B S hS :=
  TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒴.val.p 𝒵.val.p
    (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor g)

/-- **Stacks 04SD for represented stacks.** The isomorphism classes in the fibre over `U` of the
2-fibre product `𝒳 ×_𝒵 𝒴` are the sections over `U` of the fibre product `F ×_H G` of the
representing presheaves. -/
noncomputable def twoFibreProductIsoClassSectionEquiv (U : BigFppfOver B S hS) :
    _root_.Quotient (isIsomorphicSetoid
        ((twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).Fiber U)) ≃
      (Presheaf.fibreProduct (representingMap B S hS 𝒳 𝒵 F H eF eH f)
        (representingMap B S hS 𝒴 𝒵 G H eG eH g)).obj (op U) := by
  let : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.property.isFibered
  let : 𝒵.val.p.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eH
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection H)
  refine (Functor.twoFibreProductIsoClassEquiv
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒵.property
      (CatFiberedInGroupoids.homFunctor_comp_p f))
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒵.property
      (CatFiberedInGroupoids.homFunctor_comp_p g)) U).trans
    ((Equiv.prodCongr (PresheafOfCategories.isoClassSectionEquiv eF U)
      (PresheafOfCategories.isoClassSectionEquiv eG U)).subtypeEquiv ?_)
  intro ab
  have hf := morphismSpaceEquiv_app_isoClassSection B S hS 𝒳 𝒵 F H eF eH
    ⟨CatFiberedInGroupoids.homFunctor f, CatFiberedInGroupoids.homFunctor_comp_p f⟩ U ab.1
  have hg := morphismSpaceEquiv_app_isoClassSection B S hS 𝒴 𝒵 G H eG eH
    ⟨CatFiberedInGroupoids.homFunctor g, CatFiberedInGroupoids.homFunctor_comp_p g⟩ U ab.2
  refine ⟨fun h => ?_, fun h => PresheafOfCategories.isoClassSection_injective eH U ?_⟩
  · exact hf.trans ((congrArg (PresheafOfCategories.isoClassSection eH U) h).trans hg.symm)
  · exact hf.symm.trans (h.trans hg)

/-- The section of `F` in the pair attached to a class in the fibre of the 2-fibre product over
`U` is the section named by the class of the image of that class under the first projection: both
sides are the section named by the first component of a representative. -/
theorem twoFibreProductIsoClassSectionEquiv_val_fst
    [hT : (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFibered]
    (U : BigFppfOver B S hS)
    (c : _root_.Quotient (isIsomorphicSetoid
      ((twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).Fiber U))) :
    letI : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
    (twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g U c).val.1 =
      PresheafOfCategories.isoClassSection eF U
        ((Functor.isoClassMap (p := twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g)
          (q := 𝒳.val.p)
          (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.property
            TwoFibreProductOver.fst_comp_eq)).app (op U) c) := by
  induction c using _root_.Quotient.ind with
  | _ x => rfl

/-- Naturality of `AlgebraicGeometry.Stack.twoFibreProductIsoClassSectionEquiv`: the two
components of the pair attached to a class restrict to the components of the pair attached to its
restriction. -/
theorem twoFibreProductIsoClassSectionEquiv_naturality
    [(twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFibered]
    {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (c : _root_.Quotient (isIsomorphicSetoid
      ((twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).Fiber U))) :
    (twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g V
        ((twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).isoClassPresheaf.map k.op c)).val =
      (F.map k.op
          (twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g U c).val.1,
        G.map k.op
          (twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g U c).val.2) := by
  let : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.property.isFibered
  let : 𝒵.val.p.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eH
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection H)
  have hnat := Functor.twoFibreProductIsoClassMap_naturality
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒵.property
      (CatFiberedInGroupoids.homFunctor_comp_p f))
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒵.property
      (CatFiberedInGroupoids.homFunctor_comp_p g)) k c
  refine Prod.ext ?_ ?_
  · exact (congrArg (PresheafOfCategories.isoClassSection eF V) (congrArg Prod.fst hnat)).trans
      (PresheafOfCategories.isoClassSection_map eF k _)
  · exact (congrArg (PresheafOfCategories.isoClassSection eG V) (congrArg Prod.snd hnat)).trans
      (PresheafOfCategories.isoClassSection_map eG k _)

/-- Naturality of `AlgebraicGeometry.Stack.twoFibreProductIsoClassSectionEquiv`, read as an
equality of sections of the fibre product of presheaves. -/
theorem twoFibreProductIsoClassSectionEquiv_map
    [(twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFibered]
    {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (c : _root_.Quotient (isIsomorphicSetoid
      ((twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).Fiber U))) :
    twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g V
        ((twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).isoClassPresheaf.map k.op c) =
      (Presheaf.fibreProduct (representingMap B S hS 𝒳 𝒵 F H eF eH f)
          (representingMap B S hS 𝒴 𝒵 G H eG eH g)).map k.op
        (twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g U c) :=
  Subtype.ext
    (twoFibreProductIsoClassSectionEquiv_naturality B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g k c)

section Representing

variable [(twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFibered]
  (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eT : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g)
    (presheafOfCategories (T ⋙ typeToCat)).p)

/-- **Stacks 04SD for represented stacks.** A presheaf `T` representing the 2-fibre product
`𝒳 ×_𝒵 𝒴` over the site is the fibre product `F ×_H G` of the representing presheaves of the two
factors: over each object both are the isomorphism classes in the fibre of the 2-fibre product,
by naming sections. -/
noncomputable def fibreProductIsoRepresenting :
    Presheaf.fibreProduct (representingMap B S hS 𝒳 𝒵 F H eF eH f)
        (representingMap B S hS 𝒴 𝒵 G H eG eH g) ≅ T := by
  refine NatIso.ofComponents
    (fun V => ((twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g
      V.unop).symm.trans (PresheafOfCategories.isoClassSectionEquiv eT V.unop)).toIso) ?_
  intro V V' k
  ext s
  have hs : (twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g V'.unop).symm
        ((Presheaf.fibreProduct (representingMap B S hS 𝒳 𝒵 F H eF eH f)
          (representingMap B S hS 𝒴 𝒵 G H eG eH g)).map k s) =
      (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).isoClassPresheaf.map k.unop.op
        ((twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g V.unop).symm s) := by
    rw [Equiv.symm_apply_eq, twoFibreProductIsoClassSectionEquiv_map, Equiv.apply_symm_apply]
    rfl
  exact (congrArg (PresheafOfCategories.isoClassSection eT V'.unop) hs).trans
    (PresheafOfCategories.isoClassSection_map eT k.unop _)

/-- The isomorphism of `AlgebraicGeometry.Stack.fibreProductIsoRepresenting` carries a section of
the fibre product to the section of `T` named by the isomorphism class it belongs to. -/
theorem fibreProductIsoRepresenting_hom_app (V : (BigFppfOver B S hS)ᵒᵖ)
    (s : (Presheaf.fibreProduct (representingMap B S hS 𝒳 𝒵 F H eF eH f)
      (representingMap B S hS 𝒴 𝒵 G H eG eH g)).obj V) :
    (fibreProductIsoRepresenting B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g T eT).hom.app V s =
      PresheafOfCategories.isoClassSection eT V.unop
        ((twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g V.unop).symm s) :=
  rfl

end Representing

end AlgebraicGeometry.Stack

end
