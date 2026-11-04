module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory

/-!
# Morphisms between categories represented by algebraic spaces (Stacks 04SW)

Let `𝒳` and `𝒴` be categories fibred in groupoids over the big fppf site of `S` which are
represented by presheaves `F` and `G` — for instance by algebraic spaces over `S`. Then
1-morphisms `𝒳 ⟶ 𝒴` over the site, taken modulo 2-isomorphism, are exactly the morphisms
`F ⟶ G` of presheaves, and the 2-isomorphism identifying two 1-morphisms with the same image is
itself unique.

## Main definitions

* `AlgebraicGeometry.Stack.morphismSpaceEquiv`: **Stacks 04SW**, the bijection between
  1-morphisms modulo 2-isomorphism and morphisms of the representing presheaves.

## Main results

* `AlgebraicGeometry.Stack.morphismSpaceEquiv_map`: **Stacks 04SW**, the bijection is the map
  induced on isomorphism classes of objects in each fibre.
* `AlgebraicGeometry.Stack.existsUnique_twoIso_of_morphismSpaceEquiv_eq`: **Stacks 04SW**, two
  1-morphisms with the same image admit a unique 2-isomorphism over the site.

## Implementation notes

The equivalences exhibiting the two fibred categories as categories of elements are explicit
parameters: identifying a particular category with a particular presheaf requires that choice.
The quotient is by 2-isomorphisms over the site
(`CategoryTheory.Functor.twoIsoSetoid`).

The proof is the identification, in two steps, of `Mor(𝒳, 𝒴)/≅` with `Mor(F, G)`. Stacks 04SD
(`CategoryTheory.Functor.isoClassMapEquiv`) identifies it with morphisms of the presheaves of
isomorphism classes of fibres, since both categories are fibred in setoids — which they are,
being equivalent over the site to categories of elements of presheaves of sets
(`CategoryTheory.PresheafOfCategories.isFiberedInSetoids_discreteProjection`). Then
`CategoryTheory.PresheafOfCategories.isoClassEquiv` identifies those two presheaves of
isomorphism classes with `F` and `G`, pointwise and compatibly with restriction, and
`CategoryTheory.natTransEquivOfPointwiseEquiv` turns that into a bijection of morphisms; it is
stated pointwise rather than as an isomorphism of presheaves because the presheaf of isomorphism
classes does not land in the universe of `F`.

The statement is for arbitrary presheaves of sets, the algebraic-space case being its
specialization: nothing in the argument uses algebraicity, only that `𝒳` and `𝒴` are fibred in
groupoids and equivalent over the site to categories of elements. The universe of the total
categories of `𝒳` and `𝒴` is therefore free of that of `F` and `G`.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, w} (BigFppfOver B S hS))
variable (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 04SW.** One-morphisms of categories fibred in groupoids represented by `F` and `G`,
modulo two-isomorphism, are morphisms `F ⟶ G` of the representing presheaves. -/
@[stacks 04SW "equivalence of morphism spaces"]
noncomputable def morphismSpaceEquiv
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    Quotient (Functor.twoIsoSetoid 𝒳.val.p 𝒴.val.p) ≃ (F ⟶ G) := by
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI : 𝒳.val.p.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eX
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection F)
  letI : 𝒴.val.p.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eY
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection G)
  let eHom := natTransEquivOfPointwiseEquiv
    𝒳.val.p.isoClassPresheaf 𝒴.val.p.isoClassPresheaf F G
    (fun U => PresheafOfCategories.isoClassEquiv F eX U.unop)
    (fun U => PresheafOfCategories.isoClassEquiv G eY U.unop)
    (by
      intro U V f c
      simpa using PresheafOfCategories.isoClassEquiv_naturality 𝒳.2 F eX f.unop c)
    (by
      intro U V f c
      simpa using PresheafOfCategories.isoClassEquiv_naturality 𝒴.2 G eY f.unop c)
  exact (Functor.isoClassMapEquiv 𝒳.val.p 𝒴.val.p).trans eHom

-- Reading off the value of `AlgebraicGeometry.Stack.morphismSpaceEquiv` means unfolding it past
-- `CategoryTheory.Functor.isoClassMapEquiv`, whose `toFun` is a `Quotient.lift`. Unfolding it
-- with `dsimp` exposes the `Equiv` structure instance, whose `autoParam` fields leave the goal
-- not type-correct at `implicit` transparency, after which the rewrite by
-- `CategoryTheory.Functor.isoClassMap_app_isoClassMk` can no longer key-match. The step is
-- therefore named below as `hstep` and proved by `rfl`, which does the same unfolding at default
-- transparency and hands back a goal stated in the library's own vocabulary.
/-- **Stacks 04SW.** On every fibre, the forward direction of
`AlgebraicGeometry.Stack.morphismSpaceEquiv` is the map induced by the given one-morphism on
isomorphism classes of objects. -/
@[stacks 04SW "induced map on fibre isomorphism classes"]
theorem morphismSpaceEquiv_map
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : {H : 𝒳.val.obj ⥤ 𝒴.val.obj // H ⋙ 𝒴.val.p = 𝒳.val.p})
    (U : BigFppfOver B S hS) (a : F.obj (op U)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    ((Functor.isoClassMap
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.2 f.2)).app (op U))
      (Functor.isoClassMk 𝒳.val.p
        ((Functor.fiberFunctorOfCompEq eX.inv.w U).obj
          (⟨⟨U, Discrete.mk a⟩, rfl⟩ :
            (presheafOfCategories (F ⋙ typeToCat)).p.Fiber U))) =
    Functor.isoClassMk 𝒴.val.p
      ((Functor.fiberFunctorOfCompEq eY.inv.w U).obj
        (⟨⟨U, Discrete.mk
          ((morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ f)).app
            (op U) a)⟩, rfl⟩ :
          (presheafOfCategories (G ⋙ typeToCat)).p.Fiber U)) := by
  have : 𝒳.val.p.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eX
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection F)
  have : 𝒴.val.p.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eY
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection G)
  have hXclass : (PresheafOfCategories.isoClassEquiv F eX U).symm a =
      Functor.isoClassMk 𝒳.val.p
        ((Functor.fiberFunctorOfCompEq eX.inv.w U).obj
          (⟨⟨U, Discrete.mk a⟩, rfl⟩ :
            (presheafOfCategories (F ⋙ typeToCat)).p.Fiber U)) :=
    rfl
  let xF : (presheafOfCategories (F ⋙ typeToCat)).p.Fiber U := ⟨⟨U, Discrete.mk a⟩, rfl⟩
  let x := (Functor.fiberFunctorOfCompEq eX.inv.w U).obj xF
  let f' := Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.2 f.2
  let y := (Functor.fiberFunctorOfCompEq f'.comp_eq U).obj x
  let yF : (presheafOfCategories (G ⋙ typeToCat)).p.Fiber U :=
    ⟨⟨U, Discrete.mk
      ((morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ f)).app (op U) a)⟩, rfl⟩
  have hvalue :
      (morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ f)).app (op U) a =
        PresheafOfCategories.discreteFiberEquiv G U
          ((Functor.fiberFunctorOfCompEq eY.hom.w U).obj y) := by
    have hstep : (morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ f)).app (op U) a =
        PresheafOfCategories.isoClassEquiv G eY U
          ((Functor.isoClassMapOfCompEq f.2).app (op U)
            ((PresheafOfCategories.isoClassEquiv F eX U).symm a)) := rfl
    rw [hstep, hXclass, Functor.isoClassMap_app_isoClassMk]
    rfl
  have hyF : (Functor.fiberFunctorOfCompEq eY.hom.w U).obj y = yF :=
    (PresheafOfCategories.discreteFiberEquiv G U).injective hvalue.symm
  have hyIso : y ≅ (Functor.fiberFunctorOfCompEq eY.inv.w U).obj yF := by
    have hu := eY.isHomLift_unitIso_hom_app y.1
    have huU : 𝒴.val.p.IsHomLift (𝟙 U) (eY.unitIso.hom.app y.1) := by rwa [y.2] at hu
    let huIso : y.1 ≅ eY.inv.functor.obj (eY.hom.functor.obj y.1) :=
      asIso (eY.unitIso.hom.app y.1)
    have huIsoLift : 𝒴.val.p.IsHomLift (𝟙 U) huIso.hom := by
      simpa [huIso, asIso_hom] using huU
    exact (Functor.Fiber.isoMk huIso huIsoLift) ≪≫
      (Functor.fiberFunctorOfCompEq eY.inv.w U).mapIso (eqToIso hyF)
  show Functor.isoClassMk 𝒴.val.p y =
    Functor.isoClassMk 𝒴.val.p ((Functor.fiberFunctorOfCompEq eY.inv.w U).obj yF)
  exact Functor.isoClassMk_eq_of_iso hyIso

/-- **Stacks 04SW.** Two one-morphisms inducing the same morphism of representing presheaves
admit a unique two-isomorphism over the site. -/
@[stacks 04SW "uniqueness up to unique two-isomorphism"]
theorem existsUnique_twoIso_of_morphismSpaceEquiv_eq
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f g : {H : 𝒳.val.obj ⥤ 𝒴.val.obj // H ⋙ 𝒴.val.p = 𝒳.val.p})
    (h : morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ f) =
      morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ g)) :
    ∃! α : f.1 ≅ g.1,
      ∀ x : 𝒳.val.obj, 𝒴.val.p.IsHomLift (𝟙 (𝒳.val.p.obj x)) (α.hom.app x) := by
  have : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  have : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  have : 𝒳.val.p.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eX
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection F)
  have : 𝒴.val.p.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eY
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection G)
  exact Functor.existsUnique_twoIso_of_isoClassMap_eq f.2 g.2
    (Functor.isoClassMapOfCompEq_eq_of_twoIso 𝒳.val.p 𝒴.val.p
      (Quotient.exact ((morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY).injective h)))

end AlgebraicGeometry.Stack

end
