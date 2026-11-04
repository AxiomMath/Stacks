module

public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpace
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection

/-!
# Computing the morphism of representing presheaves on a named section (Stacks 04SW)

Let `𝒳` and `𝒴` be categories fibred in groupoids over the big fppf site of `S`, represented by
presheaves `F` and `G` through chosen equivalences over the site, and let `Φ : 𝒳 ⟶ 𝒴` be a
1-morphism over the site. The bijection of Stacks 04SW
(`AlgebraicGeometry.Stack.morphismSpaceEquiv`) turns `Φ` into a morphism `F ⟶ G` of presheaves.
This file computes its value: on the section of `F` named by an object `z` of `𝒳`
(`CategoryTheory.PresheafOfCategories.sectionOfObj`) it is the section of `G` named by `Φ z`.

Together with the four basic properties of naming a section, that is a complete recipe for the
induced morphism, and it is the form in which every identification of a morphism of algebraic
spaces with a presheaf-theoretic one is made.

## Main results

* `AlgebraicGeometry.Stack.morphismSpaceEquiv_app_sectionOfObj`: **Stacks 04SW**, the induced
  morphism of representing presheaves carries the section named by `z` to the section named by
  `Φ z`.
* `AlgebraicGeometry.Stack.natTrans_eq_of_forall_sectionOfObj`: two morphisms of the representing
  presheaves agreeing on every named section are equal — the uniqueness statement that identifies
  the induced morphism with a given one.

## Implementation notes

The proof reads `AlgebraicGeometry.Stack.morphismSpaceEquiv_map` as a statement about
isomorphism classes in the fibre over `W`: it says that the image of the canonical object of `F`
over `W` attached to a section `a`, pushed through `Φ`, is isomorphic in the fibre of `𝒴` over
`W` to the canonical object of `G` attached to the value of the induced morphism at `a`. Naming a
section is constant on such isomorphism classes
(`CategoryTheory.PresheafOfCategories.sectionOfObj_eq_of_fiberIso`), and the object naming `a` is
isomorphic in the fibre to the canonical one
(`CategoryTheory.PresheafOfCategories.fiberIsoOfSectionOfObj_eq`), so the two statements compose.
No unfolding of `AlgebraicGeometry.Stack.morphismSpaceEquiv` is needed, and in particular the
transparency option that `AlgebraicGeometry.Stack.morphismSpaceEquiv_map` needs is confined to
that declaration.

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
variable (eX : StacksRepresentableCFG.EquivalenceOver
    𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eY : StacksRepresentableCFG.EquivalenceOver
    𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)

/-- **Stacks 04SW.** The morphism `F ⟶ G` of representing presheaves induced by a 1-morphism `Φ`
over the site carries the section of `F` named by an object `z` of `𝒳` to the section of `G`
named by `Φ z`. -/
@[stacks 04SW "value of the induced morphism on a named section"]
theorem morphismSpaceEquiv_app_sectionOfObj
    (Φ : {H : 𝒳.val.obj ⥤ 𝒴.val.obj // H ⋙ 𝒴.val.p = 𝒳.val.p})
    (z : 𝒳.val.obj) {W : BigFppfOver B S hS} (h : 𝒳.val.p.obj z = W) :
    (morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ Φ)).app (op W)
        (PresheafOfCategories.sectionOfObj eX z h) =
      PresheafOfCategories.sectionOfObj eY (Φ.1.obj z) ((Functor.congr_obj Φ.2 z).trans h) := by
  have : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  have : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  set a := PresheafOfCategories.sectionOfObj eX z h
  set m := morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ Φ)
  -- the canonical object of `𝒳` over `W` attached to `a`, and the one of `𝒴` attached to `m a`
  set xa : 𝒳.val.obj := eX.inv.functor.obj ⟨W, Discrete.mk a⟩
  set ym : 𝒴.val.obj := eY.inv.functor.obj ⟨W, Discrete.mk (m.app (op W) a)⟩
  have hxaW : 𝒳.val.p.obj xa = W := Functor.congr_obj eX.inv.w _
  have hymW : 𝒴.val.p.obj ym = W := Functor.congr_obj eY.inv.w _
  -- `z` and `xa` name the same section of `F`, hence are isomorphic in the fibre over `W`
  have hname : PresheafOfCategories.sectionOfObj eX z h =
      PresheafOfCategories.sectionOfObj eX xa hxaW :=
    (PresheafOfCategories.sectionOfObj_inv_obj eX ⟨W, Discrete.mk a⟩).symm
  have izx : (Functor.Fiber.mk h : 𝒳.val.p.Fiber W) ≅ Functor.Fiber.mk hxaW :=
    PresheafOfCategories.fiberIsoOfSectionOfObj_eq eX h hxaW hname
  -- push that isomorphism through `Φ`
  have iyz : (Functor.Fiber.mk ((Functor.congr_obj Φ.2 z).trans h) : 𝒴.val.p.Fiber W) ≅
      Functor.Fiber.mk ((Functor.congr_obj Φ.2 xa).trans hxaW) :=
    (Functor.fiberFunctorOfCompEq Φ.2 W).mapIso izx
  -- the computation of Stacks 04SW, read as an equality of isomorphism classes
  have key := morphismSpaceEquiv_map B S hS 𝒳 𝒴 F G eX eY Φ W a
  rw [Functor.isoClassMap_app_isoClassMk] at key
  obtain ⟨ikey⟩ := Functor.exists_iso_of_isoClassMk_eq key
  refine Eq.symm ?_
  calc PresheafOfCategories.sectionOfObj eY (Φ.1.obj z) ((Functor.congr_obj Φ.2 z).trans h)
      = PresheafOfCategories.sectionOfObj eY ym hymW :=
        PresheafOfCategories.sectionOfObj_eq_of_fiberIso eY _ hymW (iyz ≪≫ ikey)
    _ = m.app (op W) a :=
        PresheafOfCategories.sectionOfObj_inv_obj eY _

/-- Two morphisms of the representing presheaves which agree on every section named by an object
are equal: every section is named by some object. -/
theorem natTrans_eq_of_forall_sectionOfObj (α β : F ⟶ G)
    (hαβ : ∀ (z : 𝒳.val.obj) (W : BigFppfOver B S hS) (h : 𝒳.val.p.obj z = W),
      α.app (op W) (PresheafOfCategories.sectionOfObj eX z h) =
        β.app (op W) (PresheafOfCategories.sectionOfObj eX z h)) :
    α = β := by
  ext W s
  obtain ⟨z, h, hz⟩ := PresheafOfCategories.exists_sectionOfObj eX (W := W.unop) s
  rw [← hz]
  exact hαβ z W.unop h

end AlgebraicGeometry.Stack

end
