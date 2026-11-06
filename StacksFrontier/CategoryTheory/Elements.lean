module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import StacksCore.Tactic.StacksAttribute

/-!
# The slice category as the category of elements of a representable presheaf

Let `C` be a category and `X : C`. This file identifies the slice category `C/X` with the
category `S_{h_X}` attached to the representable presheaf `h_X = Mor_C(-, X)` under the
correspondence between presheaves on `C` and categories fibred in sets over `C`.

For a presheaf `F : Cᵒᵖ ⥤ Type v`, the category `S_F` of the source has objects the pairs
`(U, x)` with `x ∈ F(U)` and morphisms `(V, y) ⟶ (U, x)` the maps `f : V ⟶ U` of `C` with
`f^* x = y`. Mathlib's `CategoryTheory.Functor.Elements F` has the same objects but the
opposite morphisms, so `S_F` is `(F.Elements)ᵒᵖ`, and its structure functor to `C` is
`(Functor.Elements.π F).leftOp`.

## Main results

* `CategoryTheory.overEquivElementsOp`: the equivalence `C/X ≌ S_{h_X}`.
* `CategoryTheory.overEquivElementsOpForget`: that equivalence is an equivalence *over* `C`,
  i.e. it commutes with the two structure functors to `C`.
* `CategoryTheory.Over.eq_of_hom_left_id` and `CategoryTheory.Over.hom_eq_id_of_left_id`:
  the fibre category of `C/X → C` over `U` has the morphisms `h : U ⟶ X` as objects and
  only identities as morphisms.
* `CategoryTheory.elementsUliftEquiv`: raising the universe of a presheaf does not change its
  category of elements. This is the one place where the universe lift is handled, and it is an
  isomorphism of categories: both round trips are the identity on the nose.
* `CategoryTheory.CategoryOfElements.exists_opOverEquivalenceElements`: the same identification
  in the form [Stacks, Tag 0178] words it, for the universe-lifted presheaf `uliftYoneda.obj X`
  and with the opposite taken on the slice category rather than on the elements. Deduced from
  `CategoryTheory.overEquivElementsOp` and `CategoryTheory.elementsUliftEquiv`, not proved a
  second time; taking `C = Δ` and `X = ⦋n⦌` it says that `Δ/⦋n⦌`, fibred in sets over `Δ`, is
  the simplicial set `Δ[n]`.

## Implementation notes

Tags 0044 and 0178 are the same mathematics in two shapes, and only the shapes differ: 0044
speaks of `yoneda`, whose values lie in `Type v`, while 0178 needs `uliftYoneda`, because the
simplicial set `Δ[n] : SSet.{u}` it specialises to takes values in `Type u`; and the two put
the `ᵒᵖ` on opposite sides. Neither form is definitionally an instance of the other, so one
bridge is unavoidable — but exactly one is, and it is `elementsUliftEquiv`. The comparison
functors themselves are defined once, for `yoneda`, and 0178's equivalence is obtained from
them by `Equivalence.op`, `opOpEquivalence` and that bridge. Because every step is definitional,
0178's two pinning clauses — which fix the functor's value on every object and its composite
with the projection — remain true by `rfl`, so nothing is weakened by the detour.
-/

@[expose] public section

universe w v u

open Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (X : C)

/-- The comparison functor `C/X ⥤ S_{h_X}`, sending an object `h : Y ⟶ X` of the slice
category to the element `h ∈ h_X(Y)`. -/
def overToElementsOp : Over X ⥤ ((yoneda.obj X).Elements)ᵒᵖ where
  obj A := op ((yoneda.obj X).elementsMk (op A.left) A.hom)
  map {A B} f :=
    Quiver.Hom.op
      (⟨f.left.op, Over.w f⟩ :
        ((yoneda.obj X).elementsMk (op B.left) B.hom) ⟶
          ((yoneda.obj X).elementsMk (op A.left) A.hom))

/-- The inverse comparison functor `S_{h_X} ⥤ C/X`, sending an element `x ∈ h_X(U)`, i.e. a
morphism `U ⟶ X`, to the corresponding object of the slice category. -/
def elementsOpToOver : ((yoneda.obj X).Elements)ᵒᵖ ⥤ Over X where
  obj p := Over.mk p.unop.2
  map {p q} f := Over.homMk f.unop.1.unop f.unop.2

/-- The two comparison functors are mutually inverse on the nose: an object of `C/X` *is* a
pair `(Y, h : Y ⟶ X)`, and a morphism of `C/X` *is* a morphism of `C` over `X`. -/
theorem overToElementsOp_comp_elementsOpToOver :
    overToElementsOp X ⋙ elementsOpToOver X = 𝟭 (Over X) := rfl

/-- The two comparison functors are mutually inverse on the nose; see
`CategoryTheory.overToElementsOp_comp_elementsOpToOver`. -/
theorem elementsOpToOver_comp_overToElementsOp :
    elementsOpToOver X ⋙ overToElementsOp X = 𝟭 ((yoneda.obj X).Elements)ᵒᵖ := rfl

/-- **`C/X` is the category of elements of `h_X`.** The slice category `C/X` is equivalent to
the category `S_{h_X} = ((h_X).Elements)ᵒᵖ` attached to the representable presheaf
`h_X = Mor_C(-, X)`.

Both round trips are the identity functor on the nose, so the unit and counit are
identities. -/
@[stacks 0044]
def overEquivElementsOp : Over X ≌ ((yoneda.obj X).Elements)ᵒᵖ where
  functor := overToElementsOp X
  inverse := elementsOpToOver X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun {A B} f => by
    change f ≫ 𝟙 B = 𝟙 A ≫ f
    rw [Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun {A B} f => by
    change f ≫ 𝟙 B = 𝟙 A ≫ f
    rw [Category.comp_id, Category.id_comp])
  functor_unitIso_comp := fun A => by
    change (overToElementsOp X).map (𝟙 A) ≫ 𝟙 _ = 𝟙 _
    rw [Functor.map_id, Category.comp_id]

/-- **The equivalence of `overEquivElementsOp` is an equivalence over `C`.** It carries the
structure functor `C/X → C` to the structure functor `S_{h_X} → C`, which is
`(Functor.Elements.π h_X).leftOp`. This is the sense in which `C/X` is *canonically
equivalent over `C`* to `S_{h_X}`. -/
@[stacks 0044]
def overEquivElementsOpForget :
    (overEquivElementsOp X).functor ⋙ (Functor.Elements.π (yoneda.obj X)).leftOp
      ≅ Over.forget X :=
  Iso.refl _

/-- The quasi-inverse is a functor over `C` as well. (Not part of the covering set for
Stacks 0044: `CategoryTheory.overEquivElementsOpForget` already states the compatibility.) -/
def elementsOpToOverForget :
    (overEquivElementsOp X).inverse ⋙ Over.forget X
      ≅ (Functor.Elements.π (yoneda.obj X)).leftOp :=
  Iso.refl _

section UniverseLift

variable {X}

/-- The comparison functor of `CategoryTheory.elementsUliftEquiv`: an element of the
universe-lifted presheaf `F ⋙ uliftFunctor` is an element of `F`. -/
def elementsUliftEquivFunctor (F : Cᵒᵖ ⥤ Type v) :
    (F ⋙ uliftFunctor.{w}).Elements ⥤ F.Elements where
  obj x := F.elementsMk x.obj x.val.down
  map f := Functor.Elements.homMk f.hom (congrArg ULift.down f.map_val)

/-- The inverse comparison functor of `CategoryTheory.elementsUliftEquiv`. -/
def elementsUliftEquivInverse (F : Cᵒᵖ ⥤ Type v) :
    F.Elements ⥤ (F ⋙ uliftFunctor.{w}).Elements where
  obj x := (F ⋙ uliftFunctor.{w}).elementsMk x.obj (ULift.up x.val)
  map f := Functor.Elements.homMk f.hom (congrArg ULift.up f.map_val)

/-- **Raising the universe of a presheaf does not change its category of elements.** An element
of `(F ⋙ uliftFunctor)(U)` is a `ULift` of an element of `F(U)`, and a morphism of elements is
its underlying morphism either way, so the two categories are isomorphic: both round trips are
the identity functor on the nose.

This is the only bridge between the `yoneda` form of the slice-category identification
(`CategoryTheory.overEquivElementsOp`, [Stacks, Tag 0044]) and the `uliftYoneda` form that
[Stacks, Tag 0178] needs. Mathlib has `CategoryTheory.uliftYoneda` but no such comparison for
`Functor.Elements`; it is worth upstreaming. -/
def elementsUliftEquiv (F : Cᵒᵖ ⥤ Type v) :
    (F ⋙ uliftFunctor.{w}).Elements ≌ F.Elements :=
  CategoryTheory.Equivalence.mk (elementsUliftEquivFunctor.{w} F)
    (elementsUliftEquivInverse.{w} F) (eqToIso rfl) (eqToIso rfl)

end UniverseLift

namespace CategoryOfElements

/-- **`C/X` is fibred in sets over `C`, and as a presheaf of sets it is represented by `X`.**
There is an equivalence of categories from the opposite of the category `C/X` of objects of
`C` over `X` to the category of elements of the presheaf `uliftYoneda.obj X` represented by
`X`, which sends an object `ψ : Y ⟶ X` of `C/X` to the element `ψ` of `Mor_C(Y, X)`, and which
commutes with the projections to `Cᵒᵖ`. For `C` the simplex category and `X = ⦋n⦌` this says
that `Δ/⦋n⦌`, fibred in sets over `Δ`, is the simplicial set `Δ[n]`.

This is `CategoryTheory.overEquivElementsOp` ([Stacks, Tag 0044]) transported along
`CategoryTheory.elementsUliftEquiv`; the two pinning clauses hold by `rfl` because every step
of the transport is definitional. -/
@[stacks 0178 "stated for an arbitrary category C and X : C, of which Δ/⦋n⦌ fibred in sets \
  over Δ being the presheaf Δ[n] is the case C = Δ, X = ⦋n⦌, since SSet.stdSimplex is \
  uliftYoneda; the formula Mor(Δ/⦋n⦌, U) = U_n is then SSet.yonedaEquiv",
  sga "4 IV 6.3" "special case"]
theorem exists_opOverEquivalenceElements (X : C) :
    ∃ e : (Over X)ᵒᵖ ≌ (uliftYoneda.{w}.obj X).Elements,
      (∀ ψ : Over X, e.functor.obj (op ψ) =
        (uliftYoneda.{w}.obj X).elementsMk (op ψ.left) (ULift.up ψ.hom)) ∧
      e.functor ⋙ Functor.Elements.π _ = (Over.forget X).op :=
  ⟨(overEquivElementsOp X).op.trans
    ((opOpEquivalence _).trans (elementsUliftEquiv.{w} (yoneda.obj X)).symm),
   fun _ => rfl, rfl⟩

/-! ### Precomposing the indexing functor, and smallness of the category of elements -/

section PreComp

universe w' v' u'

variable {D : Type u'} [Category.{v'} D]

/-- **Precomposition on the base, read on categories of elements.**  A functor `G : D ⥤ C` and a
functor `F : C ⥤ Type w` give a functor `(G ⋙ F).Elements ⥤ F.Elements`, which is `G` on the
base object and the identity on the element: an element of `(G ⋙ F)(Y)` *is* an element of
`F(G(Y))`. -/
@[simps]
def preComp (G : D ⥤ C) (F : C ⥤ Type w) :
    (G ⋙ F).Elements ⥤ F.Elements where
  obj a := F.elementsMk (G.obj a.obj) a.val
  map {_ _} f := Functor.Elements.homMk (G.map f.hom) f.map_val
  map_id _ := Functor.Elements.hom_ext (G.map_id _)
  map_comp _ _ := Functor.Elements.hom_ext (G.map_comp _ _)

/-- If `G` is faithful, then `preComp G F` is faithful. -/
instance faithful_preComp (G : D ⥤ C) [G.Faithful] (F : C ⥤ Type w) :
    (preComp G F).Faithful where
  map_injective h := Functor.Elements.hom_ext (G.map_injective (congrArg Functor.Elements.Hom.hom h))

/-- If `G` is full, then `preComp G F` is full. -/
instance full_preComp (G : D ⥤ C) [G.Full] (F : C ⥤ Type w) :
    (preComp G F).Full where
  map_surjective {x y} h :=
    have e : G.map (G.preimage h.hom) = h.hom := G.map_preimage (X := x.obj) (Y := y.obj) h.hom
    ⟨Functor.Elements.homMk (G.preimage h.hom) (by
        change F.map (G.map (G.preimage h.hom)) x.val = y.val
        rw [e]
        exact h.map_val),
      Functor.Elements.hom_ext e⟩

/-- If `G` is essentially surjective, then `preComp G F` is essentially surjective. -/
instance essSurj_preComp (G : D ⥤ C) [G.EssSurj] (F : C ⥤ Type w) :
    (preComp G F).EssSurj where
  mem_essImage a :=
    ⟨(G ⋙ F).elementsMk (G.objPreimage a.obj) (F.map (G.objObjPreimageIso a.obj).inv a.val),
      ⟨Functor.Elements.isoMk (G.objObjPreimageIso a.obj) (by
        change F.map (G.objObjPreimageIso a.obj).hom
          (F.map (G.objObjPreimageIso a.obj).inv a.val) = a.val
        rw [Functor.map_inv_hom'_apply])⟩⟩

/-- If `G` is an equivalence, then `preComp G F` is an equivalence. -/
instance isEquivalence_preComp (G : D ⥤ C) [G.IsEquivalence]
    (F : C ⥤ Type w) : (preComp G F).IsEquivalence where

/-- **The category of elements of a `Type w`-valued functor on an essentially `w`-small category
is initially `w`-small.**

This is the smallness side condition that the reconstruction of a point of a site from a point of
its topos (Stacks 00YA (2)) needs, and it is the reason that reconstruction is available at the
coefficient universe of the *morphisms* of a site and not only at that of its objects: the small
étale site of a scheme has objects in `Type (u + 1)` and morphisms in `Type u`, so it is
`EssentiallySmall.{u}` but **not** `Small.{u}`, and a hypothesis of `Small.{u}` restricts every
consumer to coefficients `Type (u + 1)`.

The proof replaces `C` by a small model: the category of elements of the restricted functor has
`Σ Y : SmallModel C, F.obj (G.obj Y)` as its type of objects, which is `w`-small, and
`CategoryTheory.CategoryOfElements.preComp` along the equivalence is an equivalence, hence
initial. -/
theorem initiallySmall_elements_of_essentiallySmall
    [EssentiallySmall.{w} C] (F : C ⥤ Type w) : InitiallySmall.{w} F.Elements :=
  let G := (equivSmallModel.{w} C).inverse
  have : Small.{w} (G ⋙ F).Elements :=
    small_of_surjective.{w} (α := Σ Y : SmallModel.{w} C, F.obj (G.obj Y))
      (f := fun x ↦ (G ⋙ F).elementsMk x.1 x.2) (fun x ↦ ⟨⟨x.obj, x.val⟩, rfl⟩)
  have : EssentiallySmall.{w} (G ⋙ F).Elements :=
    essentiallySmall_of_small_of_locallySmall _
  initiallySmall_of_initial_of_essentiallySmall (preComp G F)

end PreComp

end CategoryOfElements

namespace Over

variable {X}

/-- **The fibre categories of `C/X → C` have only identities (existence part).** If there is
a morphism `Over.mk f ⟶ Over.mk g` of `C/X` lying over the identity of `U`, then `f = g`. -/
@[stacks 0044]
theorem eq_of_hom_left_id {U : C} {f g : U ⟶ X} (φ : Over.mk f ⟶ Over.mk g)
    (hφ : φ.left = 𝟙 U) : f = g := by
  simpa [hφ] using (Over.w φ).symm

/-- **The fibre categories of `C/X → C` have only identities (uniqueness part).** A morphism
of `C/X` from an object to itself lying over the identity is the identity. Together with
`CategoryTheory.Over.eq_of_hom_left_id` this says that the fibre category of `C/X → C` over
`U` has the morphisms `h : U ⟶ X` as objects and only identities as morphisms. -/
@[stacks 0044]
theorem hom_eq_id_of_left_id {U : C} {f : U ⟶ X} (φ : Over.mk f ⟶ Over.mk f)
    (hφ : φ.left = 𝟙 U) : φ = 𝟙 (Over.mk f) :=
  Over.OverMorphism.ext (by simpa using hφ)

end Over

end CategoryTheory
