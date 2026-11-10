module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The pullback pseudofunctor of slice categories

For a category `C` with pullbacks, base change along `f : X ⟶ Y` is a functor
`CategoryTheory.Over.pullback f : Over Y ⥤ Over X`, and Mathlib supplies the two comparison
isomorphisms `CategoryTheory.Over.pullbackId` and `CategoryTheory.Over.pullbackComp` relating
it to the identity and to composition. It supplies no coherence between them, so the
assignment `X ↦ Over X`, `f ↦ Over.pullback f` is not available as a pseudofunctor. This file
proves the three missing coherences and assembles the pseudofunctor
`CategoryTheory.Over.pullbackPseudofunctor`.

The proof is the mate argument, and none of it is a computation with pullbacks. Both
`pullbackId` and `pullbackComp` are *defined* as `CategoryTheory.conjugateIsoEquiv` images of
`Over.mapId` and `Over.mapComp`, i.e. as the adjoint mates of the comparison isomorphisms for
post-composition `Over.map`, which is the strictly coherent side. Mathlib's
`CategoryTheory.conjugateEquiv_comp`, `conjugateEquiv_whiskerLeft`,
`conjugateEquiv_whiskerRight` and `conjugateEquiv_associator_hom` say that taking mates turns
a pasting of 2-cells into the mate of the reversed pasting, so each coherence collapses into a
single `conjugateEquiv` applied to the corresponding equation on the `Over.map` side, which
`ext` plus `simp` discharges because every component there is an identity.

Two lemmas are added on the way, because Mathlib's unitor transfer lemmas
`conjugateEquiv_leftUnitor_hom` and `conjugateEquiv_rightUnitor_hom` are stated for the `hom`
components only, while the pasting in a pseudofunctor's unitor axioms uses the `inv` component
on the right-adjoint side.

## Main definitions

* `CategoryTheory.Over.pullbackPseudofunctor`: the pseudofunctor
  `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` sending `X` to `Over X` and `f` to `Over.pullback f`.

## Main results

* `CategoryTheory.Over.pullbackComp_left_fst_fst`: `Over.pullbackComp` is compatible with the
  first projections;
* `CategoryTheory.Over.pullbackComp_assoc`: the associativity coherence (the pentagon) of
  `Over.pullbackComp`;
* `CategoryTheory.Over.pullbackComp_id_comp` and
  `CategoryTheory.Over.pullbackComp_comp_id`: its two unitor coherences against
  `Over.pullbackId`;
* `CategoryTheory.conjugateEquiv_leftUnitor_inv` and
  `CategoryTheory.conjugateEquiv_rightUnitor_inv`: the `inv` halves of Mathlib's unitor
  transfer lemmas.

## Implementation notes

The hypothesis is `Limits.HasPullbacks C` rather than the weaker `HasPullbacksAlong`. That is
deliberate and load-bearing: with `HasPullbacksAlong` the instance argument of `Over.pullback`
depends on the morphism, so an `eqToHom` along an equality of morphisms is not well typed and
`eqToIso` on `Over.pullback (f ≫ g) = Over.pullback h` fails with *motive is not type
correct* — the obstruction already met for `Stacks.Etale.pullbackSectionObjIso`. Under
`HasPullbacks` the instances are found uniformly
and the `eqToHom`s the pseudofunctor axioms are stated with elaborate without incident.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

section Mates

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- The `inv` half of `CategoryTheory.conjugateEquiv_rightUnitor_hom`: the mate of the inverse
right unitor of a left adjoint is the left unitor of its right adjoint. -/
lemma conjugateEquiv_rightUnitor_inv {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    conjugateEquiv (adj.comp Adjunction.id) adj (Functor.rightUnitor L).inv =
      (Functor.leftUnitor R).hom :=
  congrArg Iso.inv
    (Iso.ext (conjugateEquiv_rightUnitor_hom adj) :
      conjugateIsoEquiv adj (adj.comp Adjunction.id) (Functor.rightUnitor L) =
        (Functor.leftUnitor R).symm)

/-- The `inv` half of `CategoryTheory.conjugateEquiv_leftUnitor_hom`: the mate of the inverse
left unitor of a left adjoint is the right unitor of its right adjoint. -/
lemma conjugateEquiv_leftUnitor_inv {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    conjugateEquiv (Adjunction.id.comp adj) adj (Functor.leftUnitor L).inv =
      (Functor.rightUnitor R).hom :=
  congrArg Iso.inv
    (Iso.ext (conjugateEquiv_leftUnitor_hom adj) :
      conjugateIsoEquiv adj (Adjunction.id.comp adj) (Functor.leftUnitor L) =
        (Functor.rightUnitor R).symm)

end Mates

namespace Over

section Projections

variable {C : Type u₁} [Category.{v₁} C]

/-- **The comparison `CategoryTheory.Over.pullbackComp` is compatible with the first
projections.** Following it with the two first projections of the iterated pullback gives the
first projection of the pullback along the composite.

This is the counterpart for `CategoryTheory.Over.pullback` of Mathlib's
`CategoryTheory.MorphismProperty.Over.pullbackComp_left_fst_fst`. -/
lemma pullbackComp_left_fst_fst {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasPullbacksAlong f] [HasPullbacksAlong g] (A : Over Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫
        pullback.fst ((Over.pullback g).obj A).hom f ≫ pullback.fst A.hom g =
      pullback.fst A.hom (f ≫ g) := by
  simp [Over.mapComp, Over.pullbackComp]

end Projections

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]

/-- If a 2-cell between the post-composition functors `Over.map v` and `Over.map u` is the
identification of the two, then so is its mate on the `Over.pullback` side. -/
private lemma conjugateEquiv_eq_eqToHom {X Y : C} {u v : Y ⟶ X} (e : u = v)
    {m : Over.map v ⟶ Over.map u} (hm : m = eqToHom (by rw [e])) :
    conjugateEquiv (Over.mapPullbackAdj u) (Over.mapPullbackAdj v) m =
      eqToHom (by rw [e]) := by
  subst e hm
  simp

/-- The associativity coherence of `CategoryTheory.Over.pullbackComp`: the two ways of
comparing base change along `h ≫ g ≫ f` with the triple composite of base changes agree. -/
lemma pullbackComp_assoc {X Y Z T : C} (f : Y ⟶ X) (g : Z ⟶ Y) (h : T ⟶ Z) :
    (Over.pullbackComp h (g ≫ f)).hom ≫
        Functor.whiskerRight (Over.pullbackComp g f).hom (Over.pullback h) ≫
          (Functor.associator _ _ _).hom ≫
            Functor.whiskerLeft (Over.pullback f) (Over.pullbackComp h g).inv ≫
              (Over.pullbackComp (h ≫ g) f).inv = eqToHom (by simp) := by
  simp only [Over.pullbackComp, conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv,
    Iso.symm_hom, Iso.symm_inv]
  rw [← conjugateEquiv_whiskerLeft (Over.mapPullbackAdj (g ≫ f))
        ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj f)) (Over.mapPullbackAdj h),
    ← conjugateEquiv_whiskerRight ((Over.mapPullbackAdj h).comp (Over.mapPullbackAdj g))
        (Over.mapPullbackAdj (h ≫ g)) (Over.mapPullbackAdj f),
    ← conjugateEquiv_associator_hom (Over.mapPullbackAdj h) (Over.mapPullbackAdj g)
        (Over.mapPullbackAdj f)]
  simp only [conjugateEquiv_comp]
  exact conjugateEquiv_eq_eqToHom (by simp) (by ext W; simp)

/-- The left unitor coherence of `CategoryTheory.Over.pullbackComp`: comparing base change
along `f ≫ 𝟙` with base change along the identity followed by base change along `f` is the
identification of the two morphisms. -/
lemma pullbackComp_id_comp {X Y : C} (f : Y ⟶ X) :
    (Over.pullbackComp f (𝟙 X)).hom ≫
        Functor.whiskerRight (Over.pullbackId (X := X)).hom (Over.pullback f) ≫
          (Functor.leftUnitor (Over.pullback f)).hom = eqToHom (by simp) := by
  simp only [Over.pullbackComp, Over.pullbackId, conjugateIsoEquiv_apply_hom, Iso.symm_hom]
  rw [← conjugateEquiv_whiskerLeft (Over.mapPullbackAdj (𝟙 X)) Adjunction.id
        (Over.mapPullbackAdj f),
    ← conjugateEquiv_rightUnitor_inv (Over.mapPullbackAdj f)]
  simp only [conjugateEquiv_comp]
  exact conjugateEquiv_eq_eqToHom (by simp) (by ext W; simp)

/-- The right unitor coherence of `CategoryTheory.Over.pullbackComp`: comparing base change
along `𝟙 ≫ f` with base change along `f` followed by base change along the identity is the
identification of the two morphisms. -/
lemma pullbackComp_comp_id {X Y : C} (f : Y ⟶ X) :
    (Over.pullbackComp (𝟙 Y) f).hom ≫
        Functor.whiskerLeft (Over.pullback f) (Over.pullbackId (X := Y)).hom ≫
          (Functor.rightUnitor (Over.pullback f)).hom = eqToHom (by simp) := by
  simp only [Over.pullbackComp, Over.pullbackId, conjugateIsoEquiv_apply_hom, Iso.symm_hom]
  rw [← conjugateEquiv_whiskerRight (Over.mapPullbackAdj (𝟙 Y)) Adjunction.id
        (Over.mapPullbackAdj f),
    ← conjugateEquiv_leftUnitor_inv (Over.mapPullbackAdj f)]
  simp only [conjugateEquiv_comp]
  exact conjugateEquiv_eq_eqToHom (by simp) (by ext W; simp)

variable (C) in
/-- The pullback pseudofunctor of slice categories: it sends an object `X` of `C` to the slice
category `Over X` and a morphism `f : X ⟶ Y` to base change `Over.pullback f`, with the
comparison isomorphisms `Over.pullbackId` and `Over.pullbackComp`. Both the fibres and the
base-change functors are the given ones on the nose, not merely up to isomorphism. -/
noncomputable def pullbackPseudofunctor : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Over X.unop))
    (fun {_ _} φ ↦ (Over.pullback φ.unop).toCatHom)
    (fun _ ↦ Cat.Hom.isoMk Over.pullbackId)
    (fun {_ _ _} φ ψ ↦ Cat.Hom.isoMk (Over.pullbackComp ψ.unop φ.unop))
    (fun {_ _ _ _} φ ψ χ ↦ by
      ext1; simpa using! pullbackComp_assoc φ.unop ψ.unop χ.unop)
    (fun {_ _} φ ↦ by ext1; simpa using! pullbackComp_id_comp φ.unop)
    (fun {_ _} φ ↦ by ext1; simpa using! pullbackComp_comp_id φ.unop)

/-- The pullback pseudofunctor sends `X` to the slice category `Over X.unop`. -/
@[simp]
lemma pullbackPseudofunctor_obj (X : Cᵒᵖ) :
    (pullbackPseudofunctor C).obj (.mk X) = Cat.of (Over X.unop) :=
  rfl

/-- The pullback pseudofunctor sends `f.op` to the base-change functor `Over.pullback f`. -/
@[simp]
lemma pullbackPseudofunctor_map {X Y : C} (f : X ⟶ Y) :
    (pullbackPseudofunctor C).map f.op.toLoc = (Over.pullback f).toCatHom :=
  rfl

end Over

end CategoryTheory

end
