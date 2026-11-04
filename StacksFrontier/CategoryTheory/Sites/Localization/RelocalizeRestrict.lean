module

public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# Relocalization turns restriction into base change along a representable morphism

Let `C` be a category, let `a : A ⟶ X` be a morphism of `C` and let `m : B ⟶ A` be a morphism
over `A`. Relocalization `Λ_a = CategoryTheory.OverShriek.relocalizePresheafFunctor a` carries a
presheaf `F` on `C/A` to a presheaf on `C/X` *over* the representable presheaf of `A ⟶ X`, the
structural morphism reading off the factorization through `A`
(`CategoryTheory.OverShriek.relocalizeToYoneda`).

This file proves that the square

```
  Λ_{m ≫ a} (F|_B) ⟶ Λ_a F
        |               |
        v               v
    h_{m ≫ a}    ⟶     h_a
```

is a pullback of presheaves on `C/X`: relocalizing the restriction of `F` to `C/B` is the base
change of `Λ_a F` along the representable morphism `h_{m ≫ a} ⟶ h_a`. Equivalently, an algebraic
space over `A` restricted to `B` is, after being viewed over `X`, the fibre product of the
original over `A` with `B`.

That is the step a locality argument needs: a property of morphisms local on the target is
tested on the base change of the structural morphism of `Λ_a F` to a covering of `h_a`, and when
the covering consists of representables its members are exactly the restrictions of `F`.

## Main definitions

* `CategoryTheory.OverShriek.relocalizeMk`: a section of `Λ_a F` over `W`, namely a
  factorization of the structure morphism of `W` through `A` together with a section of `F`.
* `CategoryTheory.OverShriek.relocalizeToYoneda`: the structural morphism
  `Λ_a F ⟶ h_{(A ⟶ X)}`, which reads off the factorization.
* `CategoryTheory.OverShriek.relocalizeRestrictMap`: the comparison
  `Λ_{m ≫ a} (F|_B) ⟶ Λ_a F`.

## Main results

* `CategoryTheory.OverShriek.isPullback_relocalizeRestrictMap`: the square above is a pullback.
* `CategoryTheory.OverShriek.subsingleton_of_injective_relocalizeToYoneda`: if the structural
  morphism of `Λ_a F` is injective in each degree then `F` has at most one section over every
  object of `C/A`.

## Implementation notes

A section of `Λ_a F` over `W : C/X` is a pair `(ψ, s)` with `ψ : W.left ⟶ A` and
`s ∈ F(W.left →ψ A)`, subject to `ψ ≫ a = W.hom`; that description is definitional, which is
what `CategoryTheory.OverShriek.relocalizeMk` and
`CategoryTheory.OverShriek.relocalizeFactors` record, and it is why all three constructions here
are given by explicit formulas. The comparison sends `(ψ, s)` with `ψ : W.left ⟶ B` to
`(ψ ≫ m, s)`: a section of `F|_B` over `W.left →ψ B` *is* a section of `F` over
`W.left →ψ ≫ m A`.

The pullback property is proved pointwise with
`CategoryTheory.IsPullback.of_forall_isPullback_app` and then
`CategoryTheory.Limits.Types.isPullback_iff`, whose three clauses are, concretely: the square
commutes because both composites read off `ψ ≫ m`; it is jointly injective because the
factorization is determined by the lower-left corner and the section by the upper-right one; and
it is jointly surjective because a section `(ψ', s')` of `Λ_a F` whose factorization is
prescribed to be `h.left ≫ m` is the image of `(h.left, s')`.

Naturality of the comparison is the only computation with content, and it is
`CategoryTheory.OverShriek.sigmaMk_eq`: the two sides restrict the same section of `F` along two
morphisms of `C/A` with the same underlying morphism of `C`, whose sources differ by
associativity.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

namespace CategoryTheory.OverShriek

universe v u

variable {C : Type u} [Category.{v} C] {X A A' : C} (a : A ⟶ X) (m : A' ⟶ A)
  (F : (Over A)ᵒᵖ ⥤ Type v)

/-- A section of the relocalization `Λ_a F` over `W : C/X`: a factorization `ψ : W.left ⟶ A` of
the structure morphism of `W`, together with a section of `F` over `W.left →ψ A`. -/
def relocalizeMk {W : (Over X)ᵒᵖ} (ψ : (unop W).left ⟶ A) (s : F.obj (op (Over.mk ψ)))
    (h : ψ ≫ a = (unop W).hom) : ((relocalizePresheafFunctor a).obj F).obj W :=
  ⟨⟨ψ, s⟩, h⟩

/-- The factorization carried by a section of `Λ_a F` over `W` does factor the structure
morphism of `W`. -/
theorem relocalizeFactors {W : (Over X)ᵒᵖ} (x : ((relocalizePresheafFunctor a).obj F).obj W) :
    x.1.1 ≫ a = (unop W).hom :=
  x.2

/-- Restriction in `Λ_a F` is restriction in the coproduct presheaf of Stacks 03CD. -/
theorem relocalize_map_fst {W W' : (Over X)ᵒᵖ} (g : W ⟶ W')
    (x : ((relocalizePresheafFunctor a).obj F).obj W) :
    (((relocalizePresheafFunctor a).obj F).map g x).1 =
      (OverShriek.presheaf F).map (g.unop.left).op x.1 :=
  rfl

/-- The structural morphism `Λ_a F ⟶ h_{(A ⟶ X)}` of the relocalization of a presheaf on `C/A`:
it sends a section to the factorization through `A` that the section carries. This is the
morphism to the representable presheaf that Stacks 04SG equips the image of `F` with. -/
def relocalizeToYoneda : (relocalizePresheafFunctor a).obj F ⟶ yoneda.obj (Over.mk a) where
  app W := ↾fun x => Over.homMk x.1.1 x.2
  naturality _ _ _ := by
    ext x
    exact Over.OverMorphism.ext rfl

/-- The structural morphism `Λ_a F ⟶ h_{(A ⟶ X)}` sends a section of `Λ_a F` to the morphism
of `C/X` given by the factorization through `A` that the section carries. -/
@[simp]
theorem relocalizeToYoneda_app_apply {W : (Over X)ᵒᵖ}
    (x : ((relocalizePresheafFunctor a).obj F).obj W) :
    (relocalizeToYoneda a F).app W x = Over.homMk x.1.1 x.2 :=
  rfl

/-- The comparison `Λ_{m ≫ a} (F|_{C/A'}) ⟶ Λ_a F`: a section of the restriction of `F` over
`W.left →ψ A'` *is* a section of `F` over `W.left →ψ ≫ m A`, and the factorization through `A'`
becomes the factorization `ψ ≫ m` through `A`. -/
def relocalizeRestrictMap :
    (relocalizePresheafFunctor (m ≫ a)).obj ((relocalizeRestrict m).obj F) ⟶
      (relocalizePresheafFunctor a).obj F where
  app W := ↾fun x => relocalizeMk a F (x.1.1 ≫ m) x.1.2
    ((Category.assoc _ _ _).trans (relocalizeFactors (m ≫ a) _ x))
  naturality W W' g := by
    ext x
    exact Subtype.ext (sigmaMk_eq F x.1.2
      (Over.homMk g.unop.left (Category.assoc _ _ _).symm :
        Over.mk ((g.unop.left ≫ x.1.1) ≫ m) ⟶ Over.mk (x.1.1 ≫ m))
      (Over.homMk g.unop.left rfl :
        Over.mk (g.unop.left ≫ (x.1.1 ≫ m)) ⟶ Over.mk (x.1.1 ≫ m)) rfl)

/-- The comparison `Λ_{m ≫ a} (F|_{C/A'}) ⟶ Λ_a F` sends a section with factorization `ψ` through
`A'` to the same section of `F`, now with factorization `ψ ≫ m` through `A`. -/
@[simp]
theorem relocalizeRestrictMap_app_apply_fst {W : (Over X)ᵒᵖ}
    (x : ((relocalizePresheafFunctor (m ≫ a)).obj ((relocalizeRestrict m).obj F)).obj W) :
    ((relocalizeRestrictMap a m F).app W x).1 = ⟨x.1.1 ≫ m, x.1.2⟩ :=
  rfl

/-- Two sections of `Λ_a F` with the same factorization are equal only if the sections of `F`
agree. -/
private theorem eq_of_mk_eq_relocalize {W : (Over X)ᵒᵖ} {ψ : (unop W).left ⟶ A}
    {s t : F.obj (op (Over.mk ψ))} {h h' : ψ ≫ a = (unop W).hom}
    (e : relocalizeMk a F ψ s h = relocalizeMk a F ψ t h') : s = t :=
  eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp (congrArg Subtype.val e)).2

/-- **Relocalizing a restriction is a base change.** The relocalization along `m ≫ a` of the
restriction of `F` to `C/A'` is the fibre product of the relocalization of `F` along `a` with
the representable presheaf of `m` over the representable presheaf of `A ⟶ X`. -/
theorem isPullback_relocalizeRestrictMap :
    IsPullback (relocalizeRestrictMap a m F)
      (relocalizeToYoneda (m ≫ a) ((relocalizeRestrict m).obj F))
      (relocalizeToYoneda a F)
      (yoneda.map (Over.homMk m rfl : Over.mk (m ≫ a) ⟶ Over.mk a)) := by
  refine IsPullback.of_forall_isPullback_app fun W => ?_
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact Over.OverMorphism.ext rfl
  · rintro ⟨⟨ψ, s⟩, hp⟩ ⟨⟨ψ', s'⟩, hp'⟩ ⟨h1, h2⟩
    obtain rfl : ψ = ψ' := congrArg Over.Hom.left h2
    obtain rfl : s = s' := eq_of_mk_eq_relocalize a F (W := W) (ψ := ψ ≫ m) h1
    rfl
  · rintro ⟨⟨ψ, s⟩, hp⟩ h hy
    have hpa : ψ ≫ a = (unop W).hom := hp
    obtain rfl : ψ = h.left ≫ m := congrArg Over.Hom.left hy
    exact ⟨relocalizeMk (m ≫ a) ((relocalizeRestrict m).obj F) h.left s
      ((Category.assoc _ _ _).symm.trans hpa), Subtype.ext rfl, Over.OverMorphism.ext rfl⟩

/-- **The structural morphism of `Λ_a F` sees every section of `F`.** Two sections of `F` over
`W : C/A` give two sections of `Λ_a F` over the image of `W` in `C/X` carrying the *same*
factorization, namely the structure morphism of `W` itself; so if the structural morphism
`Λ_a F ⟶ h_{(A ⟶ X)}` is injective in each degree the two sections of `F` agree.

Combined with `CategoryTheory.NatTrans.mono_iff_mono_app` this says that `F` is a subsingleton
presheaf as soon as the structural morphism of its relocalization is a monomorphism, which is the
form in which a monomorphism condition imposed on an algebraic space over `A` read over `X` comes
back as a condition on the space itself. -/
theorem subsingleton_of_injective_relocalizeToYoneda
    (hinj : ∀ W, Function.Injective ((relocalizeToYoneda a F).app W)) (W : (Over A)ᵒᵖ) :
    Subsingleton (F.obj W) := by
  refine ⟨fun s t => ?_⟩
  exact eq_of_mk_eq_relocalize a F (W := op (Over.mk ((unop W).hom ≫ a))) (ψ := (unop W).hom)
    (h := rfl) (h' := rfl)
    (hinj _ rfl)

end CategoryTheory.OverShriek

end
