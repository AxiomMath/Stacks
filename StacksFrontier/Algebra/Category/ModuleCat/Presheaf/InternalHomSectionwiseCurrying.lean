module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomTensorCurrying

/-!
# Currying along a map out of a sectionwise tensor product of presheaves of modules

Let `O` be a presheaf of commutative rings on a category `C`, let `F`, `G`, `H` be presheaves
of `O`-modules and let `ε : F ⊗ G ⟶ A` be any morphism out of their sectionwise tensor
product. Composing the currying isomorphism of the presheaf clause of Stacks 03EO
(`Stacks.PresheafOfModules.InternalHom.presheafInternalHomTensorIso`) with precomposition by
`ε` gives a morphism

`Hom_O(A, H) ⟶ Hom_O(F, Hom_O(G, H))`

of presheaves of `O`-modules. This file records its value on plain sections and its naturality
in each of the three variables, each statement taking the naturality of `ε` itself as a
hypothesis.

## Main results

* `Stacks.PresheafOfModules.InternalHom.curryAlong_hom_app_plain`: on plain sections the
  composite is `s ↦ (x ↦ (y ↦ s (ε (x|_· ⊗ y))))`.
* `Stacks.PresheafOfModules.InternalHom.curryAlong_natural_left`,
  `..._natural_middle`, `..._natural_right`: naturality in the two tensor factors
  (contravariantly) and in the target (covariantly).
* `Stacks.PresheafOfModules.InternalHom.internalHomMapLeft_internalHomMapRight`: internal Hom is
  a bifunctor, contravariant in its first and covariant in its second variable.

## Implementation notes

The statements are made for an arbitrary `ε` and for presheaves of modules over `Oforget O`. A
sheaf of modules over the structure sheaf `O` carries its module structure for the presheaf of
rings `(ringSheaf O).obj`; the two are definitionally equal but not type-correct at `implicit`
transparency, so `rw` and `simp only` do not fire on a goal mentioning
`internalHom O.obj A.val B.val`. Statements about sheaves are obtained from these by `exact`, whose
defeq check runs at default transparency.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

namespace Stacks.PresheafOfModules.InternalHom

universe v u

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat)
variable (F G H : _root_.PresheafOfModules.{max u v} (Oforget O))

/-- Precomposition in the first variable of internal Hom commutes with postcomposition in the
second: internal Hom is a bifunctor. -/
theorem internalHomMapLeft_internalHomMapRight
    {A B : _root_.PresheafOfModules.{max u v} (Oforget O)} (a : A ⟶ B) (h : G ⟶ H) :
    internalHomMapLeft O a ≫ internalHomMapRight O A h =
      internalHomMapRight O B h ≫ internalHomMapLeft O a := by
  apply _root_.PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  rfl

/-- Two objects of the slice category `C/U` with equal structure maps have literally the same
module of sections of a restricted presheaf of modules, and a morphism of restricted presheaves
takes the same value at both. -/
theorem app_over_mk_congr {A N : _root_.PresheafOfModules.{max u v} (Oforget O)}
    (U : C) {W : C} {h h' : W ⟶ U} (hh : h = h')
    (s : (restrFun O U).obj A ⟶ (restrFun O U).obj N) (t : A.obj (op W)) :
    (s.app (op (Over.mk h))).hom t = (s.app (op (Over.mk h'))).hom t := by
  subst hh
  rfl

section Curry

variable {A A' : _root_.PresheafOfModules.{max u v} (Oforget O)}

/-- Currying along `ε : F ⊗ G ⟶ A`, read on plain sections: a section `s` of `Hom_O(A, H)`
over `U`, that is a morphism `A|_U ⟶ H|_U`, goes to the rule sending a section `x` of `F` over
`p : S ⟶ U` and a section `y` of `G` over `q : T ⟶ S` to the value of `s` on `ε (x|_T ⊗ y)`. -/
theorem curryAlong_hom_app_plain (ε : F ⊗ G ⟶ A) (U : C)
    (s : (restrFun O U).obj A ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    ((((((internalHomMapLeft O ε ≫
        (presheafInternalHomTensorIso O F G H).hom).app (op U)).hom s).app
        (op (Over.mk p))).hom x).app (op (Over.mk q))).hom y =
      (s.app (op (Over.mk (q ≫ p)))).hom
        ((ε.app (op T)).hom
          ((ConcreteCategory.hom (F.map q.op)) x ⊗ₜ[O.obj (op T)] y)) :=
  rfl

/-- Currying along `ε` is contravariantly natural in the first tensor factor, for any `τ`
through which `ε` is natural. -/
theorem curryAlong_natural_left
    {F' : _root_.PresheafOfModules.{max u v} (Oforget O)} (f : F' ⟶ F)
    (ε : F ⊗ G ⟶ A) (ε' : F' ⊗ G ⟶ A') (τ : A' ⟶ A)
    (hτ : (f ⊗ₘ 𝟙 G) ≫ ε = ε' ≫ τ) :
    (internalHomMapLeft O ε ≫ (presheafInternalHomTensorIso O F G H).hom) ≫
        internalHomMapLeft O f =
      internalHomMapLeft O τ ≫
        (internalHomMapLeft O ε' ≫ (presheafInternalHomTensorIso O F' G H).hom) := by
  rw [Category.assoc, presheafInternalHomTensorIso_natural_left, ← Category.assoc,
    ← Category.assoc, internalHomMapLeft_comp,
    internalHomMapLeft_comp, hτ]

/-- Currying along `ε` is contravariantly natural in the second tensor factor, for any `τ`
through which `ε` is natural. -/
theorem curryAlong_natural_middle
    {G' : _root_.PresheafOfModules.{max u v} (Oforget O)} (g : G' ⟶ G)
    (ε : F ⊗ G ⟶ A) (ε' : F ⊗ G' ⟶ A') (τ : A' ⟶ A)
    (hτ : (𝟙 F ⊗ₘ g) ≫ ε = ε' ≫ τ) :
    (internalHomMapLeft O ε ≫ (presheafInternalHomTensorIso O F G H).hom) ≫
        internalHomMapRight O F (internalHomMapLeft O g) =
      internalHomMapLeft O τ ≫
        (internalHomMapLeft O ε' ≫ (presheafInternalHomTensorIso O F G' H).hom) := by
  rw [Category.assoc, presheafInternalHomTensorIso_natural_middle, ← Category.assoc,
    ← Category.assoc, internalHomMapLeft_comp,
    internalHomMapLeft_comp, hτ]

/-- Currying along `ε` is covariantly natural in the target. -/
theorem curryAlong_natural_right (ε : F ⊗ G ⟶ A)
    {H' : _root_.PresheafOfModules.{max u v} (Oforget O)} (h : H ⟶ H') :
    internalHomMapRight O A h ≫
        (internalHomMapLeft O ε ≫ (presheafInternalHomTensorIso O F G H').hom) =
      (internalHomMapLeft O ε ≫ (presheafInternalHomTensorIso O F G H).hom) ≫
        internalHomMapRight O F (internalHomMapRight O G h) := by
  rw [← Category.assoc, ← internalHomMapLeft_internalHomMapRight, Category.assoc,
    presheafInternalHomTensorIso_natural_right, Category.assoc]

end Curry

end Stacks.PresheafOfModules.InternalHom

end
