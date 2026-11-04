module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.StandardResolution.Basic

/-!
# The standard resolution of a morphism of sheaves of rings

For a sheaf of commutative rings `A`, the free `A`-algebra on a sheaf of sets is obtained by
sheafifying the pointwise free commutative ring and taking its coproduct with `A`. The comonad
of this free-forgetful adjunction gives the standard augmented simplicial resolution of every
`A`-algebra sheaf.

## Main definitions

* `CategoryTheory.Comonad.StandardResolutionFunctorData` packages Godement's standard resolution
  of a comonad, together with the equations identifying its terms and simplicial maps.
* `CategoryTheory.Sheaf.freeAlgebraSheaf` is the free `A`-algebra sheaf functor.
* `CategoryTheory.Sheaf.standardResolutionFunctor` is the standard augmented simplicial
  endofunctor on sheaves of `A`-algebras.
* `CategoryTheory.Sheaf.standardResolution` is the standard resolution of a specified morphism
  `A ⟶ B`.

## Main results

* `CategoryTheory.Sheaf.standardResolution_obj` identifies every term with the corresponding
  iterate of the free-forgetful comonad.
* `CategoryTheory.Sheaf.standardResolutionFunctor_face` and
  `CategoryTheory.Sheaf.standardResolutionFunctor_degeneracy` identify all face and degeneracy
  maps.

## Implementation notes

A sheaf of `A`-algebras is represented by the under-category `Under A`. The free algebra on a
sheaf `E` is `A ⨿ ℤ[E]`, with the pointwise polynomial ring sheafified before taking the
coproduct, so the terms of the resolution are `A[B]`, `A[A[B]]`, and so on. The construction is
first made as an augmented simplicial object of endofunctors, which retains its canonical
naturality in `B`, and is then evaluated at the object `A ⟶ B`. The augmentation point is
definitionally this object of `Under A`; the term identifications transport the simplicial maps
to the comonad faces and degeneracies. The covering declaration is `standardResolution`; the
free-forgetful adjunction and the term and map formulas provide its defining universal property
and degreewise interface.

The universe of coefficients contains the universes of objects and arrows of the site.
Sheafification is then available without additional hypotheses: the forgetful functor from
commutative rings preserves limits and filtered colimits.

## References

* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe v u w

namespace CategoryTheory.Comonad

/-- The data used to choose Godement's standard resolution of a comonad. -/
structure StandardResolutionFunctorData {D : Type*} [Category D] (G : Comonad D) where
  /-- The augmented simplicial object of endofunctors. -/
  augmentation : SimplicialObject.Augmented (D ⥤ D)
  /-- Its term in degree `n` is the `(n + 1)`-fold iterate of the comonad. -/
  obj_eq : ∀ n : ℕ, augmentation.left.obj (op ⦋n⦌) = (G : D ⥤ D).iterate (n + 1)
  /-- Its augmentation point is the identity functor. -/
  point_eq : augmentation.right = 𝟭 D
  /-- Its face maps are Godement's. -/
  face_eq : ∀ (n : ℕ) (j : Fin (n + 2)),
    augmentation.left.δ j = eqToHom (obj_eq (n + 1)) ≫
      Godement.face G.ε (n + 1) j ≫ eqToHom (obj_eq n).symm
  /-- Its degeneracy maps are Godement's. -/
  degeneracy_eq : ∀ (n : ℕ) (j : Fin (n + 1)),
    augmentation.left.σ j = eqToHom (obj_eq n) ≫
      Godement.degeneracy G.δ n j ≫ eqToHom (obj_eq (n + 1)).symm
  /-- Its augmentation map in degree zero is the counit. -/
  augmentation_eq : augmentation.hom.app (op ⦋0⦌) =
    eqToHom (obj_eq 0) ≫ G.ε ≫ eqToHom point_eq.symm

/-- A choice of Godement's standard resolution data for a comonad. -/
noncomputable def standardResolutionFunctorData {D : Type*} [Category D]
    (G : Comonad D) : StandardResolutionFunctorData G :=
  let e := Godement.exists_augmented_standardResolution G.ε G.δ
    (by ext; simp) (by ext; simp) (by ext; simp)
  let h := e.choose_spec.choose
  let hX := e.choose_spec.choose_spec.choose
  let hs := e.choose_spec.choose_spec.choose_spec
  { augmentation := e.choose
    obj_eq := h
    point_eq := hX
    face_eq := hs.1
    degeneracy_eq := hs.2.1
    augmentation_eq := hs.2.2 }

end CategoryTheory.Comonad

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The usual sheafification construction also works when the coefficient universe is larger
than the universes of the site. -/
instance hasWeakSheafifyCommRingCat : HasWeakSheafify J CommRingCat.{max u v w} := by
  let : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget CommRingCat.{max u v w}) :=
    preservesFilteredColimitsOfSize_shrink (forget CommRingCat.{max u v w})
  let : HasColimitsOfSize.{max u v, max u v} CommRingCat.{max u v w} :=
    hasColimitsOfSizeShrink CommRingCat.{max u v w}
  infer_instance

/-- The free sheaf of `A`-algebras on a sheaf of sets. It sends `E` to the coproduct of `A`
with the sheafification of the pointwise polynomial ring `ℤ[E]`. -/
@[implicit_reducible]
noncomputable def freeAlgebraSheaf (A : Sheaf J CommRingCat.{max u v w}) :
    Sheaf J (Type (max u v w)) ⥤ Under A :=
  Sheaf.composeAndSheafify J CommRingCat.free.{max u v w} ⋙ Under.costar A

/-- The functor sending a sheaf of `A`-algebras to its underlying sheaf of sets. -/
@[implicit_reducible]
def forgetAlgebraSheaf (A : Sheaf J CommRingCat.{max u v w}) :
    Under A ⥤ Sheaf J (Type (max u v w)) :=
  Under.forget A ⋙ sheafForget J

/-- The free-forgetful adjunction for sheaves of `A`-algebras. -/
noncomputable abbrev freeAlgebraSheafAdjunction (A : Sheaf J CommRingCat.{max u v w}) :
    freeAlgebraSheaf J A ⊣ forgetAlgebraSheaf J A :=
  (Sheaf.adjunction J CommRingCat.adj.{max u v w}).comp (Under.costarAdjForget A)

/-- The free-forgetful comonad on sheaves of `A`-algebras. -/
noncomputable abbrev standardResolutionComonad (A : Sheaf J CommRingCat.{max u v w}) :
    Comonad (Under A) :=
  (freeAlgebraSheafAdjunction J A).toComonad

/-- The standard resolution, simultaneously and naturally in every sheaf of `A`-algebras. -/
noncomputable def standardResolutionFunctor (A : Sheaf J CommRingCat.{max u v w}) :
    SimplicialObject.Augmented (Under A ⥤ Under A) :=
  (Comonad.standardResolutionFunctorData (standardResolutionComonad J A)).augmentation

/-- The augmentation point of the standard resolution of endofunctors is the identity. -/
@[simp]
theorem standardResolutionFunctor_point (A : Sheaf J CommRingCat.{max u v w}) :
    (standardResolutionFunctor J A).right = 𝟭 (Under A) :=
  (Comonad.standardResolutionFunctorData (standardResolutionComonad J A)).point_eq

/-- The term in degree `n` of the standard resolution of endofunctors is the `(n + 1)`-fold
iterate of the free-forgetful comonad. -/
theorem standardResolutionFunctor_obj (A : Sheaf J CommRingCat.{max u v w}) (n : ℕ) :
    (standardResolutionFunctor J A).left.obj (op ⦋n⦌) =
      ((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).iterate
        (n + 1) :=
  (Comonad.standardResolutionFunctorData (standardResolutionComonad J A)).obj_eq n

/-- The face maps of the standard resolution of endofunctors are Godement's. -/
theorem standardResolutionFunctor_face (A : Sheaf J CommRingCat.{max u v w})
    (n : ℕ) (j : Fin (n + 2)) :
    (standardResolutionFunctor J A).left.δ j =
      eqToHom (standardResolutionFunctor_obj J A (n + 1)) ≫
        Godement.face (standardResolutionComonad J A).ε (n + 1) j ≫
          eqToHom (standardResolutionFunctor_obj J A n).symm :=
  (Comonad.standardResolutionFunctorData (standardResolutionComonad J A)).face_eq n j

/-- The degeneracy maps of the standard resolution of endofunctors are Godement's. -/
theorem standardResolutionFunctor_degeneracy (A : Sheaf J CommRingCat.{max u v w})
    (n : ℕ) (j : Fin (n + 1)) :
    (standardResolutionFunctor J A).left.σ j =
      eqToHom (standardResolutionFunctor_obj J A n) ≫
        Godement.degeneracy (standardResolutionComonad J A).δ n j ≫
          eqToHom (standardResolutionFunctor_obj J A (n + 1)).symm :=
  (Comonad.standardResolutionFunctorData (standardResolutionComonad J A)).degeneracy_eq n j

/-- In degree zero the augmentation of the standard resolution is the counit of the
free-forgetful comonad. -/
theorem standardResolutionFunctor_augmentation (A : Sheaf J CommRingCat.{max u v w}) :
    (standardResolutionFunctor J A).hom.app (op ⦋0⦌) =
      eqToHom (standardResolutionFunctor_obj J A 0) ≫
        (standardResolutionComonad J A).ε ≫
          eqToHom (standardResolutionFunctor_point J A).symm :=
  (Comonad.standardResolutionFunctorData (standardResolutionComonad J A)).augmentation_eq

/-- **Stacks 08SR.** The standard resolution of a morphism `A ⟶ B` of sheaves of commutative
rings is the augmentation obtained by evaluating the free-forgetful standard resolution at the
`A`-algebra `B`. -/
@[stacks 08SR]
noncomputable def standardResolution {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B) :
    SimplicialObject.Augmented (Under A) :=
  let X := (SimplicialObject.Augmented.whiskeringObj _ _
    ((evaluation (Under A) (Under A)).obj (Under.mk f))).obj (standardResolutionFunctor J A)
  { left := X.left
    right := Under.mk f
    hom := X.hom ≫ (SimplicialObject.const (Under A)).map
      (eqToHom (Functor.congr_obj (standardResolutionFunctor_point J A) (Under.mk f))) }

/-- The augmentation point of the standard resolution of `f` is `f` itself. -/
@[simp]
theorem standardResolution_point {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B) :
    (standardResolution J f).right = Under.mk f := rfl

/-- The term in degree `n` of the standard resolution is the `(n + 1)`-fold iterate of the
free-forgetful comonad applied to `B`. -/
theorem standardResolution_obj {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B) (n : ℕ) :
    (standardResolution J f).left.obj (op ⦋n⦌) =
      (((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).iterate
        (n + 1)).obj (Under.mk f) :=
  Functor.congr_obj (standardResolutionFunctor_obj J A n) (Under.mk f)

/-- The zeroth term of the standard resolution is the free `A`-algebra sheaf on the underlying
sheaf of sets of `B`, namely `A[B]`. -/
@[simp]
theorem standardResolution_obj_zero {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B) :
    (standardResolution J f).left.obj (op ⦋0⦌) =
      (freeAlgebraSheaf J A).obj ((forgetAlgebraSheaf J A).obj (Under.mk f)) := by
  rw [standardResolution_obj]; rfl

/-- The first term of the standard resolution is `A[A[B]]`. -/
theorem standardResolution_obj_one {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B) :
    (standardResolution J f).left.obj (op ⦋1⦌) =
      (freeAlgebraSheaf J A).obj ((forgetAlgebraSheaf J A).obj
        ((freeAlgebraSheaf J A).obj ((forgetAlgebraSheaf J A).obj (Under.mk f)))) := by
  rw [standardResolution_obj]; rfl

end CategoryTheory.Sheaf
