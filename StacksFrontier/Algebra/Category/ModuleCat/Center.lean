module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import StacksFrontier.CategoryTheory.Center.Equivalence

/-!
# The center of a ring is the center of its category of modules

For a ring `A` which is an algebra over a commutative ring `R`, the centre of `A` is the centre
of the category `ModuleCat A` in the sense of `CategoryTheory.CatCenter`, that is, the ring of
endomorphisms of the identity functor, and the identification is one of `R`-algebras.

A central element `a` acts on every `A`-module by `m ↦ a • m`; this is `A`-linear precisely
because `a` is central, and it is natural because every `A`-linear map commutes with the action
of `a`. Conversely a natural endomorphism `z` of the identity functor is determined by its
component at the free module of rank one: `z` acts on an arbitrary `m : M` through the
`A`-linear map `A → M`, `x ↦ x • m`, so `z` is multiplication by `a = z 1`, and `a` is central
because that same map, taken with `M = A`, computes `z` on `b : A` both as `a * b` and, by
`A`-linearity of `z` at `A`, as `b * a`.

## Main definitions

* `ModuleCat.centerToCatCenter`: the natural endomorphism of the identity functor of
  `ModuleCat A` given by the action of a central element of `A`.
* `ModuleCat.catCenterValue`: the element `z 1` of `A` attached to a central element `z` of the
  category `ModuleCat A`.
* `ModuleCat.centerAlgEquiv`: the resulting isomorphism of `R`-algebras
  `Subalgebra.center R A ≃ₐ[R] CatCenter (ModuleCat A)`.

## Main results

* `ModuleCat.catCenter_app_apply`: a central element of `ModuleCat A` acts on every module by
  multiplication by `ModuleCat.catCenterValue`.
* `ModuleCat.catCenterValue_mem`: that element lies in the centre of `A`.

## Implementation notes

The modules are taken in the same universe as `A`, which is forced: the argument runs through
the free module of rank one `ModuleCat.of A A`, so `A` must itself be an object of the category.

## References

* [Stacks Project, Tag 09SD](https://stacks.math.columbia.edu/tag/09SD), for which this file
  supplies the identification of the centre of an algebra with the centre of a category.
-/

@[expose] public section

open CategoryTheory

namespace ModuleCat

open scoped ModuleCat.Algebra

universe u

variable (R : Type*) [CommRing R] (A : Type u) [Ring A] [Algebra R A]

/-- The element of `A` through which a central element of the category `ModuleCat A` acts,
namely its value at `1` in the free module of rank one. -/
def catCenterValue (z : CatCenter (ModuleCat.{u} A)) : A :=
  (z.app (ModuleCat.of A A)).hom 1

/-- A central element of the category `ModuleCat A` acts on every module by multiplication by
`ModuleCat.catCenterValue`. -/
lemma catCenter_app_apply (z : CatCenter (ModuleCat.{u} A)) (M : ModuleCat.{u} A) (m : M) :
    (z.app M).hom m = catCenterValue A z • m := by
  have h := congrArg (fun (f : ModuleCat.of A A ⟶ M) => f.hom (1 : A))
    (z.naturality (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)))
  simpa [catCenterValue] using h

/-- The element of `A` attached to a central element of the category `ModuleCat A` lies in the
centre of `A`. -/
lemma catCenterValue_mem (z : CatCenter (ModuleCat.{u} A)) :
    catCenterValue A z ∈ Subalgebra.center R A := by
  rw [Subalgebra.mem_center_iff]
  intro b
  have h1 : (z.app (ModuleCat.of A A)).hom b = catCenterValue A z * b :=
    catCenter_app_apply A z (ModuleCat.of A A) b
  have h2 : (z.app (ModuleCat.of A A)).hom b = b * catCenterValue A z := by
    have h := (z.app (ModuleCat.of A A)).hom.map_smul b (1 : A)
    rw [smul_eq_mul, mul_one] at h
    exact h
  rw [← h1, h2]

/-- A central element of `A` acts on every `A`-module, naturally in the module, giving a central
element of the category `ModuleCat A`. -/
def centerToCatCenter (a : Subalgebra.center R A) : CatCenter (ModuleCat.{u} A) where
  app M := ModuleCat.ofHom
    { toFun m := (a : A) • m
      map_add' x y := smul_add _ x y
      map_smul' c m := by
        change (a : A) • c • m = c • (a : A) • m
        rw [smul_smul, smul_smul, Subalgebra.mem_center_iff.1 a.2 c] }
  naturality _ _ f := by ext m; exact ((ModuleCat.Hom.hom f).map_smul _ _).symm

/-- The component of `ModuleCat.centerToCatCenter R A a` at `M` sends `m` to `a • m`. -/
@[simp]
lemma centerToCatCenter_app_apply (a : Subalgebra.center R A) (M : ModuleCat.{u} A) (m : M) :
    ((centerToCatCenter R A a).app M).hom m = (a : A) • m := rfl

/-- **The centre of a ring is the centre of its category of modules.** For an `R`-algebra `A`,
the centre of `A` is isomorphic, as an `R`-algebra, to the ring of endomorphisms of the
identity functor of `ModuleCat A`. -/
def centerAlgEquiv : (Subalgebra.center R A) ≃ₐ[R] CatCenter (ModuleCat.{u} A) where
  toFun := centerToCatCenter R A
  invFun z := ⟨catCenterValue A z, catCenterValue_mem R A z⟩
  left_inv a := by
    ext
    change ((centerToCatCenter R A a).app (ModuleCat.of A A)).hom 1 = (a : A)
    rw [centerToCatCenter_app_apply, smul_eq_mul, mul_one]
  right_inv z :=
    CatCenter.ext _ _ fun M => ModuleCat.hom_ext (LinearMap.ext fun m => by
      rw [centerToCatCenter_app_apply]
      exact (catCenter_app_apply A z M m).symm)
  map_mul' a b :=
    CatCenter.ext _ _ fun M => ModuleCat.hom_ext (LinearMap.ext fun m => by
      rw [CatCenter.mul_app, centerToCatCenter_app_apply]
      change _ = ((centerToCatCenter R A b).app M).hom (((centerToCatCenter R A a).app M).hom m)
      rw [centerToCatCenter_app_apply, centerToCatCenter_app_apply, smul_smul]
      exact congrArg (· • m) (Subalgebra.mem_center_iff.1 b.2 _))
  map_add' a b :=
    CatCenter.ext _ _ fun M => ModuleCat.hom_ext (LinearMap.ext fun m => by
      rw [CatCenter.app_add, centerToCatCenter_app_apply]
      change _ = ((centerToCatCenter R A a).app M).hom m + ((centerToCatCenter R A b).app M).hom m
      rw [centerToCatCenter_app_apply, centerToCatCenter_app_apply]
      exact add_smul _ _ _)
  commutes' r :=
    CatCenter.ext _ _ fun M => ModuleCat.hom_ext (LinearMap.ext fun m => by
      rw [CatCenter.algebraMap_app, centerToCatCenter_app_apply]
      rfl)

/-- The isomorphism `ModuleCat.centerAlgEquiv` sends a central element `a` of `A` to
`ModuleCat.centerToCatCenter R A a`. -/
@[simp]
lemma centerAlgEquiv_apply (a : Subalgebra.center R A) :
    centerAlgEquiv R A a = centerToCatCenter R A a := rfl

/-- The inverse of `ModuleCat.centerAlgEquiv` sends a central element `z` of the category
`ModuleCat A` to `ModuleCat.catCenterValue A z`. -/
@[simp]
lemma centerAlgEquiv_symm_apply_coe (z : CatCenter (ModuleCat.{u} A)) :
    (((centerAlgEquiv R A).symm z : Subalgebra.center R A) : A) = catCenterValue A z := rfl

end ModuleCat

end
