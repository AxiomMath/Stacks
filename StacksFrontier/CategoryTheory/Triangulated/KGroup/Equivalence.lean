module

public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Ring

/-!
# The zeroth `K`-group along an exact equivalence

Let `e : C ≌ D` be an equivalence of pretriangulated categories whose two functors commute with
the shift and preserve distinguished triangles. Each of them induces a homomorphism of zeroth
`K`-groups by `CategoryTheory.Pretriangulated.K0.map`, and the two are mutually inverse: the
unit and counit of the equivalence identify the composites with the identity on classes of
objects, and a homomorphism out of a `K`-group is determined by its values on those.

## Main definitions

* `CategoryTheory.Pretriangulated.K0.mapEquiv`: the induced isomorphism `K₀(C) ≃+ K₀(D)`.

## Main results

* `CategoryTheory.Pretriangulated.K0.map_inverse_comp_map_functor` and
  `CategoryTheory.Pretriangulated.K0.map_functor_comp_map_inverse`: the two homomorphisms are
  mutually inverse.
* `CategoryTheory.Pretriangulated.K0.mapEquiv_cls` and
  `CategoryTheory.Pretriangulated.K0.mapEquiv_symm_cls`: the isomorphism and its inverse on the
  class of an object.

## Implementation notes

The four exactness hypotheses — a `CommShift` and an `IsTriangulated` instance for each of the
two functors — are separate arguments rather than a single `CategoryTheory.Equivalence.CommShift`,
because `K0.map` consumes them one functor at a time and a caller that has built the two
functors separately has them in exactly this form.

The isomorphism is assembled as a structure with both maps given, rather than through
`AddEquiv.ofBijective`, so that its inverse is `K0.map e.inverse` on the nose and
`mapEquiv_symm_cls` holds by the same computation as `mapEquiv_cls`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated.K0

universe v u v' u'

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.IsTriangulated]
  [e.inverse.CommShift ℤ] [e.inverse.IsTriangulated]

/-- Going along an equivalence and back is the identity on `K₀(C)`. -/
theorem map_inverse_comp_map_functor :
    (map e.inverse).comp (map e.functor) = AddMonoidHom.id (K0 C) :=
  hom_ext fun X => by
    rw [AddMonoidHom.comp_apply, map_cls, map_cls, AddMonoidHom.id_apply]
    exact (cls_eq_of_iso (e.unitIso.app X)).symm

/-- Going along the inverse of an equivalence and back is the identity on `K₀(D)`. -/
theorem map_functor_comp_map_inverse :
    (map e.functor).comp (map e.inverse) = AddMonoidHom.id (K0 D) :=
  hom_ext fun Y => by
    rw [AddMonoidHom.comp_apply, map_cls, map_cls, AddMonoidHom.id_apply]
    exact cls_eq_of_iso (e.counitIso.app Y)

/-- **An exact equivalence of pretriangulated categories induces an isomorphism of zeroth
`K`-groups.** -/
def mapEquiv : K0 C ≃+ K0 D where
  toFun := map e.functor
  invFun := map e.inverse
  left_inv x := by
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using
      DFunLike.congr_fun (map_inverse_comp_map_functor e) x
  right_inv y := by
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using
      DFunLike.congr_fun (map_functor_comp_map_inverse e) y
  map_add' := (map e.functor).map_add

/-- The isomorphism `mapEquiv e` sends the class of `X` to the class of `e.functor.obj X`. -/
@[simp]
theorem mapEquiv_cls (X : C) : mapEquiv e (cls X) = cls (e.functor.obj X) :=
  map_cls e.functor X

/-- The inverse of `mapEquiv e` sends the class of `Y` to the class of `e.inverse.obj Y`. -/
@[simp]
theorem mapEquiv_symm_cls (Y : D) : (mapEquiv e).symm (cls Y) = cls (e.inverse.obj Y) :=
  map_cls e.inverse Y

end CategoryTheory.Pretriangulated.K0

end
