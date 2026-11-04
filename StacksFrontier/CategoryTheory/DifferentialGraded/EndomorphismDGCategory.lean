module

public import StacksFrontier.Algebra.DGA.DGCategory

/-!
# The one-object differential graded subcategory on an object

Let `C` be a differential graded category over a commutative ring `R` and let `K` be an object
of `C`. The *one-object differential graded subcategory on `K`* is the differential graded
category `E` with a single object and with hom complex the endomorphism complex `C(K, K)` of
`K`: every structure field of `E` is the corresponding field of `C` at the pair `(K, K)`, with
no transport and no change of the composition, the differential or the identity. The inclusion
`E ⥤ C` sends the single object to `K` and is the identity on homogeneous morphisms, so it is a
fully faithful functor of differential graded categories.

Its right differential graded modules are the right differential graded `E = C(K, K)`-modules
of [Stacks, Tag 09LK].

## Main definitions

* `DGCategory.endDGCategory`: the one-object differential graded category `E = C(K, K)`.
* `DGCategory.endDGInclusion`: the inclusion `E ⥤ C` of differential graded categories.

## Main results

* `DGCategory.endDGCategory_hom`, `DGCategory.endDGCategory_d`,
  `DGCategory.endDGCategory_comp` and `DGCategory.endDGCategory_id`: the hom complex, the
  differential, the composition and the identity of `E` are those of `C` at `(K, K)`.
* `DGCategory.endDGInclusion_obj` and `DGCategory.endDGInclusion_map`: the inclusion is `K` on
  the object and the identity on homogeneous morphisms.

## Implementation notes

The single object is `PUnit` in the object universe of `C`, so that `E` and `C` are
differential graded categories at the same universe levels, and the inclusion is the identity on
homogeneous morphisms.
-/

@[expose] public section

namespace DGCategory

universe v u r

variable {R : Type r} [CommRing R]

/-- The *one-object differential graded subcategory on `K`*: the differential graded category
with a single object whose hom complex is the endomorphism complex `C(K, K)` of `K`, with the
differential, the composition and the identity of `C`. -/
@[implicit_reducible]
def endDGCategory (C : DGCategory.{v, u} R) (K : C.Obj) : DGCategory.{v, u} R where
  Obj := PUnit.{u + 1}
  Hom _ _ n := C.Hom K K n
  addCommGroup _ _ n := C.addCommGroup K K n
  module _ _ n := C.module K K n
  d := fun {_ _ _} f => C.d f
  d_add := fun {_ _ _} f g => C.d_add f g
  d_smul := fun {_ _ _} c f => C.d_smul c f
  d_d := fun {_ _ _} f => C.d_d f
  comp := fun {_ _ _ _ _ _} h g f => C.comp h g f
  comp_add_left := fun {_ _ _ _ _ _} h g₁ g₂ f => C.comp_add_left h g₁ g₂ f
  comp_add_right := fun {_ _ _ _ _ _} h g f₁ f₂ => C.comp_add_right h g f₁ f₂
  comp_smul_left := fun {_ _ _ _ _ _} h c g f => C.comp_smul_left h c g f
  comp_smul_right := fun {_ _ _ _ _ _} h c g f => C.comp_smul_right h c g f
  leibniz := fun {_ _ _ _ _ _} h g f => C.leibniz h g f
  assoc := fun {_ _ _ _ _ _ _ _ _ _} h₁ h₂ h₃ h₄ e g f => C.assoc h₁ h₂ h₃ h₄ e g f
  id := fun _ => C.id K
  id_comp := fun {_ _ _} f => C.id_comp f
  comp_id := fun {_ _ _} f => C.comp_id f
  d_id := fun _ => C.d_id K

/-- The hom complex of the one-object differential graded subcategory on `K` is the
endomorphism complex of `K`. -/
@[simp] theorem endDGCategory_hom (C : DGCategory.{v, u} R) (K : C.Obj)
    (x y : (endDGCategory C K).Obj) (n : ℤ) :
    (endDGCategory C K).Hom x y n = C.Hom K K n := rfl

/-- The differential of the one-object differential graded subcategory on `K` is that of
`C`. -/
@[simp] theorem endDGCategory_d (C : DGCategory.{v, u} R) (K : C.Obj)
    {x y : (endDGCategory C K).Obj} {n : ℤ} (f : (endDGCategory C K).Hom x y n) :
    (endDGCategory C K).d f = C.d f := rfl

/-- The composition of the one-object differential graded subcategory on `K` is that of `C`. -/
@[simp] theorem endDGCategory_comp (C : DGCategory.{v, u} R) (K : C.Obj)
    {x y z : (endDGCategory C K).Obj} {m n k : ℤ} (h : m + n = k)
    (g : (endDGCategory C K).Hom y z m) (f : (endDGCategory C K).Hom x y n) :
    (endDGCategory C K).comp h g f = C.comp h g f := rfl

/-- The identity of the one-object differential graded subcategory on `K` is the identity of
`K`. -/
@[simp] theorem endDGCategory_id (C : DGCategory.{v, u} R) (K : C.Obj)
    (x : (endDGCategory C K).Obj) : (endDGCategory C K).id x = C.id K := rfl

/-- The one-object differential graded subcategory on `K` has an object. -/
instance (C : DGCategory.{v, u} R) (K : C.Obj) : Nonempty (endDGCategory C K).Obj :=
  inferInstanceAs (Nonempty PUnit)

/-- The one-object differential graded subcategory on `K` has at most one object. -/
instance (C : DGCategory.{v, u} R) (K : C.Obj) : Subsingleton (endDGCategory C K).Obj :=
  inferInstanceAs (Subsingleton PUnit)

/-- The inclusion of the one-object differential graded subcategory on `K`: it sends the single
object to `K` and is the identity on homogeneous morphisms. -/
def endDGInclusion (C : DGCategory.{v, u} R) (K : C.Obj) :
    DGFunctor (endDGCategory C K) C where
  obj _ := K
  map := fun {_ _ _} f => f
  map_add := fun {_ _ _} _ _ => rfl
  map_smul := fun {_ _ _} _ _ => rfl
  map_d := fun {_ _ _} _ => rfl
  map_comp := fun {_ _ _ _ _ _} _ _ _ => rfl
  map_id := fun _ => rfl

/-- The inclusion sends the single object of `E` to `K`. -/
@[simp] theorem endDGInclusion_obj (C : DGCategory.{v, u} R) (K : C.Obj)
    (x : (endDGCategory C K).Obj) : (endDGInclusion C K).obj x = K := rfl

/-- The inclusion is the identity on homogeneous morphisms. -/
@[simp] theorem endDGInclusion_map (C : DGCategory.{v, u} R) (K : C.Obj)
    {x y : (endDGCategory C K).Obj} {n : ℤ} (f : (endDGCategory C K).Hom x y n) :
    (endDGInclusion C K).map f = f := rfl

end DGCategory
