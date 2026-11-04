module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Additive
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory

/-!
# The Hom complex of a differential graded category

The homogeneous morphisms of all degrees between two objects of a differential graded category,
with the differential of the category, form a cochain complex of abelian groups
`Hom^•(x, y)`. A differential graded functor acts on these complexes, additively and compatibly
with the differentials, so it induces a morphism of Hom complexes.

## Main definitions

* `DGCategory.homComplex`: the Hom complex `Hom^•(x, y)` of two objects.
* `DGCategory.DGFunctor.homComplexMap`: the morphism of Hom complexes induced by a differential
  graded functor.
* `DGCategory.homComplexModules` and `DGCategory.DGFunctor.homComplexModulesMap`: the same
  complex and the same morphism read over the base ring `R` rather than in abelian groups.

## Main results

* `CochainComplex.dgCategoryHomComplexIso`: for the differential graded category of cochain
  complexes in a preadditive category, the Hom complex is Mathlib's
  `CochainComplex.HomComplex`.
* `DGCategory.homComplexModulesForget`: forgetting the scalars of `homComplexModules` gives
  `homComplex`.
* `DGCategory.DGFunctor.homComplexModulesMap_forget`: forgetting the scalars of
  `homComplexModulesMap` gives `homComplexMap`.
* `CochainComplex.dgCategoryLinear_homComplexModules_d_apply`: for cochain complexes the
  differential of the `R`-module-valued Hom complex is `CochainComplex.HomComplex.δ`.

## Implementation notes

The differential of a cochain complex is indexed by a pair of degrees, so `homComplex` carries
the differential of the differential graded category in the degrees related by the complex shape
and zero elsewhere; `DGCategory.d'` supplies the transport to the prescribed target degree.

A differential graded category over `R` has `R`-modules of homogeneous morphisms and an
`R`-linear differential, so the Hom complex is in fact a complex of `R`-modules; that reading is
`homComplexModules`.

Both Hom complexes carry their differential as a `dite` on the degrees, since the shape of a
cochain complex relates only consecutive ones. The `dite` is removed by
`DGCategory.homComplex_d_eq` and `DGCategory.homComplexModules_d_eq`, and for cochain complexes
`CochainComplex.dgCategoryLinear_homComplexModules_d_apply` identifies the differential of
`homComplexModules` with `CochainComplex.HomComplex.δ`, on an element and at an abstract base
category.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DGCategory

variable {R : Type*} [CommRing R] (A : DGCategory R)

/-- The differential on degree-`n` homogeneous morphisms, as a morphism of abelian groups. -/
def homAddMonoidHom (x y : A.Obj) (n m : ℤ) (h : n + 1 = m) :
    AddCommGrpCat.of (A.Hom x y n) ⟶ AddCommGrpCat.of (A.Hom x y m) :=
  AddCommGrpCat.ofHom
    { toFun := fun f => A.d' h f
      map_zero' := by subst h; exact A.d_zero
      map_add' := fun f g => by subst h; exact A.d_add f g }

/-- **The Hom complex of two objects of a differential graded category.** In degree `n` it is
the abelian group of homogeneous morphisms `x ⟶ y` of degree `n`, with the differential of the
differential graded category. -/
def homComplex (x y : A.Obj) : CochainComplex AddCommGrpCat ℤ where
  X n := AddCommGrpCat.of (A.Hom x y n)
  d n m := if h : n + 1 = m then A.homAddMonoidHom x y n m h else 0
  shape _ _ h := dite_eq_right_iff.2 (fun h' => absurd h' h)
  d_comp_d' n m k hnm hmk := by
    obtain rfl : m = n + 1 := hnm.symm
    obtain rfl : k = n + 1 + 1 := hmk.symm
    rw [dite_eq_left_of_eq_true (eq_true (rfl : n + 1 = n + 1)),
      dite_eq_left_of_eq_true (eq_true (rfl : n + 1 + 1 = n + 1 + 1))]
    exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun f => A.d_d f)

/-- The degree-`n` term of the Hom complex is the group of degree-`n` homogeneous morphisms. -/
@[simp] theorem homComplex_X (x y : A.Obj) (n : ℤ) :
    (A.homComplex x y).X n = AddCommGrpCat.of (A.Hom x y n) :=
  rfl

/-- Between consecutive degrees the differential of the Hom complex is `homAddMonoidHom`. -/
theorem homComplex_d_eq (x y : A.Obj) (n m : ℤ) (h : n + 1 = m) :
    (A.homComplex x y).d n m = A.homAddMonoidHom x y n m h :=
  dite_eq_left_of_eq_true (eq_true h)

namespace DGFunctor

variable {A} {B : DGCategory R} (F : A.DGFunctor B)

/-- The morphism of Hom complexes induced by a differential graded functor: in each degree the
action of the functor on homogeneous morphisms. -/
def homComplexMap (x y : A.Obj) : A.homComplex x y ⟶ B.homComplex (F.obj x) (F.obj y) where
  f n := AddCommGrpCat.ofHom
    { toFun := fun g => F.map g
      map_zero' := F.map_zero
      map_add' := fun g g' => F.map_add g g' }
  comm' n m hnm := by
    obtain rfl : m = n + 1 := hnm.symm
    rw [A.homComplex_d_eq x y n (n + 1) rfl,
      B.homComplex_d_eq (F.obj x) (F.obj y) n (n + 1) rfl]
    exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun g => (F.map_d g).symm)

end DGFunctor

/-! ### The Hom complex read over the base ring -/

/-- The differential on degree-`n` homogeneous morphisms, as a map of `R`-modules. -/
def homLinearMap (x y : A.Obj) (n m : ℤ) (h : n + 1 = m) :
    ModuleCat.of R (A.Hom x y n) ⟶ ModuleCat.of R (A.Hom x y m) :=
  ModuleCat.ofHom
    { toFun := fun f => A.d' h f
      map_add' := fun f g => by subst h; exact A.d_add f g
      map_smul' := fun r f => by subst h; exact A.d_smul r f }

/-- **The Hom complex of two objects of a differential graded category over `R`.** In degree `n`
it is the `R`-module of homogeneous morphisms `x ⟶ y` of degree `n`, with the differential of the
differential graded category, which is `R`-linear. Forgetting the scalars gives
`DGCategory.homComplex`. -/
def homComplexModules (x y : A.Obj) : CochainComplex (ModuleCat R) ℤ where
  X n := ModuleCat.of R (A.Hom x y n)
  d n m := if h : n + 1 = m then A.homLinearMap x y n m h else 0
  shape _ _ h := dite_eq_right_iff.2 (fun h' => absurd h' h)
  d_comp_d' n m k hnm hmk := by
    obtain rfl : m = n + 1 := hnm.symm
    obtain rfl : k = n + 1 + 1 := hmk.symm
    rw [dite_eq_left_of_eq_true (eq_true (rfl : n + 1 = n + 1)),
      dite_eq_left_of_eq_true (eq_true (rfl : n + 1 + 1 = n + 1 + 1))]
    exact ModuleCat.hom_ext (LinearMap.ext fun f => A.d_d f)

/-- The degree-`n` term of the `R`-module-valued Hom complex is the module of degree-`n`
homogeneous morphisms. -/
@[simp] theorem homComplexModules_X (x y : A.Obj) (n : ℤ) :
    (A.homComplexModules x y).X n = ModuleCat.of R (A.Hom x y n) :=
  rfl

/-- Between consecutive degrees the differential of the `R`-module-valued Hom complex is
`homLinearMap`. -/
theorem homComplexModules_d_eq (x y : A.Obj) (n m : ℤ) (h : n + 1 = m) :
    (A.homComplexModules x y).d n m = A.homLinearMap x y n m h :=
  dite_eq_left_of_eq_true (eq_true h)

/-- The underlying complex of abelian groups of the `R`-module-valued Hom complex is the Hom
complex: the `R`-module structure on the homogeneous morphisms is added structure on the same
complex. -/
def homComplexModulesForget (x y : A.Obj) :
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (A.homComplexModules x y) ≅ A.homComplex x y :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro n m hnm
    obtain rfl : m = n + 1 := hnm.symm
    rw [A.homComplex_d_eq x y n (n + 1) rfl]
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d]
    rw [A.homComplexModules_d_eq x y n (n + 1) rfl]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    rfl)

namespace DGFunctor

variable {A} {B : DGCategory R} (F : A.DGFunctor B)

/-- The morphism of `R`-module-valued Hom complexes induced by a differential graded functor: in
each degree the action of the functor on homogeneous morphisms, which is `R`-linear. -/
def homComplexModulesMap (x y : A.Obj) :
    A.homComplexModules x y ⟶ B.homComplexModules (F.obj x) (F.obj y) where
  f n := ModuleCat.ofHom
    { toFun := fun g => F.map g
      map_add' := fun g g' => F.map_add g g'
      map_smul' := fun r g => F.map_smul r g }
  comm' n m hnm := by
    obtain rfl : m = n + 1 := hnm.symm
    rw [A.homComplexModules_d_eq x y n (n + 1) rfl,
      B.homComplexModules_d_eq (F.obj x) (F.obj y) n (n + 1) rfl]
    exact ModuleCat.hom_ext (LinearMap.ext fun g => (F.map_d g).symm)

/-- **Forgetting the scalars of the induced map of module-valued Hom complexes gives the induced
map of Hom complexes.** Along the isomorphisms `DGCategory.homComplexModulesForget`, the
image of `homComplexModulesMap` under the forgetful functor is `homComplexMap`. -/
theorem homComplexModulesMap_forget (x y : A.Obj) :
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (F.homComplexModulesMap x y) ≫ (B.homComplexModulesForget (F.obj x) (F.obj y)).hom =
      (A.homComplexModulesForget x y).hom ≫ F.homComplexMap x y := by
  ext n
  rfl

end DGFunctor

end DGCategory

namespace CochainComplex

open CochainComplex.HomComplex

variable {B : Type*} [Category B] [Preadditive B]

/-- **The Hom complex of the differential graded category of cochain complexes is the Hom
complex.** For cochain complexes in a preadditive category the homogeneous morphisms of
degree `n` are the degree-`n` cochains and the differential is `δ`, so the Hom complex of the
differential graded category of Tag 09L9 is Mathlib's `CochainComplex.HomComplex`. -/
def dgCategoryHomComplexIso (L M : CochainComplex B ℤ) :
    (CochainComplex.dgCategory B).homComplex L M ≅ L.HomComplex M :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro n m hnm
    obtain rfl : m = n + 1 := hnm.symm
    rw [(CochainComplex.dgCategory B).homComplex_d_eq L M n (n + 1) rfl]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    rfl)

/-- **The differential of the `R`-module-valued Hom complex of cochain complexes is `δ`.** For
cochain complexes `L` and `M` in an `R`-linear preadditive category, the differential of
`DGCategory.homComplexModules` from degree `n` to degree `m` sends a cochain `f` to `δ n m f`. -/
theorem dgCategoryLinear_homComplexModules_d_apply {R : Type*} [CommRing R] [Linear R B]
    (L M : CochainComplex B ℤ) (n m : ℤ) (h : n + 1 = m) (f : Cochain L M n) :
    ModuleCat.Hom.hom (((CochainComplex.dgCategoryLinear B R).homComplexModules L M).d n m) f =
      δ n m f := by
  subst h
  rw [DGCategory.homComplexModules_d_eq (CochainComplex.dgCategoryLinear B R) L M n (n + 1) rfl]
  rfl

end CochainComplex

end
