module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Additive
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedExtensionByZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDifferentialGradedModule
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# Extension by zero of sheaves of differential graded modules, and its adjunction

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let
`j : (Sh(C/U), O_U) ⟶ (Sh(C), O)` be the localization morphism. Let `(A, d)` be a sheaf of
differential graded `O`-algebras and `A_U = j^*A = j^{-1}A` its restriction to the slice site.

This file constructs the exact functor `j_! : Mod^dg(A_U, d) ⥤ Mod^dg(A, d)` of the source,
whose underlying graded module is the one of Tag 0FRA and whose differential is `j_!d`, and
proves the identification of hom-complexes

`Hom_{Mod^dg(A, d)}(j_!M, N) = Hom_{Mod^dg(A_U, d)}(M, j^*N)`.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.over` is the restriction `A_U` of a sheaf of
  differential graded algebras to the slice site, and
  `SheafOfModules.DifferentialGradedModule.over`,
  `SheafOfModules.LeftDifferentialGradedModule.over` restrict a right, respectively left,
  differential graded module; `SheafOfModules.DifferentialGradedModule.overFunctor` is the
  resulting functor `j^* : Mod^dg(A, d) ⥤ Mod^dg(A_U, d)`.
* `SheafOfModules.dgExtendedAction` is the right `A`-action on the degreewise extension by zero
  of a right differential graded `A_U`-module; it is the action of Tag 0FRA.
* `SheafOfModules.dgExtensionByZero` is **the right differential graded `A`-module `j_!M`**, with
  `(j_!M)^n = j_!(M^n)` and differential `j_!d`, and
  `SheafOfModules.dgExtensionByZeroFunctor` is the functor `j_!`.
* `SheafOfModules.IsHomComplexDifferential` says that one homogeneous homomorphism of right
  differential graded modules is the differential `d(f) = d_N ∘ f - (-1)^d f ∘ d_M` of another;
  this is the differential of the hom-complex `Hom_{Mod^dg(A, d)}(-, -)`.
* `SheafOfModules.bilinearAddZSMul` and `SheafOfModules.bilinearCastTarget` add an integer
  multiple of one bilinear map to another and transport the target of a bilinear map along an
  equality of degrees; they are what state the Leibniz rule for the extended action as an
  identity of two bilinear maps.

## Main results

* `SheafOfModules.dgExtendedAction_leibniz`: the extended action obeys the signed Leibniz rule
  for the differential `j_!d`. This is the one point of the construction of `j_!` that the
  source calls a straightforward verification and leaves out.
* `SheafOfModules.dgExtendHomEquiv` and `SheafOfModules.dgExtensionByZeroAdjunction`:
  **Tag 0FRW** in degree zero. The homomorphisms `j_!M ⟶ N` of right differential graded
  `A`-modules are the homomorphisms `M ⟶ j^*N` of right differential graded `A_U`-modules,
  naturally in both variables, which is the adjunction `j_! ⊣ j^*`.
* `SheafOfModules.dgHomOfDegreeExtendEquiv_isHomComplexDifferential`: **Tag 0FRW** in all
  degrees. The identification of homogeneous homomorphisms of degree `d` of Tag 0FRA matches the
  differentials of the two hom-complexes, so it is an isomorphism of complexes of abelian
  groups, which is what the displayed equality of the source asserts.

## Implementation notes

**What the two sides of the tag are.** `Mod^dg(A, d)` is a differential graded category and the
`Hom` of the source is its hom-complex: degree `d` is the homogeneous homomorphisms of degree
`d` of the underlying graded modules, which are `SheafOfModules.GradedHomOfDegree` of Tag 0FR1,
and the differential is `f ↦ d_N ∘ f - (-1)^d f ∘ d_M`, which is
`SheafOfModules.IsHomComplexDifferential`. The hom-complex is not built as an object, exactly as
in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedExtensionByZero.lean` for Tag 0FRA, where
the graded hom-module is not built either; the identification is stated in each degree together
with the compatibility with the differential, which carries the same information.

**Where the content sits.** The bijection in each degree is the one of Tag 0FRA, which already
knows that the degreewise adjunction of sheaves of modules matches `A`-linear maps with
`A_U`-linear maps. What is proved here is what the source says remains: that the bijection is
compatible with the differentials. That is a consequence of the naturality of the unit of
`j_{U!} ⊣ j_U^*` together with the additivity of `j_U^*`, because the differential of `j_!M` is
`j_!d_M` and the differential of `j^*N` is `j^*d_N`.

**The Leibniz rule for `j_!M`.** The two sides of the rule are bilinear in the pair
`(x, a) ∈ j_!M^n × A^i`, so, as for every law of the extended action, they are compared by
`SheafOfModules.extendedBilinear_ext`: it is enough to check them on the local sections supplied
by the unit, where `SheafOfModules.gradedExtendedAction_unit` turns the extended action into the
action of `M` and the naturality of the unit turns `j_!d` into `d`, leaving the Leibniz rule of
`M` itself. Writing the right-hand side as a single bilinear map is what
`SheafOfModules.bilinearAddZSMul` and `SheafOfModules.bilinearCastTarget` are for; the latter is
needed because the two sides of the rule are indexed by `(n + 1) + i` and `n + i + 1`.

**Base and universes.** As in Tag 0FRA the ringed site is unbundled as a sheaf of commutative
rings `O` on an arbitrary site, with `Stacks.SheafOfModules.Tensor.ringSheaf O` the sheaf of rings
that sheaves of modules are taken over, and the module universe is `max u v m`, which the
extension-by-zero adjunction forces. The restriction of differential graded structures needs no
hypothesis and is stated for an arbitrary sheaf of rings on an arbitrary site.

## References

* [Stacks Project, Tag 0FRW](https://stacks.math.columbia.edu/tag/0FRW)
* [Stacks Project, Tag 0FRA](https://stacks.math.columbia.edu/tag/0FRA)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
* [Stacks Project, Tag 0FR1](https://stacks.math.columbia.edu/tag/0FR1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe m w v u

namespace SheafOfModules

/-! ### Generic auxiliaries on bilinear maps and transports -/

section Generic

universe t a m₁ v₁ u₁

variable {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{t}}
  {P F G : SheafOfModules.{m₁} R}

/-- The sum of a bilinear map with an integer multiple of another. -/
noncomputable def bilinearAddZSMul (b : BilinearMap P F G) (k : ℤ) (c : BilinearMap P F G) :
    BilinearMap P F G where
  app V := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => b.app V x y + k • c.app V x y)
      (fun y y' => by
        rw [map_add (b.app V x), map_add (c.app V x), smul_add]
        abel))
    (fun x x' => AddMonoidHom.ext fun y => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [b.map_add_left, c.map_add_left, smul_add]
      abel)
  map_smul_left V r x y := by
    simp only [AddMonoidHom.mk'_apply]
    rw [b.map_smul_left, c.map_smul_left, smul_add, smul_comm k r]
  map_smul_right V r x y := by
    simp only [AddMonoidHom.mk'_apply]
    rw [b.map_smul_right, c.map_smul_right, smul_add, smul_comm k r]
  naturality {V W} f x y := by
    simp only [AddMonoidHom.mk'_apply]
    rw [map_add, map_zsmul_sections, b.naturality, c.naturality]
    rfl

/-- `bilinearAddZSMul b k c` sends `(x, y)` to `b x y + k • c x y`. -/
@[simp]
theorem bilinearAddZSMul_app (b : BilinearMap P F G) (k : ℤ) (c : BilinearMap P F G) (V : Dᵒᵖ)
    (x : P.val.obj V) (y : F.val.obj V) :
    (bilinearAddZSMul b k c).app V x y = b.app V x y + k • c.app V x y := rfl

/-- The target of a bilinear map, transported along an equality of degrees. -/
noncomputable def bilinearCastTarget (X : ℤ → SheafOfModules.{m₁} R) {i j : ℤ} (h : i = j)
    (b : BilinearMap P F (X i)) : BilinearMap P F (X j) where
  app V := AddMonoidHom.mk' (fun x => (castHom X h V).comp (b.app V x))
    (fun x x' => AddMonoidHom.ext fun y => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.add_apply]
      rw [b.map_add_left, map_add])
  map_smul_left V r x y := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [b.map_smul_left, castHom_smul]
  map_smul_right V r x y := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [b.map_smul_right, castHom_smul]
  naturality {V W} f x y := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [castHom_naturality, b.naturality]
    rfl

/-- `bilinearCastTarget X h b` sends `(x, y)` to the transport of `b x y` along `h`. -/
@[simp]
theorem bilinearCastTarget_app (X : ℤ → SheafOfModules.{m₁} R) {i j : ℤ} (h : i = j)
    (b : BilinearMap P F (X i)) (V : Dᵒᵖ) (x : P.val.obj V) (y : F.val.obj V) :
    (bilinearCastTarget X h b).app V x y = castHom X h V (b.app V x y) := rfl

end Generic

/-! ### Restriction of differential graded structures to a slice site -/

section Restriction

universe t a m₁ v₁ u₁

variable {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{t}}

/-- The restriction `A_U = j^*A` of a sheaf of differential graded algebras to the slice site at
`U`: its homogeneous pieces, multiplication, unit and differential are those of `A` read on the
objects of the slice site. -/
noncomputable def DifferentialGradedAlgebra.over (A : DifferentialGradedAlgebra.{t, a} R)
    (U : D) : DifferentialGradedAlgebra.{t, a} (R.over U) where
  complex := ((overFunctor.{a} R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A.complex
  mul i j :=
    { app V := (A.mul i j).app (op V.unop.left)
      map_smul_left V r x y := (A.mul i j).map_smul_left (op V.unop.left) r x y
      map_smul_right V r x y := (A.mul i j).map_smul_right (op V.unop.left) r x y
      naturality f x y := (A.mul i j).naturality f.unop.left.op x y }
  one := ⟨fun V => A.one.eval (op V.unop.left), fun f => A.one.property f.unop.left.op⟩
  mul_assoc i j k V := A.mul_assoc i j k (op V.unop.left)
  one_mul i V := A.one_mul i (op V.unop.left)
  mul_one i V := A.mul_one i (op V.unop.left)
  leibniz i j V := A.leibniz i j (op V.unop.left)

/-- The degree-`n` piece of `A_U` is the restriction of the degree-`n` piece of `A`. -/
@[simp]
theorem DifferentialGradedAlgebra.over_complex_X (A : DifferentialGradedAlgebra.{t, a} R) (U : D)
    (n : ℤ) : (A.over U).complex.X n = (A.complex.X n).over U := rfl

/-- The differential of `A_U` is the restriction of the differential of `A`. -/
@[simp]
theorem DifferentialGradedAlgebra.over_complex_d (A : DifferentialGradedAlgebra.{t, a} R) (U : D)
    (n i : ℤ) : (A.over U).complex.d n i = (overFunctor.{a} R U).map (A.complex.d n i) := rfl

/-- The multiplication of `A_U` on sections over `V` is that of `A` on sections over the
underlying object of `V`. -/
@[simp]
theorem DifferentialGradedAlgebra.over_mul_app (A : DifferentialGradedAlgebra.{t, a} R) (U : D)
    (i j : ℤ) (V : (Over U)ᵒᵖ) :
    ((A.over U).mul i j).app V = (A.mul i j).app (op V.unop.left) := rfl

/-- The sheaf of graded algebras underlying the restriction of `A` is the restriction of the
sheaf of graded algebras underlying `A`. -/
theorem DifferentialGradedAlgebra.over_toGradedAlgebra (A : DifferentialGradedAlgebra.{t, a} R)
    (U : D) : (A.over U).toGradedAlgebra = A.toGradedAlgebra.over U := rfl

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The restriction `j^*M` of a right differential graded `A`-module to a right differential
graded `A_U`-module. -/
noncomputable def over (M : DifferentialGradedModule.{t, a, m₁} A) (U : D) :
    DifferentialGradedModule.{t, a, m₁} (A.over U) where
  complex := ((overFunctor.{m₁} R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M.complex
  mul n i :=
    { app V := (M.mul n i).app (op V.unop.left)
      map_smul_left V r x y := (M.mul n i).map_smul_left (op V.unop.left) r x y
      map_smul_right V r x y := (M.mul n i).map_smul_right (op V.unop.left) r x y
      naturality f x y := (M.mul n i).naturality f.unop.left.op x y }
  mul_assoc n i j V := M.mul_assoc n i j (op V.unop.left)
  mul_one n V := M.mul_one n (op V.unop.left)
  leibniz n i V := M.leibniz n i (op V.unop.left)

/-- The degree-`n` piece of the restriction of `M` is the restriction of the degree-`n` piece
of `M`. -/
@[simp]
theorem over_complex_X (M : DifferentialGradedModule.{t, a, m₁} A) (U : D) (n : ℤ) :
    (M.over U).complex.X n = (M.complex.X n).over U := rfl

/-- The differential of the restriction of `M` is the restriction of the differential of `M`. -/
@[simp]
theorem over_complex_d (M : DifferentialGradedModule.{t, a, m₁} A) (U : D) (n i : ℤ) :
    (M.over U).complex.d n i = (overFunctor.{m₁} R U).map (M.complex.d n i) := rfl

/-- The action on the restriction of `M` on sections over `V` is that of `M` on sections over
the underlying object of `V`. -/
@[simp]
theorem over_mul_app (M : DifferentialGradedModule.{t, a, m₁} A) (U : D) (n i : ℤ)
    (V : (Over U)ᵒᵖ) : ((M.over U).mul n i).app V = (M.mul n i).app (op V.unop.left) := rfl

/-- The right graded module underlying the restriction of `M` is the restriction of the right
graded module underlying `M`. -/
theorem over_ofDifferentialGraded (M : DifferentialGradedModule.{t, a, m₁} A) (U : D) :
    GradedModule.ofDifferentialGraded (M.over U) =
      (GradedModule.ofDifferentialGraded M).over U := rfl

/-- The restriction of a homomorphism of right differential graded modules to the slice site. -/
noncomputable def overMap {M N : DifferentialGradedModule.{t, a, m₁} A} (f : M ⟶ N) (U : D) :
    M.over U ⟶ N.over U where
  toHomologicalComplex :=
    ((overFunctor.{m₁} R U).mapHomologicalComplex (ComplexShape.up ℤ)).map f.toHomologicalComplex
  map_mul n i V := f.map_mul n i (op V.unop.left)

/-- In each degree, the restriction of `f` is the restriction of the component of `f`. -/
@[simp]
theorem overMap_f {M N : DifferentialGradedModule.{t, a, m₁} A} (f : M ⟶ N) (U : D) (n : ℤ) :
    (overMap f U).toHomologicalComplex.f n =
      (overFunctor.{m₁} R U).map (f.toHomologicalComplex.f n) := rfl

/-- The restriction functor `j^* : Mod^dg(A, d) ⥤ Mod^dg(A_U, d)` on right differential graded
modules. -/
noncomputable def overFunctor (A : DifferentialGradedAlgebra.{t, a} R) (U : D) :
    DifferentialGradedModule.{t, a, m₁} A ⥤ DifferentialGradedModule.{t, a, m₁} (A.over U) where
  obj M := M.over U
  map f := overMap f U
  map_id M := Hom.ext fun n => (SheafOfModules.overFunctor.{m₁} R U).map_id (M.complex.X n)
  map_comp _ _ := Hom.ext fun _ => (SheafOfModules.overFunctor.{m₁} R U).map_comp _ _

/-- The restriction functor sends `M` to its restriction `M.over U`. -/
@[simp]
theorem overFunctor_obj (A : DifferentialGradedAlgebra.{t, a} R) (U : D)
    (M : DifferentialGradedModule.{t, a, m₁} A) :
    (overFunctor.{t, a, m₁} A U).obj M = M.over U := rfl

/-- The restriction functor sends `f` to its restriction `overMap f U`. -/
@[simp]
theorem overFunctor_map (A : DifferentialGradedAlgebra.{t, a} R) (U : D)
    {M N : DifferentialGradedModule.{t, a, m₁} A} (f : M ⟶ N) :
    (overFunctor.{t, a, m₁} A U).map f = overMap f U := rfl

end DifferentialGradedModule

namespace LeftDifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The restriction `N|_U` of a left differential graded `A`-module to a left differential graded
`A_U`-module. -/
noncomputable def over (N : LeftDifferentialGradedModule.{t, a, m₁} A) (U : D) :
    LeftDifferentialGradedModule.{t, a, m₁} (A.over U) where
  complex := ((overFunctor.{m₁} R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.complex
  mul i n :=
    { app V := (N.mul i n).app (op V.unop.left)
      map_smul_left V r x y := (N.mul i n).map_smul_left (op V.unop.left) r x y
      map_smul_right V r x y := (N.mul i n).map_smul_right (op V.unop.left) r x y
      naturality f x y := (N.mul i n).naturality f.unop.left.op x y }
  mul_assoc i j n V := N.mul_assoc i j n (op V.unop.left)
  one_mul n V := N.one_mul n (op V.unop.left)
  leibniz i n V := N.leibniz i n (op V.unop.left)

/-- The degree-`n` piece of the restriction of `N` is the restriction of the degree-`n` piece
of `N`. -/
@[simp]
theorem over_complex_X (N : LeftDifferentialGradedModule.{t, a, m₁} A) (U : D) (n : ℤ) :
    (N.over U).complex.X n = (N.complex.X n).over U := rfl

/-- The differential of the restriction of `N` is the restriction of the differential of `N`. -/
@[simp]
theorem over_complex_d (N : LeftDifferentialGradedModule.{t, a, m₁} A) (U : D) (n i : ℤ) :
    (N.over U).complex.d n i = (overFunctor.{m₁} R U).map (N.complex.d n i) := rfl

/-- The action on the restriction of `N` on sections over `V` is that of `N` on sections over
the underlying object of `V`. -/
@[simp]
theorem over_mul_app (N : LeftDifferentialGradedModule.{t, a, m₁} A) (U : D) (i n : ℤ)
    (V : (Over U)ᵒᵖ) : ((N.over U).mul i n).app V = (N.mul i n).app (op V.unop.left) := rfl

/-- The left graded module underlying the restriction of `N` is the restriction of the left
graded module underlying `N`. -/
theorem over_ofDifferentialGraded (N : LeftDifferentialGradedModule.{t, a, m₁} A) (U : D) :
    LeftGradedModule.ofDifferentialGraded (N.over U) =
      (LeftGradedModule.ofDifferentialGraded N).over U := rfl

/-- The restriction of a homomorphism of left differential graded modules to the slice site. -/
noncomputable def overMap {M N : LeftDifferentialGradedModule.{t, a, m₁} A} (f : M ⟶ N) (U : D) :
    M.over U ⟶ N.over U where
  toHomologicalComplex :=
    ((overFunctor.{m₁} R U).mapHomologicalComplex (ComplexShape.up ℤ)).map f.toHomologicalComplex
  map_mul i n V := f.map_mul i n (op V.unop.left)

/-- In each degree, the restriction of `f` is the restriction of the component of `f`. -/
@[simp]
theorem overMap_f {M N : LeftDifferentialGradedModule.{t, a, m₁} A} (f : M ⟶ N) (U : D) (n : ℤ) :
    (overMap f U).toHomologicalComplex.f n =
      (overFunctor.{m₁} R U).map (f.toHomologicalComplex.f n) := rfl

/-- The restriction functor `j^*` on left differential graded modules. -/
noncomputable def overFunctor (A : DifferentialGradedAlgebra.{t, a} R) (U : D) :
    LeftDifferentialGradedModule.{t, a, m₁} A ⥤
      LeftDifferentialGradedModule.{t, a, m₁} (A.over U) where
  obj N := N.over U
  map f := overMap f U
  map_id N := Hom.ext fun n => (SheafOfModules.overFunctor.{m₁} R U).map_id (N.complex.X n)
  map_comp _ _ := Hom.ext fun _ => (SheafOfModules.overFunctor.{m₁} R U).map_comp _ _

/-- The restriction functor sends `N` to its restriction `N.over U`. -/
@[simp]
theorem overFunctor_obj (A : DifferentialGradedAlgebra.{t, a} R) (U : D)
    (N : LeftDifferentialGradedModule.{t, a, m₁} A) :
    (overFunctor.{t, a, m₁} A U).obj N = N.over U := rfl

/-- The restriction functor sends `f` to its restriction `overMap f U`. -/
@[simp]
theorem overFunctor_map (A : DifferentialGradedAlgebra.{t, a} R) (U : D)
    {M N : LeftDifferentialGradedModule.{t, a, m₁} A} (f : M ⟶ N) :
    (overFunctor.{t, a, m₁} A U).map f = overMap f U := rfl

end LeftDifferentialGradedModule

/-! ### The differential of the hom-complex -/

/-- The differential of a right differential graded module, read as a morphism between the
homogeneous pieces of the underlying graded module. -/
def DifferentialGradedModule.gradedDiff {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m₁} A) (i j : ℤ) :
    (GradedModule.ofDifferentialGraded M).piece i ⟶
      (GradedModule.ofDifferentialGraded M).piece j :=
  M.complex.d i j

/-- `M.gradedDiff i j` is the differential `M.complex.d i j`. -/
@[simp]
theorem DifferentialGradedModule.gradedDiff_eq {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m₁} A) (i j : ℤ) :
    M.gradedDiff i j = M.complex.d i j := rfl

/-- `g` is the differential `d(f) = d_N ∘ f - (-1)^d f ∘ d_M` of the homogeneous homomorphism `f`
of degree `d` of right differential graded modules, written below in diagrammatic order. This
is the differential of the hom-complex of the differential graded category `Mod^dg(A, d)`, whose
degree-`d` term is `SheafOfModules.GradedHomOfDegree` of the underlying graded modules. -/
def IsHomComplexDifferential {A : DifferentialGradedAlgebra.{t, a} R}
    {M N : DifferentialGradedModule.{t, a, m₁} A} {d : ℤ}
    (f : GradedHomOfDegree (GradedModule.ofDifferentialGraded M)
      (GradedModule.ofDifferentialGraded N) d)
    (g : GradedHomOfDegree (GradedModule.ofDifferentialGraded M)
      (GradedModule.ofDifferentialGraded N) (d + 1)) : Prop :=
  ∀ (i j k : ℤ) (hj : i + d = j) (hk : i + (d + 1) = k),
    g.app i k hk = f.app i j hj ≫ N.gradedDiff j k -
      (Int.negOnePow d : ℤ) • (M.gradedDiff i (i + 1) ≫ f.app (i + 1) k (by omega))

end Restriction

/-! ### The extended action and its Leibniz rule -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v m}]
  (O : Sheaf J CommRingCat.{w}) (U : C)
  (A : DifferentialGradedAlgebra.{w, max u v m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))

/-- Extension by zero is additive, so it applies to cochain complexes. -/
instance extendSheaf_additive : (extendSheaf.{m} O U).Additive :=
  have : PreservesBinaryBiproducts (extendSheaf.{m} O U) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

variable (M : DifferentialGradedModule.{w, max u v m, max u v m} (A.over U))

/-- **The right `A`-action on the degreewise extension by zero of a right differential graded
`A_U`-module.** It is the action of Tag 0FRA on the underlying graded modules. -/
noncomputable abbrev dgExtendedAction (n i : ℤ) :
    BilinearMap ((extendSheaf.{m} O U).obj (M.complex.X n)) (A.complex.X i)
      ((extendSheaf.{m} O U).obj (M.complex.X (n + i))) :=
  gradedExtendedAction.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M) n i

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Extension by zero commutes with the unit of `j_{U!} ⊣ j_U^*`:** the extension of a
morphism, evaluated on a local section supplied by the unit, is the unit applied to the image of
that section. -/
theorem extendSheaf_map_unit
    {P Q : SheafOfModules.{max u v m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U)} (φ : P ⟶ Q)
    (W : (Over U)ᵒᵖ) (w : P.val.obj W) :
    ((extendSheaf.{m} O U).map φ).val.app (op W.unop.left)
        (((extendSheafAdjunction.{m} O U).unit.app P).val.app W w) =
      ((extendSheafAdjunction.{m} O U).unit.app Q).val.app W (φ.val.app W w) :=
  congrArg (fun s => s.val.app W w)
    ((extendSheafAdjunction.{m} O U).unit.naturality φ).symm

/-- **The extended action obeys the signed Leibniz rule** for the differential `j_!d` of
`j_!M`. -/
theorem dgExtendedAction_leibniz (n i : ℤ) (V : Cᵒᵖ)
    (x : ((extendSheaf.{m} O U).obj (M.complex.X n)).val.obj V)
    (y : (A.complex.X i).val.obj V) :
    ((extendSheaf.{m} O U).map (M.complex.d (n + i) (n + i + 1))).val.app V
        ((dgExtendedAction.{m} O U A M n i).app V x y) =
      castHom (fun q ↦ (extendSheaf.{m} O U).obj (M.complex.X q)) (add_right_comm n 1 i) V
          ((dgExtendedAction.{m} O U A M (n + 1) i).app V
            (((extendSheaf.{m} O U).map (M.complex.d n (n + 1))).val.app V x) y) +
        (Int.negOnePow n : ℤ) •
          castHom (fun q ↦ (extendSheaf.{m} O U).obj (M.complex.X q)) (add_assoc n i 1).symm V
            ((dgExtendedAction.{m} O U A M n (i + 1)).app V x
              ((A.complex.d i (i + 1)).val.app V y)) := by
  refine extendedBilinear_ext.{m, w, v, u} O U
    (bilinearPostcomp (dgExtendedAction.{m} O U A M n i)
      ((extendSheaf.{m} O U).map (M.complex.d (n + i) (n + i + 1))))
    (bilinearAddZSMul
      (bilinearCastTarget (fun q ↦ (extendSheaf.{m} O U).obj (M.complex.X q))
        (add_right_comm n 1 i)
        (Stacks.BilinearMap.compLeft (dgExtendedAction.{m} O U A M (n + 1) i)
          ((extendSheaf.{m} O U).map (M.complex.d n (n + 1))).val))
      (Int.negOnePow n : ℤ)
      (bilinearCastTarget (fun q ↦ (extendSheaf.{m} O U).obj (M.complex.X q))
        (add_assoc n i 1).symm
        (Stacks.BilinearMap.compRight (dgExtendedAction.{m} O U A M n (i + 1))
          (A.complex.d i (i + 1)).val)))
    ?_ V x y
  intro W z a
  have hact : ∀ (p q : ℤ) (w : (M.complex.X p).val.obj W)
      (b : (A.complex.X q).val.obj (op W.unop.left)),
      (dgExtendedAction.{m} O U A M p q).app (op W.unop.left)
          (((extendSheafAdjunction.{m} O U).unit.app (M.complex.X p)).val.app W w) b =
        ((extendSheafAdjunction.{m} O U).unit.app (M.complex.X (p + q))).val.app W
          ((M.mul p q).app W w b) :=
    fun p q w b => gradedExtendedAction_unit.{m} O U A.toGradedAlgebra
      (GradedModule.ofDifferentialGraded M) p q W w b
  have hadd : ∀ (k : ℤ) (p q : (M.complex.X k).val.obj W),
      ((extendSheafAdjunction.{m} O U).unit.app (M.complex.X k)).val.app W (p + q) =
        ((extendSheafAdjunction.{m} O U).unit.app (M.complex.X k)).val.app W p +
          ((extendSheafAdjunction.{m} O U).unit.app (M.complex.X k)).val.app W q :=
    fun k p q =>
      map_add (homSections ((extendSheafAdjunction.{m} O U).unit.app (M.complex.X k)) W) p q
  have hzsmul : ∀ (k c : ℤ) (p : (M.complex.X k).val.obj W),
      ((extendSheafAdjunction.{m} O U).unit.app (M.complex.X k)).val.app W (c • p) =
        c • ((extendSheafAdjunction.{m} O U).unit.app (M.complex.X k)).val.app W p :=
    fun k c p =>
      map_zsmul (homSections ((extendSheafAdjunction.{m} O U).unit.app (M.complex.X k)) W) c p
  have hcast : ∀ {p q : ℤ} (h : p = q) (w : (M.complex.X p).val.obj W),
      castHom (fun k ↦ (extendSheaf.{m} O U).obj (M.complex.X k)) h (op W.unop.left)
          (((extendSheafAdjunction.{m} O U).unit.app (M.complex.X p)).val.app W w) =
        ((extendSheafAdjunction.{m} O U).unit.app (M.complex.X q)).val.app W
          (gradedCast (fun k ↦ (M.complex.X k).val.obj W) h w) := by
    intro p q h w
    subst h
    rfl
  have key :
      ((extendSheaf.{m} O U).map (M.complex.d (n + i) (n + i + 1))).val.app (op W.unop.left)
          ((dgExtendedAction.{m} O U A M n i).app (op W.unop.left)
            (((extendSheafAdjunction.{m} O U).unit.app (M.complex.X n)).val.app W z) a) =
        castHom (fun q ↦ (extendSheaf.{m} O U).obj (M.complex.X q)) (add_right_comm n 1 i)
            (op W.unop.left)
            ((dgExtendedAction.{m} O U A M (n + 1) i).app (op W.unop.left)
              (((extendSheaf.{m} O U).map (M.complex.d n (n + 1))).val.app (op W.unop.left)
                (((extendSheafAdjunction.{m} O U).unit.app (M.complex.X n)).val.app W z)) a) +
          (Int.negOnePow n : ℤ) •
            castHom (fun q ↦ (extendSheaf.{m} O U).obj (M.complex.X q)) (add_assoc n i 1).symm
              (op W.unop.left)
              ((dgExtendedAction.{m} O U A M n (i + 1)).app (op W.unop.left)
                (((extendSheafAdjunction.{m} O U).unit.app (M.complex.X n)).val.app W z)
                ((A.complex.d i (i + 1)).val.app (op W.unop.left) a)) := by
    rw [hact, extendSheaf_map_unit, extendSheaf_map_unit, hact, hact, hcast, hcast,
      M.leibniz n i W z a, hadd, hzsmul]
    rfl
  exact key

/-- **`j_!M`, the extension by zero of a right differential graded `A_U`-module.** Its
homogeneous pieces are the extensions by zero `j_!(M^n)` of those of `M`, its differential is
`j_!d` and its action is `SheafOfModules.dgExtendedAction`. -/
noncomputable def dgExtensionByZero :
    DifferentialGradedModule.{w, max u v m, max u v m} A where
  complex := ((extendSheaf.{m} O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M.complex
  mul n i := dgExtendedAction.{m} O U A M n i
  mul_assoc := gradedExtendedAction_assoc.{m} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded M)
  mul_one := gradedExtendedAction_one.{m} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded M)
  leibniz n i V x y := by
    have h := dgExtendedAction_leibniz.{m} O U A M n i V x y
    rwa [castHom_apply, castHom_apply] at h

/-- The degree-`n` piece of `j_!M` is the extension by zero of the degree-`n` piece of `M`. -/
@[simp]
theorem dgExtensionByZero_complex_X (n : ℤ) :
    (dgExtensionByZero.{m} O U A M).complex.X n = (extendSheaf.{m} O U).obj (M.complex.X n) :=
  rfl

/-- The differential of `j_!M` is the extension by zero of the differential of `M`. -/
@[simp]
theorem dgExtensionByZero_complex_d (n i : ℤ) :
    (dgExtensionByZero.{m} O U A M).complex.d n i =
      (extendSheaf.{m} O U).map (M.complex.d n i) := rfl

/-- The action on `j_!M` is `SheafOfModules.dgExtendedAction`. -/
@[simp]
theorem dgExtensionByZero_mul (n i : ℤ) :
    (dgExtensionByZero.{m} O U A M).mul n i = dgExtendedAction.{m} O U A M n i := rfl

/-- The right graded module underlying `j_!M` is the extension by zero `j_!` of Tag 0FRA of the
right graded module underlying `M`. -/
theorem dgExtensionByZero_ofDifferentialGraded :
    GradedModule.ofDifferentialGraded (dgExtensionByZero.{m} O U A M) =
      gradedExtensionByZero.{m} O U A.toGradedAlgebra
        (GradedModule.ofDifferentialGraded M) := rfl

/-! ### The functor `j_!` on differential graded modules -/

/-- The extension by zero of a homomorphism of right differential graded `A_U`-modules. -/
noncomputable def dgExtensionByZeroMap
    {M N : DifferentialGradedModule.{w, max u v m, max u v m} (A.over U)} (f : M ⟶ N) :
    dgExtensionByZero.{m} O U A M ⟶ dgExtensionByZero.{m} O U A N where
  toHomologicalComplex :=
    ((extendSheaf.{m} O U).mapHomologicalComplex (ComplexShape.up ℤ)).map f.toHomologicalComplex
  map_mul := gradedExtendedAction_map.{m} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGradedMap f)

/-- In each degree, `j_!f` is the extension by zero of the component of `f`. -/
@[simp]
theorem dgExtensionByZeroMap_f
    {M N : DifferentialGradedModule.{w, max u v m, max u v m} (A.over U)} (f : M ⟶ N) (n : ℤ) :
    (dgExtensionByZeroMap.{m} O U A f).toHomologicalComplex.f n =
      (extendSheaf.{m} O U).map (f.toHomologicalComplex.f n) := rfl

/-- **The functor `j_! : Mod^dg(A_U, d) ⥤ Mod^dg(A, d)`.** -/
noncomputable def dgExtensionByZeroFunctor :
    DifferentialGradedModule.{w, max u v m, max u v m} (A.over U) ⥤
      DifferentialGradedModule.{w, max u v m, max u v m} A where
  obj M := dgExtensionByZero.{m} O U A M
  map f := dgExtensionByZeroMap.{m} O U A f
  map_id M := DifferentialGradedModule.Hom.ext fun n =>
    (extendSheaf.{m} O U).map_id (M.complex.X n)
  map_comp _ _ := DifferentialGradedModule.Hom.ext fun _ =>
    (extendSheaf.{m} O U).map_comp _ _

/-- The functor `j_!` sends `M` to `j_!M`. -/
@[simp]
theorem dgExtensionByZeroFunctor_obj :
    (dgExtensionByZeroFunctor.{m} O U A).obj M = dgExtensionByZero.{m} O U A M := rfl

/-- The functor `j_!` sends `f` to `SheafOfModules.dgExtensionByZeroMap f`. -/
@[simp]
theorem dgExtensionByZeroFunctor_map
    {M N : DifferentialGradedModule.{w, max u v m, max u v m} (A.over U)} (f : M ⟶ N) :
    (dgExtensionByZeroFunctor.{m} O U A).map f = dgExtensionByZeroMap.{m} O U A f := rfl

/-! ### The adjunction `j_! ⊣ j^*`: Tag 0FRW -/

variable {M}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The adjoint of a chain map out of the degreewise extension by zero of a complex is a chain
map. -/
theorem homEquiv_comm
    (K : CochainComplex
      (SheafOfModules.{max u v m} (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U)) ℤ)
    (L : CochainComplex
      (SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ℤ)
    (φ : ∀ n, (extendSheaf.{m} O U).obj (K.X n) ⟶ L.X n)
    (hφ : ∀ i j, φ i ≫ L.d i j = (extendSheaf.{m} O U).map (K.d i j) ≫ φ j) (i j : ℤ) :
    (extendSheafAdjunction.{m} O U).homEquiv (K.X i) (L.X i) (φ i) ≫
        (overFunctor.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).map
          (L.d i j) =
      K.d i j ≫ (extendSheafAdjunction.{m} O U).homEquiv (K.X j) (L.X j) (φ j) := by
  rw [← (extendSheafAdjunction.{m} O U).homEquiv_naturality_right, hφ i j,
    (extendSheafAdjunction.{m} O U).homEquiv_naturality_left]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The adjoint of a chain map into the degreewise restriction of a complex is a chain map. -/
theorem homEquiv_symm_comm
    (K : CochainComplex
      (SheafOfModules.{max u v m} (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U)) ℤ)
    (L : CochainComplex
      (SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ℤ)
    (ψ : ∀ n, K.X n ⟶
      (overFunctor.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).obj (L.X n))
    (hψ : ∀ i j, ψ i ≫
      (overFunctor.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).map
        (L.d i j) =
      K.d i j ≫ ψ j) (i j : ℤ) :
    ((extendSheafAdjunction.{m} O U).homEquiv (K.X i) (L.X i)).symm (ψ i) ≫ L.d i j =
      (extendSheaf.{m} O U).map (K.d i j) ≫
        ((extendSheafAdjunction.{m} O U).homEquiv (K.X j) (L.X j)).symm (ψ j) := by
  rw [← (extendSheafAdjunction.{m} O U).homEquiv_naturality_left_symm, ← hψ i j,
    (extendSheafAdjunction.{m} O U).homEquiv_naturality_right_symm]

/-- The homomorphism `M ⟶ j^*N` of right differential graded `A_U`-modules adjoint to a
homomorphism `j_!M ⟶ N` of right differential graded `A`-modules. -/
noncomputable def dgExtendAdjoint (N : DifferentialGradedModule.{w, max u v m, max u v m} A)
    (f : dgExtensionByZero.{m} O U A M ⟶ N) : M ⟶ N.over U where
  toHomologicalComplex :=
    { f n := (extendSheafAdjunction.{m} O U).homEquiv (M.complex.X n) (N.complex.X n)
        (f.toHomologicalComplex.f n)
      comm' i j _ := homEquiv_comm.{m} O U M.complex N.complex
        (fun n => f.toHomologicalComplex.f n) (fun p q => f.toHomologicalComplex.comm p q) i j }
  map_mul := (gradedExtendAdjoint.{m} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded M) (GradedModule.ofDifferentialGraded N)
    (GradedModule.ofDifferentialGradedMap f)).map_smul

/-- In each degree, the adjoint `M ⟶ j^*N` of `f` is the adjoint of the component of `f` under
`j_{U!} ⊣ j_U^*`. -/
@[simp]
theorem dgExtendAdjoint_f (N : DifferentialGradedModule.{w, max u v m, max u v m} A)
    (f : dgExtensionByZero.{m} O U A M ⟶ N) (n : ℤ) :
    (dgExtendAdjoint.{m} O U A N f).toHomologicalComplex.f n =
      (extendSheafAdjunction.{m} O U).homEquiv (M.complex.X n) (N.complex.X n)
        (f.toHomologicalComplex.f n) := rfl

/-- The homomorphism `j_!M ⟶ N` of right differential graded `A`-modules adjoint to a
homomorphism `M ⟶ j^*N` of right differential graded `A_U`-modules. -/
noncomputable def dgExtendAdjointInv (N : DifferentialGradedModule.{w, max u v m, max u v m} A)
    (f : M ⟶ N.over U) : dgExtensionByZero.{m} O U A M ⟶ N where
  toHomologicalComplex :=
    { f n := ((extendSheafAdjunction.{m} O U).homEquiv (M.complex.X n) (N.complex.X n)).symm
        (f.toHomologicalComplex.f n)
      comm' i j _ := homEquiv_symm_comm.{m} O U M.complex N.complex
        (fun n => f.toHomologicalComplex.f n) (fun p q => f.toHomologicalComplex.comm p q) i j }
  map_mul := (gradedExtendAdjointInv.{m} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded M) (GradedModule.ofDifferentialGraded N)
    (GradedModule.ofDifferentialGradedMap f)).map_smul

/-- In each degree, the adjoint `j_!M ⟶ N` of `f` is the adjoint of the component of `f` under
`j_{U!} ⊣ j_U^*`. -/
@[simp]
theorem dgExtendAdjointInv_f (N : DifferentialGradedModule.{w, max u v m, max u v m} A)
    (f : M ⟶ N.over U) (n : ℤ) :
    (dgExtendAdjointInv.{m} O U A N f).toHomologicalComplex.f n =
      ((extendSheafAdjunction.{m} O U).homEquiv (M.complex.X n) (N.complex.X n)).symm
        (f.toHomologicalComplex.f n) := rfl

/-- **Tag 0FRW in degree zero.** The homomorphisms `j_!M ⟶ N` of right differential graded
`A`-modules are the homomorphisms `M ⟶ j^*N` of right differential graded `A_U`-modules. The
bijection is the degreewise adjunction `j_{U!} ⊣ j_U^*` of ordinary sheaves of modules; the
content is that it matches the `A`-linear chain maps with the `A_U`-linear ones. This is the
degree-zero closed part of the hom-complex identification of the source; the identification in
every degree is `SheafOfModules.dgHomOfDegreeExtendEquiv_isHomComplexDifferential`. -/
@[stacks 0FRW "Hom(j_! M, N) = Hom(M, j^* N) in degree zero"]
noncomputable def dgExtendHomEquiv (N : DifferentialGradedModule.{w, max u v m, max u v m} A) :
    (dgExtensionByZero.{m} O U A M ⟶ N) ≃ (M ⟶ N.over U) where
  toFun f := dgExtendAdjoint.{m} O U A N f
  invFun f := dgExtendAdjointInv.{m} O U A N f
  left_inv f := DifferentialGradedModule.Hom.ext fun n =>
    ((extendSheafAdjunction.{m} O U).homEquiv (M.complex.X n)
      (N.complex.X n)).symm_apply_apply (f.toHomologicalComplex.f n)
  right_inv f := DifferentialGradedModule.Hom.ext fun n =>
    ((extendSheafAdjunction.{m} O U).homEquiv (M.complex.X n)
      (N.complex.X n)).apply_symm_apply (f.toHomologicalComplex.f n)

variable (M)

/-- **Tag 0FRW in degree zero, as an adjunction.** `j_! : Mod^dg(A_U, d) ⥤ Mod^dg(A, d)` is left
adjoint to `j^* : Mod^dg(A, d) ⥤ Mod^dg(A_U, d)`, which is the displayed identification of
Hom-sets of the source together with its naturality in both variables. -/
@[stacks 0FRW "the identification is an adjunction `j_! ⊣ j^*` of differential graded modules"]
noncomputable def dgExtensionByZeroAdjunction :
    dgExtensionByZeroFunctor.{m} O U A ⊣ DifferentialGradedModule.overFunctor A U :=
  Adjunction.mkOfHomEquiv
    { homEquiv _M N := dgExtendHomEquiv.{m} O U A N
      homEquiv_naturality_left_symm g f := DifferentialGradedModule.Hom.ext fun n =>
        (extendSheafAdjunction.{m} O U).homEquiv_naturality_left_symm
          (g.toHomologicalComplex.f n) (f.toHomologicalComplex.f n)
      homEquiv_naturality_right f k := DifferentialGradedModule.Hom.ext fun n =>
        (extendSheafAdjunction.{m} O U).homEquiv_naturality_right
          (f.toHomologicalComplex.f n) (k.toHomologicalComplex.f n) }

/-! ### The hom-complex identification: Tag 0FRW -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The adjunction isomorphism is additive and commutes with integer multiples. -/
theorem homEquiv_sub_zsmul
    {P : SheafOfModules.{max u v m} (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U)}
    {Q : SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)} (c : ℤ)
    (a b : (extendSheaf.{m} O U).obj P ⟶ Q) :
    (extendSheafAdjunction.{m} O U).homEquiv P Q (a - c • b) =
      (extendSheafAdjunction.{m} O U).homEquiv P Q a -
        c • (extendSheafAdjunction.{m} O U).homEquiv P Q b := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_sub, Functor.map_zsmul, Preadditive.comp_sub, Preadditive.comp_zsmul]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The adjunction isomorphism carries the differential of the hom-complex of `(j_!M, N)` to
the differential of the hom-complex of `(M, j^*N)`.** -/
theorem homEquiv_hom_complex_differential
    {P P' : SheafOfModules.{max u v m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U)}
    {Q Q' : SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (c : ℤ)
    (a : (extendSheaf.{m} O U).obj P ⟶ Q) (δ : Q ⟶ Q') (e : P ⟶ P')
    (b : (extendSheaf.{m} O U).obj P' ⟶ Q') :
    (extendSheafAdjunction.{m} O U).homEquiv P Q'
        (a ≫ δ - c • ((extendSheaf.{m} O U).map e ≫ b)) =
      (extendSheafAdjunction.{m} O U).homEquiv P Q a ≫
          (overFunctor.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).map δ -
        c • (e ≫ (extendSheafAdjunction.{m} O U).homEquiv P' Q' b) := by
  rw [homEquiv_sub_zsmul, (extendSheafAdjunction.{m} O U).homEquiv_naturality_right,
    (extendSheafAdjunction.{m} O U).homEquiv_naturality_left]

/-- **Tag 0FRW.** The identification of Tag 0FRA of the homogeneous homomorphisms of degree `d`
out of `j_!M` with those into `j^*N` matches the differentials of the two hom-complexes. Read in
every degree together with `SheafOfModules.gradedHomOfDegreeExtendEquiv` and its naturality, this
is the displayed identification
`Hom_{Mod^dg(A, d)}(j_!M, N) = Hom_{Mod^dg(A_U, d)}(M, j^*N)`
of complexes of abelian groups. -/
@[stacks 0FRW "Hom(j_! M, N) = Hom(M, j^* N) as complexes: compatibility with the differentials"]
theorem dgHomOfDegreeExtendEquiv_isHomComplexDifferential
    (N : DifferentialGradedModule.{w, max u v m, max u v m} A) (d : ℤ)
    (f : GradedHomOfDegree (GradedModule.ofDifferentialGraded (dgExtensionByZero.{m} O U A M))
      (GradedModule.ofDifferentialGraded N) d)
    (g : GradedHomOfDegree (GradedModule.ofDifferentialGraded (dgExtensionByZero.{m} O U A M))
      (GradedModule.ofDifferentialGraded N) (d + 1)) :
    IsHomComplexDifferential f g ↔
      IsHomComplexDifferential (A := A.over U) (M := M) (N := N.over U) (d := d)
        (gradedHomOfDegreeExtendEquiv.{m} (M := GradedModule.ofDifferentialGraded M)
          (N := GradedModule.ofDifferentialGraded N) O U A.toGradedAlgebra d f)
        (gradedHomOfDegreeExtendEquiv.{m} (M := GradedModule.ofDifferentialGraded M)
          (N := GradedModule.ofDifferentialGraded N) O U A.toGradedAlgebra (d + 1) g) := by
  refine ⟨fun h i j k hj hk => ?_, fun h i j k hj hk => ?_⟩ <;>
  have e := homEquiv_hom_complex_differential.{m} O U (Int.negOnePow d : ℤ) (f.app i j hj)
    (N.complex.d j k) (M.complex.d i (i + 1)) (f.app (i + 1) k (by omega))
  · exact (congrArg ((extendSheafAdjunction.{m} O U).homEquiv (M.complex.X i) (N.complex.X k))
      (h i j k hj hk)).trans e
  · exact ((extendSheafAdjunction.{m} O U).homEquiv (M.complex.X i)
      (N.complex.X k)).injective ((h i j k hj hk).trans e.symm)

end SheafOfModules

end
