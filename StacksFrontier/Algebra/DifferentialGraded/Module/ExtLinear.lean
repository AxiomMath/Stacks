module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Localization.Linear
public import Mathlib.CategoryTheory.Quotient.Linear
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Triangulated
public import StacksCore.Tactic.StacksAttribute

/-! # Morphisms of differential graded modules as modules over the base ring

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. The homomorphisms
between two right differential graded `A`-modules are closed under multiplication by a scalar
of `R`, so the category of differential graded modules is `R`-linear. That structure descends
first to the homotopy category `K(A, d)`, because a scalar multiple of a homotopy is again a
homotopy, and then to the derived category `D(A, d)`, the localization at the
quasi-isomorphisms, because the quasi-isomorphisms admit a left calculus of fractions.

The last of these is the `R`-module structure on
`Ext^n_{D(A, d)}(M, N) = Hom_{D(A, d)}(M, N[n])` used in Tag 0CS5, together with its
characterizing compatibilities: it is bilinear for composition, and the localization functor
is `R`-linear, so the scalar action on a morphism represented by a homomorphism of differential
graded modules is the one induced by that homomorphism.

## Main definitions

* `DifferentialGradedModule.instLinear`: `Mod_{(A, d)}` is `R`-linear.
* `DifferentialGradedModule.instLinearHomotopyCategory`: `K(A, d)` is `R`-linear.
* `DifferentialGradedModule.instLinearDerivedCategory`: `D(A, d)` is `R`-linear.

## Main results

* `DifferentialGradedModule.Hom.smul_toFun`: the scalar multiple of a homomorphism acts on
  elements by the scalar multiple of its underlying map.
* `DifferentialGradedModule.derivedCategoryQ_map_smul`: the localization functor to
  `D(A, d)` is `R`-linear, in the form used downstream: the class of `r • f` is `r` times the
  class of `f`.
* `DifferentialGradedModule.derived_smul_comp` and
  `DifferentialGradedModule.derived_comp_smul`: composition in `D(A, d)` is `R`-bilinear.

## Implementation notes

*Why the scalar action on a homotopy needs no new argument.* A homotopy is a map of right
`A`-modules, that is, a map linear over `A.Aᵐᵒᵖ`, and not an `R`-linear one a priori. It is
nonetheless `R`-linear in the relevant sense because the two actions commute
(`SMulCommClass R A.Aᵐᵒᵖ`, available since the right action of a differential graded algebra on
a module is required to be compatible with the base ring), so `r • h` is again a map of right
`A`-modules and the homotopy equation is multiplied through by `r`.

*Where the preadditive structure on the derived category comes from.* Mathlib derives one from
a left calculus of fractions, and warns that only one of the two constructions it offers may be
an instance. The quasi-isomorphisms of `K(A, d)` have such a calculus because they are the
multiplicative system attached to the acyclic objects
(`DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions'`), so that construction
is the one in force, and it is the only preadditive structure on `D(A, d)` in this
development.

## References

* [Stacks Project, Tag 0CS5](https://stacks.math.columbia.edu/tag/0CS5)
* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-! ### Differential graded modules -/

/-- The scalar multiple of a homomorphism of differential graded modules by an element of the
base ring: its underlying map is the scalar multiple of the underlying map. -/
def Hom.smul (r : R) {M N : DifferentialGradedModule A} (f : Hom M N) : Hom M N where
  toFun := r • f.toFun
  map_smul x a := by
    simp only [LinearMap.smul_apply, f.map_smul]
    exact smul_comm r (MulOpposite.op a) (f.toFun x)
  map_grading n x hx := (N.grading n).smul_mem r (f.map_grading n x hx)
  map_d := by
    ext x
    have hf := LinearMap.congr_fun f.map_d x
    simp only [LinearMap.comp_apply] at hf ⊢
    simp only [LinearMap.smul_apply, hf]
    exact (N.d.map_smul r (f.toFun x)).symm

/-- The base ring acts on the homomorphisms between two differential graded `A`-modules. -/
instance instSMulHom (M N : DifferentialGradedModule A) : SMul R (Hom M N) :=
  ⟨fun r f => Hom.smul r f⟩

/-- The underlying map of a scalar multiple of a homomorphism of differential graded modules is
the scalar multiple of its underlying map. -/
@[simp]
theorem Hom.smul_toFun (r : R) {M N : DifferentialGradedModule A} (f : Hom M N) :
    (r • f).toFun = r • f.toFun :=
  rfl

/-- The homomorphisms between two differential graded `A`-modules form an `R`-module. -/
instance instModuleHom (M N : DifferentialGradedModule A) : Module R (Hom M N) where
  one_smul f := by ext x; simp
  mul_smul a b f := by ext x; simp [mul_smul]
  smul_zero a := by ext x; simp
  smul_add a f g := by ext x; simp
  add_smul a b f := by ext x; simp [add_smul]
  zero_smul f := by ext x; simp

/-- The category of right differential graded `A`-modules is `R`-linear. -/
instance instLinear : Linear R (DifferentialGradedModule A) where
  homModule := instModuleHom
  smul_comp M N P r f g := by
    refine Hom.ext (LinearMap.ext fun x => ?_)
    exact g.toFun.map_smul r (f.toFun x)
  comp_smul M N P f r g := by
    refine Hom.ext (LinearMap.ext fun x => ?_)
    rfl

/-! ### The homotopy category -/

/-- The scalar multiple of a homotopy, a homotopy between the scalar multiples of the
homomorphisms it connects. -/
def Homotopy.smul (r : R) {M N : DifferentialGradedModule A} {f g : Hom M N}
    (h : Homotopy f g) : Homotopy (r • f) (r • g) where
  toLinearMap := r • h.toLinearMap
  map_grading n x hx := (N.grading (n - 1)).smul_mem r (h.map_grading n x hx)
  homotopy_eq x := by
    have := h.homotopy_eq x
    simp only [Hom.smul_toFun, LinearMap.smul_apply, ← smul_sub, this, smul_add, map_smul]

/-- Homotopy of homomorphisms of differential graded modules is compatible with the action of
the base ring. -/
theorem homotopyRel_smul (r : R) ⦃M N : DifferentialGradedModule A⦄ (f g : M ⟶ N)
    (h : homotopyRel A f g) : homotopyRel A (r • f) (r • g) :=
  ⟨h.some.smul r⟩

/-- The homotopy category of right differential graded `A`-modules is `R`-linear. -/
noncomputable instance instLinearHomotopyCategory : Linear R (HomotopyCategory A) :=
  Quotient.linear R (homotopyRel A) homotopyRel_smul

/-- The quotient functor to the homotopy category is `R`-linear. -/
instance instLinearToHomotopyCategory : (toHomotopyCategory A).Linear R :=
  Quotient.linear_functor R (homotopyRel A) homotopyRel_smul

/-! ### The derived category -/

/-- The derived category of right differential graded `A`-modules is `R`-linear. -/
noncomputable instance instLinearDerivedCategory :
    Linear R ((quasiIsomorphisms' A).Localization) :=
  Localization.linear R (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)

/-- The localization functor to the derived category is `R`-linear. -/
instance instLinearDerivedCategoryQ :
    ((quasiIsomorphisms' A).Q (C := HomotopyCategory A)).Linear R :=
  Localization.functor_linear R (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)

/-- Composition in the derived category is linear over the base ring in its first argument. -/
theorem derived_smul_comp {X Y Z : (quasiIsomorphisms' A).Localization} (r : R) (f : X ⟶ Y)
    (g : Y ⟶ Z) : (r • f) ≫ g = r • (f ≫ g) :=
  Linear.smul_comp (R := R) X Y Z r f g

/-- Composition in the derived category is linear over the base ring in its second argument. -/
theorem derived_comp_smul {X Y Z : (quasiIsomorphisms' A).Localization} (f : X ⟶ Y) (r : R)
    (g : Y ⟶ Z) : f ≫ (r • g) = r • (f ≫ g) :=
  Linear.comp_smul (R := R) X Y Z f r g

/-- The morphism of the derived category represented by a scalar multiple of a homomorphism of
differential graded modules is that scalar multiple of the morphism it represents. -/
theorem derivedCategoryQ_map_smul (r : R) {M N : DifferentialGradedModule A} (f : M ⟶ N) :
    (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map (r • f)) =
      r • (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map f) := by
  rw [(toHomotopyCategory A).map_smul, (quasiIsomorphisms' A).Q.map_smul]

end DifferentialGradedModule

end
