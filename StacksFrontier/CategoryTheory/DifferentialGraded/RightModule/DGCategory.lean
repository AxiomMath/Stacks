module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.HomComp

/-!
# The differential graded category of right differential graded modules

The right differential graded modules over a differential graded category `C` over a
commutative ring `R` are themselves the objects of a differential graded category over `R`: the
degree-`p` morphisms are the homogeneous morphisms of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Hom`, the differential is the graded
commutator with the differentials of the two modules, and composition is composition of maps.

Its category of complexes and its homotopy category are then the generic
`DGCategory.Comp` and `DGCategory.K` of Tag 09L7: the ordinary category of right differential
graded `C`-modules has the closed degree-zero morphisms as its morphisms, and the homotopy
category has their homotopy classes.

## Main definitions

* `DGCategory.rightModuleCategory`: the differential graded category `Mod^dg(C)` of right
  differential graded `C`-modules.
* `DGCategory.rightModuleComp` and `DGCategory.rightModuleHomotopyCategory`: its category of
  complexes and its homotopy category.

## Main results

* `DGCategory.rightModuleCategory_obj`, `DGCategory.rightModuleCategory_hom`,
  `DGCategory.rightModuleCategory_d`, `DGCategory.rightModuleCategory_comp` and
  `DGCategory.rightModuleCategory_id`: the objects, the homogeneous morphisms, the
  differential, the composition and the identities, all by definition.

## Implementation notes

The construction is implicitly reducible, as `DifferentialGradedModule.dgCategory` is, so that a
client can synthesize the additive-group and `R`-module instances on the homogeneous morphisms
of the differential graded category directly from the `Submodule` they form.

Nothing beyond the differential graded structure is built here. The additive structure (a zero
module and direct sums), the shift functors and the cones — the hypotheses `DirectSumAxiomA`,
`ShiftAxiomB` and `ConeSituation` under which `DGCategory.homotopyCategory_isTriangulated`
makes the homotopy category triangulated — are separate constructions; the first of them is
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DirectSum`.
-/

@[expose] public section

namespace DGCategory

universe w v u r

variable {R : Type r} [CommRing R]

/-- The differential graded category `Mod^dg(C)` of right differential graded modules over a
differential graded category `C`: a degree-`p` morphism is a family of `R`-linear maps raising
the degree by `p` and commuting with the right action of `C`, the differential is the graded
commutator `d_N ∘ φ - (-1)^p φ ∘ d_M`, and composition is composition of maps. -/
@[implicit_reducible]
def rightModuleCategory (C : DGCategory.{v, u} R) : DGCategory R where
  Obj := RightModule.{w} C
  Hom M N p := RightModule.HomogeneousMap M N p
  addCommGroup _ _ _ := inferInstance
  module _ _ _ := inferInstance
  d := RightModule.homD
  d_add := RightModule.homD_add
  d_smul := RightModule.homD_smul
  d_d := RightModule.homD_homD
  comp h ψ φ := RightModule.homComp h ψ φ
  comp_add_left := RightModule.homComp_add_left
  comp_add_right := RightModule.homComp_add_right
  comp_smul_left := RightModule.homComp_smul_left
  comp_smul_right := RightModule.homComp_smul_right
  leibniz := RightModule.homD_homComp
  assoc := RightModule.homComp_assoc
  id := RightModule.homId
  id_comp := RightModule.homId_homComp
  comp_id := RightModule.homComp_homId
  d_id := RightModule.homD_homId

variable (C : DGCategory.{v, u} R)

/-- The objects of `Mod^dg(C)` are the right differential graded `C`-modules. -/
@[simp] theorem rightModuleCategory_obj :
    (rightModuleCategory.{w} C).Obj = RightModule.{w} C := rfl

/-- The degree-`p` morphisms of `Mod^dg(C)` are the degree-`p` homogeneous morphisms. -/
@[simp] theorem rightModuleCategory_hom (M N : RightModule.{w} C) (p : ℤ) :
    (rightModuleCategory.{w} C).Hom M N p = RightModule.HomogeneousMap M N p := rfl

/-- The differential of `Mod^dg(C)` is the graded commutator with the differentials. -/
theorem rightModuleCategory_d {M N : RightModule.{w} C} {p : ℤ}
    (φ : (rightModuleCategory.{w} C).Hom M N p) :
    (rightModuleCategory.{w} C).d φ = RightModule.homD φ := rfl

/-- Composition in `Mod^dg(C)` is composition of homogeneous morphisms. -/
theorem rightModuleCategory_comp {M N P : RightModule.{w} C} {m n p : ℤ} (h : m + n = p)
    (ψ : (rightModuleCategory.{w} C).Hom N P m) (φ : (rightModuleCategory.{w} C).Hom M N n) :
    (rightModuleCategory.{w} C).comp h ψ φ = RightModule.homComp h ψ φ := rfl

/-- The identities of `Mod^dg(C)` are the identity homogeneous morphisms. -/
theorem rightModuleCategory_id (M : RightModule.{w} C) :
    (rightModuleCategory.{w} C).id M = RightModule.homId M := rfl

/-- The ordinary category of right differential graded `C`-modules: the objects of `Mod^dg(C)`
with its closed degree-zero morphisms, i.e. `Comp(Mod^dg(C))` in the sense of Tag 09L7. -/
abbrev rightModuleComp : Type _ := (rightModuleCategory.{w} C).Comp

/-- The homotopy category of right differential graded `C`-modules: `K(Mod^dg(C))` in the sense
of Tag 09L7, whose morphisms are the homotopy classes of closed degree-zero morphisms. -/
abbrev rightModuleHomotopyCategory : Type _ := (rightModuleCategory.{w} C).K

end DGCategory
