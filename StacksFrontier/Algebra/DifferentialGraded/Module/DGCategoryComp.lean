module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryClosedMaps

/-!
# The category of complexes of the differential graded category of differential graded modules

The category of complexes of a differential graded category has the same objects and the closed
degree-zero homogeneous morphisms as its morphisms. For the differential graded category of right
differential graded `A`-modules a closed degree-zero homogeneous map is exactly a homomorphism of
differential graded modules, so that category of complexes is the ordinary category of right
differential graded `A`-modules.

## Main definitions

* `DifferentialGradedModule.homOfCocycle` and `DifferentialGradedModule.cocycleOfHom`: the two
  translations between closed degree-zero homogeneous maps and homomorphisms of differential
  graded modules, each keeping the underlying linear map.
* `DifferentialGradedModule.compToModules` and `DifferentialGradedModule.modulesToComp`: the
  induced functors.

## Main results

* `DifferentialGradedModule.compModulesEquivalence` and
  `DifferentialGradedModule.dgCategoryCompEquivalence`: the canonical equivalence between the two
  categories, fixing objects and sending a closed degree-zero homogeneous map to the
  homomorphism with the same underlying linear map.

## Implementation notes

The source calls the two categories equal. Their morphism types are not the same type in Lean:
one is a closed homogeneous map, the other a homomorphism of differential graded modules. The
statement is therefore an equivalence of categories bundled with the two formulas pinning it
down — it is the identity on objects and does not change the underlying linear map of a morphism
— rather than the assertion that some equivalence exists.

Both translations are defined so that the underlying linear map is literally copied across, with
no choice and no transport; that is what makes the four functoriality equations and the two unit
and counit isomorphisms hold by reflexivity, and in particular the equivalence is built without
weakening the definitional transparency of the differential graded category.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- A closed degree-zero homogeneous map, read as a homomorphism of differential graded modules
with the same underlying linear map. -/
noncomputable def homOfCocycle {L M : DifferentialGradedModule A}
    (f : (dgCategoryData A).category.Cocycle L M) : Hom L M := by
  have hexists := (homogeneousMapDifferential_eq_zero_iff_exists_hom_shift A L M 0 f.1).mp f.2
  refine ⟨f.1.1, fun x a => f.1.2.2 a x, ?_, ?_⟩
  · intro n x hx
    simpa using f.1.2.1 n x hx
  · ext x
    have hd := LinearMap.congr_fun (Classical.choose hexists).map_d x
    rw [Classical.choose_spec hexists] at hd
    simpa [shift_d, Units.smul_def] using hd

/-- The underlying linear map of `homOfCocycle A f` is that of `f`. -/
@[simp] theorem homOfCocycle_toFun {L M : DifferentialGradedModule A}
    (f : (dgCategoryData A).category.Cocycle L M) :
    (homOfCocycle A f).toFun = f.1.1 := rfl

/-- A homomorphism of differential graded modules, read as a closed degree-zero homogeneous map
with the same underlying linear map. -/
def cocycleOfHom {L M : DifferentialGradedModule A} (f : Hom L M) :
    (dgCategoryData A).category.Cocycle L M :=
  ⟨(⟨f.toFun, fun i x hx => by simpa using f.map_grading i x hx,
      fun a x => f.map_smul x a⟩ : HomogeneousMap A L M 0), by
    apply Subtype.ext
    change M.d ∘ₗ f.toFun - DifferentialGraded.gradedSign R 0 • (f.toFun ∘ₗ L.d) = 0
    rw [DifferentialGraded.gradedSign_zero, one_smul, f.map_d, sub_self]⟩

/-- The underlying linear map of `cocycleOfHom A f` is that of `f`. -/
@[simp] theorem cocycleOfHom_val {L M : DifferentialGradedModule A} (f : Hom L M) :
    (cocycleOfHom A f).1.1 = f.toFun := rfl

/-- Reading a closed degree-zero homogeneous map as a homomorphism of differential graded
modules, as a functor out of the category of complexes. -/
noncomputable def compToModules :
    (dgCategoryData A).category.Comp ⥤ DifferentialGradedModule A where
  obj X := X
  map f := homOfCocycle A f
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext rfl

/-- Reading a homomorphism of differential graded modules as a closed degree-zero homogeneous
map, as a functor into the category of complexes. -/
def modulesToComp :
    DifferentialGradedModule A ⥤ (dgCategoryData A).category.Comp where
  obj X := X
  map f := cocycleOfHom A f
  map_id _ := Subtype.ext (Subtype.ext rfl)
  map_comp _ _ := Subtype.ext (Subtype.ext rfl)

/-- The canonical equivalence between the category of complexes of the differential graded
category of differential graded modules and the category of differential graded modules. -/
noncomputable def compModulesEquivalence :
    (dgCategoryData A).category.Comp ≌ DifferentialGradedModule A where
  functor := compToModules A
  inverse := modulesToComp A
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) fun _ => Subtype.ext (Subtype.ext rfl)
  counitIso := NatIso.ofComponents (fun X => Iso.refl X) fun _ => Hom.ext rfl
  functor_unitIso_comp _ := Hom.ext rfl

/-- The category of complexes of the differential graded category of differential graded modules
is canonically equivalent to the category of differential graded modules: the equivalence is the
identity on objects and does not change the underlying linear map of a morphism. -/
@[stacks 09LC "category_of_complexes"]
noncomputable def dgCategoryCompEquivalence :
    { E : (dgCategoryData A).category.Comp ≌ DifferentialGradedModule A //
      (∀ M : (dgCategoryData A).category.Comp, E.functor.obj M = M) ∧
      (∀ (L M : (dgCategoryData A).category.Comp) (f : L ⟶ M),
        HEq (E.functor.map f).toFun f.1.1) } :=
  ⟨compModulesEquivalence A, fun _ => rfl, fun _ _ _ => HEq.rfl⟩

end DifferentialGradedModule
