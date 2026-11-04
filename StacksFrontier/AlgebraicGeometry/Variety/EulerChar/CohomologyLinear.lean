module

public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology over a field is linear over the field

Let `f : X ⟶ Spec k` be a scheme over a field. The category of `𝒪_X`-modules is `k`-linear, a
scalar `c ∈ k` acting on a morphism through multiplication by its image in the functions on each
open (`AlgebraicGeometry.modulesLinear`). The functoriality
`AlgebraicGeometry.cohomologyOverFieldMap` of the cohomology `Hⁿ(X, -)` over `k` is linear for
that structure: `Hⁿ(X, c • φ) = c • Hⁿ(X, φ)`.

## Main definitions

* `AlgebraicGeometry.modulesLinearOverField`: the `k`-linear structure on `𝒪_X`-modules.
* `AlgebraicGeometry.unitHomLinearEquivCohomologyZero`: `Hom(𝒪_X, M) ≃ₗ[k] H⁰(X, M)`.

## Main results

* `AlgebraicGeometry.cohomologyOverFieldMap_smul`: `Hⁿ(X, c • φ) = c • Hⁿ(X, φ)`.
* `AlgebraicGeometry.bijective_sections_eval_top`: a global section of a sheaf of modules is its
  value on the whole space.

## Implementation notes

The right derived functors of the global sections functor, valued in modules over `Γ(X, ⊤)`,
are `k`-linear for the `k`-algebra structure of `Γ(X, ⊤)`
(`Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections`), and restricting
scalars to `k` along the same ring map turns that into linearity over `k`.

## References

* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped ModuleCat.Algebra

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The `k`-linear structure on the category of modules on a scheme over `k`: a scalar acts on a
morphism through multiplication by its image in the functions on each open. -/
abbrev modulesLinearOverField : Linear k X.Modules :=
  AlgebraicGeometry.modulesLinear k (Over.mk f)

/-- **Cohomology over a field is `k`-linear**: `Hⁿ(X, c • φ) = c • Hⁿ(X, φ)` for a morphism `φ` of
modules on a scheme over `k`, for the `k`-linear structure `modulesLinearOverField`. -/
theorem cohomologyOverFieldMap_smul (c : k) {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    letI := modulesLinearOverField k f
    cohomologyOverFieldMap k f (c • φ) n = c • cohomologyOverFieldMap k f φ n := by
  let := modulesLinearOverField k f
  let := Stacks.Cohomology.AffineBase.baseSectionsAlgebra k (Over.mk f)
  have h : ((Stacks.Cohomology.AffineBase.moduleGlobalSections (Over.mk f).left).rightDerived
      n).map (c • φ) =
      c • ((Stacks.Cohomology.AffineBase.moduleGlobalSections (Over.mk f).left).rightDerived
        n).map φ :=
    (Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections k (Over.mk f) n).map_smul
      φ c
  unfold cohomologyOverFieldMap
  ext x
  refine (congrArg (fun g => g.hom x) h).trans ?_
  set g := ((Stacks.Cohomology.AffineBase.moduleGlobalSections (Over.mk f).left).rightDerived
    n).map φ
  change (algebraMap k Γ((Over.mk f).left, ⊤) c) • (g.hom x) =
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c) • (g.hom x)
  congr 1

/-- A global section of a sheaf on a scheme is determined by its value on the whole space, and
every element of that value is the value of a global section. -/
theorem bijective_sections_eval_top (M : X.Modules) :
    Function.Bijective (fun s : M.sections => s.val (op ⊤)) := by
  refine ⟨fun s t hst => ?_, fun m => ?_⟩
  · apply Subtype.ext
    funext U
    rw [← s.property (homOfLE (le_top : U.unop ≤ ⊤)).op,
      ← t.property (homOfLE (le_top : U.unop ≤ ⊤)).op]
    exact congrArg _ hst
  · refine ⟨⟨fun U => M.val.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m, ?_⟩, ?_⟩
    · intro U V g
      change (M.val.presheaf.map (homOfLE _).op ≫ M.val.presheaf.map g) m =
        M.val.presheaf.map (homOfLE _).op m
      rw [← CategoryTheory.Functor.map_comp]
      rfl
    · change M.val.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op m = m
      rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id,
        CategoryTheory.Functor.map_id]
      rfl

/-- **Maps out of the structure sheaf are the zeroth cohomology, `k`-linearly.** For a module `M`
on a scheme over `k`, evaluating a map `𝒪_X ⟶ M` at the global section `1` identifies
`Hom(𝒪_X, M)`, with its `k`-linear structure `modulesLinearOverField`, with `H⁰(X, M)`. -/
@[ega "0 5.1.1" "Hom(O_X, special case"]
def unitHomLinearEquivCohomologyZero (M : X.Modules) :
    letI := modulesLinearOverField k f
    ((structureSheafModule X) ⟶ M) ≃ₗ[k] cohomologyOverField k f M 0 := by
  letI := modulesLinearOverField k f
  let ev : ((structureSheafModule X) ⟶ M) → cohomologyOverField k f M 0 :=
    fun g => (cohomologyOverFieldZeroIsoSections k f M).inv.hom
      (g.val.app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op ⊤)))
  have hbij : Function.Bijective ev :=
    (ConcreteCategory.bijective_of_isIso (cohomologyOverFieldZeroIsoSections k f M).inv).comp
      ((bijective_sections_eval_top M).comp M.unitHomEquiv.bijective)
  let L : ((structureSheafModule X) ⟶ M) →ₗ[k]
      cohomologyOverField k f M 0 :=
    { toFun := ev
      map_add' := fun g h => by
        change (cohomologyOverFieldZeroIsoSections k f M).inv.hom
          ((g.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤)) +
            (h.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤))) = _
        exact map_add _ _ _
      map_smul' := fun c g => by
        change (cohomologyOverFieldZeroIsoSections k f M).inv.hom ((g.val.app (op ⊤)).hom
          ((show X.ringCatSheaf.obj.obj (op ⊤) from
            AlgebraicGeometry.baseRingToSections k (Over.mk f) (op ⊤) c) •
              (1 : X.ringCatSheaf.obj.obj (op ⊤)))) =
          c • (cohomologyOverFieldZeroIsoSections k f M).inv.hom
            ((g.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤)))
        have hr : (show X.ringCatSheaf.obj.obj (op ⊤) from
            AlgebraicGeometry.baseRingToSections k (Over.mk f) (op ⊤) c) =
            ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c := by
          change ((forget₂ CommRingCat RingCat).map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫
            X.ringCatSheaf.obj.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op).hom c = _
          rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id,
            CategoryTheory.Functor.map_id]
          rfl
        rw [hr]
        refine (congrArg (cohomologyOverFieldZeroIsoSections k f M).inv.hom
          ((g.val.app (op ⊤)).hom.map_smul _ _)).trans ?_
        exact (cohomologyOverFieldZeroIsoSections k f M).inv.hom.map_smul c _ }
  exact LinearEquiv.ofBijective L hbij

end AlgebraicGeometry

end
