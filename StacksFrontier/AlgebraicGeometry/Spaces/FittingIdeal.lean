module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.RingTheory.Fitting.Basic

/-!
# Fitting ideals of modules on an algebraic space

The `r`-th *Fitting ideal sheaf* of an `𝒪_F`-module on an algebraic space `F` is the smallest
sheaf of ideals of `𝒪_F` whose sections over every affine étale chart contain the
module-theoretic Fitting ideal of the sections of the module over that chart.

## Main definitions

* `AlgebraicGeometry.Space.fittingIdealOnChart` is the module-theoretic Fitting ideal of the
  sections of an `𝒪_F`-module over one étale chart.
* `AlgebraicGeometry.Space.fittingIdeal` is the Fitting ideal sheaf: the infimum of all sheaf
  submodules of `𝒪_F` whose sections contain the chartwise Fitting ideals on affine charts.

## Main results

* `SheafOfModules.Submodule.mem_sInf_obj` computes membership in an infimum of sheaf
  submodules sectionwise.
* `AlgebraicGeometry.Space.fittingIdeal_le` and
  `AlgebraicGeometry.Space.mem_fittingIdeal_of_mem_fittingIdealOnChart` are the two halves of
  the universal property of the Fitting ideal sheaf: it is contained in every sheaf submodule
  containing the chartwise Fitting ideals, and it contains each of them.
* `AlgebraicGeometry.Space.mem_fittingIdeal_iff` is the resulting sectionwise description.

## Implementation notes

A sheaf of ideals of `𝒪_F` is a `SheafOfModules.Submodule` of the unit module
`SheafOfModules.unit` of the structure sheaf; `SheafOfModules.Submodule` is a complete lattice
whose infima are computed sectionwise, which is what makes the generated ideal sheaf a genuine
construction rather than a choice.

The chartwise ideal is only defined once the sections of the module over the chart are a finite
module over the sections of the structure sheaf, so the defining condition of the generated
ideal sheaf is guarded by a `dite` on that hypothesis; `AlgebraicGeometry.Space.fittingIdeal_le`
and `AlgebraicGeometry.Space.mem_fittingIdeal_iff` state the condition in the equivalent
unguarded form, which is what consumers should use.

The structure sheaf of the small étale ringed site is `RingCat`-valued, so the commutativity
needed to speak of an `Ideal` is recovered by `change`-ing to the `CommRingCat`-valued
`AlgebraicGeometry.Space.structureSheaf` it is built from; the two are the same ring.

## References

* [Stacks Project, Tag 0CZ5](https://stacks.math.columbia.edu/tag/0CZ5)
* [Stacks Project, Tag 07Z9](https://stacks.math.columbia.edu/tag/07Z9)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-! ### Sections of an infimum of sheaf submodules -/

namespace Submodule

/-- An infimum of submodules of a sheaf of modules is computed sectionwise: a section lies in
it exactly when it lies in each member. -/
theorem mem_sInf_obj {M : SheafOfModules.{m} R} (s : Set M.Submodule) (X : Cᵒᵖ)
    (x : M.val.obj X) :
    x ∈ (sInf s).toSubmodule.obj X ↔ ∀ N ∈ s, x ∈ N.toSubmodule.obj X := by
  simp [SheafOfModules.Submodule.toSubmodule_sInf, PresheafOfModules.Submodule.sInf_obj]

end Submodule

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The Fitting ideal on one chart -/

/-- The module-theoretic Fitting ideal of the sections of an `𝒪_F`-module over an étale chart
of `F`, as an ideal of the sections of the structure sheaf over that chart.

The ring is the `RingCat`-valued structure sheaf of the small étale ringed site; it is
commutative because it is the `CommRingCat`-valued `AlgebraicGeometry.Space.structureSheaf`
with its commutativity forgotten. -/
noncomputable def fittingIdealOnChart
    (G : Modules.{u, m} B S hS F hF) (r : ℕ) (U : SmallEtale B S hS F)
    [Module.Finite
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U))
      (G.val.obj (op U))] :
    Ideal (((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U)) := by
  let moduleInst : Module
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U))
      (G.val.obj (op U)) := inferInstance
  let finiteInst : Module.Finite
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U))
      (G.val.obj (op U)) := inferInstance
  letI : CommRing
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U)) := by
    change CommRing ((structureSheaf B S hS F hF).obj.obj (op U))
    infer_instance
  letI : Module
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U))
      (G.val.obj (op U)) := moduleInst
  letI : Module.Finite
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U))
      (G.val.obj (op U)) := finiteInst
  exact _root_.fittingIdeal (M := G.val.obj (op U)) (r : ℤ)

/-! ### The Fitting ideal sheaf -/

/-- The `r`-th Fitting ideal sheaf of an `𝒪_F`-module: the smallest sheaf submodule of `𝒪_F`
whose sections over every affine étale chart contain the chartwise Fitting ideal.

It is the infimum of all such sheaf submodules, so it is a construction and not a choice; its
universal property is `AlgebraicGeometry.Space.fittingIdeal_le` together with
`AlgebraicGeometry.Space.mem_fittingIdeal_of_mem_fittingIdealOnChart`. -/
noncomputable def fittingIdeal (G : Modules.{u, m} B S hS F hF) (r : ℕ) :
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).Submodule := by
  classical
  exact sInf { I | ∀ U : SmallEtale B S hS F,
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
    ∀ a, (if h : Module.Finite
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U))
        (G.val.obj (op U)) then
        letI := h
        a ∈ fittingIdealOnChart B S hS F hF G r U
      else False) → a ∈ I.toSubmodule.obj (op U) }

variable {B S hS F hF}

/-- The Fitting ideal sheaf is contained in every sheaf submodule of `𝒪_F` whose sections over
each affine étale chart contain the chartwise Fitting ideal. -/
theorem fittingIdeal_le (G : Modules.{u, m} B S hS F hF) (r : ℕ)
    {I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule}
    (hI : ∀ V : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V) →
      ∀ (b : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op V))
        (_ : Module.Finite
          (((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op V))
          (G.val.obj (op V))),
        b ∈ fittingIdealOnChart B S hS F hF G r V → b ∈ I.toSubmodule.obj (op V)) :
    fittingIdeal B S hS F hF G r ≤ I := by
  refine sInf_le ?_
  intro V hV b hb
  split at hb
  next finiteSections => exact hI V hV b finiteSections hb
  next notFiniteSections => exact hb.elim

/-- Every section of the chartwise Fitting ideal over an affine étale chart is a section of the
Fitting ideal sheaf over that chart. -/
theorem mem_fittingIdeal_of_mem_fittingIdealOnChart (G : Modules.{u, m} B S hS F hF) (r : ℕ)
    (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    [Module.Finite
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U))
      (G.val.obj (op U))]
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U))
    (ha : a ∈ fittingIdealOnChart B S hS F hF G r U) :
    a ∈ (fittingIdeal B S hS F hF G r).toSubmodule.obj (op U) := by
  classical
  refine (SheafOfModules.Submodule.mem_sInf_obj
    (M := SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))) _ (op U) a).mpr ?_
  intro I hI
  exact hI U hU a (by simpa using ⟨‹_›, ha⟩)

/-- A section lies in the Fitting ideal sheaf over a chart exactly when it lies in every sheaf
submodule of `𝒪_F` whose sections over each affine étale chart contain the chartwise Fitting
ideal. -/
theorem mem_fittingIdeal_iff (G : Modules.{u, m} B S hS F hF) (r : ℕ)
    (U : SmallEtale B S hS F)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U)) :
    a ∈ (fittingIdeal B S hS F hF G r).toSubmodule.obj (op U) ↔
      ∀ I : (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O))).Submodule,
        (∀ V : SmallEtale B S hS F,
          IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V) →
          ∀ (b : ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op V))
            (_ : Module.Finite
              (((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op V))
              (G.val.obj (op V))),
            b ∈ fittingIdealOnChart B S hS F hF G r V → b ∈ I.toSubmodule.obj (op V)) →
        a ∈ I.toSubmodule.obj (op U) := by
  classical
  refine ⟨fun ha I hI ↦ fittingIdeal_le G r hI (op U) ha, fun ha ↦ ha _ fun V hV b h hb ↦ ?_⟩
  have := h
  exact mem_fittingIdeal_of_mem_fittingIdealOnChart G r V hV b hb

end AlgebraicGeometry.Space

end
