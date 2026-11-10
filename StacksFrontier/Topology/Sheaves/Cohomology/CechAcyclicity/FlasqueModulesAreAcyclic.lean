module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Flasque
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Sheaf.Module

/-!
# Flasque sheaves of modules are acyclic

A flasque sheaf of modules on a ringed space is acyclic for the sections functor on every
open subset, including the whole space.

## Main definitions

No new definitions are introduced.

## Main results

* `rightAcyclic_evaluation_of_isFlasque`: a flasque sheaf of modules is right acyclic for
  evaluation on any open subset.

## Implementation notes

The sections functor on an open `U` is Mathlib's `SheafOfModules.evaluation R (op U)`.
Flasqueness is imposed on the underlying presheaf of abelian groups. The statement is made
for any chosen derived categories and right derived functor; in particular it applies to
the standard derived functor supplied by enough injectives.

The argument runs the acyclicity criterion `Functor.le_rightAcyclic` against the class of
flasque sheaves of modules: that class contains an embedding of every object, because an
injective sheaf of modules is flasque by `injective_restriction_surjective`, and it is
stable under the two-out-of-three property for short exact sequences while keeping sections
exact. The space, ring sheaf, and module carriers use a common universe, as in the
project's sheaves of modules and Mathlib's Grothendieck abelian instance for this category.

## References

* [Stacks Project, Tag 09SY](https://stacks.math.columbia.edu/tag/09SY)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u w w'

noncomputable section

namespace Stacks.Cohomology.FlasqueAcyclic

variable {X : Type u} [TopologicalSpace X]
variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Evaluation of sheaves of modules on an object of the site is additive. -/
public instance evaluation_additive (U : (Opens X)ᵒᵖ) :
    (SheafOfModules.evaluation R U).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

variable (F : SheafOfModules R) (U : Opens X)
variable [HasDerivedCategory.{w} (SheafOfModules R)]
variable [HasDerivedCategory.{w'} (ModuleCat (R.obj.obj (op U)))]
variable [((SheafOfModules.evaluation R (op U)).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules R))]

/-- **Stacks 09SY.** A flasque sheaf of modules is acyclic for the derived sections functor
on every open subset. Taking `U = ⊤` gives acyclicity for global sections. -/
@[stacks 09SY, sga "4 V 4.6" "special case"]
public lemma rightAcyclic_evaluation_of_isFlasque
    (hF : TopCat.Presheaf.IsFlasque (X := TopCat.of X)
      ((SheafOfModules.toSheaf R).obj F).obj) :
    (SheafOfModules.evaluation R (op U)).rightAcyclic F := by
  let I : ObjectProperty (SheafOfModules R) := fun G ↦
    TopCat.Presheaf.IsFlasque (X := TopCat.of X)
      ((SheafOfModules.toSheaf R).obj G).obj
  have hI₁ : ∀ G : SheafOfModules R, ∃ H, ∃ (_ : I H), ∃ i : G ⟶ H, Mono i := by
    intro G
    let : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := inferInstance
    obtain ⟨p⟩ := EnoughInjectives.presentation G
    let := p.injective
    exact ⟨p.J, ⟨fun i ↦ (AddCommGrpCat.epi_iff_surjective _).2
      (InjectiveRestriction.injective_restriction_surjective R p.J (leOfHom i.unop))⟩,
      p.f, p.mono⟩
  have hI₂ : ∀ S : ShortComplex (SheafOfModules R), S.ShortExact →
      I S.X₁ → I S.X₂ → I S.X₃ ∧
        (S.map (SheafOfModules.evaluation R (op U))).ShortExact := by
    intro S hS h₁ h₂
    let T : SheafOfModules R ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
      SheafOfModules.toSheaf R
    have : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    let Ttop : SheafOfModules R ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X) := T
    have : Ttop.PreservesZeroMorphisms := show T.PreservesZeroMorphisms from inferInstance
    have : Limits.PreservesFiniteLimits Ttop :=
      show Limits.PreservesFiniteLimits T from inferInstance
    have : Limits.PreservesFiniteColimits Ttop :=
      show Limits.PreservesFiniteColimits T from inferInstance
    let S' := S.map Ttop
    have hS' : S'.ShortExact := hS.map_of_exact Ttop
    let : S'.X₁.IsFlasque := h₁
    let : S'.X₂.IsFlasque := h₂
    have hMap := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (SheafOfModules.evaluation R (op U))).mp inferInstance S hS
    refine ⟨(TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS' : S'.X₃.IsFlasque),
      { exact := hMap.1, mono_f := hMap.2, epi_g := ?_ }⟩
    apply (ModuleCat.epi_iff_surjective _).2
    change Function.Surjective (S'.g.1.app (op U))
    exact (AddCommGrpCat.epi_iff_surjective _).1
      (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS')
  exact Functor.le_rightAcyclic (SheafOfModules.evaluation R (op U)) I hI₁ hI₂ F hF

end Stacks.Cohomology.FlasqueAcyclic

end

end
