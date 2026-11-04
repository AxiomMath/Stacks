module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocallyStrictlyPerfectComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.DualOfALocallyFiniteFreeComplex

/-!
# Graded duals of complexes of local direct summands of finite free modules

On a ringed space `X`, a sheaf of `𝒪_X`-modules is locally a direct summand of a finite free
`𝒪_X`-module in two senses: the neighbourhood condition
`Stacks.SheafOfModules.IsLocallyFiniteFreeSummand`, and the sieve condition
`Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree` of the ringed site. This file proves
the two equivalent, and states the graded duality
`Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObject` under the neighbourhood condition
and under local strict perfectness.

## Main results

* `Stacks.SheafOfModules.OnSpace.isLocallyDirectSummandOfFiniteFree_iff`: on a ringed space the
  sieve condition and the neighbourhood condition agree.
* `Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObjectOfLocallyFiniteFreeSummand`: the
  termwise dual of a bounded complex whose terms satisfy the neighbourhood condition is a left
  dual of its underlying graded object.
* `Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObjectOfLocallyStrictlyPerfect`: the same
  for a bounded, locally strictly perfect complex.

## Implementation notes

The statements here are for the underlying graded objects of a bounded complex. The statement
in the monoidal category of complexes, for a locally bounded complex, is
`Stacks.SheafOfModules.OnSpace.exists_exactPairing_ihomUnit_of_isLocallyBounded`.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace CategoryTheory.GradedObject

noncomputable section

universe u

namespace Stacks.SheafOfModules

/-- The isomorphism `free I ≅ free J` of free sheaves of modules induced by a bijection
`I ≃ J` of index types. -/
def freeIsoOfEquiv {D : Type*} [Category* D] {K : GrothendieckTopology D}
    [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R : Sheaf K RingCat.{u}} {I J : Type u} (e : I ≃ J) :
    _root_.SheafOfModules.free (R := R) I ≅ _root_.SheafOfModules.free (R := R) J :=
  _root_.SheafOfModules.freeFunctor.mapIso e.toIso

namespace OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- **The neighbourhood condition implies the sieve condition.** If every point of `X` has an
open neighbourhood on which `F` is a retract of a finite free module, then every open `U` is
covered by such opens. -/
theorem isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand
    (F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) :
    IsLocallyDirectSummandOfFiniteFree X.sheaf.obj (Strict.isSheaf_ringSheaf X.sheaf) F := by
  intro U
  refine ⟨⟨fun V _ => IsFiniteFreeSummandOn X F V,
    fun {_ _} {_} h g => isFiniteFreeSummandOn_of_le X (leOfHom g) h⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨V, hxV, hV⟩ := hF x
    exact ⟨U ⊓ V, homOfLE inf_le_left,
      isFiniteFreeSummandOn_of_le X inf_le_right hV, ⟨hx, hxV⟩⟩
  · intro V _ hV
    obtain ⟨n, hn⟩ := hV
    exact ⟨ULift.{u} (Fin n), inferInstance, hn⟩

/-- **The sieve condition implies the neighbourhood condition.** If every open of `X` is covered
by opens on which `F` is a retract of a finite free module, then every point of `X` has such an
open neighbourhood. -/
theorem isLocallyFiniteFreeSummand_of_isLocallyDirectSummandOfFiniteFree
    (F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyDirectSummandOfFiniteFree X.sheaf.obj
      (Strict.isSheaf_ringSheaf X.sheaf) F) :
    IsLocallyFiniteFreeSummand X F := by
  intro x
  obtain ⟨S, hS, hmem⟩ := hF ⊤
  obtain ⟨V, i, hi, hxV⟩ := hS x (by trivial)
  obtain ⟨I, _, ⟨ρ⟩⟩ := hmem V i hi
  exact ⟨V, hxV, Nat.card I,
    ⟨ρ.trans (Retract.ofIso (freeIsoOfEquiv ((Finite.equivFin I).trans Equiv.ulift.symm)))⟩⟩

/-- On a ringed space, the sieve condition `IsLocallyDirectSummandOfFiniteFree` and the
neighbourhood condition `IsLocallyFiniteFreeSummand` for being locally a direct summand of a
finite free module are equivalent. -/
theorem isLocallyDirectSummandOfFiniteFree_iff
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    IsLocallyDirectSummandOfFiniteFree X.sheaf.obj (Strict.isSheaf_ringSheaf X.sheaf) F ↔
      IsLocallyFiniteFreeSummand X F :=
  ⟨isLocallyFiniteFreeSummand_of_isLocallyDirectSummandOfFiniteFree X F,
    isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand X F⟩

/-- Let `ℱ^•` be a complex of `𝒪_X`-modules vanishing outside a finite set of degrees, each of
whose terms is locally a direct summand of a finite free `𝒪_X`-module in the neighbourhood
sense. Then the termwise dual `𝒢^m = SheafHom(ℱ^{-m}, 𝒪_X)` is a left dual of `ℱ^•` as a graded
`𝒪_X`-module. -/
@[instance_reducible]
def exactPairingDualGradedObjectOfLocallyFiniteFreeSummand
    (F : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (s : Finset ℤ)
    (hbd : ∀ m : ℤ, m ∉ s → IsZero (F.X m))
    (hF : ∀ n : ℤ, IsLocallyFiniteFreeSummand X (F.X n)) :
    @ExactPairing _ _ (Strict.gradedMonoidalCategoryRingSheaf X.sheaf)
      (F.X : GradedObject ℤ (Strict.Mod X.sheaf)) (Strict.dualGradedObject X.sheaf F) :=
  exactPairingDualGradedObject X F s hbd fun n =>
    isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand X (F.X n) (hF n)

/-- Let `ℱ^•` be a complex of `𝒪_X`-modules vanishing outside a finite set of degrees, and let
`X = ⋃ Uᵢ` be an open covering on which each `ℱ^•|_{Uᵢ}` is strictly perfect. Then the termwise
dual `𝒢^m = SheafHom(ℱ^{-m}, 𝒪_X)` is a left dual of `ℱ^•` as a graded `𝒪_X`-module. -/
@[instance_reducible]
def exactPairingDualGradedObjectOfLocallyStrictlyPerfect
    (F : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (s : Finset ℤ)
    (hbd : ∀ m : ℤ, m ∉ s → IsZero (F.X m)) (hF : IsLocallyStrictlyPerfect X F) :
    @ExactPairing _ _ (Strict.gradedMonoidalCategoryRingSheaf X.sheaf)
      (F.X : GradedObject ℤ (Strict.Mod X.sheaf)) (Strict.dualGradedObject X.sheaf F) :=
  exactPairingDualGradedObjectOfLocallyFiniteFreeSummand X F s hbd
    (isLocallyFiniteFreeSummand_of_isLocallyStrictlyPerfect X hF)

end OnSpace

end Stacks.SheafOfModules

end

end
