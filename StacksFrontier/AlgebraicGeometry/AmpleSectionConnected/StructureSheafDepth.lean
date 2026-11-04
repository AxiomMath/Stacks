module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.RingTheory.Depth.AssociatedPrime

/-!
# Depth of the structure sheaf at a point, and its associated points

The stalk of `𝒪_X` regarded as a sheaf of modules over itself is the local ring `𝒪_{X,x}`, as a
module over that ring: this is `Stacks.Ample.unitStalkEquiv`. Two consequences, both
needed to apply the Enriques–Severi–Zariski vanishing theorems [Stacks, Tag 0FD7] and
[Stacks, Tag 0FD8] to `ℱ = 𝒪_X`, whose hypotheses are about the depth of the *module* stalk and
about associated points of the *module*:

* the depth of that module stalk along the maximal ideal is the depth of `𝒪_{X,x}` itself, which
  is what the hypothesis of [Stacks, Tag 0FD9] is stated about;
* a point at which `𝒪_{X,x}` has positive depth is not an associated point of `𝒪_X`.

## Main results

* `Stacks.AmpleSectionConnected.depth_stalk_unit_eq`
* `Stacks.AmpleSectionConnected.notMem_associatedPoints_unit_of_one_le_depth`
* `Stacks.AmpleSectionConnected.two_le_depth_stalk_unit_of_two_le_depth` and
  `Stacks.AmpleSectionConnected.notMem_associatedPoints_unit_of_two_le_depth`: the two shapes
  Tags 0FD8 and 0FD7 ask for, from the `≥ 2` hypothesis Tag 0FD9 supplies.

## Implementation notes

The structure sheaf is written `Stacks.Ample.unitModule X`, which is
`SheafOfModules.unit X.ringCatSheaf` at the `X.Modules` type ascription. The ascription is
load-bearing rather than cosmetic: the module structure on the stalk comes from
`AlgebraicGeometry.Scheme.Modules.moduleStalk`, whose module argument has type `X.Modules`, and
instance search does not unfold `AlgebraicGeometry.Scheme.Modules` to see that the bare
`SheafOfModules.unit X.ringCatSheaf` has that type — so
`Module _ (stalk (SheafOfModules.unit X.ringCatSheaf) x)` fails to synthesize while
`Module _ (stalk (Stacks.Ample.unitModule X) x)` succeeds.

Finiteness of the module stalk, which the depth-versus-associated-primes lemma needs, is
transported along the same linear equivalence from `Module.Finite R R`; no coherence of `𝒪_X`
and hence no Noetherian hypothesis is used here.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AmpleSectionConnected

variable (X : Scheme.{u})

/-- **The depth of the module stalk of `𝒪_X` is the depth of the local ring.** -/
theorem depth_stalk_unit_eq (x : X) :
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) (Stacks.Ample.unitModule X).val.presheaf x) =
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) :=
  Module.depth_eq_depth_of_linearEquiv _ (Stacks.Ample.unitStalkEquiv X x)

/-- **A point where the local ring has positive depth is not an associated point of the
structure sheaf.** -/
theorem notMem_associatedPoints_unit_of_one_le_depth (x : X)
    (h : (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    x ∉ Stacks.Divisors.associatedPoints (Stacks.Ample.unitModule X) := by
  intro hx
  let : Module.Finite (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (Stacks.Ample.unitModule X).val.presheaf x) :=
    Module.Finite.equiv (Stacks.Ample.unitStalkEquiv X x).symm
  exact maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth
    (by rw [depth_stalk_unit_eq]; exact h) hx

section Tag0FD9Hypothesis

variable (hdepth : ∀ x : X, IsClosed ({x} : Set X) → (2 : ℕ∞) ≤
  Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (X.presheaf.stalk x))

include hdepth

/-- **The depth hypothesis of [Stacks, Tag 0FD9], read at the module stalk of `𝒪_X`**, which is
the shape [Stacks, Tag 0FD8] asks for. -/
theorem two_le_depth_stalk_unit_of_two_le_depth (x : X) (hx : IsClosed ({x} : Set X)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) (Stacks.Ample.unitModule X).val.presheaf x) := by
  rw [depth_stalk_unit_eq]
  exact hdepth x hx

/-- **No closed point is an associated point of `𝒪_X`**, which is the shape
[Stacks, Tag 0FD7] asks for. -/
theorem notMem_associatedPoints_unit_of_two_le_depth (x : X) (hx : IsClosed ({x} : Set X)) :
    x ∉ Stacks.Divisors.associatedPoints (Stacks.Ample.unitModule X) :=
  notMem_associatedPoints_unit_of_one_le_depth X x
    (le_trans (by norm_num) (hdepth x hx))

end Tag0FD9Hypothesis

end Stacks.AmpleSectionConnected

end
