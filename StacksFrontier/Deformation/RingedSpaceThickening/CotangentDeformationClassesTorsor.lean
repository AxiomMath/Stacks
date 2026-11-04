module

public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceNaiveTruncation
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionClasses
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08UZ, clause (2): the isomorphism classes of solutions on the full cotangent complex

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a first order thickening of ringed spaces, let
`f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces, let `𝒢` be an `𝒪_X`-module and let
`c : f^*t^*𝒥 ⟶ 𝒢`. Clause (2) of **Stacks 08UZ** says that if the deformation problem of
**Stacks 08UY** has a solution, then the set of isomorphism classes of solutions is principal
homogeneous under `Ext¹_{𝒪_X}(L_{X/S}, 𝒢)`.

The source's proof: "Via the identification `𝖭𝖫_{X/S} = τ_{≥ -1}L_{X/S}` (**Stacks 08UW**) ...
we have seen part (2) in Deformation Theory, Lemma **08UC**." Both inputs are theorems of the
library: **Stacks 08UC** is
`AlgebraicGeometry.RingedSpaceThickening.solutionClassesAddTorsor`, the principal homogeneous
structure under `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` on the `Quotient` of the solutions by isomorphism, and
the identification `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢) = Ext¹_{𝒪_X}(L_{X/S}, 𝒢)` that **Stacks 08UW** gives
in degree one is `Stacks.Sheaves.RingedSpaceCotangent.naiveExtCotangentAddEquiv`, precomposition
with the canonical map `L_{X/S} ⟶ 𝖭𝖫_{X/S}`. This file transports the first along the second.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.solutionClassesCotangentAddTorsor`: **Stacks 08UZ,
  clause (2)**, as Mathlib's `AddTorsor` under `cotangentExt f G 1`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.solutionClassesCotangentAddTorsor_vsub`: the class in
  `Ext¹_{𝒪_X}(L_{X/S}, 𝒢)` separating the classes of two solutions is their difference class of
  **Stacks 08UC** restricted along `L_{X/S} ⟶ 𝖭𝖫_{X/S}`.

## References

* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ)
* [Stacks Project, Tag 08UY](https://stacks.math.columbia.edu/tag/08UY)
* [Stacks Project, Tag 08UW](https://stacks.math.columbia.edu/tag/08UW)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceCotangent

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local instance] HasDerivedCategory.standard

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

variable (t ht f G c) in
/-- **Stacks Project, Tag 08UZ, clause (2).** If there exists a solution of the deformation
problem of **Stacks 08UY**, then the set of isomorphism classes of solutions is principal
homogeneous under `Ext¹_{𝒪_X}(L_{X/S}, 𝒢)`, as Mathlib's `AddTorsor`.

The set of isomorphism classes is `SolutionClasses t ht f G c`, the `Quotient` of the solutions
by `Isomorphic`. The structure is the one of **Stacks 08UC** (`solutionClassesAddTorsor`) under
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`, read through the identification
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢) = Ext¹_{𝒪_X}(L_{X/S}, 𝒢)` of **Stacks 08UW**
(`naiveExtCotangentAddEquiv`). `hne` is the source's "if there exists a solution". -/
@[stacks 08UZ "clause (2): if a solution of 08UY exists, the set of isomorphism classes of \
solutions is principal homogeneous under Ext¹(L_{X/S}, 𝒢)",
  instance_reducible,
  sga "7 VI 4.16" "more general"]
noncomputable def solutionClassesCotangentAddTorsor
    (hne : Nonempty (DeformationSolution t ht f G c)) :
    AddTorsor (cotangentExt f G 1) (SolutionClasses t ht f G c) :=
  letI := hne
  letI := solutionClassesAddTorsor (t := t) (ht := ht) (f := f) (G := G) (c := c)
  Deformation.ToposThickening.addTorsorCongr (naiveExtCotangentAddEquiv f G le_rfl).symm
    (Equiv.refl _)

/-- **The class separating two isomorphism classes**, in `Ext¹_{𝒪_X}(L_{X/S}, 𝒢)`: the difference
class of **Stacks 08UC** of two representatives, restricted along the canonical map
`L_{X/S} ⟶ 𝖭𝖫_{X/S}`. -/
theorem solutionClassesCotangentAddTorsor_vsub (hne : Nonempty (DeformationSolution t ht f G c))
    (Q₁ Q₂ : DeformationSolution t ht f G c) :
    letI := solutionClassesCotangentAddTorsor t ht f G c hne
    ((⟦Q₁⟧ : SolutionClasses t ht f G c) -ᵥ ⟦Q₂⟧) =
      naiveExtCotangentAddEquiv f G le_rfl (differenceClass Q₁ Q₂) :=
  rfl

end AlgebraicGeometry.RingedSpaceThickening

end
