module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClass
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularMeromorphicSectionExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedReduced

/-!
# The Weil divisor class of an invertible module on an integral algebraic space

Let `X` be a locally Noetherian integral algebraic space over a scheme `S`. The three
conditions on `X` under which Stacks 0EPQ produces a regular meromorphic section of an
invertible `𝒪_X`-module hold for such an `X`: the weakly associated points of a reduced
algebraic space are its codimension-zero points (Stacks 0EN1), a locally Noetherian algebraic
space has locally finite irreducible components (Stacks 0GMB), and a decent algebraic space has
a monomorphic field-valued representative at each of its points (Stacks 0BB9). So every
invertible `𝒪_X`-module has a regular meromorphic section, with no condition carried.

## Main definitions

* `AlgebraicGeometry.Space.regularMeromorphicSection` is the regular meromorphic section of an
  invertible `𝒪_X`-module that Stacks 0EPQ produces on such an `X`.

## Main results

* `AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_isIntegralSpace` is **Stacks
  0EPQ** on a locally Noetherian integral algebraic space: every invertible `𝒪_X`-module has a
  regular meromorphic section.
* `AlgebraicGeometry.Space.isRegularMeromorphicSection_regularMeromorphicSection`: the chosen
  meromorphic section is regular.

## References

* [Stacks Project, Tag 0EN1](https://stacks.math.columbia.edu/tag/0EN1)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPW](https://stacks.math.columbia.edu/tag/0EPW)
* [Stacks Project, Tag 0GMB](https://stacks.math.columbia.edu/tag/0GMB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hInt : IsIntegralSpace B S hS X)
variable (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))

include hX hInt hN in
/-- **Stacks 0EPQ.** Every invertible `𝒪_X`-module on a locally Noetherian integral algebraic
space has a regular meromorphic section.

The three conditions of Stacks 0ENA that the source asks for hold here. Condition (a), that
every weakly associated point has codimension zero, is Stacks 0EN1 for the reduced space `X`.
Condition (b), local finiteness of the irreducible components, is Stacks 0GMB for the locally
Noetherian space `X`. Condition (c), representability of the codimension-zero points by
monomorphisms from spectra of fields, holds at every point of the decent space `X` by Stacks
0BB9. The source's own statement, with those three conditions as hypotheses, is
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_isTrivialAtCodimensionZeroPoints`,
which carries the registration of the tag. -/
theorem exists_isRegularMeromorphicSection_of_isIntegralSpace (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    ∃ s : MeromorphicSection.{u, u} B S hS X hX L,
      IsRegularMeromorphicSection.{u, u} B S hS X hX L s :=
  exists_isRegularMeromorphicSection_of_isTrivialAtCodimensionZeroPoints hX
    (fun _ hz => by
      rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
        hInt.hasEtaleLocalProperty_isReduced] at hz)
    (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN)
    (IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints B S hS
      ⟨hInt.isDecentSpace, hInt.finite_irreducibleComponents⟩)
    L hL

/-- The regular meromorphic section of an invertible `𝒪_X`-module on a locally Noetherian
integral algebraic space produced by Stacks 0EPQ. -/
def regularMeromorphicSection (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    MeromorphicSection.{u, u} B S hS X hX L :=
  (exists_isRegularMeromorphicSection_of_isIntegralSpace B S hS hX hInt hN L hL).choose

/-- The meromorphic section of an invertible `𝒪_X`-module chosen by
`AlgebraicGeometry.Space.regularMeromorphicSection` is regular. -/
theorem isRegularMeromorphicSection_regularMeromorphicSection (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    IsRegularMeromorphicSection.{u, u} B S hS X hX L
      (regularMeromorphicSection B S hS hX hInt hN L hL) :=
  (exists_isRegularMeromorphicSection_of_isIntegralSpace B S hS hX hInt hN L hL).choose_spec

end AlgebraicGeometry.Space

end
