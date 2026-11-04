module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.ModuliSpaceSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.KeelMoriTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliSpaceBasics
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuotientSeparatedAbsolute

/-!
# Separation of the Keel–Mori moduli space (Stacks 0DUY)

Let `𝒳` be an algebraic stack whose inertia `I_𝒳 ⟶ 𝒳` is finite and let `f : 𝒳 ⟶ M` be the
moduli space of the Keel–Mori theorem (Stacks 0DUT). If `𝒳` is quasi-separated, so is `M`; if
`𝒳` is separated, so is `M`.

The statement is proved for every categorical moduli space `f : 𝒳 ⟶ M` (Stacks 0DUG). A
categorical moduli space is unique up to a unique isomorphism compatible with the 1-morphisms
(`AlgebraicGeometry.Stack.exists_iso_of_isCategoricalModuliSpace`), so this is the moduli space
constructed in Stacks 0DUT.

The proof is the source's. The only property of the moduli map of Stacks 0DUT that it uses is that
it is a universal homeomorphism, which is part of the conclusion of Stacks 0DUT
(`AlgebraicGeometry.Stack.exists_isUniformCategoricalModuliSpace_of_isFinite_inertia`). For a
universal homeomorphism out of an algebraic stack the two implications are
`isAbsolutelyQuasiSeparated_and_isAbsolutelySeparated_of_universalHomeomorphism` (in the namespace
`AlgebraicGeometry.Stack`): writing `Δ` for the diagonals, `Δ_M ∘ f = (f × f) ∘ Δ_𝒳` with `f × f` a
universal homeomorphism, so `Δ_M` is quasi-compact when `Δ_𝒳` is (Stacks 0AHR, 075S), and
universally closed when `Δ_𝒳` is proper (Stacks 0CQK), whence `M` is separated (Stacks 04Y0, in the
form Stacks 04YS). Both properties cross the isomorphism between the moduli space of Stacks 0DUT
and the given one (`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_iso`,
`AlgebraicGeometry.Space.isAbsolutelySeparated_of_iso`).

## Main results

* `isAbsolutelyQuasiSeparated_and_isAbsolutelySeparated_of_isFinite_inertia`, in the namespace
  `AlgebraicGeometry.Stack`: **Stacks 0DUY**, for every categorical moduli space.

## Implementation notes

Finiteness of the inertia is `AlgebraicGeometry.Stack.AlgebraicStacks.IsFinite` of the inertia
projection (Stacks 04Z2). Quasi-separatedness and separatedness are absolute, i.e. over the
terminal scheme `Spec ℤ`, whose containment in the site is the parameter `hZ`: for `𝒳` they are
`AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelyQuasiSeparated` and
`AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelySeparated` (Stacks 050D parts (8), (7)),
for `M` they are `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` and
`AlgebraicGeometry.Space.IsAbsolutelySeparated` (Stacks 03BS parts (3), (1)), all read through
Construction A of Stacks 04X5 (`AlgebraicGeometry.Space.viewOverIntegers` for spaces). Part (3)
of the source ("Add more here, for example relative versions of the above") asserts nothing.

## References

* [Stacks Project, Tag 0DUY](https://stacks.math.columbia.edu/tag/0DUY)
* [Stacks Project, Tag 0DUT](https://stacks.math.columbia.edu/tag/0DUT)
* [Stacks Project, Tag 0DUG](https://stacks.math.columbia.edu/tag/0DUG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DUY.** Let `𝒳` be an algebraic stack whose inertia `I_𝒳 ⟶ 𝒳` is finite, and let
`f : 𝒳 ⟶ M` be a categorical moduli space — for instance the moduli space constructed in
Stacks 0DUT, which every categorical moduli space of `𝒳` is up to unique isomorphism. Then
1. if `𝒳` is quasi-separated, then `M` is quasi-separated;
2. if `𝒳` is separated, then `M` is separated.

Both properties are absolute, over the terminal scheme `Spec ℤ` (Stacks 050D parts (8), (7) and
Stacks 03BS parts (3), (1)). Part (3) of the source ("Add more here") asserts nothing. -/
@[stacks 0DUY]
theorem isAbsolutelyQuasiSeparated_and_isAbsolutelySeparated_of_isFinite_inertia
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hI : AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (M : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : IsCategoricalModuliSpace B S hS M f.hom) :
    (AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳 →
        Space.IsAbsolutelyQuasiSeparated B S hS hZ M.obj) ∧
      (AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ 𝒳 →
        Space.IsAbsolutelySeparated B S hS hZ M.obj) := by
  obtain ⟨M₀, f₀, hu₀, -, -, hUH₀⟩ :=
    exists_isUniformCategoricalModuliSpace_of_isFinite_inertia B S hS 𝒳 hI
  obtain ⟨e, -⟩ := exists_iso_of_isCategoricalModuliSpace B S hS
    (isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS hu₀) hf
  have h₀ := isAbsolutelyQuasiSeparated_and_isAbsolutelySeparated_of_universalHomeomorphism
    B S hS hZ M₀.property f₀
    (fun 𝒵 k => hUH₀ 𝒵 k (twoFibreProductSquareAlgebraicStacks B S hS k f₀)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k f₀))
  let e' : M.obj ≅ M₀.obj := (ObjectProperty.ι _).mapIso e.symm
  exact ⟨fun h => Space.isAbsolutelyQuasiSeparated_of_iso B S hS hZ M.property e' (h₀.1 h),
    fun h => Space.isAbsolutelySeparated_of_iso B S hS hZ e' (h₀.2 h)⟩

end AlgebraicGeometry.Stack

end
