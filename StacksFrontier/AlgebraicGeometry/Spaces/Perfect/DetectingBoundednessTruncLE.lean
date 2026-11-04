module

public import StacksFrontier.AlgebraicGeometry.Duality.DetectingBoundedness
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DetectingBoundedBelow
import StacksCore.Tactic.StacksAttribute

/-!
# Truncating above is invisible to a perfect complex in low degrees

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S`, let
`P` be a perfect object of `D(𝒪_X)`, let `E` be an object of `D_QCoh(𝒪_X)` and let `a` be an
integer. [Stacks, Tag 0GFG] says that

1. `Hom_{D(𝒪_X)}(P⟦-i⟧, E) = 0` for `i ≪ 0`, and
2. `Hom_{D(𝒪_X)}(P⟦-i⟧, τ_{≤a}E) = 0` for `i ≪ 0`

are equivalent. It is the `τ_{≤a}` half of the pair of lemmas opening Stacks section 75.29, the
other being [Stacks, Tag 0GFF].

## Main results

* `AlgebraicGeometry.Space.eventually_subsingleton_hom_iff_truncLE_of_isPerfect`:
  [Stacks, Tag 0GFG].

## Implementation notes

**This is an instance of the abstract statement, not a new argument.** The equivalence passes
through the truncation triangle `τ_{≤a}E ⟶ E ⟶ τ_{≥a+1}E ⟶`, and what makes that triangle harmless
is the vanishing of `Hom(P⟦-i⟧, τ_{≥a+1}E)` and of `Hom(P⟦-i⟧, (τ_{≥a+1}E)⟦-1⟧)` for `i ≪ 0`. In
this `τ_{≤a}` direction — unlike in the `τ_{≥a}` direction of [Stacks, Tag 0GFF], where the source
appeals to the Hom-window of [Stacks, Tag 09MB] — that vanishing is pure t-structure
orthogonality: `P⟦-i⟧` is `≤ nP + i` once `P` is `≤ nP`, the two targets are `≥ a + 1` and
`≥ a + 2`, and `nP + i < a + 1` as soon as `i ≤ a - nP`. All of that is
`Stacks.DerivedTruncation.eventually_subsingleton_hom_iff_truncLE`, which carries
[Stacks, Tag 0GEM] and asks only that `P` be bounded above.

So the only geometric input left is that a perfect object of `D(𝒪_X)` is bounded above, which for
an algebraic space with `X` quasi-compact is
`AlgebraicGeometry.Space.exists_isLE_of_isPerfect`. (When [Stacks, Tag 0GEM] was formalized that
bound was not available in the library, which is why its statement there takes the bound as a
hypothesis; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/DetectingBoundedness.lean` record that gap, and for
algebraic spaces it is now closed.)

**Quasi-separatedness of `X` and quasi-coherence of `E` are therefore not consumed.** They are
carried as hypotheses anyway, so that the declaration carrying the tag states the source's lemma
rather than a generalization of it; the binders are underscored to say that the proof does not
read them. A consumer holding less may use
`Stacks.DerivedTruncation.eventually_subsingleton_hom_iff_truncLE` directly.

**The objects.** `𝒪_X`-modules are the sheaves of modules on the small étale ringed site of `X`,
`AlgebraicGeometry.Space.Modules`, at the module universe of the structure rings, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/PerfectHomVanishingWindow.lean`; `P` is perfect in
the sense of [Stacks, Tag 08G5] on that ringed site. Membership of `E` in `D_QCoh(𝒪_X)` is spelled
as quasi-coherence of every cohomology sheaf, which is the membership condition of
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` of [Stacks, Tag 071X]; stating it that way,
rather than with an object of the full subcategory, keeps `τ_{≤a}E` a plain object of `D(𝒪_X)`.
Quasi-separatedness is the absolute notion `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` of
[Stacks, Tag 03BS], which is why the ambient big fppf site is asked to contain the terminal
scheme. Vanishing of a group of morphisms is `Subsingleton` of the morphism type, the category
being preadditive, and "`for i ≪ 0`" is `∃ N : ℤ, ∀ i : ℤ, i ≤ N → _`.

**The model of `D(𝒪_X)`** is `CategoryTheory.HasDerivedCategory.standard`, which is the model at
which `AlgebraicGeometry.Space.exists_isLE_of_isPerfect` is stated.

## References

* [Stacks Project, Tag 0GFG](https://stacks.math.columbia.edu/tag/0GFG)
* [Stacks Project, Tag 0GFF](https://stacks.math.columbia.edu/tag/0GFF)
* [Stacks Project, Tag 0GEM](https://stacks.math.columbia.edu/tag/0GEM)
* [Stacks Project, Tag 09MB](https://stacks.math.columbia.edu/tag/09MB)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- **[Stacks, Tag 0GFG].** Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated
algebraic space over `S`, let `P` be a perfect object of `D(𝒪_X)`, let `E` be an object of
`D_QCoh(𝒪_X)` and let `a` be an integer. Then

1. `Hom_{D(𝒪_X)}(P⟦-i⟧, E) = 0` for `i ≪ 0`, and
2. `Hom_{D(𝒪_X)}(P⟦-i⟧, τ_{≤a}E) = 0` for `i ≪ 0`

are equivalent.

A perfect object on a quasi-compact algebraic space is bounded above
(`AlgebraicGeometry.Space.exists_isLE_of_isPerfect`), and for a `P` bounded above the equivalence
is t-structure orthogonality against the truncation triangle
`τ_{≤a}E ⟶ E ⟶ τ_{≥a+1}E ⟶`, which is
`Stacks.DerivedTruncation.eventually_subsingleton_hom_iff_truncLE`. Quasi-separatedness of `X` and
quasi-coherence of the cohomology sheaves of `E` are hypotheses of the source that this argument
does not read. -/
@[stacks 0GFG]
theorem eventually_subsingleton_hom_iff_truncLE_of_isPerfect
    (hqc : IsQuasiCompactSpace B S hS X)
    (_hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (P : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hP : (smallEtaleRingedSite B S hS X hX).IsPerfect P)
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (_hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj
      E).IsQuasicoherentOnSite)
    (a : ℤ) :
    (∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P⟦-i⟧ ⟶ E)) ↔
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N →
        Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncLE a).obj E) := by
  obtain ⟨nP, hnP⟩ := exists_isLE_of_isPerfect (X := ⟨X, hX⟩) hqc P hP
  exact Stacks.DerivedTruncation.eventually_subsingleton_hom_iff_truncLE nP hnP a

end AlgebraicGeometry.Space

end
