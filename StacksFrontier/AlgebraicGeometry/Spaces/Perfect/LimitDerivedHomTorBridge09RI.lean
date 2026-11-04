module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomAffineLeafReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomTorBridge

/-!
# Clause (2) of Stacks 09RI with its hypotheses in the spelling of the tag

The pseudo-coherent case of Stacks 09RI is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomAffineLeafReindex.lean` as
`AlgebraicGeometry.Space.DescentSituation.isColim_limitSystem_of_pseudoCoherent`, with its Tor
hypothesis in the spelling Stacks 0DKV carries: `K₀`, read through restriction of scalars along
`𝟙⁻¹𝒪_{X₀} ⟶ 𝒪_{X₀}`, locally has finite Tor dimension.  Clause (2) of the tag asks instead
that `K₀` have finite Tor dimension on the small étale ringed site of `X₀`, which is the
spelling of the second disjunct of the hypothesis `hcase` of
`AlgebraicGeometry.Space.DescentSituation.isHomColimit_of_ringModel`, the statement that carries
the `@[stacks 09RI]` registration.

This file restates the theorem with that hypothesis, the bridge being
`AlgebraicGeometry.Space.hasLocallyFiniteTorDimensionAlong_id_of_hasFiniteTorDimension`.  Finite
Tor dimension implies locally finite Tor dimension, so the registered theorem assumes strictly less
than the tag grants and nothing is assumed that the tag does not give.

## Why this file is the first place clause (2) does any work

In `AlgebraicGeometry.Space.DescentSituation.isHomColimit_of_ringModel`, the statement that
carries the `@[stacks 09RI]` registration, the hypothesis `hcase` is **inert**.  Its proof ends
with `hcase.elim (fun _ => key) (fun _ => key)`, and both branches discard the hypothesis: `key`
is established from the `RingModel` argument alone, and the three predicates of the two
disjuncts — `RingedSite.IsPerfect`, `RingedSite.IsPseudoCoherent` and the `HasFiniteTorDimension`
of `Stacks.SheafOfModules.DerivedTensorProduct` — each occur exactly once in that declaration, in
the binder `hcase` itself and nowhere in the proof.  There is no `hcase.1`, no `hcase.2` and no
case split on it.  So what that theorem proves is that a `RingModel` yields the colimit
statement, with the perfect-versus-pseudo-coherent distinction of the tag playing no part.

That distinction is the mathematical content of Stacks 09RI, and the theorem below is where it is
first used: the pseudo-coherence of `E₀` and the finite Tor dimension of `K₀` are consumed, by way
of Stacks 0DKV, and no ring-translation dictionary is taken as an argument.  Clause (1), the
perfect case, is not an instance of 0DKV — that tag's Tor hypothesis sits on the second argument
and clause (1) has none — and is reduced elsewhere in this tree to a statement at the structure
sheaf over an affine base.

## Main results

* `AlgebraicGeometry.Space.DescentSituation`'s
  `isColim_limitSystem_of_isPseudoCoherent_of_hasFiniteTorDimension`: **the pseudo-coherent case
  of Stacks 09RI**, with the three hypotheses of clause (2) of the tag written out exactly as the
  second disjunct of `hcase` writes them.
* `AlgebraicGeometry.Space.DescentSituation`'s
  `isHomColimit_canonicalDerivedPullbackSystem_of_isPseudoCoherent_of_hasFiniteTorDimension`: the
  same in the `AlgebraicGeometry.Space.DescentSituation.IsHomColimit` form of the tag's
  conclusion.

## What is assumed, and what is not

Nothing beyond clause (2) of the tag and the two restrictions that Stacks 0DKV carries and that
are not negotiable: the index type lies in the universe of the site, `I : Type u`, refuted beyond
it by `StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/Counterexample.lean`; and
`#I < B.cutoff.ord.cof`, refuted beyond it by
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitLargeIndexCounterexample.lean`.

`@[stacks 09RI]` is placed below on the clause (2) statement: it proves the tag's conclusion at
exactly the hypotheses of the tag's second disjunct, and is therefore one half of the covering set,
in the same way that the two halves of Stacks 09RJ's comparison carry the tag separately.  The
other registration is
`AlgebraicGeometry.Space.DescentSituation.isHomColimit_of_ringModel` in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom.lean`, which covers both clauses
of the tag and is untouched; clause (1), `E₀` perfect with `K₀` only in `D_QCoh(𝒪_{X₀})`, is not
proved here and is not a consequence of Stacks 0DKV.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)
  (E₀ K₀ : derivedModules B S hS (D.stage D.base))

/-- **The pseudo-coherent case of Stacks 09RI with its hypotheses written out in the spelling of
the tag.**  This is
`AlgebraicGeometry.Space.DescentSituation.isColim_limitSystem_of_pseudoCoherent` with its three
hypotheses replaced by the second disjunct of the hypothesis `hcase` of
`AlgebraicGeometry.Space.DescentSituation.isHomColimit_of_ringModel`, which is clause (2) of the
tag: `E₀` is a pseudo-coherent object of the small étale ringed site of `X₀`, every cohomology
sheaf of `K₀` is quasi-coherent, and `K₀` has finite Tor dimension.

The Tor hypothesis of Stacks 0DKV, locally finite Tor dimension along the identity, is supplied
by `AlgebraicGeometry.Space.hasLocallyFiniteTorDimensionAlong_id_of_hasFiniteTorDimension`; it
is implied by the tag's, so nothing is assumed that the tag does not give. -/
theorem isColim_limitSystem_of_isPseudoCoherent_of_hasFiniteTorDimension
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (hcase :
      ((smallEtaleRingedSite B S hS (D.stage D.base).obj
          (D.stage D.base).property).IsPseudoCoherent E₀ ∧
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor
          (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property)
            n).obj K₀).IsQuasicoherentOnSite) ∧
        Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T K₀)) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ :=
  isColim_limitSystem_of_isPseudoCoherent_of_isQuasicoherentOnSite D E₀ K₀ hI hcase.1 hcase.2.1
    (hasLocallyFiniteTorDimensionAlong_id_of_hasFiniteTorDimension B S hS (D.stage D.base) T K₀
      hcase.2.2)

/-- **The pseudo-coherent case of Stacks 09RI at the spelling of the tag, in the `IsHomColimit`
form of the tag's conclusion**: `Hom_{D(𝒪_X)}(E, K)` is the filtered colimit of the
`Hom_{D(𝒪_{X_i})}(E_i, K_i)` for the system of derived pullbacks of Situation 09RH with the
canonical comparisons.

This carries `@[stacks 09RI]` for **clause (2) of the tag** — `E₀` pseudo-coherent, every
cohomology sheaf of `K₀` quasi-coherent, `K₀` of finite Tor dimension — at exactly those
hypotheses, which is one half of the tag's covering set.  Clause (1), `E₀` perfect with `K₀` only
in `D_QCoh`, is **not** included here and is not a consequence of Stacks 0DKV.

The two restrictions beyond the tag are counterexample-forced for this formalization, not
conveniences: `I : Type u` is refuted beyond it by
`StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/Counterexample.lean`, and
`#I < B.cutoff.ord.cof` by
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitLargeIndexCounterexample.lean`.  `T`
is the derived tensor product the Tor condition is predicated on, not an added assumption. -/
@[stacks 09RI "clause (2); clause (1) not included"]
theorem isHomColimit_canonicalDerivedPullbackSystem_of_isPseudoCoherent_of_hasFiniteTorDimension
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (hcase :
      ((smallEtaleRingedSite B S hS (D.stage D.base).obj
          (D.stage D.base).property).IsPseudoCoherent E₀ ∧
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor
          (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property)
            n).obj K₀).IsQuasicoherentOnSite) ∧
        Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T K₀)) :
    IsHomColimit D.canonicalDerivedPullbackSystem E₀ K₀ :=
  (isHomColimit_canonicalDerivedPullbackSystem_iff D E₀ K₀).2
    (isColim_limitSystem_of_isPseudoCoherent_of_hasFiniteTorDimension D E₀ K₀ hI T hcase)

end DescentSituation

end AlgebraicGeometry.Space

end
