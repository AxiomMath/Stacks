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
spelling of the second disjunct of the hypothesis `hcase` of Stacks 09RI as it is stated in
`AlgebraicGeometry.Space.DescentSituation.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_of_mk_lt_cof_ord`
of `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomPerfectQcohLeaf.lean`, which
proves both clauses of the tag.

This file restates the theorem with that hypothesis, the bridge being
`AlgebraicGeometry.Space.hasLocallyFiniteTorDimensionAlong_id_of_hasFiniteTorDimension`.  Finite
Tor dimension implies locally finite Tor dimension, so nothing is assumed that clause (2) of the
tag does not give.

## Main results

* `AlgebraicGeometry.Space.DescentSituation`'s
  `isColim_limitSystem_of_isPseudoCoherent_of_hasFiniteTorDimension`: the pseudo-coherent case
  of Stacks 09RI, with the three hypotheses of clause (2) of the tag written out exactly as the
  second disjunct of `hcase` writes them.
* `AlgebraicGeometry.Space.DescentSituation`'s
  `isHomColimit_canonicalDerivedPullbackSystem_of_isPseudoCoherent_of_hasFiniteTorDimension`: the
  same in the `AlgebraicGeometry.Space.DescentSituation.IsHomColimit` form of the tag's
  conclusion.

## Size of the index

As in Stacks 0DKV, the index type lies in the universe of the site, `I : Type u`, refuted beyond
it by `StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/Counterexample.lean`; and
`#I < B.cutoff.ord.cof`, refuted beyond it by
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitLargeIndexCounterexample.lean`.

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
canonical comparisons, when `E₀` is pseudo-coherent, every cohomology sheaf of `K₀` is
quasi-coherent and `K₀` has finite Tor dimension.

`T` is the derived tensor product the Tor condition is predicated on.  Both clauses of the tag
together are
`AlgebraicGeometry.Space.DescentSituation.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_of_mk_lt_cof_ord`. -/
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
