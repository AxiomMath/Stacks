module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtRestrictDualTensorEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorArbitrary

/-!
# The derived dual tensor of a perfect object preserves quasi-coherent cohomology

Let `X` be an algebraic space over a scheme `S`, let `E` be a perfect object of `D(𝒪_X)` and let
`K` be an object of `D(𝒪_X)` with quasi-coherent cohomology sheaves. Then the cohomology sheaves
of `E^∨ ⊗^𝐋_{𝒪_X} K` are quasi-coherent.

Two statements about the countability of `Ext` groups,
`AlgebraicGeometry.Space.countable_ext_of_countable_sections_derivedDualTensor` and
`AlgebraicGeometry.Space.countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor`,
carry that conclusion as an explicit hypothesis. This file proves it and restates both with the
hypothesis discharged.

## The route, and why it does not go through Stacks 0A8A

The natural source for the statement is Stacks 0A8A, `R𝓗om(E, K) ∈ D_QCoh` for `E` perfect, whose
carrier `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedSheafHom` would give it through the
duality `R𝓗om(E, K) ≅ E^∨ ⊗^𝐋 K` of Stacks 08JJ. That route is unavailable: both
`qcohDerived_smallEtaleDerivedSheafHom` and its perfect case
`qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect` depend on `sorryAx`, inherited through
`AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedTensor` — the carrier of Stacks 08F5 in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedTensorClosed.lean` — and from there
through Stacks 08F4 and 08DW part (1) down to the affine comparison square of Stacks 08DW part (2).

The route taken here goes through the tensor instead, and through a *different* carrier of
Stacks 08F5: `AlgebraicGeometry.Space.derivedQuasicoherent_derivedTensor`, which proves the same
closure statement for an arbitrary derived tensor product datum on the small étale ringed site by
representing the left factor by a K-flat complex and testing quasi-coherence on the étale charts.
It depends on no `sorryAx`. The derived tensor product
`AlgebraicGeometry.Space.smallEtaleDerivedTensor` is by definition the `tensor` of the canonical
datum `AlgebraicGeometry.Space.smallEtaleDerivedTensorProduct`, so that result applies to it
directly.

The two factors are supplied by:

* `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedDual` (Stacks 08JJ): `E^∨` is perfect;
* `AlgebraicGeometry.Space.qcohDerived_of_isPerfect_derivedCategoryB` (Stacks 08JL): a perfect
  object lies in `D_QCoh`, being pseudo-coherent.

Neither mentions the derived internal Hom's quasi-coherence, so neither touches the poisoned
chain.

## Hypotheses carried

`hqcK` — that `K` itself has quasi-coherent cohomology sheaves — is an **input**, carried by every
declaration here. It is not a residue of the route: the closure statement of Stacks 08F5 needs
both tensor factors to lie in `D_QCoh`, and `K` is arbitrary, so nothing supplies it. It is also
exactly the hypothesis on `K` under which the discharged conclusion is asserted in the first
place; the hypothesis discharged is the one about the tensor product `E^∨ ⊗^𝐋 K`, not the one
about `K`.

Because `hqcK` implies `hqcL`, the two restatements below are **not** generalisations of the
statements they restate: they are those statements read in the case where `K` lies in `D_QCoh`.
Nothing here subsumes the originals, which remain the general form.

`hE` (perfectness of `E`), `hZ`, `hcount`, in the first statement `hXqc` and `hXqs`, and in the
second statement `hUqc` and `hUqs`, are carried unchanged from the two statements being
restated; see their own files.

## Main results

All three are in the namespace `AlgebraicGeometry.Space`.

* `qcohDerived_smallEtaleDerivedTensor_derivedDual_of_isPerfect`: the cohomology sheaves of
  `E^∨ ⊗^𝐋 K` are quasi-coherent.
* `countable_ext_of_countable_sections_derivedDualTensor_of_qcohDerived`: countability of
  `Ext^i(E, K)` over `X`.
* `countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor_of_qcohDerived`: the same
  after restriction along an étale `U → X`.

## References

* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **For `E` perfect and `K` with quasi-coherent cohomology, the cohomology sheaves of
`E^∨ ⊗^𝐋_{𝒪_X} K` are quasi-coherent.**

`E^∨` is perfect by Stacks 08JJ (`AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedDual`) and so
lies in `D_QCoh` by Stacks 08JL
(`AlgebraicGeometry.Space.qcohDerived_of_isPerfect_derivedCategoryB`); `K` lies in `D_QCoh` by
hypothesis; and `D_QCoh` is closed under the derived tensor product by Stacks 08F5, in the form
`AlgebraicGeometry.Space.derivedQuasicoherent_derivedTensor` read at the canonical datum
`AlgebraicGeometry.Space.smallEtaleDerivedTensorProduct`.

The hypothesis `hqcK` is an input: the closure statement needs both factors in `D_QCoh` and `K` is
arbitrary. -/
theorem qcohDerived_smallEtaleDerivedTensor_derivedDual_of_isPerfect
    (X : AlgebraicSpaces B S hS)
    (K E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hqcK : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      K).IsQuasicoherentOnSite) :
    ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      (((smallEtaleDerivedTensor B S hS X).obj
        (smallEtaleDerivedDual B S hS X E)).obj K)).IsQuasicoherentOnSite :=
  derivedQuasicoherent_derivedTensor B S hS X.2 (smallEtaleDerivedTensorProduct B S hS X)
    ⟨smallEtaleDerivedDual B S hS X E,
      qcohDerived_of_isPerfect_derivedCategoryB X _
        (isPerfect_smallEtaleDerivedDual B S hS X E hE)⟩
    ⟨K, hqcK⟩

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **`AlgebraicGeometry.Space.countable_ext_of_countable_sections_derivedDualTensor` with its
quasi-coherence hypothesis discharged.** For `X` quasi-compact and absolutely quasi-separated, `E`
perfect and `K` with quasi-coherent cohomology whose sections over the affine charts are countable
in every degree, every `Ext^i(E, K)` is countable.

The hypothesis on the cohomology of `E^∨ ⊗^𝐋 K` is supplied by
`AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedTensor_derivedDual_of_isPerfect`. The
remaining hypotheses are those of the statement being restated, with `hqcL` replaced by `hqcK`.

Note the logical direction: `hqcK` *implies* `hqcL`, so this is not a generalisation of the
statement it restates — it is that statement read in the case where `K` itself lies in `D_QCoh`,
which is the case `hqcL` was introduced to cover. -/
theorem countable_ext_of_countable_sections_derivedDualTensor_of_qcohDerived
    (X : AlgebraicSpaces B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hqcK : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      K).IsQuasicoherentOnSite)
    (hcount : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
        (((smallEtaleDerivedTensor B S hS X).obj
          (smallEtaleDerivedDual B S hS X E)).obj K)).val.obj (op v)))
    (i : ℤ) :
    Countable (DerivedCategory.Ext E K i) :=
  countable_ext_of_countable_sections_derivedDualTensor B S hS X hZ hXqc hXqs K E hE
    (qcohDerived_smallEtaleDerivedTensor_derivedDual_of_isPerfect B S hS X K E hE hqcK) hcount i

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **`AlgebraicGeometry.Space.countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor`
with its quasi-coherence hypothesis discharged.** Same input, for the restriction of `E` and `K`
along a quasi-compact absolutely quasi-separated étale `U → X`.

The hypothesis on the cohomology of `E^∨ ⊗^𝐋 K` is supplied by
`AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedTensor_derivedDual_of_isPerfect`; `hqcK` on
`K` alone takes its place. -/
theorem countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor_of_qcohDerived
    (X : AlgebraicSpaces B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hqcK : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      K).IsQuasicoherentOnSite)
    (hcount : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
        (((smallEtaleDerivedTensor B S hS X).obj
          (smallEtaleDerivedDual B S hS X E)).obj K)).val.obj (op v)))
    (U : SpacesEtale B S hS X) (hUqc : IsQuasiCompactSpace B S hS U.1.left.1)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1.left.1) (i : ℤ) :
    Countable (DerivedCategory.Ext
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj E)
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj K) i) :=
  countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor B S hS X hZ K E hE
    (qcohDerived_smallEtaleDerivedTensor_derivedDual_of_isPerfect B S hS X K E hE hqcK) hcount
    U hUqc hUqs i

end AlgebraicGeometry.Space

end
