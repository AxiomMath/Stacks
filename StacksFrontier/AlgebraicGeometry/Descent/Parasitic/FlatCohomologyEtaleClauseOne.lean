module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPullback

/-!
# Clause (1) of [Stacks, Tag 0756] at `τ = étale`, and what it gives

Let `B` be a big fppf site, `S` a scheme below its cutoff and `𝒢` a sheaf of `𝒪`-modules on
`(Sch/S)_fppf`.  [Stacks, Tag 0756] is stated for `τ ∈ {Zar, étale}`, and its clause (1) at
`τ = étale` says that the restriction `𝒢|_{S_étale}` is quasi-coherent.  In this development
that restriction is `AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforward` at `.fppf` — the
direct image along `a_S : ((Sch/S)_fppf, 𝒪) ⟶ (S_étale, 𝒪)` — and quasi-coherence on a site is
`CategoryTheory.SheafOfModules.IsQuasicoherentOnSite` of [Stacks, Tag 03DL].

This file proves the one implication that makes clause (1) at `τ = étale` usable by the
`τ = Zar` half of the tag:

```
𝒢|_{S_étale} quasi-coherent   ⟹   𝒢|_{S_Zar} quasi-coherent,
```

that is, clause (1) of 0756 at `τ = étale` implies clause (1) at `τ = Zar`.

Two steps, both already in the tree.  The restriction to the small Zariski site of a
quasi-coherent module on `S_étale` is quasi-coherent, with no hypothesis, by
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`; and restricting `𝒢` to
`S_étale` and then to `S_Zar` is restricting it to `S_Zar`, which is
`AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforwardCompIso` at `.fppf` — the factorization
of `((Sch/S)_fppf, 𝒪) ⟶ (S_Zar, 𝒪_S)` through `(S_étale, 𝒪)`.

## Main results

* `AlgebraicGeometry.BigFppfOver.isQuasicoherent_restrictModule_of_isQuasicoherentOnSite`:
  **clause (1) of [Stacks, Tag 0756] at `τ = étale` implies clause (1) at `τ = Zar`.**

## What the étale half of [Stacks, Tag 0756] still needs

The conclusion of 0756 at `τ = Zar` is proved for every `U` flat and locally of finite
presentation over `S` in
`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologyGeneralBase.lean`
(`AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv`).  The étale half is **not**
proved, and the obstruction is not clause (1) — which is what this file removes — but the
following two, in this order.

* **Clause (2) at `τ = étale` has no canonical map yet.**  The small étale pullback of sheaves
  of modules along a morphism of schemes of the big étale site exists,
  `CategoryTheory.SheafOfModules.pullback` of
  `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing`, and [Stacks, Tag 03LC] part (1)
  there — `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)`
  — holds with no quasi-coherence hypothesis.  What is missing is the étale counterpart of
  `AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso`, which is what turns those into
  the clause's map `g^*_{étale, small}(𝒢|_{S_étale}) ⟶ 𝒢|_{U_étale}`; without it clause (2) at
  `τ = étale` cannot be stated in the development at all, let alone fed to the `τ = Zar` half.

* **The conclusion's right-hand side has no [Stacks, Tag 03DW] on the site it lives on.**  The
  cohomology `H^p(U, 𝒢|_{U_étale})` of the conclusion is cohomology of the size-bounded small
  étale site `AlgebraicGeometry.SmallEtale B.toBigEtaleSite X hX` of [Stacks, Tag 021B], which
  is where `AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforward` lands.  That group is
  defined — the site is essentially small, so
  `Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite` and
  `Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite` supply its `Ext`
  universe and enough injectives at `AddCommGrpCat.{u}` — but the comparison
  `H^p(X, 𝓕) ≅ H^p(X_étale, 𝓕^a)` of [Stacks, Tag 03DW] clause (2) is carried only by
  `AlgebraicGeometry.smallEtaleQuasiCoherentSiteCohomologyAddEquiv`, which is stated on
  Mathlib's unbounded presentation `AlgebraicGeometry.Scheme.smallEtaleTopology`.
  `AlgebraicGeometry.SmallEtale.sheafEquiv` bridges the two presentations for *sheaves* only;
  no comparison of cohomology across them is available, as the module documentation of
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleExtensionReduction.lean`
  also records.  The route through [Stacks, Tag 03YX],
  `AlgebraicGeometry.bigSmallEtaleSheafCohomologyIso`, does not close the gap either: it is
  stated at coefficients `AddCommGrpCat.{u + 1}`, whereas the modules of 0756 give abelian
  sheaves at `AddCommGrpCat.{u}`, and its hypothesis
  `AlgebraicGeometry.smallEtaleInclusion_hasPointwiseLeftKanExtension` is a statement about
  colimits of size `u + 1` that `AddCommGrpCat.{u}` does not have.

**No `@[stacks 0756]` attribute is placed here**, and none should be: what is below is one
implication between the tag's two readings of clause (1), not the tag's conclusion.

## References

* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (G : SheafOfModules.{u} (structureSheaf B S hS))

/-- **Clause (1) of [Stacks, Tag 0756] at `τ = étale` implies clause (1) at `τ = Zar`.**  If the
restriction `𝒢|_{S_étale}` of `𝒢` along `a_S : ((Sch/S)_fppf, 𝒪) ⟶ (S_étale, 𝒪)` is
quasi-coherent on the small étale site, then the restriction `𝒢|_{S_Zar}` of `𝒢` along the
inclusion of the small Zariski site is a quasi-coherent `𝒪_S`-module.

The restriction of a quasi-coherent module on `S_étale` to the small Zariski site of `S` is
quasi-coherent by `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`, which needs no
hypothesis; and that restriction *is* `𝒢|_{S_Zar}`, because the morphism of ringed sites
`((Sch/S)_fppf, 𝒪) ⟶ (S_Zar, 𝒪_S)` factors through `(S_étale, 𝒪)` —
`AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforwardCompIso`.

So the `τ = Zar` half of [Stacks, Tag 0756],
`AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv`, may be fed the tag's clause (1)
in its étale reading.  Its clause (2) may not: see the module documentation. -/
public theorem isQuasicoherent_restrictModule_of_isQuasicoherentOnSite
    (h : ((smallEtaleToBasePushforward B S hS .fppf).obj G).IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) ((restrictModule B S hS).obj G) :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent S.ringCatSheaf)
    ((smallEtaleToBasePushforwardCompIso B S hS .fppf).app G)
    (SmallEtale.isQuasicoherent_restrictModule B.toBigEtaleSite S hS _ h)

end AlgebraicGeometry.BigFppfOver

end
