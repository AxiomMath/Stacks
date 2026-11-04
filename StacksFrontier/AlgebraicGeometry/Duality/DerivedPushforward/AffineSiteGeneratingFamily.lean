module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensSite
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.WeakGeneration

/-!
# The generating family for `D_QCoh(𝒪_X)` from the affine site

`AlgebraicGeometry.exists_generating_family_qcohCohomology_affineChaotic` produces a generating
family in the sense of [Stacks, Tag 0GYG] on `D_QCoh(X_affine, 𝒪)`, **indexed by a `Type u`**,
for an arbitrary scheme `X : Scheme.{u}` and with no hypothesis. The hypothesis of
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_generating`,
which is the Stacks proof of [Stacks, Tag 0A9E], is such a family on `D_QCoh(𝒪_X)` with index
type in `Type u` as well. This file joins the two across a comparison.

The index universe is the point. On the packaging of the affine site built from the big Zariski
site, `AlgebraicGeometry.smallAffineChaoticRingedSite`, the family of
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_qc_generating_family` is indexed
by a `Type (max (u + 1) w)`, which is strictly too large for the `{ι : Type u}` the 0A9E
statement binds, so no comparison whatever could have fed it. On the `Type u`-small packaging of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensSite.lean` the index type is a `Type u` and
the obstruction is gone.

## Main results

* `AlgebraicGeometry.exists_generating_family_quasiCoherentDerivedCategory_of_adjunction` — **a
  generating family in the sense of [Stacks, Tag 0GYG] for `D_QCoh(𝒪_X)`, indexed by a
  `Type u`**, granted an adjunction `Λ ⊣ Ψ` between `D_QCoh(X_affine, 𝒪)` and `D_QCoh(𝒪_X)`
  whose right adjoint reflects zero objects and preserves countable direct sums.
* `AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_affineSiteAdjunction` —
  the Stacks proof of [Stacks, Tag 0A9E] for a quasi-compact quasi-separated morphism with
  quasi-compact target, with the generating family discharged from the affine site and only that
  adjunction and [Stacks, Tag 08DZ] carried.

## What is carried as a hypothesis, and why

The adjunction. It is the comparison of (1) and (4) of [Stacks, Tag 0GZZ], in the weakest form
that transports a generating family: not an equivalence, only an adjoint pair whose right adjoint
reflects zero objects and commutes with countable direct sums. Mathematically `Ψ` is derived
restriction `Rε_*` to the affine opens and `Λ` is `ε^*`; conservativity of `Ψ` on `D_QCoh(𝒪_X)`
is the vanishing of higher quasi-coherent cohomology on affines, and its commutation with
countable direct sums is the same vanishing.

`ε^*` and the underived `ε_*` for a change of topology are
`Stacks.Cohomology.CompareTopologies.pullback` and `.pushforward`, with their adjunction; the
total right derived functor `Rε_*` on the unbounded derived category is
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward` of
`AlgebraicGeometry.RingedSite.coarseningHom`, and the equivalence the source deduces from it,
the second conclusion of [Stacks, Tag 07A8], is
`Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfLE` — in the chaotic shape
this comparison needs, `derivedPullbackEquivalenceImageOfBot`. Instantiating the latter at the
affine site of a scheme still asks for two things: that the quasi-coherent modules on
`Scheme.affineZariskiRingedSite` form a weak Serre subcategory, and that `H^p_Zar(U, F)` vanish
for `p > 0`, `U` an affine open and `F` such a module.
The comparison of (1) with (3) is available **on derived categories**, with no hypothesis:
`AlgebraicGeometry.Scheme.affineOpensToOpens` is a dense subsite of the site `X.Opens` which
carries `𝒪_X` itself, so the two Stacks steps (1) ≃ (2) ≃ (3) collapse to one, and
`AlgebraicGeometry.Scheme.quasicoherentDerivedAffineOpensEquivalence` is
`D_QCoh(𝒪_X) ≌ D_QCoh(X_{affine, Zar}, 𝒪)`, induced by derived restriction. It does not shorten
the hypothesis below, because the family is produced on the **chaotic** affine site and not on
the Zariski one:
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_qc_generating_family` is stated
for modules over a presheaf of rings on a bare category, and the identification of `QC` with
`D_QCoh` that carries it to `qcohCohomologyProperty` needs `J = ⊥`. What that comparison does is
reduce what is missing to the affine site alone: the change of topology from (3) to (4), which
is where the family lives.

**No `@[stacks]` attribute is attached here.** Tag 0A9E asserts the existence of the right
adjoint for a morphism of quasi-compact quasi-separated schemes with no further hypothesis, and
the second statement below reaches that only modulo the adjunction it carries. That adjunction is
discharged in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensChaoticQuasicoherentEquality.lean`, where
the chain (1) ≃ (2) ≃ (3) ≃ (4) of [Stacks, Tag 0GZZ] is completed into an equivalence onto
`qcohCohomologyProperty` and the tag is registered as
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward`. Tag 0GYG is weak Brown
representability itself, not the production of a family satisfying its hypothesis.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentCohomology

universe u

namespace AlgebraicGeometry

/-- **A generating family in the sense of [Stacks, Tag 0GYG] for `D_QCoh(𝒪_X)`, indexed by a
`Type u`, from a comparison with the affine site.** Let `X` be a scheme and suppose
`Λ ⊣ Ψ` is an adjunction between `D_QCoh(X_affine, 𝒪)` and `D_QCoh(𝒪_X)` in which `Ψ` reflects
zero objects and both functors preserve countable direct sums. Then `D_QCoh(𝒪_X)` carries a
family `E : ι → D_QCoh(𝒪_X)` with `ι : Type u` which detects nonzero objects and through which
morphisms into countable direct sums factor.

The family on the affine site is
`AlgebraicGeometry.exists_generating_family_qcohCohomology_affineChaotic`, which carries no
hypothesis at all, and the transport is
`CategoryTheory.exists_generating_family_of_adjunction`. The index type is a `Type u` because
the affine site is packaged as a `RingedSite.{u, u, u}`; that is what makes the conclusion the
shape the 0A9E statement binds. -/
theorem exists_generating_family_quasiCoherentDerivedCategory_of_adjunction (X : Scheme.{u})
    {Λ : (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory ⥤
        Stacks.Duality.quasiCoherentDerivedCategory X}
    {Ψ : Stacks.Duality.quasiCoherentDerivedCategory X ⥤
        (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory}
    (adj : Λ ⊣ Ψ) [Ψ.PreservesZeroMorphisms]
    [PreservesColimitsOfShape (Discrete ℕ) Ψ] [PreservesColimitsOfShape (Discrete ℕ) Λ]
    (hcons : ∀ K : Stacks.Duality.quasiCoherentDerivedCategory X, IsZero (Ψ.obj K) → IsZero K) :
    ∃ (ι : Type u) (E : ι → Stacks.Duality.quasiCoherentDerivedCategory X),
      (∀ K : Stacks.Duality.quasiCoherentDerivedCategory X, ¬ IsZero K →
          ∃ (i : ι) (g : E i ⟶ K), g ≠ 0) ∧
        ∀ (K : ℕ → Stacks.Duality.quasiCoherentDerivedCategory X) (i : ι) (α : E i ⟶ ∐ K),
          ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ K n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
            α = γ ≫ Limits.Sigma.map β := by
  obtain ⟨ι, E, hE, hE'⟩ := exists_generating_family_qcohCohomology_affineChaotic X
  obtain ⟨h1, h2⟩ :=
    CategoryTheory.exists_generating_family_of_adjunction adj hcons E hE hE'
  exact ⟨ι, _, h1, h2⟩

open Stacks.Duality.DerivedPushforward in
/-- **The Stacks proof of [Stacks, Tag 0A9E] with the generating family discharged from the
affine site.** Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes with `Y`
quasi-compact. If `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with direct sums
([Stacks, Tag 08DZ]) and `D_QCoh(𝒪_X)` admits the comparison with its affine site described in
`AlgebraicGeometry.exists_generating_family_quasiCoherentDerivedCategory_of_adjunction`, then
`Rf_*` has a right adjoint — the twisted inverse image `f^×`.

Compared with
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_generating`
the generating family of [Stacks, Tag 0GYG] is no longer a hypothesis: it is produced, with no
hypothesis, on the `Type u`-small affine site, and transported across the comparison. Two
hypotheses remain, Tag 08DZ and the comparison; see the note of this file. -/
theorem isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_affineSiteAdjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward f
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f))]
    {Λ : (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory ⥤
        Stacks.Duality.quasiCoherentDerivedCategory X}
    {Ψ : Stacks.Duality.quasiCoherentDerivedCategory X ⥤
        (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory}
    (adj : Λ ⊣ Ψ) [Ψ.PreservesZeroMorphisms]
    [PreservesColimitsOfShape (Discrete ℕ) Ψ] [PreservesColimitsOfShape (Discrete ℕ) Λ]
    (hcons : ∀ K : Stacks.Duality.quasiCoherentDerivedCategory X, IsZero (Ψ.obj K) → IsZero K) :
    (Stacks.Duality.quasiCoherentDerivedPushforward f
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).IsLeftAdjoint := by
  obtain ⟨ι, E, hE, hE'⟩ :=
    exists_generating_family_quasiCoherentDerivedCategory_of_adjunction X adj hcons
  exact isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_generating f E hE hE'

end AlgebraicGeometry

end
