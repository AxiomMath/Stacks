module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCech

/-!
# Sections of an extension of the structure sheaf over an affine étale chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let

```
0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒞 ⟶ 0
```

be a short exact sequence of abelian sheaves on the small étale site of `F` whose first term is
the abelian sheaf underlying a quasi-coherent `𝒪_F`-module.  This file proves that the sequence
of sections over an **affine** étale chart is again short exact, that is, that `𝒜(W) ⟶ 𝒞(W)` is
surjective.

Neither `𝒜` nor `𝒞` is asked to be a sheaf of modules.  That is the point.  The sequence from
which [Stacks, Tag 05ZT] builds a first order thickening out of a square-zero extension of the
structure sheaf has a sheaf of *rings* in the middle and the structure sheaf on the right, and a
sheaf of rings is not an `𝒪_F`-module; the first step of that proof is exactly the exactness of
`0 → ℐ(U) → 𝒜(U) → 𝒪_F(U) → 0` for `U` an affine object of the site.  Every surjectivity
statement this tree already has is about a morphism of `𝒪_F`-modules, so none of them applies
to it: `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`,
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian`, and the latter's
unconditional form
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_unconditional` of
`StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart`.

## Main results

* `AlgebraicGeometry.Space.surjective_app_of_shortExact_of_isQuasicoherentOnSite`: **a short
  exact sequence of abelian sheaves on the small étale site whose first term is the abelian
  sheaf underlying a quasi-coherent `𝒪_F`-module is surjective on the sections over an affine
  étale chart**, with no hypothesis.

## Implementation notes

**Where the strength comes from, and why nothing is deferred.**  Three library inputs compose and
none of them is assumed here.

* Cohomology on Sites, Lemma [Stacks, Tag 03F8] — vanishing of the first Čech cohomology of the
  kernel on a cofinal system of coverings makes the last map of a short exact sequence of
  abelian sheaves surjective on sections — is
  `Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology`, stated for an arbitrary
  site and an arbitrary short exact sequence of abelian sheaves.  It is *not* a statement about
  sheaves of modules, which is what makes the generalisation below cost nothing: the module
  hypothesis in the existing consumers of 03F8 on this site comes from the way they produce the
  short exact sequence, as the kernel sequence of an epimorphism of modules, and not from 03F8.
* The cofinality of the finite affine covering families among the covering sieves of an affine
  chart is `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_univ`,
  resting on the dense-subsite theorem [Stacks, Tag 04JS].
* The Čech vanishing itself is
  `AlgebraicGeometry.Space.isZero_cechCohomology_succ_of_isQuasicoherentOnSite` of
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing`, which carries **no
  hypothesis**: the essential surjectivity input of the transported [Stacks, Tag 03FJ] is
  discharged there by
  `AlgebraicGeometry.Space.exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite`.

The implementation notes of `StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCech`
take `hCech` as a hypothesis.  That hypothesis is discharged in the library, and this file
does not re-discharge it: it is the `p = 1` case of
`isZero_cechCohomology_succ_of_isQuasicoherentOnSite` after quasi-coherence is traded for
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` by Descent, Proposition [Stacks, Tag 03DX]
(2), and the module-valued conclusion that follows from it is already proved as
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_unconditional`, by the
independent `hEss` route of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromEssSurj`.  Only the
abelian-sheaf conclusion below is new.

**The first term is asked to *be* the abelian sheaf of a quasi-coherent module**, by an equality
hypothesis rather than by an isomorphism, so that the Čech vanishing transports by a rewrite and
no comparison of Čech complexes is performed.  A consumer holding only an isomorphism transports
the conclusion along it instead, the conclusion being a property of `T.g` alone.

**The index universe.**  The covering families are taken at `CategoryTheory.PreZeroHypercover.{u}`,
`u` being the universe of the schemes, because that is the index universe the transported Čech
vanishing is stated at.  No Čech complex is reindexed anywhere: the refinement is produced at
index universe `u` to begin with.  Stacks 03F8 is applied at explicit universes
`.{u, u, u + 1, u}` — index universe of the families, morphisms of the site, objects of the
site, coefficients — since left implicit the coefficient universe is still a metavariable when
`CategoryTheory.HasSheafify` is synthesized and instance search solves it at `u + 1`.

**No `@[stacks 03DW]` and no `@[stacks 05ZT]` attribute is claimed.**  The conclusion here is a
*consequence* of Descent, Proposition 03DW on this site and not that proposition, whose content
is the vanishing of the higher étale cohomology of a quasi-coherent module on an affine; and it
is the first step of the proof of [Stacks, Tag 05ZT] and not a clause of that lemma, whose
conclusion is the existence of a first order thickening with a prescribed structure sheaf.  The
thickening predicates are in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order` and the scheme-level construction
[Stacks, Tag 05YV] that the algebraic-space case is assembled from is
`Stacks.Thickenings.squareZeroExtension_realization` of
`StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension`.

*What Tag 05ZT still owes, beyond this first step.*  There is no square-zero extension of the
structure sheaf of an algebraic *space* anywhere in this development — the structure of
`StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension` is for a scheme, and the
spaces-level converse direction, `𝒞_{Z/X} ≅ ker(i^♯)` with that kernel of square zero in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalModuleInverseImageKernel`, supplies
the fields of such a structure without packaging it.  After this first step the source still
builds `U ↦ Spec(𝒜(U))` as an étale functor into affine schemes, extends it over the site by
the scheme-level Tag 05YV, descends it along an étale equivalence relation presentation by
Tag 02WW, and only then passes to an arbitrary base by Tag 05ZN.

*Which of those steps is a blocker, and which is not.*  The descent is available: an arbitrary
algebraic space has an étale equivalence-relation presentation by
`AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace` of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence`, unconditionally, and the
quotient of such a relation is an algebraic space by
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional` of
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional`, which carries
`@[stacks 02WW]` with nothing granted.  **Nor is Tag 04KL over a base needed**: the source builds the ambient space over `Spec ℤ` and applies
Tag 05ZN *there*, with `Y = Y' = B` and the trivial thickening, so only the terminal-base form
of Tag 05ZN is on the path.  That form is
`AlgebraicGeometry.Space.existsUnique_thickeningHom_of_isLocallyRinged_specULiftZ` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RecoveredFromSmallEtaleTerminalBase`, whose
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` argument is discharged there from the
absolute Tag 04KL: over the terminal base the category of algebraic spaces over the base is the
absolute one, so the 2-compatibility with the structure morphisms is an unused hypothesis.  The
Tag 04SG deduction that no declaration performs is needed only for a *general* base, which this
route does not use.

What is missing is therefore twofold.  The construction `U ↦ Spec(𝒜(U))` and its
extension over the site is absent entirely: no declaration anywhere produces an ambient
algebraic space together with a first order thickening from sheaf data, and the scheme-level
Tag 05YV is reachable only through its two public theorems, every helper of its construction
being private.  And the terminal-base Tag 05ZN still takes the locally ringed condition on
`(f_{spaces,étale}, α)` as an argument.  Of Tag 05ZM this development now has the equivalence of
topoi at sheaves of sets (`AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening`), at
sheaves of rings (`AlgebraicGeometry.Space.spacesEtaleRingSheafEquiv_of_isThickening`, carrying
`𝒪_{X'}` to the site of the thickening as
`AlgebraicGeometry.Space.thickeningStructureSheaf`), and the locally ringed clause
(`AlgebraicGeometry.Space.thickeningFundamentalHom_isLocallyRinged` and
`AlgebraicGeometry.Space.thickeningFundamentalHomInverse_isLocallyRinged`, for the comparison of
the equation and its inverse).  That last one does *not* discharge the argument of Tag 05ZN,
which is the cartesian-units-square condition of Tag 04HA on an arbitrary *morphism* of ringed
topoi rather than on that comparison; what is still absent is any
morphism out of the transported sheaf, and the lemma that a surjection of sheaves of rings with
square-zero kernel reflects units, which is what makes the structure map of that morphism a
local homomorphism.

The finite products in the slice over the chart that the Čech complex is built from are derived
from the terminal object of the slice and the pullbacks of the small étale site rather than
assumed, and are not registered as a global instance.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **A short exact sequence of abelian sheaves on the small étale site of an algebraic space
whose first term is the abelian sheaf underlying a quasi-coherent `𝒪_F`-module is surjective on
the sections over an affine étale chart.**

Nothing is asked of the middle and the right-hand term beyond the sheaf condition: they are
arbitrary abelian sheaves, not sheaves of modules.  This is the form in which the first step of
the proof of [Stacks, Tag 05ZT] is used — there the middle term is a sheaf of rings `𝒜`, the
right-hand term is the structure sheaf, the first term is a square-zero ideal quasi-coherent as
an `𝒪_F`-module, and the conclusion is the exactness of `0 → ℐ(U) → 𝒜(U) → 𝒪_F(U) → 0` for `U`
an affine object of the small étale site.

The proof is Cohomology on Sites, Lemma 03F8 applied to the cofinal system of finite affine
covering families of the chart, whose first Čech cohomology group for the first term vanishes
by `AlgebraicGeometry.Space.isZero_cechCohomology_succ_of_isQuasicoherentOnSite`. -/
theorem surjective_app_of_shortExact_of_isQuasicoherentOnSite
    {K : Modules.{u, u} B S hS F hF} (hK : K.IsQuasicoherentOnSite)
    (T : ShortComplex (Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (hT₁ : T.X₁ = (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).obj K)
    (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective
      (((sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).map T.g).app
        (op W)) := by
  have hfl : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have hprod : ∀ E : PreZeroHypercover.{u} W,
      E ∈ {E : PreZeroHypercover.{u} W | Finite E.I₀ ∧
          (∀ i, IsAffine
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
          E.sieve₀ ∈ SmallEtale.topology B S hS F W} →
      ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
        HasProduct fun a ↦ Over.mk (E.f (i a)) := fun _ _ _ _ ↦ inferInstance
  exact Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology.{u, u, u + 1, u}
    (SmallEtale.topology B S hS F) T hT W
    {E : PreZeroHypercover.{u} W | Finite E.I₀ ∧
      (∀ i, IsAffine
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
      E.sieve₀ ∈ SmallEtale.topology B S hS F W}
    (fun _ hE ↦ hE.2.2)
    (fun R hR ↦ SmallEtale.exists_finite_affine_preZeroHypercover_univ W hW R hR) hprod
    (fun E hE ↦ hT₁ ▸ isZero_cechCohomology_succ_of_isQuasicoherentOnSite B S hS F hF K hK W hW
      E hE.1 hE.2.1 hE.2.2 1 one_pos)

end AlgebraicGeometry.Space

end
