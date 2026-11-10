module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSiteLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingBaseChangeCoefficients
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComparisonAtTheFibreProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOverTheTerminalSlice

/-!
# Čech vanishing on the small étale site of an algebraic space, for base-change coefficients

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `W` be an
étale chart of `F` with *affine* underlying scheme `Y`, and let `M` be a module over
`R = Γ(Y, 𝒪)` in an arbitrary universe.  This file proves that **the Čech cohomology, on a
finite affine covering family of `W`, of any abelian presheaf on the site whose sections over the
affine charts over `W` are the base change `Γ(-, 𝒪) ⊗_R M`, vanishes in every positive
degree.**

It is `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishing` with the module
universe freed.  That file runs the same three links but with the pullback-sections presheaf
`Mᵃ` of [Stacks, Tag 03DU] as coefficients, which exists only when the module lives in the
universe of the schemes; here the coefficients are the base-change presheaf of
`StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingBaseChangeCoefficients`, which exists in
every universe and agrees with `Mᵃ` over the affine objects.

## Why the comparison is asked only at the fibre products

The base-change presheaf and the sections of a quasi-coherent module agree over an *affine*
object and not over a general one, so the coefficient identification cannot be asked on the whole
slice at `W` — that would be asking for something false.  What the Čech complex of the family
reads is only its iterated fibre products, and those are affine charts again.  So the hypothesis
carried here is a morphism of coefficient presheaves on the slice which is invertible **at the
iterated fibre products of the family**, and
`Stacks.CechSite.isZero_cechCohomology_of_isoAtFibreProducts` is what consumes it.  That is the
one structural difference from the quasi-coherent case, where the identification is a natural
isomorphism on all of the slice.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isStandardCovering_sliceImageFamily'`: the image of a
  finite affine covering family of an affine chart is a standard étale covering of the chart's
  scheme, at an arbitrary index universe.
* `AlgebraicGeometry.Space.SmallEtale.isZero_sliceCechCohomology_baseChange`: the Čech cohomology
  of the base-change presheaf, read on the slice at the chart, vanishes in every positive degree.
* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_of_isoAtFibreProducts_baseChange`:
  **the same for a coefficient presheaf on the site compared with the base-change presheaf at the
  iterated fibre products of the family.**

## Implementation notes

`AlgebraicGeometry.Space.SmallEtale.isStandardCovering_sliceImageFamily` is stated at index
universe `u`, the universe of the schemes, because the quasi-coherent case it serves is.  Nothing
in its proof uses that, and the four clauses of [Stacks, Tag 03X9] are indexed by a type in an
arbitrary universe, so the statement is repeated here at an arbitrary index universe rather than
transported: there is no invariance of a covering family under reindexing in the tree, and
`AlgebraicGeometry.IsStandardCovering` has its index type free, so repeating costs one copy of a
nine-line proof and transporting would cost a new piece of machinery.

The `CategoryTheory.Limits.HasProduct` instances of the three families are supplied by `haveI`
and not registered, and `CategoryTheory.Limits.HasFiniteLimits (Over U)` for a chart `U` is a
`local instance`.  That is the same choice
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheafCohomologyVanishing` makes, and for the
same reason: a global instance would oblige every consumer of the small étale site to a full
library build.

No `@[stacks]` attribute is claimed.  The conclusion is one clause of Descent, Lemma 03FJ for one
of the sites of [Stacks, Tag 03P2], under a hypothesis that Lemma 03FJ does not carry.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : SmallEtale B S hS F)

/- The slice of the small étale site at a chart has finite limits, as an instance local to this
file; the theorem is `AlgebraicGeometry.Space.hasFiniteLimits_overChart`, deliberately not an
instance there.  Only the attribute is local, so no second declaration is needed. -/
attribute [local instance] hasFiniteLimits_overChart

namespace SmallEtale

/-- **The image of a finite affine covering family of an affine chart is a standard étale
covering of the chart's scheme**, with the index type in an arbitrary universe.

This is `AlgebraicGeometry.Space.SmallEtale.isStandardCovering_sliceImageFamily` with the index
universe of the family freed; the proof is the same, and the module documentation explains why it
is repeated rather than transported.  The four clauses of [Stacks, Tag 03X9] come from four
different places: finiteness and the affineness of the members are hypotheses, étaleness of the
members is part (2) of [Stacks, Tag 03EC] in the form
`AlgebraicGeometry.Space.SmallEtale.etale_sliceToOver_obj_hom`, and joint surjectivity is the
pointwise criterion for the covering sieves of the small étale site,
`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`, together with the fact
that an arrow of `CategoryTheory.Sieve.ofArrows` factors through a member of the family. -/
theorem isStandardCovering_sliceImageFamily' [IsAffine (chartScheme W)]
    (E : PreZeroHypercover.{u + 1} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS F W) :
    IsStandardCovering .etale
      (Stacks.CechSite.sliceImageFamily E (sliceToOver B S hS F W)).X
      (Stacks.CechSite.sliceImageFamily E (sliceToOver B S hS F W)).f where
  finite_index := hfin
  affine_source := haff
  jointly_surjective := by
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
    obtain ⟨V, g, hg, y, hy⟩ :=
      (SmallEtale.mem_topology_iff_exists_mem_range B S hS F E.sieve₀).mp hcov x
    obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff E.X E.f g).mp hg
    refine ⟨i, ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map h)) y, ?_⟩
    rw [← hy]
    -- the morphism of the image family is the underlying morphism of schemes, by definition
    change ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (E.f i)))
        (((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map h)) y) =
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (h ≫ E.f i))) y
    rw [Functor.map_comp, Functor.map_comp]
    simp
  standard := fun i ↦ etale_sliceToOver_obj_hom B S hS F W (Over.mk (E.f i))

variable {B S hS F W}

/-- **The Čech cohomology of the base-change presheaf of an `R`-module, read on the slice of the
small étale site at an affine chart, vanishes in every positive degree.**

The chain is the one of
`AlgebraicGeometry.Space.SmallEtale.isZero_sliceCechCohomology_associatedPresheaf`: the
identification of a family of schemes over the chart's scheme with its reading inside the slice
at the terminal object, then the Čech comparison along the slice projection
`AlgebraicGeometry.Space.SmallEtale.sliceToOver`, which preserves the iterated fibre products of
the family.  Only the coefficients differ, and the vanishing they are fed is
`AlgebraicGeometry.isZero_cechCohomology_succ_baseChange`. -/
theorem isZero_sliceCechCohomology_baseChange [IsAffine (chartScheme W)]
    (E : PreZeroHypercover.{u + 1} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS F W)
    [hprodE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (M : Type (u + 1)) [AddCommGroup M]
    [Module (Γ(chartScheme W, ⊤) : Type u) M] (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.sliceCechCohomology E
      ((sliceToOver B S hS F W).op ⋙
        baseChangeAbelianPresheaf (chartScheme W) M) p) := by
  -- the image family of schemes over the chart's scheme, and the products of all three families
  set 𝒢 := Stacks.CechSite.sliceImageFamily E (sliceToOver B S hS F W) with h𝒢
  have hprod𝒢 : ∀ (n : ℕ) (i : Fin (n + 1) → 𝒢.I₀),
      HasProduct (fun a ↦ Over.mk (𝒢.f (i a))) := fun _ _ ↦ inferInstance
  have hfl : HasFiniteLimits (Over (terminalOver (chartScheme W))) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have hprodT : ∀ (n : ℕ) (i : Fin (n + 1) → (Stacks.CechSite.toTerminalSliceFamily 𝒢).I₀),
      HasProduct (fun a ↦ Over.mk ((Stacks.CechSite.toTerminalSliceFamily 𝒢).f (i a))) :=
    fun _ _ ↦ inferInstance
  -- the slice projection preserves the iterated fibre products of `E`
  have hiso : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      IsIso (Stacks.CechSite.cechProductMapOfSliceFunctor E (sliceToOver B S hS F W) n i) :=
    fun n i ↦ Stacks.CechSite.isIso_cechProductMapOfSliceFunctor E (sliceToOver B S hS F W) n i
  -- the scheme-side vanishing, at the chart's scheme as base and its identity as the object
  have hcase : IsZero (Stacks.CechSite.cechCohomology
      (Stacks.CechSite.toTerminalSliceFamily 𝒢)
      (baseChangeAbelianPresheaf (chartScheme W) M) p) :=
    isZero_cechCohomology_succ_baseChange (chartScheme W) M .etale
      (Stacks.CechSite.toTerminalSliceFamily 𝒢)
      (isStandardCovering_sliceImageFamily' B S hS F W E hfin haff hcov) p hp
  exact Stacks.CechSite.isZero_sliceCechCohomology_of_isZero_of_sliceFunctor E
    (sliceToOver B S hS F W) (baseChangeAbelianPresheaf (chartScheme W) M) hiso p
    (Stacks.CechSite.isZero_sliceCechCohomology_of_isZero_cechCohomology_toTerminalSliceFamily
      𝒢 (baseChangeAbelianPresheaf (chartScheme W) M) p hcase)

/-- **The `Ȟ^p = 0` clause of Descent, Lemma 03FJ on the small étale site of an algebraic space,
for a coefficient presheaf identified with the base-change presheaf at the iterated fibre
products of the covering family.**

This is the form the geometry supplies: quasi-coherence identifies the sections of a module with
a base change over the affine objects, the iterated fibre products of a finite affine covering
family of an affine chart are affine charts, and nothing is asked anywhere else. -/
theorem isZero_cechCohomology_of_isoAtFibreProducts_baseChange [IsAffine (chartScheme W)]
    (E : PreZeroHypercover.{u + 1} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS F W)
    [hprodE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (M : Type (u + 1)) [AddCommGroup M] [Module (Γ(chartScheme W, ⊤) : Type u) M]
    (Coeff : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (α : (sliceToOver B S hS F W).op ⋙ baseChangeAbelianPresheaf (chartScheme W) M ⟶
      (Over.forget W).op ⋙ Coeff)
    (hα : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      IsIso (α.app (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))))))
    (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E Coeff p) :=
  Stacks.CechSite.isZero_cechCohomology_of_isoAtFibreProducts E α hα p
    (isZero_sliceCechCohomology_baseChange E hfin haff hcov M p hp)

end SmallEtale

end AlgebraicGeometry.Space

end
