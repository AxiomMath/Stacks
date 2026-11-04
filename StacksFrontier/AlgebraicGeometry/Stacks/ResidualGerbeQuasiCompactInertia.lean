module

public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOfFlatInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeResidualGerbeExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedSubstackLocallyClosed

/-!
# Residual gerbes exist when the inertia is quasi-compact (Stacks 06RD)

**Stacks 06RD**: let `𝒳` be an algebraic stack over `S` whose inertia projection `I_𝒳 ⟶ 𝒳` is
quasi-compact. Then the residual gerbe of `𝒳` at every point `x ∈ |𝒳|` exists.

The source's proof: let `𝒳' ⊆ 𝒳` be the reduced closed substack with `|𝒳'| = \overline{\{x\}}`
(**Stacks 0509**). Its inertia is quasi-compact, so it has a dense open substack `𝒰` which is a
gerbe (**Stacks 06RC**); `x` lies in `|𝒰|`, being the generic point of `|𝒳'|`, and the residual
gerbe of `𝒰` at `x` exists (**Stacks 06RA**). It is a residual gerbe of `𝒳` at `x`.

Here Stacks 06RC is applied in the form
`AlgebraicGeometry.Stack.exists_dense_openSubstack_isGerbe_of_isomSpace`, whose hypothesis is the
quasi-compactness of the automorphism spaces; that hypothesis passes from `𝒳` to its substacks
by `AlgebraicGeometry.Stack.isQuasiCompact_isomSpace_of_fullyFaithful`, which is what the source's
appeal to Stacks 06R5 and Stacks 050V provides. Stacks 06RA produces a monomorphism with a
single point over `x`; the existence of the residual gerbe is read as the reduced form,
condition (2) of Stacks 06MT (`AlgebraicGeometry.Stack.HasReducedSingletonPointMonomorphism`),
which is reached by passing to the reduction (**Stacks 050C**) of the source, a closed substack
with the same single point.

Stacks 06RC rests on Stacks 06QJ (2) `⟹` (1), which is proved from the bootstrap theorem Stacks
04S6 part (3), `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.

## Main results

* `AlgebraicGeometry.Stack.hasReducedSingletonPointMonomorphism_of_isQuasiCompact_inertia`:
  **Stacks 06RD**.

## References

* [Stacks Project, Tag 050C](https://stacks.math.columbia.edu/tag/050C)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06RA](https://stacks.math.columbia.edu/tag/06RA)
* [Stacks Project, Tag 06RC](https://stacks.math.columbia.edu/tag/06RC)
* [Stacks Project, Tag 06RD](https://stacks.math.columbia.edu/tag/06RD)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A closed immersion of algebraic stacks is a monomorphism and an embedding on points. -/
private theorem isMonomorphism_and_isEmbedding_pointsMap_of_isClosedImmersion
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsClosedImmersion B S hS f) :
    AlgebraicStacks.IsMonomorphism B S hS f ∧
      @Topology.IsEmbedding _ _ (pointTopology B S hS 𝒳.val) (pointTopology B S hS 𝒴.val)
        (AlgebraicStacks.pointsMap B S hS f) := by
  have hf' := AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS f hf
  exact ⟨AlgebraicStacks.isMonomorphism_of_isImmersion B S hS f hf',
    AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion B S hS f hf'⟩

/-- Let `𝒳` be an algebraic stack over `S` whose inertia projection `I_𝒳 ⟶ 𝒳` is
quasi-compact. Then the residual gerbe of `𝒳` exists at every point `x` of `|𝒳|`, in the sense
of Stacks 06MU (1), condition (2) of Stacks 06MT: there is a reduced algebraic stack `𝒵` with a
monomorphism `𝒵 ⟶ 𝒳` whose space of points is a single point lying over `x`. -/
@[stacks 06RD]
theorem hasReducedSingletonPointMonomorphism_of_isQuasiCompact_inertia
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property)) :
    HasReducedSingletonPointMonomorphism B S hS 𝒳 x := by
  let := pointTopology B S hS 𝒳.val
  -- The reduced closed substack on the closure of `x` (Stacks 0509).
  obtain ⟨P, ⟨⟨_hPiso, hP, hPimm⟩, hpts, hPred⟩, -⟩ :=
    existsUnique_reducedClosedSubstack B S hS 𝒳 (closure {x}) isClosed_closure
  let i := fullSubcategoryInclusion 𝒳 P hP
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS i) = closure {x} := hpts hP
  obtain ⟨hPmono, hemb⟩ :=
    isMonomorphism_and_isEmbedding_pointsMap_of_isClosedImmersion B S hS i hPimm
  -- Stacks 06RC on it.
  have hqc' := isQuasiCompact_isomSpace_of_fullyFaithful B S hS i
    (isQuasiCompact_isomSpace_of_isQuasiCompactMorphism_inertiaProjection B S hS 𝒳 hqc)
  obtain ⟨𝒰, hdense, hger⟩ := exists_dense_openSubstack_isGerbe_of_isomSpace B S hS
    (fullSubcategoryAlgebraicStack 𝒳 P hP) (hPred hP) hqc'
  -- `x` comes from a point `x'` of the closed substack, which lies in `|𝒰|`.
  obtain ⟨x', hx'⟩ : x ∈ Set.range (AlgebraicStacks.pointsMap B S hS i) :=
    hrange ▸ subset_closure (Set.mem_singleton x)
  let := pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP).val
  have hgen : closure {x'} = Set.univ := by
    rw [hemb.closure_eq_preimage_closure_image, Set.image_singleton]
    show AlgebraicStacks.pointsMap B S hS i ⁻¹'
      closure {AlgebraicStacks.pointsMap B S hS i x'} = _
    rw [hx', ← hrange, Set.preimage_range]
  have hx'U : x' ∈ 𝒰.pointSet B S hS := by
    by_contra hnot
    have hC : IsClosed (𝒰.pointSet B S hS)ᶜ :=
      (OpenSubstack.isOpen_pointSet B S hS 𝒰).isClosed_compl
    have hsub : closure {x'} ⊆ (𝒰.pointSet B S hS)ᶜ :=
      closure_minimal (Set.singleton_subset_iff.2 hnot) hC
    rw [hgen] at hsub
    have hempty : 𝒰.pointSet B S hS = ∅ :=
      Set.eq_empty_of_forall_notMem fun z hz => hsub (Set.mem_univ z) hz
    have := hdense.closure_eq
    rw [hempty, closure_empty] at this
    exact (Set.eq_empty_iff_forall_notMem.1 this.symm) x' (Set.mem_univ x')
  obtain ⟨x'', hx''⟩ := hx'U
  -- The residual gerbe of `𝒰` at `x''` (Stacks 06RA), made reduced (Stacks 050C).
  obtain ⟨𝒵, f, hfm, z, hz, hfz⟩ := hasSingletonPointMonomorphism_of_isGerbe B S hS
    𝒰.toAlgebraicStack hger x''
  obtain ⟨Q, ⟨_hQiso, hQ, hQimm⟩, hQred⟩ := exists_reduction B S hS 𝒵
  obtain ⟨hQr, hQs⟩ := hQred hQ
  let k := fullSubcategoryInclusion 𝒵 Q hQ
  let := pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒵 Q hQ).val
  let := pointTopology B S hS 𝒵.val
  obtain ⟨hkmono, hkemb⟩ :=
    isMonomorphism_and_isEmbedding_pointsMap_of_isClosedImmersion B S hS k hQimm
  have hUi : AlgebraicStacks.IsImmersion B S hS 𝒰.inclusion :=
    AlgebraicStacks.isImmersion_of_isOpenImmersion B S hS _ 𝒰.isOpenImmersion
  refine ⟨fullSubcategoryAlgebraicStack 𝒵 Q hQ, k ≫ f ≫ 𝒰.inclusion ≫ i, hQr, ?_, ?_⟩
  · exact AlgebraicStacks.isMonomorphism_comp B S hS _ _
      hkmono
      (AlgebraicStacks.isMonomorphism_comp B S hS _ _ hfm
        (AlgebraicStacks.isMonomorphism_comp B S hS _ _
          (AlgebraicStacks.isMonomorphism_of_isImmersion B S hS _ hUi)
          hPmono))
  · obtain ⟨z', hz'⟩ := hQs z
    refine ⟨z', fun w => hkemb.injective ((hz _).trans (hz _).symm |>.trans hz'.symm), ?_⟩
    show AlgebraicStacks.pointsMap B S hS (k ≫ f ≫ 𝒰.inclusion ≫ i) z' = x
    rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp,
      AlgebraicStacks.pointsMap_comp]
    simp only [Function.comp_apply]
    show AlgebraicStacks.pointsMap B S hS i (AlgebraicStacks.pointsMap B S hS 𝒰.inclusion
      (AlgebraicStacks.pointsMap B S hS f (AlgebraicStacks.pointsMap B S hS k z'))) = x
    rw [hz']
    have hfz' : AlgebraicStacks.pointsMap B S hS f z = x'' := hfz
    rw [hfz', hx'', hx']

end AlgebraicGeometry.Stack

end
