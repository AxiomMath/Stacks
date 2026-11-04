module

public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemRestrictionIso
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemSourcePresentation
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerSystemExtLifting

/-!
# The core case of Stacks 0G2H in the degrees where no induction is needed

The core case of [Stacks, Tag 0G2H] — the hypothesis `hcore` of
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core` — is indexed by a pair of
integers `p`, `q`: the degree `p` in which the source system is concentrated and the degree `q`
in which the target is. Through
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_single_degree` it is the
bijectivity of

`colim_n Ext^i_X(𝓘^n𝓗, 𝓑) ⟶ Ext^i_U(𝓗|_U, 𝓑|_U)`, where `q + i = p`,

for `𝓗 = H^p(𝓕^•)` and `𝓑` coherent, and the source's proof of that is an induction on `i`.

This file discharges the two degrees in which the induction has nothing to do, namely `i = 0`
and the degenerate range:

* `p < q`, where every group in sight vanishes — in Mathlib's convention
  `Hom_{D(𝒜)}(A[p], B[q]) = Ext^{p-q}(A, B)`, so there is no such `Ext`-group at all. This is
  `CategoryTheory.restrictionLifting_singleFunctor_of_lt`.
* `p = q`, i.e. `i = 0`, which is the first display of [Stacks, Tag 01YB]:
  `AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem_degreeZero`.

Together they give the core case for every `p ≤ q`
(`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_le`), so the residue of
[Stacks, Tag 0G2H] is exactly the range `p > q`, where the `Ext`-degree `i = p - q` is positive
and the source runs its two diagram chases.

## Main results

* `AlgebraicGeometry.DeligneSystem.opensRange_eq_supportCompl`: the image of `j` is the
  complement of the vanishing locus of the ideal sheaf of a Deligne system — the hypothesis in
  which the degree-zero `Ext`-colimit statement is phrased.
* `AlgebraicGeometry.DeligneSystem.isCoherent_homology`: the cohomology sheaves of the complex
  of a Deligne system are coherent.
* `AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_le`: **the core case of
  [Stacks, Tag 0G2H] for `p ≤ q`**, unconditionally.
* `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core_pos`: **[Stacks, Tag 0G2H]
  from its core case in positive `Ext`-degree only** — the same conclusion as
  `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core` with `hcore` assumed only
  for `q < p`.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

attribute [local instance] HasDerivedCategory.standard CategoryTheory.HasExt.standard

universe u

namespace AlgebraicGeometry.DeligneSystem

variable {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]
  (D : DeligneSystem j)

/-- **The image of `j` is the complement of the vanishing locus of the ideal sheaf of a Deligne
system.** The structure field `AlgebraicGeometry.DeligneSystem.support_idealSheaf` says that the
vanishing locus is the complement of the image; this is the same statement read as an equality
of opens, which is the form the `Ext`-colimit statements of
`StacksFrontier/AlgebraicGeometry/Duality/ExtensionZeroCoherent/ExtIdealPowerRestrict.lean` are
phrased in. -/
public lemma opensRange_eq_supportCompl : j.opensRange = D.idealSheaf.support.compl := by
  apply TopologicalSpace.Opens.ext
  show Set.range j.base = (D.idealSheaf.support : Set X)ᶜ
  rw [D.support_idealSheaf, compl_compl]

/-- **The cohomology sheaves of the complex of a Deligne system are coherent.** Its terms are
coherent by the structure field `AlgebraicGeometry.DeligneSystem.isCoherent_complex`, and
coherent modules on a locally Noetherian scheme are closed under kernels and cokernels
(`AlgebraicGeometry.isCoherent_kernel` and `AlgebraicGeometry.isCoherent_cokernel`, [Stacks, Tag
01Y0]), which is all that `CategoryTheory.ShortComplex.homologyIsoCokernelLift` asks of the
degree-`p` short complex.

This is what the degree-zero `Ext`-colimit statement needs of the module whose ideal powers it
runs over, namely `H^p(𝓕^•)`. -/
public lemma isCoherent_homology (p : ℤ) : (D.complex.homology p).IsCoherent := by
  let := isWeakSerreClass_coherentModules X
  have : ((D.complex.sc p).X₁).IsCoherent := D.isCoherent_complex _
  have : ((D.complex.sc p).X₂).IsCoherent := D.isCoherent_complex _
  have : ((D.complex.sc p).X₃).IsCoherent := D.isCoherent_complex _
  have : (kernel (D.complex.sc p).g).IsCoherent := isCoherent_kernel _
  exact ObjectProperty.prop_of_iso (P := fun F : X.Modules => F.IsCoherent)
    (ShortComplex.homologyIsoCokernelLift (D.complex.sc p)).symm
    (isCoherent_cokernel
      (kernel.lift (D.complex.sc p).g (D.complex.sc p).f (D.complex.sc p).zero))

/-- **The core case of [Stacks, Tag 0G2H] for a target in a degree `q ≥ p`.** The identification
for the one-degree truncation system `(τ^{≥p}τ^{≤p}K_n)` against a target concentrated in the
single degree `q`, whenever `p ≤ q`.

The source's induction on the `Ext`-degree `i = p - q` has nothing to do here. For `p < q` there
is no such degree and all the groups vanish
(`CategoryTheory.restrictionLifting_singleFunctor_of_lt`); for `p = q` the degree is `0` and the
statement is the first display of [Stacks, Tag 01YB], available as
`AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem_degreeZero`. The reduction
of the core case to the ideal powers of the cohomology sheaf is
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_single_degree`.

There is no hypothesis beyond `p ≤ q`: the coherence of `H^p(𝓕^•)` that the degree-zero
statement needs of the module whose ideal powers it runs over is
`AlgebraicGeometry.DeligneSystem.isCoherent_homology`. -/
public lemma restrictionLifting_truncGELE_of_le (p q : ℤ) (hpq : p ≤ q)
    (L : BoundedCoherentDerived X)
    (hGE : (boundedCoherentTStructure X).IsGE L q)
    (hLE : (boundedCoherentTStructure X).IsLE L q) :
    RestrictionLifting (D.system ⋙ (boundedCoherentTStructure X).truncGELE p p)
      (restrictBoundedCoherent j) L := by
  refine D.restrictionLifting_truncGELE_of_single_degree p q L hGE hLE fun B hB => ?_
  rcases lt_or_eq_of_le hpq with h | h
  · exact restrictionLifting_singleFunctor_of_lt _ _ _ p q h
  · subst h
    have := D.isCoherent_homology p
    have := hB
    have := isQuasicoherent_of_isCoherent B
    exact restrictionLifting_singleFunctor_idealPowerSystem_degreeZero j D.idealSheaf
      D.opensRange_eq_supportCompl (D.complex.homology p) B p

/-- **[Stacks, Tag 0G2H] needs its core case only in positive `Ext`-degree.** The same statement
as `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core`, with the hypothesis
`hcore` restricted to the pairs `q < p` — that is, to the positive `Ext`-degrees `i = p - q`, the
range in which the source's proof of the core case runs its two diagram chases. The remaining
pairs `p ≤ q` are discharged by
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_le`.

Nothing else is assumed: this is `isIso_restrictionNatTrans_of_core` with a strictly weaker
hypothesis. -/
public theorem isIso_restrictionNatTrans_of_core_pos (K : BoundedCoherentDerived U)
    (e : D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K))
    (hcore : ∀ p q : ℤ, q < p → ∀ L : BoundedCoherentDerived X,
      (boundedCoherentTStructure X).IsGE L q → (boundedCoherentTStructure X).IsLE L q →
      RestrictionLifting (D.system ⋙ (boundedCoherentTStructure X).truncGELE p p)
        (restrictBoundedCoherent j) L) :
    IsIso (D.restrictionNatTrans K e) :=
  D.isIso_restrictionNatTrans_of_core K e fun p q L hq hq' => by
    rcases lt_or_ge q p with h | h
    · exact hcore p q h L hq hq'
    · exact D.restrictionLifting_truncGELE_of_le p q h L hq hq'

end AlgebraicGeometry.DeligneSystem

end
