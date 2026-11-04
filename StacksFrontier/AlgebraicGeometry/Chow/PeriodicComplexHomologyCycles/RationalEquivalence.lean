module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkLinearEquiv
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Length
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthDeterminantFormula
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.DeterminantsAndComponents
import all StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.DeterminantsAndComponents
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.StalkComplex
import all StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.StalkComplex
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.StalkLocalization
import all StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.StalkLocalization

/-!
# Cycles of the cohomology of a two-periodic complex of a coherent sheaf

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `F` be a coherent `𝒪_X`-module carrying a `(2, 1)`-periodic
complex
`… ⟶ F --φ--> F --ψ--> F --φ--> F ⟶ …`,
that is, two endomorphisms with `φ ∘ ψ = 0` and `ψ ∘ φ = 0`. If the support of `F` has
delta-dimension at most `k + 1` and both cohomology sheaves `H⁰(F, φ, ψ)` and `H¹(F, φ, ψ)` are
supported in delta-dimension at most `k`, then the two `k`-cycles `[H⁰(F, φ, ψ)]_k` and
`[H¹(F, φ, ψ)]_k` are rationally equivalent.

The rational equivalence is explicit. Let `{W_j}` be the irreducible
components of `Supp(F)` of delta-dimension `k + 1`, a locally finite family of closed subsets of
`X`, and let `ξ_j` be the generic point of `W_j`. At `ξ_j` the stalk `F_{ξ_j}` has finite length
and the localized complex is exact, so it has a periodic determinant
`f_j = det_{κ(ξ_j)}(F_{ξ_j}, φ_{ξ_j}, ψ_{ξ_j})`, a nonzero element of the function field of `W_j`.
The claim is that
`- [H⁰(F, φ, ψ)]_k + [H¹(F, φ, ψ)]_k = ∑_j (W_j → X)_* div(f_j)`,
and it is checked one integral closed subscheme `Z ⊆ X` of delta-dimension `k` at a time. At the
generic point `x` of such a `Z` the local ring `A = 𝒪_{X,x}` is Noetherian local, the module
`M = F_x` is finite with one-dimensional support, and the components `W_j` through `x` correspond
to the minimal primes of that support; the coefficient of `[Z]` on the left is minus the
multiplicity `e_A(M, φ, ψ)` of the periodic complex, while on the right it is the sum of the orders
of the periodic determinants of the localizations. These agree by the local determinant formula.

## Main results

* `Stacks.Chow.rationallyEquivalent_cycles_of_twoPeriodicComplex` — the two cohomology cycles of a
  `(2, 1)`-periodic complex of a coherent sheaf are rationally equivalent.

## Implementation notes

A `(2, 1)`-periodic complex is presented as a `ZMod 2`-indexed cochain complex `K` of
`𝒪_X`-modules together with isomorphisms `K.X i ≅ F` of its two terms with the sheaf; this is the
invariant form of two mutually annihilating endomorphisms of `F`, and the two cohomology sheaves
are `K.homology 0` and `K.homology 1`. The hypothesis on the cohomology is stated pointwise, as a
bound on the relative dimension at the points of the supports, because forming the
delta-dimension of the support of a sheaf presupposes its coherence, which is part of the
conclusion here; the two forms are equivalent, and
`Stacks.Chow.relativeDimension_le_of_support_dimension_le` is the passage from the delta-dimension
bound to the pointwise one.

Coherence of the two cohomology sheaves, and the resulting bounds on the delta-dimensions of their
supports, are consequences of the hypotheses rather than additional assumptions, so they appear as
existentials in the conclusion: they are exactly the data needed to form the two cycles.

The local input is the determinant formula of Stacks 02QD, applied to the stalk of the complex at
the generic point of `Z`. Transporting it to the scheme setting uses that the stalk of a
two-periodic complex of `𝒪_X`-modules is a two-periodic complex of modules over the local ring
(the stalk functor is exact), that the stalk at a generization is the corresponding localization,
and that the periodic determinant is compatible with localization and with the identification of
the residue field at the generic point of `W_j` with the function field of `W_j`.

## References

* [Stacks Project, Tag 02MW](https://stacks.math.columbia.edu/tag/02MW)
* [Stacks Project, Tag 02PJ](https://stacks.math.columbia.edu/tag/02PJ)
* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
* [Stacks Project, Tag 02SB](https://stacks.math.columbia.edu/tag/02SB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.FlatShortExact TopologicalSpace

universe u

namespace Stacks.Chow

/-- The bijection between the components of the support passing through `x` and the minimal primes
of the support of the stalk at `x`. -/
private noncomputable def supportComponentPrimeEquiv {X : Scheme.{u}}
    (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)] (x : X) :
    letI := stalkModule (X := X.toRingedSpace) F x
    {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
      x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F))} ≃
    {p : PrimeSpectrum (X.presheaf.stalk x) //
      Minimal (· ∈ Module.support (X.presheaf.stalk x) (abStalk F x)) p} := by
  classical
  letI := stalkModule (X := X.toRingedSpace) F x
  let g : {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
      x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F))} →
      {p : PrimeSpectrum (X.presheaf.stalk x) //
        Minimal (· ∈ Module.support (X.presheaf.stalk x) (abStalk F x)) p} :=
    fun Z => ⟨(exists_minimalSupportPrime_over_component F x Z.1 Z.2).choose,
      (exists_minimalSupportPrime_over_component F x Z.1 Z.2).choose_spec.1⟩
  have hg (Z) : X.fromSpecStalk x (g Z).1 = (Z.1.2.1.genericPoint).1 :=
    (exists_minimalSupportPrime_over_component F x Z.1 Z.2).choose_spec.2
  apply Equiv.ofBijective g
  constructor
  · intro Z V h
    have hη : Z.1.2.1.genericPoint = V.1.2.1.genericPoint := by
      apply Subtype.ext
      exact (hg Z).symm.trans ((congrArg (fun p : {p : PrimeSpectrum (X.presheaf.stalk x) //
          Minimal (· ∈ Module.support (X.presheaf.stalk x) (abStalk F x)) p} =>
            X.fromSpecStalk x p.1) h).trans (hg V))
    apply Subtype.ext
    apply Subtype.ext
    exact (Z.1.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.1.2)).symm.trans
        ((congrArg (fun z => closure ({z} : Set (SheafOfModules.supp F))) hη).trans
          (V.1.2.1.isGenericPoint_genericPoint
            (isClosed_of_mem_irreducibleComponents _ V.1.2)))
  · intro p
    obtain ⟨Z, hxZ, hpZ⟩ := exists_component_over_minimalSupportPrime F x p.1 p.2
    refine ⟨⟨Z, hxZ⟩, Subtype.ext ?_⟩
    exact (X.fromSpecStalk x).isEmbedding.injective ((hg ⟨Z, hxZ⟩).trans hpZ.symm)

/-- The prime attached to a component cuts out the generic point of that component. -/
private theorem supportComponentPrimeEquiv_apply {X : Scheme.{u}}
    (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)] (x : X)
    (Z : {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
      x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F))}) :
    X.fromSpecStalk x (supportComponentPrimeEquiv F x Z).1 =
      (Z.1.2.1.genericPoint).1 :=
  (exists_minimalSupportPrime_over_component F x Z.1 Z.2).choose_spec.2

/-- If the support of the stalk at a point of relative dimension `k` contains a prime other than
the closed point, then every component of the support through that point has relative dimension
`k + 1`. -/
private theorem supportComponent_relativeDimension_eq_succ
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)] (k : ℤ)
    (hsupport : ∀ z ∈ SheafOfModules.supp F,
      relativeDimension C.dimensionFunction f z ≤ k + 1)
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k)
    (hex : letI := stalkModule (X := X.toRingedSpace) F x
      ∃ q : PrimeSpectrum (X.presheaf.stalk x),
        q ∈ Module.support (X.presheaf.stalk x) (abStalk F x) ∧
          q ≠ IsLocalRing.closedPoint (X.presheaf.stalk x))
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    (hxZ : x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F))) :
    relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1 := by
  let := stalkModule (X := X.toRingedSpace) F x
  obtain ⟨p, hp, hpη⟩ := exists_minimalSupportPrime_over_component F x Z hxZ
  obtain ⟨q, hq, hqne⟩ := hex
  have hpne : p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x) := by
    intro heq
    apply hqne
    exact le_antisymm (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)
      (heq ▸ hp.2 hq (heq ▸ IsLocalRing.le_maximalIdeal q.isPrime.ne_top))
  have hηne : (Z.2.1.genericPoint).1 ≠ x := by
    intro hηx
    apply hpne
    apply (X.fromSpecStalk x).isEmbedding.injective
    rw [hpη, hηx, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction f
  have hlt := d.strictAnti_specializes
    ((supportComponent_isGenericPoint F Z).specializes hxZ) hηne
  rw [hd, hd, hx] at hlt
  have hle := hsupport _ Z.2.1.genericPoint.property
  omega

/-- The generic point of the subscheme cut out by a component of the support is a generic point of
that component in the ambient scheme. -/
private theorem supportComponentIdeal_isGenericPoint {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    [IsIntegral (supportComponentIdeal F Z).subscheme] :
    IsGenericPoint ((supportComponentIdeal F Z).subschemeι
      (genericPoint (supportComponentIdeal F Z).subscheme))
      (Subtype.val '' (Z : Set (SheafOfModules.supp F)) : Set X) := by
  let I := supportComponentIdeal F Z
  change closure ({I.subschemeι (genericPoint I.subscheme)} : Set X) = _
  rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
    genericPoint_closure, Set.image_univ, I.range_subschemeι]
  exact supportComponentIdeal_support F Z

/-- At the generic point of a top-dimensional component of the support, the two conjugated stalk
maps form an exact pair in both orders. -/
private theorem periodicStalkLinearMaps_exact_of_supportComponent
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (k : ℤ)
    (hHk : ∀ (i : ZMod 2) (x : X),
      x ∈ SheafOfModules.supp (K.homology i) →
        relativeDimension C.dimensionFunction f x ≤ k)
    [IsLocallyNoetherian X] [QuasiSober (SheafOfModules.supp F)]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    (hZ : relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1)
    [IsIntegral (supportComponentIdeal F Z).subscheme] :
    Function.Exact (periodicStalkLinearMaps F K e ((supportComponentIdeal F Z).subschemeι
        (genericPoint (supportComponentIdeal F Z).subscheme))).1
      (periodicStalkLinearMaps F K e ((supportComponentIdeal F Z).subschemeι
        (genericPoint (supportComponentIdeal F Z).subscheme))).2 ∧
    Function.Exact (periodicStalkLinearMaps F K e ((supportComponentIdeal F Z).subschemeι
        (genericPoint (supportComponentIdeal F Z).subscheme))).2
      (periodicStalkLinearMaps F K e ((supportComponentIdeal F Z).subschemeι
        (genericPoint (supportComponentIdeal F Z).subscheme))).1 := by
  have hgt : k < relativeDimension C.dimensionFunction f
      ((supportComponentIdeal F Z).subschemeι
        (genericPoint (supportComponentIdeal F Z).subscheme)) := by
    rw [supportComponentIdeal_genericPoint, hZ]
    omega
  exact periodicStalkLinearMaps_exact F K e _
    (homology_stalk_subsingleton_of_relativeDimension_gt C f K 0 _ k hHk hgt)
    (homology_stalk_subsingleton_of_relativeDimension_gt C f K 1 _ k hHk hgt)

/-- The periodic determinant of the complex at the generic point of a component of the support of
delta-dimension `k + 1`, as a nonzero rational function on that component. -/
private noncomputable def supportComponentPeriodicDeterminant
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (k : ℤ)
    (hHk : ∀ (i : ZMod 2) (x : X),
      x ∈ SheafOfModules.supp (K.homology i) →
        relativeDimension C.dimensionFunction f x ≤ k)
    [QuasiSober (SheafOfModules.supp F)]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    (hδ : relativeDimension C.dimensionFunction f
      (Z.2.1.genericPoint).1 = k + 1) :
    (rationalFunctions (supportComponentIdeal F Z).subscheme)ˣ := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let I := supportComponentIdeal F Z
  letI : IsIntegral I.subscheme := supportComponentIdeal_integral F Z
  let η : I.subscheme := genericPoint I.subscheme
  let x : X := I.subschemeι η
  letI := stalkModule (X := X.toRingedSpace) F x
  have hx : IsGenericPoint x (Subtype.val '' (Z : Set (SheafOfModules.supp F))) :=
    supportComponentIdeal_isGenericPoint F Z
  have hfinite : IsFiniteLength (X.presheaf.stalk x) (abStalk F x) :=
    isFiniteLength_stalk_of_isGenericPoint_component_supp F Z x hx
  let P := periodicStalkLinearMaps F K e x
  have he := periodicStalkLinearMaps_exact_of_supportComponent C f F K e k hHk Z hδ
  let d := AlgebraicGeometry.periodicDeterminant P.1 P.2 he.1 he.2 hfinite
  let h : X.residueField x →+* rationalFunctions I.subscheme :=
    (rationalFunctionsEquivResidueField I.subscheme).1.symm.toRingHom.comp
      (I.subschemeι.residueFieldMap η).hom
  exact Units.map h.toMonoidHom d

/-- At a point of relative dimension `k` the coefficient of the difference of the cycles of two
coherent sheaves is the difference of their multiplicities there. -/
private theorem cycleDifference_apply_eq_stalkLengthDifference_of_relativeDimension
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (H₀ H₁ : X.Modules) [H₀.IsCoherent] [H₁.IsCoherent]
    (k : ℤ)
    (d₀ : schemeDeltaDimension C
      ((reducedSupport H₀).subschemeι ≫ f) ≤ (k : EInt))
    (d₁ : schemeDeltaDimension C
      ((reducedSupport H₁).subschemeι ≫ f) ≤ (k : EInt))
    (x : X)
    (hδ : relativeDimension C.dimensionFunction f x = k) :
    ((cycleAssociatedToCoherentSheaf C f H₀ k d₀ -
      cycleAssociatedToCoherentSheaf C f H₁ k d₁ :
        CycleGroup C f k) : AlgebraicCycle X ℤ) x =
      sheafMultiplicity H₀ x - sheafMultiplicity H₁ x := by
  change ((cycleAssociatedToCoherentSheaf C f H₀ k d₀ :
      AlgebraicCycle X ℤ) -
    (cycleAssociatedToCoherentSheaf C f H₁ k d₁ :
      AlgebraicCycle X ℤ)) x = _
  rw [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply,
    cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f H₀ k d₀ hδ,
    cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f H₁ k d₁ hδ]

/-- If the stalk of the sheaf has finite length at every point of relative dimension `k`, the two
cohomology cycles are equal. -/
private theorem homology_cycles_eq_of_stalks_finiteLength
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (k : ℤ)
    [h₀ : (K.homology 0).IsCoherent] [h₁ : (K.homology 1).IsCoherent]
    (d₀ : schemeDeltaDimension C
      ((reducedSupport (K.homology 0)).subschemeι ≫ f) ≤ (k : EInt))
    (d₁ : schemeDeltaDimension C
      ((reducedSupport (K.homology 1)).subschemeι ≫ f) ≤ (k : EInt))
    (hfin : ∀ (x : X), relativeDimension C.dimensionFunction f x = k →
      letI := stalkModule (X := X.toRingedSpace) F x
      IsFiniteLength (X.presheaf.stalk x) (abStalk F x)) :
    cycleAssociatedToCoherentSheaf C f (K.homology 0) k d₀ =
      cycleAssociatedToCoherentSheaf C f (K.homology 1) k d₁ := by
  apply Subtype.ext
  ext x
  by_cases hδ : relativeDimension C.dimensionFunction f x = k
  · have h := cycleDifference_apply_eq_stalkLengthDifference_of_relativeDimension
      C f (K.homology 0) (K.homology 1) k d₀ d₁ x hδ
    rw [sheafMultiplicity_sub_eq_zero_of_finiteLength F K e x (hfin x hδ)] at h
    exact sub_eq_zero.mp h
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f
      (K.homology 0) k d₀ hδ,
      cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f
        (K.homology 1) k d₁ hδ]

/-- Two `k`-cycles whose difference has the coefficients of a locally finite family of pushed
forward principal divisors are rationally equivalent. -/
private theorem rationallyEquivalent_of_principalDivisorFamily_coefficients
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (α β : CycleGroup C f k)
    {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ f) =
      ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite (fun j ↦ ((W j).support : Set X)))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ)
    (hcoeff : ∀ x : X,
      ((α - β : CycleGroup C f k) : AlgebraicCycle X ℤ) x =
        principalDivisorFamilyCoefficient C f W hW g x) :
    RationallyEquivalent C f k α β := by
  rw [RationallyEquivalent, mem_rationalEquivalences]
  apply (isRationallyEquivalentToZero_iff C f k (α - β)).2
  exact ⟨J, W, hW, hDim, hLocal, ⟨g, hcoeff⟩⟩

/-- A `k`-cycle vanishes at every point whose relative dimension is not `k`. -/
private theorem cycle_apply_eq_zero_of_dimension_ne
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (c : CycleGroup C f k) (x : X)
    (hx : relativeDimension C.dimensionFunction f x ≠ k) :
    (c : AlgebraicCycle X ℤ) x = 0 := by
  by_contra h
  let Z : IrreducibleCloseds X := irreducibleSetEquivPoints.symm x
  have hZ : Z.isIrreducible.genericPoint = x :=
    irreducibleSetEquivPoints.apply_symm_apply x
  have hc := (mem_cyclesOfDimension C f k c.val).1 c.property Z
    (by simpa only [hZ] using h)
  rw [deltaDimension_eq_of_isGenericPoint C f Z x isGenericPoint_closure] at hc
  exact hx hc

/-- For rational equivalence it is enough to compare coefficients at the points of relative
dimension `k`: both sides vanish elsewhere. -/
private theorem rationallyEquivalent_of_principalDivisorFamily_coefficients_on_dimension
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (α β : CycleGroup C f k)
    {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ f) =
      ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite (fun j ↦ ((W j).support : Set X)))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ)
    (hcoeff : ∀ x : X, relativeDimension C.dimensionFunction f x = k →
      ((α - β : CycleGroup C f k) : AlgebraicCycle X ℤ) x =
        principalDivisorFamilyCoefficient C f W hW g x) :
    RationallyEquivalent C f k α β := by
  obtain ⟨γ, hγ⟩ := exists_principalDivisorFamilySum C f k W hW hDim hLocal g
  apply rationallyEquivalent_of_principalDivisorFamily_coefficients
    C f k α β W hW hDim hLocal g
  intro x
  by_cases hx : relativeDimension C.dimensionFunction f x = k
  · exact hcoeff x hx
  · rw [← hγ x, cycle_apply_eq_zero_of_dimension_ne C f k (α - β) x hx,
      cycle_apply_eq_zero_of_dimension_ne C f k γ x hx]

/-- If a point of relative dimension `k` lies on a component of the support of relative dimension
`k + 1`, the support of the stalk there contains a prime other than the closed point. -/
private theorem exists_mem_support_ne_closedPoint_of_mem_supportComponent
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)] (k : ℤ)
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k)
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    (hZ : relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1)
    (hxZ : x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F))) :
    letI := stalkModule (X := X.toRingedSpace) F x
    ∃ p : PrimeSpectrum (X.presheaf.stalk x),
      p ∈ Module.support (X.presheaf.stalk x) (abStalk F x) ∧
        p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x) := by
  let := stalkModule (X := X.toRingedSpace) F x
  obtain ⟨p, hp, heq⟩ := exists_minimalSupportPrime_over_component F x Z hxZ
  refine ⟨p, hp.1, fun hpclosed => ?_⟩
  have hηx : (Z.2.1.genericPoint).1 = x := by
    rw [← heq, hpclosed, Scheme.fromSpecStalk_closedPoint]
  rw [hηx, hx] at hZ
  omega

/-- At a point of relative dimension `k` whose stalk has a support prime other than the closed
point, the components of the support through the point are the top-dimensional ones through it. -/
private def supportComponentTopEquiv
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)] (k : ℤ)
    (hsupport : ∀ z ∈ SheafOfModules.supp F,
      relativeDimension C.dimensionFunction f z ≤ k + 1)
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k)
    (hex : letI := stalkModule (X := X.toRingedSpace) F x
      ∃ q : PrimeSpectrum (X.presheaf.stalk x),
        q ∈ Module.support (X.presheaf.stalk x) (abStalk F x) ∧
          q ≠ IsLocalRing.closedPoint (X.presheaf.stalk x)) :
    {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
      x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F))} ≃
    {j : {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
        relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1} //
      x ∈ (supportComponentIdeal F j.1).support} where
  toFun Z := ⟨⟨Z.1, supportComponent_relativeDimension_eq_succ C f F k hsupport x hx hex Z.1 Z.2⟩,
    (mem_supportComponentIdeal_support F Z.1 x).2 Z.2⟩
  invFun j := ⟨j.1.1, (mem_supportComponentIdeal_support F j.1.1 x).1 j.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A point of relative dimension `k` on a component of the support of relative dimension `k + 1`
is a point of codimension one of the integral closed subscheme carried by the component. -/
private theorem exists_coheight_eq_one_of_mem_supportComponent
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)] (k : ℤ)
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    (hZ : relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1)
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k)
    (hxZ : x ∈ (supportComponentIdeal F Z).support) :
    ∃ y : (supportComponentIdeal F Z).subscheme,
      (supportComponentIdeal F Z).subschemeι y = x ∧ Order.coheight y = 1 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := supportComponentIdeal_integral F Z
  obtain ⟨y, rfl⟩ : x ∈ Set.range (supportComponentIdeal F Z).subschemeι := by
    rw [(supportComponentIdeal F Z).range_subschemeι]
    exact hxZ
  refine ⟨y, rfl, ?_⟩
  apply coheight_eq_one_of_relativeDimension C ((supportComponentIdeal F Z).subschemeι ≫ f) k
    (supportComponentIdeal_schemeDeltaDimension C f F Z (k + 1) hZ)
  rw [relativeDimension_comp_closedImmersion C.dimensionFunction _ f]
  exact hx

/-- At a minimal prime of the support of the stalk at `x` lying under the generic point of a
top-dimensional component, the order of the localized periodic determinant is the order of the
periodic determinant of the component. -/
private theorem ordFrac_periodicDeterminant_eq_supportComponent
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (k : ℤ)
    (hHk : ∀ (i : ZMod 2) (x : X),
      x ∈ SheafOfModules.supp (K.homology i) →
        relativeDimension C.dimensionFunction f x ≤ k)
    [IsLocallyNoetherian X] [QuasiSober (SheafOfModules.supp F)]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    (hZ : relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1)
    [IsIntegral (supportComponentIdeal F Z).subscheme]
    (x : X) (y : (supportComponentIdeal F Z).subscheme)
    (hy : (supportComponentIdeal F Z).subschemeι y = x) (hcodim : Order.coheight y = 1)
    (q : PrimeSpectrum (X.presheaf.stalk x))
    (hq : X.fromSpecStalk x q = (supportComponentIdeal F Z).subschemeι
      (genericPoint (supportComponentIdeal F Z).subscheme))
    [Ring.KrullDimLE 1 ((X.presheaf.stalk x) ⧸ q.asIdeal)] :
    letI : IsLocallyNoetherian (supportComponentIdeal F Z).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian ((supportComponentIdeal F Z).subschemeι ≫ f)
    letI : Ring.KrullDimLE 1 ((supportComponentIdeal F Z).subscheme.presheaf.stalk y) :=
      AlgebraicGeometry.krullDimLE_of_coheight_le hcodim.le
    letI := stalkModule (X := X.toRingedSpace) F x
    ∀ (hex : Function.Exact
        (LocalizedModule.map q.asIdeal.primeCompl
          (stalkLinearMap ((e 0).inv ≫ K.d 0 1 ≫ (e 1).hom) x))
        (LocalizedModule.map q.asIdeal.primeCompl
          (stalkLinearMap ((e 1).inv ≫ K.d 1 0 ≫ (e 0).hom) x)))
      (hex' : Function.Exact
        (LocalizedModule.map q.asIdeal.primeCompl
          (stalkLinearMap ((e 1).inv ≫ K.d 1 0 ≫ (e 0).hom) x))
        (LocalizedModule.map q.asIdeal.primeCompl
          (stalkLinearMap ((e 0).inv ≫ K.d 0 1 ≫ (e 1).hom) x)))
      (hfin : IsFiniteLength (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (abStalk F x))),
      Ring.ordFrac ((X.presheaf.stalk x) ⧸ q.asIdeal)
          (AlgebraicGeometry.periodicDeterminant
            (LocalizedModule.map q.asIdeal.primeCompl
              (stalkLinearMap ((e 0).inv ≫ K.d 0 1 ≫ (e 1).hom) x))
            (LocalizedModule.map q.asIdeal.primeCompl
              (stalkLinearMap ((e 1).inv ≫ K.d 1 0 ≫ (e 0).hom) x))
            hex hex' hfin : q.asIdeal.ResidueField) =
        Ring.ordFrac ((supportComponentIdeal F Z).subscheme.presheaf.stalk y)
          ((rationalFunctionsEquivFunctionField (supportComponentIdeal F Z).subscheme).1
            (supportComponentPeriodicDeterminant C f F K e k hHk Z hZ :
              rationalFunctions (supportComponentIdeal F Z).subscheme)) := by
  intro hex hex' hfin
  let : IsLocallyNoetherian (supportComponentIdeal F Z).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((supportComponentIdeal F Z).subschemeι ≫ f)
  let : Ring.KrullDimLE 1 ((supportComponentIdeal F Z).subscheme.presheaf.stalk y) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le hcodim.le
  let := stalkModule (X := X.toRingedSpace) F x
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let η := (supportComponentIdeal F Z).subschemeι
    (genericPoint (supportComponentIdeal F Z).subscheme)
  let := stalkModule (X := X.toRingedSpace) F η
  have hNfin : IsFiniteLength (X.presheaf.stalk η) (abStalk F η) :=
    isFiniteLength_stalk_of_isGenericPoint_component_supp F Z η
      (supportComponentIdeal_isGenericPoint F Z)
  have hNex := periodicStalkLinearMaps_exact_of_supportComponent C f F K e k hHk Z hZ
  rw [periodicStalkLinearMaps_eq] at hNex
  have heq := ordFrac_periodicDeterminant_stalk (supportComponentIdeal F Z).subschemeι y x hy F
    ((e 0).inv ≫ K.d 0 1 ≫ (e 1).hom) ((e 1).inv ≫ K.d 1 0 ≫ (e 0).hom) q hq
    hex hex' hfin hNex.1 hNex.2 hNfin
  simp only [supportComponentPeriodicDeterminant, periodicStalkLinearMaps_eq,
    RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe]
  convert heq using 1 <;> rfl

/-- At a point of codimension one on each member of the family, the coefficient of the principal
divisors is the sum of the orders of the functions in the local rings there. -/
private theorem principalDivisorFamilyCoefficient_eq_finsum_ordFrac
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ f) =
      ((k + 1 : ℤ) : EInt))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (x : X)
    (y : ∀ j : {j : J // x ∈ (W j).support}, (W j.1).subscheme)
    (hy : ∀ j : {j : J // x ∈ (W j).support}, (W j.1).subschemeι (y j) = x)
    (hcodim : ∀ j : {j : J // x ∈ (W j).support}, Order.coheight (y j) = 1) :
    principalDivisorFamilyCoefficient C f W hW g x =
      ∑ᶠ j : {j : J // x ∈ (W j).support},
        letI := hW j.1
        letI := LocallyOfFiniteType.isLocallyNoetherian ((W j.1).subschemeι ≫ f)
        letI : Ring.KrullDimLE 1 ((W j.1).subscheme.presheaf.stalk (y j)) :=
          AlgebraicGeometry.krullDimLE_of_coheight_le (hcodim j).le
        Multiplicative.toAdd ((Ring.ordFrac ((W j.1).subscheme.presheaf.stalk (y j))
          ((rationalFunctionsEquivFunctionField (W j.1).subscheme).val
            (g j.1 : rationalFunctions (W j.1).subscheme))).unzeroD 1) := by
  rw [principalDivisorFamilyCoefficient_eq_finsum_on_support C f k W hW hDim g x y hy]
  refine finsum_congr fun j ↦ ?_
  let := hW j.1
  let : IsLocallyNoetherian (W j.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((W j.1).subschemeι ≫ f)
  exact ord_eq_toAdd_unzeroD_ordFrac _ (y j) (hcodim j)

/-- At a point of relative dimension `k` whose stalk has a support prime other than the closed
point, minus the periodic length of the stalk complex, presented by the two conjugated stalk
maps, is the coefficient of the principal divisors of the top-dimensional components. -/
private theorem neg_periodicLength_twoPeriodicComplex_eq_coefficient
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (k : ℤ)
    (hHk : ∀ (i : ZMod 2) (x : X),
      x ∈ SheafOfModules.supp (K.homology i) →
        relativeDimension C.dimensionFunction f x ≤ k)
    [IsLocallyNoetherian X] [QuasiSober (SheafOfModules.supp F)]
    (hsupport : ∀ z ∈ SheafOfModules.supp F,
      relativeDimension C.dimensionFunction f z ≤ k + 1)
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k) :
    letI := stalkModule (X := X.toRingedSpace) F x
    ∀ (φ ψ : Module.End (X.presheaf.stalk x) (abStalk F x))
      (_ : φ = stalkLinearMap ((e 0).inv ≫ K.d 0 1 ≫ (e 1).hom) x)
      (_ : ψ = stalkLinearMap ((e 1).inv ≫ K.d 1 0 ≫ (e 0).hom) x)
      (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
      (_ : ∀ i : ZMod 2, IsFiniteLength (X.presheaf.stalk x)
        ((AlgebraicGeometry.twoPeriodicComplex φ ψ hφψ hψφ).homology i))
      (_ : ∃ p : PrimeSpectrum (X.presheaf.stalk x),
        p ∈ Module.support (X.presheaf.stalk x) (abStalk F x) ∧
          p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x)),
      -AlgebraicGeometry.periodicLength (AlgebraicGeometry.twoPeriodicComplex φ ψ hφψ hψφ) =
        principalDivisorFamilyCoefficient C f
          (fun j : {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
              relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1} =>
            supportComponentIdeal F j.1)
          (fun j => supportComponentIdeal_integral F j.1)
          (fun j => supportComponentPeriodicDeterminant C f F K e k hHk j.1 j.2) x := by
  intro φ ψ hφ hψ hφψ hψφ hcoh hex
  let := stalkModule (X := X.toRingedSpace) F x
  subst hφ hψ
  have : Module.Finite (X.presheaf.stalk x) (abStalk F x) :=
    Scheme.Modules.finite_stalk_of_isCoherent F x
  have hdimM : Module.supportDim (X.presheaf.stalk x) (abStalk F x) = 1 := by
    obtain ⟨p, hp, hpne⟩ := hex
    exact supportDim_eq_one_of_mem_nonclosed
      (supportDim_stalk_le_one_of_relativeDimension_support_le C f F k hsupport x hx) p hp hpne
  obtain ⟨hdim, hfinite, hexactφψ, hexactψφ, hlength⟩ :=
    AlgebraicGeometry.neg_periodicLength_eq_finsum_ordFrac_periodicDeterminant
      _ _ hφψ hψφ hcoh hdimM
  let J := {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
    relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1}
  let W : J → X.IdealSheafData := fun j => supportComponentIdeal F j.1
  have hW (j : J) : IsIntegral (W j).subscheme := supportComponentIdeal_integral F j.1
  have hDim (j : J) :
      schemeDeltaDimension C ((W j).subschemeι ≫ f) = ((k + 1 : ℤ) : EInt) :=
    supportComponentIdeal_schemeDeltaDimension C f F j.1 (k + 1) j.2
  let g : ∀ j : J, (rationalFunctions (W j).subscheme)ˣ := fun j =>
    supportComponentPeriodicDeterminant C f F K e k hHk j.1 j.2
  change _ = principalDivisorFamilyCoefficient C f W hW g x
  let Jx := {j : J // x ∈ (W j).support}
  let eTop := supportComponentTopEquiv C f F k hsupport x hx hex
  let ePrime : Jx ≃ {p : PrimeSpectrum (X.presheaf.stalk x) //
      Minimal (· ∈ Module.support (X.presheaf.stalk x) (abStalk F x)) p} :=
    eTop.symm.trans (supportComponentPrimeEquiv F x)
  have hePrime (j : Jx) : X.fromSpecStalk x (ePrime j).1 =
      (W j.1).subschemeι (genericPoint (W j.1).subscheme) := by
    let := hW j.1
    rw [supportComponentIdeal_genericPoint]
    exact supportComponentPrimeEquiv_apply F x (eTop.symm j)
  choose y hy hcodim using fun j : Jx =>
    exists_coheight_eq_one_of_mem_supportComponent C f F k j.1.1 j.1.2 x hx j.2
  rw [principalDivisorFamilyCoefficient_eq_finsum_ordFrac C f k W hW hDim g x y hy hcodim,
    hlength]
  symm
  apply finsum_eq_of_bijective ePrime ePrime.bijective
  intro j
  symm
  let := hdim (ePrime j)
  let := hW j.1
  rw [← WithZero.unzeroD_eq_unzero (d := 1)]
  exact congrArg (fun z : WithZero (Multiplicative ℤ) => Multiplicative.toAdd (z.unzeroD 1))
    (ordFrac_periodicDeterminant_eq_supportComponent C f F K e k hHk j.1.1 j.1.2 x (y j) (hy j)
      (hcodim j) (ePrime j).1 (hePrime j) (hexactφψ _) (hexactψφ _) (hfinite _))

/-- At a point of relative dimension `k` on a top-dimensional component of the support, minus the
periodic length of the complex of stalks is the coefficient of the principal divisors of the
top-dimensional components. -/
private theorem neg_periodicLength_eq_coefficient_of_mem_supportComponent
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (k : ℤ)
    (hHk : ∀ (i : ZMod 2) (x : X),
      x ∈ SheafOfModules.supp (K.homology i) →
        relativeDimension C.dimensionFunction f x ≤ k)
    [IsLocallyNoetherian X] [QuasiSober (SheafOfModules.supp F)]
    (hsupport : ∀ z ∈ SheafOfModules.supp F,
      relativeDimension C.dimensionFunction f z ≤ k + 1)
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k)
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    (hZ : relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1)
    (hxZ : x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F))) :
    -AlgebraicGeometry.periodicLength (moduleStalkComplex K x) =
      principalDivisorFamilyCoefficient C f
        (fun j : {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
            relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1} =>
          supportComponentIdeal F j.1)
        (fun j => supportComponentIdeal_integral F j.1)
        (fun j => supportComponentPeriodicDeterminant C f F K e k hHk j.1 j.2) x := by
  let := stalkModule (X := X.toRingedSpace) F x
  let M := ModuleCat.of (X.presheaf.stalk x) (abStalk F x)
  let Eterm : ∀ i : ZMod 2, (moduleStalkComplex K x).X i ≅ M := fun i =>
    ((moduleStalkFunctor x).mapIso (e i)).trans (moduleStalkIso F x)
  let φ := ((Eterm 0).inv ≫ (moduleStalkComplex K x).d 0 1 ≫ (Eterm 1).hom).hom
  let ψ := ((Eterm 1).inv ≫ (moduleStalkComplex K x).d 1 0 ≫ (Eterm 0).hom).hom
  obtain ⟨hφψ, hψφ, ⟨E⟩⟩ := exists_twoPeriodicComplex_iso (moduleStalkComplex K x) M Eterm
  have hcoh (i : ZMod 2) : IsFiniteLength (X.presheaf.stalk x)
      ((AlgebraicGeometry.twoPeriodicComplex φ ψ hφψ hψφ).homology i) :=
    (moduleStalkComplex_homology_isFiniteLength C f F K e k hHk x hx i).of_surjective
      (HomologicalComplex.homologyMapIso E i).toLinearEquiv.surjective
  rw [AlgebraicGeometry.periodicLength_eq_of_iso E]
  exact neg_periodicLength_twoPeriodicComplex_eq_coefficient C f F K e k hHk hsupport x hx φ ψ
    (moduleStalkComplex_conjugate_eq_stalkLinearMap F K e x 0 1)
    (moduleStalkComplex_conjugate_eq_stalkLinearMap F K e x 1 0) hφψ hψφ hcoh
    (exists_mem_support_ne_closedPoint_of_mem_supportComponent C f F k x hx Z hZ hxZ)

/-- At a point of relative dimension `k`, the difference of the multiplicities of the two
cohomology sheaves is the coefficient of the principal divisors of the periodic determinants of
the top-dimensional components of the support. -/
private theorem sheafMultiplicity_sub_eq_principalDivisorFamilyCoefficient
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (k : ℤ)
    (hFk : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hHk : ∀ (i : ZMod 2) (x : X),
      x ∈ SheafOfModules.supp (K.homology i) →
        relativeDimension C.dimensionFunction f x ≤ k)
    [IsLocallyNoetherian X] [QuasiSober (SheafOfModules.supp F)]
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k) :
    sheafMultiplicity (K.homology 1) x - sheafMultiplicity (K.homology 0) x =
      principalDivisorFamilyCoefficient C f
        (fun j : {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
            relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1} =>
          supportComponentIdeal F j.1)
        (fun j => supportComponentIdeal_integral F j.1)
        (fun j => supportComponentPeriodicDeterminant C f F K e k hHk j.1 j.2) x := by
  classical
  let J := {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
    relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1}
  let W : J → X.IdealSheafData := fun j => supportComponentIdeal F j.1
  have hW (j : J) : IsIntegral (W j).subscheme := supportComponentIdeal_integral F j.1
  let g : ∀ j : J, (rationalFunctions (W j).subscheme)ˣ := fun j =>
    supportComponentPeriodicDeterminant C f F K e k hHk j.1 j.2
  change _ = principalDivisorFamilyCoefficient C f W hW g x
  rw [← neg_sub (sheafMultiplicity (K.homology 0) x) (sheafMultiplicity (K.homology 1) x),
    sheafMultiplicity_sub_eq_periodicLength]
  have hsupport (y : X) (hy : y ∈ SheafOfModules.supp F) :
      relativeDimension C.dimensionFunction f y ≤ k + 1 :=
    relativeDimension_le_of_support_dimension_le C f F (k + 1) hFk y hy
  by_cases htopx : ∀ j : J, x ∉ (W j).support
  · have hfinite := isFiniteLength_stalk_of_not_mem_top_components C f F k hsupport x hx
      fun Z hZ => (mem_supportComponentIdeal_support F Z x).not.1 (htopx ⟨Z, hZ⟩)
    rw [← sheafMultiplicity_sub_eq_periodicLength,
      sheafMultiplicity_sub_eq_zero_of_finiteLength F K e x hfinite, neg_zero]
    symm
    unfold principalDivisorFamilyCoefficient
    refine finsum_eq_zero_of_forall_eq_zero fun j ↦ ?_
    exact principalDivisorPushforward_apply_eq_zero_of_notMem_support C f (W j) (hW j)
      (g j) (htopx j)
  obtain ⟨j, hj⟩ := not_forall.mp htopx
  exact neg_periodicLength_eq_coefficient_of_mem_supportComponent C f F K e k hHk hsupport x hx
    j.1 j.2 ((mem_supportComponentIdeal_support F j.1 x).1 (not_not.mp hj))

/-- **Stacks 02SB.** Let `F` be a coherent sheaf on a scheme `X` locally of finite type over the
base, carrying a `(2, 1)`-periodic complex whose support has delta-dimension at most `k + 1` and
whose two cohomology sheaves are supported in delta-dimension at most `k`. Then the two cohomology
sheaves are coherent, their supports have delta-dimension at most `k`, and the associated
`k`-cycles `[H⁰]_k` and `[H¹]_k` are rationally equivalent. -/
@[stacks 02SB]
theorem rationallyEquivalent_cycles_of_twoPeriodicComplex
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (k : ℤ)
    (hFk : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hHk : ∀ (i : ZMod 2) (x : X),
      x ∈ SheafOfModules.supp (K.homology i) →
        relativeDimension C.dimensionFunction f x ≤ k) :
    ∃ (h₀ : (K.homology (0 : ZMod 2)).IsCoherent)
      (h₁ : (K.homology (1 : ZMod 2)).IsCoherent),
      letI := h₀
      letI := h₁
      ∃ (d₀ : schemeDeltaDimension C
          ((reducedSupport (K.homology 0)).subschemeι ≫ f) ≤ (k : EInt))
        (d₁ : schemeDeltaDimension C
          ((reducedSupport (K.homology 1)).subschemeι ≫ f) ≤ (k : EInt)),
        RationallyEquivalent C f k
          (cycleAssociatedToCoherentSheaf C f (K.homology 0) k d₀)
          (cycleAssociatedToCoherentSheaf C f (K.homology 1) k d₁) := by
  let h₀ : (K.homology (0 : ZMod 2)).IsCoherent := homology_isCoherent C f F K e 0
  let h₁ : (K.homology (1 : ZMod 2)).IsCoherent := homology_isCoherent C f F K e 1
  refine ⟨h₀, h₁, ?_⟩
  let d₀ : schemeDeltaDimension C
      ((reducedSupport (K.homology 0)).subschemeι ≫ f) ≤ (k : EInt) :=
    schemeDeltaDimension_reducedSupport_le_of_pointwise C f (K.homology 0) k (hHk 0)
  let d₁ : schemeDeltaDimension C
      ((reducedSupport (K.homology 1)).subschemeι ≫ f) ≤ (k : EInt) :=
    schemeDeltaDimension_reducedSupport_le_of_pointwise C f (K.homology 1) k (hHk 1)
  refine ⟨d₀, d₁, ?_⟩
  by_cases htop : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)
  · rw [homology_cycles_eq_of_stalks_finiteLength C f F K e k d₀ d₁
      fun x hx => isFiniteLength_stalk_of_relativeDimension_eq C f F htop hx]
    change _ - _ ∈ rationalEquivalences C f k
    rw [sub_self]
    exact (rationalEquivalences C f k).zero_mem
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let : QuasiSober (SheafOfModules.supp F) :=
    (SheafOfModules.isClosed_supp F).isClosedEmbedding_subtypeVal.quasiSober
  let J := {Z : irreducibleComponents (SheafOfModules.supp F : Set X) //
    relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1}
  let W : J → X.IdealSheafData := fun j => supportComponentIdeal F j.1
  have hW (j : J) : IsIntegral (W j).subscheme := supportComponentIdeal_integral F j.1
  have hDim (j : J) :
      schemeDeltaDimension C ((W j).subschemeι ≫ f) = ((k + 1 : ℤ) : EInt) :=
    supportComponentIdeal_schemeDeltaDimension C f F j.1 (k + 1) j.2
  have hLocal : LocallyFinite (fun j : J => ((W j).support : Set X)) :=
    supportComponentIdeal_locallyFinite F _
  let g : ∀ j : J, (rationalFunctions (W j).subscheme)ˣ := fun j =>
    supportComponentPeriodicDeterminant C f F K e k hHk j.1 j.2
  suffices hrat : RationallyEquivalent C f k
      (cycleAssociatedToCoherentSheaf C f (K.homology 1) k d₁)
      (cycleAssociatedToCoherentSheaf C f (K.homology 0) k d₀) by
    simpa only [neg_sub] using (rationalEquivalences C f k).neg_mem hrat
  apply rationallyEquivalent_of_principalDivisorFamily_coefficients_on_dimension
    C f k _ _ W hW hDim hLocal g
  intro x hx
  rw [cycleDifference_apply_eq_stalkLengthDifference_of_relativeDimension
    C f (K.homology 1) (K.homology 0) k d₁ d₀ x hx]
  exact sheafMultiplicity_sub_eq_principalDivisorFamilyCoefficient C f F K e k hFk hHk x hx

end Stacks.Chow
