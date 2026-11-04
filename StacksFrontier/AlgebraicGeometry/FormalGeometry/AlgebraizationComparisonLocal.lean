module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdeal

/-!
# Comparing local cohomology with completed local cohomology, the local case

Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊆ A` be an ideal, let `M` be a finite `A`-module
and let `s` and `d` be integers. Write `(-)^∧` for derived `I`-adic completion. Stacks 0DXP
asserts, assuming that `A` is `I`-adically complete with a dualizing complex, that
`cd(A, I) ≤ d`, and that every prime `𝔭 ∉ V(I)` with `V(𝔭) ∩ V(I) ≠ {𝔪}` satisfies
`depth(M_𝔭) ≥ s` or `depth(M_𝔭) + dim(A/𝔭) > d + s`, that there is an ideal `J₀` with
`V(J₀) ∩ V(I) = {𝔪}` such that for every ideal `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}` the map

`RΓ_J(M) ⟶ RΓ_J(M)^∧ = RΓ_𝔪(M)^∧`

is an isomorphism on cohomology in degrees `≤ s`.

This is the case `J = 𝔪` of Stacks 0EFL, which the source states first because it carries the
structure of the argument without the inequalities. The equality displayed in the statement is
proved here, and so is the conclusion, by the source's reduction to Stacks 0EFL.

## Main definitions

* `Stacks.Algebraization.LocalAlgebraizationHypotheses` — hypotheses (1), (3) and (4) of the
  source.
* `Stacks.Algebraization.IsLocalAlgebraizationIdeal` — the conclusion of the source, as a
  property of a candidate ideal `J₀`.

## Main results

* `Stacks.Algebraization.completedLocalCohomologyMaximalIdealIso` — the equality
  `RΓ_J(M)^∧ = RΓ_𝔪(M)^∧` appearing in the statement of the source, for every ideal `J` with
  `V(J) ∩ V(I) = {𝔪}`.
* `Stacks.Algebraization.exists_isLocalAlgebraizationIdeal` — **Stacks 0DXP**: the ideal `J₀`
  exists.
* `Stacks.Algebraization.isLocalAlgebraizationIdeal_of_lt_zero` — the conclusion for `s < 0`,
  with `J₀ = 𝔪`.
* `Stacks.Algebraization.LocalAlgebraizationHypotheses.toAlgebraizationHypotheses` — the
  hypotheses of the source give those of Stacks 0EFL at `J = 𝔪`, for any dimension function and
  with `δmax = δmin = δ(𝔪)`.
* `Stacks.Algebraization.isLocalAlgebraizationIdeal_of_isAlgebraizationIdeal` — the conclusion
  of Stacks 0EFL at `J = 𝔪` gives the conclusion of the source.

## Implementation notes

`V(J₀) ∩ V(I) = {𝔪}` forces `𝔪 ∈ V(I)`, so the source statement is unattainable for `I = A`,
where `V(I)` is empty; the properness of `I` is therefore a field of
`Stacks.Algebraization.LocalAlgebraizationHypotheses` and a parameter of
`Stacks.Algebraization.IsLocalAlgebraizationIdeal`, exactly as in the development of
Stacks 0DXM. In a local ring `I ≠ ⊤` is `I ⊆ 𝔪`.

Condition (4) of the source is phrased against `dim(A/𝔭)`, whereas the condition it specializes
from in Stacks 0EFL is phrased against the relative dimension `dim((A/𝔭)_𝔮)` for
`𝔮 ∈ V(𝔭) ∩ V(J) ∩ V(I)`. At `J = 𝔪` the only available `𝔮` is `𝔪` itself, where the two agree;
`Stacks.Algebraization.ringKrullDim_localization_maximalIdeal_quotient_map` records that. The
hypotheses are stated in the source's own form, with `dim(A/𝔭)`.

The equality of the statement is the chain
`Stacks.Algebraization.completedLocalCohomologyShrinkIso`, which is the opening paragraph of
the source's proof: Stacks 0A6W and Stacks 0BJC, together with the fact that local cohomology
sees its support ideal only through its zero locus. The source's first step, replacing `RΓ_𝔞` by
`RΓ_{V(𝔞)}`, is vacuous in this library's model of local cohomology.

The case `s < 0` needs the vanishing of `Hⁱ(RΓ_𝔪(M)^∧)` for `i < 0`. The source gets this from
Stacks 0DXJ; the library's route is the same statement for the derived limit of the tower
`n ↦ RΓ_𝔪(M/IⁿM)`, which is Stacks 0EEW, together with the identification of `RΓ_𝔪(M)^∧` with
that derived limit, which is part (1) of the same tag.

The source's proof of the lemma is "this is a special case of Stacks 0EFL, since condition (5)(c)
is implied by condition (4) as `δmax = δmin = δ(𝔪)`". Both halves of that specialization are
carried out: `Stacks.Algebraization.LocalAlgebraizationHypotheses.toAlgebraizationHypotheses` on
the hypotheses and `Stacks.Algebraization.isLocalAlgebraizationIdeal_of_isAlgebraizationIdeal` on
the conclusion. The specialization of the hypotheses needs a dimension function on `Spec(A)`,
which the statement of Stacks 0DXP does not mention, so one is taken as data; the source's
condition (5) is then discharged in its form (5)(c), whose bound `d + s - 2` is weaker than the
bound `d + s` of condition (4). A Noetherian local ring need not admit a dimension function, so
that datum is a hypothesis beyond the source's, and it is named in the tag attribute of
`Stacks.Algebraization.exists_isLocalAlgebraizationIdeal`. The dualizing complex of that
statement lives in the ring's own module universe, as it does in Stacks 0EFI and Stacks 0EFH.

## References

* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0DXM](https://stacks.math.columbia.edu/tag/0DXM)
* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Algebraization

/-- The hypotheses (1), (3) and (4) of Stacks 0DXP for a Noetherian local ring `(A, 𝔪)`.
Condition (2) of the source is empty.

Primes in `V(I)` carry no condition. A prime `𝔭 ∉ V(I)` with `V(𝔭) ∩ V(I) ≠ {𝔪}` must have
`depth(M_𝔭) ≥ s` or `depth(M_𝔭) + dim(A/𝔭) > d + s`. The source's standing assumption that `I`
is proper is recorded as `ne_top`; without it `V(I)` is empty and the conclusion is
unattainable. -/
public structure LocalAlgebraizationHypotheses
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A)) : Prop where
  /-- The ideal `I` is proper, so that `𝔪 ∈ V(I)`. -/
  ne_top : I ≠ ⊤
  /-- The ring is `I`-adically complete. -/
  adicComplete : IsAdicComplete I A
  /-- The ring has a dualizing complex, witnessed by `omega`. -/
  dualizing : Dualizing.IsDualizingComplex (A := A) (K := omega)
  /-- The cohomological dimension of `I` is at most `d`. -/
  cohomologicalDimension_le :
    Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d
  /-- Condition (4): a prime outside `V(I)` whose closed set meets `V(I)` in more than `𝔪` has
  depth at least `s`, or depth plus the dimension of `A/𝔭` exceeding `d + s`. -/
  depthOrDimensionBound : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ≠
        {closedPoint A} →
      ((enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) ≥ (s : EInt)) ∨
        (enatToEInt
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M)) +
            krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal)) > ((d + s : ℤ) : EInt)))

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

omit [IsNoetherianRing A] in
/-- An ideal meeting `V(I)` in the closed point only meets it in the same set as `𝔪` does. -/
public theorem zeroLocus_inter_eq_maximalIdeal_inter {I J : Ideal A} (hI : I ≠ ⊤)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) :=
  hV.trans (zeroLocus_maximalIdeal_inter hI).symm

/-- **Stacks 0DXP, the equality displayed in the statement.** For an ideal `J` of a Noetherian
local ring with `V(J) ∩ V(I) = {𝔪}`, the derived `I`-adic completions of `RΓ_J(M)` and of
`RΓ_𝔪(M)` agree.

This is the opening paragraph of the source's proof: by Stacks 0A6W completing after `RΓ_I`
changes nothing, by Stacks 0BJC the iterated local cohomology is `RΓ_{J + I}`, and `V(J + I)`
only depends on `V(J) ∩ V(I)`. -/
public def completedLocalCohomologyMaximalIdealIso (I J : Ideal A) (hI : I ≠ ⊤)
    (M : ModuleCat.{u} A)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    Dualizing.completedLocalCohomology A I J I.fg_of_isNoetherianRing
        J.fg_of_isNoetherianRing M ≅
      Dualizing.completedLocalCohomology A I (maximalIdeal A) I.fg_of_isNoetherianRing
        (Ideal.fg_of_isNoetherianRing _) M :=
  completedLocalCohomologyShrinkIso A I (maximalIdeal A) J I.fg_of_isNoetherianRing
    (Ideal.fg_of_isNoetherianRing _) J.fg_of_isNoetherianRing M
    (zeroLocus_inter_eq_maximalIdeal_inter hI hV)

/-- The conclusion of Stacks 0DXP, as a property of a candidate ideal `J₀`.

The zero locus of `J₀` meets `V(I)` in the closed point only, and for every ideal `J ⊆ J₀` with
that same property the canonical map `RΓ_J(M) ⟶ RΓ_𝔪(M)^∧` of
`Stacks.Algebraization.localCohomologyToCompletedLocalCohomology` is an isomorphism on
cohomology in degrees `≤ s`. The properness of `I` is a parameter: it is what makes the closed
point lie on `V(I)`, and hence what makes the comparison map available. -/
public structure IsLocalAlgebraizationIdeal
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I ≠ ⊤) (s : ℤ) (J₀ : Ideal A) : Prop where
  /-- The zero locus of `J₀` meets `V(I)` in the closed point only. -/
  zeroLocus_inter :
    PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}
  /-- For every admissible further shrinking the comparison with the completion at `𝔪` is an
  isomorphism in degrees `≤ s`. -/
  isIso : ∀ J : Ideal A, J ≤ J₀ →
      ∀ hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        {closedPoint A},
      ∀ i : ℤ, i ≤ s →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        (localCohomologyToCompletedLocalCohomology A I (maximalIdeal A) J
          I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
          J.fg_of_isNoetherianRing (ModuleCat.of A M)
          (zeroLocus_inter_eq_maximalIdeal_inter hI hV)))

/-- **Stacks 0DXP for `s < 0`.** For negative `s` the maximal ideal itself has the property
asserted of `J₀`: local cohomology of a module vanishes in negative degrees, and so does the
cohomology of the derived `I`-adic completion of `RΓ_𝔪(M)`, so the comparison map is an
isomorphism in every degree `≤ s`.

The second vanishing is the reason the source isolates this case; it is part (1) of Stacks 0EEW,
the identification of `RΓ_𝔪(M)^∧` with a derived limit of the tower `n ↦ RΓ_𝔪(M/IⁿM)`. The
hypotheses of Stacks 0DXP are carried but unused: for `s < 0` the conclusion holds for every
finite module. -/
public theorem isLocalAlgebraizationIdeal_of_lt_zero (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (H : LocalAlgebraizationHypotheses (M := M) I s d omega)
    (hs : s < 0) :
    IsLocalAlgebraizationIdeal (M := M) I H.ne_top s (maximalIdeal A) where
  zeroLocus_inter := zeroLocus_maximalIdeal_inter H.ne_top
  isIso J _ _ i hi := by
    refine IsZero.isIso ?_ ?_ _
    · exact Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg A J
        J.fg_of_isNoetherianRing (ModuleCat.of A M) i (lt_of_le_of_lt hi hs)
    · exact Dualizing.isZero_homology_completedLocalCohomology_of_neg A I (maximalIdeal A)
        I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of A M)
        (Dualizing.isDerivedLimit_completedLocalCohomology A I (maximalIdeal A)
          I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of A M)) i
        (lt_of_le_of_lt hi hs)

/-- **The hypotheses of Stacks 0DXP specialize those of Stacks 0EFL at `J = 𝔪`.** Given any
dimension function `δ` on `Spec(A)`, the hypotheses (1), (3) and (4) of Stacks 0DXP give the
hypotheses (1), (3), (4) and (5) of Stacks 0EFL for `J = 𝔪`, with `δmax = δmin = δ(𝔪)`.

At `J = 𝔪` the set `V(𝔪) ∩ V(I)` is the single closed point, so `δ` attains both its maximum and
its minimum there at `𝔪`, and the relative dimension `dim((A/𝔭)_𝔮)` of Stacks 0EFL is
`dim(A/𝔭)`. Condition (5) then holds in its form (5)(c), whose bound is
`d + s + δmax - δmin - 2 = d + s - 2`: at a prime where the depth is less than `s`, condition
(4) already gives the stronger bound `d + s`. This is the source's own reduction. -/
public theorem LocalAlgebraizationHypotheses.toAlgebraizationHypotheses {I : Ideal A} {s d : ℤ}
    {omega : DerivedCategory (ModuleCat.{w} A)}
    (H : LocalAlgebraizationHypotheses (M := M) I s d omega)
    (δ : PrimeSpectrum A → ℤ) (hδ : IsDimensionFunctionProp δ) :
    AlgebraizationHypotheses (M := M) I (maximalIdeal A) s d omega δ
      (δ (closedPoint A)) (δ (closedPoint A)) := by
  have hdim : ∀ (p : PrimeSpectrum A) (q : PrimeSpectrum A),
      q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
        PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A)) ∩
        PrimeSpectrum.zeroLocus (I : Set A) →
      ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) =
        ringKrullDim (A ⧸ p.asIdeal) := fun p q hq ↦
    ringKrullDim_localization_quotient_map_of_eq_closedPoint
      (eq_closedPoint_of_mem_zeroLocus_maximalIdeal hq.1.2) p.asIdeal
  have hbase : ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      p ∉ associatedSubset I (maximalIdeal A) →
      ((enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) ≥ (s : EInt)) ∨
        (enatToEInt
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M)) +
            krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal)) > ((d + s : ℤ) : EInt))) :=
    fun p hp hT ↦ H.depthOrDimensionBound p hp
      (fun h ↦ hT ((mem_associatedSubset_maximalIdeal_iff H.ne_top p).2 h))
  have himage : δ '' (PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A)) = {δ (closedPoint A)} := by
    rw [zeroLocus_maximalIdeal_inter H.ne_top, Set.image_singleton]
  refine ⟨H.adicComplete, H.dualizing, H.cohomologicalDimension_le, ?_, hδ, ?_, ?_, ?_⟩
  · intro p hp hT
    rcases hbase p hp hT with h | h
    · exact Or.inl h
    · exact Or.inr fun q hq ↦ by rw [hdim p q hq]; exact h
  · rw [himage]; exact isGreatest_singleton
  · rw [himage]; exact isLeast_singleton
  · intro p hp hT _ hdepth
    rcases hbase p hp hT with h | h
    · exact absurd h (not_le.mpr hdepth)
    · refine Or.inr (Or.inr fun q hq ↦ ?_)
      rw [hdim p q hq]
      refine lt_of_le_of_lt (WithBotTop.coe_le_coe.mpr ?_) h
      omega

/-- **The conclusion of Stacks 0EFL at `J = 𝔪` is the conclusion of Stacks 0DXP.** An ideal `J₀`
with the property that Stacks 0EFL asserts, for the ideal `𝔪`, has the property that Stacks 0DXP
asserts.

The two conclusions differ only in how the condition on `V(J) ∩ V(I)` is written: in a local ring
with `I` proper it is `{𝔪}` exactly when it is `V(𝔪) ∩ V(I)`. The comparison map is literally the
same one. -/
public theorem isLocalAlgebraizationIdeal_of_isAlgebraizationIdeal {I : Ideal A} (hI : I ≠ ⊤)
    {s : ℤ} {J₀ : Ideal A}
    (h : IsAlgebraizationIdeal (M := M) I (maximalIdeal A) s J₀) :
    IsLocalAlgebraizationIdeal (M := M) I hI s J₀ where
  zeroLocus_inter := h.zeroLocus_inter.trans (zeroLocus_maximalIdeal_inter hI)
  isIso J hJ hV i hi :=
    h.isIso J hJ (zeroLocus_inter_eq_maximalIdeal_inter hI hV) i hi

/-- A dimension function in the bundled sense of Stacks 02I8 satisfies the unbundled predicate
`IsDimensionFunctionProp` of Stacks 02I9.

The two formulations of "no intermediate point" are contrapositives of one another:
`TopologicalSpace.IsImmediateSpecialization` says that every point between `x` and `y` is one of
the two endpoints. -/
public theorem isDimensionFunctionProp_toFun {X : Type*} [TopologicalSpace X]
    (δ : TopologicalSpace.DimensionFunction X) : IsDimensionFunctionProp δ.toFun :=
  ⟨fun _ _ h hne => δ.strictAnti_specializes h hne, fun _ _ h => δ.step_immediate h⟩

/-- **Stacks 0DXP.** Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊆ A` be a proper ideal, let
`M` be a finite `A`-module and let `s` and `d` be integers. Assume `A` is `I`-adically complete
with a dualizing complex, that `cd(A, I) ≤ d`, and that every prime `𝔭 ∉ V(I)` with
`V(𝔭) ∩ V(I) ≠ {𝔪}` has `depth(M_𝔭) ≥ s` or `depth(M_𝔭) + dim(A/𝔭) > d + s`. Then there is an
ideal `J₀` with `V(J₀) ∩ V(I) = {𝔪}` such that for every ideal `J ⊆ J₀` with
`V(J) ∩ V(I) = {𝔪}` the canonical map

`RΓ_J(M) ⟶ RΓ_𝔪(M)^∧`

is an isomorphism on cohomology in all degrees `≤ s`.

This is the source's own proof: the case `s < 0` is
`Stacks.Algebraization.isLocalAlgebraizationIdeal_of_lt_zero`, and for `0 ≤ s` the statement is
the case `J = 𝔪` of Stacks 0EFL, by
`Stacks.Algebraization.LocalAlgebraizationHypotheses.toAlgebraizationHypotheses` on the
hypotheses and `Stacks.Algebraization.isLocalAlgebraizationIdeal_of_isAlgebraizationIdeal` on
the conclusion.

Condition (5) of Stacks 0EFL is stated against a dimension function on `Spec(A)`, which the
statement of Stacks 0DXP does not mention. No such datum is assumed here: hypothesis (1)
provides a dualizing complex, and the dimension function attached to one by Stacks 0A7Z is
`Dualizing.dualizingDimensionFunctionOfArbitraryUniverse`. -/
@[stacks 0DXP "existence of J₀"]
public theorem exists_isLocalAlgebraizationIdeal (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : LocalAlgebraizationHypotheses (M := M) I s d omega) :
    ∃ J₀ : Ideal A, IsLocalAlgebraizationIdeal (M := M) I H.ne_top s J₀ := by
  set δ := Dualizing.dualizingDimensionFunctionOfArbitraryUniverse omega H.dualizing with hδdef
  obtain ⟨J₀, h⟩ := exists_isAlgebraizationIdeal (M := M) I (maximalIdeal A) s d omega δ.toFun
    (δ (closedPoint A)) (δ (closedPoint A))
    (H.toAlgebraizationHypotheses δ.toFun (isDimensionFunctionProp_toFun δ))
  exact ⟨J₀, isLocalAlgebraizationIdeal_of_isAlgebraizationIdeal H.ne_top h⟩

end

end Stacks.Algebraization

end
