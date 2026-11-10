module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparisonLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ConnectednessApplication
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternative
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.TildeStalkPrime
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
public import StacksFrontier.RingTheory.Dualizing.FiniteDimension
public import StacksFrontier.RingTheory.Serre.Defs
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conditions of Stacks 0EIF are the hypotheses of Stacks 0EFL for `s = 1`

Let `I` and `𝔞` be ideals of a Noetherian ring `A` (the source assumes `I ⊆ 𝔞`; nothing here
needs it), let `U = Spec(A) ∖ V(𝔞)` and let `F` be a coherent module on `U` satisfying
conditions (1), (2) and (3) of Stacks 0EIF (`Stacks.Algebraization.FormalSectionsHypotheses`).
The proof of Stacks 0EIF in the source begins: choose a finite `A`-module `M` with `F = M̃|_U`
(Stacks 0BK0); then "the hypotheses of Lemma 0EFL are satisfied for `s = 1` and `d = cd(A, I)`;
here we use condition (3)". This file proves that sentence.

## Main results

* `Stacks.Algebraization.exists_isGreatest_isLeast_image_dimensionFunction` — a dimension
  function on the spectrum of a Noetherian ring of finite dimension has a largest and a smallest
  value on every nonempty set of primes. These are the `δmax` and `δmin` that the hypotheses of
  Stacks 0EFL are stated against.
* `Stacks.Algebraization.depth_stalk_eq_depth_localizedModule_of_iso` and
  `Stacks.Algebraization.supportDim_stalk_eq_supportDim_localizedModule_of_iso` — for
  `F ≅ M̃|_U` and a point `x ∈ U` with prime `𝔭`, the depth and the dimension of the support
  of `F_x` are those of `M_𝔭`.
* `Stacks.Algebraization.algebraizationHypotheses_of_formalSectionsHypotheses` — the
  conditions of Stacks 0EIF give the hypotheses of Stacks 0EFL for `M`, `J = 𝔞`, `s = 1` and
  `d = cd(A, I)`.
* `Stacks.Algebraization.exists_isAlgebraizationIdeal_of_formalSectionsHypotheses` — hence the
  ideal `J₀` of Stacks 0EFL for `s = 1`, which is the first step of the proof of Stacks 0EIF.

## Implementation notes

The dimension function is chosen according to which alternative of condition (3) holds. Under
`(S₁)` off `V(I)` the first alternative of condition (5) of Stacks 0EFL holds at every relevant
prime and any dimension function serves; the one of the dualizing complex is taken. Under the
dimension alternative the function is the one condition (3)(b) provides, for which
`δmax - δmin ≤ 2` on `V(𝔞)`, so that the third alternative of condition (5) is weaker than
condition (4), which condition (2) supplies.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.AlgebraicGeometry.ReflexiveModules

/-! ### The extremal values of a dimension function -/

/-- **A dimension function has a largest and a smallest value on every nonempty set of primes**
of a Noetherian ring of finite Krull dimension: its range is finite. -/
public theorem exists_isGreatest_isLeast_image_dimensionFunction {A : Type u} [CommRing A]
    [IsNoetherianRing A] (hA : ringKrullDim A < ⊤)
    (δ : DimensionFunction (PrimeSpectrum A)) {S : Set (PrimeSpectrum A)} (hS : S.Nonempty) :
    (∃ m : ℤ, IsGreatest (δ.toFun '' S) m) ∧ ∃ m : ℤ, IsLeast (δ.toFun '' S) m := by
  have hfin : (δ.toFun '' S).Finite :=
    (finite_range_dimensionFunction δ hA).subset (Set.image_subset_range _ _)
  have hne : (δ.toFun '' S).Nonempty := hS.image _
  obtain ⟨M, hM, hMmax⟩ := Set.exists_max_image _ id hfin hne
  obtain ⟨m, hm, hmmin⟩ := Set.exists_min_image _ id hfin hne
  exact ⟨⟨M, hM, fun y hy => hMmax y hy⟩, ⟨m, hm, fun y hy => hmmin y hy⟩⟩

/-! ### Stalks of `M̃|_U` -/

section Stalks

variable {A : Type u} [CommRing A] {a : Ideal A}
  {F : (complementZeroLocus A a : Scheme).Modules} {M : ModuleCat.{u} A}
  (e : F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict (complementZeroLocus A a).ι)

include e in
/-- **The depth of `F_x` is the depth of `M_𝔭`** for `F ≅ M̃|_U` and a point `x` of `U` with
prime `𝔭`. The point and the prime are passed separately, with the equation identifying them,
so that each side is written at the spelling whose instances exist. -/
public theorem depth_stalk_eq_depth_localizedModule_of_iso
    (x : (complementZeroLocus A a : Scheme)) (p : PrimeSpectrum A)
    (hp : (p : Spec (CommRingCat.of A)) = x.1) :
    Module.depth ((complementZeroLocus A a : Scheme).presheaf.stalk x)
        (maximalIdeal ((complementZeroLocus A a : Scheme).presheaf.stalk x))
        (F.presheaf.stalk x) =
      Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) :=
  by
  have h1 := Scheme.Modules.depth_stalk_congr e x
  have h2 := Scheme.Modules.depth_stalk_restrict (complementZeroLocus A a).ι
    ((tilde.functor (CommRingCat.of A)).obj M) x
  have h3 := depth_stalk_tilde_eq_depth_localizedModule (R := CommRingCat.of A) M
    ((complementZeroLocus A a).ι.base x) p hp
  rw [h1, h2]
  exact h3

include e in
/-- **The dimension of the support of `F_x` is that of `M_𝔭`** for `F ≅ M̃|_U` and a point `x`
of `U` with prime `𝔭`. -/
public theorem supportDim_stalk_eq_supportDim_localizedModule_of_iso
    (x : (complementZeroLocus A a : Scheme)) (p : PrimeSpectrum A)
    (hp : (p : Spec (CommRingCat.of A)) = x.1) :
    Module.supportDim ((complementZeroLocus A a : Scheme).presheaf.stalk x)
        (F.presheaf.stalk x) =
      Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) :=
  by
  have h1 := Scheme.Modules.supportDim_stalk_congr e x
  have h2 := Scheme.Modules.supportDim_stalk_restrict (complementZeroLocus A a).ι
    ((tilde.functor (CommRingCat.of A)).obj M) x
  have h3 := supportDim_stalk_tilde_eq_supportDim_localizedModule (R := CommRingCat.of A) M
    ((complementZeroLocus A a).ι.base x) p hp
  rw [h1, h2]
  exact h3

/-- **A point at whose stalk a coherent module has depth zero is one of its associated
points**, on a locally Noetherian scheme: over the Noetherian local ring `𝒪_{X,x}` a finite
module of depth zero has the maximal ideal among its associated primes. This is the converse of
`Stacks.Divisors.notMem_associatedPoints_of_one_le_depth`. -/
@[ega "0 16.4.6" "(i)"]
public theorem mem_associatedPoints_of_depth_stalk_eq_zero {X : Scheme.{u}}
    [IsLocallyNoetherian X] (G : X.Modules) [G.IsCoherent] (x : X)
    (h : Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) = 0) :
    x ∈ Stacks.Divisors.associatedPoints G := by
  have : Module.Finite (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
    Scheme.Modules.finite_stalk_of_isCoherent G x
  exact (isAssociatedPrimeStacks_iff_mem_associatedPrimes _).2
    (Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes.1 h)

end Stalks

/-! ### The hypotheses of Stacks 0EFL -/

section Hypotheses

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I a : Ideal A}
  {F : (complementZeroLocus A a : Scheme).Modules} [F.IsCoherent] {M : ModuleCat.{u} A}
  [Module.Finite A M]
  (e : F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict (complementZeroLocus A a).ι)

omit [IsNoetherianRing A] in
/-- A prime outside `associatedSubset I 𝔞` is a point of `U = Spec(A) ∖ V(𝔞)`: a prime of `V(𝔞)`
has all its specializations in `V(𝔞)`, so it lies in `associatedSubset I 𝔞`. -/
private theorem mem_complementZeroLocus_of_notMem {p : PrimeSpectrum A}
    (hp : p ∉ associatedSubset I a) : p ∈ complementZeroLocus A a :=
  fun hpa => hp fun _q hq => ⟨PrimeSpectrum.zeroLocus_anti_mono
    ((PrimeSpectrum.mem_zeroLocus _ _).1 hpa) hq.1, hq.2⟩

/-- A depth below one, read in the extended integers, is depth zero. -/
private theorem eq_zero_of_enatToEInt_lt_one {n : ℕ∞} (h : enatToEInt n < ((1 : ℤ) : EInt)) :
    n = 0 := by
  by_contra hn
  exact absurd h (not_lt.2 (le_of_eq_of_le rfl
    (enatToEInt_mono (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hn)))))

omit [Module.Finite A M] in
include e in
/-- **The relative-dimension bound at a prime of `Ass(M)` off the formal locus.** If `𝔭 ∉ V(I)`
has `M_𝔭` of depth zero and its closure meets `V(I)` outside `V(𝔞)`, then condition (2) of
Stacks 0EIF gives `depth(M_𝔭) + dim((A/𝔭)_𝔮) > cd(A, I) + 1` at every `𝔮 ∈ V(𝔭) ∩ V(𝔞)`. -/
private theorem depth_add_dim_gt_of_depth_eq_zero
    (h2 : AssociatedPointsClosureDimensionBound A I a F) (p : PrimeSpectrum A)
    (hpI : p ∉ PrimeSpectrum.zeroLocus (I : Set A)) (hpT : p ∉ associatedSubset I a)
    (hd : Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M) = 0)
    (q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) (haq : a ≤ q.asIdeal) :
    enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) := by
  let x : (complementZeroLocus A a : Scheme) := ⟨p, mem_complementZeroLocus_of_notMem hpT⟩
  have : IsLocallyNoetherian (complementZeroLocus A a : Scheme) :=
    isLocallyNoetherian_of_isOpenImmersion (complementZeroLocus A a).ι
  have hx : x ∈ Stacks.Divisors.associatedPoints F :=
    mem_associatedPoints_of_depth_stalk_eq_zero F x
      ((depth_stalk_eq_depth_localizedModule_of_iso e x p rfl).trans hd)
  have hy : ∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal := by
    obtain ⟨y, ⟨hyp, hyI⟩, hya⟩ := Set.not_subset.1 hpT
    refine ⟨y, (PrimeSpectrum.mem_zeroLocus _ _).1 hyp, (PrimeSpectrum.mem_zeroLocus _ _).1 hyI,
      fun h => hya ⟨(PrimeSpectrum.mem_zeroLocus _ _).2 h, hyI⟩⟩
  have hbound := h2 x hx hpI hy q hpq haq
  rw [closureLocalDimension_eq_ringKrullDim_quotient_localizationAtPrime] at hbound
  rw [hd]
  change _ < ((0 : ℤ) : EInt) + _
  rwa [show ((0 : ℤ) : EInt) = 0 from rfl, zero_add]

include e in
/-- **The conditions of Stacks 0EIF give the hypotheses of Stacks 0EFL for `s = 1`.** Let
`I` and `𝔞` be ideals of a Noetherian ring `A`, let `F ≅ M̃|_U` be a coherent module on
`U = Spec(A) ∖ V(𝔞)` with `M` a finite `A`-module, and assume conditions (1), (2) and (3) of
Stacks 0EIF for `F`, and let `V(𝔞) ∩ V(I)` be nonempty. The source's standing assumption
`I ⊆ 𝔞` is not needed: a prime outside `V(I)` but inside `V(𝔞)` lies in the set `T` of
Stacks 0EFL, where conditions (4) and (5) ask nothing. Then there are a dualizing complex `ω`, a
dimension function `δ` on `Spec(A)` and its maximum and minimum on `V(𝔞) ∩ V(I)` for which `M`,
`J = 𝔞`, `s = 1` and `d = cd(A, I)` satisfy the hypotheses of Stacks 0EFL.

Condition (4) at a prime `𝔭` of depth zero is condition (2), `𝔭` being an associated point of
`F`. In condition (5), under `(S₁)` off `V(I)` the support of `M_𝔭` has dimension `0`; under the
dimension alternative `δ` is the function it provides, with `δmax - δmin ≤ 2`, and the third
alternative follows from condition (4). -/
public theorem algebraizationHypotheses_of_formalSectionsHypotheses
    (h : FormalSectionsHypotheses A I a F)
    (hVne : (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A)).Nonempty) :
    ∃ (omega : DerivedCategory (ModuleCat.{u} A)) (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ),
      AlgebraizationHypotheses (M := M) I a 1
        (cohomologicalDimension A I I.fg_of_isNoetherianRing) omega δ δmax δmin := by
  obtain ⟨omega, homega⟩ := h.dualizing
  have hA := Dualizing.ringKrullDim_lt_top_of_isDualizingComplex homega
  obtain ⟨δ', hδ'⟩ : ∃ δ' : DimensionFunction (PrimeSpectrum A),
      ¬ IsSerreOneOffVanishing A I a F →
        ∀ x z : PrimeSpectrum A, a ≤ x.asIdeal → a ≤ z.asIdeal → δ' x ≤ δ' z + 2 := by
    rcases h.serreOneOrSmallDimension with h3 | ⟨δ, hδ⟩
    · exact ⟨Dualizing.dualizingDimensionFunctionOfArbitraryUniverse omega homega,
        fun hn => absurd h3 hn⟩
    · exact ⟨δ, fun _ => hδ⟩
  obtain ⟨⟨δmax, hmax⟩, ⟨δmin, hmin⟩⟩ :=
    exists_isGreatest_isLeast_image_dimensionFunction hA δ' hVne
  have hbound := depth_add_dim_gt_of_depth_eq_zero e h.associatedPointsDimension
  refine ⟨omega, δ'.toFun, δmax, δmin,
    { adicComplete := h.adicComplete
      dualizing := homega
      cohomologicalDimension_le := le_rfl
      depthOrDimensionBound := ?_
      isDimensionFunction := isDimensionFunctionProp_toFun δ'
      isGreatest_δmax := hmax
      isLeast_δmin := hmin
      supplementaryBound := ?_ }⟩
  · intro p hpI hpT
    by_cases hd : Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal)) (LocalizedModule p.asIdeal.primeCompl M) = 0
    · right
      rintro q ⟨⟨hqp, hqa⟩, -⟩
      exact hbound p hpI hpT hd q hqp hqa
    · left
      exact enatToEInt_mono (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hd))
  · intro p hpI hpT _ hdlt
    have hd := eq_zero_of_enatToEInt_lt_one hdlt
    by_cases h3 : IsSerreOneOffVanishing A I a F
    · left
      let x : (complementZeroLocus A a : Scheme) :=
        ⟨p, mem_complementZeroLocus_of_notMem hpT⟩
      have hxW : x ∈ opensOffVanishing A I a :=
        (mem_opensOffVanishing A I a x).2 hpI
      let x' : (opensOffVanishing A I a).toScheme := ⟨x, hxW⟩
      have hS := min_supportDim_le_depth_of_sheafHasPropertySk _ 1 h3 x'
      have hdep := Scheme.Modules.depth_stalk_restrict (opensOffVanishing A I a).ι F x'
      have hsd := Scheme.Modules.supportDim_stalk_restrict (opensOffVanishing A I a).ι F x'
      have hdep' := depth_stalk_eq_depth_localizedModule_of_iso e
        ((opensOffVanishing A I a).ι.base x') p rfl
      have hsd' := supportDim_stalk_eq_supportDim_localizedModule_of_iso e
        ((opensOffVanishing A I a).ι.base x') p rfl
      rw [hdep, hsd, hdep', hsd', hd] at hS
      have hle : Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
        rcases min_le_iff.1 hS with h1 | h1
        · exact absurd h1 (by decide)
        · exact h1
      refine lt_of_le_of_lt (krullDimToEInt_mono hle) ?_
      rw [krullDimToEInt_natCast]
      exact WithBotTop.coe_lt_coe.2 (by norm_num)
    · right; right
      intro q hq
      obtain ⟨⟨hqp, hqa⟩, -⟩ := hq
      have hb := hbound p hpI hpT hd q hqp hqa
      obtain ⟨z₁, ⟨hz₁a, -⟩, hz₁⟩ := hmax.1
      obtain ⟨z₂, ⟨hz₂a, -⟩, hz₂⟩ := hmin.1
      have h2 := hδ' h3 z₁ z₂ hz₁a hz₂a
      change δ' z₁ = δmax at hz₁
      change δ' z₂ = δmin at hz₂
      refine lt_of_le_of_lt (WithBotTop.coe_le_coe.2 ?_) hb
      omega

include e in
/-- **The ideal `J₀` of the proof of Stacks 0EIF.** Under the conditions of Stacks 0EIF for
`F ≅ M̃|_U`, Stacks 0EFL for `s = 1` produces an ideal `J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)`
such that for every `J ⊆ J₀` with the same intersection the maps `H^i_J(M) → H^i(RΓ_𝔞(M)^∧)`
are isomorphisms for `i ≤ 1`. When `V(𝔞) ∩ V(I)` is empty `J₀ = 𝔞` serves. -/
public theorem exists_isAlgebraizationIdeal_of_formalSectionsHypotheses
    (h : FormalSectionsHypotheses A I a F) :
    ∃ J₀ : Ideal A, IsAlgebraizationIdeal (M := M) I a 1 J₀ := by
  by_cases hne : (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A)).Nonempty
  · obtain ⟨omega, δ, δmax, δmin, H⟩ :=
      algebraizationHypotheses_of_formalSectionsHypotheses e h hne
    exact exists_isAlgebraizationIdeal I a 1 _ omega δ δmax δmin H
  · exact ⟨a, isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty I a 1 h.adicComplete
      (Set.not_nonempty_iff_eq_empty.1 hne)⟩

end Hypotheses

end Stacks.Algebraization

end
