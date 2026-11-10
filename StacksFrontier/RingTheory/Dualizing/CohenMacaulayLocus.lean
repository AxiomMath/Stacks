module

public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayFromModule

/-!
# The Cohen--Macaulay locus of a ring with a dualizing complex

Let `A` be a Noetherian ring with a dualizing complex `ω`. The set of primes `𝔭` at which the
local ring `A_𝔭` is Cohen--Macaulay is a dense open subset of `Spec(A)`.

Openness is read off the supports of the cohomology modules of `ω`. Derived extension of scalars
along `A → A_𝔭` is flat, so it commutes with cohomology, whence `H^i(ω_𝔭)` vanishes exactly when
`𝔭` avoids `Supp_A H^i(ω)`; and `A_𝔭` is Cohen--Macaulay exactly when `ω_𝔭` has cohomology in at
most one degree, which is [Stacks, Tag 0AWS] read through the criterion of [Stacks, Tag 0B5A].
Since `ω` is bounded, those supports are finitely many closed sets, and "at most one of them
contains `𝔭`" cuts out a finite intersection of their complements around any such `𝔭`.

Density needs no dualizing complex: a minimal prime has `dim(A_𝔭) = 0`, so `A_𝔭` is
Cohen--Macaulay, and a set of primes containing every minimal prime meets every nonempty open,
because every prime specializes from a minimal prime below it.

## Main results

* `Dualizing.isZero_homology_localizationAtPrime_iff_notMem_support` identifies vanishing of the
  cohomology of the localized complex with avoidance of the support.
* `Dualizing.exists_homology_concentrated_of_isMaximalCohenMacaulay_self` is the implication
  (1) ⇒ (2) of [Stacks, Tag 0AWS].
* `Dualizing.isMaximalCohenMacaulay_localizationAtPrime_iff_notMem_support` is the pointwise
  criterion that openness is read off.
* `Dualizing.isOpen_setOf_isMaximalCohenMacaulay_of_isDualizingComplex` and
  `Dualizing.dense_setOf_isMaximalCohenMacaulay` are the two halves.
* `Dualizing.isOpen_and_dense_setOf_isMaximalCohenMacaulay_of_isDualizingComplex` is Tag 0EHT,
  and `Dualizing.isOpen_and_dense_setOf_isCohenMacaulayLocalRingPropForm` restates it in
  Definition 00NC's spelling.

## Implementation notes

Cohen--Macaulayness of the local ring `A_𝔭` is written `Module.IsMaximalCohenMacaulay` of
`Localization.AtPrime 𝔭` over itself, the spelling the other Cohen--Macaulay-locus statements of
this library use (tags 00RF, 00RG, 00RH); it agrees with Definition 00NC's condition at `𝔭` by
`Dualizing.isCohenMacaulayAtMaximalIdeal_self_iff_isMaximalCohenMacaulay` together with
`Dualizing.isCohenMacaulayLocalRingPropForm_iff_isCohenMacaulayAtMaximalIdeal`. "Dense open" is
the conjunction of `IsOpen` and `Dense`.

The dualizing complex is an argument rather than an existentially bound witness; since the
conclusion does not mention it, the two readings are equivalent and this one is the usable form.

Vanishing of `H^i(ω_𝔭)` is turned into a statement about `Supp_A H^i(ω)` without ever needing the
`A_𝔭`-module structure on the base change: being a subsingleton depends only on the underlying
type, so the additive comparison `Dualizing.extendScalarsCarrierAddEquiv` between the extension
of scalars and the tensor product suffices, and the tensor product is a localization of modules
by `tensorProduct_isLocalizedModule`, whose vanishing is avoidance of the support by
`Module.notMem_support_iff`. The intervening universe lift is invisible to supports by
`LinearEquiv.support_eq`. In particular no finiteness of the cohomology is used for that step.

The source argues openness by choosing one `f ∉ 𝔭` killing all the other cohomology modules, so
that `D(f)` lies in the locus. The finite intersection of support complements used here is that
`D(f)`, before a generator of the ideal is chosen; nothing in the argument needs the single
element.

## References

* [Stacks Project, Tag 0EHT](https://stacks.math.columbia.edu/tag/0EHT)
* [Stacks Project, Tag 0EHS](https://stacks.math.columbia.edu/tag/0EHS)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-! ### Bookkeeping -/

/-- Shifting reindexes the vanishing of cohomology. -/
theorem isZero_homology_shift_iff {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (m i j : ℤ) (hij : m + i = j) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj (K⟦m⟧)) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) j).obj K) :=
  (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).shiftIso
    m i j hij).app K).isZero_iff

/-- For a local ring over itself the dimension of the support is the Krull dimension, so the
Cohen--Macaulay conditions of Definitions 00N3 and 00NF agree. -/
theorem isCohenMacaulayAtMaximalIdeal_self_iff_isMaximalCohenMacaulay
    (R : Type*) [CommRing R] [IsLocalRing R] :
    Module.IsCohenMacaulayAtMaximalIdeal R R ↔ Module.IsMaximalCohenMacaulay R R := by
  change (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) = Module.supportDim R R ↔
    (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) = ringKrullDim R
  rw [Module.supportDim_self_eq_ringKrullDim]

/-- The underlying additive group of the extension of scalars of `M` along `algebraMap R S` is
the tensor product `S ⊗_R M`. Only additivity is recorded: the `S`-module structures agree too,
but the statements below need no more than a bijection. -/
def extendScalarsCarrierAddEquiv {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{max u v} R) :
    ((ModuleCat.extendScalars (algebraMap R S)).obj M) ≃+ TensorProduct R S M :=
  have : SMulCommClass R S ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (ModuleCat.of S S)) :=
    ⟨fun r s t ↦ mul_left_comm (algebraMap R S r) s (t : S)⟩
  let e : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { AddEquiv.refl S with map_smul' := fun r s ↦ (Algebra.smul_def (R := R) (A := S) r s).symm }
  (TensorProduct.congr e (LinearEquiv.refl R M)).toAddEquiv

/-- The extension of scalars of `M` along `A → A_𝔭` is zero exactly when `𝔭` is outside the
support of `M`: the tensor product is a localization of `M` at `𝔭`, whose vanishing is the
definition of lying outside the support. -/
theorem subsingleton_extendScalars_localizationAtPrime_iff_notMem_support {A : Type u}
    [CommRing A] (q : PrimeSpectrum A) (M : ModuleCat.{max u v} A) :
    Subsingleton ((ModuleCat.extendScalars
        (algebraMap A (Localization.AtPrime q.asIdeal))).obj M) ↔
      q ∉ Module.support A M := by
  rw [Module.notMem_support_iff]
  refine Equiv.subsingleton_congr ?_
  exact (extendScalarsCarrierAddEquiv.{u, v}
      (S := Localization.AtPrime q.asIdeal) M).toEquiv.trans
    (IsLocalizedModule.iso q.asIdeal.primeCompl
      (TensorProduct.mk A (Localization.AtPrime q.asIdeal)
        (M : Type (max u v)) 1)).toEquiv.symm

/-! ### Cohen--Macaulayness forces the cohomology into one degree -/

/-- **Stacks Project, Tag 0AWS, the implication (1) ⇒ (2).** Over a Cohen--Macaulay Noetherian
local ring a dualizing complex has cohomology in at most one degree: the criterion of
[Stacks, Tag 0B5A] puts `Ext` into the normalized shift in at most one degree, and derived Hom
out of the ring is the identity, so that `Ext` is the cohomology. -/
theorem exists_homology_concentrated_of_isMaximalCohenMacaulay_self
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (hK : IsDualizingComplex K)
    (hCM : Module.IsMaximalCohenMacaulay A A) :
    ∃ d : ℤ, ∀ i : ℤ, i ≠ d →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K) := by
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, v} K hK
  have hlift : Module.IsCohenMacaulayAtMaximalIdeal A (ULift.{v} A) := by
    change (Module.depth A (IsLocalRing.maximalIdeal A) (ULift.{v} A) : WithBot ℕ∞) =
      Module.supportDim A (ULift.{v} A)
    rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal A)
        (ULift.moduleEquiv (R := A) (M := A)),
      Module.supportDim_eq_of_equiv (ULift.moduleEquiv (R := A) (M := A))]
    exact (isCohenMacaulayAtMaximalIdeal_self_iff_isMaximalCohenMacaulay A).mpr hCM
  have hpair := ((isCohenMacaulay_iff_ext_concentrated.{u, v} (M := ULift.{v} A)
    (K⟦-m⟧) hm).out 1 2).mp hlift
  have htransfer : ∀ i : ℤ,
      ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K) →
      Nontrivial (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A (ULift.{v} A))) (K⟦-m⟧) (m + i)) := by
    intro i hi
    obtain ⟨x, y, hxy⟩ : Nontrivial
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (m + i)).obj (K⟦-m⟧)) :=
      not_subsingleton_iff_nontrivial.mp fun h => hi
        ((isZero_homology_shift_iff.{u, v} K (-m) (m + i) i (by omega)).mp
          (ModuleCat.isZero_iff_subsingleton.mpr h))
    exact ⟨(extULiftRingLinearEquiv.{u, v} A (K⟦-m⟧) (m + i)).symm x,
      (extULiftRingLinearEquiv.{u, v} A (K⟦-m⟧) (m + i)).symm y,
      (extULiftRingLinearEquiv.{u, v} A (K⟦-m⟧) (m + i)).symm.injective.ne hxy⟩
  by_cases hall : ∀ i : ℤ,
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)
  · exact ⟨0, fun i _ => hall i⟩
  · push Not at hall
    obtain ⟨k₀, hk₀⟩ := hall
    refine ⟨k₀, fun i hi => ?_⟩
    by_contra hz
    have heq := hpair (m + i) (m + k₀) (htransfer _ hz) (htransfer _ hk₀)
    omega

/-! ### Localizing the cohomology -/

/-- Degree-`i` cohomology of the derived extension of scalars along a localization is the base
change of degree-`i` cohomology, up to the universe lift the extension is composed with. -/
def homologyDerivedExtensionScalarsIso {A : Type u} [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] (S : Submonoid A) [IsLocalization S B]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj K) ≅
      (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A B)).obj
        ((ModuleCat.uliftFunctor.{u, max u v, u} A).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) :=
  (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, u, max u v}
      (algebraMap A B) (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B S)) i).app
      ((ModuleCat.uliftFunctor.{u, max u v, u} A).mapDerivedCategory.obj K) ≪≫
    (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A B)).mapIso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
        (ModuleCat.uliftFunctor.{u, max u v, u} A) i).app K)

/-- **The cohomology of the localized complex vanishes exactly off the support.** For a prime
`𝔭`, the module `H^i(K_𝔭)` is zero if and only if `𝔭` lies outside the support of `H^i(K)`. -/
theorem isZero_homology_localizationAtPrime_iff_notMem_support {A : Type u} [CommRing A]
    (q : PrimeSpectrum A) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{max u v} (Localization.AtPrime q.asIdeal)) i).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap A (Localization.AtPrime q.asIdeal))).obj K)) ↔
      q ∉ Module.support A
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K) := by
  have hiso := homologyDerivedExtensionScalarsIso.{u, v} (Localization.AtPrime q.asIdeal)
    q.asIdeal.primeCompl K i
  have hULift : Module.support A
        ((ModuleCat.uliftFunctor.{u, max u v, u} A).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) =
      Module.support A ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K) :=
    LinearEquiv.support_eq (ULift.moduleEquiv (R := A)
      (M := ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K :
        Type (max u v))))
  rw [hiso.isZero_iff, ModuleCat.isZero_iff_subsingleton,
    subsingleton_extendScalars_localizationAtPrime_iff_notMem_support.{u, v}, hULift]

/-! ### The pointwise criterion -/

/-- **Cohen--Macaulayness at a prime, read off the supports.** For a dualizing complex `ω` over a
Noetherian ring, the local ring `A_𝔭` is Cohen--Macaulay exactly when at most one cohomology
module of `ω` has `𝔭` in its support. -/
theorem isMaximalCohenMacaulay_localizationAtPrime_iff_notMem_support
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A)) (homega : IsDualizingComplex omega)
    (q : PrimeSpectrum A) :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal) ↔
      ∃ d : ℤ, ∀ i : ℤ, i ≠ d →
        q ∉ Module.support A
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj omega) := by
  have hloc := isDualizingComplex_localizationAtPrime.{u, v} omega homega q
  constructor
  · intro hCM
    obtain ⟨d, hd⟩ :=
      exists_homology_concentrated_of_isMaximalCohenMacaulay_self.{u, v} _ hloc hCM
    exact ⟨d, fun i hi => (isZero_homology_localizationAtPrime_iff_notMem_support.{u, v}
      q omega i).mp (hd i hi)⟩
  · rintro ⟨d, hd⟩
    exact (isCohenMacaulayAtMaximalIdeal_self_iff_isMaximalCohenMacaulay _).mp
      (isCohenMacaulayAtMaximalIdeal_self_of_homology_concentrated.{u, v} _ hloc d fun i hi =>
        (isZero_homology_localizationAtPrime_iff_notMem_support.{u, v} q omega i).mpr (hd i hi))

/-! ### Openness -/

/-- **The Cohen--Macaulay locus of a ring with a dualizing complex is open.** Around a prime at
which the local ring is Cohen--Macaulay, the complements of the supports of the other cohomology
modules of `ω` meet in an open set — finitely many of them matter, because `ω` is bounded — and
that open set lies in the locus. -/
theorem isOpen_setOf_isMaximalCohenMacaulay_of_isDualizingComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A)) (homega : IsDualizingComplex omega) :
    IsOpen {q : PrimeSpectrum A | Module.IsMaximalCohenMacaulay
      (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)} := by
  obtain ⟨a, b, I, hIGE, hILE, hinj, ⟨eI⟩⟩ := homega.finiteInjectiveDimension
  have := hIGE
  have := hILE
  have hGE : omega.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eI.symm a
  have hLE : omega.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso eI.symm b
  have houtside : ∀ i : ℤ, i ∉ Set.Icc a b → ∀ q : PrimeSpectrum A,
      q ∉ Module.support A
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj omega) := by
    intro i hi q
    have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj omega) := by
      rw [Set.mem_Icc] at hi
      rcases not_and_or.mp hi with h | h
      · exact DerivedCategory.isZero_of_isGE omega a i (by omega)
      · exact DerivedCategory.isZero_of_isLE omega b i (by omega)
    have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj omega) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    rw [Module.support_eq_empty]
    exact Set.notMem_empty q
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  obtain ⟨d, hd⟩ :=
    (isMaximalCohenMacaulay_localizationAtPrime_iff_notMem_support.{u, v} omega homega q).mp hq
  refine ⟨⋂ i ∈ Set.Icc a b \ {d},
    (Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj omega))ᶜ, ?_, ?_, ?_⟩
  · intro q' hq'
    refine (isMaximalCohenMacaulay_localizationAtPrime_iff_notMem_support.{u, v}
      omega homega q').mpr ⟨d, fun i hi => ?_⟩
    by_cases hmem : i ∈ Set.Icc a b
    · exact Set.mem_iInter₂.mp hq' i ⟨hmem, hi⟩
    · exact houtside i hmem q'
  · refine Set.Finite.isOpen_biInter ((Set.finite_Icc a b).subset Set.sdiff_subset) fun i _ => ?_
    have : Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj omega) :=
      homega.finiteCohomology i
    exact Module.isClosed_support.isOpen_compl
  · exact Set.mem_iInter₂.mpr fun i hi => hd i hi.2

/-! ### Density -/

/-- A set of primes containing every minimal prime is dense: every prime specializes from a
minimal prime below it. -/
theorem dense_of_minimalPrimes_subset {A : Type u} [CommRing A] {W : Set (PrimeSpectrum A)}
    (hW : ∀ q : PrimeSpectrum A, q.asIdeal ∈ minimalPrimes A → q ∈ W) : Dense W := by
  intro x
  obtain ⟨m, hm, hmx⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
  have hmp : m.IsPrime := hm.1.1
  have hsp : (⟨m, hmp⟩ : PrimeSpectrum A) ⤳ x := (PrimeSpectrum.le_iff_specializes _ _).mp hmx
  exact closure_mono (Set.singleton_subset_iff.mpr (hW ⟨m, hmp⟩ hm))
    (specializes_iff_mem_closure.mp hsp)

/-- **The Cohen--Macaulay locus is dense.** The local ring at a minimal prime has dimension zero,
hence is Cohen--Macaulay, and the minimal primes are dense. No dualizing complex is needed. -/
theorem dense_setOf_isMaximalCohenMacaulay (A : Type u) [CommRing A] :
    Dense {q : PrimeSpectrum A | Module.IsMaximalCohenMacaulay
      (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)} :=
  dense_of_minimalPrimes_subset fun q hq =>
    Module.isMaximalCohenMacaulay_self_of_ringKrullDim_eq_zero (by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal,
        Ideal.height_eq_zero_iff.mpr hq]
      rfl)

/-! ### Tag 0EHT -/

/-- **Stacks Project, Tag 0EHT.** For a Noetherian ring with a dualizing complex, the set of
primes at which the local ring is Cohen--Macaulay is a dense open subset of the spectrum. -/
@[stacks 0EHT]
theorem isOpen_and_dense_setOf_isMaximalCohenMacaulay_of_isDualizingComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A)) (homega : IsDualizingComplex omega) :
    IsOpen {q : PrimeSpectrum A | Module.IsMaximalCohenMacaulay
        (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)} ∧
      Dense {q : PrimeSpectrum A | Module.IsMaximalCohenMacaulay
        (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)} :=
  ⟨isOpen_setOf_isMaximalCohenMacaulay_of_isDualizingComplex.{u, v} omega homega,
    dense_setOf_isMaximalCohenMacaulay A⟩

/-- Tag 0EHT with Cohen--Macaulayness of the local ring spelled as in Definition 00NC, the form
`IsCohenMacaulayRing` quantifies over primes. -/
theorem isOpen_and_dense_setOf_isCohenMacaulayLocalRingPropForm
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A)) (homega : IsDualizingComplex omega) :
    IsOpen {q : PrimeSpectrum A |
        IsCohenMacaulayLocalRingPropForm (Localization.AtPrime q.asIdeal)} ∧
      Dense {q : PrimeSpectrum A |
        IsCohenMacaulayLocalRingPropForm (Localization.AtPrime q.asIdeal)} := by
  have hset : {q : PrimeSpectrum A |
        IsCohenMacaulayLocalRingPropForm (Localization.AtPrime q.asIdeal)} =
      {q : PrimeSpectrum A | Module.IsMaximalCohenMacaulay
        (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)} := by
    ext q
    exact (isCohenMacaulayLocalRingPropForm_iff_isCohenMacaulayAtMaximalIdeal _).trans
      (isCohenMacaulayAtMaximalIdeal_self_iff_isMaximalCohenMacaulay _)
  rw [hset]
  exact isOpen_and_dense_setOf_isMaximalCohenMacaulay_of_isDualizingComplex.{u, v} omega homega

end Dualizing

end
