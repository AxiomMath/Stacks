module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.UFD
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.StalkwiseRegular
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Codimension-one integral subschemes over unique factorization local rings

Let `X` be a locally Noetherian scheme and `D ⊆ X` an integral closed subscheme of codimension
one.  If `𝒪_{X,x}` is a unique factorization domain for every `x ∈ D`, then `D` is an effective
Cartier divisor.

## Main results

* `AlgebraicGeometry.isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid`:
  an integral closed subscheme of codimension one along which the local rings of `X` are unique
  factorization domains is an effective Cartier divisor.

## References

* [Stacks Project, Tag 0AGA](https://stacks.math.columbia.edu/tag/0AGA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors TopologicalSpace

universe u

namespace AlgebraicGeometry

private theorem affine_prime_height_one_gives_stalk_regular
    {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (U : X.affineOpens) (hxU : x ∈ U.1)
    (p : Ideal Γ(X, U)) (hp : p.IsPrime)
    (hpU : p ≤ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal)
    (hheight : p.height = 1)
    (hUFD : UniqueFactorizationMonoid (X.presheaf.stalk x))
    (hI : I.ideal U = p) :
    ∃ f : X.presheaf.stalk x,
      IsRegular f ∧ IdealSheafData.stalk I x = Ideal.span {f} := by
  let q := U.2.primeIdealOf ⟨x, hxU⟩
  let S := X.presheaf.stalk x
  let _ : Algebra Γ(X, U) S := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime S q.asIdeal := U.2.isLocalization_stalk ⟨x, hxU⟩
  have hdisj : Disjoint (q.asIdeal.primeCompl : Set Γ(X, U)) (p : Set Γ(X, U)) :=
    Set.disjoint_left.mpr fun _ hrq hrp ↦ hrq (hpU hrp)
  let J : Ideal S := Ideal.map (algebraMap Γ(X, U) S) p
  have : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.asIdeal.primeCompl S p hp hdisj
  have hJ : J.height = 1 := by
    rw [IsLocalization.height_map_of_disjoint q.asIdeal.primeCompl p hdisj, hheight]
  have : IsDomain S := (isDomain_iff_cancelMulZero_and_nontrivial S).2
    ⟨inferInstance, inferInstance⟩
  have hprincipal := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hJ
  refine ⟨hprincipal.generator, .of_ne_zero fun hf ↦ Ideal.ne_bot_of_height_eq_one hJ ?_, ?_⟩
  · rw [← hprincipal.span_singleton_generator, hf, Ideal.span_singleton_eq_bot]
  · rw [IdealSheafData.stalk_eq_map_germ I x U hxU, hI]
    exact hprincipal.span_singleton_generator.symm

/-- The image of the generic point of `I.subscheme` is a generic point of `I.support`. -/
private lemma isGenericPoint_subschemeι_genericPoint {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] :
    IsGenericPoint (I.subschemeι (_root_.genericPoint I.subscheme)) (I.support : Set X) := by
  have h := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
  simpa [I.range_subschemeι, I.support.isClosed.closure_eq] using h

/-- The generic point of `I.subscheme` lies in every open set meeting `I.support`. -/
private lemma genericPoint_mem_of_mem_support {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] {x : X} (hx : x ∈ I.support) {U : X.Opens} (hxU : x ∈ U) :
    I.subschemeι (_root_.genericPoint I.subscheme) ∈ U :=
  ((isGenericPoint_subschemeι_genericPoint I).mem_open_set_iff U.isOpen).2 ⟨x, hx, hxU⟩

/-- A point of an affine open lies in the support iff its prime contains the ideal of `I`. -/
private lemma primeIdealOf_mem_zeroLocus_iff {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) {w : X} (hw : w ∈ U.1) :
    U.2.primeIdealOf ⟨w, hw⟩ ∈ PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U)) ↔
      w ∈ I.support := by
  rw [← U.2.fromSpec_preimage_zeroLocus]
  change U.2.fromSpec (U.2.primeIdealOf ⟨w, hw⟩) ∈ X.zeroLocus (U := U.1) (I.ideal U) ↔ _
  rw [U.2.fromSpec_primeIdealOf]
  exact (I.mem_support_iff_of_mem hw).symm

private theorem affineIdeal_eq_genericPrime_of_integral
    {X : Scheme.{u}} (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (x : X) (hx : x ∈ I.support) (U : X.affineOpens) (hxU : x ∈ U.1)
    (hcodim : codimension (IrreducibleCloseds.closureSingleton
      (I.subschemeι (_root_.genericPoint I.subscheme))) = 1) :
    I.ideal U = (U.2.primeIdealOf
      ⟨I.subschemeι (_root_.genericPoint I.subscheme),
        genericPoint_mem_of_mem_support I hx hxU⟩).asIdeal ∧
      (I.ideal U).IsPrime ∧ (I.ideal U).height = 1 := by
  let η := _root_.genericPoint I.subscheme
  let y := I.subschemeι η
  have hU : IsAffineOpen U.1 := U.2
  have hyGen : IsGenericPoint y (I.support : Set X) := isGenericPoint_subschemeι_genericPoint I
  have hyU : y ∈ U.1 := genericPoint_mem_of_mem_support I hx hxU
  let q := hU.primeIdealOf ⟨y, hyU⟩
  let V : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ U.1
  have hηV : η ∈ V := hyU
  have _ : Nonempty V := ⟨⟨η, hηV⟩⟩
  have hdomV : IsDomain Γ(I.subscheme, V) := inferInstance
  let e := (I.subschemeObjIso U).commRingCatIsoToRingEquiv
  have hdomQ : IsDomain (Γ(X, U) ⧸ I.ideal U) := e.isDomain_iff.mp (by
    simpa [V] using hdomV)
  let _ : IsDomain (Γ(X, U) ⧸ I.ideal U) := hdomQ
  have hIprime : (I.ideal U).IsPrime := (Ideal.Quotient.isDomain_iff_prime (I.ideal U)).mp hdomQ
  have hgenV : IsGenericPoint ⟨y, hyU⟩ (Subtype.val ⁻¹' (I.support : Set X)) := by
    rw [isGenericPoint_iff_specializes]
    intro z
    rw [subtype_specializes_iff]
    exact hyGen.specializes_iff_mem
  let f : U.1 → PrimeSpectrum Γ(X, U) := fun z => hU.primeIdealOf z
  have hf : Continuous f := by
    change Continuous (fun z : U.1 => hU.isoSpec.hom z)
    exact Scheme.Hom.continuous hU.isoSpec.hom
  have himage : f '' (Subtype.val ⁻¹' (I.support : Set X)) =
      PrimeSpectrum.zeroLocus (I.ideal U) := by
    ext z
    constructor
    · rintro ⟨⟨w, hwU⟩, hwS, rfl⟩
      exact (primeIdealOf_mem_zeroLocus_iff I U hwU).mpr hwS
    · intro hz
      let zS : Spec Γ(X, U) := z
      let w := hU.fromSpec zS
      have hwU : w ∈ U.1 := by
        have hwR : w ∈ Set.range hU.fromSpec := ⟨zS, rfl⟩
        rwa [hU.range_fromSpec] at hwR
      rw [← hU.fromSpec_preimage_zeroLocus] at hz
      refine ⟨⟨w, hwU⟩, (I.mem_support_iff_of_mem hwU).mpr hz, ?_⟩
      change hU.isoSpec.hom ⟨w, hwU⟩ = z
      have hsub : (⟨w, hwU⟩ : U.1.toScheme) = hU.isoSpec.inv zS :=
        Subtype.ext rfl
      rw [hsub]
      change hU.isoSpec.hom (hU.isoSpec.inv zS) = zS
      simp
  have hgenQ : IsGenericPoint q (PrimeSpectrum.zeroLocus (I.ideal U)) := by
    have h := hgenV.image hf
    rwa [himage, (PrimeSpectrum.isClosed_zeroLocus (I.ideal U : Set Γ(X, U))).closure_eq] at h
  let q0 : PrimeSpectrum Γ(X, U) := ⟨I.ideal U, hIprime⟩
  have hgenQ0 : IsGenericPoint q0 (PrimeSpectrum.zeroLocus (I.ideal U)) := by
    have hid : (I.ideal U : Ideal Γ(X, U)) = PrimeSpectrum.vanishingIdeal ({q0} : Set _) := by
      rw [PrimeSpectrum.vanishingIdeal_singleton]
    rw [hid, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact isGenericPoint_closure
  have hq : q = q0 := hgenQ.eq hgenQ0
  have hIdeal : I.ideal U = q.asIdeal := by
    simpa [q0] using congrArg PrimeSpectrum.asIdeal hq.symm
  have hcodim' : Order.coheight (IrreducibleCloseds.closureSingleton y) = 1 := by
    simpa [codimension_eq_coheight, y] using hcodim
  have hycodim : Order.coheight y = 1 := by
    have hEq : (irreducibleSetEquivPoints (α := X)).symm y =
        IrreducibleCloseds.closureSingleton y := IrreducibleCloseds.ext rfl
    rw [← hEq, Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm] at hcodim'
    exact hcodim'
  let uPoint : U.1.toScheme := ⟨y, hyU⟩
  have hheightQ : q.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight (CommRingCat.of (Γ(X, U))) q]
    change Order.coheight (hU.isoSpec.hom uPoint) = 1
    calc
      Order.coheight (hU.isoSpec.hom uPoint) = Order.coheight uPoint :=
        coheight_eq_of_isOpenImmersion hU.isoSpec.hom
      _ = Order.coheight (Scheme.Opens.ι U.1 uPoint) :=
        (coheight_eq_of_isOpenImmersion (Scheme.Opens.ι U.1) (x := uPoint)).symm
      _ = 1 := by simpa [uPoint, y] using hycodim
  exact ⟨hIdeal, hIprime, by simpa [hIdeal] using hheightQ⟩

/-- A codimension-one integral closed subscheme is an effective Cartier
divisor when the ambient local rings along it are UFDs. -/
@[stacks 0AGA, ega "IV 21.7.4" "c) => a'')", ega "IV 21.6.9" "(ii) c) ⇒ b)"]
theorem isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (hcodim : codimension (IrreducibleCloseds.closureSingleton
      (I.subschemeι (_root_.genericPoint I.subscheme))) = 1)
    (hUFD : ∀ x : X, x ∈ I.support →
      UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    IsEffectiveCartierDivisor I := by
  refine isEffectiveCartierDivisor_of_stalk_regular_principal I fun x hx ↦ ?_
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) (by simp)
  let U : X.affineOpens := ⟨W, hW⟩
  have hxU : x ∈ U.1 := hxW
  obtain ⟨-, hprime, hheight⟩ := affineIdeal_eq_genericPrime_of_integral I x hx U hxU hcodim
  have hqx := (primeIdealOf_mem_zeroLocus_iff I U hxU).mpr hx
  exact affine_prime_height_one_gives_stalk_regular I x U hxU (I.ideal U) hprime
    ((PrimeSpectrum.mem_zeroLocus _ _).mp hqx) hheight (hUFD x hx) rfl

end AlgebraicGeometry

end
