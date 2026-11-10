module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# The codimension of a component of an effective Cartier divisor

Let `X` be a locally Noetherian scheme. A generic point `ξ` of an irreducible component of a
locally principal closed subscheme `D ⊆ X` satisfies `dim 𝒪_{X,ξ} ≤ 1`, and if `D` is an
effective Cartier divisor then `dim 𝒪_{X,ξ} = 1`.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_le_one_of_isLocallyPrincipal`: a component of a locally
  principal closed subscheme has codimension at most one.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor`: a component of an
  effective Cartier divisor has codimension exactly one.

## References

* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry

private theorem eq_of_specializes_of_generic_component
    {T : Type*} [TopologicalSpace T] [T0Space T] {x y : T}
    (hx : ∃ Z : irreducibleComponents T, IsGenericPoint x (Z : Set T))
    (h : y ⤳ x) : x = y := by
  obtain ⟨Z, hgen⟩ := hx
  have hsub : (Z : Set T) ⊆ closure ({y} : Set T) := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp h))
      isClosed_closure
  have hclsub : closure ({y} : Set T) ⊆ (Z : Set T) :=
    Z.2.2 isIrreducible_singleton.closure hsub
  exact hgen.eq (Set.Subset.antisymm hclsub hsub)

private theorem minimal_prime_of_generic_component
    {D : Type*} [TopologicalSpace D] [T0Space D] {R : Type*} [CommRing R]
    (K : Ideal R) (ξ : D)
    (hξ : ∃ Z : irreducibleComponents D, IsGenericPoint ξ (Z : Set D))
    (p : PrimeSpectrum R) (hKp : K ≤ p.asIdeal)
    (hlift : ∀ q : PrimeSpectrum R, K ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal →
      ∃ y : D, y ⤳ ξ ∧ (y = ξ → q = p)) :
    K.IsMinimalPrime p.asIdeal := by
  refine ⟨⟨p.isPrime, hKp⟩, fun q hq hqp => ?_⟩
  obtain ⟨y, hy, hqy⟩ := hlift ⟨q, hq.1⟩ hq.2 hqp
  exact le_of_eq (congrArg PrimeSpectrum.asIdeal
    (hqy (eq_of_specializes_of_generic_component hξ hy).symm)).symm

private theorem chart_prime_minimal
    {X : Scheme} (I : X.IdealSheafData) (ξ : I.subscheme)
    (hξ : ∃ Z : irreducibleComponents I.subscheme,
      IsGenericPoint ξ (Z : Set I.subscheme))
    (U : X.affineOpens) (hxU : I.subschemeι ξ ∈ (U : Set X)) :
    (I.ideal U).IsMinimalPrime
      (U.2.primeIdealOf ⟨I.subschemeι ξ, hxU⟩).asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  let x : X := I.subschemeι ξ
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have hpfrom : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hxSupport : x ∈ I.supportSet :=
    (I.range_subschemeι ▸ ⟨ξ, rfl⟩ : x ∈ (I.support : Set X))
  have hJp : I.ideal U ≤ p.asIdeal := by
    intro f hf
    have hnot : x ∉ X.basicOpen f :=
      (Scheme.mem_zeroLocus_iff X (I.ideal U : Set Γ(X, U.1)) x).mp
        (I.supportSet_subset_zeroLocus U hxSupport) f hf
    by_contra hfp
    have hxbasic : x ∈ X.basicOpen f := by
      rw [← hpfrom]
      change p ∈ (hU.fromSpec ⁻¹ᵁ X.basicOpen f)
      rw [hU.fromSpec_preimage_basicOpen f]
      exact (PrimeSpectrum.mem_basicOpen f p).2 hfp
    exact hnot hxbasic
  apply minimal_prime_of_generic_component (I.ideal U) ξ hξ p hJp
  intro qpt hq hqp
  let yX : X := hU.fromSpec qpt
  have hyU : yX ∈ (U : Set X) := by rw [← hU.range_fromSpec]; exact ⟨qpt, rfl⟩
  have hqzero : yX ∈ X.zeroLocus (U := U.1) (I.ideal U) := by
    apply (Scheme.mem_zeroLocus_iff X (I.ideal U : Set Γ(X, U.1)) yX).2
    intro f hf hbasic
    have hqbasic : qpt ∈ PrimeSpectrum.basicOpen f := by
      rw [← hU.fromSpec_preimage_basicOpen f]
      exact hbasic
    exact (PrimeSpectrum.mem_basicOpen f qpt).mp hqbasic (hq hf)
  obtain ⟨y, hy⟩ : yX ∈ Set.range I.subschemeι :=
    I.range_subschemeι ▸ (I.mem_supportSet_iff_of_mem hyU).2 hqzero
  have hqpSpec : qpt ⤳ p := PrimeSpectrum.le_iff_specializes qpt p |>.mp
    ((PrimeSpectrum.asIdeal_le_asIdeal qpt p).mpr hqp)
  have hqpX : yX ⤳ x := by
    simpa [yX, x, hpfrom] using hqpSpec.map hU.fromSpec.continuous
  have hsource : ξ ∈ closure ({y} : Set I.subscheme) := by
    have hclX : I.subschemeι ξ ∈ closure ({I.subschemeι y} : Set X) :=
      by simpa [x, yX, hy] using (specializes_iff_mem_closure.mp hqpX)
    rw [I.subschemeι.isClosedEmbedding.isInducing.closure_eq_preimage_closure_image]
    change I.subschemeι ξ ∈ closure (I.subschemeι '' ({y} : Set I.subscheme))
    simpa [Set.image_singleton] using hclX
  exact ⟨y, specializes_iff_mem_closure.mpr hsource, fun hyξ =>
    hU.fromSpec.isOpenEmbedding.injective
      (hy.symm.trans ((congrArg I.subschemeι hyξ).trans hpfrom.symm))⟩

private theorem quotient_chart_prime_minimal
    {X D : Scheme.{u}} (i : D ⟶ X) (ξ : D)
    (hξ : ∃ Z : irreducibleComponents D, IsGenericPoint ξ (Z : Set D))
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : i ξ ∈ U)
    (K : Ideal Γ(X, U))
    (e : pullback i U.ι ≅ Spec (.of (Γ(X, U) ⧸ K)))
    (he : pullback.snd i U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :
    K.IsMinimalPrime (hU.primeIdealOf ⟨i ξ, hxU⟩).asIdeal := by
  let x : X := i ξ
  let p : PrimeSpectrum Γ(X,U) := hU.primeIdealOf ⟨x,hxU⟩
  let P := pullback i U.ι
  let j : P ⟶ D := pullback.fst i U.ι
  have hEmb : Topology.IsOpenEmbedding j := j.isOpenEmbedding
  have hξRange : ξ ∈ Set.range j := by
    rw [IsOpenImmersion.range_pullbackFst U.ι i]
    change i ξ ∈ U.ι.opensRange
    simpa only [Scheme.Opens.opensRange_ι] using hxU
  obtain ⟨z, hz⟩ := hξRange
  have hsnd : (pullback.snd i U.ι) z = ⟨x, hxU⟩ := by
    apply Subtype.ext
    change U.ι ((pullback.snd i U.ι) z) = x
    exact (congrArg (fun g : P ⟶ X => g z) pullback.condition).symm.trans (congrArg i hz)
  have hpoint : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) (e.hom z) = p := by
    have hh := congrArg (fun g : P ⟶ Spec (.of (Γ(X,U))) => g z) he
    have hh' : hU.isoSpec.hom ((pullback.snd i U.ι) z) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) (e.hom z) := by
      simpa only [Scheme.Hom.comp_apply] using hh
    exact hh'.symm.trans ((congrArg hU.isoSpec.hom hsnd).trans rfl)
  have hcomap : (e.hom z).asIdeal.comap (Ideal.Quotient.mk K) = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hpoint
  have hKp : K ≤ p.asIdeal := by
    intro a ha
    rw [← hcomap, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact (e.hom z).asIdeal.zero_mem
  apply minimal_prime_of_generic_component K ξ hξ p hKp
  intro q hq hqp
  let _ : q.asIdeal.IsPrime := q.isPrime
  let qbar : PrimeSpectrum (Γ(X,U) ⧸ K) :=
    ⟨q.asIdeal.map (Ideal.Quotient.mk K), Ideal.isPrime_map_quotientMk_of_isPrime hq⟩
  have hqbar : qbar.asIdeal ≤ (e.hom z).asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (hcomap ▸ hqp)
  have hqspec : qbar ⤳ e.hom z :=
    (PrimeSpectrum.le_iff_specializes qbar (e.hom z)).mp
      ((PrimeSpectrum.asIdeal_le_asIdeal qbar (e.hom z)).mpr hqbar)
  let E := Scheme.homeoOfIso e
  let y : P := E.symm qbar
  have hyz : y ⤳ z := by
    simpa [y, E, Scheme.homeoOfIso_apply] using hqspec.map E.symm.continuous
  refine ⟨j y, by simpa [hz] using hyz.map j.continuous, ?_⟩
  intro hyξ'
  have hyz' : y = z := hEmb.injective (hyξ'.trans hz.symm)
  have hqeq : qbar = e.hom z := by
    change qbar = E z
    exact (E.apply_symm_apply qbar).symm.trans (congrArg E hyz')
  apply PrimeSpectrum.ext
  have hh := congrArg PrimeSpectrum.asIdeal (show
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) qbar = p by simpa [hqeq] using hpoint)
  change (q.asIdeal.map (Ideal.Quotient.mk K)).comap (Ideal.Quotient.mk K) = p.asIdeal at hh
  simpa [Ideal.comap_map_quotientMk, sup_of_le_right hq] using hh

/-- The Krull dimension of a stalk is the height of the corresponding prime of an affine chart. -/
private theorem ringKrullDim_stalk_eq_height {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.height := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.AtPrime.ringKrullDim_eq_height _ _

/-- A component of a locally principal closed subscheme has codimension at most one. -/
@[stacks 0BCN "part (1)"]
theorem ringKrullDim_stalk_le_one_of_isLocallyPrincipal
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : IsLocallyPrincipal I)
    (ξ : I.subscheme)
    (hξ : ∃ Z : irreducibleComponents I.subscheme, IsGenericPoint ξ (Z : Set I.subscheme)) :
    ringKrullDim (X.presheaf.stalk (I.subschemeι ξ)) ≤ 1 := by
  obtain ⟨U, hxU, hprincipal⟩ := hI (I.subschemeι ξ)
  have hU : IsAffineOpen U.1 := U.2
  have _ : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let p := hU.primeIdealOf ⟨I.subschemeι ξ, hxU⟩
  have _ : (I.ideal U).IsPrincipal := hprincipal
  have hpheight : p.asIdeal.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (I.ideal U) p.asIdeal
      (chart_prime_minimal I ξ hξ U hxU)
  rw [ringKrullDim_stalk_eq_height hU hxU]
  exact_mod_cast hpheight

/-- A component of an effective Cartier divisor has codimension exactly one. -/
@[stacks 0BCN "part (2)"]
theorem ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I)
    (ξ : I.subscheme)
    (hξ : ∃ Z : irreducibleComponents I.subscheme, IsGenericPoint ξ (Z : Set I.subscheme)) :
    ringKrullDim (X.presheaf.stalk (I.subschemeι ξ)) = 1 := by
  have hxSupport : I.subschemeι ξ ∈ I.supportSet :=
    (I.range_subschemeι ▸ ⟨ξ, rfl⟩ : I.subschemeι ξ ∈ (I.support : Set X))
  obtain ⟨U, hU, hxU, f, hf, e, he⟩ :=
    (isEffectiveCartierDivisor_iff_affineLocal I).mp hI (I.subschemeι ξ) hxSupport
  have hmin := quotient_chart_prime_minimal I.subschemeι ξ hξ U hU hxU (Ideal.span {f}) e he
  have _ : IsNoetherianRing Γ(X,U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let p : PrimeSpectrum Γ(X,U) := hU.primeIdealOf ⟨I.subschemeι ξ, hxU⟩
  let _ : (Ideal.span {f} : Ideal Γ(X,U)).IsPrincipal := inferInstance
  have hpheight : p.asIdeal.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) p.asIdeal hmin)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      ((isRegular_iff_mem_nonZeroDivisors (R := Γ(X,U)) (r := f)).mp hf)).trans
      (Ideal.height_mono hmin.le))
  rw [ringKrullDim_stalk_eq_height hU hxU]
  exact_mod_cast hpheight

end AlgebraicGeometry

end
