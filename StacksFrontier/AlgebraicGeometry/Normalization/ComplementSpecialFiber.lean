module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.PullbackNormal
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE

/-!
# Normality away from the completed special fibre

Let a scheme over a discrete valuation ring be a model of a geometrically normal variety.
After base change to the completion of the valuation ring, the complement of the special
fibre is normal.

## Main definitions

* `AlgebraicGeometry.SemistableReduction.complementSpecialFiber` is the open subscheme obtained
  by removing the fibre over the closed point of a local base.

## Main results

* `AlgebraicGeometry.SemistableReduction.isNormal_complementSpecialFiber_baseChange_adicCompletion`
  states that the complement of the special fibre in the completed model is normal.

## Implementation notes

The completion is the adic completion at the maximal ideal. The complement of the special
fibre is represented directly as the inverse image of the punctured spectrum, rather than as
an iterated generic-fibre pullback. Only the identification of the original generic fibre
with the geometrically normal scheme, including its compatibility with the structural maps,
is needed; the other conditions in the definition of a model play no role in this result.

The completed base is again a discrete valuation ring, so its punctured spectrum is the basic
open of a uniformizer and its fraction field is the corresponding localization. That exhibits
the complement of the special fibre as a base change of the generic fibre along the fraction
field of the completion, where Tag 06DG applies.

## References

* [Stacks Project, Section 55.8, Lemma preceding Tag 0C2T]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SemistableReduction

/-- In a discrete valuation ring the fraction field is the localization away from a
uniformizer. -/
private theorem away_fractionRing_of_dvr
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) : IsLocalization.Away π K := by
  have hne : ∀ a : A, a ≠ 0 → algebraMap A K a ≠ 0 := fun a ha =>
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ha
  have hπK := hne π hπ.ne_zero
  refine IsLocalization.Away.mk π (isUnit_iff_ne_zero.mpr hπK) (fun z => ?_) (fun a b hab => ?_)
  · obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective A z
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hb) hπ
    refine ⟨n, a * (↑(u⁻¹) : A), ?_⟩
    rw [← hz, hu, map_mul, map_pow, div_eq_mul_inv]
    have huK := hne (u : A) u.ne_zero
    field_simp [hπK, huK]
    simp only [map_mul, map_units_inv]
    field_simp [huK]
  · obtain rfl := IsFractionRing.injective A K hab
    exact ⟨0, by simp⟩

/-- The punctured spectrum of a local domain with principal maximal ideal is the basic open of
a generator. -/
private theorem puncturedSpectrum_eq_basicOpen_of_uniformizer
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    (π : A) (hgen : IsLocalRing.maximalIdeal A = Ideal.span {π}) :
    Stacks.Divisors.puncturedSpectrum A = PrimeSpectrum.basicOpen π := by
  ext x
  rw [Stacks.Divisors.puncturedSpectrum]
  simp only [SetLike.mem_coe]
  constructor
  · intro hx hmem
    have hmaxle : IsLocalRing.maximalIdeal A ≤ x.asIdeal := by
      rw [hgen]
      exact Ideal.span_le.2 (by simpa using hmem)
    have : x.asIdeal.IsPrime := x.2
    exact hx (PrimeSpectrum.ext
      (le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime x.asIdeal) hmaxle))
  · intro hnot hclosed
    apply hnot
    have heq : x.asIdeal = IsLocalRing.maximalIdeal A := by
      simpa [IsLocalRing.closedPoint] using congrArg PrimeSpectrum.asIdeal hclosed
    rw [heq, hgen]
    exact Ideal.mem_span_singleton_self π

/-- The image of the spectrum of a localization away from an element is that element's basic
open. -/
private theorem opensRange_specMap_away
    (A L : Type u) [CommRing A] [CommRing L] [Algebra A L]
    (π : A) [IsLocalization.Away π L]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A L)))] :
    (Spec.map (CommRingCat.ofHom (algebraMap A L))).opensRange =
      PrimeSpectrum.basicOpen π := by
  ext x
  change x ∈ Set.range (PrimeSpectrum.comap (algebraMap A L)) ↔
    x ∈ PrimeSpectrum.basicOpen π
  rw [PrimeSpectrum.localization_away_comap_range L π]
  rfl

/-- The inverse image of the range of an open immersion is the pullback along it. -/
private noncomputable def complementPullbackIso
    {A : Type u} [CommRing A] [IsLocalRing A] {Y Z : Scheme.{u}}
    (q : Y ⟶ Spec (.of A)) (U : (Spec (.of A)).Opens) (j : Z ⟶ Spec (.of A))
    [IsOpenImmersion j] (hU : U = j.opensRange) :
    (q ⁻¹ᵁ U).toScheme ≅ pullback q j := by
  let W := q ⁻¹ᵁ U
  have hrange : Set.range W.ι = Set.range (pullback.fst q j) := by
    dsimp [W]
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange,
      Scheme.Hom.opensRange_pullbackFst, hU]
  exact IsOpenImmersion.isoOfRangeEq W.ι (pullback.fst q j) hrange

/-- Associativity of iterated pullbacks, in the form needed to compose two base changes. -/
private noncomputable def pullbackCompIso
    {S T U X : Scheme.{u}} (p : X ⟶ S) (i : T ⟶ S) (j : U ⟶ T) :
    pullback (pullback.snd p i) j ≅ pullback p (j ≫ i) := by
  let s := pullbackSymmetry p i
  let m := pullback.map j (pullback.snd p i) j (pullback.fst i p)
    (𝟙 U) s.hom (𝟙 T) (by simp) (by
      rw [Category.comp_id, pullbackSymmetry_hom_comp_fst])
  let e : pullback j (pullback.snd p i) ≅ pullback j (pullback.fst i p) := asIso m
  exact (pullbackSymmetry (pullback.snd p i) j) ≪≫ e ≪≫
    pullbackRightPullbackFstIso i p j ≪≫ pullbackSymmetry (j ≫ i) p


/-- Replace a pullback along a composite by a pullback along an identified fibre. -/
private noncomputable def changeFiberIso
    {S T U X V : Scheme.{u}} (p : X ⟶ S) (i : T ⟶ S) (v : V ⟶ T)
    (e : V ≅ pullback p i) (he : e.hom ≫ pullback.snd p i = v) (j : U ⟶ T) :
    pullback p (j ≫ i) ≅ pullback v j := by
  let e' : V ≅ pullback i p := e ≪≫ pullbackSymmetry p i
  have he' : e'.hom ≫ pullback.fst i p = v := by simp [e', he]
  have hinv : e'.inv ≫ v = pullback.fst i p := by rw [← he', Iso.inv_hom_id_assoc]
  let m := pullback.map j (pullback.fst i p) j v (𝟙 U) e'.inv (𝟙 T)
    (by simp) (by rw [Category.comp_id, hinv])
  let ePB : pullback j (pullback.fst i p) ≅ pullback j v := asIso m
  exact (pullbackSymmetry p (j ≫ i)) ≪≫
    (pullbackRightPullbackFstIso i p j).symm ≪≫ ePB ≪≫
      (pullbackSymmetry v j).symm

/-- The open complement of the special fibre of a scheme over a local ring. -/
public noncomputable def complementSpecialFiber {A : Type u} [CommRing A] [IsLocalRing A]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of A)) : Scheme.{u} :=
  (q ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum A).toScheme

/-- If the generic fibre of an `R`-scheme is identified, over the fraction field `K`, with a
geometrically normal `K`-scheme, then the complement of the special fibre after base change
to the completion of the discrete valuation ring `R` is normal. -/
public theorem isNormal_complementSpecialFiber_baseChange_adicCompletion
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (V X : Scheme.{u}) (v : V ⟶ Spec (.of K))
    (hV : IsGeometricallyNormal v)
    (p : X ⟶ Spec (.of R))
    (e : V ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (he : e.hom ≫ pullback.snd p
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) = v) :
    let Rhat := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let i : Spec (.of Rhat) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R Rhat))
    let Y : Scheme.{u} := pullback p i
    let q : Y ⟶ Spec (.of Rhat) := pullback.snd p i
    IsNormal (complementSpecialFiber q) := by
  dsimp only
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  have hRhat :=
    (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := R)).mp
      ⟨inferInstance, inferInstance⟩
  have : IsDomain A := hRhat.choose
  have : IsDiscreteValuationRing A := hRhat.choose_spec
  let L := FractionRing A
  let : Field L := IsFractionRing.toField A
  let iA : Spec (.of A) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  let iK : Spec (.of K) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hRA : Function.Injective (algebraMap R A) := by
    intro r s hrs
    apply AdicCompletion.of_injective (IsLocalRing.maximalIdeal R) R
    simpa [A, AdicCompletion.algebraMap_apply] using hrs
  let : Algebra R L := Algebra.compHom L (algebraMap R A)
  have hRL : Function.Injective (algebraMap R L) := fun r s hrs =>
    hRA (IsFractionRing.injective A L hrs)
  let klift : K →+* L :=
    IsFractionRing.lift (A := R) (K := K) (L := L) (g := algebraMap R L) hRL
  let : Algebra K L := klift.toAlgebra
  let iL : Spec (.of L) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A L))
  let ell : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have : IsLocalization.Away π L := away_fractionRing_of_dvr A L π hπ
  have : IsOpenImmersion iL := IsOpenImmersion.of_isLocalization π
  have hjrange : iL.opensRange = Stacks.Divisors.puncturedSpectrum A := by
    rw [opensRange_specMap_away A L π,
      puncturedSpectrum_eq_basicOpen_of_uniformizer A π hπ.maximalIdeal_eq]
  have hbase : iL ≫ iA = ell ≫ iK := by
    dsimp only [iL, iA, ell, iK]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    calc
      algebraMap A L (algebraMap R A r) = algebraMap R L r :=
        (Algebra.compHom_algebraMap_apply L (algebraMap R A) r).symm
      _ = klift (algebraMap R K r) := (IsFractionRing.lift_algebraMap hRL r).symm
  have : IsNormal (Spec (.of L)) := isNormal_spec_of_isIntegrallyClosed L
  have : IsNormal (pullback v ell) := isNormal_pullback_of_isGeometricallyNormal v ell hV
  exact isNormal_of_iso
    (complementPullbackIso (pullback.snd p iA) (Stacks.Divisors.puncturedSpectrum A) iL
        hjrange.symm ≪≫
      (changeFiberIso p iA (pullback.snd p iA) (Iso.refl _) (by simp) iL).symm ≪≫
      pullback.congrHom (f₁ := p) (f₂ := p) (g₁ := iL ≫ iA) (g₂ := ell ≫ iK) rfl hbase ≪≫
      changeFiberIso p iK v e he ell)

end AlgebraicGeometry.SemistableReduction

end
