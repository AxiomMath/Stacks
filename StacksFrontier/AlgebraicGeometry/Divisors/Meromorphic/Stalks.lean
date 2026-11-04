module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient
public import StacksFrontier.Topology.Sheaves.Presheaf.LocalizationStalk
public import StacksFrontier.Topology.Sheaves.Presheaf.Localization

/-!
# Meromorphic functions on a locally Noetherian scheme

On a locally Noetherian scheme the presheaf of meromorphic functions is easy to describe: on
an affine open it is the total quotient ring of the ring of regular functions, and at a point
it is the total quotient ring of the local ring. The reason is that a nonzerodivisor in a local
ring of a locally Noetherian scheme extends to a section which is a nonzerodivisor at every
nearby point. Only the stalk statements use that; the affine statement holds on an arbitrary
scheme, since the denominator submonoid of the total quotient presheaf on an affine open is
already the whole of `nonZeroDivisors Γ(X, U)`.

## Main results

* `AlgebraicGeometry.isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen`: on an affine
  open, the meromorphic functions are the localization at all nonzerodivisors.
* `AlgebraicGeometry.regularSectionGerms_eq_nonZeroDivisors_of_isLocallyNoetherian`: the germs
  of regular local sections are exactly the nonzerodivisors in the local ring.
* `AlgebraicGeometry.stalk_totalQuotientPresheaf_isFractionRing_of_isLocallyNoetherian`: the
  stalk of the presheaf of meromorphic functions is the total quotient ring of the local ring.

## Implementation notes

The presheaf of meromorphic functions is Mathlib's `TopCat.Presheaf.totalQuotientPresheaf`, the
objectwise localization at `TopCat.Presheaf.submonoidPresheafOfStalk` applied to the
nonzerodivisors of the stalks. Rather than choosing an isomorphism with a particular
localization type, the affine statement records the universal localization property, with the
algebra structure induced by the canonical map from the structure sheaf. The supremum appearing
in the stalk statement is the usual explicit description of the stalk of that submonoid
presheaf: the images of regular sections on all neighbourhoods of the given point.

## References

* [Stacks Project, Tag 02OV](https://stacks.math.columbia.edu/tag/02OV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On an affine open of a scheme, meromorphic functions form the total quotient ring of the
ring of regular functions. No Noetherian hypothesis is needed: the denominator submonoid of
the total quotient presheaf on an affine open is already all of `nonZeroDivisors Γ(X, U)`. -/
@[stacks 02OV "affine_total_quotient"]
theorem isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen
    (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U)
        ((X.presheaf.totalQuotientPresheaf).obj (Opposite.op U)) :=
      (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
    IsLocalization (nonZeroDivisors Γ(X, U))
      ((X.presheaf.totalQuotientPresheaf).obj (Opposite.op U)) := by
  let S := X.presheaf.submonoidPresheafOfStalk
    (fun x ↦ nonZeroDivisors (X.presheaf.stalk x))
  have hS := submonoidPresheafOfStalk_obj_eq_nonZeroDivisors X U hU
  let Astd : Algebra Γ(X, U)
      (S.localizationPresheaf.obj (Opposite.op U)) := inferInstance
  have hAlg : (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
      = Astd := by
    apply Algebra.algebra_ext; intro r; rfl
  let : Algebra Γ(X, U)
      (S.localizationPresheaf.obj (Opposite.op U)) :=
    (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
  change @IsLocalization (Γ(X, U)) _ (nonZeroDivisors Γ(X, U))
    (S.localizationPresheaf.obj (Opposite.op U)) _
    ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra)
  rw [← hS]
  exact hAlg.symm ▸ (inferInstance : @IsLocalization (Γ(X, U)) _
    (S.obj (Opposite.op U)) (S.localizationPresheaf.obj (Opposite.op U)) _ Astd)

section RegularStalk

private lemma exists_annihilator_killed
    {R S : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S]
    (P : Ideal R) [P.IsPrime] [Algebra R S]
    [IsLocalization P.primeCompl S] (a : R)
    (ha : (algebraMap R S a) ∈ nonZeroDivisors S) :
    ∃ s : P.primeCompl, ∀ b : R, b * a = 0 → (s : R) * b = 0 := by
  let I : Ideal R := (⊥ : Ideal R).colon {a}
  obtain ⟨T, hTfin, hTspan⟩ :=
    (Submodule.fg_def.mp (show (I : Submodule R R).FG from
      Ideal.fg_of_isNoetherianRing I))
  have hTzero : ∀ b ∈ T, algebraMap R S b = 0 := by
    intro b hb
    have hba : b * a = 0 := by
      simpa [I, Submodule.mem_colon_singleton] using
        (hTspan ▸ Ideal.subset_span hb : b ∈ I)
    exact (mem_nonZeroDivisors_iff.mp ha).2 _ (by simp [← map_mul, hba])
  choose m hm using fun b : T =>
    (IsLocalization.map_eq_zero_iff P.primeCompl S b.1).mp (hTzero b.1 b.2)
  let := hTfin.fintype
  let s : P.primeCompl := ∏ b : T, m b
  refine ⟨s, ?_⟩
  intro b hba
  have hle : I ≤ LinearMap.ker (LinearMap.lsmul R R (s : R)) := by
    rw [← hTspan]
    apply Submodule.span_le.mpr
    intro t ht
    obtain ⟨u, hu⟩ : m ⟨t, ht⟩ ∣ s :=
      Finset.dvd_prod_of_mem (fun b : T => m b) (Finset.mem_univ (⟨t, ht⟩ : T))
    change (s : R) * t = 0
    rw [hu]
    change ((m ⟨t, ht⟩ : P.primeCompl) : R) * (u : R) * t = 0
    calc
      _ = (u : R) * ((m ⟨t, ht⟩ : P.primeCompl) * t) := by ring
      _ = 0 := by rw [hm ⟨t, ht⟩, mul_zero]
  exact hle (by simpa [I, Submodule.mem_colon_singleton] using hba)

private lemma regular_of_annihilator_killed
    {R T : Type*} [CommRing R] [CommRing T] (M : Submonoid R)
    [Algebra R T] [IsLocalization M T] (a s : R) (hs : s ∈ M)
    (h : ∀ b : R, b * a = 0 → s * b = 0) :
    (algebraMap R T a) ∈ nonZeroDivisors T := by
  have hleft : ∀ z : T, algebraMap R T a * z = 0 → z = 0 := by
    intro z hz
    obtain ⟨⟨b, d⟩, hzd⟩ := IsLocalization.surj M z
    have hab : algebraMap R T (b * a) = 0 := by
      calc
        _ = (z * algebraMap R T (d : R)) * algebraMap R T a := by rw [hzd, map_mul]
        _ = (z * algebraMap R T a) * algebraMap R T (d : R) := by ring
        _ = 0 := by rw [mul_comm z, hz, zero_mul]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M T (b * a)).mp hab
    have hsmb : s * ((m : R) * b) = 0 := h _ (by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm)
    have hb : algebraMap R T b = 0 := by
      have heq : (algebraMap R T s * algebraMap R T (m : R)) *
          algebraMap R T b = 0 := by
        simpa only [map_mul, map_zero, mul_assoc] using
          congrArg (algebraMap R T) hsmb
      have hu : IsUnit (algebraMap R T s * algebraMap R T (m : R)) :=
        (IsLocalization.map_units T ⟨s, hs⟩).mul (IsLocalization.map_units T m)
      exact hu.mul_left_cancel (by simpa using heq)
    exact (IsLocalization.map_units T d).mul_right_cancel (by simp [hzd, hb])
  exact mem_nonZeroDivisors_iff.mpr ⟨hleft, fun z hz =>
    hleft z (by simpa [mul_comm] using hz)⟩

private lemma exists_regular_neighborhood (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X)
    (z : X.presheaf.stalk x) (hz : z ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    ∃ (V : Opens X) (hxV : x ∈ V) (t : Γ(X, V)),
      X.presheaf.germ V x hxV t = z ∧
      ∀ (y : X) (hy : y ∈ V),
        X.presheaf.germ V y hy t ∈ nonZeroDivisors (X.presheaf.stalk y) := by
  obtain ⟨U, hxU, hU, s, hs⟩ :=
    X.presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens x z
  change IsAffineOpen U at hU
  let : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : P.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsLocalization P.primeCompl (X.presheaf.stalk x) :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨f, hf⟩ := exists_annihilator_killed P s (by
    rw [X.presheaf.stalk_open_algebraMap ⟨x, hxU⟩]
    simpa only [hs] using hz)
  let V := X.basicOpen (f : Γ(X, U))
  have hxV : x ∈ V := by
    apply (X.mem_basicOpen' (f : Γ(X, U)) ⟨x, hxU⟩).2
    change IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (f : Γ(X, U)))
    exact IsLocalization.map_units _ f
  let : IsLocalization (Submonoid.powers (f : Γ(X, U))) Γ(X, V) :=
    hU.isLocalization_basicOpen (f : Γ(X, U))
  have hmem : (f : Γ(X, U)) ∈ Submonoid.powers (f : Γ(X, U)) := ⟨1, pow_one _⟩
  have htreg : algebraMap Γ(X, U) Γ(X, V) s ∈ nonZeroDivisors Γ(X, V) :=
    regular_of_annihilator_killed _ s (f : Γ(X, U)) hmem hf
  let t : Γ(X, V) := X.presheaf.map (homOfLE (X.basicOpen_le (f : Γ(X, U)))).op s
  refine ⟨V, hxV, t, ?_, ?_⟩
  · simpa only [t, X.presheaf.germ_res_apply] using hs
  · intro y hy
    have hV : IsAffineOpen V := hU.basicOpen (f : Γ(X, U))
    let : Algebra Γ(X, V) (X.presheaf.stalk y) :=
      X.presheaf.algebra_section_stalk ⟨y, hy⟩
    let : IsLocalization
        (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (X.presheaf.stalk y) :=
      hV.isLocalization_stalk ⟨y, hy⟩
    change algebraMap Γ(X, V) (X.presheaf.stalk y) t ∈ _
    exact (IsLocalization.nonZeroDivisors_le_comap
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (X.presheaf.stalk y))
        (by simpa only [t, RingHom.algebraMap_toAlgebra] using htreg)

end RegularStalk

/-- At a point of a locally Noetherian scheme, the germs of regular local
sections are exactly the non-zero-divisors in the local ring. -/
@[stacks 02OV "regular_stalk"]
theorem regularSectionGerms_eq_nonZeroDivisors_of_isLocallyNoetherian
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    (⨆ (U : Opens X) (hx : x ∈ U),
      ((X.presheaf.submonoidPresheafOfStalk
        (fun y ↦ nonZeroDivisors (X.presheaf.stalk y))).obj (Opposite.op U)).map
          (X.presheaf.germ U x hx).hom) =
      nonZeroDivisors (X.presheaf.stalk x) := by
  apply le_antisymm
  · refine iSup_le fun U => iSup_le fun hx => ?_
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hz
    change s ∈ ⨅ y : U, Submonoid.comap
      (X.presheaf.germ U y.1 y.2).hom (nonZeroDivisors (X.presheaf.stalk y)) at hs
    exact (Submonoid.mem_iInf.mp hs ⟨x, hx⟩)
  · intro z hz
    obtain ⟨U, hx, s, hs, hreg⟩ := exists_regular_neighborhood X x z hz
    rw [← hs]
    apply Submonoid.mem_iSup_of_mem U
    apply Submonoid.mem_iSup_of_mem hx
    apply Submonoid.mem_map_of_mem
    change s ∈ ⨅ y : U, Submonoid.comap
      (X.presheaf.germ U y.1 y.2).hom (nonZeroDivisors (X.presheaf.stalk y))
    exact Submonoid.mem_iInf.mpr (fun y => hreg y y.2)

/-- At every point of a locally Noetherian scheme, the stalk of the presheaf of meromorphic
functions is the total quotient ring of the local ring. -/
@[stacks 02OV "stalk_total_quotient", ega "IV 21.6.7" "partial"]
lemma stalk_totalQuotientPresheaf_isFractionRing_of_isLocallyNoetherian
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        X.presheaf.toTotalQuotientPresheaf).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) := by
  let D : Stacks.Presheaf.PresheafLocalizationData :=
    ⟨X, X.presheaf, X.presheaf.submonoidPresheafOfStalk
      (fun y ↦ nonZeroDivisors (X.presheaf.stalk y))⟩
  have h := Stacks.Presheaf.Localization.localizationPresheaf_stalk_isLocalization D x
  rw [show D.S.stalk x = nonZeroDivisors (X.presheaf.stalk x) from
    regularSectionGerms_eq_nonZeroDivisors_of_isLocallyNoetherian X x] at h
  exact h

end AlgebraicGeometry
