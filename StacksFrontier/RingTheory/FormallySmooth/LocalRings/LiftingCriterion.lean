module

public import Mathlib
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import Mathlib.Topology.UniformSpace.Completion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.FormallySmooth.RegularLocal
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.Kaehler.SmoothRingMapsInTheNoetherianCase
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import StacksFrontier.RingTheory.FormallySmooth.LocalRings.SquareZeroLifting
public import StacksFrontier.RingTheory.FormallySmooth.LocalRings.ArtinianSmallExtensions

/-!
# Formally smooth maps of local rings: the local lifting criterion

This file proves the local lifting criterion for formal smoothness of a local homomorphism for
the maximal-ideal-adic topologies.

## Main definitions

* `FormallySmoothAdic`: formal smoothness of a local homomorphism for the maximal-ideal-adic
  topologies on source and target.
* `LiftsLocalSquareZero`: lifts exist through residually trivial square-zero quotients whose
  source has nilpotent maximal ideal.
* `LiftsLocalSmallExtension`: the same lifting condition, for small extensions.

## Main results

* `formallySmooth_adic_iff_lifts_local_squareZero`: a local homomorphism is formally smooth for
  the adic topologies if and only if it satisfies `LiftsLocalSquareZero`; if the target is
  Noetherian, `LiftsLocalSmallExtension` suffices.

## Implementation notes

The maximal-ideal-adic topologies are installed as local instances inside the definitions, so
`IsFormallySmooth` receives them by instance resolution. The universe parameters of
`FormallySmoothAdic` list the universe of the test algebras first, since it occurs only in the
body and cannot be inferred at a use site. An induced map on residue fields is an isomorphism
precisely when `IsLocalRing.ResidueField.map` is bijective.

## References

* [Stacks Project, Tag 0DYG](https://stacks.math.columbia.edu/tag/0DYG)
-/

@[expose] public section

section

section

open InfinitesimalLifting

/-- If `I` maps into `J` under an injective ring map and `J ^ n = ⊥`, then `I ^ n = ⊥`. -/
private theorem pow_eq_bot_of_le_comap {P A : Type*} [CommRing P] [CommRing A] (f : P →+* A)
    (hf : Function.Injective f) {I : Ideal P} {J : Ideal A} (hIJ : ∀ x ∈ I, f x ∈ J) {n : ℕ}
    (hJ : J ^ n = ⊥) : I ^ n = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hmap : Ideal.map f I ≤ J := Ideal.map_le_iff_le_comap.mpr hIJ
  have hxJ : f x ∈ J ^ n := by
    refine Ideal.pow_right_mono hmap n ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hx
  exact (hf (by simpa [hJ] using hxJ) : x = 0) ▸ Submodule.zero_mem _

private theorem lift_of_smallExtensions_squareZero_annihilated.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ]
    (hsmall : ∀ (A : Type u) [CommRing A] [IsLocalRing A] (J : Ideal A)
      [IsLocalRing (A ⧸ J)], J ^ 2 = ⊥ →
      (∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥) →
      IsSmallExtension (CommRingCat.ofHom (Ideal.Quotient.mk J)) →
      ∀ (f : R →+* A) [IsLocalHom f] (gbar : S →+* A ⧸ J) [IsLocalHom gbar],
        gbar.comp φ = (Ideal.Quotient.mk J).comp f →
        Function.Bijective (IsLocalRing.ResidueField.map gbar) →
        ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
          (Ideal.Quotient.mk J).comp g = gbar)
    {A : Type u} [CommRing A] [IsLocalRing A]
    (J : Ideal A) [IsLocalRing (A ⧸ J)]
    (hJ : J ^ 2 = ⊥)
    (hann : IsLocalRing.maximalIdeal A * J = ⊥)
    (hnil : ∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥)
    (f : R →+* A) [IsLocalHom f]
    (gbar : S →+* A ⧸ J) [IsLocalHom gbar]
    (hcomm : gbar.comp φ = (Ideal.Quotient.mk J).comp f)
    (_hbij : Function.Bijective (IsLocalRing.ResidueField.map gbar)) :
    ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
      (Ideal.Quotient.mk J).comp g = gbar := by
  classical
  have hJne : J ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  let T : Subring (A ⧸ J) := gbar.range
  let gT : S →+* T := gbar.rangeRestrict
  let : IsLocalRing T := IsLocalRing.of_surjective' gT gbar.rangeRestrict_surjective
  let : IsLocalHom gT := IsLocalHom.of_surjective gT gbar.rangeRestrict_surjective
  let : IsLocalHom T.subtype := by
    refine ⟨?_⟩
    intro x hx
    obtain ⟨s, hs⟩ := gbar.rangeRestrict_surjective x
    have hsunit : IsUnit (gbar s) := by
      rwa [← hs] at hx
    have hsu : IsUnit s := isUnit_of_map_unit gbar s hsunit
    rw [← hs]
    exact hsu.map gT
  let : IsNoetherianRing T :=
    isNoetherianRing_of_surjective S T gT gbar.rangeRestrict_surjective
  have hnilQ := quotient_maximalIdeal_nilpotent J hnil
  obtain ⟨n, hn, hpowQ⟩ := hnilQ
  have hnilT : IsLocalRing.maximalIdeal T ^ n = ⊥ :=
    pow_eq_bot_of_le_comap T.subtype T.subtype_injective
      (fun x hx => map_nonunit T.subtype x hx) hpowQ
  let : IsArtinianRing T :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal T).2 ⟨n, hnilT⟩
  let P : Subring A := T.comap (Ideal.Quotient.mk J)
  let : IsLocalRing P := isLocalRing_comap_quotient_squareZero J T hJ
  let qP : P →+* T :=
    ((Ideal.Quotient.mk J).comp P.subtype).codRestrict T (by
      intro x; exact x.property)
  have hqP : Function.Surjective qP := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (y : A ⧸ J)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show (Ideal.Quotient.mk J) x ∈ T
      rw [hx]; exact y.property
    · apply Subtype.ext; exact hx
  let : IsLocalHom qP := IsLocalHom.of_surjective qP hqP
  let : IsLocalHom P.subtype := by
    have hcomp : (Ideal.Quotient.mk J).comp P.subtype = T.subtype.comp qP := by
      rfl
    have : IsLocalHom ((Ideal.Quotient.mk J).comp P.subtype) := by
      rw [hcomp]
      infer_instance
    exact isLocalHom_of_comp P.subtype (Ideal.Quotient.mk J)
  let K : Ideal P := RingHom.ker qP
  have hKJ : ∀ y ∈ K, (y : A) ∈ J := fun y hy =>
    (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
      (congrArg Subtype.val (RingHom.mem_ker.mp hy))
  have hK : K ^ 2 = ⊥ := pow_eq_bot_of_le_comap P.subtype P.subtype_injective hKJ hJ
  let e : P ⧸ K ≃+* T := qP.quotientKerEquivOfSurjective hqP
  let : IsLocalRing (P ⧸ K) := e.symm.isLocalRing
  let : IsArtinianRing (P ⧸ K) := e.symm.isArtinianRing
  have hnilP : ∃ m : ℕ, 0 < m ∧ IsLocalRing.maximalIdeal P ^ m = ⊥ :=
    hnil.imp fun m ⟨hm, hpowA⟩ => ⟨hm, pow_eq_bot_of_le_comap P.subtype P.subtype_injective
      (fun x hx => map_nonunit P.subtype x hx) hpowA⟩
  have hannP : IsLocalRing.maximalIdeal P * K = ⊥ := by
    apply bot_unique
    rw [Ideal.mul_le]
    intro x hx y hy
    have hxA : (x : A) ∈ IsLocalRing.maximalIdeal A :=
      map_nonunit P.subtype x hx
    have hyA : (y : A) ∈ J := hKJ y hy
    have hxy : (x : A) * (y : A) = 0 := by
      have hh : (x : A) * (y : A) ∈ IsLocalRing.maximalIdeal A * J :=
        Ideal.mul_mem_mul hxA hyA
      simpa [hann] using hh
    exact Subtype.ext hxy
  let fP : R →+* P := f.codRestrict P (by
    intro r
    show (Ideal.Quotient.mk J) (f r) ∈ T
    rw [← RingHom.comp_apply, ← hcomm]
    exact ⟨φ r, rfl⟩)
  have : IsLocalHom fP := by
    have hh : qP.comp fP = gT.comp φ := by
      exact RingHom.ext fun r => Subtype.ext (congrArg (fun h : R →+* A ⧸ J => h r) hcomm).symm
    have : IsLocalHom (qP.comp fP) := by rw [hh]; infer_instance
    exact isLocalHom_of_comp fP qP
  let : IsLocalHom e.symm.toRingHom :=
    IsLocalHom.of_surjective e.symm.toRingHom e.symm.surjective
  let gP : S →+* P ⧸ K := e.symm.toRingHom.comp gT
  have : IsLocalHom gP := by dsimp [gP]; infer_instance
  have hgPsurj : Function.Surjective gP :=
    e.symm.surjective.comp gbar.rangeRestrict_surjective
  have hgbijP : Function.Bijective (IsLocalRing.ResidueField.map gP) :=
    residueField_map_bijective_of_surjective gP hgPsurj
  have hcommP : gP.comp φ = (Ideal.Quotient.mk K).comp fP := by
    rw [← qP.quotientKerEquivOfSurjective_symm_comp hqP]
    exact RingHom.ext fun r => congrArg e.symm <|
      Subtype.ext (congrArg (fun h : R →+* A ⧸ J => h r) hcomm)
  obtain ⟨g, hg, hgφ, hgq⟩ :=
    lift_of_smallExtensions_artinian_squareZero_annihilated
      φ hsmall K hK hannP hnilP fP gP hcommP hgbijP
  refine ⟨P.subtype.comp g, ?_, ?_, ?_⟩
  · infer_instance
  · exact (RingHom.comp_assoc ..).trans (by rw [hgφ]; rfl)
  · apply RingHom.ext
    intro s
    have he : e ((Ideal.Quotient.mk K) (g s)) = e (gP s) :=
      congrArg e (congrArg (fun h : S →+* P ⧸ K => h s) hgq)
    have hq : qP (g s) = gT s := by
      have hmk : e ((Ideal.Quotient.mk K) (g s)) = qP (g s) :=
        qP.quotientKerEquivOfSurjective_apply_mk hqP (g s)
      have hsec : e (gP s) = gT s := by
        show e (e.symm (gT s)) = gT s
        exact e.apply_symm_apply _
      rwa [hmk, hsec] at he
    exact congrArg Subtype.val hq

private theorem lift_mod_maximalIdeal_mul.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ]
    (hsmall : ∀ (A : Type u) [CommRing A] [IsLocalRing A] (J : Ideal A)
      [IsLocalRing (A ⧸ J)], J ^ 2 = ⊥ →
      (∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥) →
      IsSmallExtension (CommRingCat.ofHom (Ideal.Quotient.mk J)) →
      ∀ (f : R →+* A) [IsLocalHom f] (gbar : S →+* A ⧸ J) [IsLocalHom gbar],
        gbar.comp φ = (Ideal.Quotient.mk J).comp f →
        Function.Bijective (IsLocalRing.ResidueField.map gbar) →
        ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
          (Ideal.Quotient.mk J).comp g = gbar)
    {A : Type u} [CommRing A] [IsLocalRing A]
    (J : Ideal A) [IsLocalRing (A ⧸ J)]
    (hJ : J ^ 2 = ⊥)
    (hnil : ∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥)
    (f : R →+* A) [IsLocalHom f]
    (gbar : S →+* A ⧸ J) [IsLocalHom gbar]
    (hcomm : gbar.comp φ = (Ideal.Quotient.mk J).comp f)
    (hbij : Function.Bijective (IsLocalRing.ResidueField.map gbar)) :
    ∃ g : S →+* A ⧸ (IsLocalRing.maximalIdeal A * J),
      IsLocalHom g ∧
        g.comp φ = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A * J)).comp f ∧
        (Ideal.Quotient.factor
            (Ideal.mul_le_right : IsLocalRing.maximalIdeal A * J ≤ J)).comp g = gbar := by
  classical
  let I : Ideal A := IsLocalRing.maximalIdeal A * J
  have hIJ : I ≤ J := Ideal.mul_le_right
  have hJne : J ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hIne : I ≠ ⊤ := fun h => hJne (top_le_iff.mp (h ▸ hIJ))
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let p : A ⧸ I →+* A ⧸ J := Ideal.Quotient.factor hIJ
  let : IsLocalHom p := IsLocalHom.of_surjective p (Ideal.Quotient.factor_surjective hIJ)
  let L : Ideal (A ⧸ I) := Ideal.map (Ideal.Quotient.mk I) J
  let e : (A ⧸ I) ⧸ L ≃+* A ⧸ J := DoubleQuot.quotQuotEquivQuotOfLE hIJ
  let : IsLocalRing ((A ⧸ I) ⧸ L) := e.symm.isLocalRing
  let : IsLocalHom e.symm.toRingHom :=
    IsLocalHom.of_surjective e.symm.toRingHom e.symm.surjective
  have hL : L ^ 2 = ⊥ := by
    show (Ideal.map (Ideal.Quotient.mk I) J) ^ 2 = ⊥
    rw [← Ideal.map_pow, hJ]
    simp
  have hannL : IsLocalRing.maximalIdeal (A ⧸ I) * L = ⊥ := by
    calc
      IsLocalRing.maximalIdeal (A ⧸ I) * L =
          Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal A) *
            Ideal.map (Ideal.Quotient.mk I) J := by
              rw [IsLocalRing.map_maximalIdeal_of_surjective
                (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective]
      _ = Ideal.map (Ideal.Quotient.mk I) I := by
        rw [Ideal.map_mul]
      _ = ⊥ := Ideal.map_quotient_self I
  have hnilI := quotient_maximalIdeal_nilpotent I hnil
  let fI : R →+* A ⧸ I := (Ideal.Quotient.mk I).comp f
  have : IsLocalHom fI := by dsimp [fI]; infer_instance
  let gbarI : S →+* (A ⧸ I) ⧸ L := e.symm.toRingHom.comp gbar
  have : IsLocalHom gbarI := by dsimp [gbarI]; infer_instance
  have hecomp : e.toRingHom.comp (Ideal.Quotient.mk L) = p := by
    apply RingHom.ext
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk a hIJ
  have hcommI : gbarI.comp φ = (Ideal.Quotient.mk L).comp fI := by
    apply RingHom.ext
    intro r
    apply e.injective
    have hh := congrArg (fun h : R →+* A ⧸ J => h r) hcomm
    calc
      e ((gbarI.comp φ) r) = gbar (φ r) := by simp [gbarI]
      _ = (Ideal.Quotient.mk J) (f r) := hh
      _ = e (((Ideal.Quotient.mk L).comp fI) r) := by
        show (Ideal.Quotient.mk J) (f r) =
          e ((Ideal.Quotient.mk L) ((Ideal.Quotient.mk I) (f r)))
        exact (DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk (f r) hIJ).symm
  have hbijI : Function.Bijective (IsLocalRing.ResidueField.map gbarI) := by
    rw [show IsLocalRing.ResidueField.map gbarI =
      (IsLocalRing.ResidueField.map e.symm.toRingHom).comp
        (IsLocalRing.ResidueField.map gbar) from
      IsLocalRing.ResidueField.map_comp gbar e.symm.toRingHom]
    exact (residueField_map_bijective_of_surjective e.symm.toRingHom
      e.symm.surjective).comp hbij
  obtain ⟨g, hg, hgφ, hgq⟩ :=
    lift_of_smallExtensions_squareZero_annihilated
      φ hsmall L hL hannL hnilI fI gbarI hcommI hbijI
  have hgp : p.comp g = gbar := by
    apply RingHom.ext
    intro s
    have hh := congrArg (fun h : S →+* (A ⧸ I) ⧸ L => e (h s)) hgq
    change e ((Ideal.Quotient.mk L) (g s)) = e (gbarI s) at hh
    rw [show e ((Ideal.Quotient.mk L) (g s)) = p (g s) from
      congrArg (fun h : A ⧸ I →+* A ⧸ J => h (g s)) hecomp] at hh
    simpa [gbarI, RingHom.comp_apply] using hh
  exact ⟨g, hg, hgφ, hgp⟩

private theorem lift_of_smallExtensions_pow_maximalIdeal_mul_eq_bot.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ]
    (hsmall : ∀ (A : Type u) [CommRing A] [IsLocalRing A] (J : Ideal A)
      [IsLocalRing (A ⧸ J)], J ^ 2 = ⊥ →
      (∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥) →
      IsSmallExtension (CommRingCat.ofHom (Ideal.Quotient.mk J)) →
      ∀ (f : R →+* A) [IsLocalHom f] (gbar : S →+* A ⧸ J) [IsLocalHom gbar],
        gbar.comp φ = (Ideal.Quotient.mk J).comp f →
        Function.Bijective (IsLocalRing.ResidueField.map gbar) →
        ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
          (Ideal.Quotient.mk J).comp g = gbar)
    {A : Type u} [CommRing A] [IsLocalRing A]
    (hnil : ∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥)
    (f : R →+* A) [IsLocalHom f]
    (J : Ideal A) [IsLocalRing (A ⧸ J)]
    (hJ : J ^ 2 = ⊥)
    (k : ℕ) (hpow : IsLocalRing.maximalIdeal A ^ k * J = ⊥)
    (gbar : S →+* A ⧸ J) [IsLocalHom gbar]
    (hcomm : gbar.comp φ = (Ideal.Quotient.mk J).comp f)
    (hbij : Function.Bijective (IsLocalRing.ResidueField.map gbar)) :
    ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
      (Ideal.Quotient.mk J).comp g = gbar := by
  classical
  have hall : ∀ k : ℕ, ∀ (J : Ideal A) [IsLocalRing (A ⧸ J)],
      J ^ 2 = ⊥ → IsLocalRing.maximalIdeal A ^ k * J = ⊥ →
      ∀ (gbar : S →+* A ⧸ J) [IsLocalHom gbar],
        gbar.comp φ = (Ideal.Quotient.mk J).comp f →
        Function.Bijective (IsLocalRing.ResidueField.map gbar) →
        ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
          (Ideal.Quotient.mk J).comp g = gbar := by
    intro k
    induction k with
    | zero =>
        intro J _ hJ hpow gbar _ hcomm hbij
        have hJ0 : J = ⊥ := by simpa using hpow
        have hann : IsLocalRing.maximalIdeal A * J = ⊥ := by simp [hJ0]
        exact lift_of_smallExtensions_squareZero_annihilated
          φ hsmall J hJ hann hnil f gbar hcomm hbij
    | succ k ih =>
        intro J _ hJ hpow gbar _ hcomm hbij
        let I : Ideal A := IsLocalRing.maximalIdeal A * J
        have hIJ : I ≤ J := Ideal.mul_le_right
        have hJne : J ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
        have hIne : I ≠ ⊤ := fun h => hJne (top_le_iff.mp (h ▸ hIJ))
        let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
        let : IsLocalRing (A ⧸ I) :=
          IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        let p : A ⧸ I →+* A ⧸ J := Ideal.Quotient.factor hIJ
        let : IsLocalHom p :=
          IsLocalHom.of_surjective p (Ideal.Quotient.factor_surjective hIJ)
        have hI : I ^ 2 = ⊥ := by
          exact bot_unique ((Ideal.pow_right_mono hIJ 2).trans_eq hJ)
        obtain ⟨gI, hgI, hgIφ, hpgI⟩ :=
          lift_mod_maximalIdeal_mul φ hsmall J hJ hnil f gbar hcomm hbij
        have hbijgI : Function.Bijective (IsLocalRing.ResidueField.map gI) := by
          have hmap : (IsLocalRing.ResidueField.map p).comp
              (IsLocalRing.ResidueField.map gI) =
              IsLocalRing.ResidueField.map gbar := by
            calc
              (IsLocalRing.ResidueField.map p).comp
                  (IsLocalRing.ResidueField.map gI) =
                  IsLocalRing.ResidueField.map (p.comp gI) :=
                (IsLocalRing.ResidueField.map_comp gI p).symm
              _ = IsLocalRing.ResidueField.map gbar := by
                apply RingHom.ext
                intro x
                obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective x
                rw [IsLocalRing.ResidueField.map_residue,
                  IsLocalRing.ResidueField.map_residue]
                exact congrArg (IsLocalRing.residue (A ⧸ J))
                  (congrArg (fun h : S →+* A ⧸ J => h s) hpgI)
          have hbcomp : Function.Bijective
              ((IsLocalRing.ResidueField.map p).comp
                (IsLocalRing.ResidueField.map gI)) := by
            rw [hmap]
            exact hbij
          have hbp : Function.Bijective (IsLocalRing.ResidueField.map p) :=
            residueField_map_bijective_of_surjective p
              (Ideal.Quotient.factor_surjective hIJ)
          exact Function.Bijective.of_comp_left hbcomp hbp.1
        have hpowI : IsLocalRing.maximalIdeal A ^ k * I = ⊥ := by
          simpa only [I, pow_succ, mul_assoc] using hpow
        obtain ⟨g, hg, hgφ, hgI⟩ := ih I hI hpowI gI hgIφ hbijgI
        refine ⟨g, hg, hgφ, ?_⟩
        apply RingHom.ext
        intro s
        have hh := congrArg (fun h : S →+* A ⧸ I => p (h s)) hgI
        have hcomp : p ((Ideal.Quotient.mk I) (g s)) =
            (Ideal.Quotient.mk J) (g s) :=
          congrArg (fun h : A →+* A ⧸ J => h (g s))
            (Ideal.Quotient.factor_comp_mk hIJ)
        change p ((Ideal.Quotient.mk I) (g s)) = p (gI s) at hh
        rw [hcomp] at hh
        exact hh.trans (congrArg (fun h : S →+* A ⧸ J => h s) hpgI)
  exact hall k J hJ hpow gbar hcomm hbij

universe u v w

/-- Formal smoothness of a local homomorphism for the maximal-ideal-adic topologies on source
and target, tested against algebras in universe `u₁`. -/
public def FormallySmoothAdic.{u₁, v₁, w₁}
    {R : Type v₁} {S : Type w₁} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) : Prop :=
  letI : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
  letI : IsTopologicalRing R := (IsLocalRing.maximalIdeal R).ringFilterBasis.isTopologicalRing
  letI : IsLinearTopology R R := (IsLocalRing.maximalIdeal R).isLinearTopology
  letI : TopologicalSpace S := (IsLocalRing.maximalIdeal S).adicTopology
  letI : IsTopologicalRing S := (IsLocalRing.maximalIdeal S).ringFilterBasis.isTopologicalRing
  letI : IsLinearTopology S S := (IsLocalRing.maximalIdeal S).isLinearTopology
  IsFormallySmooth.{u₁} φ

/-- The lifting criterion through residually trivial square-zero quotients. -/
public def LiftsLocalSquareZero.{u₁, v₁, w₁}
    {R : Type v₁} {S : Type w₁} [CommRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) : Prop :=
  ∀ (A : Type u₁) [CommRing A] [IsLocalRing A] (J : Ideal A)
    [IsLocalRing (A ⧸ J)], J ^ 2 = ⊥ →
    (∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥) →
    ∀ (f : R →+* A) [IsLocalHom f] (gbar : S →+* A ⧸ J) [IsLocalHom gbar],
      gbar.comp φ = (Ideal.Quotient.mk J).comp f →
      Function.Bijective (IsLocalRing.ResidueField.map gbar) →
      ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
        (Ideal.Quotient.mk J).comp g = gbar

/-- The lifting criterion through residually trivial small extensions. -/
public def LiftsLocalSmallExtension.{u₁, v₁, w₁}
    {R : Type v₁} {S : Type w₁} [CommRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) : Prop :=
  ∀ (A : Type u₁) [CommRing A] [IsLocalRing A] (J : Ideal A)
    [IsLocalRing (A ⧸ J)], J ^ 2 = ⊥ →
    (∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥) →
    IsSmallExtension (CommRingCat.ofHom (Ideal.Quotient.mk J)) →
    ∀ (f : R →+* A) [IsLocalHom f] (gbar : S →+* A ⧸ J) [IsLocalHom gbar],
      gbar.comp φ = (Ideal.Quotient.mk J).comp f →
      Function.Bijective (IsLocalRing.ResidueField.map gbar) →
      ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
        (Ideal.Quotient.mk J).comp g = gbar

/-- A local homomorphism of local rings is formally smooth for the adic
topologies if and only if it lifts through all residually trivial square-zero quotients whose
source has nilpotent maximal ideal. If the target is Noetherian, testing residually trivial
small extensions suffices. -/
@[stacks 0DYG, ega "0 22.1.4", sga "1 III 2.2" "(iv ter)", sga "1 III 2.1" "(i) ⇔ (iv bis)"]
public theorem formallySmooth_adic_iff_lifts_local_squareZero
    {R : Type v} {S : Type w} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] :
    (FormallySmoothAdic.{u, v, w} φ ↔ LiftsLocalSquareZero.{u, v, w} φ) ∧
      (IsNoetherianRing S →
        (FormallySmoothAdic.{u, v, w} φ ↔ LiftsLocalSmallExtension.{u, v, w} φ)) := by
  constructor
  · constructor
    · exact formallySmooth_lifts_local_squareZero φ
    · exact lifts_localSquareZero_formallySmooth φ
  · intro hNoeth
    let : IsNoetherianRing S := hNoeth
    constructor
    · intro hfs A _ _ J _ hJ hnil _ f _ gbar _ hcomm hbij
      exact formallySmooth_lifts_local_squareZero φ hfs A J hJ hnil f gbar hcomm hbij
    · intro hsmall
      apply lifts_localSquareZero_formallySmooth φ
      intro A _ _ J _ hJ hnil f _ gbar _ hcomm hbij
      have : Nontrivial A := inferInstance
      obtain ⟨n, hn, hpow⟩ := hnil
      have hpowJ : IsLocalRing.maximalIdeal A ^ n * J = ⊥ := by
        rw [hpow]
        simp
      exact lift_of_smallExtensions_pow_maximalIdeal_mul_eq_bot
        φ hsmall ⟨n, hn, hpow⟩ f J hJ n hpowJ gbar hcomm hbij

end

end

end
