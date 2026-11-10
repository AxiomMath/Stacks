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

/-!
# Formally smooth maps of local rings: lifting through small extensions of Artinian rings

This file continues the proof of the local lifting criterion: lifts through residually trivial
small extensions produce lifts through square-zero quotients of Artinian local rings whose
kernel is annihilated by the maximal ideal, by factoring such a quotient into small extensions.

## References

* [Stacks Project, Tag 0DYG](https://stacks.math.columbia.edu/tag/0DYG)
-/

@[expose] public section

section

section

open InfinitesimalLifting

private theorem ringHom_retract_of_squareZero_ker
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (e : A →+* B) (p : B →+* C) (q : A →+* C)
    (hcomm : p.comp e = q) (_hp : Function.Surjective p)
    (hq : Function.Surjective q) (he : Function.Injective e)
    (hsq : (RingHom.ker p) ^ 2 = ⊥)
    (hsem : letI : Module A (RingHom.ker p) := Module.compHom _ e
      IsSemisimpleModule A (RingHom.ker p)) :
    ∃ r : B →+* A, r.comp e = RingHom.id A ∧ q.comp r = p := by
  let J : Ideal A := RingHom.ker q
  let K : Ideal B := RingHom.ker p
  let : Module A K := Module.compHom K e
  let : IsSemisimpleModule A K := hsem
  let i : J →ₗ[A] K :=
    { toFun := fun x => ⟨e x.1, by
        change p (e x.1) = 0
        have hx : q x.1 = 0 := x.2
        rw [← hcomm] at hx
        exact hx⟩
      map_add' := by
        intro x y
        exact Subtype.ext (map_add e _ _)
      map_smul' := by
        intro a x
        exact Subtype.ext (map_mul e _ _) }
  have hi : Function.Injective i := by
    intro x y hxy
    exact Subtype.ext (he (congrArg Subtype.val hxy))
  obtain ⟨l, hl⟩ := IsSemisimpleModule.extension_property i hi (LinearMap.id)
  have hki (x y : K) : (x : B) * (y : B) = 0 := by
    have hmem : (x : B) * (y : B) ∈ K * K := Ideal.mul_mem_mul x.2 y.2
    simpa only [← pow_two, K, hsq, Submodule.mem_bot] using hmem
  have hdec (b : B) : ∃ a : A, ∃ k : K, b = e a + k := by
    obtain ⟨a, ha⟩ := hq (p b)
    refine ⟨a, ⟨b - e a, ?_⟩, ?_⟩
    · change p (b - e a) = 0
      rw [map_sub, show p (e a) = q a from congrArg (fun f : A →+* C => f a) hcomm]
      exact sub_eq_zero.mpr ha.symm
    · simp
  let M : Ideal B :=
    { carrier := {b | ∃ k : K, (k : B) = b ∧ l k = 0}
      zero_mem' := ⟨0, rfl, map_zero l⟩
      add_mem' := by
        rintro b c ⟨kb, hkb, hlb⟩ ⟨kc, hkc, hlc⟩
        refine ⟨kb + kc, by simp [hkb, hkc], ?_⟩
        simp [hlb, hlc]
      smul_mem' := by
        rintro b c ⟨kc, hkc, hlc⟩
        obtain ⟨a, k, hb⟩ := hdec b
        refine ⟨a • kc, ?_, ?_⟩
        · change e a * (kc : B) = b * c
          rw [hb, ← hkc, add_mul, hki k kc, add_zero]
        · simp [hlc] }
  let eqv : A →+* B ⧸ M := (Ideal.Quotient.mk M).comp e
  have h_inj : Function.Injective eqv := by
    intro a a' haa
    apply sub_eq_zero.mp
    have hmem : e (a - a') ∈ M := by
      have hh : e a - e a' ∈ M := Ideal.Quotient.eq.mp haa
      simpa only [map_sub] using hh
    obtain ⟨k, hk, hlk⟩ := hmem
    have haJ : a - a' ∈ J := by
      change q (a - a') = 0
      rw [← hcomm]
      change p (e (a - a')) = 0
      rw [← hk]
      exact k.2
    have hik : i ⟨a - a', haJ⟩ = k := by
      exact Subtype.ext hk.symm
    have hli : l (i ⟨a - a', haJ⟩) = ⟨a - a', haJ⟩ := by
      have := congrArg (fun f : J →ₗ[A] J => f ⟨a - a', haJ⟩) hl
      simpa using this
    have hz : (⟨a - a', haJ⟩ : J) = 0 := by
      rw [hik, hlk] at hli
      exact hli.symm
    exact congrArg Subtype.val hz
  have h_surj : Function.Surjective eqv := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, k, hb⟩ := hdec b
    refine ⟨a + (l k).1, ?_⟩
    apply Ideal.Quotient.eq.mpr
    change e (a + (l k).1) - b ∈ M
    refine ⟨i (l k) - k, ?_, ?_⟩
    · change e (l k).1 - (k : B) = e (a + (l k).1) - b
      rw [hb, map_add]
      ring
    · have := congrArg (fun f : J →ₗ[A] J => f (l k)) hl
      change l (i (l k)) = l k at this
      simp [map_sub, this]
  let E : A ≃+* B ⧸ M := RingEquiv.ofBijective eqv ⟨h_inj, h_surj⟩
  let r : B →+* A := E.symm.toRingHom.comp (Ideal.Quotient.mk M)
  have hre : r.comp e = RingHom.id A := by
    apply RingHom.ext
    intro a
    change E.symm (eqv a) = a
    exact E.symm_apply_apply a
  have hMker : M ≤ RingHom.ker p := by
    intro b hb
    obtain ⟨k, hk, _⟩ := hb
    rw [RingHom.mem_ker, ← hk]
    exact k.2
  have hMp (b : B) (hb : b ∈ M) : p b = 0 := RingHom.mem_ker.mp (hMker hb)
  let p' : B ⧸ M →+* C := Ideal.Quotient.lift M p hMp
  have hp'e (a : A) : p' (E a) = q a := by
    change p' ((Ideal.Quotient.mk M) (e a)) = q a
    dsimp [p']
    exact congrArg (fun h : A →+* C => h a) hcomm
  have hqr : q.comp r = p := by
    apply RingHom.ext
    intro b
    change q (r b) = p b
    rw [← hp'e (r b)]
    change p' (E (E.symm ((Ideal.Quotient.mk M) b))) = p b
    rw [E.apply_symm_apply]
    dsimp [p']
  exact ⟨r, hre, hqr⟩

/-- An element of an ideal lies in the image of a submodule of that ideal iff it lies in it. -/
private theorem mem_map_subtype_iff {A : Type*} [CommRing A] {J : Ideal A} (K : Submodule A J)
    (x : J) : (x : A) ∈ Submodule.map J.subtype K ↔ x ∈ K :=
  ⟨by rintro ⟨y, hy, hxy⟩; exact (Subtype.ext hxy : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩

private theorem simple_ker_factor
    {A : Type*} [CommRing A] (J : Ideal A) (K : Submodule A J)
    (hK : IsCoatom K) :
    IsSimpleModule (A ⧸ Submodule.map J.subtype K)
      (RingHom.ker (Ideal.Quotient.factor (Submodule.map_subtype_le J K))) := by
  classical
  let I : Ideal A := Submodule.map J.subtype K
  have hIJ : I ≤ J := Submodule.map_subtype_le J K
  let p : A ⧸ I →+* A ⧸ J := Ideal.Quotient.factor hIJ
  let q : J →ₛₗ[Ideal.Quotient.mk I] RingHom.ker p :=
    { toFun := fun x => ⟨(Ideal.Quotient.mk I) x.1, by
        change p ((Ideal.Quotient.mk I) x.1) = 0
        rw [← RingHom.comp_apply, Ideal.Quotient.factor_comp_mk]
        exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mpr x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        change (Ideal.Quotient.mk I) (a * (x : A)) =
          (Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) (x : A)
        exact map_mul _ _ _ }
  have hKker : K ≤ LinearMap.ker q := by
    intro x hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change (Ideal.Quotient.mk I) (x : A) = 0
    apply (Ideal.Quotient.eq_zero_iff_mem (I := I)).mpr
    exact (mem_map_subtype_iff K x).mpr hx
  let q' : J ⧸ K →ₛₗ[Ideal.Quotient.mk I] RingHom.ker p := K.liftQ q hKker
  have hqinj : Function.Injective q' := by
    rw [← LinearMap.ker_eq_bot]
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker, Submodule.liftQ_apply] at hx
      have hmem : (x : A) ∈ I :=
        (Ideal.Quotient.eq_zero_iff_mem (I := I)).mp
          (show (Ideal.Quotient.mk I) (x : A) = 0 from congrArg Subtype.val hx)
      exact (Submodule.Quotient.mk_eq_zero K).mpr ((mem_map_subtype_iff K x).mp hmem)
  have hqsurj : Function.Surjective q' := by
    intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y : A ⧸ I)
    have haJ : a ∈ J := by
      apply (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
      have hy0 : p (y : A ⧸ I) = 0 := y.property
      rwa [← ha] at hy0
    refine ⟨Submodule.Quotient.mk ⟨a, haJ⟩, ?_⟩
    exact Subtype.ext ha
  let : RingHomSurjective (Ideal.Quotient.mk I) :=
    RingHomSurjective.mk Ideal.Quotient.mk_surjective
  exact (LinearMap.isSimpleModule_iff_of_bijective q' ⟨hqinj, hqsurj⟩).mp
    (isSimpleModule_iff_isCoatom.mpr hK)

private theorem lift_of_smallExtension_surjective.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ]
    (hsmall : ∀ (A : Type u) [CommRing A] [IsLocalRing A] (J : Ideal A)
      [IsLocalRing (A ⧸ J)], J ^ 2 = ⊥ →
      (∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥) →
      IsSmallExtension (CommRingCat.ofHom (Ideal.Quotient.mk J)) →
      ∀ (f : R →+* A) [IsLocalHom f] (gbar : S →+* A ⧸ J) [IsLocalHom gbar],
        gbar.comp φ = (Ideal.Quotient.mk J).comp f →
        Function.Bijective (IsLocalRing.ResidueField.map gbar) →
        ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
          (Ideal.Quotient.mk J).comp g = gbar)
    {B C : Type u} [CommRing B] [IsLocalRing B]
    [CommRing C] [IsLocalRing C] [IsArtinianRing C]
    (p : B →+* C) (hp : Function.Surjective p)
    [IsSimpleModule B (RingHom.ker p)]
    (hnil : ∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal B ^ n = ⊥)
    (f : R →+* B) [IsLocalHom f]
    (gbar : S →+* C) [IsLocalHom gbar]
    (hcomm : gbar.comp φ = p.comp f)
    (hbij : Function.Bijective (IsLocalRing.ResidueField.map gbar)) :
    ∃ g : S →+* B, IsLocalHom g ∧ g.comp φ = f ∧ p.comp g = gbar := by
  let J : Ideal B := RingHom.ker p
  let e : B ⧸ J ≃+* C := p.quotientKerEquivOfSurjective hp
  let : IsLocalRing (B ⧸ J) := e.symm.isLocalRing
  let : IsArtinianRing (B ⧸ J) := e.symm.isArtinianRing
  have : IsSimpleModule B J := inferInstance
  have hsmallp : IsSmallExtension (CommRingCat.ofHom p) :=
    isSmallExtension_of_surjective_simple_ker p hp
  have hJ : J ^ 2 = ⊥ :=
    (IsSmallExtension.isSquareZeroSurjection (CommRingCat.ofHom p) hsmallp).2.2.2
  have hsmallq : IsSmallExtension (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    have : IsSimpleModule B (RingHom.ker (Ideal.Quotient.mk J)) := by
      rw [Ideal.mk_ker]
      exact inferInstance
    exact isSmallExtension_of_surjective_simple_ker
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let gbar' : S →+* B ⧸ J := e.symm.toRingHom.comp gbar
  let : IsLocalHom e.symm.toRingHom :=
    IsLocalHom.of_surjective e.symm.toRingHom e.symm.surjective
  have : IsLocalHom gbar' := by
    dsimp [gbar']
    infer_instance
  have hcomm' : gbar'.comp φ = (Ideal.Quotient.mk J).comp f := by
    rw [← p.quotientKerEquivOfSurjective_symm_comp hp]
    exact (RingHom.comp_assoc ..).trans (by rw [hcomm]; rfl)
  have hbij' : Function.Bijective (IsLocalRing.ResidueField.map gbar') := by
    rw [show IsLocalRing.ResidueField.map gbar' =
      (IsLocalRing.ResidueField.map e.symm.toRingHom).comp
        (IsLocalRing.ResidueField.map gbar) from
      IsLocalRing.ResidueField.map_comp gbar e.symm.toRingHom]
    exact (residueField_map_bijective_of_surjective e.symm.toRingHom
      e.symm.surjective).comp hbij
  obtain ⟨g, hg, hgφ, hgq⟩ := hsmall B J hJ hnil hsmallq f gbar' hcomm' hbij'
  refine ⟨g, hg, hgφ, ?_⟩
  apply RingHom.ext
  intro s
  have he := congrArg (fun h : S →+* B ⧸ J => e (h s)) hgq
  change e ((Ideal.Quotient.mk J) (g s)) = e (gbar' s) at he
  have hmk : e ((Ideal.Quotient.mk J) (g s)) = p (g s) :=
    p.quotientKerEquivOfSurjective_apply_mk hp (g s)
  rw [hmk] at he
  simpa [gbar', RingHom.comp_apply] using he

private theorem isSemisimpleModule_of_maximalIdeal_smul_eq_zero
    {A M : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M]
    (h : ∀ a ∈ IsLocalRing.maximalIdeal A, ∀ x : M, a • x = 0) :
    IsSemisimpleModule A M := by
  have ht : Module.IsTorsionBySet A M (IsLocalRing.maximalIdeal A) := by
    intro x a
    exact h a a.property x
  let : Module (A ⧸ IsLocalRing.maximalIdeal A) M := ht.module
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  exact ht.isSemisimpleModule_iff.mp inferInstance

private theorem lift_to_coatom_quotient.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ]
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
    (J : Ideal A) [IsLocalRing (A ⧸ J)] [IsArtinianRing (A ⧸ J)]
    (hJ : J ^ 2 = ⊥)
    (hnil : ∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥)
    (f : R →+* A) [IsLocalHom f]
    (gbar : S →+* A ⧸ J) [IsLocalHom gbar]
    (hcomm : gbar.comp φ = (Ideal.Quotient.mk J).comp f)
    (hbij : Function.Bijective (IsLocalRing.ResidueField.map gbar))
    (K : Submodule A J) (hK : IsCoatom K) :
    ∃ g : S →+* A ⧸ Submodule.map J.subtype K,
      g.comp φ = (Ideal.Quotient.mk (Submodule.map J.subtype K)).comp f ∧
        (Ideal.Quotient.factor (Submodule.map_subtype_le J K)).comp g = gbar := by
  classical
  let I : Ideal A := Submodule.map J.subtype K
  have hIJ : I ≤ J := Submodule.map_subtype_le J K
  let p : A ⧸ I →+* A ⧸ J := Ideal.Quotient.factor hIJ
  have hJne : J ≠ ⊤ := by
    intro htop
    have hh : (⊤ : Ideal A) = ⊥ := by simp [htop, Ideal.top_pow] at hJ
    have h1 : (1 : A) = 0 := by
      have : (1 : A) ∈ (⊥ : Ideal A) := hh ▸ (show (1 : A) ∈ (⊤ : Ideal A) from trivial)
      simp at this
    exact one_ne_zero h1
  have hIne : I ≠ ⊤ := fun h => hJne (top_le_iff.mp (h ▸ hIJ))
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsSimpleModule (A ⧸ I) (RingHom.ker p) :=
    simple_ker_factor J K hK
  have hnilI := quotient_maximalIdeal_nilpotent I hnil
  let fI : R →+* A ⧸ I := (Ideal.Quotient.mk I).comp f
  have : IsLocalHom fI := by dsimp [fI]; infer_instance
  have hcommI : gbar.comp φ = p.comp fI := by
    calc
      gbar.comp φ = (Ideal.Quotient.mk J).comp f := hcomm
      _ = p.comp fI := by
        rw [← Ideal.Quotient.factor_comp_mk hIJ]
        rfl
  obtain ⟨g, _, hgφ, hgp⟩ := lift_of_smallExtension_surjective
    φ hsmall p (Ideal.Quotient.factor_surjective hIJ) hnilI fI gbar hcommI hbij
  exact ⟨g, hgφ, hgp⟩

theorem lift_of_smallExtensions_artinian_squareZero_annihilated.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ]
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
    (J : Ideal A) [IsLocalRing (A ⧸ J)] [IsArtinianRing (A ⧸ J)]
    (hJ : J ^ 2 = ⊥)
    (hann : IsLocalRing.maximalIdeal A * J = ⊥)
    (hnil : ∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥)
    (f : R →+* A) [IsLocalHom f]
    (gbar : S →+* A ⧸ J) [IsLocalHom gbar]
    (hcomm : gbar.comp φ = (Ideal.Quotient.mk J).comp f)
    (hbij : Function.Bijective (IsLocalRing.ResidueField.map gbar)) :
    ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
      (Ideal.Quotient.mk J).comp g = gbar := by
  classical
  let ι := {K : Submodule A J // IsCoatom K}
  let I (i : ι) : Ideal A := Submodule.map J.subtype i.1
  have hIJ (i : ι) : I i ≤ J := Submodule.map_subtype_le J i.1
  let pᵢ (i : ι) : A ⧸ I i →+* A ⧸ J := Ideal.Quotient.factor (hIJ i)
  have hLift (i : ι) : ∃ g : S →+* A ⧸ I i,
      g.comp φ = (Ideal.Quotient.mk (I i)).comp f ∧ (pᵢ i).comp g = gbar :=
    lift_to_coatom_quotient φ hsmall J hJ hnil f gbar hcomm hbij i.1 i.2
  let gᵢ (i : ι) : S →+* A ⧸ I i := Classical.choose (hLift i)
  have hgφ (i : ι) : (gᵢ i).comp φ = (Ideal.Quotient.mk (I i)).comp f :=
    (Classical.choose_spec (hLift i)).1
  have hgp (i : ι) : (pᵢ i).comp (gᵢ i) = gbar :=
    (Classical.choose_spec (hLift i)).2
  let q : A →+* A ⧸ J := Ideal.Quotient.mk J
  let qPi : A →+* (i : ι) → A ⧸ I i :=
    RingHom.pi (fun i => Ideal.Quotient.mk (I i))
  let gPi : S →+* (i : ι) → A ⧸ I i := RingHom.pi gᵢ
  let diag : A ⧸ J →+* (i : ι) → A ⧸ J :=
    RingHom.pi (fun _ => RingHom.id (A ⧸ J))
  let pPi : ((i : ι) → A ⧸ I i) →+* (i : ι) → A ⧸ J :=
    RingHom.pi (fun i => (pᵢ i).comp (Pi.evalRingHom (fun j : ι => A ⧸ I j) i))
  let P : Subring ((A ⧸ J) × ((i : ι) → A ⧸ I i)) := diag.pullback pPi
  let e : A →+* P := (q.prod qPi).codRestrict P (by
    intro a
    change diag (q a) = pPi (qPi a)
    funext i
    change q a = (pᵢ i) ((Ideal.Quotient.mk (I i)) a)
    exact (congrArg (fun h : A →+* A ⧸ J => h a)
      (Ideal.Quotient.factor_comp_mk (hIJ i))).symm)
  let l : S →+* P := (gbar.prod gPi).codRestrict P (by
    intro s
    change diag (gbar s) = pPi (gPi s)
    funext i
    change gbar s = (pᵢ i) ((gᵢ i) s)
    exact (congrArg (fun h : S →+* A ⧸ J => h s) (hgp i)).symm)
  let p : P →+* A ⧸ J := diag.pullbackFst pPi
  have hpe : p.comp e = q := by rfl
  have hpl : p.comp l = gbar := by rfl
  have hlφ : l.comp φ = e.comp f := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun h : R →+* A ⧸ J => h r) hcomm
    · funext i
      exact congrArg (fun h : R →+* A ⧸ I i => h r) (hgφ i)
  have hp : Function.Surjective p := by
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨e a, rfl⟩
  let : IsSemisimpleModule A J :=
    isSemisimpleModule_ideal_of_maximalIdeal_mul_eq_bot J hann
  have he : Function.Injective e := by
    intro a b hab
    have hq : q a = q b := congrArg (fun x : P => x.1.1) hab
    have hi (i : ι) : (Ideal.Quotient.mk (I i)) a =
        (Ideal.Quotient.mk (I i)) b :=
      congrArg (fun x : P => x.1.2 i) hab
    have habJ : a - b ∈ J := (Ideal.Quotient.eq).mp hq
    have hk (i : ι) : (⟨a - b, habJ⟩ : J) ∈ i.1 :=
      (mem_map_subtype_iff i.1 _).mp ((Ideal.Quotient.eq).mp (hi i))
    have hrad : (⟨a - b, habJ⟩ : J) ∈ Module.jacobson A J := by
      rw [Module.jacobson, Submodule.mem_sInf]
      intro K hK
      exact hk ⟨K, hK⟩
    rw [IsSemisimpleModule.jacobson_eq_bot A J] at hrad
    exact sub_eq_zero.mp (congrArg Subtype.val (show (⟨a - b, habJ⟩ : J) = 0 by simpa using hrad))
  have hcompat (z : P) (i : ι) : z.1.1 = (pᵢ i) (z.1.2 i) := by
    have hh := congrArg (fun t : (i : ι) → A ⧸ J => t i) z.property
    exact hh
  let K : Ideal P := RingHom.ker p
  have hkerPi (z : K) (i : ι) : (z.1 : P).1.2 i ∈ RingHom.ker (pᵢ i) := by
    rw [RingHom.mem_ker]
    have hz : (z.1 : P).1.1 = 0 := z.property
    rw [← hcompat z.1 i, hz]
  have hkerPi_sq (i : ι) : (RingHom.ker (pᵢ i)) ^ 2 = ⊥ := by
    rw [Ideal.Quotient.factor_ker (hIJ i), ← Ideal.map_pow, hJ]
    simp
  have hsq : K ^ 2 = ⊥ := by
    apply bot_unique
    rw [pow_two, Ideal.mul_le]
    intro x hx y hy
    change x * y = 0
    apply Subtype.ext
    apply Prod.ext
    · have hx0 : (x : P).1.1 = 0 := hx
      change (x : P).1.1 * (y : P).1.1 = 0
      simp [hx0]
    · funext i
      have hm : (x : P).1.2 i * (y : P).1.2 i ∈
          (RingHom.ker (pᵢ i)) ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul (hkerPi ⟨x, hx⟩ i) (hkerPi ⟨y, hy⟩ i)
      simpa [hkerPi_sq i] using hm
  let : Module A K := Module.compHom K e
  have hsem : IsSemisimpleModule A K := by
    apply isSemisimpleModule_of_maximalIdeal_smul_eq_zero
    intro a ha z
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hz : (z.1 : P).1.1 = 0 := z.property
      change (q a) * (z.1 : P).1.1 = 0
      simp [hz]
    · funext i
      have hm := hkerPi z i
      rw [Ideal.Quotient.factor_ker (hIJ i)] at hm
      obtain ⟨j, hj, hrep⟩ :=
        (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (I i))
          Ideal.Quotient.mk_surjective).mp hm
      have hz : a * j = 0 := by
        have hh : a * j ∈ IsLocalRing.maximalIdeal A * J :=
          Ideal.mul_mem_mul ha hj
        simpa [hann] using hh
      change (Ideal.Quotient.mk (I i)) a * (z.1 : P).1.2 i = 0
      rw [← hrep, ← map_mul, hz, map_zero]
  obtain ⟨r, hre, hrp⟩ := ringHom_retract_of_squareZero_ker
    e p q hpe hp Ideal.Quotient.mk_surjective he hsq hsem
  let g : S →+* A := r.comp l
  have hqg : q.comp g = gbar := by
    calc
      q.comp g = (q.comp r).comp l := by rfl
      _ = p.comp l := by rw [hrp]
      _ = gbar := hpl
  have : IsLocalHom g := by
    have : IsLocalHom (q.comp g) := hqg ▸ inferInstance
    exact isLocalHom_of_comp g q
  refine ⟨g, inferInstance, ?_, hqg⟩
  calc
    g.comp φ = r.comp (l.comp φ) := by rfl
    _ = r.comp (e.comp f) := by rw [hlφ]
    _ = (r.comp e).comp f := by rfl
    _ = f := by rw [hre]; rfl

end

end

end
