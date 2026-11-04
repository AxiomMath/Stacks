module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.FiniteAlgebras
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite algebras over a strictly henselian local ring

A module-finite algebra over a strictly henselian local ring splits as a finite product of
strictly henselian local rings: the henselian decomposition of such an algebra already has
local factors, and each factor is again strictly henselian because its residue field is
algebraic over the separably closed residue field of the base.

The homomorphisms from such an algebra to an algebraically closed field over a fixed local
homomorphism from the base are in bijection with the index set of the decomposition: each local
factor admits exactly one.

## Main results

* `exists_algEquiv_pi_strictHenselian_of_module_finite`: the decomposition into strictly
  henselian local factors.
* `exists_ringHom_to_algClosed_of_finite_local_algebra` and
  `unique_ringHom_to_algClosed_of_finite_local_algebra`: existence and uniqueness of the
  extension of a local homomorphism into an algebraically closed field along a module-finite
  extension of local rings with separably closed residue field.
* `finiteAlgHomCharsEquiv`: the index set of a product decomposition is in bijection with the
  homomorphisms to an algebraically closed field over a fixed local homomorphism.
* `Stacks.Henselian.henselianLocalRing_of_ringEquiv`: henselianness of a local ring transfers
  along a ring isomorphism.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace Stacks.Henselian

/-- A ring isomorphic to a henselian local ring is henselian local. -/
theorem henselianLocalRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [HenselianLocalRing R] (e : R ≃+* S) : HenselianLocalRing S := by
  let : IsLocalRing S := e.isLocalRing
  refine { is_henselian := ?_ }
  intro p hp a ha hunit
  have evalMap (q : Polynomial S) (x : S) :
      (q.map (e.symm : S →+* R)).eval (e.symm x) = e.symm (q.eval x) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (e.symm : S →+* R) x
  have hmem : (p.map (e.symm : S →+* R)).eval (e.symm a) ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff, evalMap, isUnit_map_iff]
    exact (mem_maximalIdeal _).mp ha
  have hunit' : IsUnit ((p.map (e.symm : S →+* R)).derivative.eval (e.symm a)) := by
    rw [Polynomial.derivative_map, evalMap]
    exact hunit.map (e.symm : S →+* R)
  obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian
    (p.map (e.symm : S →+* R)) (hp.map _) (e.symm a) hmem hunit'
  refine ⟨e b, ?_, ?_⟩
  · apply e.symm.injective
    simpa only [Polynomial.IsRoot, ← evalMap, RingEquiv.symm_apply_apply, map_zero] using hb
  · rw [mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff e.symm, map_sub,
      e.symm_apply_apply]
    exact (mem_maximalIdeal _).mp hba

end Stacks.Henselian

/-- A henselian local algebra which is module-finite over a local ring with separably closed
residue field is strictly henselian. -/
theorem strictlyHenselianLocalRing_of_module_finite
    (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S]
    [HenselianLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Finite R S] [IsSepClosed (ResidueField R)] :
    StrictlyHenselianLocalRing S := by
  let : Algebra.IsAlgebraic (ResidueField R) (ResidueField S) :=
    Algebra.IsAlgebraic.of_finite _ _
  let : IsSepClosed (ResidueField S) :=
    Algebra.IsAlgebraic.isSepClosed (F := ResidueField R) (E := ResidueField S)
  exact ⟨⟩

/-- A ring isomorphic to a strictly henselian local ring is strictly henselian local. -/
theorem strictlyHenselianLocalRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [StrictlyHenselianLocalRing R] (e : R ≃+* S) : StrictlyHenselianLocalRing S := by
  let : IsLocalRing S := e.isLocalRing
  let : HenselianLocalRing S := Stacks.Henselian.henselianLocalRing_of_ringEquiv e
  let : IsSepClosed (ResidueField S) :=
    IsSepClosed.of_ringEquiv (ResidueField.mapEquiv e.symm)
  exact ⟨⟩

/-- The structure map of a module-finite algebra between local rings is a local homomorphism. -/
theorem isLocalHom_algebraMap_of_finite_local
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [Module.Finite R S] :
    IsLocalHom (algebraMap R S) := by
  refine ⟨fun a ha => notMem_maximalIdeal.mp fun h =>
    notMem_maximalIdeal.mpr ha (Ideal.mem_comap.mp ?_)⟩
  rwa [eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (maximalIdeal S))]

/-- A module-finite algebra over a strictly henselian local ring is a finite product of
strictly henselian local rings, each finite over the base. -/
@[ega "IV 18.5.10" "special case", sga "4 VIII 4.1" "(i), special case"]
theorem exists_algEquiv_pi_strictHenselian_of_module_finite
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∃ (ι : Type u) (_ : Finite ι) (B : ι → Type u)
      (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
      (_ : ∀ i, StrictlyHenselianLocalRing (B i)),
      (∀ i, Module.Finite R (B i)) ∧ Nonempty (A ≃ₐ[R] ∀ i, B i) := by
  obtain ⟨ι, hι, B, hBcomm, hBalg, hBhen, hBfinite, he⟩ :=
    exists_algEquiv_pi_henselianLocalRing_of_module_finite R A
  let : Finite ι := hι
  let : ∀ i, CommRing (B i) := hBcomm
  let : ∀ i, Algebra R (B i) := hBalg
  let : ∀ i, HenselianLocalRing (B i) := hBhen
  have hBstrict : ∀ i, StrictlyHenselianLocalRing (B i) := by
    intro i
    let : IsLocalRing (B i) := hBhen i |>.toIsLocalRing
    let : Module.Finite R (B i) := hBfinite i
    let : IsLocalHom (algebraMap R (B i)) := isLocalHom_algebraMap_of_finite_local R (B i)
    exact strictlyHenselianLocalRing_of_module_finite R (B i)
  exact ⟨ι, hι, B, hBcomm, hBalg, hBstrict, hBfinite, he⟩

/-- A local homomorphism from a local ring with separably closed residue field into an
algebraically closed field extends along any module-finite local extension. -/
theorem exists_ringHom_to_algClosed_of_finite_local_algebra
    {R S k : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Field k] [IsAlgClosed k] [Algebra R S] [Module.Finite R S]
    [IsLocalHom (algebraMap R S)] [IsSepClosed (ResidueField R)]
    (φ : R →+* k) [IsLocalHom φ] : ∃ ψ : S →+* k, ψ.comp (algebraMap R S) = φ := by
  let : Algebra R k := φ.toAlgebra
  let κ := ResidueField R
  let kS := ResidueField S
  let : Algebra.IsAlgebraic κ kS := Algebra.IsAlgebraic.of_finite κ kS
  let fκ : κ →+* k := ResidueField.lift φ
  let : Algebra κ k := fκ.toAlgebra
  let : IsScalarTower R κ k :=
    IsScalarTower.of_algebraMap_eq' (ResidueField.lift_comp_residue φ).symm
  let ψκ : kS →ₐ[κ] k := IsAlgClosed.lift
  refine ⟨ψκ.toRingHom.comp (residue S), ?_⟩
  ext x
  show ψκ (residue S (algebraMap R S x)) = φ x
  rw [← ResidueField.map_residue (algebraMap R S) x]
  show ψκ (algebraMap κ kS (residue R x)) = φ x
  have hcomp := congrArg (fun h : κ →+* k => h (residue R x)) (AlgHom.comp_algebraMap ψκ)
  exact hcomp.trans (ResidueField.lift_residue_apply φ x)

/-- A homomorphism into a field which restricts to a local homomorphism on a module-finite
local subring is itself local. -/
theorem isLocalHom_of_ringHom_to_field_of_finite_local_algebra
    (R S k : Type u) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Field k] [Algebra R S] [Module.Finite R S]
    (φ : R →+* k) [IsLocalHom φ] (ψ : S →+* k)
    (hψ : ψ.comp (algebraMap R S) = φ) : IsLocalHom ψ := by
  have hkerφ : RingHom.ker φ = maximalIdeal R := by
    ext x
    simp only [RingHom.mem_ker, mem_maximalIdeal, mem_nonunits_iff]
    refine ⟨fun hx hxunit => not_isUnit_zero (hx ▸ hxunit.map φ), fun hx => ?_⟩
    simpa using fun hu => hx ((isUnit_map_iff φ x).mp hu)
  have hcomap : (RingHom.ker ψ).comap (algebraMap R S) = maximalIdeal R := by
    ext x
    show (ψ.comp (algebraMap R S)) x = 0 ↔ x ∈ maximalIdeal R
    rw [hψ, ← RingHom.mem_ker, hkerφ]
  let : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hmax : (RingHom.ker ψ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) (S := S) (RingHom.ker ψ)
      (hcomap ▸ maximalIdeal.isMaximal R)
  refine ⟨fun x hx => notMem_maximalIdeal.mp ?_⟩
  rw [← eq_maximalIdeal hmax, RingHom.mem_ker]
  exact hx.ne_zero

/-- The extension of a local homomorphism into an algebraically closed field along a
module-finite local extension with separably closed base residue field is unique. -/
theorem unique_ringHom_to_algClosed_of_finite_local_algebra
    (R S k : Type u) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Field k] [IsAlgClosed k] [IsSepClosed (ResidueField R)]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    (φ : R →+* k) [IsLocalHom φ] (ψ ψ' : S →+* k)
    (hψ : ψ.comp (algebraMap R S) = φ) (hψ' : ψ'.comp (algebraMap R S) = φ) : ψ = ψ' := by
  let : Algebra R k := φ.toAlgebra
  let κ := ResidueField R
  let kS := ResidueField S
  let fκ : κ →+* k := ResidueField.lift φ
  let : Algebra κ k := fκ.toAlgebra
  let : IsScalarTower R κ k :=
    IsScalarTower.of_algebraMap_eq' (ResidueField.lift_comp_residue φ).symm
  let : IsLocalHom ψ := isLocalHom_of_ringHom_to_field_of_finite_local_algebra R S k φ ψ hψ
  let : IsLocalHom ψ' := isLocalHom_of_ringHom_to_field_of_finite_local_algebra R S k φ ψ' hψ'
  have hlift (χ : S →+* k) [IsLocalHom χ] (hχ : χ.comp (algebraMap R S) = φ) :
      (ResidueField.lift χ).comp (ResidueField.map (algebraMap R S)) = fκ := by
    ext x
    obtain ⟨r, rfl⟩ := residue_surjective x
    show ResidueField.lift χ (ResidueField.map (algebraMap R S) (residue R r)) =
      fκ (residue R r)
    rw [ResidueField.map_residue, ResidueField.lift_residue_apply]
    calc
      χ (algebraMap R S r) = φ r := congrArg (fun h : R →+* k => h r) hχ
      _ = fκ (residue R r) := (ResidueField.lift_residue_apply φ r).symm
  let : Algebra.IsAlgebraic κ kS := Algebra.IsAlgebraic.of_finite κ kS
  let : IsPurelyInseparable κ kS := Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
  let lift (χ : S →+* k) [IsLocalHom χ] (hχ : χ.comp (algebraMap R S) = φ) : kS →ₐ[κ] k :=
    { toRingHom := ResidueField.lift χ
      commutes' := fun r => by
        show ResidueField.lift χ (ResidueField.map (algebraMap R S) r) = fκ r
        exact congrArg (fun h : κ →+* k => h r) (hlift χ hχ) }
  ext x
  have h := congrArg (fun h : kS →ₐ[κ] k => h (residue S x))
    (Subsingleton.elim (lift ψ hψ) (lift ψ' hψ'))
  exact (ResidueField.lift_residue_apply ψ x).symm.trans
    (h.trans (ResidueField.lift_residue_apply ψ' x))

/-- A homomorphism from a finite product of module-finite local algebras into an algebraically
closed field, restricting to a given local homomorphism on the base, factors through exactly
one projection, and the factor through it is unique. -/
theorem existsUnique_factor_ringHom_pi
    {R k ι : Type u} [CommRing R] [IsLocalRing R] [IsSepClosed (ResidueField R)]
    [Field k] [IsAlgClosed k]
    [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)]
    [∀ i, Algebra R (B i)] [∀ i, Module.Finite R (B i)]
    [∀ i, IsLocalHom (algebraMap R (B i))]
    (φ : R →+* k) [IsLocalHom φ] (ψ : (∀ i, B i) →+* k)
    (hψ : ψ.comp (algebraMap R (∀ i, B i)) = φ) :
    ∃! z : Σ i, B i →+* k,
      z.2.comp (algebraMap R (B z.1)) = φ ∧ ψ = z.2.comp (Pi.evalRingHom B z.1) := by
  classical
  let p : PrimeSpectrum (∀ i, B i) := ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩
  obtain ⟨⟨i, q⟩, hp⟩ := (PrimeSpectrum.sigmaToPi_bijective B).surjective p
  have hker : RingHom.ker ψ = (q.asIdeal.comap (Pi.evalRingHom B i)) := by
    have h := congrArg PrimeSpectrum.asIdeal hp
    simpa [p, PrimeSpectrum.sigmaToPi_apply, PrimeSpectrum.comap_asIdeal] using h.symm
  let e : ∀ j, B j := Pi.single i 1
  have he_ne : ψ e ≠ 0 := fun h => by
    have he : e ∈ q.asIdeal.comap (Pi.evalRingHom B i) := hker ▸ RingHom.mem_ker.mpr h
    change Pi.single i (1 : B i) i ∈ q.asIdeal at he
    rw [Pi.single_eq_same] at he
    exact (Ideal.ne_top_iff_one _).mp q.2.ne_top he
  have he_one : ψ e = 1 := by
    have hee : e * e = e := by
      show Pi.single i (1 : B i) * Pi.single i 1 = Pi.single i 1
      rw [← Pi.single_mul, mul_one]
    have hz : ψ e * (ψ e - 1) = 0 := by rw [mul_sub, ← map_mul, hee, mul_one, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left he_ne)
  have hmul (a : ∀ j, B j) : Pi.single i (a i) = e * a := by
    ext j
    by_cases h : j = i
    · subst j
      simp [e]
    · simp [e, h]
  let β : B i →+* k :=
    { toFun := fun b => ψ (Pi.single i b)
      map_one' := he_one
      map_mul' := fun a b => by rw [Pi.single_mul, map_mul]
      map_zero' := by rw [Pi.single_zero, map_zero]
      map_add' := fun a b => by rw [Pi.single_add, map_add] }
  have hβ : β.comp (algebraMap R (B i)) = φ := by
    ext r
    show ψ (Pi.single i (algebraMap R (∀ j, B j) r i)) = φ r
    rw [hmul, map_mul, he_one, one_mul]
    exact congrArg (fun h : R →+* k => h r) hψ
  have hfactor : ψ = β.comp (Pi.evalRingHom B i) := by
    refine RingHom.ext fun a => ?_
    show ψ a = ψ (Pi.single i (a i))
    rw [hmul, map_mul, he_one, one_mul]
  refine ⟨⟨i, β⟩, ⟨hβ, hfactor⟩, ?_⟩
  rintro ⟨j, γ⟩ ⟨hγ, hγfactor⟩
  change γ.comp (algebraMap R (B j)) = φ at hγ
  change ψ = γ.comp (Pi.evalRingHom B j) at hγfactor
  let q' : PrimeSpectrum (B j) := ⟨RingHom.ker γ, RingHom.ker_isPrime γ⟩
  have hp' : PrimeSpectrum.sigmaToPi B ⟨j, q'⟩ = p := by
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.sigmaToPi_apply, PrimeSpectrum.comap_asIdeal]
    show (RingHom.ker γ).comap (Pi.evalRingHom B j) = RingHom.ker ψ
    rw [hγfactor]
    rfl
  obtain rfl : i = j :=
    congrArg Sigma.fst ((PrimeSpectrum.sigmaToPi_injective B) (hp.trans hp'.symm))
  rw [unique_ringHom_to_algClosed_of_finite_local_algebra R (B i) k φ γ β hγ hβ]

/-- For a module-finite algebra presented as a finite product of local algebras over a local
ring with separably closed residue field, the index set is in bijection with the homomorphisms
to a fixed algebraically closed field extending a fixed local homomorphism from the base. -/
def finiteAlgHomCharsEquiv
    {R k ι A : Type u} [CommRing R] [IsLocalRing R] [IsSepClosed (ResidueField R)]
    [Field k] [IsAlgClosed k]
    [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)]
    [∀ i, Algebra R (B i)] [∀ i, Module.Finite R (B i)]
    [∀ i, IsLocalHom (algebraMap R (B i))]
    [CommRing A] [Algebra R A] (e : A ≃ₐ[R] (∀ i, B i))
    (φ : R →+* k) [IsLocalHom φ] :
    ι ≃ {ψ : A →+* k // ψ.comp (algebraMap R A) = φ} := by
  classical
  let ψi : ∀ i, B i →+* k := fun i =>
    Classical.choose (exists_ringHom_to_algClosed_of_finite_local_algebra
      (R := R) (S := B i) (k := k) φ)
  have hψi (i) : (ψi i).comp (algebraMap R (B i)) = φ :=
    Classical.choose_spec (exists_ringHom_to_algClosed_of_finite_local_algebra
      (R := R) (S := B i) (k := k) φ)
  let cpi : ∀ i, {ψ : (∀ j, B j) →+* k // ψ.comp (algebraMap R (∀ j, B j)) = φ} := fun i =>
    ⟨(ψi i).comp (Pi.evalRingHom B i), RingHom.ext fun r => DFunLike.congr_fun (hψi i) r⟩
  have hcpi_inj : Function.Injective cpi := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    obtain ⟨z, hz, hzu⟩ := existsUnique_factor_ringHom_pi
      (R := R) (k := k) (ι := ι) (B := B) φ (ψ := (cpi i).val) (hψ := (cpi i).property)
    have hi : (⟨i, ψi i⟩ : Σ j, B j →+* k) = z := hzu _ ⟨hψi i, rfl⟩
    have hj : (⟨j, ψi j⟩ : Σ j, B j →+* k) = z := hzu _ ⟨hψi j, hij'⟩
    exact congrArg Sigma.fst (hi.trans hj.symm)
  have hcpi_surj : Function.Surjective cpi := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨z, hz, hzu⟩ := existsUnique_factor_ringHom_pi
      (R := R) (k := k) (ι := ι) (B := B) φ (ψ := ψ) (hψ := hψ)
    rcases z with ⟨i, ψ'⟩
    have hψ' : ψ' = ψi i :=
      unique_ringHom_to_algClosed_of_finite_local_algebra R (B i) k φ ψ' (ψi i) hz.1 (hψi i)
    refine ⟨i, Subtype.ext ?_⟩
    change (ψi i).comp (Pi.evalRingHom B i) = ψ
    rw [hz.2, hψ']
  let eChar : {ψ : A →+* k // ψ.comp (algebraMap R A) = φ} ≃
      {ψ : (∀ i, B i) →+* k // ψ.comp (algebraMap R (∀ i, B i)) = φ} :=
    { toFun := fun ψ => ⟨ψ.1.comp e.symm.toRingHom, by
        have hcomm : e.symm.toRingHom.comp (algebraMap R (∀ i, B i)) = algebraMap R A := by
          ext r
          exact e.symm.commutes r
        rw [RingHom.comp_assoc, hcomm, ψ.2]⟩
      invFun := fun ψ => ⟨ψ.1.comp e.toRingHom, by
        have hcomm : e.toRingHom.comp (algebraMap R A) = algebraMap R (∀ i, B i) := by
          ext r i
          exact congrArg (fun z : (∀ j, B j) => z i) (e.commutes r)
        rw [RingHom.comp_assoc, hcomm, ψ.2]⟩
      left_inv := by
        rintro ⟨ψ, hψ⟩
        apply Subtype.ext
        ext x
        simp
      right_inv := by
        rintro ⟨ψ, hψ⟩
        apply Subtype.ext
        ext x
        simp }
  exact (Equiv.ofBijective cpi ⟨hcpi_inj, hcpi_surj⟩).trans eChar.symm

end
