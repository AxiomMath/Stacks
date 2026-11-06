module

public import StacksFrontier.RingTheory.Length.RingEquiv
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.FieldTheory.PurelyInseparable.BaseChange
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksFrontier.RingTheory.Noetherian.TensorProduct
public import StacksFrontier.RingTheory.Smooth.Field
public import StacksFrontier.RingTheory.TensorProduct.LocalAlgebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Multiplicities of components after an extension of the base field

Let `k` be a field and let `Z` be an integral scheme locally of finite type over `k`. For a
field extension `K/k` the base change `Z_K` need be neither irreducible nor reduced, and each
of its irreducible components carries a multiplicity: the length of the local ring of `Z_K` at
the generic point of that component. This file shows that every such multiplicity is one, or a
power of the characteristic of `k`; in particular it is one whenever `k` has characteristic
zero.

## Main results

* `Stacks.Chow.componentMultiplicity_baseChange_eq_one_or_char_pow` — the multiplicity of an
  irreducible component of a base change along a field extension is one, or the characteristic
  of the base field is positive and the multiplicity is a power of it.

## References

* [Stacks Project, Tag 0H4F](https://stacks.math.columbia.edu/tag/0H4F)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace CommRingCat
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-! ### Local algebra -/

/-- A factor of a prime power in `ℕ∞` is a prime power. -/
private lemma exists_eq_prime_pow_of_mul_eq_prime_pow
    {p n : ℕ} (hp : Nat.Prime p) {a b : ℕ∞} (h : a * b = (p : ℕ∞) ^ n) :
    ∃ m, a = (p : ℕ∞) ^ m := by
  have hp0 : (p : ℕ∞) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hfin : a ≠ ⊤ := by
    rintro rfl
    rw [ENat.top_mul (right_ne_zero_of_mul (h ▸ hp0))] at h
    exact ENat.natCast_ne_top (p ^ n) (by exact_mod_cast h.symm)
  have hnat := congrArg ENat.toNat h
  rw [ENat.toNat_mul] at hnat
  norm_cast at hnat
  obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow hp).mp ⟨_, hnat.symm⟩
  refine ⟨m, ?_⟩
  rw [← ENat.natCast_toNat hfin, hm]
  norm_cast

/-- A nontrivial commutative ring with a unique prime ideal is local. -/
private lemma isLocalRing_of_unique_prime
    {R : Type u} [CommRing R] [Nontrivial R]
    (h : ∃! P : Ideal R, P.IsPrime) : IsLocalRing R := by
  obtain ⟨P, hP, huniq⟩ := h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := R)
  exact .of_unique_max_ideal
    ⟨m, hm, fun n hn => (huniq n hn.isPrime).trans (huniq m hm.isPrime).symm⟩

/-- Base changing a local ring along a finite purely inseparable field extension keeps it
local. -/
@[ega "0 22.5.5" "more general"]
private lemma isLocalRing_tensorProduct_of_isPurelyInseparable
    (k A K : Type u) [Field k] [CommRing A] [IsLocalRing A] [Field K]
    [Algebra k A] [Algebra k K] [Module.Finite k K] [IsPurelyInseparable k K] :
    IsLocalRing (A ⊗[k] K) := by
  let : Algebra A (A ⊗[k] K) := Algebra.TensorProduct.leftAlgebra
  have hmap : Function.Injective (algebraMap A (A ⊗[k] K)) :=
    Algebra.TensorProduct.includeLeft_injective (S := A) (algebraMap k K).injective
  have : Nontrivial (A ⊗[k] K) := hmap.nontrivial
  have hInt : Algebra.IsIntegral A (A ⊗[k] K) := Algebra.IsIntegral.tensorProduct k A K
  have hhomeo := PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K A
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := A ⊗[k] K)
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨m, hm, fun n hn => ?_⟩
  have hmc : Ideal.comap (algebraMap A (A ⊗[k] K)) m = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal <|
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (hI := hm) m
  have hnc : Ideal.comap (algebraMap A (A ⊗[k] K)) n = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal <|
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (hI := hn) n
  have hspec : PrimeSpectrum.comap (algebraMap A (A ⊗[k] K)) ⟨m, hm.isPrime⟩ =
      PrimeSpectrum.comap (algebraMap A (A ⊗[k] K)) ⟨n, hn.isPrime⟩ :=
    PrimeSpectrum.ext (hmc.trans hnc.symm)
  exact (congrArg PrimeSpectrum.asIdeal (hhomeo.injective hspec)).symm

/-- Any ring map out of an artinian local ring into a local ring is local. -/
@[ega "IV 11.4.11"]
private lemma isLocalHom_of_artinian
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsArtinianRing R] (f : R →+* S) : IsLocalHom f := by
  apply ((IsLocalRing.local_hom_TFAE f).out 5 1).mp
  exact IsLocalRing.eq_maximalIdeal (inferInstanceAs
    ((IsLocalRing.maximalIdeal S).comap f).IsMaximal)

/-- A flat local algebra whose maximal ideal is generated by that of the base has the same
length over itself as the base does. -/
private lemma length_eq_of_flat_local_map_with_same_maximal_ideal
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B) :
    Module.length A A = Module.length B B := by
  have hlen := length_baseChange_eq_length_mul_length_quotient A B A
  have hquot : Module.length B (B ⧸ extendedMaximalIdeal A B) = 1 := by
    rw [show extendedMaximalIdeal A B = IsLocalRing.maximalIdeal B from hmax]
    exact Module.length_eq_one_iff.mpr <| isSimpleModule_iff_quot_maximal.mpr
      ⟨_, IsLocalRing.maximalIdeal.isMaximal B, ⟨LinearEquiv.refl B _⟩⟩
  have htensor : Module.length B (B ⊗[A] A) = Module.length B B :=
    (Algebra.TensorProduct.rid A B B).toLinearEquiv.length_eq
  rw [hquot, htensor] at hlen
  simpa using hlen

/-- If the length of a flat local extension is a power of `p`, so is the length of the base. -/
private lemma length_is_prime_pow_of_flat_local
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (p : ℕ) (hp : Nat.Prime p)
    (hlenB : ∃ n, Module.length B B = (p : ℕ∞) ^ n) :
    ∃ n, Module.length A A = (p : ℕ∞) ^ n := by
  obtain ⟨n, hn⟩ := hlenB
  have hbase := length_baseChange_eq_length_mul_length_quotient A B A
  rw [(Algebra.TensorProduct.rid A B B).toLinearEquiv.length_eq, hn] at hbase
  exact exists_eq_prime_pow_of_mul_eq_prime_pow hp hbase

/-- A purely inseparable finite extension of a field has length a power of the exponential
characteristic after base change to any extension field. -/
private lemma length_tensorProduct_eq_prime_pow_of_isPurelyInseparable
    (k K k' : Type u) [Field k] [Field K] [Field k']
    [Algebra k K] [Algebra k k'] [Module.Finite k k']
    [IsPurelyInseparable k k'] (p : ℕ) (hp : Nat.Prime p)
    [ExpChar k p] [ExpChar K p] :
    ∃ n, Module.length (K ⊗[k] k') (K ⊗[k] k') = (p : ℕ∞) ^ n := by
  let A := K ⊗[k] k'
  let : IsLocalRing A := isLocalRing_tensorProduct_of_isPurelyInseparable k K k'
  let : Algebra K A := Algebra.TensorProduct.leftAlgebra
  let : Module.Finite K A := Module.Finite.base_change k K k'
  have hsmul (r : K) (x : A) : r • x = algebraMap K A r * x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show r • (a ⊗ₜ[k] b) = algebraMap K A r * (a ⊗ₜ[k] b)
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp [smul_eq_mul]
    | add x y hx hy => rw [smul_add, hx, hy, mul_add]
  let : IsScalarTower K A A := ⟨fun r x y => by simp only [smul_eq_mul, hsmul, mul_assoc]⟩
  have hpure : IsPurelyInseparable K (IsLocalRing.ResidueField A) := by
    rw [isPurelyInseparable_iff_pow_mem K p]
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) x
    obtain ⟨n, b, hb⟩ :=
      IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
        (R := K) (K := k') p a
    exact ⟨n, b, by rw [← map_pow, ← hb]; rfl⟩
  have hdim : Module.length K A = (p : ℕ∞) ^ Classical.choose
      (IsPurelyInseparable.finrank_eq_pow (F := k) (E := k') p) := by
    rw [Module.length_eq_finrank, Module.finrank_baseChange]
    exact_mod_cast (Classical.choose_spec
      (IsPurelyInseparable.finrank_eq_pow (F := k) (E := k') p))
  let : IsPurelyInseparable K (IsLocalRing.ResidueField A) := hpure
  let eK : K ≃+* IsLocalRing.ResidueField K :=
    RingEquiv.ofBijective (IsLocalRing.residue K) ⟨by
      rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue]
      exact Ideal.eq_bot_of_prime _, IsLocalRing.residue_surjective⟩
  have hcomp : RingHom.comp (algebraMap (IsLocalRing.ResidueField K)
        (IsLocalRing.ResidueField A)) (eK : K →+* IsLocalRing.ResidueField K) =
      RingHom.comp (RingHom.id _) (algebraMap K (IsLocalRing.ResidueField A)) := by
    ext b
    show algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField A)
        (eK b) = IsLocalRing.residue A (algebraMap K A b)
    rw [← IsLocalRing.ResidueField.algebraMap_residue]
    rfl
  let : ExpChar (IsLocalRing.ResidueField K) p :=
    expChar_of_injective_ringHom (f := eK.toRingHom) eK.injective p
  let : Module.Finite (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField A) :=
    Module.Finite.of_equiv_equiv eK (RingEquiv.refl _) hcomp
  have hpureRes : IsPurelyInseparable (IsLocalRing.ResidueField K)
      (IsLocalRing.ResidueField A) := by
    rw [isPurelyInseparable_iff_pow_mem (IsLocalRing.ResidueField K) p]
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) x
    obtain ⟨n, b, hb⟩ :=
      (isPurelyInseparable_iff_pow_mem K p).mp hpure (IsLocalRing.residue A a)
    refine ⟨n, eK b, ?_⟩
    rw [← hb]
    simpa [RingHom.comp_apply] using DFunLike.congr_fun hcomp b
  let : IsPurelyInseparable (IsLocalRing.ResidueField K)
    (IsLocalRing.ResidueField A) := hpureRes
  have hresPow := IsPurelyInseparable.finrank_eq_pow
    (F := IsLocalRing.ResidueField K) (E := IsLocalRing.ResidueField A) p
  have hresDim : Module.length (IsLocalRing.ResidueField K)
      (IsLocalRing.ResidueField A) = (p : ℕ∞) ^ Classical.choose hresPow := by
    rw [Module.length_eq_finrank]
    exact_mod_cast Classical.choose_spec hresPow
  have hlen := IsLocalRing.length_restrictScalars K A A
  have hrel : (p : ℕ∞) ^ Classical.choose
        (IsPurelyInseparable.finrank_eq_pow (F := k) (E := k') p) =
      Module.length A A * (p : ℕ∞) ^ Classical.choose hresPow := by
    simpa [hdim, hresDim] using hlen
  exact exists_eq_prime_pow_of_mul_eq_prime_pow hp hrel.symm

/-- A reduced quotient by the extended maximal ideal forces that ideal to be maximal. -/
private lemma maximalIdeal_map_eq_of_reduced_quotient
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [IsArtinianRing S]
    [IsReduced (S ⧸ extendedMaximalIdeal R S)] :
    extendedMaximalIdeal R S = IsLocalRing.maximalIdeal S := by
  have hne : extendedMaximalIdeal R S ≠ ⊤ :=
    ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S))
  let : Nontrivial (S ⧸ extendedMaximalIdeal R S) := Ideal.Quotient.nontrivial_iff.mpr hne
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk (extendedMaximalIdeal R S))
    Ideal.Quotient.mk_surjective
  have hf := IsArtinianRing.isField_of_isReduced_of_isLocalRing
    (S ⧸ extendedMaximalIdeal R S)
  exact IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hf)

/-- Reducedness of a quotient is inherited by the corresponding quotient of a localization. -/
private lemma isReduced_quotient_of_localization
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R)
    [IsReduced (R ⧸ I)] : IsReduced (S ⧸ I.map (algebraMap R S)) :=
  isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (R ⧸ I) M) _ inferInstance

/-- A localization of `L ⊗[k] D` at a prime has the same length over itself as `D` does, when
the residue fibre `L ⊗[k] κ(D)` is reduced. -/
private lemma length_localization_tensor_eq_of_reduced_fiber
    (k L D V : Type u) [Field k] [CommRing L] [CommRing D] [CommRing V]
    [Algebra k L] [Algebra k D] [IsLocalRing D] [IsArtinianRing D]
    [IsLocalRing V] [IsArtinianRing V] [Algebra (L ⊗[k] D) V]
    (N : Submonoid (L ⊗[k] D)) [IsLocalization N V]
    [IsReduced (L ⊗[k] IsLocalRing.ResidueField D)] :
    Module.length D D = Module.length V V := by
  let E := L ⊗[k] D
  let : Algebra D E := Algebra.TensorProduct.rightAlgebra
  let : Algebra D V := ((algebraMap E V).comp (algebraMap D E)).toAlgebra
  have : IsScalarTower D E V := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalHom (algebraMap D V) := isLocalHom_of_artinian _
  have : Module.Flat D E := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight k D L).symm.toLinearEquiv
  have : Module.Flat E V := IsLocalization.flat V N
  have : Module.Flat D V := Module.Flat.trans D E V
  let I : Ideal E := (IsLocalRing.maximalIdeal D).map (algebraMap D E)
  have : IsReduced (E ⧸ I) := by
    have : IsReduced (L ⊗[k] (D ⧸ IsLocalRing.maximalIdeal D)) :=
      ‹IsReduced (L ⊗[k] IsLocalRing.ResidueField D)›
    let eQ := Algebra.TensorProduct.tensorQuotientEquiv (R := k) k D L
      (IsLocalRing.maximalIdeal D)
    exact isReduced_of_injective eQ.symm eQ.symm.injective
  have hI : I.map (algebraMap E V) = extendedMaximalIdeal D V := by
    dsimp [I, extendedMaximalIdeal]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq D E V]
  have : IsReduced (V ⧸ extendedMaximalIdeal D V) := by
    rw [← hI]
    exact isReduced_quotient_of_localization E V N I
  exact length_eq_of_flat_local_map_with_same_maximal_ideal D V
    (maximalIdeal_map_eq_of_reduced_quotient D V)

/-- The length computation with the two auxiliary purely inseparable extensions supplied: `A'`
is finite purely inseparable over the field `A`, the subfield `k'` is finite purely inseparable
over `k`, and `A'` is separable over `k'`. -/
private lemma length_eq_prime_pow_of_separable_fibre
    (k K A T C A' k' : Type u)
    [Field k] [Field K] [Field A] [CommRing T] [CommRing C] [Field A'] [Field k']
    [Algebra k K] [Algebra k A] [Algebra A T] [Algebra T C] [Algebra A C]
    [IsScalarTower A T C] [IsLocalRing C] [IsArtinianRing C]
    [Algebra A A'] [Module.Finite A A'] [IsPurelyInseparable A A']
    [Algebra k k'] [Module.Finite k k'] [IsPurelyInseparable k k']
    [Algebra k A'] [Algebra k' A'] [IsScalarTower k k' A'] [IsScalarTower k A A']
    (hsep : Algebra.IsSeparableExtension k' A')
    (e : A ⊗[k] K ≃ₐ[A] T) (M : Submonoid T) [IsLocalization M C]
    (p : ℕ) (hp : Nat.Prime p) [ExpChar k p] [ExpChar K p] :
    ∃ n, Module.length C C = (p : ℕ∞) ^ n := by
  classical
  let C' := C ⊗[A] A'
  let : IsLocalRing C' := isLocalRing_tensorProduct_of_isPurelyInseparable A C A'
  have hD : ∃ n : ℕ, Module.length (K ⊗[k] k') (K ⊗[k] k') = (p : ℕ∞) ^ n :=
    length_tensorProduct_eq_prime_pow_of_isPurelyInseparable k K k' p hp
  let D := K ⊗[k] k'
  let : IsLocalRing D := isLocalRing_tensorProduct_of_isPurelyInseparable k K k'
  let : Algebra k' D := Algebra.TensorProduct.rightAlgebra
  have hredFiber : IsReduced (A' ⊗[k'] IsLocalRing.ResidueField D) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated
      (S := IsLocalRing.ResidueField D) (Or.inl hsep)
  let U := A' ⊗[A] T
  let V := A' ⊗[A] C
  let : Algebra A' U := Algebra.TensorProduct.leftAlgebra
  let : Algebra A' V := Algebra.TensorProduct.leftAlgebra
  let φA : T →ₐ[A] C := IsScalarTower.toAlgHom A T C
  let ψ : U →ₐ[A] V := Algebra.TensorProduct.map (AlgHom.id A A') φA
  let : Algebra U V := ψ.toRingHom.toAlgebra
  let : IsScalarTower A' U V := ⟨fun a x y => by
    have hinc : ψ (algebraMap A' U a) = algebraMap A' V a := by
      show ψ (a ⊗ₜ[A] (1 : T)) = a ⊗ₜ[A] (1 : C)
      rw [Algebra.TensorProduct.map_tmul]
      simp
    rw [Algebra.smul_def (R := A') (A := U) a x,
      Algebra.smul_def (R := U) (A := V) (algebraMap A' U a * x) y,
      Algebra.smul_def (R := A') (A := V) a (x • y), Algebra.smul_def (R := U) (A := V) x y]
    show ψ (algebraMap A' U a * x) * y = algebraMap A' V a * (ψ x * y)
    rw [map_mul, hinc, mul_assoc]⟩
  have hlocV : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := A) (A := A'))) V :=
    IsLocalization.tensorProduct_tensorProduct_right A A' M C
      (RingHom.ext fun t => Algebra.TensorProduct.map_tmul (AlgHom.id A A') φA 1 t)
  let eT : U ≃ₐ[A'] A' ⊗[A] (A ⊗[k] K) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A' ≃ₐ[A'] A') e.symm
  let eCancelA : A' ⊗[A] (A ⊗[k] K) ≃ₐ[A] A' ⊗[k] K :=
    Algebra.TensorProduct.cancelBaseChange k A A A' K
  let : Algebra k' (k' ⊗[k] K) := Algebra.TensorProduct.leftAlgebra
  let eCancelK' : A' ⊗[k'] (k' ⊗[k] K) ≃ₐ[k'] A' ⊗[k] K :=
    Algebra.TensorProduct.cancelBaseChange k k' k' A' K
  let eD : D ≃ₐ[k'] k' ⊗[k] K := (Algebra.TensorProduct.commRight k k' K).symm
  let E := A' ⊗[k'] D
  let : Algebra k' E := Algebra.TensorProduct.instAlgebra
  let eE : E ≃ₐ[k'] A' ⊗[k'] (k' ⊗[k] K) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A' ≃ₐ[k'] A') eD
  let eRing : U ≃+* E :=
    eT.toRingEquiv.trans eCancelA.toRingEquiv |>.trans
      eCancelK'.symm.toRingEquiv |>.trans eE.symm.toRingEquiv
  let N := M.map (Algebra.TensorProduct.includeRight (R := A) (A := A'))
  let : Algebra E V := ((algebraMap U V).comp eRing.symm.toRingHom).toAlgebra
  have : IsLocalization (N.map eRing) V :=
    IsLocalization.isLocalization_of_base_ringEquiv N V eRing
  let eV : C' ≃+* V := (Algebra.TensorProduct.comm A C A').toRingEquiv
  have : Module.Finite C C' := Module.Finite.base_change A C A'
  have : IsArtinianRing C' := IsArtinianRing.of_finite C C'
  have : IsArtinianRing V := eV.isArtinianRing
  have : IsLocalRing V := eV.isLocalRing
  have : Module.Finite K D := Module.Finite.base_change k K k'
  have : IsArtinianRing D := IsArtinianRing.of_finite K D
  have hlenV : ∃ n, Module.length V V = (p : ℕ∞) ^ n := by
    rw [← length_localization_tensor_eq_of_reduced_fiber k' A' D V (N.map eRing)]
    exact hD
  have : Module.Flat C C' := Module.Flat.baseChange A C A'
  have : IsLocalHom (algebraMap C C') := isLocalHom_of_artinian _
  have hlenC' : ∃ n, Module.length C' C' = (p : ℕ∞) ^ n := by
    rwa [Module.length_eq_of_ringEquiv eV]
  exact length_is_prime_pow_of_flat_local C C' p hp hlenC'

/-- The length of an artinian local localization of `A ⊗[k] K` is a power of the exponential
characteristic, for `A` an essentially finite type `k`-algebra. -/
private lemma length_localization_tensor_eq_prime_pow
    (k K A T C : Type u) [Field k] [Field K] [Field A] [CommRing T] [CommRing C]
    [Algebra k K] [Algebra k A] [Algebra A T] [Algebra T C] [Algebra A C]
    [IsScalarTower A T C] [IsLocalRing C] [IsArtinianRing C]
    [Algebra.EssFiniteType k A] (e : A ⊗[k] K ≃ₐ[A] T)
    (M : Submonoid T) [IsLocalization M C]
    (p : ℕ) (hp : Nat.Prime p) [ExpChar k p] [ExpChar K p] :
    ∃ n, Module.length C C = (p : ℕ∞) ^ n := by
  classical
  let Ω := AlgebraicClosure A
  obtain ⟨A', k', hA'fin, hA'pi, hk'fin, hk'pi, hsep, _⟩ :=
    exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType k A Ω
  let : Module.Finite A (↥A') := hA'fin
  let : Module.Finite k (↥k') := hk'fin
  let : IsScalarTower k A (↥A') := IsScalarTower.of_algebraMap_eq' rfl
  exact length_eq_prime_pow_of_separable_fibre k K A T C (↥A') (↥k') hsep e M p hp

/-! ### Generic points and multiplicities -/

/-- The multiplicity of a component along the identity closed immersion is the length of the
stalk at its generic point as a module over itself. -/
theorem componentMultiplicity_id {X : Scheme.{u}} (ξ : genericPoints X) :
    componentMultiplicity (𝟙 X) ξ =
      (@Module.length (X.presheaf.stalk ((𝟙 X : X ⟶ X) ξ.1))
        (X.presheaf.stalk ξ.1) _ _
        (Module.compHom (X.presheaf.stalk ξ.1)
          ((𝟙 X : X ⟶ X).stalkMap ξ.1).hom)).toNat :=
  rfl

/-- The multiplicity along the identity is the length of the stalk over itself. -/
private lemma componentMultiplicity_id_eq_length {X : Scheme.{u}} (ξ : genericPoints X) :
    componentMultiplicity (𝟙 X) ξ =
      (Module.length (X.presheaf.stalk ξ.1) (X.presheaf.stalk ξ.1)).toNat := by
  have hid : ((𝟙 X : X ⟶ X).stalkMap ξ.1).hom = RingHom.id _ :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_id X ξ.1)
  rw [componentMultiplicity_id]
  show ((@Module.length _ _ _ _ (Module.compHom _ ((𝟙 X : X ⟶ X).stalkMap ξ.1).hom)).toNat : ℤ) = _
  rw [hid]
  rfl

/-- Along a flat morphism the generic point of an irreducible component maps to the generic
point of an irreducible component. -/
private lemma genericPoint_component_mem_range_ofComponent
    {P X : Scheme.{u}} (p : P ⟶ X) [Flat p] (W : irreducibleComponents P) :
    ∃ V : irreducibleComponents X, p W.2.1.genericPoint = genericPoints.ofComponent V := by
  let ξ : P := W.2.1.genericPoint
  let V : irreducibleComponents X :=
    ⟨irreducibleComponent (p ξ), irreducibleComponent_mem_irreducibleComponents (p ξ)⟩
  let η : X := genericPoints.ofComponent V
  have hWclosed : IsClosed (W : Set P) :=
    isClosed_of_mem_irreducibleComponents (W : Set P) W.2
  have hξW : IsGenericPoint ξ (W : Set P) := W.2.1.isGenericPoint_genericPoint hWclosed
  have hηx : η ⤳ p ξ :=
    (genericPoints.isGenericPoint_ofComponent V).specializes mem_irreducibleComponent
  obtain ⟨ξ', hξ'ξ, hξ'η⟩ := (Flat.generalizingMap p) hηx
  have hWsub : (W : Set P) ⊆ closure ({ξ'} : Set P) := by
    rw [← hξW]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξ'ξ.mem_closure) isClosed_closure
  have hclsub : closure ({ξ'} : Set P) ⊆ (W : Set P) :=
    W.2.2 isIrreducible_singleton.closure hWsub
  have hξ'W : IsGenericPoint ξ' (W : Set P) := Set.Subset.antisymm hclsub hWsub
  have heq : ξ' = ξ := hξ'W.eq hξW
  exact ⟨V, by simpa [ξ, η, heq] using hξ'η⟩

/-! ### The multiplicity after a field extension -/

/-- The multiplicity of an irreducible component of the base change of an integral scheme
locally of finite type over a field along a field extension is one or, in positive
characteristic, a power of the characteristic. -/
@[stacks 0H4F]
theorem componentMultiplicity_baseChange_eq_one_or_char_pow
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsIntegral Z]
    [LocallyOfFiniteType f]
    (ξ : genericPoints
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme)) :
    let ZK : Scheme := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    componentMultiplicity (𝟙 ZK) ξ = 1 ∨
      (ringChar k ≠ 0 ∧
        ∃ n : ℕ, componentMultiplicity (𝟙 ZK) ξ = (ringChar k : ℤ) ^ n) := by
  classical
  by_cases hchar : ringChar k = 0
  · left
    let : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp hchar
    let : PerfectField k := PerfectField.ofCharZero
    let : IsReduced Z := inferInstance
    let : GeometricallyReduced f := geometricallyReduced_of_isReduced f
    let ZK : Scheme := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let : IsReduced ZK :=
      GeometricallyReduced.geometrically_isReduced (f := f) g
        (pullback.fst f g) (pullback.snd f g) (IsPullback.of_hasPullback f g)
    have hfield : IsField (ZK.presheaf.stalk ξ.1) :=
      isField_stalk_of_closure_mem_irreducibleComponents ZK ξ.1 ξ.2
    rw [componentMultiplicity_id_eq_length]
    let : Field (ZK.presheaf.stalk ξ.1) := hfield.toField
    rw [Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule _ (ZK.presheaf.stalk ξ.1))]
    rfl
  · right
    let p := ringChar k
    have hp : Nat.Prime p := CharP.char_prime_of_ne_zero k hchar
    let : CharP k p := by dsimp [p]; infer_instance
    let : ExpChar k p := ExpChar.prime hp
    let : ExpChar K p :=
      expChar_of_injective_ringHom (f := algebraMap k K) (RingHom.injective _) p
    let ZK : Scheme := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let pX : ZK ⟶ Z := pullback.fst f g
    let pY : ZK ⟶ Spec (.of K) := pullback.snd f g
    let : IsLocallyNoetherian ZK := LocallyOfFiniteType.isLocallyNoetherian pY
    have : Flat g := Flat.SpecMap_iff.mpr
      (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k K))
    let W : irreducibleComponents ZK := genericPoints.component ξ
    obtain ⟨V, hV⟩ := genericPoint_component_mem_range_ofComponent pX W
    have hWξ : W.2.1.genericPoint = ξ.1 :=
      congrArg Subtype.val (genericPoints.ofComponent_component ξ)
    have hx : pX ξ.1 = genericPoint Z := by
      have hmem : pX ξ.1 ∈ genericPoints Z := by
        rw [← hWξ, hV]
        exact (genericPoints.ofComponent V).2
      simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hmem
    let x := pX ξ.1
    let y : PrimeSpectrum K := pY ξ.1
    let z : PrimeSpectrum k := (pX ≫ f).base ξ.1
    let hbase : (pX ≫ f).base ξ.1 = (pY ≫ g).base ξ.1 :=
      congrArg (fun q : ZK ⟶ Spec (.of k) => q.base ξ.1) pullback.condition
    let R := (Spec (.of k)).presheaf.stalk z
    let A := Z.presheaf.stalk x
    let B := (Spec (.of K)).presheaf.stalk y
    let C := ZK.presheaf.stalk ξ.1
    have : Ring.KrullDimLE 0 C := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr
      (ringKrullDim_stalk_eq_zero_of_mem_genericPoints ZK ξ.1 ξ.2)
    have : IsArtinianRing C := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
    let : z.asIdeal.IsPrime := z.isPrime
    let : y.asIdeal.IsPrime := y.isPrime
    let : Algebra k R := StructureSheaf.stalkAlgebra k z
    let : Algebra R A := (f.stalkMap x).hom.toAlgebra
    let : Algebra k A := ((f.stalkMap x).hom.comp (algebraMap k R)).toAlgebra
    let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra K B := StructureSheaf.stalkAlgebra K y
    let : Algebra k B := ((algebraMap K B).comp (algebraMap k K)).toAlgebra
    let : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra R B :=
      ((eqToHom (congrArg (Spec (.of k)).presheaf.stalk hbase)) ≫ g.stalkMap y).hom.toAlgebra
    let : Algebra R C := ((pX ≫ f).stalkMap ξ.1).hom.toAlgebra
    have locR : IsLocalization.AtPrime R z.asIdeal := by
      show IsLocalization.AtPrime ((structurePresheafInCommRingCat k).stalk z) _
      infer_instance
    have hr : Function.Bijective (algebraMap k R) :=
      Field.localization_map_bijective (M := z.asIdeal.primeCompl) (by simp)
    have locB : IsLocalization.AtPrime B y.asIdeal := by
      show IsLocalization.AtPrime ((structurePresheafInCommRingCat K).stalk y) _
      infer_instance
    have hb : Function.Bijective (algebraMap K B) :=
      Field.localization_map_bijective (M := y.asIdeal.primeCompl) (by simp)
    let : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq'
      (stalkMap_spec_comp_algebraMap y ((pX ≫ f).base ξ.1) hbase).symm
    let eB : K ≃ₐ[k] B := AlgEquiv.ofBijective (IsScalarTower.toAlgHom k K B) hb
    let : Field B := (MulEquiv.isField (Field.toIsField K) eB.symm.toMulEquiv).toField
    let : ExpChar B p := expChar_of_injective_ringHom (f := algebraMap K B) hb.1 p
    have hcompatible : TensorProduct.CompatibleSMul k R A B :=
      TensorProduct.CompatibleSMul.of_algebraMap_surjective A B hr.surjective
    let e : A ⊗[k] K ≃ₐ[A] A ⊗[R] B :=
      (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) eB).trans
        (Algebra.TensorProduct.equivOfCompatibleSMul k R A A B).symm
    obtain ⟨φ, hleft, hright, M, hlocal⟩ := BaseChangeStalk.pullback_stalk_isLocalization f g ξ.1
    let T := A ⊗[R] B
    let : Algebra T C := φ.toAlgebra
    let : Algebra A T := Algebra.TensorProduct.leftAlgebra
    let : Algebra A C :=
      (φ.comp (Algebra.TensorProduct.includeLeft : A →ₐ[R] T).toRingHom).toAlgebra
    let : IsLocalization M C := hlocal
    have hRA : Algebra.EssFiniteType R A := by
      rw [← RingHom.essFiniteType_algebraMap]
      exact LocallyOfFiniteType.stalkMap f x
    have hR : Algebra.EssFiniteType k R := by
      let eR : k ≃ₐ[k] R := AlgEquiv.ofBijective (IsScalarTower.toAlgHom k k R) hr
      exact Algebra.EssFiniteType.of_surjective eR.toAlgHom eR.surjective
    have hA : Algebra.EssFiniteType k A := Algebra.EssFiniteType.comp k R A
    have hfieldA : IsField A := by
      have hxmem : closure ({x} : Set Z) ∈ irreducibleComponents Z := by
        show closure ({pX ξ.1} : Set Z) ∈ irreducibleComponents Z
        rw [hx]
        simp [irreducibleComponents_eq_singleton]
      exact isField_stalk_of_closure_mem_irreducibleComponents Z x hxmem
    let : Field A := hfieldA.toField
    have : IsScalarTower A T C := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨n, hn⟩ := length_localization_tensor_eq_prime_pow k K A T C e M p hp
    refine ⟨hchar, n, ?_⟩
    rw [componentMultiplicity_id_eq_length, hn]
    norm_cast

end Stacks.Chow
