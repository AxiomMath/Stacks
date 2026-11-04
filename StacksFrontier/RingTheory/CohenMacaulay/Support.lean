module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Support

/-!
# The support of a ring over itself, and the dimension of a full support

A commutative ring is faithful over itself, so its annihilator is zero and its support is all of
`Spec(R)`; and a module whose support is all of `Spec(R)` has `dim Supp(M) = dim R`, both sides
being the Krull dimension of the same subset. Both facts are used wherever a statement about
`Module.supportDim` is to be read as a statement about `ringKrullDim`.

## Main results

* `Module.support_self`: `Supp(R) = Spec(R)` for `R` as a module over itself.
* `Module.supportDim_eq_ringKrullDim_of_support_eq_univ`: a module of full support has the
  dimension of the ring for the dimension of its support.
* `Module.supportDim_eq_of_ringEquiv`: the dimension of the support of a module carrying two
  module structures matched by a ring isomorphism is the same computed over either ring.
* `Module.supportDim_eq_of_semilinearEquiv`: the dimension of the support is invariant under an
  additive isomorphism of modules which is semilinear over a ring isomorphism.

## Implementation notes

Mathlib's `Module.support_of_noZeroSMulDivisors` and `Module.support_of_isTorsionFree` need a
domain or a nonzero module; the statement here needs neither, and over the zero ring both sides
are empty.
-/

@[expose] public section

/-- **The support of a commutative ring as a module over itself is its whole prime spectrum**:
`R` acts faithfully on itself, so `Ann(R) = ⊥` and `Supp(R) = V(⊥) = Spec(R)`. Unlike
`Module.support_of_noZeroSMulDivisors` this needs neither a domain nor a nonzero module; over the
zero ring both sides are empty. -/
public theorem Module.support_self (R : Type*) [CommRing R] : Module.support R R = Set.univ := by
  rw [Module.support_eq_zeroLocus, Module.annihilator_eq_bot.2 (inferInstance : FaithfulSMul R R),
    PrimeSpectrum.zeroLocus_bot]

/-- **A module of full support has the dimension of the ring for the dimension of its support**,
both being the Krull dimension of the same subset of `Spec(R)`, namely of `Spec(R)` itself. -/
public theorem Module.supportDim_eq_ringKrullDim_of_support_eq_univ {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (hsupp : Module.support R M = Set.univ) :
    Module.supportDim R M = ringKrullDim R :=
  le_antisymm (Module.supportDim_le_ringKrullDim R M)
    (Order.krullDim_le_of_strictMono
      (fun p => (⟨p, hsupp ▸ Set.mem_univ p⟩ : Module.support R M)) fun _ _ lt => lt)

/-- **The dimension of the support of a module is invariant under a ring isomorphism** matching
the two module structures: both sides are the Krull dimension of the quotient by the
annihilator, and the isomorphism carries one annihilator onto the other. -/
public theorem Module.supportDim_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (M : Type*) [AddCommGroup M] [Module A M] [Module B M] [Algebra A B]
    [IsScalarTower A B M] (hAlg : algebraMap A B = e.toRingHom) [Module.Finite A M]
    [Module.Finite B M] : Module.supportDim A M = Module.supportDim B M := by
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  have hAnn : Ideal.comap (algebraMap A B) (Module.annihilator B M) =
      Module.annihilator A M := Module.comap_annihilator
  have hmap : Ideal.map (algebraMap A B) (Module.annihilator A M) =
      Module.annihilator B M := by
    rw [← hAnn]
    exact Ideal.map_comap_of_surjective (algebraMap A B) (hAlg ▸ e.surjective) _
  exact ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquiv _ _ e (by simpa [hAlg] using hmap.symm))

/-- **The support is carried along a semilinear isomorphism.** If `e : A ≃+* B` and `φ : M ≃+ N`
satisfy `φ (a • m) = e a • φ m`, then a prime `𝔭` of `A` lies in the support of `M` exactly when
its image `e(𝔭)` lies in the support of `N`: an element `m` is killed by no element outside `𝔭`
exactly when `φ m` is killed by no element outside `e(𝔭)`. -/
public theorem Module.mem_support_iff_of_semilinearEquiv {A B : Type*} [CommRing A]
    [CommRing B] (e : A ≃+* B) {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module B N] (φ : M ≃+ N) (hφ : ∀ (a : A) (m : M), φ (a • m) = e a • φ m)
    (p : PrimeSpectrum A) :
    p ∈ Module.support A M ↔ PrimeSpectrum.comapEquiv e p ∈ Module.support B N := by
  have hsmul : ∀ (b : B) (m : M), b • φ m = φ (e.symm b • m) := fun b m => by
    rw [hφ, e.apply_symm_apply]
  rw [Module.mem_support_iff', Module.mem_support_iff']
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨φ m, fun b hb => ?_⟩
    rw [hsmul, Ne, AddEquivClass.map_eq_zero_iff]
    exact hm _ hb
  · rintro ⟨n, hn⟩
    refine ⟨φ.symm n, fun a ha h0 => hn (e a) (by simpa using ha) ?_⟩
    rwa [← φ.apply_symm_apply n, ← hφ, AddEquivClass.map_eq_zero_iff]

/-- **The dimension of the support is invariant under a semilinear isomorphism.** If
`e : A ≃+* B` and `φ : M ≃+ N` satisfy `φ (a • m) = e a • φ m`, then `dim Supp_A(M) =
dim Supp_B(N)`: the order isomorphism of spectra induced by `e` restricts to one of supports, by
`Module.mem_support_iff_of_semilinearEquiv`. No finiteness is needed. -/
public theorem Module.supportDim_eq_of_semilinearEquiv {A B : Type*} [CommRing A]
    [CommRing B] (e : A ≃+* B) {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module B N] (φ : M ≃+ N) (hφ : ∀ (a : A) (m : M), φ (a • m) = e a • φ m) :
    Module.supportDim A M = Module.supportDim B N := by
  let σ := PrimeSpectrum.comapEquiv e
  let τ : Module.support A M ≃o Module.support B N :=
    { toFun := fun p => ⟨σ p, (Module.mem_support_iff_of_semilinearEquiv e φ hφ p).1 p.2⟩
      invFun := fun q => ⟨σ.symm q,
        (Module.mem_support_iff_of_semilinearEquiv e φ hφ _).2
          ((σ.apply_symm_apply q).symm ▸ q.2)⟩
      left_inv := fun p => Subtype.ext (σ.symm_apply_apply p)
      right_inv := fun q => Subtype.ext (σ.apply_symm_apply q)
      map_rel_iff' := fun {p q} => σ.le_iff_le }
  exact Order.krullDim_eq_of_orderIso τ

end
