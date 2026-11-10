module

public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreEssentiallyFiniteType
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFormulaFiniteType

/-!
# Weakly associated primes of a flat tensor product over an essentially finite type algebra

Let `R → S` be a ring map essentially of finite type, let `N` be a localization of a finite
`S`-module which is flat over `R`, and let `M` be an `R`-module. For a prime `q` of `S` lying
over `p`,

`q ∈ WeakAss_S(N ⊗_R M) ↔ (p ∈ WeakAss_R(M) and q ∈ WeakAss_S(N ⊗_R κ(p)))`,

and, for `M` in the universe of the two rings, the weakly associated primes of `N ⊗_R M` are the
contractions of the associated primes of the fibre modules over the weakly associated primes of
`M`.

## Main results

* `isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_finiteTypeModel'`:
  the pointwise equivalence for a localization of a finite module over a localization of a finite
  type algebra.
* `isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_essentiallyOfFiniteType'`:
  the pointwise equivalence for an essentially finite type ring map.
* `weaklyAssociatedPrimes_tensorProduct_eq_fibrewise_assStacks_of_small'`:
  the set equality, for a module in the universe of the two rings.

## References

* [Stacks Project, Tag 05II](https://stacks.math.columbia.edu/tag/05II)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
-/

@[expose] public section

open TensorProduct

universe u w x

namespace Stacks.WeaklyAssociatedPrimes

/-- For `N` a localization of a finite module over a localization `S` of a finite type
`R`-algebra, with `N` flat over `R`, a prime `q` of `S` is weakly associated to `N ⊗[R] M` exactly
when its contraction `p` is weakly associated to `M` and `q` is weakly associated to
`N ⊗[R] κ(p)`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_finiteTypeModel'
    (R A S : Type u) [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    [Algebra.FiniteType R A]
    (P M : Type u) (N₀ : Type w) (N : Type x)
    [AddCommGroup P] [Module A P] [Module R P]
    [IsScalarTower R A P] [Module.Finite A P]
    [AddCommGroup N₀] [Module S N₀] [Module A N₀] [Module R N₀]
    [IsScalarTower A S N₀] [IsScalarTower R A N₀] [IsScalarTower R S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    [AddCommGroup M] [Module R M]
    (U : Submonoid A) [IsLocalization U S]
    (φ : P →ₗ[A] N₀) [IsLocalizedModule U φ]
    (V : Submonoid S) (f : N₀ →ₗ[S] N) [IsLocalizedModule V f]
    (q : Ideal S) [q.IsPrime] (hV : V ≤ q.primeCompl) :
    IsWeaklyAssociatedPrime S (N ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime R M (q.comap (algebraMap R S)) ∧
        IsWeaklyAssociatedPrime S
          (N ⊗[R] (q.comap (algebraMap R S)).ResidueField) q := by
  let qA : Ideal A := q.comap (algebraMap A S)
  let : qA.IsPrime := Ideal.IsPrime.comap _
  let p : Ideal R := q.comap (algebraMap R S)
  let : p.IsPrime := Ideal.IsPrime.comap _
  have hp : qA.comap (algebraMap R A) = p := by
    ext r
    change algebraMap A S (algebraMap R A r) ∈ q ↔ algebraMap R S r ∈ q
    rw [← IsScalarTower.algebraMap_apply R A S]
  have hdisj : Disjoint (V : Set S) (q : Set S) :=
    Set.disjoint_left.mpr fun s hs hq => hV hs hq
  have hflatA := flat_localizedModule_of_finiteTypeModel (R := R) (T := A) (S := S) U φ V f q hV
  have : qA.LiesOver p := ⟨hp.symm⟩
  have hA := isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteType'
    (R := R) (A := A) (P := P) (M := M) p qA hflatA
  have hM := isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteTypeModel
    (R := R) (A := A) (S := S) (P := P) (N₀ := N₀) (N := N) (M := M)
    U φ V f q hdisj
  have hK := isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteTypeModel
    (R := R) (A := A) (S := S) (P := P) (N₀ := N₀) (N := N)
    (M := p.ResidueField) U φ V f q hdisj
  exact hM.trans (hA.trans (and_congr_right fun _ => hK.symm))

/-- For `R → S` essentially of finite type and `N` a localization of a finite `S`-module which
is flat over `R`, a prime `q` of `S` disjoint from the localizing submonoid is weakly associated
to `N ⊗[R] M` exactly when its contraction `p` is weakly associated to `M` and `q` is weakly
associated to `N ⊗[R] κ(p)`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_essentiallyOfFiniteType'
    (R S : Type u) (M : Type u) (N₀ : Type w) (N : Type x)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N₀] [Module S N₀] [Module.Finite S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    (hfinite : IsEssentiallyOfFiniteType R S (algebraMap R S))
    (V : Submonoid S) (f : N₀ →ₗ[S] N) [IsLocalizedModule V f]
    (q : Ideal S) [q.IsPrime]
    (hdisj : Disjoint (V : Set S) (q : Set S)) :
    IsWeaklyAssociatedPrime S (N ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime R M (q.comap (algebraMap R S)) ∧
        IsWeaklyAssociatedPrime S
          (N ⊗[R] (q.comap (algebraMap R S)).ResidueField) q := by
  classical
  obtain ⟨A, hA, aRA, hFT, U, aAS, hTower, hLoc,
    P, hPAdd, hPA, hPfin, φ, hφ⟩ := exists_finite_type_model hfinite N₀
  let : CommRing A := hA
  let : Algebra R A := aRA
  let : Algebra.FiniteType R A := hFT
  let : Algebra A S := aAS
  have hcomp : (algebraMap A S).comp (algebraMap R A) = algebraMap R S := by
    ext r
    let : Algebra R S := (algebraMap R S).toAlgebra
    let : IsScalarTower R A S := hTower
    exact (IsScalarTower.algebraMap_apply R A S r).symm
  let : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let : IsLocalization U S := hLoc
  let : AddCommGroup P := hPAdd
  let : Module A P := hPA
  let : Module.Finite A P := hPfin
  let : Module R P := Module.compHom P (algebraMap R A)
  let : IsScalarTower R A P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module A N₀ := Module.compHom N₀ (algebraMap A S)
  let : IsScalarTower A S N₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module R N₀ := Module.compHom N₀ (algebraMap R A)
  let : IsScalarTower R A N₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R S N₀ := IsScalarTower.of_algebraMap_smul fun r m => by
    change algebraMap R S r • m = algebraMap A S (algebraMap R A r) • m
    rw [← hcomp]
    rfl
  let : IsLocalizedModule U φ := hφ
  exact isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_finiteTypeModel'
    R A S P M N₀ N U φ V f q fun _ hs => Set.disjoint_left.mp hdisj hs

/-- For `M` in the universe of the two rings, the weakly associated primes of `N ⊗[R] M` are the
contractions of the primes of the fibre rings associated to the fibre modules, over the weakly
associated primes of `M`. -/
@[stacks 05II "the full set equality, for a module in the universe of the two rings"]
theorem weaklyAssociatedPrimes_tensorProduct_eq_fibrewise_assStacks_of_small'
    (R S : Type u) (M : Type u) (N₀ : Type w) (N : Type x)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N₀] [Module S N₀] [Module.Finite S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    (hfinite : IsEssentiallyOfFiniteType R S (algebraMap R S))
    (T : Submonoid S) (f : N₀ →ₗ[S] N) [IsLocalizedModule T f] :
    weaklyAssociatedPrimes S (N ⊗[R] M) =
      {q : Ideal S | ∃ p ∈ weaklyAssociatedPrimes R M, ∃ hp : p.IsPrime,
        letI : p.IsPrime := hp
        ∃ q' ∈ assStacks (S ⊗[R] p.ResidueField)
          ((S ⊗[R] p.ResidueField) ⊗[S] N),
          q = Ideal.comap (Algebra.TensorProduct.includeLeft (R := R)
            (S := S) (A := S) (B := p.ResidueField)).toRingHom q'} := by
  classical
  let : Module R N₀ := Module.compHom N₀ (algebraMap R S)
  let : IsScalarTower R S N₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  ext q
  constructor
  · intro hq
    have := IsWeaklyAssociatedPrime.isPrime S (N ⊗[R] M) hq
    have hdisj : Disjoint (T : Set S) (q : Set S) := by
      let ψ := TensorProduct.AlgebraTensorModule.map f (LinearMap.id : M →ₗ[R] M)
      let : IsLocalizedModule T ψ := isLocalizedModule_tensorRight (S := Localization T) T f
      exact disjoint_of_isWeaklyAssociatedPrime_localizedModule T ψ q
        ((mem_weaklyAssociatedPrimes_iff S (N ⊗[R] M)).mp hq)
    have hh := (isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_essentiallyOfFiniteType'
      R S M N₀ N hfinite T f q hdisj).mp
        ((mem_weaklyAssociatedPrimes_iff S (N ⊗[R] M)).mp hq)
    let p := q.comap (algebraMap R S)
    let : p.IsPrime := Ideal.IsPrime.comap _
    let : IsNoetherianRing (S ⊗[R] p.ResidueField) :=
      isNoetherianRing_tensorResidueField_of_isEssentiallyOfFiniteType hfinite p
    obtain ⟨q', hq', hqeq⟩ :=
      (isWeaklyAssociatedPrime_tensorResidueField_iff p q).mp hh.2
    exact ⟨p, hh.1, inferInstance, q', hq', hqeq⟩
  · rintro ⟨p, hp, hprime, q', hq', rfl⟩
    have := hq'.1
    let q := q'.comap (algebraMap S (S ⊗[R] p.ResidueField))
    let : q.IsPrime := Ideal.IsPrime.comap _
    have hbase : q.comap (algebraMap R S) = p := comap_comap_algebraMap_tensorResidueField p q'
    let : IsNoetherianRing (S ⊗[R] p.ResidueField) :=
      isNoetherianRing_tensorResidueField_of_isEssentiallyOfFiniteType hfinite p
    have hfiber : IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) q :=
      (isWeaklyAssociatedPrime_tensorResidueField_iff p q).mpr ⟨q', hq', rfl⟩
    have hdisj : Disjoint (T : Set S) (q : Set S) := by
      let ψ := TensorProduct.AlgebraTensorModule.map f
        (LinearMap.id : p.ResidueField →ₗ[R] p.ResidueField)
      let : IsLocalizedModule T ψ := isLocalizedModule_tensorRight (S := Localization T) T f
      exact disjoint_of_isWeaklyAssociatedPrime_localizedModule T ψ q hfiber
    refine (mem_weaklyAssociatedPrimes_iff S (N ⊗[R] M)).mpr
      ((isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_essentiallyOfFiniteType'
        R S M N₀ N hfinite T f q hdisj).mpr ⟨?_,
          (isWeaklyAssociatedPrime_tensorResidueField_congr (N := N) hbase.symm q).mp hfiber⟩)
    rw [hbase]
    exact hp

end Stacks.WeaklyAssociatedPrimes

end
