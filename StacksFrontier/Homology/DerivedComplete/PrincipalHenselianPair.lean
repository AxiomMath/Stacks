module

public import Mathlib
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.Homology.DerivedComplete.PrincipalCompletionKernel
public import StacksFrontier.RingTheory.Henselian.Pair
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria
public import StacksFrontier.RingTheory.Henselian.Pair.Limits
public import StacksFrontier.RingTheory.Henselian.Pair.Nilpotent
public import StacksFrontier.RingTheory.Henselian.Pair.Operations

/-!
# Derived complete rings form henselian pairs

Let `A` be a commutative ring and `I ⊆ A` an ideal such that `A`, viewed as a module over itself,
is derived complete with respect to `I`. Then `(A, I)` is a henselian pair.

The proof reduces to the case of a principal ideal `(f) ⊆ I`. There the canonical map
`A → A^` to the `(f)`-adic completion is surjective by Stacks 091R, its kernel is square-zero by
Stacks 0G3G, hence consists of nilpotents; so `(A, ker)` is a henselian pair by Stacks 0ALI, and
henselianness of the `(f)`-adic completion descends along the surjection. Since `I` is the union
of the principal ideals it contains, and the henselian ideals of `A` have a largest element
(Stacks 0G1S) which is closed under the transitivity of Stacks 0DYD, the pair `(A, I)` is
henselian.

## Main definitions

There are no new definitions; derived completeness is `IsDerivedCompleteModule` of
`StacksFrontier.Homology.DerivedComplete`, and henselian pairs are `HenselianPair` of
`StacksFrontier.RingTheory.Henselian.Pair`.

## Main results

* `PrincipalHenselianPair.henselianPair_of_isDerivedCompleteModule`: a ring derived complete with
  respect to an ideal forms a henselian pair with that ideal.

## Implementation notes

Derived completeness is expressed using the ring as a module over itself, regarded as an object of
the derived category concentrated in degree zero. The countable products in the derived category
that the predicate refers to are supplied inside the statement by Stacks 07KC rather than assumed,
so the result carries no product hypothesis.

Mathlib's `HenselianRing` is the intermediate notion used to transport henselianness along the
surjection `A → A^`: lifting a simple root along a surjection with nilpotent kernel is Stacks
0ALI, and the passage from `HenselianRing` to `HenselianPair` goes through Gabber's unique-root
criterion, the fifth clause of Stacks 09XI.

## References

* [The Stacks Project, Tag 0G3H](https://stacks.math.columbia.edu/tag/0G3H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u

namespace PrincipalHenselianPair

open Polynomial
open scoped Ring

/-- A simple root of a monic polynomial over the target of a surjection with nilpotent kernel
lifts to a simple root over the source. -/
private theorem exists_root_lift
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (hk : RingHom.ker φ ≤ nilradical R)
    (p : R[X]) (hp : p.Monic) (x : S) (hx : (p.map φ).IsRoot x)
    (hd : IsUnit ((p.map φ).derivative.eval x)) :
    ∃ y : R, p.IsRoot y ∧ φ y = x ∧ IsUnit (p.derivative.eval y) := by
  let _ : HenselianRing R (RingHom.ker φ) :=
    (etaleBaseChange_isEquivalence_and_henselianRing_of_le_nilradical _ hk).2
  obtain ⟨z, rfl⟩ := hφ x
  have hz : p.eval z ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, ← eval_map_apply, hx.eq_zero]
  have hq : IsUnit ((Ideal.Quotient.mk (RingHom.ker φ)) (p.derivative.eval z)) := by
    obtain ⟨w, hw⟩ := hd.exists_right_inv
    obtain ⟨v, rfl⟩ := hφ w
    rw [isUnit_iff_exists_inv]
    refine ⟨Ideal.Quotient.mk _ v, ?_⟩
    change Ideal.Quotient.mk _ (p.derivative.eval z * v) = Ideal.Quotient.mk _ 1
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, map_mul, map_one, ← eval_map_apply,
      ← derivative_map, hw, sub_self]
  obtain ⟨y, hy, hyz⟩ := HenselianRing.is_henselian p hp z hz hq
  have hyz' : φ y = φ z := by
    rw [← sub_eq_zero, ← map_sub]
    exact hyz
  refine ⟨y, hy, hyz', isUnit_of_map_of_surjective_of_ker_le_nilradical φ hφ hk ?_⟩
  rwa [← eval_map_apply, ← derivative_map, hyz']

/-- Henselianness descends along a surjection with kernel inside both the nilradical and the
ideal under consideration. -/
private theorem henselianRing_of_surjective_of_ker_le_nilradical
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (I : Ideal R) (hkerI : RingHom.ker φ ≤ I)
    (hk : RingHom.ker φ ≤ nilradical R) [HenselianRing S (I.map φ)] :
    HenselianRing R I where
  jac := by
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    apply isUnit_of_map_of_surjective_of_ker_le_nilradical φ hφ hk
    simpa only [map_mul, map_add, map_one] using
      Ideal.mem_jacobson_bot.mp (HenselianRing.jac (Ideal.mem_map_of_mem φ hx)) (φ y)
  is_henselian := by
    intro p hp a₀ hpa hdu
    let q : R ⧸ I →+* S ⧸ I.map φ := Ideal.Quotient.lift I
      ((Ideal.Quotient.mk (I.map φ)).comp φ) fun x hx =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hx)
    have hdq : IsUnit ((Ideal.Quotient.mk (I.map φ))
        ((p.map φ).derivative.eval (φ a₀))) := by
      rw [derivative_map, eval_map_apply]
      simpa only [q, Ideal.Quotient.lift_mk, RingHom.comp_apply] using hdu.map q
    have hpmem : (p.map φ).eval (φ a₀) ∈ I.map φ := by
      simpa only [eval_map_apply] using Ideal.mem_map_of_mem φ hpa
    obtain ⟨b, hb, hba⟩ := HenselianRing.is_henselian (p.map φ) (hp.map φ)
      (φ a₀) hpmem hdq
    have hdb : IsUnit ((p.map φ).derivative.eval b) := by
      let : IsLocalHom (Ideal.Quotient.mk (I.map φ)) :=
        isLocalHom_of_le_jacobson_bot _ HenselianRing.jac
      apply IsUnit.of_map (Ideal.Quotient.mk (I.map φ))
      rwa [show Ideal.Quotient.mk (I.map φ) ((p.map φ).derivative.eval b) =
          Ideal.Quotient.mk (I.map φ) ((p.map φ).derivative.eval (φ a₀)) by
        rw [Ideal.Quotient.eq]
        exact (SModEq.sub_mem).1 (((SModEq.sub_mem).2 hba).eval _)]
    obtain ⟨a, ha, hab, _⟩ := exists_root_lift φ hφ hk p hp b hb hdb
    refine ⟨a, ha, ?_⟩
    obtain ⟨i, hi, hii⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hba
    have : a - a₀ - i ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, map_sub, hab, hii]
      ring
    convert I.add_mem (hkerI this) hi using 1
    ring

/-- Alias of `henselianPair_of_henselianRing`. -/
private alias henselianPair_of_henselianRing := _root_.henselianPair_of_henselianRing

/-- **Stacks 0G3H.** A commutative ring derived complete with respect to an ideal forms a
henselian pair with that ideal. -/
@[stacks 0G3H]
theorem henselianPair_of_isDerivedCompleteModule
    (A : Type u) [CommRing A] (I : Ideal A) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_nat
    IsDerivedCompleteModule I (ModuleCat.of A A) → HenselianPair A I := by
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_nat
  intro hA
  have hprincipal : ∀ f ∈ I, HenselianPair A (Ideal.span {f}) := by
    intro f hf
    let K : Ideal A := Ideal.span {f}
    have hKI : K ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hf
    have hK : IsDerivedCompleteModule K (ModuleCat.of A A) :=
      fun g hg => hA g (hKI hg)
    have hfg : K.FG := Submodule.fg_span_singleton f
    let φ : A →+* AdicCompletion K A := algebraMap A (AdicCompletion K A)
    have hφ : Function.Surjective φ :=
      (isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective
        A K A).2 hfg hK
    have hker : RingHom.ker φ ≤ ⨅ n : ℕ, K ^ n := by
      intro x hx
      refine Ideal.mem_iInf.mpr fun n => ?_
      have hx0 : AdicCompletion.of K A x = 0 := hx
      have he := congrArg (AdicCompletion.evalₐ K n) hx0
      rw [AdicCompletion.evalₐ_of, map_zero] at he
      exact Ideal.Quotient.eq_zero_iff_mem.mp he
    have hkerK : RingHom.ker φ ≤ K :=
      hker.trans (by simpa using (iInf_le (fun n : ℕ => K ^ n) 1))
    have hsq : (⨅ n : ℕ, K ^ n) ^ 2 = ⊥ :=
      (PrincipalCompletionKernel.iInf_principal_powers_annihilates_ker_adicCompletion
        A f A).2 hK
    have hnil : RingHom.ker φ ≤ nilradical A := by
      intro x hx
      apply mem_nilradical.mpr
      refine ⟨2, ?_⟩
      have hx2 := Ideal.pow_mem_pow (hker hx) 2
      rwa [hsq, Ideal.mem_bot] at hx2
    let : IsAdicComplete (K.map φ) (AdicCompletion K A) :=
      (IsAdicComplete.map_algebraMap_iff (S := AdicCompletion K A) K (AdicCompletion K A)).mpr
        (AdicCompletion.isAdicComplete hfg)
    let : HenselianRing A K :=
      henselianRing_of_surjective_of_ker_le_nilradical φ hφ K hkerK hnil
    exact henselianPair_of_henselianRing A K
  obtain ⟨J, hJ, hmax⟩ := exists_greatest_henselianPair A
  have hIJ : I ≤ J := fun f hf =>
    hmax (Ideal.span {f}) (hprincipal f hf) (Ideal.mem_span_singleton_self f)
  exact ((henselianPair_iff_of_le hIJ).mpr hJ).1

end PrincipalHenselianPair

end

end
