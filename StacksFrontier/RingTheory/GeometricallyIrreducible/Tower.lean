module


public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs
import StacksFrontier.RingTheory.GeometricallyIrreducible.Criteria
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric irreducibility of towers and of field extensions

Let `k` be a field. A `k`-algebra is geometrically irreducible when the spectrum of its base change
along every field extension of `k` is an irreducible topological space [stacks, 037L]. This file
proves:

* in a tower `k → K → S` in which `k` and `K` are fields, if `K/k` is geometrically irreducible and
  `S` is geometrically irreducible over `K`, then `S` is geometrically irreducible over `k`;
* a field extension `K/k` in which `k` is algebraically closed is geometrically irreducible;
* a field extension `K/k` is geometrically irreducible if and only if every element of `K`
  separably algebraic over `k` lies in `k`.

## Main results

* `Algebra.IsGeometricallyIrreducible.trans`: geometric irreducibility is transitive in a tower
  `k → K → S` over fields `k` and `K`.
* `Algebra.IsGeometricallyIrreducible.of_algebraicClosure_eq_bot`: a field extension `K/k` with
  `algebraicClosure k K = ⊥` is geometrically irreducible over `k`.
* `separableClosure.eq_bot_iff_geometricallyIrreducible`: the separable closure of `k` in `K` is
  trivial if and only if `K/k` is geometrically irreducible.
* `Stacks.Irreducibility.TrivialSepClosure.isGeometricallyIrreducible_of_injective`: a subalgebra
  of a geometrically irreducible `k`-algebra is geometrically irreducible.

## Implementation notes

`Algebra.IsGeometricallyIrreducible` abbreviates the morphism property
`AlgebraicGeometry.GeometricallyIrreducible` for a structure morphism of affine schemes, so the
rings involved lie in one universe. The tower is spelled with `IsScalarTower k K S`, so that the
conclusion is about `algebraMap k S` itself. "`k` is algebraically closed in `K`" is spelled
`algebraicClosure k K = ⊥`, and "every element of `K` separably algebraic over `k` lies in `k`" is
spelled `separableClosure k K = ⊥`.

## References

* [Stacks Project, Tag 0G30](https://stacks.math.columbia.edu/tag/0G30)
* [Stacks Project, Tag 037P](https://stacks.math.columbia.edu/tag/037P)
* [Stacks Project, Tag 0G33](https://stacks.math.columbia.edu/tag/0G33)
-/

@[expose] public section

universe u

/-! ### Transitivity in a tower -/

namespace Stacks.Irreducibility.TowerTransitivity



open AlgebraicGeometry CategoryTheory CommRingCat

/-- In a tower of algebras `R → A → B` the structure morphism `Spec B ⟶ Spec R` is the composite
of `Spec B ⟶ Spec A` and `Spec A ⟶ Spec R`. -/
private theorem specMap_algebraMap_eq_comp (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] :
    Spec.map (ofHom (algebraMap R B)) =
      Spec.map (ofHom (algebraMap A B)) ≫ Spec.map (ofHom (algebraMap R A)) := by
  rw [IsScalarTower.algebraMap_eq R A B, ofHom_comp, Spec.map_comp]

/-- Let `K/k` be a geometrically irreducible field extension and let `S` be a geometrically
irreducible `K`-algebra. Then `S` is geometrically irreducible over `k`. -/
public theorem solution (k K S : Type u) [Field k] [Field K] [CommRing S] [Algebra k K]
    [Algebra K S] [Algebra k S] [IsScalarTower k K S]
    [Algebra.IsGeometricallyIrreducible k K] [Algebra.IsGeometricallyIrreducible K S] :
    Algebra.IsGeometricallyIrreducible k S := by
  rw [Algebra.IsGeometricallyIrreducible, specMap_algebraMap_eq_comp k K S]
  exact GeometricallyIrreducible.comp _ _

end Stacks.Irreducibility.TowerTransitivity


@[expose] public section



/-- Let `K/k` be a geometrically irreducible field extension and let `S` be a geometrically
irreducible `K`-algebra. Then `S` is geometrically irreducible over `k`. -/
@[stacks 0G30]
public theorem Algebra.IsGeometricallyIrreducible.trans (k K S : Type u) [Field k] [Field K]
    [CommRing S] [Algebra k K] [Algebra K S] [Algebra k S] [IsScalarTower k K S]
    [Algebra.IsGeometricallyIrreducible k K] [Algebra.IsGeometricallyIrreducible K S] :
    Algebra.IsGeometricallyIrreducible k S :=
  Stacks.Irreducibility.TowerTransitivity.solution k K S

end

/-! ### Extensions in which the base is algebraically closed -/

namespace Stacks.Irreducibility.TrivialAlgClosure



open Polynomial TensorProduct

section Polynomials

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- If `k` is algebraically closed in `K`, then a monic divisor in `K[X]` of a monic polynomial
coming from `k[X]` already comes from a monic polynomial in `k[X]`. -/
private theorem exists_monic_map_eq_of_monic_of_dvd_map (h : algebraicClosure k K = ⊥) {p : k[X]}
    (hp : p.Monic) {q : K[X]} (hq : q.Monic) (hdvd : q ∣ p.map (algebraMap k K)) :
    ∃ q₀ : k[X], q₀.Monic ∧ q₀.map (algebraMap k K) = q := by
  have hlifts : q ∈ lifts (algebraMap k K) := (lifts_iff_coeff_lifts q).mpr fun n =>
    IntermediateField.mem_bot.mp (h ▸ mem_algebraicClosure_iff.mpr
      (Polynomial.isIntegral_coeff_of_dvd p q hp hq hdvd n).isAlgebraic)
  obtain ⟨q₀, hmap, -, hmonic⟩ := lifts_and_degree_eq_and_monic hlifts hq
  exact ⟨q₀, hmonic, hmap⟩

/-- If `k` is algebraically closed in `K`, then a monic irreducible polynomial over `k` stays
irreducible over `K`. -/
private theorem irreducible_map_of_algebraicClosure_eq_bot (h : algebraicClosure k K = ⊥)
    {p : k[X]} (hp : p.Monic) (hirr : Irreducible p) :
    Irreducible (p.map (algebraMap k K)) := by
  have hinj := Polynomial.map_injective (algebraMap k K) (algebraMap k K).injective
  rw [Polynomial.irreducible_of_monic (hp.map _)
    fun h1 => hirr.ne_one (hinj (by rw [h1, Polynomial.map_one]))]
  intro a b ha hb hab
  obtain ⟨A, hA, hAa⟩ := exists_monic_map_eq_of_monic_of_dvd_map h hp ha (Dvd.intro _ hab)
  obtain ⟨B, hB, hBb⟩ := exists_monic_map_eq_of_monic_of_dvd_map h hp hb (Dvd.intro_left _ hab)
  have hABp : A * B = p := hinj (by rw [Polynomial.map_mul, hAa, hBb, hab])
  exact ((Polynomial.irreducible_of_monic hp hirr.ne_one).mp hirr A B hA hB hABp).imp
    (fun h1 => by rw [← hAa, h1, Polynomial.map_one])
    (fun h1 => by rw [← hBb, h1, Polynomial.map_one])

end Polynomials

/-- Let the `k`-algebra `k'` be generated by an element `α` whose minimal polynomial stays
irreducible over the extension `K/k`. Then `K ⊗[k] k'` is a domain. -/
private theorem isDomain_tensorProduct_of_irreducible_map {k K k' : Type*} [Field k] [Field K]
    [Algebra k K] [Field k'] [Algebra k k'] {α : k'} (hα : Algebra.adjoin k {α} = ⊤)
    (hirr : Irreducible ((minpoly k α).map (algebraMap k K))) : IsDomain (K ⊗[k] k') := by
  have : Fact (Irreducible ((minpoly k α).map (algebraMap k K))) := ⟨hirr⟩
  have haeval : aeval ((1 : K) ⊗ₜ[k] α) ((minpoly k α).map (algebraMap k K)) = 0 := by
    rw [aeval_map_algebraMap K, ← Algebra.TensorProduct.includeRight_apply, aeval_algHom_apply,
      minpoly.aeval, map_zero]
  set ψ := AdjoinRoot.liftAlgHom ((minpoly k α).map (algebraMap k K))
    (Algebra.ofId K (K ⊗[k] k')) (1 ⊗ₜ[k] α) (by simpa [aeval_def] using haeval) with hψ
  have hgen : Algebra.adjoin K {(1 : K) ⊗ₜ[k] α} = ⊤ := by
    simpa using Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := K) {α} hα
  have hsurj : Function.Surjective ψ := (AlgHom.range_eq_top ψ).mp <| top_le_iff.mp <| hgen ▸
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ⟨AdjoinRoot.root _, by simp [hψ]⟩)
  have e : AdjoinRoot ((minpoly k α).map (algebraMap k K)) ≃ₐ[K] K ⊗[k] k' :=
    AlgEquiv.ofBijective ψ ⟨ψ.toRingHom.injective, hsurj⟩
  exact e.symm.toRingEquiv.injective.isDomain

/-- Let `K/k` be a field extension. If `k` is algebraically closed in `K`, that is, if the relative
algebraic closure `algebraicClosure k K` is trivial, then `K` is geometrically irreducible over
`k`. -/
public theorem solution (k K : Type u) [Field k] [Field K] [Algebra k K]
    (h : algebraicClosure k K = ⊥) : Algebra.IsGeometricallyIrreducible k K := by
  refine ((AlgebraicGeometry.geometricallyIrreducible_tfae k K (SeparableClosure k)
    (AlgebraicClosure k)).out 2 5).mp ?_
  intro k' _ _ _ _
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k k'
  have hint : IsIntegral k α := IsIntegral.of_finite k α
  have : IsDomain (K ⊗[k] k') := isDomain_tensorProduct_of_irreducible_map
    (by rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα,
      IntermediateField.top_toSubalgebra])
    (irreducible_map_of_algebraicClosure_eq_bot h (minpoly.monic hint) (minpoly.irreducible hint))
  infer_instance

end Stacks.Irreducibility.TrivialAlgClosure





/-- Let `K/k` be a field extension. If `k` is algebraically closed in `K`, that is, if the relative
algebraic closure `algebraicClosure k K` is trivial, then `K` is geometrically irreducible over
`k`. -/
@[stacks 037P]
public theorem Algebra.IsGeometricallyIrreducible.of_algebraicClosure_eq_bot (k K : Type u)
    [Field k] [Field K] [Algebra k K] (h : algebraicClosure k K = ⊥) :
    Algebra.IsGeometricallyIrreducible k K :=
  Stacks.Irreducibility.TrivialAlgClosure.solution k K h


/-! ### Extensions with trivial separable closure of the base -/

namespace Stacks.Irreducibility.TrivialSepClosure



open AlgebraicGeometry CommRingCat

open scoped IntermediateField TensorProduct

/-- The spectrum of a subring of a ring with irreducible spectrum is irreducible. -/
theorem irreducibleSpace_primeSpectrum_of_injective {A B : Type*} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (h : IrreducibleSpace (PrimeSpectrum B)) : IrreducibleSpace (PrimeSpectrum A) :=
  PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mpr
    (SeparableCriteria.isPrime_nilradical_of_injective f hf
      (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp h))

/-- If `B ⊗[k] A` has irreducible spectrum, so does `A ⊗[k] B`. -/
private theorem irreducibleSpace_primeSpectrum_tensorProduct_comm {k : Type*} (A B : Type*)
    [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (h : IrreducibleSpace (PrimeSpectrum (B ⊗[k] A))) :
    IrreducibleSpace (PrimeSpectrum (A ⊗[k] B)) :=
  irreducibleSpace_primeSpectrum_of_injective
    (Algebra.TensorProduct.comm k A B).toRingHom (AlgEquiv.injective _) h

/-- A subalgebra of a geometrically irreducible `k`-algebra is geometrically irreducible. -/
theorem isGeometricallyIrreducible_of_injective {k A B : Type u} [Field k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [Algebra.IsGeometricallyIrreducible k B]
    (f : A →ₐ[k] B) (hf : Function.Injective f) : Algebra.IsGeometricallyIrreducible k A := by
  rw [Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  intro F _ _
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := F) f.toLinearMap hf
  have heq : ((Algebra.TensorProduct.map f (AlgHom.id k F)).toLinearMap :
      (A ⊗[k] F) →ₗ[k] (B ⊗[k] F)) = LinearMap.rTensor F f.toLinearMap := by
    ext x y; simp
  rw [← heq] at hinj
  exact irreducibleSpace_primeSpectrum_of_injective
    (Algebra.TensorProduct.map f (AlgHom.id k F)).toRingHom hinj
    ((Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct k B).mp
      ‹_› F)

/-- Let `L/k` be a finite separable field extension and let `k̄` be an algebraic closure of `k`.
If the spectrum of `L ⊗[k] k̄` is irreducible, then `[L : k] = 1`. -/
private theorem finrank_eq_one_of_irreducibleSpace (k L : Type u) [Field k] [Field L]
    [Algebra k L] [Algebra.IsSeparable k L] [FiniteDimensional k L]
    (h : IrreducibleSpace (PrimeSpectrum (L ⊗[k] AlgebraicClosure k))) :
    Module.finrank k L = 1 := by
  have : Algebra.FormallyEtale k L := .of_isSeparable k L
  have hred : IsReduced (AlgebraicClosure k ⊗[k] L) :=
    Algebra.FormallyUnramified.isReduced_of_field (AlgebraicClosure k) _
  have hirr : IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] L)) :=
    irreducibleSpace_primeSpectrum_tensorProduct_comm _ _ h
  have hbot : (⊥ : Ideal (AlgebraicClosure k ⊗[k] L)).IsPrime := by
    rw [← nilradical_eq_bot_iff.mpr hred]
    exact PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hirr
  have : IsDomain (AlgebraicClosure k ⊗[k] L) := .of_bot_isPrime _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := AlgebraicClosure k) (K := AlgebraicClosure k ⊗[k] L)
  rw [← Module.finrank_baseChange (R := AlgebraicClosure k) (S := k) (M' := L)]
  simpa using (AlgEquiv.ofBijective (Algebra.ofId (AlgebraicClosure k)
    (AlgebraicClosure k ⊗[k] L)) hb).toLinearEquiv.finrank_eq.symm

/-- A purely inseparable field extension `L/k` is geometrically irreducible. -/
@[sga "3 IX 5.4" "partial"]
private theorem isGeometricallyIrreducible_of_isPurelyInseparable (k L : Type u) [Field k]
    [Field L] [Algebra k L] [IsPurelyInseparable k L] :
    Algebra.IsGeometricallyIrreducible k L := by
  rw [Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  intro F _ _
  exact irreducibleSpace_primeSpectrum_tensorProduct_comm _ _
    ((Homeomorph.irreducibleSpace_iff
      ((PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k L F).homeomorph _)).mpr
      inferInstance)

/-- If the separable closure of `k` in `K` is trivial, then every algebraic subextension of `K/k`
is purely inseparable over `k`. -/
private theorem isPurelyInseparable_of_separableClosure_eq_bot {k K : Type u} [Field k] [Field K]
    [Algebra k K] (h : separableClosure k K = ⊥) (L : IntermediateField k K)
    [Algebra.IsAlgebraic k L] : IsPurelyInseparable k ↥L := by
  rw [isPurelyInseparable_iff]
  intro x
  refine ⟨Algebra.IsIntegral.isIntegral x, fun hx => ?_⟩
  have hmem : (x : K) ∈ (⊥ : IntermediateField k K) := by
    rw [← h]
    exact mem_separableClosure_iff.mpr (by rwa [IsSeparable, ← IntermediateField.minpoly_eq])
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hmem
  exact ⟨y, Subtype.ext hy⟩

/-- Let `K/k` be an extension of fields. The separable closure of `k` in `K` is trivial — every
element of `K` separably algebraic over `k` lies in `k` — if and only if `K` is geometrically
irreducible over `k`. -/
public theorem solution (k K : Type u) [Field k]
    [Field K] [Algebra k K] :
    separableClosure k K = ⊥ ↔ GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) := by
  constructor
  · intro h
    have := isPurelyInseparable_of_separableClosure_eq_bot h (algebraicClosure k K)
    have h1 : Algebra.IsGeometricallyIrreducible k ↥(algebraicClosure k K) :=
      isGeometricallyIrreducible_of_isPurelyInseparable k _
    have h2 : Algebra.IsGeometricallyIrreducible ↥(algebraicClosure k K) K :=
      Algebra.IsGeometricallyIrreducible.of_algebraicClosure_eq_bot _ K
        (algebraicClosure.algebraicClosure_eq_bot k K)
    exact Algebra.IsGeometricallyIrreducible.trans k ↥(algebraicClosure k K) K
  · intro h
    rw [eq_bot_iff, IsConcreteLE.le_iff]
    intro α hα
    have hsep : IsSeparable k α := mem_separableClosure_iff.mp hα
    have : FiniteDimensional k ↥k⟮α⟯ :=
      IntermediateField.adjoin.finiteDimensional hsep.isIntegral
    have : Algebra.IsSeparable k ↥k⟮α⟯ :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k K).mpr hsep
    have : Algebra.IsGeometricallyIrreducible k ↥k⟮α⟯ :=
      isGeometricallyIrreducible_of_injective (B := K) k⟮α⟯.val Subtype.val_injective
    rw [← IntermediateField.adjoin_simple_eq_bot_iff]
    refine IntermediateField.finrank_eq_one_iff.mp
      (finrank_eq_one_of_irreducibleSpace k _ ?_)
    exact (Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct
      k ↥k⟮α⟯).mp ‹_› (AlgebraicClosure k)

end Stacks.Irreducibility.TrivialSepClosure





open AlgebraicGeometry CommRingCat

/-- Let `K/k` be an extension of fields. The separable closure of `k` in `K` is trivial — every
element of `K` separably algebraic over `k` lies in `k` — if and only if `K` is geometrically
irreducible over `k`. -/
@[stacks 0G33]
public theorem separableClosure.eq_bot_iff_geometricallyIrreducible (k K : Type u) [Field k]
    [Field K] [Algebra k K] :
    separableClosure k K = ⊥ ↔ GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) :=
  Stacks.Irreducibility.TrivialSepClosure.solution k K

end
