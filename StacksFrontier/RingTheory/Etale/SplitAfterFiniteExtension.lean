module

public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Unramified.Field

/-!
# An étale algebra over a field splits after a finite extension

Let `K` be a field and `E` an étale `K`-algebra with a `K`-basis `b`. If `F` is a field extension
of `K` over which the minimal polynomial of every `b i` splits, then every residue field of
`F ⊗_K E` is `F` itself, so `F ⊗_K E` is a finite product of copies of `F` and in particular is
spanned over `F` by its idempotents. A splitting field of the product of these minimal polynomials
is such an `F`, and it is finite over `K`.

## Main results

* `Algebra.Etale.surjective_algebraMap_quotient_maximal`: under the splitting hypothesis, the
  map from `F` to each residue field of `F ⊗_K E` at a maximal ideal is surjective.
* `Algebra.Etale.span_setOf_isIdempotentElem_tensorProduct_eq_top`: under the splitting
  hypothesis, the idempotents of `F ⊗_K E` span it over `F`.
* `Algebra.Etale.exists_finiteDimensional_span_setOf_isIdempotentElem_eq_top`: some finite field
  extension `L` of `K` has this property, and so does every field extension of `L`.

## Implementation notes

`F ⊗_K E` is étale over `F`, hence finite, reduced and Artinian, so it is the product of its
residue fields at its maximal ideals (`IsArtinianRing.equivPi`). Each residue field is spanned
over `F` by the images of the `1 ⊗ b i`, and each such image is a root of the minimal polynomial
of `b i`, which splits over `F`; so it lies in the image of `F`
(`Polynomial.Splits.mem_range_of_isRoot`). An element of `F ⊗_K E` is then the `F`-linear
combination of the primitive idempotents with coefficients its components.

## References

* [Stacks Project, Tag 00U3](https://stacks.math.columbia.edu/tag/00U3)
-/

@[expose] public section

open scoped TensorProduct
open Polynomial

namespace Algebra.Etale

universe u

variable {K : Type u} {F E : Type*} [Field K] [Field F] [Algebra K F] [CommRing E] [Algebra K E]

/-- **The residue fields of `F ⊗_K E` are `F`.** If the minimal polynomials over `K` of the
members of a `K`-basis of the étale `K`-algebra `E` split over `F`, then `F` maps onto the
quotient of `F ⊗_K E` by any maximal ideal. -/
theorem surjective_algebraMap_quotient_maximal [Algebra.Etale K E] {ι : Type*} [Finite ι]
    (b : Module.Basis ι K E) (hb : ∀ i, ((minpoly K (b i)).map (algebraMap K F)).Splits)
    (m : Ideal (F ⊗[K] E)) [m.IsMaximal] :
    Function.Surjective (algebraMap F (F ⊗[K] E ⧸ m)) := by
  classical
  let : Field (F ⊗[K] E ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite K E := Module.Finite.of_basis b
  have hgen : ∀ i, Ideal.Quotient.mk m (1 ⊗ₜ[K] b i) ∈ (algebraMap F (F ⊗[K] E ⧸ m)).range := by
    intro i
    refine (hb i).mem_range_of_isRoot
      (map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b i)))) ?_
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, IsRoot, eval_map_algebraMap]
    have h1 : aeval (Ideal.Quotient.mk m (1 ⊗ₜ[K] b i)) (minpoly K (b i)) =
        Ideal.Quotient.mkₐ K m (Algebra.TensorProduct.includeRight (aeval (b i)
          (minpoly K (b i)))) := by
      rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
      rfl
    rw [h1, minpoly.aeval, map_zero, map_zero]
  let V : Submodule F (F ⊗[K] E ⧸ m) := LinearMap.range (Algebra.linearMap F (F ⊗[K] E ⧸ m))
  have hle : Submodule.span F (Set.range fun i => Ideal.Quotient.mk m (1 ⊗ₜ[K] b i)) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := hgen i
    exact ⟨c, hc⟩
  have hspan : Submodule.span F (Set.range fun i => Ideal.Quotient.mk m (1 ⊗ₜ[K] b i)) = ⊤ := by
    refine (Submodule.eq_top_iff').2 fun z => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h := Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ F m).toLinearMap)
      ((Algebra.TensorProduct.basis F b).mem_span y)
    rw [Submodule.map_span, ← Set.range_comp] at h
    have hfun : ((Ideal.Quotient.mkₐ F m).toLinearMap ∘ (Algebra.TensorProduct.basis F b)) =
        fun i => Ideal.Quotient.mk m (1 ⊗ₜ[K] b i) := by
      funext i
      simp [Algebra.TensorProduct.basis_apply]
    rwa [hfun] at h
  intro z
  have hz : z ∈ V := hle (hspan ▸ Submodule.mem_top)
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, hc⟩

/-- **After the splitting extension, an étale algebra is spanned by its idempotents.** If the
minimal polynomials over `K` of the members of a `K`-basis of the étale `K`-algebra `E` split over
`F`, then `F ⊗_K E` is spanned over `F` by its idempotent elements. -/
theorem span_setOf_isIdempotentElem_tensorProduct_eq_top [Algebra.Etale K E] {ι : Type*}
    [Finite ι] (b : Module.Basis ι K E)
    (hb : ∀ i, ((minpoly K (b i)).map (algebraMap K F)).Splits) :
    Submodule.span F {x : F ⊗[K] E | IsIdempotentElem x} = ⊤ := by
  classical
  have : Module.Finite K E := Module.Finite.of_basis b
  have : IsArtinianRing (F ⊗[K] E) := isArtinian_of_tower F inferInstance
  have : IsReduced (F ⊗[K] E) := Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[K] E)
  have : Fintype (MaximalSpectrum (F ⊗[K] E)) := Fintype.ofFinite _
  let e := IsArtinianRing.equivPi (F ⊗[K] E)
  refine (Submodule.eq_top_iff').2 fun x => ?_
  choose c hc using fun m : MaximalSpectrum (F ⊗[K] E) =>
    surjective_algebraMap_quotient_maximal b hb m.asIdeal (e x m)
  have hx : x = ∑ m, c m • e.symm (Pi.single m 1) := by
    apply e.injective
    funext m'
    rw [map_sum, Finset.sum_apply]
    simp only [Algebra.smul_def, map_mul, Pi.mul_apply, AlgEquiv.apply_symm_apply]
    rw [Finset.sum_eq_single m']
    · rw [Pi.single_eq_same, mul_one, ← hc m']
      simp only [e, IsArtinianRing.equivPi_apply]
      rfl
    · intro m _ hm
      rw [Pi.single_eq_of_ne' hm, mul_zero]
    · simp
  rw [hx]
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have hidem : IsIdempotentElem (Pi.single m 1 : ∀ m', F ⊗[K] E ⧸ m'.asIdeal) := by
    show _ * _ = _
    rw [← Pi.single_mul, mul_one]
  exact hidem.map e.symm

/-- **Every étale algebra over a field splits over a finite extension.** For an étale algebra
`E` with a finite basis over the field `K`, there is a field `L` finite over `K` such that every
field extension `F` of `L` makes `F ⊗_K E` spanned over `F` by its idempotents. -/
theorem exists_finiteDimensional_span_setOf_isIdempotentElem_eq_top [Algebra.Etale K E]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧
      ∀ i, ((minpoly K (b i)).map (algebraMap K L)).Splits := by
  classical
  have : Module.Finite K E := Module.Finite.of_basis b
  let g : K[X] := ∏ i, minpoly K (b i)
  refine ⟨g.SplittingField, inferInstance, inferInstance, inferInstance, fun i => ?_⟩
  exact (SplittingField.splits g).of_dvd
    (map_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ =>
      minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b j))))
    (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

end Algebra.Etale

end
