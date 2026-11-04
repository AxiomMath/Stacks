module

public import StacksFrontier.RingTheory.Henselian.IntegralDomain

/-!
# Inverting a unit integral over a henselian local ring

Let `R` be a henselian local ring and let `C` be a local ring which is a domain, with `R → C` a
local homomorphism. If `t : C` is a unit and is integral over `R`, then `t⁻¹` is again integral
over `R`.

The hypotheses are all used. For `R = ℤ_p`, `C = ℚ_p` and `t = p` the element `t` is a unit of `C`
integral over `R` whose inverse is not integral over `R`; what fails there is that `R → C` is not
local.

## Main results

* `HenselianLocalRing.isIntegral_val_inv`: the inverse of a unit of `C` whose value is integral
  over `R` is integral over `R`.
* `HenselianLocalRing.isLocalHom_of_isIntegral`: an `R`-algebra map from a local ring integral
  over `R` into `C` is a local homomorphism. This needs no henselianness and is the step which
  consumes locality of `R → C`.

## Implementation notes

The argument is the standard one for Stacks 04GG(10) — a finite algebra over a henselian local
ring splits as a product of local rings, and `t` becomes a unit in the factor through which the
map to the local ring `C` factors — but routed so that the splitting is never formed. Instead the
single factor that matters is produced directly as `E := R[t] ⊆ C`: it is module-finite over `R`
because `t` is integral, and it is a domain because `C` is, so
`RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain` (**Stacks 092X**) makes it local
without any product decomposition. The locality of `E → C` then transfers the unit `t` of `C` back
to a unit of `E`, whose inverse lies in `E` and is therefore integral over `R`.

Locality of `E → C` is where the hypothesis on `R → C` enters: the contraction of the maximal
ideal of `C` to `E` is a prime whose further contraction to `R` is the maximal ideal of `R`, so it
is maximal by going-up along the integral extension `R → E`, hence is the maximal ideal of the
local ring `E`.

## References

* [The Stacks Project, Tag 092X](https://stacks.math.columbia.edu/tag/092X)
* [The Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace HenselianLocalRing

variable {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]

/-- An `R`-algebra map from a local ring `E` integral over the local ring `R` into a local ring
`C` is local, provided `R → C` is local.

The contraction `𝔭` of the maximal ideal of `C` along the map is a prime of `E`, and its
contraction to `R` is the contraction of the maximal ideal of `C` to `R`, which is the maximal
ideal of `R` because `R → C` is local. Going up along the integral extension `R → E`
(`Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`) makes `𝔭` maximal, so `𝔭` is *the* maximal
ideal of `E`. -/
theorem isLocalHom_of_isIntegral [IsLocalRing R] [IsLocalRing C]
    [IsLocalHom (algebraMap R C)] {E : Type*} [CommRing E] [IsLocalRing E] [Algebra R E]
    [Algebra.IsIntegral R E] (g : E →ₐ[R] C) : IsLocalHom (g : E →+* C) := by
  have hcomap : (maximalIdeal C).comap (g : E →+* C) =
      maximalIdeal E := by
    have hprime : ((maximalIdeal C).comap (g : E →+* C)).IsPrime :=
      Ideal.comap_isPrime _ _
    have hR : (((maximalIdeal C).comap (g : E →+* C)).comap (algebraMap R E)).IsMaximal := by
      have hcomp : ((maximalIdeal C).comap (g : E →+* C)).comap (algebraMap R E) =
          (maximalIdeal C).comap (algebraMap R C) := by
        rw [Ideal.comap_comap]
        congr 1
        ext r
        simpa using (g.commutes r).symm
      rw [hcomp, maximalIdeal_comap (algebraMap R C)]
      exact maximalIdeal.isMaximal R
    exact eq_maximalIdeal
      (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
        ((maximalIdeal C).comap (g : E →+* C)) hR)
  exact ((local_hom_TFAE (g : E →+* C)).out 5 1 rfl rfl).mp hcomap

/-- **The inverse of a unit integral over a henselian local ring is integral.** Let `R` be a
henselian local ring and let `C` be a local ring which is a domain, with `R → C` local. If the
value of a unit `t : Cˣ` is integral over `R`, then so is the value of `t⁻¹`.

The subalgebra `E := R[t] ⊆ C` is module-finite over `R` because `t` is integral over `R`, and is
a domain because `C` is one; so it is local by **Stacks 092X**. Since `E → C` is local
(`isLocalHom_of_isIntegral`) and `t` is a unit of `C` lying in `E`, it is already a unit of `E`,
and the inverse it has there is integral over `R` because `E` is finite over `R`. -/
theorem isIntegral_val_inv [HenselianLocalRing R] [IsLocalRing C] [IsDomain C]
    [IsLocalHom (algebraMap R C)] (t : Cˣ) (ht : IsIntegral R (t : C)) :
    IsIntegral R ((t⁻¹ : Cˣ) : C) := by
  -- `E = R[t]`, module-finite over `R` and a domain, hence local by Stacks 092X.
  set E : Subalgebra R C := Algebra.adjoin R {(t : C)} with hE
  have : Module.Finite R E := Algebra.finite_adjoin_simple_of_isIntegral ht
  obtain ⟨hEhens, -, -⟩ :=
    (algebraMap R E).exists_henselianLocalRing_of_isIntegral_of_isDomain
      (fun x => IsIntegral.of_finite R x)
  have hEloc : IsLocalRing E := hEhens.toIsLocalRing
  -- `E → C` is local, so the unit `t` of `C` is already a unit of `E`.
  have hlocal : IsLocalHom (E.val : E →+* C) :=
    isLocalHom_of_isIntegral (E := E) E.val
  have htE : (t : C) ∈ E := Algebra.self_mem_adjoin_singleton R _
  have hunit : IsUnit (⟨(t : C), htE⟩ : E) :=
    isUnit_of_map_unit (E.val : E →+* C) _ (by simpa using t.isUnit)
  obtain ⟨u, hu⟩ := hunit
  -- its inverse in `E` is integral over `R` and maps to `t⁻¹`.
  have hvinv : (E.val ((u⁻¹ : Eˣ) : E)) * (t : C) = 1 := by
    have : ((u⁻¹ : Eˣ) : E) * (⟨(t : C), htE⟩ : E) = 1 := by
      rw [← hu]; exact u.inv_val
    simpa using congrArg (E.val : E →+* C) this
  have heq : ((t⁻¹ : Cˣ) : C) = E.val ((u⁻¹ : Eˣ) : E) := by
    rw [← one_mul ((t⁻¹ : Cˣ) : C), ← hvinv, mul_assoc, t.mul_inv, mul_one]
  rw [heq]
  exact (IsIntegral.of_finite R ((u⁻¹ : Eˣ) : E)).map E.val

end HenselianLocalRing

end
