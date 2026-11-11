module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SpecProduct
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowUnramifiedAtPoint
public import StacksFrontier.GroupTheory.OrderOf.ReductionPrimeToPart

/-!
# Reduction of torsion points of a commutative group scheme

Let `𝒜` be a commutative group scheme over `Spec R`, separated and of finite type. For an
`R`-algebra `S` write `𝒜(S)` for the group of morphisms `Spec S ⟶ 𝒜` over `Spec R`.

Let `O` be a local domain over `R`, whose maximal ideal lies over a maximal ideal `𝔪` of `R`,
together with an injective `R`-algebra map `gk : O → k` into a field. This file proves:

* restriction along `gk` is an injective homomorphism `𝒜(O) → 𝒜(k)`, since `Spec k ⟶ Spec O` is
  dominant, `Spec O` is reduced and `𝒜` is separated;
* an element of `𝒜(O)` killed by a prime `q` invertible in `R/𝔪` and trivial on the closed point
  is trivial, since multiplication by `q` is unramified at points of residue characteristic
  different from `q` (`AlgebraicGeometry.unramifiedAt_zpow_id_left_of_isUnit`) and two sections
  of a local scheme over a morphism unramified at the image of the closed point agree
  (`AlgebraicGeometry.eq_of_comp_eq_of_unramifiedAt`);
* hence, if the residue field of `O` embeds over `R` into a finite field `F`, the part prime to
  the residue characteristic of the order of a torsion point of `𝒜(k)` coming from `𝒜(O)` is at
  most `#𝒜(F)`.

## Notation

`AlgebraicGeometry.specOver R S` is `Spec S` as a scheme over `Spec R`, and
`AlgebraicGeometry.specOverMap φ` the morphism over `Spec R` of an `R`-algebra map, both from
`StacksFrontier.AlgebraicGeometry.Descent.Algebra.SpecProduct`.

## Main results

* `AlgebraicGeometry.specOverMap_comp_injective`: restriction to the generic point is injective.
* `AlgebraicGeometry.eq_one_of_pow_prime_eq_one`: the kernel of reduction has no `q`-torsion.
* `AlgebraicGeometry.ordCompl_addOrderOf_le_natCard`: the bound on the prime-to-`ℓ` part of the
  order.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-- **Restriction to a dominant point is injective**: if `O` is a domain and `gk : O → k` an
injective `R`-algebra map to a field, two morphisms `Spec O ⟶ 𝒜` over `Spec R` into a separated
scheme over `Spec R` that agree on `Spec k` are equal. -/
theorem specOverMap_comp_injective {O k : Type u} [CommRing O] [IsDomain O] [Algebra R O]
    [Field k] [Algebra R k] (𝒜 : Over (Spec (.of R))) [IsSeparated 𝒜.hom] (gk : O →ₐ[R] k)
    (hgk : Function.Injective gk) :
    Function.Injective (fun a : specOver R O ⟶ 𝒜 => specOverMap gk ≫ a) := by
  intro a b h
  have hdom : IsDominant (Spec.map (CommRingCat.ofHom gk.toRingHom)) := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    have hp : (Spec.map (CommRingCat.ofHom gk.toRingHom)) (IsLocalRing.closedPoint k) =
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := by
      apply PrimeSpectrum.ext
      change Ideal.comap gk.toRingHom (IsLocalRing.maximalIdeal k) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ hgk
    refine Set.eq_univ_of_subset (closure_mono (Set.singleton_subset_iff.mpr ⟨_, hp⟩)) ?_
    change closure ({(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)} : Set (PrimeSpectrum O)) =
      Set.univ
    rw [PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  have : IsReduced (specOver R O).left := inferInstanceAs (IsReduced (Spec (.of O)))
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated 𝒜.hom ((Over.w a).trans (Over.w b).symm)
    (Spec.map (CommRingCat.ofHom gk.toRingHom)) (congrArg CommaMorphism.left h)

end AlgebraicGeometry

end
