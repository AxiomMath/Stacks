module

public import StacksFrontier.RingTheory.Etale.IndEtaleTensorProduct
public import StacksFrontier.RingTheory.Henselian.Henselization.IndEtaleBase
import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite

/-!
# Henselization of a localized tensor product after an ind-étale extension

Let `k → B → A` be a tower of `k`-algebras with `A` ind-étale over `B` — for instance `A` a
henselization or a strict henselization of a local ring `B` — let `𝔭₀ ⊆ B ⊗[k] B` and
`𝔭 ⊆ A ⊗[k] A` be primes with `𝔭` lying over `𝔭₀`, and let `R₀` and `R` be the localizations of
`B ⊗[k] B` at `𝔭₀` and of `A ⊗[k] A` at `𝔭`. Then `R` is ind-étale over `R₀`, so a henselization
of `R₀` is a henselization of `R` as soon as the residue field extension `κ(R₀) ⊆ κ(R)` is
trivial.

## Main results

* `StacksDraft.indEtale_localizedTensorProduct`: `R` is ind-étale over `R₀`.
* `StacksDraft.isHenselization_localizedTensorProduct`: a henselization of `R₀` with residue
  field `L` is a henselization of `R` with residue field `L`.
* `StacksDraft.isLocalHom_algebraMap_localizedTensorProduct_left` and
  `..._right`: the two composites `A → A ⊗[k] A → R → C` given by the two tensor factors are
  local ring maps.
* `StacksDraft.isLocalHom_comp_algebraMap_atPrime`: a map into a localization at a prime is local
  when the prime contracts to the maximal ideal of the source.
* `StacksDraft.comap_nonZeroDivisors_eq_primeCompl`: inverting the elements with nonzero image
  under a map to a field is localizing at the kernel.

## Implementation notes

The two localizations are abstract (`IsLocalization.AtPrime`), and the compatibility of the
square `B ⊗[k] B → R₀ → R` with `B ⊗[k] B → A ⊗[k] A → R` is the hypothesis `hsq`; the
`B ⊗[k] B`-algebra structure on `R` is then built from it inside the proofs rather than assumed,
which keeps the instance list down to the structures a caller actually carries.

The ind-étaleness of `R` over `R₀` is cancellation (Lemma 08HS) applied to the two ind-étale maps
out of `B ⊗[k] B`: the localization `B ⊗[k] B → R₀`, and the composite
`B ⊗[k] B → A ⊗[k] A → R` of `StacksDraft.indEtale_tensorProduct_map` with the localization
`A ⊗[k] A → R`.

## References

* [StacksProject 08HS](https://stacks.math.columbia.edu/tag/08HS), cancellation
* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ), the henselization
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u v

namespace StacksDraft

/-- A ring map into a localization at a prime is a local ring map as soon as the prime contracts
to the maximal ideal of the source. -/
theorem isLocalHom_comp_algebraMap_atPrime {S T R : Type u} [CommRing S] [IsLocalRing S]
    [CommRing T] [CommRing R] [Algebra T R] [IsLocalRing R] (𝔮 : Ideal T) [𝔮.IsPrime]
    [IsLocalization.AtPrime R 𝔮] (f : S →+* T) (hf : 𝔮.comap f = maximalIdeal S) :
    IsLocalHom ((algebraMap T R).comp f) := by
  refine ((local_hom_TFAE ((algebraMap T R).comp f)).out 5 1).mp ?_
  rw [← Ideal.comap_comap,
    show Ideal.comap (algebraMap T R) (maximalIdeal R) = 𝔮 from
      IsLocalization.AtPrime.under_maximalIdeal R 𝔮, hf]

/-- For a ring map to a field with kernel a prime `𝔭`, the elements whose image is a nonzero
divisor are exactly those outside `𝔭`; so inverting them is localizing at `𝔭`. -/
theorem comap_nonZeroDivisors_eq_primeCompl {S K : Type u} [CommRing S] [Field K] (f : S →+* K)
    (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : RingHom.ker f = 𝔭) :
    Submonoid.comap f (nonZeroDivisors K) = 𝔭.primeCompl := by
  ext x
  simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, Ideal.primeCompl,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff, SetLike.mem_coe]
  rw [← h𝔭, RingHom.mem_ker]

section IndEtale

variable (k B A : Type u) [CommRing k] [CommRing B] [CommRing A]
  [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
  (𝔭₀ : Ideal (B ⊗[k] B)) [𝔭₀.IsPrime] (𝔭 : Ideal (A ⊗[k] A)) [𝔭.IsPrime]
  (R₀ R : Type u) [CommRing R₀] [CommRing R]
  [Algebra (B ⊗[k] B) R₀] [IsLocalization.AtPrime R₀ 𝔭₀]
  [Algebra (A ⊗[k] A) R] [IsLocalization.AtPrime R 𝔭]
  [Algebra (B ⊗[k] B) (A ⊗[k] A)] [Algebra R₀ R]

include 𝔭₀ 𝔭 in
/-- **The localized tensor square is ind-étale over the localized tensor square of the base.**
If `A` is a filtered colimit of étale `B`-algebras, then the localization `R` of `A ⊗[k] A` at a
prime is a filtered colimit of étale `R₀`-algebras, `R₀` being the localization of `B ⊗[k] B` at
the prime underneath it. -/
theorem indEtale_localizedTensorProduct
    (hmap : ∀ b b' : B, algebraMap (B ⊗[k] B) (A ⊗[k] A) (b ⊗ₜ b') =
      algebraMap B A b ⊗ₜ algebraMap B A b')
    (hsq : (algebraMap R₀ R).comp (algebraMap (B ⊗[k] B) R₀) =
      (algebraMap (A ⊗[k] A) R).comp (algebraMap (B ⊗[k] B) (A ⊗[k] A)))
    (h : IndEtale B A) :
    IndEtale R₀ R := by
  let : Algebra (B ⊗[k] B) R :=
    ((algebraMap (A ⊗[k] A) R).comp (algebraMap (B ⊗[k] B) (A ⊗[k] A))).toAlgebra
  have : IsScalarTower (B ⊗[k] B) (A ⊗[k] A) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (B ⊗[k] B) R₀ R :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hsq x).symm
  have hAA : IndEtale (B ⊗[k] B) (A ⊗[k] A) :=
    indEtale_tensorProduct_map k B A B A hmap h h
  exact indEtale_of_comp (indEtale_atPrime 𝔭₀) (indEtale_comp hAA (indEtale_atPrime 𝔭))

end IndEtale

section Henselization

variable (k B A : Type u) [CommRing k] [CommRing B] [CommRing A]
  [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
  (𝔭₀ : Ideal (B ⊗[k] B)) [𝔭₀.IsPrime] (𝔭 : Ideal (A ⊗[k] A)) [𝔭.IsPrime]
  (R₀ R C : Type u) [CommRing R₀] [IsLocalRing R₀] [CommRing R] [IsLocalRing R]
  [CommRing C] [IsLocalRing C]
  [Algebra (B ⊗[k] B) R₀] [IsLocalization.AtPrime R₀ 𝔭₀]
  [Algebra (A ⊗[k] A) R] [IsLocalization.AtPrime R 𝔭]
  [Algebra (B ⊗[k] B) (A ⊗[k] A)] [Algebra R₀ R] [IsLocalHom (algebraMap R₀ R)]
  [Algebra R₀ C] [Algebra R C] [IsScalarTower R₀ R C]
  (L : Type v) [Field L] [Algebra (ResidueField R₀) L] [Algebra (ResidueField R) L]

include 𝔭₀ 𝔭 in
/-- **A henselization of the localized tensor square of the base is one of the localized tensor
square.** Let `A` be a filtered colimit of étale `B`-algebras, let `R₀` and `R` be the
localizations of `B ⊗[k] B` and of `A ⊗[k] A` at compatible primes with `R₀ → R` local and
trivial residue field extension, and let `C` be a henselization of `R₀` with residue field `L`.
Then `C` is a henselization of `R` with residue field `L`. -/
theorem isHenselization_localizedTensorProduct
    [IsScalarTower (ResidueField R₀) (ResidueField R) L] [IsHenselization R₀ L C]
    (hmap : ∀ b b' : B, algebraMap (B ⊗[k] B) (A ⊗[k] A) (b ⊗ₜ b') =
      algebraMap B A b ⊗ₜ algebraMap B A b')
    (hsq : (algebraMap R₀ R).comp (algebraMap (B ⊗[k] B) R₀) =
      (algebraMap (A ⊗[k] A) R).comp (algebraMap (B ⊗[k] B) (A ⊗[k] A)))
    (h : IndEtale B A)
    (hres : Function.Surjective (algebraMap (ResidueField R₀) (ResidueField R))) :
    IsHenselization R L C :=
  IsHenselization.of_indEtale_tower (L := L)
    (indEtale_iff.mp (indEtale_localizedTensorProduct k B A 𝔭₀ 𝔭 R₀ R hmap hsq h)) hres

/-- A ring map into a henselization `C` of the localization `R` of `A ⊗[k] A` at `𝔭` is local if
its source map to `A ⊗[k] A` pulls `𝔭` back to the maximal ideal. -/
private theorem isLocalHom_comp_henselization [IsLocalRing A] [IsHenselization R L C]
    (f : A →+* A ⊗[k] A) (hf : 𝔭.comap f = maximalIdeal A) :
    IsLocalHom ((algebraMap R C).comp ((algebraMap (A ⊗[k] A) R).comp f)) :=
  have : IsLocalHom (algebraMap R C) := IsHenselization.isLocalHom (L := L)
  have : IsLocalHom ((algebraMap (A ⊗[k] A) R).comp f) :=
    isLocalHom_comp_algebraMap_atPrime 𝔭 f hf
  RingHom.isLocalHom_comp _ _

include 𝔭₀ 𝔭 in
/-- **The left projection into a henselization of the localized tensor square is local.** If `𝔭`
contracts to the maximal ideal of `A` along the left tensor factor, then the composite
`A → A ⊗[k] A → R → C` is a local ring map. -/
theorem isLocalHom_algebraMap_localizedTensorProduct_left [IsLocalRing A]
    [IsScalarTower (ResidueField R₀) (ResidueField R) L] [IsHenselization R₀ L C]
    (hmap : ∀ b b' : B, algebraMap (B ⊗[k] B) (A ⊗[k] A) (b ⊗ₜ b') =
      algebraMap B A b ⊗ₜ algebraMap B A b')
    (hsq : (algebraMap R₀ R).comp (algebraMap (B ⊗[k] B) R₀) =
      (algebraMap (A ⊗[k] A) R).comp (algebraMap (B ⊗[k] B) (A ⊗[k] A)))
    (h : IndEtale B A)
    (hres : Function.Surjective (algebraMap (ResidueField R₀) (ResidueField R)))
    (hp : 𝔭.comap (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A).toRingHom =
      maximalIdeal A) :
    IsLocalHom ((algebraMap R C).comp ((algebraMap (A ⊗[k] A) R).comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A).toRingHom)) :=
  have := isHenselization_localizedTensorProduct k B A 𝔭₀ 𝔭 R₀ R C L hmap hsq h hres
  isLocalHom_comp_henselization k A 𝔭 R C L _ hp

include 𝔭₀ 𝔭 in
/-- **The right projection into a henselization of the localized tensor square is local.** If `𝔭`
contracts to the maximal ideal of `A` along the right tensor factor, then the composite
`A → A ⊗[k] A → R → C` is a local ring map. -/
theorem isLocalHom_algebraMap_localizedTensorProduct_right [IsLocalRing A]
    [IsScalarTower (ResidueField R₀) (ResidueField R) L] [IsHenselization R₀ L C]
    (hmap : ∀ b b' : B, algebraMap (B ⊗[k] B) (A ⊗[k] A) (b ⊗ₜ b') =
      algebraMap B A b ⊗ₜ algebraMap B A b')
    (hsq : (algebraMap R₀ R).comp (algebraMap (B ⊗[k] B) R₀) =
      (algebraMap (A ⊗[k] A) R).comp (algebraMap (B ⊗[k] B) (A ⊗[k] A)))
    (h : IndEtale B A)
    (hres : Function.Surjective (algebraMap (ResidueField R₀) (ResidueField R)))
    (hp : 𝔭.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A).toRingHom =
      maximalIdeal A) :
    IsLocalHom ((algebraMap R C).comp ((algebraMap (A ⊗[k] A) R).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A).toRingHom)) :=
  have := isHenselization_localizedTensorProduct k B A 𝔭₀ 𝔭 R₀ R C L hmap hsq h hres
  isLocalHom_comp_henselization k A 𝔭 R C L _ hp

end Henselization

end StacksDraft

end
