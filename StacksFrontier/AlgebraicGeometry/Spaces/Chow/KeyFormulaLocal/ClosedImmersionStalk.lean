module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence

/-!
# The kernel of the stalk map of a closed immersion of schemes

Let `π : T ⟶ U` be a closed immersion of schemes and `y ∈ T`. The stalk map
`𝒪_{U, π y} → 𝒪_{T, y}` is surjective, and its kernel `I` cuts out, among the primes of
`A = 𝒪_{U, π y}`, exactly those whose point of `U` lies in the image of `π`. When `T` is reduced
`I` is radical, hence the intersection of those primes. This is the local form of the statement
that a reduced closed subscheme is cut out by the ideal of functions vanishing on its points, and
it is what identifies the local ring of a reduced closed subscheme with `A ⧸ I`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ker_stalkMap_le_iff_of_isClosedImmersion`: a prime of `A`
  contains `I` if and only if its point lies in the image of `π`.
* `AlgebraicGeometry.Scheme.Hom.isRadical_ker_stalkMap_of_isClosedImmersion` and
  `AlgebraicGeometry.Scheme.Hom.ker_stalkMap_eq_sInf_of_isClosedImmersion`: for reduced `T`,
  `I` is radical and is the intersection of the primes of `A` whose points lie in the image.
* `AlgebraicGeometry.Scheme.Hom.mem_minimalPrimes_iff_comap_mem_minimalPrimes_ker_stalkMap`:
  the minimal primes of `𝒪_{T, y}` are the minimal primes of `I` pulled back.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {T U : Scheme.{u}} (π : T ⟶ U) (y : T)

/-- The point of `U` of the pullback of a prime of `𝒪_{T, y}` along the stalk map of `π` is the
image under `π` of the point of `T` of that prime. -/
theorem fromSpecStalk_comap_stalkMap (q : PrimeSpectrum (T.presheaf.stalk y)) :
    U.fromSpecStalk (π y) (PrimeSpectrum.comap (π.stalkMap y).hom q) = π (T.fromSpecStalk y q) :=
  congrArg (fun g : Spec (T.presheaf.stalk y) ⟶ U => g q)
    (Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y))

variable [IsClosedImmersion π]

/-- **The primes containing the kernel of the stalk map of a closed immersion.** A prime of
`𝒪_{U, π y}` contains the kernel of the (surjective) stalk map at `y` if and only if its point
of `U` lies in the image of `π`. -/
theorem ker_stalkMap_le_iff_of_isClosedImmersion (p : PrimeSpectrum (U.presheaf.stalk (π y))) :
    RingHom.ker (π.stalkMap y).hom ≤ p.asIdeal ↔ U.fromSpecStalk (π y) p ∈ Set.range π := by
  have hrange := _root_.range_comap_of_surjective _ (π.stalkMap y).hom (π.stalkMap_surjective y)
  have hmem : p ∈ PrimeSpectrum.zeroLocus (RingHom.ker (π.stalkMap y).hom : Set _) ↔
      RingHom.ker (π.stalkMap y).hom ≤ p.asIdeal := PrimeSpectrum.mem_zeroLocus _ _
  rw [← hmem, ← hrange]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, (fromSpecStalk_comap_stalkMap π y q).symm⟩
  · rintro ⟨t, ht⟩
    have hty : t ⤳ y := by
      rw [← π.isClosedEmbedding.isInducing.specializes_iff, ht]
      exact Stacks.Chow.specializes_fromSpecStalk (π y) p
    obtain ⟨q, rfl⟩ := Stacks.Chow.exists_fromSpecStalk_eq hty
    exact ⟨q, (U.fromSpecStalk (π y)).isEmbedding.injective
      ((fromSpecStalk_comap_stalkMap π y q).trans ht)⟩

/-- For a closed immersion from a reduced scheme, the kernel of the stalk map is radical: the
quotient by it is the stalk of the reduced scheme. -/
theorem isRadical_ker_stalkMap_of_isClosedImmersion [IsReduced T] :
    (RingHom.ker (π.stalkMap y).hom).IsRadical :=
  (RingHom.ker_isRadical_iff_reduced_of_surjective (π.stalkMap_surjective y)).mpr inferInstance

/-- **The kernel of the stalk map of a closed immersion from a reduced scheme is the
intersection of the primes whose points lie in the image.** -/
theorem ker_stalkMap_eq_sInf_of_isClosedImmersion [IsReduced T] :
    RingHom.ker (π.stalkMap y).hom = sInf {P : Ideal (U.presheaf.stalk (π y)) |
      ∃ hP : P.IsPrime, U.fromSpecStalk (π y) ⟨P, hP⟩ ∈ Set.range π} := by
  rw [← (isRadical_ker_stalkMap_of_isClosedImmersion π y).radical, Ideal.radical_eq_sInf]
  congr 1
  ext P
  exact ⟨fun ⟨hle, hP⟩ ↦ ⟨hP, (ker_stalkMap_le_iff_of_isClosedImmersion π y ⟨P, hP⟩).mp hle⟩,
    fun ⟨hP, hmem⟩ ↦ ⟨(ker_stalkMap_le_iff_of_isClosedImmersion π y ⟨P, hP⟩).mpr hmem, hP⟩⟩

/-- **The minimal primes of the local ring of a closed subscheme.** A prime of `𝒪_{T, y}` is
minimal exactly when its pullback along the (surjective) stalk map is a minimal prime of the
kernel. -/
theorem mem_minimalPrimes_iff_comap_mem_minimalPrimes_ker_stalkMap
    (p : Ideal (T.presheaf.stalk y)) :
    p ∈ minimalPrimes (T.presheaf.stalk y) ↔
      p.comap (π.stalkMap y).hom ∈ (RingHom.ker (π.stalkMap y).hom).minimalPrimes := by
  have hsurj := π.stalkMap_surjective y
  have key := Ideal.comap_minimalPrimes_eq_of_surjective hsurj (⊥ : Ideal (T.presheaf.stalk y))
  rw [← RingHom.ker_eq_comap_bot] at key
  rw [key]
  exact ⟨fun hp ↦ ⟨p, hp, rfl⟩, fun ⟨q, hq, hqp⟩ ↦ by
    rwa [← Ideal.comap_injective_of_surjective _ hsurj hqp]⟩

end AlgebraicGeometry.Scheme.Hom

end
