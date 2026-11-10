module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleUnit
public import StacksFrontier.AlgebraicGeometry.Meromorphic.RegularSectionExistence

/-!
# The base case of the Hilbert polynomial of a coherent triple

Let `A` be a Noetherian local ring, let `f ∈ 𝔪` act regularly, let `(F, F₀, α)` be a coherent
triple for `(A, f)` and let `(L, L₀, λ)` be an invertible one. This file proves the base case of
the induction of [Stacks, Tag 0F27]: if `F = 0` then the Euler characteristics of the twists
`(F, F₀, α) ⊗ (L, L₀, λ)^{⊗ n}` do not depend on `n`, so the function `n ↦ χ` of that tag is
constant.

The source's reason is that for `F = 0` the twist is `(0, F₀ ⊗ L₀^{⊗ n}, 0)`, and that triple is
isomorphic to `(0, F₀, 0)` because `L₀` is invertible on the spectrum of a local ring and hence
trivial.

## Main definitions

* `Stacks.Algebraization.IsInvertibleTriple.tensorPowClosedFibreIsoUnit`: every tensor power of
  the closed-fibre member of an invertible coherent triple is the structure sheaf.
* `Stacks.Algebraization.CoherentTriple.homTwistZOfIsZero`: the isomorphism of coherent triples
  between a twist of a triple with vanishing punctured-spectrum member and the triple itself.

## Main results

* `Stacks.Algebraization.isZero_obj_of_isZero`: a functor preserving zero morphisms sends a zero
  object to a zero object.
* `Stacks.Algebraization.CoherentTriple.isZero_twistZ_F`: the punctured-spectrum member of every
  twist of a triple with vanishing punctured-spectrum member vanishes.
* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_twistZ_eq_of_isZero`: the Euler
  characteristics of the twists are all equal to that of the triple.
* `Stacks.Algebraization.exists_polynomial_eulerCharacteristic_twistZ_of_isZero`: the base case
  of [Stacks, Tag 0F27], as the existence of a constant polynomial.

## Implementation notes

Both components of the comparison morphism of triples are isomorphisms, so the Euler
characteristics agree by `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_of_hom`; no
prepared extension has to be built.

On the punctured spectrum both members are zero objects: tensoring on the right by an invertible
module is an equivalence, hence preserves zero morphisms, hence zero objects. On the closed fibre
the comparison is the trivialisation of the tensor power followed by the right unit constraint;
the trivialisation is
`AlgebraicGeometry.nonempty_iso_unit_of_isInvertible_spec_isLocalRing`, which needs the closed
fibre to be the spectrum of a *local* ring — that is where `f ∈ 𝔪` is used, through
`Stacks.Algebraization.isLocalRing_quotient_span`.

The compatibility square of the morphism of triples commutes because its target,
the inverse image of `F₀` on the punctured closed fibre, is a zero object: the gluing
isomorphism of the triple identifies it with the inverse image of `F`, which is zero because the
inverse image functor is additive.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

/-! ### Zero objects under a functor -/

/-- **A functor preserving zero morphisms sends a zero object to a zero object.** -/
public theorem isZero_obj_of_isZero {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] (G : C ⥤ D)
    [G.PreservesZeroMorphisms] {M : C} (hM : IsZero M) : IsZero (G.obj M) := by
  rw [IsZero.iff_id_eq_zero] at hM ⊢
  rw [← G.map_id, hM, G.map_zero]

/-- **The punctured-spectrum member of a twist of a coherent triple whose punctured-spectrum
member vanishes vanishes.** Tensoring on the right by an invertible module is an equivalence,
hence preserves zero objects. -/
public theorem CoherentTriple.isZero_twistZ_F {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) (hT : IsZero T.F) (n : ℤ) :
    IsZero ((T.twistZ L hL n).F) := by
  let := hL.invertible_F
  let := isInvertibleModule_tensorPowScheme
    (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n
  exact isZero_obj_of_isZero
    (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules
      (Stacks.Divisors.puncturedSpectrum A).toScheme
      (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)) hT

/-! ### The closed fibre is the spectrum of a local ring -/

/-- **The closed fibre of `(A, f)` at an `f` in the maximal ideal is the spectrum of a local
ring.** -/
public theorem isLocalRing_quotient_span {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (hf : f ∈ maximalIdeal A) : IsLocalRing (A ⧸ Ideal.span {f}) :=
  have hI : Ideal.span {f} ≠ (⊤ : Ideal A) := fun h =>
    (maximalIdeal.isMaximal A).ne_top
      (top_unique (h ▸ Ideal.span_le.mpr (by simpa using hf)))
  have : Nontrivial (A ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective

/-- **Every invertible module on the closed fibre is the structure sheaf**, the closed fibre
being the spectrum of a local ring. -/
public theorem nonempty_iso_unitModule_closedFibre {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (hf : f ∈ maximalIdeal A) (M : (closedFibre A f).Modules)
    [Stacks.Ample.IsInvertibleModule (closedFibre A f) M] :
    Nonempty (M ≅ Stacks.Ample.unitModule (closedFibre A f)) := by
  let := isLocalRing_quotient_span (A := A) (f := f) hf
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).presheaf
      (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).ringCatSheaf.2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).1 ‹_›
  exact AlgebraicGeometry.nonempty_iso_unit_of_isInvertible_spec_isLocalRing
    (A ⧸ Ideal.span {f}) M

/-- **The `n`-th tensor power of the closed-fibre member of an invertible coherent triple is the
structure sheaf of the closed fibre.** -/
public noncomputable def IsInvertibleTriple.tensorPowClosedFibreIsoUnit {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (hf : f ∈ maximalIdeal A) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :
    letI := hL.invertible_F₀
    tensorPowScheme (closedFibre A f) L.F₀ n ≅ Stacks.Ample.unitModule (closedFibre A f) :=
  letI := hL.invertible_F₀
  letI := isInvertibleModule_tensorPowScheme (closedFibre A f) L.F₀ n
  (nonempty_iso_unitModule_closedFibre hf
    (tensorPowScheme (closedFibre A f) L.F₀ n)).some

/-! ### The comparison of a twist with the triple -/

/-- **The closed-fibre member of a twist is the closed-fibre member of the triple**, the twisting
power being trivial on the closed fibre. -/
public noncomputable def CoherentTriple.twistZF₀Iso {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (hf : f ∈ maximalIdeal A) (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (n : ℤ) : (T.twistZ L hL n).F₀ ≅ T.F₀ :=
  letI := hL.invertible_F₀
  letI := isInvertibleModule_tensorPowScheme (closedFibre A f) L.F₀ n
  tensorModulesMapIso (closedFibre A f) (Iso.refl T.F₀)
      (IsInvertibleTriple.tensorPowClosedFibreIsoUnit hf hL n) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor (closedFibre A f).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (closedFibre A f)) T.F₀

/-- **A twist of a coherent triple whose punctured-spectrum member vanishes is isomorphic to the
triple itself.** On the punctured spectrum both members are zero objects; on the closed fibre the
comparison is `Stacks.Algebraization.CoherentTriple.twistZF₀Iso`. The compatibility square
commutes because its target is a zero object. -/
public noncomputable def CoherentTriple.homTwistZOfIsZero {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (hf : f ∈ maximalIdeal A) (T L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) (hT : IsZero T.F) (n : ℤ) :
    CoherentTriple.Hom (T.twistZ L hL n) T where
  onPunctured := ((T.isZero_twistZ_F L hL hT n).iso hT).hom
  onClosedFibre := (T.twistZF₀Iso hf L hL n).hom
  compatible := by
    have hzi : IsZero ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))).obj T.F) :=
      isZero_obj_of_isZero _ hT
    exact (IsZero.of_iso hzi T.alpha.symm).eq_of_tgt _ _

/-! ### The base case of Tag 0F27 -/

/-- **The base case of [Stacks, Tag 0F27].** If the punctured-spectrum member of a coherent
triple vanishes, then the Euler characteristics of its twists by the integer tensor powers of an
invertible coherent triple are all equal to the Euler characteristic of the triple itself. -/
public theorem CoherentTriple.eulerCharacteristic_twistZ_eq_of_isZero {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A)
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) (hT : IsZero T.F) (n : ℤ) :
    (T.twistZ L hL n).eulerCharacteristic = T.eulerCharacteristic :=
  have : IsIso (T.homTwistZOfIsZero hf L hL hT n).onPunctured :=
    inferInstanceAs (IsIso ((T.isZero_twistZ_F L hL hT n).iso hT).hom)
  have : IsIso (T.homTwistZOfIsZero hf L hL hT n).onClosedFibre :=
    inferInstanceAs (IsIso (T.twistZF₀Iso hf L hL n).hom)
  CoherentTriple.eulerCharacteristic_eq_of_hom hf (T.homTwistZOfIsZero hf L hL hT n)

/-- **The base case of [Stacks, Tag 0F27], as polynomiality.** If the punctured-spectrum member
of a coherent triple vanishes, then `n ↦ χ((F, F₀, α) ⊗ (L, L₀, λ)^{⊗ n})` is given at every
integer by a constant rational polynomial. -/
public theorem exists_polynomial_eulerCharacteristic_twistZ_of_isZero {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A)
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) (hT : IsZero T.F) :
    ∃ P : Polynomial ℚ, P.natDegree = 0 ∧
      ∀ n : ℤ, (((T.twistZ L hL n).eulerCharacteristic : ℤ) : ℚ) = P.eval (n : ℚ) :=
  ⟨Polynomial.C ((T.eulerCharacteristic : ℤ) : ℚ), Polynomial.natDegree_C _, fun n => by
    rw [T.eulerCharacteristic_twistZ_eq_of_isZero hf L hL hT n]
    simp⟩

end Stacks.Algebraization

end
