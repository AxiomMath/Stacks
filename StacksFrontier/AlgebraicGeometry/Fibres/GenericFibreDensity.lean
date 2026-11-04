module

public import StacksFrontier.AlgebraicGeometry.Fibres.StandardOpenUnion
public import StacksFrontier.RingTheory.GeometricallyIntegral.FibrewiseDensity

/-!
# Scheme-theoretic density of a union of standard opens spreads from the generic fibre

Let `A` be a domain, `B` a finite type `A`-algebra and `g₁, …, gₙ ∈ B`. The union
`U = ⋃ⱼ D(gⱼ)` of standard opens of `Spec B` meets each fibre of `Spec B → Spec A` over a point
with residue field `L` in the union of the standard opens `D(1 ⊗ gⱼ)` of
`Spec (L ⊗[A] B)`. This file proves that if that union is scheme-theoretically dense in the fibre
over the generic point of `Spec A`, then it is scheme-theoretically dense in every fibre over some
nonempty standard open `D(h)` of `Spec A`: the affine case of Stacks 0573, for an open subscheme
presented as a finite union of standard opens.

The two ingredients are already in the tree and are only joined here. Stacks 056C,
`Stacks.Morphisms.schemeTheoreticallyDense_iff_localizationKernel_eq_bot`, says that such a union
is scheme-theoretically dense exactly when `R → ∏ⱼ R_{gⱼ}` is injective; Stacks 0565,
`bigLambda_injective_iff_bigPhi_injective`, replaces that by injectivity of the multiplication map
`R → ∏ⱼ R`, `r ↦ (g₁ r, …, gₙ r)`; and
`Algebra.exists_ne_zero_injective_bigPhi_tmul_of_algebraMap_ne_zero` spreads injectivity of the
multiplication map from the generic fibre to the fibres over a standard open, which is the
algebraic content of Stacks 0573.

## Main results

* `Stacks.Morphisms.localizationKernel_eq_bot_iff_injective_bigPhi`: the kernel of
  `R → ∏ⱼ R_{gⱼ}` vanishes exactly when the multiplication map of the family is injective
  (Stacks 0565, in the model of the localizations that Stacks 056C uses).
* `Stacks.Morphisms.isSchemeTheoreticallyDense_standardOpenUnion_iff_injective_bigPhi`: a finite
  union of standard opens of an affine scheme is scheme-theoretically dense exactly when the
  multiplication map of the family is injective.
* `Stacks.Morphisms.exists_ne_zero_isSchemeTheoreticallyDense_standardOpenUnion_tmul`: the affine
  case of Stacks 0573 for a union of standard opens.

## Implementation notes

`Stacks.Morphisms.localizationKernel` is built from `Localization.Away (gⱼ)` while `bigLambda` of
Stacks 0565 is built from `LocalizedModule.Away (gⱼ) R`; the two are different models of the same
localization, so the bridge is proved by comparing kernels elementwise rather than by transporting
along an isomorphism. In both models the kernel of the `j`-th component consists of the elements
annihilated by some power of `gⱼ`, which is `IsLocalization.map_eq_zero_iff` on one side and
`mem_ker_lambdaMap_iff` on the other.

The fibres are not expressed through `AlgebraicGeometry.Scheme.Hom.fiber` here: the statement is
about the rings `L ⊗[A] B` for the fields `L` over `A`, which is the form in which the ring-level
spreading statement is available and the form a consumer working with an affine morphism needs.
The point of `Spec A` is recorded by its residue field rather than by a prime, and the condition
that it lie in `D(h)` is that `h` stay nonzero in that field.

## References

* [Stacks Project, Tag 0573](https://stacks.math.columbia.edu/tag/0573)
* [Stacks Project, Tag 0565](https://stacks.math.columbia.edu/tag/0565)
* [Stacks Project, Tag 056C](https://stacks.math.columbia.edu/tag/056C)
* [Stacks Project, Tag 01RB](https://stacks.math.columbia.edu/tag/01RB)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.Morphisms

/-- **Stacks 0565 in the localization model of Stacks 056C.** For a finite family `f` in a ring
`R`, the kernel of `R → ∏ᵢ R_{fᵢ}` vanishes exactly when the multiplication map
`R → ∏ᵢ R`, `r ↦ (fᵢ r)ᵢ`, is injective.

Both conditions say that an element annihilated by a power of every `fᵢ` is zero: on the left
because the kernel of `R → R_{fᵢ}` consists of such elements
(`IsLocalization.map_eq_zero_iff`), on the right by Stacks 0565,
`bigLambda_injective_iff_bigPhi_injective`. -/
theorem localizationKernel_eq_bot_iff_injective_bigPhi {R : Type u} [CommRing R] (n : ℕ)
    (f : Fin n → R) :
    localizationKernel f = ⊥ ↔ Function.Injective (bigPhi (M := R) n f) := by
  rw [← bigLambda_injective_iff_bigPhi_injective, bigLambda_injective_iff_powerTorsion,
    localizationKernel, ← RingHom.injective_iff_ker_eq_bot, injective_iff_map_eq_zero]
  refine forall_congr' fun a =>
    ⟨fun ha hpow => ha (funext fun i => ?_), fun ha h0 => ha fun i => ?_⟩
  · obtain ⟨k, hk⟩ := hpow i
    rw [RingHom.pi_apply, (IsLocalization.map_eq_zero_iff (Submonoid.powers (f i))
      (Localization.Away (f i)) a).mpr ⟨⟨f i ^ k, k, rfl⟩, by simpa [smul_eq_mul] using hk⟩]
    rfl
  · obtain ⟨⟨m, k, hmk⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (f i))
        (Localization.Away (f i)) a).mp (by simpa [RingHom.pi_apply] using congrFun h0 i)
    exact ⟨k, by simpa [smul_eq_mul, ← hmk] using hm⟩

/-- **Scheme-theoretic density of a finite union of standard opens, as injectivity of a
multiplication map.** The union `⋃ᵢ D(fᵢ)` is scheme-theoretically dense in `Spec R` exactly when
the map `R → ∏ᵢ R`, `r ↦ (fᵢ r)ᵢ`, is injective.

This is Stacks 056C, `Stacks.Morphisms.schemeTheoreticallyDense_iff_localizationKernel_eq_bot`,
composed with Stacks 0565; it is the dictionary in which the proof of Stacks 0573 reads its
hypothesis and writes its conclusion. -/
theorem isSchemeTheoreticallyDense_standardOpenUnion_iff_injective_bigPhi {R : Type u}
    [CommRing R] (n : ℕ) (f : Fin n → R) :
    AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense (standardOpenUnion f) ↔
      Function.Injective (bigPhi (M := R) n f) :=
  (schemeTheoreticallyDense_iff_localizationKernel_eq_bot f).trans
    (localizationKernel_eq_bot_iff_injective_bigPhi n f)

/-- **Stacks 0573 for an affine morphism and a union of standard opens.** Let `A` be a domain,
`B` a finite type `A`-algebra, `g` a finite family in `B` and `K` a field over `A` with `A → K`
injective — the generic point of `Spec A`. If `⋃ⱼ D(1 ⊗ gⱼ)` is scheme-theoretically dense in
`Spec (K ⊗[A] B)`, then there is a nonzero `h : A` such that `⋃ⱼ D(1 ⊗ gⱼ)` is
scheme-theoretically dense in `Spec (L ⊗[A] B)` for every field `L` over `A` in which `h` stays
nonzero, i.e. over every point of the standard open `D(h)` of `Spec A`.

The density is converted to injectivity of the multiplication map on both sides by
`Stacks.Morphisms.isSchemeTheoreticallyDense_standardOpenUnion_iff_injective_bigPhi`, and the
spreading of that injectivity is
`Algebra.exists_ne_zero_injective_bigPhi_tmul_of_algebraMap_ne_zero`, whose proof is the generic
freeness argument of the source. -/
theorem exists_ne_zero_isSchemeTheoreticallyDense_standardOpenUnion_tmul
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    {n : ℕ} (g : Fin n → B) (K : Type u) [Field K] [Algebra A K]
    (hAK : Function.Injective (algebraMap A K))
    (hK : AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense
      (standardOpenUnion fun j => (1 : K) ⊗ₜ[A] g j)) :
    ∃ h : A, h ≠ 0 ∧ ∀ (L : Type u) [Field L] [Algebra A L], algebraMap A L h ≠ 0 →
      AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense
        (standardOpenUnion fun j => (1 : L) ⊗ₜ[A] g j) := by
  rw [isSchemeTheoreticallyDense_standardOpenUnion_iff_injective_bigPhi] at hK
  obtain ⟨h, hne, hmain⟩ :=
    Algebra.exists_ne_zero_injective_bigPhi_tmul_of_algebraMap_ne_zero g K hAK hK
  exact ⟨h, hne, fun L _ _ hL =>
    (isSchemeTheoreticallyDense_standardOpenUnion_iff_injective_bigPhi _ _).mpr (hmain L hL)⟩

end Stacks.Morphisms

end
