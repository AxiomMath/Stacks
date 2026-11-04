module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicAlgebraization.NeighbourhoodTruncations

/-!
# Maps between truncations of quotients of a complete local ring

Let `(R, 𝔪)` be the complete local ring of a formal base `A` over `S`, and `L ⊆ R` an ideal. This
file constructs, as morphisms of the big fppf site over `S`, the closed immersion
`Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺¹)` and, for `L' ≤ L`, the map
`Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec((R/L')/𝔪ⁿ⁺¹)`, and proves that they commute with the transition maps
and with the closed immersions into `Spec R` and `Spec(R/L)`. It also computes the ring map on
global sections of a closed immersion `Spec(A/K) ⟶ Spec A` and shows that it is surjective.

## Main definitions

* `AlgebraicGeometry.FormalSpace.quotientTruncationToTruncation`: the closed immersion
  `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺¹)`.
* `AlgebraicGeometry.FormalSpace.quotientTruncationMap`: the map
  `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec((R/L')/𝔪ⁿ⁺¹)` for `L' ≤ L`.

## Main results

* `AlgebraicGeometry.FormalSpace.quotientTruncationToTruncation_comp`: the square through
  `Spec(R/𝔪ⁿ⁺¹) ⟶ Spec R` and `Spec(R/L) ⟶ Spec R` commutes.
* `AlgebraicGeometry.FormalSpace.quotientTruncationMap_comp_toTruncation`: the maps
  `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec((R/L')/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺¹)` compose to the closed immersion.
* `AlgebraicGeometry.FormalSpace.surjective_chartRing_quotientToAffineOver`: the ring map on
  global sections of `Spec(A/K) ⟶ Spec A` is surjective.

## References

* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.FormalSpace

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Maps

variable (hS) (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n)) (L : Ideal A.R)

/-- The ring map `R/𝔪ⁿ⁺¹ ⟶ (R/L)/𝔪ⁿ⁺¹`. -/
abbrev quotientTruncationRingHom (n : ℕ) :
    A.R ⧸ maximalIdeal A.R ^ (n + 1) →+* (A.R ⧸ L) ⧸ quotientBaseStage A L n :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (Ideal.Quotient.mk L)) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)

/-- Two squares of `Spec` of ring maps commute when the corresponding ring map squares do. -/
private theorem spec_map_comp_eq_of_comp_eq {R₁ R₂ R₃ R₄ : Type u} [CommRing R₁] [CommRing R₂]
    [CommRing R₃] [CommRing R₄] (f : R₁ →+* R₂) (g : R₂ →+* R₄) (f' : R₁ →+* R₃) (g' : R₃ →+* R₄)
    (h : g.comp f = g'.comp f') :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom f') := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h]

/-- The square of closed immersions `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺¹) ⟶ Spec R` and
`Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/L) ⟶ Spec R` commutes, as a square of schemes. -/
theorem spec_quotientTruncationRingHom_comp (n : ℕ) :
    Spec.map (CommRingCat.ofHom (quotientTruncationRingHom A L n)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A.R ^ (n + 1)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (quotientBaseStage A L n))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L)) := by
  exact spec_map_comp_eq_of_comp_eq _ _ _ _ rfl

/-- The closed immersion `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺¹)`. -/
def quotientTruncationToTruncation (n : ℕ) :
    quotientTruncation hS A hA L n ⟶ truncationOver B S hS A hA n :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (quotientTruncationRingHom A L n))))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (quotientTruncationRingHom A L n)) ≫
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A.R ^ (n + 1)))) ≫ A.toS) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (quotientBaseStage A L n))) ≫
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L)) ≫ A.toS)
      rw [← Category.assoc, spec_quotientTruncationRingHom_comp, Category.assoc])

/-- The square of closed immersions `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺¹) ⟶ Spec R` and
`Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/L) ⟶ Spec R` commutes in the site. -/
theorem quotientTruncationToTruncation_comp (n : ℕ) :
    quotientTruncationToTruncation hS A hA L n ≫ truncationToChart hS A hA n =
      quotientTruncationι hS A hA L n ≫ quotientBaseToChart hS A hA L :=
  (BigFppfOver.toScheme B S hS).map_injective (spec_quotientTruncationRingHom_comp A L n)

/-- The closed immersions `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺¹)` commute with the transition maps
between successive truncations. -/
theorem quotientTruncationSucc_comp_toTruncation (n : ℕ) :
    quotientTruncationSucc hS A hA L n ≫ quotientTruncationToTruncation hS A hA L (n + 1) =
      quotientTruncationToTruncation hS A hA L n ≫ truncationOverSucc B S hS A hA n := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  exact spec_map_comp_eq_of_comp_eq _ _ _ _ (by ext; rfl)

/-- The ring map `(R/L')/𝔪ⁿ⁺¹ ⟶ (R/L)/𝔪ⁿ⁺¹` for `L' ≤ L`. -/
abbrev quotientTruncationMapRingHom {L L' : Ideal A.R} (h : L' ≤ L) (n : ℕ) :
    (A.R ⧸ L') ⧸ quotientBaseStage A L' n →+* (A.R ⧸ L) ⧸ quotientBaseStage A L n :=
  Ideal.quotientMap (quotientBaseStage A L n) (Ideal.Quotient.factor h) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, Ideal.Quotient.factor_comp_mk])

/-- For `L' ≤ L`, the square `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec((R/L')/𝔪ⁿ⁺¹) ⟶ Spec(R/L')` and
`Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/L) ⟶ Spec(R/L')` commutes, as a square of schemes. -/
theorem spec_quotientTruncationMapRingHom_comp {L L' : Ideal A.R} (h : L' ≤ L) (n : ℕ) :
    Spec.map (CommRingCat.ofHom (quotientTruncationMapRingHom A h n)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (quotientBaseStage A L' n))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (quotientBaseStage A L n))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) := by
  exact spec_map_comp_eq_of_comp_eq _ _ _ _ rfl

/-- The map `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec((R/L')/𝔪ⁿ⁺¹)` for `L' ≤ L`. -/
def quotientTruncationMap {L L' : Ideal A.R} (h : L' ≤ L) (n : ℕ) :
    quotientTruncation hS A hA L n ⟶ quotientTruncation hS A hA L' n :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
    (quotientTruncationMapRingHom A h n))))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (quotientTruncationMapRingHom A h n)) ≫
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (quotientBaseStage A L' n))) ≫
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L')) ≫ A.toS)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (quotientBaseStage A L n))) ≫
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L)) ≫ A.toS)
      rw [← Category.assoc, spec_quotientTruncationMapRingHom_comp, Category.assoc,
        ← Category.assoc (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))),
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk])

/-- For `L' ≤ L`, the square `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec((R/L')/𝔪ⁿ⁺¹) ⟶ Spec(R/L')` and
`Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/L) ⟶ Spec(R/L')` commutes in the site. -/
theorem quotientTruncationMap_comp_ι {L L' : Ideal A.R} (h : L' ≤ L) (n : ℕ) :
    quotientTruncationMap hS A hA h n ≫ quotientTruncationι hS A hA L' n =
      quotientTruncationι hS A hA L n ≫
        (BigAffineFppf.inclusion B S hS).map (quotientOverTransition B S hS A.toS
          (A.contains_spec_of_contains_truncation hA) h) :=
  (BigFppfOver.toScheme B S hS).map_injective (spec_quotientTruncationMapRingHom_comp A h n)

/-- For `L' ≤ L`, the composite `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec((R/L')/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺¹)` is the
closed immersion `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺¹)`. -/
theorem quotientTruncationMap_comp_toTruncation {L L' : Ideal A.R} (h : L' ≤ L) (n : ℕ) :
    quotientTruncationMap hS A hA h n ≫ quotientTruncationToTruncation hS A hA L' n =
      quotientTruncationToTruncation hS A hA L n := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a
  rfl

end Maps

section ChartRing

variable {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))} {f : Spec (.of A) ⟶ S}

/-- The ring map on global sections of the closed immersion `Spec(A/K) ⟶ Spec A` sends `a` to
the global section corresponding to its class in `A/K`. -/
theorem chartRing_quotientToAffineOver (K : Ideal A) (a : A) :
    chartRing (Space.quotientToAffineOver B S hS f hA K) a =
      (Scheme.ΓSpecIso (.of (A ⧸ K))).inv (Ideal.Quotient.mk K a) := by
  show ((Scheme.ΓSpecIso (.of A)).inv ≫
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop).hom a = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The ring map on global sections of the closed immersion `Spec(A/K) ⟶ Spec A` is
surjective. -/
theorem surjective_chartRing_quotientToAffineOver (K : Ideal A) :
    Function.Surjective (chartRing (Space.quotientToAffineOver B S hS f hA K)) := by
  intro b
  obtain ⟨c, rfl⟩ := (Scheme.ΓSpecIso (.of (A ⧸ K))).commRingCatIsoToRingEquiv.symm.surjective b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact ⟨a, chartRing_quotientToAffineOver K a⟩

end ChartRing

end AlgebraicGeometry.FormalSpace

end
