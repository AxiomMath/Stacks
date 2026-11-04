module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.SectionDivision.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic

/-!
# Charts of the morphism to projective space attached to generating sections

[Stacks, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE) says that `ℙⁿ_ℤ` represents the
functor sending a scheme `Y` to the pairs `(L, (s₀, …, sₙ))` consisting of an invertible
`𝒪_Y`-module and `n + 1` global sections generating it; the induced morphism
`φ_{(L, s)} : Y → ℙⁿ_S` is described in the discussion following
[Tag 01NF](https://stacks.math.columbia.edu/tag/01NF).

A morphism into `ℙⁿ_S` is determined by its composite with the projection to the base and a
morphism into the integral model `projectiveSpaceAtUniverse` of projective space, at an arbitrary
universe; this is the universal property of the pullback, and is `liftAtUniverse`.

Given an invertible module `L` on a scheme `X` and global sections `s₀, …, sₙ`, each nonvanishing
locus `X_{sᵢ}` carries the `n + 1` functions `sₖ / sᵢ` (`Stacks.SheafOfModules.divBySection`), of
which the `i`-th is `1`. They determine a ring homomorphism `ℤ[T₀, …, Tₙ] → Γ(X_{sᵢ}, 𝒪)` whose
image of the irrelevant ideal is the unit ideal, and `AlgebraicGeometry.Proj.fromOfGlobalSections`
turns it into a morphism `X_{sᵢ} ⟶ ℙⁿ_ℤ`. On `X_{sᵢ}` the section `sᵢ` trivializes `L`, which is
what makes the ratios functions. The nonvanishing loci of a generating family cover `X`.

## Main definitions

* `AlgebraicGeometry.projectiveSpaceOver.liftAtUniverse`: the lift of a morphism to the integral
  model of projective space at an arbitrary universe.
* `Stacks.ProjectiveSpaceSections.chartRatio`: the function `sₖ / sᵢ` on `X_{sᵢ}`.
* `Stacks.ProjectiveSpaceSections.chartHom`: the ring homomorphism `ℤ[T₀, …, Tₙ] → Γ(X_{sᵢ}, 𝒪)`
  sending `Tₖ` to `sₖ / sᵢ`.
* `Stacks.ProjectiveSpaceSections.chartMorphism`: the resulting morphism
  `X_{sᵢ} ⟶ projectiveSpaceAtUniverse n`.

## Main results

* `AlgebraicGeometry.projectiveSpaceOver.liftAtUniverse_fst` and
  `AlgebraicGeometry.projectiveSpaceOver.liftAtUniverse_toIntegralAtUniverse`: the lift is a
  morphism over the base and recovers the given morphism to the integral model.
* `Stacks.ProjectiveSpaceSections.map_irrelevant_chartHom_eq_top`: the image of the irrelevant
  ideal under `chartHom` is the unit ideal.
* `Stacks.ProjectiveSpaceSections.iSup_nonvanishingOpen_eq_top`: the nonvanishing loci of a
  generating family of global sections of an invertible module cover `X`.

## Implementation notes

`AlgebraicGeometry.Proj` of `MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)` is
definitionally `AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n`, so `chartMorphism` is stated
with the latter as its target; the grading instance `MvPolynomial.gradedAlgebra` is a local
instance here, since it is not a global one.

The coefficient ring of the integral model at universe `u` is `ULift.{u} ℤ`, which has a unique
ring homomorphism to any ring; `baseHom` is that homomorphism.

The invertibility hypothesis is `Stacks.SheafOfModules.IsInvertible`, for which
`Stacks.SheafOfModules.nonvanishingOpen` and `divBySection` are defined; it is equivalent to
`AlgebraicGeometry.SheafOfModules.IsInvertible` by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

/-- The morphism `X ⟶ ℙⁿ_S` determined by a morphism `f : X ⟶ S` and a morphism `g` to the
integral model of projective space in the universe of the base, given by the universal property
of the pullback defining `projectiveSpaceOver`. -/
noncomputable def liftAtUniverse {X S : Scheme.{u}} (n : ℕ) (f : X ⟶ S)
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) : X ⟶ projectiveSpaceOver n S :=
  pullback.lift f g (by simp)

/-- The lift is a morphism over the base. -/
@[simp] theorem liftAtUniverse_fst {X S : Scheme.{u}} (n : ℕ) (f : X ⟶ S)
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) :
    liftAtUniverse n f g ≫ pullback.fst _ _ = f :=
  pullback.lift_fst _ _ _

/-- The lift recovers the given morphism to the integral model. -/
@[simp] theorem liftAtUniverse_toIntegralAtUniverse {X S : Scheme.{u}} (n : ℕ) (f : X ⟶ S)
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) :
    liftAtUniverse n f g ≫ toIntegralAtUniverse n S = g :=
  pullback.lift_snd _ _ _

/-- At universe zero the two lifts agree, the morphism to the integral model being transported
along `projectiveSpaceIntegralIso`. -/
theorem lift_eq_liftAtUniverse {X S : Scheme.{0}} (n : ℕ) (f : X ⟶ S)
    (g : X ⟶ projectiveSpace n) :
    lift n f g = liftAtUniverse n f (g ≫ (projectiveSpaceIntegralIso n).hom) :=
  rfl

end AlgebraicGeometry.projectiveSpaceOver

namespace Stacks.ProjectiveSpaceSections

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The unique ring homomorphism out of the coefficient ring `ULift ℤ` of the integral model of
projective space at universe `u`. -/
noncomputable def baseHom (R : Type u) [CommRing R] : ULift.{u} ℤ →+* R :=
  (Int.castRingHom R).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]

/-- The nonvanishing locus of a global section of an invertible module, ascribed at `X.Opens`. -/
noncomputable def nonvanishingChart (s : L.sections) : X.Opens :=
  SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) L s

/-- The ratio `sₖ / sᵢ`, a global function on the chart `X_{sᵢ}`. -/
noncomputable def chartRatio {n : ℕ} (s : Fin (n + 1) → L.sections) (i k : Fin (n + 1)) :
    Γ((nonvanishingChart L (s i)).toScheme, ⊤) :=
  (nonvanishingChart L (s i)).topIso.inv.hom
    (SheafOfModules.divBySection (X := X.toRingedSpace) L (s i) le_rfl ((s k).eval (op _)))

/-- The `i`-th ratio on the `i`-th chart is `1`. -/
@[simp] theorem chartRatio_self {n : ℕ} (s : Fin (n + 1) → L.sections) (i : Fin (n + 1)) :
    chartRatio L s i i = 1 :=
  (congrArg (nonvanishingChart L (s i)).topIso.inv.hom
      (SheafOfModules.divBySection_self (X := X.toRingedSpace) L (s i) le_rfl)).trans
    (map_one _)

/-- The ring homomorphism `ℤ[T₀, …, Tₙ] → Γ(X_{sᵢ}, 𝒪)` sending the homogeneous coordinate `Tₖ`
to the ratio `sₖ / sᵢ`. -/
noncomputable def chartHom {n : ℕ} (s : Fin (n + 1) → L.sections) (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ) →+*
      Γ((nonvanishingChart L (s i)).toScheme, ⊤) :=
  MvPolynomial.eval₂Hom (baseHom _) (fun k => chartRatio L s i k)

/-- `chartHom` sends the homogeneous coordinate `Tₖ` to the ratio `sₖ / sᵢ`. -/
@[simp] theorem chartHom_X {n : ℕ} (s : Fin (n + 1) → L.sections) (i k : Fin (n + 1)) :
    chartHom L s i (MvPolynomial.X k) = chartRatio L s i k :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- The `i`-th homogeneous coordinate goes to `1` on the `i`-th chart. -/
theorem chartHom_X_self {n : ℕ} (s : Fin (n + 1) → L.sections) (i : Fin (n + 1)) :
    chartHom L s i (MvPolynomial.X i) = 1 := by
  rw [chartHom_X, chartRatio_self]

/-- Each variable `Tₖ` is homogeneous of degree one. -/
private theorem X_mem_homogeneousSubmodule_one {n : ℕ} (k : Fin (n + 1)) :
    (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X _ k)

/-- The image of the irrelevant ideal under `chartHom` is the unit ideal. -/
theorem map_irrelevant_chartHom_eq_top {n : ℕ} (s : Fin (n + 1) → L.sections)
    (i : Fin (n + 1)) :
    (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))).toIdeal.map
      (chartHom L s i) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← chartHom_X_self L s i]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (X_mem_homogeneousSubmodule_one i))

/-- The morphism `X_{sᵢ} ⟶ ℙⁿ` on the nonvanishing locus of `sᵢ` defined by the functions
`s₀/sᵢ, …, sₙ/sᵢ`, namely `AlgebraicGeometry.Proj.fromOfGlobalSections` for the ring
homomorphism `chartHom`. -/
noncomputable def chartMorphism {n : ℕ} (s : Fin (n + 1) → L.sections) (i : Fin (n + 1)) :
    (nonvanishingChart L (s i)).toScheme ⟶ projectiveSpaceAtUniverse.{u} n :=
  Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (chartHom L s i) (map_irrelevant_chartHom_eq_top L s i)

/-- The preimage under the `i`-th chart morphism of the standard open `D₊(Tₖ)` is the
nonvanishing locus of the function `sₖ / sᵢ`. -/
theorem chartMorphism_preimage_basicOpen {n : ℕ} (s : Fin (n + 1) → L.sections)
    (i k : Fin (n + 1)) :
    chartMorphism L s i ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X k)
      = (nonvanishingChart L (s i)).toScheme.basicOpen (chartRatio L s i k) := by
  rw [← chartHom_X L s i k]
  exact Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos
    (X_mem_homogeneousSubmodule_one k)

/-- The nonvanishing loci of a generating family of global sections of an invertible module
cover the scheme. -/
theorem iSup_nonvanishingOpen_eq_top (g : L.GeneratingSections) :
    (⨆ i : g.I, nonvanishingChart L (g.s i)) = ⊤ :=
  top_unique fun x _ => by
    obtain ⟨i, hi⟩ := SheafOfModules.exists_generatingSection_nonvanishing L g x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩

end Stacks.ProjectiveSpaceSections

end
