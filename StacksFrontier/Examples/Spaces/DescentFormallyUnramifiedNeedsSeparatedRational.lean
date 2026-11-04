module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.RingHom.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.Examples.Spaces.DescentFormallyUnramifiedNeedsSeparated
public import StacksFrontier.RingTheory.Etale.ResidueFieldColimit

/-!
# Parts (5) and (6) of Stacks 04CY are false as written

`AlgebraicGeometry.Space.DoubledSection.exists_not_formallyUnramified_of_comp` turns a
square-zero closed immersion of affines `i : T ⟶ T'` with no retraction, together with an
étale surjection `π : X ⟶ T'` with no section, into a representable, surjective, étale
situation `F ⟶ G ⟶ H` whose composite is formally étale while `G ⟶ H` is not formally
unramified. This file supplies such data over `ℚ`, so the refutation depends on no input.

Let `S = T = Spec ℚ`, let `T' = Spec ℚ[ε]` with `i` cut out by `ε`, and let
`X = Spec (ℚ[ε] ⊗_ℚ K)` with `K = ℚ[x]/(x² + 1)`, the map `π` being the base change of
`Spec K ⟶ Spec ℚ`. Then:

* `i` is a square-zero closed immersion with no retraction: a retraction would make the ring
  map `ℚ[ε] ⟶ ℚ`, `ε ↦ 0`, injective;
* `π` is étale, because `K` is the standard étale algebra of `x² + 1` (its derivative `2x` is a
  unit in `K`), and surjective, because `K` is a nonzero free `ℚ`-module, so `ℚ[ε] ⊗_ℚ K` is
  faithfully flat over `ℚ[ε]`;
* there is no morphism `T' ⟶ X` at all: one would give a ring map `K ⟶ ℚ[ε] ⟶ ℚ`, that is, a
  square root of `-1` in `ℚ`.

## Main results

* `AlgebraicGeometry.Space.DoubledSection.Rational.exists_not_formallyUnramified_of_comp`:
  a representable, surjective, étale situation on a big fppf site over `Spec ℚ` whose composite
  is formally étale, hence formally unramified, while its second transformation is neither.
* `AlgebraicGeometry.Space.DoubledSection.Rational.not_forall_descend`: **parts (5) and (6) of
  Stacks 04CY, as written, are false**, stated as the negations of the two universal
  statements.

## Implementation notes

The example lives in universe `0`, the universe of `ℚ`. That suffices to refute the source's
statements, which quantify over every scheme and every big fppf site; lifting `ℚ` along `ULift`
does not give the tensor product `ℚ[ε] ⊗ K` its ring structure without further instances.

## References

* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Polynomial (C derivative)

namespace AlgebraicGeometry.Space.DoubledSection.Rational

/-! ### The rings -/

/-- The dual numbers `ℚ[ε]`, the ring of the thickening `T'`. -/
abbrev D : Type := DualNumber ℚ

/-- The polynomial `x² + 1`. -/
abbrev p : Polynomial ℚ := Polynomial.X ^ 2 + C 1

/-- The étale `ℚ`-algebra `K = ℚ[x]/(x² + 1)`. -/
abbrev K : Type := AdjoinRoot p

/-- The ring `ℚ[ε] ⊗_ℚ K` of the étale cover `X`. -/
abbrev E : Type := D ⊗[ℚ] K

/-- The class `x` of the variable in `K = ℚ[x]/(x² + 1)` satisfies `x² + 1 = 0`. -/
theorem root_sq_add_one : AdjoinRoot.root p ^ 2 + 1 = 0 := by
  have h := AdjoinRoot.mk_self (f := p)
  simpa [p, map_add, map_pow] using h

/-- `K = ℚ[x]/(x² + 1)` is étale over `ℚ`: the derivative `2x` of `x² + 1` is a unit in `K`,
with inverse `-x/2`. -/
instance etale_K : Algebra.Etale ℚ K := by
  refine Stacks.Etale.ResidueFieldColimit.etale_adjoinRoot (Polynomial.monic_X_pow_add_C _
      two_ne_zero) ?_
  have hd : AdjoinRoot.mk p (derivative p) = 2 * AdjoinRoot.root p := by
    simp [p, map_mul]
    norm_num
  rw [hd]
  have h2 : (2 : K) * algebraMap ℚ K 2⁻¹ = 1 := by
    rw [show (2 : K) = algebraMap ℚ K 2 from (map_ofNat _ 2).symm, ← map_mul,
      mul_inv_cancel₀ two_ne_zero, map_one]
  refine isUnit_iff_exists_inv.mpr ⟨-(algebraMap ℚ K 2⁻¹) * AdjoinRoot.root p, ?_⟩
  linear_combination (-(2 * algebraMap ℚ K 2⁻¹)) * root_sq_add_one + h2

/-- `K = ℚ[x]/(x² + 1)` is a nontrivial ring. -/
instance nontrivial_K : Nontrivial K :=
  AdjoinRoot.nontrivial p (by rw [Polynomial.degree_X_pow_add_C two_pos]; decide)

/-- `K` is a free `ℚ`-module. -/
instance free_K : Module.Free ℚ K := Module.Free.of_divisionRing _ _

/-- `ℚ[ε] ⊗_ℚ K` is faithfully flat over `ℚ[ε]`. -/
instance faithfullyFlat_E : Module.FaithfullyFlat D E :=
  Module.FaithfullyFlat.instTensorProduct (R := ℚ) (M := K) D

/-- `K` has no ring map to `ℚ`: it would send `x` to a square root of `-1`. -/
theorem not_ringHom_K (χ : K →+* ℚ) : False := by
  have h := congrArg χ root_sq_add_one
  rw [map_add, map_pow, map_one, map_zero] at h
  nlinarith [sq_nonneg (χ (AdjoinRoot.root p))]

/-! ### The ring maps -/

/-- The ring map `ℚ[ε] ⟶ ℚ`, `ε ↦ 0`, which cuts out `T` in `T'`. -/
abbrev fstC : CommRingCat.of D ⟶ CommRingCat.of ℚ :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom ℚ ℚ ℚ).toRingHom

/-- The ring map `ℚ[ε] ⟶ ℚ[ε] ⊗_ℚ K` of the étale cover. -/
abbrev piC : CommRingCat.of D ⟶ CommRingCat.of E :=
  CommRingCat.ofHom (algebraMap D E)

/-- The structure map `ℚ ⟶ ℚ[ε]`. -/
abbrev baseC : CommRingCat.of ℚ ⟶ CommRingCat.of D :=
  CommRingCat.ofHom (algebraMap ℚ D)

/-- The kernel of `ℚ[ε] ⟶ ℚ`, `ε ↦ 0`, has square zero. -/
theorem ker_fstC_sq : RingHom.ker fstC.hom ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  rw [RingHom.mem_ker] at ha hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  rw [Ideal.mem_bot]
  ext <;> simp [ha, hb]

/-- The ring map `ℚ[ε] ⟶ ℚ`, `ε ↦ 0`, is not injective. -/
theorem not_injective_fstC : ¬ Function.Injective fstC.hom := by
  intro h
  have : (DualNumber.eps : D) = 0 := h (by simp [fstC])
  have := congrArg TrivSqZeroExt.snd this
  simp at this

/-! ### The schemes -/

/-- The closed immersion `Spec ℚ ⟶ Spec ℚ[ε]` is a first-order thickening. -/
theorem isFirstOrderThickening_fstC :
    Stacks.Thickenings.IsFirstOrderThickening (Spec.map fstC) :=
  Stacks.Smooth.isFirstOrderThickening_specMap _ (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)
    ker_fstC_sq

/-- The morphism `Spec (ℚ[ε] ⊗_ℚ K) ⟶ Spec ℚ[ε]` is étale. -/
theorem etale_piC : Etale (Spec.map piC) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- The morphism `Spec (ℚ[ε] ⊗_ℚ K) ⟶ Spec ℚ[ε]` is surjective. -/
theorem surjective_piC : Surjective (Spec.map piC) :=
  ((flat_and_surjective_SpecMap_iff piC).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2

/-- There is no morphism of schemes `Spec ℚ[ε] ⟶ Spec (ℚ[ε] ⊗_ℚ K)`. -/
theorem not_hom_spec (f : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of E)) : False := by
  let χ : CommRingCat.of E ⟶ CommRingCat.of ℚ :=
    (Scheme.ΓSpecIso _).inv ≫ f.appTop ≫ (Scheme.ΓSpecIso _).hom ≫ fstC
  exact not_ringHom_K (χ.hom.comp Algebra.TensorProduct.includeRight.toRingHom)

/-- The closed immersion `Spec ℚ ⟶ Spec ℚ[ε]` has no retraction. -/
theorem not_retraction_spec (g : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of ℚ))
    (hg : g ≫ Spec.map fstC = 𝟙 _) : False := by
  apply not_injective_fstC
  have hbij := fun R => ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom
  have h := congrArg Scheme.Hom.appTop hg
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
  have hinj : Function.Injective (Spec.map fstC).appTop.hom := by
    intro a b hab
    have := congrArg g.appTop.hom hab
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, h] at this
    simpa using this
  have hinj2 : Function.Injective ((Spec.map fstC).appTop ≫ (Scheme.ΓSpecIso _).hom).hom :=
    (hbij _).1.comp hinj
  rw [Scheme.ΓSpecIso_naturality fstC] at hinj2
  intro a b hab
  obtain ⟨a', rfl⟩ := (hbij _).2 a
  obtain ⟨b', rfl⟩ := (hbij _).2 b
  exact congrArg _ (hinj2 (by simpa using hab))

/-! ### The site -/

/-- The three spectra of the example. -/
abbrev spectra : Set Scheme.{0} :=
  {Spec (CommRingCat.of ℚ), Spec (CommRingCat.of D), Spec (CommRingCat.of E)}

/-- There is a big fppf site containing each of the three spectra in `spectra`. -/
theorem exists_site : ∃ B : BigFppfSite.{0}, ∀ Y ∈ spectra, B.Contains Y :=
  BigFppfSite.exists_containing spectra

/-- A big fppf site containing the three spectra. -/
abbrev site : BigFppfSite.{0} := exists_site.choose

/-- The site `site` contains `Spec ℚ`. -/
theorem site_contains_Q : site.Contains (Spec (CommRingCat.of ℚ)) :=
  exists_site.choose_spec _ (by simp)

/-- The site `site` contains `Spec ℚ[ε]`. -/
theorem site_contains_D : site.Contains (Spec (CommRingCat.of D)) :=
  exists_site.choose_spec _ (by simp)

/-- The site `site` contains `Spec (ℚ[ε] ⊗_ℚ K)`. -/
theorem site_contains_E : site.Contains (Spec (CommRingCat.of E)) :=
  exists_site.choose_spec _ (by simp)

/-- The base scheme `S = Spec ℚ`. -/
abbrev S : Scheme.{0} := Spec (CommRingCat.of ℚ)

/-- The thickening `T' = Spec ℚ[ε]`, over `S`. -/
abbrev T' : BigFppfOver site S site_contains_Q :=
  BigFppfOver.mk site S site_contains_Q site_contains_D (Spec.map baseC)

/-- The closed subscheme `T = Spec ℚ` of `T'`, over `S`. -/
abbrev T : BigFppfOver site S site_contains_Q :=
  BigFppfOver.mk site S site_contains_Q site_contains_Q (Spec.map fstC ≫ Spec.map baseC)

/-- The étale cover `X = Spec (ℚ[ε] ⊗_ℚ K)` of `T'`, over `S`. -/
abbrev X : BigFppfOver site S site_contains_Q :=
  BigFppfOver.mk site S site_contains_Q site_contains_E (Spec.map piC ≫ Spec.map baseC)

/-- The square-zero closed immersion `i : T ⟶ T'`. -/
abbrev i : T ⟶ T' :=
  BigFppfOver.homMk site S site_contains_Q site_contains_D (Spec.map baseC) (Spec.map fstC) rfl

/-- The étale surjection `π : X ⟶ T'`. -/
abbrev π : X ⟶ T' :=
  BigFppfOver.homMk site S site_contains_Q site_contains_D (Spec.map baseC) (Spec.map piC) rfl

/-! ### The counterexample -/

/-- **A representable, surjective, étale situation over `Spec ℚ` refuting parts (5) and (6) of
Stacks 04CY.** Its composite transformation is formally étale, hence formally unramified, while
its second transformation is not formally unramified, hence not formally étale either. -/
theorem exists_not_formallyUnramified_of_comp :
    ∃ s : RepresentableSurjectiveEtaleSituation.{0},
      FormallyEtale (s.a ≫ s.b) ∧ FormallyUnramified (s.a ≫ s.b) ∧
        ¬ FormallyUnramified s.b ∧ ¬ FormallyEtale s.b := by
  obtain ⟨s, -, -, het, hnu, hne⟩ := DoubledSection.exists_not_formallyUnramified_of_comp i π
    (preservesLimitsOfShape_walkingCospan_toScheme site S site_contains_Q)
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of ℚ))))
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of D))))
    isFirstOrderThickening_fstC etale_piC surjective_piC
    (fun ξ _ => not_hom_spec ((BigFppfOver.toScheme site S site_contains_Q).map ξ))
    (fun g hg => not_retraction_spec ((BigFppfOver.toScheme site S site_contains_Q).map g)
      (by
        have h := congrArg (BigFppfOver.toScheme site S site_contains_Q).map hg
        rwa [Functor.map_comp, CategoryTheory.Functor.map_id] at h))
  exact ⟨s, het, fun T₀ T₀' hT₀ hT₀' i₀ hi₀ x y hxy z₁ z₂ h₁ h₂ =>
    (het T₀ T₀' hT₀ hT₀' i₀ hi₀ x y hxy).unique h₁ h₂, hnu, hne⟩

/-- **Parts (5) and (6) of Stacks 04CY are false as written.** The source states, for an
arbitrary representable, surjective, étale `a : F ⟶ G` and any `b : G ⟶ H` of set-valued
functors on a big fppf site, that `b` is formally unramified when `b ∘ a` is (part (5)) and
formally étale when `b ∘ a` is (part (6)). Both universal statements fail, already over
`Spec ℚ`.

The corrected forms are `AlgebraicGeometry.Space.formallyUnramified_of_comp_of_isSeparated`
and `AlgebraicGeometry.Space.formallyEtale_of_comp_of_isSeparated`. -/
@[stacks 04CY "counterexample to parts (5),(6) as written"]
theorem not_forall_descend :
    ¬ (∀ s : RepresentableSurjectiveEtaleSituation.{0},
        FormallyUnramified (s.a ≫ s.b) → FormallyUnramified s.b) ∧
      ¬ (∀ s : RepresentableSurjectiveEtaleSituation.{0},
        FormallyEtale (s.a ≫ s.b) → FormallyEtale s.b) := by
  obtain ⟨s, het, hun, hnu, hne⟩ := exists_not_formallyUnramified_of_comp
  exact ⟨fun h => hnu (h s hun), fun h => hne (h s het)⟩

end AlgebraicGeometry.Space.DoubledSection.Rational

end
