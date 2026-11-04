module

public import Mathlib.AlgebraicGeometry.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Curves.RationalMapExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineDimension

/-!
# A nonconstant rational function on a curve as a morphism to the projective line

Let `k` be a field and let `X` be an integral scheme over `k` of topological dimension one. On a
dense affine open `U` of `X` there is a dominant morphism `U ⟶ ℙ¹_k` over `k`, attached to a
nonconstant regular function on `U`: a nonzero non-unit `s ∈ Γ(U, 𝒪)` is transcendental over
`k`, so `k[T] ⟶ Γ(U, 𝒪)`, `T ↦ s`, is injective, and `U ≅ Spec Γ(U, 𝒪) ⟶ Spec k[T]` followed by
the first chart of `ℙ¹_k` is dominant. When `X` is a normal proper curve this partial map extends
([Stacks, Tag 0BXZ]) to a proper dominant morphism `X ⟶ ℙ¹_k` over `k`.

## Main results

* `AlgebraicGeometry.isDominant_Spec_map_of_injective` — an injective map of domains induces a
  dominant morphism of spectra.
* `Stacks.Chow.injective_eval₂RingHom_of_ne_zero_of_not_isUnit` — a nonzero non-unit of a domain
  over a field is transcendental.
* `Stacks.Chow.exists_ne_zero_not_isUnit_globalSections` — an integral affine scheme with more
  than one point has a nonzero non-unit global section.
* `Stacks.Chow.exists_affineOpen_not_subsingleton` — an integral scheme of dimension one has a
  dense affine open with more than one point.
* `Stacks.Chow.exists_isDominant_partialMap_to_projectiveLine` — **the partial map**: a dense
  affine open of `X` carrying a dominant morphism to `ℙ¹_k` over `k`.
* `Stacks.Chow.exists_isProper_isDominant_to_projectiveLine` — a normal proper curve over `k`
  admits a proper dominant morphism to `ℙ¹_k` over `k`.

## Implementation notes

Morphisms into an affine scheme are handled through `AlgebraicGeometry.Scheme.toSpecΓ` rather
than through `AlgebraicGeometry.IsAffineOpen.isoSpec`: every morphism `g : W ⟶ Spec R` factors as
`W.toSpecΓ ≫ Spec.map ρ` with `ρ = (ΓSpecIso R).inv ≫ g.appTop`.

## References

* [Stacks Project, Tag 0CC1](https://stacks.math.columbia.edu/tag/0CC1)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 0BXZ](https://stacks.math.columbia.edu/tag/0BXZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **An injective map of domains induces a dominant morphism of spectra.** -/
theorem isDominant_Spec_map_of_injective {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S]
    (φ : R ⟶ S) (hφ : Function.Injective φ.hom) : IsDominant (Spec.map φ) := by
  refine ((tfae_isDominant_of_isIntegral (Spec.map φ)).out 1 2).mpr ?_
  rw [genericPoint_eq_bot_of_affine R, genericPoint_eq_bot_of_affine S]
  refine PrimeSpectrum.ext ?_
  show Ideal.comap φ.hom (⊥ : PrimeSpectrum S).asIdeal = (⊥ : PrimeSpectrum R).asIdeal
  ext x
  show φ.hom x ∈ (⊥ : Ideal S) ↔ x ∈ (⊥ : Ideal R)
  simp [map_eq_zero_iff _ hφ]

/-- Every morphism to an affine scheme factors through the canonical morphism to the spectrum of
the global sections of its source. -/
theorem eq_toSpecΓ_comp_Spec_map {W : Scheme.{u}} {R : CommRingCat.{u}} (g : W ⟶ Spec R) :
    g = W.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ g.appTop) := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  simp

end AlgebraicGeometry

namespace Stacks.Chow

/-- **A nonzero non-unit of a domain over a field is transcendental**: evaluation of polynomials
at a nonzero non-unit is injective. -/
theorem injective_eval₂RingHom_of_ne_zero_of_not_isUnit {k : Type u} [Field k]
    {A : Type u} [CommRing A] [IsDomain A] (ρ : k →+* A) {s : A}
    (hs0 : s ≠ 0) (hsu : ¬ IsUnit s) :
    Function.Injective (Polynomial.eval₂RingHom ρ s) := by
  let _ : Algebra k A := ρ.toAlgebra
  have halg : ¬ IsAlgebraic k s := fun h ↦ hsu (h.isIntegral.isUnit hs0)
  have hinj : Function.Injective (Polynomial.aeval s : Polynomial k →ₐ[k] A) :=
    transcendental_iff_injective.mp halg
  intro a b hab
  refine hinj ?_
  rw [Polynomial.aeval_def, Polynomial.aeval_def]
  simpa [RingHom.algebraMap_toAlgebra] using hab

/-- **An integral affine scheme with more than one point has a nonzero non-unit global
section.** -/
theorem exists_ne_zero_not_isUnit_globalSections (W : Scheme.{u}) [IsAffine W] [IsIntegral W]
    (hns : ¬ Subsingleton W) : ∃ s : Γ(W, ⊤), s ≠ 0 ∧ ¬ IsUnit s := by
  have _ := not_subsingleton_iff_nontrivial.mp hns
  obtain ⟨w, hw⟩ := (Scheme.homeoOfIso W.isoSpec).injective.exists_ne
    (⊥ : PrimeSpectrum Γ(W, ⊤))
  obtain ⟨s, hsmem, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h ↦ hw (PrimeSpectrum.ext h) : (W.isoSpec.hom.base w).asIdeal ≠ ⊥)
  exact ⟨s, hs0, fun hu ↦
    (W.isoSpec.hom.base w).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hsmem hu)⟩

/-- A topological space of Krull dimension at least one has two distinct points. -/
theorem not_subsingleton_of_one_le_topologicalKrullDim {Z : Type u} [TopologicalSpace Z]
    (hdim : 1 ≤ topologicalKrullDim Z) : ¬ Subsingleton Z := by
  obtain ⟨D, T, hDT⟩ := Order.one_le_krullDim_iff.mp hdim
  obtain ⟨a, ha⟩ := D.isIrreducible.nonempty
  obtain ⟨b, -, hbD⟩ := Set.not_subset.mp (fun h : (T : Set Z) ⊆ (D : Set Z) ↦ hDT.not_ge h)
  exact not_subsingleton_iff_nontrivial.mpr ⟨a, b, fun h ↦ hbD (h ▸ ha)⟩

/-- **An integral scheme of dimension at least one has a dense affine open with more than one
point.** -/
theorem exists_affineOpen_not_subsingleton {X : Scheme.{u}} [IsIntegral X]
    (hdim : 1 ≤ topologicalKrullDim X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ Dense (U : Set X) ∧ ¬ Subsingleton U.toScheme := by
  have _ := not_subsingleton_iff_nontrivial.mp
    (not_subsingleton_of_one_le_topologicalKrullDim hdim)
  obtain ⟨z, hz⟩ := exists_ne (genericPoint X)
  obtain ⟨-, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hdense : Dense (U : Set X) := U.isOpen.dense ⟨z, hzU⟩
  have hgen : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨z, Set.mem_univ _, hzU⟩
  refine ⟨U, hU, hdense, not_subsingleton_iff_nontrivial.mpr
    ⟨⟨z, hzU⟩, ⟨genericPoint X, hgen⟩, fun h ↦ hz (congrArg Subtype.val h)⟩⟩

/-- **A dominant morphism from a dense affine open to the projective line.** For an integral
scheme `X` over a field `k` of dimension at least one there is a dense affine open `U` and a
dominant morphism `U ⟶ ℙ¹_k` over `k`. -/
theorem exists_isDominant_partialMap_to_projectiveLine {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (q : X ⟶ AlgebraicGeometry.Spec (.of k))
    (hdim : 1 ≤ topologicalKrullDim X) :
    ∃ (U : X.Opens) (ψ : U.toScheme ⟶ projectiveLine k),
      Dense (U : Set X) ∧ IsDominant ψ ∧
        ψ ≫ (projectiveLine k ↘ AlgebraicGeometry.Spec (.of k)) = U.ι ≫ q := by
  obtain ⟨U, hU, hdense, hns⟩ := exists_affineOpen_not_subsingleton (X := X) hdim
  have _ : IsAffine U.toScheme := hU
  obtain ⟨u₀, -, -⟩ := not_subsingleton_iff_nontrivial.mp hns
  have _ : Nonempty U := ⟨u₀⟩
  have _ : IsIntegral U.toScheme := inferInstance
  obtain ⟨s, hs0, hsu⟩ := exists_ne_zero_not_isUnit_globalSections U.toScheme hns
  set ρ : CommRingCat.of k ⟶ Γ(U.toScheme, ⊤) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ q).appTop
  set φ : CommRingCat.of (Polynomial k) ⟶ Γ(U.toScheme, ⊤) :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom ρ.hom s)
  have hφinj : Function.Injective φ.hom :=
    injective_eval₂RingHom_of_ne_zero_of_not_isUnit ρ.hom hs0 hsu
  have hCφ : CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) ≫ φ = ρ := by
    refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
    show Polynomial.eval₂RingHom ρ.hom s (Polynomial.C c) = ρ.hom c
    simp
  refine ⟨U, U.toScheme.toSpecΓ ≫ Spec.map φ ≫ projectiveLineXChart k, hdense, ?_, ?_⟩
  · have _ : IsDominant (Spec.map φ) := isDominant_Spec_map_of_injective φ hφinj
    have _ : IsDominant U.toScheme.toSpecΓ := by
      have _ : IsIso U.toScheme.toSpecΓ := inferInstance
      infer_instance
    infer_instance
  · rw [Category.assoc, Category.assoc, projectiveLineXChart_comp_structureMorphism,
      projectiveLineAffineStructureMorphism, ← Spec.map_comp, hCφ]
    exact (eq_toSpecΓ_comp_Spec_map (U.ι ≫ q)).symm

/-! ### Extending the partial map across the curve -/

/-- A morphism whose rational map is dominant is dominant. -/
theorem isDominant_of_isDominant_toRationalMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : f.toRationalMap.IsDominant) : IsDominant f := by
  rw [Scheme.Hom.toRationalMap, Scheme.PartialMap.isDominant_toRationalMap_iff] at h
  have hd : IsDominant f.toPartialMap.hom := h
  dsimp [Scheme.Hom.toPartialMap] at hd
  rwa [IsDominant.comp_iff] at hd

/-- **A normal proper curve admits a proper dominant morphism to the projective line.** For a
normal proper curve `X` over a field `k` there is a proper dominant morphism `X ⟶ ℙ¹_k` over
`k`. -/
theorem exists_isProper_isDominant_to_projectiveLine (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsCurve k (X ↘ AlgebraicGeometry.Spec (.of k))] [IsNormal X]
    [IsProper (X ↘ AlgebraicGeometry.Spec (.of k))] :
    ∃ p : X ⟶ projectiveLine k, IsProper p ∧ IsDominant p ∧
      p ≫ (projectiveLine k ↘ AlgebraicGeometry.Spec (.of k)) =
        X ↘ AlgebraicGeometry.Spec (.of k) := by
  have hdim : topologicalKrullDim X = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := X ↘ AlgebraicGeometry.Spec (.of k))
  obtain ⟨U, ψ, hdense, hψdom, hψover⟩ :=
    exists_isDominant_partialMap_to_projectiveLine (X ↘ AlgebraicGeometry.Spec (.of k))
      (le_of_eq hdim.symm)
  let pm : Scheme.PartialMap X (projectiveLine k) := ⟨U, hdense, ψ⟩
  have _ : IsDominant pm.hom := hψdom
  have _ : pm.IsOver (AlgebraicGeometry.Spec (.of k)) := by
    rwa [Scheme.PartialMap.isOver_iff]
  set XO : CategoryTheory.Over (AlgebraicGeometry.Spec (.of k)) :=
    CategoryTheory.Over.mk (X ↘ AlgebraicGeometry.Spec (.of k))
  set YO : CategoryTheory.Over (AlgebraicGeometry.Spec (.of k)) :=
    CategoryTheory.Over.mk (projectiveLine k ↘ AlgebraicGeometry.Spec (.of k))
  have _ : IsCurve k XO.hom :=
    inferInstanceAs (IsCurve k (X ↘ AlgebraicGeometry.Spec (.of k)))
  have _ : IsNormal XO.left := inferInstanceAs (IsNormal X)
  have _ : IsProperVariety k YO.hom :=
    inferInstanceAs (IsProperVariety k (projectiveLine k ↘ AlgebraicGeometry.Spec (.of k)))
  obtain ⟨f, hf⟩ := (toRationalMap_bijective k XO YO).2
    ⟨pm.toRationalMap, Scheme.RationalMap.IsOver.mk ⟨pm, by
      rwa [Scheme.PartialMap.isOver_iff], rfl⟩⟩
  have hrat : f.left.toRationalMap = pm.toRationalMap := congrArg Subtype.val hf
  have _ : IsProper (f.left ≫ (projectiveLine k ↘ AlgebraicGeometry.Spec (.of k))) := by
    rw [show f.left ≫ (projectiveLine k ↘ AlgebraicGeometry.Spec (.of k)) =
      X ↘ AlgebraicGeometry.Spec (.of k) from f.w]
    infer_instance
  refine ⟨f.left, IsProper.of_comp f.left (projectiveLine k ↘ AlgebraicGeometry.Spec (.of k)),
    isDominant_of_isDominant_toRationalMap f.left ?_, f.w⟩
  rw [hrat]
  infer_instance

end Stacks.Chow

end
