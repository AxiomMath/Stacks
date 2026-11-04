module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionDegree
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusSingleTriangleHomology

/-!
# `H² ∘ Φ ∘ Φ` is exact and faithful on sheaves with finite stalks

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. The Fourier transform is a triangulated functor, and `Φ(Φ(F))` is concentrated in
degree two for `F` with finite geometric stalks
(`Stacks.EtaleCohomology.isZero_homology_fourierTransform_comp`), so the long exact cohomology
sequence of the image under `ΦΦ` of the triangle of a short exact sequence of such sheaves reduces
to a short exact sequence in degree two. With the reflection of zero objects
(`Stacks.EtaleCohomology.isZero_of_isZero_homology_two_fourierTransform_comp`), the functor
`F ↦ H²(Φ(Φ(F[0])))` is faithful on these sheaves. Consequently, for a monomorphism `α : A ⟶ G`
of such sheaves, if `ℓᵉ • Φ(α) = 0` then `ℓᵉ` kills `A`.

This is the formal lemma (E1) of the single-level argument for the irreducibility of the Fourier
transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.finite_globalSections_inverseImage_of_mono` and `_of_epi`: finite
  geometric stalks pass to subsheaves and quotients.
* `Stacks.EtaleCohomology.fourierTransformCommShift`,
  `Stacks.EtaleCohomology.isTriangulated_fourierTransform`: `Φ` is triangulated.
* `Stacks.EtaleCohomology.eq_zero_of_homology_two_fourierTransform_comp_map_eq_zero`.
* `Stacks.EtaleCohomology.eq_zero_of_fourierTransform_map_comp_mono_eq_zero` (E1).

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
  AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

section Stalks

variable (Λ : Type) [Ring Λ] {X : Scheme.{u}}

/-- **Finite geometric stalks pass to subsheaves.** -/
theorem finite_globalSections_inverseImage_of_mono {A G : EtaleModules.{u, 0} Λ X}
    (ι : A ⟶ G) [Mono ι]
    (hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ X),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj G)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ X) :
    Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ w).obj A)) := by
  have := hG Ω w
  let φ := (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).map
    ((etaleModuleInverseImage.{u, 0} Λ w).map ι)
  have : Mono φ := inferInstance
  exact Finite.of_injective φ.hom ((ModuleCat.mono_iff_injective φ).1 inferInstance)

/-- **Finite geometric stalks pass to quotients**: over a separably closed field global sections
are an equivalence. -/
theorem finite_globalSections_inverseImage_of_epi {G C : EtaleModules.{u, 0} Λ X}
    (π : G ⟶ C) [Epi π]
    (hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ X),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj G)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ X) :
    Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ w).obj C)) := by
  have := hG Ω w
  have : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{0, u, u + 1}
  have : HasSheafify (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    hasSheafifyEtale.{u, 0} (Spec (.of Ω)) Λ
  have := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))
  have : Γ.IsEquivalence := inferInstanceAs (Sheaf.Γ _ _).IsEquivalence
  let φ := Γ.map ((etaleModuleInverseImage.{u, 0} Λ w).map π)
  have : Epi φ := inferInstance
  exact Finite.of_surjective φ.hom ((ModuleCat.epi_iff_surjective φ).1 inferInstance)

end Stalks

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **The Fourier transform commutes with the shift**: it is a composite of an inverse image, a
tensor product and a lower shriek, each computed degreewise or as a right derived functor. -/
@[instance_reducible]
def fourierTransformCommShift (j : CompactificationOf (Over.mk 𝔸f)) :
    (fourierTransform k Λ ψ B p₀ j).CommShift ℤ :=
  have h := isExactTensorRight_fourierKernel k Λ ψ B p₀
  have := h.1
  have := h.2.1
  have := h.2.2
  inferInstanceAs ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst 𝔸f 𝔸f) ⋙
    (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
      (affineLineArtinSchreierSheaf k Λ ψ B p₀))).mapDerivedCategoryPlus ⋙
    derivedLowerShriek.{u, 0} (pullback.snd 𝔸f 𝔸f)
      (j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)) Λ).CommShift ℤ)

attribute [local instance] fourierTransformCommShift in
/-- **The Fourier transform is a triangulated functor.** -/
theorem isTriangulated_fourierTransform (j : CompactificationOf (Over.mk 𝔸f)) :
    (fourierTransform k Λ ψ B p₀ j).IsTriangulated :=
  have h := isExactTensorRight_fourierKernel k Λ ψ B p₀
  have := h.1
  have := h.2.1
  have := h.2.2
  inferInstanceAs ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst 𝔸f 𝔸f) ⋙
    (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
      (affineLineArtinSchreierSheaf k Λ ψ B p₀))).mapDerivedCategoryPlus ⋙
    derivedLowerShriek.{u, 0} (pullback.snd 𝔸f 𝔸f)
      (j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)) Λ).IsTriangulated)

section Exact

/-- **`H²(Φ(Φ(-[0])))` is faithful on sheaves with finite geometric stalks**: it is exact on them
(`Φ` is triangulated and `Φ(Φ(F[0]))` is concentrated in degree two) and reflects zero objects,
so it kills the image of a morphism it kills. -/
theorem eq_zero_of_homology_two_fourierTransform_comp_map_eq_zero
    (hψ : ∑ a : k, ψ a = 0) (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    {A C : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))} (f : A ⟶ C)
    (hA : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj A)))
    (hC : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj C)))
    (h : (DerivedCategory.Plus.homologyFunctor _ 2).map
      ((fourierTransform k Λ ψ B p₀ j ⋙ fourierTransform k Λ ψ B p₀ j).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map f)) = 0) : f = 0 :=
  @Stacks.DerivedCategoryPlus.eq_zero_of_homology_map_map_singleFunctor_map_eq_zero
    (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) _ _ _
    (fourierTransform k Λ ψ B p₀ j) (fourierTransform k Λ ψ B p₀ j)
    (fourierTransformCommShift k Λ ψ B p₀ j) (fourierTransformCommShift k Λ ψ B p₀ j)
    (isTriangulated_fourierTransform k Λ ψ B p₀ j) (isTriangulated_fourierTransform k Λ ψ B p₀ j)
    (fun A ↦ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj A)))
    (fun ι _ hB ↦ finite_globalSections_inverseImage_of_mono Λ ι hB)
    (fun π _ hA ↦ finite_globalSections_inverseImage_of_epi Λ π hA) 2
    (fun X hX i hi ↦ isZero_homology_fourierTransform_comp k Λ ψ B p₀ hψ hq j jQ X hX i hi)
    (fun X hX hz ↦
      isZero_of_isZero_homology_two_fourierTransform_comp k Λ ψ B p₀ hψ hq j jQ X hX hz)
    _ _ f hA hC h

/-- **(E1) If `Φ((φ ≫ α)[0]) = 0` for a monomorphism `α : A ⟶ G` and `φ : A ⟶ A`, then
`φ = 0`**, for sheaves with finite geometric stalks; for instance `Φ(ℓᵉ • α) = 0` forces
`ℓᵉ • 𝟙 A = 0`. -/
theorem eq_zero_of_fourierTransform_map_comp_mono_eq_zero
    (hψ : ∑ a : k, ψ a = 0) (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    {A G : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))} (α : A ⟶ G) [Mono α] (φ : A ⟶ A)
    (hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj G)))
    (h : (fourierTransform k Λ ψ B p₀ j).map ((DerivedCategory.Plus.singleFunctor _ 0).map
      (φ ≫ α)) = 0) : φ = 0 :=
  (cancel_mono α).1 <| by
    let := fourierTransformCommShift k Λ ψ B p₀ j
    have := isTriangulated_fourierTransform k Λ ψ B p₀ j
    rw [Limits.zero_comp]
    exact eq_zero_of_homology_two_fourierTransform_comp_map_eq_zero k Λ ψ B p₀ hψ hq j jQ (φ ≫ α)
      (finite_globalSections_inverseImage_of_mono Λ α hG) hG
      (by rw [Functor.comp_map, h, Functor.map_zero, Functor.map_zero])

end Exact

end Stacks.EtaleCohomology

end
