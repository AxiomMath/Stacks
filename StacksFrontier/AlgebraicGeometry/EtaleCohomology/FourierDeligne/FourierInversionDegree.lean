module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionKernel
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierAntidiagonalCoordinates
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RelativeAffineLineCompactSupport

/-!
# The composite of two Fourier transforms is a sheaf in degree two, and detects zero

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with `∑ ψ = 0` and `Φ` the Fourier transform on `D⁺(𝔸¹_k, Λ)`. For a
sheaf `F` on `𝔸¹_k` with finite geometric stalks, put
`D(F) = R(u|_{Q_Δ})_!((x|_{Q_Δ})⁻¹ F)` on the antidiagonal `Q_Δ = {x + u = 0}`, so that
`Φ(Φ(F)) ≅ D(F)` (`Stacks.EtaleCohomology.nonempty_fourierTransform_comp_iso`). Then
`Hⁱ(D(F)) = 0` for `i ≠ 2` and `H²(D(F)) = 0` only for `F = 0`, and likewise for `Φ(Φ(F))`.

## Main definitions

* `Stacks.EtaleCohomology.fourierAntidiagonalTransform`: the functor `D`.

## Main results

* `Stacks.EtaleCohomology.isZero_homology_fourierAntidiagonalTransform`: `Hⁱ(D(F)) = 0` for
  `i ≠ 2`.
* `Stacks.EtaleCohomology.isZero_of_isZero_homology_two_fourierAntidiagonalTransform`:
  `H²(D(F)) = 0` only for `F = 0`.
* `Stacks.EtaleCohomology.isZero_homology_fourierTransform_comp`: `Hⁱ(Φ(Φ(F))) = 0` for `i ≠ 2`.
* `Stacks.EtaleCohomology.isZero_of_isZero_homology_two_fourierTransform_comp`: `H²(Φ(Φ(F))) = 0`
  only for `F = 0`.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ]

local notation "𝔸f" => affineLineStructureMap k

/-- **`D(K) = R(u|_{Q_Δ})_!((x|_{Q_Δ})⁻¹ K)`**, the composite of two Fourier transforms on the
antidiagonal `Q_Δ = {x + u = 0}`, through the compactification of `Q_Δ` induced by one of the
triple product. -/
abbrev fourierAntidiagonalTransform
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f))) :
    DerivedCategory.Plus (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) ⥤
      DerivedCategory.Plus (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) :=
  etaleModuleDerivedInverseImagePlus.{u, 0} Λ
      (fourierAntidiagonalι k ≫ tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst 𝔸f 𝔸f) ⋙
    derivedLowerShriek.{u, 0}
      (fourierAntidiagonalι k ≫ tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)
      (jQ.restrictClosed (fourierAntidiagonalι k)) Λ

omit [Fintype k] in
/-- **`D(F) ≅ R pr_!(pr⁻¹(ν⁻¹ F))`**, for `pr : Q_Δ → 𝔸¹_u` the projection and `ν` the negation
of the affine line. -/
theorem nonempty_fourierAntidiagonalTransform_iso (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) :
    Nonempty ((fourierAntidiagonalTransform k Λ jQ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (derivedLowerShriek.{u, 0} (fourierAntidiagonalProjU k)
        (j.baseChange (isPullback_fourierAntidiagonal k)) Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((etaleModuleInverseImage.{u, 0} Λ
          (fourierAntidiagonalProjU k)).obj ((etaleModuleInverseImage.{u, 0} Λ
            (affineLineNeg k)).obj F)))) := by
  let sq := isPullback_fourierAntidiagonal k
  let a := fourierAntidiagonalProjU k
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : LocallyOfFiniteType a :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have : IsSeparated a := MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : QuasiCompact a := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  let I := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ etaleModuleInverseImage.{u, 0} Λ f
  let eF : (I (fourierAntidiagonalProjX k)).obj F ≅ (I a).obj ((I (affineLineNeg k)).obj F) :=
    eqToIso (congrArg (fun m ↦ (etaleModuleInverseImage.{u, 0} Λ m).obj F)
        (fourierAntidiagonalProjX_eq k)) ≪≫
      (etaleModuleInverseImageCompIso Λ a (affineLineNeg k)).app F
  let eK : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (fourierAntidiagonalProjX k)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((I a).obj ((I (affineLineNeg k)).obj F)) :=
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (I (fourierAntidiagonalProjX k)) 0).app F ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso eF
  exact ⟨(derivedLowerShriek.{u, 0} a (jQ.restrictClosed (fourierAntidiagonalι k)) Λ).mapIso eK ≪≫
    (derivedLowerShriekCompactificationIso a (jQ.restrictClosed (fourierAntidiagonalι k))
      (j.baseChange sq) Λ).app ⟨_, isTorsionPlus_of_finite Λ _ _⟩⟩

omit [Fintype k] [Finite Λ] in
/-- The negation of the affine line keeps finite geometric stalks. -/
theorem finite_globalSections_inverseImage_affineLineNeg
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj F)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))) :
    Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ w).obj
        ((etaleModuleInverseImage.{u, 0} Λ (affineLineNeg k)).obj F))) :=
  have := hF Ω (w ≫ affineLineNeg k)
  Finite.of_equiv _ ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).mapIso
    ((etaleModuleInverseImageCompIso Λ w (affineLineNeg k)).app F)).toLinearEquiv.toEquiv

/-- **`Hⁱ(D(F)) = 0` for `i ≠ 2`**, for a sheaf `F` on `𝔸¹_k` with finite geometric stalks. -/
theorem isZero_homology_fourierAntidiagonalTransform (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj F))) (i : ℤ) (hi : i ≠ 2) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((fourierAntidiagonalTransform k Λ jQ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  obtain ⟨e⟩ := nonempty_fourierAntidiagonalTransform_iso k Λ j jQ F
  exact (isZero_homology_derivedLowerShriek_inverseImage_affineLine k Λ hq j 𝔸f
    (isPullback_fourierAntidiagonal k) _ (finite_globalSections_inverseImage_affineLineNeg k Λ F hF)
      i hi).of_iso ((DerivedCategory.Plus.homologyFunctor _ i).mapIso e)

/-- **`H²(D(F)) = 0` only for `F = 0`**, for a sheaf `F` on `𝔸¹_k` with finite geometric stalks. -/
theorem isZero_of_isZero_homology_two_fourierAntidiagonalTransform
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj F)))
    (h : IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((fourierAntidiagonalTransform k Λ jQ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) :
    IsZero F := by
  obtain ⟨e⟩ := nonempty_fourierAntidiagonalTransform_iso k Λ j jQ F
  have hG := isZero_of_isZero_homology_two_derivedLowerShriek_inverseImage_affineLine k Λ hq j 𝔸f
    (isPullback_fourierAntidiagonal k) _ (finite_globalSections_inverseImage_affineLineNeg k Λ F hF)
      (h.of_iso ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso e).symm)
  exact isZero_of_forall_isZero_etaleModuleInverseImage Λ (ι := PUnit.{u + 1})
    (fun _ ↦ affineLineNeg k) (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2
      ⟨PUnit.unit, (Scheme.homeoOfIso (asIso (affineLineNeg k))).surjective x⟩) F fun _ ↦ hG

variable (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- **`Hⁱ(Φ(Φ(F))) = 0` for `i ≠ 2`**, for a sheaf `F` on `𝔸¹_k` with finite geometric stalks:
the composite of two Fourier transforms of a sheaf is a sheaf placed in degree two. -/
theorem isZero_homology_fourierTransform_comp (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj F))) (i : ℤ) (hi : i ≠ 2) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((fourierTransform k Λ ψ B p₀ j ⋙ fourierTransform k Λ ψ B p₀ j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  obtain ⟨e⟩ := nonempty_fourierTransform_comp_iso k Λ ψ B p₀ hψ hq j jQ F hF
  exact (isZero_homology_fourierAntidiagonalTransform k Λ hq j jQ F hF i hi).of_iso
    ((DerivedCategory.Plus.homologyFunctor _ i).mapIso e)

/-- **`H²(Φ(Φ(F))) = 0` only for `F = 0`**, for a sheaf `F` on `𝔸¹_k` with finite geometric
stalks: the composite of two Fourier transforms reflects zero sheaves. -/
theorem isZero_of_isZero_homology_two_fourierTransform_comp (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj F)))
    (h : IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((fourierTransform k Λ ψ B p₀ j ⋙ fourierTransform k Λ ψ B p₀ j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) :
    IsZero F := by
  obtain ⟨e⟩ := nonempty_fourierTransform_comp_iso k Λ ψ B p₀ hψ hq j jQ F hF
  exact isZero_of_isZero_homology_two_fourierAntidiagonalTransform k Λ hq j jQ F hF
    (h.of_iso ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso e).symm)

end Stacks.EtaleCohomology

end
