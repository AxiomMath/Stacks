module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsPseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.Homology.DerivedCategory.PerfectApproximation
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Triangle
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactnessGeneral
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.PerfectToPseudoCoherentGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections

/-!
# Pseudo-coherence of `RΓ(X, E ⊗^L K)` from perfect to pseudo-coherent `E`

Let `U = Spec A` be affine, `X` a quasi-compact and quasi-separated algebraic space over `U` and
`K ∈ D⁻_QCoh(𝒪_X)`. If `RΓ(X, E ⊗^L K)` is a pseudo-coherent object of `D(A)` for every perfect
`E`, then it is for every pseudo-coherent `E` (Stacks 0CWH). Here `RΓ(X, -) = RΓ(U, Rf_* -)`.

## Main results

* `AlgebraicGeometry.Space.exists_isZero_homology_representedAffineDerivedSections_of_isLE`:
  `RΓ(X, -) : D_QCoh(𝒪_X) ⥤ D(A)` has finite cohomological dimension.
* `AlgebraicGeometry.Space.isPseudoCoherent_representedAffineDerivedSections_tensor`:
  **Stacks 0CWH**.

## References

* [Stacks Project, Tag 0CWH](https://stacks.math.columbia.edu/tag/0CWH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The representable algebraic space of an affine object of the site is quasi-compact and
quasi-separated. -/
theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_yoneda_of_isAffine :
    IsQuasiCompactSpace B S hS (yoneda.obj U) ∧
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (yoneda.obj U) := by
  refine ⟨isQuasiCompactSpace_yoneda_of_isAffine B S hS U inferInstance, ?_⟩
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS B.contains_terminal
    (X := yoneda.obj U) ⟨U, inferInstance, ⟨Functor.representableByEquiv.symm (Iso.refl _)⟩⟩

/-- **`RΓ(X, -) = RΓ(U, Rf_* -)` has finite cohomological dimension on `D_QCoh(𝒪_X)`** for `X`
quasi-compact and quasi-separated over the affine `U`: there is `N` with `Hⁱ(X, M) = 0` for
`i > a + N` whenever `M ∈ D_QCoh(𝒪_X)` lies in degrees `≤ a`. -/
theorem exists_isZero_homology_representedAffineDerivedSections_of_isLE
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace U)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) :
    ∃ N : ℤ, ∀ M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), QcohDerived B S hS X M →
      ∀ a : ℤ, M.IsLE a → ∀ i : ℤ, a + N < i →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((representedAffineDerivedSections B S hS U).obj
            ((derivedModulePushforward B S hS f).obj M))) := by
  obtain ⟨hUqc, hUqs⟩ :=
    isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_yoneda_of_isAffine (B := B) (S := S)
      (hS := hS) (U := U)
  have hfqc : IsQuasiCompact B S hS f.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal
      (isAlgebraicSpace_yoneda B S hS U) hUqs hXqc f.hom
  have hfqs : IsQuasiSeparated B S hS f.hom :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS B.contains_terminal X.2 hXqs
      f.hom
  obtain ⟨N, hN⟩ := exists_isLE_derivedModulePushforward_obj f hfqc hfqs hUqc
  refine ⟨N, fun M hM a ha i hi => ?_⟩
  refine IsZero.of_iso ?_ (representedAffineDerivedSectionsHomologyIso B S hS U _
    (qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs M hM) i)
  exact (representedAffineSections B S hS U).map_isZero
    ((DerivedCategory.isLE_iff _ (a + N)).1 (hN M hM a ha) i hi)

/-- **Stacks 0CWH.** Let `U = Spec A` be affine and `f : X ⟶ U` with `X` quasi-compact and
quasi-separated, and let `K ∈ D⁻_QCoh(𝒪_X)`. If `RΓ(X, E ⊗^L K)` is pseudo-coherent in `D(A)` for
every perfect `E` in `D(𝒪_X)`, then it is pseudo-coherent in `D(A)` for every pseudo-coherent `E`
in `D(𝒪_X)`. Here `RΓ(X, -)` is `RΓ(U, Rf_* -)`. -/
theorem isPseudoCoherent_representedAffineDerivedSections_tensor
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace U)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hK : QcohDerived B S hS X K)
    (hKb : ∃ b : ℤ, K.IsLE b)
    (h : ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
            (((smallEtaleDerivedTensor B S hS X).obj E).obj K))))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj K))) := by
  obtain ⟨b, hb⟩ := hKb
  obtain ⟨N, hN⟩ := exists_isZero_homology_representedAffineDerivedSections_of_isLE f hXqc hXqs
  obtain ⟨r, hr⟩ := exists_approximatesFrom_of_isPseudoCoherentFrom B S hS X hXqc hXqs
  have hEq : QcohDerived B S hS X E :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE
  rw [StacksDraft.PseudoCoherence.pseudoCoherent_iff_all]
  intro m
  let c : ℤ := m - N - 1 - b
  obtain ⟨P, α, hP, hαiso, hαepi⟩ := hr ⟨E, hEq⟩ c (by
    obtain ⟨L, hL, e⟩ := hE
    exact ⟨L, hL (c - r), e⟩)
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle α
  have hZq : QcohDerived B S hS X Z :=
    (QcohDerived B S hS X).ext_of_isTriangulatedClosed₃ _ hT
      (qcohDerived_of_isPerfect _ _ _ X P hP) hEq
  have hZ : ∀ i : ℤ, c ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj Z) :=
    (DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃ _ hT c).1 ⟨hαiso, hαepi⟩
  have hZle : Z.IsLE (c - 1) := (DerivedCategory.isLE_iff _ _).2 fun i hi => hZ i (by omega)
  let T := smallEtaleDerivedTensorProduct B S hS X
  let : ((smallEtaleDerivedTensor B S hS X).flip.obj K).CommShift ℤ := T.commShift_left K
  have : ((smallEtaleDerivedTensor B S hS X).flip.obj K).IsTriangulated := T.exact_left K
  let := derivedModulePushforward_commShift B S hS f
  have := derivedModulePushforward_isTriangulated B S hS f
  have hT' := (representedAffineDerivedSections B S hS U).map_distinguished _
    ((derivedModulePushforward B S hS f).map_distinguished _
      (((smallEtaleDerivedTensor B S hS X).flip.obj K).map_distinguished _ hT))
  have hZK : (((smallEtaleDerivedTensor B S hS X).obj Z).obj K).IsLE (c - 1 + b) :=
    Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor_general T Z K (c - 1) b
  refine _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m _ hT'
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).1 (h P hP) m) ?_
  refine StacksDraft.PseudoCoherence.isPseudoCoherentFrom_of_homology_isZero _ m fun i hi => ?_
  exact hN _ (qcohDerived_smallEtaleDerivedTensor X Z K hZq hK) (c - 1 + b) hZK i (by omega)

end AlgebraicGeometry.Space

end
