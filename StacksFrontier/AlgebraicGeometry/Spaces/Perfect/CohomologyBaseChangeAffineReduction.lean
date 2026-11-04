module

public import StacksFrontier.Algebra.Homology.DerivedCategory.StupidTruncationTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePullbackGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompactQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor

/-!
# Cohomology and base change: reductions in the two variables

Let `f : X ⟶ Y` be a morphism of algebraic spaces. Perfectness of `Rf_*(E ⊗^L 𝒢^•)` is a thick
condition in each variable, which gives two reductions used in the proof of Stacks 0A1P.

* In `𝒢^•`: for a bounded complex it suffices that `Rf_*(E ⊗^L 𝒢ⁿ[-n])` is perfect for every
  `n`, by the stupid filtration.
* In `E`: if `g' : X ⟶ X₀` is affine and `X`, `X₀` are quasi-compact and quasi-separated, it
  suffices that `Rf_*(Lg'^*P₀ ⊗^L 𝒢^•)` is perfect for every perfect `P₀` on `X₀`. Indeed
  `Lg'^*` of a compact generator of `D_QCoh(𝒪_{X₀})` (Stacks 09IY) is a compact generator of
  `D_QCoh(𝒪_X)`, whose thick closure consists of the perfect objects (Stacks 09M8).

## Main results

* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedTensor_of_single`
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedTensor_of_affineHom`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **Dévissage of the coefficient complex.** For a bounded complex `𝒢^•`, `Rf_*(E ⊗^L 𝒢^•)` is
perfect when `Rf_*(E ⊗^L 𝒢ⁿ[-n])` is perfect for every `n`. -/
theorem isPerfect_derivedModulePushforward_derivedTensor_of_single (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite)
    (h : ∀ n : ℤ, RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj
          ((DerivedCategory.singleFunctor _ n).obj (G.X n))))) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) := by
  let T : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
    (smallEtaleDerivedTensor B S hS X).obj E
  let R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) :=
    derivedModulePushforward B S hS f
  let Φ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) := T ⋙ R
  let : T.CommShift ℤ := (smallEtaleDerivedTensorProduct B S hS X).commShift_right E
  let : T.IsTriangulated := (smallEtaleDerivedTensorProduct B S hS X).exact_right E
  let : R.CommShift ℤ := derivedModulePushforward_commShift B S hS f
  let : R.IsTriangulated := derivedModulePushforward_isTriangulated B S hS f
  let : Φ.CommShift ℤ := Functor.CommShift.comp T R
  let : Φ.IsTriangulated := (inferInstance : (T ⋙ R).IsTriangulated)
  have : ((perfectProperty B S hS Y).inverseImage Φ).IsClosedUnderIsomorphisms :=
    ⟨fun e hK => RingedSite.IsPerfect.of_iso _ hK (Φ.mapIso e)⟩
  obtain ⟨hT, -⟩ :=
    @perfectProperty_inverseImage_isTriangulated_isStableUnderRetracts B S hS _ _ _ _ _ _ _ Y Φ
    (inferInstance : Φ.CommShift ℤ) (inferInstance : Φ.IsTriangulated)
  exact Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex_of_distTriang
    ((perfectProperty B S hS Y).inverseImage Φ)
    (fun e hK => RingedSite.IsPerfect.of_iso _ hK (Φ.mapIso e))
    (fun K hK => ((perfectProperty B S hS Y).inverseImage Φ).prop_of_isZero hK)
    (fun T hT₁ h₁ h₃ => ((perfectProperty B S hS Y).inverseImage Φ).ext_of_isTriangulatedClosed₂
      T hT₁ h₁ h₃)
    G hGb h

/-- **Reduction to pullbacks along an affine morphism.** Let `g' : X ⟶ X₀` be affine with `X`
and `X₀` quasi-compact and quasi-separated. If `Rf_*(Lg'^*P₀ ⊗^L 𝒢^•)` is perfect for every
perfect `P₀` on `X₀`, then `Rf_*(E ⊗^L 𝒢^•)` is perfect for every perfect `E` on `X`. -/
theorem isPerfect_derivedModulePushforward_derivedTensor_of_affineHom {X₀ : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g' : X ⟶ X₀) (hg' : IsAffineHom B S hS g'.hom)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hX₀qc : IsQuasiCompactSpace B S hS X₀.1)
    (hX₀qs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X₀.1)
    (G : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (h : ∀ P₀ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₀)),
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS X₀.1 X₀.2) P₀ →
        RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
          ((derivedModulePushforward B S hS f).obj
            (((smallEtaleDerivedTensor B S hS X).obj
              ((smallEtaleDerivedModulePullback B S hS g').obj P₀)).obj G)))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj G)) := by
  let T : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
    (smallEtaleDerivedTensor B S hS X).flip.obj G
  let R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) :=
    derivedModulePushforward B S hS f
  let ι := ObjectProperty.ι (QcohDerived B S hS X)
  let Φ : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) := ι ⋙ T ⋙ R
  let : T.CommShift ℤ := (smallEtaleDerivedTensorProduct B S hS X).commShift_left G
  let : T.IsTriangulated := (smallEtaleDerivedTensorProduct B S hS X).exact_left G
  let : R.CommShift ℤ := derivedModulePushforward_commShift B S hS f
  let : R.IsTriangulated := derivedModulePushforward_isTriangulated B S hS f
  let : (T ⋙ R).CommShift ℤ := Functor.CommShift.comp T R
  let : (T ⋙ R).IsTriangulated := inferInstance
  let : Φ.CommShift ℤ := Functor.CommShift.comp ι (T ⋙ R)
  let : Φ.IsTriangulated := (inferInstance : (ι ⋙ T ⋙ R).IsTriangulated)
  obtain ⟨hT, hR⟩ :=
    @perfectProperty_inverseImage_isTriangulated_isStableUnderRetracts B S hS _ _ _ _ _ _ _ Y Φ
    (inferInstance : Φ.CommShift ℤ) (inferInstance : Φ.IsTriangulated)
  obtain ⟨G₀, hc, hg⟩ := exists_isCompactObject_isWeakTriangulatedGenerator_of_qcqs B S hS
    B.contains_terminal X₀ hX₀qc hX₀qs
  obtain ⟨hc', hg''⟩ :=
    isCompactObject_and_isWeakTriangulatedGenerator_quasicoherentDerivedModulePullback g' hg' G₀
      hc hg
  have := hT
  have := hR
  exact prop_of_isCompactObject_of_isWeakTriangulatedGenerator _ hc' hg''
    ((perfectProperty B S hS Y).inverseImage Φ)
    (h G₀.obj (isPerfect_of_isCompactObject X₀ hX₀qs G₀ hc))
    ⟨E, qcohDerived_of_isPerfect_derivedCategoryB X E hE⟩
    (isCompactObject_of_isPerfect X hXqc hXqs _ hE)

end AlgebraicGeometry.Space

end
