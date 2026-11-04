module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.BaseChange
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFromGlobalSections
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOpenLocality
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseOpen
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectGlobalSectionsAffineBase
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfectPushforward

/-!
# The relative dualizing complex is relatively perfect

Let `Y` be quasi-compact and quasi-separated and `f : X ⟶ Y` proper, flat and of finite
presentation, with relative dualizing complex `ω_{X/Y} = a(𝒪_Y)` ([Stacks, Remark 0B6S]). Then
`ω_{X/Y}` is `Y`-perfect: [Stacks, Tag 0E4L] (1).

The proof is the source's. Formation of `ω_{X/Y}` commutes with base change
(`Stacks.Duality.StandardModel.pullbackRelativeDualizingComplexIso`) and relative perfectness is
local on the source and on the base, so it suffices to treat `f : X ⟶ Spec A`. For a perfect `E`
the object `Rf_*(E ⊗^L ω)` is the dual of the perfect object `Rf_*E^∨`
(`Stacks.Duality.StandardModel.pushforwardTensorDualIso`), so `RΓ(X, E ⊗^L ω)` is a perfect
object of `D(A)`, and [Stacks, Tag 0GET] concludes.

## Main results

* `Stacks.Duality.StandardModel.isRelativelyPerfect_relativeDualizingComplex_of_spec` — the case
  of an affine base `Spec A`.
* `Stacks.Duality.StandardModel.isRelativelyPerfect_relativeDualizingComplex` —
  **[Stacks, Tag 0E4L] (1)**.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality.StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings StrictlyPerfect.structureModule
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf TopCat.Sheaf

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- Relative perfectness depends only on the isomorphism class of the object. -/
theorem isRelativelyPerfect_of_iso {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] {E E' : DerivedCategory X.Modules} (e : E ≅ E')
    (h : f.IsRelativelyPerfect E) : f.IsRelativelyPerfect E' := by
  obtain ⟨⟨K, hK, ⟨g⟩⟩, h₂⟩ := h
  exact ⟨⟨K, hK, ⟨g ≪≫ e⟩⟩, Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_iso
    ((Scheme.Hom.derivedScalarRestriction f).mapIso e) h₂⟩

section Spec

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

/-- For a perfect `E`, `RΓ(X, E ⊗^L a(𝒪))` is a perfect object of `D(A)`: `Rf_*(E ⊗^L a(𝒪))` is
the dual of the perfect object `Rf_*E^∨`. -/
theorem isPerfect_derivedGlobalSectionsOver_tensor_relativeDualizingComplex
    (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver f).obj
      (((tensor X).obj E).obj (relativeDualizingComplex f).obj)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hP : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec (CommRingCat.of A)).toRingedSpace) ((derivedPushforward f).obj (dual E)) :=
    (ProperFlatBaseChange.isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat f
      ⟨inferInstance, inferInstance, inferInstance⟩ inferInstance inferInstance _
      (Stacks.DerivedQCoh.isPerfect_derivedDual X E hE)).1
  have hT : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec (CommRingCat.of A)).toRingedSpace)
      ((derivedPushforward f).obj (((tensor X).obj E).obj (relativeDualizingComplex f).obj)) :=
    isPerfect_of_iso_scheme (pushforwardTensorDualIso f E hE hP).symm
      (Stacks.DerivedQCoh.isPerfect_derivedDual _ _ hP)
  have hQ := isQuasicoherent_homology_derivedPushforward f
    ⟨((tensor X).obj E).obj (relativeDualizingComplex f).obj,
      AlgebraicGeometry.isQuasicoherent_homology_derivedTensor_obj_obj X _ _
        (isQuasicoherent_homology_of_isPerfect E hE) (relativeDualizingComplex f).property⟩
  exact StacksDraft.Perfect.isPerfect_of_iso
    ((derivedGlobalSectionsOverPushforwardIso f).app _)
    (isPerfect_derivedGlobalSectionsOver_id_of_isPerfect (CommRingCat.of A) _ hT hQ)

/-- **[Stacks, Tag 0E4L] (1) over `Spec A`.** For `f : X ⟶ Spec A` proper, flat and of finite
presentation, `a(𝒪)` is `Spec(A)`-perfect. -/
theorem isRelativelyPerfect_relativeDualizingComplex_of_spec :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    f.IsRelativelyPerfect (relativeDualizingComplex f).obj := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact Scheme.Hom.isRelativelyPerfect_of_isPerfect_derivedGlobalSectionsOver_tensor f _
    (relativeDualizingComplex f).property
    (isPerfect_derivedGlobalSectionsOver_tensor_relativeDualizingComplex f)

end Spec

/-- **[Stacks, Tag 0E4L] (1).** Let `Y` be a quasi-compact and quasi-separated scheme and
`f : X ⟶ Y` a proper, flat morphism of finite presentation, with relative dualizing complex
`ω_{X/Y} = a(𝒪_Y)` ([Stacks, Remark 0B6S]). Then `ω_{X/Y}` is a `Y`-perfect object of `D(𝒪_X)`.

Over an affine open `V ⊆ Y`, with `Spec Γ(V) ⟶ Y` the inclusion, the base change of `ω_{X/Y}` to
`f⁻¹V ⟶ Spec Γ(V)` is the relative dualizing complex of the base change
(`Stacks.Duality.StandardModel.pullbackRelativeDualizingComplexIso`), which is
`Spec Γ(V)`-perfect (`isRelativelyPerfect_relativeDualizingComplex_of_spec`); relative
perfectness is local on the source and on the base. -/
@[stacks 0E4L "(1)", sga "6 III 4.9.1" "Case S = Y and F = O_Y", sga "6 IV 3.3.2" "3.3.2.4"]
theorem isRelativelyPerfect_relativeDualizingComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    f.IsRelativelyPerfect (relativeDualizingComplex f).obj := by
  refine Scheme.Hom.isPerfectRelativeTo_of_iSup_eq_top f (fun W : Y.affineOpens => f ⁻¹ᵁ W.1)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) f.base.1) _ fun W => ?_
  have : IsAffine W.1.toScheme := W.2
  let e := W.1.toScheme.isoSpec
  let j : Spec Γ(W.1.toScheme, ⊤) ⟶ Y := e.inv ≫ W.1.ι
  let f' : (f ⁻¹ᵁ W.1).toScheme ⟶ Spec Γ(W.1.toScheme, ⊤) := (f ∣_ W.1) ≫ e.hom
  have sq₁ := (isPullback_morphismRestrict f W.1).flip
  have sq₂ : IsPullback (𝟙 _) f' (f ∣_ W.1) e.inv :=
    IsPullback.of_horiz_isIso ⟨by simp [f']⟩
  have sq : IsPullback (f ⁻¹ᵁ W.1).ι f' f j := by
    simpa using sq₂.paste_horiz sq₁
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have : Flat f' := MorphismProperty.of_isPullback sq inferInstance
  have : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback sq inferInstance
  have : CompactSpace (f ⁻¹ᵁ W.1).toScheme := compactSpace_of_isPullback sq₁
  exact (Scheme.Hom.isPerfectRelativeTo_baseOpen_iff f' j sq.w.symm _).2 <|
    isRelativelyPerfect_of_iso f' (pullbackRelativeDualizingComplexIso sq).symm
      (@isRelativelyPerfect_relativeDualizingComplex_of_spec Γ(W.1.toScheme, ⊤) _ _ f'
        ‹IsProper f'› ‹Flat f'› ‹LocallyOfFinitePresentation f'›)

/-- **[Stacks, Tag 0E4L] (1)** in the spelling `Scheme.Hom.IsPerfectRelativeTo` at the canonical
family of derived tensor products, the form of [Stacks, Definition 0E2T]. -/
theorem isPerfectRelativeTo_relativeDualizingComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
      (RingedSpace.inverseImage Y.toRingedSpace f.base)) (relativeDualizingComplex f).obj :=
  isRelativelyPerfect_relativeDualizingComplex f

end Stacks.Duality.StandardModel

end
