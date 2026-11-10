module

public import StacksFrontier.AlgebraicGeometry.Perfect.ExtProjectionDegreeIso
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound

/-!
# Assembling the isomorphisms of [Stacks, Tag 0A1F] on quasi-coherent modules

`StacksFrontier/AlgebraicGeometry/Perfect/ExtProjectionDegreeIso.lean` gives, for every object `M`
of
`D(𝒪_S)` with quasi-coherent cohomology, isomorphisms `H^i(S, K ⊗^𝐋 M) ≅ H^i(X, E ⊗^𝐋 R(M))`
compatible with connecting morphisms, for any functor `R` with a shift structure and an
isomorphism `R ≅ 𝒢 ⊗^𝐋 Lf^*(-)`.  This file restricts them to quasi-coherent modules `ℱ` placed
in degree zero, composes them with an identification `R(ℱ[0]) ≅ 𝒢 ⊗_{𝒪_X} f^*ℱ`, natural in `ℱ`,
and shows that the connecting morphisms of a short exact sequence of quasi-coherent modules are
respected as soon as that identification carries the image under `R` of the distinguished
triangle of the sequence to the distinguished triangle of the short exact sequence of complexes
`0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0`.

## Main results

* `Stacks.Cohomology.ExtProjectionAssembly.hasQuasicoherentCohomology_single`
* `Stacks.Cohomology.ExtProjectionAssembly.exists_isos_of_model`: the isomorphisms and their
  compatibility with connecting morphisms, from a model `R` of `𝒢 ⊗^𝐋 Lf^*(-)` together with the
  identification on modules and its compatibility with triangles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Pretriangulated
open StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedSectionsLeray (derivedSectionsOverOpen derivedPreimageSections)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.SupportedProjectionFormula (DX HasQuasicoherentCohomology)
open Stacks.Cohomology.ExtProjectionDegreeIso

universe u

namespace Stacks.Cohomology.ExtProjectionAssembly

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

/-- `𝒪_S`-modules, at the spelling of the derived tensor product. -/
abbrev ModS (S : Scheme.{u}) := Stacks.DerivedTensor.RingedSite.Modules S.toRingedSpace.sheaf

/-- The quasi-coherent `𝒪_S`-modules. -/
abbrev qcModules (S : Scheme.{u}) : ObjectProperty (ModS S) :=
  fun F => (F : S.Modules).IsQuasicoherent

/-- **A quasi-coherent module placed in degree `0` has quasi-coherent cohomology sheaves.** -/
theorem hasQuasicoherentCohomology_single {S : Scheme.{u}} (F : ModS S) (hF : qcModules S F) :
    HasQuasicoherentCohomology
      (((DerivedCategory.singleFunctor (ModS S) 0).obj F : DT S) : DX S) := by
  intro j
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor (ModS S) 0).obj F) 0 j
        hj).isoZero.symm (AlgebraicGeometry.isQuasicoherent_zero S)
  · exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModS S) 0).app F).symm hF
  · exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor (ModS S) 0).obj F) 0 j
        hj).isoZero.symm (AlgebraicGeometry.isQuasicoherent_zero S)

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
  (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)

/-- `ℱ ↦ 𝒢 ⊗_{𝒪_X} f^*ℱ`, the degreewise tensor product of [Stacks, Tag 0A1F]. -/
abbrev Ψ :
    ModS S ⥤ CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ :=
  RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom ⋙
    Stacks.Cohomology.ExtProjectionFormula.tensorModuleComplex X G

/-- **The isomorphisms of [Stacks, Tag 0A1F], from a model of `𝒢 ⊗^𝐋 Lf^*(-)`.**  Let `R` be a
functor `D(𝒪_S) ⥤ D(𝒪_X)` with a shift structure and an isomorphism `μ : R ≅ 𝒢 ⊗^𝐋 Lf^*(-)`,
let `ν : R(ℱ[0]) ≅ 𝒢 ⊗ f^*ℱ` naturally in the `𝒪_S`-module `ℱ`, and suppose that for every short
exact sequence of `𝒪_S`-modules some morphism from the image under `R` of its distinguished
triangle to the distinguished triangle of `0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0` has `ν` as
its first and third components.  Then there are isomorphisms
`H^i(S, K ⊗^𝐋 ℱ) ≅ H^i(X, E ⊗^𝐋 (𝒢 ⊗ f^*ℱ))`, natural in the quasi-coherent `ℱ`, compatible with
the connecting morphisms of short exact sequences of quasi-coherent modules. -/
theorem exists_isos_of_model [IsNoetherian S] [LocallyOfFiniteType f]
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hG : PerfectPushforward.FlatProperSupportComplex f G)
    (R : DT S ⥤ DT X) [R.CommShift ℤ] (μ : R ≅ pullbackTensorG f G)
    [(Ψ f G).PreservesZeroMorphisms]
    (hΨ : ∀ T : ShortComplex (ModS S), T.ShortExact → (T.map (Ψ f G)).ShortExact)
    (ν : DerivedCategory.singleFunctor (ModS S) 0 ⋙ R ≅ Ψ f G ⋙ DerivedCategory.Q)
    (hTri : ∀ (T : ShortComplex (ModS S)) (hT : T.ShortExact),
      ∃ φ : R.mapTriangle.obj hT.singleTriangle ⟶ DerivedCategory.triangleOfSES (hΨ T hT),
        φ.hom₁ = ν.hom.app T.X₁ ∧ φ.hom₃ = ν.hom.app T.X₃) :
    ∃ Φ : ∀ i : ℤ, (qcModules S).ι ⋙ DerivedCategory.singleFunctor (ModS S) 0 ⋙
          (derivedTensorProductFunctor S.toRingedSpace.sheaf).obj (Kobj f E G) ⋙
          derivedSectionsOverOpen S.toRingedSpace ⊤ ⋙ DerivedCategory.homologyFunctor _ i ≅
        (qcModules S).ι ⋙ Ψ f G ⋙ DerivedCategory.Q ⋙
          (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E ⋙
          derivedPreimageSections f.toLRSHom.toShHom ⊤ ⋙ DerivedCategory.homologyFunctor _ i,
      ∀ (T : ShortComplex (ModS S)) (hT : T.ShortExact) (h₁ : qcModules S T.X₁)
        (h₃ : qcModules S T.X₃) (i : ℤ),
        (Φ i).hom.app ⟨T.X₃, h₃⟩ ≫
          (H0 (S := S)).homologySequenceδ
            ((sourceSections f E).mapTriangle.obj (DerivedCategory.triangleOfSES (hΨ T hT)))
            i (i + 1) rfl =
        (H0 (S := S)).homologySequenceδ
            ((sectionsS (S := S)).mapTriangle.obj
              ((tensorK f E G).mapTriangle.obj hT.singleTriangle))
            i (i + 1) rfl ≫
          (Φ (i + 1)).hom.app ⟨T.X₁, h₁⟩ := by
  obtain ⟨Z, hZp, hsupp⟩ := hG.properSupport
  obtain ⟨U, hZU, i₁, i₂, i₃, i₄⟩ := ExtProjectionSetup.exists_supportOpen f Z hZp
  have hN := ExtProjectionSetup.cohomologySupportedOn_derivedTensorG E G hE (Z : Set X) hsupp
  have hNq := ExtProjectionSetup.hasQuasicoherentCohomology_derivedTensorG f E G hE hG
  have hZ : IsClosed (Z : Set X) := Z.isClosed
  have hβ : ∀ (F : ModS S) (hF : qcModules S F) (i : ℤ),
      IsIso ((betaT f E G U hZ hZU hN R μ).app
        (((DerivedCategory.singleFunctor (ModS S) 0).obj F)⟦i⟧)) := fun F hF i =>
    isIso_betaT_app f E G U hZ hZU hN R μ hNq _
      (hasQuasicoherentCohomology_shift (hasQuasicoherentCohomology_single F hF) i)
  have hα : ∀ (F : ModS S) (hF : qcModules S F) (i : ℤ),
      IsIso ((alphaT f E G U hZ hZU hN).app
        (((DerivedCategory.singleFunctor (ModS S) 0).obj F)⟦i⟧)) := fun F hF i =>
    isIso_alphaT_app f E G U hZ hZU hN hNq _
      (hasQuasicoherentCohomology_shift (hasQuasicoherentCohomology_single F hF) i)
  have ht : ∀ i (F : (qcModules S).FullSubcategory),
      IsIso (degreeMap f E G U hZ hZU hN R μ i
        ((DerivedCategory.singleFunctor (ModS S) 0).obj F.obj) (hβ F.obj F.property i)) :=
    fun i F => isIso_degreeMap f E G U hZ hZU hN R μ i _ (hα F.obj F.property i) _
  have hδc : ∀ (T : ShortComplex (ModS S)) (hT : T.ShortExact) (h₁ : qcModules S T.X₁)
      (h₃ : qcModules S T.X₃) (i : ℤ),
      (degreeMap f E G U hZ hZU hN R μ i ((DerivedCategory.singleFunctor (ModS S) 0).obj T.X₃)
          (hβ T.X₃ h₃ i) ≫ ((sourceCohomology f E).shift i).map (ν.hom.app T.X₃)) ≫
        (H0 (S := S)).homologySequenceδ
          ((sourceSections f E).mapTriangle.obj (DerivedCategory.triangleOfSES (hΨ T hT)))
          i (i + 1) rfl =
      (H0 (S := S)).homologySequenceδ
          ((sectionsS (S := S)).mapTriangle.obj ((tensorK f E G).mapTriangle.obj hT.singleTriangle))
          i (i + 1) rfl ≫
        (degreeMap f E G U hZ hZU hN R μ (i + 1)
          ((DerivedCategory.singleFunctor (ModS S) 0).obj T.X₁) (hβ T.X₁ h₁ (i + 1)) ≫
          ((sourceCohomology f E).shift (i + 1)).map (ν.hom.app T.X₁)) := by
    intro T hT h₁ h₃ i
    have hφ₁ := (hTri T hT).choose_spec.1
    have hφ₃ := (hTri T hT).choose_spec.2
    have e₃ : IsIso ((betaT f E G U hZ hZU hN R μ).app ((hT.singleTriangle.obj₃)⟦i⟧)) :=
      hβ T.X₃ h₃ i
    have e₁ : IsIso ((betaT f E G U hZ hZU hN R μ).app ((hT.singleTriangle.obj₁)⟦i + 1⟧)) :=
      hβ T.X₁ h₁ (i + 1)
    have hδ : degreeMap f E G U hZ hZU hN R μ i
          ((DerivedCategory.singleFunctor (ModS S) 0).obj T.X₃) (hβ T.X₃ h₃ i) ≫
          (sourceCohomology f E).homologySequenceδ (R.mapTriangle.obj hT.singleTriangle) i (i + 1)
            rfl =
        (baseCohomology (S := S)).homologySequenceδ ((tensorK f E G).mapTriangle.obj
            hT.singleTriangle) i (i + 1) rfl ≫
          degreeMap f E G U hZ hZU hN R μ (i + 1)
            ((DerivedCategory.singleFunctor (ModS S) 0).obj T.X₁) (hβ T.X₁ h₁ (i + 1)) :=
      degreeMap_comp_homologySequenceδ f E G U hZ hZU hN R μ hT.singleTriangle i (i + 1) rfl e₃ e₁
    have hnat :=
      (sourceCohomology f E).homologySequenceδ_naturality (hTri T hT).choose i (i + 1) rfl
    rw [hφ₁, hφ₃] at hnat
    rw [Functor.homologySequenceδ_leftComp (sourceSections f E) (H0 (S := S))
      (DerivedCategory.triangleOfSES (hΨ T hT))] at hnat
    rw [Functor.homologySequenceδ_leftComp (sectionsS (S := S)) (H0 (S := S))
      ((tensorK f E G).mapTriangle.obj hT.singleTriangle)] at hδ
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun x => degreeMap f E G U hZ hZU hN R μ i
          ((DerivedCategory.singleFunctor (ModS S) 0).obj T.X₃) (hβ T.X₃ h₃ i) ≫ x) hnat).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun x => x ≫ ((sourceCohomology f E).shift (i + 1)).map (ν.hom.app T.X₁))
            hδ).trans (Category.assoc _ _ _))))
  refine ⟨fun i => NatIso.ofComponents (fun F =>
      (@asIso _ _ _ _ (degreeMap f E G U hZ hZU hN R μ i
        ((DerivedCategory.singleFunctor (ModS S) 0).obj F.obj) (hβ F.obj F.property i)) (ht i F)) ≪≫
      ((sourceCohomology f E).shift i).mapIso (ν.app F.obj)) ?_, ?_⟩
  · intro F F' φ
    have h₁ := degreeMap_naturality f E G U hZ hZU hN R μ i
      ((DerivedCategory.singleFunctor (ModS S) 0).map φ.hom) (hβ F.obj F.property i)
      (hβ F'.obj F'.property i)
    have h₂ := ν.hom.naturality φ.hom
    simp only [Functor.comp_obj, Functor.comp_map] at h₂
    have h₃ := congrArg (· ≫ ((sourceCohomology f E).shift i).map (ν.hom.app F'.obj)) h₁
    simp only [Category.assoc, ← Functor.map_comp, h₂] at h₃
    simp only [Functor.map_comp] at h₃ ⊢
    exact h₃
  · intro T hT h₁ h₃ i
    exact hδc T hT h₁ h₃ i

end Stacks.Cohomology.ExtProjectionAssembly

end
