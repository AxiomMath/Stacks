module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleAffineUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffIndexEmptyLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelAffinePushforwardAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointProductsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointRelocalizeMap

/-!
# Pseudo-coherence of `RΓ` from a Noetherian model over `Spec ℤ`

Let `f : X ⟶ T` be a proper, flat morphism of finite presentation from an algebraic space over
the terminal scheme to an affine scheme `T = Spec R`. The proof of Stacks 0CTM writes
`R = colim Rᵢ` over its finitely generated `ℤ`-subalgebras, descends `f` to a proper, flat
morphism of finite presentation `fᵢ : Xᵢ ⟶ Tᵢ = Spec Rᵢ` with `X = Xᵢ ×_{Tᵢ} T` (Stacks 07SK,
08K0, 08K1), descends a perfect object `P` of `D(𝒪_X)` to a perfect `Pᵢ` with `Lgᵢ^*Pᵢ ≅ P`
along the projection `gᵢ : X ⟶ Xᵢ` (Stacks 09RJ), and uses that `RΓ(Xᵢ, Pᵢ^∨)` is perfect
over the Noetherian ring `Rᵢ` (Stacks 08AR and 066E), together with affine base change
`Rgᵢ_* Lf^*(M[0]) ≅ Lfᵢ^*((M as an `Rᵢ`-module)[0])` (Stacks 073H and 07U8). This file assembles
these inputs into the hypothesis of
`isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_baseChangeModels`.

## Main results

* `isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_noetherianModels`: `RΓ(X, E)` is
  pseudo-coherent over `R` for every perfect `E`, given the descent of perfect objects along the
  approximating system (`hdescent`) and the underived affine base change on the models of the
  spaces-étale sites (`hbc`).
* `isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_noetherianModels`: the same inputs
  give perfectness of `Rf_*E` on the point over any base scheme.

Both inputs are intermediate steps of the formalization of Stacks 0CTM; nothing here is
registered.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

attribute [local instance] hasCoproducts_derivedCategory_point
  hasCoproducts_derivedCategory_spacesEtaleModel

/-- **`RΓ(X, E)` is pseudo-coherent over `R`, from a Noetherian model.** Let `f : X ⟶ T` be
proper, flat and of finite presentation over the terminal scheme, with `T` affine and
`R = Γ(T, 𝒪_T)`. Suppose that perfect objects descend along every approximating system with
bounded charts (`hdescent`, the essential surjectivity half of Stacks 09RJ) and that for every
cartesian square `X = X₀ ×_{T₀} T` over a morphism `j : T ⟶ T₀` of affines the underived base
change `g_*(𝒪_X ⊗_R M) ≅ 𝒪_{X₀} ⊗_{R₀} M` holds naturally in `M` on the models (`hbc`). Then the
image of `Rf_*E` in `D(R)` is pseudo-coherent for every perfect `E`. -/
theorem isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_noetherianModels
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hdescent : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), ChartsBounded B _ hZ D.system →
      ∀ E : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).Modules,
        (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).toRingedSite.IsPerfect E →
        ∃ (i : I) (_ : D.base ≤ i) (Eᵢ : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).Modules),
          (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).toRingedSite.IsPerfect Eᵢ ∧
          Nonempty ((derivedPullback (spacesEtaleModelHom B _ hZ
            (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E))
    (hbc : ∀ (X X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ) (T T₀ : BigFppfOver B _ hZ)
      (f : X ⟶ schemeSpace T) (f₀ : X₀ ⟶ schemeSpace T₀) (g : X ⟶ X₀) (j : T ⟶ T₀),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj T) →
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj T₀) →
      IsPullback g.hom f.hom f₀.hom (yoneda.map j) →
      Nonempty (((baseRingPointModulesEquiv (R := baseRing B _ hZ T)).inverse ⋙
          (spacesEtaleModelToBaseRing B _ hZ X (baseRingHomOfMap f)).pullbackTopos) ⋙
          (spacesEtaleModelHom B _ hZ g).pushforwardTopos ≅
        (ModuleCat.restrictScalars.{u} (baseRingMapOfHom T j) ⋙
          (baseRingPointModulesEquiv (R := baseRing B _ hZ T₀)).inverse) ⋙
          (spacesEtaleModelToBaseRing B _ hZ X₀ (baseRingHomOfMap f₀)).pullbackTopos))
    {X : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ} {T : BigFppfOver B _ hZ}
    (f : X ⟶ schemeSpace T) (hT : IsAffine ((BigFppfOver.toScheme B _ hZ).obj T))
    (hf : IsProper B _ hZ f.hom) (hflat : IsFlat B _ hZ f.hom)
    (hfp : IsFinitePresentation B _ hZ f.hom)
    (E : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ X).Modules)
    (hE : (spacesEtaleModelRingedTopos B _ hZ X).toRingedSite.IsPerfect E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((pointDerivedEquiv (R := baseRing B _ hZ T)).functor.obj
        ((derivedPushforward (spacesEtaleModelToBaseRing B _ hZ X (baseRingHomOfMap f))).obj
          E)) := by
  have hXqcqs := qcqs_of_isFinitePresentation_schemeSpace hZ f hT hfp
  refine isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_baseChangeModels hZ f hflat hT
    hXqcqs.1 hXqcqs.2 (fun P hP => ?_) E hE
  obtain ⟨I, _, _, D, π, Tsys, tπ, fsys, hlim, hb, -, hNoeth, hprops, hpb, -⟩ :=
    exists_descentSituation_noetherianApproximation (B := B) ⟨T, hT⟩ X.1 X.2 f.hom hfp hflat hf
  have key : ∀ c : Cone D.system, D.limitCone = c → ∀ hc : IsAlgebraicSpace B _ hZ c.pt,
      ∀ E : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ ⟨c.pt, hc⟩).Modules,
        (spacesEtaleModelRingedTopos B _ hZ ⟨c.pt, hc⟩).toRingedSite.IsPerfect E →
        ∃ (i : I) (Eᵢ : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).Modules),
          (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).toRingedSite.IsPerfect Eᵢ ∧
          Nonempty ((derivedPullback (spacesEtaleModelHom B _ hZ
            (ObjectProperty.homMk (c.π.app (op i)) :
              (⟨c.pt, hc⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E) := by
    rintro c rfl hc E hE
    obtain ⟨i, -, Eᵢ, hEᵢ, eP⟩ := hdescent I D hb E hE
    exact ⟨i, Eᵢ, hEᵢ, eP⟩
  obtain ⟨i, Eᵢ, hEᵢ, ⟨eP⟩⟩ := key _ hlim X.2 P hP
  let T₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ := (BigAffineFppf.inclusion B _ _).obj (Tsys.obj (op i))
  let j : T ⟶ T₀ := (BigAffineFppf.inclusion B _ _).map (tπ.app (op i))
  have hT₀ : IsAffine ((BigFppfOver.toScheme B _ hZ).obj T₀) := (Tsys.obj (op i)).property
  let X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨D.system.obj (op i), D.algebraicSpace i⟩
  let f₀ : X₀ ⟶ schemeSpace T₀ := ObjectProperty.homMk (fsys.app (op i))
  let g : X ⟶ X₀ := ObjectProperty.homMk (π.app (op i))
  obtain ⟨hfp₀, hflat₀, hpr₀⟩ := hprops i
  have hX₀ := qcqs_of_isFinitePresentation_schemeSpace hZ f₀ hT₀ hfp₀
  have hj : IsAffineHom B _ hZ (yoneda.map j) := by
    have := hT
    have := hT₀
    exact isAffineHom_yoneda_map_of_isAffineHom _ inferInstance
  have : IsNoetherianRing (baseRing B _ hZ T₀) := hNoeth i
  refine ⟨X₀, T₀, f₀, hflat₀, hT₀, hX₀.1, hX₀.2, g, baseRingMapOfHom T j, Eᵢ, hEᵢ, ⟨eP⟩,
    isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper_of_isNoetherianRing B _ hZ
      hZ hT₀ f₀ hpr₀ hfp₀ hflat₀ _ (RingedSite.isPerfect_derivedDual _ _ hEᵢ), ⟨?_⟩⟩
  exact derivedPushforwardPullbackSingleIso f hflat hT f₀ hflat₀ hT₀ g (baseRingMapOfHom T j)
    (singleDerivedPushforwardPullbackToBaseRingIso B _ hZ f g
      (IsAffineHom.of_isPullback (hpb i).flip hj))
    (hbc X X₀ T T₀ f f₀ g j hT hT₀ (hpb i)).some

/-- **The point form of Stacks 0CTM, from Noetherian models.** Over any base scheme `S`, let
`f : X ⟶ T` be proper, flat and of finite presentation with `T` affine. Given the descent of
perfect objects along approximating systems over `Spec ℤ` (`hdescent`) and the underived affine
base change on the models (`hbc`), `Rf_*E` is perfect on the point `(pt, Γ(T, 𝒪_T))` for every
perfect `E`: reduce to `Spec ℤ`
(`AlgebraicGeometry.Space.isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_integers`)
and apply
`AlgebraicGeometry.Space.isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_noetherianModels`
there. -/
theorem isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_noetherianModels
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hdescent : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), ChartsBounded B _ hZ D.system →
      ∀ E : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).Modules,
        (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).toRingedSite.IsPerfect E →
        ∃ (i : I) (_ : D.base ≤ i) (Eᵢ : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).Modules),
          (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).toRingedSite.IsPerfect Eᵢ ∧
          Nonempty ((derivedPullback (spacesEtaleModelHom B _ hZ
            (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E))
    (hbc : ∀ (X X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ) (T T₀ : BigFppfOver B _ hZ)
      (f : X ⟶ schemeSpace T) (f₀ : X₀ ⟶ schemeSpace T₀) (g : X ⟶ X₀) (j : T ⟶ T₀),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj T) →
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj T₀) →
      IsPullback g.hom f.hom f₀.hom (yoneda.map j) →
      Nonempty (((baseRingPointModulesEquiv (R := baseRing B _ hZ T)).inverse ⋙
          (spacesEtaleModelToBaseRing B _ hZ X (baseRingHomOfMap f)).pullbackTopos) ⋙
          (spacesEtaleModelHom B _ hZ g).pushforwardTopos ≅
        (ModuleCat.restrictScalars.{u} (baseRingMapOfHom T j) ⋙
          (baseRingPointModulesEquiv (R := baseRing B _ hZ T₀)).inverse) ⋙
          (spacesEtaleModelToBaseRing B _ hZ X₀ (baseRingHomOfMap f₀)).pullbackTopos))
    {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hflat : IsFlat B S hS f.hom)
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E) :=
  isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_integers B S hS X hZ hT f hf hfp
    hflat (fun _ _ f' hT' hf' hflat' hfp' E' hE' =>
      isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_noetherianModels hZ hdescent hbc f'
        hT' hf' hflat' hfp' E' hE') E hE

end AlgebraicGeometry.Space

end
