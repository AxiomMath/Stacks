module

public import StacksFrontier.AlgebraicGeometry.Spaces.TensorSingleSectionsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SectionsProjectionUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
public import StacksFrontier.Homology.Tor.StandardModelExtensionScalars
public import StacksFrontier.CategoryTheory.Adjunction.TransposeTensorHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.HomotopyColimitTensorSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums

/-!
# `RΓ(U, K) ⊗^𝐋_R R₀ ⟶ RΓ(U₀, Lj₀^*(F[0]))` for an étale `U ⟶ X` and a closed stage `X₀ ⟶ X`

Let `X` be an algebraic space over an affine `T` (ring `R`), `i : X₀ ⟶ X` an affine morphism over
an affine `T₀ ⟶ T` (ring `R₀`), `F` a quasi-coherent `𝒪_{X₀}`-module, `j : U ⟶ X` quasi-compact and
quasi-separated, and `U₀ = U ×_X X₀` with projections `j₀ : U₀ ⟶ X₀`, `i' : U₀ ⟶ U`. For a map
`φ : K ⟶ (i_*F)[0]` in `D(𝒪_X)` this file builds

* `ψ_U : RΓ_R(U, Lj^*((i_*F)[0])) ⟶ RΓ_{R₀}(U₀, Lj₀^*(F[0]))` (read in `D(R)`), through `X` and
  `X₀`: the inverse of the projection formula at the unit `RΓ(X, Rj_*𝒪_U ⊗^𝐋 -) ≅ RΓ(U, Lj^* -)`
  ([Stacks, Tag 08IN]), `ψ_i` at `Rj_*𝒪_U` (`tensorSingleSectionsNatTrans`), the base change map
  `Li^*Rj_*𝒪_U ⟶ Rj₀_*𝒪_{U₀}` ([Stacks, Tag 08IR]) and the projection formula at the unit for `j₀`;
* the base change map `c_U : RΓ_R(U, Lj^*K) ⊗^𝐋_R R₀ ⟶ RΓ_{R₀}(U₀, Lj₀^*(F[0]))`, the adjoint of
  `RΓ_R(U, Lj^*φ)` followed by `ψ_U`;
* the analogous map `a_E : RΓ_R(X, E ⊗^𝐋 K) ⊗^𝐋_R R₀ ⟶ RΓ_{R₀}(X₀, Li^*E ⊗^𝐋 F[0])` for every
  `E`, the adjoint of `RΓ_R(X, E ⊗^𝐋 φ)` followed by `ψ_i` at `E`.

## Main definitions

* `AlgebraicGeometry.Space.etaleStructurePushforwardMap`: `Li^*Rj_*𝒪_U ⟶ Rj₀_*𝒪_{U₀}`.
* `AlgebraicGeometry.Space.etaleTensorSectionsProjection`: the second half of `ψ_U`.
* `AlgebraicGeometry.Space.etaleTensorSectionsBaseChangeMap`: `c_U`.
* `AlgebraicGeometry.Space.tensorSingleSectionsBaseChangeMap`: `a_E`.

## Main results

* `AlgebraicGeometry.Space.isIso_etaleTensorSectionsBaseChangeMap`: `c_U` is an isomorphism
  when the `a_{Eₘ}` are, for a presentation `Rj_*𝒪_U = hocolim Eₘ` by perfect objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T T₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
  {X X₀ U U₀ : AlgebraicSpaces B S hS}
  (h : X ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
  (h₀ : X₀ ⟶ ⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩)
  (g₀ : T₀ ⟶ T) (i₀ : X₀ ⟶ X) (w₀ : i₀ ≫ h = h₀ ≫ representedSpaceMap B S hS g₀)
  (hi₀ : IsAffineHom B S hS i₀.hom)
  (F : Modules.{u, u} B S hS X₀.1 X₀.2) (hF : F.IsQuasicoherentOnSite)
  (j : U ⟶ X) (j₀ : U₀ ⟶ X₀) (i' : U₀ ⟶ U) (wU : i' ≫ j = j₀ ≫ i₀)
  (hjqc : IsQuasiCompact B S hS j.hom) (hjqs : IsQuasiSeparated B S hS j.hom)
  (hG : QcohDerived B S hS X
    ((DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS i₀).obj F)))
  {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
  (φ : K ⟶ (DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS i₀).obj F))

/-- `Li^*Rj_*𝒪_U ⟶ Rj₀_*𝒪_{U₀}`: the base change map of the square `U₀ = U ×_X X₀` followed by
`L(i')^*𝒪_U ≅ 𝒪_{U₀}`. -/
def etaleStructurePushforwardMap :
    (smallEtaleDerivedModulePullback B S hS i₀).obj
        ((derivedModulePushforward B S hS j).obj (structureDerived U)) ⟶
      (derivedModulePushforward B S hS j₀).obj (structureDerived U₀) :=
  smallEtaleDerivedModuleBaseChangeMap B S hS j i₀ j₀ i' wU (structureDerived U) ≫
    (derivedModulePushforward B S hS j₀).map (smallEtaleDerivedModulePullbackUnitIso i').hom

/-- `π'_F : RΓ_{R₀}(X₀, Li^*Rj_*𝒪_U ⊗^𝐋 F[0]) ⟶ RΓ_{R₀}(U₀, Lj₀^*(F[0]))`:
`etaleStructurePushforwardMap` in the first factor, then the projection formula at the unit for
`j₀` over `T₀` (`sectionsProjectionUnitNatTrans`). -/
def etaleTensorSectionsProjection :
    (representedAffineDerivedSections B S hS T₀).obj
      ((derivedModulePushforward B S hS h₀).obj
        (((smallEtaleDerivedTensor B S hS X₀).obj
          ((smallEtaleDerivedModulePullback B S hS i₀).obj
            ((derivedModulePushforward B S hS j).obj (structureDerived U)))).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) ⟶
      (representedAffineDerivedSections B S hS T₀).obj
        ((derivedModulePushforward B S hS (j₀ ≫ h₀)).obj
          ((smallEtaleDerivedModulePullback B S hS j₀).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS T₀).map
      (((smallEtaleDerivedTensor B S hS X₀).map
        (etaleStructurePushforwardMap B S hS i₀ j j₀ i' wU)).app
          ((DerivedCategory.singleFunctor _ 0).obj F)) ≫
    (sectionsProjectionUnitNatTrans T₀ j₀ h₀).app ((DerivedCategory.singleFunctor _ 0).obj F)

/-- **The base change map `c_U : RΓ_R(U, Lj^*K) ⊗^𝐋_R R₀ ⟶ RΓ_{R₀}(U₀, Lj₀^*(F[0]))`**: the
adjoint, under derived extension and restriction of scalars along `R ⟶ R₀`, of `RΓ_R(U, Lj^*φ)`
followed by `ψ_U`, where `ψ_U` is the inverse of the projection formula at the unit
`RΓ_R(X, Rj_*𝒪_U ⊗^𝐋 -) ≅ RΓ_R(U, Lj^* -)` at `(i_*F)[0]` ([Stacks, Tag 08IN]), then `ψ_i` at
`Rj_*𝒪_U`, then `π'_F` (`CategoryTheory.transposeUnitMap`). -/
def etaleTensorSectionsBaseChangeMap :
    (StacksDraft.ringExtendScalars (representedAffineCommRingCatHom B S hS g₀).hom).obj
      ((derivedModulePushforward B S hS (j ≫ h) ⋙ representedAffineDerivedSections B S hS T).obj
        ((smallEtaleDerivedModulePullback B S hS j).obj K)) ⟶
      (representedAffineDerivedSections B S hS T₀).obj
        ((derivedModulePushforward B S hS (j₀ ≫ h₀)).obj
          ((smallEtaleDerivedModulePullback B S hS j₀).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  transposeUnitMap (smallEtaleDerivedTensor B S hS X)
    (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS T)
    (smallEtaleDerivedModulePullback B S hS j)
    (derivedModulePushforward B S hS (j ≫ h) ⋙ representedAffineDerivedSections B S hS T)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g₀).hom)
    (smallEtaleDerivedModulePullback B S hS i₀ ⋙
      (smallEtaleDerivedTensor B S hS X₀).flip.obj ((DerivedCategory.singleFunctor _ 0).obj F) ⋙
      (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS T₀))
    φ (tensorSingleSectionsNatTrans B S hS h h₀ g₀ i₀ w₀ hi₀ F hF)
    (sectionsProjectionUnitNatTrans T j h)
    (isIso_sectionsProjectionUnitNatTrans_app T j h hjqc hjqs _ hG)
    (etaleTensorSectionsProjection B S hS h₀ i₀ F j j₀ i' wU)

/-- **The base change map `a_E : RΓ_R(X, E ⊗^𝐋 K) ⊗^𝐋_R R₀ ⟶ RΓ_{R₀}(X₀, Li^*E ⊗^𝐋 F[0])`**: the
adjoint of `RΓ_R(X, E ⊗^𝐋 φ)` followed by `ψ_i` at `E` (`CategoryTheory.transposeTensorMap`). -/
def tensorSingleSectionsBaseChangeMap
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (StacksDraft.ringExtendScalars (representedAffineCommRingCatHom B S hS g₀).hom).obj
      ((derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS T).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj K)) ⟶
      (smallEtaleDerivedModulePullback B S hS i₀ ⋙
        (smallEtaleDerivedTensor B S hS X₀).flip.obj ((DerivedCategory.singleFunctor _ 0).obj F) ⋙
        (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS T₀)).obj E :=
  transposeTensorMap (smallEtaleDerivedTensor B S hS X)
    (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS T)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g₀).hom)
    (smallEtaleDerivedModulePullback B S hS i₀ ⋙
      (smallEtaleDerivedTensor B S hS X₀).flip.obj ((DerivedCategory.singleFunctor _ 0).obj F) ⋙
      (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS T₀))
    φ (tensorSingleSectionsNatTrans B S hS h h₀ g₀ i₀ w₀ hi₀ F hF) E

/-- `a_E` unfolded: the adjoint of `RΓ_R(X, E ⊗^𝐋 φ)` followed by `ψ_i` at `E`. -/
theorem tensorSingleSectionsBaseChangeMap_eq
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    tensorSingleSectionsBaseChangeMap B S hS h h₀ g₀ i₀ w₀ hi₀ F hF φ E =
      ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
          (representedAffineCommRingCatHom B S hS g₀).hom).homEquiv
        ((representedAffineDerivedSections B S hS T).obj
          ((derivedModulePushforward B S hS h).obj
            (((smallEtaleDerivedTensor B S hS X).obj E).obj K)))
        ((representedAffineDerivedSections B S hS T₀).obj
          ((derivedModulePushforward B S hS h₀).obj
            (((smallEtaleDerivedTensor B S hS X₀).obj
              ((smallEtaleDerivedModulePullback B S hS i₀).obj E)).obj
              ((DerivedCategory.singleFunctor _ 0).obj F))))).symm
        ((representedAffineDerivedSections B S hS T).map
            ((derivedModulePushforward B S hS h).map
              (((smallEtaleDerivedTensor B S hS X).obj E).map φ)) ≫
          (tensorSingleSectionsNatTrans B S hS h h₀ g₀ i₀ w₀ hi₀ F hF).app E) :=
  rfl

/-- `F[0]` has quasi-coherent cohomology for a quasi-coherent `F`. -/
theorem qcohDerived_singleFunctor_of_isQuasicoherentOnSite {Y : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite) :
    QcohDerived B S hS Y ((DerivedCategory.singleFunctor _ 0).obj M) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm hM
  · rcases lt_or_gt_of_ne hi with h | h
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
        (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor _ 0).obj M) 0 i h)
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
        (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor _ 0).obj M) 0 i h)

include hjqc hjqs hF in
/-- `π'_F` is an isomorphism for a cartesian square `U₀ = U ×_X X₀` with `U` and `X₀` Tor
independent over `X`. -/
theorem isIso_etaleTensorSectionsProjection (sq : IsPullback i' j₀ j i₀)
    (hj₀qc : IsQuasiCompact B S hS j₀.hom) (hj₀qs : IsQuasiSeparated B S hS j₀.hom)
    (hTor : TorIndependent U.2 X₀.2 X.2 j.hom i₀.hom) :
    IsIso (etaleTensorSectionsProjection B S hS h₀ i₀ F j j₀ i' sq.w) := by
  have hbc := isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS j i₀ j₀ i' sq hjqc hjqs
    hTor (structureDerived U) (qcohDerived_singleFunctor_structureModule (X := U.1) (hX := U.2))
  have h₁ : IsIso (etaleStructurePushforwardMap B S hS i₀ j j₀ i' sq.w) :=
    IsIso.comp_isIso' hbc inferInstance
  have h₂ : IsIso ((smallEtaleDerivedTensor B S hS X₀).map
      (etaleStructurePushforwardMap B S hS i₀ j j₀ i' sq.w)) := Functor.map_isIso _ _
  have h₃ : IsIso (((smallEtaleDerivedTensor B S hS X₀).map
      (etaleStructurePushforwardMap B S hS i₀ j j₀ i' sq.w)).app
        ((DerivedCategory.singleFunctor _ 0).obj F)) := NatIso.isIso_app_of_isIso _ _
  exact IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ h₃)
    (isIso_sectionsProjectionUnitNatTrans_app T₀ j₀ h₀ hj₀qc hj₀qs _
      (qcohDerived_singleFunctor_of_isQuasicoherentOnSite B S hS F hF))

/-- **The base change map `c_U` is an isomorphism**, given a homotopy colimit presentation
`Rj_*𝒪_U = hocolim Eₘ` by perfect objects at whose terms the maps `a_{Eₘ}` are isomorphisms. -/
theorem isIso_etaleTensorSectionsBaseChangeMap (sq : IsPullback i' j₀ j i₀)
    (hhqc : IsQuasiCompact B S hS h.hom) (hhqs : IsQuasiSeparated B S hS h.hom)
    (hh₀qc : IsQuasiCompact B S hS h₀.hom) (hh₀qs : IsQuasiSeparated B S hS h₀.hom)
    (hj₀qc : IsQuasiCompact B S hS j₀.hom) (hj₀qs : IsQuasiSeparated B S hS j₀.hom)
    (hTor : TorIndependent U.2 X₀.2 X.2 j.hom i₀.hom) (hK : QcohDerived B S hS X K)
    (E : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : ∀ m, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (E.obj m))
    (c : ∀ m, E.obj m ⟶ (derivedModulePushforward B S hS j).obj (structureDerived U))
    (instE : HasCoproduct E.obj) (hc : haveI := instE; IsHomotopyColimitCocone E c)
    (hiso : ∀ m, IsIso (tensorSingleSectionsBaseChangeMap B S hS h h₀ g₀ i₀ w₀ hi₀ F hF φ
      (E.obj m))) :
    IsIso (etaleTensorSectionsBaseChangeMap B S hS h h₀ g₀ i₀ w₀ hi₀ F hF j j₀ i' sq.w hjqc hjqs
      hG φ) := by
  have := instE
  let R₀ := Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)
  have : HasExactColimitsOfShape ℕ (ModuleCat.{u} R₀) :=
    (AB5OfSize_of_univLE.{0, 0, u, u} (ModuleCat.{u} R₀)).ofShape ℕ
  have : HasCountableCoproducts (DerivedCategory (ModuleCat.{u} R₀)) :=
    derivedCategory_hasCountableCoproducts _ ⟨inferInstance, fun _ _ => ⟨inferInstance,
      inferInstance⟩⟩
  have : ∀ n : ℤ, PreservesColimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R₀) n) := fun n =>
    have := Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor
      (ModuleCat.{u} R₀) (J := ULift.{u} ℕ) n
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  let f₀ := (representedAffineCommRingCatHom B S hS g₀).hom
  let : (StacksDraft.ringExtendScalars f₀).CommShift ℤ :=
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f₀).commShift
  have : (StacksDraft.ringExtendScalars f₀).IsTriangulated :=
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      f₀).isTriangulated
  have := (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
    f₀).leftAdjoint_preservesColimits
  have := (smallEtaleDerivedModuleAdjunction B S hS i₀).leftAdjoint_preservesColimits
  let : (smallEtaleDerivedModulePullback B S hS i₀).CommShift ℤ :=
    commShift_smallEtaleDerivedModulePullback B S hS i₀
  have : (smallEtaleDerivedModulePullback B S hS i₀).IsTriangulated :=
    isTriangulated_smallEtaleDerivedModulePullback B S hS i₀
  have := isIso_sectionsProjectionUnitNatTrans_app T j h hjqc hjqs K hK
  have hπ' := isIso_etaleTensorSectionsProjection B S hS h₀ i₀ F hF j j₀ i' hjqc hjqs sq hj₀qc
    hj₀qs hTor
  have hc₁ := ((isHomotopyColimitCocone_representedAffineDerivedSections_tensor T h hhqc hhqs E hE
    hc K hK).comp_iso (asIso ((sectionsProjectionUnitNatTrans T j h).app K))).map
      (StacksDraft.ringExtendScalars f₀)
  have : HasColimit (Discrete.functor E.obj ⋙ smallEtaleDerivedModulePullback B S hS i₀) :=
    ⟨⟨⟨_, isColimitOfPreserves (smallEtaleDerivedModulePullback B S hS i₀)
      (colimit.isColimit _)⟩⟩⟩
  have : HasCoproduct (E ⋙ smallEtaleDerivedModulePullback B S hS i₀).obj :=
    hasColimit_of_iso (Discrete.compNatIsoDiscrete E.obj
      (smallEtaleDerivedModulePullback B S hS i₀)).symm
  have hcL := hc.map (smallEtaleDerivedModulePullback B S hS i₀)
  have hc₂ := (isHomotopyColimitCocone_representedAffineDerivedSections_tensor T₀ h₀ hh₀qc hh₀qs
    (E ⋙ smallEtaleDerivedModulePullback B S hS i₀)
    (fun m => isPerfect_smallEtaleDerivedModulePullback i₀ _ (hE m)) hcL _
    (qcohDerived_singleFunctor_of_isQuasicoherentOnSite B S hS F hF)).comp_iso
      (@asIso _ _ _ _ (etaleTensorSectionsProjection B S hS h₀ i₀ F j j₀ i' sq.w) hπ')
  exact isIso_transposeUnitMap (Lj := smallEtaleDerivedModulePullback B S hS j)
    (GU := derivedModulePushforward B S hS (j ≫ h) ⋙ representedAffineDerivedSections B S hS T)
    (hπ := isIso_sectionsProjectionUnitNatTrans_app T j h hjqc hjqs _ hG) (hc := hc₁) (hc' := hc₂)
    (hiso := hiso)

end AlgebraicGeometry.Space

end
