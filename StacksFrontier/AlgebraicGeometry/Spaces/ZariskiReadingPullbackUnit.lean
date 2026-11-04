module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleAdjunctionUnitTranspose

/-!
# The base change of the Zariski reading at the structure sheaf

Let `τ : T' ⟶ T` be a morphism of test objects, `φ` the morphism of represented algebraic spaces
and `r` the morphism of schemes it induces.  The base-change map of the Zariski reading
`r^*(R_T 𝒪) ⟶ R_{T'}(φ^*𝒪)` (`AlgebraicGeometry.Space.zariskiReadingPullbackHom`) is, at the
structure sheaf, the canonical identification: read through `𝒪_T ≅ R_T 𝒪`, `φ^*𝒪 ≅ 𝒪` and
`r^*𝒪_T ⟶ 𝒪_{T'}`, it is the identity.  Both sides are checked after transposing along
`r^* ⊣ r_*`, on the sections over the Zariski opens of `T`, where both send a function `f` to
`r^♯ f`.

## Main results

* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_unit_transpose`: the transposed unit law.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_app_unit`: **the unit law**.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The Zariski reading of a morphism into a direct image, preceded by `𝒪_T ⟶ R_T 𝒪` and
followed by the identification of sections of the direct image, on sections. -/
theorem zariskiReadingUnitHom_comp_map_comp_zariskiDirectImageNatTrans_val_app
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (N : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T')))
    (g : SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T)) ⟶
      (testToposHom τ).pushforwardModules.obj N)
    (O : (chartScheme (idEtaleChart B S hS T)).Opensᵒᵖ)
    (r : (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).val.obj O) :
    (zariskiReadingUnitHom T ≫ (zariskiReadingFunctor T).map g ≫
        (zariskiDirectImageNatTrans τ).app N).val.app O r =
      directImageSelfOpensModuleSection τ O.unop N
        (g.val.app _ ((selfOpensStructureMap B S hS T).hom.app O r)) := by
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  exact (SheafOfModules.comp_val_app_apply _ _ _ _)

/-- The identification of sections of a direct image, at the structure map of `φ`. -/
theorem directImageSelfOpensModuleSection_pushforwardStructureProjection
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (r : Γ((BigFppfOver.toScheme B S hS).obj T, O)) :
    directImageSelfOpensModuleSection τ O
        (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T')))
        ((pushforwardStructureProjection B S hS (representedSpaceMap B S hS τ)).val.app _
          ((selfOpensStructureMap B S hS T).hom.app (op O) r)) =
      (selfOpensStructureMap B S hS T').hom.app (op (preimageOpens τ O))
        (((BigFppfOver.toScheme B S hS).map τ).app O r) :=
  directImageSelfOpensSection_structureSharp τ O r

/-- The transposed unit law of the base change of the Zariski reading, at the level of
morphisms: the unit followed by the direct image of `φ^*𝒪 ≅ 𝒪` is the transpose of the
latter. -/
theorem zariskiReadingPullbackHom_unit_transpose_eq {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) :
    zariskiReadingUnitHom T ≫
        (zariskiReadingFunctor T).map
          ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app
            (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T)))) ≫
        (zariskiDirectImageNatTrans τ).app _ ≫
        (Stacks.RingedSpace.pushforwardFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          ((zariskiReadingFunctor T').map
            (modulePullbackUnitIso B S hS (representedSpaceMap B S hS τ)).hom) =
      zariskiReadingUnitHom T ≫
        (zariskiReadingFunctor T).map
          ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv
            _ _ (modulePullbackUnitIso B S hS (representedSpaceMap B S hS τ)).hom) ≫
        (zariskiDirectImageNatTrans τ).app _ := by
  have hn := (zariskiDirectImageNatTrans τ).naturality
    (modulePullbackUnitIso B S hS (representedSpaceMap B S hS τ)).hom
  have hu := (etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv_unit
    (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T))) _
    (modulePullbackUnitIso B S hS (representedSpaceMap B S hS τ)).hom
  refine (congrArg (fun k => zariskiReadingUnitHom T ≫ (zariskiReadingFunctor T).map
    ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app
        (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T)))) ≫ k)
      hn.symm).trans ?_
  refine congrArg (zariskiReadingUnitHom T ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg (· ≫ _) ?_
  exact ((zariskiReadingFunctor T).map_comp _ _).symm.trans
    (congrArg (zariskiReadingFunctor T).map hu.symm)

/-- The transposed unit law of the base change of the Zariski reading. -/
theorem zariskiReadingPullbackHom_unit_transpose {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) :
    zariskiReadingUnitHom T ≫
        (zariskiReadingFunctor T).map
          ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app
            (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T)))) ≫
        (zariskiDirectImageNatTrans τ).app _ ≫
        (Stacks.RingedSpace.pushforwardFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          ((zariskiReadingFunctor T').map
            (modulePullbackUnitIso B S hS (representedSpaceMap B S hS τ)).hom) =
      RingedSpaceModuleAdjunction.structureSheafModuleHom
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)) ≫
        (Stacks.RingedSpace.pushforwardFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          (zariskiReadingUnitHom T') := by
  refine (zariskiReadingPullbackHom_unit_transpose_eq τ).trans ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun O =>
    ModuleCat.hom_ext (LinearMap.ext fun r => ?_))
  refine (zariskiReadingUnitHom_comp_map_comp_zariskiDirectImageNatTrans_val_app τ _ _ O r).trans ?_
  have key := etaleModuleAdjunction_homEquiv_modulePullbackUnitIso_val_app
    (representedSpaceMap B S hS τ) (op ((selfOpensFunctor B S hS T).obj O.unop))
    ((selfOpensStructureMap B S hS T).hom.app O r)
  refine (congrArg (directImageSelfOpensModuleSection τ O.unop _) key).trans ?_
  refine (directImageSelfOpensModuleSection_pushforwardStructureProjection τ O.unop r).trans ?_
  exact (SheafOfModules.comp_val_app_apply (RingedSpaceModuleAdjunction.structureSheafModuleHom
    (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)))
    ((Stacks.RingedSpace.pushforwardFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
      (zariskiReadingUnitHom T')) O r).symm

/-- **The unit law of the base change of the Zariski reading**: at the structure sheaf, read
through `𝒪_T ≅ R_T 𝒪`, `φ^*𝒪 ≅ 𝒪` and `𝒪_{T'} ≅ R_{T'} 𝒪`, the base-change map
`r^*(R_T 𝒪) ⟶ R_{T'}(φ^*𝒪)` is the canonical map `r^*𝒪_T ⟶ 𝒪_{T'}`. -/
theorem zariskiReadingPullbackHom_app_unit {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) :
    (Stacks.RingedSpace.pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          (zariskiReadingUnitHom T) ≫
        (zariskiReadingPullbackHom τ).app
          (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T))) ≫
        (zariskiReadingFunctor T').map
          (modulePullbackUnitIso B S hS (representedSpaceMap B S hS τ)).hom =
      RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)) ≫
        zariskiReadingUnitHom T' := by
  refine ((Stacks.RingedSpace.pullbackAdjunction
    (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).injective ?_
  refine ((Stacks.RingedSpace.pullbackAdjunction _).homEquiv_naturality_left _ _).trans ?_
  refine Eq.trans ?_ ((Stacks.RingedSpace.pullbackAdjunction _).homEquiv_naturality_right _ _).symm
  refine Eq.trans ?_ (congrArg (· ≫ _)
    (RingedSpaceModuleAdjunction.homEquiv_modulePullbackUnitToUnit _).symm)
  refine Eq.trans ?_ (zariskiReadingPullbackHom_unit_transpose τ)
  refine congrArg (zariskiReadingUnitHom T ≫ ·) ?_
  refine ((Stacks.RingedSpace.pullbackAdjunction _).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) rfl)

end AlgebraicGeometry.Space

end
