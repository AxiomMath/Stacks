module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactKernelQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiReadingInvertibleQuotients

/-!
# The conormal module of a closed immersion of represented algebraic spaces

Let `j : Z ⟶ T` be a morphism of the big fppf site over `S` whose scheme morphism is a closed
immersion, and let `φ = yonedaSpaceMap j` be the morphism of represented algebraic spaces.  The
kernel ideal sheaf `𝓘 = Ker(𝒪 ⟶ φ_*𝒪)` lives on the small étale site of `T`; its Zariski
reading `R_T 𝓘` is the ideal sheaf `𝓘_j = Ker(𝒪_T ⟶ j_*𝒪_Z)` of the scheme morphism, because on
the étale chart of a Zariski open `O` the structure map of `φ` is `j^♯ : 𝒪_T(O) ⟶ 𝒪_Z(j⁻¹O)`.
Since `𝓘` is quasi-coherent (Stacks 082Z), the base change isomorphism of the Zariski reading
gives `R_Z(φ^*𝓘) ≅ j^*(R_T 𝓘) ≅ j^*𝓘_j`, which is the conormal sheaf of `j`
(`Stacks.CartierConormal.conormalSheafIsoPullbackSelf`).

## Main definitions

* `AlgebraicGeometry.Space.zariskiReadingKernelIdealIso`: `R_T 𝓘 ≅ 𝓘_j`.
* `AlgebraicGeometry.Space.zariskiReadingConormalIso`: the Zariski reading of the degree-one
  piece of the conormal algebra of `φ` is the conormal sheaf of `j`.

## Main results

* `AlgebraicGeometry.Space.structureSharp_selfOpensStructureMap_eq_zero_iff`: on a Zariski
  open, the structure map of `φ` kills a function exactly when `j^♯` does.
* `AlgebraicGeometry.Space.zariskiReadingKernelIdealIso_hom_comp_ι`: `R_T 𝓘 ≅ 𝓘_j` is
  compatible with the inclusions into `𝒪_T`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalAlgebra_piece_one_yonedaSpaceMap`:
  the degree-one piece of the conormal algebra of `φ` is quasi-coherent.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Kernel

variable {Z T : BigFppfOver B S hS} (j : Z ⟶ T)

/-- **The kernel of the structure map, on a Zariski open.**  A function on a Zariski open `O` of
`T`, read on the étale chart of `O`, is killed by the structure map of `yonedaSpaceMap j` exactly
when it is killed by `j^♯`. -/
theorem structureSharp_selfOpensStructureMap_eq_zero_iff
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (r : Γ((BigFppfOver.toScheme B S hS).obj T, O)) :
    (structureSharp B S hS (yonedaSpaceMap j)).hom.app (op ((selfOpensFunctor B S hS T).obj O))
        ((selfOpensStructureMap B S hS T).hom.app (op O) r) = 0 ↔
      ((BigFppfOver.toScheme B S hS).map j).app O r = 0 := by
  have h := directImageSelfOpensSection_structureSharp j O r
  have h0 := directImageSelfOpensSection_structureSharp j O 0
  have hz : (structureSharp B S hS (yonedaSpaceMap j)).hom.app
      (op ((selfOpensFunctor B S hS T).obj O))
        ((selfOpensStructureMap B S hS T).hom.app (op O) 0) = 0 :=
    (congrArg _ (map_zero _)).trans (map_zero _)
  refine ⟨fun hx => (bijective_selfOpensStructureMap_hom_app Z _).1 ?_, fun hr => ?_⟩
  · exact h.symm.trans ((congrArg (directImageSelfOpensSection j O _) (hx.trans hz.symm)).trans
      (h0.trans (congrArg _ (map_zero _))))
  · exact ((directImageSelfOpensSection_bijective j O _).1
      (h.trans ((congrArg _ (hr.trans (map_zero _).symm)).trans h0.symm))).trans hz

/-- The Zariski reading of the kernel ideal sheaf of `yonedaSpaceMap j`, included in `𝒪_T`
through the inverse of `zariskiReadingUnitHom`. -/
def zariskiReadingKernelIdealι :
    (zariskiReadingFunctor T).obj (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ⟶
      SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf :=
  (zariskiReadingFunctor T).map (kernelIdealSheaf B S hS (yonedaSpaceMap j)).ι ≫
    (zariskiReadingUnitHomIso T).inv

/-- The inverse of `𝒪_T ≅ R_T 𝒪`, followed by the structure map, is the identity on sections. -/
theorem zariskiReadingUnitHom_val_app_inv (O : (chartScheme (idEtaleChart B S hS T)).Opensᵒᵖ)
    (x : ((zariskiReadingFunctor T).obj
      (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T)))).val.obj O) :
    (selfOpensStructureMap B S hS T).hom.app O ((zariskiReadingUnitHomIso T).inv.val.app O x) = x :=
  congrArg (fun g => g.val.app O x) (zariskiReadingUnitHomIso T).inv_hom_id

/-- The Zariski reading of the kernel ideal sheaf lands in the kernel of `𝒪_T ⟶ j_*𝒪_Z`. -/
theorem zariskiReadingKernelIdealι_mem (O : (chartScheme (idEtaleChart B S hS T)).Opensᵒᵖ)
    (m : ((zariskiReadingFunctor T).obj
      (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules).val.obj O) :
    (zariskiReadingKernelIdealι j).val.app O m ∈ (Stacks.SheafOfModules.kerSubmodule
      (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom))).obj O := by
  have hm : (structureSharp B S hS (yonedaSpaceMap j)).hom.app
      (op ((selfOpensFunctor B S hS T).obj O.unop)) m.1 = 0 := m.2
  rw [← zariskiReadingUnitHom_val_app_inv O m.1] at hm
  exact (structureSharp_selfOpensStructureMap_eq_zero_iff j O.unop _).1 hm

/-- The Zariski reading of the kernel ideal sheaf of `yonedaSpaceMap j`, mapped into the
sectionwise kernel of `𝒪_T ⟶ j_*𝒪_Z`. -/
def zariskiReadingKernelIdealToKer :
    (zariskiReadingFunctor T).obj (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ⟶
      (Stacks.SheafOfModules.kerSubmodule (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom))).toSheafOfModules :=
  Stacks.SheafOfModules.sheafFactorThruSubmodule (zariskiReadingKernelIdealι j) _
    (zariskiReadingKernelIdealι_mem j)

/-- The map `R_T 𝓘 ⟶ Ker(𝒪_T ⟶ j_*𝒪_Z)` is bijective on sections over every Zariski open, hence
an isomorphism. -/
theorem isIso_zariskiReadingKernelIdealToKer : IsIso (zariskiReadingKernelIdealToKer j) := by
  refine SheafOfModules.isIso_of_bijective_val_app' _ fun O => ⟨fun m m' hmm' => ?_, fun y => ?_⟩
  · exact Subtype.ext (Function.LeftInverse.injective (zariskiReadingUnitHom_val_app_inv O)
      (congrArg Subtype.val hmm'))
  · refine ⟨⟨(selfOpensStructureMap B S hS T).hom.app O y.1, ?_⟩, ?_⟩
    · exact (structureSharp_selfOpensStructureMap_eq_zero_iff j O.unop _).2 y.2
    · exact Subtype.ext ((bijective_selfOpensStructureMap_hom_app T O.unop).1
        (zariskiReadingUnitHom_val_app_inv O _))

/-- **The Zariski reading of the kernel ideal sheaf of `yonedaSpaceMap j` is the ideal sheaf of
`j`**, the kernel of `𝒪_T ⟶ j_*𝒪_Z`. -/
def zariskiReadingKernelIdealIso :
    (zariskiReadingFunctor T).obj (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≅
      Stacks.ClosedImmersion.idealSheaf ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom :=
  @asIso _ _ _ _ (zariskiReadingKernelIdealToKer j) (isIso_zariskiReadingKernelIdealToKer j) ≪≫
    IsLimit.conePointUniqueUpToIso (Stacks.SheafOfModules.isLimitKernelForkKerSubmodule _)
      (limit.isLimit _)

/-- The isomorphism `zariskiReadingKernelIdealIso` followed by the inclusion of the ideal sheaf
of `j` into `𝒪_T` is the inclusion `zariskiReadingKernelIdealι`. -/
theorem zariskiReadingKernelIdealIso_hom_comp_ι :
    (zariskiReadingKernelIdealIso j).hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)) =
      zariskiReadingKernelIdealι j := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp
    (Stacks.SheafOfModules.isLimitKernelForkKerSubmodule (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)))
    (limit.isLimit _) WalkingParallelPair.zero
  exact (Category.assoc (zariskiReadingKernelIdealToKer j) _ _).trans
    ((congrArg (fun g => zariskiReadingKernelIdealToKer j ≫ g) h).trans
      (Stacks.SheafOfModules.sheafFactorThruSubmodule_ι _ _ _))

/-- The kernel ideal sheaf of `yonedaSpaceMap j` is quasi-coherent when `j` is quasi-compact
(Stacks 082Z). -/
theorem isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map j)] :
    (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_kernelIdealSheaf B S hS _
    (isQuasiCompact_yoneda_map B S hS j inferInstance)

/-- **The degree-one piece of the conormal algebra of `yonedaSpaceMap j` is quasi-coherent** for
a closed immersion `j`: it is the inverse image of the quasi-coherent kernel ideal sheaf. -/
theorem isQuasicoherentOnSite_conormalAlgebra_piece_one_yonedaSpaceMap
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1).IsQuasicoherentOnSite := by
  rw [conormalAlgebra_piece_one]
  exact isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
    (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)

/-- The degree-one piece of the conormal algebra of `yonedaSpaceMap j` is `φ^*𝓘`. -/
def conormalAlgebraPieceOneIso :
    (conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1 ≅
      (modulePullback B S hS (yonedaSpaceMap j)).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules :=
  eqToIso (conormalAlgebra_piece_one B S hS _)

end Kernel

section Conormal

variable {Z T : BigFppfOver B S hS} (j : Z ⟶ T)

/-- **The Zariski reading of the conormal module of `yonedaSpaceMap j` is the conormal sheaf of
the closed immersion `j`**: `R_Z(φ^*𝓘) ≅ j^*(R_T 𝓘) ≅ j^*𝓘_j ≅ 𝒞_{Z/T}`. -/
def zariskiReadingConormalIso
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    (zariskiReadingFunctor Z).obj ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≅
      Stacks.Conormal.conormalSheaf (Z := (BigFppfOver.toScheme B S hS).obj Z)
        (X := (BigFppfOver.toScheme B S hS).obj T) ((BigFppfOver.toScheme B S hS).map j) :=
  (zariskiReadingFunctor Z).mapIso (conormalAlgebraPieceOneIso j) ≪≫
    (zariskiReadingPullbackIso j _
      (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).symm ≪≫
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).mapIso
      (zariskiReadingKernelIdealIso j) ≪≫
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf _).symm

end Conormal

end AlgebraicGeometry.Space

end
