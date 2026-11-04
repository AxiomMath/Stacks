module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeStageModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFrameChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension

/-!
# Finite locally free and invertible modules on a limit bounded by the cutoff come from a stage

Stacks 0D2X is registered on
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_stage_model` and
`AlgebraicGeometry.Space.exists_isInvertibleModule_stage_model`, in the setting of Stacks 07SK,
whose index category is smaller than the cofinality of the site's size cutoff. This file proves
both parts for a system bounded by the cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`):
fewer stages than the cutoff, one cardinal below the cutoff bounding the hom types, and uniformly
bounded base changes of the stages, with no condition on the cofinality. This is the convention
under which the approximation of Stacks 0A0X exists, so these are the forms the assembly of
Stacks 0D3D consumes.

Let `X = lim Xᵢ` be the limit of such a cofiltered system of quasi-compact and quasi-separated
algebraic spaces over `S` with affine transition morphisms. Then

1. every finite locally free `𝒪_X`-module is the pullback of a finite locally free
   `𝒪_{Xᵢ}`-module for some `i`, and
2. every invertible `𝒪_X`-module is the pullback of an invertible `𝒪_{Xᵢ}`-module for some `i`.

The proofs are those of the registered theorems, through
`AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_stage_model_of_hasLocalFrames`.

## Main results

* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_isFiniteLocallyFreeOnSite_stage_model`:
  Stacks 0D2X, part (1), for a system bounded by the cutoff.
* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_isInvertibleModule_stage_model`:
  Stacks 0D2X, part (2), for a system bounded by the cutoff.
* `DescentSituation.exists_isInvertibleModule_stage_model_of_isCutoffBoundedSystem`:
  part (2) in the situation of Stacks 084R, at its chosen limit.
* `DescentSituation.exists_isFiniteLocallyFreeOnSite_stage_model_of_isCutoffBoundedSystem`:
  part (1) in the same situation.

## References

* [Stacks Project, Tag 0D2X](https://stacks.math.columbia.edu/tag/0D2X)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Cardinal Stacks.SheafOfModules.ChartFrames

universe u

namespace AlgebraicGeometry.Space.IsCutoffBoundedSystem

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hc : IsCutoffBoundedSystem B S hS D)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
  (hZ : B.Contains (⊤_ Scheme.{u}))
  (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))

include hZ hQc hQs in
/-- **Stacks 0D2X, part (1), for a system bounded by the cutoff.** Let `X = lim Xᵢ` be the limit
of a cofiltered system of quasi-compact and quasi-separated algebraic spaces over `S` with affine
transition morphisms, bounded by the cutoff. Every finite locally free `𝒪_X`-module is the
pullback of a finite locally free `𝒪_{Xᵢ}`-module for some `i`.

This is `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_stage_model` with the bound by
the cofinality of the cutoff traded for `AlgebraicGeometry.Space.IsCutoffBoundedSystem`. -/
theorem exists_isFiniteLocallyFreeOnSite_stage_model
    (F : Modules.{u, u} B S hS
      (limitAlgebraicSpace B S hS D hc hD hAffine).1
      (limitAlgebraicSpace B S hS D hc hD hAffine).2)
    (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F) :
    ∃ (i : I) (Fᵢ : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      SheafOfModules.IsFiniteLocallyFreeOnSite Fᵢ ∧
        Nonempty (F ≅ (modulePullback B S hS
          (limitProjection B S hS D hc hD hAffine i)).obj Fᵢ) := by
  obtain ⟨i, M, K, _, W, n, -, hW, hfr, hiso⟩ :=
    exists_stage_model_of_hasLocalFrames hc hD hAffine hZ hQc hQs F
      (hasLocalFrames_of_isFiniteLocallyFreeOnSite F hF)
  choose e he using hfr
  exact ⟨i, M, isFiniteLocallyFreeOnSite_of_isFrame (coversTop_of_pointsCover hW) M he, hiso⟩

include hZ hQc hQs in
/-- **Stacks 0D2X, part (2), for a system bounded by the cutoff.** Let `X = lim Xᵢ` be the limit
of a cofiltered system of quasi-compact and quasi-separated algebraic spaces over `S` with affine
transition morphisms, bounded by the cutoff. Every invertible `𝒪_X`-module is the pullback of an
invertible `𝒪_{Xᵢ}`-module for some `i`.

This is `AlgebraicGeometry.Space.exists_isInvertibleModule_stage_model` with the bound by the
cofinality of the cutoff traded for `AlgebraicGeometry.Space.IsCutoffBoundedSystem`. -/
theorem exists_isInvertibleModule_stage_model
    (L : Modules.{u, u} B S hS
      (limitAlgebraicSpace B S hS D hc hD hAffine).1
      (limitAlgebraicSpace B S hS D hc hD hAffine).2)
    (hL : IsInvertibleModule (limitAlgebraicSpace B S hS D hc hD hAffine) L) :
    ∃ (i : I) (Lᵢ : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      IsInvertibleModule (stageAlgebraicSpace B S hS D hD i) Lᵢ ∧
        Nonempty (L ≅ (modulePullback B S hS
          (limitProjection B S hS D hc hD hAffine i)).obj Lᵢ) := by
  obtain ⟨i, M, K, _, W, n, hn, hW, hfr, hiso⟩ :=
    exists_stage_model_of_hasLocalFrames hc hD hAffine hZ hQc hQs L
      (hasLocalFrames_of_isFiniteLocallyFreeOfRank L
        ((isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one L).mp hL))
  choose e he using hfr
  refine ⟨i, M, (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one M).mpr ?_, hiso⟩
  exact isFiniteLocallyFreeOfRank_of_isFrame (coversTop_of_pointsCover hW) M he 1 hn

end AlgebraicGeometry.Space.IsCutoffBoundedSystem

namespace AlgebraicGeometry.Space.DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

/-- The limit of the system of a situation of Stacks 084R bounded by the cutoff, as an algebraic
space, is isomorphic to the chosen limit. -/
def limitAlgebraicSpaceIsoOfIsCutoffBoundedSystem {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] (D : DescentSituation B S hS hZ I)
    (hc : IsCutoffBoundedSystem B S hS D.system) :
    IsCutoffBoundedSystem.limitAlgebraicSpace B S hS D.system hc
        (fun i => D.algebraicSpace i.unop) D.transition_affine ≅
      (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.isoMk _ ((limit.isLimit D.system).conePointUniqueUpToIso D.isLimit)

/-- The identification of the limits is compatible with the projections. -/
theorem limitAlgebraicSpaceIsoOfIsCutoffBoundedSystem_inv_comp {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] (D : DescentSituation B S hS hZ I)
    (hc : IsCutoffBoundedSystem B S hS D.system) (i : Iᵒᵖ) :
    (D.limitAlgebraicSpaceIsoOfIsCutoffBoundedSystem hc).inv ≫
        IsCutoffBoundedSystem.limitProjection B S hS D.system hc
          (fun i => D.algebraicSpace i.unop) D.transition_affine i =
      (ObjectProperty.homMk (D.limitCone.π.app i) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj i, D.algebraicSpace i.unop⟩) := by
  ext1
  exact IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit D.system) D.isLimit i

/-- Transport of a module along the identification of the chosen limit with the limit of the
system: a module on the chosen limit which is the pullback of a module on a stage along the
projection of the limit of the system, read back through the isomorphism, is the pullback along
the projection of the chosen cone. -/
theorem nonempty_iso_modulePullback_homMk_of_iso {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)
    {Z : AlgebraicSpaces B S hS} (p : X ⟶ Z) (q : Y ⟶ Z) (hpq : e.inv ≫ p = q)
    (L : Modules.{u, u} B S hS Y.1 Y.2) (M : Modules.{u, u} B S hS Z.1 Z.2)
    (eL : (modulePullback B S hS e.hom).obj L ≅ (modulePullback B S hS p).obj M) :
    Nonempty (L ≅ (modulePullback B S hS q).obj M) :=
  ⟨((modulePullbackIdIso B S hS Y).app L).symm ≪≫
    eqToIso (congrArg (fun (m : Y ⟶ Y) => (modulePullback B S hS m).obj L)
      e.inv_hom_id.symm) ≪≫
    ((modulePullbackCompIso B S hS e.inv e.hom).app L).symm ≪≫
    (modulePullback B S hS e.inv).mapIso eL ≪≫
    (modulePullbackCompIso B S hS e.inv p).app M ≪≫
    eqToIso (congrArg (fun (m : Y ⟶ Z) => (modulePullback B S hS m).obj M) hpq)⟩

/-- **Stacks 0D2X, part (2), in the situation of Stacks 084R, for a system bounded by the
cutoff.** Let `D` be a directed inverse system of quasi-compact and quasi-separated algebraic
spaces over `S` with affine transition morphisms and a chosen limit `X`, bounded by the cutoff.
Every invertible `𝒪_X`-module is the pullback of an invertible module on some stage.

This is `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_isInvertibleModule_stage_model`,
transported from the limit of the system to the chosen limit of the situation. -/
theorem exists_isInvertibleModule_stage_model_of_isCutoffBoundedSystem {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hc : IsCutoffBoundedSystem B S hS D.system)
    (L : Modules.{u, u} B S hS D.limitCone.pt D.limitAlgebraicSpace)
    (hL : IsInvertibleModule ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ L) :
    ∃ (i : I) (Lᵢ : Modules.{u, u} B S hS (D.system.obj (op i)) (D.algebraicSpace i)),
      IsInvertibleModule ⟨D.system.obj (op i), D.algebraicSpace i⟩ Lᵢ ∧
        Nonempty (L ≅ (modulePullback B S hS (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op i), D.algebraicSpace i⟩)).obj Lᵢ) := by
  have _ : Nonempty I := ⟨D.base⟩
  let eA := D.limitAlgebraicSpaceIsoOfIsCutoffBoundedSystem hc
  have hπ := D.limitAlgebraicSpaceIsoOfIsCutoffBoundedSystem_inv_comp hc
  have hL' := Stacks.SheafOfModules.isInvertible_pullbackModules_obj
    (f := smallEtaleRingedToposModulesHom B S hS eA.hom) (L := L) (hL := hL)
  obtain ⟨i, Lᵢ, hLᵢ, ⟨eL⟩⟩ := IsCutoffBoundedSystem.exists_isInvertibleModule_stage_model B S hS
    D.system hc (fun i => D.algebraicSpace i.unop) D.transition_affine hZ
    (fun i => D.quasiCompact i.unop) (fun i => D.quasiSeparated i.unop)
    ((modulePullback B S hS eA.hom).obj L) hL'
  exact ⟨i.unop, Lᵢ, hLᵢ, nonempty_iso_modulePullback_homMk_of_iso eA _ _ (hπ i) L Lᵢ eL⟩

/-- **Stacks 0D2X, part (1), in the situation of Stacks 084R, for a system bounded by the
cutoff.** Let `D` be a directed inverse system of quasi-compact and quasi-separated algebraic
spaces over `S` with affine transition morphisms and a chosen limit `X`, bounded by the cutoff.
Every finite locally free `𝒪_X`-module is the pullback of a finite locally free module on some
stage. -/
theorem exists_isFiniteLocallyFreeOnSite_stage_model_of_isCutoffBoundedSystem {I : Type u}
    [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hc : IsCutoffBoundedSystem B S hS D.system)
    (F : Modules.{u, u} B S hS D.limitCone.pt D.limitAlgebraicSpace)
    (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F) :
    ∃ (i : I) (Fᵢ : Modules.{u, u} B S hS (D.system.obj (op i)) (D.algebraicSpace i)),
      SheafOfModules.IsFiniteLocallyFreeOnSite Fᵢ ∧
        Nonempty (F ≅ (modulePullback B S hS (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op i), D.algebraicSpace i⟩)).obj Fᵢ) := by
  have _ : Nonempty I := ⟨D.base⟩
  let eA := D.limitAlgebraicSpaceIsoOfIsCutoffBoundedSystem hc
  have hπ := D.limitAlgebraicSpaceIsoOfIsCutoffBoundedSystem_inv_comp hc
  have hF' : SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS eA.hom).obj F) :=
    isFiniteLocallyFreeOnSite_modulePullback_of_isEtale B S hS eA.hom
      (isEtale_of_iso B S hS ((limit.isLimit D.system).conePointUniqueUpToIso D.isLimit)) F hF
  obtain ⟨i, Fᵢ, hFᵢ, ⟨eF⟩⟩ := IsCutoffBoundedSystem.exists_isFiniteLocallyFreeOnSite_stage_model
    B S hS D.system hc (fun i => D.algebraicSpace i.unop) D.transition_affine hZ
    (fun i => D.quasiCompact i.unop) (fun i => D.quasiSeparated i.unop)
    ((modulePullback B S hS eA.hom).obj F) hF'
  exact ⟨i.unop, Fᵢ, hFᵢ, nonempty_iso_modulePullback_homMk_of_iso eA _ _ (hπ i) F Fᵢ eF⟩

end AlgebraicGeometry.Space.DescentSituation

end
