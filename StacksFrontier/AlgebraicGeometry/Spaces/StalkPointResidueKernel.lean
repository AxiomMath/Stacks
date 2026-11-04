module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatGlobalSectionsRingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkPointFibreSquare

/-!
# The residue map of `𝒪_{Y,y}`, read on algebraic spaces

Let `Y` be a Noetherian scheme of the big fppf site and `y ∈ Y`.  The closed immersion
`Spec κ(y) ⟶ Spec 𝒪_{Y,y}` induces, on the rings of global regular functions of the algebraic
spaces they represent, the residue map `𝒪_{Y,y} ⟶ κ(y)`.  Its kernel, the maximal ideal of the
local ring, is contained in the Jacobson radical.

## Main results

* `AlgebraicGeometry.Space.ker_globalSectionsRingHomSite_residueToStalkPointHom_le_jacobson`: the
  kernel of the residue map `Γ(Spec 𝒪_{Y,y}) ⟶ Γ(Spec κ(y))` lies in the Jacobson radical.

## References

* [Stacks Project, Tag 0D39](https://stacks.math.columbia.edu/tag/0D39)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (Y : BigFppfOver B S hS)
  [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
  (y : (BigFppfOver.toScheme B S hS).obj Y)

/-- The diagram of identity charts over `Spec κ(y) ⟶ Spec 𝒪_{Y,y}`. -/
def residueToStalkPointChartDiagram : ChartDiagram B S hS (yoneda.obj (residuePointObject Y y))
    (yoneda.obj (stalkPointObject Y y)) (yoneda.map (residueToStalkPointHom Y y)) :=
  ⟨idEtaleChart B S hS (residuePointObject Y y), idEtaleChart B S hS (stalkPointObject Y y),
    residueToStalkPointHom Y y, (Category.id_comp _).trans (Category.comp_id _).symm⟩

/-- **The kernel of the residue map `Γ(Spec 𝒪_{Y,y}) ⟶ Γ(Spec κ(y))` lies in the Jacobson
radical**, read on the algebraic spaces the two schemes represent. -/
theorem ker_globalSectionsRingHomSite_residueToStalkPointHom_le_jacobson :
    RingHom.ker (globalSectionsRingHomSite B S hS
      (representedSpaceMap B S hS (residueToStalkPointHom Y y))) ≤ Ideal.jacobson ⊥ := by
  let T := stalkPointObject Y y
  have hbT := bijective_globalSectionsChartEval_of_isTerminal B S hS
    (representedAlgebraicSpace B S hS T) (isTerminalIdEtaleChart B S hS T)
  let eT := RingEquiv.ofBijective _ hbT
  let O := ((BigFppfOver.toScheme B S hS).obj Y).presheaf.stalk y
  let e : _ ≃+* O := eT.trans (Scheme.ΓSpecIso O).commRingCatIsoToRingEquiv
  intro x hx
  have key := globalSectionsChartEval_globalSectionsRingHomSite B S hS
    (representedSpaceMap B S hS (residueToStalkPointHom Y y))
    (residueToStalkPointChartDiagram Y y) x
  rw [RingHom.mem_ker.1 hx] at key
  have key' : (Spec.map (((BigFppfOver.toScheme B S hS).obj Y).residue y)).appTop (eT x) = 0 :=
    key.symm.trans (map_zero _)
  have hres : ((BigFppfOver.toScheme B S hS).obj Y).residue y (e x) = 0 := by
    have h₂ := congrArg (fun φ ↦ φ.hom ((Scheme.ΓSpecIso O).hom (eT x)))
      (Scheme.ΓSpecIso_inv_naturality (((BigFppfOver.toScheme B S hS).obj Y).residue y))
    have hz : (Scheme.ΓSpecIso O).inv ((Scheme.ΓSpecIso O).hom (eT x)) = eT x :=
      Iso.hom_inv_id_apply _ _
    simp only [CommRingCat.comp_apply] at h₂
    have h₃ : (Scheme.ΓSpecIso (((BigFppfOver.toScheme B S hS).obj Y).residueField y)).inv
        (((BigFppfOver.toScheme B S hS).obj Y).residue y (e x)) = 0 :=
      h₂.trans ((congrArg _ hz).trans key')
    simpa using congrArg (Scheme.ΓSpecIso
      (((BigFppfOver.toScheme B S hS).obj Y).residueField y)).hom h₃
  have hm : e x ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.residue_eq_zero_iff _).1 hres
  rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hm
  rw [Ideal.mem_jacobson_bot] at hm ⊢
  intro z
  let e' : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (yoneda.obj (stalkPointObject Y y)) (isAlgebraicSpace_yoneda B S hS _)).O).obj ≃+* O := e
  have hw : e x * e z + 1 = e' (x * z + 1) := by
    rw [map_add e', map_mul e', map_one e']
    rfl
  exact (MulEquiv.isUnit_map e'.toMulEquiv).1 (hw ▸ hm (e z))

end AlgebraicGeometry.Space

end
