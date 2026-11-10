module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap

/-!
# Restriction of sections along an étale morphism, read on the restricted sheaf

Let `j : Y ⟶ X` be an étale morphism, `W` an étale scheme over `X` and `r : Y ⟶ W` a morphism
over `X`. Restricting a section of an abelian sheaf `F` on `X_étale` over `W` to a global section
of `j⁻¹F` on `Y` (`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb`) is, once `j⁻¹F` is
identified with the restriction `F|_Y`
(`Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleRestriction`),
the restriction of sections of `F` along `r`, read as a morphism of étale schemes over `X`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_etale` — that identification.
* `Stacks.EtaleCohomology.isIso_smallEtaleSectionsPullbackAb_of_isIso` — for `r` an
  isomorphism, the restriction map is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

namespace Stacks.EtaleCohomology

variable {Y X : Scheme.{u}} (j : Y ⟶ X) [Etale j] (W : X.Etale) (r : Y ⟶ W.left)
  (hr : r ≫ W.hom = j)

/-- The morphism of étale schemes over `X` from `Y` to `W` given by `r`. -/
def etaleSectionsMorphism : (smallEtaleCompose j).obj (Scheme.Etale.mk (𝟙 Y)) ⟶ W :=
  MorphismProperty.Over.homMk r (by
    change r ≫ W.hom = 𝟙 Y ≫ j
    rw [hr, Category.id_comp]) trivial

/-- The unit of restriction along an étale morphism, on sections: restriction along the
projection `W ×_X Y ⟶ W`. -/
theorem etaleRestrictionAbelianDirectImageAdj_unit_app_hom_app
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    ((etaleRestrictionAbelianDirectImageAdj.{u, 0} j).unit.app F).hom.app (op W) =
      F.obj.map ((smallEtaleComposeBaseChangeAdj j).counit.app W).op := by
  simp only [etaleRestrictionAbelianDirectImageAdj, Adjunction.restrictFullyFaithful,
    Adjunction.whiskerLeft, Functor.FullyFaithful.homEquiv]
  simp
  rfl

/-- **Restriction of sections along an étale morphism, read on the restricted sheaf.** Under
`j⁻¹F ≅ F|_Y`, restricting a section of `F` over `W` to a global section of `j⁻¹F` along
`r : Y ⟶ W` is restricting it along `r`, as a morphism of étale schemes over `X`, followed by
the identification of global sections with sections over the final object. -/
theorem smallEtaleSectionsPullbackAb_etale (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    (smallEtaleSectionsPullbackAb j W r hr).app F ≫
        (Sheaf.Γ Y.smallEtaleTopology Ab.{u + 1}).map
          ((smallEtalePullbackAbIsoEtaleRestriction j).hom.app F) =
      F.obj.map (etaleSectionsMorphism j W r hr).op ≫
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology Ab.{u + 1}
          (isTerminalEtaleMkId Y)).inv.app ((etaleRestriction.{u, 0} j).obj F) := by
  let e := smallEtalePullbackAbIsoEtaleRestriction j
  let L := smallEtaleBaseChangeLift j W r hr
  have hu := congrArg (fun φ => φ.hom.app (op W))
    (Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleAdjunctionAb j)
      (etaleRestrictionAbelianDirectImageAdj.{u, 0} j) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  have hnat := (e.hom.app F).hom.naturality L.op
  have hΓ := (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology Ab.{u + 1}
    (isTerminalEtaleMkId Y)).inv.naturality (e.hom.app F)
  have hm : (smallEtaleCompose j).map L ≫ (smallEtaleComposeBaseChangeAdj j).counit.app W =
      etaleSectionsMorphism j W r hr :=
    MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)
  change ((smallEtaleAdjunctionAb j).unit.app F).hom.app (op W) ≫
      ((smallEtalePullbackAb j).obj F).obj.map L.op ≫
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology Ab.{u + 1}
          (isTerminalEtaleMkId Y)).inv.app ((smallEtalePullbackAb j).obj F) ≫
          (Sheaf.Γ Y.smallEtaleTopology Ab.{u + 1}).map (e.hom.app F) = _
  let u := ((smallEtaleAdjunctionAb j).unit.app F).hom.app (op W)
  let i' := (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology Ab.{u + 1}
    (isTerminalEtaleMkId Y)).inv.app ((etaleRestriction.{u, 0} j).obj F)
  refine (congrArg (fun x => u ≫ ((smallEtalePullbackAb j).obj F).obj.map L.op ≫ x)
    hΓ.symm).trans ?_
  refine (congrArg (u ≫ ·) (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (fun x => u ≫ x ≫ i') hnat).trans ?_
  refine (congrArg (u ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hu).trans ?_
  rw [etaleRestrictionAbelianDirectImageAdj_unit_app_hom_app, ← hm]
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ i') ?_)
  exact (F.obj.map_comp _ _).symm

/-- **Sections over an étale scheme are the global sections of the restriction.** For `r` an
isomorphism, the restriction `F(W) ⟶ Γ(Y, j⁻¹F)` along `r` is an isomorphism. -/
theorem isIso_smallEtaleSectionsPullbackAb_app_of_isIso (hiso : IsIso r)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    IsIso ((smallEtaleSectionsPullbackAb j W r hr).app F) := by
  obtain ⟨r', h₁, h₂⟩ := hiso.out
  have : IsIso (etaleSectionsMorphism j W r hr) :=
    ⟨⟨MorphismProperty.Over.homMk r' (by
        change r' ≫ 𝟙 Y ≫ j = W.hom
        rw [Category.id_comp, ← hr, ← Category.assoc, h₂, Category.id_comp]) trivial,
      by apply MorphismProperty.Over.Hom.ext; exact h₁,
      by apply MorphismProperty.Over.Hom.ext; exact h₂⟩⟩
  have : IsIso (F.obj.map (etaleSectionsMorphism j W r hr).op) := inferInstance
  have h2 : IsIso ((smallEtaleSectionsPullbackAb j W r hr).app F ≫
      (Sheaf.Γ Y.smallEtaleTopology Ab.{u + 1}).map
        ((smallEtalePullbackAbIsoEtaleRestriction j).hom.app F)) := by
    rw [smallEtaleSectionsPullbackAb_etale]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (Iso.isIso_inv ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology Ab.{u + 1}
        (isTerminalEtaleMkId Y)).app ((etaleRestriction.{u, 0} j).obj F)))
  exact IsIso.of_isIso_comp_right _ ((Sheaf.Γ Y.smallEtaleTopology Ab.{u + 1}).map
    ((smallEtalePullbackAbIsoEtaleRestriction j).hom.app F))

end Stacks.EtaleCohomology

end
