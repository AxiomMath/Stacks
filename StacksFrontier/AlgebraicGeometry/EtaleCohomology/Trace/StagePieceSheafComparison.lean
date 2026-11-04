module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedFiltrationCharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StratificationLFunction

/-!
# The restriction of a sheaf to an open stratum, on the two sites

For a closed filtration of `X` with members `Y j`, a sheaf `G` of `Λ`-modules on Mathlib's small
étale site of `X` restricts to the open stratum of `Y j` in two steps: inverse image to `Y j`, then
restriction to the open stratum. A sheaf `F` on the small étale site of a big étale site restricts
in one step, by `smallEtalePullObj` along the composite inclusion. For `G` the image of `F` under
the equivalence of the two sheaf categories the two restrictions agree: inverse image composes,
inverse image along an open immersion is restriction
(`Stacks.EtaleCohomology.etaleModuleInverseImageRestrictionIso`), and the equivalence commutes with
inverse image (`Stacks.EtaleCohomology.sheafEquivSmallEtalePullObjIso`).

## Main definitions

* `Stacks.EtaleCohomology.filtrationPieceSheafIso`: the two restrictions of a sheaf to an open
  stratum are isomorphic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k]
  {B : BigEtaleSite.{u}} {X : B.Scheme} (f : X.obj ⟶ Spec (.of k))
  {s : ConstructibleStratification B X ⊤} (Φ : s.ClosedFiltration)
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

omit [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint] in
include Φ in
/-- The image in schemes of the composite inclusion of the `j`-th open stratum into `X` is the
open immersion of the stratum into `Y j` followed by the closed immersion of `Y j` into `X`. -/
theorem map_stageOpenInclusion_comp_stageInclusion (j : ℕ) :
    B.inclusion.map (Φ.stageOpenInclusion j ≫ Φ.stageInclusion j) =
      (Φ.stageOpen j).ι ≫ B.inclusion.map (Φ.stageInclusion j) := by
  rw [Functor.map_comp, Φ.map_stageOpenInclusion]
  rfl

/-- **The two restrictions of a sheaf to an open stratum agree.** -/
def filtrationPieceSheafIso
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) (j : ℕ) :
    filtrationPieceSheaf Λ Φ
        ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj F) j ≅
      (SmallEtale.sheafEquiv B (Φ.stageOpenObj j).obj (Φ.stageOpenObj j).property
        (ModuleCat.{u + 1} Λ)).functor.obj
        (smallEtalePullObj B (Φ.stageOpenInclusion j ≫ Φ.stageInclusion j) F) :=
  (etaleModuleInverseImageRestrictionIso.{u, 0} Λ (Φ.stageOpen j).ι).symm.app _ ≪≫
    ((etaleModuleInverseImageCompIso.{u, 0} Λ (Φ.stageOpen j).ι
      (B.inclusion.map (Φ.stageInclusion j))).app _).symm ≪≫
    eqToIso (by simp only [fS]; rw [map_stageOpenInclusion_comp_stageInclusion]; rfl) ≪≫
    (sheafEquivSmallEtalePullObjIso B (Φ.stageOpenInclusion j ≫ Φ.stageInclusion j) Λ F).symm

omit [Fintype k] [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint] in
/-- The composite inclusion of the `j`-th open stratum into `X`, followed by `f`, is the structure
morphism `filtrationPieceMap f Φ j` of the stratum. -/
theorem map_comp_eq_filtrationPieceMap (j : ℕ) :
    B.inclusion.map (Φ.stageOpenInclusion j ≫ Φ.stageInclusion j) ≫ f =
      filtrationPieceMap f Φ j := by
  rw [map_stageOpenInclusion_comp_stageInclusion Φ]
  exact Category.assoc _ _ _

end Stacks.EtaleCohomology
