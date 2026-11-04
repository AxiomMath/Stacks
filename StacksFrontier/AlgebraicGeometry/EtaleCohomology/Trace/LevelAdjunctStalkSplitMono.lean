module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DirectImageLevelStalkBridge

/-!
# Kernels of the level adjunct stalk maps along a split monomorphism

For `χ : f⁻¹ F → F'` with a left inverse (e.g. an isomorphism, such as the base change morphism
`G|_V → R¹g'_!(K|_{U'})` along an open immersion in Laumon's degeneration), the stalk at `s̄` of
the adjunct `Fₙ → f_* F'ₙ` of `χₙ` has the same kernel as the stalk of the unit `Fₙ → f_* f⁻¹ Fₙ`
(`Stacks.EtaleCohomology.levelUnitStalkMap_eq_zero_of_levelAdjunctStalkMap_eq_zero`). This turns
the absence of punctual sections of `G` at a missing point of a curve into the kernel bound of
`Stacks.EtaleCohomology.CurveSpecializationMapInput`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.levelAdjunctStalkMap_comp_apply`: the stalk of the adjunct of `χ ≫ θ`
  is that of `χ` followed by the stalk of `f_* θₙ`.
* `Stacks.EtaleCohomology.levelUnitStalkMap_eq_zero_of_levelAdjunctStalkMap_eq_zero`: if `χ` has
  a left inverse, a germ killed by the stalk of the adjunct of `χₙ` is killed by the stalk of the
  unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.SmallEtale.LAdicSheaf

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.1) {ℓ : ℕ}
  [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- **The stalk of the adjunct of `χ ≫ θ`** is that of `χ` followed by the stalk of `f_* θₙ`. -/
public theorem levelAdjunctStalkMap_comp_apply (F : LAdicSheaf.{u, u + 1} B Y ℓ)
    {F' F'' : LAdicSheaf.{u, u + 1} B X ℓ}
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (θ : F' ⟶ F'') (n : ℕ)
    (w : finiteLevelStalk B Y ℓ F s n) :
    (levelAdjunctStalkMap f s F F'' (χ ≫ θ) n).hom w =
      (colim.map (Functor.whiskerLeft
          ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.2 s)).op)
          ((levelPushforward f n).map (θ.app n)).hom)).hom
        ((levelAdjunctStalkMap f s F F' χ n).hom w) := by
  let π := (CategoryOfElements.π (geometricPointFiber B Y.1 Y.2 s)).op
  have e : ((levelAdjunction f n).homEquiv _ _) ((χ ≫ θ).app n) =
      ((levelAdjunction f n).homEquiv _ _) (χ.app n) ≫ (levelPushforward f n).map (θ.app n) :=
    Adjunction.homEquiv_naturality_right _ _ _
  have h2 := congrArg (fun (g : F.level n ⟶ (levelPushforward f n).obj (F''.level n)) =>
    (colim.map (Functor.whiskerLeft π g.hom)).hom w) e
  have h3 : colim.map (Functor.whiskerLeft π
      ((((levelAdjunction f n).homEquiv _ _) (χ.app n)).hom ≫
        ((levelPushforward f n).map (θ.app n)).hom)) =
      colim.map (Functor.whiskerLeft π (((levelAdjunction f n).homEquiv _ _) (χ.app n)).hom) ≫
        colim.map (Functor.whiskerLeft π ((levelPushforward f n).map (θ.app n)).hom) := by
    rw [Functor.whiskerLeft_comp, colim.map_comp]
  exact h2.trans (congrArg (fun g => g.hom w) h3)

/-- **Along a split monomorphism `χ` the adjunct has the kernel of the unit**: if `χ` has a left
inverse, a germ killed by the stalk of the adjunct of `χₙ` is killed by the stalk of the unit. -/
public theorem levelUnitStalkMap_eq_zero_of_levelAdjunctStalkMap_eq_zero
    (F : LAdicSheaf.{u, u + 1} B Y ℓ) {F' : LAdicSheaf.{u, u + 1} B X ℓ}
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F')
    (χ' : F' ⟶ AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F) (hχ : χ ≫ χ' = 𝟙 _)
    (n : ℕ) (w : finiteLevelStalk B Y ℓ F s n)
    (hw : (levelAdjunctStalkMap f s F F' χ n).hom w = 0) :
    (levelUnitStalkMap f F s n).hom w = 0 := by
  have h1 := congrArg (fun c => (levelAdjunctStalkMap f s F _ c n).hom w) hχ
  refine ((congrArg (fun g => g.hom w) (levelAdjunctStalkMap_id f s F n)).symm.trans
    h1.symm).trans ?_
  refine (levelAdjunctStalkMap_comp_apply f s F χ χ' n w).trans ?_
  rw [hw]
  exact map_zero (colim.map (Functor.whiskerLeft
    ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.2 s)).op)
    ((levelPushforward f n).map (χ'.app n)).hom)).hom

end Stacks.EtaleCohomology

end
