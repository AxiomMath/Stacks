module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.SourceStructureSheafRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.SourceSliceCartesianSection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.SliceUnitModule
import StacksCore.Tactic.StacksAttribute

/-!
# The localized structure sheaves of Situation 08PA, as the rank-one modules see them

The reduction of **Stacks 08PC part (2)** recorded in
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ModuleLowerShriekForget.lean` leaves
one isomorphism to construct, and the obstruction to writing it down was not a transpose but the
two endpoints of its middle steps. Stacks 08P4 rewrites the abelian sheaf underlying
`j_{U'!} O_{U'}` as `j^{Ab}_{U'!}` applied to the abelian sheaf underlying
`Stacks.Sites.OverModules.sheafUnit (O_{U'})`, whereas the two steps that follow —
`MorphismSituation.localizedLowerShriekSourceProjectionIso`, which is Stacks 08PB, and the
Stacks 0FN2 comparison — want that argument to be the restriction of the base slice's structure
sheaf along the localised projection. This file closes that gap, on both sides of the square.

Three identifications separated the two, and all three are now available:

1. the `ULift` on the sections of `sheafUnit`, undone by
   `Stacks.Sites.OverModules.toSheafSheafUnitIso`;
2. the commutation of `forget₂ RingCat AddCommGrpCat` with restriction along the localised
   projections, which is `CategoryTheory.Functor.sheafComposeSheafPushforwardIso` and holds by
   `rfl`, so it needs no transport here;
3. the identification of the situation's structure sheaves — *topos* inverse images, by
   `MorphismSituation.sourceTopos_O` and `.totalTopos_O` — with restrictions along `p'` and `p`,
   which is `MorphismSituation.sourceToposORestrictionIso` on the source side and
   `MorphismSituation.targetToposORestrictionIso` below on the target side.

The localisation step itself is a strict equality on either side:
`MorphismSituation.overPullback_comp_sourceSliceProjection_eq` for the reindexed source
projection and `CategoryTheory.sheafPushforwardContinuous_overPost_eq` (Stacks 03CF) for the
target one. So both composites below are `toSheafSheafUnitIso` followed by `sheafCompose` of the
structure-sheaf identification, with nothing between them.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.targetToposORestrictionIso` and
  `.targetStructureRingSheafRestrictionIso`: the target-side analogues of
  `MorphismSituation.sourceToposORestrictionIso`, for `π` and `p` in place of `π'` and `p'`.
* `Stacks.Sites.FibredCategory.MorphismSituation.localizedSourceSheafUnitIso`: the abelian sheaf
  underlying the rank-one module of `C'/U'` over `O_{U'}` is the restriction of the abelian sheaf
  underlying `O_{p(u(U'))}` along the localised source projection.
* `Stacks.Sites.FibredCategory.MorphismSituation.localizedTargetSheafUnitIso`: the same on the
  target side, along the localised target projection `Over.post p`.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 08P4](https://stacks.math.columbia.edu/tag/08P4)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08PB](https://stacks.math.columbia.edu/tag/08PB)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- **The structure sheaf of the target ringed topos of Situation 08PA is the restriction of the
base structure sheaf along `p`.** The target-side analogue of
`MorphismSituation.sourceToposORestrictionIso`: `MorphismSituation.totalTopos_O` gives the
structure sheaf as the topos inverse image `π⁻¹O_D`, and the inverse image of `π` is restriction
along `p` by `MorphismSituation.pi_inverseImage`. -/
def targetToposORestrictionIso :
    (S.totalTopos S.pi).O ≅
      (S.p.sheafPushforwardContinuous CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        S.totalTopology S.base.J).obj S.base.O :=
  Stacks.Sheaves.ToposPullback.restrictionCommRingIso S.totalTopology S.base.J S.p S.base.O

/-- The identification of the target structure sheaf with a restriction is the identity on
underlying sheaves of sets. -/
@[simp]
theorem targetToposORestrictionIso_hom_forget :
    (sheafCompose S.totalTopology (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).map
        S.targetToposORestrictionIso.hom =
      𝟙 ((S.p.sheafPushforwardContinuous (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
        S.totalTopology S.base.J).obj
          ((sheafCompose S.base.J (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).obj
            S.base.O)) :=
  rfl

/-- The same identification on underlying sheaves of rings, which is the level sheaves of modules
are taken over. -/
def targetStructureRingSheafRestrictionIso :
    Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O ≅
      (S.p.sheafPushforwardContinuous RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          S.totalTopology S.base.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf S.baseTopos.O) :=
  (sheafCompose S.totalTopology
    (forget₂ CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).mapIso S.targetToposORestrictionIso

variable (U' : S.source)

/-- **The rank-one module of the source slice, as the localised projection sees it.** The abelian
sheaf underlying `Stacks.Sites.OverModules.sheafUnit (O_{U'})` — which is what Stacks 08P4 hands
back when it rewrites the abelian sheaf underlying `j_{U'!} O_{U'}` — is the restriction along the
localised source projection `π'_{U'} : C'/U' ⥤ D/p(u(U'))` of the abelian sheaf underlying the
structure sheaf of the base slice.

This is the composite of the three identifications listed in the module docstring: the `ULift` on
the sections of `sheafUnit` is undone by `Stacks.Sites.OverModules.toSheafSheafUnitIso`, the
structure sheaf of the source is a restriction along `p'` by
`MorphismSituation.sourceStructureRingSheafRestrictionIso`, and that restriction localises to one
along `π'_{U'}` by `MorphismSituation.overPullback_comp_sourceSliceProjection_eq`, which is a
strict equality. The commutation of `forget₂ RingCat AddCommGrpCat` with the two restrictions is
`CategoryTheory.Functor.sheafComposeSheafPushforwardIso`, also a strict equality, so it appears
nowhere in the term.

The lift target of `sheafUnit` is given as `max u₂ v₂ u₁ v₁`, which is the value the criterion's
spelling of `j_{U'!} O_{U'}` produces and which the situation's ring universe absorbs. -/
def localizedSourceSheafUnitIso :
    (SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        ((S.sourceTopology.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} U').obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O))).obj
        (Stacks.Sites.OverModules.sheafUnit.{v₂, max u₂ v₂,
          max w u₀ u₁ u₂ v₀ v₁ v₂, max u₂ v₂ u₁ v₁}
          ((S.sourceTopology.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} U').obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O))) ≅
      ((sourceSliceProjection S U').sheafPushforwardContinuous
          AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (S.sourceTopology.over U')
          (S.base.J.over (S.p.obj (S.u.obj U')))).obj
        ((sheafCompose (S.base.J.over (S.p.obj (S.u.obj U')))
            (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
              AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).obj
          ((S.base.J.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
              (S.p.obj (S.u.obj U'))).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf S.baseTopos.O))) :=
  Stacks.Sites.OverModules.toSheafSheafUnitIso.{v₂, max u₂ v₂,
      max w u₀ u₁ u₂ v₀ v₁ v₂, max u₂ v₂ u₁ v₁}
      ((S.sourceTopology.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} U').obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O)) ≪≫
    (sheafCompose (S.sourceTopology.over U')
      (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).mapIso
      ((S.sourceTopology.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} U').mapIso
        S.sourceStructureRingSheafRestrictionIso)

/-- **The rank-one module of the target slice, as the localised projection sees it.** The target
counterpart of `MorphismSituation.localizedSourceSheafUnitIso`: the abelian sheaf underlying
`Stacks.Sites.OverModules.sheafUnit (O_{u(U')})` is the restriction along the localised target
projection `Over.post p : C/u(U') ⥤ D/p(u(U'))` of the abelian sheaf underlying the structure
sheaf of the same base slice.

No reindexing is needed on this side, so the localisation step is
`CategoryTheory.sheafPushforwardContinuous_overPost_eq`, Stacks 03CF, rather than
`MorphismSituation.overPullback_comp_sourceSliceProjection_eq`; it is equally a strict equality,
and the two isomorphisms therefore land over one and the same sheaf on `D/p(u(U'))`, which is
what lets the source and target halves of the Stacks 08PC part (2) reduction be compared. -/
def localizedTargetSheafUnitIso :
    (SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        ((S.totalTopology.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
            (S.u.obj U')).obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O))).obj
        (Stacks.Sites.OverModules.sheafUnit.{v₁, max u₁ v₁,
          max w u₀ u₁ u₂ v₀ v₁ v₂, max u₁ v₁ u₂ v₂}
          ((S.totalTopology.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
              (S.u.obj U')).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O))) ≅
      ((Over.post S.p : Over (S.u.obj U') ⥤
            Over (S.p.obj (S.u.obj U'))).sheafPushforwardContinuous
          AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (S.totalTopology.over (S.u.obj U'))
          (S.base.J.over (S.p.obj (S.u.obj U')))).obj
        ((sheafCompose (S.base.J.over (S.p.obj (S.u.obj U')))
            (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
              AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).obj
          ((S.base.J.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
              (S.p.obj (S.u.obj U'))).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf S.baseTopos.O))) :=
  Stacks.Sites.OverModules.toSheafSheafUnitIso.{v₁, max u₁ v₁,
      max w u₀ u₁ u₂ v₀ v₁ v₂, max u₁ v₁ u₂ v₂}
      ((S.totalTopology.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (S.u.obj U')).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O)) ≪≫
    (sheafCompose (S.totalTopology.over (S.u.obj U'))
      (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).mapIso
      ((S.totalTopology.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          (S.u.obj U')).mapIso S.targetStructureRingSheafRestrictionIso)

end Stacks.Sites.FibredCategory.MorphismSituation

end
