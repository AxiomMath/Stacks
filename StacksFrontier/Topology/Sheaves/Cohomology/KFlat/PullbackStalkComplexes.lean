module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackOnRingedSpaces
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback

/-!
# Discharging the Stacks 0098 hypothesis of Stacks 06YC

`Stacks.SheafOfModules.KFlatPullback.kFlat_pullback` — the pullback of a K-flat complex of sheaves
  of modules along a
morphism of ringed spaces is K-flat — carries two hypotheses,
  `Stacks.SheafOfModules.KFlatPullback.StalkCriterion`
(Stacks 06YB) and `Stacks.SheafOfModules.KFlatPullback.PullbackStalkComplexes` (the complex-level
  form of
Stacks 0098). The second is proved: it is
`Stacks.RingedSpace.stalkModulePullbackComplexIso` at the complex shape `ComplexShape.up ℤ`,
evaluated at the complex.

This file is the join of the two developments, and nothing more. Its single theorem
`Stacks.SheafOfModules.KFlatPullback.pullbackStalkComplexes` has no hypotheses, and the two
  corollaries restate
Stacks 06YC with only Stacks 06YB left to supply.

## Main results

* `Stacks.SheafOfModules.KFlatPullback.pullbackStalkComplexes`: `PullbackStalkComplexes`,
  unconditionally.
* `Stacks.SheafOfModules.KFlatPullback.kFlat_pullback_of_stalkCriterion`: **Stacks 06YC** granted
  Stacks 06YB alone.
* `Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_of_stalkCriterion`: the same at the
  retyped pullback
  functor `StacksDraft.KFlat.modulePullback`.

## Implementation notes

The ring map asked for existentially by `exists_extendStalk_iso` is supplied by the germ map
`Stacks.RingedSpace.stalkRingMap f x : 𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}`, which is the one in the source;
because the hypothesis only asks that *some* ring map work, no compatibility clause arises.

The two sides reach the stalk ring and its commutativity by different routes, and the single
thing this discharge turns on is that the routes agree definitionally:

* the sheaf of rings. `StalkModulePullback` is stated over
  `structureSheafRing Y`, `PullbackKFlat` over
  `Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf`. The former is a `def` whose body is the latter,
    so the two
  are equal by `rfl` but the equality is invisible to `rw`, to `refine` and to instance search.
  Nothing here needs a bridge, because the whole proof is one term in `exact` position, where
  the elaborator checks the definitional equality at default transparency instead of searching
  for it. That is why the proof is a structure instance with term-mode fields and not a tactic
  block.
* commutativity of the stalk ring. `StalkModulePullback.structureStalkCommRing` and
  `StacksDraft.StalkTensor.commRing_stalk_ringSheaf` are two separate `CommRing` structures on
  the same carrier. They agree: each takes its `Ring` field from the one the `RingCat` object
  already carries, and the remaining field `mul_comm` is a `Prop`, hence proof-irrelevant. So
  `Stacks.RingedSpace.stalkBaseChange f x` and `ModuleCat.extendScalars (stalkRingMap f x).hom`
  at the instances `Stacks.SheafOfModules.KFlatPullback.extendStalk` resolves are the same functor,
    and the
  `Functor.Additive` arguments of the two `mapHomologicalComplex` applications — one
  `Stacks.RingedSpace.stalkBaseChange_additive`, one seated by `letI` inside
  `CochainComplex.extendScalarsLarge` — are likewise proof-irrelevant.

Both crossings are checked by the elaborator, and the theorem's axiom list is
`[propext, Classical.choice, Quot.sound]`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace Stacks.SheafOfModules.KFlatPullback

/-- **The complex-level form of Stacks 0098, no longer a hypothesis.** For a morphism of ringed
spaces `f : X ⟶ Y`, a point `x` of `X` and a complex `M` of `𝒪_Y`-modules, the stalk complex of
the degreewise pullback `f^*M` at `x` is an extension of scalars of the stalk complex of `M` at
`f(x)`, along the germ map `𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}`.

This is `Stacks.RingedSpace.stalkModulePullbackComplexIso` at `ComplexShape.up ℤ`, evaluated at
`M`, with `Stacks.RingedSpace.stalkRingMap f x` as the ring map the hypothesis asks to exist. -/
theorem pullbackStalkComplexes : PullbackStalkComplexes.{u} where
  exists_extendStalk_iso f x M :=
    ⟨(Stacks.RingedSpace.stalkRingMap f x).hom,
      ⟨(Stacks.RingedSpace.stalkModulePullbackComplexIso f x (ComplexShape.up ℤ)).app M⟩⟩

/-- **Stacks 06YC granted Stacks 06YB alone.** The degreewise pullback of a K-flat complex of
`𝒪_Y`-modules along a morphism of ringed spaces is a K-flat complex of `𝒪_X`-modules. This is
`kFlat_pullback` with its Stacks 0098 hypothesis discharged by `pullbackStalkComplexes`. -/
theorem kFlat_pullback_of_stalkCriterion (hYB : StalkCriterion.{u})
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat Y.sheaf K) :
    Stacks.SheafOfModules.IsKFlat X.sheaf
      (((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
  kFlat_pullback hYB pullbackStalkComplexes f K hK

/-- `kFlat_pullback_of_stalkCriterion` in the shape
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.PullbackKFlatInput.kFlat_pullback` consumes:
  the pullback functor is the retyping
`StacksDraft.KFlat.modulePullback` and K-flatness is
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat`. -/
theorem kFlat_modulePullback_of_stalkCriterion (hYB : StalkCriterion.{u})
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) (hK :
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X (((StacksDraft.KFlat.modulePullback
      f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) :=
  kFlat_modulePullback hYB pullbackStalkComplexes f K hK

end Stacks.SheafOfModules.KFlatPullback

end

end
