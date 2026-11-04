module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivalenceRelationGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules

/-!
# The groupoid of a kernel pair of algebraic spaces

Let `u : U ⟶ Y` be a morphism of algebraic spaces and `t, s : R ⟶ U` a kernel pair of `u`. The
pair `(t, s)` is an equivalence relation on `U` over `Y`, so it extends to a groupoid in
algebraic spaces over `Y` (Stacks 043Y), with objects `U`, arrows `R`, target `t` and source
`s`. This is the groupoid `(U, U ×_Y U, pr₁, pr₂, pr₁₃)` of Stacks 03M3.

## Main definitions

* `AlgebraicGeometry.Space.kernelPairGroupoid`: the groupoid.

## Main results

* `AlgebraicGeometry.Space.kernelPairGroupoid_target`,
  `AlgebraicGeometry.Space.kernelPairGroupoid_source`: its target and source.
* `AlgebraicGeometry.Space.isPullback_kernelPairGroupoid`: its arrows are the kernel pair.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U Y R : AlgebraicSpaces B S hS} (u : U ⟶ Y) {t s : R ⟶ U}
  (hk : IsPullback t.hom s.hom u.hom u.hom)

/-- The target of the kernel pair, as a morphism over `Y`. -/
abbrev kernelPairGroupoidTargetOver (t : R ⟶ U) (_s : R ⟶ U) :
    Over.mk (t ≫ u).hom ⟶ Over.mk u.hom :=
  Over.homMk t.hom rfl

include hk in
/-- The two legs of a kernel pair of `u` have the same composite with `u`. -/
theorem kernelPairGroupoid_comp_eq : s ≫ u = t ≫ u := ObjectProperty.hom_ext _ hk.w.symm

/-- The source of the kernel pair, as a morphism over `Y`. -/
abbrev kernelPairGroupoidSourceOver : Over.mk (t ≫ u).hom ⟶ Over.mk u.hom :=
  Over.homMk s.hom (congrArg (fun m => m.hom) (kernelPairGroupoid_comp_eq u hk))

/-- The kernel pair as a pre-relation on `U` over `Y`. -/
abbrev kernelPairGroupoidRelation : PreRelation (Over.mk (t ≫ u).hom) (Over.mk u.hom) :=
  prod.lift (kernelPairGroupoidTargetOver u t s) (kernelPairGroupoidSourceOver u hk)

/-- The target of the kernel pair pre-relation is `kernelPairGroupoidTargetOver`. -/
theorem kernelPairGroupoidRelation_target :
    (kernelPairGroupoidRelation u hk).target = kernelPairGroupoidTargetOver u t s :=
  prod.lift_fst _ _

/-- The source of the kernel pair pre-relation is `kernelPairGroupoidSourceOver`. -/
theorem kernelPairGroupoidRelation_source :
    (kernelPairGroupoidRelation u hk).source = kernelPairGroupoidSourceOver u hk :=
  prod.lift_snd _ _

/-- Over `Y`, the target and the source form a kernel pair of `u`, seen as a morphism to the
final object `𝟙 Y`. -/
theorem isKernelPair_kernelPairGroupoidOver :
    IsKernelPair (Over.homMk u.hom (Category.comp_id _) :
        Over.mk u.hom ⟶ Over.mk (𝟙 Y.obj))
      (kernelPairGroupoidTargetOver u t s) (kernelPairGroupoidSourceOver u hk) :=
  IsPullback.of_map (Over.forget Y.obj) (Over.OverMorphism.ext hk.w) hk

/-- The kernel pair is an equivalence relation on `U` over `Y`. -/
instance isEquivalenceRelation_kernelPairGroupoidRelation :
    IsEquivalenceRelation (kernelPairGroupoidRelation u hk).target
      (kernelPairGroupoidRelation u hk).source := by
  rw [kernelPairGroupoidRelation_target, kernelPairGroupoidRelation_source]
  exact (IsKernelPair.equivalenceRelation _ _ _ (pullbackIsPullback _ _)
    (isKernelPair_kernelPairGroupoidOver u hk)).isEquivalenceRelation

/-- **The groupoid of a kernel pair** (Stacks 043Y applied to the kernel pair of `u`): objects
`U`, arrows `R`, target `t`, source `s`, over `Y`. -/
def kernelPairGroupoid : GroupoidInAlgebraicSpaces B S hS Y :=
  groupoidOfIsEquivalenceRelation (kernelPairGroupoidRelation u hk)

/-- The objects of the groupoid of a kernel pair are `U`. -/
theorem kernelPairGroupoid_objects : (kernelPairGroupoid u hk).objects = U := rfl

/-- The arrows of the groupoid of a kernel pair are `R`. -/
theorem kernelPairGroupoid_arrows : (kernelPairGroupoid u hk).arrows = R := rfl

/-- The target of the groupoid of a kernel pair is `t`. -/
theorem kernelPairGroupoid_target : (kernelPairGroupoid u hk).target = t :=
  ObjectProperty.hom_ext _ (congrArg CommaMorphism.left (kernelPairGroupoidRelation_target u hk))

/-- The source of the groupoid of a kernel pair is `s`. -/
theorem kernelPairGroupoid_source : (kernelPairGroupoid u hk).source = s :=
  ObjectProperty.hom_ext _ (congrArg CommaMorphism.left (kernelPairGroupoidRelation_source u hk))

/-- The structure morphism of the objects of the groupoid of a kernel pair is `u`. -/
theorem kernelPairGroupoid_objectsToBase : (kernelPairGroupoid u hk).objectsToBase = u := rfl

/-- **The arrows of the groupoid of a kernel pair are the kernel pair.** -/
theorem isPullback_kernelPairGroupoid :
    IsPullback (kernelPairGroupoid u hk).target.hom (kernelPairGroupoid u hk).source.hom
      u.hom u.hom := by
  rw [kernelPairGroupoid_target, kernelPairGroupoid_source]
  exact hk

/-- The target and the source of the groupoid of a kernel pair have the same composite with `u`.
-/
theorem kernelPairGroupoid_target_comp_source :
    (kernelPairGroupoid u hk).target ≫ u = (kernelPairGroupoid u hk).source ≫ u := by
  rw [kernelPairGroupoid_target, kernelPairGroupoid_source]
  exact (kernelPairGroupoid_comp_eq u hk).symm

end AlgebraicGeometry.Space

end
