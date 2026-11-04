module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Flat morphisms of ringed sites

A morphism of ringed sites is flat when the structure map in its inverse-image form
`f⁻¹ O_Y ⟶ O_X` is a flat morphism of sheaves of rings, that is, when `O_X` is flat as an
`f⁻¹ O_Y`-module.

Both the inverse image and flatness are computed after lifting the rings of sections into a
universe containing both themselves and the site.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.commRingCatULift`: the universe lift of commutative rings,
  as a functor.
* `AlgebraicGeometry.SheafOfModules.sheafULift`: the induced universe lift of sheaves of
  commutative rings on a fixed site.
* `AlgebraicGeometry.SheafOfModules.IsFlatMapULift`: flatness of a morphism of sheaves of
  commutative rings, computed after that lift.
* `AlgebraicGeometry.RingedSite.Hom.fsharpPullbackULift`: the inverse-image form of the
  structure map of a morphism of ringed sites, between lifted structure sheaves.
* `AlgebraicGeometry.RingedSite.Hom.IsFlat`: flatness of a morphism of ringed sites.

## Main results

* `AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat` and
  `AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat`: the two sheafification facts
  that hold in every universe of sections containing the site.
* `AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat`: in
  such a universe the direct image of sheaves of commutative rings has a left adjoint.

## References

* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SheafOfModules

section Sheafification

/-- Sheafification equivalences are the local bijections in every universe of sections
containing the site. -/
lemma wEqualsLocallyBijective_addCommGrpCat.{z, u, v}
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{u, z}] [UnivLE.{v, z}]
    [UnivLE.{max u v z, z}] [UnivLE.{max v z, z}] :
    J.WEqualsLocallyBijective AddCommGrpCat.{z} := by
  have : HasLimitsOfSize.{max v z, max u v z} AddCommGrpCat.{z} :=
    hasLimitsOfSizeOfUnivLE.{z, z, max v z, max u v z} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, z, u, z + 1, z} J

/-- Sheafification of presheaves of commutative rings exists in every universe of sections
containing the site. -/
lemma hasSheafify_commRingCat.{z, u, v}
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{u, z}] [UnivLE.{v, z}] :
    HasSheafify J CommRingCat.{z} :=
  hasSheafifyEssentiallySmallSite.{v, z, u, z + 1, z} J _

/-- In a universe of sections containing the site, the direct image of sheaves of commutative
rings has a left adjoint, the inverse image. -/
lemma isRightAdjoint_sheafPushforwardContinuous_commRingCat.{z, u, v}
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
    [UnivLE.{u, z}] [UnivLE.{v, z}] [UnivLE.{max u v z, z}]
    (G : C ⥤ D) [G.IsContinuous J K] :
    (G.sheafPushforwardContinuous CommRingCat.{z} J K).IsRightAdjoint := by
  have : HasSheafify K CommRingCat.{z} := hasSheafify_commRingCat.{z, u, v} K
  have : HasColimitsOfSize.{v, max u v} CommRingCat.{z} :=
    hasColimitsOfSizeOfUnivLE.{z, z, v, max u v} _
  infer_instance

end Sheafification

/-- Lift commutative rings to a larger universe, without changing their algebraic
structure. -/
def commRingCatULift.{w, z} : CommRingCat.{w} ⥤ CommRingCat.{max w z} where
  obj R := CommRingCat.of (ULift.{z} R)
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp (f.hom.comp ULift.ringEquiv.toRingHom))

/-- Lift a sheaf of commutative rings into a universe containing both its sections and the
site. -/
def sheafULift.{w, u, v} {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    Sheaf J CommRingCat.{w} ⥤ Sheaf J CommRingCat.{max w u v} where
  obj O := {
    obj := O.obj ⋙ commRingCatULift.{w, max u v}
    property := by
      have : HasLimitsOfSize.{v, max v u} CommRingCat.{max w u v} :=
        hasLimitsOfSizeShrink.{v, max v u, max w u v, max w u v} _
      apply (Presheaf.isSheaf_iff_isSheaf_comp J _
        (forget CommRingCat.{max w u v})).mpr
      change Presheaf.IsSheaf J ((O.obj ⋙ forget CommRingCat) ⋙ uliftFunctor.{max u v})
      exact Presheaf.isSheaf_comp_of_isSheaf _ _ _
        ((sheafCompose J (forget CommRingCat)).obj O).property }
  map f := ⟨Functor.whiskerRight f.hom commRingCatULift.{w, max u v}⟩

/-- Flatness of a morphism of sheaves of commutative rings, computed after lifting the
sections into a universe containing the site. -/
abbrev IsFlatMapULift.{w, u, v} {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O') : Prop := by
  letI : HasSheafify J AddCommGrpCat.{max w u v} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max w u v, v, u} J
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max w u v} :=
    wEqualsLocallyBijective_addCommGrpCat.{max w u v, u, v} J
  exact IsFlatMap.{v, u, max w u v} ((sheafULift.{w, u, v} J).map f)

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.RingedSite.Hom

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

/-- The inverse-image form of the structure map of a morphism of ringed sites, between the
structure sheaves lifted into a universe containing the site. -/
noncomputable def fsharpPullbackULift.{u, w} {X Y : RingedSite.{u, u, w}} (f : Hom X Y) :
    (f.u.sheafPullback CommRingCat.{max w u} Y.J X.J).obj
        ((SheafOfModules.sheafULift.{w, u, u} Y.J).obj Y.O) ⟶
      (SheafOfModules.sheafULift.{w, u, u} X.J).obj X.O := by
  let φ : (SheafOfModules.sheafULift.{w, u, u} Y.J).obj Y.O ⟶
      (f.u.sheafPushforwardContinuous CommRingCat.{max w u} Y.J X.J).obj
        ((SheafOfModules.sheafULift.{w, u, u} X.J).obj X.O) :=
    ⟨Functor.whiskerRight f.fsharp.hom SheafOfModules.commRingCatULift.{w, u}⟩
  exact ((f.u.sheafAdjunctionContinuous CommRingCat.{max w u} Y.J X.J).homEquiv _ _).symm φ

/-- A morphism of ringed sites is flat when the inverse-image form of its structure map is a
flat morphism of sheaves of rings. -/
@[sga "4 V 1.8" "left flat (sites)"]
abbrev IsFlat.{u, w} {X Y : RingedSite.{u, u, w}} (f : Hom X Y) : Prop :=
  SheafOfModules.IsFlatMapULift (fsharpPullbackULift f)

end AlgebraicGeometry.RingedSite.Hom
