module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites

/-! # Flatness on a ringed topos (`04JB`)

Everything the statement of Tag 04JB involves except the ringed-*topoi* flatness predicate is
already in the library, in `StacksFrontier/CategoryTheory/Sites/Modules/FlatMorphisms/RingedSites.lean`, under
restated names:

| name used here | library declaration |
|---|---|
| `ringULift` | `AlgebraicGeometry.SheafOfModules.commRingCatULift` |
| `sheafULift` | `AlgebraicGeometry.SheafOfModules.sheafULift` |
| `IsFlatMap` | `AlgebraicGeometry.SheafOfModules.IsFlatMapULift` |
| `hasSheafify_addCommGrp` | `GrothendieckTopology.hasSheafify_addCommGrpCat` |
| `wEqualsLocallyBijective_addCommGrp` | `…SheafOfModules.wEqualsLocallyBijective_addCommGrpCat` |
| `hasSheafify_commRing` | `AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat` |
| `isRightAdjoint_ringPushforward` | `…isRightAdjoint_sheafPushforwardContinuous_commRingCat` |
| `RingedSite.Hom.fsharpPullback` | `AlgebraicGeometry.RingedSite.Hom.fsharpPullbackULift` |
| `RingedSite.Hom.IsFlat` | `AlgebraicGeometry.RingedSite.Hom.IsFlat` |

So this file does not restate that mathematics: it only forwards the names in the left column to
the library's declarations, with universe arguments in the order used here, and supplies the one
declaration not available elsewhere — `RingedToposHom.IsFlat`, the clause of Tag 04JB about
morphisms of ringed *topoi*, which
`FlatMorphisms.RingedSites` deliberately omits.

`wEqualsLocallyBijective_addCommGrp` is the one row with no forwarder here: the library lemma is
named directly at its use site, in its own `.{z, u, v}` universe order. -/

@[expose] public section

open CategoryTheory

namespace Stacks.Sheaf.RingedToposFlat

/-- Sheafification of presheaves of abelian groups exists in any universe of sections
containing the site. -/
lemma hasSheafify_addCommGrp.{v, u, z} {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [UnivLE.{max u v, z}] :
    HasSheafify J AddCommGrpCat.{z} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat J

/-- Sheafification of presheaves of commutative rings exists in any universe of sections
containing the site. -/
lemma hasSheafify_commRing.{v, u, z} {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [UnivLE.{u, z}] [UnivLE.{v, z}] :
    HasSheafify J CommRingCat.{z} :=
  AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat.{z, u, v} J

/-- Lift commutative rings without changing their algebraic structure. -/
abbrev ringULift.{w, z} : CommRingCat.{w} ⥤ CommRingCat.{max w z} :=
  AlgebraicGeometry.SheafOfModules.commRingCatULift.{w, z}

/-- Lift a sheaf of commutative rings to a universe containing both the site and its
section rings. -/
abbrev sheafULift.{v, u, w} {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    Sheaf J CommRingCat.{w} ⥤ Sheaf J CommRingCat.{max w u v} :=
  AlgebraicGeometry.SheafOfModules.sheafULift.{w, u, v} J

/-- Flatness of a morphism of sheaves of commutative rings, computed after lifting its
rings to accommodate the site. -/
abbrev IsFlatMap.{v, u, w} {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O') : Prop :=
  AlgebraicGeometry.SheafOfModules.IsFlatMapULift.{w, u, v} f

namespace RingedToposHom

/-- A morphism of ringed topoi is flat when its inverse-image structure map is flat. -/
abbrev IsFlat.{v, u, w, v', u', w'} {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    (f : AlgebraicGeometry.RingedToposHom X Y) : Prop :=
  IsFlatMap.{v, u, w} f.fSharpInverseImage

end RingedToposHom

namespace RingedSite.Hom

/-- The inverse-image structure map after lifting the section rings to the site universe. -/
noncomputable abbrev fsharpPullback.{u, w} {X Y : AlgebraicGeometry.RingedSite.{u, u, w}}
    (f : AlgebraicGeometry.RingedSite.Hom X Y) :=
  AlgebraicGeometry.RingedSite.Hom.fsharpPullbackULift.{u, w} f

/-- A morphism of ringed sites is flat when the structure map of its associated morphism of
ringed topoi is flat. -/
abbrev IsFlat.{u, w} {X Y : AlgebraicGeometry.RingedSite.{u, u, w}}
    (f : AlgebraicGeometry.RingedSite.Hom X Y) : Prop :=
  AlgebraicGeometry.RingedSite.Hom.IsFlat.{u, w} f

end RingedSite.Hom

end Stacks.Sheaf.RingedToposFlat

end
