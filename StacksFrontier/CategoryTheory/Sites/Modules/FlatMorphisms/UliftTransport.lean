module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites

/-!
# Flatness of a morphism of sheaves of rings, as flatness of one sheaf of modules

Flatness of a morphism `f : O ⟶ O'` of sheaves of commutative rings is flatness of `O'` as an
`O`-module.  When the universe of sections does not contain the site, this is asserted after the
universe lift `AlgebraicGeometry.SheafOfModules.sheafULift`, and the module in question is the
lifted `O'` restricted along the lifted `f`.  That module is named here, and flatness of a
sheaf of modules is shown to depend only on its isomorphism class, so that flatness of `f` can
be read off any module isomorphic to it — for instance the sheafification of a presheaf of
modules known to be objectwise flat.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.uliftRestrictedUnit`: the lifted target of a morphism of
  sheaves of commutative rings, as a module over the lifted source.
* `AlgebraicGeometry.SheafOfModules.IsFlatULift`: flatness of a sheaf of modules over a lifted
  sheaf of commutative rings.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFlat_of_iso`: flatness of a sheaf of modules transports
  along an isomorphism.
* `AlgebraicGeometry.SheafOfModules.isFlatMapULift_iff_isFlatULift`: a morphism of sheaves of
  commutative rings is flat in the universe-lifted sense exactly when
  `AlgebraicGeometry.SheafOfModules.uliftRestrictedUnit` is flat.
* `AlgebraicGeometry.SheafOfModules.isFlatMapULift_of_isFlatULift_of_iso`: a morphism of sheaves
  of commutative rings is flat as soon as some flat module is isomorphic to that one.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace AlgebraicGeometry.SheafOfModules

/-- **Flatness of a sheaf of modules transports along an isomorphism**: an isomorphic module is
a retract of it. -/
theorem isFlat_of_iso {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {O : Sheaf J CommRingCat.{w}}
    {M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (e : M ≅ N)
    (hM : IsFlat.{v, u, w, w} M) : IsFlat.{v, u, w, w} N :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso O e hM

/-- The target of a morphism of sheaves of commutative rings, lifted into a universe containing
the site and viewed as a module over the lifted source by restriction of scalars. -/
noncomputable abbrev uliftRestrictedUnit.{w', u', v'} {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} {O O' : Sheaf J CommRingCat.{w'}} (f : O ⟶ O') :
    _root_.SheafOfModules.{max w' u' v'}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max w' u' v'}
        ((sheafULift.{w', u', v'} J).obj O)) :=
  (_root_.SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{max w' u' v'} RingCat.{max w' u' v'})).map
      ((sheafULift.{w', u', v'} J).map f))).obj
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max w' u' v'}
        ((sheafULift.{w', u', v'} J).obj O')))

/-- Flatness of a sheaf of modules over a sheaf of commutative rings whose sections have been
lifted into a universe containing the site, where the tensor product of sheaves of modules is
available. -/
abbrev IsFlatULift.{w', u', v'} {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    {O : Sheaf J CommRingCat.{w'}}
    (M : _root_.SheafOfModules.{max w' u' v'}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max w' u' v'}
        ((sheafULift.{w', u', v'} J).obj O))) : Prop := by
  letI : HasSheafify J AddCommGrpCat.{max w' u' v'} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max w' u' v', v', u'} J
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max w' u' v'} :=
    wEqualsLocallyBijective_addCommGrpCat.{max w' u' v', u', v'} J
  exact IsFlat.{v', u', max w' u' v', max w' u' v'} M

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O O' : Sheaf J CommRingCat.{w}}

/-- A morphism of sheaves of commutative rings is flat, in the universe-lifted sense, exactly
when its lifted target is flat as a module over its lifted source. -/
theorem isFlatMapULift_iff_isFlatULift (f : O ⟶ O') :
    IsFlatMapULift.{w, u, v} f ↔ IsFlatULift.{w, u, v} (uliftRestrictedUnit.{w, u, v} f) :=
  Iff.rfl

/-- **A morphism of sheaves of commutative rings is flat as soon as some flat sheaf of modules
is isomorphic to its lifted target.**  This is the form in which objectwise flatness of a
presheaf of modules, passed through its sheafification, yields flatness of the morphism. -/
theorem isFlatMapULift_of_isFlatULift_of_iso (f : O ⟶ O')
    {M : _root_.SheafOfModules.{max w u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max w u v} ((sheafULift.{w, u, v} J).obj O))}
    (hM : IsFlatULift.{w, u, v} M) (e : M ≅ uliftRestrictedUnit.{w, u, v} f) :
    IsFlatMapULift.{w, u, v} f := by
  let : HasSheafify J AddCommGrpCat.{max w u v} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max w u v, v, u} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max w u v} :=
    wEqualsLocallyBijective_addCommGrpCat.{max w u v, u, v} J
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _ e hM

end AlgebraicGeometry.SheafOfModules

end
