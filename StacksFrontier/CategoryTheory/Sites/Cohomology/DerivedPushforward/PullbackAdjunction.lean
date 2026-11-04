module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived adjunction `Lf^* ⊣ Rf_*` for a morphism of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. Stacks 07A6 asserts that
the total left derived pullback `Lf^*` of Stacks 06YY is left adjoint to the total right derived
pushforward `Rf_*` of Stacks 07A5, with unit and counit obtained from the ordinary degreewise
adjunction of Stacks 03D7.

The `DerivedPushforward.Existence` module supplies the three ingredients on the pushforward
side: the existence of `Rf_*`, the absoluteness of a right derived functor over a
Grothendieck abelian category, and the resulting form
`Stacks.Cohomology.UnboundedComplexes.derivedAdjunction` of Stacks 09T5. This file supplies the
pullback side and assembles the adjunction.

## What is assumed, and why

Stacks 09T5 needs both derived functors to be *absolute*. For `Rf_*` that is free, because
`Mod(O_C)` is Grothendieck abelian. For `Lf^*` it is not: a left derived functor is absolute
when it is computed by a resolving class, and the resolving class for `Lf^*` is the K-flat
complexes, whose existence and behaviour under pullback is the content of Stacks 06YY. That
content is **not** proved here. It is isolated into `LeftDerivedPullback`, a bundle carrying a
resolving class `P` on `K(Mod(O_D))`, the fact that `P` resolves every object, the fact that
degreewise pullback takes a quasi-isomorphism between `P`-objects to a quasi-isomorphism, and
the derived pullback together with its comparison map. Everything else — the degreewise
adjunction on homotopy categories, the absoluteness of `Lf^*`, the adjunction and the two
factorization identities — is proved.

So the three results below are stated relative to a `LeftDerivedPullback f`, and for that reason
they do **not** carry the `@[stacks 07A6]` attribute. Stacks 06YY, once formalized, supplies the
bundle — via `LeftDerivedPullback.ofResolving`, which asks only for the class of K-flat
complexes, the existence of K-flat resolutions, and the fact that pullback preserves
quasi-isomorphisms between K-flat complexes — and the tag then belongs on the resulting
unconditional specialization, which is not in this file.

## Main definitions

* `Stacks.Cohomology.DerivedPushforward.LeftDerivedPullback.isLeftDerivedFunctor_comp`:
  `Lf^* ⋙ Rf_*` is again a left derived functor.  The general statement it specializes,
  **left derived functors computed by a resolving class are absolute**, is
  `CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_comp_of_resolutions`.
* `Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy` and `pushforwardMapHomotopy`:
  degreewise pullback and pushforward on the unbounded homotopy categories.
* `Stacks.Cohomology.DerivedPushforward.pullbackAdjPushforwardMapHomotopy`: **Stacks 03D7 on
  homotopy categories**, the degreewise adjunction, which is the input Stacks 09T5 takes.
* `Stacks.Cohomology.DerivedPushforward.LeftDerivedPullback`: the Stacks 06YY input described
  above, with `LeftDerivedPullback.ofResolving` building it from a resolving class alone.

## Main results

* `Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction`: **Stacks 07A6**,
  the adjunction `Lf^* ⊣ Rf_*` on unbounded derived categories.
* `derivedPullbackPushforwardAdjunction_unit_fac` and
  `derivedPullbackPushforwardAdjunction_counit_fac`: its unit and counit are the ones induced by
  the degreewise unit and counit.

## Implementation notes

The module universes of the two ringed topoi are independent, as they are for the direct image
and for the pullback.

Grothendieck abelianness of `Mod(O_C)` in the universe `w` of the sections does not follow from
the hypotheses making `Mod(O_C)` abelian, so it is assumed, exactly as in
`Stacks.Cohomology.DerivedPushforward.derivedPushforward`, and of the source only.

It is assumed in the form `CategoryTheory.IsGrothendieckAbelian.{w} X.Modules` rather than as
the two hypotheses `UnivLE.{u, w}` and `UnivLE.{v, w}` of
`Stacks.SheafOfModules.Small.isGrothendieckAbelian_sheafOfModules`, which is the usual route to
it. That route is strictly narrower: the small étale ringed topos of an algebraic space is
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, so it asks the unsynthesizable
`UnivLE.{u + 1, u}`, while its modules are Grothendieck abelian at `u` all the same by essential
smallness of the site (`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`). A consumer
holding the two `UnivLE` instances has this one synthesized for it, so nothing is lost.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry

namespace Stacks.Cohomology.DerivedPushforward

universe w w' v u v' u'

open AlgebraicGeometry.RingedToposHom
open Stacks.SheafOfModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

attribute [local instance] HasDerivedCategory.standard

/-- The class of quasi-isomorphisms of the unbounded homotopy category of `Mod(O_D)`, the class
at which `D(O_D)` is the localization and relative to which `Lf^*` is derived. -/
abbrev targetQuasiIso (Y : RingedTopos.{v', u', w'})
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] [HasSheafify Y.J AddCommGrpCat.{w'}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] :
    MorphismProperty
      (HomotopyCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso (SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ)

/-- The class of quasi-isomorphisms of the unbounded homotopy category of `Mod(O_C)`, relative
to which `Rf_*` is derived. -/
abbrev sourceQuasiIso (X : RingedTopos.{v, u, w}) [X.J.HasSheafCompose (forget RingCat.{w})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    MorphismProperty
      (HomotopyCategory (SheafOfModules.{w} (Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso (SheafOfModules.{w} (Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)

/-- Degreewise pullback of complexes of sheaves of modules along a morphism of ringed topoi, as
a functor between the unbounded homotopy categories. It is defined because pullback is additive
(`AlgebraicGeometry.RingedToposHom.pullbackModules_additive`). -/
abbrev pullbackMapHomotopy (f : RingedToposHom X Y) :
    HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) :=
  (f.toModulesHom.pullbackModules).mapHomotopyCategory (ComplexShape.up ℤ)

/-- Degreewise pullback, read as a functor from the unbounded homotopy category of the target to
the unbounded derived category of the source. Its left derived functor is `Lf^*`. -/
abbrev pullbackOnHomotopy (f : RingedToposHom X Y) :
    HomotopyCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{w} (Tensor.ringSheaf X.O)) :=
  pullbackMapHomotopy f ⋙ DerivedCategory.Qh

/-- Degreewise direct image of complexes of sheaves of modules along a morphism of ringed topoi,
as a functor between the unbounded homotopy categories. Composing it with the localization
`Qh` gives `pushforwardOnHomotopy`, whose right derived functor is `Rf_*`. -/
abbrev pushforwardMapHomotopy (f : RingedToposHom X Y) :
    HomotopyCategory (SheafOfModules.{w} (Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ) :=
  (pushforwardModules f).mapHomotopyCategory (ComplexShape.up ℤ)

/-- **Stacks 03D7 on unbounded homotopy categories**: degreewise pullback is left adjoint to
degreewise direct image, with the degreewise unit and counit. Both functors are additive, so
`CategoryTheory.Adjunction.mapHomotopyCategory` applies to the adjunction
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` of Stacks 03D7.

This is the adjunction that Stacks 09T5 derives. -/
@[stacks 03D7 "on unbounded homotopy categories"]
def pullbackAdjPushforwardMapHomotopy (f : RingedToposHom X Y) :
    pullbackMapHomotopy f ⊣ pushforwardMapHomotopy f :=
  letI := (pullbackAdjPushforwardModules f).right_adjoint_additive
  (pullbackAdjPushforwardModules f).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The input that **Stacks 06YY** supplies to the derived adjunction of Stacks 07A6: a total
left derived pullback `Lf^*`, *computed by a resolving class*.

`resolving` is the class of K-flat complexes of Stacks 06YY, `exists_resolution` is the
existence of K-flat resolutions, `isIso_map` is the fact that degreewise pullback takes a
quasi-isomorphism between K-flat complexes to a quasi-isomorphism, and `functor` with
`comparison` is `Lf^*` with its canonical map, invertible on K-flat complexes.

Only the last three fields are what `CategoryTheory.Adjunction.derived` literally asks for; the
first three are what makes `Lf^*` *absolute*, which it also asks for and which does not follow
from being a left derived functor. `LeftDerivedPullback.ofResolving` builds the whole bundle out
of the first three fields alone. -/
structure LeftDerivedPullback (f : RingedToposHom X Y) where
  /-- The resolving class, i.e. the K-flat complexes of Stacks 06YY. -/
  resolving : ObjectProperty
    (HomotopyCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))
  /-- Every complex of `O_D`-modules receives a quasi-isomorphism from one in the resolving
  class. -/
  exists_resolution (M : HomotopyCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    ∃ (N : HomotopyCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) (_ : resolving N) (s : N ⟶ M), targetQuasiIso Y s
  /-- Degreewise pullback takes a quasi-isomorphism between complexes in the resolving class to
  a quasi-isomorphism. -/
  isIso_map {M N : HomotopyCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)} (s : M ⟶ N) :
    targetQuasiIso Y s → resolving M → resolving N → IsIso ((pullbackOnHomotopy f).map s)
  /-- The total left derived pullback `Lf^*`. -/
  functor : DerivedCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) ⥤
    DerivedCategory (SheafOfModules.{w} (Tensor.ringSheaf X.O))
  /-- Its canonical comparison map, from the localization of degreewise pullback. -/
  comparison : DerivedCategory.Qh ⋙ functor ⟶ pullbackOnHomotopy f
  /-- The comparison map is invertible on the resolving class. -/
  isIso_comparison (M : HomotopyCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) : resolving M → IsIso (comparison.app M)

namespace LeftDerivedPullback

variable {f : RingedToposHom X Y}

/-- A resolving class on which degreewise pullback inverts quasi-isomorphisms determines a
`LeftDerivedPullback`: the functor is the total left derived functor of degreewise pullback,
which exists by `LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions`, and
its counit is invertible on the class by
`LeftDerivedByResolutions.isIso_app_of_resolutions`.

This is the shape in which Stacks 06YY is expected to supply the bundle: nothing beyond the
class of K-flat complexes, the existence of K-flat resolutions and the behaviour of pullback on
quasi-isomorphisms between them is needed. -/
def ofResolving (f : RingedToposHom X Y)
    (P : ObjectProperty
      (HomotopyCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)))
    (hP : ∀ M, ∃ (N : _) (_ : P N) (s : N ⟶ M), targetQuasiIso Y s)
    (hF : ∀ {M N} (s : M ⟶ N), targetQuasiIso Y s → P M → P N →
      IsIso ((pullbackOnHomotopy f).map s)) :
    LeftDerivedPullback f :=
  letI : (pullbackOnHomotopy f).HasPointwiseLeftDerivedFunctor (targetQuasiIso Y) :=
    LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions _ P hP _
      (fun s hs hM hN => hF s hs hM hN)
  { resolving := P
    exists_resolution := hP
    isIso_map := fun s hs hM hN => hF s hs hM hN
    functor := (pullbackOnHomotopy f).totalLeftDerived DerivedCategory.Qh (targetQuasiIso Y)
    comparison :=
      (pullbackOnHomotopy f).totalLeftDerivedCounit DerivedCategory.Qh (targetQuasiIso Y)
    isIso_comparison := fun M hM =>
      LeftDerivedByResolutions.isIso_app_of_resolutions _ P hP _
        (fun s hs hM' hN' => hF s hs hM' hN') DerivedCategory.Qh _ _ M hM }

/-- `Lf^*` is a left derived functor of degreewise pullback: its comparison map is invertible on
a resolving class, which is the criterion
`LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions`. -/
theorem isLeftDerivedFunctor (d : LeftDerivedPullback f) :
    d.functor.IsLeftDerivedFunctor d.comparison (targetQuasiIso Y) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions _ d.resolving
    d.exists_resolution _ (fun s hs hM hN => d.isIso_map s hs hM hN) DerivedCategory.Qh
    d.functor d.comparison d.isIso_comparison

variable [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Tensor.ringSheaf X.O))]

/-- `Lf^*` is an *absolute* left derived functor, in the one instance of that which Stacks 09T5
needs: the composite `Lf^* ⋙ Rf_*` is again a left derived functor, of degreewise pullback
followed by `Rf_*`. This is
`LeftDerivedByResolutions.isLeftDerivedFunctor_comp_of_resolutions`, and it is
where the resolving class in `LeftDerivedPullback` is used. -/
theorem isLeftDerivedFunctor_comp (d : LeftDerivedPullback f) :
    (d.functor ⋙ derivedPushforward (X := X) (Y := Y) f).IsLeftDerivedFunctor
      ((DerivedCategory.Qh.associator d.functor (derivedPushforward (X := X) (Y := Y) f)).inv ≫
        Functor.whiskerRight d.comparison (derivedPushforward (X := X) (Y := Y) f))
      (targetQuasiIso Y) :=
  letI := d.isLeftDerivedFunctor
  LeftDerivedByResolutions.isLeftDerivedFunctor_comp_of_resolutions _ d.resolving
    d.exists_resolution _
    (fun s hs hM hN => d.isIso_map s hs hM hN) DerivedCategory.Qh d.functor d.comparison
    (derivedPushforward (X := X) (Y := Y) f)

end LeftDerivedPullback

variable [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Tensor.ringSheaf X.O))]

/-- **Stacks 07A6**, relative to Stacks 06YY: the total left derived pullback `Lf^*` is left
adjoint to the total right derived direct image `Rf_*`,
`Hom_{D(O_C)}(Lf^*G, F) = Hom_{D(O_D)}(G, Rf_*F)`.

This is Stacks 09T5, in the form `Stacks.Cohomology.UnboundedComplexes.derivedAdjunction` takes
it, applied to the degreewise adjunction `pullbackAdjPushforwardMapHomotopy` of Stacks 03D7. Its
three inputs are met as follows: `Rf_*` is a right derived functor by construction and is
absolute because `Mod(O_C)` is Grothendieck abelian, which `derivedAdjunction` already
discharges; `Lf^*` is a left derived functor by `LeftDerivedPullback.isLeftDerivedFunctor`; and
`Lf^* ⋙ Rf_*` is one by `LeftDerivedPullback.isLeftDerivedFunctor_comp`.

The attribute `@[stacks 07A6]` is deliberately absent: the statement is conditional on the
Stacks 06YY bundle `d`. It belongs on the specialization of this definition at the K-flat
complexes, which Stacks 06YY makes possible and which is not in this file. -/
def derivedPullbackPushforwardAdjunction (f : RingedToposHom X Y)
    (d : LeftDerivedPullback f) : d.functor ⊣ derivedPushforward (X := X) (Y := Y) f :=
  letI := d.isLeftDerivedFunctor
  letI := d.isLeftDerivedFunctor_comp
  UnboundedComplexes.derivedAdjunction (pullbackAdjPushforwardMapHomotopy f) (targetQuasiIso Y)
    d.comparison
    ((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
      (sourceQuasiIso X))

/-- The unit of the derived adjunction is the one induced by the degreewise unit: on the image
of a complex `M` of `O_D`-modules it agrees, after the comparison maps of `Lf^*` and `Rf_*`,
with the degreewise unit of Stacks 03D7. -/
theorem derivedPullbackPushforwardAdjunction_unit_fac (f : RingedToposHom X Y)
    (d : LeftDerivedPullback f)
    (M : HomotopyCategory (SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    (derivedPullbackPushforwardAdjunction f d).unit.app (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward (X := X) (Y := Y) f).map (d.comparison.app M) =
      DerivedCategory.Qh.map ((pullbackAdjPushforwardMapHomotopy f).unit.app M) ≫
        ((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
          (sourceQuasiIso X)).app ((pullbackMapHomotopy f).obj M) :=
  letI := d.isLeftDerivedFunctor
  letI := d.isLeftDerivedFunctor_comp
  UnboundedComplexes.derivedAdjunction_unit_app (pullbackAdjPushforwardMapHomotopy f)
    (targetQuasiIso Y) d.comparison
    ((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
      (sourceQuasiIso X)) M

/-- The counit of the derived adjunction is the one induced by the degreewise counit: on the
image of a complex `K` of `O_C`-modules it agrees, after the comparison maps of `Rf_*` and
`Lf^*`, with the degreewise counit of Stacks 03D7. -/
theorem derivedPullbackPushforwardAdjunction_counit_fac (f : RingedToposHom X Y)
    (d : LeftDerivedPullback f)
    (K : HomotopyCategory (SheafOfModules.{w} (Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    d.functor.map
        (((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
          (sourceQuasiIso X)).app K) ≫
        (derivedPullbackPushforwardAdjunction f d).counit.app (DerivedCategory.Qh.obj K) =
      d.comparison.app ((pushforwardMapHomotopy f).obj K) ≫
        DerivedCategory.Qh.map ((pullbackAdjPushforwardMapHomotopy f).counit.app K) :=
  letI := d.isLeftDerivedFunctor
  letI := d.isLeftDerivedFunctor_comp
  UnboundedComplexes.derivedAdjunction_counit_app (pullbackAdjPushforwardMapHomotopy f)
    (targetQuasiIso Y) d.comparison
    ((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
      (sourceQuasiIso X)) K

end Stacks.Cohomology.DerivedPushforward

end
