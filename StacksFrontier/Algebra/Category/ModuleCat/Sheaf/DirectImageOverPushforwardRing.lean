module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NoncommExtendScalarsSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjointPullPush
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfModulesRestrictScalarsCongr

/-!
# The left adjoint of the direct image of modules over the direct-image sheaf of rings

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi, `O` a sheaf of rings on `C` and
`𝒜 = f_*O` the direct-image sheaf of rings on `D`.  Stacks 03D4 asserts the bijection

`Mor_{Mod(O)}(O ⊗_{f⁻¹𝒜} f⁻¹G, F) = Mor_{Mod(𝒜)}(G, f_*F)`,

and `Stacks.Sheaves.RingedToposModules.tensorInverseImageAdjDirectImageModules` proves it.  This
file identifies the right-hand functor and removes a smallness hypothesis.

The right-hand functor is the direct image of Stacks 03D1 itself.  The adjunction of Stacks 03D4
is assembled out of Stacks 03D3, whose right-hand functor is the direct image over `f⁻¹𝒜` read as
an `𝒜`-module by restriction of scalars along the unit `𝒜 ⟶ f_*f⁻¹𝒜`, composed with restriction
of scalars along the counit `f⁻¹𝒜 ⟶ O`; `restrictScalarsRingCounitCompDirectImageIso` identifies
this composite with the direct image of Stacks 03D1, as an isomorphism of functors.

Stacks 03D4 is stated there for a **small** source site,
because the extension of scalars it uses is
`Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction`, which inherits `SmallCategory`
from `PresheafOfModules.pullbackObjIsDefined_eq_top`.  The small étale site of an algebraic space
has its objects one universe above its morphisms, so that form of Stacks 03D4 does not apply to
it.  `tensorInverseImageAdjPushforwardModuleFunctor` is the same adjunction built from
`Stacks.NoncommChangeOfRings.Sheaf.extendRestrictScalarsAdjunction`, which is unconditional, so
it holds over an arbitrary site.

## Main results

* `Stacks.Sheaves.ToposPushforward.ringSheafMap_pushforwardRingMap` — the direct image of a
  morphism of sheaves of rings is, on underlying sheaves of sets, the direct image of its
  underlying morphism.
* `Stacks.Sheaves.ToposPushforward.ringUnit_comp_pushforwardRingMap_ringCounit` — the composite
  `𝒜 ⟶ f_*f⁻¹𝒜 ⟶ 𝒜` of the unit of Stacks 03D3 with the direct image of the counit of
  Stacks 03D4 is the identity, as a morphism of sheaves of **rings**.
* `Stacks.Sheaves.RingedToposModules.restrictScalarsRingCounitCompDirectImageIso` — restriction
  of scalars along `f⁻¹𝒜 ⟶ O` followed by the direct image of Stacks 03D3 is the direct image
  of Stacks 03D1.
* `Stacks.Sheaves.RingedToposModules.tensorInverseImageAdjPushforwardModuleFunctor` — the
  statement of Stacks 03D4 over an arbitrary site, with the direct image of Stacks 03D1 as its
  right adjoint.

## Implementation notes

`ringSheafMap_ringUnit_comp_pushforward_map_ringCounit` already records the triangle identity
behind `ringUnit_comp_pushforwardRingMap_ringCounit`, but on underlying sheaves of *sets*, which
is not enough to rewrite a restriction of scalars: restriction of scalars is indexed by a
morphism of sheaves of rings.  Faithfulness of `sheafCompose _ (forget RingCat)` promotes the one
to the other, and `ringSheafMap_pushforwardRingMap` is what identifies the underlying morphism of
`Stacks.Sheaves.ToposPushforward.pushforwardRingMap`; that identification is
`ringSheafMap_pullbackRingSheafMap`, which does not fire by rewriting because
`pushforwardRingMap` is a definition and not an abbreviation.

The comparison of functors is `SheafOfModules.restrictScalarsCongr` of that identity and not
`CategoryTheory.eqToIso` of it, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfModulesRestrictScalarsCongr.lean`: the component of
`eqToIso` is a transport along an opaque proof and is stuck, while here the component is the
identity on sections.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPushforward

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  (O : Sheaf J RingCat.{ww})

/-- The underlying morphism of sheaves of sets of the direct image of a morphism of sheaves of
rings is the direct image of its underlying morphism of sheaves of sets. -/
@[simp]
lemma ringSheafMap_pushforwardRingMap {S S' : Sheaf J RingCat.{ww}} (a : S ⟶ S') :
    (sheafCompose K (forget RingCat.{ww'})).map (pushforwardRingMap f a) =
      f.pushforward.map ((sheafCompose J (forget RingCat.{ww})).map a) :=
  ringSheafMap_pullbackRingSheafMap K f.pushforward a

/-- **The triangle identity of `f⁻¹ ⊣ f_*` at the direct-image sheaf of rings**, as a morphism of
sheaves of rings: the unit `f_*O ⟶ f_*f⁻¹f_*O` of Stacks 03D3 followed by the direct image of the
counit `f⁻¹f_*O ⟶ O` of Stacks 03D4 is the identity of `f_*O`.

`Stacks.Sheaves.ToposPushforward.ringSheafMap_ringUnit_comp_pushforward_map_ringCounit` is this
identity on underlying sheaves of sets, and `sheafCompose _ (forget RingCat)` is faithful. -/
theorem ringUnit_comp_pushforwardRingMap_ringCounit :
    ringUnit f (pushforwardRingSheaf f O) ≫ pushforwardRingMap f (ringCounit f O) =
      𝟙 (pushforwardRingSheaf f O) := by
  refine (sheafCompose K (forget RingCat.{ww'})).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    ringSheafMap_pushforwardRingMap]
  exact ringSheafMap_ringUnit_comp_pushforward_map_ringCounit f O

end Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf J RingCat.{w})

/-- **The right-hand functor of Stacks 03D4 is the direct image of Stacks 03D1.**  Restriction of
scalars along the counit `f⁻¹f_*O ⟶ O`, followed by the direct image of Stacks 03D3 over
`f⁻¹f_*O`, is the direct image of `O`-modules over `f_*O`.

Both sides apply `f_*` to the sheaf of sets underlying the module, so the comparison is the
identity on sections; the content is that the two `f_*O`-actions agree.  The direct image of
Stacks 03D3 acts through the unit `f_*O ⟶ f_*f⁻¹f_*O`, so the composite acts through
`f_*O ⟶ f_*f⁻¹f_*O ⟶ f_*O`, and
`Stacks.Sheaves.ToposPushforward.ringUnit_comp_pushforwardRingMap_ringCounit` says that this is
the identity. -/
noncomputable def restrictScalarsRingCounitCompDirectImageIso :
    SheafOfModules.restrictScalars (ringCounit f O) ⋙
        directImageModules f (pushforwardRingSheaf f O) ≅
      pushforwardModuleFunctor f O :=
  Functor.isoWhiskerRight
      (pullbackModuleFunctorRestrictScalarsIso K f.pushforward (ringCounit f O)).symm
      (SheafOfModules.restrictScalars (ringUnit f (pushforwardRingSheaf f O))) ≪≫
    Functor.isoWhiskerLeft (pushforwardModuleFunctor f O)
      (SheafOfModules.restrictScalarsCongr
        (ringUnit_comp_pushforwardRingMap_ringCounit f O))

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The statement of Stacks 03D4 over an arbitrary site**: for a morphism of topoi
`f : Sh(C) ⟶ Sh(D)` and a sheaf of rings `O` on `C`, the functor `G ↦ O ⊗_{f⁻¹f_*O} f⁻¹G` from
sheaves of `f_*O`-modules to sheaves of `O`-modules is left adjoint to the direct image of
Stacks 03D1.

It differs from `Stacks.Sheaves.RingedToposModules.tensorInverseImageAdjDirectImageModules`
in two ways.  The extension of scalars is
`Stacks.NoncommChangeOfRings.Sheaf.extendScalars`, which exists over an arbitrary site, in place
of `Stacks.Sheaves.ModuleAdjunction.extendScalars`, which needs the source site small; and the
right adjoint is the direct image of Stacks 03D1 itself rather than the composite of Stacks 03D3
with a restriction of scalars, by
`restrictScalarsRingCounitCompDirectImageIso`. -/
noncomputable def tensorInverseImageAdjPushforwardModuleFunctor :
    inverseImageModules f (pushforwardRingSheaf f O) ⋙
        Stacks.NoncommChangeOfRings.Sheaf.extendScalars.{w} (ringCounit f O) ⊣
      pushforwardModuleFunctor f O :=
  ((inverseImageAdjDirectImageModules f (pushforwardRingSheaf f O)).comp
      (Stacks.NoncommChangeOfRings.Sheaf.extendRestrictScalarsAdjunction.{w}
        (ringCounit f O))).ofNatIsoRight
    (restrictScalarsRingCounitCompDirectImageIso f O)

end Stacks.Sheaves.RingedToposModules

end
