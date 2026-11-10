module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom

/-!
# Pullback of sheaves of modules along a morphism of ringed topoi, at independent universes

`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` of Stacks 03D6 part (2) is stated for two
ringed topoi in `RingedTopos.{w, w, w}`, so the objects of the underlying sites, their morphisms
and the sections of the structure sheaves are forced into one universe.  Every site of schemes
in this development has objects in `Type (u + 1)` and morphisms in `Type u`, with a structure
sheaf whose sections are in `Type u`, so no such site can be an endpoint of a morphism of ringed
topoi carrying a pullback of sheaves of modules.

This file adds the pullback at **independent** object and morphism universes, the source site
being asked only to be essentially small in the universe of the sections.  The existence of the
left adjoint comes from `SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall`, which
already holds at these binders; `AlgebraicGeometry.RingedToposSiteHom.pushforwardTopos` is
likewise already stated at them, and nothing else about the pullback needed the universes to
agree.

## Main definitions

* `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`: the pullback
  `f^* : Mod(O_Y) ⥤ Mod(O_X)` of sheaves of modules, at independent universes.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral`: it is left
  adjoint to the pushforward.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneralIso`: it is the sheafification of
  `O_X ⊗_{f⁻¹ O_Y} f⁻¹ G`, the formula of the source.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral_additive`: the pullback is
  additive.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral_eq_pullbackTopos`: where the two
  ringed topoi have all three universes equal, this is the pullback already defined, by `rfl`.

## Implementation notes

**This is a widening, not a second functor.**  Both the general and the pinned pullback are
`SheafOfModules.pullback` of the same structure map `fSharpRing`, and that functor is a chosen
left adjoint of the pushforward, extracted from the `Prop`-valued class
`CategoryTheory.Functor.IsRightAdjoint`; by proof irrelevance it does not depend on which
instance supplied the adjointness, which is why
`pullbackToposGeneral_eq_pullbackTopos` is `rfl` even though the two instances in play are
different.  The right fix is to widen the universes of the `Pullback` section of
`StacksFrontier/CategoryTheory/Sites/Modules/RingedToposHom.lean` itself; the generalisation is
introduced additively here because that file's interface may not change, exactly as
`AlgebraicGeometry.RingedSite.HomGeneral` is introduced alongside
`AlgebraicGeometry.RingedSite.Hom`.

The hypotheses are those of Mathlib's construction with the adjointness discharged: the source
site essentially small and the target site locally small in the universe `w` of the sections,
and sheafification of abelian presheaves on the target site.  `EssentiallySmall.{w} Y.C` is
what the small étale site of a scheme satisfies — its objects are a `Type (u + 1)`, so it is
not `Small.{u}` and Mathlib's `SmallCategory` hypothesis is unavailable, but every object is
isomorphic to one of a `u`-small family.

The presheaf-level existence instance *is* restated at these binders, as
`presheafPushforward_isRightAdjointGeneral`.  It is needed even though
`SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall` exists, because the type
of `fSharpRing` is written at the normal form of the ring sheaf, and
`Stacks.SheafOfModules.Tensor.ringSheaf` is an anonymous-constructor pair whose first component
is `O.obj ⋙ forget₂ CommRingCat RingCat`, so `(Tensor.ringSheaf Y.O).obj` reduces at
reducible transparency instead of standing as an atom, and Mathlib's key `φ : ?S ⟶ ?F.op ⋙ ?R`
cannot recover `?F` and `?R` from the target.  So `F`, `R` and `S` are supplied explicitly.  The
analogous bridge at `RingedToposHom.lean:168`
exists only for `RingedTopos.{w, w, w}`, so it does not cover these independent universes.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' w

namespace AlgebraicGeometry.RingedToposSiteHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03D6, part (2), at independent universes.** The pullback of sheaves of modules
along a morphism of ringed topoi, characterised as the left adjoint of the pushforward, with the
objects and the morphisms of the two underlying sites in universes independent of each other and
of the universe of the sections of the structure sheaves.  By `pullbackToposGeneralIso` it is
the sheafification of `O_X ⊗_{f⁻¹ O_Y} f⁻¹ G`, which is the formula of the source. -/
@[stacks 03D6 "part (2): pullback of sheaves of modules along a morphism of ringed topoi,
presented by a morphism of the underlying sites, with the object and morphism universes of the
two sites independent of each other and of the universe of the sections of the structure
sheaves; the source site is asked to be essentially small in that universe rather than small"]
def pullbackToposGeneral (f : RingedToposSiteHom X Y) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  SheafOfModules.pullback.{w} f.fSharpRing

/-- **Stacks 03D7 at independent universes.** The pullback of sheaves of modules is left adjoint
to the pushforward. -/
@[stacks 03D7 "ringed topoi, with the geometric morphism presented by a morphism of the
underlying sites and the object and morphism universes of the two sites independent of each
other and of the universe of the sections of the structure sheaves"]
def pullbackPushforwardAdjunctionToposGeneral (f : RingedToposSiteHom X Y) :
    f.pullbackToposGeneral ⊣ f.pushforwardTopos :=
  SheafOfModules.pullbackPushforwardAdjunction.{w} f.fSharpRing

/-- **The presheaf-level pushforward along `f^♯` is a right adjoint** at these binders: the
source site is essentially small in the universe of the rings and module sections and the target
site is locally small in it.

`F`, `R` and `S` are given explicitly on purpose.  `fSharpRing` is
`ObjectProperty.homMk f.fSharpPresheaf`, so the two goals agree at default transparency, but
after canonicalization `(Tensor.ringSheaf Y.O).obj` reduces rather than standing as an atom, and
the three parameters are no longer recoverable from the target by unification. -/
instance presheafPushforward_isRightAdjointGeneral (f : RingedToposSiteHom X Y) :
    (PresheafOfModules.pushforward.{w} f.fSharpRing.hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall.{w}
    (F := f.u) (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) f.fSharpPresheaf

instance isLeftAdjoint_pullbackToposGeneral (f : RingedToposSiteHom X Y) :
    f.pullbackToposGeneral.IsLeftAdjoint :=
  f.pullbackPushforwardAdjunctionToposGeneral.isLeftAdjoint

/-- The pullback of sheaves of modules is additive, being a left adjoint of the additive functor
`pushforwardTopos`. -/
instance pullbackToposGeneral_additive (f : RingedToposSiteHom X Y) :
    f.pullbackToposGeneral.Additive :=
  Adjunction.left_adjoint_additive f.pullbackPushforwardAdjunctionToposGeneral

/-- The pullback of a sheaf of modules is the sheafification of the presheaf-level extension of
scalars along `f^♯`, that is, of `O_X ⊗_{f⁻¹ O_Y} f⁻¹ G`. -/
def pullbackToposGeneralIso (f : RingedToposSiteHom X Y) :
    f.pullbackToposGeneral ≅ SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
      PresheafOfModules.pullback.{w} f.fSharpRing.hom ⋙
        PresheafOfModules.sheafification (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
  SheafOfModules.pullbackIso.{w} f.fSharpRing

end AlgebraicGeometry.RingedToposSiteHom

namespace AlgebraicGeometry.RingedToposSiteHom

variable {X Y : RingedTopos.{w, w, w}}
  [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Where the two ringed topoi have their objects, their morphisms and the sections of their
structure sheaves in one universe, the pullback of sheaves of modules at independent universes
is the one already defined.  Both are a chosen left adjoint of the same pushforward, and
adjointness is a `Prop`, so the two differ in no data. -/
theorem pullbackToposGeneral_eq_pullbackTopos (f : RingedToposSiteHom X Y) :
    f.pullbackToposGeneral = f.pullbackTopos :=
  rfl

end AlgebraicGeometry.RingedToposSiteHom

end
