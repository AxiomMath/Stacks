module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidal
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of sheaves of modules along a morphism of ringed spaces is monoidal

Let `f : X ⟶ Y` be a morphism of ringed spaces.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidal` proves that the **presheaf**-level
module pullback is a strong monoidal functor, with full coherence, and that its tensorator is the
presheaf-level comparison of Tag 01CD. This file lifts that statement to **sheaves** of modules:
`Stacks.PullbackMonoidalSheaf.pullbackMonoidal` equips
`RingedSpaceModuleAdjunction.modulePullback f` with a `CategoryTheory.Functor.Monoidal` structure
for the monoidal structure `Stacks.SheafOfModules.monoidalCategory` on each side.

The lift is one application of `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`: the
monoidal structure on sheaves of modules *is* the localization of the objectwise monoidal
structure on presheaves of modules along sheafification, so a functor out of it is monoidal as
soon as its composite with sheafification is, and Mathlib's
`SheafOfModules.sheafificationCompPullback` is exactly the required lifting isomorphism
`sheafification ⋙ f^* ≅ f^*_pre ⋙ sheafification`.

As a consequence, **Stacks Tag 0B8L**: the pullback of an invertible sheaf of modules is
invertible. With `f^*` monoidal this is `CategoryTheory.MonoidalCategory.IsInvertible.map` together
with the agreement of the two notions of invertibility
(`Stacks.SheafOfModules.isInvertible_iff_monoidalIsInvertible`), and nothing else.

## Main definitions

* `Stacks.PullbackMonoidalSheaf.sheafifyFunctor`, `localIso`, `sheafifyUnitIso`,
  `monoidalCategory`, `sheafifyFunctorMonoidal` and `isLocalization`: the data of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal` at a ringed space. Each is a one-step
  instantiation of the corresponding declaration there, retyped over
  `Stacks.RingedSpace.structureRingSheaf`; see the implementation notes for why the retyping is
  forced.
* `Stacks.PullbackMonoidalSheaf.sheafifiedPresheafPullback` and
  `sheafifiedPresheafPullbackMonoidal`: the presheaf-level pullback followed by sheafification,
  monoidal as a composite of two monoidal functors.
* `Stacks.PullbackMonoidalSheaf.liftingIso` and `lifting`: Mathlib's
  `SheafOfModules.sheafificationCompPullback`, retyped, and the
  `CategoryTheory.Localization.Lifting` instance it provides.
* `Stacks.PullbackMonoidalSheaf.pullbackMonoidal`: **the pullback of sheaves of modules along a
  morphism of ringed spaces is a monoidal functor.**

## Main results

* `Stacks.PullbackMonoidalSheaf.pullbackMonoidal_mu`: **where the structure map is pinned.** The
  tensorator of `pullbackMonoidal`, at a pair of sheafified presheaves, is the tensorator of
  `sheafifiedPresheafPullback` conjugated by the lifting isomorphism and by the tensorator of
  sheafification on the source site.
* `Stacks.PullbackMonoidalSheaf.presheafPullback_mu_comp`: the tensorator of the presheaf-level
  pullback is inverse to `Stacks.PullbackTensor.pullbackTensorIso`, the presheaf-level comparison
  of Tag 01CD. Together with the previous result this says precisely which comparison the sheaf
  tensorator is built from.
* `Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj`: **Stacks Tag 0B8L**, the
  pullback of an invertible sheaf of modules is invertible.

## Implementation notes

**Where the canonicity claim lands, and where it does not.** The two results above pin the sheaf
tensorator to a composite whose only non-formal ingredient is
`Stacks.PullbackTensor.pullbackTensorIso`, the **presheaf**-level 01CD comparison. They do **not**
identify it with `Stacks.RingedSpace.comparison`, the sheaf-level comparison that carries
`@[stacks 01CD]`. That identification is a separate statement and is not proved here: it is the
sheaf-level analogue of `Stacks.PullbackTensor.pullbackTensorSheafObjIso_hom_eq_comparison`, and
proving it would need the action on local sections of
`CategoryTheory.Localization.Monoidal.μ` and of `Stacks.SheafOfModules.tensorObjIso`, neither of
which is available — the localized monoidal structure has no sectionwise formulas, as the
implementation notes of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal` record. So the
honest statement is: what is built here is *a* monoidal structure on `f^*` whose tensorator is
assembled from the canonical presheaf-level comparison, not one whose tensorator is provably
`Stacks.RingedSpace.comparison`. Tag 0B8L does not need the stronger statement, because
invertibility is a proposition and `IsInvertible.map` holds for any monoidal structure.

**No new tensor product and no new monoidal structure.** Every monoidal structure used already
existed: Mathlib's `PresheafOfModules.monoidalCategory` at the presheaf level, and
`Stacks.SheafOfModules.monoidalCategory` at the sheaf level. The declarations `monoidalCategory`,
`sheafifyFunctorMonoidal` and `isLocalization` below are *the same terms* under new names, not
parallel constructions: each is defined by `:=` from the corresponding declaration of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal`, so they are definitionally equal to it
and nothing can diverge.

**Why the retyping is forced.** `Stacks.SheafOfModules.monoidalCategory` and its companions are
indexed by a presheaf of commutative rings `𝒪` together with a proof that
`𝒪 ⋙ forget₂ CommRingCat RingCat` is a sheaf, and their statements mention the sheaf of rings in
the spelling `Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪`. The ringed-space
pullback `RingedSpaceModuleAdjunction.modulePullback` is indexed instead by
`Stacks.RingedSpace.structureRingSheaf X`, i.e. by `CategoryTheory.Sheaf.toRingCat` of the
structure sheaf. The two are equal by `rfl` (`structureSheaf_eq` below) but not syntactically
equal, and the discrimination-tree key of an instance built at one spelling does not match a goal
written in the other, so instance search finds nothing: with
`attribute [local instance] Stacks.SheafOfModules.monoidalCategory` the goal
`MonoidalCategory (SheafOfModules (Stacks.RingedSpace.structureRingSheaf Z))` fails. Naming each
instance once, at the `structureRingSheaf` spelling, and letting the defeq check of `:=` cross the
boundary, is what makes the chain elaborate. This is the "three instances are restated here to
short-circuit instance search" discipline of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso` and the "ascribe the type, do not
rewrite" discipline of `...PullbackMonoidal`; no limit is raised anywhere.

For the same reason `sheafifyFunctor`, `sheafifiedPresheafPullback` and `liftingIso` carry an
**ascribed** type rather than inheriting the type of their right-hand side. Without the ascription
on `sheafifyFunctor` the goal `(sheafifyFunctor Z).IsLocalization (localIso Z)` is sought at the
other spelling and fails; with it, the tensor notation `⊗ₘ` in `pullbackMonoidal_mu` resolves
against `monoidalCategory`.

**Universes.** Everything is at a single universe `u`. That is forced by
`RingedSpaceModuleAdjunction.modulePullback`, which exists only for `RingedSpace.{u, u}` with
modules in `u`, and by Mathlib's monoidal structure on presheaves of modules, which is declared
only for `PresheafOfModules.{u}` over a ring presheaf `𝒪 ⋙ forget₂ CommRingCat.{u} RingCat.{u}`.
Nothing is narrowed relative to the imported files.

## References

* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace

universe u

namespace Stacks.PullbackMonoidalSheaf

/-! ### The data of the localized monoidal structure, at a ringed space -/

/-- The two spellings of the structure sheaf of a ringed space as a sheaf of not necessarily
commutative rings agree on the nose: the one indexed by a presheaf of commutative rings together
with a sheaf condition, and the one obtained by postcomposing with
`forget₂ CommRingCat RingCat`. -/
theorem structureSheaf_eq (Z : RingedSpace.{u, u}) :
    Stacks.SheafOfModules.TensorSheafification.structureSheaf Z.presheaf
      (structureSheafRing Z).property =
      structureRingSheaf Z :=
  rfl

/-- Sheafification of presheaves of `𝒪_Z`-modules, with its target spelled over
`Stacks.RingedSpace.structureRingSheaf`, which is the spelling the ringed-space pullback uses. -/
@[sga "4 IV 12.4" "A-module structure on aM"]
noncomputable abbrev sheafifyFunctor (Z : RingedSpace.{u, u}) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      Z.presheaf) ⥤
      SheafOfModules.{u} (structureRingSheaf Z) :=
  Stacks.SheafOfModules.sheafifyFunctor Z.presheaf (structureSheafRing Z).property

/-- The class of morphisms of presheaves of `𝒪_Z`-modules inverted by sheafification. -/
abbrev localIso (Z : RingedSpace.{u, u}) :
    MorphismProperty (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Z.presheaf)) :=
  Stacks.SheafOfModules.localIso (J := Opens.grothendieckTopology Z.carrier) Z.presheaf

/-- Sheafification is the localization functor at the local isomorphisms, as a one-step
instantiation at the spelling used here. -/
instance isLocalization (Z : RingedSpace.{u, u}) :
    (sheafifyFunctor Z).IsLocalization (localIso Z) :=
  Stacks.SheafOfModules.isLocalization_sheafify Z.presheaf (structureSheafRing Z).property

/-- The sheafification of the presheaf tensor unit is `SheafOfModules.unit`, as a one-step
instantiation at the spelling used here. This is the preferred unit object of the localized
monoidal structure. -/
noncomputable abbrev sheafifyUnitIso (Z : RingedSpace.{u, u}) :
    (sheafifyFunctor Z).obj
        (𝟙_ (PresheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
          Z.presheaf))) ≅
      SheafOfModules.unit (structureRingSheaf Z) :=
  Stacks.SheafOfModules.sheafifyUnitIso Z.presheaf (structureSheafRing Z).property

/-- The monoidal structure on sheaves of `𝒪_Z`-modules of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal`, as a one-step instantiation at the
spelling used here. It is the same term, not a second monoidal structure. -/
@[instance_reducible]
noncomputable def monoidalCategory (Z : RingedSpace.{u, u}) :
    MonoidalCategory (SheafOfModules.{u} (structureRingSheaf Z)) :=
  Stacks.SheafOfModules.monoidalCategory Z.presheaf (structureSheafRing Z).property

attribute [local instance] monoidalCategory

/-- Sheafification of presheaves of modules is a monoidal functor, as a one-step instantiation at
the spelling used here. -/
@[instance_reducible]
noncomputable def sheafifyFunctorMonoidal (Z : RingedSpace.{u, u}) :
    (sheafifyFunctor Z).Monoidal :=
  Stacks.SheafOfModules.sheafifyFunctor_monoidal Z.presheaf (structureSheafRing Z).property

attribute [local instance] sheafifyFunctorMonoidal

/-! ### The presheaf-level pullback followed by sheafification -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The presheaf-level pullback of modules along `f`, followed by sheafification on the target
site. This is the functor that `sheafification ⋙ f^*` lifts. -/
noncomputable abbrev sheafifiedPresheafPullback :
    PresheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      Y.presheaf) ⥤
      SheafOfModules.{u} (structureRingSheaf X) :=
  PresheafOfModules.pullback.{u} (Stacks.PullbackMonoidal.structurePresheafHom f) ⋙
    sheafifyFunctor X

/-- The presheaf-level pullback followed by sheafification is monoidal, as a composite of the
monoidal functor `Stacks.PullbackMonoidal.presheafPullbackMonoidal` with the monoidal localization
functor on the target site. -/
@[instance_reducible]
noncomputable def sheafifiedPresheafPullbackMonoidal :
    (sheafifiedPresheafPullback f).Monoidal :=
  letI := Stacks.PullbackMonoidal.presheafPullbackMonoidal f
  inferInstance

attribute [local instance] sheafifiedPresheafPullbackMonoidal

/-- **Pullback of modules commutes with sheafification**, Mathlib's
`SheafOfModules.sheafificationCompPullback`, retyped so that both sides are spelled with the
functors named in this file. This is the lifting isomorphism of the localization. -/
noncomputable abbrev liftingIso :
    sheafifyFunctor Y ⋙ pullbackFunctor f ≅ sheafifiedPresheafPullback f :=
  SheafOfModules.sheafificationCompPullback.{u} (structureSheafHom f)

/-- The sheaf-level pullback lifts the presheaf-level pullback followed by sheafification, along
sheafification on the source site. -/
noncomputable instance lifting :
    Localization.Lifting (sheafifyFunctor Y) (localIso Y) (sheafifiedPresheafPullback f)
      (pullbackFunctor f) :=
  ⟨liftingIso f⟩

/-! ### The pullback of sheaves of modules is monoidal -/

/-- **The pullback of sheaves of modules along a morphism of ringed spaces is a monoidal
functor**, for the monoidal structure `Stacks.SheafOfModules.monoidalCategory` on each side.

The monoidal structure on sheaves of modules is the localization of the objectwise one on
presheaves of modules along sheafification, so this follows from monoidality of the
presheaf-level pullback by
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`. -/
@[instance_reducible, ega "0 4.3.4" "partial"]
noncomputable def pullbackMonoidal : (pullbackFunctor f).Monoidal :=
  Localization.Monoidal.functorMonoidalOfComp (sheafifyFunctor Y) (localIso Y)
    (pullbackFunctor f) (sheafifiedPresheafPullback f)

/-- The tensorator of the presheaf-level pullback is inverse to
`Stacks.PullbackTensor.pullbackTensorIso`, the presheaf-level comparison of Tag 01CD. This is the
only non-formal ingredient of the sheaf-level tensorator computed in `pullbackMonoidal_mu`. -/
theorem presheafPullback_mu_comp
    (M N : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      Y.presheaf)) :
    Functor.LaxMonoidal.μ
          (self := (Stacks.PullbackMonoidal.presheafPullbackMonoidal f).toLaxMonoidal)
          (PresheafOfModules.pullback.{u} (Stacks.PullbackMonoidal.structurePresheafHom f)) M N ≫
        (Stacks.PullbackTensor.pullbackTensorIso f.hom.c).hom.app (M, N) =
      CategoryStruct.id _ :=
  let := Stacks.PullbackMonoidal.presheafPullbackMonoidal f
  (congrArg (fun g => Functor.LaxMonoidal.μ
      (PresheafOfModules.pullback.{u} (Stacks.PullbackMonoidal.structurePresheafHom f)) M N ≫ g)
    (Stacks.PullbackMonoidal.presheafPullbackMonoidal_delta f M N)).symm.trans
    (Functor.Monoidal.μ_δ _ M N)

/-- **Where the structure map of `pullbackMonoidal` is pinned.** At a pair of sheafified presheaves
the tensorator is the tensorator of `sheafifiedPresheafPullback`, conjugated by the lifting
isomorphism `liftingIso` and by the tensorator of sheafification on the source site.

Together with `presheafPullback_mu_comp` this says the sheaf-level tensorator is assembled from the
*presheaf*-level comparison of Tag 01CD. It is **not** a statement that it equals
`Stacks.RingedSpace.comparison`; see the implementation notes. -/
theorem pullbackMonoidal_mu
    (M N : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      Y.presheaf)) :
    Functor.LaxMonoidal.μ (self := (pullbackMonoidal f).toLaxMonoidal) (pullbackFunctor f)
        ((sheafifyFunctor Y).obj M) ((sheafifyFunctor Y).obj N) =
      (((liftingIso f).hom.app M ⊗ₘ (liftingIso f).hom.app N) ≫
          Functor.LaxMonoidal.μ (self := (sheafifiedPresheafPullbackMonoidal f).toLaxMonoidal)
            (sheafifiedPresheafPullback f) M N) ≫
        (liftingIso f).inv.app (M ⊗ N) ≫
          (pullbackFunctor f).map
            (Functor.OplaxMonoidal.δ (self := (sheafifyFunctorMonoidal Y).toOplaxMonoidal)
              (sheafifyFunctor Y) M N) :=
  Localization.Monoidal.functorMonoidalOfComp_μ (sheafifyFunctor Y) (localIso Y)
    (pullbackFunctor f) (sheafifiedPresheafPullback f) M N

/-! ### Stacks 0B8L -/

/-- The pullback of an invertible sheaf of modules along a morphism of ringed spaces is
invertible, at the `(structureSheafRing _).property` spelling of the sheaf condition.

With `f^*` monoidal this is `CategoryTheory.MonoidalCategory.IsInvertible.map` — a monoidal functor
preserves invertible objects, the observation Stacks makes just after Tag 0FFN — read through the
agreement of the two notions of invertibility,
`Stacks.SheafOfModules.isInvertible_iff_monoidalIsInvertible` (Tags 0FFM and 0FFN).

This is `Stacks.RingedSpace.modulePullback_isInvertible` with `pullbackFunctor` and the sheaf
condition written out (`pullbackFunctor` is an `abbrev` for `modulePullback`, and
`structureRingSheaf X = structureSheafRing X` by `rfl`), registered as an `instance` at this
spelling of the sheaf condition. -/
@[instance]
theorem isInvertible_pullbackFunctor_obj (L : SheafOfModules.{u} (structureRingSheaf Y))
    [Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y).property L] :
    Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property
      ((pullbackFunctor f).obj L) :=
  let := pullbackMonoidal f
  Stacks.SheafOfModules.isInvertible_of_monoidalIsInvertible X.presheaf
    (structureSheafRing X).property
    (MonoidalCategory.IsInvertible.map (pullbackFunctor f)
      ((Stacks.SheafOfModules.isInvertible_iff_monoidalIsInvertible Y.presheaf
        (structureSheafRing Y).property L).mp inferInstance))

end Stacks.PullbackMonoidalSheaf

end
