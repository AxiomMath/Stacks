module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFullyFaithful.PullbackModuleFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.ClosedImmersion.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The direct image of modules along a closed immersion of ringed topoi is fully faithful

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi which is a closed immersion of
topoi and whose structure map `i^# : O' ⟶ i_*O` is locally surjective. Stacks 08M3 asserts,
among other things, that the direct image `i_* : Mod(O) ⥤ Mod(O')` is fully faithful.

The direct image on sheaves of modules of a morphism of ringed topoi is the Stacks 03D1 direct
image followed by restriction of scalars along the structure map, which is
`AlgebraicGeometry.RingedToposHom.pushforwardModules` below. Both factors are fully faithful
under the hypotheses of a closed immersion, for separate reasons: the Stacks 03D1 direct image
because `i_*` is fully faithful on sheaves of sets, an embedding of topoi being exactly that
(`Stacks.Sheaves.ToposPushforward.fullyFaithfulPushforwardModuleFunctor`); restriction of
scalars because `i^#` is locally surjective, which is Stacks 0930
(`Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective`).

## Main definitions

* `AlgebraicGeometry.RingedToposHom.structureRingMap`: the structure map of a morphism of ringed
  topoi, read as a morphism of the underlying sheaves of rings.
* `AlgebraicGeometry.RingedToposHom.pushforwardModules`: the direct image on sheaves of modules
  of a morphism of ringed topoi.

## Main results

* `AlgebraicGeometry.RingedToposHom.pushforwardModulesUnderlyingIso`: the underlying sheaf of
  sets of a pushed-forward sheaf of modules is the direct image of the underlying sheaf of sets,
  naturally in the module.
* `AlgebraicGeometry.ClosedRingedImmersion.structureRingMap_isLocallySurjective`: the structure
  map of a closed immersion of ringed topoi is locally surjective as a morphism of sheaves of
  rings.
* `AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful`: **Stacks 08M3**,
  full faithfulness of the direct image on sheaves of modules.

## Implementation notes

`AlgebraicGeometry.ClosedRingedImmersion` records local surjectivity of the structure map after
forgetting all ring structure, i.e. as a morphism of sheaves of *sets*, while Stacks 0930 wants
it as a morphism of sheaves of *rings*. The two are the same condition, because local
surjectivity of a morphism of presheaves valued in a concrete category is by definition that of
the underlying morphism of presheaves of sets; `Presheaf.isLocallySurjective_iff_whisker_forget`
is the passage, and the forgetful functor of `CommRingCat` factors through `RingCat` on the nose.

Full faithfulness of the composite is `CategoryTheory.Functor.FullyFaithful.comp` of the two
factors. The statement is phrased with `Nonempty` because `Functor.FullyFaithful` is data:
asserting full faithfulness should not choose inverses to the maps on hom sets.

The structure map of `AlgebraicGeometry.RingedToposHom` is *typed by* the direct image of
sheaves of commutative rings, so the structure map at the level of sheaves of rings is the
image of `f♯` under the forgetful functor and nothing else: there is no comparison isomorphism
between the direct image of the structure sheaf and a separately constructed sheaf of rings to
compose with, because the two are the same object.

Stacks 03D6 part (1) is already recorded on
`Stacks.Sheaves.RingedToposModules.pushforwardModules`, which is the same construction for the
four-field `Stacks.Sheaves.RingedToposModules.RingedToposHom`. That structure is a strictly
richer datum than the two-field one of Stacks 01D3 part (2) — it stores the inverse-image form
of the structure map and the equation making the two adjunct — and
`AlgebraicGeometry.ClosedRingedImmersion` carries the two-field one, so that functor cannot be
applied here. `pushforwardModules` below is therefore not tagged: a second `@[stacks 03D6]`
attribute would record a second formalization of one clause.

The direct image of modules is stated for a morphism of ringed topoi with the two section
universes independent, as the construction allows; a `ClosedRingedImmersion` has them equal
because its underlying morphism of topoi does.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

universe v u w v' u' w'

namespace AlgebraicGeometry

namespace RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- The structure map `f♯ : O_D ⟶ f_*O_C` of a morphism of ringed topoi, read as a morphism of
the underlying sheaves of rings. Sheaves of modules are taken over sheaves of rings rather than
over sheaves of commutative rings, so this is the form in which the structure map restricts
scalars; the direct image of the underlying sheaf of rings of `O_C` is the underlying sheaf of
rings of the direct image of `O_C`, which is why no comparison isomorphism intervenes. -/
noncomputable def structureRingMap :
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O ⟶
      pushforwardRingSheaf f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) :=
  (Stacks.forgetCommRingSheaf Y.J).map f.fSharp

/-- The direct image on sheaves of modules of a morphism of ringed topoi: the Stacks 03D1
direct image, followed by restriction of scalars along the structure map. This is the content
of Stacks 03D6 part (1) at the two-field morphism of ringed topoi of Stacks 01D3 part (2); see
the implementation notes for why the tag sits elsewhere. It is
`Stacks.Sheaves.ToposPushforward.pushforwardModulesAlong` at the structure map. -/
noncomputable def pushforwardModules :
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⥤
      SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) :=
  pushforwardModulesAlong f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)
    f.structureRingMap

/-- The underlying sheaf of sets of a pushed-forward sheaf of modules is the direct image of the
underlying sheaf of sets, naturally in the module: neither the Stacks 03D1 direct image nor
restriction of scalars changes the underlying sheaf of sets. -/
noncomputable def pushforwardModulesUnderlyingIso :
    f.pushforwardModules ⋙
        Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ≅
      Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        f.toToposHom.pushforward :=
  Iso.refl _

end RingedToposHom

namespace ClosedRingedImmersion

variable (S : ClosedRingedImmersion.{v, u, v', u', w})

/-- The structure map of a closed immersion of ringed topoi is locally surjective as a morphism
of sheaves of rings. The structure carries local surjectivity of the morphism of sheaves of
sets underlying the structure map, and local surjectivity of a morphism of sheaves valued in a
concrete category is that of the underlying morphism of sheaves of sets. -/
theorem structureRingMap_isLocallySurjective :
    Sheaf.IsLocallySurjective S.hom.structureRingMap := by
  change Presheaf.IsLocallySurjective S.target.J S.hom.structureRingMap.hom
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  exact S.structureMap_surjective

/-- **Stacks 08M3.** The direct image of sheaves of modules along a closed immersion of ringed
topoi with locally surjective structure map is fully faithful.

The direct image is the Stacks 03D1 direct image followed by restriction of scalars along the
structure map. The first factor is fully faithful because the direct image of sheaves of sets
is, the underlying morphism of topoi being an embedding; the second is fully faithful by
Stacks 0930, the structure map being locally surjective. -/
@[stacks 08M3 "full_faithfulness"]
theorem pushforwardModules_fullyFaithful :
    Nonempty S.hom.pushforwardModules.FullyFaithful := by
  have : S.hom.toToposHom.pushforward.Full := S.isClosedImmersion.1.full
  have : S.hom.toToposHom.pushforward.Faithful := S.isClosedImmersion.1.faithful
  have : Sheaf.IsLocallySurjective S.hom.structureRingMap :=
    S.structureRingMap_isLocallySurjective
  exact ⟨(fullyFaithfulPushforwardModuleFunctor S.hom.toToposHom _).comp
    (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
      S.hom.structureRingMap)⟩

end ClosedRingedImmersion

end AlgebraicGeometry

end
