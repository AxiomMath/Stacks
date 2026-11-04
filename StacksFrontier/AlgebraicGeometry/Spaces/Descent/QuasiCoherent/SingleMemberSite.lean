module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteModel

/-!
# The charts of a single étale morphism as a site

For a single surjective étale morphism `g : Y ⟶ X` of algebraic spaces, the site of the charts
of the members of the one-member family `{g}` is the site of the charts of `Y`, with the morphisms
of the induced charts of `X`, and the Comparison Lemma
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberRestrictionEquivalence` specializes to it.
The objects of `AlgebraicGeometry.Space.QuasiCoherentDescent.SingleSite` are the charts of `Y`
with no index carried alongside, and the sections of the restriction of an `𝒪_X`-module over a
chart of `Y`, and the ring they are a module over, are by definition those on the small étale
site of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.SingleSite`: the charts of `Y`, with the
  morphisms of the induced charts of `X`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.singleObj` and `…singleHom`: a chart of `Y` and a
  morphism of the induced charts of `X`, read as an object and a morphism of that site.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.singleRing` and `…singleRestriction`: the
  structure sheaf of `X` and the `𝒪_X`-modules, read on that site.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.singleRestrictionEquivalence`: **the Comparison
  Lemma for one surjective étale morphism** — restriction of `𝒪_X`-modules to the charts of `Y`
  is an equivalence onto the modules over the restricted structure sheaf.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.singleRestriction_obj_val_obj`: the sections of
  the restriction of an `𝒪_X`-module over a chart of `Y` are the sections of its étale pullback
  along `g` over that chart.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.singleRing_obj_obj`: the ring they are a module
  over is the structure ring of the chart, read on the small étale site of `Y`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isCoverDense_singleFunctor`: the charts of `Y`
  are cover dense in the small étale site of `X`, for a surjective étale `g`.

## Implementation notes

The index type is `PUnit.{u + 1}`, not `Unit`, because
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberRestrictionEquivalence` is built for a family
indexed by a type in the universe of the schemes; a covering indexed by `Unit` is carried to one
indexed by `PUnit.{u + 1}` by `AlgebraicGeometry.Space.IsEtaleCovering.reindex`.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)

/-- The one-member family attached to a single morphism of algebraic spaces, indexed by the
one-element type of the universe of the schemes. -/
abbrev singleFamily : PUnit.{u + 1} → AlgebraicSpaces B S hS := fun _ => Y

/-- The one-member family of morphisms attached to a single morphism. -/
abbrev singleMap : ∀ i : PUnit.{u + 1}, singleFamily B S hS (Y := Y) i ⟶ X := fun _ => g

/-- Every member of the one-member family is étale. -/
abbrev singleEtale : ∀ i, IsEtale B S hS (singleMap B S hS g i).hom := fun _ => hg

/-- **The site of the charts of a single étale morphism**: the charts of `Y`, with the morphisms
of the induced charts of `X`. -/
abbrev SingleSite : Type (u + 1) :=
  MemberSite B S hS (singleFamily B S hS (Y := Y)) (singleMap B S hS g) (singleEtale B S hS g hg)

/-- A chart of `Y`, as an object of the site of the charts of `g`. -/
abbrev singleObj (V : SmallEtale B S hS Y.1) : SingleSite B S hS g hg := ⟨PUnit.unit, V⟩

/-- A morphism of the induced charts of `X`, as a morphism of the site of the charts of `g`. -/
abbrev singleHom {V W : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj W) :
    singleObj B S hS g hg V ⟶ singleObj B S hS g hg W :=
  InducedCategory.homMk k

/-- The morphism of the induced charts of `X` underlying a morphism of the site of the charts of
`g`. -/
abbrev singleHomOut {V W : SmallEtale B S hS Y.1}
    (k : singleObj B S hS g hg V ⟶ singleObj B S hS g hg W) :
    (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj W :=
  k.hom

/-- The two readings of a morphism of the site of the charts of `g` are inverse. -/
theorem singleHom_singleHomOut {V W : SmallEtale B S hS Y.1}
    (k : singleObj B S hS g hg V ⟶ singleObj B S hS g hg W) :
    singleHom B S hS g hg (singleHomOut B S hS g hg k) = k := rfl

/-- The two readings of a morphism of the induced charts of `X` are inverse. -/
theorem singleHomOut_singleHom {V W : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj W) :
    singleHomOut B S hS g hg (singleHom B S hS g hg k) = k := rfl

/-- The functor from the charts of `g` to the charts of `X`. -/
abbrev singleFunctor : SingleSite B S hS g hg ⥤ SmallEtale B S hS X.1 :=
  memberFunctor B S hS (singleFamily B S hS (Y := Y)) (singleMap B S hS g)
    (singleEtale B S hS g hg)

/-- The topology of the charts of `g`, restricted from the small étale topology of `X`. -/
abbrev singleTopology : GrothendieckTopology (SingleSite B S hS g hg) :=
  memberTopology B S hS (singleFamily B S hS (Y := Y)) (singleMap B S hS g)
    (singleEtale B S hS g hg)

/-- **The charts of a surjective étale morphism are cover dense in the small étale site of the
target.**  Here `g` is given as an étale covering of `X` indexed by `Unit`. -/
theorem isCoverDense_singleFunctor
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => Y.1) (fun _ => g.hom)) :
    (singleFunctor B S hS g hg).IsCoverDense (SmallEtale.topology B S hS X.1) :=
  isCoverDense_memberFunctor B S hS (singleFamily B S hS (Y := Y)) (singleMap B S hS g)
    (singleEtale B S hS g hg)
    (hcov.reindex B S hS (σ := fun _ : PUnit.{u + 1} => ()) fun _ => ⟨PUnit.unit, rfl⟩)

section CoverDense

variable [(singleFunctor B S hS g hg).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- The structure sheaf of `X`, read on the charts of `g`. -/
abbrev singleRing : Sheaf (singleTopology B S hS g hg) RingCat.{u} :=
  memberRing B S hS (singleFamily B S hS (Y := Y)) (singleMap B S hS g)
    (singleEtale B S hS g hg)

/-- Restriction of `𝒪_X`-modules to the charts of `g`. -/
abbrev singleRestriction :
    Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u} (singleRing B S hS g hg) :=
  memberRestriction B S hS (singleFamily B S hS (Y := Y)) (singleMap B S hS g)
    (singleEtale B S hS g hg)

/-- **The Comparison Lemma for the charts of one surjective étale morphism.**  Restriction of
`𝒪_X`-modules to the charts of `Y` is an equivalence onto the modules over the restricted
structure sheaf. -/
def singleRestrictionEquivalence :
    Modules.{u, u} B S hS X.1 X.2 ≌ SheafOfModules.{u} (singleRing B S hS g hg) :=
  memberRestrictionEquivalence B S hS (singleFamily B S hS (Y := Y)) (singleMap B S hS g)
    (singleEtale B S hS g hg)

/-- The equivalence is restriction itself. -/
theorem singleRestrictionEquivalence_functor :
    (singleRestrictionEquivalence B S hS g hg).functor = singleRestriction B S hS g hg := rfl

/-- **Restriction of `𝒪_X`-modules to the charts of `g` is an equivalence.** -/
instance isEquivalence_singleRestriction : (singleRestriction B S hS g hg).IsEquivalence :=
  isEquivalence_memberRestriction B S hS (singleFamily B S hS (Y := Y)) (singleMap B S hS g)
    (singleEtale B S hS g hg)

/-- **The sections of the restriction of an `𝒪_X`-module over a chart of `Y` are the sections of
its étale pullback along `g` over that chart.** -/
theorem singleRestriction_obj_val_obj (M : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1) :
    ((singleRestriction B S hS g hg).obj M).val.obj (.op (singleObj B S hS g hg V)) =
      ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (.op V) :=
  rfl

/-- **The ring the sections over a chart of `Y` are a module over is the structure ring of that
chart**, read on the small étale site of `Y`. -/
theorem singleRing_obj_obj (V : SmallEtale B S hS Y.1) :
    (singleRing B S hS g hg).obj.obj (.op (singleObj B S hS g hg V)) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (.op V) :=
  rfl

/-- The restriction of a morphism of `𝒪_X`-modules, over a chart of `Y`, is its étale pullback
along `g` read on sections over that chart. -/
theorem singleRestriction_map_val_app {M N : Modules.{u, u} B S hS X.1 X.2} (ψ : M ⟶ N)
    (V : SmallEtale B S hS Y.1) :
    ((singleRestriction B S hS g hg).map ψ).val.app (.op (singleObj B S hS g hg V)) =
      ((etaleModulePullback.{u, u} B S hS g hg).map ψ).val.app (.op V) :=
  rfl

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
