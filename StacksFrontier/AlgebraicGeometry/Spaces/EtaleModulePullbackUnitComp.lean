module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# The unit and composition laws for the pullback of modules along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Stacks 03LV reads the pullback of modules along `f` as plain restriction of
sections along postcomposition of étale charts,
`AlgebraicGeometry.Space.etaleModulePullback`.  In that reading the pseudofunctor laws are
immediate, because postcomposition of charts is *strictly* functorial: the postcomposition
functor of a composite is the composite of the postcomposition functors and that of an identity
is the identity functor, both on the nose.  This file records the two laws for étale
restriction.

## Main results

* `AlgebraicGeometry.Space.smallEtalePostcomp_id`: postcomposition of étale charts along an
  identity morphism is the identity functor.
* `AlgebraicGeometry.Space.etaleModulePullbackIdIso` and
  `AlgebraicGeometry.Space.etaleModulePullbackCompIso`: the unit and composition comparisons for
  étale restriction of modules, both of which are the identity isomorphism.
* `AlgebraicGeometry.Space.etaleModulePullback_congr`: étale restriction depends on the morphism
  only, not on the proof that it is étale.

## Implementation notes

The two laws for `AlgebraicGeometry.Space.etaleModulePullback` are Mathlib's
`SheafOfModules.pushforwardId` and `SheafOfModules.pushforwardComp`, each of which is
`Iso.refl`.  They apply here *unchanged* because
`AlgebraicGeometry.Space.etaleModulePullback` is literally
`SheafOfModules.pushforward` at an identity morphism of sheaves of rings, and because
postcomposition of charts is strictly functorial on the nose — which is
`AlgebraicGeometry.Space.smallEtalePostcomp_id` below for an identity and
`AlgebraicGeometry.Space.smallEtalePostcomp_comp` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompIsoEtaleRestriction.lean` for a
composite, each by `rfl`.  A chart of the small étale site is a costructured arrow whose
underlying object of the big fppf site postcomposition leaves untouched, and the structure maps
`U ⟶ X ⟶ X` and `U ⟶ X` of the identity case agree definitionally in a category of presheaves
of types.

The corresponding unit laws for the inverse image and the direct image of modules of
Stacks 03LU themselves, `AlgebraicGeometry.Space.modulePullbackIdIso` and
`AlgebraicGeometry.Space.modulePushforwardIdIso`, are *not* proved here: they are the content of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackId.lean`, which this file imports
and whose statements it reuses.  Transporting the identity law of étale restriction to the
inverse image instead would need the identification of
`AlgebraicGeometry.Space.structureSharp` at an identity with the canonical comparison of
structure sheaves, which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentTransition.lean` record as the
obstruction to computing the direct image directly.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Postcomposition of étale charts along an identity is the identity functor**, on the nose:
a chart of `X` and its postcomposite with `𝟙 X` have the same underlying object of the big fppf
site and the same structure map. -/
theorem smallEtalePostcomp_id {X : AlgebraicSpaces B S hS}
    (h : IsEtale B S hS (𝟙 X : X ⟶ X).hom) :
    smallEtalePostcomp B S hS (𝟙 X) h = 𝟭 (SmallEtale B S hS X.1) := rfl

/-- Étale restriction of modules depends only on the morphism, not on the proof that it is
étale. -/
theorem etaleModulePullback_congr {X Y : AlgebraicSpaces B S hS} {f g : X ⟶ Y}
    (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom) (h : f = g) :
    etaleModulePullback.{u, m} B S hS f hf = etaleModulePullback.{u, m} B S hS g hg := by
  subst h; rfl

/-- **The unit law for étale restriction of modules**: restriction along an identity morphism of
algebraic spaces is the identity functor.  It is the identity isomorphism, since restriction is
restriction of sections along postcomposition of charts and that functor is the identity. -/
noncomputable def etaleModulePullbackIdIso {X : AlgebraicSpaces B S hS}
    (h : IsEtale B S hS (𝟙 X : X ⟶ X).hom) :
    etaleModulePullback.{u, m} B S hS (𝟙 X) h ≅ 𝟭 (Modules.{u, m} B S hS X.1 X.2) :=
  SheafOfModules.pushforwardId _

/-- **The composition law for étale restriction of modules**: restricting along `g` and then
along `f` is restricting along `f ≫ g`.  It is the identity isomorphism, since postcomposition
of charts is strictly functorial. -/
noncomputable def etaleModulePullbackCompIso {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    (hfg : IsEtale B S hS (f ≫ g).hom) :
    etaleModulePullback.{u, m} B S hS g hg ⋙ etaleModulePullback.{u, m} B S hS f hf ≅
      etaleModulePullback.{u, m} B S hS (f ≫ g) hfg :=
  SheafOfModules.pushforwardComp (F := smallEtalePostcomp B S hS f hf)
    (G := smallEtalePostcomp B S hS g hg) (φ := 𝟙 _) (ψ := 𝟙 _)

end AlgebraicGeometry.Space

end
