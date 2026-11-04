module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.Homology.Tor.IndependenceFlatModule
import StacksCore.Tactic.StacksAttribute

/-!
# Tor-independent base change of algebraic spaces, and relative Tor amplitude

Let `S` be a scheme and let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over `S` with `f` and `g` Tor independent.  Stacks
0DKD says that derived pullback along `g'` preserves Tor amplitude in `[a, b]` relative to the
base, and that the derived pullback of an `𝒪_X`-module flat over `Y` is its ordinary pullback.

The source proves both clauses at the geometric points of `X'`: its argument is "we can
compute tor dimension at stalks, see Cohomology on Sites, Lemma 0DJJ and Properties of Spaces,
Theorem 04K5", followed by the identification
`(L(g')^*E)_{x̄'} = E_{x̄} ⊗^{\mathbf L}_{𝒪_{X, x̄}} 𝒪_{X', x̄'}` and an application of More on
Algebra, Lemmas 0661 and 066L to the étale local rings.  This file provides the inputs of that
application at a geometric point `x̄'` of `X'` with images `x̄` in `X`, `ȳ'` in `Y'` and `ȳ` in
`Y`, stated at the canonical maps of étale local rings of Stacks 04NG: Tor independence of the
étale local rings, and the cartesian input `IsEtaleStalkTensorFlat`.  Both clauses are proved
at the level of sheaves, as
`AlgebraicGeometry.Space.hasTorAmplitude_derivedScalarRestriction_smallEtaleDerivedModulePullback`
and `AlgebraicGeometry.Space.isIso_smallEtaleDerivedModulePullbackComparison_of_isFlatOver`.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleStalkTensorFlat` is the cartesian input: the étale local ring
  of the upper-left corner is a flat algebra over `𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}` through a
  ring map restricting on the two factors to the canonical maps of Stacks 04NG.

## Main results

* `AlgebraicGeometry.Space.torIndependent_etaleLocalRing`: Tor independence of two algebraic
  spaces over a base, Stacks 08IP, read at the *canonical* homomorphisms of étale local rings
  of Stacks 04NG rather than at the existential witnesses its definition quantifies over.

## Implementation notes

`AlgebraicGeometry.Space.TorIndependent` of Stacks 08IP asks, at each compatible pair of
geometric points, for the *existence* of homomorphisms of étale local rings compatible with
the germ maps in the sense of `AlgebraicGeometry.Space.IsEtaleLocalRingMap`, because no
canonical homomorphism is available for a general morphism of algebraic spaces at the point
where that definition is made.  Stacks 04NG, in the form
`AlgebraicGeometry.Space.existsUnique_etaleLocalRingMap`, says that such a homomorphism is
unique, so the witnesses *are* the canonical maps
`AlgebraicGeometry.Space.etaleLocalRingMap`; `torIndependent_etaleLocalRing` performs that
identification once, so that statements using it are made entirely with the canonical
maps.  This is what makes their algebra structures the ones the ring-level engine looks for:
the scalar towers of the tensor product are pinned by the explicit factorizations that
`IsEtaleStalkTensorFlat` carries, and an instance stated at a different spelling of the same
map is not found.

The four étale local rings of Stacks 04KG live in `CommRingCat.{u + 1}` — each is a colimit
indexed by the small étale neighbourhoods of a geometric point, which is a type one universe
above the schemes — so the ring-level notions are instantiated at `u + 1`.  All four rings lie
in the *same* universe, so no lift is interposed.

`IsEtaleStalkTensorFlat` is the analogue of the cartesian input to
`AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_stalk_of_cartesian` and to
the stalkwise input to Stacks 0C0V used by
`AlgebraicGeometry.pullback_quasiIso_of_isFlatOver`
(`StacksFrontier/AlgebraicGeometry/Perfect/RelativeTorAmplitudeBaseChange.lean`), with the scheme
stalk maps replaced by the canonical maps of étale local rings.  On the scheme side the
cartesian input is a theorem,
`AlgebraicGeometry.BaseChangeStalk.cartesian_stalk_tensor_flat`: the local ring of the
upper-left corner is a localization of the tensor product.  For algebraic spaces it is
`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat`
(`StacksFrontier/AlgebraicGeometry/Spaces/EtaleLocalRingFibreProduct.lean`): `IsEtaleStalkTensorFlat`
holds at every geometric point of every cartesian square.

The equality of the two images of `x̄'` in `Y` is `IsPullback.w` transported by
`congrArg`: `AlgebraicGeometry.Space.geometricPointMap` is functorial by `rfl`, and the
morphisms of `AlgebraicGeometry.AlgebraicSpaces` compose by `rfl` on their underlying maps of
presheaves, so `geometricPointMap (g' ≫ f).hom x̄'` and
`geometricPointMap f.hom (geometricPointMap g'.hom x̄')` are the same term and no transport
along an equality of geometric points is needed beyond the one `eqToHom` that
`AlgebraicGeometry.Space.TorIndependent` itself carries.

## References

* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 0C0V](https://stacks.math.columbia.edu/tag/0C0V)
* [Stacks Project, Tag 08IP](https://stacks.math.columbia.edu/tag/08IP)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 066L](https://stacks.math.columbia.edu/tag/066L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Tor independence at the canonical homomorphisms of étale local rings -/

/-- **Stacks 08IP at the canonical maps.** Tor independence of `X` and `G` over `Y` gives, at
every compatible pair of geometric points, Tor independence of the étale local rings for the
algebra structures defined by the *canonical* homomorphisms of étale local rings of
Stacks 04NG.

The definition of `AlgebraicGeometry.Space.TorIndependent` quantifies over the existence of
germ-compatible homomorphisms; Stacks 04NG says such a homomorphism is unique, so the
witnesses are the canonical maps. -/
theorem torIndependent_etaleLocalRing {X G Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : G ⟶ Y) (htor : TorIndependent X.2 G.2 Y.2 f.hom g.hom)
    (x : GeometricPoint B S hS X.1) (y : GeometricPoint B S hS G.1)
    (h : geometricPointMap f.hom x = geometricPointMap g.hom y) :
    letI : Algebra ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x))
        ↥(etaleLocalRing B S hS X.1 x) := (etaleLocalRingMap X.2 f.hom x).toAlgebra
    letI : Algebra ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x))
        ↥(etaleLocalRing B S hS G.1 y) :=
      ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) h) ≫
        CommRingCat.ofHom (etaleLocalRingMap G.2 g.hom y)).hom).toAlgebra
    RingTheory.TorIndependence.TorIndependent
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x))
      ↥(etaleLocalRing B S hS X.1 x) ↥(etaleLocalRing B S hS G.1 y) := by
  obtain ⟨φ, ψ, hφ, hψ, hti⟩ := htor x y h
  obtain rfl := eq_etaleLocalRingMap X.2 f.hom x hφ
  obtain rfl := eq_etaleLocalRingMap G.2 g.hom y hψ
  exact hti

/-! ### The cartesian input -/

/-- The cartesian input to Stacks 0DKD at a geometric point `x'` of the upper-left corner: the
étale local ring `𝒪_{X', x̄'}` is a flat algebra over
`𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}` through a ring map restricting on the two factors to the
canonical homomorphisms of étale local rings of Stacks 04NG.

This is the algebraic-spaces analogue of
`AlgebraicGeometry.BaseChangeStalk.cartesian_stalk_tensor_flat`, which on the scheme side is a
theorem: there the local ring upstairs is a localization of the tensor product.  For algebraic
spaces it holds at every geometric point of every cartesian square, by
`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat`. -/
def IsEtaleStalkTensorFlat {X' X Y' Y : AlgebraicSpaces B S hS}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hpb : IsPullback g' f' f g) (x' : GeometricPoint B S hS X'.1) : Prop :=
  let h : geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap g.hom (geometricPointMap f'.hom x') :=
    congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') hpb.w
  letI : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
    (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
  letI : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) h) ≫
      CommRingCat.ofHom
        (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).toAlgebra
  ∃ φ : TensorProduct
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) →+*
      ↥(etaleLocalRing B S hS X'.1 x'),
    φ.comp Algebra.TensorProduct.includeLeftRingHom = etaleLocalRingMap X'.2 g'.hom x' ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        etaleLocalRingMap X'.2 f'.hom x' ∧ φ.Flat

end AlgebraicGeometry.Space

end
