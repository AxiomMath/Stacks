module

public import StacksFrontier.Algebra.DirectSum.RangeGrading
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.Completion
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.TotalChernClass

/-!
# The operations of bivariant classes on nonhomogeneous classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`. A nonhomogeneous bivariant class is an
element of the graded group `A^*(X ⟶ Y) = ⊕_p A^p(X ⟶ Y)`
(`Stacks.Chow.nonhomogeneousBivariantGroup`). Every operation on bivariant classes that the
Stacks Project applies to such an element is additive in each argument and is extended to the
graded groups by additivity, degree by degree:

* the composition `A^*(X ⟶ Y) × A^*(Y ⟶ Z) ⟶ A^*(X ⟶ Z)` of Stacks 0B75, placing the composite
  of a class of degree `p` with one of degree `q` in degree `p + q`;
* the restriction `A^*(X ⟶ Y) ⟶ A^*(X ×_Y Y' ⟶ Y')` along `h : Y' ⟶ Y` of Stacks 0F9Z;
* the transport `A^*(A ⟶ W) ⟶ A^*(B ⟶ W)` along an isomorphism `A ≅ B` over `W`;
* the identification `A^*(X ⟶ Y) = A^*(X ⟶ Y)` along an equality `f = f'` of morphisms.

Each is characterised by its value on a homogeneous class `DirectSum.of _ p c`, which is the
homogeneous operation applied to `c`, in the expected degree.

## Main definitions

* `Stacks.Chow.nonhomogeneousBivariantComposite` — the composition of Stacks 0B75 on the graded
  groups, for a Gysin system with the two compatibilities that Stacks 0B75 needs.
* `Stacks.Chow.nonhomogeneousBivariantCompositeOfInvertible` — the same at the Gysin system of
  the first Chern class rule, where nothing is assumed.
* `Stacks.Chow.nonhomogeneousBivariantRestriction` — the restriction of Stacks 0F9Z on the graded
  groups.
* `Stacks.Chow.nonhomogeneousBivariantTransport` — the transport along an isomorphism of sources.
* `Stacks.Chow.nonhomogeneousBivariantGroupCongr` — the identification of the graded groups of two
  equal morphisms.

## Main results

* `Stacks.Chow.nonhomogeneousBivariantComposite_of_of`,
  `Stacks.Chow.nonhomogeneousBivariantCompositeOfInvertible_of_of`,
  `Stacks.Chow.nonhomogeneousBivariantRestriction_of`,
  `Stacks.Chow.nonhomogeneousBivariantTransport_of`,
  `Stacks.Chow.nonhomogeneousBivariantGroupCongr_of` — the operations on homogeneous classes.

## Implementation notes

The composition is the convolution `Stacks.Chow.directSumBilinear` of the bilinear composition
`Stacks.Chow.bivariantCompositeBilinear`, the construction that
`Stacks.Chow.completedBivariantComposite` applies on each connected component of the completed
groups of Stacks 0FE0; the restriction and the transport are `DirectSum.map` of the additive
homogeneous operations.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Composition -/

section Composite

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)

/-- **Stacks 0B75 on nonhomogeneous classes.** The composition
`A^*(X ⟶ Y) × A^*(Y ⟶ Z) ⟶ A^*(X ⟶ Z)`, the bilinear extension of the composition of
homogeneous classes: the composite of a class of degree `p` with a class of degree `q` is their
composite of Stacks 0B75, in degree `p + q`. -/
def nonhomogeneousBivariantComposite (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    nonhomogeneousBivariantGroup C G sX sY f hf →+ nonhomogeneousBivariantGroup C G sY sZ g hg →+
      nonhomogeneousBivariantGroup C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) :=
  directSumBilinear fun p q ↦ bivariantCompositeBilinear C G sX sY sZ f g hf hg p q hgys hgysc

/-- The composition on nonhomogeneous classes, on homogeneous classes. -/
@[simp]
theorem nonhomogeneousBivariantComposite_of_of (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) (p q : ℤ)
    (a : BivariantClass C G sX sY f hf p) (b : BivariantClass C G sY sZ g hg q) :
    nonhomogeneousBivariantComposite C G sX sY sZ f g hf hg hgys hgysc (DirectSum.of _ p a)
        (DirectSum.of _ q b) =
      DirectSum.of _ (p + q) (bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc) :=
  directSumBilinear_of_of _ p q a b

/-- **Stacks 0B75 on nonhomogeneous classes.** The composition
`A^*(X ⟶ Y) × A^*(Y ⟶ Z) ⟶ A^*(X ⟶ Z)` at the Gysin system of the first Chern class rule of an
invertible module, with nothing assumed: `Stacks.Chow.nonhomogeneousBivariantComposite` with
both Gysin compatibilities discharged. -/
def nonhomogeneousBivariantCompositeOfInvertible :
    nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf →+
      nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) sY sZ g hg →+
        nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
          (comp_comp_structureMorphism_eq hf hg) :=
  nonhomogeneousBivariantComposite C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

/-- The composition on nonhomogeneous classes at the Gysin system of the first Chern class rule,
on homogeneous classes. -/
@[simp]
theorem nonhomogeneousBivariantCompositeOfInvertible_of_of (p q : ℤ)
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) :
    nonhomogeneousBivariantCompositeOfInvertible C sX sY sZ f g hf hg (DirectSum.of _ p a)
        (DirectSum.of _ q b) =
      DirectSum.of _ (p + q) (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a b) :=
  directSumBilinear_of_of _ p q a b

end Composite

/-! ### Restriction -/

section Restriction

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  (h : Y' ⟶ Y) [LocallyOfFiniteType h]

/-- **Stacks 0F9Z on nonhomogeneous classes.** The restriction
`A^*(X ⟶ Y) ⟶ A^*(X ×_Y Y' ⟶ Y')` along `h : Y' ⟶ Y`, degree by degree. -/
def nonhomogeneousBivariantRestriction (hgys : G.IsNaturalUnderBaseChangeIso) :
    nonhomogeneousBivariantGroup C G sX sY f hf →+
      nonhomogeneousBivariantGroup C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) :=
  DirectSum.map fun p ↦ bivariantRestrictionAddHom C G sX sY f hf h p hgys

/-- The restriction of a homogeneous class is the restriction of Stacks 0F9Z, in the same
degree. -/
@[simp]
theorem nonhomogeneousBivariantRestriction_of (hgys : G.IsNaturalUnderBaseChangeIso) (p : ℤ)
    (c : BivariantClass C G sX sY f hf p) :
    nonhomogeneousBivariantRestriction C G sX sY f hf h hgys (DirectSum.of _ p c) =
      DirectSum.of _ p (bivariantRestriction C G sX sY f hf h p hgys c) :=
  DirectSum.map_of _ p c

end Restriction

/-! ### Transport along an isomorphism of sources -/

section Transport

variable (C : ChowSituation.{u}) (G : GysinSystem C) {A B W : Scheme.{u}} (sA : A ⟶ C.S)
  [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sW : W ⟶ C.S)
  [LocallyOfFiniteType sW] (v : A ⟶ W) [LocallyOfFiniteType v] (hv : v ≫ sW = sA)
  (u : B ⟶ W) [LocallyOfFiniteType u] (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)

/-- The transport `A^*(A ⟶ W) ⟶ A^*(B ⟶ W)` along an isomorphism `θ : A ≅ B` over `W`, degree by
degree. -/
def nonhomogeneousBivariantTransport (hgys : G.IsNaturalUnderBaseChangeIso) :
    nonhomogeneousBivariantGroup C G sA sW v hv →+ nonhomogeneousBivariantGroup C G sB sW u hu :=
  DirectSum.map fun p ↦ bivariantTransportAddHom C G sA sB sW v hv u hu θ hθ p hgys

/-- The transport of a homogeneous class is its transport, in the same degree. -/
@[simp]
theorem nonhomogeneousBivariantTransport_of (hgys : G.IsNaturalUnderBaseChangeIso) (p : ℤ)
    (c : BivariantClass C G sA sW v hv p) :
    nonhomogeneousBivariantTransport C G sA sB sW v hv u hu θ hθ hgys (DirectSum.of _ p c) =
      DirectSum.of _ p (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c) :=
  DirectSum.map_of _ p c

end Transport

/-! ### Equal morphisms -/

section Congr

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The graded groups of bivariant classes of two equal morphisms are the same group. -/
def nonhomogeneousBivariantGroupCongr {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) :
    nonhomogeneousBivariantGroup C G sX sY f hf ≃+ nonhomogeneousBivariantGroup C G sX sY f' hf' :=
  DFinsupp.mapRange.addEquiv fun p ↦ bivariantClassCongr C G sX sY hff hf hf' p

/-- The identification along an equality of morphisms, on a homogeneous class. -/
@[simp]
theorem nonhomogeneousBivariantGroupCongr_of {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) (p : ℤ)
    (c : BivariantClass C G sX sY f hf p) :
    nonhomogeneousBivariantGroupCongr C G sX sY hff hf hf' (DirectSum.of _ p c) =
      DirectSum.of _ p (bivariantClassCongr C G sX sY hff hf hf' p c) :=
  mapRange_addEquiv_of _ p c

end Congr

end Stacks.Chow

end
