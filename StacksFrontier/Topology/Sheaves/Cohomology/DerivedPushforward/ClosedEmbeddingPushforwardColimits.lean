module

public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.SupportedSectionsOnClosed
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardCounit

/-!
# Pushforward along a homeomorphism onto a closed subset: colimits and totalization

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose underlying continuous map
is a homeomorphism onto a closed subset, which is `Topology.IsClosedEmbedding f.hom.base`.
This file records the two properties of `f_*` on which the source's proof of the projection
formula for such an `f`, [Stacks, Tag 0B55], rests:

* `f_*` is **exact**, so `Rf_*` may be computed by applying `f_*` termwise to any complex
  representing an object of `D(𝒪_X)`;
* `f_*` **commutes with arbitrary direct sums**, hence with the totalization of a bicomplex.

Both are stated for a morphism of ringed spaces with no further hypothesis, and the second is
new: the library had right exactness of `f_*` for a closed embedding
(`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward`, [Stacks, Tag 08KS]) but
not preservation of infinite colimits, which is what the source's step
"`f_*` commutes with direct sums" needs.

## Main definitions

There are no new definitions.

## Main results

* `preservesColimits_sheafPushforward`: pushforward of sheaves of abelian groups along a closed
  embedding of topological spaces preserves all colimits.
* `preservesColimitsOfSize_modulePushforward`: **pushforward of sheaves of modules along a
  morphism of ringed spaces that is a homeomorphism onto a closed subset preserves all small
  colimits**, in particular arbitrary direct sums.
* `isIso_derivedPushforwardUnit_app`: **the derived pushforward of such a morphism is computed
  by applying `f_*` termwise**: the comparison `Qh (f_* K) ⟶ Rf_* (Qh K)` is invertible at
  every object `K` of the homotopy category, with no K-injectivity hypothesis.
* `isIso_totalMap_modulePushforward`: **`f_*` commutes with the total complex of a
  bicomplex**, with no boundedness hypothesis on the bicomplex.

## What of [Stacks, Tag 0B55] is not here

The conclusion of [Stacks, Tag 0B55] — that the projection-formula map of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism for arbitrary `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)` — is **not proved here**, and
nothing below mentions that map.  The source's proof has, besides the two inputs above, two
further steps that this file does not carry out:

* the identity `f_*(ℰ ⊗_{𝒪_X} f^*𝒦) = f_*ℰ ⊗_{𝒪_Y} 𝒦` for a single `𝒪_X`-module `ℰ` and a
  single `𝒪_Y`-module `𝒦`, checked on stalks — over a point outside the image both stalks
  vanish, and over `y = f(x)` it is
  `ℰ_x ⊗_{𝒪_{X,x}} (𝒪_{X,x} ⊗_{𝒪_{Y,y}} 𝒦_y) = ℰ_x ⊗_{𝒪_{Y,y}} 𝒦_y`.  No declaration in this
  library states that identity, and the ordinary projection-formula map for a morphism of
  ringed spaces, of which it asserts the invertibility, is not constructed either: the
  construction in `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` is for a
  morphism of schemes.
* the passage from that identity to the derived statement, by representing `K` by a K-flat
  complex `𝒦^•` — whose pullback `f^*𝒦^•` is again K-flat — and
  identifying both sides of the map with the totalizations
  `Tot(f_*ℰ^• ⊗_{𝒪_Y} 𝒦^•)` and `f_* Tot(ℰ^• ⊗_{𝒪_X} f^*𝒦^•)`.  The first two steps above
  are exactly what makes those two totalizations correspond, which is why they are recorded
  here; what is missing is the identification of the map of [Stacks, Tag 0B53] with the
  resulting morphism of complexes.

## Implementation notes

*Why the sheaf-level statement is proved by factoring through the image.*  A closed embedding
factors as a homeomorphism onto its range followed by the inclusion of a closed subset.
Pushforward along a homeomorphism is an equivalence of categories of abelian sheaves, so it
preserves colimits as a left adjoint; pushforward along the inclusion of a closed subset
preserves colimits because it has a right adjoint, the sheaf of sections supported on that
subset, which is `ClosedImmersionSheaves.closedInclusionPushforward_preservesColimits`,
[Stacks, Tag 01AZ].  The factorization holds on the nose, so the composite is the pushforward
along `f` itself.

*Why the module-level statement is reduced to the sheaf-level one.*  `f_*` of sheaves of
modules sits over `f_*` of abelian sheaves: composing with the forgetful functor
`SheafOfModules.toSheaf` on the target gives the same functor as composing with
`SheafOfModules.toSheaf` on the source and then pushing forward abelian sheaves, by
definitional unfolding.  `SheafOfModules.toSheaf` preserves colimits and reflects
isomorphisms, hence reflects colimits, and
`CategoryTheory.Limits.preservesColimits_of_reflects_of_preserves` turns that into preservation
by `f_*`.  The composite of the two colimit-preserving functors has to be assembled by applying
`CategoryTheory.Limits.comp_preservesColimits` with its two functors and its two instance
arguments given explicitly: the category of abelian sheaves on `X` carries two equal but
syntactically different `Category` instances, the one that
`AlgebraicGeometry.SheafOfModules.toSheaf` produces as its codomain and the one that
`TopCat.Sheaf.pushforward` produces as its domain, and instance search does not identify them,
whereas the definitional-equality check that an explicit argument undergoes does.  The
`WEqualsLocallyBijective` binder on each of the two sites is the one under which
`AlgebraicGeometry.SheafOfModules.toSheaf` is known to preserve colimits; it is a `Prop`
inhabited for every ringed space, by
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`, so it is not a weakening.

*The shape universe.*  `PreservesColimitsOfSize.{0, 0}` is the form the totalization lemma
needs: the index set of a total degree of a bicomplex of `ℤ`-shape is a subtype of `ℤ × ℤ` and
so lives in `Type 0`.  It is obtained from `PreservesColimits` on the sheaf level by
`CategoryTheory.Limits.preservesColimitsOfSize_shrink`.

## References

* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01AZ](https://stacks.math.columbia.edu/tag/01AZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

noncomputable section

namespace Stacks.Cohomology.ClosedEmbeddingPushforward

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf

/-! ### Colimits -/

/-- Pushforward of sheaves of abelian groups along a homeomorphism of base spaces is an
equivalence of categories: it is the equivalence of presheaf categories of
`TopCat.Presheaf.presheafEquivOfIso`, which carries sheaves to sheaves. -/
private def sheafEquivOfIso {X Y : TopCat.{u}} (e : X ≅ Y) :
    X.Sheaf AddCommGrpCat.{u} ≌ Y.Sheaf AddCommGrpCat.{u} :=
  let E := TopCat.Presheaf.presheafEquivOfIso AddCommGrpCat.{u} e
  { functor := TopCat.Sheaf.pushforward _ e.hom
    inverse := TopCat.Sheaf.pushforward _ e.inv
    unitIso := NatIso.ofComponents (fun F => ObjectProperty.isoMk _ (E.unitIso.app F.obj))
      (fun g => ObjectProperty.hom_ext _ (E.unitIso.hom.naturality g.hom))
    counitIso := NatIso.ofComponents (fun F => ObjectProperty.isoMk _ (E.counitIso.app F.obj))
      (fun g => ObjectProperty.hom_ext _ (E.counitIso.hom.naturality g.hom))
    functor_unitIso_comp F := ObjectProperty.hom_ext _ (E.functor_unitIso_comp F.obj) }

/-- **Pushforward of sheaves of abelian groups along a closed embedding preserves all
colimits.**  A closed embedding is a homeomorphism onto its range followed by the inclusion of
a closed subset; pushforward along the first is an equivalence and pushforward along the second
has a right adjoint, [Stacks, Tag 01AZ]. -/
theorem preservesColimits_sheafPushforward {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f.hom) :
    PreservesColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) := by
  let e : X ≅ TopCat.of (Set.range f) := TopCat.isoOfHomeo hf.isEmbedding.toHomeomorph
  let i : TopCat.of (Set.range f) ⟶ Y := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let : PreservesColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) :=
    (sheafEquivOfIso e).functor.asEquivalence.toAdjunction.leftAdjoint_preservesColimits
  let : PreservesColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i) :=
    ClosedImmersionSheaves.closedInclusionPushforward_preservesColimits _ hf.isClosed_range
  exact inferInstanceAs (PreservesColimits
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} i))

variable {X Y : RingedSpace.{u, u}}
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Pushforward of sheaves of modules along a morphism of ringed spaces which is a
homeomorphism onto a closed subset preserves all small colimits**, in particular arbitrary
direct sums.  This is the input "`f_*` commutes with direct sums" of the source's proof of
[Stacks, Tag 0B55]; the library had only right exactness,
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward`.

The statement is reduced to `preservesColimits_sheafPushforward` through the forgetful functor
to abelian sheaves, which preserves colimits and reflects isomorphisms. -/
@[stacks 0B55 "f_* commutes with direct sums: the input of the source's proof"]
theorem preservesColimitsOfSize_modulePushforward
    (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f.hom.base) :
    PreservesColimitsOfSize.{0, 0} (modulePushforward f) := by
  let hpush : PreservesColimitsOfSize.{0, 0}
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base) := by
    let := preservesColimits_sheafPushforward f.hom.base hf
    exact preservesColimitsOfSize_shrink _
  let hforget :
      PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{u} (structureSheafRing X)) :=
    preservesColimitsOfSize_shrink _
  let : PreservesColimitsOfSize.{0, 0}
      (modulePushforward f ⋙ SheafOfModules.toSheaf.{u} (structureSheafRing Y)) :=
    @comp_preservesColimits _ _ _ _ _ _ (SheafOfModules.toSheaf.{u} (structureSheafRing X))
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base) hforget hpush
  let : PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{u} (structureSheafRing Y)) :=
    preservesColimitsOfSize_shrink _
  let : ReflectsColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{u} (structureSheafRing Y)) :=
    reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{u} (structureSheafRing Y))

/-! ### The derived pushforward is computed termwise -/

/-- **For a morphism of ringed spaces which is a homeomorphism onto a closed subset the derived
pushforward is computed by applying `f_*` termwise**: the comparison `Qh (f_* K) ⟶ Rf_* (Qh K)`
is invertible at every object `K` of the homotopy category, with no K-injectivity hypothesis.

This is the first step of the source's proof of [Stacks, Tag 0B55].  It is
`Stacks.Cohomology.ExactPushforwardAdjunction.isIso_derivedPushforwardUnit_app`, whose
hypothesis of right exactness is discharged by
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward`, [Stacks, Tag 08KS]. -/
@[stacks 0B55 "step 1: Rf_* is computed by applying f_* termwise"]
theorem isIso_derivedPushforwardUnit_app (f : X ⟶ Y)
    (hf : Topology.IsClosedEmbedding f.hom.base)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit f).app K) :=
  let := Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward f hf
  Stacks.Cohomology.ExactPushforwardAdjunction.isIso_derivedPushforwardUnit_app f K

/-! ### Totalization -/

/-- **`f_*` commutes with the total complex of a bicomplex** when `f` is a homeomorphism onto a
closed subset: the comparison `Tot(f_* K) ⟶ f_* Tot(K)` of
`HomologicalComplex₂.TotalMap.totalMap` is an isomorphism.  There is no boundedness hypothesis
on the bicomplex, which is what the source's proof of [Stacks, Tag 0B55] needs: the
totalizations it compares are those of unbounded bicomplexes. -/
@[stacks 0B55 "f_* commutes with the totalization of an unbounded bicomplex"]
theorem isIso_totalMap_modulePushforward (f : X ⟶ Y)
    (hf : Topology.IsClosedEmbedding f.hom.base)
    (K : HomologicalComplex₂ (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    [HomologicalComplex₂.HasTotal
      (HomologicalComplex₂.TotalMap.mapBicomplex (modulePushforward f) K)
      (ComplexShape.up ℤ)] :
    IsIso (HomologicalComplex₂.TotalMap.totalMap (c₁₂ := ComplexShape.up ℤ)
      (modulePushforward f) K) := by
  let := preservesColimitsOfSize_modulePushforward f hf
  rw [← HomologicalComplex₂.TotalMap.totalIso_hom_eq_totalMap (c₁₂ := ComplexShape.up ℤ)]
  exact (HomologicalComplex₂.TotalMap.totalIso (c₁₂ := ComplexShape.up ℤ)
    (modulePushforward f) K).isIso_hom

end Stacks.Cohomology.ClosedEmbeddingPushforward

end

end
