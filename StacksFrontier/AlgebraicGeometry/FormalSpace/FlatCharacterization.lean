module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Flat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic

/-!
# Characterizations of flatness of a morphism of locally Noetherian formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCD** says that the following
four conditions are equivalent:

1. `f` is flat;
2. for every commutative square with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a
   flat map in `WAdm^{Noeth}`;
3. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM with each `Xⱼᵢ ⟶ Yⱼ` corresponding to a flat map
   in `WAdm^{Noeth}`;
4. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` with `Yᵢ` an affine formal algebraic space representable by algebraic spaces
   and étale over `Y` and `Xᵢ ⟶ Yᵢ` corresponding to a flat map in `WAdm^{Noeth}`.

Flatness is a local property of arrows of `WAdm^{Noeth}` (Stacks 0GC9), so conditions (2),
(3) and (4) are the three conditions of Stacks 0ANG for the class of Noetherian adic
topological rings and the property of being a flat ring homomorphism, in the Noetherian
variant of Remark 0ANI. Conditions (1) and (2) agree because condition (2) *is* Definition
0GCC, which is how the source's own proof disposes of that equivalence.

## Main definitions

* `TopologicalRing.IsNoetherianAdic`: membership in `WAdm^{Noeth}`, the class of rings on
  which the conditions above are tested.
* `TopologicalRing.IsFlatHom`: flatness of a ring homomorphism, in the shape in which the
  local-property machinery of Stacks 0ANG takes a property of arrows.

## Main results

* `AlgebraicGeometry.FormalSpace.isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`: Definition
  0GCC is the chart-tested condition of Stacks 0ANG for Noetherian adic rings and flatness.
* `AlgebraicGeometry.FormalSpace.isFlat_tfae`: the four conditions of Stacks 0GCD are
  equivalent for a morphism into a formal algebraic space, given the inputs `hpb`, `hasc`,
  `hdesc` and `href`. Stacks 0GCD itself, under exactly the source's hypotheses, is
  `AlgebraicGeometry.FormalSpace.isFlat_tfae_of_isLocallyNoetherian` of
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterizationLocallyNoetherian`.

The implication from condition (2) to condition (3) of **Stacks 0ANG**, used below, is
`AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_of_afterTargetCover` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability`.

## Implementation notes

The equivalence of (1) and (2) is not a tautology in Lean even though it is one in the source:
`AlgebraicGeometry.FormalSpace.IsFlat` carries the Noetherian condition on the two presenting
rings as instance arguments and the adicness as a hypothesis, while
`AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap` carries both in the single class
argument `TopologicalRing.IsNoetherianAdic`, and the representability and étaleness of the two
charts are split in the first and bundled in the second. The equivalence repackages those
binders and asserts nothing further; it is recorded here, rather than claimed in prose, because
condition (1) of Stacks 0GCD is one of the four conditions that tag asserts.

The implication from (2) to (3) is `hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram` and
the implication from (4) to (2) is `hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover`,
both already carried for an arbitrary local property. The leg closing the cycle, from (3) to
(4), is proved here: the charts of the fibre products `Yⱼ ×_Y X` map to `X` by composing with
the second projection, which is representable étale because it is a base change of `Yⱼ ⟶ Y`,
and they jointly cover `X` because a jointly surjective family of sheaves stays jointly
surjective after base change (`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd`)
and after refinement by coverings of its members
(`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_sigma`). The factorization required by
condition (4) is through `Yⱼ` itself, by the first projection, and the square commutes by the
universal property of the fibre product.

In `isFlat_tfae` four inputs of the source are explicit hypotheses, and none of them is a
conjunct of any of the four conditions. For locally Noetherian `X` and `Y` the library now
proves all of them, and
`AlgebraicGeometry.FormalSpace.isFlat_tfae_of_isLocallyNoetherian` states Stacks 0GCD without
them. Stacks 0AJ3, that the fibre product
of a chart of `Y` with `f` is a formal algebraic space, is `hpb`; it is what the implication
from (2) to (3) needs in order to produce the inner coverings. The refinement of a covering as
in condition (4) against a square as in condition (2), which uses Stacks 0AJ2 and
quasi-compactness of an affine formal algebraic space, is `href`. The two locality axioms of
Situation 0CBA for flatness, which hold by Stacks 0GC9 for arrows of `WAdm^{Noeth}` but have to
be transported to morphisms of affine formal algebraic spaces through Stacks 0AN8 and Stacks
0AN9, are `hasc` and `hdesc`. For locally Noetherian spaces Stacks 0AJ3 is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`,
and the refinement and the locality axioms are carried out in
`FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyNoetherian`
(Remark 0ANI).

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GC9](https://stacks.math.columbia.edu/tag/0GC9)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GCD](https://stacks.math.columbia.edu/tag/0GCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

/-- Flatness of a ring homomorphism, read as a property of homomorphisms of topological rings.
This is the shape in which the local-property machinery of Stacks 0ANG takes a property of
arrows; the topology plays no role in the condition itself. -/
abbrev IsFlatHom {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) : Prop :=
  φ.Flat

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- Definition **Stacks 0GCC** of flatness of a morphism of formal algebraic spaces is the
chart-tested condition of Stacks 0ANG for the class of Noetherian adic topological rings and
the property of being a flat ring homomorphism.

The two sides differ only in how the binders are packaged: `IsFlat` keeps the Noetherian
condition on the presenting rings as an instance argument and the adicness as a hypothesis,
and splits representability from étaleness for the two charts, while the chart-tested condition
bundles each pair. -/
theorem isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsFlat B S hS f ↔ HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f := by
  constructor
  · intro hf U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA' hR' hA D E eU eV g hg
    have := hA'.2
    have := hR'.2
    exact hf U V hU hV a b t ha.1 hb.1 ha.2 hb.2 hsq A R hA'.1 hR'.1 hA D E eU eV g hg
  · intro hf U V hU hV a b t ha hb hae hbe hsq A R _ _ _ _ _ _ _ _ _ _ hAadic hRadic hA D E
      eU eV g hg
    exact hf U V a b t hU hV ⟨ha, hae⟩ ⟨hb, hbe⟩ hsq A R ⟨hAadic, inferInstance⟩
      ⟨hRadic, inferInstance⟩ hA D E eU eV g hg

/-- **The four conditions of Stacks 0GCD, under explicit inputs.** For a morphism
`f : X ⟶ Y` into a formal algebraic space `Y`, flatness of `f` in the sense of Definition 0GCC,
the condition that every affine representable étale square over `f` carry a flat map of
Noetherian adic topological rings, the existence of an affine étale covering of `Y` together
with affine étale coverings of the fibre products of its members with `X` on which that
condition holds, and the existence of an affine étale covering of `X` whose members factor
flatly through affine representable étale charts of `Y`, are all equivalent, given the
hypotheses `hpb`, `href`, `hasc` and `hdesc`. These carry Stacks 0AJ3, the covering refinement
of Stacks 0AJ2, and the locality axioms of Situation 0CBA read through Stacks 0AN8 and Stacks
0AN9.

Stacks 0GCD itself, for locally Noetherian `X` and `Y` and with none of these inputs, is
`AlgebraicGeometry.FormalSpace.isFlat_tfae_of_isLocallyNoetherian`, where each input is proved.
This form is kept for its callers, which supply the inputs directly. -/
theorem isFlat_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hpb : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f))
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom)
    (href : HasEtaleRefinementOfSourceCover B S hS f) :
    List.TFAE
      [IsFlat B S hS f,
        HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f,
        HasPropertyAfterTargetCover B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f,
        HasPropertyAfterSourceCover B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f] := by
  tfae_have 1 ↔ 2 := isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f hY hpb h
  tfae_have 3 → 4 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f h
  tfae_have 4 → 2 := fun h ↦ hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f hasc hdesc href h
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
