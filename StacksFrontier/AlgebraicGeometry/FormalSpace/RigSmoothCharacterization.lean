module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmooth
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagramNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability
public import StacksFrontier.RingTheory.Rig.RigSmoothLocalityRefined

/-!
# Characterising rig-smooth morphisms of formal algebraic spaces on affine charts

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCQ** says that the following are
equivalent:

1. `f` is rig-smooth (Definition 0GCP);
2. every commutative square with affine formal algebraic spaces `U`, `V` and representable étale
   maps `U ⟶ X`, `V ⟶ Y` has its upper horizontal map `U ⟶ V` given by a rig-smooth arrow of
   `WAdm^{Noeth}`;
3. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM with each `Xⱼᵢ ⟶ Yⱼ` given by a rig-smooth arrow of
   `WAdm^{Noeth}`;
4. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` through an affine formal algebraic space `Yᵢ` representable étale over `Y`
   with `Xᵢ ⟶ Yᵢ` given by a rig-smooth arrow of `WAdm^{Noeth}`.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSmooth_tfae`: **Stacks 0GCQ**.

## Implementation notes

Conditions (2), (3) and (4) are the three conditions of Stacks 0ANG for the class
`TopologicalRing.IsNoetherianAdic` of Noetherian adic topological rings and the property
`RingHom.IsRigSmoothArrow`:
`AlgebraicGeometry.FormalSpace.HasPropertyOnEveryAffineEtaleDiagram`,
`AlgebraicGeometry.FormalSpace.HasPropertyAfterTargetCover` and
`AlgebraicGeometry.FormalSpace.HasPropertyAfterSourceCover`. The proof follows the source:

* (1) ⟺ (2) is Definition 0GCP,
  `AlgebraicGeometry.FormalSpace.isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram`;
* (2) ⟹ (3) is the first step of Stacks 0ANG, with the fibre products `Yⱼ ×_Y X` formal
  algebraic spaces by Stacks 0AJ3,
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`;
* (3) ⟹ (4) is the second step of Stacks 0ANG, which holds for any class and property;
* (4) ⟹ (2) is the variant of Stacks 0ANG for locally Noetherian formal algebraic spaces of
  Remark 0ANI, applied to the local property of arrows of `WAdm^{Noeth}` that rig-smoothness is
  by Stacks 0GCK, `Rig.rigSmooth_isLocalNoetherian'`.

## References

* [Stacks Project, Tag 0GCQ](https://stacks.math.columbia.edu/tag/0GCQ)
* [Stacks Project, Tag 0GCP](https://stacks.math.columbia.edu/tag/0GCP)
* [Stacks Project, Tag 0GCK](https://stacks.math.columbia.edu/tag/0GCK)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GCQ.** For a morphism `f : X ⟶ Y` of locally Noetherian formal algebraic spaces
over `S`, the following are equivalent: `f` is rig-smooth (Definition 0GCP); every commutative
square with affine formal algebraic spaces `U`, `V` and representable étale maps `U ⟶ X`,
`V ⟶ Y` has `U ⟶ V` given by a rig-smooth arrow of `WAdm^{Noeth}`; there are an affine étale
covering `{Yⱼ ⟶ Y}` and, for each `j`, an affine étale covering `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` with every
`Xⱼᵢ ⟶ Yⱼ` given by a rig-smooth arrow of `WAdm^{Noeth}`; and there is an affine étale covering
`{Xᵢ ⟶ X}` with factorizations `Xᵢ ⟶ Yᵢ ⟶ Y` through affine formal algebraic spaces
representable étale over `Y` with every `Xᵢ ⟶ Yᵢ` given by a rig-smooth arrow of
`WAdm^{Noeth}`. -/
@[stacks 0GCQ]
theorem isRigSmooth_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    List.TFAE
      [IsRigSmooth B S hS f,
        HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
          (fun φ ↦ RingHom.IsRigSmoothArrow φ) f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsNoetherianAdic
          (fun φ ↦ RingHom.IsRigSmoothArrow φ) f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic
          (fun φ ↦ RingHom.IsRigSmoothArrow φ) f] := by
  tfae_have 1 ↔ 2 := isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsNoetherianAdic (fun φ ↦ RingHom.IsRigSmoothArrow φ) f hY.1
    (fun _V v hV _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS
      v f hY.1 hV hX.1) h
  tfae_have 3 → 4 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS
    TopologicalRing.IsNoetherianAdic (fun φ ↦ RingHom.IsRigSmoothArrow φ) f h
  tfae_have 4 → 2 := fun h ↦
    hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyNoetherian B S hS
      (fun φ ↦ RingHom.IsRigSmoothArrow φ) Rig.rigSmooth_isLocalNoetherian.{u}
      Rig.rigSmooth_isomorphismInvariant.{u} f hX hY h
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
