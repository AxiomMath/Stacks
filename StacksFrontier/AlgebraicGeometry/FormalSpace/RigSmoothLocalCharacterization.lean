module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianChartLocality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigSmoothLocality
public import StacksFrontier.RingTheory.Rig.RigSmoothStableUnderComposition
public import StacksFrontier.RingTheory.Rig.RigSmoothTower

/-!
# Rig-smooth morphisms of locally Noetherian formal algebraic spaces are étale local

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCQ** says that the following are
equivalent:

1. `f` is rig-smooth;
2. for every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y`, the upper map `U ⟶ V` corresponds to a rig-smooth map in
   `WAdm^{Noeth}`;
3. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to a
   rig-smooth map in `WAdm^{Noeth}`;
4. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` with `Yᵢ` an affine formal algebraic space, `Yᵢ ⟶ Y` representable étale,
   and `Xᵢ ⟶ Yᵢ` corresponding to a rig-smooth map in `WAdm^{Noeth}`.

As the source's proof says, (1) and (2) agree by Definition 0GCP, and the equivalence of (2),
(3) and (4) holds because rig-smoothness is a local property of arrows of `WAdm^{Noeth}`
(Stacks 0GCK). This file instantiates the results of
`StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianChartLocality` for rig-smoothness.

## Main results

* `AlgebraicGeometry.FormalSpace.propertyHoldsOnEtaleCompletion_isRigSmoothArrow`: the canonical
  map to the completion of an étale algebra is rig-smooth.
* `AlgebraicGeometry.FormalSpace.isRigSmooth_of_correspondsToNoetherianMapAfterSourceCover`:
  (4) ⟹ (1), with no Noetherian hypothesis on `X` and `Y`.
* `AlgebraicGeometry.FormalSpace.isRigSmooth_tfae_of_isLocallyNoetherian`: **Stacks 0GCQ**.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0GCK](https://stacks.math.columbia.edu/tag/0GCK)
* [Stacks Project, Tag 0GCP](https://stacks.math.columbia.edu/tag/0GCP)
* [Stacks Project, Tag 0GCQ](https://stacks.math.columbia.edu/tag/0GCQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The canonical map to the completion of an étale algebra is rig-smooth**: for an étale
`c : A → A₁` out of a Noetherian adic ring whose completion `(A₁)^` over `A` is Noetherian adic,
`A → (A₁)^` is a rig-smooth arrow of `WAdm^{Noeth}`. -/
theorem propertyHoldsOnEtaleCompletion_isRigSmoothArrow :
    PropertyHoldsOnEtaleCompletion.{u} (fun φ ↦ RingHom.IsRigSmoothArrow φ) := by
  intro A _ _ _ _ A₁ _ c hc hA hC
  have : IsNoetherianRing A := hA.2
  intro _ _ _ _
  exact Rig.isRigSmoothArrow_canonicalMap c hc hA.1 hC

/-- **Stacks 0GCQ, (4) ⟹ (1).** If the members of an affine étale covering of `X` factor through
affine representable étale charts of `Y` by maps corresponding to rig-smooth maps in
`WAdm^{Noeth}`, then `f` is rig-smooth. No Noetherian hypothesis on `X` or `Y` is needed. -/
theorem isRigSmooth_of_correspondsToNoetherianMapAfterSourceCover {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y)
    (hf : CorrespondsToNoetherianMapAfterSourceCover B S hS
      (fun φ ↦ RingHom.IsRigSmoothArrow φ) f) :
    IsRigSmooth B S hS f :=
  (isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToNoetherianMapAfterSourceCover
      (Rig.rigSmooth_isStableUnderCompositionNoetherian Rig.rigSmooth_isLocalNoetherian)
      propertyInvariantUnderRingEquiv_isRigSmoothArrow
      propertyHoldsOnEtaleCompletion_isRigSmoothArrow f hf)

/-- **Stacks 0GCQ.** Let `f : X ⟶ Y` be a morphism of locally Noetherian formal algebraic spaces
over `S`. The following are equivalent:

1. `f` is rig-smooth (Definition 0GCP);
2. for every commutative square with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a
   rig-smooth map in `WAdm^{Noeth}`;
3. there exist a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to a
   rig-smooth map in `WAdm^{Noeth}`;
4. there exist a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` where `Yᵢ` is an affine formal algebraic space, `Yᵢ ⟶ Y` is representable by
   algebraic spaces and étale, and `Xᵢ ⟶ Yᵢ` corresponds to a rig-smooth map in
   `WAdm^{Noeth}`.

In (2), (3) and (4) "corresponds to a rig-smooth map in `WAdm^{Noeth}`" is
`CorrespondsToNoetherianMap` for rig-smoothness: source and target are formal spectra of
Noetherian adic rings and the map is the formal spectrum of a rig-smooth homomorphism. -/
@[stacks 0GCQ]
theorem isRigSmooth_tfae_of_isLocallyNoetherian {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    List.TFAE
      [IsRigSmooth B S hS f,
        CorrespondsToNoetherianMapOnEveryAffineEtaleDiagram B S hS
          (fun φ ↦ RingHom.IsRigSmoothArrow φ) f,
        CorrespondsToNoetherianMapAfterTargetCover B S hS (fun φ ↦ RingHom.IsRigSmoothArrow φ) f,
        CorrespondsToNoetherianMapAfterSourceCover B S hS
          (fun φ ↦ RingHom.IsRigSmoothArrow φ) f] := by
  have h2 := correspondsToNoetherianMapOnEveryAffineEtaleDiagram_iff
    propertyInvariantUnderRingEquiv_isRigSmoothArrow f hX hY
  tfae_have 1 ↔ 2 := (isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).trans h2.symm
  tfae_have 2 → 3 := fun h ↦
    correspondsToNoetherianMapAfterTargetCover_of_hasPropertyOnEveryAffineEtaleDiagram f hX hY
      (h2.1 h)
  tfae_have 3 → 4 := correspondsToNoetherianMapAfterSourceCover_of_afterTargetCover f
  tfae_have 4 → 1 := isRigSmooth_of_correspondsToNoetherianMapAfterSourceCover B S hS f
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
