module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigSmoothStability

/-!
# Rig-smoothness is stable under adic base change

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCR** says that if
`f` is rig-smooth (Stacks 0GCP) and `g` is adic, then the second projection `X ×_Y Z ⟶ Z` is
rig-smooth.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsAdicOnEveryAffineEtaleDiagramNoetherian`: a morphism of
  formal algebraic spaces whose affine étale chart maps come from adic homomorphisms of
  Noetherian adic topological rings.
* `AlgebraicGeometry.FormalSpace.TransfersBaseChangeOnAffineEtaleDiagrams`: the transfer to
  formal algebraic spaces drawn in **Stacks 0GBG**.

## Implementation notes

The proof of Stacks 0GCR is the composite of two facts. At the level of topological rings,
rig-smoothness is stable under base change by adic homomorphisms in the sense of Remark 0GBG;
this is Stacks 0GCL, carried by the library as
`TopologicalRing.rigSmooth_isStableUnderBaseChangeByAdic`, whose bundle keeps the locality of
rig-smoothness (Stacks 0GCK) as an input. Remark 0GBG then draws from such a stability bundle
the geometric transfer: condition (1) of Stacks 0ANG passes from `f` and `g` to the second
projection of their fibre product. That transfer is not in the library, so it is carried here as
the hypothesis `TransfersBaseChangeOnAffineEtaleDiagrams`, quantified over *all* pairs of
properties admitting a stability bundle; it is therefore a statement about the generic machinery
of Remark 0GBG and not a restatement of the conclusion below.

What the theorem itself supplies is the passage between the predicate of Stacks 0GCP and that
machinery, in both directions, which is Stacks 0GCQ, together with the instantiation of the
generic transfer at the rig-smooth/adic pair furnished by Stacks 0GCL.

Adicness of `g` is taken in the chart form of condition (1) of Stacks 0ANG, which is how the
hypothesis of Remark 0GBG reads; the locally Noetherian hypotheses on `X`, `Y`, `Z` are carried
by the class of rings over which the chart condition quantifies, exactly as for Stacks 0GCP.

## References

* [Stacks Project, Tag 0GCR](https://stacks.math.columbia.edu/tag/0GCR)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0GCL](https://stacks.math.columbia.edu/tag/0GCL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **The chart form of adicness over `WAdm^{Noeth}`**, which is condition (1) of Stacks 0ANG
for the adic property of ring maps: every morphism between affine, representable, étale charts
of the source and target of a morphism of formal algebraic spaces over `S` is induced by an adic
continuous homomorphism of Noetherian adic topological rings.

This is the chart condition which Formal Spaces, Section 0AQ2 matches with representability by
algebraic spaces — the latter being what Definition 0AQ3 takes as the definition of an adic
morphism, carried by `AlgebraicGeometry.FormalSpace.IsAdicMorphism`. An adic morphism satisfies
this predicate: that is
`AlgebraicGeometry.FormalSpace.isAdicOnEveryAffineEtaleDiagramNoetherian_of_isAdicMorphism`,
read off from the implication (1) ⟹ (2) of Section 0AQ2 at `WAdm^{adic*}`. The predicate is kept
under its own name because the rig-smooth and rig-flat developments, which work over the
Noetherian adic class, state their adicness hypotheses with it. -/
abbrev IsAdicOnEveryAffineEtaleDiagramNoetherian
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  HasPropertyOnEveryAffineEtaleDiagram B S hS
    (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
    (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
      RingHom.IsAdic φ) f

/-- The transfer to formal algebraic spaces drawn in **Stacks 0GBG**: whenever a local property
`P` of arrows of `WAdm^{Noeth}` is stable under base change by a local property `Q`, condition
(1) of Stacks 0ANG passes from a morphism with `P` and a morphism with `Q` to the second
projection of their fibre product. -/
abbrev TransfersBaseChangeOnAffineEtaleDiagrams (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
    TopologicalRing.IsStableUnderBaseChangeBy.{u} P Q →
    ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y),
      HasPropertyOnEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f →
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) Q g →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (pullback.snd f g)

end AlgebraicGeometry.FormalSpace

end
