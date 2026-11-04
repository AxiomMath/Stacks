module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Galois
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper

/-!
# Finite étale Galois covers with a given group

Following [Stacks, Section 03SF], a finite étale morphism `Y ⟶ X` is a Galois cover with group
`G` when `Y` is a Galois object of `FÉt_X` whose automorphism group is identified with `G`. This
file records that notion through a right action of `G` on `Y` over `X` making `Y` a `G`-torsor
over `X`, together with connectedness of `Y`.

## Main definitions

* `AlgebraicGeometry.FiniteEtaleGaloisCover X G`: a finite étale cover of `X` with connected
  total space and a right action of `G` for which the canonical map `G × Y ⟶ Y ×_X Y` is an
  isomorphism.
* `AlgebraicGeometry.genericFiberSection`: the rational point of the generic fibre of a morphism
  to an integral scheme induced by a section.

## Implementation notes

The right action is a monoid map `Gᵐᵒᵖ →* Aut Y`; the torsor condition is phrased with
`Stacks.Descent.galoisCoverComparison`, whose summand at `σ` is `(id, σ)`. For a connected
finite étale cover of a connected scheme this torsor condition is equivalent to `Y` being a
Galois object with `G ≅ Aut_X(Y)`, which is the equivalence (1) ⇔ (4) of [Stacks, Section 03SF].

## References

* [Stacks Project, Section 03SF](https://stacks.math.columbia.edu/tag/03SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- A finite étale Galois cover of `X` with group `G`: a finite étale cover with connected total
space and a right action of `G` over `X` for which `G × Y ⟶ Y ×_X Y`, `(σ, y) ↦ (y, yσ)`, is an
isomorphism. -/
public structure FiniteEtaleGaloisCover (X : Scheme.{u}) (G : Type v) [Group G] [Finite G] where
  /-- The underlying finite étale cover. -/
  obj : FiniteEtaleOver X
  /-- The total space is connected. -/
  connected : ConnectedSpace obj.left
  /-- The right action of `G` on the cover. -/
  action : Gᵐᵒᵖ →* Aut obj
  /-- The action makes the cover a `G`-torsor: `G × Y ≅ Y ×_X Y`. -/
  comparisonIsIso : IsIso (Stacks.Descent.galoisCoverComparison obj.hom
    (((MorphismProperty.Over.forget finiteEtale ⊤ X).mapAut obj).comp action))

attribute [instance] FiniteEtaleGaloisCover.connected FiniteEtaleGaloisCover.comparisonIsIso

/-- The rational point of the generic fibre `f⁻¹(η)` induced by a section `σ` of `f : X ⟶ S`,
for `S` integral with generic point `η`; it lies over `σ(η)`. -/
public def genericFiberSection {S X : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    [IsIntegral S] :
    Spec (S.residueField (genericPoint S)) ⟶ f.fiber (genericPoint S) :=
  pullback.lift (S.fromSpecResidueField (genericPoint S) ≫ σ) (𝟙 _) (by
    rw [Category.assoc, hσ, Category.comp_id]
    rfl)

/-- The generic-fibre point induced by a section lies over the image of the generic point. -/
public lemma genericFiberSection_fiberι {S X : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) [IsIntegral S] :
    genericFiberSection f σ hσ ≫ f.fiberι (genericPoint S) =
      S.fromSpecResidueField (genericPoint S) ≫ σ :=
  pullback.lift_fst _ _ _

end AlgebraicGeometry
