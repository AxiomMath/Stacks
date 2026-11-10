module

public import StacksFrontier.Deformation.ClassicalCase
public import StacksFrontier.Deformation.Examples.Linear.RepresentationIsomorphismClasses
public import StacksFrontier.Deformation.Examples.Linear.RepresentationsRimSchlessinger
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClassesHull

/-!
# A hull for the deformations of a representation

Fix a classical base `Λ`, a group `Γ` and a finite-dimensional representation `ρ₀` of `Γ` on a
`k`-vector space `V`. The deformations of `ρ₀` form a deformation category, so its functor of
fibrewise isomorphism classes satisfies Schlessinger's conditions (S1) and (S2); if in
addition its tangent space is finite dimensional, the functor has a hull.

That last hypothesis is the tangent-space clause of Stacks 0DVZ's companion for
representations, Stacks 0DVT, which holds whenever `Γ` is finitely generated. It is carried
explicitly here, so the theorem below is *weaker* than Stacks 0ET1 and does not carry its tag.
What blocks discharging it is not a missing result but a missing bridge. Stacks 0DVT is proved,
at `Deformation.finiteDimensional_tangentSpace_representation`, and so are both links of the
source chain: `T𝓕 = Ext¹_{k[Γ]}(V, V)` is Stacks 0DVE and finite-dimensionality of the first
cohomology of a finitely generated group with finite-dimensional coefficients is Stacks 0DVF.
All three are stated over the `Deformation.RepresentationCategory` presentation of the category
of Stacks 0D3J, while the functor below is built from the
`Deformation.Examples.FiniteProjectiveRepresentation` presentation, and the two presentations are
not bridged. Bridging them discharges this hypothesis from the `Group.FG Γ` already recorded in
`Deformation.Examples.RepresentationDeformationSituation`, and then the tag moves here.

Stacks 0ET1 has a second clause as well — that `F` is prorepresentable when
`H⁰(Γ, End_k(V)) = k`. That clause is proved over the `Deformation.RepresentationCategory`
presentation, at `Deformation.isProrepresentableULift_isomorphismClasses_representation`.

## Main results

All of them live in the namespace
`Deformation.Examples.RepresentationDeformationSituation`.

* `isDeformationCategory_deformationProjection`, `isPredeformationCategory_deformationProjection`
  and `satisfiesRS_deformationProjection`: the deformations of a representation form a
  deformation category, read off from Stacks 0DVS.
* `schlessingerConditionS1_deformationProjection` and
  `schlessingerConditionS2_deformationProjection`: Schlessinger's conditions for it.
* `schlessingerConditionS2_isomorphismClassFunctor`: condition (S2) for the associated functor
  of isomorphism classes.
* `exists_hull_isomorphismClassFunctor`: the functor of isomorphism classes of deformations of
  `ρ₀` has a hull, given that its tangent space is finite dimensional.

## Implementation notes

The vector space structure on the tangent space is the canonical one of Stacks 06IH, which
instance search reads off two `Fact` instances. They are derivable — the first from the
predeformation structure and the second from condition (S2) through Stacks 06I0 — but the
finite-dimensionality hypothesis cannot even be stated before they are in scope, so they are
introduced by `letI` inside the hypothesis. This is the shape in which Stacks 06IW, 06IX and
06IZ state the same hypothesis.

The deformation category is taken in the `Deformation.Examples.FiniteProjectiveRepresentation`
model, which is the one `Deformation.Examples.RepresentationDeformationSituation` is phrased
in. The parallel `Deformation.RepresentationCategory` model carries the identification of the
tangent space with a self-Ext group; the two are not bridged here.

## References

* [Stacks Project, Tag 0ET1](https://stacks.math.columbia.edu/tag/0ET1)
* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples.RepresentationDeformationSituation

universe u w g m

variable {Λ : Type u} {k : Type w} {Γ : Type g} {V : Type (max w m)}
  [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [AddCommGroup V] [Module k V]

/-- **Stacks 0DVS.** The deformations of a finite-dimensional representation satisfy the
Rim–Schlessinger condition (RS) and form a predeformation category. -/
public theorem isDeformationCategory_deformationProjection
    (S : RepresentationDeformationSituation Λ k Γ V) :
    IsDeformationCategory S.deformationProjection :=
  let : Module.Finite k V := S.finiteDimensional
  FiniteProjectiveRepresentation.isDeformationCategory_deformationCategory
    (Λ := Λ) V S.representation

/-- The deformations of a finite-dimensional representation form a predeformation category. -/
public theorem isPredeformationCategory_deformationProjection
    (S : RepresentationDeformationSituation Λ k Γ V) :
    IsPredeformationCategory S.deformationProjection :=
  S.isDeformationCategory_deformationProjection.predeformation

/-- The deformations of a finite-dimensional representation satisfy condition (RS). -/
public theorem satisfiesRS_deformationProjection
    (S : RepresentationDeformationSituation Λ k Γ V) :
    SatisfiesRS S.deformationProjection :=
  S.isDeformationCategory_deformationProjection.satisfiesRS

/-- **Stacks 06J7.** The deformations of a finite-dimensional representation satisfy
Schlessinger's condition (S1). -/
public theorem schlessingerConditionS1_deformationProjection
    (S : RepresentationDeformationSituation Λ k Γ V) :
    SchlessingerConditionS1 S.deformationProjection :=
  schlessingerConditionS1_of_satisfiesRS S.satisfiesRS_deformationProjection

/-- **Stacks 06J7.** The deformations of a finite-dimensional representation satisfy
Schlessinger's condition (S2). -/
public theorem schlessingerConditionS2_deformationProjection
    (S : RepresentationDeformationSituation Λ k Γ V) :
    SchlessingerConditionS2 S.deformationProjection :=
  schlessingerConditionS2_of_satisfiesRS S.satisfiesRS_deformationProjection

/-- **Stacks 06I0.** The functor of isomorphism classes of deformations of a finite-dimensional
representation satisfies Schlessinger's condition (S2). -/
public theorem schlessingerConditionS2_isomorphismClassFunctor
    (S : RepresentationDeformationSituation Λ k Γ V) :
    SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
      (BasedCategory.ofFunctor S.deformationProjection)
      S.isPredeformationCategory_deformationProjection.cofibered)) :=
  schlessingerConditionS2_of_isIsomorphismClasses _
    S.isPredeformationCategory_deformationProjection.cofibered
    S.schlessingerConditionS2_deformationProjection
    (Or.inl S.isPredeformationCategory_deformationProjection)

/-- The functor of isomorphism classes of deformations of a finite-dimensional representation
of `Γ` over a classical base has a hull, provided its tangent space is finite dimensional: a
versal formal object with bijective differential.

This is the first clause of Stacks 0ET1 with the finite-dimensionality of the tangent space —
the tangent-space clause of Stacks 0DVT, which that lemma cites for a finitely generated `Γ` —
carried as a hypothesis rather than discharged, since this library proves 0DVT for the
`Deformation.RepresentationCategory` presentation and that presentation is not bridged to the
one used here. -/
public theorem exists_hull_isomorphismClassFunctor
    (S : RepresentationDeformationSituation Λ k Γ V)
    (hfinite :
      letI : Fact (IsPredeformationCategory.{u, w, w}
          (BasedCategory.ofFunctor S.deformationProjection).p) :=
        ⟨S.isPredeformationCategory_deformationProjection⟩
      letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
          (BasedCategory.ofFunctor S.deformationProjection)
          S.isPredeformationCategory_deformationProjection.cofibered))) :=
        ⟨S.schlessingerConditionS2_isomorphismClassFunctor⟩
      FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k (isomorphismClasses
        (BasedCategory.ofFunctor S.deformationProjection)
        S.isPredeformationCategory_deformationProjection.cofibered))) :
    ∃ ξ : FormalObject (Functor.Elements.π S.isomorphismClassFunctor),
      IsVersal (categoryOfElements_projection_isCofibered S.isomorphismClassFunctor) ξ ∧
        HasBijectiveDifferential
          (categoryOfElements_projection_isCofibered S.isomorphismClassFunctor) ξ := by
  let : IsNoetherianRing Λ := S.classical.isNoetherianRing
  let : Module.Finite Λ k := S.classical.moduleFinite
  let : Algebra.IsSeparable (residueImageField Λ k) k := S.classical.isSeparable
  let : Fact (IsPredeformationCategory.{u, w, w}
      (BasedCategory.ofFunctor S.deformationProjection).p) :=
    ⟨S.isPredeformationCategory_deformationProjection⟩
  let : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
      (BasedCategory.ofFunctor S.deformationProjection)
      S.isPredeformationCategory_deformationProjection.cofibered))) :=
    ⟨S.schlessingerConditionS2_isomorphismClassFunctor⟩
  let : FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k (isomorphismClasses
      (BasedCategory.ofFunctor S.deformationProjection)
      S.isPredeformationCategory_deformationProjection.cofibered)) := hfinite
  obtain ⟨ξ, -, hversal, hbijective⟩ :=
    exists_hull_isomorphismClasses.{u, w, w} Λ k
      (BasedCategory.ofFunctor S.deformationProjection)
      S.isPredeformationCategory_deformationProjection
      S.schlessingerConditionS1_deformationProjection
      S.schlessingerConditionS2_deformationProjection inferInstance
  exact ⟨imageInIsomorphismClasses _ S.isPredeformationCategory_deformationProjection ξ,
    hversal, hbijective⟩

end Deformation.Examples.RepresentationDeformationSituation

end
