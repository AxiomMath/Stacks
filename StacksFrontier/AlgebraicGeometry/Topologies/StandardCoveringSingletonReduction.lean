module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverSliceContinuity
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongACoefficientFunctor

/-!
# Reducing a standard covering to the morphism from its disjoint union

A standard `τ`-covering `{Uᵢ → T}` of an affine object has finitely many members, each affine,
and [Stacks, Tag 03OZ] replaces it by the single morphism `∐ Uᵢ → T`.  This file turns the two
halves of that replacement into the two statements the Amitsur endpoint of [Stacks, Tag 03FJ]
consumes.

The first is a transport of Čech vanishing: 03OZ part (3) says the Čech complexes of the family
and of the one-member covering agree for an abelian sheaf, so positive-degree Čech vanishing for
the one-member covering gives it for the family.  Only finiteness of the index type and the
sheaf condition are used, so the statement is proved for an arbitrary finite family on a
topology on `Over S` refining the big Zariski topology, and the `τ`-uniform form for a standard
covering is a corollary.

The second is faithful flatness of `Γ(T, 𝒪) ⟶ Γ(∐ Uᵢ, 𝒪)`.  Both sides are affine — the target
by 03OZ part (1) — and the morphism is flat and surjective, so
`AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` applies.  Flatness
is uniform in `τ` because a covering morphism of any of the five topologies is flat, and
flatness is Zariski-local at the source, hence stable under `Sigma.desc`.

## Main results

* `AlgebraicGeometry.isZero_cechCohomology_of_isZero_singleton_sigmaDesc`: **Čech vanishing
  transfers from the one-member covering to the family**, for an abelian sheaf on a topology on
  `Over S` refining the big Zariski topology.
* `AlgebraicGeometry.IsStandardCovering.isZero_cechCohomology_of_isZero_singleton_bigSite`: the
  same for a standard `τ`-covering of an affine object of the big `τ`-site.
* `AlgebraicGeometry.IsStandardCovering.flat_sigmaDesc` and
  `AlgebraicGeometry.IsStandardCovering.surjective_sigmaDesc`: the morphism from the disjoint
  union of a standard covering is flat and surjective.
* `AlgebraicGeometry.IsStandardCovering.faithfullyFlat_appTop_sigmaDesc`: **global sections
  along the morphism from the disjoint union of a standard covering are faithfully flat.**
* `AlgebraicGeometry.IsStandardCovering.flat_left_sigmaDesc`,
  `AlgebraicGeometry.IsStandardCovering.surjective_left_sigmaDesc` and
  `AlgebraicGeometry.IsStandardCovering.faithfullyFlat_appTop_left_sigmaDesc`: the same three
  statements for a family in `Over S`, where the disjoint union is taken in the slice.
* `AlgebraicGeometry.IsStandardCovering.faithfullyFlat_left_sigmaDesc`: the last of those in the
  `Module.FaithfullyFlat` shape, for the algebra structure induced by the morphism itself.

## Implementation notes

03OZ part (3) is stated for the coefficient presheaf composed with
`AddCommGrpCat.uliftFunctor`, because the Čech complex of a family indexed in universe `w`
needs products of that size in the coefficients and the general statement leaves the two
universes unrelated.  Here they coincide, so the lift is undone rather than needed:
`Stacks.CechSite.isZero_cechCohomology_comp_coefficients` pushes the vanishing through the lift
and `Stacks.CechSite.sliceCechCohomologyCompCoefficientsIso` brings it back, the last step being
`CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero` for the fully faithful
`AddCommGrpCat.uliftFunctor`.  Proving a version of 03OZ part (3) without the lift would need
`FinitaryExtensive (Over S)`, which the source file has only as a `private` instance.

For a family in `Over S` the disjoint union is computed in the slice, so its total space is only
*isomorphic* to the disjoint union of the total spaces; the isomorphism is
`AlgebraicGeometry.sigmaLeftIso`, and the two morphism properties are moved across it through
the factorization `AlgebraicGeometry.left_sigmaDesc_eq`: both are stable under composition and
hold of isomorphisms, so instance search closes the transported goal.  Going through
`CategoryTheory.MorphismProperty.cancel_left_of_respectsIso` instead does not work, because
`CategoryTheory.MorphismProperty.RespectsIso @Flat` is not found by instance search — the bare
class `@Flat` does not have a `CategoryTheory.MorphismProperty` as its type.  This is the same
identification that `AlgebraicGeometry.IsStandardCovering.isAffine_left_sigmaObj` makes inline;
it is named here because three statements need it.

No `@[stacks]` attribute is attached.  Tag 03OZ is carried by
`StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion`, and everything here is
a corollary of its parts (1) and (3) together with Mathlib's criterion for faithful flatness.

## References

* [Stacks Project, Tag 03OZ](https://stacks.math.columbia.edu/tag/03OZ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CechSite
open scoped AlgebraicGeometry

universe u w

namespace AlgebraicGeometry

/-! ### Čech vanishing transfers from the one-member covering -/

/-- **Čech vanishing transfers from the morphism out of the disjoint union to the family.**  For
an abelian sheaf on a topology on `Over S` refining the big Zariski topology and a finite family
of morphisms with fixed target, vanishing of the degree-`p` Čech cohomology of the one-member
covering by the morphism from the disjoint union gives vanishing for the family itself.

This is [Stacks, Tag 03OZ] part (3), in the form
`AlgebraicGeometry.isIso_cechComplexMap_coproductRefinement_over`, with the coefficient universe
lift that statement carries undone on both sides. -/
public theorem isZero_cechCohomology_of_isZero_singleton_sigmaDesc (S : Scheme.{u})
    (J : GrothendieckTopology (Over S)) (hJ : Scheme.zariskiTopology.over S ≤ J) {T : Over S}
    (E : PreZeroHypercover.{u} T) [Finite E.I₀] (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hF : Presheaf.IsSheaf J F) (p : ℕ)
    (h : IsZero (cechCohomology (PreZeroHypercover.singleton.{u} (Sigma.desc E.f)) F p)) :
    IsZero (cechCohomology E F p) := by
  have hiso := isIso_cechComplexMap_coproductRefinement_over S J hJ E F hF
  have hlift : IsZero (cechCohomology (PreZeroHypercover.singleton.{u} (Sigma.desc E.f))
      (F ⋙ AddCommGrpCat.uliftFunctor.{u, u}) p) :=
    isZero_cechCohomology_comp_coefficients _ AddCommGrpCat.uliftFunctor.{u, u} F p h
  have hfam : IsZero (cechCohomology E (F ⋙ AddCommGrpCat.uliftFunctor.{u, u}) p) :=
    hlift.of_iso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℕ) p).mapIso (asIso (cechComplexMap E
        (PreZeroHypercover.singleton.{u} (Sigma.desc E.f)) (coproductRefinement E)
        (F ⋙ AddCommGrpCat.uliftFunctor.{u, u})))).symm
  exact IsZero.of_full_of_faithful_of_isZero AddCommGrpCat.uliftFunctor.{u, u} _
    (hfam.of_iso (sliceCechCohomologyCompCoefficientsIso E AddCommGrpCat.uliftFunctor.{u, u}
      ((Over.forget T).op ⋙ F) p).symm)

/-- **Čech vanishing transfers from the morphism out of the disjoint union to a standard
`τ`-covering.**  The `τ`-uniform form of
`AlgebraicGeometry.isZero_cechCohomology_of_isZero_singleton_sigmaDesc`: the big Zariski
topology is coarser than each of the five, by
`AlgebraicGeometry.Scheme.zariskiTopology_le_grothendieckTopology`. -/
public theorem IsStandardCovering.isZero_cechCohomology_of_isZero_singleton_bigSite
    (τ : CoveringTopology) (S : Scheme.{u}) {T : Over S} [IsAffine T.left]
    (E : PreZeroHypercover.{u} T)
    (h : IsStandardCovering τ (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left))
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hF : Presheaf.IsSheaf
      ((Scheme.grothendieckTopology (coveringMorphismProperty τ)).over S) F)
    (p : ℕ)
    (hone : letI : Finite E.I₀ := h.finite_index
      IsZero (cechCohomology (PreZeroHypercover.singleton.{u} (Sigma.desc E.f)) F p)) :
    IsZero (cechCohomology E F p) := by
  have : Finite E.I₀ := h.finite_index
  refine isZero_cechCohomology_of_isZero_singleton_sigmaDesc S _ (fun T' R hR ↦ ?_) E F hF p hone
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact Scheme.zariskiTopology_le_grothendieckTopology τ _ hR

/-! ### Flatness and surjectivity of the morphism from the disjoint union -/

/-- Every member of a standard `τ`-covering is flat: a covering morphism of any of the five
topologies is flat and locally of finite presentation. -/
public theorem IsStandardCovering.flat (τ : CoveringTopology) {T : Scheme.{u}} [IsAffine T]
    {I : Type w} (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T) (h : IsStandardCovering τ U f) (i : I) :
    Flat (f i) :=
  (coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation τ (f i)
    (((Scheme.ofArrows_mem_precoverage_iff _).mp (h.ofArrows_mem_precoverage τ U f)).2 i)).1

/-- **The morphism from the disjoint union of a standard `τ`-covering is flat**, flatness being
Zariski-local at the source. -/
public theorem IsStandardCovering.flat_sigmaDesc (τ : CoveringTopology) {T : Scheme.{u}}
    [IsAffine T] {I : Type w} (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T)
    (h : IsStandardCovering τ U f) :
    letI : Finite I := h.finite_index
    Flat (Sigma.desc f) :=
  have : Finite I := h.finite_index
  have : ∀ i, Flat (f i) := h.flat τ U f
  inferInstance

/-- **The morphism from the disjoint union of a standard `τ`-covering is surjective**, the
members being jointly surjective. -/
public theorem IsStandardCovering.surjective_sigmaDesc (τ : CoveringTopology) {T : Scheme.{u}}
    [IsAffine T] {I : Type w} (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T)
    (h : IsStandardCovering τ U f) :
    letI : Finite I := h.finite_index
    Surjective (Sigma.desc f) :=
  have : Finite I := h.finite_index
  Surjective.sigmaDesc_of_union_range_eq_univ h.jointly_surjective

/-- A flat surjective morphism of affine schemes induces a faithfully flat map on global
sections. -/
private theorem faithfullyFlat_appTop_of_flat_of_surjective {X Y : Scheme.{u}} [IsAffine X]
    [IsAffine Y] (f : X ⟶ Y) (hf : Flat f) (hs : Surjective f) : f.appTop.hom.FaithfullyFlat :=
  (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).1 ⟨hf, hs⟩

/-- **Global sections along the morphism from the disjoint union of a standard `τ`-covering are
faithfully flat.**  The disjoint union is affine by [Stacks, Tag 03OZ] part (1) and the morphism
is flat and surjective, so
`AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` applies. -/
public theorem IsStandardCovering.faithfullyFlat_appTop_sigmaDesc (τ : CoveringTopology)
    {T : Scheme.{u}} [IsAffine T] {I : Type w} (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T)
    (h : IsStandardCovering τ U f) :
    letI : Finite I := h.finite_index
    (Sigma.desc f).appTop.hom.FaithfullyFlat :=
  have : Finite I := h.finite_index
  have : IsAffine (∐ U) := h.isAffine_sigmaObj τ U f
  faithfullyFlat_appTop_of_flat_of_surjective _ (h.flat_sigmaDesc τ U f)
    (h.surjective_sigmaDesc τ U f)

/-! ### The same for a family in the slice over a base -/

/-- The total space of the disjoint union, in `Over S`, of a finite family of objects of
`Over S` is the disjoint union of their total spaces: the forgetful functor to schemes preserves
coproducts. -/
public def sigmaLeftIso (S : Scheme.{u}) {I : Type w} (X : I → Over S) [HasCoproduct X]
    [HasCoproduct (fun i ↦ (X i).left)] : (∐ fun i ↦ (X i).left) ≅ (∐ X).left :=
  (coproductIsCoproduct (fun i ↦ (X i).left)).coconePointUniqueUpToIso
    ((isColimitMapCoconeCofanMkEquiv (Over.forget S) X _)
      (isColimitOfPreserves (Over.forget S) (coproductIsCoproduct X)))

/-- `AlgebraicGeometry.sigmaLeftIso` carries the `i`-th component inclusion of the disjoint
union of total spaces to the total space of the `i`-th component inclusion. -/
public theorem sigmaIota_comp_sigmaLeftIso_hom (S : Scheme.{u}) {I : Type w} (X : I → Over S)
    [HasCoproduct X] [HasCoproduct (fun i ↦ (X i).left)] (i : I) :
    Sigma.ι (fun j ↦ (X j).left) i ≫ (sigmaLeftIso S X).hom = (Sigma.ι X i).left :=
  (coproductIsCoproduct (fun j ↦ (X j).left)).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩

/-- `AlgebraicGeometry.sigmaLeftIso` identifies the total space of the morphism induced by a
family in `Over S` with the morphism induced by the family of total spaces. -/
public theorem sigmaLeftIso_hom_comp_left_sigmaDesc {S : Scheme.{u}} {T : Over S} {I : Type w}
    (X : I → Over S) (f : ∀ i, X i ⟶ T) [HasCoproduct X] [HasCoproduct (fun i ↦ (X i).left)] :
    (sigmaLeftIso S X).hom ≫ (Sigma.desc f).left = Sigma.desc (fun i ↦ (f i).left) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [Sigma.ι_comp_desc, ← Category.assoc, sigmaIota_comp_sigmaLeftIso_hom]
  exact congrArg (fun g : X i ⟶ T ↦ g.left) (Sigma.ι_comp_desc f i)

/-- The total space of the morphism induced by a family in `Over S` factors the morphism induced
by the family of total spaces through `AlgebraicGeometry.sigmaLeftIso`.  This is the shape in
which a property of morphisms stable under composition and holding of isomorphisms is carried
across the identification. -/
public theorem left_sigmaDesc_eq {S : Scheme.{u}} {T : Over S} {I : Type w} (X : I → Over S)
    (f : ∀ i, X i ⟶ T) [HasCoproduct X] [HasCoproduct (fun i ↦ (X i).left)] :
    (sigmaLeftIso S X).inv ≫ Sigma.desc (fun i ↦ (f i).left) = (Sigma.desc f).left := by
  rw [← sigmaLeftIso_hom_comp_left_sigmaDesc, Iso.inv_hom_id_assoc]

variable (τ : CoveringTopology) (S : Scheme.{u})

/-- **The total space of the morphism from the disjoint union of a standard `τ`-covering in
`Over S` is flat.** -/
public theorem IsStandardCovering.flat_left_sigmaDesc {T : Over S} [IsAffine T.left]
    (E : PreZeroHypercover.{w} T)
    (h : IsStandardCovering τ (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left)) :
    letI : Finite E.I₀ := h.finite_index
    Flat ((Sigma.desc E.f).left) := by
  have : Finite E.I₀ := h.finite_index
  have : Flat (Sigma.desc (fun i ↦ (E.f i).left)) :=
    h.flat_sigmaDesc τ (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left)
  change Flat ((Sigma.desc E.f).left)
  rw [← left_sigmaDesc_eq E.X E.f]
  infer_instance

/-- **The total space of the morphism from the disjoint union of a standard `τ`-covering in
`Over S` is surjective.** -/
public theorem IsStandardCovering.surjective_left_sigmaDesc {T : Over S} [IsAffine T.left]
    (E : PreZeroHypercover.{w} T)
    (h : IsStandardCovering τ (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left)) :
    letI : Finite E.I₀ := h.finite_index
    Surjective ((Sigma.desc E.f).left) := by
  have : Finite E.I₀ := h.finite_index
  have : Surjective (Sigma.desc (fun i ↦ (E.f i).left)) :=
    h.surjective_sigmaDesc τ (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left)
  change Surjective ((Sigma.desc E.f).left)
  rw [← left_sigmaDesc_eq E.X E.f]
  infer_instance

/-- **Global sections along the morphism from the disjoint union, in `Over S`, of a standard
`τ`-covering of an affine object are faithfully flat.**  This is the input `Γ(T, 𝒪) ⟶ Γ(∐ Uᵢ, 𝒪)`
faithfully flat that the Amitsur endpoint of [Stacks, Tag 03FJ] takes. -/
public theorem IsStandardCovering.faithfullyFlat_appTop_left_sigmaDesc {T : Over S}
    [IsAffine T.left] (E : PreZeroHypercover.{w} T)
    (h : IsStandardCovering τ (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left)) :
    letI : Finite E.I₀ := h.finite_index
    ((Sigma.desc E.f).left).appTop.hom.FaithfullyFlat :=
  have : Finite E.I₀ := h.finite_index
  have : IsAffine (∐ E.X).left := h.isAffine_left_sigmaObj τ S E
  faithfullyFlat_appTop_of_flat_of_surjective _ (h.flat_left_sigmaDesc τ S E)
    (h.surjective_left_sigmaDesc τ S E)

/-- `AlgebraicGeometry.IsStandardCovering.faithfullyFlat_appTop_left_sigmaDesc` in the
`Module.FaithfullyFlat` shape, for the algebra structure on `Γ(∐ Uᵢ, 𝒪)` induced by the morphism
itself.  This is the instance the Amitsur endpoint asks for. -/
public theorem IsStandardCovering.faithfullyFlat_left_sigmaDesc {T : Over S} [IsAffine T.left]
    (E : PreZeroHypercover.{w} T)
    (h : IsStandardCovering τ (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left)) :
    letI : Finite E.I₀ := h.finite_index
    letI : Algebra (Γ(T.left, ⊤) : Type u) (Γ((∐ E.X).left, ⊤) : Type u) :=
      ((Sigma.desc E.f).left).appTop.hom.toAlgebra
    Module.FaithfullyFlat (Γ(T.left, ⊤) : Type u) (Γ((∐ E.X).left, ⊤) : Type u) :=
  have : Finite E.I₀ := h.finite_index
  h.faithfullyFlat_appTop_left_sigmaDesc τ S E

end AlgebraicGeometry

end
