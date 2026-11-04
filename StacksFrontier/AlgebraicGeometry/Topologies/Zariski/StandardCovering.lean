module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.StandardCoverings

/-!
# Standard Zariski coverings

A Zariski covering of an affine scheme `T` is *standard*, that is
`AlgebraicGeometry.IsStandardZariskiCovering`, when it has finitely many members and each
member is identified by its structure morphism with a standard affine open `T.basicOpen f`
of the target.

Every Zariski covering of an affine scheme admits a standard refinement: the covering can be
refined by finitely many basic opens, each contained in a member of the original covering.
This is the usual reduction of a Zariski covering of an affine scheme to a finite covering by
distinguished opens, and it is what makes the affine Zariski site cofinal in the Zariski site.

## Main results

* `AlgebraicGeometry.Scheme.OpenCover.exists_isStandardZariski_refinement` — every Zariski
  covering of an affine scheme admits a standard refinement.

## Implementation notes

A Zariski covering is Mathlib's `AlgebraicGeometry.Scheme.OpenCover`, equivalently a cover for
`Scheme.zariskiPrecoverage`; the two are the same type, so `IsStandardZariskiCovering`
applies to either spelling. A refinement is a morphism of covers, and finiteness of the
refining cover's index type expresses the finite list of basic opens. A member is
identified with a standard
affine open exactly when its structure morphism factors as an isomorphism onto
`T.basicOpen f` followed by that open subscheme's inclusion; since a component of a morphism
of covers is itself an open immersion, the refinement datum also exhibits each basic open
inside the corresponding member of the original covering.

## References

* [Stacks Project, Tag 020Q](https://stacks.math.columbia.edu/tag/020Q)
* [Stacks Project, Tag 020R](https://stacks.math.columbia.edu/tag/020R)
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

/-- **Stacks Project, Tag 020Q.** Every Zariski covering of an affine scheme has a finite
refinement by standard opens, each contained in a member of the original covering. -/
@[stacks 020Q]
public theorem OpenCover.exists_isStandardZariski_refinement {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.OpenCover.{v}) :
    ∃ (𝒱 : T.OpenCover.{v}) (_refinement : 𝒱 ⟶ 𝒰),
      AlgebraicGeometry.IsStandardZariskiCovering 𝒱 := by
  let β := Σ i, {f : Γ(T, ⊤) // T.basicOpen f ≤ (𝒰.f i).opensRange}
  have hcov : (Set.univ : Set T) ⊆ ⋃ b : β, (T.basicOpen b.2.1 : Set T) := by
    intro x _
    have hxrange : x ∈ Set.range (𝒰.f (𝒰.idx x)) := 𝒰.covers x
    obtain ⟨V, hVB, hxV, hV⟩ :=
      (isBasis_basicOpen T).exists_subset_of_mem_open hxrange
        (IsOpenImmersion.isOpen_range (𝒰.f (𝒰.idx x)))
    obtain ⟨_, ⟨f, rfl⟩, rfl⟩ := hVB
    exact Set.mem_iUnion.mpr ⟨⟨𝒰.idx x, f, hV⟩, hxV⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : β ↦ (T.basicOpen b.2.1 : Set T))
    (fun b ↦ (T.basicOpen b.2.1).isOpen) hcov
  let φ : Fin t.card → β := fun j ↦ t.equivFin.symm j
  let U : ULift.{v} (Fin t.card) → T.Opens := fun j ↦ T.basicOpen (φ j.down).2.1
  have hU : IsOpenCover U := by
    apply IsOpenCover.mk
    apply Opens.ext
    ext x
    simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine ⟨ULift.up (t.equivFin ⟨b, hb⟩), ?_⟩
    have hφ : φ (t.equivFin ⟨b, hb⟩) = b := by simp [φ]
    show x ∈ T.basicOpen (φ (t.equivFin ⟨b, hb⟩)).2.1
    rw [hφ]
    exact hxb
  let 𝒱 : T.OpenCover.{v} := T.openCoverOfIsOpenCover U hU
  let refinement : 𝒱 ⟶ 𝒰 :=
    { s₀ := fun j ↦ (φ j.down).1
      h₀ := fun j ↦ T.homOfLE (φ j.down).2.2 ≫ (𝒰.f (φ j.down).1).isoOpensRange.inv
      w₀ := fun b ↦ by
        show (T.homOfLE (φ b.down).2.2 ≫
          (𝒰.f (φ b.down).1).isoOpensRange.inv) ≫ 𝒰.f (φ b.down).1 =
            (T.basicOpen (φ b.down).2.1).ι
        simp [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] }
  refine ⟨𝒱, refinement, Finite.of_injective ULift.down ULift.down_injective, ?_⟩
  exact fun j ↦ ⟨(φ j.down).2.1, Iso.refl _, (Category.id_comp _).symm⟩

end AlgebraicGeometry.Scheme
