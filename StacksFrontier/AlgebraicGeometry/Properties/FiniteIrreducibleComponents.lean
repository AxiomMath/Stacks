module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.IrreducibleComponents
public import StacksFrontier.Topology.Sober.SpecializationStableNeighborhood

/-!
# Schemes whose quasi-compact opens have finitely many irreducible components

Call a scheme `S` *locally component-finite* when every quasi-compact open of `S` has finitely
many irreducible components. On such a scheme a subset stable under specialization and under
generalization is open, because every point has an affine open neighbourhood, which is
quasi-sober and quasi-compact, so the local openness criterion for doubly stable subsets
applies there. The condition also passes from `S` to the source of an étale morphism `X ⟶ S`,
since it is local in the fppf topology.

## Main results

* `AlgebraicGeometry.isOpen_of_stableUnderSpecialization_of_stableUnderGeneralization`: on a
  locally component-finite scheme a doubly stable subset is open.
* `AlgebraicGeometry.finiteIrreducibleComponents_of_etale`: the condition ascends along an
  étale morphism of schemes.

## References

* [Stacks Project, Tag 0BAL](https://stacks.math.columbia.edu/tag/0BAL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- On a scheme all of whose quasi-compact opens have finitely many irreducible components, a
subset stable under specialization and under generalization is open. -/
theorem isOpen_of_stableUnderSpecialization_of_stableUnderGeneralization
    {S : Scheme.{u}} (hS : ∀ U : S.Opens, IsCompact (U : Set S) → (irreducibleComponents U).Finite)
    {E : Set S} (hspec : StableUnderSpecialization E) (hgen : StableUnderGeneralization E) :
    IsOpen E := by
  refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := x) (by trivial)
  have hemb := U.2.isOpenEmbedding_subtypeVal
  have : QuasiSober ↥U := hemb.quasiSober
  have hmem : (Subtype.val ⁻¹' E : Set ↥U) ∈ nhds (⟨x, hxU⟩ : ↥U) :=
    (hspec.preimage continuous_subtype_val).mem_nhds_of_stableUnderGeneralization
      (hgen.preimage continuous_subtype_val) (hS U hU.isCompact) hx
  exact Filter.mem_of_superset (hemb.image_mem_nhds.mpr hmem) (Set.image_preimage_subset _ _)

/-- Having finitely many irreducible components on every quasi-compact open passes from the
target of an étale morphism of schemes to its source. -/
theorem finiteIrreducibleComponents_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (hS : ∀ V : S.Opens, IsCompact (V : Set S) → (irreducibleComponents V).Finite) :
    ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite := by
  let Y : Bool → Scheme.{u} := fun b => if b then X else S
  let g : ∀ b, Y b ⟶ S := fun b => by
    cases b
    · exact 𝟙 S
    · exact f
  have hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage S := by
    refine (Scheme.ofArrows_mem_precoverage_iff
      (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr ⟨fun s => ⟨false, s, rfl⟩, fun b => ?_⟩
    cases b
    · show Flat (𝟙 S) ∧ LocallyOfFinitePresentation (𝟙 S)
      exact ⟨inferInstance, inferInstance⟩
    · show Flat f ∧ LocallyOfFinitePresentation f
      exact ⟨inferInstance, inferInstance⟩
  exact ObjectProperty.IsLocal.component
    (P := fun Z : Scheme.{u} => ∀ V : Z.Opens, IsCompact (V : Set Z) →
      (irreducibleComponents V).Finite) hg (g true) ⟨true⟩ hS

end AlgebraicGeometry
