module

public import StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteOverDenseOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# A birational morphism is an isomorphism over a dense open

A birational morphism between schemes with finitely many irreducible components is an
isomorphism over a dense open subscheme of its target, provided it is quasi-compact or
separated and provided it is locally of finite type with reduced target or locally of finite
presentation.

The two hypotheses play different roles. The second one is what makes the morphism an
isomorphism between *some* pair of dense opens, one in the source and one in the target. The
first one is what lets that pair be replaced by a single dense open of the target: it makes the
morphism finite over a dense open, and a finite morphism is closed, so the locus where the
source open fails to cover the fibre can be removed from the target.

## Main results

* `AlgebraicGeometry.exists_dense_open_isIso_morphismRestrict_of_isBirational`: a birational
  morphism satisfying the two hypotheses is an isomorphism over a dense open of its target.

## Implementation notes

The proof is the composition of two results already available. Shrinking the target to a dense
open over which the morphism becomes finite is
`AlgebraicGeometry.exists_dense_open_isFinite`, whose hypothesis that the preimage of the
generic points is exactly the generic points is supplied for a birational morphism by
`AlgebraicGeometry.preimage_genericPoints_eq_genericPoints_of_isBirational`. Turning the
resulting finite birational morphism into an isomorphism over a further dense open is
`AlgebraicGeometry.exists_dense_open_isIso_morphismRestrict_of_isIntegralHom`, since a finite
morphism is integral. Composing the two restrictions back into a single one uses Mathlib's
`AlgebraicGeometry.morphismRestrictRestrict`.

Both halves need the schemes involved to have finitely many irreducible components, and the
second half needs this for the two open subschemes cut out along the way; that an open
subscheme inherits the property is `AlgebraicGeometry.finite_irreducibleComponents_opens`,
obtained by transporting generic points along the open immersion.

## References

* [Stacks Project, Tag 0BAJ](https://stacks.math.columbia.edu/tag/0BAJ)
* [Stacks Project, Tag 0BAI](https://stacks.math.columbia.edu/tag/0BAI)
* [Stacks Project, Tag 0BAC](https://stacks.math.columbia.edu/tag/0BAC)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An open subscheme of a scheme with finitely many irreducible components again has finitely
many irreducible components: its generic points inject into those of the ambient scheme. -/
theorem finite_irreducibleComponents_opens {X : Scheme.{u}}
    [Finite (irreducibleComponents X)] (U : X.Opens) :
    Finite (irreducibleComponents U.toScheme) := by
  have hX : Finite (genericPoints X) := Finite.of_equiv _ (genericPoints.equiv (α := X)).symm
  have hU : Topology.IsOpenEmbedding U.ι.base := U.ι.isOpenEmbedding
  have hUgen : Finite (genericPoints U.toScheme) := by
    refine Finite.of_injective
      (fun η : genericPoints U.toScheme =>
        (⟨U.ι η.1, hU.mem_genericPoints η.2⟩ : genericPoints X)) ?_
    intro a b hab
    exact Subtype.ext (hU.injective (congrArg (fun z : genericPoints X => (z : X)) hab))
  exact Finite.of_equiv _ (genericPoints.equiv (α := U.toScheme))

/-- **Stacks Project, Tag 0BAJ.** A birational morphism between schemes with finitely many
irreducible components is an isomorphism over a dense open subscheme of its target, provided it
is quasi-compact or separated and provided it is locally of finite type with reduced target or
locally of finite presentation. -/
@[stacks 0BAJ]
theorem exists_dense_open_isIso_morphismRestrict_of_isBirational
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (hf : IsBirational f) (hqc_or_sep : QuasiCompact f ∨ IsSeparated f)
    (hfin : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsIso (f ∣_ V) := by
  have hLFT : LocallyOfFiniteType f := by
    rcases hfin with ⟨h, -⟩ | h
    · exact h
    · have := h; infer_instance
  have hX : (genericPoints X).Finite := genericPoints.finite (Set.toFinite _)
  have hY : (genericPoints Y).Finite := genericPoints.finite (Set.toFinite _)
  obtain ⟨V, hVdense, hVfin⟩ := exists_dense_open_isFinite f hX hY
    (preimage_genericPoints_eq_genericPoints_of_isBirational f hf) hqc_or_sep
  have : IsFinite (f ∣_ V) := hVfin
  have := finite_irreducibleComponents_opens (f ⁻¹ᵁ V)
  have := finite_irreducibleComponents_opens V
  have hfin' : (LocallyOfFiniteType (f ∣_ V) ∧ IsReduced V.toScheme) ∨
      LocallyOfFinitePresentation (f ∣_ V) := by
    rcases hfin with ⟨-, h⟩ | h
    · have := h
      exact Or.inl ⟨inferInstance, inferInstance⟩
    · have := h
      exact Or.inr inferInstance
  obtain ⟨W, hWdense, hWiso⟩ := exists_dense_open_isIso_morphismRestrict_of_isIntegralHom
    (f ∣_ V) (hf.morphismRestrict V) hfin'
  refine ⟨V.ι ''ᵁ W, ?_, ?_⟩
  · have hVrange : DenseRange V.ι.base := by rwa [DenseRange, Scheme.Opens.range_ι]
    simpa only [Scheme.Hom.coe_image] using hVrange.dense_image V.ι.continuous hWdense
  · exact (Arrow.isIso_iff_isIso_of_isIso (morphismRestrictRestrict f V W).hom).mp hWiso

end AlgebraicGeometry

end
