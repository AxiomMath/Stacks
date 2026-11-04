module
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
import all StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Artinian.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension

/-!
# ZeroUnconditional

Stronger forms of declarations of `StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero`,
stated as separate declarations beside the ones there: over more general coefficient universes,
or with inputs that are carried there as hypotheses discharged, together with the new results
built on them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme locally of finite type over a field and of dimension zero has locally quasi-finite
structure morphism, its fibres being discrete. -/
private lemma locallyQuasiFinite_of_dimension_zero_general
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim X ≤ 0) :
    LocallyQuasiFinite f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  exact locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun _ ↦
    IsDiscrete.univ.mono (Set.subset_univ _)

/-- The structure morphism of a zero-dimensional scheme of finite type over a field is finite. -/
private lemma isFinite_toSpec_of_dimension_zero_general
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 0) : IsFinite f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : LocallyQuasiFinite f := locallyQuasiFinite_of_dimension_zero_general k f hdim
  exact IsFinite.of_locallyQuasiFinite f

/-- The structure morphism of a scheme of finite type over a field of dimension at most zero —
zero-dimensional or empty — is finite. This generalizes
`AlgebraicGeometry.isFinite_of_finiteType_of_dimension_zero` to the empty scheme, which has
dimension `⊥`. -/
alias isFinite_of_finiteType_of_topologicalKrullDim_le_zero :=
  isFinite_toSpec_of_dimension_zero_general

end AlgebraicGeometry

end
