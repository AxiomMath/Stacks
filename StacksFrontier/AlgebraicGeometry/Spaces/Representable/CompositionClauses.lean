module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp

/-!
# Further entries of the composition list

Five more properties of morphisms of schemes that are preserved by composition:
quasi-affine, (locally) quasi-finite, syntomic, H-projective and finite locally free. Each
is already available as a declaration elsewhere in this library and is adopted rather than
restated.

Quasi-affineness is `AlgebraicGeometry.IsQuasiAffineHom` and its stability is
`AlgebraicGeometry.isQuasiAffineHom_isStableUnderComposition`; being syntomic is
`AlgebraicGeometry.Syntomic` with
`AlgebraicGeometry.syntomic_isStableUnderComposition`; being H-projective is
`AlgebraicGeometry.IsProjectiveMorphism` with
`AlgebraicGeometry.IsProjectiveMorphism.comp`; and being finite locally free is
`AlgebraicGeometry.IsFiniteLocallyFree` with
`Stacks.Morphisms.isFiniteLocallyFree_comp`.

Quasi-finiteness is a conjunction: a morphism is locally quasi-finite when it is locally of
finite type with discrete fibres, and quasi-finite when it is moreover quasi-compact. Its
two entries are therefore the conjunction-level statements
`AlgebraicGeometry.locallyQuasiFinite_conditions_comp` and
`AlgebraicGeometry.quasiFinite_conditions_comp`.

## References

* [Stacks Project, Tag 02WG](https://stacks.math.columbia.edu/tag/02WG)
-/

@[expose] public section

add_to_stacks 02WG "finite_locally_free" Stacks.Morphisms.isFiniteLocallyFree_comp

add_to_stacks 02WG "h_projective" AlgebraicGeometry.IsProjectiveMorphism.comp

add_to_stacks 02WG "quasi_affine"
  AlgebraicGeometry.isQuasiAffineHom_isStableUnderComposition

add_to_stacks 02WG "quasi_finite" AlgebraicGeometry.locallyQuasiFinite_conditions_comp

add_to_stacks 02WG "quasi_finite" AlgebraicGeometry.quasiFinite_conditions_comp

add_to_stacks 02WG "syntomic" AlgebraicGeometry.syntomic_isStableUnderComposition

end
