module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.GenericPoints

/-!
# Normalizing a modification

The normalization morphism of an integral Nagata scheme is itself a modification: it is
birational, it is finite and hence proper, and its source is integral. Consequently a
modification `f : X ⟶ S` may always be replaced by a modification whose source is normal,
namely the composite of `f` with the normalization morphism of `X`. When the target `S` is a
Nagata scheme this needs no further assumption on `X`, because a modification is locally of
finite type and a scheme locally of finite type over a Nagata scheme is Nagata.

## Main results

* `AlgebraicGeometry.isModification_normalization`: the normalization morphism of an integral
  Nagata scheme is a modification.
* `AlgebraicGeometry.isModification_normalization_comp_of_isNagataScheme`: the normalization
  morphism of the source of a modification, composed with that modification, is a modification.
* `AlgebraicGeometry.exists_isNormal_isModification_normalization`: for a modification over a
  Nagata target, the resulting normal modification packaged with the factorization, so that a
  consumer need not produce the finiteness datum of the irreducible components.

## Implementation notes

Forming the normalization morphism `AlgebraicGeometry.Scheme.normalization` requires the
quasi-compact opens of the scheme to have finitely many irreducible components. The first two
results take that datum as an argument, since it appears in the type of the morphism and there
is more than one way to produce it; the third supplies
`AlgebraicGeometry.finite_irreducibleComponents_of_isNagataScheme`, which derives it from the
Nagata condition, and so fixes one spelling of the morphism. For an integral scheme the datum is
also immediate from irreducibility, by
`AlgebraicGeometry.finite_irreducibleComponents_of_irreducibleSpace`; that route is not used
here because the Nagata condition is needed anyway, for finiteness of the normalization.

Properness of the normalization morphism comes from its finiteness, which is where the Nagata
condition enters; birationality needs only reducedness of the scheme, and integrality of the
normalization of an integral scheme is an instance.

## References

The inputs are [Stacks, Tag 035N] for the normalization morphism, [Stacks, Tag 035S] for its
finiteness over a Nagata scheme, [Stacks, Tag 0BXC] for its birationality, [Stacks, Tag 035A]
for stability of the Nagata condition under morphisms locally of finite type, and
[Stacks, Tag 0AAZ] for the definition of a modification.

* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 035S](https://stacks.math.columbia.edu/tag/035S)
* [Stacks Project, Tag 0BXC](https://stacks.math.columbia.edu/tag/0BXC)
* [Stacks Project, Tag 035A](https://stacks.math.columbia.edu/tag/035A)
* [Stacks Project, Tag 0AAZ](https://stacks.math.columbia.edu/tag/0AAZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The normalization morphism of an integral Nagata scheme is a modification.** It is
birational because the scheme is reduced, proper because it is finite, and its source is
integral because the scheme is. -/
theorem isModification_normalization {X : Scheme.{u}} [IsIntegral X] (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsModification (X.normalization hX) :=
  have : IsFinite (X.normalization hX) := Scheme.isFinite_normalization hNagata hX
  ⟨X.isBirational_normalization hX, inferInstance, inferInstance⟩

/-- **A modification stays a modification after normalizing its source.** For a modification
`f : X ⟶ S` with `X` an integral Nagata scheme, the composite of the normalization morphism of
`X` with `f` is again a modification of `S`. -/
theorem isModification_normalization_comp_of_isNagataScheme {X S : Scheme.{u}} [IsIntegral S]
    [IsIntegral X] (f : X ⟶ S) (hf : IsModification f) (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsModification (X.normalization hX ≫ f) :=
  have hν := isModification_normalization hNagata hX
  have := hν.isProper
  have := hf.isProper
  ⟨hν.isBirational.comp hf.isBirational, inferInstance, inferInstance⟩

/-- **Every modification over a Nagata target is dominated by a normal modification.** For a
modification `f : X ⟶ S` with `S` a Nagata scheme there is a normal scheme `Y`, a modification
`ν : Y ⟶ X` and a modification `g : Y ⟶ S` with `g = ν ≫ f`; one may take `Y` to be the
normalization of `X`, which is Nagata because `f` is locally of finite type. -/
theorem exists_isNormal_isModification_normalization {X S : Scheme.{u}} [IsIntegral S]
    [IsIntegral X] (f : X ⟶ S) (hf : IsModification f) (hS : IsNagataScheme S) :
    ∃ (Y : Scheme.{u}) (_ : IsNormal Y) (ν : Y ⟶ X) (g : Y ⟶ S),
      IsModification ν ∧ IsModification g ∧ g = ν ≫ f := by
  have : IsProper f := hf.isProper
  have hNagata : IsNagataScheme X := isNagataScheme_of_locallyOfFiniteType f hS
  have hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite :=
    Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme X hNagata
  exact ⟨X.normalizationScheme hX, Scheme.isNormal_normalizationScheme X hX, X.normalization hX,
    X.normalization hX ≫ f, isModification_normalization hNagata hX,
    isModification_normalization_comp_of_isNagataScheme f hf hNagata hX, rfl⟩

end AlgebraicGeometry

end
