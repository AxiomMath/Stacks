module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of families of schemes and their disjoint unions

A morphism from a family of schemes over `S'` to a family of schemes over `S` consists of a
morphism `S' ⟶ S`, a map of index types, and component morphisms compatible with the two
structure maps. Such a morphism induces a morphism between the disjoint unions of the
members, lying over the given morphism of base schemes.

## Main definitions

* `AlgebraicGeometry.MorphismOfSchemeFamilies` bundles the two families and their morphism.
* `AlgebraicGeometry.MorphismOfSchemeFamilies.ofHomOver` is that bundling, read as a function
  of the two families, the morphism of bases, and the morphism of families over it.
* `AlgebraicGeometry.MorphismOfSchemeFamilies.coproductHom` is the induced morphism between
  their disjoint unions.

## Main results

* `AlgebraicGeometry.MorphismOfSchemeFamilies.coproductHom_comp` states that the induced
  morphism commutes with the maps to the base schemes.

## Implementation notes

Families and their morphisms are represented by `PreZeroHypercover` and
`PreZeroHypercover.HomOver`. The index types are taken in the universe of the schemes, so
the corresponding coproducts of schemes exist.

## References

* [Stacks Project, Section 35.2](https://stacks.math.columbia.edu/tag/0238)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The data of a morphism from a family of schemes over `S'` to a family of
schemes over `S`: a map `h : S' ⟶ S`, a map of index types, and compatible
component morphisms. -/
structure MorphismOfSchemeFamilies where
  /-- The base of the source family. -/
  sourceBase : Scheme.{u}
  /-- The base of the target family. -/
  targetBase : Scheme.{u}
  /-- The family over `sourceBase`. -/
  sourceFamily : PreZeroHypercover.{u} sourceBase
  /-- The family over `targetBase`. -/
  targetFamily : PreZeroHypercover.{u} targetBase
  /-- The morphism of base schemes. -/
  baseHom : sourceBase ⟶ targetBase
  /-- The morphism of families lying over `baseHom`. -/
  familyHom : sourceFamily.HomOver targetFamily baseHom

namespace MorphismOfSchemeFamilies

/-- A morphism of families of schemes with fixed target, bundled together with its two families
and its morphism of base schemes. -/
abbrev ofHomOver {R T : Scheme.{u}} (𝒳 : PreZeroHypercover.{u} R) (𝒴 : PreZeroHypercover.{u} T)
    (g : R ⟶ T) (φ : 𝒳.HomOver 𝒴 g) : MorphismOfSchemeFamilies.{u} where
  sourceBase := R
  targetBase := T
  sourceFamily := 𝒳
  targetFamily := 𝒴
  baseHom := g
  familyHom := φ

/-- The disjoint union of the schemes in the source family. -/
noncomputable abbrev sourceCoproduct (F : MorphismOfSchemeFamilies.{u}) : Scheme.{u} :=
  ∐ fun i ↦ F.sourceFamily.X i

/-- The disjoint union of the schemes in the target family. -/
noncomputable abbrev targetCoproduct (F : MorphismOfSchemeFamilies.{u}) : Scheme.{u} :=
  ∐ fun j ↦ F.targetFamily.X j

/-- The morphism between disjoint unions induced componentwise by a morphism
of families. -/
@[ega "IV 11.10.3"]
noncomputable def coproductHom (F : MorphismOfSchemeFamilies.{u}) :
    F.sourceCoproduct ⟶ F.targetCoproduct :=
  Sigma.desc fun i ↦ F.familyHom.h₀ i ≫ Sigma.ι _ (F.familyHom.s₀ i)

/-- The morphism induced on disjoint unions lies over the given morphism of
base schemes. -/
lemma coproductHom_comp (F : MorphismOfSchemeFamilies.{u}) :
    F.coproductHom ≫ Sigma.desc F.targetFamily.f =
      Sigma.desc F.sourceFamily.f ≫ F.baseHom := by
  ext i
  simp [coproductHom, Category.assoc, F.familyHom.w₀]

end MorphismOfSchemeFamilies

end AlgebraicGeometry
