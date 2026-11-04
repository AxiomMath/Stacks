module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DimensionFormula

/-!
# The parts of constant dimension of a smooth morphism

A smooth morphism `s_X : X ⟶ S` decomposes `X` into the open and closed subschemes `X_d` on which
it has relative dimension `d` (Stacks 02NM); over a field, `X_d` is the part of `X` of dimension
`d`. The constructions of Stacks Section 0FC0 and Section 0FC9 for a smooth `X` of varying
dimension "decompose into the parts lying over the open and closed subschemes of `X` where `X` has
a given dimension": a scheme `Y` over `X` is the disjoint union of the open and closed parts
`Y_d = a⁻¹(X_d)` lying over them, and a Chow class of `Y` restricts to each.

## Main definitions

* `Stacks.WeilCohomology.dimPart`: the open and closed part `X_d` of `X` on which a smooth
  morphism has relative dimension `d` (Stacks 02NM), with structure morphism `partBase`.
* `Stacks.Chow.dimPartOver`, `Stacks.Chow.dimPartOverHom`: the part `Y_d = a⁻¹(X_d)` of a scheme
  `a : Y ⟶ X` over `X`, and the restriction `a_d : Y_d ⟶ X_d` of `a`.
* `Stacks.Chow.chowGroupDimPartOver`: restriction `CH_n(Y) ⟶ CH_n(Y_d)`.

## References

* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Section 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Section 0FC9](https://stacks.math.columbia.edu/tag/0FC9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

section Parts

variable {X S : Scheme.{u}} (sX : X ⟶ S) [Smooth sX]

/-- **Stacks 02NM** for a smooth morphism: the open and closed part of `X` on which `sX` has
relative dimension `d`; over a field, the part of dimension `d`. -/
def dimPart (d : ℕ) : X.Opens :=
  relativeDimensionOpen sX (fun s ↦ isCohenMacaulay_fiber_of_smooth sX s) d

/-- The structure morphism of the part of dimension `d`. -/
abbrev partBase (d : ℕ) : (dimPart sX d).toScheme ⟶ S := (dimPart sX d).ι ≫ sX

/-- The structure morphism `X_d ⟶ S` of the part of dimension `d` has relative dimension `d`. -/
theorem relativeDimension_partBase (d : ℕ) : RelativeDimension (partBase sX d) d :=
  relativeDimensionOpen_relativeDimension sX _ d

/-- The parts `X_d` of constant relative dimension form a decomposition of `X` into pairwise
disjoint open and closed subschemes covering `X`. -/
theorem isClopenDecomposition_dimPart : IsClopenDecomposition (dimPart sX) where
  disjoint _ _ h := pairwise_disjoint_relativeDimensionOpen sX _ h
  iSup_eq_top := iSup_relativeDimensionOpen sX _

/-- The structure morphism `X_d ⟶ S` of the part of dimension `d` is smooth. -/
instance (d : ℕ) : Smooth (partBase sX d) := inferInstance

/-- If `sX` is proper, then so is the structure morphism `X_d ⟶ S` of the part of
dimension `d`. -/
instance [IsProper sX] (d : ℕ) : IsProper (partBase sX d) := by
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  infer_instance

end Parts

end Stacks.WeilCohomology

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase)

section PartsOver

variable {X Y S : Scheme.{u}} (sX : X ⟶ S) [Smooth sX] (a : Y ⟶ X)

/-- The part `Y_d = a⁻¹(X_d)` of a scheme `a : Y ⟶ X` lying over the part `X_d` of `X` of
relative dimension `d`, an open and closed subscheme of `Y`. -/
abbrev dimPartOver (d : ℕ) : Y.Opens :=
  a ⁻¹ᵁ dimPart sX d

/-- The restriction `a_d : Y_d ⟶ X_d` of `a : Y ⟶ X` to the parts over `X_d`. -/
abbrev dimPartOverHom (d : ℕ) : (dimPartOver sX a d).toScheme ⟶ (dimPart sX d).toScheme :=
  a ∣_ dimPart sX d

/-- `Y_d ⟶ X_d ⟶ S` is `Y_d ⟶ Y ⟶ X ⟶ S`. -/
theorem dimPartOverHom_comp_partBase (d : ℕ) :
    dimPartOverHom sX a d ≫ partBase sX d = (dimPartOver sX a d).ι ≫ (a ≫ sX) := by
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

end PartsOver

section ChowParts

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [Smooth sX] (a : Y ⟶ X)
  [LocallyOfFiniteType a]

/-- Restriction `CH_n(Y) ⟶ CH_n(Y_d)` of a Chow class of a scheme `Y` over `X` to its part
`Y_d = a⁻¹(X_d)` over the part `X_d` of `X` of relative dimension `d`, presented on the structure
morphism `Y_d ⟶ X_d ⟶ S`. -/
def chowGroupDimPartOver (d : ℕ) (n : ℤ) :
    chowGroup C (a ≫ sX) n →+ chowGroup C (dimPartOverHom sX a d ≫ partBase sX d) n :=
  chowGroupRestrict C (a ≫ sX) _ (dimPartOver sX a d).ι
    (dimPartOverHom_comp_partBase sX a d).symm n

end ChowParts

end Stacks.Chow

end
