module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleDerivedSheaves
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ReductionTower

/-!
# The tower of derived reductions of a pro-étale complex

Let `Λ` be a ring, `I ⊆ Λ` an ideal, `X` a scheme and `K` an object of `D(X_proét, Λ)`. The
reductions `K ⊗_Λ^L \underline{Λ/Iⁿ}` form an inverse system indexed by `n`, whose transition maps
are induced by the reductions `Λ/Iⁿ⁺¹ → Λ/Iⁿ`. Taking degree-zero cohomology and sections over
`X` gives the inverse system `n ↦ H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` of `Λ`-modules,
`AlgebraicGeometry.ProEtale.derivedReductionSectionsSystem`.

## Main definitions

* `AlgebraicGeometry.ProEtale.derivedReductionTower`: the inverse system
  `n ↦ K ⊗_Λ^L \underline{Λ/Iⁿ}` in the derived category of sheaves of `Λ`-modules on `X_proét`.

## Implementation notes

The tower is the tower `Stacks.ModuleSheaf.derivedReductionTower` of an arbitrary site, the
derived tensor product of `K` with the tower of constant sheaves `n ↦ \underline{Λ/IⁿΛ}` placed
in degree zero, so its transition maps are the images of the reduction maps under the derived
tensor product and involve no choice. Its `n`-th term, read
over `Λ`, is the derived reduction `AlgebraicGeometry.ProEtale.derivedReduction` modulo `Iⁿ`
(`Stacks.ModuleSheaf.nonempty_restrictScalars_derivedExtendScalars_iso`).

## References

* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
* [Stacks Project, Tag 09C6](https://stacks.math.columbia.edu/tag/09C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.ModuleSheaf.derivedMonoidal

/-- Local isomorphisms of presheaves of modules on `X_proét` are stable under tensor products;
this is the hypothesis under which the tensor product of sheaves of modules is defined. It is
recorded as an instance here because its search through the general criterion is expensive. -/
instance isMonoidal_W_moduleCat (X : Scheme.{u}) (R : Type (max (u + 1) w)) [CommRing R] :
    ((Scheme.ProEt.topology X).W (A := ModuleCat.{max (u + 1) w} R)).IsMonoidal :=
  inferInstance

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)

/-- The tower `n ↦ K ⊗_Λ^L \underline{Λ/Iⁿ}` of derived reductions of an object `K` of the
derived category of sheaves of `Λ`-modules on `X_proét`, with the transition maps induced by
the reductions `Λ/Iⁿ⁺¹ → Λ/Iⁿ`: the tower `Stacks.ModuleSheaf.derivedReductionTower` of the
pro-étale site. -/
abbrev derivedReductionTower
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :=
  Stacks.ModuleSheaf.derivedReductionTower (Scheme.ProEt.topology X) Λ I K

end AlgebraicGeometry.ProEtale

end
