module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.Tactic.StacksAttribute

/-!
# The genus of a scheme over a field

The genus of a scheme over a field is the dimension over that field of the first cohomology
group of its structure sheaf.

## Main definitions

* `AlgebraicGeometry.structureSheafCohomology` is the cohomology of the structure sheaf,
  retaining its module structure over the base ring.
* `AlgebraicGeometry.genus` is the genus of a scheme equipped with a morphism to the spectrum
  of a field.

## Main results

* `AlgebraicGeometry.genus_eq_finrank_structureSheafCohomology` is the characterizing formula
  `g = dim_k H¹(X, 𝒪_X)`.

## Implementation notes

The cohomology is expressed as the right-derived functor of global sections. To retain the
canonical vector-space structure over the specified field, global sections are taken after
pushforward to its spectrum. The definition is made for every scheme over a field; the
properness, dimension-one and global-sections hypotheses of the source ensure the expected
finiteness and geometric interpretation, but are not needed to form the invariant. The
cohomology construction packages the additive structure needed by the right-derived-functor
presentation, so clients do not need to supply that instance.

## References

* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The `i`-th cohomology of the structure sheaf of `X`, with scalars retained over the ring
defining the chosen affine base. -/
noncomputable abbrev structureSheafCohomology {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (i : ℕ) : ModuleCat.{u} R :=
  letI : (moduleSpecΓFunctor (R := .of R)).Additive := ⟨by intro M N φ ψ; ext x; rfl⟩
  ((((Scheme.Modules.pushforward f) ⋙ moduleSpecΓFunctor).rightDerived i).obj
    (SheafOfModules.unit X.ringCatSheaf))

/-- The genus of a scheme `X` over a field `k`, namely `dim_k H¹(X, 𝒪_X)`. -/
@[stacks 0BY7, stacks 0B9W "smooth projective geometrically irreducible curve over a field"]
noncomputable def genus {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : ℕ := Module.finrank k (structureSheafCohomology f 1)

/-- The genus is the dimension over the base field of the first cohomology of the structure
sheaf. -/
@[simp] theorem genus_eq_finrank_structureSheafCohomology {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    genus f = Module.finrank k (structureSheafCohomology f 1) := rfl

end AlgebraicGeometry
