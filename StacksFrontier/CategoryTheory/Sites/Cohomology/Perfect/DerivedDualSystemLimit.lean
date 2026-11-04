module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfDerivedHoms
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFilteredColimitsSections
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a homotopy colimit of perfect objects

Let `(𝒞, 𝒪)` be a ringed site, let `(Kₙ)` be a system of perfect objects of `D(𝒪)` and let
`K = hocolim Kₙ` be its derived colimit. **Stacks 0A0A**, which the source labels *trivial
duality for systems of perfect objects*, says that for every object `E` of `D(𝒪)`

`R𝑆heafHom_𝒪(K, E) = R lim (E ⊗^𝐋_𝒪 Kₙ^∨)`,

the right-hand side being the derived limit of the inverse system of tensor products with the
dual perfect complexes.

## Main results

* `AlgebraicGeometry.RingedSite.derivedHom_isDerivedLimit_tensorDual`: **Stacks 0A0A**, at the
  hypotheses of the source — that each `Kₙ` is perfect and that `K` is the derived colimit of
  the system.

## Implementation notes

The source's proof has two steps, and both are in the library. The first rewrites the
right-hand side as `R lim R𝑆heafHom_𝒪(Kₙ, E)`, which is Stacks 08JJ at each term: tensoring
with the dual of a perfect object computes derived internal Hom,
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso`. That isomorphism is
contravariantly natural in the dualized object between perfect objects,
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso_naturality_dual`, so the perfectness
of every term makes the two inverse systems
`AlgebraicGeometry.RingedSite.tensorDerivedDualSystem` and
`AlgebraicGeometry.RingedSite.derivedSheafHomSystem` isomorphic, and being a derived limit
transports along an isomorphism of systems by
`CategoryTheory.Pretriangulated.IsDerivedLimit.of_natIso`.

The second step compares the triangle defining the derived limit of the system
`n ↦ R𝑆heafHom_𝒪(Kₙ, E)` with the image under `R𝑆heafHom_𝒪(-, E)` of the triangle
`⊕ Kₙ → ⊕ Kₙ → K` defining the derived colimit, through the identification
`R𝑆heafHom_𝒪(⊕ Kₙ, E) = ∏ R𝑆heafHom_𝒪(Kₙ, E)`. It is
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit'`, which holds
for an arbitrary system of objects of `D(𝒪)`: the identification of the internal Hom out of a
direct sum with the product is
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison` and the comparison of
triangles is
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit`.

The derived tensor product is the canonical one of Stacks 06YU,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, which is the datum the isomorphism of
Stacks 08JJ is stated for; its bifunctor is
`Stacks.SheafOfModules.derivedTensorProductFunctor`.

The ringed site carries no hypothesis at all: the statement's only binders are the system, the
two objects, the perfectness of the terms and the derived colimit, which are exactly the
source's. The sheafification, additivity and `HomologicalComplex.HasMapBifunctor` instances that
the constructions appearing in the statement need are not assumed but synthesized, every one of
them being available for an arbitrary `RingedSite.{u, u, u}`; and no existence assumption is
carried either, `CategoryTheory.Pretriangulated.IsHomotopyColimit` and
`CategoryTheory.Pretriangulated.IsDerivedLimit` mentioning `⊕ Kₙ` and the product of the system
in their types and so each taking a `CategoryTheory.Limits.HasCoproduct` or
`CategoryTheory.Limits.HasProduct` instance argument, supplied by instance search from the
unconditional instances of Stacks 07D9 for the derived category of a Grothendieck abelian
category, as recorded in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit`.

The universes are the diagonal `RingedSite.{u, u, u}` with the standard derived category, as in
every file of the derived internal Hom cluster.

## References

* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-! ### Universe-pinned instances

Every class below is available for an arbitrary `RingedSite.{u, u, u}`, so none of them is a
hypothesis of the tag. Instance search nevertheless reaches them only through declarations
stated over `max u v w`-indexed data, which from the diagonal goal makes it solve
`max ?u ?v ?w =?= u` before it can commit; restating each at the diagonal collapses that to a
head match. Nothing is assumed here that search could not already find — these only make it
find it quickly. The four sheafification instances are the library's own diagonal ones,
`Stacks.SheafOfModules.InternalHom.hasSheafifyAbelian_sections`,
`Stacks.SheafOfModules.InternalHom.wEqualsLocallyBijectiveAbelian_sections`,
`AlgebraicGeometry.RingedSite.hasSheafifyOver` and
`AlgebraicGeometry.RingedSite.wEqualsLocallyBijectiveOver`, made local instances here under the
names they had in this file; the remaining ones are proved by `inferInstance`. -/

alias hasSheafify_diag := Stacks.SheafOfModules.InternalHom.hasSheafifyAbelian_sections

alias wEqualsLocallyBijective_diag :=
  Stacks.SheafOfModules.InternalHom.wEqualsLocallyBijectiveAbelian_sections

alias hasSheafify_over_diag := AlgebraicGeometry.RingedSite.hasSheafifyOver

alias wEqualsLocallyBijective_over_diag := AlgebraicGeometry.RingedSite.wEqualsLocallyBijectiveOver

attribute [local instance] hasSheafify_diag wEqualsLocallyBijective_diag hasSheafify_over_diag
  wEqualsLocallyBijective_over_diag

/-- The tensor product bifunctor of sheaves of `X.O`-modules is additive in its first variable. -/
local instance sheafTensor_additive_diag :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive := inferInstance

/-- For each sheaf of `X.O`-modules `A`, the functor `A ⊗ -` is additive. -/
local instance sheafTensor_obj_additive_diag (A) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive :=
  inferInstance

/-- Any two cochain complexes of sheaves of `X.O`-modules admit the total complex of their
tensor product bicomplex. -/
local instance hasMapBifunctor_diag
    (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) := inferInstance

/-- **Stacks 0A0A: derived internal Hom out of a homotopy colimit of perfect objects.** Let
`(𝒞, 𝒪)` be a ringed site, let `(Kₙ)` be a system of perfect objects of `D(𝒪)`, let
`K = hocolim Kₙ` and let `E` be an object of `D(𝒪)`. Then

`R𝑆heafHom_𝒪(K, E) = R lim (E ⊗^𝐋_𝒪 Kₙ^∨)`.

Perfectness of the terms turns the system of tensor products with the duals into the system
`n ↦ R𝑆heafHom_𝒪(Kₙ, E)`, by Stacks 08JJ and its contravariant naturality; the latter system
has `R𝑆heafHom_𝒪(K, E)` as its derived limit for every system with derived colimit `K`. -/
@[stacks 0A0A "the identity `R𝑆heafHom(K, E) = R lim (E ⊗^L_O Kₙ^∨)` for a system of perfect \
objects `Kₙ` with derived colimit `K`, at the hypotheses of the source: the perfectness of each \
`Kₙ` and `K = hocolim Kₙ`. The direct-sum comparison and the identification of Stacks 08JJ that \
the source's proof uses are both proved in the library, so this needs nothing beyond those two \
hypotheses: the ringed site carries no hypothesis, the sheafification and additivity instances \
the statement's constructions need being synthesized rather than assumed, and the existence of \
`⊕ Kₙ` and of the products coming from the instances of Stacks 07D9"]
theorem derivedHom_isDerivedLimit_tensorDual
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hF : ∀ n : ℕ, X.IsPerfect (F.obj n))
    (hK : IsHomotopyColimit F K) :
    IsDerivedLimit
        (tensorDerivedDualSystem X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) F E)
      (((derivedSheafHomBifunctor X).obj (op K)).obj E) :=
  IsDerivedLimit.of_natIso
    (NatIso.ofComponents
        (fun n ↦ derivedDualTensorSheafHomIso X (F.obj n.unop) E (hF n.unop))
        (fun {n m} g ↦ derivedDualTensorSheafHomIso_naturality_dual X (hF n.unop) (hF m.unop) E
          (F.map g.unop))).symm
    (isDerivedLimit_derivedSheafHom_of_isHomotopyColimit' X F E hK)

end AlgebraicGeometry.RingedSite

end
