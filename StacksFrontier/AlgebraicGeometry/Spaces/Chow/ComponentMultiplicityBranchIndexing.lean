module

public import StacksFrontier.AlgebraicGeometry.Spaces.BranchesOverComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BranchMultiplicityOverComponent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.EtaleLocalRingHub
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio

/-!
# The multiplicity of a branch, in the indexing the multiplicity of Stacks 0EE9 uses

Let `Y` be an algebraic space in Situation 0EDT (for instance a closed subspace of an ambient
space), let `V` be an étale scheme chart of `Y`, let `u` be a point of it and let `Bh` be a
henselization or a strict henselization of `𝒪_{V, u}` — for instance the henselian local ring
`𝒪^h_{Y, ξ}` of Stacks 0ENK at the image `ξ` of `u`, or the étale local ring at a geometric
point above `ξ`. A *branch* of `Y` at `ξ` is a minimal prime `q` of `Bh`. This file proves

  `m_{W, Y} = length_{(Bh)_q}((Bh)_q)`

for `W` the irreducible component of `|Y|` on which the branch lies, `m_{W, Y}` being
`AlgebraicGeometry.Space.closedSubspaceMultiplicity`, the multiplicity of Stacks 0EE9, part (1).

Two indexings of the components meet here, and that is the whole point of the file. The
multiplicity `m_{W, Y}` is indexed by an `AlgebraicGeometry.Space.IntegralClosedSubspace` of `Y`,
while the component carrying a branch is produced by
`AlgebraicGeometry.Space.componentOfBranch` as a *topological* member of
`irreducibleComponents |Y|`. The bijection between the two is Stacks 0ENF,
`AlgebraicGeometry.Space.bijective_integralClosedSubspaceSupport`; what is done below is to take
the component to the subspace through it and to check that the resulting subspace has the
branch's point for its generic point, which is what makes the two lengths lengths at one and the
same point of `|Y|`.

## Main definitions

* `AlgebraicGeometry.Space.integralClosedSubspaceOfComponent`: an irreducible component of `|X|`
  as an integral closed subspace of `X`, the direction (2) ⟶ (3) of Stacks 0ENF applied to a
  component.
* `AlgebraicGeometry.Space.irreducibleComponentMultiplicity`: the multiplicity `m_{W, Y}` of
  Stacks 0EE9 of an irreducible component of `|Y|`, indexed topologically.

## Main results

* `AlgebraicGeometry.Space.ambientGenericPoint_integralClosedSubspaceOfComponent`: the generic
  point of the subspace attached to a component is the generic point of the component.
* `AlgebraicGeometry.Space.spaceMultiplicity_eq_length_localizationAtPrime`:
  **the comparison.** The multiplicity `m_{W, Y}` of an integral closed subspace whose generic
  point is cut out by the prime below a branch is the length of the localization of `Bh` at that
  branch.
* `AlgebraicGeometry.Space.natCast_length_localizationAtPrime_eq_multiplicity_componentOfBranch`
  and
`AlgebraicGeometry.Space.natCast_length_localizationAtPrime_eq_multiplicity_componentOfFlatBranch`:
  **the hypothesis `hm` of `AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul`,
  discharged.** The length of `(Bh)_q` is the multiplicity of the component
  `AlgebraicGeometry.Space.componentOfBranch` attaches to the branch, in the two indexings of
  the branches that file's consumers use.
* `AlgebraicGeometry.Space.PrimeDivisor.natCast_length_localizationAtPrime_eq_multiplicity`:
  the same at `A = 𝒪^h_{Y, ξ}`, the henselian local ring of Stacks 0ENK at the generic point of a
  prime divisor, which is the ring the additivity is applied to.

## Implementation notes

### What has content and what is bookkeeping

The length comparison itself is
`AlgebraicGeometry.Space.length_localizationAtPrime_eq_geometricLength_of_isHenselization`
(`StacksFrontier.AlgebraicGeometry.Spaces.Chow.BranchMultiplicityOverComponent`), which is Stacks
02M1 at the flat local homomorphism `(𝒪_{V, u})_p ⟶ (Bh)_q` followed by Stacks 0EE1; it is not
restated. What is added is the identification of the two indexings, and with it the last
statement a consumer of
`AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul` owed: the module docstring of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentOrderAdditivity` names the missing statement
as the equality of `length_{A_q}(A_q)` with `closedSubspaceMultiplicity`, and that equality is
the main result below.

### The multiplicity is read on the space itself

`AlgebraicGeometry.Space.spaceMultiplicity` is the multiplicity of Stacks 0EE9, part (1), of an
integral closed subspace of an algebraic space `Y` in `Y` itself: the length of `𝒪_Y` at its
generic point. For a closed subspace `Y' ⊆ X` it is
`AlgebraicGeometry.Space.closedSubspaceMultiplicity` by definition
(`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_spaceMultiplicity`). The statements below
are phrased for an arbitrary algebraic space `Y` — its étale charts, its points, its
irreducible components and its integral closed subspaces — so that they apply to `X` itself as
well as to a closed subspace of it.

### The hypothesis that pins the component, and why it is not the content

The comparison takes the integral closed subspace `W` as a parameter together with `hW`, which
says that its generic point is the point of `|Y|` cut out by the prime below the branch. That is
an identification of a *point*, and it is what says which component the branch lies on; the
conclusion is an equality of two numbers, and `hW` says nothing about either. The same shape is
`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_componentMultiplicity`
(`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChartMultiplicity`), whose `hξ` plays
the same role. In the two `componentOfBranch` forms the subspace is *constructed* from the branch
and nothing is carried.

### References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 0DQ3](https://stacks.math.columbia.edu/tag/0DQ3)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### An irreducible component as an integral closed subspace -/

section OfComponent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)

/-- An irreducible component of `|X|` as an irreducible closed subset of `|X|`: a component is
irreducible by definition and closed by `isClosed_of_mem_irreducibleComponents`. -/
def irreducibleComponentCloseds (W : irreducibleComponents (points B S hS X)) :
    IrreducibleCloseds (points B S hS X) where
  carrier := (W : Set (points B S hS X))
  isIrreducible' := W.2.1
  isClosed' := isClosed_of_mem_irreducibleComponents _ W.2

/-- The carrier of `irreducibleComponentCloseds W` is the component `W` itself. -/
@[simp]
theorem coe_irreducibleComponentCloseds (W : irreducibleComponents (points B S hS X)) :
    (irreducibleComponentCloseds B S hS W : Set (points B S hS X)) =
      (W : Set (points B S hS X)) :=
  rfl

/-- **An irreducible component of `|X|` as an integral closed subspace of `X`**, by the direction
(2) ⟶ (3) of Stacks 0ENF: the reduced induced closed subspace of Stacks 03IQ on the component,
which is integral because the component is irreducible. -/
def integralClosedSubspaceOfComponent (W : irreducibleComponents (points B S hS X)) :
    IntegralClosedSubspace B S hS X :=
  integralClosedSubspaceOfPoints B S hS hX hXdec (irreducibleComponentCloseds B S hS W)

/-- The point set of the integral closed subspace attached to a component `W` is `W`. -/
@[simp]
theorem subspacePointSet_integralClosedSubspaceOfComponent
    (W : irreducibleComponents (points B S hS X)) :
    subspacePointSet B S hS X
        (integralClosedSubspaceOfComponent B S hS hX hXdec W).subspace =
      (W : Set (points B S hS X)) :=
  subspacePointSet_integralClosedSubspaceOfPoints B S hS hX hXdec _

/-- **The generic point of the subspace attached to a component is the generic point of the
component.** The two notions of generic point agree because the point set of the subspace is the
component and generic points of a Kolmogorov space are unique. -/
theorem ambientGenericPoint_integralClosedSubspaceOfComponent
    (W : irreducibleComponents (points B S hS X)) (η : points B S hS X)
    (hη : IsGenericPoint η (W : Set (points B S hS X))) :
    (integralClosedSubspaceOfComponent B S hS hX hXdec W).ambientGenericPoint B S hS = η :=
  (eq_pointsMap_genericPoint_of_isGenericPoint B S hS hX _ η
    (by rwa [subspacePointSet_integralClosedSubspaceOfComponent])).symm

end OfComponent

/-! ### The multiplicity of Stacks 0EE9 of a component, indexed topologically -/

section Multiplicity

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y)

/-- **Stacks 0EE9, part (1), for the space itself.** The multiplicity `m_{W, Y}` of an
integral closed subspace `W` of an algebraic space `Y` in `Y`: the length of `𝒪_Y` at the generic
point of `W`, at a geometric representative of that generic point.

This is `AlgebraicGeometry.Space.closedSubspaceMultiplicity` read on the algebraic space `Y`
itself rather than on a closed subspace of an ambient space: for a closed subspace `Y' ⊆ X` the
two agree by definition
(`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_spaceMultiplicity`).
The representative used is `AlgebraicGeometry.Space.canonicalGeometricPoint`; by Stacks 0EE1
(`AlgebraicGeometry.Space.spaceMultiplicity_eq_toNat_geometricLength`) the value does not depend
on this choice. -/
def spaceMultiplicity (W : IntegralClosedSubspace D.site D.base D.base_mem Y) : ℤ :=
  ((geometricLength D.site D.base D.base_mem ⟨Y, hY⟩
    (canonicalGeometricPoint D.site D.base D.base_mem Y
      (W.ambientGenericPoint D.site D.base D.base_mem)) (SheafOfModules.unit _)).toNat : ℤ)

/-- The multiplicity of Stacks 0EE9 of an integral closed subspace of a closed subspace
`Y' ⊆ X` is its multiplicity in the algebraic space `Y'`. -/
theorem closedSubspaceMultiplicity_eq_spaceMultiplicity (Y' : Subfunctor X)
    (hY' : IsClosedSubspace D.site D.base D.base_mem Y')
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y'.toFunctor) :
    closedSubspaceMultiplicity D Y' hY' W = spaceMultiplicity D Y'.toFunctor hY'.1 W :=
  rfl

/-- **Point-independence of the multiplicity, Stacks 0EE1.** The multiplicity `m_{W, Y}` is the
(cast of the) length of `𝒪_Y` at *any* geometric point lying over the generic point of `W`. -/
theorem spaceMultiplicity_eq_toNat_geometricLength
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (x : GeometricPoint D.site D.base D.base_mem Y)
    (hx : x.image = W.ambientGenericPoint D.site D.base D.base_mem) :
    spaceMultiplicity D Y hY W =
      ((geometricLength D.site D.base D.base_mem ⟨Y, hY⟩ x (SheafOfModules.unit _)).toNat : ℤ) := by
  unfold spaceMultiplicity
  rw [geometricLength_eq_of_image_eq D.site D.base D.base_mem hY
    (canonicalGeometricPoint D.site D.base D.base_mem Y
      (W.ambientGenericPoint D.site D.base D.base_mem)) x
    ((canonicalGeometricPoint_image D.site D.base D.base_mem Y
      (W.ambientGenericPoint D.site D.base D.base_mem)).trans hx.symm) (SheafOfModules.unit _)]

/-- **The multiplicity `m_{W, Y}` of Stacks 0EE9, part (1), of an irreducible component of
`|Y|`**, the component being given topologically rather than as an integral closed subspace:
the multiplicity of the subspace
`AlgebraicGeometry.Space.integralClosedSubspaceOfComponent` attached to it. -/
def irreducibleComponentMultiplicity
    (W : irreducibleComponents (points D.site D.base D.base_mem Y)) : ℤ :=
  spaceMultiplicity D Y hY
    (integralClosedSubspaceOfComponent D.site D.base D.base_mem hY hYdec W)

end Multiplicity

/-! ### The multiplicity of a branch -/

section Branch

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y)
    (V : SmallEtale D.site D.base D.base_mem Y) (u : chartScheme V)

/-- **The multiplicity of Stacks 0EE9 of a component is the length at a branch lying on it.**
Let `Y` be an algebraic space, `V` an étale scheme chart of `Y`, `u` a point of the chart,
`Bh` a henselization or a strict henselization of `𝒪_{V, u}` and `q` a minimal prime of `Bh`
lying over the prime `p` of `𝒪_{V, u}` — a branch of `Y` at the image of `u`. Let `W ⊆ Y` be an
integral closed subspace whose generic point is the point of `|Y|` cut out by `p`. Then

  `m_{W, Y} = length_{(Bh)_q}((Bh)_q)`.

Both sides are lengths of the structure sheaf at one geometric point above that point of `|Y|`:
the left-hand side by Stacks 0EE1
(`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_toNat_geometricLength`), the right-hand
side by
`AlgebraicGeometry.Space.length_localizationAtPrime_eq_geometricLength_of_isHenselization`. -/
theorem spaceMultiplicity_eq_length_localizationAtPrime
    {Bh : Type w} [CommRing Bh] [IsLocalRing Bh]
    [Algebra ↥((chartScheme V).presheaf.stalk u) Bh]
    (L : Type v) [Field L]
    [Algebra (IsLocalRing.ResidueField ↥((chartScheme V).presheaf.stalk u)) L]
    [IsLocalRing.IsHenselization ↥((chartScheme V).presheaf.stalk u) L Bh]
    (p : PrimeSpectrum ↥((chartScheme V).presheaf.stalk u)) (q : Ideal Bh) [q.IsPrime]
    [q.LiesOver p.asIdeal] (hq : q ∈ minimalPrimes Bh)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hW : W.ambientGenericPoint D.site D.base D.base_mem =
      chartSchemeToPoints D.site D.base D.base_mem Y V
        ((chartScheme V).fromSpecStalk u p)) :
    spaceMultiplicity D Y hY W =
      ((Module.length (Localization.AtPrime q) (Localization.AtPrime q)).toNat : ℤ) := by
  unfold spaceMultiplicity
  rw [← length_localizationAtPrime_eq_geometricLength_of_isHenselization D.site D.base D.base_mem
      hY V u L p q hq
      (canonicalGeometricPoint D.site D.base D.base_mem Y
        (W.ambientGenericPoint D.site D.base D.base_mem))
      (((canonicalGeometricPoint_image D.site D.base D.base_mem Y
        (W.ambientGenericPoint D.site D.base D.base_mem)).trans hW).symm)]

/-- **The length at a branch is the multiplicity of the component the branch lies on.** This is
the hypothesis `hm` of `AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul` with
`c = AlgebraicGeometry.Space.componentOfBranch` and the weight of a component its multiplicity
`m_{W, Y}` of Stacks 0EE9, in the indexing of the branches by the minimal primes of the chart
local ring.

The component is `AlgebraicGeometry.Space.componentOfBranch` of the prime below the branch, and
the subspace is the one attached to it by
`AlgebraicGeometry.Space.integralClosedSubspaceOfComponent`; its generic point is the image of
the point `(chartScheme V).fromSpecStalk u p`, by
`AlgebraicGeometry.Space.isGenericPoint_componentOfBranch`, which is the hypothesis `hW` of the
comparison above. -/
theorem natCast_length_localizationAtPrime_eq_multiplicity_componentOfBranch
    {Bh : Type w} [CommRing Bh] [IsLocalRing Bh]
    [Algebra ↥((chartScheme V).presheaf.stalk u) Bh]
    (L : Type v) [Field L]
    [Algebra (IsLocalRing.ResidueField ↥((chartScheme V).presheaf.stalk u)) L]
    [IsLocalRing.IsHenselization ↥((chartScheme V).presheaf.stalk u) L Bh]
    (p : {p : PrimeSpectrum ↥((chartScheme V).presheaf.stalk u) //
      p.asIdeal ∈ minimalPrimes ↥((chartScheme V).presheaf.stalk u)})
    (q : Ideal Bh) [q.IsPrime] [q.LiesOver p.1.asIdeal] (hq : q ∈ minimalPrimes Bh) :
    ((Module.length (Localization.AtPrime q) (Localization.AtPrime q)).toNat : ℤ) =
      irreducibleComponentMultiplicity D Y hY hYdec
        (componentOfBranch D.site D.base D.base_mem hY hYdec V u p).1 :=
  (spaceMultiplicity_eq_length_localizationAtPrime D Y hY V u L
    p.1 q hq _
    (ambientGenericPoint_integralClosedSubspaceOfComponent D.site D.base D.base_mem hY hYdec _ _
      (isGenericPoint_componentOfBranch D.site D.base D.base_mem hY hYdec V u p))).symm

/-- **The length at a branch of a flat algebra over the chart local ring is the multiplicity of
the component the branch lies on.** This is the hypothesis `hm` of
`AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul` in the indexing of the branches that
file's consumers use: by the minimal primes of the henselian local ring `𝒪^h_{Y, ξ}` of
Stacks 0ENK, or of the étale local ring at a geometric point above `ξ`, matched with the branches
on the chart by going down along the flat local homomorphism from `𝒪_{V, u}`.

It is the previous statement at the prime below the branch, which is what
`AlgebraicGeometry.Space.componentOfFlatBranch` is defined to be. -/
theorem natCast_length_localizationAtPrime_eq_multiplicity_componentOfFlatBranch
    {Bh : Type w} [CommRing Bh] [IsLocalRing Bh]
    [Algebra ↥((chartScheme V).presheaf.stalk u) Bh]
    [Module.Flat ↥((chartScheme V).presheaf.stalk u) Bh]
    (L : Type v) [Field L]
    [Algebra (IsLocalRing.ResidueField ↥((chartScheme V).presheaf.stalk u)) L]
    [IsLocalRing.IsHenselization ↥((chartScheme V).presheaf.stalk u) L Bh]
    (q : {q : PrimeSpectrum Bh // q.asIdeal ∈ minimalPrimes Bh}) :
    ((Module.length (Localization.AtPrime q.1.asIdeal)
        (Localization.AtPrime q.1.asIdeal)).toNat : ℤ) =
      irreducibleComponentMultiplicity D Y hY hYdec
        (componentOfFlatBranch D.site D.base D.base_mem hY hYdec V u Bh q).1 := by
  have : q.1.asIdeal.IsPrime := q.2.1.1
  have : q.1.asIdeal.LiesOver (PrimeSpectrum.comap
      (algebraMap ↥((chartScheme V).presheaf.stalk u) Bh) q.1).asIdeal := ⟨rfl⟩
  rw [componentOfFlatBranch]
  exact natCast_length_localizationAtPrime_eq_multiplicity_componentOfBranch
    D Y hY hYdec V u L _ q.1.asIdeal q.2

end Branch

/-! ### The multiplicity of a branch of the henselian local ring at a prime divisor -/

section GenericHenselian

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y)
    (Z : PrimeDivisor D.site D.base D.base_mem Y)

/-- The local ring of the generic chart of a prime divisor, spelled through the chart's object
of the small étale site. This is `AlgebraicGeometry.Space.PrimeDivisor.genericStalkRing`, but
written as the stalk of `chartScheme` at a point of it, which is the spelling the branch
machinery of `StacksFrontier.AlgebraicGeometry.Spaces.BranchesOverComponents` takes; instance
search does not pass between the two, because `chartScheme` and
`AlgebraicGeometry.Space.PrimeDivisor.genericEtaleChart` are not reducible. -/
abbrev PrimeDivisor.genericEtaleChartStalk : CommRingCat.{u} :=
  (chartScheme (Z.genericEtaleChart D.site D.base D.base_mem hY hYdec)).presheaf.stalk
    (Z.genericChart D.site D.base D.base_mem hY hYdec).point

/-- The local ring of the generic chart is a local ring, at the chart spelling. -/
abbrev PrimeDivisor.isLocalRing_genericEtaleChartStalk :
    IsLocalRing ↥(Z.genericEtaleChartStalk D Y hY hYdec) :=
  inferInstanceAs (IsLocalRing ↥(Z.genericStalkRing D.site D.base D.base_mem hY hYdec))

/-- `𝒪^h_{Y, ξ}` is an algebra over the local ring of the generic chart, at the chart
spelling. -/
abbrev PrimeDivisor.genericEtaleChartStalkAlgebra :
    Algebra ↥(Z.genericEtaleChartStalk D Y hY hYdec)
      ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) :=
  Z.genericStalkAlgebra D.site D.base D.base_mem hY hYdec

/-- `𝒪^h_{Y, ξ}` is a henselization of the local ring of the generic chart, at the chart
spelling. -/
abbrev PrimeDivisor.isHenselization_genericEtaleChartStalk :
    letI := Z.isLocalRing_genericEtaleChartStalk D Y hY hYdec
    letI := henselianLocalRing_isLocalRing D.site D.base D.base_mem Y hY
      (Z.genericPoint D.site D.base D.base_mem Y) hYdec
    letI := Z.genericEtaleChartStalkAlgebra D Y hY hYdec
    IsLocalRing.IsHenselization ↥(Z.genericEtaleChartStalk D Y hY hYdec)
      (IsLocalRing.ResidueField ↥(Z.genericEtaleChartStalk D Y hY hYdec))
      ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) :=
  Z.isHenselization_genericHenselianLocalRing D.site D.base D.base_mem hY hYdec

/-- `𝒪^h_{Y, ξ}` is flat over the local ring of the generic chart, at the chart spelling: a
henselization is flat. -/
abbrev PrimeDivisor.flat_genericEtaleChartStalk :
    letI := Z.isLocalRing_genericEtaleChartStalk D Y hY hYdec
    letI := Z.genericEtaleChartStalkAlgebra D Y hY hYdec
    Module.Flat ↥(Z.genericEtaleChartStalk D Y hY hYdec)
      ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) :=
  letI := Z.isLocalRing_genericEtaleChartStalk D Y hY hYdec
  letI := henselianLocalRing_isLocalRing D.site D.base D.base_mem Y hY
    (Z.genericPoint D.site D.base D.base_mem Y) hYdec
  letI := Z.genericEtaleChartStalkAlgebra D Y hY hYdec
  letI := Z.isHenselization_genericEtaleChartStalk D Y hY hYdec
  IsLocalRing.IsHenselization.flat
    (L := IsLocalRing.ResidueField ↥(Z.genericEtaleChartStalk D Y hY hYdec))

/-- **The hypothesis `hm` of `AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul` at the
henselian local ring of a prime divisor.** For `A = 𝒪^h_{Y, ξ}` the henselian local ring of
Stacks 0ENK at the generic point `ξ` of a prime divisor `Z` of an algebraic space `Y`, and `q`
a branch of `Y` at `ξ` — a minimal prime of `A` —

  `length_{A_q}(A_q) = m_{W, Y}`,

`W` being the irreducible component of `|Y|` on which the branch lies and `m_{W, Y}` its
multiplicity of Stacks 0EE9. With `c` the branch-to-component map
`AlgebraicGeometry.Space.componentOfFlatBranch` at the generic chart and `m` the weight
`AlgebraicGeometry.Space.irreducibleComponentMultiplicity`, this *is* the hypothesis `hm` of the
additivity, so a consumer of that statement at `A = 𝒪^h_{Y, ξ}` no longer owes it.

`𝒪^h_{Y, ξ}` is a henselization of the local ring of the chosen generic chart
(`AlgebraicGeometry.Space.PrimeDivisor.isHenselization_genericHenselianLocalRing`), hence flat
over it, so
`AlgebraicGeometry.Space.natCast_length_localizationAtPrime_eq_multiplicity_componentOfFlatBranch`
applies. The four instances are restated at the chart spelling because instance search does not
pass between `AlgebraicGeometry.Space.PrimeDivisor.genericStalkRing` and the stalk of
`chartScheme` at a point, the intervening definitions not being reducible. -/
theorem PrimeDivisor.natCast_length_localizationAtPrime_eq_multiplicity
    (q : {q : PrimeSpectrum ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) //
      q.asIdeal ∈
        minimalPrimes ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)}) :
    letI := Z.isLocalRing_genericEtaleChartStalk D Y hY hYdec
    letI := Z.genericEtaleChartStalkAlgebra D Y hY hYdec
    letI := Z.flat_genericEtaleChartStalk D Y hY hYdec
    ((Module.length (Localization.AtPrime q.1.asIdeal)
        (Localization.AtPrime q.1.asIdeal)).toNat : ℤ) =
      irreducibleComponentMultiplicity D Y hY hYdec
        (componentOfFlatBranch D.site D.base D.base_mem hY hYdec
          (Z.genericEtaleChart D.site D.base D.base_mem hY hYdec)
          (Z.genericChart D.site D.base D.base_mem hY hYdec).point
          ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) q).1 :=
  let := Z.isLocalRing_genericEtaleChartStalk D Y hY hYdec
  let := henselianLocalRing_isLocalRing D.site D.base D.base_mem Y hY
    (Z.genericPoint D.site D.base D.base_mem Y) hYdec
  let := Z.genericEtaleChartStalkAlgebra D Y hY hYdec
  let := Z.isHenselization_genericEtaleChartStalk D Y hY hYdec
  let := Z.flat_genericEtaleChartStalk D Y hY hYdec
  natCast_length_localizationAtPrime_eq_multiplicity_componentOfFlatBranch
    D Y hY hYdec _ _
    (IsLocalRing.ResidueField ↥(Z.genericEtaleChartStalk D Y hY hYdec)) q

end GenericHenselian

end AlgebraicGeometry.Space

end
