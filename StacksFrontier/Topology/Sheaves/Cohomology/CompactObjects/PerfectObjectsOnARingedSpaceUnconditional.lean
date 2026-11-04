module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactObjects.PerfectDualReduction
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactObjects.PerfectObjectsOnARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FiniteTorDimensionOfAPerfectObject
import StacksCore.Tactic.StacksAttribute

/-!
# Compactness of a perfect object on a ringed space

Let `X` be a ringed space whose underlying topological space is quasi-compact, has a basis of
quasi-compact opens, and in which the intersection of two quasi-compact opens is quasi-compact —
hypotheses (1), (2) and (3) of **Stacks 09J7**, which are Mathlib's `CompactSpace`,
`PrespectralSpace` and `QuasiSeparatedSpace`. Let `K` be a perfect object of `D(O_X)`. Then

* (a) `Hom(K, ⨁ Mᵢ) = ⨁ Hom(K, Mᵢ)` for every family `Mᵢ` whose direct sum is bounded below;
* (b) if `X` has finite cohomological dimension, `K` is a compact object of `D(O_X)`.

## Main results

* `Stacks.Cohomology.RingedSpaceCompact.isCompactObject_of_isPerfect_of_finiteCohomDim`:
  **Stacks 09J7 (b)**.
* `Stacks.Cohomology.RingedSpaceCompact.hom_coproduct_bijective_of_isPerfect_of_compactSpace`:
  **Stacks 09J7 (a)**.

## The argument

Both clauses follow the source. By Stacks 08DQ morphisms out of `K` are morphisms out of
`j_{X!}O_X` after applying `K^∨ ⊗^L_{O_X} -`, a functor commuting with direct sums
(`AlgebraicGeometry.RingedSite.derivedDualHomEquivOfIsoStructureSheaf` and
`AlgebraicGeometry.RingedSite.preservesColimitsOfShape_derivedTensorFlip`, assembled in
`StacksFrontier.Topology.Sheaves.Cohomology.CompactObjects.PerfectDualReduction`), so it suffices
that `RΓ(X, -)` commutes with the relevant direct sums. The three topological conditions make
`F ↦ Hᵖ(X, F)` commute with arbitrary direct sums (Stacks 01FF); with the dimension bound this
is what Stacks 094D consumes for (b).

For (a) the sum `K^∨ ⊗^L_{O_X} ⨁ M_i` has to be bounded below when `⨁ M_i` is, which is the
finite Tor amplitude of a perfect complex (Stacks 08G8): the dual of a perfect object is perfect
(Stacks 08JJ, `AlgebraicGeometry.RingedSite.isPerfect_derivedDual`), perfectness gives Tor
amplitude locally (`Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect`),
and quasi-compactness turns the local intervals into one interval
(`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`). The ringed-space and
ringed-site spellings of Tor amplitude and of perfectness agree by
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_derivedTensorProduct` and
`Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite`.

`…hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension` below is the same bijection for
a perfect object whose dual is given to have finite Tor dimension, the form in which the site
statement is applied.

## Implementation notes

The additivity of `⊗_{O_X}` in each variable and the existence of the total tensor complexes are
`Stacks.SheafOfModules.Tensor.sheafTensor_additive`,
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive` and
`Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor` at the site of opens of `X`; they are
installed as local instances because the library instances are stated with the sections universe
tied to the site universes as `max u v`, which instance synthesis cannot solve against the
diagonal `u` used here.

## References

* [Stacks Project, Lemma 36.6.2 (Tag 09J7)](https://stacks.math.columbia.edu/tag/09J7)
* [Stacks Project, Lemma 20.50.9 (Tag 09JC)](https://stacks.math.columbia.edu/tag/09JC)
* [Stacks Project, Tag 094D](https://stacks.math.columbia.edu/tag/094D)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.Cohomology.RingedSpaceCompact

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- The top open set is a final object of the site of opens: there is exactly one morphism into
it from every open, the opens forming a poset with a greatest element. -/
def isTerminal_top : IsTerminal (⊤ : (RingedSpace.ringedSite X).C) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)

/-- `⊗_{O_X}` is additive in its first variable, pinned by hand: the library instance ties the
sections universe to the site universes as `max u v`, which instance synthesis cannot solve
against the diagonal `u` of this cluster. -/
local instance opensSheafTensorAdditive :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (RingedSpace.ringedSite X).O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive
    (J := Opens.grothendieckTopology X.carrier) X.sheaf

/-- `ℱ ⊗_{O_X} -` is additive, pinned for the same reason. -/
local instance opensSheafTensorObjAdditive
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (RingedSpace.ringedSite X).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
    (J := Opens.grothendieckTopology X.carrier) X.sheaf M

/-- The total complexes of the tensor double complexes exist, pinned for the same reason. -/
local instance opensHasMapBifunctor
    (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (RingedSpace.ringedSite X).O))
      (ComplexShape.up ℤ)) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (RingedSpace.ringedSite X).O)
      (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor
    (J := Opens.grothendieckTopology X.carrier) X.sheaf K₁ K₂

/-- **Stacks 09J7 (b).** Let `X` be a ringed space whose underlying topological
space is quasi-compact, has a basis of quasi-compact opens, and has quasi-compact intersections
of quasi-compact opens — hypotheses (1), (2) and (3) of the tag. Let `K` be a perfect object of
`D(O_X)` and suppose `X` has finite cohomological dimension, that is `Hᵖ(X, F) = 0` for every
`O_X`-module `F` and every `p` beyond a fixed bound `d`. Then `K` is a compact object of
`D(O_X)`.

The reduction the source performs first — by Stacks 08DQ morphisms out of
`K` are morphisms out of `j_{X!}O_X` after applying `K^∨ ⊗^L_{O_X} -`, a functor commuting with
direct sums — is
`AlgebraicGeometry.RingedSite.derivedDualHomEquivOfIsoStructureSheaf` together with
`AlgebraicGeometry.RingedSite.preservesColimitsOfShape_derivedTensorFlip`, and it is applied at
the final object `⊤` of the site of opens. The three topological conditions enter through
Stacks 01FF: they make the cohomology functors `F ↦ Hᵖ(X, F)` commute
with arbitrary direct sums, which with the dimension bound is what Stacks 094D consumes. -/
@[stacks 09J7 "(b): on a ringed space satisfying (1), (2) and (3) and of finite cohomological \
dimension, a perfect object is a compact object of D(O_X)"]
theorem isCompactObject_of_isPerfect_of_finiteCohomDim [CompactSpace X.carrier]
    (hBasis : PrespectralSpace X.carrier)
    (hInter : QuasiSeparatedSpace X.carrier)
    (K : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)))
    (hK : (RingedSpace.ringedSite X).IsPerfect K)
    (hcd : ∃ d : ℤ, ∀ (p : ℕ) (F : _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)),
      d < (p : ℤ) → IsZero (Hgroup
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O) ⊤ p F)) :
    IsCompactObject.{u} K := by
  have hvanish : ∃ d : ℤ, ∀ (p : ℕ)
      (F : _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)), d < (p : ℤ) →
      IsZero (((_root_.SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)
        (op (⊤ : (RingedSpace.ringedSite X).C))).rightDerived p).obj F) := by
    obtain ⟨d, hd⟩ := hcd
    exact ⟨d, fun p F hp =>
      (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O) ⊤ p F).2 (hd p F hp)⟩
  have hsums : ∀ (p : ℕ) (I : Type u), PreservesColimitsOfShape (Discrete I)
      ((_root_.SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)
        (op (⊤ : (RingedSpace.ringedSite X).C))).rightDerived p) := fun p I =>
    preservesColimitsOfShape_discrete_rightDerived_evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O) hBasis hInter ⊤
      (by simpa using CompactSpace.isCompact_univ) p I
  exact RingedSite.isCompactObject_of_isPerfect_of_isTerminal (RingedSpace.ringedSite X)
    ⊤ (isTerminal_top X) K hK hvanish hsums


/-- **Compactness relative to bounded below objects, for a perfect object with dual of finite
Tor dimension.** On a ringed space satisfying (1), (2) and (3) of Stacks 09J7, let `K` be a
perfect object of `D(O_X)` whose dual `K^∨` has finite Tor dimension, and let `M : I → D(O_X)`
be a family whose coproduct is bounded below. Then `Hom(K, ⨁ Mᵢ) = ⨁ Hom(K, Mᵢ)`. This is
`AlgebraicGeometry.RingedSite.hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension` at
the site of opens of `X`. -/
theorem hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension [CompactSpace X.carrier]
    (hBasis : PrespectralSpace X.carrier)
    (hInter : QuasiSeparatedSpace X.carrier)
    (K : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)))
    (hK : (RingedSpace.ringedSite X).IsPerfect K)
    (hdual : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (RingedSpace.ringedSite X))
      (RingedSite.derivedDual (RingedSpace.ringedSite X) K))
    {I : Type u} [DecidableEq I]
    (M : I → DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O))) [HasCoproduct M]
    (hplus : DerivedCategoryB.IsBoundedBelow (∐ M)) :
    Function.Bijective
      (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι M j)) := by
  have hcpt : IsCompact (((⊤ : Opens X.carrier) : Set X.carrier)) := by
    simpa using CompactSpace.isCompact_univ (X := (X.carrier : Type u))
  exact RingedSite.hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension
    (RingedSpace.ringedSite X) _
    (Stacks.Cohomology.Basis.compactOpens (X.carrier : Type u))
    (fun U => compactHypercovers U)
    (fun _ E hE => sieve₀_mem_of_mem_compactHypercovers E hE)
    (fun _ E hE => hasIntersectionsIn_of_mem_compactHypercovers hInter E hE)
    (fun U hU S hS => exists_mem_compactHypercovers_sieve₀_le hBasis hInter U hU S hS)
    ⊤ hcpt (isTerminal_top X) K hK hdual M hplus

/-! ### Stacks 09J7 (a) -/

/-- **Stacks 09J7 (a).** Let `X` be a ringed space whose underlying topological
space is quasi-compact, has a basis of quasi-compact opens, and has quasi-compact intersections
of quasi-compact opens — hypotheses (1), (2) and (3) of the tag. Let `K` be a perfect object of
`D(O_X)` and let `M : I → D(O_X)` be a family whose coproduct is bounded below. Then
`Hom(K, ⨁ Mᵢ) = ⨁ Hom(K, Mᵢ)`: the canonical map from the direct sum of the `Hom(K, Mᵢ)` is
bijective.

The proof applies `hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension`; the finite
Tor dimension of `K^∨` is the global form of Stacks 08G8,
`Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_ringedSite_isPerfect`, applied to the
dual `K^∨`, which is perfect by Stacks 08JJ
(`AlgebraicGeometry.RingedSite.isPerfect_derivedDual`): perfectness gives the Tor amplitude of
`K^∨` only locally, quasi-compactness makes the local intervals one interval, and the bridge
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_derivedTensorProduct` reads that interval
against the derived tensor product datum the reduction measures Tor dimension by.

The index type lies in the universe of the space, as for clause (b). -/
@[stacks 09J7 "(a): on a ringed space satisfying (1), (2) and (3), a perfect object K satisfies \
Hom(K, ⨁ M_i) = ⨁ Hom(K, M_i) whenever ⨁ M_i is bounded below"]
theorem hom_coproduct_bijective_of_isPerfect_of_compactSpace [CompactSpace X.carrier]
    (hBasis : PrespectralSpace X.carrier)
    (hInter : QuasiSeparatedSpace X.carrier)
    (K : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)))
    (hK : (RingedSpace.ringedSite X).IsPerfect K)
    {I : Type u} [DecidableEq I]
    (M : I → DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O))) [HasCoproduct M]
    (hplus : DerivedCategoryB.IsBoundedBelow (∐ M)) :
    Function.Bijective
      (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι M j)) :=
  hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension X hBasis hInter K hK
    (Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_ringedSite_isPerfect X _ _
      (AlgebraicGeometry.RingedSite.isPerfect_derivedDual (RingedSpace.ringedSite X) K hK))
    M hplus

end Stacks.Cohomology.RingedSpaceCompact


end
