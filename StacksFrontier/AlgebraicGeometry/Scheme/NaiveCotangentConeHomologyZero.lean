module

public import StacksFrontier.Algebra.Homology.MappingConeTwoTermHomology
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeDifferential
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkTowerCokernel
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkTowerHomotopy
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
public import StacksFrontier.Topology.Sheaves.Modules.StalkCokernelQuotient

/-!
# Stacks 0E1Y: the canonical map into the shifted cone is an isomorphism on `H⁰`

Let `A ⟶ B ⟶ C` be morphisms of sheaves of commutative rings on a topological space, with
canonical maps `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}` and `g : NL_{C/A} ⟶ NL_{C/B}`, and let
`c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]` be the canonical map of Stacks 0E1Y, the factorisation of
Stacks 08RI (2) of `c₁` attached to the null homotopy of `c₁ ≫ g`.  This file proves that **`c`
induces an isomorphism on `H⁰`**.

That is the comparison the two remaining assertions of the six-term exact sequence of
Stacks 0E1Y rest on — its exactness at `H^{-1}(NL_{C/B})` and at `H⁰(NL_{B/A} ⊗_B C)`, together
with the connecting morphism, all drawn in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSixTerm`.  The companion in
degree `-1`, that `H^{-1}(c)` is surjective, is
`Stacks.SheafOfModules.epi_homologyMap_spaceNaiveCotangentConeMap_negOne`.

## The argument

Three reductions, each proved elsewhere, meet here.

* `CochainComplex.mappingCone.isIso_homologyMap_zero_iff` turns `IsIso (H⁰(c))` into `IsIso` of
  a map of cokernels `coker (d^{-1}) ⟶ coker (g^{-1})` in which no cone, no shift and no
  connecting morphism occurs.  The morphism being descended is the degree `-1` component of the
  null homotopy, with no sign, by
  `CochainComplex.mappingCone.shiftedSndZero_factorThroughShiftedMappingCone`.  Its hypotheses
  are the vanishing of three terms of the three complexes and the invertibility of `g` in degree
  `0`, which is `Stacks.SheafOfModules.isIso_spaceRelativeNaiveCotangentComplexMap_zero`.
* `AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_comp_π_iff_forall_bijective_liftQ` turns
  that into bijectivity, at every point `z`, of the induced map of quotient modules over the
  stalk ring
  `(NL_{B/A} ⊗_B C)^0_z ⧸ im (d^{-1}_z) ⟶ (NL_{C/B})^{-1}_z ⧸ im (g^{-1}_z)`.
* Both quotients and the map between them are read through Stacks 0D09, which identifies the
  stalks with the terms of the naive cotangent complexes of the canonical presentations of the
  stalk rings: `Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquivZero` and
  `stalkBaseChangeAddEquiv_d` on the source,
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` on the target,
  `Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_baseChangeRelativeNullHomotopy` and
  `Stacks.NaiveCotangentStalkJacobiZariski.stalkLegNegOneLinear_spaceRelativeMap` on the two
  maps.  What is left is exactly the two elementwise halves of
  `NaiveCotangent.bijective_towerCokernelMap` recorded in
  `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkTowerCokernel`.

## Main results

* `Stacks.SheafOfModules.shiftedSndZero_spaceNaiveCotangentConeMap`: the degree `0` component of
  `c` read against the second projection of the cone is the single component of the null
  homotopy.
* `Stacks.SheafOfModules.stalkLegNegOneLinear_shiftedSndZero` and
  `cotangentMap_stalkLegNegOneLinear_spaceRelativeMap`: that component and `g` in degree `-1`,
  read at a stalk through Stacks 0D09.
* `Stacks.SheafOfModules.mem_range_cotangentMap_stalkTowerHomRel`,
  `mem_range_stalkMap_d_of_mem_range_baseChange` and
  `exists_shiftedSndZero_add_stalkMap_relative`: the transport of the two halves of
  `NaiveCotangent.bijective_towerCokernelMap` to germs.
* `Stacks.SheafOfModules.injective_liftQ_stalk_shiftedSndZero` and
  `surjective_liftQ_stalk_shiftedSndZero`: the induced map of quotients is bijective at every
  point.
* `Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`: **`H⁰(c)` is an
  isomorphism.**

## Implementation notes

The stalkwise bijectivity is split into an injectivity and a surjectivity statement, and each of
those again into an element-level lemma stated over the canonical presentations of the stalk
rings, because none of the chains fits inside the default heartbeat budget: the objects are
stalks of sheafifications and each step costs a comparison of two of them.  For the same reason
a class of the *target* quotient is lifted to a germ with `Quotient.ind` rather than
`Submodule.mkQ_surjective`, which re-synthesises that quotient's module structure over the stalk
ring and exhausts the budget on its own.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the canonical map and
  the six-term sequence.
* [Stacks Project, Tag 08RI](https://stacks.math.columbia.edu/tag/08RI), part (2), the
  factorisation through the shifted cone.
* [Stacks Project, Tag 07VC](https://stacks.math.columbia.edu/tag/07VC), the explicit null
  homotopy of a tower of rings.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex.
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG), isomorphy is stalkwise.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (stalkFunctor stalkMap stalkObj)
open Stacks.NaiveCotangentAffineStalkLegs
open Stacks.NaiveCotangentStalkBaseChange
open Stacks.NaiveCotangentStalkJacobiZariski
open Stacks.NaiveCotangentTowerStalk
open Stacks.RelativeDifferentialStalk (algebraStalk)
open Stacks.Sites.Conormal (stalkIsScalarTowerSquareTarget stalkIsScalarTowerSquareBase)
open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.SheafOfModules

attribute [local instance 1]
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C)

/-- The degree `0` component of the canonical map `c` of Stacks 0E1Y, read against the second
projection of the cone, is the single component of the null homotopy of `c₁ ≫ g`. -/
theorem shiftedSndZero_spaceNaiveCotangentConeMap :
    CochainComplex.mappingCone.shiftedSndZero
        (spaceRelativeNaiveCotangentComplexMap A B C a b)
        (spaceNaiveCotangentConeMap A B C a b) =
      (baseChangeRelativeNullHomotopy.{u, u, u} (Opens.grothendieckTopology T) A B C a b).hom
        0 (-1) := by
  have h := CochainComplex.mappingCone.shiftedSndZero_factorThroughShiftedMappingCone
    (relativeNaiveCotangentComplexMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b)
    (baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b)
    (baseChangeRelativeNullHomotopy.{u, u, u} (Opens.grothendieckTopology T) A B C a b)
  exact h

/-- The homotopy component of the canonical map `c` of Stacks 0E1Y kills the boundaries of
`NL_{B/A} ⊗_B C` modulo the image of `g` in degree `-1`, so it descends to a morphism of
cokernels. -/
theorem d_comp_shiftedSndZero_comp_π_space :
    (spaceBaseChangeNaiveCotangentComplex A B C a b).d (-1) 0 ≫
        CochainComplex.mappingCone.shiftedSndZero
            (spaceRelativeNaiveCotangentComplexMap A B C a b)
            (spaceNaiveCotangentConeMap A B C a b) ≫
          cokernel.π ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1)) = 0 :=
  CochainComplex.mappingCone.d_comp_shiftedSndZero_comp_π
    (relativeNaiveCotangentComplexMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b)
    (spaceNaiveCotangentConeMap A B C a b)
    (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) B C b (-2)
      (by decide) (by decide))

/-- **The stalk of the homotopy component of the canonical map of Stacks 0E1Y is the base change
of the null homotopy of Stacks 07VC.**  This is
`Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_baseChangeRelativeNullHomotopy` with
the homotopy component recognised as the degree `0` component of `c` read against the second
projection of the cone. -/
theorem stalkLegNegOneLinear_shiftedSndZero (z : T)
    (ξ : ToType (stalkObj (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).X 0))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    letI := algebraStalk (a ≫ b).hom z
    haveI := stalkIsScalarTowerSquareBase A B C b (a ≫ b) a z rfl
    letI := moduleRingStalkCotangentSpace A B a z
    stalkLegNegOneLinear B C b z
        ((stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
          (CochainComplex.mappingCone.shiftedSndZero
            (spaceRelativeNaiveCotangentComplexMap A B C a b)
            (spaceNaiveCotangentConeMap A B C a b))).hom ξ) =
      NaiveCotangent.towerNullHomotopyBaseChange (ToType (TopCat.Presheaf.stalk A.obj z))
          (ToType (TopCat.Presheaf.stalk B.obj z)) (ToType (TopCat.Presheaf.stalk C.obj z))
        (stalkBaseChangeAddEquivZero A B C a b z ξ) := by
  let := algebraStalk a.hom z
  let := algebraStalk b.hom z
  let := algebraStalk (a ≫ b).hom z
  have _ := stalkIsScalarTowerSquareBase A B C b (a ≫ b) a z rfl
  let := moduleRingStalkCotangentSpace A B a z
  rw [shiftedSndZero_spaceNaiveCotangentConeMap A B C a b]
  exact stalkLegNegOneLinear_baseChangeRelativeNullHomotopy A B C a b z ξ

/-- **The stalk of the canonical map `g` of Stacks 0E1Y in degree `-1` is
`Algebra.Extension.Cotangent.map` of the morphism of canonical presentations of the stalks.**
This is `Stacks.NaiveCotangentStalkJacobiZariski.stalkLegNegOneLinear_spaceRelativeMap` with the
degree `-1` component of `NaiveCotangent.nlExtensionOverMap` written in the native spelling. -/
theorem cotangentMap_stalkLegNegOneLinear_spaceRelativeMap (z : T)
    (ω : ToType (stalkObj (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b)).X (-1)))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk b.hom z
    letI := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
    stalkLegNegOneLinear B C b z
        ((stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
          ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1))).hom ω) =
      Algebra.Extension.Cotangent.map (stalkTowerHomRel A B B C a b a b z rfl)
        (stalkLegNegOneLinear A C (a ≫ b) z ω) := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  exact stalkLegNegOneLinear_spaceRelativeMap A B C a b z ω

/-- A germ of `NL_{B/A} ⊗_B C` in degree `0` whose image under the homotopy component of the
canonical map of Stacks 0E1Y lies in the image of `g` in degree `-1` has its value under the
homotopy of Stacks 07VC in the image of `Algebra.Extension.Cotangent.map` of the morphism of
canonical presentations of the stalks. -/
theorem mem_range_cotangentMap_stalkTowerHomRel (z : T)
    (ξ : ToType (stalkObj (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).X 0)))
    (hξ : (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
        (CochainComplex.mappingCone.shiftedSndZero
          (spaceRelativeNaiveCotangentComplexMap A B C a b)
          (spaceNaiveCotangentConeMap A B C a b))).hom ξ ∈
      LinearMap.range (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
        ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1))).hom) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk b.hom z
    letI := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
    NaiveCotangent.towerNullHomotopyBaseChange (ToType (TopCat.Presheaf.stalk A.obj z))
          (ToType (TopCat.Presheaf.stalk B.obj z)) (ToType (TopCat.Presheaf.stalk C.obj z))
        (stalkBaseChangeAddEquivZero A B C a b z ξ) ∈
      LinearMap.range (Algebra.Extension.Cotangent.map
        (stalkTowerHomRel A B B C a b a b z rfl)) := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  obtain ⟨ω, hω⟩ := hξ
  refine ⟨stalkLegNegOneLinear A C (a ≫ b) z ω, ?_⟩
  refine Eq.trans
    (cotangentMap_stalkLegNegOneLinear_spaceRelativeMap A B C a b z ω).symm ?_
  refine Eq.trans (congrArg (fun y => stalkLegNegOneLinear B C b z y) hω) ?_
  exact stalkLegNegOneLinear_shiftedSndZero A B C a b z ξ

/-- A germ of `NL_{B/A} ⊗_B C` in degree `0` whose image under the identification of
Stacks 0D09 is a boundary of the base changed naive cotangent complex of the canonical
presentations is itself a boundary. -/
theorem mem_range_stalkMap_d_of_mem_range_baseChange (z : T)
    (ξ : ToType (stalkObj (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).X 0)))
    (hξ : letI := algebraStalk a.hom z
      letI := algebraStalk b.hom z
      stalkBaseChangeAddEquivZero A B C a b z ξ ∈
        LinearMap.range ((Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
          (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.cotangentComplex.baseChange
            (ToType (TopCat.Presheaf.stalk C.obj z)))) :
    ξ ∈ LinearMap.range (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).d (-1) 0)).hom := by
  let := algebraStalk a.hom z
  let := algebraStalk b.hom z
  obtain ⟨v, hv⟩ := hξ
  refine ⟨(stalkBaseChangeAddEquivNegOne A B C a b z).symm v, ?_⟩
  refine (stalkBaseChangeAddEquivZero A B C a b z).injective ?_
  refine Eq.trans (stalkBaseChangeAddEquiv_d A B C a b z _) ?_
  refine Eq.trans (congrArg (fun y => (NaiveCotangent.nlExtensionBaseChange
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension
      (ToType (TopCat.Presheaf.stalk C.obj z))).d y)
    ((stalkBaseChangeAddEquivNegOne A B C a b z).apply_symm_apply v)) ?_
  exact hv

/-- **A germ of `NL_{C/B}` in degree `-1` is the sum of a value of the homotopy component of the
canonical map of Stacks 0E1Y and an element of the image of `g` in degree `-1`.**  This is the
surjectivity half of `NaiveCotangent.bijective_towerCokernelMap`, read through the
identifications of Stacks 0D09. -/
theorem exists_shiftedSndZero_add_stalkMap_relative (z : T)
    (m : ToType (stalkObj (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).X (-1)))) :
    ∃ (ξ : ToType (stalkObj (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
        ((spaceBaseChangeNaiveCotangentComplex A B C a b).X 0)))
      (ω : ToType (stalkObj (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C
          (a ≫ b)).X (-1)))),
      (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
          (CochainComplex.mappingCone.shiftedSndZero
            (spaceRelativeNaiveCotangentComplexMap A B C a b)
            (spaceNaiveCotangentConeMap A B C a b))).hom ξ +
        (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
          ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1))).hom ω = m := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  obtain ⟨n, w, hnw⟩ := exists_towerNullHomotopy_add_stalk A B C a b z
    (stalkLegNegOneLinear B C b z m)
  refine ⟨(stalkBaseChangeAddEquivZero A B C a b z).symm n,
    (stalkLegNegOneLinear A C (a ≫ b) z).symm w, ?_⟩
  have h₁ : stalkLegNegOneLinear B C b z
      ((stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
        (CochainComplex.mappingCone.shiftedSndZero
          (spaceRelativeNaiveCotangentComplexMap A B C a b)
          (spaceNaiveCotangentConeMap A B C a b))).hom
        ((stalkBaseChangeAddEquivZero A B C a b z).symm n)) =
      NaiveCotangent.towerNullHomotopyBaseChange (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z)) (ToType (TopCat.Presheaf.stalk C.obj z)) n :=
    (stalkLegNegOneLinear_shiftedSndZero A B C a b z _).trans
      (congrArg (fun y => NaiveCotangent.towerNullHomotopyBaseChange
          (ToType (TopCat.Presheaf.stalk A.obj z)) (ToType (TopCat.Presheaf.stalk B.obj z))
          (ToType (TopCat.Presheaf.stalk C.obj z)) y)
        ((stalkBaseChangeAddEquivZero A B C a b z).apply_symm_apply n))
  have h₂ : stalkLegNegOneLinear B C b z
      ((stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
        ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1))).hom
        ((stalkLegNegOneLinear A C (a ≫ b) z).symm w)) =
      Algebra.Extension.Cotangent.map (stalkTowerHomRel A B B C a b a b z rfl) w :=
    (cotangentMap_stalkLegNegOneLinear_spaceRelativeMap A B C a b z _).trans
      (congrArg (fun y => Algebra.Extension.Cotangent.map
          (stalkTowerHomRel A B B C a b a b z rfl) y)
        ((stalkLegNegOneLinear A C (a ≫ b) z).apply_symm_apply w))
  refine (stalkLegNegOneLinear B C b z).injective ?_
  refine Eq.trans (map_add (stalkLegNegOneLinear B C b z) _ _) ?_
  rw [h₁, h₂]
  exact hnw

/-- **The map of cokernels induced by the homotopy component of the canonical map of
Stacks 0E1Y is injective at every stalk.** -/
theorem injective_liftQ_stalk_shiftedSndZero (z : T) :
    Function.Injective ((LinearMap.range
        (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
          ((spaceBaseChangeNaiveCotangentComplex A B C a b).d (-1) 0)).hom).liftQ
      ((LinearMap.range (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
            ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1))).hom).mkQ.comp
        (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
          (CochainComplex.mappingCone.shiftedSndZero
            (spaceRelativeNaiveCotangentComplexMap A B C a b)
            (spaceNaiveCotangentConeMap A B C a b))).hom)
      (AlgebraicGeometry.SheafOfModules.range_stalkMap_le_ker_mkQ_comp_stalkMap
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
        (d_comp_shiftedSndZero_comp_π_space A B C a b))) := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => ?_
  obtain ⟨ξ, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range
    (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).d (-1) 0)).hom) q
  refine (Submodule.Quotient.mk_eq_zero _).2
    (mem_range_stalkMap_d_of_mem_range_baseChange A B C a b z ξ ?_)
  exact mem_range_baseChange_cotangentComplex_of_mem_range_stalk A B C a b z _
    (mem_range_cotangentMap_stalkTowerHomRel A B C a b z ξ
      ((Submodule.Quotient.mk_eq_zero _).1 hq))

/-- **The map of cokernels induced by the homotopy component of the canonical map of
Stacks 0E1Y is surjective at every stalk.** -/
theorem surjective_liftQ_stalk_shiftedSndZero (z : T) :
    Function.Surjective ((LinearMap.range
        (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
          ((spaceBaseChangeNaiveCotangentComplex A B C a b).d (-1) 0)).hom).liftQ
      ((LinearMap.range (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
            ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1))).hom).mkQ.comp
        (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
          (CochainComplex.mappingCone.shiftedSndZero
            (spaceRelativeNaiveCotangentComplexMap A B C a b)
            (spaceNaiveCotangentConeMap A B C a b))).hom)
      (AlgebraicGeometry.SheafOfModules.range_stalkMap_le_ker_mkQ_comp_stalkMap
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
        (d_comp_shiftedSndZero_comp_π_space A B C a b))) := by
  refine Quotient.ind fun m => ?_
  obtain ⟨ξ, ω, hξω⟩ := exists_shiftedSndZero_add_stalkMap_relative A B C a b z m
  refine ⟨(LinearMap.range (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
    ((spaceBaseChangeNaiveCotangentComplex A B C a b).d (-1) 0)).hom).mkQ ξ, ?_⟩
  refine (Submodule.Quotient.eq _).2 ⟨-ω, ?_⟩
  rw [map_neg, ← hξω]
  abel

/-- **Stacks 0E1Y: the canonical map `c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]` is an isomorphism on
`H⁰`.** -/
instance isIso_homologyMap_spaceNaiveCotangentConeMap_zero :
    IsIso (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) 0) := by
  rw [CochainComplex.mappingCone.isIso_homologyMap_zero_iff
    (spaceRelativeNaiveCotangentComplexMap A B C a b) (spaceNaiveCotangentConeMap A B C a b)
    (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b) 1
      (by decide) (by decide))
    (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) B C b (-2)
      (by decide) (by decide))
    (CategoryTheory.Functor.map_isZero
      (towerExtendScalars.{u, u, u} (Opens.grothendieckTopology T) B C b)
      (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) A B a 1
        (by decide) (by decide)))]
  exact (AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_comp_π_iff_forall_bijective_liftQ
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) _ _ _ _).2
    fun z => ⟨injective_liftQ_stalk_shiftedSndZero A B C a b z,
      surjective_liftQ_stalk_shiftedSndZero A B C a b z⟩

end Stacks.SheafOfModules

end

end
