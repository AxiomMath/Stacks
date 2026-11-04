module

public import StacksFrontier.Algebra.Homology.MappingConeTwoTermConnecting
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSixTerm
public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiConormalZigZag

/-!
# The connecting morphism of Stacks 0E1Y on a conormal class, at a stalk

Let `A ⟶ B ⟶ C` be morphisms of sheaves of commutative rings on a topological space.  The
connecting morphism

`∂ : H^{-1}(NL_{C/B}) ⟶ H⁰(NL_{B/A} ⊗_B C)`

of the six-term exact sequence of [Stacks Project, Tag 0E1Y] is, by construction, the morphism
induced by the inclusion of the cone of `g : NL_{C/A} ⟶ NL_{C/B}` composed with the inverse of
`H⁰` of the canonical map `c` of that tag.  Nothing in that description says what `∂` does, and a
distinguished triangle pins it only up to automorphisms of its source and target, so it has to be
computed.  This file computes it **at a stalk, on a conormal class**, and the answer is

`∂ [f] = -(1 ⊗ d f)`.

The sign is minus.

## Route

`CochainComplex.mappingCone.cycle_connecting_apply` reduces `∂` to a zig-zag: a cycle of
`NL_{C/B}` in degree `-1` whose image in the degree `-1` term is the value of the null homotopy
of [Stacks Project, Tag 07VC] on an element `ω`, modulo the image of `g` in degree `-1`, is
carried by `∂` to the class of `ω`.  The zig-zag datum on a conormal class is
`NaiveCotangent.cotangent_mk_C_eq_towerNullHomotopy_add`: the class of the constant polynomial
`f` is `h (-(1 ⊗ d[f])) + g([0])`.  Both are transported to a stalk by the identifications of
[Stacks Project, Tag 0D09] already in the library —
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear`,
`Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquivZero`,
`Stacks.SheafOfModules.stalkLegNegOneLinear_shiftedSndZero` and
`Stacks.SheafOfModules.cotangentMap_stalkLegNegOneLinear_spaceRelativeMap`.

The zig-zag is *not* natural: `ω` is obtained from `f` by taking the variable of the canonical
presentation indexed by `f`, which is a map of sheaves of sets and not of modules.  That is why
the computation is elementwise and why `cycle_connecting_apply` is stated under a functor.

## Main results

* `Stacks.SheafOfModules.stalkAddCommGroupFunctor_map_apply`: the abelian-group-valued and the
  module-valued spellings of the stalk of a morphism agree on the nose.
* `Stacks.SheafOfModules.isZero_spaceBaseChangeNaiveCotangentComplex_X_one`: the source of the
  canonical map of [Stacks Project, Tag 0E1Y] vanishes in degree `1`.
* `Stacks.SheafOfModules.stalk_zigzag_cotangent_mk`: the zig-zag of
  [Stacks Project, Tag 07VC] on a conormal class, at a stalk.
* `Stacks.SheafOfModules.stalk_connecting_cotangent_mk`: **the connecting morphism of
  [Stacks Project, Tag 0E1Y] at a stalk carries a conormal class `[f]` to the class of
  `-(1 ⊗ d[f])`.**  The sign is minus.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the six-term sequence.
* [Stacks Project, Tag 07VC](https://stacks.math.columbia.edu/tag/07VC), the null homotopy.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex.
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the conormal sequence,
  whose first arrow is what the answer is minus.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (stalkFunctor stalkMap stalkObj stalkAddCommGroupFunctor)
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

/-- **The two spellings of the stalk of a morphism of sheaves of modules agree on the nose.**
`AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor` forgets to abelian groups and
`AlgebraicGeometry.SheafOfModules.stalkMap` keeps the module structure over the stalk of the
sheaf of rings, but both are the stalk of the underlying presheaf of abelian groups. -/
theorem stalkAddCommGroupFunctor_map_apply (z : T)
    {M N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C)}
    (φ : M ⟶ N)
    (w : ToType
      ((stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj M)) :
    (stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map φ w =
      (stalkMap (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z φ).hom w :=
  rfl

/-- The naive cotangent complex of the canonical presentation of `C` over `A` vanishes in
degree `1`. -/
theorem isZero_naiveCotangentComplex_X_one_total :
    IsZero ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C
      (a ≫ b)).X 1) :=
  naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b) 1
    (by decide) (by decide)

/-- The naive cotangent complex of the canonical presentation of `C` over `B` vanishes in
degree `-2`. -/
theorem isZero_naiveCotangentComplex_X_negTwo :
    IsZero ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).X (-2)) :=
  naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) B C b (-2)
    (by decide) (by decide)

/-- `NL_{B/A} ⊗_B C` vanishes in degree `1`, being the termwise extension of scalars of a
complex that does. -/
theorem isZero_spaceBaseChangeNaiveCotangentComplex_X_one :
    IsZero ((spaceBaseChangeNaiveCotangentComplex A B C a b).X 1) :=
  CategoryTheory.Functor.map_isZero
    (towerExtendScalars.{u, u, u} (Opens.grothendieckTopology T) B C b)
    (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) A B a 1
      (by decide) (by decide))

/-- **The zig-zag of [Stacks Project, Tag 07VC] on a conormal class, at a stalk.**  For a germ
`f` of `B` at `z` in the kernel of `B ⟶ C`, a germ of the cycles of `NL_{C/B}` in degree `-1`
whose underlying germ is the conormal class of `f` is the value of the degree `0` component of the
canonical map of [Stacks Project, Tag 0E1Y], read against the second projection of the cone, on
`-(1 ⊗ d[f])`, plus an element of the image of `g` in degree `-1`.

The two members of the presentation ideals — the constant `f` of
`B_z[C_z]` and the variable `[0]` of `A_z[C_z]` — are parameters rather than written out, because
a subterm `⟨C f, _⟩` is only type-correct after unfolding `Algebra.Extension.Ring` and `rw`
refuses to act on a goal containing one. -/
theorem stalk_zigzag_cotangent_mk (z : T)
    (fz : ToType (TopCat.Presheaf.stalk B.obj z))
    (hfz : letI := algebraStalk b.hom z
      algebraMap (ToType (TopCat.Presheaf.stalk B.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z)) fz = 0)
    (jf : letI := algebraStalk b.hom z
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk B.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z))).ker)
    (hjf : letI := algebraStalk b.hom z
      jf.1 = MvPolynomial.C fz)
    (x0 : letI := algebraStalk (a ≫ b).hom z
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z))).ker)
    (hx0 : letI := algebraStalk (a ≫ b).hom z
      x0.1 = MvPolynomial.X (0 : ToType (TopCat.Presheaf.stalk C.obj z)))
    (ξ : ToType
      ((stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).cycles
          (-1))))
    (hξ : letI := algebraStalk b.hom z
      stalkLegNegOneLinear B C b z
          ((stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).iCycles
              (-1)) ξ) =
        Algebra.Extension.Cotangent.mk jf) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk b.hom z
    letI := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
    (stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).iCycles
          (-1)) ξ =
      (stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          (CochainComplex.mappingCone.shiftedSndZero
            (spaceRelativeNaiveCotangentComplexMap A B C a b)
            (spaceNaiveCotangentConeMap A B C a b))
          ((stalkBaseChangeAddEquivZero A B C a b z).symm
            (-((1 : ToType (TopCat.Presheaf.stalk C.obj z)) ⊗ₜ
              (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
                (ToType (TopCat.Presheaf.stalk B.obj z))).cotangentSpaceBasis fz))) +
        (stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1))
          ((stalkLegNegOneLinear A C (a ≫ b) z).symm
            (Algebra.Extension.Cotangent.mk x0)) := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  have h₁ : stalkLegNegOneLinear B C b z
      ((stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        (CochainComplex.mappingCone.shiftedSndZero
          (spaceRelativeNaiveCotangentComplexMap A B C a b)
          (spaceNaiveCotangentConeMap A B C a b))
        ((stalkBaseChangeAddEquivZero A B C a b z).symm
          (-((1 : ToType (TopCat.Presheaf.stalk C.obj z)) ⊗ₜ
            (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
              (ToType (TopCat.Presheaf.stalk B.obj z))).cotangentSpaceBasis fz)))) =
      NaiveCotangent.towerNullHomotopyBaseChange (ToType (TopCat.Presheaf.stalk A.obj z))
          (ToType (TopCat.Presheaf.stalk B.obj z)) (ToType (TopCat.Presheaf.stalk C.obj z))
        (-((1 : ToType (TopCat.Presheaf.stalk C.obj z)) ⊗ₜ
          (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
            (ToType (TopCat.Presheaf.stalk B.obj z))).cotangentSpaceBasis fz)) :=
    (stalkLegNegOneLinear_shiftedSndZero A B C a b z _).trans
      (congrArg (fun y => NaiveCotangent.towerNullHomotopyBaseChange
          (ToType (TopCat.Presheaf.stalk A.obj z)) (ToType (TopCat.Presheaf.stalk B.obj z))
          (ToType (TopCat.Presheaf.stalk C.obj z)) y)
        ((stalkBaseChangeAddEquivZero A B C a b z).apply_symm_apply _))
  have h₂ : stalkLegNegOneLinear B C b z
      ((stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1))
        ((stalkLegNegOneLinear A C (a ≫ b) z).symm
          (Algebra.Extension.Cotangent.mk x0))) =
      Algebra.Extension.Cotangent.map
        (NaiveCotangent.towerTopHom (ToType (TopCat.Presheaf.stalk A.obj z))
            (ToType (TopCat.Presheaf.stalk B.obj z))
            (ToType (TopCat.Presheaf.stalk C.obj z))).toExtensionHom
        (Algebra.Extension.Cotangent.mk x0) :=
    ((cotangentMap_stalkLegNegOneLinear_spaceRelativeMap A B C a b z _).trans
      (congrArg (fun y => Algebra.Extension.Cotangent.map
          (stalkTowerHomRel A B B C a b a b z rfl) y)
        ((stalkLegNegOneLinear A C (a ≫ b) z).apply_symm_apply _))).trans
      (DFunLike.congr_fun (cotangentMap_stalkTowerHomRel A B C a b z) _)
  refine (stalkLegNegOneLinear B C b z).injective
    (hξ.trans (Eq.trans ?_ (map_add (stalkLegNegOneLinear B C b z) _ _).symm))
  rw [h₁, h₂]
  exact NaiveCotangent.cotangent_mk_eq_towerNullHomotopy_add
    (ToType (TopCat.Presheaf.stalk A.obj z)) (ToType (TopCat.Presheaf.stalk B.obj z))
    (ToType (TopCat.Presheaf.stalk C.obj z)) hfz jf hjf x0 hx0

/-- **The connecting morphism of the six-term exact sequence of [Stacks Project, Tag 0E1Y], at a
stalk, on a conormal class.**  For a germ `f` of `B` at `z` in the kernel of `B ⟶ C`, the
connecting morphism

`∂ : H^{-1}(NL_{C/B}) ⟶ H⁰(NL_{B/A} ⊗_B C)`

carries the class of the cycle `[f]` to the class of `-(1 ⊗ d[f])`, which under the
identification `H⁰(NL_{B/A} ⊗_B C) = C ⊗_B Ω_{B/A}` is `-(1 ⊗ d f)`
(`NaiveCotangent.toKaehler_baseChange_neg_basis`).

So the connecting morphism of [Stacks Project, Tag 0E1Y] is **minus** the first arrow
`I/I² ⟶ C ⊗_B Ω_{B/A}` of the conormal sequence of [Stacks Project, Tag 01UZ].  That sign is
what any comparison of the two has to carry, and neither the exactness of the sequence nor the
distinguished triangle it comes from determines it: both maps have the same image, and a
distinguished triangle pins its maps only up to automorphisms of their sources and targets. -/
theorem stalk_connecting_cotangent_mk (z : T)
    (fz : ToType (TopCat.Presheaf.stalk B.obj z))
    (hfz : letI := algebraStalk b.hom z
      algebraMap (ToType (TopCat.Presheaf.stalk B.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z)) fz = 0)
    (jf : letI := algebraStalk b.hom z
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk B.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z))).ker)
    (hjf : letI := algebraStalk b.hom z
      jf.1 = MvPolynomial.C fz)
    (x0 : letI := algebraStalk (a ≫ b).hom z
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z))).ker)
    (hx0 : letI := algebraStalk (a ≫ b).hom z
      x0.1 = MvPolynomial.X (0 : ToType (TopCat.Presheaf.stalk C.obj z)))
    (ξ : ToType
      ((stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).cycles
          (-1))))
    (hξ : letI := algebraStalk b.hom z
      stalkLegNegOneLinear B C b z
          ((stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).iCycles
              (-1)) ξ) =
        Algebra.Extension.Cotangent.mk jf) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk b.hom z
    letI := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
    (stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).homologyπ
            (-1) ≫
          spaceJacobiZariskiConnecting A B C a b) ξ =
      (stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        ((spaceBaseChangeNaiveCotangentComplex A B C a b).toHomologyZero
          (isZero_spaceBaseChangeNaiveCotangentComplex_X_one A B C a b))
        ((stalkBaseChangeAddEquivZero A B C a b z).symm
          (-((1 : ToType (TopCat.Presheaf.stalk C.obj z)) ⊗ₜ
            (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
              (ToType (TopCat.Presheaf.stalk B.obj z))).cotangentSpaceBasis fz))) :=
  CochainComplex.mappingCone.cycle_connecting_apply
    (spaceRelativeNaiveCotangentComplexMap A B C a b)
    (spaceNaiveCotangentConeMap A B C a b)
    (stalkAddCommGroupFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z)
    (isZero_naiveCotangentComplex_X_one_total A B C a b)
    (isZero_naiveCotangentComplex_X_negTwo B C b)
    (isZero_spaceBaseChangeNaiveCotangentComplex_X_one A B C a b)
    ξ _ _ (stalk_zigzag_cotangent_mk A B C a b z fz hfz jf hjf x0 hx0 ξ hξ)

end Stacks.SheafOfModules

end

end
