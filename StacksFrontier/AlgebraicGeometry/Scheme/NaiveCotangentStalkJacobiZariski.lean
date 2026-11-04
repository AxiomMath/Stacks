module

public import StacksFrontier.Algebra.Homology.TwoTermHomologyExact
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentTowerStalkQuasiIso
public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiPresentations

/-!
# The stalk of the Jacobi-Zariski sequence of Stacks 0E1Y

Let `A ⟶ B ⟶ C` be morphisms of sheaves of commutative rings on a topological space `T` and let
`z` be a point of `T`.  Stacks 0E1Y attaches to the tower the two canonical chain maps

`c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}`  and  `g : NL_{C/A} ⟶ NL_{C/B}`

of complexes of sheaves of `C`-modules.  This file identifies the stalk at `z` of `g`,
degreewise, with the ring-level comparison `NaiveCotangent.nlExtensionOverMap` of the canonical
presentations of the stalk rings, exactly as
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeComparison` does for `c₁`, and
deduces from Algebra, Lemma 00S2 over the canonical presentations
(`NaiveCotangent.jacobiZariski_sixTerm_exact_canonical`) the two elementwise exactness statements
about the stalks of the three complexes that the six-term sequence of sheaves of Stacks 0E1Y
consumes at the nodes `H^{-1}(NL_{C/A})` and `H⁰(NL_{C/A})`.

The two elementwise statements are the hypotheses of
`HomologicalComplex.exact_homologyMap_of_exists_cycle` and
`HomologicalComplex.exact_homologyMap_of_exists_add_d`, which turn them into exactness of the
sequence of homology modules of the three complexes of stalks; the passage from there to the
sequence of cohomology sheaves is
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSheaves`.

## Main results

* `Stacks.NaiveCotangentStalkJacobiZariski.stalkLegNegOneLinear_spaceRelativeMap` and
  `stalkLegZeroLinear_spaceRelativeMap`: **the stalk of the canonical map `g` of Stacks 0E1Y**,
  in degrees `-1` and `0`, as `NaiveCotangent.nlExtensionOverMap` of
  `Stacks.NaiveCotangentTowerStalk.stalkTowerHomRel`.
* `Stacks.NaiveCotangentStalkJacobiZariski.stalkLegNegOneLinear_spaceBaseChangeMap` and
  `stalkLegZeroLinear_spaceBaseChangeMap`: the stalk of the canonical map `c₁`, as
  `NaiveCotangent.nlExtensionBaseChangeMap` of
  `Stacks.NaiveCotangentTowerStalk.stalkTowerHomBase`.  These are
  `Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_spaceBaseChangeNaiveCotangentMap`
  and its degree `0` companion with the comparison algebra structure of the two equal base rings
  normalized to the identity one, which is what the ring-level sequence is stated over.
* `Stacks.NaiveCotangentStalkJacobiZariski.exists_cycle_stalk`: **exactness at `H^{-1}` of the
  stalks**, elementwise: a cycle of the stalk of `NL_{C/A}` in degree `-1` killed by `g` is the
  image under `c₁` of a cycle of the stalk of `NL_{B/A} ⊗_B C`.
* `Stacks.NaiveCotangentStalkJacobiZariski.exists_add_d_stalk`: **exactness at `H⁰` of the
  stalks**, elementwise: an element of the stalk of `NL_{C/A}` in degree `0` whose image under
  `g` is a boundary differs from an element of the image of `c₁` by a boundary.

## Implementation notes

The identification of the stalk of `g` is the second factor of
`Stacks.NaiveCotangentTowerStalk.stalkLegNegOneLinear_towerComposite`, taken alone: `g` is the
canonical map of the square with vertical morphisms `a` and `𝟙 C`
(`Stacks.SheafOfModules.spaceRelativeNaiveCotangentComplexMap_eq_square`, which is the
`eqToHom`-absorption of `StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentTowerSquare` at the
pair of equal towers), and
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_negOne`
computes the stalk of that map.  The `Algebra Cₓ Cₓ` structure read off the stalk of `𝟙 C` is not
the identity one — the stalk functor is a colimit, so it does not preserve identities on the nose
— and `Stacks.NaiveCotangentTowerStalk.cotangentMap_homCongrEq` moves the functorial map onto the
identity structure, which is the one the ring-level sequence is stated over.

The instances carried by the statements are the three algebra structures read off `a`, `b` and
`a ≫ b` together with the tower they form; those are the instances
`NaiveCotangent.nlExtensionBaseChangeMap` and `NaiveCotangent.nlExtensionOverMap` consume, and
they are the ones carried by
`Stacks.NaiveCotangentTowerStalk.stalkLegNegOneLinear_towerComposite`.  The further structures
read off the stalks of `𝟙 A` and `𝟙 C`, and the scalar towers of the two squares, appear only
inside the proofs.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the two canonical maps
  and the six-term sequence.
* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2), the ring-level six-term
  sequence, over the canonical presentations of
  [Stacks Project, Tag 07BL](https://stacks.math.columbia.edu/tag/07BL).
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), the canonical map
  attached to a square of sheaves of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.NaiveCotangentAffineStalkLegs
open Stacks.NaiveCotangentStalkBaseChange
open Stacks.NaiveCotangentTowerStalk
open Stacks.RelativeDifferentialStalk (algebraStalk)
open AlgebraicGeometry.SheafOfModules (stalkFunctor)
open Stacks.Sites.Conormal (stalkIsScalarTowerSquareBase stalkIsScalarTowerSquareTarget)

universe u

noncomputable section

namespace Stacks.SheafOfModules

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C)

/-- **The canonical map `g : NL_{C/A} ⟶ NL_{C/B}` is the canonical map of the square with
vertical morphisms `a` and `𝟙 C`**, with no transport: the two towers `A ⟶ B ⟶ C` and
`A ⟶ B ⟶ C` of `Stacks.SheafOfModules.eqToHom_comp_spaceRelativeNaiveCotangentComplexMap` are
equal, so the `eqToHom` of that statement is the identity. -/
theorem spaceRelativeNaiveCotangentComplexMap_eq_square :
    spaceRelativeNaiveCotangentComplexMap A B C a b =
      spaceNaiveCotangentComplexMapOfSquare A B C C (a ≫ b) b a (𝟙 C)
        (comp_id_eq_of_tower A B B C a b a b rfl) :=
  (Category.id_comp _).symm.trans
    (eqToHom_comp_spaceRelativeNaiveCotangentComplexMap A B B C a b a b rfl)

end Stacks.SheafOfModules

namespace Stacks.NaiveCotangentStalkJacobiZariski

attribute [local instance 1]
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C) (z : T)

/-! ### The stalk of the canonical map `c₁`, over the identity comparison -/

/-- **The stalk of the canonical map `c₁` of Stacks 0E1Y in degree `-1`**, as the ring-level
comparison attached to `Stacks.NaiveCotangentTowerStalk.stalkTowerHomBase`. -/
theorem stalkLegNegOneLinear_spaceBaseChangeMap
    (ξ : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).X (-1)))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk b.hom z
    letI := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
    stalkLegNegOneLinear A C (a ≫ b) z
        (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceBaseChangeNaiveCotangentMap A B C a b).f (-1))).hom ξ) =
      (NaiveCotangent.nlExtensionBaseChangeMap
          (T := ToType (TopCat.Presheaf.stalk C.obj z))
          (stalkTowerHomBase A B C a b z)).f₁
        (stalkBaseChangeAddEquivNegOne A B C a b z ξ) := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 A)) z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  let := stalkIsScalarTowerSquareBase A A C (a ≫ b) (a ≫ b) (𝟙 A) z (Category.id_comp (a ≫ b))
  refine Eq.trans (stalkLegNegOneLinear_spaceBaseChangeNaiveCotangentMap A B C a b z ξ) ?_
  exact nlExtensionBaseChangeMap_f₁_homCongrEq
    (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 A)) z) (Algebra.id _)
    (algebraStalk_id A z)
    (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
      (Category.id_comp (a ≫ b)).symm) _ (IsScalarTower.left _) _

/-- **The stalk of the canonical map `c₁` of Stacks 0E1Y in degree `0`**, as the ring-level
comparison attached to `Stacks.NaiveCotangentTowerStalk.stalkTowerHomBase`. -/
theorem stalkLegZeroLinear_spaceBaseChangeMap
    (ξ : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).X 0))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk b.hom z
    letI := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
    stalkLegZeroLinear A C (a ≫ b) z
        (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceBaseChangeNaiveCotangentMap A B C a b).f 0)).hom ξ) =
      (NaiveCotangent.nlExtensionBaseChangeMap
          (T := ToType (TopCat.Presheaf.stalk C.obj z))
          (stalkTowerHomBase A B C a b z)).f₀
        (stalkBaseChangeAddEquivZero A B C a b z ξ) := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 A)) z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  let := stalkIsScalarTowerSquareBase A A C (a ≫ b) (a ≫ b) (𝟙 A) z (Category.id_comp (a ≫ b))
  refine Eq.trans (stalkLegZeroLinear_spaceBaseChangeNaiveCotangentMap A B C a b z ξ) ?_
  exact nlExtensionBaseChangeMap_f₀_homCongrEq
    (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 A)) z) (Algebra.id _)
    (algebraStalk_id A z)
    (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
      (Category.id_comp (a ≫ b)).symm) _ (IsScalarTower.left _) _

/-! ### The stalk of the canonical map `g` -/

/-- **The stalk of the canonical map `g : NL_{C/A} ⟶ NL_{C/B}` of Stacks 0E1Y in degree `-1`**,
as the ring-level comparison `NaiveCotangent.nlExtensionOverMap` attached to
`Stacks.NaiveCotangentTowerStalk.stalkTowerHomRel`. -/
theorem stalkLegNegOneLinear_spaceRelativeMap
    (ω : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b)).X (-1)))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk b.hom z
    letI := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
    stalkLegNegOneLinear B C b z
        (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1))).hom ω) =
      (NaiveCotangent.nlExtensionOverMap (stalkTowerHomRel A B B C a b a b z rfl)).f₁
        (stalkLegNegOneLinear A C (a ≫ b) z ω) := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  refine Eq.trans (congrArg (fun φ => stalkLegNegOneLinear B C b z
      (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        (HomologicalComplex.Hom.f φ (-1))).hom ω))
    (spaceRelativeNaiveCotangentComplexMap_eq_square A B C a b)) ?_
  refine Eq.trans (stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_negOne A B C C (a ≫ b) b
    a (𝟙 C) z (comp_id_eq_of_tower A B B C a b a b rfl) (a ≫ b) rfl ω) ?_
  exact cotangentMap_homCongrEq (algebraStalk a.hom z) (algebraStalk a.hom z)
    (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z) (Algebra.id _) rfl
    (algebraStalk_id C z)
    (generatorsSelfStalkHomOfSquare A B C C (a ≫ b) b a (𝟙 C) z
      (comp_id_eq_of_tower A B B C a b a b rfl)) _
    (stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl) _ _

/-- **The stalk of the canonical map `g : NL_{C/A} ⟶ NL_{C/B}` of Stacks 0E1Y in degree `0`**,
as the ring-level comparison `NaiveCotangent.nlExtensionOverMap` attached to
`Stacks.NaiveCotangentTowerStalk.stalkTowerHomRel`. -/
theorem stalkLegZeroLinear_spaceRelativeMap
    (ω : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b)).X 0))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk b.hom z
    letI := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
    stalkLegZeroLinear B C b z
        (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceRelativeNaiveCotangentComplexMap A B C a b).f 0)).hom ω) =
      (NaiveCotangent.nlExtensionOverMap (stalkTowerHomRel A B B C a b a b z rfl)).f₀
        (stalkLegZeroLinear A C (a ≫ b) z ω) := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  refine Eq.trans (congrArg (fun φ => stalkLegZeroLinear B C b z
      (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        (HomologicalComplex.Hom.f φ 0)).hom ω))
    (spaceRelativeNaiveCotangentComplexMap_eq_square A B C a b)) ?_
  refine Eq.trans (stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_zero A B C C (a ≫ b) b
    a (𝟙 C) z (comp_id_eq_of_tower A B B C a b a b rfl) (a ≫ b) rfl ω) ?_
  exact cotangentSpaceMap_homCongrEq (algebraStalk a.hom z) (algebraStalk a.hom z)
    (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z) (Algebra.id _) rfl
    (algebraStalk_id C z)
    (generatorsSelfStalkHomOfSquare A B C C (a ≫ b) b a (𝟙 C) z
      (comp_id_eq_of_tower A B B C a b a b rfl)) _
    (stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl) _ _

/-! ### The two exactness statements at a stalk -/

/-- **Exactness of the Jacobi-Zariski sequence at `H^{-1}(NL_{C/A})`, at a stalk, elementwise.**
A cycle of the stalk of `NL_{C/A}` in degree `-1` killed by `g` is the image under `c₁` of a
cycle of the stalk of `NL_{B/A} ⊗_B C`.

This is the exactness of Algebra, Lemma 00S2 at `H₁(NL_{Cₓ/Aₓ})` over the canonical
presentations of the stalk rings, read through Stacks 0D09 at the three complexes and through the
identifications of the stalks of the two canonical maps. -/
theorem exists_cycle_stalk
    (y : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b)).X (-1))))
    (hy : ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C
          (a ≫ b)).d (-1) 0)).hom y = 0)
    (hg : ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        ((spaceRelativeNaiveCotangentComplexMap A B C a b).f (-1))).hom y = 0) :
    ∃ x : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).X (-1))),
      ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceBaseChangeNaiveCotangentComplex A B C a b).d (-1) 0)).hom x = 0 ∧
        ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceBaseChangeNaiveCotangentMap A B C a b).f (-1))).hom x = y := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  let := moduleRingStalkCotangent A C (a ≫ b) z
  let := moduleRingStalkCotangentSpace A C (a ≫ b) z
  let := moduleRingStalkCotangent B C b z
  refine CochainComplex.exists_cycle_of_addEquiv
    (u₁ := stalkBaseChangeAddEquivNegOne A B C a b z)
    (u₀ := stalkBaseChangeAddEquivZero A B C a b z)
    (v₁ := (stalkLegNegOneLinear A C (a ≫ b) z).toAddEquiv)
    (v₀ := (stalkLegZeroLinear A C (a ≫ b) z).toAddEquiv)
    (w₁ := (stalkLegNegOneLinear B C b z).toAddEquiv)
    (stalkBaseChangeAddEquiv_d A B C a b z) (stalkLegLinear_d A C (a ≫ b) z)
    (stalkLegNegOneLinear_spaceBaseChangeMap A B C a b z)
    (stalkLegNegOneLinear_spaceRelativeMap A B C a b z)
    (fun m hm hrm => NaiveCotangent.exists_cycle_of_exact_onH₁
      (NaiveCotangent.nlExtensionBaseChangeMap
        (T := ToType (TopCat.Presheaf.stalk C.obj z)) (stalkTowerHomBase A B C a b z))
      (NaiveCotangent.nlExtensionOverMap (stalkTowerHomRel A B B C a b a b z rfl))
      (NaiveCotangent.jacobiZariski_sixTerm_exact_canonical (stalkTowerHomBase A B C a b z)
        (stalkTowerHomRel A B B C a b a b z rfl)).1 m hm hrm) y hy hg

/-- **Exactness of the Jacobi-Zariski sequence at `H⁰(NL_{C/A})`, at a stalk, elementwise.**  An
element of the stalk of `NL_{C/A}` in degree `0` whose image under `g` is a boundary differs from
an element of the image of `c₁` by a boundary.

This is the exactness of Algebra, Lemma 00S2 at `H₀(NL_{Cₓ/Aₓ})` over the canonical
presentations of the stalk rings, read through the same identifications. -/
theorem exists_add_d_stalk
    (y : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b)).X 0)))
    (hy : ∃ w : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).X (-1))),
      ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C
            b).d (-1) 0)).hom w =
        ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceRelativeNaiveCotangentComplexMap A B C a b).f 0)).hom y) :
    ∃ (x : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
        ((spaceBaseChangeNaiveCotangentComplex A B C a b).X 0)))
      (w : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C
          (a ≫ b)).X (-1)))),
      ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            ((spaceBaseChangeNaiveCotangentMap A B C a b).f 0)).hom x +
          ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C
              (a ≫ b)).d (-1) 0)).hom w =
        y := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  let := moduleRingStalkCotangent A C (a ≫ b) z
  let := moduleRingStalkCotangentSpace A C (a ≫ b) z
  let := moduleRingStalkCotangent B C b z
  let := moduleRingStalkCotangentSpace B C b z
  refine CochainComplex.exists_add_d_of_addEquiv
    (u₀ := stalkBaseChangeAddEquivZero A B C a b z)
    (v₁ := (stalkLegNegOneLinear A C (a ≫ b) z).toAddEquiv)
    (v₀ := (stalkLegZeroLinear A C (a ≫ b) z).toAddEquiv)
    (w₁ := (stalkLegNegOneLinear B C b z).toAddEquiv)
    (w₀ := (stalkLegZeroLinear B C b z).toAddEquiv)
    (stalkLegLinear_d A C (a ≫ b) z) (stalkLegLinear_d B C b z)
    (stalkLegZeroLinear_spaceBaseChangeMap A B C a b z)
    (stalkLegZeroLinear_spaceRelativeMap A B C a b z)
    (fun n hn => NaiveCotangent.exists_add_d_of_exact_onH₀
      (NaiveCotangent.nlExtensionBaseChangeMap
        (T := ToType (TopCat.Presheaf.stalk C.obj z)) (stalkTowerHomBase A B C a b z))
      (NaiveCotangent.nlExtensionOverMap (stalkTowerHomRel A B B C a b a b z rfl))
      (NaiveCotangent.jacobiZariski_sixTerm_exact_canonical (stalkTowerHomBase A B C a b z)
        (stalkTowerHomRel A B B C a b a b z rfl)).2.2.2.1 n hn) y hy

/-- **Surjectivity of the canonical map `g` on `H⁰`, at a stalk, elementwise.**  Every element of
the stalk of `NL_{C/B}` in degree `0` differs from an element of the image of `g` by a boundary.

This is the surjectivity clause of Algebra, Lemma 00S2 over the canonical presentations of the
stalk rings — the final `⟶ 0` of the six-term sequence — read through Stacks 0D09 at the two
complexes and through the identification of the stalk of `g`. -/
theorem exists_add_d_relative_stalk
    (y : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).X 0))) :
    ∃ (x : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b)).X 0)))
      (w : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b).X (-1)))),
      ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            ((spaceRelativeNaiveCotangentComplexMap A B C a b).f 0)).hom x +
          ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C
              b).d (-1) 0)).hom w =
        y := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  let := moduleRingStalkCotangent A C (a ≫ b) z
  let := moduleRingStalkCotangentSpace A C (a ≫ b) z
  let := moduleRingStalkCotangent B C b z
  let := moduleRingStalkCotangentSpace B C b z
  refine CochainComplex.exists_add_d_eq_of_addEquiv
    (u₀ := (stalkLegZeroLinear A C (a ≫ b) z).toAddEquiv)
    (v₁ := (stalkLegNegOneLinear B C b z).toAddEquiv)
    (v₀ := (stalkLegZeroLinear B C b z).toAddEquiv)
    (stalkLegLinear_d B C b z) (stalkLegZeroLinear_spaceRelativeMap A B C a b z)
    (fun n => NaiveCotangent.exists_add_d_of_surjective_onH₀
      (NaiveCotangent.nlExtensionOverMap (stalkTowerHomRel A B B C a b a b z rfl))
      (NaiveCotangent.jacobiZariski_sixTerm_exact_canonical (stalkTowerHomBase A B C a b z)
        (stalkTowerHomRel A B B C a b a b z rfl)).2.2.2.2 n) y

end Stacks.NaiveCotangentStalkJacobiZariski

end

end
