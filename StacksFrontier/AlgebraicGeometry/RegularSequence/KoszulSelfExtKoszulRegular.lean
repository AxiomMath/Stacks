module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGlobalAnnihilation
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGlobalQuotient
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtAlgebraFromKInjective

/-!
# The self-Ext algebra of the quotient by a Koszul-regular sheaf of ideals

Let `Y` be a ringed space, `𝓘 ⊆ O_Y` a Koszul-regular sheaf of ideals and `O_X = O_Y/𝓘` the
quotient.  Composition makes the self-Ext sheaves `Extⁿ_{O_Y}(O_X, O_X)` a sheaf of graded
`O_X`-algebras, and [Stacks, Tag 0BQY] asserts that the comparison

`⋀ⁿ(Ext¹_{O_Y}(O_X, O_X)) ⟶ Extⁿ_{O_Y}(O_X, O_X)`

out of the exterior algebra of the degree-one piece is an isomorphism in every degree.  This file
proves it.

The self-Ext algebra is taken in the form it has for an arbitrary object of the derived category:
the composition-product algebra of a chosen K-injective complex presenting `O_X`
(`Stacks.SheafOfModules.kInjectiveModel`), descended along the quotient map so as to be an algebra
over `O_X` rather than over `O_Y`.  Nothing of a Koszul model enters the statement; the three
inputs the gluing of the local statements needs are supplied here:

* the annihilation of every homogeneous piece by `𝓘`, which is what makes the descent exist
  (`smul_globalHomologyPiece_eq_zero`);
* member by member, that the presentation's sequence generates `𝓘` on the slice site
  (`sectionIdeal_sliceIdealOfSections_eq`);
* member by member, the identification of the quotient of the slice structure sheaf by that
  sequence with the restriction of `O_X` (`sliceQuotientRingHom`).

## Main definitions

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.koszulRegularSelfExtAlgebra`: the sheaf of graded
  `O_X`-algebras whose degree-`n` piece is `Extⁿ_{O_Y}(O_X, O_X)` and whose multiplication is
  composition.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isIso_desc_app_isKoszulRegularIdealSheaf`:
  for a Koszul-regular `𝓘`, the comparison `⋀ⁿ(Ext¹_{O_Y}(O_X, O_X)) ⟶ Extⁿ_{O_Y}(O_X, O_X)` is
  an isomorphism in every degree.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Definition 31.21.2 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingedSpace
open _root_.SheafOfModules.GradedAlgebra

attribute [local instance] HasDerivedCategory.standard

variable {Y : RingedSpace.{u, u}} (J : (structureSheafModule Y).Submodule)
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    HasSheafify ((Opens.grothendieckTopology Y.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    ((Opens.grothendieckTopology Y.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasSheafify (Opens.grothendieckTopology ↥V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    (Opens.grothendieckTopology ↥V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]

/-! ### The chosen resolution of the quotient -/

/-- **A K-injective complex of `O_Y`-modules presenting `O_X = O_Y/𝓘`.**  The quotient is the
cokernel of the inclusion of `𝓘`, and this is `Stacks.SheafOfModules.kInjectiveModel` of its
class in the derived category. -/
abbrev koszulQuotientModel :
    CochainComplex (_root_.SheafOfModules.{u}
      (structureSheafRing Y)) ℤ :=
  kInjectiveModel Y.sheaf (DerivedCategory.Q.obj
    ((single (_root_.SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ) 0).obj (cokernel J.ι)))

omit [∀ V : Opens Y.carrier,
    HasSheafify ((Opens.grothendieckTopology Y.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    ((Opens.grothendieckTopology Y.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasSheafify (Opens.grothendieckTopology ↥V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    (Opens.grothendieckTopology ↥V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}] in
/-- The complex `koszulQuotientModel J` presenting `O_X = O_Y/𝓘` is K-injective. -/
theorem isKInjective_koszulQuotientModel : (koszulQuotientModel J).IsKInjective :=
  isKInjective_kInjectiveModel _ _

/-- The chosen complex does present the quotient. -/
def koszulQuotientModelIso :
    DerivedCategory.Q.obj
        ((single (_root_.SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ) 0).obj (cokernel J.ι)) ≅
      DerivedCategory.Q.obj (koszulQuotientModel J) :=
  (kInjectiveModelIso Y.sheaf _).symm

/-! ### The self-Ext algebra, and the comparison of [Stacks, Tag 0BQY] -/

/-- **The quotient map of the structure sheaf by a sheaf of ideals is locally surjective.** -/
instance isLocallySurjective_quotientRingHom_structureSheafModule :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.carrier)
      (quotientRingHom J).hom :=
  Stacks.Sites.isLocallySurjective_quotientRingHom J

/-- **The self-Ext algebra of `O_X` over `O_Y`, as a sheaf of graded `O_X`-algebras.**  Its
degree-`n` piece is `Extⁿ_{O_Y}(O_X, O_X)` and its multiplication is composition; the scalars are
restricted to `O_X` along the quotient map, which is possible because `𝓘` annihilates every
homogeneous piece. -/
abbrev koszulRegularSelfExtAlgebra (hJ : IsKoszulRegularIdealSheaf Y J) :
    _root_.SheafOfModules.GradedAlgebra.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (quotientRingSheaf.{u, u, u} J)) :=
  descendedSelfExtAlgebra (Osharp := quotientRingSheaf.{u, u, u} J)
    (hαloc := Stacks.Sites.isLocallySurjective_quotientRingHom J)
    (koszulQuotientModel J) (quotientRingHom J)
    (smul_globalHomologyPiece_eq_zero J (koszulQuotientModel J)
      (isKInjective_koszulQuotientModel J) (koszulQuotientModelIso J) hJ)

/-- **The degree-one generator of the self-Ext algebra has square zero.** -/
theorem squareZero_id_koszulRegularSelfExtAlgebra (hJ : IsKoszulRegularIdealSheaf Y J) :
    _root_.SheafOfModules.GradedAlgebra.SquareZero
      (𝟙 ((koszulRegularSelfExtAlgebra J hJ).piece 1)) :=
  squareZero_id_descend_koszulRegular (Osharp := quotientRingSheaf.{u, u, u} J)
    (hαloc := Stacks.Sites.isLocallySurjective_quotientRingHom J)
    J J.ι (koszulQuotientModel J)
    (isKInjective_koszulQuotientModel J) (koszulQuotientModelIso J) (quotientRingHom J) _
    (fun d => sectionIdeal_sliceIdealOfSections_eq d.U d.f J d.generated)
    (fun d => sliceQuotientRingHom d.U J d.f d.generated)
    (fun d => isLocallySurjective_sliceQuotientRingHom d.U J d.f d.generated)
    (fun d => quotientRingHom_comp_sliceQuotientRingHom d.U J d.f d.generated) hJ

/-- Let `Y` be a ringed space, `𝓘 ⊆ O_Y` a Koszul-regular sheaf of ideals and `O_X = O_Y/𝓘`.
Let `A` be, with its degree-one generator `ι`, the exterior algebra over `O_X` of
`Ext¹_{O_Y}(O_X, O_X)`.  Then the homomorphism of sheaves of graded algebras that the identity of
`Ext¹_{O_Y}(O_X, O_X)` induces out of `A` — the comparison

`⋀ⁿ(Ext¹_{O_Y}(O_X, O_X)) ⟶ Extⁿ_{O_Y}(O_X, O_X)`

that composition makes — is an isomorphism in every degree `n`. -/
@[stacks 0BQY]
theorem isIso_desc_app_isKoszulRegularIdealSheaf (hJ : IsKoszulRegularIdealSheaf Y J)
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (quotientRingSheaf.{u, u, u} J)))
    (ι : (koszulRegularSelfExtAlgebra J hJ).piece 1 ⟶ A.piece 1)
    (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A ι) (n : ℤ) :
    IsIso ((hA.desc (koszulRegularSelfExtAlgebra J hJ)
      (𝟙 ((koszulRegularSelfExtAlgebra J hJ).piece 1))
      (squareZero_id_koszulRegularSelfExtAlgebra J hJ)).app n) :=
  isIso_desc_app_koszulRegular (Osharp := quotientRingSheaf.{u, u, u} J)
    (hαloc := Stacks.Sites.isLocallySurjective_quotientRingHom J)
    J J.ι (koszulQuotientModel J)
    (isKInjective_koszulQuotientModel J) (koszulQuotientModelIso J) (quotientRingHom J) _
    (fun d => sectionIdeal_sliceIdealOfSections_eq d.U d.f J d.generated)
    (fun d => sliceQuotientRingHom d.U J d.f d.generated)
    (fun d => isLocallySurjective_sliceQuotientRingHom d.U J d.f d.generated)
    (fun d => quotientRingHom_comp_sliceQuotientRingHom d.U J d.f d.generated) hJ A ι hA n

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
