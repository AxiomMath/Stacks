module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomAnnihilatorSource
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientRingSheafOpenSubspaceIdeal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Duality.Sweep.SheafExtDerivedComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.KoszulRank
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtStructureSheafUnit
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulResolutionOfIdealSheaf
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulRestrictedQuotient
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtKoszulRegular
public import StacksFrontier.Homology.DerivedCategory.ZeroDifferentialCoproduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafExtOpenSubspace
public import StacksFrontier.Topology.Sheaves.Cohomology.LocallyConcentratedFormality
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
import StacksCore.Tactic.StacksAttribute

/-!
# The derived dual of a Koszul-regular quotient: [Stacks, Tag 0BQZ]

Let `Y` be a ringed space, `𝓘 ⊆ O_Y` a sheaf of ideals, `O_X = O_Y/𝓘` and
`𝒩 = 𝓗om_{O_Y}(𝓘/𝓘², O_X)` the normal sheaf. [Stacks, Tag 0BQZ]: if `𝓘` is Koszul-regular, then

`R𝓗om_{O_Y}(O_X, O_Y) = ⋀^r 𝒩 [-r]`,

where `r` sends `y` to the minimal number of generators of `𝓘` needed in a neighbourhood of `y`.
This file proves it.

## The objects

* `R𝓗om_{O_Y}(O_X, O_Y)` is the derived internal Hom `Stacks.SheafOfModules.derivedSheafHom` of
  [Stacks, Tag 08DH] evaluated at `O_X` and `O_Y` placed in degree zero.
* `r` is `Stacks.AlgebraicGeometry.RegularIdealSheaf.localGeneratorCount`, literally the minimal
  number of generators of `𝓘` needed near `y`.
* `𝒩` is `Stacks.Duality.normalSheafOfIdealSheaf`, the normal sheaf of [Stacks, Tag 0BQW]; it is
  annihilated by `𝓘` and so is a sheaf of `O_X`-modules, `normalSheafQuotient`. Its exterior
  powers are formed over `O_X`, by the exterior algebra of `SheafOfModules.algebras`, or more
  generally by any exterior algebra `A` of `𝒩` over `O_X` (`IsExteriorAlgebra`), and read over
  `O_Y`.
* The function `r` is locally constant on the support `X` of `O_X`, and every term of the formula
  is supported on `X`. So `⋀^r 𝒩 [-r]` is the complex with zero differential whose degree-`n`
  term is `⋀ⁿ𝒩` on the part of `X` where `r = n` and zero elsewhere: `rankExteriorTerm A n` is
  `⋀ⁿ𝒩` restricted to `rankLocus 𝓘 n`, the largest open on which `r = n` at every point of `X`,
  and extended by zero. Off `X` both sides vanish, which is why the value of `r` there plays no
  role.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.nonempty_derivedSheafHom_iso_rankExterior`:
  **[Stacks, Tag 0BQZ]**, for the exterior algebra `SheafOfModules.algebras` of `𝒩`.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.nonempty_derivedSheafHom_iso_of_isExteriorAlgebra`:
  the same for any exterior algebra of `𝒩` over `O_X`.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.extIsoRankExteriorTerm`: the cohomology sheaves,
  `𝓔xtⁿ_{O_Y}(O_X, O_Y) ≅ ⋀ⁿ𝒩` on the rank-`n` locus, extended by zero.

## The proof

As in the source. By [Stacks, Tag 0BQW] (`Stacks.Duality.isIso_normalSheafToSheafExtOne`, read in
the derived model by `Stacks.RingedSpace.sheafExtIsoDerivedSheafExt`) and [Stacks, Tag 0BQY]
(`isIso_desc_app_isKoszulRegularIdealSheaf`), `⋀ⁿ𝒩 ≅ 𝓔xtⁿ(O_X, O_X)` globally
(`exteriorPieceIsoSelfExt`). It then suffices that `𝓔xtⁿ(O_X, O_Y)` vanishes for `n ≠ r` and that
`𝓔xtʳ(O_X, O_Y) ⟶ 𝓔xtʳ(O_X, O_X)` is an isomorphism. These are local: on the open `U` of a Koszul
presentation `f₁, …, f_r` of `𝓘` the Ext sheaves are computed on the open subspace `U`
(`Stacks.SheafOfModules.derivedSheafExtOpenSubspaceIso`, natural in the coefficients) by the Koszul
complex, where they are `Stacks.RegularSequence.KoszulChainData.isZero_derivedSheafExt_unit_of_ne`
and `Stacks.RegularSequence.KoszulChainData.isIso_derivedSheafExtMap_unit_quotient` (the
self-duality of the Koszul complex, at stalks). The rank of a presentation at a point of `X` is
`r` (`localGeneratorCount_eq`), so presentations of different ranks meet only off `X`, where the
model `R𝓗om(O_X, O_Y) = Q(𝓗om^•(O_X, I))`, `I` a K-injective model of `O_Y`, has zero terms
(`isZero_overFunctor_dualModel_X`). Its cohomology is therefore locally concentrated in one
degree on a cover whose differently-graded members meet where its terms vanish, and
`Stacks.SheafOfModules.nonempty_iso_zeroDifferentialComplex_homology_of_cover` identifies it with
the zero-differential complex of its cohomology sheaves, which are the terms of `⋀^r 𝒩 [-r]`
(`extIsoRankExteriorTermOfLocal`).

## Implementation notes

**The codomain of `r`.** The source writes `r : Y → {1, 2, 3, …}`. The minimal number of local
generators is `0` exactly near points where `𝓘` vanishes, and there the formula holds with
`⋀⁰𝒩 = O_X = O_Y`; `localGeneratorCount` takes values in `ℕ` and the theorem covers those points
too. Off the support of `O_X` the minimal number is `1` (or `0` where `O_Y` vanishes), and there
both sides of the formula vanish.

**The instance hypotheses** on the sheafification of the various sites are those of the
statement of [Stacks, Tag 0BQY] in `KoszulSelfExtKoszulRegular`; they hold for every ringed space
`Y` (instance search finds them), and are carried as binders only so that the elaboration of the
statement uses one instance throughout.

**The isomorphism is asserted to exist.** The source's `=` is an isomorphism in the derived
category, and the source remarks that its normalization depends on the conventions for Koszul
complexes; the formalization asserts that an isomorphism exists. Its components on cohomology are
the canonical maps `𝓔xtⁿ(O_X, O_Y) ⟶ 𝓔xtⁿ(O_X, O_X) ≅ ⋀ⁿ𝒩` of the proof.

## References

* [Stacks Project, Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ)
* [Stacks Project, Tag 0BQW](https://stacks.math.columbia.edu/tag/0BQW)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Definition 31.21.2 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open HomologicalComplex ExtensionByZeroModules

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

open Stacks.Sites Stacks.SheafOfModules Stacks.RingedSpace CategoryTheory.Sheaf

attribute [local instance] HasDerivedCategory.standard

variable {Y : RingedSpace.{u, u}} (J : (structureSheafModule Y).Submodule)
  [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]

/-- A section lies in the kernel of the quotient map exactly when it lies in `𝓘`. -/
private theorem mem_ker_quotientRingHom_iff (X : (Opens Y.carrier)ᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj.obj X) :
    a ∈ RingHom.ker ((quotientRingHom J).hom.app X).hom ↔ a ∈ J.obj X :=
  (SheafOfModules.mem_kerIdeal (quotientRingHom J) X a).symm.trans
    (by rw [kerIdeal_quotientRingHom J]; exact Iff.rfl)

/-- **The sheaf of ideals annihilates the normal sheaf**: a homomorphism into `O_X` is killed by
every section of `𝓘`, because `O_X` is. -/
theorem smul_normalSheaf_eq_zero : ∀ (X : (Opens Y.carrier)ᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj.obj X),
    a ∈ RingHom.ker ((quotientRingHom J).hom.app X).hom →
      ∀ m : (Stacks.Duality.normalSheafOfIdealSheaf Y J).val.obj X, a • m = 0 := by
  intro X a ha m
  exact smulHom_eq_zero _ _ _ X.unop a
    (fun V x => Stacks.Duality.smul_quotientByIdealSheaf_eq_zero Y J V.unop.left _
      (J.toSubmodule.map_mem V.unop.hom.op ((mem_ker_quotientRingHom_iff J X a).1 ha)) x) m

/-- **The normal sheaf `𝒩 = 𝓗om_{O_Y}(𝓘/𝓘², O_X)` as a sheaf of `O_X`-modules.** It is
annihilated by `𝓘` (`smul_normalSheaf_eq_zero`), so it is the restriction of scalars along
`O_Y ⟶ O_X` of this `O_X`-module (`ChangeOfRings.restrictScalarsLiftedSheafIso`). -/
def normalSheafQuotient :
    SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology Y.carrier) (quotientRingSheaf.{u, u, u} J)) :=
  @Stacks.SheafOfModules.ChangeOfRings.liftedSheaf _ _ _ (structureSheaf Y.sheaf)
    (toRingCat (Opens.grothendieckTopology Y.carrier) (quotientRingSheaf.{u, u, u} J))
    (quotientRingHom J)
    (Stacks.Duality.normalSheafOfIdealSheaf Y J) (smul_normalSheaf_eq_zero J)
    (Stacks.Sites.isLocallySurjective_quotientRingHom J)

section OffSupport

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}] in
/-- **Off the support the sheaf of ideals contains `1`.** Membership in a sheaf of ideals is
local, and a point off the support of `O_Y/𝓘` has a neighbourhood on which `1 ∈ 𝓘`. -/
theorem one_mem_of_forall_notMem (W : Opens Y.carrier)
    (hW : ∀ y ∈ W, y ∉ idealQuotientSupport Y J) : (1 : Y.presheaf.obj (op W)) ∈ J.obj (op W) := by
  refine J.isSheaf (X := op W) (show (structureSheafModule Y).val.obj (op W) from
    (1 : Y.presheaf.obj (op W))) ((Opens.mem_grothendieckTopology _).mpr fun y hy => ?_)
  obtain ⟨U, hyU, h1⟩ := (notMem_idealQuotientSupport_iff J y).mp (hW y hy)
  refine ⟨U ⊓ W, homOfLE inf_le_right, ?_, ⟨hyU, hy⟩⟩
  have h := J.toSubmodule.map_mem (homOfLE (inf_le_left : U ⊓ W ≤ U)).op h1
  change Y.presheaf.map (homOfLE inf_le_right).op 1 ∈ J.obj (op (U ⊓ W))
  change Y.presheaf.map (homOfLE inf_le_left).op 1 ∈ J.obj (op (U ⊓ W)) at h
  rw [map_one] at h ⊢
  assumption

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}] in
/-- **A module annihilated by `𝓘` has no nonzero sections where `1 ∈ 𝓘`.** -/
theorem section_eq_zero_of_annihilated {M : StructureSheafModules Y.sheaf}
    (hM : ∀ (V : Opens Y.carrier) (a : (structureSheaf Y.sheaf).obj.obj (op V)),
      a ∈ J.obj (op V) → ∀ m : M.val.obj (op V), a • m = 0)
    {W : Opens Y.carrier} (h1 : (1 : Y.presheaf.obj (op W)) ∈ J.obj (op W))
    {V : Opens Y.carrier} (hVW : V ≤ W) (m : M.val.obj (op V)) : m = 0 := by
  have h1V : (1 : Y.presheaf.obj (op V)) ∈ J.obj (op V) := by
    have h := J.toSubmodule.map_mem (homOfLE hVW).op h1
    change Y.presheaf.map (homOfLE hVW).op 1 ∈ J.obj (op V) at h
    rwa [map_one] at h
  rw [← one_smul ((structureSheaf Y.sheaf).obj.obj (op V)) m]
  exact hM V 1 h1V m

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}] in
/-- **A module annihilated by `𝓘` restricts to zero on an open where `1 ∈ 𝓘`**, read on the slice
site. -/
theorem isZero_overFunctor_obj_of_annihilated {M : StructureSheafModules Y.sheaf}
    (hM : ∀ (V : Opens Y.carrier) (a : (structureSheaf Y.sheaf).obj.obj (op V)),
      a ∈ J.obj (op V) → ∀ m : M.val.obj (op V), a • m = 0)
    {W : Opens Y.carrier} (h1 : (1 : Y.presheaf.obj (op W)) ∈ J.obj (op W)) :
    IsZero ((_root_.SheafOfModules.overFunctor (structureSheaf Y.sheaf) W).obj M) := by
  rw [IsZero.iff_id_eq_zero]
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun m => ?_))
  exact (section_eq_zero_of_annihilated J hM h1 (leOfHom V.unop.hom) m).trans
    (section_eq_zero_of_annihilated J hM h1 (leOfHom V.unop.hom) _).symm

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}] in
/-- **A module annihilated by `𝓘` restricts to zero on an open where `1 ∈ 𝓘`**, read on the open
subspace. -/
theorem isZero_jStar_obj_of_annihilated {M : StructureSheafModules Y.sheaf}
    (hM : ∀ (V : Opens Y.carrier) (a : (structureSheaf Y.sheaf).obj.obj (op V)),
      a ∈ J.obj (op V) → ∀ m : M.val.obj (op V), a • m = 0)
    {W : Opens Y.carrier} (h1 : (1 : Y.presheaf.obj (op W)) ∈ J.obj (op W)) :
    IsZero ((jStar W (structureSheaf Y.sheaf)).obj M) :=
  Functor.map_isZero (sliceToSubspaceFunctor Y.sheaf W)
    (isZero_overFunctor_obj_of_annihilated J hM h1)

end OffSupport

section Glue

variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
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

/-- `𝒩 ≅ 𝓔xt¹(O_X, O_X)` with the Ext sheaf in the composition-product model of [Stacks, Tag 0BQY],
read over `O_Y`. -/
def normalSheafIsoSelfExtOnePiece (hJ : IsKoszulRegularIdealSheaf Y J) :
    Stacks.Duality.normalSheafOfIdealSheaf Y J ≅
      (_root_.SheafOfModules.restrictScalars (quotientRingHom J)).obj
        ((koszulRegularSelfExtAlgebra J hJ).piece 1) :=
  haveI := Stacks.Duality.isIso_normalSheafToSheafExtOne Y J
  haveI : CochainComplex.IsKInjective
      (show CochainComplex (StructureSheafModules Y.sheaf) ℤ from koszulQuotientModel J) :=
    isKInjective_koszulQuotientModel J
  asIso (Stacks.Duality.normalSheafToSheafExtOne Y J) ≪≫
    Stacks.RingedSpace.sheafExtIsoDerivedSheafExt Y _ _ 1 ≪≫
    derivedSheafExtIsoEndComplexHomology Y.sheaf (koszulQuotientModel J) _
      (koszulQuotientModelIso J).symm 1 ≪≫
    (_root_.SheafOfModules.GradedAlgebra.restrictScalars_descend_piece_iso
      (quotientRingHom J) (globalHomologyGradedAlgebra (koszulQuotientModel J))
      (smul_globalHomologyPiece_eq_zero J (koszulQuotientModel J)
        (isKInjective_koszulQuotientModel J) (koszulQuotientModelIso J) hJ) 1).symm

/-- **[Stacks, Tag 0BQW] read over `O_X`.** The normal sheaf, as an `O_X`-module, is the degree-one
piece of the self-Ext algebra of [Stacks, Tag 0BQY]. -/
def normalSheafQuotientIsoSelfExtOne (hJ : IsKoszulRegularIdealSheaf Y J) :
    normalSheafQuotient J ≅ (koszulRegularSelfExtAlgebra J hJ).piece 1 :=
  letI : Sheaf.IsLocallySurjective (quotientRingHom J) :=
    Stacks.Sites.isLocallySurjective_quotientRingHom J
  (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
      (quotientRingHom J)).preimageIso
    (Stacks.SheafOfModules.ChangeOfRings.restrictScalarsLiftedSheafIso
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
        (quotientRingHom J) (Stacks.Duality.normalSheafOfIdealSheaf Y J)
        (smul_normalSheaf_eq_zero J) ≪≫
      normalSheafIsoSelfExtOnePiece J hJ)

/-- **`⋀ⁿ 𝒩 ≅ 𝓔xtⁿ(O_X, O_X)`**, gluing [Stacks, Tag 0BQW] and [Stacks, Tag 0BQY]: for every
exterior algebra `A` over `O_X` of the normal sheaf, its degree-`n` piece, read over `O_Y`, is the
Ext sheaf `𝓔xtⁿ_{O_Y}(O_X, O_X)` of the derived internal Hom. -/
def exteriorPieceIsoSelfExt (hJ : IsKoszulRegularIdealSheaf Y J)
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u}
      (toRingCat (Opens.grothendieckTopology Y.carrier) (quotientRingSheaf.{u, u, u} J)))
    (ι : normalSheafQuotient J ⟶ A.piece 1)
    (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A ι) (n : ℤ) :
    (_root_.SheafOfModules.restrictScalars (quotientRingHom J)).obj (A.piece n) ≅
      derivedSheafExt Y.sheaf
        (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
          (cokernel J.ι)))
        (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
          (cokernel J.ι))) n :=
  haveI : CochainComplex.IsKInjective
      (show CochainComplex (StructureSheafModules Y.sheaf) ℤ from koszulQuotientModel J) :=
    isKInjective_koszulQuotientModel J
  let c := normalSheafQuotientIsoSelfExtOne J hJ
  have hA' : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A (c.inv ≫ ι) :=
    hA.comp_iso c.inv (Iso.isIso_inv c)
  (_root_.SheafOfModules.restrictScalars (quotientRingHom J)).mapIso
      (@asIso _ _ _ _ _ (isIso_desc_app_isKoszulRegularIdealSheaf J hJ A (c.inv ≫ ι) hA' n)) ≪≫
    _root_.SheafOfModules.GradedAlgebra.restrictScalars_descend_piece_iso
      (quotientRingHom J) (globalHomologyGradedAlgebra (koszulQuotientModel J))
      (smul_globalHomologyPiece_eq_zero J (koszulQuotientModel J)
        (isKInjective_koszulQuotientModel J) (koszulQuotientModelIso J) hJ) n ≪≫
    (derivedSheafExtIsoEndComplexHomology Y.sheaf (koszulQuotientModel J) _
      (koszulQuotientModelIso J).symm n).symm

end Glue

section Model

variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    HasSheafify ((Opens.grothendieckTopology Y.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    ((Opens.grothendieckTopology Y.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The chosen K-injective model of `O_Y` placed in degree zero. -/
abbrev unitModel : CochainComplex (StructureSheafModules Y.sheaf) ℤ :=
  kInjectiveModel Y.sheaf (DerivedCategory.Q.obj
    ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (structureSheaf Y.sheaf))))

/-- **The model of `R𝓗om(O_X, O_Y)`**: the internal Hom complex out of `O_X` placed in degree
zero into the chosen K-injective model of `O_Y`. -/
abbrev dualModel : CochainComplex (StructureSheafModules Y.sheaf) ℤ :=
  (RingedSite.sheafHomComplex (ringedSite Y.sheaf)
    (Stacks.RingedSpace.singleZero Y (cokernel J.ι)) (unitModel (Y := Y))).obj

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}] in
/-- If every term of a complex restricts to zero on `V`, so does its cohomology. -/
theorem isZero_overFunctor_homology_of_isZero_X
    (K : CochainComplex (StructureSheafModules Y.sheaf) ℤ)
    (V : Opens Y.carrier)
    (h : ∀ k, IsZero ((_root_.SheafOfModules.overFunctor (structureSheaf Y.sheaf) V).obj (K.X k)))
    (k : ℤ) :
    IsZero ((_root_.SheafOfModules.overFunctor (structureSheaf Y.sheaf) V).obj (K.homology k)) :=
  have := Stacks.SheafOfModules.preservesHomology_overFunctor (R := structureSheaf Y.sheaf) V
  IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _ (h k))
    ((K.sc k).mapHomologyIso
      (_root_.SheafOfModules.overFunctor (structureSheaf Y.sheaf) V)).symm

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasSheafify ((Opens.grothendieckTopology Y.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    ((Opens.grothendieckTopology Y.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The terms of the model are annihilated by `𝓘`**: they are internal Homs out of `O_X`. -/
theorem isZero_overFunctor_dualModel_X {W : Opens Y.carrier}
    (h1 : (1 : Y.presheaf.obj (op W)) ∈ J.obj (op W)) (k : ℤ) :
    IsZero ((_root_.SheafOfModules.overFunctor (structureSheaf Y.sheaf) W).obj
      ((dualModel J).X k)) := by
  refine IsZero.of_iso ?_ ((_root_.SheafOfModules.overFunctor (structureSheaf Y.sheaf) W).mapIso
    (Stacks.RingedSpace.sheafHomSingleSourceXIso Y (cokernel J.ι) (unitModel (Y := Y)) k))
  refine isZero_overFunctor_obj_of_annihilated J (fun V a ha m => ?_) h1
  exact smulHom_eq_zero_of_source _ _ _ V a
    (fun V' x => Stacks.Duality.smul_quotientByIdealSheaf_eq_zero Y J V'.unop.left _
      (J.toSubmodule.map_mem V'.unop.hom.op ha) x) m

/-- **The Ext sheaves `𝓔xtⁿ(O_X, O_Y)` are the cohomology sheaves of the model.** -/
def derivedSheafExtIsoDualModelHomology (n : ℤ) :
    derivedSheafExt Y.sheaf
        (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
          (cokernel J.ι)))
        (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)))) n ≅
      (dualModel J).homology n :=
  haveI := isKInjective_kInjectiveModel Y.sheaf (DerivedCategory.Q.obj
    ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (structureSheaf Y.sheaf))))
  derivedSheafExtMapIso Y.sheaf n (Iso.refl _) (kInjectiveModelIso Y.sheaf _).symm ≪≫
    (DerivedCategory.homologyFunctor (StructureSheafModules Y.sheaf) n).mapIso
      (derivedSheafHomComparison Y.sheaf _ (unitModel (Y := Y))) ≪≫
    (DerivedCategory.homologyFunctorFactors (StructureSheafModules Y.sheaf) n).app _

/-- **`R𝓗om(O_X, O_Y)` is the class of the model.** -/
def derivedSheafHomIsoDualModel :
    ((derivedSheafHom Y.sheaf).obj (op (DerivedCategory.Q.obj
        ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj (cokernel J.ι))))).obj
        (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)))) ≅
      DerivedCategory.Q.obj (dualModel J) :=
  haveI := isKInjective_kInjectiveModel Y.sheaf (DerivedCategory.Q.obj
    ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (structureSheaf Y.sheaf))))
  ((derivedSheafHom Y.sheaf).obj _).mapIso (kInjectiveModelIso Y.sheaf _).symm ≪≫
    derivedSheafHomComparison Y.sheaf _ (unitModel (Y := Y))

end Model

variable {J} in
/-- **The terms of `⋀^r 𝒩 [-r]`.** For an exterior algebra `A` of `𝒩` over `O_X`, the degree-`n`
term is `⋀ⁿ𝒩 = A.piece n`, read over `O_Y`, restricted to the rank-`n` locus — the largest open on
which every point of the support of `O_X` has `r = n` — and extended by zero. -/
def rankExteriorTerm (A : _root_.SheafOfModules.GradedAlgebra.{u, u}
      (toRingCat (Opens.grothendieckTopology Y.carrier) (quotientRingSheaf.{u, u, u} J))) (n : ℤ) :
    SheafOfModules.{u} (structureSheaf Y.sheaf) :=
  (jShriek (rankLocus J n) (structureSheaf Y.sheaf)).obj
    ((jStar (rankLocus J n) (structureSheaf Y.sheaf)).obj
      ((_root_.SheafOfModules.restrictScalars (quotientRingHom J)).obj (A.piece n)))

section Assembly

variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
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

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
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
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- A sheaf of modules zero on an open subspace has zero stalks there. -/
theorem isZero_stalk_of_isZero_jStar {V : Opens Y.carrier} {M : StructureSheafModules Y.sheaf}
    (h : IsZero ((jStar V (structureSheaf Y.sheaf)).obj M)) (x : Y.carrier) (hx : x ∈ V) :
    IsZero (TopCat.Presheaf.stalk (X := Y.carrier) M.val.presheaf x) :=
  IsZero.of_iso ((AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff
      (resRing V (structureSheaf Y.sheaf)) ⟨x, hx⟩ _).1
      ((AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj
        (resRing V (structureSheaf Y.sheaf)) _).1 h ⟨x, hx⟩))
    (TopCat.Presheaf.stalkRestrictIso V M.val.presheaf ⟨x, hx⟩).symm

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
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
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- A sheaf of modules zero on the slice site over `V` is zero on the open subspace `V`. -/
theorem isZero_jStar_of_isZero_overFunctor {V : Opens Y.carrier} {M : StructureSheafModules Y.sheaf}
    (h : IsZero ((_root_.SheafOfModules.overFunctor (structureSheaf Y.sheaf) V).obj M)) :
    IsZero ((jStar V (structureSheaf Y.sheaf)).obj M) :=
  Functor.map_isZero (sliceToSubspaceFunctor Y.sheaf V) h

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
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
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- A sheaf of modules zero on the open subspace `V` is zero on the slice site over `V`. -/
theorem isZero_overFunctor_of_isZero_jStar {V : Opens Y.carrier} {M : StructureSheafModules Y.sheaf}
    (h : IsZero ((jStar V (structureSheaf Y.sheaf)).obj M)) :
    IsZero ((_root_.SheafOfModules.overFunctor (structureSheaf Y.sheaf) V).obj M) :=
  IsZero.of_iso (Functor.map_isZero (V.sheafOfModulesEquivOver (structureSheaf Y.sheaf)).inverse h)
    ((V.sheafOfModulesEquivOver (structureSheaf Y.sheaf)).unitIso.app _)

/-- The quotient map `O_Y ⟶ O_X`, in the spelling of the Ext sheaves. -/
abbrev quotientMap : _root_.SheafOfModules.unit (structureSheaf Y.sheaf) ⟶ cokernel J.ι :=
  cokernel.π J.ι

/-- The Ext sheaf `𝓔xtⁿ_{O_Y}(O_X, M)` for a module `M` placed in degree zero. -/
abbrev extInto (M : StructureSheafModules Y.sheaf) (n : ℤ) : StructureSheafModules Y.sheaf :=
  derivedSheafExt Y.sheaf
    (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
      (cokernel J.ι)))
    (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj M)) n

/-- The map `𝓔xtⁿ(O_X, O_Y) ⟶ 𝓔xtⁿ(O_X, O_X)` induced by `O_Y ⟶ O_X`. -/
abbrev extQuotientMap (n : ℤ) :
    extInto J (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)) n ⟶
      extInto J (cokernel J.ι) n :=
  derivedSheafExtMap Y.sheaf n (𝟙 _)
    (DerivedCategory.Q.map ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).map
      (quotientMap J)))

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
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
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- The restriction of scalars of an `O_X`-module is annihilated by `𝓘`. -/
theorem smul_restrictScalars_eq_zero
    (P : _root_.SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology Y.carrier) (quotientRingSheaf.{u, u, u} J)))
    (V : Opens Y.carrier) (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj.obj (op V))
    (ha : a ∈ J.obj (op V))
    (m : ((_root_.SheafOfModules.restrictScalars (quotientRingHom J)).obj P).val.obj (op V)) :
    a • m = 0 := by
  have hker : (quotientRingHom J).hom.app (op V) a = 0 := (mem_ker_quotientRingHom_iff J _ a).2 ha
  change (show (toRingCat (Opens.grothendieckTopology Y.carrier)
      (quotientRingSheaf.{u, u, u} J)).obj.obj (op V) from
        (quotientRingHom J).hom.app (op V) a) • (show P.val.obj (op V) from m) = 0
  rw [show (show (toRingCat (Opens.grothendieckTopology Y.carrier)
      (quotientRingSheaf.{u, u, u} J)).obj.obj (op V) from
        (quotientRingHom J).hom.app (op V) a) = 0 from hker, zero_smul]

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  [∀ V : Opens Y.carrier, HasSheafify (Opens.grothendieckTopology ↥V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    (Opens.grothendieckTopology ↥V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- **`𝓔xtⁿ(O_X, O_Y)` vanishes on an open where `1 ∈ 𝓘`**: it is the cohomology of the model,
whose terms vanish there. -/
theorem isZero_jStar_extInto_of_one_mem {W : Opens Y.carrier}
    (h1 : (1 : Y.presheaf.obj (op W)) ∈ J.obj (op W)) (n : ℤ) :
    IsZero ((jStar W (structureSheaf Y.sheaf)).obj
      (extInto J (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)) n)) :=
  IsZero.of_iso (isZero_jStar_of_isZero_overFunctor
      (isZero_overFunctor_homology_of_isZero_X _ W
        (fun k => isZero_overFunctor_dualModel_X J h1 k) n))
    ((jStar W (structureSheaf Y.sheaf)).mapIso (derivedSheafExtIsoDualModelHomology J n))

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
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
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- **The rank-`n` piece of `⋀ʳ𝒩` vanishes on an open where `1 ∈ 𝓘`.** -/
theorem isZero_jStar_restrictScalars_of_one_mem {W : Opens Y.carrier}
    (h1 : (1 : Y.presheaf.obj (op W)) ∈ J.obj (op W))
    (P : _root_.SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology Y.carrier) (quotientRingSheaf.{u, u, u} J))) :
    IsZero ((jStar W (structureSheaf Y.sheaf)).obj
      ((_root_.SheafOfModules.restrictScalars (quotientRingHom J)).obj P)) :=
  isZero_jStar_obj_of_annihilated J (smul_restrictScalars_eq_zero J P) h1

/-- The sequence of a Koszul presentation, as global sections of the open subspace. -/
abbrev presentationSections (d : KoszulPresentation Y J) :
    Fin d.r → (openSubspace d.U).sheaf.obj.obj (op ⊤) :=
  fun j => sectionOnRestriction Y d.U (d.f j)

/-- The Koszul morphism of a presentation, on the open subspace. -/
abbrev presentationHom (d : KoszulPresentation Y J) :=
  Stacks.RegularSequence.koszulHomOfSections (openSubspace d.U).sheaf (presentationSections J d)

/-- **The restriction of `O_X` to the open of a presentation is the Koszul quotient there.** -/
def restrictQuotientIso (d : KoszulPresentation Y J) :
    (openSubspaceRestrictFunctor d.U).obj (cokernel J.ι) ≅
      Stacks.RegularSequence.KoszulChainData.quotient (openSubspace d.U).sheaf
        (φ := presentationHom J d) :=
  koszulRestrictedQuotientIso d.U d.f J.ι
    (fun W => sectionIdeal_sliceIdealOfSections_eq d.U d.f J d.generated W)

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasSheafify ((Opens.grothendieckTopology Y.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    ((Opens.grothendieckTopology Y.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasSheafify (Opens.grothendieckTopology ↥V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    (Opens.grothendieckTopology ↥V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- The restriction of the quotient map to the open subspace, in the two spellings of the
restriction functor. -/
theorem restrictMap_eq (d : KoszulPresentation Y J) :
    (openSubspaceRestrictFunctor d.U).map (cokernel.π J.ι) =
      (openSubspaceEquiv d.U).functor.map
        ((_root_.SheafOfModules.overFunctor (structureSheafRing Y) d.U).map (cokernel.π J.ι)) :=
  rfl

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- **`koszulRestrictedQuotientIso` carries the restricted quotient map to the quotient map of the
Koszul morphism**, in the spelling of the restriction that it is defined with. -/
theorem koszulRestrictedQuotientIso_comm (d : KoszulPresentation Y J) :
    (openSubspaceEquiv d.U).functor.map
        ((_root_.SheafOfModules.overFunctor (structureSheafRing Y) d.U).map (cokernel.π J.ι)) ≫
      (koszulRestrictedQuotientIso d.U d.f J.ι
        (fun W => sectionIdeal_sliceIdealOfSections_eq d.U d.f J d.generated W)).hom =
      cokernel.π (presentationHom J d) := by
  have h0 := congrArg (fun t => (openSubspaceEquiv d.U).functor.map t)
    (PreservesCokernel.π_iso_hom (_root_.SheafOfModules.overFunctor (structureSheafRing Y) d.U)
      J.ι)
  have h1 : (openSubspaceEquiv d.U).functor.map
        ((_root_.SheafOfModules.overFunctor (structureSheafRing Y) d.U).map (cokernel.π J.ι)) ≫
      (openSubspaceRestrictCokernelIso d.U J.ι).hom =
        cokernel.π (openSubspaceRestrictHom d.U J.ι) :=
    (Functor.map_comp_assoc _ _ _ _).symm.trans ((congrArg (· ≫ _) h0).trans
      (PreservesCokernel.π_iso_hom _ _))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    (Stacks.Sites.cokernelπ_comp_cokernelIsoOfSectionIdealEq_hom.{u} _ _ _))

/-- Moving a map in the second variable across a change-of-objects isomorphism of Ext sheaves. -/
theorem derivedSheafExtMapIso_comm {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] (n : ℤ)
    {K K' L L' M M' : DerivedCategory (StructureSheafModules Rc)} (k : K' ≅ K) (l : L ≅ L')
    (m : M ≅ M') (g : L ⟶ M) (g' : L' ⟶ M') (h : g ≫ m.hom = l.hom ≫ g') :
    derivedSheafExtMap Rc n (𝟙 K) g ≫ (derivedSheafExtMapIso Rc n k m).hom =
      (derivedSheafExtMapIso Rc n k l).hom ≫ derivedSheafExtMap Rc n (𝟙 K') g' := by
  rw [derivedSheafExtMapIso_hom, derivedSheafExtMapIso_hom, derivedSheafExtMap_comp,
    derivedSheafExtMap_comp, Category.comp_id, Category.id_comp, h]

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- **The restriction of the quotient map is the quotient map of the Koszul morphism.** -/
theorem restrictQuotientIso_comm (d : KoszulPresentation Y J) :
    (openSubspaceRestrictFunctor d.U).map (cokernel.π J.ι) ≫ (restrictQuotientIso J d).hom =
      cokernel.π (presentationHom J d) := by
  rw [restrictMap_eq]
  exact koszulRestrictedQuotientIso_comm J d

/-- **`𝓔xtⁿ(O_X, O_Y)` restricted to the open of a presentation is the Ext sheaf of the Koszul
quotient there.** -/
def restrictExtIso (d : KoszulPresentation Y J) (n : ℤ) :
    (openSubspaceRestrictFunctor d.U).obj
        (extInto J (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)) n) ≅
      derivedSheafExt (openSubspace d.U).sheaf
        (DerivedCategory.Q.obj ((single (StructureSheafModules (openSubspace d.U).sheaf)
          (ComplexShape.up ℤ) 0).obj (Stacks.RegularSequence.KoszulChainData.quotient
            (openSubspace d.U).sheaf (φ := presentationHom J d))))
        (DerivedCategory.Q.obj ((single (StructureSheafModules (openSubspace d.U).sheaf)
          (ComplexShape.up ℤ) 0).obj (_root_.SheafOfModules.unit
            (structureSheaf (openSubspace d.U).sheaf)))) n :=
  derivedSheafExtOpenSubspaceIso d.U _ _ n ≪≫
    derivedSheafExtMapIso (openSubspace d.U).sheaf n
      ((DerivedCategory.singleFunctor _ 0).mapIso (restrictQuotientIso J d).symm ≪≫
        (((openSubspaceRestrictFunctor d.U).mapDerivedCategorySingleFunctor 0).app _).symm)
      (((openSubspaceRestrictFunctor d.U).mapDerivedCategorySingleFunctor 0).app _)

/-- **`𝓔xtⁿ(O_X, O_X)` restricted to the open of a presentation is the self-Ext sheaf of the
Koszul quotient there.** -/
def restrictExtQuotientIso (d : KoszulPresentation Y J) (n : ℤ) :
    (openSubspaceRestrictFunctor d.U).obj (extInto J (cokernel J.ι) n) ≅
      derivedSheafExt (openSubspace d.U).sheaf
        (DerivedCategory.Q.obj ((single (StructureSheafModules (openSubspace d.U).sheaf)
          (ComplexShape.up ℤ) 0).obj (Stacks.RegularSequence.KoszulChainData.quotient
            (openSubspace d.U).sheaf (φ := presentationHom J d))))
        (DerivedCategory.Q.obj ((single (StructureSheafModules (openSubspace d.U).sheaf)
          (ComplexShape.up ℤ) 0).obj (Stacks.RegularSequence.KoszulChainData.quotient
            (openSubspace d.U).sheaf (φ := presentationHom J d)))) n :=
  derivedSheafExtOpenSubspaceIso d.U _ _ n ≪≫
    derivedSheafExtMapIso (openSubspace d.U).sheaf n
      ((DerivedCategory.singleFunctor _ 0).mapIso (restrictQuotientIso J d).symm ≪≫
        (((openSubspaceRestrictFunctor d.U).mapDerivedCategorySingleFunctor 0).app _).symm)
      (((openSubspaceRestrictFunctor d.U).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (restrictQuotientIso J d))

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- **The restriction of `𝓔xtⁿ(O_X, O_Y) ⟶ 𝓔xtⁿ(O_X, O_X)` to the open of a presentation is the
map induced by the Koszul quotient map there.** -/
theorem restrictExtIso_natural (d : KoszulPresentation Y J) (n : ℤ) :
    (openSubspaceRestrictFunctor d.U).map (extQuotientMap J n) ≫
        (restrictExtQuotientIso J d n).hom =
      (restrictExtIso J d n).hom ≫ derivedSheafExtMap (openSubspace d.U).sheaf n (𝟙 _)
        (DerivedCategory.Q.map ((single (StructureSheafModules (openSubspace d.U).sheaf)
          (ComplexShape.up ℤ) 0).map (cokernel.π (presentationHom J d)))) := by
  have hnat := ((openSubspaceRestrictFunctor d.U).mapDerivedCategorySingleFunctor 0).hom.naturality
    (cokernel.π J.ι)
  dsimp only [Functor.comp_map] at hnat
  have key : (openSubspaceRestrictFunctor d.U).mapDerivedCategory.map
        (DerivedCategory.Q.map ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).map
          (quotientMap J))) ≫
      ((((openSubspaceRestrictFunctor d.U).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (restrictQuotientIso J d)).hom) =
      (((openSubspaceRestrictFunctor d.U).mapDerivedCategorySingleFunctor 0).app _).hom ≫
        DerivedCategory.Q.map ((single (StructureSheafModules (openSubspace d.U).sheaf)
          (ComplexShape.up ℤ) 0).map (cokernel.π (presentationHom J d))) := by
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    change (openSubspaceRestrictFunctor d.U).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor _ 0).map (cokernel.π J.ι)) ≫ _ = _
    rw [reassoc_of% hnat, ← Functor.map_comp, restrictQuotientIso_comm J d]
    rfl
  have hOSI := derivedSheafExtOpenSubspaceIso_natural_right d.U
    (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
      (cokernel J.ι)))
    (DerivedCategory.Q.map ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).map
      (quotientMap J))) n
  have hcomm := derivedSheafExtMapIso_comm (openSubspace d.U).sheaf n
    ((DerivedCategory.singleFunctor _ 0).mapIso (restrictQuotientIso J d).symm ≪≫
        (((openSubspaceRestrictFunctor d.U).mapDerivedCategorySingleFunctor 0).app _).symm)
    (((openSubspaceRestrictFunctor d.U).mapDerivedCategorySingleFunctor 0).app _)
    (((openSubspaceRestrictFunctor d.U).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (restrictQuotientIso J d)) _ _ key
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hOSI).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hcomm)))

/-- The Koszul complex of a presentation resolves its quotient. -/
instance quasiIso_presentation_augmentation (d : KoszulPresentation Y J) :
    QuasiIso (Stacks.RegularSequence.koszulChainData (presentationHom J d)).augmentation :=
  Stacks.RegularSequence.quasiIso_koszulChainData_augmentation _
    (Stacks.RegularSequence.quasiIso_koszulAugmentation_restrict Y d.U d.f d.koszulExact)

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasSheafify ((Opens.grothendieckTopology Y.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- **The first local statement: over the open of a presentation of length `r`, `𝓔xtⁿ(O_X, O_Y)`
vanishes for `n ≠ r`.** -/
theorem isZero_restrict_extInto_of_ne (d : KoszulPresentation Y J) (n : ℤ) (hn : n ≠ d.r) :
    IsZero ((openSubspaceRestrictFunctor d.U).obj
      (extInto J (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)) n)) :=
  IsZero.of_iso (Stacks.RegularSequence.KoszulChainData.isZero_derivedSheafExt_unit_of_ne
      (openSubspace d.U).sheaf (presentationSections J d)
      (Stacks.RegularSequence.freeHomEquiv_koszulHomOfSections _ _)
      (Stacks.RegularSequence.koszulChainData (presentationHom J d))
      (fun x => isKoszulRegular_germSequence_restrict Y d.U d.f x
        ((isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular Y d.U d.f).1 d.koszulExact
          x.1 x.2)) hn)
    (restrictExtIso J d n)

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasSheafify ((Opens.grothendieckTopology Y.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- The first local statement, read with restriction to the open subspace as `j^*`. -/
theorem isZero_jStar_extInto_of_ne (d : KoszulPresentation Y J) (n : ℤ) (hn : n ≠ d.r) :
    IsZero ((jStar d.U (structureSheaf Y.sheaf)).obj
      (extInto J (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)) n)) := by
  have h := isZero_restrict_extInto_of_ne J d n hn
  rwa [openSubspaceRestrictFunctor_eq_jStar] at h

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- **The second local statement: over the open of a presentation of length `r`,
`𝓔xtʳ(O_X, O_Y) ⟶ 𝓔xtʳ(O_X, O_X)` is an isomorphism.** -/
theorem isIso_restrict_extQuotientMap (d : KoszulPresentation Y J) :
    IsIso ((openSubspaceRestrictFunctor d.U).map (extQuotientMap J d.r)) := by
  have h := Stacks.RegularSequence.KoszulChainData.isIso_derivedSheafExtMap_unit_quotient
    (openSubspace d.U).sheaf (presentationSections J d)
    (Stacks.RegularSequence.freeHomEquiv_koszulHomOfSections _ _)
    (Stacks.RegularSequence.koszulChainData (presentationHom J d))
  have : (openSubspaceRestrictFunctor d.U).map (extQuotientMap J d.r) =
      (restrictExtIso J d d.r).hom ≫ derivedSheafExtMap (openSubspace d.U).sheaf d.r (𝟙 _)
        (DerivedCategory.Q.map ((single (StructureSheafModules (openSubspace d.U).sheaf)
          (ComplexShape.up ℤ) 0).map (cokernel.π (presentationHom J d)))) ≫
        (restrictExtQuotientIso J d d.r).inv := by
    rw [← Category.assoc, ← restrictExtIso_natural J d d.r, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [this]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h (Iso.isIso_inv _))

omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}] in
/-- The second local statement, read with restriction to the open subspace as `j^*`. -/
theorem isIso_jStar_extQuotientMap (d : KoszulPresentation Y J) :
    IsIso ((jStar d.U (structureSheaf Y.sheaf)).map (extQuotientMap J d.r)) := by
  have h := isIso_restrict_extQuotientMap J d
  rwa [openSubspaceRestrictFunctor_eq_jStar] at h

/-- **`𝓔xtⁿ(O_X, O_Y) ≅ ⋀ⁿ𝒩` on the rank-`n` locus, extended by zero**, granted the two local
statements over the opens of Koszul presentations: the vanishing of `𝓔xtⁿ(O_X, O_Y)` for `n` other
than the length of the presentation, and the invertibility of
`𝓔xtʳ(O_X, O_Y) ⟶ 𝓔xtʳ(O_X, O_X)` in that length. -/
def extIsoRankExteriorTermOfLocal (hJ : IsKoszulRegularIdealSheaf Y J)
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u}
      (toRingCat (Opens.grothendieckTopology Y.carrier) (quotientRingSheaf.{u, u, u} J)))
    (ι : normalSheafQuotient J ⟶ A.piece 1)
    (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A ι)
    (hL1 : ∀ (d : KoszulPresentation Y J) (n : ℤ), n ≠ d.r →
      IsZero ((jStar d.U (structureSheaf Y.sheaf)).obj
        (extInto J (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)) n)))
    (hL2 : ∀ d : KoszulPresentation Y J,
      IsIso ((jStar d.U (structureSheaf Y.sheaf)).map (extQuotientMap J d.r)))
    (n : ℤ) :
    extInto J (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)) n ≅ rankExteriorTerm A n := by
  let O := structureSheaf Y.sheaf
  let E := extInto J (_root_.SheafOfModules.unit O) n
  let ψ : E ⟶ (_root_.SheafOfModules.restrictScalars (quotientRingHom J)).obj (A.piece n) :=
    extQuotientMap J n ≫ (exteriorPieceIsoSelfExt J hJ A ι hA n).inv
  have hcover : ∀ x : Y.carrier, ∃ d : KoszulPresentation Y J, x ∈ d.U := fun x =>
    Opens.mem_iSup.mp ((iSup_koszulPresentation_eq_top J hJ).ge (Opens.mem_top x))
  -- the stalks of `E` vanish off the rank-`n` locus
  have hE : ∀ x : Y.carrier, x ∉ rankLocus J n →
      IsZero (TopCat.Presheaf.stalk (X := Y.carrier) E.val.presheaf x) := by
    intro x hx
    by_cases hxS : x ∈ idealQuotientSupport Y J
    · obtain ⟨d, hxd⟩ := hcover x
      exact isZero_stalk_of_isZero_jStar
        (hL1 d n fun h => hx (h ▸ le_rankLocus d.koszulExact d.generated hxd)) x hxd
    · obtain ⟨W, hxW, h1⟩ := (notMem_idealQuotientSupport_iff J x).mp hxS
      exact isZero_stalk_of_isZero_jStar (isZero_jStar_extInto_of_one_mem J h1 n) x hxW
  haveI := counit_isIso_of_stalk_isZero (rankLocus J n) O E hE
  -- `ψ` is an isomorphism on the rank-`n` locus
  haveI : IsIso ((jStar (rankLocus J n) O).map ψ) := by
    refine Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_jStar_map_of_stalk_isIso O _ ψ
      fun z hz => ?_
    obtain ⟨d, hzd⟩ := hcover z
    by_cases hdn : (d.r : ℤ) = n
    · subst hdn
      have h2 := Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_stalk_of_isIso_jStar_map O d.U
        _ (hL2 d) z hzd
      have e : (TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map
          ((ExtensionByZeroModules.toAb O).map ψ) = _ :=
        (congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map
          ((ExtensionByZeroModules.toAb O).map_comp _ _)).trans
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map_comp _ _)
      rw [e]
      exact IsIso.comp_isIso' h2
        (Iso.isIso_hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat z).mapIso
          ((ExtensionByZeroModules.toAb O).mapIso (exteriorPieceIsoSelfExt J hJ A ι hA _).symm)))
    · have hzS : z ∉ idealQuotientSupport Y J := fun hzS => hdn
        ((localGeneratorCount_eq d.koszulExact d.generated z hzd hzS).symm ▸
          localGeneratorCount_eq_of_mem_rankLocus hz hzS)
      obtain ⟨W, hzW, h1⟩ := (notMem_idealQuotientSupport_iff J z).mp hzS
      exact isIso_of_source_target_iso_zero _
        (isZero_stalk_of_isZero_jStar (isZero_jStar_extInto_of_one_mem J h1 n) z hzW).isoZero
        (isZero_stalk_of_isZero_jStar (isZero_jStar_restrictScalars_of_one_mem J h1 _) z
          hzW).isoZero
  exact (asIso ((jShriekAdjunction (rankLocus J n) O).counit.app E)).symm ≪≫
    (jShriek (rankLocus J n) O).mapIso (asIso ((jStar (rankLocus J n) O).map ψ))

/-- Two zero-differential complexes with isomorphic terms are isomorphic. -/
def zeroDifferentialComplexIsoOfIso {F G : ℤ → StructureSheafModules Y.sheaf}
    (e : ∀ n, F n ≅ G n) :
    CochainComplex.zeroDifferentialComplex F ≅ CochainComplex.zeroDifferentialComplex G :=
  HomologicalComplex.Hom.isoOfComponents e (fun i j _ => by simp)

/-- **[Stacks, Tag 0BQZ], granted the two local statements.** -/
theorem nonempty_derivedSheafHom_iso_of_local (hJ : IsKoszulRegularIdealSheaf Y J)
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u}
      (toRingCat (Opens.grothendieckTopology Y.carrier) (quotientRingSheaf.{u, u, u} J)))
    (ι : normalSheafQuotient J ⟶ A.piece 1)
    (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A ι)
    (hL1 : ∀ (d : KoszulPresentation Y J) (n : ℤ), n ≠ d.r →
      IsZero ((jStar d.U (structureSheaf Y.sheaf)).obj
        (extInto J (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)) n)))
    (hL2 : ∀ d : KoszulPresentation Y J,
      IsIso ((jStar d.U (structureSheaf Y.sheaf)).map (extQuotientMap J d.r))) :
    Nonempty (((derivedSheafHom Y.sheaf).obj (op (DerivedCategory.Q.obj
        ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj (cokernel J.ι))))).obj
        (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)))) ≅
      DerivedCategory.Q.obj
        (CochainComplex.zeroDifferentialComplex (rankExteriorTerm (J := J) A))) := by
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_zeroDifferentialComplex_homology_of_cover
    (structureSheaf Y.sheaf) (dualModel J) (fun d : KoszulPresentation Y J => d.U)
    (iSup_koszulPresentation_eq_top J hJ) (fun d => (d.r : ℤ))
    (fun d k hk => isZero_overFunctor_of_isZero_jStar (IsZero.of_iso (hL1 d k hk)
      ((jStar d.U (structureSheaf Y.sheaf)).mapIso
        (derivedSheafExtIsoDualModelHomology J k).symm)))
    (fun d d' k hdd' => isZero_overFunctor_dualModel_X J
      (one_mem_of_forall_notMem J (d.U ⊓ d'.U) fun y (hy : y ∈ d.U ⊓ d'.U) =>
        notMem_idealQuotientSupport_of_ne d.koszulExact d.generated d'.koszulExact d'.generated
          (fun h => hdd' (by rw [h])) y hy.1 hy.2) k)
  exact ⟨derivedSheafHomIsoDualModel J ≪≫ e ≪≫ DerivedCategory.Q.mapIso
    (zeroDifferentialComplexIsoOfIso fun n => (derivedSheafExtIsoDualModelHomology J n).symm ≪≫
      extIsoRankExteriorTermOfLocal J hJ A ι hA hL1 hL2 n)⟩

end Assembly

variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **[Stacks, Tag 0BQZ], the cohomology sheaves.** For a Koszul-regular sheaf of ideals `𝓘` and
an exterior algebra `A` of the normal sheaf over `O_X`, `𝓔xtⁿ_{O_Y}(O_X, O_Y)` is `⋀ⁿ𝒩` on the
rank-`n` locus, extended by zero. -/
def extIsoRankExteriorTerm (hJ : IsKoszulRegularIdealSheaf Y J)
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u}
      (toRingCat (Opens.grothendieckTopology Y.carrier) (quotientRingSheaf.{u, u, u} J)))
    (ι : normalSheafQuotient J ⟶ A.piece 1)
    (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A ι) (n : ℤ) :
    extInto J (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)) n ≅ rankExteriorTerm A n :=
  extIsoRankExteriorTermOfLocal J hJ A ι hA (isZero_jStar_extInto_of_ne J)
    (isIso_jStar_extQuotientMap J) n

/-- **[Stacks, Tag 0BQZ], for any exterior algebra of `𝒩`.** Let `Y` be a ringed space, `𝓘 ⊆ O_Y`
a Koszul-regular sheaf of ideals, `O_X = O_Y/𝓘`, and `A` with `ι : 𝒩 ⟶ A¹` an exterior algebra
over `O_X` of the normal sheaf `𝒩 = 𝓗om_{O_Y}(𝓘/𝓘², O_X)`. Then in `D(O_Y)`

`R𝓗om_{O_Y}(O_X, O_Y) ≅ ⋀^r 𝒩 [-r]`,

the right-hand side being the complex with zero differential whose degree-`n` term is `⋀ⁿ𝒩` on
the locus where `r = n` and zero elsewhere (`rankExteriorTerm`), `r` sending a point to the
minimal number of generators of `𝓘` needed near it (`localGeneratorCount`). -/
theorem nonempty_derivedSheafHom_iso_of_isExteriorAlgebra (hJ : IsKoszulRegularIdealSheaf Y J)
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u}
      (toRingCat (Opens.grothendieckTopology Y.carrier) (quotientRingSheaf.{u, u, u} J)))
    (ι : normalSheafQuotient J ⟶ A.piece 1)
    (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A ι) :
    Nonempty (((derivedSheafHom Y.sheaf).obj (op (DerivedCategory.Q.obj
        ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj (cokernel J.ι))))).obj
        (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)))) ≅
      DerivedCategory.Q.obj
        (CochainComplex.zeroDifferentialComplex (rankExteriorTerm (J := J) A))) :=
  nonempty_derivedSheafHom_iso_of_local J hJ A ι hA (isZero_jStar_extInto_of_ne J)
    (isIso_jStar_extQuotientMap J)

/-- **Stacks Project, Tag 0BQZ.** Let `Y` be a ringed space, `𝓘 ⊆ O_Y` a sheaf of ideals,
`O_X = O_Y/𝓘` and `𝒩 = 𝓗om_{O_Y}(𝓘/𝓘², O_X)`. If `𝓘` is Koszul-regular, then

`R𝓗om_{O_Y}(O_X, O_Y) ≅ ⋀^r 𝒩 [-r]`

in `D(O_Y)`, where `r : Y → ℕ` sends `y` to the minimal number of generators of `𝓘` needed in a
neighbourhood of `y` (`localGeneratorCount`). The right-hand side is the complex with zero
differential whose degree-`n` term is the `n`-th exterior power of `𝒩` over `O_X` (the exterior
algebra `SheafOfModules.algebras` of `normalSheafQuotient`) on the locus where `r = n`, extended
by zero (`rankExteriorTerm`): `r` is locally constant on the support of `O_X`, and every term of
the formula vanishes off it. See the module docstring for the codomain of `r`. -/
@[stacks 0BQZ]
theorem nonempty_derivedSheafHom_iso_rankExterior (hJ : IsKoszulRegularIdealSheaf Y J) :
    Nonempty (((derivedSheafHom Y.sheaf).obj (op (DerivedCategory.Q.obj
        ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj (cokernel J.ι))))).obj
        (DerivedCategory.Q.obj ((single (StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (structureSheaf Y.sheaf)))) ≅
      DerivedCategory.Q.obj (CochainComplex.zeroDifferentialComplex (rankExteriorTerm (J := J)
        (_root_.SheafOfModules.algebras (Opens.grothendieckTopology Y.carrier)
          (normalSheafQuotient J)).exterior))) :=
  nonempty_derivedSheafHom_iso_of_isExteriorAlgebra J hJ _ _
    (_root_.SheafOfModules.algebras (Opens.grothendieckTopology Y.carrier)
      (normalSheafQuotient J)).exterior_isExteriorAlgebra

end Stacks.AlgebraicGeometry.RegularIdealSheaf
