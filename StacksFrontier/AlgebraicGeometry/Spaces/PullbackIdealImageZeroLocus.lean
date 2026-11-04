module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealFiniteTypeOfQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealCoproductGenericIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType

/-!
# The inverse-image ideal: finiteness, its quotient and its zero locus

Let `g : X ⟶ X'` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `𝓘 ⊆ 𝒪_{X'}` be a sheaf of ideals on the small étale site of `X'`.  The
inverse-image ideal `g⁻¹𝓘 · 𝒪_X` is `AlgebraicGeometry.Space.pullbackIdealImage`, the image of
`g^*𝓘 ⟶ g^*𝒪_{X'} ⟶ 𝒪_X`.  **This file proves, for an arbitrary morphism `g`, that the
inverse-image ideal of a finite type quasi-coherent sheaf of ideals is again one, that the
quotient `𝒪_X / g⁻¹𝓘 · 𝒪_X` is the pullback `g^*(𝒪_{X'} / 𝓘)`, and that the zero locus of
`g⁻¹𝓘 · 𝒪_X` is the inverse image of the zero locus of `𝓘`.**  No hypothesis on `g` is used:
in particular `g` need not be representable.

## Main definitions

* `AlgebraicGeometry.Space.cokernelPullbackIdealImageIso` — **the comparison
  `𝒪_X / g⁻¹𝓘 · 𝒪_X ≅ g^*(𝒪_{X'} / 𝓘)`.**

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_cokernel_ι_eq_idealZeroLocus` — for an arbitrary sheaf
  of ideals `ℐ ⊆ 𝒪_X`, the support of `𝒪_X / ℐ` is the zero locus `|V(ℐ)|`.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_pullbackIdealImage` and
  `AlgebraicGeometry.Space.isFiniteTypeQuasicoherentIdeal_pullbackIdealImage` — **the inverse
  image of a sheaf of ideals of finite type is of finite type, and that of a finite type
  quasi-coherent sheaf of ideals is a finite type quasi-coherent sheaf of ideals.**  The
  quasi-coherent half is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_pullbackIdealImage`.
* `AlgebraicGeometry.Space.cokernel_π_cokernelPullbackIdealImageIso_hom` and
  `AlgebraicGeometry.Space.structureModulePullbackMap_cokernel_π_cokernelPullbackIdealImageIso_hom`
  — the comparison is compatible with the projections from `𝒪_X` and from `g^*𝒪_{X'}`.
* `AlgebraicGeometry.Space.idealZeroLocus_pullbackIdealImage` — **for `𝓘` quasi-coherent,
  `|V(g⁻¹𝓘 · 𝒪_X)| = |g|⁻¹ |V(𝓘)|`.**

## Implementation notes

The corestriction `AlgebraicGeometry.Space.toPullbackIdealImage` of `g^*𝓘 ⟶ 𝒪_X` to the
inverse-image ideal is an epimorphism (`AlgebraicGeometry.Space.epi_toPullbackIdealImage`), the
ideal being the sheaf of sections lying locally in the pointwise image.  So finite type is
inherited from `g^*𝓘`, which is of finite type by Stacks 03DO, and the cokernel of the inclusion
of the ideal is the cokernel of `g^*𝓘 ⟶ 𝒪_X`.

The zero locus is computed through supports.  The support of `𝒪_X / ℐ` is `|V(ℐ)|` for every
sheaf of ideals: over a chart on which `ℐ` is the unit ideal every section of the quotient is
locally the image of a section of `ℐ`, hence zero; conversely, at a point off the support the
quotient vanishes on an étale neighbourhood
(`AlgebraicGeometry.Space.exists_zero_neighborhood_of_isFiniteTypeOnSite`, the quotient being a
quotient of `𝒪_X`), so the unit section dies in the quotient there and lies in `ℐ`
(`AlgebraicGeometry.Space.cokernel_π_app_eq_zero_iff`).  The zero locus of the inverse-image
ideal is then the support of `g^*(𝒪_{X'} / 𝓘)`, which is the inverse image of the support of
`𝒪_{X'} / 𝓘` by Stacks 07TZ (`AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq`); that
needs `𝒪_{X'} / 𝓘` quasi-coherent and of finite type, which is why `𝓘` is assumed
quasi-coherent (finite type of the quotient is automatic).

The second `CategoryTheory.Abelian` instance
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` on sheaves of modules is switched off in
this file: with it in scope the cokernels below are stuck at an undetermined universe.

## References

* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 0GV2](https://stacks.math.columbia.edu/tag/0GV2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The zero locus of a sheaf of ideals is the support of the quotient -/

/-- **The support of `𝒪_X / ℐ` is the zero locus of `ℐ`**, for an arbitrary sheaf of ideals
`ℐ ⊆ 𝒪_X` on an algebraic space.

Off the zero locus the quotient vanishes over a chart on which `ℐ` is the unit ideal, the
inclusion `ℐ ⊆ 𝒪_X` being surjective there
(`AlgebraicGeometry.Space.supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective`).  Off the
support, the
quotient — a quotient of `𝒪_X`, hence of finite type — vanishes over an étale neighbourhood of a
geometric point over the given point, so the unit section of `𝒪_X` dies in the quotient there,
that is, lies in `ℐ`, and `ℐ` is the unit ideal on that neighbourhood. -/
theorem supportOfSheaf_cokernel_ι_eq_idealZeroLocus (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj
          (cokernel I.ι)) =
      idealZeroLocus B S hS X I := by
  refine Set.Subset.antisymm
    (supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective B S hS X I I.ι fun W hW s =>
      ⟨⟨s, hW.ge Submodule.mem_top⟩, rfl⟩) fun x hx => ?_
  by_contra hxs
  obtain ⟨p, hpx⟩ := exists_geometricRepresentative B S hS X.1 x
  have hpzero : Subsingleton (stalkSet p
      (((SheafOfModules.toSheaf _).obj (cokernel I.ι)).obj ⋙ forget AddCommGrpCat)) := by
    by_contra h
    exact hxs ⟨p, hpx, h⟩
  obtain ⟨U, hU⟩ := @exists_zero_neighborhood_of_isFiniteTypeOnSite B S hS X.1 X.2 _ _
    (isFiniteTypeOnSite_unit_structureRingSheaf B S hS X) (cokernel.π I.ι)
    (Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi (cokernel.π I.ι)) p hpzero
  have hsub := hU U.chart (𝟙 _)
  have h1 : SheafOfModules.unitOf (1 : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op U.chart))) ∈ I.obj (op U.chart) :=
    (cokernel_π_app_eq_zero_iff B S hS X.1 X.2 I (op U.chart) _).1 (@Subsingleton.elim _ hsub _ _)
  have htop : I.obj (op U.chart) = ⊤ := by
    refine eq_top_iff.2 fun s _ ↦ ?_
    have h3 := Submodule.smul_mem (I.obj (op U.chart)) (SheafOfModules.unitVal s) h1
    rwa [show SheafOfModules.unitVal s • SheafOfModules.unitOf
        (1 : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op U.chart))) = s from
      mul_one (SheafOfModules.unitVal s)] at h3
  exact (mem_idealZeroLocus_iff B S hS X I x).1 hx U.chart htop
    ⟨(neighborhoodPoint B S hS X.1 U).image, (neighborhoodPoint_image B S hS X.1 U).trans hpx⟩

/-! ### Finiteness of the inverse-image ideal -/

variable {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    (𝓘 : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X'.1 X'.2).O))).Submodule)

/-- **The inverse image of a sheaf of ideals of finite type is of finite type**: it is a quotient
of `g^*𝓘`, which is of finite type by Stacks 03DO. -/
theorem isFiniteTypeOnSite_pullbackIdealImage
    (h : SheafOfModules.IsFiniteTypeOnSite 𝓘.toSheafOfModules) :
    SheafOfModules.IsFiniteTypeOnSite (pullbackIdealImage B S hS g 𝓘).toSheafOfModules :=
  have := epi_toPullbackIdealImage B S hS g 𝓘
  isFiniteTypeOnSite_of_epi B S hS X.1 X.2 (toPullbackIdealImage B S hS g 𝓘)
    (isFiniteTypeOnSite_modulePullback B S hS g 𝓘.toSheafOfModules h)

/-- **The inverse image of a finite type quasi-coherent sheaf of ideals is a finite type
quasi-coherent sheaf of ideals**, along an arbitrary morphism `g : X ⟶ X'` of algebraic
spaces. -/
theorem isFiniteTypeQuasicoherentIdeal_pullbackIdealImage
    (h : IsFiniteTypeQuasicoherentIdeal B S hS X' 𝓘) :
    IsFiniteTypeQuasicoherentIdeal B S hS X (pullbackIdealImage B S hS g 𝓘) :=
  ⟨isQuasicoherentOnSite_pullbackIdealImage B S hS g 𝓘 h.1,
    isFiniteTypeOnSite_pullbackIdealImage B S hS g 𝓘 h.2⟩

/-! ### The quotient by the inverse-image ideal -/

/-- The inverse-image morphism `g^*𝓘 ⟶ 𝒪_X` is the inverse image of the inclusion `𝓘 ⊆ 𝒪_{X'}`
followed by the identification `g^*𝒪_{X'} ≅ 𝒪_X` of Stacks 03LU, the canonical map
`AlgebraicGeometry.Space.structureModulePullbackMap` being the forward map of that
identification by
`AlgebraicGeometry.Space.structureModulePullbackMap_eq_modulePullbackUnitIso_hom`. -/
theorem pullbackIdealHom_eq_map_comp_modulePullbackUnitIso_hom :
    pullbackIdealHom B S hS g 𝓘 =
      (modulePullback B S hS g).map 𝓘.ι ≫ (modulePullbackUnitIso B S hS g).hom :=
  congrArg ((modulePullback B S hS g).map 𝓘.ι ≫ ·)
    (structureModulePullbackMap_eq_modulePullbackUnitIso_hom B S hS g)

/-- **The quotient by the inverse-image ideal is the pullback of the quotient**:
`𝒪_X / g⁻¹𝓘 · 𝒪_X ≅ g^*(𝒪_{X'} / 𝓘)`, cokernels being taken in the abelian category of
`𝒪_X`-modules on the small étale site.

The cokernel of the inclusion of the image is the cokernel of `g^*𝓘 ⟶ 𝒪_X`, the corestriction
to the image being an epimorphism; that morphism is `g^*(𝓘 ⊆ 𝒪_{X'})` followed by the
isomorphism `g^*𝒪_{X'} ≅ 𝒪_X`, which does not change the cokernel; and the pullback of
Stacks 03LU is a left adjoint, so it carries the cokernel of `𝓘 ⊆ 𝒪_{X'}` to the cokernel of
`g^*(𝓘 ⊆ 𝒪_{X'})`. -/
def cokernelPullbackIdealImageIso :
    cokernel (pullbackIdealImage B S hS g 𝓘).ι ≅
      (modulePullback B S hS g).obj (cokernel 𝓘.ι) :=
  haveI := epi_toPullbackIdealImage B S hS g 𝓘
  haveI := (modulePullbackAdjunction B S hS g).isLeftAdjoint
  (cokernelEpiComp (toPullbackIdealImage B S hS g 𝓘) (pullbackIdealImage B S hS g 𝓘).ι).symm ≪≫
    cokernelIsoOfEq ((toPullbackIdealImage_ι B S hS g 𝓘).trans
      (pullbackIdealHom_eq_map_comp_modulePullbackUnitIso_hom B S hS g 𝓘)) ≪≫
    cokernelCompIsIso ((modulePullback B S hS g).map 𝓘.ι) (modulePullbackUnitIso B S hS g).hom ≪≫
    (PreservesCokernel.iso (modulePullback B S hS g) 𝓘.ι).symm

/-- **The comparison of quotients is compatible with the projections**: the projection
`𝒪_X ⟶ 𝒪_X / g⁻¹𝓘 · 𝒪_X` followed by `AlgebraicGeometry.Space.cokernelPullbackIdealImageIso`
is the inverse of the identification `g^*𝒪_{X'} ≅ 𝒪_X` followed by the pullback of the
projection `𝒪_{X'} ⟶ 𝒪_{X'} / 𝓘`. -/
@[reassoc]
theorem cokernel_π_cokernelPullbackIdealImageIso_hom :
    cokernel.π (pullbackIdealImage B S hS g 𝓘).ι ≫
        (cokernelPullbackIdealImageIso B S hS g 𝓘).hom =
      (modulePullbackUnitIso B S hS g).inv ≫ (modulePullback B S hS g).map (cokernel.π 𝓘.ι) := by
  have := epi_toPullbackIdealImage B S hS g 𝓘
  have := (modulePullbackAdjunction B S hS g).isLeftAdjoint
  simp only [cokernelPullbackIdealImageIso, Iso.trans_hom, Iso.symm_hom, PreservesCokernel.iso_inv,
    cokernelEpiComp_inv, cokernelCompIsIso_hom, cokernel.π_desc_assoc]
  rw [π_comp_cokernelIsoOfEq_hom_assoc, cokernel.π_desc_assoc, IsIso.Iso.inv_hom,
    Category.assoc, π_comp_cokernelComparison]

/-- The same compatibility read through the canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` of Stacks 03G8:
the square from `g^*𝒪_{X'}` to `g^*(𝒪_{X'} / 𝓘)` through `𝒪_X / g⁻¹𝓘 · 𝒪_X` commutes. -/
theorem structureModulePullbackMap_cokernel_π_cokernelPullbackIdealImageIso_hom :
    structureModulePullbackMap B S hS g ≫ cokernel.π (pullbackIdealImage B S hS g 𝓘).ι ≫
        (cokernelPullbackIdealImageIso B S hS g 𝓘).hom =
      (modulePullback B S hS g).map (cokernel.π 𝓘.ι) :=
  (congrArg (fun m => m ≫ cokernel.π (pullbackIdealImage B S hS g 𝓘).ι ≫
      (cokernelPullbackIdealImageIso B S hS g 𝓘).hom)
    (structureModulePullbackMap_eq_modulePullbackUnitIso_hom B S hS g)).trans
    ((congrArg ((modulePullbackUnitIso B S hS g).hom ≫ ·)
      (cokernel_π_cokernelPullbackIdealImageIso_hom B S hS g 𝓘)).trans
      ((modulePullbackUnitIso B S hS g).hom_inv_id_assoc _))

/-! ### The zero locus of the inverse-image ideal -/

/-- **The zero locus of the inverse-image ideal is the inverse image of the zero locus**:
for a quasi-coherent sheaf of ideals `𝓘 ⊆ 𝒪_{X'}` and an arbitrary morphism `g : X ⟶ X'` of
algebraic spaces, `|V(g⁻¹𝓘 · 𝒪_X)| = |g|⁻¹ |V(𝓘)|`.

Both zero loci are supports of quotients
(`AlgebraicGeometry.Space.supportOfSheaf_cokernel_ι_eq_idealZeroLocus`), the quotient by the
inverse-image ideal is `g^*(𝒪_{X'} / 𝓘)`
(`AlgebraicGeometry.Space.cokernelPullbackIdealImageIso`), and the support of the pullback of the
finite type quasi-coherent module `𝒪_{X'} / 𝓘` is the inverse image of its support by
Stacks 07TZ. -/
theorem idealZeroLocus_pullbackIdealImage (h : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) :
    idealZeroLocus B S hS X (pullbackIdealImage B S hS g 𝓘) =
      pointsMap B S hS X.1 g.hom ⁻¹' idealZeroLocus B S hS X' 𝓘 := by
  have hO : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X'.1 X'.2).O))).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ isCartesianOnAffineCharts_unit
  have hqc : (cokernel 𝓘.ι).IsQuasicoherentOnSite :=
    have := isClosedUnderCokernels_quasicoherentSheaves B S hS X'.1 X'.2
    ObjectProperty.prop_cokernel _ 𝓘.ι h hO
  have hft : SheafOfModules.IsFiniteTypeOnSite (cokernel 𝓘.ι) :=
    isFiniteTypeOnSite_of_epi B S hS X'.1 X'.2 (cokernel.π 𝓘.ι)
      (isFiniteTypeOnSite_unit_structureRingSheaf B S hS X')
  exact (supportOfSheaf_cokernel_ι_eq_idealZeroLocus B S hS X
      (pullbackIdealImage B S hS g 𝓘)).symm.trans
    ((supportOfSheaf_eq_of_iso B S hS X (cokernelPullbackIdealImageIso B S hS g 𝓘)).trans
      ((supportOfSheaf_modulePullback_eq B S hS g _ hqc hft).trans
        (congrArg (pointsMap B S hS X.1 g.hom ⁻¹' ·)
          (supportOfSheaf_cokernel_ι_eq_idealZeroLocus B S hS X' 𝓘))))

end AlgebraicGeometry.Space

end
