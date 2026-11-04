module

public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Quotient
public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.GradedIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.Quotient

/-!
# The graded ring of sections of a graded quotient, over an affine open of the base

Work in Situation 01NN: a scheme `S`, a quasi-coherent graded `𝒪_S`-algebra `𝒜` in the
sheaf-level form `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, and a graded
ideal `ℐ ⊆ 𝒜` with quasi-coherent pieces. Over an **affine** open `U` of the base, this file
identifies the graded ring of sections of the quotient `𝒜/ℐ` with the quotient of the graded ring
`Γ(U, 𝒜)` by the homogeneous ideal of local sections of `ℐ`:

    Γ(U, 𝒜/ℐ) = Γ(U, 𝒜) / ℐ(U).

Both sides are graded rings — the left by
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.grading`, the right by
`Stacks.HomogeneousIdeal.quotientGrading`, which is the grading the absolute statements about a
closed subscheme of a `Proj` are written at — and the identification is an isomorphism of graded
rings, exhibited as a pair of mutually inverse graded ring homomorphisms.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionIdeal`: the kernel of
  `Γ(U, 𝒜) ⟶ Γ(U, 𝒜/ℐ)`, as a **homogeneous** ideal of `Γ(U, 𝒜)`. Over any open its elements are
  exactly the sections all of whose homogeneous components are local sections of `ℐ`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionQuotEquiv`: the ring isomorphism
  `Γ(U, 𝒜)/ℐ(U) ≅ Γ(U, 𝒜/ℐ)` over an affine open of the base.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotGradedHom` and `quotGradedInv`: that
  isomorphism and its inverse as homomorphisms of **graded** rings.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.chartIsoProjSectionQuotient`: the induced
  isomorphism `Proj Γ(U, 𝒜/ℐ) ≅ Proj (Γ(U, 𝒜)/ℐ(U))` of the two chart models.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.isHomogeneous_ker_sectionRingHom_quotHom`:
  the kernel of the quotient homomorphism on the graded ring of sections over an arbitrary open is
  a homogeneous ideal.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotGradedHom_quotientMk` and
  `quotGradedHom_comp_quotientMk`: the identification is the canonical one — it carries the class
  of a section of `𝒜` to the image of that section in `𝒜/ℐ`. This is what pins the isomorphism to
  the two quotient maps rather than leaving it abstract.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.chartMap_eq_comp_mapHomOfTop_quotientMk`: the
  chart map of `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.projQuotientHom` over an affine
  open of the base is, through that isomorphism, the morphism of projective spectra induced by the
  quotient map `Γ(U, 𝒜) ⟶ Γ(U, 𝒜)/ℐ(U)` — the shape in which the absolute statements of Tag 0801
  are written.

## Implementation notes

The two halves of the identification are already in the tree and are consumed rather than
reproved: the kernel is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionHom_quotHom_eq_zero_iff`, which holds
over an arbitrary open of the base because the sections of the degreewise cokernel over an open
have exactly `ℐ` as the kernel of the projection, with no sheafification; and the surjectivity is
`Stacks.AlgebraicGeometry.ProjBundleSurjection.surjective_sectionHom` applied to
`surjectiveOnAffineSections_quotHom`, which is where affineness of `U` enters and is the only
place it does.

Homogeneity of the kernel is where the degreewise shape of `sectionHom_quotHom_eq_zero_iff`
pays: a section lies in the kernel exactly when each of its components is a local section of
`ℐ`, and that condition is inherited by each component. The homogeneous components of a section
of `⨁_{n ≥ 0} Γ(𝒜_n, U)` are computed by `coe_decompose_grading`, which identifies
`DirectSum.decompose` for the internal grading `grading U` with the external direct-sum
coordinates; `grading U n` is the range of the `n`-th inclusion, so the two agree, but not by
`rfl`.

The quotient map is taken as `Stacks.HomogeneousIdeal.quotientMk` of the `AddSubgroup`-valued
quotient grading rather than `Stacks.RingTheory.HomogeneousQuotient.quotientMk`, because
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.grading` is `AddSubgroup`-valued:
the degree-zero piece of a `SheafGradedAlgebra` is an arbitrary quasi-coherent module and the
section ring is not presented as an algebra over it.

There is no bundled type of graded ring isomorphisms in Mathlib or in this repository, so the
identification is given as a pair of mutually inverse `GradedRingHom`s, which is the form
`Stacks.AlgebraicGeometry.ProjPolynomialSections.projIsoOfGradedSections` consumes.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)

## Not done here

No Stacks tag is claimed **here**; Tag 0801 is proved in the sibling `Identification.lean`, on
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_twistKer`, and this
file is one of its inputs. What this file supplies is the second of
the two points listed as open in the `Not done here` section of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Quotient.lean`: the graded identification
of `Γ(U, 𝒜/ℐ)` with `Γ(U, 𝒜)/ℐ(U)` that the absolute chart comparison
`Stacks.ProjQuotientFiniteCover.app_awayMk_eq_zero_iff_of_cover` is stated at.

The first point is no longer open either: the graded ideal `ℐ` cut out by a closed subscheme
`i : Z ⟶ Proj_S(𝒜)` is `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal` of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/TwistRestriction.lean`. Everything in this
file is about an ideal already in hand, so it applies to that one.

What Tag 0801 needs beyond this file, and nothing here touches, is the comparison of the two ideals
of `Γ(U, 𝒜)`. The ideal appearing here is the kernel of the quotient homomorphism, i.e. `ℐ(U)`, and
**not** the absolute ideal of equations
`Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme` of a closed subscheme of
the chart. That identification is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionIdeal_eq_idealOfClosedSubscheme` of
`ChartComparison.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.HomogeneousIdeal

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S)

/-! ### The homogeneous components of a section of the graded ring of sections -/

/-- **The internal and the external grading of the section ring agree.** The degree-`i`
homogeneous component of a section of `⨁_{n ≥ 0} Γ(𝒜_n, U)`, computed for the internal grading
`grading U`, is the `i`-th external coordinate pushed back into the direct sum. -/
theorem coe_decompose_grading (U : S.Opens) (x : 𝒜.sectionRing U) (i : ℕ) :
    ((DirectSum.decompose (𝒜.grading U) x i : 𝒜.grading U i) : 𝒜.sectionRing U) =
      DirectSum.of (𝒜.sectionPieces U) i (x i) := by
  induction x using DirectSum.induction_on with
  | zero => rw [DirectSum.decompose_zero, DFinsupp.zero_apply, DFinsupp.zero_apply, map_zero]; rfl
  | of m y =>
    rcases eq_or_ne i m with rfl | hne
    · rw [DirectSum.decompose_of_mem_same _ (𝒜.of_mem_grading U y), DirectSum.of_eq_same]
    · rw [DirectSum.decompose_of_mem_ne _ (𝒜.of_mem_grading U y) (Ne.symm hne),
        DirectSum.of_eq_of_ne m i y hne, map_zero]
  | add a b ha hb =>
    rw [DirectSum.decompose_add, DFinsupp.add_apply, AddMemClass.coe_add, ha, hb,
      DFinsupp.add_apply, map_add]

variable (ℐ : QcohGradedIdeal 𝒜)

/-! ### The homogeneous ideal of local sections of `ℐ` -/

/-- Membership in the kernel of the quotient homomorphism on sections, componentwise. -/
private theorem mem_ker_sectionRingHom_quotHom_iff (U : S.Opens) (x : 𝒜.sectionRing U) :
    x ∈ RingHom.ker ((quotHom 𝒜 ℐ).sectionRingHom U) ↔
      ∀ n : ℕ, x n ∈ (ℐ.piece (n : ℤ)).toSubmodule.obj (op U) :=
  RingHom.mem_ker.trans (sectionHom_quotHom_eq_zero_iff 𝒜 ℐ U x)

/-- **The kernel of the quotient homomorphism on the graded ring of sections is a homogeneous
ideal.** A section lies in it exactly when every one of its homogeneous components is a local
section of `ℐ`, by
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionHom_quotHom_eq_zero_iff`, and that
condition is visibly inherited by each component. -/
theorem isHomogeneous_ker_sectionRingHom_quotHom (U : S.Opens) :
    (RingHom.ker ((quotHom 𝒜 ℐ).sectionRingHom U)).IsHomogeneous (𝒜.grading U) := by
  intro i x hx
  rw [mem_ker_sectionRingHom_quotHom_iff] at hx ⊢
  intro n
  rw [coe_decompose_grading 𝒜 U x i]
  rcases eq_or_ne n i with rfl | hne
  · rw [DirectSum.of_eq_same n (x n)]
    exact hx n
  · rw [DirectSum.of_eq_of_ne i n (x i) hne]
    exact Submodule.zero_mem _

/-- **`ℐ(U)`, the homogeneous ideal of local sections of the graded ideal over an open of the
base**: the kernel of `Γ(U, 𝒜) ⟶ Γ(U, 𝒜/ℐ)`. -/
def sectionIdeal (U : S.Opens) : HomogeneousIdeal (𝒜.grading U) :=
  ⟨RingHom.ker ((quotHom 𝒜 ℐ).sectionRingHom U),
    isHomogeneous_ker_sectionRingHom_quotHom 𝒜 ℐ U⟩

/-- A section lies in `ℐ(U)` exactly when each of its homogeneous components is a local section of
the corresponding piece of `ℐ`. -/
theorem mem_sectionIdeal_iff (U : S.Opens) (x : 𝒜.sectionRing U) :
    x ∈ (sectionIdeal 𝒜 ℐ U).toIdeal ↔
      ∀ n : ℕ, x n ∈ (ℐ.piece (n : ℤ)).toSubmodule.obj (op U) :=
  mem_ker_sectionRingHom_quotHom_iff 𝒜 ℐ U x

/-! ### The identification of the two quotients -/

/-- The quotient of the graded ring of sections by `ℐ(U)`, mapped to the graded ring of sections
of `𝒜/ℐ`: the quotient homomorphism factored through its own kernel. -/
def quotToSection (U : S.Opens) :
    𝒜.sectionRing U ⧸ (sectionIdeal 𝒜 ℐ U).toIdeal →+* (quotAlgebra 𝒜 ℐ).sectionRing U :=
  Ideal.Quotient.lift _ ((quotHom 𝒜 ℐ).sectionRingHom U) fun _ ha => RingHom.mem_ker.mp ha

/-- `quotToSection` sends the class of a section to its image under the quotient homomorphism. -/
@[simp]
theorem quotToSection_mk (U : S.Opens) (x : 𝒜.sectionRing U) :
    quotToSection 𝒜 ℐ U (Ideal.Quotient.mk (sectionIdeal 𝒜 ℐ U).toIdeal x) =
      (quotHom 𝒜 ℐ).sectionRingHom U x :=
  rfl

/-- Over an affine open of the base, `quotToSection` is bijective. -/
theorem bijective_quotToSection (U : S.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (quotToSection 𝒜 ℐ U) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun b => ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.Quotient.eq_zero_iff_mem.2 (RingHom.mem_ker.mpr hz)
  · obtain ⟨x, hx⟩ :=
      ProjBundleSurjection.surjective_sectionHom (surjectiveOnAffineSections_quotHom 𝒜 ℐ) hU b
    exact ⟨Ideal.Quotient.mk _ x, hx⟩

/-- **`Γ(U, 𝒜)/ℐ(U) ≅ Γ(U, 𝒜/ℐ)` over an affine open of the base.** The quotient homomorphism
`Γ(U, 𝒜) ⟶ Γ(U, 𝒜/ℐ)` is surjective over an affine open — it is an epimorphism of quasi-coherent
modules in every degree — and its kernel is `ℐ(U)` by `mem_sectionIdeal_iff`. -/
def sectionQuotEquiv (U : S.Opens) (hU : IsAffineOpen U) :
    𝒜.sectionRing U ⧸ (sectionIdeal 𝒜 ℐ U).toIdeal ≃+* (quotAlgebra 𝒜 ℐ).sectionRing U :=
  RingEquiv.ofBijective _ (bijective_quotToSection 𝒜 ℐ U hU)

/-- `sectionQuotEquiv` sends the class of a section to its image under the quotient
homomorphism. -/
@[simp]
theorem sectionQuotEquiv_mk (U : S.Opens) (hU : IsAffineOpen U) (x : 𝒜.sectionRing U) :
    sectionQuotEquiv 𝒜 ℐ U hU (Ideal.Quotient.mk (sectionIdeal 𝒜 ℐ U).toIdeal x) =
      (quotHom 𝒜 ℐ).sectionRingHom U x :=
  rfl

/-- **The identification is one of graded rings.** The class of a homogeneous section of `𝒜` of
degree `i` is carried to its image in `(𝒜/ℐ)_i`. -/
def quotGradedHom (U : S.Opens) (hU : IsAffineOpen U) :
    quotientGrading (sectionIdeal 𝒜 ℐ U) →+*ᵍ (quotAlgebra 𝒜 ℐ).grading U where
  __ := (sectionQuotEquiv 𝒜 ℐ U hU).toRingHom
  map_mem := by
    rintro i z hz
    obtain ⟨a, ha, rfl⟩ := (mem_quotientGrading_iff (sectionIdeal 𝒜 ℐ U) z).mp hz
    exact ((quotHom 𝒜 ℐ).sectionHom U).map_mem ha

/-- `quotGradedHom` sends the class of a section to its image under the quotient homomorphism. -/
@[simp]
theorem quotGradedHom_quotientMk (U : S.Opens) (hU : IsAffineOpen U) (x : 𝒜.sectionRing U) :
    quotGradedHom 𝒜 ℐ U hU (quotientMk (sectionIdeal 𝒜 ℐ U) x) =
      (quotHom 𝒜 ℐ).sectionHom U x :=
  rfl

/-- The inverse identification, again as a homomorphism of graded rings: a homogeneous section of
`𝒜/ℐ` of degree `i` over an affine open lifts to one of `𝒜` of the same degree. -/
def quotGradedInv (U : S.Opens) (hU : IsAffineOpen U) :
    (quotAlgebra 𝒜 ℐ).grading U →+*ᵍ quotientGrading (sectionIdeal 𝒜 ℐ U) where
  __ := (sectionQuotEquiv 𝒜 ℐ U hU).symm.toRingHom
  map_mem := by
    rintro i b hb
    obtain ⟨y, rfl⟩ := ((quotAlgebra 𝒜 ℐ).mem_grading_iff U b).mp hb
    obtain ⟨a, ha⟩ := surjectiveOnAffineSections_quotHom 𝒜 ℐ U hU i y
    change (sectionQuotEquiv 𝒜 ℐ U hU).symm
        (DirectSum.of ((quotAlgebra 𝒜 ℐ).sectionPieces U) i y) ∈
      quotientGrading (sectionIdeal 𝒜 ℐ U) i
    have hval : sectionQuotEquiv 𝒜 ℐ U hU
        (Ideal.Quotient.mk (sectionIdeal 𝒜 ℐ U).toIdeal
          (DirectSum.of (𝒜.sectionPieces U) i a)) =
        DirectSum.of ((quotAlgebra 𝒜 ℐ).sectionPieces U) i y := by
      rw [sectionQuotEquiv_mk, (quotHom 𝒜 ℐ).sectionRingHom_of, ha]
    rw [← hval, (sectionQuotEquiv 𝒜 ℐ U hU).symm_apply_apply]
    exact mk_mem_quotientGrading (sectionIdeal 𝒜 ℐ U) (𝒜.of_mem_grading U a)

/-- `quotGradedInv` is a right inverse of `quotGradedHom`. -/
theorem quotGradedHom_quotGradedInv (U : S.Opens) (hU : IsAffineOpen U)
    (b : (quotAlgebra 𝒜 ℐ).sectionRing U) :
    quotGradedHom 𝒜 ℐ U hU (quotGradedInv 𝒜 ℐ U hU b) = b :=
  (sectionQuotEquiv 𝒜 ℐ U hU).apply_symm_apply b

/-- `quotGradedInv` is a left inverse of `quotGradedHom`. -/
theorem quotGradedInv_quotGradedHom (U : S.Opens) (hU : IsAffineOpen U)
    (z : 𝒜.sectionRing U ⧸ (sectionIdeal 𝒜 ℐ U).toIdeal) :
    quotGradedInv 𝒜 ℐ U hU (quotGradedHom 𝒜 ℐ U hU z) = z :=
  (sectionQuotEquiv 𝒜 ℐ U hU).symm_apply_apply z

/-- Over an affine open of the base, `quotGradedHom` is surjective. -/
theorem surjective_quotGradedHom (U : S.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (quotGradedHom 𝒜 ℐ U hU) :=
  (sectionQuotEquiv 𝒜 ℐ U hU).surjective

/-- **The identification is the canonical one, as graded ring homomorphisms.** The quotient
homomorphism on the graded rings of sections factors as the quotient by `ℐ(U)` followed by the
identification. -/
theorem quotGradedHom_comp_quotientMk (U : S.Opens) (hU : IsAffineOpen U) :
    (quotGradedHom 𝒜 ℐ U hU).comp (quotientMk (sectionIdeal 𝒜 ℐ U)) =
      (quotHom 𝒜 ℐ).sectionHom U :=
  GradedRingHom.ext fun x => quotGradedHom_quotientMk 𝒜 ℐ U hU x

/-! ### The two chart models of the quotient -/

/-- **The two chart models of the graded quotient agree.** Over an affine open `U` of the base,
`Proj` of the graded ring of sections of `𝒜/ℐ` is `Proj` of the quotient of the graded ring
`Γ(U, 𝒜)` by `ℐ(U)`, the model the absolute statements are written at. -/
def chartIsoProjSectionQuotient (U : S.Opens) (hU : IsAffineOpen U) :
    AlgebraicGeometry.Proj ((quotAlgebra 𝒜 ℐ).grading U) ≅
      AlgebraicGeometry.Proj (quotientGrading (sectionIdeal 𝒜 ℐ U)) :=
  ProjPolynomialSections.projIsoOfGradedSections _ _ (quotGradedHom 𝒜 ℐ U hU)
    (quotGradedInv 𝒜 ℐ U hU) (quotGradedHom_quotGradedInv 𝒜 ℐ U hU)
    (quotGradedInv_quotGradedHom 𝒜 ℐ U hU)

/-- **The chart map of `Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)` over an affine open of the base is, through the
identification of the two chart models, the morphism induced by the quotient of the graded ring of
sections by `ℐ(U)`.** This is the shape the absolute statements about a closed subscheme of a
`Proj` are written at — compare
`Stacks.ClosedSubschemeProjQuotient.ambientHom`, which is `mapHomOfTop` of the quotient map by a
homogeneous ideal. -/
theorem chartMap_eq_comp_mapHomOfTop_quotientMk (U : S.Opens) (hU : IsAffineOpen U) :
    ProjBundleSurjection.chartMap (surjectiveOnAffineSections_quotHom 𝒜 ℐ) U hU =
      (chartIsoProjSectionQuotient 𝒜 ℐ U hU).hom ≫
        mapHomOfTop (𝒜.grading U) (quotientGrading (sectionIdeal 𝒜 ℐ U))
          (quotientMk (sectionIdeal 𝒜 ℐ U))
          (mapDomain_eq_top_of_surjective _ _ _
            (surjective_quotientMk (sectionIdeal 𝒜 ℐ U))) := by
  have hdc : mapDomain (𝒜.grading U) ((quotAlgebra 𝒜 ℐ).grading U)
      ((quotGradedHom 𝒜 ℐ U hU).comp (quotientMk (sectionIdeal 𝒜 ℐ U))) = ⊤ :=
    mapDomain_eq_top_of_surjective _ _ _
      ((surjective_quotGradedHom 𝒜 ℐ U hU).comp (surjective_quotientMk (sectionIdeal 𝒜 ℐ U)))
  have h1 : ProjBundleSurjection.chartMap (surjectiveOnAffineSections_quotHom 𝒜 ℐ) U hU =
      mapHomOfTop (𝒜.grading U) ((quotAlgebra 𝒜 ℐ).grading U)
        ((quotGradedHom 𝒜 ℐ U hU).comp (quotientMk (sectionIdeal 𝒜 ℐ U))) hdc :=
    ProjPolynomialSections.mapHomOfTop_congr _ _
      (quotGradedHom_comp_quotientMk 𝒜 ℐ U hU).symm _ _
  rw [h1, ProjBundleSurjection.mapHomOfTop_comp _ _ _ _ _
    (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
      (surjective_quotientMk (sectionIdeal 𝒜 ℐ U)))
    (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
      (surjective_quotGradedHom 𝒜 ℐ U hU))
    (mapDomain_eq_top_of_surjective _ _ _ (surjective_quotientMk (sectionIdeal 𝒜 ℐ U)))
    (mapDomain_eq_top_of_surjective _ _ _ (surjective_quotGradedHom 𝒜 ℐ U hU)) hdc]
  rfl

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
