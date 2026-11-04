module

public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.GradedIso
public import StacksFrontier.AlgebraicGeometry.SymTwistChart.Basic

/-!
# `Proj` of the chart comparison of a twisted symmetric algebra

`StacksFrontier/AlgebraicGeometry/SymTwistChart/Basic.lean` identifies the graded rings of sections
of `Sym(E)` and of `Sym(E ⊗ L)` over an affine open `U` on which a trivialization `e` of `L` has
been given. This file reads that identification as an isomorphism of **graded** rings and takes
`Proj` of it, obtaining

`Proj Γ(U, Sym(E ⊗ L)) ≅ Proj Γ(U, Sym(E))`,

an isomorphism over `Spec Γ(X, U)` and hence over `X`: the chart of the projective bundle of
`E ⊗ L` over `U` is the chart of the projective bundle of `E` over `U`.

This is the chart half of [Stacks, Tag 02NC] over a base scheme. That the chart isomorphism does
not depend on `e`, and that it is natural in `U`, are the two further facts the glueing consumes;
they are proved in `StacksFrontier/AlgebraicGeometry/SymTwistChart/Compare.lean`.

## Main definitions

* `Stacks.SymTwistChart.chartGradedHom` and `chartGradedInv`: the comparison as a pair of
  mutually inverse graded ring homomorphisms.
* `Stacks.SymTwistChart.chartProjIso`: **the isomorphism of the two charts.**

## Main results

* `Stacks.SymTwistChart.chartRingEquiv_strHom`: the comparison is a `Γ(X, U)`-algebra map, that
  is, it carries the structure map of one graded section ring to that of the other.
* `Stacks.SymTwistChart.chartProjIso_hom_toSpecZero` and
  `Stacks.SymTwistChart.strZero_comp_zeroHom_chartGradedHom`: **the comparison is a morphism over
  the base.** The first is the commuting square of [Stacks, Tag 01NO] for the comparison, the
  second says its degree-zero part carries one degree-zero identification of the base to the
  other; composed, they give
* `Stacks.SymTwistChart.chartProjIso_hom_toBase`: **the chart isomorphism carries the structure
  morphism of one chart to the base to the structure morphism of the other.** This is the
  compatibility that the glueing of the charts over the base consumes.

## Implementation notes

`Stacks.SymTwistChart.chartProjIso_hom_toBase` is written in term mode, copying
`Stacks.AlgebraicGeometry.TwistChart.chartProjIso_hom_toBase`: the degree-zero part of a graded
ring homomorphism reaches `CommRingCat.ofHom` through a `CommRing` instance that `rw` cannot see
is the one `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.strZero` uses, so the two squares
are composed by `Eq.trans` and `congrArg` instead.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace Stacks.SymTwistChart

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {X : Scheme.{u}} (E L : X.Modules)
  [E.IsQuasicoherent] [(tensorObj E L).IsQuasicoherent]
  (hqcE : Stacks.SymGraded.IsQuasicoherentPieces E)
  (hqcEL : Stacks.SymGraded.IsQuasicoherentPieces (tensorObj E L))
  {U : X.Opens} (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
  (hUaff : IsAffineOpen U)

/-- The identification of a section ring with a symmetric algebra carries the structure map to
`algebraMap`. -/
private theorem symSectionRingEquiv_strHom (F : X.Modules) [F.IsQuasicoherent]
    (hqc : Stacks.SymGraded.IsQuasicoherentPieces F) (hUaff : IsAffineOpen U) (r : Γ(X, U)) :
    letI := Stacks.SymGraded.AffinePieces.sectionAlgebra F hqc (V := U)
    (Stacks.SymGraded.AffinePieces.symSectionRingEquiv F hUaff hqc)
      ((Stacks.SymGraded.schemeSheafGradedAlgebra F hqc).strHom U r) =
      algebraMap Γ(X, U) (SymmetricAlgebra Γ(X, U) Γ(F, U)) r := by
  let := Stacks.SymGraded.AffinePieces.sectionAlgebra F hqc (V := U)
  exact (Stacks.SymGraded.AffinePieces.symSectionAlgEquiv F hUaff hqc).commutes r

/-- **The comparison is a `Γ(X, U)`-algebra map.** Both section rings are `Γ(X, U)`-algebras
through their structure maps, both identifications with symmetric algebras are `Γ(X, U)`-algebra
equivalences, and `SymmetricAlgebra.mapEquiv` commutes with the structure map of a symmetric
algebra; so the composite carries one structure map to the other. -/
public theorem chartRingEquiv_strHom (r : Γ(X, U)) :
    chartRingEquiv E L hqcE hqcEL e hUaff
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).strHom U r) =
      (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).strHom U r := by
  have h₁ := symSectionRingEquiv_strHom E hqcE hUaff r
  have h₂ := symSectionRingEquiv_strHom (tensorObj E L) hqcEL hUaff r
  have hrfl : chartRingEquiv E L hqcE hqcEL e hUaff
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).strHom U r) =
      (Stacks.SymGraded.AffinePieces.symSectionRingEquiv (tensorObj E L) hUaff hqcEL).symm
        (SymmetricAlgebra.mapEquiv (sectionsEquiv E L e)
          ((Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hUaff hqcE)
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).strHom U r))) := rfl
  rw [hrfl, h₁, SymmetricAlgebra.mapEquiv_algebraMap, ← h₂,
    RingEquiv.symm_apply_apply]

/-- **The comparison as a graded ring homomorphism.** -/
public def chartGradedHom :
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U →+*ᵍ
      (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U where
  toRingHom := (chartRingEquiv E L hqcE hqcEL e hUaff : _ →+* _)
  map_mem {n x} hx := (chartRingEquiv_mem_grading E L hqcE hqcEL e hUaff n x).2 hx

/-- **The inverse comparison as a graded ring homomorphism.** -/
public def chartGradedInv :
    (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U →+*ᵍ
      (Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U where
  toRingHom := ((chartRingEquiv E L hqcE hqcEL e hUaff).symm : _ →+* _)
  map_mem {n x} hx :=
    (chartRingEquiv_mem_grading E L hqcE hqcEL e hUaff n
      ((chartRingEquiv E L hqcE hqcEL e hUaff).symm x)).1
      (((chartRingEquiv E L hqcE hqcEL e hUaff).apply_symm_apply x).symm ▸ hx)

/-- The two graded ring homomorphisms are mutually inverse, one way round. -/
public theorem chartGradedHom_inv (x) :
    chartGradedHom E L hqcE hqcEL e hUaff (chartGradedInv E L hqcE hqcEL e hUaff x) = x :=
  (chartRingEquiv E L hqcE hqcEL e hUaff).apply_symm_apply x

/-- The two graded ring homomorphisms are mutually inverse, the other way round. -/
public theorem chartGradedInv_hom (x) :
    chartGradedInv E L hqcE hqcEL e hUaff (chartGradedHom E L hqcE hqcEL e hUaff x) = x :=
  (chartRingEquiv E L hqcE hqcEL e hUaff).symm_apply_apply x

/-- **The chart of the projective bundle of `E ⊗ L` over an open trivializing `L` is the chart of
the projective bundle of `E`.** This is [Stacks, Tag 02NC] on one chart. -/
public def chartProjIso :
    AlgebraicGeometry.Proj
        ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U) ≅
      AlgebraicGeometry.Proj
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U) :=
  Stacks.AlgebraicGeometry.ProjPolynomialSections.projIsoOfGradedSections _ _
    (chartGradedHom E L hqcE hqcEL e hUaff) (chartGradedInv E L hqcE hqcEL e hUaff)
    (chartGradedHom_inv E L hqcE hqcEL e hUaff) (chartGradedInv_hom E L hqcE hqcEL e hUaff)

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` is free for the comparison: it has a
graded section. -/
public theorem irrelevant_le_map_chartGradedHom :
    HomogeneousIdeal.irrelevant
        ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U) ≤
      (HomogeneousIdeal.irrelevant
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U)).map
          (chartGradedHom E L hqcE hqcEL e hUaff) :=
  Stacks.AlgebraicGeometry.ProjPolynomialSections.irrelevant_le_map_of_graded_section _ _
    (chartGradedHom E L hqcE hqcEL e hUaff) (chartGradedInv E L hqcE hqcEL e hUaff)
    (chartGradedHom_inv E L hqcE hqcEL e hUaff)

/-- The forward morphism of the chart isomorphism is Mathlib's `AlgebraicGeometry.Proj.map`, which
is where the well-definedness criterion for a rescaled grading is stated. -/
public theorem chartProjIso_hom_eq_map :
    (chartProjIso E L hqcE hqcEL e hUaff).hom =
      AlgebraicGeometry.Proj.map (chartGradedHom E L hqcE hqcEL e hUaff)
        (irrelevant_le_map_chartGradedHom E L hqcE hqcEL e hUaff) :=
  Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map _ _
    (chartGradedHom E L hqcE hqcEL e hUaff)
    (irrelevant_le_map_chartGradedHom E L hqcE hqcEL e hUaff)
    (Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (irrelevant_le_map_chartGradedHom E L hqcE hqcEL e hUaff))

/-! ### The chart isomorphism is an isomorphism over the base -/

/-- **The chart isomorphism commutes with the structure morphisms to the spectra of the
degree-zero parts.** This is the commuting square of [Stacks, Tag 01NO] for the comparison. -/
public theorem chartProjIso_hom_toSpecZero :
    (chartProjIso E L hqcE hqcEL e hUaff).hom ≫
        AlgebraicGeometry.Proj.toSpecZero
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U) =
      AlgebraicGeometry.Proj.toSpecZero
          ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U) ≫
        Spec.map (CommRingCat.ofHom (Stacks.AlgebraicGeometry.RelativeProj.zeroHom _ _
          (chartGradedHom E L hqcE hqcEL e hUaff))) :=
  Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_toSpecZero _ _
    (chartGradedHom E L hqcE hqcEL e hUaff)
    (Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (irrelevant_le_map_chartGradedHom E L hqcE hqcEL e hUaff))

section Base

variable (W : X.AffineZariskiSite)
  (eW : L.over W.toOpens ≅ SheafOfModules.unit (X.ringCatSheaf.over W.toOpens))

/-- **The degree-zero part of the comparison carries one degree-zero identification to the
other.** Both are the structure map of the graded section ring projected to degree zero, and the
comparison carries one structure map to the other by
`Stacks.SymTwistChart.chartRingEquiv_strHom`. -/
public theorem strZero_comp_zeroHom_chartGradedHom :
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).toGradedAlgebra.strZero W ≫
        CommRingCat.ofHom (Stacks.AlgebraicGeometry.RelativeProj.zeroHom _ _
          (chartGradedHom E L hqcE hqcEL eW W.2)) =
      (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).toGradedAlgebra.strZero
        W := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  refine Eq.trans (Stacks.AlgebraicGeometry.RelativeProj.coe_zeroHom_apply _ _
    (chartGradedHom E L hqcE hqcEL eW W.2) _) ?_
  refine Eq.trans (congrArg (chartRingEquiv E L hqcE hqcEL eW W.2)
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).toGradedAlgebra.coe_strZero_apply W r))
    ?_
  refine Eq.trans (chartRingEquiv_strHom E L hqcE hqcEL eW W.2 r) ?_
  exact ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L)
    hqcEL).toGradedAlgebra.coe_strZero_apply W r).symm

/-- **The chart isomorphism is a morphism over the base**: it commutes with the structure
morphisms of the two charts to the base scheme. The structure morphism of a chart factors through
the spectrum of the degree-zero part and the spectrum of the sections of `𝒪_X` over the affine
open, so this is the square of [Stacks, Tag 01NO] followed by the contravariance of `Spec`
applied to `Stacks.SymTwistChart.strZero_comp_zeroHom_chartGradedHom`.

This is the compatibility that the glueing of the charts over the base consumes. -/
public theorem chartProjIso_hom_toBase :
    (chartProjIso E L hqcE hqcEL eW W.2).hom ≫
        (Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).toGradedAlgebra.toBase W =
      (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).toGradedAlgebra.toBase
        W := by
  have hzero : Spec.map (CommRingCat.ofHom
          (Stacks.AlgebraicGeometry.RelativeProj.zeroHom _ _
            (chartGradedHom E L hqcE hqcEL eW W.2))) ≫
        Spec.map ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).toGradedAlgebra.strZero W) ≫
          W.2.fromSpec =
      Spec.map ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L)
        hqcEL).toGradedAlgebra.strZero W) ≫ W.2.fromSpec :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ W.2.fromSpec)
      ((Spec.map_comp ((Stacks.SymGraded.schemeSheafGradedAlgebra E
          hqcE).toGradedAlgebra.strZero W) _).symm.trans
        (congrArg Spec.map (strZero_comp_zeroHom_chartGradedHom E L hqcE hqcEL W eW))))
  show (chartProjIso E L hqcE hqcEL eW W.2).hom ≫ AlgebraicGeometry.Proj.toSpecZero
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading W.toOpens) ≫
      Spec.map ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).toGradedAlgebra.strZero W) ≫
        W.2.fromSpec =
    AlgebraicGeometry.Proj.toSpecZero
        ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading W.toOpens) ≫
      Spec.map ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L)
        hqcEL).toGradedAlgebra.strZero W) ≫ W.2.fromSpec
  refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans (congrArg
    (fun f => f ≫ Spec.map ((Stacks.SymGraded.schemeSheafGradedAlgebra E
      hqcE).toGradedAlgebra.strZero W) ≫ W.2.fromSpec)
    (chartProjIso_hom_toSpecZero E L hqcE hqcEL eW W.2)) ?_)
  exact (Category.assoc _ _ _).trans (congrArg (fun f => AlgebraicGeometry.Proj.toSpecZero
    ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading W.toOpens) ≫ f)
    hzero)

end Base

end Stacks.SymTwistChart

end
