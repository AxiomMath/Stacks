module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjRegrading
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.GlobalSections

/-!
# The projective bundle over an affine base is the projective space of a module

Let `R` be a commutative ring and `M` an `R`-module. `Stacks.SymGraded.projectiveBundle M` is
`P(M~) = Proj_{Spec R}(Sym(M~))`. Over an affine base the relative homogeneous spectrum is the
ordinary `Proj` of its graded ring of global sections
(`Stacks.FiniteMorphismProjective.projTopIso`), and that graded ring is `Sym_R(M)`
(`Stacks.SymGraded.globalSectionsRingEquiv`). **So the projective bundle of `M~` is the
projective space `Proj (Sym_R M)` of the module `M`**, and when `M` has a basis indexed by
`Fin (n + 1)` it is projective `n`-space over `R`.

## Main definitions

* `Stacks.SymGraded.gradedSectionsMvPolynomialHom` and
  `Stacks.SymGraded.gradedSectionsMvPolynomialInv`: for `M` with a basis indexed by
  `Fin (n + 1)`, mutually inverse homomorphisms of **graded rings** between the graded ring of
  global sections of `Sym(M~)` and the total-degree grading of `R[T₀, …, Tₙ]`.
* `Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOfModule`: **`P(M~) ≅ Proj (Sym_R M)`.**
* `Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOverRing`: **`P(O_{Spec R}^{n+1}) ≅ ℙⁿ_R`**
  for a module with a basis indexed by `Fin (n + 1)`.

## Main results

* `Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOfModule_hom_toSpec`: **the identification
  `P(M~) ≅ Proj (Sym_R M)` is an identification over `Spec R`.** It carries
  `AlgebraicGeometry.projectiveSpaceOfModuleToSpec` to the projection of the bundle to its base,
  so it may be substituted into a fibre product over `Spec R`.
* `Stacks.SymGraded.strZero_top_eq_gradedZeroRingHom_comp` and
  `Stacks.SymGraded.gradedZeroRingHom_gradedGlobalSectionsHom_apply_algebraMap`: the whole
  content of that compatibility, namely the degree-zero square relating the structure map
  `R → Sym⁰_R(M)` to `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.strZero` at the top
  open through `AlgebraicGeometry.Scheme.ΓSpecIso`.

## Implementation notes

`Stacks.SymGraded.gradedSectionsMvPolynomialHom` is the declaration the implementation notes of
`StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Basic` ask for by name — "an isomorphism
of graded rings between `Stacks.SymGraded.qcohSheafGradedAlgebra` of `𝒪_S^{n+1}` at the top open
and `Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading`". It is the composite of the two halves
that were missing separately: `Stacks.SymGraded.gradedGlobalSectionsInv`, which identifies the
section ring with `Sym_R(M)`, and `SymPow.gradedMvPolynomialHom`, which identifies `Sym_R(M)`
with the polynomial ring along a basis.

Both irrelevant-ideal hypotheses of `AlgebraicGeometry.Proj.map` come from
`Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id`: a graded ring homomorphism with a
section satisfies them, and here each homomorphism has a two-sided inverse.

## Not done here

**No tag is claimed, and in particular not 01OE.** Tag 01OE is the statement that `ℙⁿ_S` is a
projective bundle over `S` for an **arbitrary** scheme `S`; the base here is affine. The passage
to an arbitrary base is Tag 01O3 — that forming the relative homogeneous spectrum commutes with
base change — which is carried by
`Stacks.RelativeProj.Situation.relativeProjBaseChangeIso` but takes as its input an
identification of the graded algebra over the new base with the pullback of the one over the old,
and that identification is not available for the algebra here.
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` has morphisms over a *fixed* base
(`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom`) but no pullback along a
morphism of base schemes, so the right-hand side `Proj_{S'}(g^*A)` of that tag cannot yet be
written for a general `A`; and the local half that *is* proved
(`StacksFrontier/AlgebraicGeometry/RelativeProjBaseChange/Charts.lean`) does not assemble into the
comparison morphism, because the affine opens of `S'` carried by `g` into an affine open of `S`
cover `S'` but are not cofinal in its affine Zariski site. See that file's own `Not done here`
section.

**`Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOverRing` is not known to be an
isomorphism over `Spec R`.** The first of the two isomorphisms below *is* one over `Spec R`
(`Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOfModule_hom_toSpec`); the second
composes it with `AlgebraicGeometry.projectiveSpaceOfModuleIsoProjMvPolynomial`, which is over
`Spec R` by
`AlgebraicGeometry.projectiveSpaceOfModuleIsoProjMvPolynomial_hom_comp_toSpecZero`, and with
`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`, whose compatibility with the
structure morphism of `AlgebraicGeometry.projectiveSpaceOverRing` is not recorded.

**The bundle here is the one built from the associated sheaves of the symmetric powers**,
`Stacks.SymGraded.projectiveBundle`, and not `Stacks.SymGraded.schemeProjectiveBundle`, built
from the degreewise sheafification of the sectionwise symmetric algebra. The two agree over
`Spec R` — both are relative `Proj` of a sheaf-level graded algebra whose degree-`n` sections
over an affine open are a symmetric power — but the comparison is not written: it needs
`Stacks.SymGraded.AffinePieces.symSectionRingEquiv` at the top open, whose target is the
symmetric algebra of the `Γ(Spec R, ⊤)`-module `Γ(M~, ⊤)`, to be transported onto `Sym_R(M)`
along `AlgebraicGeometry.Scheme.ΓSpecIso` and `AlgebraicGeometry.tilde.isoTop`, as a map of
**graded** rings. That transport is the one thing standing between this file and
`Stacks.SymGraded.schemeProjectiveBundle (AlgebraicGeometry.tilde M) _ ≅
AlgebraicGeometry.projectiveSpaceOfModule R M` over `Spec R`.

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace Stacks.SymGraded

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-! ### The bundle over an affine base is the projective space of the module -/

/-- **The projective bundle of `M~` over `Spec R` is the projective space `Proj (Sym_R M)` of
`M`.** Over an affine base the relative homogeneous spectrum is the `Proj` of its graded ring of
global sections, and that ring is `Sym_R(M)`. -/
def projectiveBundleIsoProjectiveSpaceOfModule :
    (projectiveBundle M).scheme ≅ projectiveSpaceOfModule R M :=
  haveI : IsIso (Proj.map (gradedGlobalSectionsHom M)
      (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
        (gradedGlobalSectionsHom_comp_inv M))) :=
    Proj.isIso_map _
      (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
        (gradedGlobalSectionsInv_comp_hom M))
      (gradedGlobalSectionsInv_comp_hom M) (gradedGlobalSectionsHom_comp_inv M)
  (Stacks.FiniteMorphismProjective.projTopIso
      (symSheafGradedAlgebra M) (projectiveBundle M)).symm ≪≫
    asIso (Proj.map (gradedGlobalSectionsHom M)
      (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
        (gradedGlobalSectionsHom_comp_inv M)))

/-! ### The identification is an identification over `Spec R` -/

section OverBase

open Stacks.AlgebraicGeometry.RelativeProj

/-- **The base ring sits the same way in both graded rings.** The degree-zero part of the
identification `Sym_R(M) ≅ Γ(Sym(M~), ⊤)` carries the structure map `R → Sym⁰_R(M)` of the
symmetric algebra to the structure map of `Sym(M~)` read through
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem gradedZeroRingHom_gradedGlobalSectionsHom_apply_algebraMap (r : R) :
    (gradedGlobalSectionsHom M).gradedZeroRingHom
        (algebraMap R (SymPow.symmetricPower 0 R M) r) =
      GradedRing.projZeroRingHom'
          ((symSheafGradedAlgebra M).grading (⊤ : (Spec R).Opens))
        ((symSheafGradedAlgebra M).strHom (⊤ : (Spec R).Opens)
          ((Scheme.ΓSpecIso R).inv.hom r)) := by
  refine Subtype.ext ?_
  rw [projZeroRingHom'_coe_of_mem _
    ((symSheafGradedAlgebra M).strHom_mem (⊤ : (Spec R).Opens) _)]
  have hmem : ((algebraMap R ↥(SymPow.symmetricPower 0 R M) r :
      ↥(SymPow.symmetricPower 0 R M)) : SymmetricAlgebra R M) ∈
      SymPow.symmetricPower 0 R M :=
    (algebraMap R ↥(SymPow.symmetricPower 0 R M) r).2
  change globalSectionsRingEquiv M _ = _
  rw [globalSectionsRingEquiv_apply,
    DirectSum.decompose_of_mem (fun n : ℕ => SymPow.symmetricPower n R M) hmem,
    globalSectionsDirectSumEquiv_of, SheafGradedAlgebra.strHom_apply]
  refine congrArg (DirectSum.of _ 0) ?_
  refine Eq.trans (congrArg (globalPieceEquiv M 0)
    (Algebra.algebraMap_eq_smul_one (A := ↥(SymPow.symmetricPower 0 R M)) r)) ?_
  refine Eq.trans (map_smul (globalPieceEquiv M 0) r (oneG (R := R) M)) ?_
  refine Eq.trans (congrArg (fun z => r • z) (globalPieceEquiv_one M)) ?_
  exact (algebraMap_smul Γ(Spec R, (⊤ : (Spec R).Opens)) r
    ((symSheafGradedAlgebra M).one (⊤ : (Spec R).Opens))).symm

/-- **The degree-zero square, as a commuting square of rings.** The same statement as
`Stacks.SymGraded.gradedZeroRingHom_gradedGlobalSectionsHom_apply_algebraMap`, written against
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.strZero`, which is the morphism the
structure morphism of the chart at the top open is built from. -/
theorem strZero_top_eq_gradedZeroRingHom_comp :
    CommRingCat.ofHom (algebraMap R (SymPow.symmetricPower 0 R M)) ≫
        CommRingCat.ofHom (gradedGlobalSectionsHom M).gradedZeroRingHom =
      (Scheme.ΓSpecIso R).inv ≫
        (symSheafGradedAlgebra M).toGradedAlgebra.strZero
          (⟨⊤, isAffineOpen_top (Spec R)⟩ : (Spec R).AffineZariskiSite) :=
  CommRingCat.hom_ext (RingHom.ext fun r =>
    gradedZeroRingHom_gradedGlobalSectionsHom_apply_algebraMap M r)

/-- **The identification of the projective bundle with the projective space of the module is an
identification over `Spec R`.** The structure morphism of
`AlgebraicGeometry.projectiveSpaceOfModule`, pulled back along
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOfModule`, is the projection of the bundle
to its base. -/
theorem projectiveBundleIsoProjectiveSpaceOfModule_hom_toSpec :
    (projectiveBundleIsoProjectiveSpaceOfModule M).hom ≫
        projectiveSpaceOfModuleToSpec R M =
      projectiveBundleToBase M := by
  have hS : IsAffineOpen (⊤ : (Spec R).Opens) := isAffineOpen_top (Spec R)
  have hiso : (projectiveBundleIsoProjectiveSpaceOfModule M).hom =
      (Stacks.FiniteMorphismProjective.projTopIso
          (symSheafGradedAlgebra M) (projectiveBundle M)).inv ≫
        Proj.map (gradedGlobalSectionsHom M)
          (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
            (gradedGlobalSectionsHom_comp_inv M)) := rfl
  have hb : projectiveBundleToBase M = (projectiveBundle M).toBase := rfl
  have hfrom : hS.fromSpec = Spec.map (Scheme.ΓSpecIso R).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hL : Proj.map (gradedGlobalSectionsHom M)
          (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
            (gradedGlobalSectionsHom_comp_inv M)) ≫
        projectiveSpaceOfModuleToSpec R M =
      Proj.toSpecZero ((symSheafGradedAlgebra M).grading (⊤ : (Spec R).Opens)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (SymPow.symmetricPower 0 R M)) ≫
          CommRingCat.ofHom (gradedGlobalSectionsHom M).gradedZeroRingHom) := by
    rw [projectiveSpaceOfModuleToSpec, ← Category.assoc, Proj.map_toSpecZero,
      Category.assoc, ← Spec.map_comp]
  have hR : projInclusionToOpen (symSheafGradedAlgebra M) (⊤ : (Spec R).Opens) hS ≫
        (⊤ : (Spec R).Opens).ι =
      Proj.toSpecZero ((symSheafGradedAlgebra M).grading (⊤ : (Spec R).Opens)) ≫
        Spec.map ((Scheme.ΓSpecIso R).inv ≫
          (symSheafGradedAlgebra M).toGradedAlgebra.strZero
            (⟨⊤, hS⟩ : (Spec R).AffineZariskiSite)) := by
    refine Eq.trans (GradedAlgebra.toOpen_ι (symSheafGradedAlgebra M).toGradedAlgebra
      (⟨⊤, hS⟩ : (Spec R).AffineZariskiSite)) ?_
    change Proj.toSpecZero ((symSheafGradedAlgebra M).grading (⊤ : (Spec R).Opens)) ≫
        Spec.map ((symSheafGradedAlgebra M).toGradedAlgebra.strZero
          (⟨⊤, hS⟩ : (Spec R).AffineZariskiSite)) ≫ hS.fromSpec = _
    refine Eq.trans (congrArg (fun g =>
      Proj.toSpecZero ((symSheafGradedAlgebra M).grading (⊤ : (Spec R).Opens)) ≫
        Spec.map ((symSheafGradedAlgebra M).toGradedAlgebra.strZero
          (⟨⊤, hS⟩ : (Spec R).AffineZariskiSite)) ≫ g) hfrom) ?_
    exact congrArg (fun x =>
      Proj.toSpecZero ((symSheafGradedAlgebra M).grading (⊤ : (Spec R).Opens)) ≫ x)
      (Spec.map_comp (Scheme.ΓSpecIso R).inv
        ((symSheafGradedAlgebra M).toGradedAlgebra.strZero
          (⟨⊤, hS⟩ : (Spec R).AffineZariskiSite))).symm
  rw [hiso, Category.assoc]
  refine (Iso.inv_comp_eq _).mpr ?_
  rw [hb, Stacks.FiniteMorphismProjective.projTopIso_hom_toBase, hL, hR]
  exact congrArg (fun ψ =>
    Proj.toSpecZero ((symSheafGradedAlgebra M).grading (⊤ : (Spec R).Opens)) ≫ Spec.map ψ)
    (strZero_top_eq_gradedZeroRingHom_comp M)

end OverBase

/-! ### Homogeneous coordinates on the bundle -/

section Basis

variable {n : ℕ} (b : Module.Basis (Fin (n + 1)) R M)

/-- **The graded ring of global sections of `Sym(M~)` is `R[T₀, …, Tₙ]`** when `M` has a basis
indexed by `Fin (n + 1)`. -/
def gradedSectionsMvPolynomialHom :
    (symSheafGradedAlgebra M).grading ⊤ →+*ᵍ polyGrading R n :=
  (SymPow.gradedMvPolynomialHom b).comp (gradedGlobalSectionsInv M)

/-- The inverse of `Stacks.SymGraded.gradedSectionsMvPolynomialHom`. -/
def gradedSectionsMvPolynomialInv :
    polyGrading R n →+*ᵍ (symSheafGradedAlgebra M).grading ⊤ :=
  (gradedGlobalSectionsHom M).comp (SymPow.gradedMvPolynomialInv b)

/-- `gradedSectionsMvPolynomialHom` followed by `gradedSectionsMvPolynomialInv` is the identity of
`R[T₀, …, Tₙ]`. -/
theorem gradedSectionsMvPolynomialHom_comp_inv :
    (gradedSectionsMvPolynomialHom M b).comp (gradedSectionsMvPolynomialInv M b) =
      GradedRingHom.id (polyGrading R n) :=
  GradedRingHom.ext fun x =>
    (congrArg (SymPow.gradedMvPolynomialHom b)
      congr($(gradedGlobalSectionsInv_comp_hom M) (SymPow.gradedMvPolynomialInv b x))).trans
      congr($(SymPow.gradedMvPolynomialHom_comp_inv b) x)

/-- `gradedSectionsMvPolynomialInv` followed by `gradedSectionsMvPolynomialHom` is the identity of
the graded ring of global sections of `Sym(M~)`. -/
theorem gradedSectionsMvPolynomialInv_comp_hom :
    (gradedSectionsMvPolynomialInv M b).comp (gradedSectionsMvPolynomialHom M b) =
      GradedRingHom.id ((symSheafGradedAlgebra M).grading ⊤) :=
  GradedRingHom.ext fun x =>
    (congrArg (gradedGlobalSectionsHom M)
      congr($(SymPow.gradedMvPolynomialInv_comp_hom b) (gradedGlobalSectionsInv M x))).trans
      congr($(gradedGlobalSectionsHom_comp_inv M) x)

/-- **The projective bundle of a free module of rank `n + 1` over an affine base is projective
`n`-space.** This is Tag 01OE for an affine base; see the `Not done here` section of this file
for what the arbitrary-base case still needs. -/
def projectiveBundleIsoProjectiveSpaceOverRing :
    (projectiveBundle M).scheme ≅ projectiveSpaceOverRing n R :=
  projectiveBundleIsoProjectiveSpaceOfModule M ≪≫
    projectiveSpaceOfModuleIsoProjMvPolynomial b ≪≫
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).iso.symm

end Basis

end Stacks.SymGraded

end
