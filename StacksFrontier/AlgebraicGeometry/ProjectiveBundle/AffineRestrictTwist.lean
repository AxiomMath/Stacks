module

public import StacksFrontier.AlgebraicGeometry.SymSectionsBaseChangeDischarge.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Iso
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjRegrading
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TautologicalMap

/-!
# The projective bundle over an affine open, with its twist

Let `ℰ` be a quasi-coherent module on a scheme `X`, `V ⊆ X` an affine open and `𝒢` a
quasi-coherent module on `V` identified with `ℰ|_V`. This file identifies the part `π ⁻¹ V` of
the projective bundle `π : 𝐏(ℰ) ⟶ X` lying over `V` with the projective bundle `𝐏(𝒢)` over `V`,
**together with the twist `𝒪(1)`**: the isomorphism lies over `V` and carries `𝒪_{𝐏(ℰ)}(1)`
restricted to `π ⁻¹ V` to `𝒪_{𝐏(𝒢)}(1)`.

## The route

Over the affine base `V` the bundle `𝐏(𝒢)` is its own chart at the top open
(`Stacks.FiniteMorphismProjective.projTopIso`), the `Proj` of the graded ring `Γ(V, Sym(𝒢))`;
and `π ⁻¹ V` is the image of the chart of `𝐏(ℰ)` over `V`, the `Proj` of `Γ(V, Sym(ℰ))`. The
first graded ring is the base change of `Sym Γ(ℰ, V)` along the restriction of functions
`Γ(X, V) ⟶ Γ(V, ⊤)` (`Stacks.SymSectionsBaseChange.symSectionTensorEquiv`), that restriction is
bijective, so the base change collapses (`Stacks.ProjectiveBundle.tensorCollapse`), and
`Sym Γ(ℰ, V)` is the second graded ring (`Stacks.SymGraded.AffinePieces.symSectionAlgEquiv`).
The resulting graded isomorphism is compatible with the structure maps from the functions on `V`,
so the two `Proj`s are isomorphic over `V`. The twists are read through the chart
identifications of the two canonical twist data and the comparison of twisting sheaves
`Stacks.ProjTwistComparison.twistMap`, which is invertible along a graded isomorphism, this being
a degreewise localization away from `1`.

## Main definitions

* `Stacks.ProjectiveBundle.tensorCollapse`: `R' ⊗_R B ≅ B` for a bijective `R ⟶ R'`.
* `Stacks.ProjectiveBundle.restrictSectionRingEquiv`: `Γ(V, Sym(𝒢)) ≅ Γ(V, Sym(ℰ))`, an
  isomorphism of graded rings compatible with the functions on `V`.
* `Stacks.ProjectiveBundle.restrictBundleMap`: the open immersion `𝐏(𝒢) ⟶ 𝐏(ℰ)` over `V ⊆ X`.
* `Stacks.ProjectiveBundle.restrictBundleIso`: `𝐏(𝒢) ≅ π ⁻¹ V`.
* `Stacks.ProjectiveBundle.restrictBundleTwistIso` and
  `Stacks.ProjectiveBundle.restrictBundleIsoTwistIso`: the pullback of `𝒪_{𝐏(ℰ)}(1)` is
  `𝒪_{𝐏(𝒢)}(1)`.

## Main results

* `Stacks.ProjectiveBundle.mem_grading_restrictSectionRingEquiv` and
  `Stacks.ProjectiveBundle.restrictSectionRingEquiv_strHom`: the comparison is graded and
  compatible with the functions on `V`.
* `Stacks.ProjectiveBundle.restrictProjMap_toOpen`: the comparison of projective spectra lies over
  `V`.
* `Stacks.ProjectiveBundle.restrictBundleIso_hom_morphismRestrict`: **`𝐏(𝒢) ≅ π ⁻¹ V` lies over
  `V`.**

## Not done here

This is the base change of a projective bundle together with its twist along the inclusion of an
**affine** open only. The base change along an arbitrary morphism, of which this is the chart, is
not drawn: it needs the chart isomorphisms over the affine opens of the new base to be glued,
for instance through the tautological epimorphisms onto the twists.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.SymGraded
open scoped TensorProduct

universe u

namespace Stacks.ProjectiveBundle

/-! ### Base change along a bijective ring map -/

section Collapse

variable {R R' B : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing B] [Algebra R B]
  (h : Function.Bijective (algebraMap R R'))

/-- **The base change along a bijective ring map is trivial**: `R' ⊗_R B ≅ B` when
`R ⟶ R'` is bijective. -/
def tensorCollapse : R' ⊗[R] B ≃ₐ[R] B :=
  (Algebra.TensorProduct.congr (AlgEquiv.ofBijective (Algebra.ofId R R') h).symm
    AlgEquiv.refl).trans (Algebra.TensorProduct.lid R B)

/-- `tensorCollapse` sends `algebraMap R R' r ⊗ₜ b` to `r • b`. -/
theorem tensorCollapse_tmul (r : R) (b : B) :
    tensorCollapse h (algebraMap R R' r ⊗ₜ b) = r • b := by
  have hr : (AlgEquiv.ofBijective (Algebra.ofId R R') h).symm (algebraMap R R' r) = r :=
    (AlgEquiv.ofBijective (Algebra.ofId R R') h).symm_apply_apply r
  change Algebra.TensorProduct.lid R B (Algebra.TensorProduct.congr
    (AlgEquiv.ofBijective (Algebra.ofId R R') h).symm AlgEquiv.refl
      (algebraMap R R' r ⊗ₜ b)) = r • b
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change Algebra.TensorProduct.lid R B
    ((AlgEquiv.ofBijective (Algebra.ofId R R') h).symm (algebraMap R R' r) ⊗ₜ b) = r • b
  rw [hr]
  exact Algebra.TensorProduct.lid_tmul r b

/-- `tensorCollapse` sends `1 ⊗ₜ b` to `b`. -/
theorem tensorCollapse_one_tmul (b : B) : tensorCollapse h ((1 : R') ⊗ₜ b) = b := by
  rw [← map_one (algebraMap R R'), tensorCollapse_tmul, one_smul]

/-- **The base change of a submodule is carried onto the submodule** by the trivialisation of a
base change along a bijective ring map. -/
theorem mem_baseChange_iff_tensorCollapse (P : Submodule R B) (x : R' ⊗[R] B) :
    x ∈ P.baseChange R' ↔ tensorCollapse h x ∈ P := by
  constructor
  · intro hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨p, hp, rfl⟩ := hx
        rw [TensorProduct.mk_apply, tensorCollapse_one_tmul]
        exact hp
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r' x _ hx =>
        obtain ⟨r, rfl⟩ := h.2 r'
        rw [algebraMap_smul, map_smul]
        exact P.smul_mem r hx
  · intro hx
    convert Submodule.tmul_mem_baseChange_of_mem (1 : R') hx
    apply (tensorCollapse h).injective
    rw [tensorCollapse_one_tmul]

end Collapse

/-! ### The graded ring of sections over an affine open -/

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)
  {V : X.Opens} (hV : IsAffineOpen V) (G : V.toScheme.Modules) [G.IsQuasicoherent]
  (hqcG : IsQuasicoherentPieces G) (eG : E.restrict V.ι ≅ G)

include hV in
/-- An affine open, as a scheme, is affine. -/
theorem isAffine_of_isAffineOpen : IsAffine V.toScheme := hV

include hV in
/-- The top open of an affine open subscheme is affine. -/
theorem isAffineOpen_top_of_isAffineOpen : IsAffineOpen (⊤ : V.toScheme.Opens) := by
  have : IsAffine V.toScheme := hV
  exact isAffineOpen_top V.toScheme

/-- The restriction of functions from `V` to the open subscheme `V` is bijective. -/
theorem bijective_ι_appLE :
    letI := Stacks.SymSectionsBaseChange.baseAlgebra V.ι V.ι_preimage_self.ge
    Function.Bijective (algebraMap Γ(X, V) Γ(V.toScheme, ⊤)) :=
  ConcreteCategory.bijective_of_isIso (V.ι.appLE V ⊤ V.ι_preimage_self.ge)

/-- The identification `𝒢 ≅ (V ⟶ X)^* ℰ` that the base-change comparison of section rings
consumes. -/
def restrictPullbackIso : G ≅ (Scheme.Modules.pullback V.ι).obj E :=
  eG.symm ≪≫ (Scheme.Modules.restrictFunctorIsoPullback V.ι).app E

/-- **`Γ(V, Sym(𝒢)) ≅ Γ(V, Sym(ℰ))`**: the graded ring of global sections of `Sym(𝒢)` on `V` is
the base change, along the restriction `Γ(X, V) ⟶ Γ(V, ⊤)` of functions, of the symmetric
algebra of `Γ(ℰ, V)`; that restriction is bijective, and `Sym Γ(ℰ, V)` is the graded ring of
sections of `Sym(ℰ)` over `V`. -/
def restrictSectionRingEquiv :
    (schemeSheafGradedAlgebra G hqcG).sectionRing ⊤ ≃+*
      (schemeSheafGradedAlgebra E hqc).sectionRing V :=
  letI := Stacks.SymSectionsBaseChange.baseAlgebra V.ι V.ι_preimage_self.ge
  letI := AffinePieces.sectionAlgebra G hqcG (V := ⊤)
  letI := AffinePieces.sectionAlgebra E hqc (V := V)
  (Stacks.SymSectionsBaseChange.symSectionTensorEquiv V.ι V.ι_preimage_self.ge E G hqcG
      (isAffineOpen_top_of_isAffineOpen hV)
      (Stacks.SymSectionsBaseChangeDischarge.sectionsBaseChangeEquiv V.ι E G
        (restrictPullbackIso E G eG) hV (isAffineOpen_top_of_isAffineOpen hV)
        V.ι_preimage_self.ge)).toRingEquiv.trans
    ((tensorCollapse (bijective_ι_appLE (V := V))).trans
      (AffinePieces.symSectionAlgEquiv E hV hqc).symm).toRingEquiv

/-- The isomorphism, unfolded. -/
theorem restrictSectionRingEquiv_apply (x : (schemeSheafGradedAlgebra G hqcG).sectionRing ⊤) :
    letI := Stacks.SymSectionsBaseChange.baseAlgebra V.ι V.ι_preimage_self.ge
    letI := AffinePieces.sectionAlgebra G hqcG (V := ⊤)
    letI := AffinePieces.sectionAlgebra E hqc (V := V)
    restrictSectionRingEquiv E hqc hV G hqcG eG x =
      ((tensorCollapse (bijective_ι_appLE (V := V))).trans
        (AffinePieces.symSectionAlgEquiv E hV hqc).symm)
        (Stacks.SymSectionsBaseChange.symSectionTensorEquiv V.ι V.ι_preimage_self.ge E G hqcG
          (isAffineOpen_top_of_isAffineOpen hV)
          (Stacks.SymSectionsBaseChangeDischarge.sectionsBaseChangeEquiv V.ι E G
            (restrictPullbackIso E G eG) hV (isAffineOpen_top_of_isAffineOpen hV)
            V.ι_preimage_self.ge) x) := by
  simp only [restrictSectionRingEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]

omit [E.IsQuasicoherent] in
/-- The inverse of `Stacks.SymGraded.AffinePieces.symSectionAlgEquiv` is that of
`Stacks.SymGraded.AffinePieces.symSectionRingEquiv`. -/
theorem symSectionAlgEquiv_symm_apply [E.IsQuasicoherent]
    (y : SymmetricAlgebra Γ(X, V) Γ(E, V)) :
    letI := AffinePieces.sectionAlgebra E hqc (V := V)
    (AffinePieces.symSectionAlgEquiv E hV hqc).symm y =
      (AffinePieces.symSectionRingEquiv E hV hqc).symm y :=
  rfl

/-- **The isomorphism is one of graded rings.** -/
theorem mem_grading_restrictSectionRingEquiv (n : ℕ)
    (x : (schemeSheafGradedAlgebra G hqcG).sectionRing ⊤) :
    restrictSectionRingEquiv E hqc hV G hqcG eG x ∈
        (schemeSheafGradedAlgebra E hqc).grading V n ↔
      x ∈ (schemeSheafGradedAlgebra G hqcG).grading ⊤ n := by
  let := Stacks.SymSectionsBaseChange.baseAlgebra V.ι V.ι_preimage_self.ge
  let := AffinePieces.sectionAlgebra G hqcG (V := ⊤)
  let := AffinePieces.sectionAlgebra E hqc (V := V)
  rw [restrictSectionRingEquiv_apply, AlgEquiv.trans_apply, symSectionAlgEquiv_symm_apply,
    ← AffinePieces.mem_symmetricPower_symSectionRingEquiv E hV hqc n, RingEquiv.apply_symm_apply,
    Stacks.SymSectionsBaseChange.symSectionTensorEquiv_grading V.ι V.ι_preimage_self.ge E G
      hqcG _ _ n x,
    mem_baseChange_iff_tensorCollapse (bijective_ι_appLE (V := V))]

/-- **The isomorphism is compatible with the functions on `V`**: it carries the structure map
of `Sym(𝒢)` at a function restricted from `X` to the structure map of `Sym(ℰ)` at that
function. -/
theorem restrictSectionRingEquiv_strHom (r : Γ(X, V)) :
    restrictSectionRingEquiv E hqc hV G hqcG eG
        ((schemeSheafGradedAlgebra G hqcG).strHom ⊤ (V.ι.appLE V ⊤ V.ι_preimage_self.ge r)) =
      (schemeSheafGradedAlgebra E hqc).strHom V r := by
  let := Stacks.SymSectionsBaseChange.baseAlgebra V.ι V.ι_preimage_self.ge
  let := AffinePieces.sectionAlgebra G hqcG (V := ⊤)
  let := AffinePieces.sectionAlgebra E hqc (V := V)
  have h1 : (schemeSheafGradedAlgebra G hqcG).strHom ⊤ (V.ι.appLE V ⊤ V.ι_preimage_self.ge r) =
      algebraMap Γ(V.toScheme, ⊤) _ (algebraMap Γ(X, V) Γ(V.toScheme, ⊤) r) :=
    (AffinePieces.algebraMap_sectionRingAlgebra _ ⊤ _).symm
  have h2 : (schemeSheafGradedAlgebra E hqc).strHom V r = algebraMap Γ(X, V) _ r :=
    (AffinePieces.algebraMap_sectionRingAlgebra _ V r).symm
  rw [h1, h2, restrictSectionRingEquiv_apply, AlgEquiv.commutes,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, AlgEquiv.trans_apply,
    tensorCollapse_tmul, ← Algebra.algebraMap_eq_smul_one, AlgEquiv.commutes]

/-- The comparison of graded rings of sections as a homomorphism of graded rings. -/
def restrictGradedHom :
    (schemeSheafGradedAlgebra G hqcG).grading ⊤ →+*ᵍ (schemeSheafGradedAlgebra E hqc).grading V
    where
  toRingHom := (restrictSectionRingEquiv E hqc hV G hqcG eG).toRingHom
  map_mem {_ _} hx := (mem_grading_restrictSectionRingEquiv E hqc hV G hqcG eG _ _).2 hx

/-- The inverse comparison of graded rings of sections. -/
def restrictGradedInv :
    (schemeSheafGradedAlgebra E hqc).grading V →+*ᵍ (schemeSheafGradedAlgebra G hqcG).grading ⊤
    where
  toRingHom := (restrictSectionRingEquiv E hqc hV G hqcG eG).symm.toRingHom
  map_mem {i x} hx := by
    rw [← mem_grading_restrictSectionRingEquiv E hqc hV G hqcG eG]
    change restrictSectionRingEquiv E hqc hV G hqcG eG
      ((restrictSectionRingEquiv E hqc hV G hqcG eG).symm x) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hx

/-- `restrictGradedHom` is a left inverse of `restrictGradedInv`. -/
theorem restrictGradedHom_comp_inv :
    (restrictGradedHom E hqc hV G hqcG eG).comp (restrictGradedInv E hqc hV G hqcG eG) =
      GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (restrictSectionRingEquiv E hqc hV G hqcG eG).apply_symm_apply x

/-- `restrictGradedInv` is a left inverse of `restrictGradedHom`. -/
theorem restrictGradedInv_comp_hom :
    (restrictGradedInv E hqc hV G hqcG eG).comp (restrictGradedHom E hqc hV G hqcG eG) =
      GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (restrictSectionRingEquiv E hqc hV G hqcG eG).symm_apply_apply x

/-- The irrelevant-ideal hypothesis of `AlgebraicGeometry.Proj.map` for the comparison. -/
theorem irrelevant_le_map_restrictGradedHom :
    HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E hqc).grading V) ≤
      (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra G hqcG).grading ⊤)).map
        (restrictGradedHom E hqc hV G hqcG eG) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
    (restrictGradedHom_comp_inv E hqc hV G hqcG eG)

/-- The irrelevant-ideal hypothesis of `AlgebraicGeometry.Proj.map` for the inverse. -/
theorem irrelevant_le_map_restrictGradedInv :
    HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra G hqcG).grading ⊤) ≤
      (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E hqc).grading V)).map
        (restrictGradedInv E hqc hV G hqcG eG) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
    (restrictGradedInv_comp_hom E hqc hV G hqcG eG)

/-- The morphism of projective spectra induced by the comparison of graded rings. -/
abbrev restrictProjMap :
    AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E hqc).grading V) ⟶
      AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra G hqcG).grading ⊤) :=
  Proj.map (restrictGradedHom E hqc hV G hqcG eG)
    (irrelevant_le_map_restrictGradedHom E hqc hV G hqcG eG)

/-- The comparison of projective spectra is an isomorphism, with inverse induced by
`restrictGradedInv`. -/
instance isIso_restrictProjMap : IsIso (restrictProjMap E hqc hV G hqcG eG) :=
  Proj.isIso_map _ (irrelevant_le_map_restrictGradedInv E hqc hV G hqcG eG)
    (restrictGradedInv_comp_hom E hqc hV G hqcG eG) (restrictGradedHom_comp_inv E hqc hV G hqcG eG)

/-- **The comparison of graded rings is compatible with the degree-zero structure maps**: the
structure map of `Sym(ℰ)` over `V` at a function is the comparison applied to the structure map
of `Sym(𝒢)` at its restriction to `V`. -/
theorem restrictGradedHom_strZero (r : Γ(X, V)) :
    (restrictGradedHom E hqc hV G hqcG eG).gradedZeroRingHom
        ((schemeSheafGradedAlgebra G hqcG).toGradedAlgebra.strZero
          (⟨⊤, isAffineOpen_top_of_isAffineOpen hV⟩ : V.toScheme.AffineZariskiSite)
          (V.ι.appLE V ⊤ V.ι_preimage_self.ge r)) =
      (schemeSheafGradedAlgebra E hqc).toGradedAlgebra.strZero
        (⟨V, hV⟩ : X.AffineZariskiSite) r := by
  refine Subtype.ext ?_
  have h1 := GradedAlgebra.coe_strZero_apply (schemeSheafGradedAlgebra E hqc).toGradedAlgebra
    (⟨V, hV⟩ : X.AffineZariskiSite) r
  have h2 := GradedAlgebra.coe_strZero_apply (schemeSheafGradedAlgebra G hqcG).toGradedAlgebra
    (⟨⊤, isAffineOpen_top_of_isAffineOpen hV⟩ : V.toScheme.AffineZariskiSite)
    (V.ι.appLE V ⊤ V.ι_preimage_self.ge r)
  exact (congrArg (restrictSectionRingEquiv E hqc hV G hqcG eG) h2).trans
    ((restrictSectionRingEquiv_strHom E hqc hV G hqcG eG r).trans h1.symm)

omit [E.IsQuasicoherent] [G.IsQuasicoherent] in
/-- `Spec` of a threefold composite, against a common morphism out of the spectrum. -/
theorem spec_map_comp_three {R₁ R₂ R₃ R₄ : CommRingCat.{u}} {Y : Scheme.{u}} (a : R₃ ⟶ R₄)
    (b : R₂ ⟶ R₃) (c : R₁ ⟶ R₂) (d : R₁ ⟶ R₄) (f : Spec R₁ ⟶ Y) (h : c ≫ b ≫ a = d) :
    Spec.map a ≫ Spec.map b ≫ Spec.map c ≫ f = Spec.map d ≫ f := by
  rw [← h, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]

/-- The structure morphism of a chart, read through `Proj.toSpecZero`. -/
@[reassoc]
theorem projInclusionToOpen_ι {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)
    (hU : IsAffineOpen U) :
    projInclusionToOpen A U hU ≫ U.ι =
      Proj.toSpecZero (A.grading U) ≫
        Spec.map (A.toGradedAlgebra.strZero (⟨U, hU⟩ : S.AffineZariskiSite)) ≫ hU.fromSpec :=
  GradedAlgebra.toOpen_ι _ _

/-- **The comparison of projective spectra lies over `V`.** -/
theorem restrictProjMap_toOpen :
    restrictProjMap E hqc hV G hqcG eG ≫
        projInclusionToOpen (schemeSheafGradedAlgebra G hqcG) ⊤
          (isAffineOpen_top_of_isAffineOpen hV) ≫ (⊤ : V.toScheme.Opens).ι =
      projInclusionToOpen (schemeSheafGradedAlgebra E hqc) V hV := by
  rw [← cancel_mono V.ι, Category.assoc, Category.assoc, projInclusionToOpen_ι,
    projInclusionToOpen_ι_assoc, Proj.map_toSpecZero_assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec V.ι hV (isAffineOpen_top_of_isAffineOpen hV)
      V.ι_preimage_self.ge]
  congr 1
  refine spec_map_comp_three _ _ _ _ _ (CommRingCat.hom_ext (RingHom.ext fun r => ?_))
  exact restrictGradedHom_strZero E hqc hV G hqcG eG r

/-- The comparison of graded rings is a degreewise localization away from `1`. -/
theorem isAwayDegreewise_restrictGradedHom :
    Stacks.GradedLocalization.IsAwayDegreewise (restrictGradedHom E hqc hV G hqcG eG) 1 where
  isUnit_map := by rw [map_one]; exact isUnit_one
  surj n y hy := by
    refine ⟨0, restrictGradedInv E hqc hV G hqcG eG y,
      (restrictGradedInv E hqc hV G hqcG eG).map_mem hy, ?_⟩
    rw [pow_zero, one_mul]
    exact (restrictSectionRingEquiv E hqc hV G hqcG eG).apply_symm_apply y
  torsion n x _ h := by
    refine ⟨0, ?_⟩
    rw [pow_zero, one_mul]
    exact (restrictSectionRingEquiv E hqc hV G hqcG eG).injective (h.trans (map_zero _).symm)

/-- **The twisting sheaves are carried to each other by the comparison of projective spectra**,
in every degree. -/
instance isIso_restrictTwistMap (n : ℤ) :
    IsIso (Stacks.ProjTwistComparison.twistMap (restrictGradedHom E hqc hV G hqcG eG)
      (irrelevant_le_map_restrictGradedHom E hqc hV G hqcG eG) n) :=
  Stacks.ProjTwistComparison.isIso_twistMap _ _ n
    (isAwayDegreewise_restrictGradedHom E hqc hV G hqcG eG) (SetLike.one_mem_graded _)

/-- Pulling back along the inverse of an isomorphism undoes pulling back along it. -/
def pullbackInvHomIso {Y Z : Scheme.{u}} (e : Y ≅ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp e.inv e.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫ (Scheme.Modules.pullbackId (X := Z)).app M

/-- The chart of `𝐏(ℰ)` over `V`, read on the bundle `𝐏(𝒢)`: the inverse of the chart of `𝐏(𝒢)` at
the top open, the inverse comparison of projective spectra, and the chart of `𝐏(ℰ)` over `V`. -/
def restrictBundleMap :
    (relativeProj (schemeSheafGradedAlgebra G hqcG)).scheme ⟶
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme :=
  haveI := isAffine_of_isAffineOpen hV
  (Stacks.FiniteMorphismProjective.projTopIso (schemeSheafGradedAlgebra G hqcG)
      (relativeProj (schemeSheafGradedAlgebra G hqcG))).inv ≫
    inv (restrictProjMap E hqc hV G hqcG eG) ≫
    (relativeProj (schemeSheafGradedAlgebra E hqc)).chart V hV

/-- `restrictBundleMap` is an open immersion. -/
instance isOpenImmersion_restrictBundleMap :
    IsOpenImmersion (restrictBundleMap E hqc hV G hqcG eG) := by
  unfold restrictBundleMap
  infer_instance

/-- **The map lies over the inclusion of `V`.** -/
theorem restrictBundleMap_toBase :
    restrictBundleMap E hqc hV G hqcG eG ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase =
      (relativeProj (schemeSheafGradedAlgebra G hqcG)).toBase ≫ V.ι := by
  have := isAffine_of_isAffineOpen hV
  have h1 := Stacks.FiniteMorphismProjective.projTopIso_hom_toBase
    (schemeSheafGradedAlgebra G hqcG) (relativeProj (schemeSheafGradedAlgebra G hqcG))
  have h2 := restrictProjMap_toOpen E hqc hV G hqcG eG
  rw [restrictBundleMap, Category.assoc, Category.assoc,
    Stacks.AlgebraicGeometry.RelativeProjMapDomain.chart_comp_toBase, ← h2]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [Iso.inv_comp_eq, ← reassoc_of% h1]

/-- **The degree-one twist on the chart of `𝐏(ℰ)` over `V` is the twisting sheaf**, through the
chart identification of the canonical twist datum. -/
def chartTwistIso :
    (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart V hV)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
        ((schemeSheafGradedAlgebra E hqc).grading V) 1 :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart V hV)).app _).symm ≪≫
    (projectiveBundleTwistData E hqc).chartData.chartIso V hV 1

/-- **The twist of `𝐏(ℰ)` pulled back along `restrictBundleMap` is the twist of `𝐏(𝒢)`.** -/
def restrictBundleTwistIso :
    (Scheme.Modules.pullback (restrictBundleMap E hqc hV G hqcG eG)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist G hqcG := by
  haveI := isAffine_of_isAffineOpen hV
  let t := Stacks.FiniteMorphismProjective.projTopIso (schemeSheafGradedAlgebra G hqcG)
    (relativeProj (schemeSheafGradedAlgebra G hqcG))
  let Ψ := asIso (restrictProjMap E hqc hV G hqcG eG)
  let c := (relativeProj (schemeSheafGradedAlgebra E hqc)).chart V hV
  let L := Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc
  have hΘ : restrictBundleMap E hqc hV G hqcG eG = t.inv ≫ Ψ.inv ≫ c := rfl
  refine (Scheme.Modules.pullbackCongr hΘ).app L ≪≫
    ((Scheme.Modules.pullbackComp t.inv (Ψ.inv ≫ c)).app L).symm ≪≫
    (Scheme.Modules.pullback t.inv).mapIso
      (((Scheme.Modules.pullbackComp Ψ.inv c).app L).symm ≪≫
        (Scheme.Modules.pullback Ψ.inv).mapIso (chartTwistIso E hqc hV) ≪≫
        (Scheme.Modules.pullback Ψ.inv).mapIso
          (asIso (Stacks.ProjTwistComparison.twistMap (restrictGradedHom E hqc hV G hqcG eG)
            (irrelevant_le_map_restrictGradedHom E hqc hV G hqcG eG) 1)).symm ≪≫
        pullbackInvHomIso Ψ _ ≪≫
        ((projectiveBundleTwistData G hqcG).chartData.chartIso ⊤ (isAffineOpen_top _) 1).symm ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback t.hom).app _) ≪≫
    pullbackInvHomIso t _

/-- The image of `restrictBundleMap` is the part of `𝐏(ℰ)` lying over `V`. -/
theorem opensRange_restrictBundleMap :
    (restrictBundleMap E hqc hV G hqcG eG).opensRange =
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V := by
  have := isAffine_of_isAffineOpen hV
  change ((Stacks.FiniteMorphismProjective.projTopIso (schemeSheafGradedAlgebra G hqcG)
      (relativeProj (schemeSheafGradedAlgebra G hqcG))).inv ≫
    inv (restrictProjMap E hqc hV G hqcG eG) ≫
    (relativeProj (schemeSheafGradedAlgebra E hqc)).chart V hV).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_comp_of_isIso, ← Scheme.Hom.image_top_eq_opensRange]
  exact Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top _ V hV

/-- **The part of `𝐏(ℰ)` lying over an affine open `V` is `𝐏(𝒢)`**, for `𝒢` identified with
`ℰ|_V`. -/
def restrictBundleIso :
    (relativeProj (schemeSheafGradedAlgebra G hqcG)).scheme ≅
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V).toScheme :=
  (restrictBundleMap E hqc hV G hqcG eG).isoOpensRange ≪≫
    Scheme.isoOfEq _ (opensRange_restrictBundleMap E hqc hV G hqcG eG)

/-- `restrictBundleIso` followed by the inclusion of `π ⁻¹ V` into `𝐏(ℰ)` is
`restrictBundleMap`. -/
@[reassoc (attr := simp)]
theorem restrictBundleIso_hom_ι :
    (restrictBundleIso E hqc hV G hqcG eG).hom ≫
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V).ι =
      restrictBundleMap E hqc hV G hqcG eG := by
  simp [restrictBundleIso]

/-- **The isomorphism lies over `V`.** -/
theorem restrictBundleIso_hom_morphismRestrict :
    (restrictBundleIso E hqc hV G hqcG eG).hom ≫
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ∣_ V) =
      (relativeProj (schemeSheafGradedAlgebra G hqcG)).toBase := by
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, restrictBundleIso_hom_ι_assoc,
    restrictBundleMap_toBase]

/-- **The isomorphism carries `𝒪_{𝐏(ℰ)}(1)`, restricted to the part over `V`, to
`𝒪_{𝐏(𝒢)}(1)`.** -/
def restrictBundleIsoTwistIso :
    (Scheme.Modules.pullback (restrictBundleIso E hqc hV G hqcG eG).hom).obj
        ((Scheme.Modules.pullback
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V).ι).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist G hqcG :=
  (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (restrictBundleIso_hom_ι E hqc hV G hqcG eG)).app _ ≪≫
    restrictBundleTwistIso E hqc hV G hqcG eG

end Stacks.ProjectiveBundle

end
