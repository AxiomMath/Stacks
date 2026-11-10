module

public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalComparison
public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalTransport
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.SectionsDeRhamComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleValuedRefinement
public import StacksFrontier.AlgebraicGeometry.DeRham.CechCupProduct
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.RestrictScalarsCechComputes
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# The elementwise total Čech complex of the de Rham complex computes de Rham cohomology

Let `p : X ⟶ S` be a morphism of schemes and `U` an open covering of `X`. The elementwise total
Čech complex `Tot(Č(U, Ω^•_{X/S}))` of the sections of the relative de Rham complex, a complex of
`Γ(S, 𝒪_S)`-modules (`Stacks.CategoryTheory.CechComplex.cechTot` of
`AlgebraicGeometry.Scheme.Hom.sectionsDeRhamComplex`), is the total Čech complex of the
library's comparison with derived global sections (`Stacks.Cech.Hypercohomology.cech`), with its
scalars restricted along `Γ(S, 𝒪_S) ⟶ Γ(X, p⁻¹𝒪_S)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ComplexShape
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheafFunctor)
open Stacks.CategoryTheory.CechComplex

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The sheaf of rings `p⁻¹𝒪_S` over which the relative de Rham complex is a complex of modules. -/
abbrev baseSheaf : TopCat.Sheaf CommRingCat.{u} X.carrier :=
  (TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf

/-- The ring map `Γ(S, 𝒪_S) ⟶ Γ(X, p⁻¹𝒪_S)`. -/
abbrev baseRingHom : Γ(S, ⊤) →+* SectionRing (ringSheaf (baseSheaf p)) ⊤ :=
  (Scheme.Hom.inverseImageGlobalSections p).hom

/-- **The relative de Rham complex, restricted to the opens of `X`**: the `ℕ`-indexed complex of
presheaves of `Γ(X, p⁻¹𝒪_S)`-modules on the slice over `X` of which the library's Čech
complexes are formed. -/
def sliceDeRhamComplex :
    CochainComplex ((Over (⊤ : X.Opens))ᵒᵖ ⥤
      ModuleCat.{u} (SectionRing (ringSheaf (baseSheaf p)) ⊤)) ℕ :=
  haveI := Stacks.Cohomology.CechDerived.preservesZeroMorphisms_sectionsPresheafFunctor.{u}
    (ringSheaf (baseSheaf p)) ⊤
  ((sectionsPresheafFunctor ⊤).mapHomologicalComplex (up ℕ)).obj
    (SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)))

/-- The two actions of `Γ(S, 𝒪_S)` on the sections of `Ω^b_{X/S}` over an open agree: through
`Γ(X, p⁻¹𝒪_S)` and the structure map, or through `p^♯`. -/
theorem slice_smul (b : ℕ) (W : Over (⊤ : X.Opens)) (r : Γ(S, ⊤))
    (x : ((restrictComplex (baseRingHom p) (sliceDeRhamComplex p)).X b).obj (op W)) :
    r • x = (show ((overComplex p.sectionsDeRhamComplex).X b).obj (op W) from
      letI := baseModule p (Scheme.Hom.relativeDifferentialForms p (b : ℤ)) W.left
      (r • (show Γ(Scheme.Hom.relativeDifferentialForms p (b : ℤ), W.left) from x))) := by
  change (show Γ(X, W.left) from (inverseImageStructureMap p).hom.app (op W.left)
      ((baseSheaf p).obj.map (homOfLE (le_top : W.left ≤ ⊤)).op
        (Scheme.Hom.inverseImageGlobalSections p r))) •
      (show Γ(Scheme.Hom.relativeDifferentialForms p (b : ℤ), W.left) from x) = _
  rw [Scheme.Hom.inverseImageStructureMap_app_map_inverseImageGlobalSections p W.left r]
  rfl

/-- **The slice de Rham complex, read over `Γ(S, 𝒪_S)`, is the de Rham complex of sections**
restricted to the slice, in each degree. -/
def sliceIsoX (b : ℕ) :
    (restrictComplex (baseRingHom p) (sliceDeRhamComplex p)).X b ≅
      (overComplex p.sectionsDeRhamComplex).X b :=
  NatIso.ofComponents
    (fun W => LinearEquiv.toModuleIso (show
        ((restrictComplex (baseRingHom p) (sliceDeRhamComplex p)).X b).obj W ≃ₗ[Γ(S, ⊤)]
          ((overComplex p.sectionsDeRhamComplex).X b).obj W from
      { toFun := fun x => (x : ((overComplex p.sectionsDeRhamComplex).X b).obj W)
        invFun := fun x =>
          (x : ((restrictComplex (baseRingHom p) (sliceDeRhamComplex p)).X b).obj W)
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => slice_smul p b W.unop r x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }))
    (fun _ => rfl)

/-- **The slice de Rham complex, read over `Γ(S, 𝒪_S)`, is the de Rham complex of sections
restricted to the slice.** -/
def sliceIso :
    restrictComplex (baseRingHom p) (sliceDeRhamComplex p) ≅
      overComplex p.sectionsDeRhamComplex :=
  HomologicalComplex.Hom.isoOfComponents (sliceIsoX p) (fun _ _ _ => by
    ext W x
    rfl)

/-- The relative de Rham complex as a bounded below complex of `p⁻¹𝒪_S`-modules, the complex
whose hypercohomology is `H^*_{dR}(X/S)`. -/
abbrev deRhamPlus :=
  SheafOfModules.deRhamComplexPlus (Scheme.Hom.deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))

/-- The `ℤ`-indexed slice de Rham complex the library's Čech complexes are formed of. -/
abbrev sliceDeRhamComplexInt :=
  (Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor (baseSheaf p) ⊤).obj (deRhamPlus p).obj

/-- In a nonnegative degree the `ℤ`-indexed slice de Rham complex is the `ℕ`-indexed one. -/
def sliceExtendXIso (b : ℕ) : (sliceDeRhamComplexInt p).X (b : ℤ) ≅ (sliceDeRhamComplex p).X b :=
  (sectionsPresheafFunctor ⊤).mapIso
    ((SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).extendXIso
        embeddingUpNat rfl)

/-- The isomorphisms `sliceExtendXIso` commute with the differentials of the `ℤ`-indexed and
`ℕ`-indexed slice de Rham complexes. -/
theorem sliceExtendXIso_comm (b : ℕ) :
    (sliceDeRhamComplexInt p).d b (b + 1) ≫ (sliceExtendXIso p (b + 1)).hom =
      (sliceExtendXIso p b).hom ≫ (sliceDeRhamComplex p).d b (b + 1) := by
  let C := SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))
  have h := HomologicalComplex.extend_d_eq C embeddingUpNat (i := b) (j := b + 1)
    (i' := (b : ℤ)) (j' := (b : ℤ) + 1) rfl (by simp)
  have h2 := congrArg (fun φ => (sectionsPresheafFunctor ⊤).map φ ≫
    (sectionsPresheafFunctor ⊤).map (C.extendXIso embeddingUpNat (i := b + 1)
      (i' := (b : ℤ) + 1) (by simp)).hom) h
  simp only [← Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h2
  exact h2.trans (Functor.map_comp _ _ _)

/-- In a negative degree the `ℤ`-indexed extension of the de Rham complex is zero. -/
private theorem isZero_deRhamComplex_extend_X_of_neg (a : ℤ) (ha : a < 0) :
    IsZero (((SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).extend
        embeddingUpNat).X a) :=
  HomologicalComplex.isZero_extend_X _ embeddingUpNat a fun b hb => by
    have : ((b : ℕ) : ℤ) = a := hb
    omega

/-- In a negative degree the `ℤ`-indexed slice de Rham complex is zero. -/
theorem isZero_sliceDeRhamComplexInt_X (a : ℤ) (ha : a < 0) :
    IsZero ((sliceDeRhamComplexInt p).X a) := by
  have := Stacks.Cohomology.CechDerived.preservesZeroMorphisms_sectionsPresheafFunctor.{u}
    (ringSheaf (baseSheaf p)) ⊤
  exact (sectionsPresheafFunctor ⊤).map_isZero (isZero_deRhamComplex_extend_X_of_neg p a ha)

variable {ι : Type u} (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i)

/-- **The elementwise total Čech complex of the de Rham complex of sections is the library's
total Čech complex of the de Rham complex**, read over `Γ(S, 𝒪_S)`. -/
def cechIso : cechTot U p.sectionsDeRhamComplex ≅
    ((ModuleCat.restrictScalars (baseRingHom p)).mapHomologicalComplex _).obj
      ((Stacks.Cech.Hypercohomology.cech (baseSheaf p) U hU).obj (deRhamPlus p).obj) :=
  letI := Stacks.Cech.ModuleCupProduct.sectionCommRing (baseSheaf p) ⊤
  cechTotOverIso U (fun _ => le_top) p.sectionsDeRhamComplex ≪≫
    cechTotMapIso _ (sliceIso p).symm ≪≫
    cechTotRestrictIso _ (baseRingHom p) (sliceDeRhamComplex p) ≪≫
    ((ModuleCat.restrictScalars (baseRingHom p)).mapHomologicalComplex _).mapIso
      (totalCechIso (coverObject U hU) (sliceDeRhamComplexInt p) (sliceDeRhamComplex p)
        (sliceExtendXIso p) (isZero_sliceDeRhamComplexInt_X p) (sliceExtendXIso_comm p)).symm

/-- Homology commutes with restriction of scalars. -/
def restrictScalarsHomologyIso {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')
    (K : CochainComplex (ModuleCat.{u} R') ℤ) (i : ℤ) :
    (((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj K).homology i ≅
      (ModuleCat.restrictScalars φ).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (ModuleCat.restrictScalars φ)

/-- **The class in `H^N_{dR}(X/S)` of a cohomology class of the elementwise total Čech
complex**, through the library's Čech class map. -/
def classMap (N : ℤ) :
    (cechTot U p.sectionsDeRhamComplex).homology N ⟶ Scheme.Hom.deRhamCohomologyBaseModule p N :=
  HomologicalComplex.homologyMap (cechIso p U hU).hom N ≫
    (letI := Stacks.Cech.ModuleCupProduct.sectionCommRing (baseSheaf p) ⊤;
      restrictScalarsHomologyIso (baseRingHom p) _ N).hom ≫
      (ModuleCat.restrictScalars (baseRingHom p)).map
        (Stacks.Cech.Hypercohomology.cechClass (baseSheaf p) U hU (deRhamPlus p) N ≫
          (SheafOfModules.hypercohomologyIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras p)
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) N).hom)

attribute [local instance] HasDerivedCategory.standard in
/-- **The terms of the de Rham complex are acyclic on the intersections of an affine covering** of
a scheme with affine diagonal: they are quasi-coherent modules read over `p⁻¹𝒪_S`
([Stacks, Tag 01XB]). -/
theorem acyclic_deRhamPlus [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hUaff : ∀ i, IsAffineOpen (U i)) (q : ℤ) (r : ℕ) (s : Fin (r + 1) → ι) (m : ℕ)
    (hm : 0 < m) :
    IsZero (((SheafOfModules.evaluation.{u} (ringSheaf (baseSheaf p))
      (op (⨅ k, U (s k)))).rightDerived m).obj ((deRhamPlus p).1.X q)) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms p n
    have h0 :=
      Stacks.Cech.Hypercohomology.isZero_rightDerived_singlePlus_restrictScalars_of_isAffineOpen
        X (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p)) U hUaff
        (Scheme.Hom.relativeDifferentialForms p (n : ℤ)) 0 r s m hm
    change IsZero (((SheafOfModules.evaluation.{u} (ringSheaf (baseSheaf p))
      (op (⨅ k, U (s k)))).rightDerived m).obj ((SheafOfModules.deRhamComplexInt
        (Scheme.Hom.deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).X (n : ℤ)))
    rw [SheafOfModules.deRhamComplexInt_X_of_nonneg _ _ _ (Int.natCast_nonneg n)]
    exact h0.of_iso (((SheafOfModules.evaluation.{u} (ringSheaf (baseSheaf p))
      (op (⨅ k, U (s k)))).rightDerived m).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _)).symm
  · have hz : IsZero ((deRhamPlus p).1.X q) := isZero_deRhamComplex_extend_X_of_neg p q (by omega)
    have := Stacks.Cohomology.FlasqueAcyclic.evaluation_additive.{u, u} (ringSheaf (baseSheaf p))
      (op (⨅ k, U (s k)))
    exact Functor.map_isZero _ hz

/-- **The class map is bijective** on a covering by affine opens of a scheme with affine
diagonal: the Čech class map of such a covering is an isomorphism ([Stacks, Tag 0FLH]). -/
theorem bijective_classMap [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hUaff : ∀ i, IsAffineOpen (U i)) (N : ℤ) : Function.Bijective (classMap p U hU N).hom := by
  have hc := Stacks.Cech.Hypercohomology.bijective_cechClass_of_acyclic (baseSheaf p) U hU
    (deRhamPlus p) (acyclic_deRhamPlus p U hUaff) N
  have h1 := ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMapIso (cechIso p U hU) N).hom
  have h2 :=
    let := Stacks.Cech.ModuleCupProduct.sectionCommRing (baseSheaf p) ⊤
    ConcreteCategory.bijective_of_isIso
      (restrictScalarsHomologyIso (baseRingHom p)
        ((Stacks.Cech.Hypercohomology.cech (baseSheaf p) U hU).obj (deRhamPlus p).obj) N).hom
  have h3 : Function.Bijective
      (SheafOfModules.hypercohomologyIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) N).hom.hom :=
    (SheafOfModules.hypercohomologyIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) N).toLinearEquiv.bijective
  exact (h3.comp hc).comp (h2.comp h1)

end AlgebraicGeometry.DeRhamKatzOdaCech

end
