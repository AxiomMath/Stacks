module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedExtendRestrictKFlat
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedExtensionOfScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedConstantSheaf
public import StacksFrontier.Homology.KFlat.BifunctorOneSided

/-!
# The action of `Λ₂` on restrictions of complexes of `Λ₂`-modules

Let `φ : Λ₁ → Λ₂` be a homomorphism of commutative rings and `X` a scheme.  The counit of
derived extension of coefficients `- ⊗^L_{Λ₁} Λ₂ ⊣ res_φ`, read through
`res(E ⊗^L_{Λ₁} Λ₂) ≅ E ⊗^L_{Λ₁} Λ̲₂`, is an action map `res(d) ⊗^L_{Λ₁} Λ̲₂ ⟶ res(d)` for
`d ∈ D(X_étale, Λ₂)`.  This file computes it on a complex `J` of `Λ₂`-modules: against a resolution
`N ⟶ Λ₂` of `Λ₂` by a complex whose constant sheaf complexes are K-flat, it is the total complex
`Tot(res J ⊗ N̲)` mapped to `res J ⊗ Λ̲₂` and then by the sheaf-level action `res J ⊗ Λ̲₂ ⟶ res J`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CochainComplex.KFlatBifunctor

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

/- The instance proofs `F.Additive`, `(F.obj X).Additive` and `HasMapBifunctor` for the tensor
product over `Λ₁` are the named ones of `ModuleTensor.TensorBifunctorInstances`, stated as
`etaleModuleDerivedTensor` records them, so that every `derivedBifunctor (etaleModuleTensor Λ₁ X)`
written here is the unfolding of `etaleModuleDerivedTensor Λ₁ X` up to proofs of the same
propositions; with independently synthesized proofs the kernel compares the two by evaluating the
derived bifunctor, which is prohibitively slow. -/
attribute [local instance high] etaleModuleTensor_additive etaleModuleTensor_obj_additive
  etaleModuleTensor_hasTotal_mapBifunctor

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂) (X : Scheme.{u})

/-- **The action of `Λ₂` on the restriction of a sheaf of `Λ₂`-modules**,
`res F ⊗_{Λ₁} Λ̲₂ ⟶ res F`: the counit of extension of coefficients read through
`res(G ⊗_{Λ₁} Λ₂) ≅ G ⊗_{Λ₁} Λ̲₂`. -/
def etaleModuleCoefficientAction :
    etaleModuleRestrictScalarsUniv.{u, r} φ X ⋙ tensorRight (coefficientSheaf.{u} φ X) ⟶
      etaleModuleRestrictScalarsUniv.{u, r} φ X :=
  Functor.whiskerLeft (etaleModuleRestrictScalarsUniv.{u, r} φ X)
      (etaleModuleExtendRestrictScalarsIso.{u, r} φ X).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleModuleExtendRestrictAdj.{u, r} φ X).counit
      (etaleModuleRestrictScalarsUniv.{u, r} φ X) ≫
    (etaleModuleRestrictScalarsUniv.{u, r} φ X).leftUnitor.hom

/-- **The derived action of `Λ₂`**, `res(d) ⊗^L_{Λ₁} Λ̲₂ ⟶ res(d)` for `d ∈ D(X_étale, Λ₂)`. -/
def etaleModuleDerivedCoefficientAction (d : DerivedCategory (EtaleModules.{u, r} Λ₂ X)) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d)).obj
        (DerivedCategory.Q.obj (coefficientSheafComplex.{u, r} φ X)) ⟶
      (etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d :=
  (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ X).inv.app
      ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d) ≫
    (etaleModuleDerivedRestrictScalars.{u, r} φ X).map
      ((etaleModuleDerivedExtendRestrictAdj.{u, r} φ X).counit.app d)

/-- The comparison of the constant sheaf complex of a resolution `N ⟶ Λ₂` with `Λ̲₂` in degree
zero. -/
def coefficientSheafComplexMap (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ)) :
    ((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶
      coefficientSheafComplex.{u, r} φ X :=
  ((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫
    (HomologicalComplex.singleMapHomologicalComplex (etaleModuleConstantSheafFunctor.{u, r} Λ₁ X)
      (ComplexShape.up ℤ) 0).hom.app (coefficientModule.{u} φ)

/-- The chain-level action against a resolution `q : N ⟶ Λ₂`:
`Tot(res J ⊗ N̲) ⟶ Tot(res J ⊗ Λ̲₂[0]) ≅ res J ⊗ Λ̲₂ ⟶ res J`. -/
def etaleModuleTotalCoefficientAction (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ)
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ)) :
    totalComplex (etaleModuleTensor.{u, r} Λ₁ X)
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) ⟶
      ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J :=
  (((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj _).map (coefficientSheafComplexMap φ X N q) ≫
    (totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) _ (coefficientSheaf.{u} φ X) ≪≫
      rowComplexIsoMapTensorRight X _ (coefficientSheaf.{u} φ X)).hom ≫
    (NatTrans.mapHomologicalComplex (etaleModuleCoefficientAction φ X) (ComplexShape.up ℤ)).app J

/-- The composite of four commutative squares, in the shape used for the chain-level square of
`etaleModuleTotalCoefficientAction_comm`. -/
theorem comp_four_squares {C : Type*} [Category C] {x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : C}
    (a₁ : x₁ ⟶ x₂) (c₂ : x₂ ⟶ x₃) (c₁ : x₁ ⟶ x₄) (a₂ : x₄ ⟶ x₃) (t : x₂ ⟶ x₅) (t' : x₃ ⟶ x₆)
    (m₁ : x₅ ⟶ x₆) (i : x₅ ⟶ x₇) (i' : x₆ ⟶ x₈) (m₂ : x₇ ⟶ x₈) (k : x₈ ⟶ x₉) (act : x₆ ⟶ x₉)
    (f : x₇ ⟶ x₉) (g : x₄ ⟶ x₉)
    (h₁ : a₁ ≫ c₂ = c₁ ≫ a₂) (h₂ : c₂ ≫ t' = t ≫ m₁) (h₃ : m₁ ≫ i' = i ≫ m₂)
    (h₄ : i' ≫ k = act) (h₅ : f = m₂ ≫ k) (h₆ : g = a₂ ≫ t' ≫ act) :
    (a₁ ≫ t ≫ i) ≫ f = c₁ ≫ g := by
  subst h₅ h₆ h₄
  rw [Category.assoc, Category.assoc, ← reassoc_of% h₃, ← reassoc_of% h₂, reassoc_of% h₁]

/-- Degreewise, the identification `res(ext(res J)) ≅ res J ⊗ Λ̲₂` followed by the counit is the
sheaf-level action of `Λ₂`. -/
theorem mapHomologicalComplexCompIso_inv_app_comp_counit
    (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ) :
    (Functor.mapHomologicalComplexCompIso (etaleModuleExtendRestrictScalarsIso.{u, r} φ X)
        (ComplexShape.up ℤ)).inv.app
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J) ≫
      ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (etaleModuleExtendRestrictAdj.{u, r} φ X).counit
          (ComplexShape.up ℤ)).app J) =
      (NatTrans.mapHomologicalComplex (etaleModuleCoefficientAction φ X)
        (ComplexShape.up ℤ)).app J := by
  ext n
  simp [etaleModuleCoefficientAction]

/-- **The chain-level square** behind `etaleModuleDerivedCoefficientAction_fac`: for a map
`p : P ⟶ res J`, the total complex `Tot(P ⊗ N̲)` mapped to `res(ext(res J))` through `P ⊗ Λ̲₂`
and the counit agrees with `Tot(p ⊗ N̲)` followed by the chain-level action. -/
theorem etaleModuleTotalCoefficientAction_comm (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ)
    {P : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ}
    (p : P ⟶ ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J)
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ)) :
    ((((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).map (coefficientSheafComplexMap φ X N q) ≫
      (totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) P (coefficientSheaf.{u} φ X) ≪≫
        rowComplexIsoMapTensorRight X P (coefficientSheaf.{u} φ X)).hom ≫
      (Functor.mapHomologicalComplexCompIso (etaleModuleExtendRestrictScalarsIso.{u, r} φ X)
        (ComplexShape.up ℤ)).inv.app P) ≫
      ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).map p ≫
          (NatTrans.mapHomologicalComplex (etaleModuleExtendRestrictAdj.{u, r} φ X).counit
            (ComplexShape.up ℤ)).app J) =
      (((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map p).app _ ≫
        etaleModuleTotalCoefficientAction φ X J N q := by
  have h₁ := (((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map p).naturality (coefficientSheafComplexMap φ X N q)
  have h₂ := totalSingleIso_trans_rowComplexIsoMapTensorRight_naturality φ X p
  have h₃ := (Functor.mapHomologicalComplexCompIso (etaleModuleExtendRestrictScalarsIso.{u, r} φ X)
    (ComplexShape.up ℤ)).inv.naturality p
  have h₄ := mapHomologicalComplexCompIso_inv_app_comp_counit φ X J
  exact comp_four_squares _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ (Functor.map_comp _ _ _) rfl

/-- The diagram chase behind `etaleModuleDerivedCoefficientAction_fac`, for an arbitrary adjunction
counit `ε`, isomorphism `Φ : E ⋙ R ≅ T.flip.obj s` and bifunctor `T`.  The map `k ≫ finv` from an
object `x` (the class of a resolution) to `R.obj d` is invertible, so it suffices to compare both
sides after precomposition with it; the hypotheses compute each side there. -/
theorem coefficientAction_fac_aux {D₁ D₂ : Type*} [Category D₁] [Category D₂]
    (T : D₁ ⥤ D₁ ⥤ D₁) (R : D₂ ⥤ D₁) (E : D₁ ⥤ D₂) (ε : R ⋙ E ⟶ 𝟭 D₂) {s n : D₁}
    (Φ : E ⋙ R ≅ T.flip.obj s) (cq : n ⟶ s) (d : D₂) {b x y z t : D₁} {v : D₂}
    (fh : R.obj d ⟶ b) (finv : b ⟶ R.obj d) (hf : finv ≫ fh = 𝟙 b) (k : x ⟶ b) [IsIso k]
    [IsIso finv] {v₁ v₂ : D₂} (α₁ : E.obj x ⟶ v₁) (α₂ : v₁ ⟶ v₂) (α₃ : v₂ ⟶ v) (w : v ⟶ d)
    (hε : E.map (k ≫ finv) ≫ ε.app d = α₁ ≫ α₂ ≫ α₃ ≫ w)
    (Z : (T.obj x).obj n ⟶ y) (a₁ : y ⟶ z) (exQi : z ⟶ R.obj v)
    (hΦ : (T.obj x).map cq ≫ Φ.inv.app x ≫ R.map (α₁ ≫ α₂ ≫ α₃) = Z ≫ a₁ ≫ exQi)
    (a₂ : z ⟶ b) (hw : exQi ≫ R.map w = a₂ ≫ finv)
    (cR : (T.obj b).obj n ⟶ t) (a₃ : y ⟶ t) (hcR : (T.map k).app n ≫ cR = Z ≫ a₃)
    (a₄ : t ⟶ b) (hchain : a₁ ≫ a₂ = a₃ ≫ a₄) :
    (T.obj (R.obj d)).map cq ≫ (Φ.inv.app (R.obj d) ≫ R.map (ε.app d)) =
      (T.map fh).app n ≫ cR ≫ a₄ ≫ finv := by
  rw [← cancel_epi ((T.map (k ≫ finv)).app n)]
  have e₁ : (T.map (k ≫ finv)).app n ≫ (T.obj (R.obj d)).map cq =
      (T.obj x).map cq ≫ (T.map (k ≫ finv)).app s := ((T.map (k ≫ finv)).naturality cq).symm
  have e₂ : (T.map (k ≫ finv)).app s ≫ Φ.inv.app (R.obj d) =
      Φ.inv.app x ≫ R.map (E.map (k ≫ finv)) := Φ.inv.naturality (k ≫ finv)
  have e₃ : (T.map (k ≫ finv)).app n ≫ (T.map fh).app n = (T.map k).app n := by
    rw [← NatTrans.comp_app, ← T.map_comp, Category.assoc, hf, Category.comp_id]
  have e₄ : R.map (E.map (k ≫ finv)) ≫ R.map (ε.app d) = R.map (α₁ ≫ α₂ ≫ α₃) ≫ R.map w := by
    rw [← R.map_comp, ← R.map_comp, hε]
    simp only [Category.assoc]
  rw [reassoc_of% e₁, reassoc_of% e₂, e₄, reassoc_of% e₃, reassoc_of% hcR, reassoc_of% hΦ, hw,
    reassoc_of% hchain]

/-- The diagram chase computing the derived action on the class of a complex `P` K-flat in the
left variable, for an arbitrary isomorphism `I : LF ⋙ RG ≅ T.flip.obj s` whose value at `x` is
known (`hE2`): it is pushed along `j : y ⟶ x` and along `cq : n ⟶ s` by naturality. -/
theorem coefficientAction_iso_aux {D₁ D₂ : Type*} [Category D₁] [Category D₂]
    (T : D₁ ⥤ D₁ ⥤ D₁) (RG : D₂ ⥤ D₁) (LF : D₁ ⥤ D₂) {s n : D₁} (I : LF ⋙ RG ≅ T.flip.obj s)
    (cq : n ⟶ s) {x y : D₁} (j : y ⟶ x) {w₀ w : D₂} (α₀ : LF.obj x ⟶ w₀) (qc : w₀ ⟶ w)
    {m zS zN tS tN b : D₁} (E3h : RG.obj w₀ ⟶ m) (exQ : RG.obj w ≅ m)
    (hE3' : E3h = RG.map qc ≫ exQ.hom) (tQ : zS ≅ m) (cS : (T.obj x).obj s ≅ zS)
    (hE2 : I.hom.app x = RG.map α₀ ≫ E3h ≫ tQ.inv ≫ cS.inv)
    (ci : m ⟶ b) (facinv : b ⟶ RG.obj w) (hE3 : exQ.inv = ci ≫ facinv)
    (totS : zS ⟶ tS) (ts : tS ⟶ m) (hE4 : tQ.hom = totS ≫ ts)
    (cN : (T.obj x).obj n ⟶ zN) (hcq : zN ⟶ zS) (h₆ : (T.obj x).map cq ≫ cS.hom = cN ≫ hcq)
    (totN : zN ⟶ tN) (totcq : tN ⟶ tS) (h₇ : hcq ≫ totS = totN ≫ totcq)
    (cR : (T.obj y).obj n ⟶ tN) (h₈ : (T.map j).app n ≫ cN ≫ totN = cR)
    (v : tN ⟶ b) (hv : v = totcq ≫ ts ≫ ci) :
    (T.obj y).map cq ≫ I.inv.app y ≫ RG.map (LF.map j ≫ α₀ ≫ qc) = cR ≫ v ≫ facinv := by
  subst hE3' hv h₈
  have i₂ : I.inv.app x ≫ RG.map α₀ ≫ RG.map qc = cS.hom ≫ tQ.hom ≫ exQ.inv := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, hE2]
    simp
  have e₁ : (T.map j).app s ≫ I.inv.app x = I.inv.app y ≫ RG.map (LF.map j) :=
    I.inv.naturality j
  have e₂ : (T.obj y).map cq ≫ (T.map j).app s = (T.map j).app n ≫ (T.obj x).map cq :=
    (T.map j).naturality cq
  rw [RG.map_comp, RG.map_comp, ← reassoc_of% e₁, reassoc_of% e₂, i₂, reassoc_of% h₆, hE4, hE3]
  simp only [Category.assoc]
  rw [reassoc_of% h₇]

/-- The one-sided factorisation `comparisonLeftFac` at a complex `P` K-flat in the left variable,
read against the derived tensor product `etaleModuleDerivedTensor`. -/
def etaleModuleComparisonLeftFacApp (P : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (hP : KFlatLeft (etaleModuleTensor.{u, r} Λ₁ X) P)
    (G : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj P)).obj
        (DerivedCategory.Q.obj G) ≅
      ((totalToDerivedLeft (etaleModuleTensor.{u, r} Λ₁ X)).obj G).obj
        ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩ :=
  ((comparisonLeftFac (etaleModuleTensor.{u, r} Λ₁ X)).app G).app
    ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩

/-- Naturality of `etaleModuleComparisonLeftFacApp` in the right complex. -/
theorem etaleModuleComparisonLeftFacApp_naturality
    (P : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (hP : KFlatLeft (etaleModuleTensor.{u, r} Λ₁ X) P)
    {G G' : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ} (g : G ⟶ G') :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj P)).map
        (DerivedCategory.Q.map g) ≫ (etaleModuleComparisonLeftFacApp X P hP G').hom =
      (etaleModuleComparisonLeftFacApp X P hP G).hom ≫
        ((totalToDerivedLeft (etaleModuleTensor.{u, r} Λ₁ X)).map g).app
          ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩ :=
  NatTrans.congr_app ((comparisonLeftFac (etaleModuleTensor.{u, r} Λ₁ X)).hom.naturality g)
    ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩

/-- The one-sided comparison `comparisonRight` against a K-flat complex `G`, read against the
derived tensor product `etaleModuleDerivedTensor`. -/
def etaleModuleComparisonRight (K G : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (hG : KFlat (etaleModuleTensor.{u, r} Λ₁ X) G) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj G) ⟶
      DerivedCategory.Q.obj (totalComplex (etaleModuleTensor.{u, r} Λ₁ X) K G) :=
  (comparisonRight (etaleModuleTensor.{u, r} Λ₁ X) K G hG).hom

/-- Naturality of `etaleModuleComparisonRight` in the left complex. -/
theorem etaleModuleComparisonRight_naturality_left
    {K K' : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ} (f : K ⟶ K')
    (G : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (hG : KFlat (etaleModuleTensor.{u, r} Λ₁ X) G) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).map (DerivedCategory.Q.map f)).app
        (DerivedCategory.Q.obj G) ≫ (comparisonRight (etaleModuleTensor.{u, r} Λ₁ X) K' G hG).hom =
      etaleModuleComparisonRight X K G hG ≫
        DerivedCategory.Q.map
          ((((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).app G) :=
  comparisonRight_naturality_left _ f G hG

/-- On a complex `P` K-flat in the left variable, `comparisonRight` is computed by
`etaleModuleComparisonLeftFacApp`, as is `comparisonLeft`. -/
theorem etaleModuleComparisonLeftFacApp_comparisonRight
    (P : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (hP : KFlatLeft (etaleModuleTensor.{u, r} Λ₁ X) P)
    (G : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (hG : KFlat (etaleModuleTensor.{u, r} Λ₁ X) G) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).map
        ((DerivedCategory.quotientCompQhIso _).inv.app P)).app (DerivedCategory.Q.obj G) ≫
      (etaleModuleComparisonLeftFacApp X P hP G).hom ≫
      (totalComplexQhIso (etaleModuleTensor.{u, r} Λ₁ X) P G).hom =
    etaleModuleComparisonRight X P G hG := by
  have h₁ : (comparisonLeft (etaleModuleTensor.{u, r} Λ₁ X) P G hP).hom =
      (comparisonRight (etaleModuleTensor.{u, r} Λ₁ X) P G hG).hom :=
    congrArg Iso.hom ((comparisonLeft_eq_comparison (etaleModuleTensor.{u, r} Λ₁ X) P G hP
      hG).trans (comparisonRight_eq_comparison (etaleModuleTensor.{u, r} Λ₁ X) P G hP hG).symm)
  rw [etaleModuleComparisonRight, ← h₁, comparisonLeft_hom]
  rfl

/-- `etaleModuleDerivedExtendRestrictScalarsIso_hom_app_kFlatLeft` at `Qh` of the homotopy class,
through `etaleModuleComparisonLeftFacApp`. -/
theorem etaleModuleDerivedExtendRestrictScalarsIso_hom_app_quotient
    (P : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (hP : KFlatLeft (etaleModuleTensor.{u, r} Λ₁ X) P) :
    (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ X).hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj P) =
      (etaleModuleDerivedRestrictScalars.{u, r} φ X).map
          ((etaleModuleDerivedExtendScalarsCounit.{u, r} φ X).app
            ((HomotopyCategory.quotient _ _).obj P)) ≫
        (etaleModuleExtendScalarsRestrictComplexIso.{u, r} φ X).hom.app P ≫
        ((tensorCoefficientSheafComplexIso.{u, r} φ X).app P).inv ≫
        (etaleModuleComparisonLeftFacApp X P hP (coefficientSheafComplex.{u, r} φ X)).inv :=
  etaleModuleDerivedExtendRestrictScalarsIso_hom_app_kFlatLeft φ X P hP

/-- **The derived action at the class of a K-flat-left complex**, pushed along `Q(c q)`: the
isomorphism `res(E ⊗^L Λ₂) ≅ E ⊗^L Λ̲₂` at `Q P`, followed by the derived counit of extension of
coefficients at `P`, is the one-sided comparison against the resolution `N̲` followed by the
degreewise identification `Tot(P ⊗ Λ̲₂[0]) ≅ P ⊗_{Λ₁} Λ̲₂ ≅ res(ext P)`. -/
theorem etaleModuleDerivedExtendRestrictScalarsIso_inv_app_kFlatLeft
    (P : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (hP : KFlatLeft (etaleModuleTensor.{u, r} Λ₁ X) P)
    (N : (constantSheafKFlatObjects.{u, r} Λ₁).FullSubcategory)
    (q : N.obj.as ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (coefficientModule.{u} φ)) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj (DerivedCategory.Q.obj P)).map
        (DerivedCategory.Q.map (coefficientSheafComplexMap φ X N.obj.as q)) ≫
      (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ X).inv.app (DerivedCategory.Q.obj P) ≫
      (etaleModuleDerivedRestrictScalars.{u, r} φ X).map
        ((etaleModuleDerivedExtendScalars.{u, r} φ X).map
            ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
          (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X).app
            ((HomotopyCategory.quotient _ _).obj P) ≫
          (DerivedCategory.quotientCompQhIso _).hom.app
            (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) =
      etaleModuleComparisonRight X P _ (N.property X).1 ≫
      DerivedCategory.Q.map
        ((((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).map
            (coefficientSheafComplexMap φ X N.obj.as q) ≫
          (totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) P (coefficientSheaf.{u} φ X) ≪≫
            rowComplexIsoMapTensorRight X P (coefficientSheaf.{u} φ X)).hom ≫
          (Functor.mapHomologicalComplexCompIso (etaleModuleExtendRestrictScalarsIso.{u, r} φ X)
            (ComplexShape.up ℤ)).inv.app P) ≫
      (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.app
        (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  coefficientAction_iso_aux (etaleModuleDerivedTensor.{u, r} Λ₁ X)
    (etaleModuleDerivedRestrictScalars.{u, r} φ X) (etaleModuleDerivedExtendScalars.{u, r} φ X)
    (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ X)
    (DerivedCategory.Q.map (coefficientSheafComplexMap φ X N.obj.as q))
    ((DerivedCategory.quotientCompQhIso _).inv.app P)
    ((etaleModuleDerivedExtendScalarsCounit.{u, r} φ X).app ((HomotopyCategory.quotient _ _).obj P))
    ((DerivedCategory.quotientCompQhIso _).hom.app
      (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    ((etaleModuleExtendScalarsRestrictComplexIso.{u, r} φ X).hom.app P)
    ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.app
        (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
        (etaleModuleExtendRestrictScalarsIso.{u, r} φ X) (ComplexShape.up ℤ)).app P))
    rfl ((tensorCoefficientSheafComplexIso.{u, r} φ X).app P)
    (etaleModuleComparisonLeftFacApp X P hP (coefficientSheafComplex.{u, r} φ X))
    (etaleModuleDerivedExtendRestrictScalarsIso_hom_app_quotient φ X P hP)
    (DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
      (etaleModuleExtendRestrictScalarsIso.{u, r} φ X) (ComplexShape.up ℤ)).inv.app P))
    ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.app
      (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    rfl
    (totalComplexQhIso (etaleModuleTensor.{u, r} Λ₁ X) P (coefficientSheafComplex.{u, r} φ X)).hom
    (DerivedCategory.Q.map
      (totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) P (coefficientSheaf.{u} φ X) ≪≫
        rowComplexIsoMapTensorRight X P (coefficientSheaf.{u} φ X)).hom)
    (tensorCoefficientSheafComplexIso_hom_app φ X P)
    (etaleModuleComparisonLeftFacApp X P hP _).hom
    (((totalToDerivedLeft (etaleModuleTensor.{u, r} Λ₁ X)).map
      (coefficientSheafComplexMap φ X N.obj.as q)).app ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩)
    (etaleModuleComparisonLeftFacApp_naturality X P hP (coefficientSheafComplexMap φ X N.obj.as q))
    (totalComplexQhIso (etaleModuleTensor.{u, r} Λ₁ X) P
      (((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        N.obj.as)).hom
    (DerivedCategory.Q.map ((((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).map
        (coefficientSheafComplexMap φ X N.obj.as q)))
    (totalComplexQhIso_naturality_right (etaleModuleTensor.{u, r} Λ₁ X) P
      (coefficientSheafComplexMap φ X N.obj.as q))
    (etaleModuleComparisonRight X P _ (N.property X).1)
    (etaleModuleComparisonLeftFacApp_comparisonRight X P hP _ (N.property X).1)
    _ ((DerivedCategory.Q.map_comp _ _).trans (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _)))


/-- **The derived action on a complex.**  Against a resolution `q : N ⟶ Λ₂` with `N` in
`constantSheafKFlatObjects`, the derived action of `Λ₂` on the class of a complex `J` of
`Λ₂`-modules is the class of `etaleModuleTotalCoefficientAction`. -/
theorem etaleModuleDerivedCoefficientAction_fac (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ)
    (N : (constantSheafKFlatObjects.{u, r} Λ₁).FullSubcategory)
    (q : N.obj.as ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (coefficientModule.{u} φ)) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj J))).map
        (DerivedCategory.Q.map (coefficientSheafComplexMap φ X N.obj.as q)) ≫
      etaleModuleDerivedCoefficientAction φ X (DerivedCategory.Q.obj J) =
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).map
        ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.hom.app J)).app _ ≫
      (comparisonRight (etaleModuleTensor.{u, r} Λ₁ X) _ _ (N.property X).1).hom ≫
      DerivedCategory.Q.map (etaleModuleTotalCoefficientAction φ X J N.obj.as q) ≫
      (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.app J := by
  obtain ⟨P, p, hP, hp⟩ := exists_etaleModule_kFlatLeft_quasiIso Λ₁ X
    (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
  have : IsIso (DerivedCategory.Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have hε := etaleModuleDerivedExtendRestrictAdj_counit_app_Q φ X J p
  have hΦ := etaleModuleDerivedExtendRestrictScalarsIso_inv_app_kFlatLeft φ X P hP N q
  have hw : (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.app
        (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
      (etaleModuleDerivedRestrictScalars.{u, r} φ X).map (DerivedCategory.Q.map
        (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).map p ≫
          (NatTrans.mapHomologicalComplex (etaleModuleExtendRestrictAdj.{u, r} φ X).counit
            (ComplexShape.up ℤ)).app J)) =
      DerivedCategory.Q.map
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).map p ≫
            (NatTrans.mapHomologicalComplex (etaleModuleExtendRestrictAdj.{u, r} φ X).counit
              (ComplexShape.up ℤ)).app J)) ≫
        (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.app J :=
    ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.naturality _).symm
  have hcR : ((etaleModuleDerivedTensor.{u, r} Λ₁ X).map (DerivedCategory.Q.map p)).app
        (DerivedCategory.Q.obj
          (((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            N.obj.as)) ≫
      (comparisonRight (etaleModuleTensor.{u, r} Λ₁ X) _ _ (N.property X).1).hom =
      etaleModuleComparisonRight X P _ (N.property X).1 ≫
        DerivedCategory.Q.map
          ((((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map p).app _) :=
    etaleModuleComparisonRight_naturality_left X p _ (N.property X).1
  have hchain : DerivedCategory.Q.map
        ((((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).map
            (coefficientSheafComplexMap φ X N.obj.as q) ≫
          (totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) P (coefficientSheaf.{u} φ X) ≪≫
            rowComplexIsoMapTensorRight X P (coefficientSheaf.{u} φ X)).hom ≫
          (Functor.mapHomologicalComplexCompIso (etaleModuleExtendRestrictScalarsIso.{u, r} φ X)
            (ComplexShape.up ℤ)).inv.app P) ≫
      DerivedCategory.Q.map
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).map p ≫
            (NatTrans.mapHomologicalComplex (etaleModuleExtendRestrictAdj.{u, r} φ X).counit
              (ComplexShape.up ℤ)).app J)) =
      DerivedCategory.Q.map
          ((((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map p).app _) ≫
        DerivedCategory.Q.map (etaleModuleTotalCoefficientAction φ X J N.obj.as q) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
      (etaleModuleTotalCoefficientAction_comm φ X J p N.obj.as q)).trans
        (DerivedCategory.Q.map_comp _ _))
  rw [etaleModuleDerivedCoefficientAction]
  have key := coefficientAction_fac_aux (etaleModuleDerivedTensor.{u, r} Λ₁ X)
    (etaleModuleDerivedRestrictScalars.{u, r} φ X) (etaleModuleDerivedExtendScalars.{u, r} φ X)
    (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X).counit
    (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ X)
    (DerivedCategory.Q.map (coefficientSheafComplexMap φ X N.obj.as q)) (DerivedCategory.Q.obj J)
    ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.hom.app J)
    ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.app J)
    (Iso.inv_hom_id_app _ _) (DerivedCategory.Q.map p) _ _ _ _ hε _ _ _ hΦ _ hw
    (comparisonRight (etaleModuleTensor.{u, r} Λ₁ X) _ _ (N.property X).1).hom _ hcR
    (DerivedCategory.Q.map (etaleModuleTotalCoefficientAction φ X J N.obj.as q)) hchain
  exact key

end Stacks.EtaleCohomology

end
