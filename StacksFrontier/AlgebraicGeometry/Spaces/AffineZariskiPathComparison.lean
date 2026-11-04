module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentDerivedSquareComparison
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsModel

/-!
# The Zariski path of the affine base change on complexes

Let `g_0 : X' ⟶ X`, `j : X ⟶ Spec A`, `j' : X' ⟶ Spec A'` and `c : A ⟶ A'` with
`g_0 ≫ j = j' ≫ Spec c`. For `M ∈ D(A)` there is an isomorphism
`L g_0^* L j^* M^~ ≅ L j'^* (A' ⊗^L_A M)^~` composed of the composition isomorphisms of derived
pullbacks (Stacks 0D5S), the square, the affine comparison of Stacks 08DW and the comparison of the
two models of derived extension of scalars. On a complex `M` it is computed degreewise.

## Main results

* `AlgebraicGeometry.affineZariskiPath_comparison`: the isomorphism
  `L g_0^* L j^* M^~ ≅ L j'^* (A' ⊗^L_A M)^~`, read through the comparisons with degreewise
  pullback, is the degreewise path `affineZariskiPathHomotopy`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

attribute [local instance 10000] extendScalarsSpec_additive

variable {X X' : Scheme.{u}} {A A' : CommRingCat.{u}} (g₀ : X' ⟶ X) (j : X ⟶ Spec A)
  (j' : X' ⟶ Spec A') (c : A ⟶ A') (h : g₀ ≫ j = j' ≫ Spec.map c)
  (P : CochainComplex (ModuleCat.{u} A) ℤ)


section Generic

variable {X₁ X₂ X₃ : Scheme.{u}}

/-- The composition isomorphism of derived pullbacks, read through the comparisons with degreewise
pullback, at a morphism into the localization of a complex. -/
theorem derivedPullbackCompIso_hom_app_comp_map_comparison (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    {E : DerivedCategory X₃.Modules} {W : HomotopyCategory X₃.Modules (ComplexShape.up ℤ)}
    (φ : E ⟶ DerivedCategory.Qh.obj W) :
    (Stacks.Duality.derivedPullbackCompIso f₁ f₂).hom.app E ≫
        (Stacks.Duality.derivedPullback (f₁ ≫ f₂)).map φ ≫
        (Stacks.Duality.derivedPullbackComparison (f₁ ≫ f₂)).app W =
      (Stacks.Duality.derivedPullback f₁).map ((Stacks.Duality.derivedPullback f₂).map φ ≫
          (Stacks.Duality.derivedPullbackComparison f₂).app W) ≫
        (Stacks.Duality.derivedPullbackComparison f₁).app
          (((Scheme.Modules.pullback f₂).mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
        DerivedCategory.Qh.map ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso
          f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.app W) := by
  rw [← Category.assoc, ← (Stacks.Duality.derivedPullbackCompIso f₁ f₂).hom.naturality φ,
    Category.assoc, Stacks.Duality.derivedPullbackCompIso_hom_app_comparison f₁ f₂ W,
    Functor.map_comp, Category.assoc]
  rfl

/-- The inverse of the composition isomorphism of derived pullbacks, read through the comparisons
with degreewise pullback, at a morphism into the localization of a complex. -/
theorem derivedPullbackCompIso_inv_app_comp_map_comparison (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    {E : DerivedCategory X₃.Modules} {W : HomotopyCategory X₃.Modules (ComplexShape.up ℤ)}
    (φ : E ⟶ DerivedCategory.Qh.obj W) :
    (Stacks.Duality.derivedPullbackCompIso f₁ f₂).inv.app E ≫
        (Stacks.Duality.derivedPullback f₁).map ((Stacks.Duality.derivedPullback f₂).map φ ≫
          (Stacks.Duality.derivedPullbackComparison f₂).app W) ≫
        (Stacks.Duality.derivedPullbackComparison f₁).app
          (((Scheme.Modules.pullback f₂).mapHomotopyCategory (ComplexShape.up ℤ)).obj W) =
      (Stacks.Duality.derivedPullback (f₁ ≫ f₂)).map φ ≫
        (Stacks.Duality.derivedPullbackComparison (f₁ ≫ f₂)).app W ≫
        DerivedCategory.Qh.map ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso
          f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).inv.app W) := by
  have h := derivedPullbackCompIso_hom_app_comp_map_comparison f₁ f₂ φ
  refine (Iso.inv_comp_eq ((Stacks.Duality.derivedPullbackCompIso f₁ f₂).app E)).2 ?_
  refine ((Iso.eq_comp_inv (DerivedCategory.Qh.mapIso
    ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso
      f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).app W))).2
    ((Category.assoc _ _ _).trans h.symm)).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))

/-- Transport of a degreewise comparison along an equality of morphisms of schemes. -/
theorem eqToHom_derivedPullback_comparison {t t' : X₁ ⟶ X₂} (h : t = t')
    {E : DerivedCategory X₂.Modules} {W : HomotopyCategory X₂.Modules (ComplexShape.up ℤ)}
    (φ : E ⟶ DerivedCategory.Qh.obj W) :
    eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj E) h) ≫
        (Stacks.Duality.derivedPullback t').map φ ≫
        (Stacks.Duality.derivedPullbackComparison t').app W =
      (Stacks.Duality.derivedPullback t).map φ ≫
        (Stacks.Duality.derivedPullbackComparison t).app W ≫
        DerivedCategory.Qh.map (eqToHom (congrArg (fun t =>
          ((Scheme.Modules.pullback t).mapHomotopyCategory (ComplexShape.up ℤ)).obj W) h)) := by
  subst h
  simp

end Generic


section Unfold

/-- The component of `derivedPullbackComplexComparison g` at a complex `K` is the comparison of
the derived pullback with degreewise pullback at the image of `K` in the homotopy category,
conjugated by `DerivedCategory.quotientCompQhIso`. -/
theorem _root_.Stacks.DerivedPullback.derivedPullbackComplexComparison_app
    {X₁ X₂ : RingedSpace.{u, u}}
    (g : X₁ ⟶ X₂) [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X₁))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing X₂))]
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X₂)) ℤ) :
    (Stacks.DerivedPullback.derivedPullbackComplexComparison g).app K =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).map
          ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g).app
          ((HomotopyCategory.quotient _ _).obj K) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app _ := by
  simp only [Stacks.DerivedPullback.derivedPullbackComplexComparison,
    Functor.mapHomotopyCategoryFactors, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Quotient.lift.isLift_hom, Category.id_comp]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ((congrArg (· ≫ _)
    (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _)))

/-- The component of `extendScalarsTildeComparison R S f` at a complex `P` is the image under
`(tilde.functor S).mapDerivedCategory` of the comparison of derived extension of scalars at `P`,
followed by `mapDerivedCategoryFactors`. -/
theorem extendScalarsTildeComparison_app (R S : CommRingCat.{u}) (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extendScalarsTildeComparison R S f).app P =
      (tilde.functor S).mapDerivedCategory.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
            f.hom).comparison.app P) ≫
        (tilde.functor S).mapDerivedCategoryFactors.hom.app _ := by
  simp only [extendScalarsTildeComparison, extendScalarsTildeFactor, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]
  exact congrArg (_ ≫ ·)
    (CochainComplex.DerivedExtensionScalars.associator_trans_isoWhiskerLeft_hom_app _ _ P)

/-- The component of `tildeDerivedPullbackComparison R S f` at a complex `P` is the derived
pullback along `Spec.map f` of `mapDerivedCategoryFactors`, followed by the comparison of derived
and degreewise pullback at `P^~`. -/
theorem tildeDerivedPullbackComparison_app (R S : CommRingCat.{u}) (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tildeDerivedPullbackComparison R S f).app P =
      (Stacks.Duality.derivedPullback (Spec.map f)).map
          ((tilde.functor R).mapDerivedCategoryFactors.hom.app P) ≫
        (Stacks.DerivedPullback.derivedPullbackComplexComparison (Spec.map f).toLRSHom.toShHom).app
          (((tilde.functor R).mapHomologicalComplex _).obj P) := by
  simp [tildeDerivedPullbackComparison, tildeDerivedPullbackFactor]
  rfl

/-- The component of `tildePullbackComplexCompQIso R S f` at a complex `P` is the image under
`DerivedCategory.Q` of the component of `tildePullbackComplexIso R S f` at `P`. -/
theorem tildePullbackComplexCompQIso_hom_app (R S : CommRingCat.{u}) (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tildePullbackComplexCompQIso R S f).hom.app P =
      DerivedCategory.Q.map ((tildePullbackComplexIso R S f).hom.app P) := by
  simp [tildePullbackComplexCompQIso]

end Unfold


section Chase

variable {C : Type*} [Category C]

/-- An identity between composites of morphisms in a category, deduced from the given
commutative squares and the retraction `qh' ≫ qi = 𝟙 _`. -/
theorem chase_affinePullback {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Y₁ Y₂ : C} {a' : X₀ ⟶ X₂} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (ℓ : X₂ ⟶ X₃) (qh : X₃ ⟶ X₄) (t : X₄ ⟶ X₅) (m : X₃ ⟶ X₆) (qh' : X₆ ⟶ X₅)
    (qi : X₅ ⟶ X₆) (d : X₀ ⟶ Y₁) (k : Y₁ ⟶ Y₂) (z : Y₂ ⟶ X₅) (e : X₁ ⟶ X₄) (hab : a' = a ≫ b)
    (he : e = b ≫ ℓ ≫ qh)
    (h : d ≫ k ≫ z = (a ≫ e) ≫ t) (hq : m ≫ qh' = qh ≫ t) (hi : qh' ≫ qi = 𝟙 _) :
    a' ≫ ℓ ≫ m = d ≫ k ≫ z ≫ qi := by
  have hm : m = qh ≫ t ≫ qi := by rw [← reassoc_of% hq, hi, Category.comp_id]
  rw [hm, hab, reassoc_of% h, he]
  simp

/-- An identity between composites of morphisms in `C`, partly in the image of a functor
`F : D ⥤ C`, deduced from the given commutative diagrams. -/
theorem chase_zariskiPath {D : Type*} [Category D] (F : D ⥤ C)
    {S₀ S₁ S₂ M₁ N₁ Rg R₀ R₁' R₁ R₂ R₄ : C} {T₀ T₁ T₂ T₃ U₁ U₂ U₃ U₄ : D}
    (cI : S₀ ⟶ S₁) (eq : S₁ ⟶ S₂) (cJinv : S₂ ⟶ F.obj T₀) (u : T₀ ⟶ T₁) (lc : T₁ ⟶ T₂)
    (x : T₂ ⟶ T₃) (dw : T₀ ⟶ U₁) (zμ : U₁ ⟶ U₂) (zg : U₂ ⟶ U₃) (zκ : U₁ ⟶ U₃) (zf : U₃ ⟶ U₄)
    (qi : U₄ ⟶ T₃) (lj : F.obj T₃ ⟶ R₄) (lj0 : F.obj T₂ ⟶ R₂) (jx : R₂ ⟶ R₄) (r0 : S₀ ⟶ Rg)
    (rg : Rg ⟶ R₀) (q1 : R₀ ⟶ R₁') (q2 : R₁' ⟶ R₁) (qp : R₁ ⟶ R₂) (qall : R₀ ⟶ R₄)
    (m1 : S₁ ⟶ M₁) (m2 : M₁ ⟶ R₁') (n1 : S₂ ⟶ N₁) (n2 : N₁ ⟶ R₁)
    (hqall : qall = q1 ≫ q2 ≫ qp ≫ jx) (hA : cI ≫ m1 ≫ m2 = r0 ≫ rg ≫ q1)
    (hB : eq ≫ n1 ≫ n2 = m1 ≫ m2 ≫ q2) (hC : cJinv ≫ F.map (u ≫ lc) ≫ lj0 = n1 ≫ n2 ≫ qp)
    (hE : F.map x ≫ lj = lj0 ≫ jx) (hD : u ≫ lc ≫ x = dw ≫ zκ ≫ zf ≫ qi)
    (hμ : zμ ≫ zg = zκ) :
    cI ≫ eq ≫ cJinv ≫ F.map (dw ≫ zμ ≫ zg ≫ zf ≫ qi) ≫ lj = r0 ≫ rg ≫ qall := by
  rw [hqall, ← reassoc_of% hA, ← reassoc_of% hB, ← reassoc_of% hC, reassoc_of% hμ, ← hD]
  simp [hE]

end Chase

/-- The degreewise composition isomorphism `g_0^* j^* M^~ ≅ (g_0 ≫ j)^* M^~`. -/
def affineZariskiPathCompHom :
    ((Scheme.Modules.pullback g₀).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.pullback j).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor A).mapHomologicalComplex _).obj P))) ⟶
      ((Scheme.Modules.pullback (g₀ ≫ j)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor A).mapHomologicalComplex _).obj P)) :=
  (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso g₀.toLRSHom.toShHom
      j.toLRSHom.toShHom).hom.app _

/-- The identification `(g_0 ≫ j)^* M^~ = (j' ≫ Spec c)^* M^~`. -/
def affineZariskiPathSquare :
      ((Scheme.Modules.pullback (g₀ ≫ j)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor A).mapHomologicalComplex _).obj P)) ⟶
      ((Scheme.Modules.pullback (j' ≫ Spec.map c)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor A).mapHomologicalComplex _).obj P)) :=
  eqToHom (congrArg (fun t => ((Scheme.Modules.pullback t).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
        (((tilde.functor A).mapHomologicalComplex _).obj P))) h)

/-- The degreewise isomorphism `(j' ≫ Spec c)^* M^~ ≅ j'^*(Spec c)^* M^~ ≅ j'^*(A' ⊗_A M)^~`. -/
def affineZariskiPathSpecHom :
      ((Scheme.Modules.pullback (j' ≫ Spec.map c)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor A).mapHomologicalComplex _).obj P)) ⟶
      ((Scheme.Modules.pullback j').mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj (((tilde.functor A').mapHomologicalComplex _).obj
          (((ModuleCat.extendScalars.{u, u, u} c.hom).mapHomologicalComplex _).obj P))) :=
  (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso j'.toLRSHom.toShHom
      (Spec.map c).toLRSHom.toShHom).inv.app _ ≫
    ((Scheme.Modules.pullback j').mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient _ _).map ((tildePullbackComplexIso A A' c).hom.app P))

/-- The degreewise path `g_0^* j^* M^~ ≅ (g_0 ≫ j)^* M^~ = (j' ≫ Spec c)^* M^~ ≅ j'^*(Spec c)^* M^~
≅ j'^*(A' ⊗_A M)^~` in the homotopy category, for a complex `M` of `A`-modules. -/
def affineZariskiPathHomotopy :
    ((Scheme.Modules.pullback g₀).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.pullback j).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor A).mapHomologicalComplex _).obj P))) ⟶
      ((Scheme.Modules.pullback j').mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj (((tilde.functor A').mapHomologicalComplex _).obj
          (((ModuleCat.extendScalars.{u, u, u} c.hom).mapHomologicalComplex _).obj P))) :=
  affineZariskiPathCompHom g₀ j P ≫ affineZariskiPathSquare g₀ j j' c h P ≫
    affineZariskiPathSpecHom j' c P

/-- `μ⁻¹` followed by the comparison at the standard model is the comparison at the locally small
model. -/
theorem totalDerivedExtensionScalarsModelIso_inv_app_comparison :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso c.hom).inv.app
        (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) |>.obj P) ≫
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A')).functor.map
        ((@CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.comparison.{u, u, u}
          A A' _ _ c.hom (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          (@CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            A A' _ _ c.hom (HasDerivedCategory.standard _)
              (HasDerivedCategory.standard _))).app P) =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        c.hom).comparison.app P := by
  have h :=
    CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso_hom_app_comparison
      c.hom P
  have e :
      (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} A))).hom.app P =
        𝟙 _ := rfl
  have e' : (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} A'))).hom.app
      (((ModuleCat.extendScalars.{u, u, u} c.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) = 𝟙 _ := rfl
  rw [e, e'] at h
  exact (Iso.inv_comp_eq
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso c.hom).app _)).2
      (((Category.comp_id _).symm.trans h.symm).trans
        (congrArg (_ ≫ ·) ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
          (Category.id_comp _))))

/-- The derived pullback along `Spec.map c` of `M^~`, read through the comparison with degreewise
pullback and `tildePullbackComplexIso`, agrees with `affinePullbackComparison` followed by the
comparison of derived extension of scalars at `M`. -/
theorem affinePullbackComparison_comparison :
    (Stacks.Duality.derivedPullback (Spec.map c)).map
        ((tilde.functor A).mapDerivedCategoryFactors.hom.app P ≫
          (DerivedCategory.quotientCompQhIso (Spec A).Modules).inv.app _) ≫
      (Stacks.Duality.derivedPullbackComparison (Spec.map c)).app _ ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((tildePullbackComplexIso A A' c).hom.app P)) =
    (affinePullbackComparison _ _ c).hom.app (DerivedCategory.Q.obj P) ≫
      (tilde.functor _).mapDerivedCategory.map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
          c.hom).comparison.app P) ≫
      (tilde.functor A').mapDerivedCategoryFactors.hom.app _ ≫
      (DerivedCategory.quotientCompQhIso (Spec A').Modules).inv.app _ := by
  have h := affinePullbackComparison_fac A A' c P
  rw [extendScalarsTildeComparison_app, tildeDerivedPullbackComparison_app,
    tildePullbackComplexCompQIso_hom_app] at h
  exact chase_affinePullback _ _ _ _ _ _ _ _ _ _ _ _
    (CategoryTheory.Functor.map_comp _ _ _)
    (Stacks.DerivedPullback.derivedPullbackComplexComparison_app _ _) h
    ((DerivedCategory.quotientCompQhIso (Spec A').Modules).hom.naturality
      ((tildePullbackComplexIso A A' c).hom.app P))
    ((DerivedCategory.quotientCompQhIso (Spec A').Modules).hom_inv_id_app _)

/-- **The Zariski path on complexes.** The composite `L(g_0)^*L j^* M^~ ≅ L j'^* (A' ⊗^L_A M)^~` of
the composition isomorphisms of derived pullbacks, the square `g_0 ≫ j = j' ≫ Spec c`, Stacks 08DW
and the comparison of models of derived extension of scalars, read through the comparisons with
degreewise pullback, is the degreewise path `affineZariskiPathHomotopy`. -/
theorem affineZariskiPath_comparison :
    (Stacks.Duality.derivedPullbackCompIso g₀ j).hom.app ((tilde.functor A).mapDerivedCategory.obj
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj
          (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) |>.obj P))) ≫
      eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj
        ((tilde.functor A).mapDerivedCategory.obj
          ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj
            (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) |>.obj P)))) h) ≫
      (Stacks.Duality.derivedPullbackCompIso j' (Spec.map c)).inv.app _ ≫
      (Stacks.Duality.derivedPullback j').map
        ((affinePullbackComparison _ _ c).hom.app _ ≫
          (tilde.functor _).mapDerivedCategory.map
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso
              c.hom).inv.app _) ≫
          (tilde.functor _).mapDerivedCategory.map
            ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A')).functor.map
              ((@CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.comparison.{
                u, u, u}
                A A' _ _ c.hom (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
                (@CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                  A A' _ _ c.hom (HasDerivedCategory.standard _)
                  (HasDerivedCategory.standard _))).app P)) ≫
          (tilde.functor A').mapDerivedCategoryFactors.hom.app _ ≫
          (DerivedCategory.quotientCompQhIso (Spec A').Modules).inv.app _) ≫
      (Stacks.Duality.derivedPullbackComparison j').app _ =
    (Stacks.Duality.derivedPullback g₀).map
        ((Stacks.Duality.derivedPullback j).map
            ((tilde.functor A).mapDerivedCategoryFactors.hom.app P ≫
              (DerivedCategory.quotientCompQhIso (Spec A).Modules).inv.app _) ≫
          (Stacks.Duality.derivedPullbackComparison j).app _) ≫
      (Stacks.Duality.derivedPullbackComparison g₀).app _ ≫
      DerivedCategory.Qh.map (affineZariskiPathHomotopy g₀ j j' c h P) :=
  chase_zariskiPath (Stacks.Duality.derivedPullback j') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _
    ((CategoryTheory.Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·)
      ((CategoryTheory.Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·)
        (CategoryTheory.Functor.map_comp _ _ _)))))
    (derivedPullbackCompIso_hom_app_comp_map_comparison g₀ j _)
    (eqToHom_derivedPullback_comparison h _)
    (derivedPullbackCompIso_inv_app_comp_map_comparison j' (Spec.map c) _)
    ((Stacks.Duality.derivedPullbackComparison j').naturality _)
    (affinePullbackComparison_comparison c P)
    (((tilde.functor A').mapDerivedCategory.map_comp _ _).symm.trans
      (congrArg (tilde.functor A').mapDerivedCategory.map
        (totalDerivedExtensionScalarsModelIso_inv_app_comparison c P)))


end AlgebraicGeometry
