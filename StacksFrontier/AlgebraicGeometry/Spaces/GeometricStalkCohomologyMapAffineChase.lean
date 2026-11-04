module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffineIff
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp

/-!
# The chase identifying Equation 0DKF on affine representables with the ring-level map

Let `g : P ⟶ U` be a morphism of affine objects of the big fppf site over `S` and `x̄'` a
geometric point of `yoneda.obj P`. This file computes, on a complex `M` of `Γ(U)`-modules, the
derived pullback-stalk comparison at `Φ_U(M)` followed by the stalk of the affine base change
morphism and the stalk isomorphisms of `Φ`, as the localization of explicit morphisms of
complexes.

## Main results

* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_square_comparison`:
  the composition isomorphisms of derived extension of scalars around a commutative square of
  rings, on complexes.
* `AlgebraicGeometry.Space.derivedExtensionGeometricStalkComplexIso_hom_app`,
  `AlgebraicGeometry.Space.extensionGeometricStalkComplexIso_hom_app`: the components of the
  isomorphisms out of which the derived pullback-stalk comparison is built.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

namespace CochainComplex.DerivedExtensionScalars

variable {A B C A' : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing A']

/-- **Two composites of derived extension of scalars around a square of rings, on complexes.** -/
theorem totalDerivedExtensionScalarsComp_square_comparison (a : A →+* B) (c : B →+* C)
    (ρ : A →+* A') (d : A' →+* C) (h : c.comp a = d.comp ρ)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (totalDerivedExtensionScalarsComp.{u, u} a c).hom.app (DerivedCategory.Q.obj M) ≫
      eqToHom (congrArg (fun φ : A →+* C =>
        (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj (DerivedCategory.Q.obj M)) h) ≫
      (totalDerivedExtensionScalarsComp.{u, u} ρ d).inv.app (DerivedCategory.Q.obj M) ≫
      (totalDerivedExtensionScalars.{u, u, u} d).functor.map
        ((totalDerivedExtensionScalars.{u, u, u} ρ).comparison.app M) ≫
      (totalDerivedExtensionScalars.{u, u, u} d).comparison.app
        (((ModuleCat.extendScalars.{u, u, u} ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
    (totalDerivedExtensionScalars.{u, u, u} c).functor.map
        ((totalDerivedExtensionScalars.{u, u, u} a).comparison.app M) ≫
      (totalDerivedExtensionScalars.{u, u, u} c).comparison.app
        (((ModuleCat.extendScalars.{u, u, u} a).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (ModuleCat.extendScalarsComp a c).inv (ComplexShape.up ℤ)).app M ≫
        eqToHom (congrArg (fun φ : A →+* C =>
          ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) h) ≫
        (NatTrans.mapHomologicalComplex
          (ModuleCat.extendScalarsComp ρ d).hom (ComplexShape.up ℤ)).app M) := by
  have hP := totalDerivedExtensionScalarsComp_comparison ρ d M
  have hU := totalDerivedExtensionScalarsComp_comparison a c M
  have k1 := (Iso.inv_comp_eq ((totalDerivedExtensionScalarsComp.{u, u} ρ d).app
    (DerivedCategory.Q.obj M))).2 (((Iso.comp_inv_eq ((extensionOfScalarsComplexComp ρ d).app M)).1
      ((Category.assoc _ _ _).trans hP)).trans (Category.assoc _ _ _))
  have k2 := totalDerivedExtensionScalars_eqToHom_comp_comparison h M
  refine (congrArg (fun t => _ ≫ _ ≫ t) k1).trans ?_
  refine (congrArg (fun t => _ ≫ t) (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (fun t => _ ≫ t ≫ _) k2).trans ?_
  refine (congrArg (fun t => _ ≫ t) (Category.assoc _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ _) hU.symm).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (fun t => _ ≫ t) ((Category.assoc _ _ _).trans
    (congrArg (fun t => _ ≫ t) ?_)))
  exact (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _).symm).trans
    (DerivedCategory.Q.map_comp _ _).symm

end CochainComplex.DerivedExtensionScalars




namespace Stacks.Generic

/-- The component of a composite of two right whiskerings. -/
theorem isoWhiskerRight_trans_isoWhiskerRight_hom_app {C D E F : Type*} [Category* C]
    [Category* D] [Category* E] [Category* F] {F₁ F₂ : C ⥤ D} {G₂ : C ⥤ E}
    (α : F₁ ≅ F₂) (H : D ⥤ E) (K : E ⥤ F) (β : F₂ ⋙ H ≅ G₂) (P : C) :
    (Functor.isoWhiskerRight α (H ⋙ K) ≪≫ Functor.isoWhiskerRight β K).hom.app P =
      K.map (H.map (α.hom.app P)) ≫ K.map (β.hom.app P) := rfl

/-- The component of a composite of the shape of
`AlgebraicGeometry.Space.extensionGeometricStalkComplexIso`. -/
theorem extensionShape_hom_app {C Cs Cs' K C₁ D₁ H₁ H : Type*} [Category* C] [Category* Cs]
    [Category* Cs'] [Category* K] [Category* C₁] [Category* D₁] [Category* H₁] [Category* H]
    (Fs : C ⥤ Cs) (E₁ E₂ : Cs ⥤ Cs') (Q : Cs' ⥤ K) (h : Fs ⋙ E₁ ⋙ Q = Fs ⋙ E₂ ⋙ Q)
    (Fm : C ⥤ C₁) (S' : C₁ ⥤ Cs') (α : Fm ⋙ S' ≅ Fs ⋙ E₂)
    (Q₁ : C₁ ⥤ D₁) (G' : D₁ ⥤ K) (β : Q₁ ⋙ G' ≅ S' ⋙ Q)
    (quot₁ : C₁ ⥤ H₁) (Qh₁ : H₁ ⥤ D₁) (γ : quot₁ ⋙ Qh₁ ≅ Q₁)
    (quot : C ⥤ H) (Fh : H ⥤ H₁) (δ : quot ⋙ Fh ≅ Fm ⋙ quot₁) (P : C) :
    (eqToIso h ≪≫ Functor.isoWhiskerRight α.symm Q ≪≫ Functor.isoWhiskerLeft Fm β.symm ≪≫
        Functor.isoWhiskerLeft Fm (Functor.isoWhiskerRight γ.symm G') ≪≫
        Functor.isoWhiskerRight δ.symm (Qh₁ ⋙ G')).hom.app P =
      (eqToIso h).hom.app P ≫ Q.map (α.inv.app P) ≫ β.inv.app (Fm.obj P) ≫
        G'.map (γ.inv.app (Fm.obj P)) ≫ G'.map (Qh₁.map (δ.inv.app P)) := rfl

/-- Reassociation of five morphisms. -/
theorem assoc_four_one {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) :
    (a ≫ b ≫ c ≫ d) ≫ e = (a ≫ b) ≫ c ≫ d ≫ e := by
  simp only [Category.assoc]


/-- Merging three images under a functor. -/
theorem map_comp_of_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X Y Z W : C}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ W} {r : X ⟶ W} {t : F.obj Y ⟶ F.obj W}
    (h₁ : t = F.map b ≫ F.map c) (h₂ : a ≫ b ≫ c = r) : F.map a ≫ t = F.map r := by
  rw [h₁, ← h₂, F.map_comp, F.map_comp]

/-- Cancelling a retraction against an expansion. -/
theorem cancel_of_eq {C : Type*} [Category* C] {X Y Y₁ Y₂ Z W : C} {i : X ⟶ Y} {a : Y ⟶ X}
    {b : X ⟶ Y₁} {c : Y₁ ⟶ Z} {m₁ : Y ⟶ Y₂} {m₂ : Y₂ ⟶ Z} {q : Z ⟶ W} {s : Y ⟶ W}
    (hs : s = m₁ ≫ m₂ ≫ q) (hb : a ≫ b ≫ c = m₁ ≫ m₂) (h : i ≫ a = 𝟙 X) :
    i ≫ s = b ≫ c ≫ q := by
  rw [hs, ← reassoc_of% hb, reassoc_of% h]

/-- Merging four images under a functor. -/
theorem map_comp₄_of_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X Y Z W V : C}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ W} {d : W ⟶ V} {r : X ⟶ V} (h : a ≫ b ≫ c ≫ d = r) :
    F.map a ≫ F.map b ≫ F.map c ≫ F.map d = F.map r := by
  rw [← h, F.map_comp, F.map_comp, F.map_comp]

/-- Assembling the tail of the chase. -/
theorem tail_of_eq {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ A₁₀ : C}
    {E : A₀ ⟶ A₅} {e₁ : A₀ ⟶ A₁} {q₁ : A₁ ⟶ A₂} {f₁ : A₂ ⟶ A₃} {s₁ : A₃ ⟶ A₄} {m : A₄ ⟶ A₅}
    {R : A₅ ⟶ A₆} {s₂ : A₆ ⟶ A₇} {dQ : A₃ ⟶ A₇} {f₂ : A₇ ⟶ A₈} {Qf : A₂ ⟶ A₈}
    {Fi : A₆ ⟶ A₉} {Sg : A₉ ⟶ A₁₀} {qc : A₈ ⟶ A₁₀}
    (hE : E = e₁ ≫ q₁ ≫ f₁ ≫ s₁ ≫ m) (hd : s₁ ≫ m ≫ R ≫ s₂ = dQ) (he : f₁ ≫ dQ ≫ f₂ = Qf)
    (hP : Fi ≫ Sg = s₂ ≫ f₂ ≫ qc) :
    E ≫ R ≫ Fi ≫ Sg = e₁ ≫ q₁ ≫ Qf ≫ qc := by
  rw [hE, hP, ← he, ← hd]
  simp only [Category.assoc]

/-- The localization of the image of a morphism in the homotopy category. -/
theorem quotientCompQhIso_inv_comp_map_comp_hom {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    (DerivedCategory.quotientCompQhIso C).inv.app X ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app Y = DerivedCategory.Q.map f := by
  exact NatIso.naturality_1 (DerivedCategory.quotientCompQhIso C) f

/-- The factorization of a functor induced on derived categories, against a morphism of
complexes. -/
theorem mapDerivedCategoryFactors_inv_comp_map_comp_hom {C D : Type*} [Category C] [Abelian C]
    [Category D] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D)
    [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    F.mapDerivedCategoryFactors.inv.app X ≫ F.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
      F.mapDerivedCategoryFactors.hom.app Y =
    DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  exact NatIso.naturality_1 F.mapDerivedCategoryFactors f

/-- Removing an identity and rewriting a middle factor. -/
theorem cancel_id_of_eq {C : Type*} [Category* C] {X Y Z W : C} {a : X ⟶ Y} {m : Y ⟶ Y}
    {h h' : Y ⟶ Z} {b : Z ⟶ W} {c : X ⟶ W} (hm : m = 𝟙 Y) (hh : h = h') (hq : a ≫ h' ≫ b = c) :
    a ≫ m ≫ h ≫ b = c := by
  rw [hm, hh, Category.id_comp, hq]

/-- Assembling the derived pullback-stalk side of the chase. -/
theorem assembleL {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₅ A₆ A₇ A₉ : C}
    {Lhs : A₀ ⟶ A₉} {h : A₀ ⟶ A₁} {c : A₁ ⟶ A₅} {r : A₅ ⟶ A₆} {fi : A₆ ⟶ A₇} {sg : A₇ ⟶ A₉}
    {y : A₀ ⟶ A₂} {d : A₁ ⟶ A₂} {k : A₂ ⟶ A₃} {e : A₃ ⟶ A₅} {t : A₃ ⟶ A₉}
    (h₁ : Lhs = h ≫ c ≫ r ≫ fi ≫ sg) (hH : h ≫ d = y) (hC : c = d ≫ k ≫ e)
    (hT : e ≫ r ≫ fi ≫ sg = t) : Lhs = y ≫ k ≫ t := by
  rw [h₁, hC, ← hH, ← hT]
  simp only [Category.assoc]

/-- Assembling the ring side of the chase. -/
theorem assembleR {C₀ C D E : Type*} [Category* C₀] [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (Q₁ : C₀ ⥤ C) (Q : E ⥤ D)
    {X₀ X₁ X₃ : C} {Z₁ Z₂ : C₀} {Y₁ Y₂ Y₃ Y₄ : D} {W₁ W₂ W₃ : E}
    {e : X₀ ⟶ X₁} {cmp : X₁ ⟶ Q₁.obj Z₂} {σ : X₀ ⟶ Q₁.obj Z₂} {y₁ : X₀ ⟶ X₃}
    {y₂ : X₃ ⟶ Q₁.obj Z₁} {z : Z₁ ⟶ Z₂}
    {c₁ : F.obj X₁ ⟶ Y₁} {eq : Y₁ ⟶ Y₂} {c₂ : Y₂ ⟶ Y₃} {dm : Y₃ ⟶ Y₄} {cp : Y₄ ⟶ Q.obj W₃}
    {cmpc : F.obj (Q₁.obj Z₂) ⟶ Q.obj W₂} {k : F.obj (Q₁.obj Z₁) ⟶ Q.obj W₁}
    {Gz : Q.obj W₁ ⟶ Q.obj W₂} {a : W₁ ⟶ W₂} {w : W₂ ⟶ W₃}
    (hsq : c₁ ≫ eq ≫ c₂ ≫ dm ≫ cp = F.map cmp ≫ cmpc ≫ Q.map w)
    (he : e ≫ cmp = σ) (hSig : σ = y₁ ≫ y₂ ≫ Q₁.map z)
    (hn : (Q₁ ⋙ F).map z ≫ cmpc = k ≫ Gz) (hG : Gz = Q.map a) :
    F.map e ≫ c₁ ≫ eq ≫ c₂ ≫ dm ≫ cp = F.map (y₁ ≫ y₂) ≫ k ≫ Q.map (a ≫ w) := by
  rw [hsq, ← F.map_comp_assoc, he, hSig]
  simp only [Functor.comp_map] at hn
  simp only [F.map_comp, Category.assoc, reassoc_of% hn, hG, Q.map_comp]

/-- The degree-`n` component of the inverse of a composite of the shape of Stacks 05V5 for
complexes. -/
theorem mapHomologicalComplexCompIso_trans_symm_inv_app_f {V W W' V' : Type*} [Category* V]
    [Category* W] [Category* W'] [Category* V'] [Preadditive V] [Preadditive W] [Preadditive W']
    [Preadditive V'] {F : V ⥤ W} {G : W ⥤ W'} {F' : V ⥤ V'} {G' : V' ⥤ W'}
    {_ : F.Additive} {_ : G.Additive} {_ : F'.Additive} {_ : G'.Additive} {_ : (F ⋙ G).Additive}
    {_ : (F' ⋙ G').Additive}
    (e : F ⋙ G ≅ F' ⋙ G') (K : CochainComplex V ℤ) (n : ℤ) :
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G'))
        (ComplexShape.up ℤ)).symm).inv.app K).f n =
      e.inv.app (K.X n) := by
  simp

/-- The degree-`n` component of a composite of the shape of the degreewise pullback of
associated modules. -/
theorem mapHomologicalComplexCompIso_trans_symm_hom_app_f {V W W' V' : Type*} [Category* V]
    [Category* W] [Category* W'] [Category* V'] [Preadditive V] [Preadditive W] [Preadditive W']
    [Preadditive V'] {F : V ⥤ W} {G : W ⥤ W'} {F' : V ⥤ V'} {G' : V' ⥤ W'}
    {_ : F.Additive} {_ : G.Additive} {_ : F'.Additive} {_ : G'.Additive} {_ : (F ⋙ G).Additive}
    {_ : (F' ⋙ G').Additive}
    (e : F ⋙ G ≅ F' ⋙ G') (K : CochainComplex V ℤ) (n : ℤ) :
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G'))
        (ComplexShape.up ℤ)).symm).hom.app K).f n =
      e.hom.app (K.X n) := by
  simp

end Stacks.Generic

namespace AlgebraicGeometry.Space



section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X' X : AlgebraicSpaces B S hS}
  (g : X' ⟶ X) (x' : GeometricPoint B S hS X'.1)

/-- The value of `AlgebraicGeometry.Space.derivedExtensionGeometricStalkComplexIso` at a
complex. -/
theorem derivedExtensionGeometricStalkComplexIso_hom_app
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (derivedExtensionGeometricStalkComplexIso g x').hom.app P =
      (geometricStalkDerivedExtension g x').functor.map
          ((geometricDerivedStalk B S hS (geometricPointMap g.hom x')).map
            ((DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))).hom.app P)) ≫
        (geometricStalkDerivedExtension g x').functor.map
          ((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
            (smallEtaleRingedTopos B S hS X).O).mapDerivedCategoryFactors.hom.app P) :=
  Stacks.Generic.isoWhiskerRight_trans_isoWhiskerRight_hom_app _ _ _ _ P

private theorem eGSCI_eq : extensionGeometricStalkComplexIso g x' =
    eqToIso (congrArg (fun φ => (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q)
        (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived g x')) ≪≫
    (Functor.isoWhiskerRight (pullbackStalkComplexNatIso g x').symm DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ))
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
        (smallEtaleRingedTopos B S hS X').O).mapDerivedCategoryFactors.symm ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)) (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm
        (geometricDerivedStalk B S hS x')) ≪≫
    Functor.isoWhiskerRight
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).symm (DerivedCategory.Qh ⋙ geometricDerivedStalk B S hS x')) := rfl

private theorem eGSCI_trans_app (P : CochainComplex (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (eqToIso (congrArg (fun φ => (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q)
        (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived g x')) ≪≫
          (Functor.isoWhiskerRight (pullbackStalkComplexNatIso g x').symm DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ))
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
        (smallEtaleRingedTopos B S hS X').O).mapDerivedCategoryFactors.symm ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)) (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm
        (geometricDerivedStalk B S hS x')) ≪≫
    Functor.isoWhiskerRight
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).symm (DerivedCategory.Qh ⋙
          geometricDerivedStalk B S hS x'))).hom.app P =
          (eqToIso (congrArg (fun φ => (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q)
        (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived g x'))).hom.app P ≫
          (Functor.isoWhiskerRight (pullbackStalkComplexNatIso g x').symm DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ))
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
        (smallEtaleRingedTopos B S hS X').O).mapDerivedCategoryFactors.symm ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)) (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm
        (geometricDerivedStalk B S hS x')) ≪≫
    Functor.isoWhiskerRight
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).symm (DerivedCategory.Qh ⋙
          geometricDerivedStalk B S hS x')).hom.app P := rfl

private theorem eGSCI_tail_app (P : CochainComplex (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (Functor.isoWhiskerRight (pullbackStalkComplexNatIso g x').symm DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ))
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
        (smallEtaleRingedTopos B S hS X').O).mapDerivedCategoryFactors.symm ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)) (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm
        (geometricDerivedStalk B S hS x')) ≪≫
    Functor.isoWhiskerRight
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).symm (DerivedCategory.Qh ⋙
          geometricDerivedStalk B S hS x')).hom.app P =
      DerivedCategory.Q.map ((pullbackStalkComplexNatIso g x').inv.app P) ≫
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
        (smallEtaleRingedTopos B S hS X').O).mapDerivedCategoryFactors.inv.app
          (((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
      (geometricDerivedStalk B S hS x').map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))).inv.app
          (((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ≫
      (geometricDerivedStalk B S hS x').map (DerivedCategory.Qh.map
        (((smallEtaleRingedToposHom B S hS
          g).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app P)) := rfl

/-- The value of `AlgebraicGeometry.Space.extensionGeometricStalkComplexIso` at a complex. -/
theorem extensionGeometricStalkComplexIso_hom_app
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (extensionGeometricStalkComplexIso g x').hom.app P =
      (eqToIso (congrArg (fun φ => (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q)
        (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived g x'))).hom.app P ≫
      DerivedCategory.Q.map ((pullbackStalkComplexNatIso g x').inv.app P) ≫
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
        (smallEtaleRingedTopos B S hS X').O).mapDerivedCategoryFactors.inv.app
          (((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
      (geometricDerivedStalk B S hS x').map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))).inv.app
          (((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ≫
      (geometricDerivedStalk B S hS x').map (DerivedCategory.Qh.map
        (((smallEtaleRingedToposHom B S hS
          g).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app P)) :=
  (congrArg (fun e => e.hom.app P) (eGSCI_eq g x')).trans
    ((eGSCI_trans_app g x' P).trans (congrArg (_ ≫ ·) (eGSCI_tail_app g x' P)))


/-- The value of `AlgebraicGeometry.Space.derivedPullbackGeometricStalkComplexMap` at a complex. -/
theorem derivedPullbackGeometricStalkComplexMap_app
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (derivedPullbackGeometricStalkComplexMap g x').app P =
      (derivedExtensionGeometricStalkComplexIso g x').hom.app P ≫
        (geometricStalkDerivedExtension g x').comparison.app
          (((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
            (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (extensionGeometricStalkComplexIso g x').hom.app P :=
  rfl

end General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chase

variable {P U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
  (g₀ : P ⟶ U) (x : GeometricPoint B S hS (yoneda.obj P))

/-- The first step of the chase: the derived pullback-stalk comparison at `Φ(M)`, followed by the
stalk of the affine base change morphism and the stalk isomorphism of `Φ_P`, through the
comparisons of derived extension of scalars. -/
theorem chaseL₁ (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (derivedPullbackGeometricStalkMap (representedSpaceMap B S hS g₀) x).app
        ((representedAffineDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj M)) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedBaseChangeIso B S hS g₀).hom.app (DerivedCategory.Q.obj M) ≫
          (representedAffineDerivedAssociated B S hS P).map
            ((representedAffineDerivedExtension B S hS g₀).comparison.app M)) ≫
      (representedAffineDerivedStalkIso B S hS P x).hom.app (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS P x)).comparison.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) =
    (geometricStalkDerivedExtension (representedSpaceMap B S hS g₀) x).functor.map
        ((geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
          (geometricPointMap (representedSpaceMap B S hS g₀).hom x)).map
            ((representedAffineDerivedAssociatedFactors B S hS U).hom.app M)) ≫
      (derivedPullbackGeometricStalkComplexMap (representedSpaceMap B S hS g₀) x).app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        (DerivedCategory.Qh.map ((representedAffineHomotopyPullbackIso B S hS g₀).hom.app M)) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedAssociatedFactors B S hS P).inv.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
      (representedAffineDerivedStalkComparison B S hS P x).hom.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) := by
  have h₁ := derivedPullbackGeometricStalkMap_app_representedAffine B S hS g₀ x M
  have h₂ := representedAffineDerivedStalkIso_hom_app_comp_comparison B S hS P x
    (((ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)
  refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
  refine (congrArg₂ (· ≫ ·) h₁ h₂).trans ?_
  exact Stacks.Generic.assoc_four_one _ _ _ _ _

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] in
/-- The head of the chase: the stalk at `g(x̄')` of the factorization of `Φ_U` followed by the
first component of the comparison on complexes. -/
theorem chaseHead (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (geometricStalkDerivedExtension (representedSpaceMap B S hS g₀) x).functor.map
        ((geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
          (geometricPointMap (representedSpaceMap B S hS g₀).hom x)).map
            ((representedAffineDerivedAssociatedFactors B S hS U).hom.app M)) ≫
      (derivedExtensionGeometricStalkComplexIso (representedSpaceMap B S hS g₀) x).hom.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
    (geometricStalkDerivedExtension (representedSpaceMap B S hS g₀) x).functor.map
      ((representedStalkFunctor B S hS U (geometricPointMap
        (representedSpaceMap B S hS g₀).hom x)).mapDerivedCategory.map
          ((representedAffineAssociated B S hS U).mapDerivedCategoryFactors.hom.app M) ≫
        (representedStalkFunctor B S hS U
          (geometricPointMap
            (representedSpaceMap B S hS g₀).hom x)).mapDerivedCategoryFactors.hom.app
            (((representedAffineAssociated B S hS U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) := by
  have h1 := derivedExtensionGeometricStalkComplexIso_hom_app (representedSpaceMap B S hS g₀) x
    (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
  have hh := geometricDerivedStalk_map_representedAffineDerivedAssociatedFactors B S hS
    (geometricPointMap (representedSpaceMap B S hS g₀).hom x) M
  exact Stacks.Generic.map_comp_of_eq _ h1 hh

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- The stalk isomorphism of `Φ_P` against the factorization of `Φ_P`, in the spelling of the
ringed topos. -/
theorem representedAffineDerivedStalkComparison_factors
    (N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj P, ⊤)) ℤ) :
    (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedAssociatedFactors B S hS P).inv.app N) ≫
      (representedAffineDerivedStalkComparison B S hS P x).hom.app N =
    (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩))).hom.app
            (((representedAffineAssociated B S hS P).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj N)) ≫
      (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS (yoneda.obj P) x (isAlgebraicSpace_yoneda B S hS P))
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩).O).mapDerivedCategoryFactors.hom.app
        (((representedAffineAssociated B S hS P).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
      DerivedCategory.Q.map ((representedAffineComplexStalkIso B S hS P x).hom.app N) :=
  Stacks.Generic.cancel_of_eq (representedAffineDerivedStalkComparison_hom_app B S hS P x N)
    (geometricDerivedStalk_map_representedAffineDerivedAssociatedFactors B S hS x N)
    (((geometricDerivedStalk B S hS (X :=
      ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map_comp _ _).symm.trans
      ((congrArg (geometricDerivedStalk B S hS (X :=
        ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedAssociatedFactors B S hS P).inv_hom_id_app N)).trans
        ((geometricDerivedStalk B S hS (X :=
          ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map_id _)))

/-- The tail of the chase: after the comparison of derived with degreewise extension of scalars,
everything is the localization of a morphism of complexes. -/
theorem chaseTail (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (extensionGeometricStalkComplexIso (representedSpaceMap B S hS g₀) x).hom.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        (DerivedCategory.Qh.map ((representedAffineHomotopyPullbackIso B S hS g₀).hom.app M)) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedAssociatedFactors B S hS P).inv.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
      (representedAffineDerivedStalkComparison B S hS P x).hom.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) =
    (eqToIso (congrArg (fun φ => (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS).obj
          (geometricPointMap (representedSpaceMap B S hS g₀).hom x)
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS).property)
        (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q)
        (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived
          (representedSpaceMap B S hS g₀) x))).hom.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Q.map ((pullbackStalkComplexNatIso (representedSpaceMap B S hS g₀) x).inv.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) ≫
      DerivedCategory.Q.map (((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS (yoneda.obj P) x (isAlgebraicSpace_yoneda B S hS P))
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩).O).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ((representedAffineComplexPullbackIso B S hS g₀).hom.app M)) ≫
      DerivedCategory.Q.map ((representedAffineComplexStalkIso B S hS P x).hom.app
        (((ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) := by
  have hE := extensionGeometricStalkComplexIso_hom_app (representedSpaceMap B S hS g₀) x
    (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
  have hP := representedAffineDerivedStalkComparison_factors B S hS x
    (((ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)
  have hq := Stacks.Generic.quotientCompQhIso_inv_comp_map_comp_hom
    (C := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩))
    ((representedAffineComplexPullbackIso B S hS g₀).hom.app M)
  have hn := Stacks.Generic.mapDerivedCategoryFactors_inv_comp_map_comp_hom
    (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj P) x (isAlgebraicSpace_yoneda B S hS P))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩).O)
    ((representedAffineComplexPullbackIso B S hS g₀).hom.app M)
  exact Stacks.Generic.tail_of_eq hE (Stacks.Generic.map_comp₄_of_eq _
    (Stacks.Generic.cancel_id_of_eq
      ((congrArg DerivedCategory.Qh.map (Quotient.lift.isLift_inv _ _ _ _)).trans
        (DerivedCategory.Qh.map_id _))
      (congrArg DerivedCategory.Qh.map
        (representedAffineHomotopyPullbackIso_hom_app B S hS g₀ M)) hq)) hn hP

/-- Naturality of the stalk isomorphism of `Φ_P`, in the spelling of the derived pullback. -/
theorem representedAffineDerivedStalkIso_naturality
    {K K' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj P, ⊤))}
    (f : K ⟶ K') :
    (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedAssociated B S hS P).map f) ≫
      (representedAffineDerivedStalkIso B S hS P x).hom.app K' =
    (representedAffineDerivedStalkIso B S hS P x).hom.app K ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS P x)).functor.map f :=
  (representedAffineDerivedStalkIso B S hS P x).hom.naturality f

/-- The ring side of the chase. -/
theorem chaseR (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (geometricStalkDerivedExtension (representedSpaceMap B S hS g₀) x).functor.map
        ((representedAffineDerivedStalkIso B S hS U
          (geometricPointMap (representedSpaceMap B S hS g₀).hom x)).hom.app
            (DerivedCategory.Q.obj M)) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        (representedAffineGlobalStalkRingHom B S hS U (geometricPointMap
          (representedSpaceMap B S hS g₀).hom x))
        (stalkStructureMap B S hS (representedSpaceMap B S hS g₀) x).hom).hom.app
          (DerivedCategory.Q.obj M) ≫
      eqToHom (congrArg (fun φ =>
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj
          (DerivedCategory.Q.obj M)) (representedAffineStalkRingHom_square B S hS g₀ x)) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom
          (representedAffineGlobalStalkRingHom B S hS P x)).inv.app
          (DerivedCategory.Q.obj M) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS P x)).functor.map
          ((representedAffineDerivedExtension B S hS g₀).comparison.app M) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS P x)).comparison.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) =
    (geometricStalkDerivedExtension (representedSpaceMap B S hS g₀) x).functor.map
      ((representedStalkFunctor B S hS U (geometricPointMap
        (representedSpaceMap B S hS g₀).hom x)).mapDerivedCategory.map
          ((representedAffineAssociated B S hS U).mapDerivedCategoryFactors.hom.app M) ≫
        (representedStalkFunctor B S hS U
          (geometricPointMap
            (representedSpaceMap B S hS g₀).hom x)).mapDerivedCategoryFactors.hom.app
            (((representedAffineAssociated B S hS U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
      (geometricStalkDerivedExtension (representedSpaceMap B S hS g₀) x).comparison.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (representedStalkFunctor B S hS U
            (geometricPointMap (representedSpaceMap B S hS g₀).hom x)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Q.map (((ModuleCat.extendScalars.{u, u, u}
          (stalkStructureMap B S hS (representedSpaceMap B S hS g₀) x).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ((representedAffineComplexStalkIso B S hS U
              (geometricPointMap (representedSpaceMap B S hS g₀).hom x)).hom.app M) ≫
        (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp
          (representedAffineGlobalStalkRingHom B S hS U (geometricPointMap
            (representedSpaceMap B S hS g₀).hom x))
          (stalkStructureMap B S hS (representedSpaceMap B S hS g₀) x).hom).inv
            (ComplexShape.up ℤ)).app M ≫
        eqToHom (congrArg (fun φ =>
          ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
          (representedAffineStalkRingHom_square B S hS g₀ x)) ≫
        (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp
          (representedAffineCommRingCatHom B S hS g₀).hom
            (representedAffineGlobalStalkRingHom B S hS P x)).hom
            (ComplexShape.up ℤ)).app M) := by
  have hsq :=
    CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_square_comparison
      (representedAffineGlobalStalkRingHom B S hS U
        (geometricPointMap (representedSpaceMap B S hS g₀).hom x))
      (stalkStructureMap B S hS (representedSpaceMap B S hS g₀) x).hom
      (representedAffineCommRingCatHom B S hS g₀).hom
      (representedAffineGlobalStalkRingHom B S hS P x)
      (representedAffineStalkRingHom_square B S hS g₀ x) M
  have he := representedAffineDerivedStalkIso_hom_app_comp_comparison B S hS U
    (geometricPointMap (representedSpaceMap B S hS g₀).hom x) M
  have hSig := representedAffineDerivedStalkComparison_hom_app B S hS U
    (geometricPointMap (representedSpaceMap B S hS g₀).hom x) M
  have hn :=
    (geometricStalkDerivedExtension (representedSpaceMap B S hS g₀) x).comparison.naturality
      ((representedAffineComplexStalkIso B S hS U
        (geometricPointMap (representedSpaceMap B S hS g₀).hom x)).hom.app M)
  exact Stacks.Generic.assembleR _ DerivedCategory.Q DerivedCategory.Q
    (Z₂ := ((ModuleCat.extendScalars.{u, u, u} (representedAffineGlobalStalkRingHom B S hS U
      (geometricPointMap (representedSpaceMap B S hS g₀).hom x))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) hsq he hSig hn rfl

/-- The components of the identification through the stalk ring maps. -/
theorem representedAffineStalkPathRight_hom_app
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineStalkPathRight B S hS g₀ x).hom.app N =
      (ModuleCat.extendScalars.{u, u, u} (stalkStructureMap B S hS
        (representedSpaceMap B S hS g₀) x).hom).map
          ((representedAffineStalkIso B S hS U (geometricPointMap
            (representedSpaceMap B S hS g₀).hom x)).inv.app N) ≫
        (ModuleCat.extendScalarsComp
          (representedAffineGlobalStalkRingHom B S hS U (geometricPointMap
            (representedSpaceMap B S hS g₀).hom x))
          (stalkStructureMap B S hS (representedSpaceMap B S hS g₀) x).hom).inv.app N ≫
        eqToHom (congrArg (fun φ => (ModuleCat.extendScalars.{u, u, u} φ).obj N)
          (representedAffineStalkRingHom_square B S hS g₀ x)) ≫
        (ModuleCat.extendScalarsComp (representedAffineCommRingCatHom B S hS g₀).hom
          (representedAffineGlobalStalkRingHom B S hS P x)).hom.app N := by
  simp only [representedAffineStalkPathRight, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, eqToIso.hom, eqToHom_app]

end Chase

end AlgebraicGeometry.Space

end
