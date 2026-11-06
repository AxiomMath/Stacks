module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSingleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesSpellingBridge

/-!
# The derived counit against a map into an affine direct image, in degree zero

For an affine morphism `f : X ⟶ Y` of algebraic spaces, a quasi-coherent `𝒪_X`-module `M` and a
map `a : G ⟶ f_*M`, consider `Lf^*(G[0]) ⟶ Lf^*((f_*M)[0]) ≅ Lf^*Rf_*(M[0]) ⟶ M[0]`, built from
`a`, the identification `Rf_*(M[0]) ≅ (f_*M)[0]` and the counit of `Lf^* ⊣ Rf_*`. When the
transpose `f^*G ⟶ M` of `a` is an isomorphism, this map is the comparison
`Lf^*(G[0]) ⟶ (f^*G)[0]` followed by an isomorphism (Stacks 0FPI in degree `0`).

## Main definitions

* `AlgebraicGeometry.Space.SingleCounitCompatible`: that statement, in the topos spelling, the
  site-spelled inputs crossing through the identity bridges of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulesSpellingBridge.lean`.

## Main results

* `Stacks.DerivedSingleCounit.exists_single_counit`: the statement for abstract data, from
  Stacks 0FPI for the derived adjunction and the comparison of the two degreewise adjunctions.
* `Stacks.DerivedSingleCounit.exists_single_counit_comparison`: the same, with the comparison of
  the two degreewise pullbacks folded into the isomorphism, which is the form of
  `AlgebraicGeometry.Space.SingleCounitCompatible`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedSingleCounit

variable {A Bc : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Category Bc] [Abelian Bc] [HasDerivedCategory Bc]

/-- Bookkeeping shape for `singleFunctor_map_comp_mapSingleQhIso_inv`. -/
theorem comp_comp_shape {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ Z : C} (sa : X₁ ⟶ X₂)
    (qi₂ : X₂ ⟶ Y₂) (qs : Y₂ ⟶ Z) (i : X₁ ⟶ X₁) (qi₁ : X₁ ⟶ Y₁) (qa : Y₁ ⟶ Y₂) (qas : Y₁ ⟶ Z)
    (hi : i = 𝟙 _) (h : sa ≫ qi₂ = qi₁ ≫ qa) (hc : qas = qa ≫ qs) :
    sa ≫ qi₂ ≫ qs = i ≫ qi₁ ≫ qas := by
  subst hi hc
  simp [reassoc_of% h]

/-- `a[0] ≫ (w-single comparison)⁻¹` is the image of a map of complexes. -/
@[reassoc]
theorem singleFunctor_map_comp_mapSingleQhIso_inv (w : A ⥤ Bc) [w.Additive] {G : Bc} {M : A}
    (a : G ⟶ w.obj M) :
    (DerivedCategory.singleFunctor Bc 0).map a ≫
        (Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app M =
      (DerivedCategory.singleFunctorIsoCompQ Bc 0).hom.app G ≫
        (DerivedCategory.quotientCompQhIso Bc).inv.app
          ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient Bc (ComplexShape.up ℤ)).map
          ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).map a ≫
            (HomologicalComplex.singleMapHomologicalComplex w (ComplexShape.up ℤ) 0).inv.app
              M)) := by
  rw [mapSingleQhIso_inv_app]
  exact comp_comp_shape _ _ _ _ _ _ _ rfl
    ((DerivedCategory.quotientCompQhIso Bc).inv.naturality
      ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).map a))
    (by rw [Functor.map_comp, Functor.map_comp]; rfl)

/-- Bookkeeping shape for `exists_single_counit`. -/
theorem exists_single_counit_shape {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {X₀ X₁ X₂ : C} {Y₀ Y₁ : D} {Z₁ Z₂ Z₃ Z₄ : D}
    (i : X₀ ⟶ X₀) (qi : X₀ ⟶ X₁) (θ : X₁ ⟶ X₂) (uK : X₂ ⟶ R.obj Y₀) (d : Y₀ ⟶ Y₁)
    (c₂ : L.obj X₂ ⟶ Z₂) (e : Z₂ ⟶ Y₀) (c₁ : L.obj X₁ ⟶ Z₁) (Pθ : Z₁ ⟶ Z₂)
    (k : Z₁ ⟶ Z₃) (m : Z₃ ⟶ Z₄) (vh : Z₄ ⟶ Y₁) (hi : i = 𝟙 _)
    (hLu : L.map uK ≫ adj.counit.app Y₀ = c₂ ≫ e) (hn : L.map θ ≫ c₂ = c₁ ≫ Pθ)
    (hD : Pθ ≫ e ≫ d = k ≫ m ≫ vh) :
    L.map ((i ≫ qi ≫ θ) ≫ uK ≫ R.map d) ≫ adj.counit.app Y₁ =
      L.map i ≫ (L.map qi ≫ c₁ ≫ k ≫ m) ≫ vh := by
  subst hi
  have hc := adj.counit.naturality d
  simp only [Functor.comp_map, Functor.id_map] at hc
  simp only [Functor.map_comp, Category.assoc, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hc, reassoc_of% hLu, reassoc_of% hn, hD]

/-- The degreewise counit after `P(a[0])`, through the comparison of left adjoints. -/
theorem complex_counit_comp (F : A ⥤ Bc) [F.Additive] (P mp : Bc ⥤ A) [P.Additive] [mp.Additive]
    (adjT : P ⊣ F) (adjM : mp ⊣ F) {G : Bc} {M : A} (a : G ⟶ F.obj M) :
    (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).map a ≫
          (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M) ≫
      (NatTrans.mapHomologicalComplex adjT.counit (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) =
    (NatIso.mapHomologicalComplex (adjT.leftAdjointUniq adjM) (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G) ≫
      (HomologicalComplex.singleMapHomologicalComplex mp (ComplexShape.up ℤ) 0).hom.app G ≫
        (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map ((adjM.homEquiv _ _).symm a) := by
  rw [Functor.map_comp, Category.assoc, complex_counit F P mp adjT adjM M]
  have h₁ :=
    (NatIso.mapHomologicalComplex (adjT.leftAdjointUniq adjM) (ComplexShape.up ℤ)).hom.naturality
    ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).map a)
  have h₂ :=
    (HomologicalComplex.singleMapHomologicalComplex mp (ComplexShape.up ℤ) 0).hom.naturality a
  simp only [Functor.comp_map] at h₁ h₂
  rw [reassoc_of% h₁, reassoc_of% h₂, Adjunction.homEquiv_counit, Functor.map_comp]

/-- **The derived counit against a map into a direct image, in degree `0`, for abstract data.**
`L ⊣ R` is a derived adjunction whose unit `u` and comparison `cmp` satisfy Stacks 0FPI
(`h0`) for the degreewise adjunction `P ⊣ F`; `mp ⊣ w` is a second degreewise adjunction with
`F = w`, and `pm : P ≅ mp` is the comparison of left adjoints. If the transpose of
`a : G ⟶ w M` under `mp ⊣ w` is an isomorphism, then `L(a[0]) ≫ L(canonical map) ≫ ε` is the
comparison `L(G[0]) ⟶ (mp G)[0]` followed by an isomorphism. -/
theorem exists_single_counit (F w : A ⥤ Bc) [F.Additive] [w.Additive] (hF : F = w)
    (P mp : Bc ⥤ A) (hP : P.Additive) (hmp : mp.Additive) (adjT : P ⊣ F) (adjM : mp ⊣ w)
    (L : DerivedCategory Bc ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ DerivedCategory Bc)
    (adjD : L ⊣ R)
    (u : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    (cmp : DerivedCategory.Qh ⋙ L ⟶ P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (h0 : ∀ K, L.map (u.app K) ≫ adjD.counit.app (DerivedCategory.Qh.obj K) =
      cmp.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((adjT.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K))
    (E : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh =
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    (hα : α = eqToHom E ≫ u)
    {G : Bc} {M : A} (a : G ⟶ w.obj M) (ha : IsIso ((adjM.homEquiv _ _).symm a))
    (i₁ : (DerivedCategory.singleFunctor Bc 0).obj G ⟶ (DerivedCategory.singleFunctor Bc 0).obj G)
    (hi₁ : i₁ = 𝟙 _)
    (i₂ : R.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      R.obj ((DerivedCategory.singleFunctor A 0).obj M)) (hi₂ : i₂ = 𝟙 _) :
    ∃ v : DerivedCategory.Q.obj ((mp.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≅
        (DerivedCategory.singleFunctor A 0).obj M,
      L.map (i₁ ≫ ((DerivedCategory.singleFunctor Bc 0).map a ≫
          ((Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app M ≫
            α.app ((HomotopyCategory.singleFunctor A 0).obj M) ≫
            R.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app M))) ≫ i₂) ≫
        adjD.counit.app ((DerivedCategory.singleFunctor A 0).obj M) =
      L.map ((DerivedCategory.singleFunctorIsoCompQ Bc 0).hom.app G) ≫
        (L.map ((DerivedCategory.quotientCompQhIso Bc).inv.app
            ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≫
          cmp.app ((HomotopyCategory.quotient Bc (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≫
          (DerivedCategory.quotientCompQhIso A).hom.app
            ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (adjT.leftAdjointUniq (adjM.ofNatIsoRight (eqToIso hF).symm))
              (ComplexShape.up ℤ)).hom.app
              ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G))) ≫ v.hom := by
  subst hF hi₁ hi₂ hα
  have hadj : adjM.ofNatIsoRight (eqToIso rfl).symm = adjM := by
    ext X
    simp [Adjunction.ofNatIsoRight]
  rw [hadj]
  let τ := (adjM.homEquiv _ _).symm a
  refine ⟨DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex mp (ComplexShape.up ℤ) 0).app G ≪≫
      (HomologicalComplex.single A (ComplexShape.up ℤ) 0).mapIso (asIso τ)), ?_⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [singleFunctor_map_comp_mapSingleQhIso_inv_assoc]
  refine exists_single_counit_shape adjD _ _ _ _ _ _ _ _ _ _ _ _ rfl (h0 _)
    (cmp.naturality _) ?_
  rw [singleFunctorIsoCompQh_inv_app]
  refine (quotientCompQhIso_shape _ _ _ _ _ (complex_counit_comp F P mp adjT adjM a)).trans ?_
  simp only [Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp, Iso.app_hom, asIso_hom, τ]


/-- Bookkeeping shape for `exists_single_counit_comparison`. -/
theorem assoc_shape {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C} (x : X₀ ⟶ X₁)
    (p : X₁ ⟶ X₂) (q : X₂ ⟶ X₃) (r : X₃ ⟶ X₄) (s : X₄ ⟶ X₅) (t : X₅ ⟶ X₆) (st : X₄ ⟶ X₆)
    (hst : st = s ≫ t) : x ≫ (p ≫ q ≫ r ≫ s) ≫ t = x ≫ (p ≫ q ≫ r) ≫ st := by
  subst hst
  simp only [Category.assoc]

/-- `Stacks.DerivedSingleCounit.exists_single_counit` with the comparison of left adjoints folded
into the isomorphism: the comparison is the one of the derived pullback with the degreewise
pullback `P`. -/
theorem exists_single_counit_comparison (F w : A ⥤ Bc) [F.Additive] [w.Additive] (hF : F = w)
    (P mp : Bc ⥤ A) (hP : P.Additive) (hmp : mp.Additive) (adjT : P ⊣ F) (adjM : mp ⊣ w)
    (L : DerivedCategory Bc ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ DerivedCategory Bc)
    (adjD : L ⊣ R)
    (u : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    (cmp : DerivedCategory.Qh ⋙ L ⟶ P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (h0 : ∀ K, L.map (u.app K) ≫ adjD.counit.app (DerivedCategory.Qh.obj K) =
      cmp.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((adjT.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K))
    (E : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh =
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    (hα : α = eqToHom E ≫ u)
    {G : Bc} {M : A} (a : G ⟶ w.obj M) (ha : IsIso ((adjM.homEquiv _ _).symm a))
    (i₁ : (DerivedCategory.singleFunctor Bc 0).obj G ⟶ (DerivedCategory.singleFunctor Bc 0).obj G)
    (hi₁ : i₁ = 𝟙 _)
    (i₂ : R.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      R.obj ((DerivedCategory.singleFunctor A 0).obj M)) (hi₂ : i₂ = 𝟙 _) :
    ∃ v : DerivedCategory.Q.obj ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≅
        (DerivedCategory.singleFunctor A 0).obj M,
      L.map (i₁ ≫ ((DerivedCategory.singleFunctor Bc 0).map a ≫
          ((Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app M ≫
            α.app ((HomotopyCategory.singleFunctor A 0).obj M) ≫
            R.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app M))) ≫ i₂) ≫
        adjD.counit.app ((DerivedCategory.singleFunctor A 0).obj M) =
      L.map ((DerivedCategory.singleFunctorIsoCompQ Bc 0).hom.app G) ≫
        (L.map ((DerivedCategory.quotientCompQhIso Bc).inv.app
            ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≫
          cmp.app ((HomotopyCategory.quotient Bc (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≫
          (DerivedCategory.quotientCompQhIso A).hom.app
            ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G))) ≫ v.hom := by
  obtain ⟨v, hv⟩ := exists_single_counit F w hF P mp hP hmp adjT adjM L R adjD u cmp h0 E α hα a
    ha i₁ hi₁ i₂ hi₂
  refine ⟨DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
    (adjT.leftAdjointUniq (adjM.ofNatIsoRight (eqToIso hF).symm)) (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≪≫ v, ?_⟩
  rw [hv]
  exact assoc_shape _ _ _ _ _ _ _ rfl

end Stacks.DerivedSingleCounit

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  AlgebraicGeometry.Space.modules_abelian
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The derived counit against a map into an affine direct image, in degree `0`.** For an
affine `f : X ⟶ Y`, a quasi-coherent `𝒪_X`-module `M` and a map `a : G ⟶ f_*M`, the map
`Lf^*(G[0]) ⟶ Lf^*((f_*M)[0]) ≅ Lf^*Rf_*(M[0]) ⟶ M[0]` is the comparison
`Lf^*(G[0]) ⟶ (f^*G)[0]` of the derived pullback with the degreewise pullback of the ringed
topoi (`AlgebraicGeometry.Space.smallEtaleDerivedPullbackQComparison`) followed by an
isomorphism. Stated in the topos spelling; the inputs in the site spelling enter through
`AlgebraicGeometry.Space.spaceToToposModules`, `AlgebraicGeometry.Space.spaceToToposDerived` and
the identity isomorphisms of `StacksFrontier/AlgebraicGeometry/Spaces/ModulesSpellingBridge.lean`. -/
def SingleCounitCompatible (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    {G : Modules.{u, u} B S hS Y.1 Y.2} (a : G ⟶ (modulePushforward B S hS f).obj M) : Prop :=
  ∃ v : (@DerivedCategory.Q (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _
      (toposModulesAbelian X) (toposHasDerivedCategory X)).obj
      (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (ComplexShape.up ℤ) 0).obj ((spaceToToposModules Y).obj G))) ≅
      (spaceToToposDerived X).obj ((spaceDerivedSingle B S hS X 0).obj M),
    (smallEtaleDerivedModulePullback B S hS f).map
        ((singleSpaceToToposIso Y).inv.app G ≫
          (spaceToToposDerived Y).map
            ((spaceDerivedSingle B S hS Y 0).map a ≫
              (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS f hf M hM).inv) ≫
          (derivedPushforwardSpaceToToposIso f).hom.app ((spaceDerivedSingle B S hS X 0).obj M)) ≫
      (smallEtaleDerivedModuleAdjunction B S hS f).counit.app
        ((spaceToToposDerived X).obj ((spaceDerivedSingle B S hS X 0).obj M)) =
    (smallEtaleDerivedModulePullback B S hS f).map
        ((DerivedCategory.singleFunctorIsoCompQ
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0).hom.app
            ((spaceToToposModules Y).obj G)) ≫
      smallEtaleDerivedPullbackQComparison f
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (ComplexShape.up ℤ) 0).obj ((spaceToToposModules Y).obj G)) ≫ v.hom
end AlgebraicGeometry.Space
