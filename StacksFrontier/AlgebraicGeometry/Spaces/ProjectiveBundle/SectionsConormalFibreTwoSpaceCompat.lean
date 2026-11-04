module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceCocycle

/-!
# The two identifications of `(u ∘ h ∘ f')^*ℰ` with an inverse image along `f' ≫ h` agree

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `u : T ⟶ X` and `v : T' ⟶ X'` scheme points,
`h : T' ⟶ T` with `v ≫ g = u ∘ h`, and `f' : Z ⟶ T'`.  The Zariski reading of `(u ∘ h ∘ f')^*ℰ`
is identified with the inverse image of `(u^*ℰ)_Zar` along `f' ≫ h` in two ways: directly
(`AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso`), and through `(v ∘ f')^* g^*ℰ`, the
base change along `f'` and the identification `(v^*g^*ℰ)_Zar ≅ h^*(u^*ℰ)_Zar`.  This file proves
that they agree, from the cocycle of Stacks 03LU at the points and the naturality and cocycle law
of the base-change isomorphisms of the Zariski reading.

## Main results

* `AlgebraicGeometry.Space.pointTwoSpaceCompIso_hom_comp_modulePullbackCompIso_symm_hom`: the
  cocycle of Stacks 03LU at the points, in the spelling of `(v^*g^*ℰ)_Zar ≅ h^*(u^*ℰ)_Zar`.
* `AlgebraicGeometry.Space.zariskiReadingPullbackIso_symm_trans_mapIso_trans`,
  `AlgebraicGeometry.Space.zariskiReadingPullbackIso_symm_trans_comp`: naturality and cocycle law
  of the base change of the Zariski reading, as isomorphisms.
* `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso_eq_twoSpace`: the two identifications
  agree, as isomorphisms; `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso_twoSpace`: the
  same on the underlying morphisms.
* `CategoryTheory.iso_trans_eq_of_paste`: the paste of the comparison, in a bare setting.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/-- Removing two identities from a composite, in a bare category. -/
theorem CategoryTheory.comp_eq_of_comp_eq_of_eq_id {𝒞 : Type*} [Category 𝒞]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : 𝒞} (φ : A₀ ⟶ A₁) (e₁ : A₁ ⟶ A₁) (m₁ : A₁ ⟶ A₂) (a : A₂ ⟶ A₃)
    (b : A₃ ⟶ A₄) (e₂ : A₄ ⟶ A₄) (c : A₄ ⟶ A₅) (d : A₅ ⟶ A₆) (e₆ : A₀ ⟶ A₇) (k : A₇ ⟶ A₆)
    (k' : A₀ ⟶ A₆) (H : (φ ≫ e₁ ≫ m₁ ≫ a ≫ b) ≫ e₂ ≫ c ≫ d = e₆ ≫ k) (he₁ : e₁ = 𝟙 A₁)
    (he₂ : e₂ = 𝟙 A₄) (hk : e₆ ≫ k = k') : φ ≫ m₁ ≫ ((a ≫ b) ≫ c) ≫ d = k' := by
  rw [← hk, ← H, he₁, he₂]
  simp only [Category.assoc, Category.id_comp]

/-- Four images of morphisms under a functor, the first two images of isomorphisms, in a bare
setting. -/
theorem CategoryTheory.Functor.mapIso_hom_comp_mapIso_hom_comp_map_comp_map {𝒞 𝒟 : Type*}
    [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {A₀ A₁ A₂ A₃ A₄ : 𝒞} (i : A₀ ≅ A₁) (j : A₁ ≅ A₂)
    (a : A₂ ⟶ A₃) (b : A₃ ⟶ A₄) (k : A₀ ≅ A₄) (H : i.hom ≫ j.hom ≫ a ≫ b = k.hom) :
    (F.mapIso i).hom ≫ (F.mapIso j).hom ≫ F.map a ≫ F.map b = (F.mapIso k).hom := by
  simp only [Functor.mapIso_hom, ← Functor.map_comp, H]

/-- The paste behind `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso_twoSpace`, for
composites of isomorphisms, in a bare setting. -/
theorem CategoryTheory.iso_trans_hom_eq_of_paste {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒟 ⥤ 𝒞) {A₀ A₁ A₂ A₃ A₄ A₇ : 𝒞} {B₀ B₁ B₂ B₃ : 𝒟}
    (i₀ : A₀ ≅ A₁) (j₀ : A₁ ≅ A₂) (iφ : A₀ ≅ A₃) (i₁ : A₃ ≅ A₄) (j₁ : A₄ ≅ F.obj B₀)
    (k₂ : B₀ ≅ B₁) (k₃ : B₁ ≅ B₂) (l₃ : B₂ ≅ B₃) (pc : F.obj B₃ ⟶ A₂) (pq : A₂ ⟶ A₂)
    (rα : A₄ ⟶ A₇) (rm : A₇ ⟶ A₁) (z₁' : A₇ ⟶ F.obj B₂)
    (hR : iφ.hom ≫ i₁.hom ≫ rα ≫ rm = i₀.hom)
    (C2 : j₁.hom ≫ F.map (k₂.hom ≫ k₃.hom) = rα ≫ z₁')
    (C1 : z₁' ≫ F.map l₃.hom ≫ pc = rm ≫ j₀.hom) (hq : pq = 𝟙 A₂) :
    (i₀ ≪≫ j₀).hom = (iφ ≪≫ i₁ ≪≫ j₁).hom ≫ F.map (k₂ ≪≫ k₃ ≪≫ l₃).hom ≫ pc ≫ pq := by
  rw [hq, Category.comp_id, Iso.trans_hom, ← hR]
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc] at C2 ⊢
  rw [reassoc_of% C2, C1]

/-- Rewriting the factors of a composite with an image under a functor, in a bare setting. -/
theorem CategoryTheory.comp_map_comp_eq_of_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {A₀ A₁ A₆ : 𝒟} {P Q R W : 𝒞} (φ : A₀ ⟶ A₁) (m₁ m₁' : A₁ ⟶ F.obj P) (x : P ⟶ Q)
    (a : P ⟶ R) (b : R ⟶ Q) (c c' : Q ⟶ W) (d : F.obj W ⟶ A₆) (k k' : A₀ ⟶ A₆)
    (hm : m₁ = m₁') (hx : x = a ≫ b) (hc : c = c') (hk : k = k')
    (S : φ ≫ m₁' ≫ ((F.map a ≫ F.map b) ≫ F.map c') ≫ d = k') :
    φ ≫ m₁ ≫ F.map (x ≫ c) ≫ d = k := by
  rw [hm, hx, hc, hk, ← S]
  simp only [Functor.map_comp, Category.assoc]

/-- The paste behind `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso_eq_twoSpace`, for
isomorphisms, in a bare setting. -/
theorem CategoryTheory.iso_trans_eq_of_paste {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒟 ⥤ 𝒞) {A₀ A₁ A₂ A₃ A₄ A₇ : 𝒞} {B₀ B₁ B₂ B₃ : 𝒟}
    (i₀ : A₀ ≅ A₁) (j₀ : A₁ ≅ A₂) (iφ : A₀ ≅ A₃) (i₁ : A₃ ≅ A₄) (j₁ : A₄ ≅ F.obj B₀)
    (k₂ : B₀ ≅ B₁) (k₃ : B₁ ≅ B₂) (l₃ : B₂ ≅ B₃) (pc : F.obj B₃ ≅ A₂) (pq : A₂ ≅ A₂)
    (rα : A₄ ≅ A₇) (rm : A₇ ≅ A₁) (z₁' : A₇ ≅ F.obj B₂)
    (hR : iφ ≪≫ i₁ ≪≫ rα ≪≫ rm = i₀) (C2 : j₁ ≪≫ F.mapIso (k₂ ≪≫ k₃) = rα ≪≫ z₁')
    (C1 : z₁' ≪≫ F.mapIso l₃ ≪≫ pc = rm ≪≫ j₀) (hq : pq.hom = 𝟙 A₂) :
    i₀ ≪≫ j₀ = (iφ ≪≫ i₁ ≪≫ j₁) ≪≫ F.mapIso (k₂ ≪≫ k₃ ≪≫ l₃) ≪≫ pc ≪≫ pq := by
  exact Iso.ext (CategoryTheory.iso_trans_hom_eq_of_paste F i₀ j₀ iφ i₁ j₁ k₂ k₃ l₃ pc.hom pq.hom
    rα.hom rm.hom z₁'.hom (congrArg Iso.hom hR) (congrArg Iso.hom C2) (congrArg Iso.hom C1) hq)

/-- Four images of isomorphisms under a functor, in a bare setting. -/
theorem CategoryTheory.Functor.mapIso_trans_mapIso_trans_mapIso_eq {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {A₀ A₁ A₂ A₃ A₄ : 𝒞} (i : A₀ ≅ A₁) (j : A₁ ≅ A₂) (a : A₂ ≅ A₃)
    (b : A₃ ≅ A₄) (k : A₀ ≅ A₄) (H : i ≪≫ j ≪≫ a ≪≫ b = k) :
    F.mapIso i ≪≫ F.mapIso j ≪≫ F.mapIso a ≪≫ F.mapIso b = F.mapIso k := by
  rw [← H]
  simp only [Functor.mapIso_trans]

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ZariskiNaturality

variable {T₀ T₁ : BigFppfOver B S hS}

/-- **The inverse base-change isomorphisms of the Zariski reading are natural**, at a composite
of two isomorphisms. -/
theorem zariskiReadingPullbackIso_symm_hom_naturality_trans (τ : T₁ ⟶ T₀)
    {M K N : Modules.{u, u} B S hS (yoneda.obj T₀) (isAlgebraicSpace_yoneda B S hS T₀)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (a : M ≅ K) (b : K ≅ N) :
    (zariskiReadingPullbackIso τ M hM).symm.hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ)).map
          (((zariskiReadingFunctor T₀).mapIso a).hom ≫ ((zariskiReadingFunctor T₀).mapIso b).hom) =
      (zariskiReadingFunctor T₁).map
          ((modulePullback B S hS (representedSpaceMap B S hS τ)).map (a.hom ≫ b.hom)) ≫
        (zariskiReadingPullbackIso τ N hN).symm.hom :=
  (congrArg (fun x => (zariskiReadingPullbackIso τ M hM).inv ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ)).map x)
      ((zariskiReadingFunctor T₀).map_comp a.hom b.hom).symm).trans
    (zariskiReadingPullbackIso_inv_naturality τ hM hN (a.hom ≫ b.hom))

/-- **The inverse base-change isomorphisms of the Zariski reading are natural**, at a composite
of two isomorphisms, as isomorphisms. -/
theorem zariskiReadingPullbackIso_symm_trans_mapIso_trans (τ : T₁ ⟶ T₀)
    {M K N : Modules.{u, u} B S hS (yoneda.obj T₀) (isAlgebraicSpace_yoneda B S hS T₀)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (a : M ≅ K) (b : K ≅ N) :
    (zariskiReadingPullbackIso τ M hM).symm ≪≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ)).mapIso
          ((zariskiReadingFunctor T₀).mapIso a ≪≫ (zariskiReadingFunctor T₀).mapIso b) =
      (zariskiReadingFunctor T₁).mapIso
          ((modulePullback B S hS (representedSpaceMap B S hS τ)).mapIso (a ≪≫ b)) ≪≫
        (zariskiReadingPullbackIso τ N hN).symm :=
  Iso.ext (zariskiReadingPullbackIso_symm_hom_naturality_trans τ hM hN a b)

variable {T₂ : BigFppfOver B S hS} in
/-- **The cocycle of the base-change isomorphisms of the Zariski reading**, as isomorphisms. -/
theorem zariskiReadingPullbackIso_symm_trans_comp (τ₁ : T₂ ⟶ T₁) (τ₂ : T₁ ⟶ T₀)
    (N : Modules.{u, u} B S hS (yoneda.obj T₀) (isAlgebraicSpace_yoneda B S hS T₀))
    (hN : N.IsQuasicoherentOnSite)
    (hN' : ((modulePullback B S hS (representedSpaceMap B S hS τ₂)).obj N).IsQuasicoherentOnSite) :
    (zariskiReadingPullbackIso τ₁ _ hN').symm ≪≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ₁)).mapIso
          (zariskiReadingPullbackIso τ₂ N hN).symm ≪≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map τ₁)
          ((BigFppfOver.toScheme B S hS).map τ₂)).app ((zariskiReadingFunctor T₀).obj N) =
      (zariskiReadingFunctor T₂).mapIso ((modulePullbackCompIso B S hS
          (representedSpaceMap B S hS τ₁) (representedSpaceMap B S hS τ₂)).app N) ≪≫
        (zariskiReadingPullbackIso (τ₁ ≫ τ₂) N hN).symm :=
  Iso.ext (zariskiReadingPullbackIso_inv_comp τ₁ τ₂ N hN hN')

end ZariskiNaturality

/-- The comparison of Stacks 03LU along `a`, `c` followed by the identification along
`a ≫ c = d`, at a module. -/
theorem modulePullbackCompIso_trans_eqToIso_app_hom {Y X₁ X₀ : AlgebraicSpaces B S hS} (a : Y ⟶ X₁)
    (c : X₁ ⟶ X₀) (d : Y ⟶ X₀) (p : a ≫ c = d) (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    ((modulePullbackCompIso B S hS a c ≪≫
        eqToIso (congrArg (modulePullback B S hS) p)).app M).hom =
      (modulePullbackCompIso B S hS a c).hom.app M ≫
        (eqToHom (congrArg (modulePullback B S hS) p)).app M := by
  rw [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom]

/-- The inverse of the comparison of Stacks 03LU at a sheaf of modules. -/
theorem modulePullbackCompIso_app_symm_hom_sheaf {Y X₁ X₀ : AlgebraicSpaces B S hS} (a : Y ⟶ X₁)
    (b : X₁ ⟶ X₀) (M : SheafOfModules.{u} (structureRingSheaf B S hS X₀)) :
    ((modulePullbackCompIso B S hS a b).app M).symm.hom =
      (modulePullbackCompIso B S hS a b).inv.app M :=
  rfl

/-- The comparison of Stacks 03LU along `x`, `c` only depends on `x`. -/
theorem modulePullbackCompIso_inv_app_heq_of_eq {W X₁ X₀ : AlgebraicSpaces B S hS}
    {x y : W ⟶ X₁} (e : x = y) (c : X₁ ⟶ X₀) (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullbackCompIso B S hS x c).inv.app M ≍
        (modulePullbackCompIso B S hS y c).inv.app M := by
  subst e
  rfl

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite)
  {T : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {T' : BigFppfOver B S hS}
  (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T) (hvh : v ≫ g.hom = yoneda.map h ≫ u)
  {Z : BigFppfOver B S hS} (f' : Z ⟶ T')

/-- The comparison along `f' ≫ h`, `u` is the identification along `u ∘ h ∘ f' = (f' ≫ h) ≫ u`
followed by the comparison along `f' ; h`, `u`. -/
theorem eqToHom_comp_modulePullbackCompIso_inv_app_representedSpaceMap :
    eqToHom (modulePullback_obj_pointTwoSpace_comp_comp_eq X E u h f') ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f' ≫ representedSpaceMap B S hS h)
          (pointHom u)).inv.app E =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS (f' ≫ h)) (pointHom u)).inv.app E :=
  by
  refine eq_of_heq ?_
  refine (eqToHom_comp_heq _ _).trans ?_
  exact modulePullbackCompIso_inv_app_heq_of_eq
    (ObjectProperty.hom_ext _ (yoneda.map_comp f' h).symm : CategoryStruct.comp
      (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS f')
        (representedSpaceMap B S hS h) =
        representedSpaceMap B S hS (f' ≫ h)) _ _

include hvh

/-- The cocycle of Stacks 03LU at the points, with the comparison `v^*g^* ≅ (u ∘ h)^*` split. -/
theorem pointTwoSpaceCompIso_hom_comp_modulePullbackCompIso_inv_app_split :
    (pointTwoSpaceCompIso X E u g v h hvh f').hom ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
          (pointHom v)).inv.app ((modulePullback B S hS g).obj E) ≫
        (((modulePullback B S hS (representedSpaceMap B S hS f')).map
          ((modulePullbackCompIso B S hS
              (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
              (pointHom v) g).hom.app E) ≫
        (modulePullback B S hS (representedSpaceMap B S hS f')).map
          ((eqToHom (congrArg (modulePullback B S hS
              (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS)))
            (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
              (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
              (pointHom v) g =
                pointHom (X := X) (yoneda.map h ≫ u)))).app E)) ≫
        (modulePullback B S hS (representedSpaceMap B S hS f')).map
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
                (pointHom u)).inv.app E)) ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
          (representedSpaceMap B S hS h)).hom.app ((modulePullback B S hS (pointHom u)).obj E) =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS (f' ≫ h)) (pointHom u)).inv.app E :=
  CategoryTheory.comp_eq_of_comp_eq_of_eq_id _ _ _ _ _ _ _ _ _ _ _
    (pointTwoSpaceCompIso_hom_comp X E u g v h hvh f') (eqToHom_refl _ _)
    ((congrArg _ (eqToHom_refl _ _)).trans (CategoryTheory.Functor.map_id _ _))
    (eqToHom_comp_modulePullbackCompIso_inv_app_representedSpaceMap X E u h f')

/-- `AlgebraicGeometry.Space.pointZariskiModuleTwoSpaceIso`, with the source of `v` read as the
represented algebraic space of `T'`. -/
theorem pointZariskiModuleTwoSpaceIso_eq :
    pointZariskiModuleTwoSpaceIso X E hE g u v h hvh =
      (zariskiReadingFunctor T').mapIso ((modulePullbackCompIso B S hS
          (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
          (pointHom v) g ≪≫
        eqToIso (congrArg (modulePullback B S hS
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS)))
          (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
            (pointHom v) g =
              pointHom (X := X) (yoneda.map h ≫ u)))).app E) ≪≫
        pointZariskiModuleBaseChangeIso X E hE u h :=
  rfl

/-- **The cocycle of Stacks 03LU at the points, in the spelling of
`AlgebraicGeometry.Space.pointZariskiModuleTwoSpaceIso`**: the identification
`(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ`, the comparison along `f'`, `v`, the comparison
`v^*g^* ≅ (u ∘ h)^*` with the comparison along `h`, `u`, and the comparison along `f'`, `h` compose
to the comparison along `f' ≫ h`, `u`. -/
theorem pointTwoSpaceCompIso_hom_comp_modulePullbackCompIso_symm_hom :
    (pointTwoSpaceCompIso X E u g v h hvh f').hom ≫
        CategoryStruct.comp (Y :=
            (modulePullback B S hS (X :=
            (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
            (pointHom v) ⋙ (modulePullback B S hS (representedSpaceMap B S hS f'))).obj
            ((modulePullback B S hS g).obj E)) ((modulePullbackCompIso B S hS
            (representedSpaceMap B S hS f') (pointHom v)).app
            ((modulePullback B S hS g).obj E)).symm.hom
        ((modulePullback B S hS (representedSpaceMap B S hS f')).map
            ((((modulePullbackCompIso B S hS
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
            (pointHom v) g) ≪≫ eqToIso
            (congrArg (modulePullback B S hS
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS)))
            (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
            (pointHom v) g = pointHom (X := X) (yoneda.map h ≫ u)))).app E).hom ≫
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
            (pointHom u)).app E).symm.hom) ≫
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
            (representedSpaceMap B S hS h)).hom.app ((modulePullback B S hS (pointHom u)).obj E))) =
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS (f' ≫ h))
            (pointHom u)).app E).symm.hom :=
  CategoryTheory.comp_map_comp_eq_of_eq (modulePullback B S hS
      (representedSpaceMap B S hS f')) (P :=
      (modulePullback B S hS (X :=
      (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
      (pointHom v)).obj ((modulePullback B S hS g).obj E)) _ _ _ _ _ _ _ _ _ _ _
    (modulePullbackCompIso_app_symm_hom_sheaf _ _ _)
    (modulePullbackCompIso_trans_eqToIso_app_hom
        (Y := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
        (pointHom v) g _ (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp
        (obj := AlgebraicSpaces B S hS)
        (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
        (pointHom v) g = pointHom (X := X) (yoneda.map h ≫ u)) E)
    (modulePullbackCompIso_app_symm_hom_sheaf _ _ _)
    (modulePullbackCompIso_app_symm_hom_sheaf _ _ _)
    (pointTwoSpaceCompIso_hom_comp_modulePullbackCompIso_inv_app_split X E u g v h hvh f')


/-- The cocycle of Stacks 03LU at the points, as isomorphisms: the identification
`(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ`, the comparison along `f'`, `v`, the comparison
`v^*g^* ≅ (u ∘ h)^*` with the comparison along `h`, `u`, and the comparison along `f'`, `h` compose
to the comparison along `f' ≫ h`, `u`. -/
theorem pointTwoSpaceCompIso_trans_modulePullbackCompIso_symm :
    (pointTwoSpaceCompIso X E u g v h hvh f') ≪≫
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS f') (pointHom v)).app
        ((modulePullback B S hS g).obj E)).symm ≪≫
        (modulePullback B S hS
            (representedSpaceMap B S hS f')).mapIso (((modulePullbackCompIso B S hS
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
            (pointHom v) g ≪≫ eqToIso
            (congrArg (modulePullback B S hS
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS)))
            (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
            (pointHom v) g = pointHom (X := X) (yoneda.map h ≫ u)))).app E) ≪≫
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
            (pointHom u)).app E).symm) ≪≫
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
            (representedSpaceMap B S hS h)).app ((modulePullback B S hS (pointHom u)).obj E)) =
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS (f' ≫ h))
            (pointHom u)).app E).symm :=
  Iso.ext (pointTwoSpaceCompIso_hom_comp_modulePullbackCompIso_symm_hom X E u g v h hvh f')

/-- The cocycle of Stacks 03LU at the points, read on the Zariski site of `Z`. -/
theorem zariskiReading_mapIso_pointTwoSpaceCompIso_trans :
    (zariskiReadingFunctor Z).mapIso (pointTwoSpaceCompIso X E u g v h hvh f') ≪≫
        (zariskiReadingFunctor Z).mapIso ((modulePullbackCompIso B S hS
        (representedSpaceMap B S hS f') (pointHom v)).app ((modulePullback B S hS g).obj E)).symm ≪≫
        (zariskiReadingFunctor Z).mapIso ((modulePullback B S hS
            (representedSpaceMap B S hS f')).mapIso
            (((modulePullbackCompIso B S hS
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
            (pointHom v) g ≪≫ eqToIso
            (congrArg (modulePullback B S hS
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS)))
            (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
            (pointHom v) g = pointHom (X := X) (yoneda.map h ≫ u)))).app E) ≪≫
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
            (pointHom u)).app E).symm)) ≪≫
        (zariskiReadingFunctor Z).mapIso ((modulePullbackCompIso B S hS
            (representedSpaceMap B S hS f') (representedSpaceMap B S hS h)).app
            ((modulePullback B S hS (pointHom u)).obj E)) =
            (zariskiReadingFunctor Z).mapIso ((modulePullbackCompIso B S hS
            (representedSpaceMap B S hS (f' ≫ h)) (pointHom u)).app E).symm :=
  CategoryTheory.Functor.mapIso_trans_mapIso_trans_mapIso_eq (zariskiReadingFunctor Z) _ _ _ _ _
    (pointTwoSpaceCompIso_trans_modulePullbackCompIso_symm X E u g v h hvh f')

/-- **The two identifications of `((u ∘ h ∘ f')^*ℰ)_Zar` with `(f' ≫ h)^*(u^*ℰ)_Zar` agree**, as
isomorphisms: the base change of the Zariski reading along `f' ≫ h` is the identification
`(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ`, the base change along `f'`, the inverse image along `f'` of
`(v^*g^*ℰ)_Zar ≅ h^*(u^*ℰ)_Zar` and the comparisons of inverse images along `f'`, `h`
(Stacks 03LU). -/
theorem pointZariskiModuleBaseChangeIso_eq_twoSpace :
    pointZariskiModuleBaseChangeIso X E hE u (f' ≫ h) =
      ((zariskiReadingFunctor Z).mapIso (pointTwoSpaceCompIso X E u g v h hvh f') ≪≫
          pointZariskiModuleBaseChangeIso X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) v f') ≪≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map f')).mapIso
          (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) ≪≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map f')
            ((BigFppfOver.toScheme B S hS).map h)).app (pointZariskiModule X E T u) ≪≫
        (Scheme.Modules.pullbackCongr ((BigFppfOver.toScheme B S hS).map_comp f' h).symm).app
          (pointZariskiModule X E T u) := by
  rw [pointZariskiModuleTwoSpaceIso_eq X E hE u g v h hvh]
  simp only [pointZariskiModuleBaseChangeIso]
  exact CategoryTheory.iso_trans_eq_of_paste _ _ _ _ _ _ _ _ _ _ _
    ((zariskiReadingFunctor Z).mapIso
        ((modulePullback B S hS (representedSpaceMap B S hS f')).mapIso
        (((modulePullbackCompIso B S hS
        (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
        (pointHom v) g ≪≫ eqToIso
        (congrArg (modulePullback B S hS
        (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS)))
        (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
        (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
        (pointHom v) g = pointHom (X := X) (yoneda.map h ≫ u)))).app E) ≪≫
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom u)).app E).symm)))
    ((zariskiReadingFunctor Z).mapIso
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
        (representedSpaceMap B S hS h)).app ((modulePullback B S hS (pointHom u)).obj E)))
    (zariskiReadingPullbackIso f' ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
        ((modulePullback B S hS (pointHom u)).obj E))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) _ (isQuasicoherentOnSite_pointPullback X E hE T u))).symm
    (zariskiReading_mapIso_pointTwoSpaceCompIso_trans X E u g v h hvh f')
    (zariskiReadingPullbackIso_symm_trans_mapIso_trans f'
        (isQuasicoherentOnSite_pointPullback X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) _ (isQuasicoherentOnSite_pointPullback X E hE T u))
        ((modulePullbackCompIso B S hS
        (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
        (pointHom v) g ≪≫ eqToIso
        (congrArg (modulePullback B S hS
        (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS)))
        (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
        (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
        (pointHom v) g = pointHom (X := X) (yoneda.map h ≫ u)))).app E)
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom u)).app E).symm)
    (zariskiReadingPullbackIso_symm_trans_comp f' h ((modulePullback B S hS (pointHom u)).obj E)
        (isQuasicoherentOnSite_pointPullback X E hE T u)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) _ (isQuasicoherentOnSite_pointPullback X E hE T u)))
    ((Stacks.RelativeProj.pullbackCongr_hom_app ((BigFppfOver.toScheme B S hS).map_comp f' h).symm
      (pointZariskiModule X E T u)).trans (eqToHom_refl _ _))

/-- **The two identifications of `((u ∘ h ∘ f')^*ℰ)_Zar` with `(f' ≫ h)^*(u^*ℰ)_Zar` agree**: the
base change of the Zariski reading along `f' ≫ h` is the identification
`(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ`, the base change along `f'`, the inverse image along `f'` of
`(v^*g^*ℰ)_Zar ≅ h^*(u^*ℰ)_Zar` and the comparisons of inverse images along `f'`, `h`
(Stacks 03LU). -/
theorem pointZariskiModuleBaseChangeIso_twoSpace :
    (pointZariskiModuleBaseChangeIso X E hE u (f' ≫ h)).hom =
      ((zariskiReadingFunctor Z).mapIso (pointTwoSpaceCompIso X E u g v h hvh f') ≪≫
          pointZariskiModuleBaseChangeIso X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) v f').hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map f')).map
          (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh).hom ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map f')
            ((BigFppfOver.toScheme B S hS).map h)).hom.app (pointZariskiModule X E T u) ≫
        (Scheme.Modules.pullbackCongr ((BigFppfOver.toScheme B S hS).map_comp f' h).symm).hom.app
          (pointZariskiModule X E T u) :=
  congrArg Iso.hom (pointZariskiModuleBaseChangeIso_eq_twoSpace X E hE u g v h hvh f')

end AlgebraicGeometry.Space

end
