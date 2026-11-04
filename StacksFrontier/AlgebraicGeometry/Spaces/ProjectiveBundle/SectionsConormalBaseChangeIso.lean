module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalBaseChange

/-!
# Base change of the conormal isomorphism of Stacks 0B4I at a chart of the source

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `σ` a section of `𝐏(ℰ) ⟶ X` and `σ'` a
section of `𝐏(g^*ℰ) ⟶ X'` over it, and let `v : T' ⟶ X'`, `u : T ⟶ X` be étale scheme points
with `v ≫ g = u ∘ h`.  This file checks the base change of a glued conormal isomorphism on the
Zariski reading at `v`, for arbitrary sources `K` on `X`, `K'` on `X'` and a base-change map
`g^*K ⟶ K'`, given the readings of the two isomorphisms at `u` and at `v` as chart isomorphisms
and the compatibility of the source readings along `h`.

## Main results

* `AlgebraicGeometry.Space.sectionConormalTargetBaseChangeHom_paste_chartIso`,
  `AlgebraicGeometry.Space.sectionConormalTargetBaseChangeHom_paste_comparison`: the paste of the
  target maps along `v ≫ g = u ∘ h` with the chart isomorphism at `v`, through the comparison
  `h^*u^* ≅ v^*g^*` of Stacks 03LU.
* `AlgebraicGeometry.Space.zariskiReading_conormal_baseChange_chart`: the base change of a glued
  conormal isomorphism at a chart of the source.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

/-- The comparison of the source readings in `CategoryTheory.Functor.conormalGlue_baseChange`:
`R'` of `a` followed by `c`. -/
def CategoryTheory.Functor.conormalGlueComparison {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [Category ℬ] [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ 𝒟) (R : ℬ ⥤ 𝒞) (R' : 𝒜 ⥤ 𝒟)
    {Ku : ℬ} {Kx N : 𝒜} (a : Kx ⟶ N) (c : R'.obj N ⟶ P.obj (R.obj Ku)) :
    R'.obj Kx ⟶ P.obj (R.obj Ku) :=
  R'.map a ≫ c

/-- The comparison of the source readings in `CategoryTheory.Functor.conormalGlue_baseChange`
built from inverses `b` of `a` and `pK` of `c` is a left inverse of `pK ≫ R'(b)`. -/
theorem CategoryTheory.Functor.conormalGlue_baseChange_hcK {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [Category ℬ] [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ 𝒟) (R : ℬ ⥤ 𝒞) (R' : 𝒜 ⥤ 𝒟)
    (Φ : ℬ ⥤ 𝒜) {Ku : ℬ} {Kx : 𝒜} (a : Kx ⟶ Φ.obj Ku) (b : Φ.obj Ku ⟶ Kx) (hab : a ≫ b = 𝟙 Kx)
    (c : R'.obj (Φ.obj Ku) ⟶ P.obj (R.obj Ku)) (pK : P.obj (R.obj Ku) ⟶ R'.obj (Φ.obj Ku))
    (hc : c ≫ pK = 𝟙 _) :
    CategoryTheory.Functor.conormalGlueComparison P R R' a c ≫ pK ≫ R'.map b = 𝟙 _ := by
  unfold CategoryTheory.Functor.conormalGlueComparison
  rw [Category.assoc, reassoc_of% hc, ← R'.map_comp, hab, R'.map_id]

/-- Naturality of a transformation between two composites of functors, with the objects
spelled through the two functors. -/
theorem CategoryTheory.NatTrans.naturality_comp_comp {𝒞 𝒟 𝒟' ℰ : Type*} [Category 𝒞]
    [Category 𝒟] [Category 𝒟'] [Category ℰ] (F₁ : 𝒞 ⥤ 𝒟) (F₂ : 𝒟 ⥤ ℰ) (G₁ : 𝒞 ⥤ 𝒟')
    (G₂ : 𝒟' ⥤ ℰ) (η : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) {M N : 𝒞} (f : M ⟶ N) :
    @CategoryStruct.comp ℰ _ (F₂.obj (F₁.obj M)) (F₂.obj (F₁.obj N)) (G₂.obj (G₁.obj N))
        (F₂.map (F₁.map f)) (η.app N) =
      @CategoryStruct.comp ℰ _ (F₂.obj (F₁.obj M)) (G₂.obj (G₁.obj M)) (G₂.obj (G₁.obj N))
        (η.app M) (G₂.map (G₁.map f)) :=
  η.naturality f

/-- The isomorphism `α ≪≫ eqToIso e ≪≫ β⁻¹` evaluated at `M`, followed by its inverse written
out. -/
theorem CategoryTheory.Iso.trans_eqToIso_symm_hom_app_comp {𝒞 ℰ : Type*} [Category 𝒞]
    [Category ℰ] {F G H K : 𝒞 ⥤ ℰ} (α : F ≅ G) (e : G = H) (β : K ≅ H) (M : 𝒞)
    (e' : H.obj M = G.obj M) :
    (α ≪≫ eqToIso e ≪≫ β.symm).hom.app M ≫ β.hom.app M ≫ eqToHom e' ≫ α.inv.app M = 𝟙 _ := by
  subst e
  simp

/-- Cancelling a left inverse `a ≫ b ≫ c` of `Ψ` in a description `t = a ≫ b ≫ c ≫ R`. -/
theorem CategoryTheory.comp_eq_of_comp_comp_comp_eq_id {𝒞 : Type*} [Category 𝒞]
    {A D E₁ E₂ W : 𝒞} (Ψ : A ⟶ D) (a : D ⟶ E₁) (b : E₁ ⟶ E₂) (c : E₂ ⟶ A) (R : A ⟶ W)
    (t : D ⟶ W) (hΨ : Ψ ≫ a ≫ b ≫ c = 𝟙 A) (ht : t = a ≫ b ≫ c ≫ R) : Ψ ≫ t = R := by
  rw [ht]
  simp only [← Category.assoc] at hΨ ⊢
  rw [hΨ, Category.id_comp]

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))
  {T T' : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1) (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T)
  (hvh : v ≫ g.hom = yoneda.map h ≫ u)
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)
  (σ' : X' ⟶ relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
  (hσ' : σ' ≫ projectiveBundleπ X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' = 𝟙 X')
  (comm : σ' ≫ (projectiveBundleBaseChange X E hE hb g hb') = g ≫ σ)

/-- **The paste of the target maps along `v ≫ g = u ∘ h`, with the chart isomorphism at `v`**
(`u`, `v` étale): `v^*` of the base-change map `g^*𝒞_σ ⟶ 𝒞_{σ'}` followed by the chart
isomorphism at `v` is, through the composition comparisons of Stacks 03LU, `h^*` of the chart
isomorphism at `u` followed by the map of conormal algebras of the square of sections `k'_v`,
`k_u` over `h`. -/
theorem sectionConormalTargetBaseChangeHom_paste_chartIso (hu : IsEtale B S hS u)
    (hv : IsEtale B S hS v) :
    ((modulePullback B S hS (pointHom v)).map (X :=
        (modulePullback B S hS g).obj (conormalModuleOfImmersion B S hS
        (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) (Y :=
              (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X' ((modulePullback B
              S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2
              X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
              (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm)) ≫
              (sectionConormalChartIso X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
              hv).hom =
    (modulePullbackCompIso B S hS (pointHom v) g).hom.app (conormalModuleOfImmersion B S hS
        (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫
      eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶
          X => (modulePullback B S hS k).obj (conormalModuleOfImmersion B S hS
          (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) (ObjectProperty.hom_ext
              _ hvh : pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u)) ≫
      (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u)).inv.app
          (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫
      (modulePullback B S hS (yonedaSpaceMap h)).map (sectionConormalChartIso X E hE hb σ hσ T u
          hu).hom ≫ (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap h) (yonedaSpaceMap
          (sectionFibreLift X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v))
          (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T u)) (yonedaSpaceMap
          (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh))
          (yonedaSpaceMap_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v
          h hvh σ hσ σ' hσ' comm) 1) := by
  have e₁ : (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm) =
      (conormalAlgebraPieceSquareMapOfIsos B S hS g σ' σ (projectiveBundleBaseChange X E hE hb g
      hb') comm 1 (M := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2
      X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
              (sectionConormalTargetPieceIso X E hE hb σ hσ) (M' :=
              (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X' ((modulePullback B
              S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2
              X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
              (sectionConormalTargetPieceIso X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')) := rfl
  have e₂ : (sectionConormalChartIso X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v hv).hom =
      (conormalAlgebraPieceSquareMapOfIso B S hS (pointHom v) (yonedaSpaceMap (sectionFibreLift X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
      hE g) hb' σ' hσ' T' v)) σ' (pointHom (X :=
      relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreToSpace T' v)) (isPullback_sectionFibreLift X' ((modulePullback B
      S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T'
      v).w.symm 1 (M := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
      hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
              (sectionConormalTargetPieceIso X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')) :=
    (sectionConormalTargetPointHom_eq_chartIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
        hv).symm.trans rfl
  have a := congrArg₂ (fun (a : (modulePullback B S hS g).obj (conormalModuleOfImmersion B S hS
      (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ⟶
              (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X' ((modulePullback B
              S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2
              X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
      (b : (modulePullback B S hS (pointHom v)).obj (conormalModuleOfImmersion B S hS
          (relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))) ⟶
        (conormalAlgebra B S hS (yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj
            E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T'
            v))).piece 1) =>
      (modulePullback B S hS (pointHom v)).map a ≫ b) e₁ e₂
  have b := modulePullback_map_conormalAlgebraPieceSquareMapOfIsos_comp σ g σ'
      (projectiveBundleBaseChange X E hE hb g hb') (pointHom v)
    (yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)) (pointHom
        (X := relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v)) comm (isPullback_sectionFibreLift X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' σ' hσ' T' v).w.symm (sectionFibreLift_baseChange_outer_w X E hE hb g hb' v σ σ'
        hσ' comm) 1 (M := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE
        hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
              (sectionConormalTargetPieceIso X E hE hb σ hσ) (M' :=
              (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X' ((modulePullback B
              S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2
              X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
              (sectionConormalTargetPieceIso X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')
  exact CategoryTheory.conormalTargetPaste_right _ _ _ _ _ _ _ _ (a.trans b)
    (sectionConormalTargetBaseChangeHom_paste_right X E hE hb g hb' u v h hvh σ hσ σ' hσ' comm hu)
    (Iso.inv_hom_id_app _ _) ((eqToHom_trans _ _).trans (eqToHom_refl _ _))


/-- **The paste of the target maps along `v ≫ g = u ∘ h`, through the comparison of the inverse
images**: the comparison `h^*u^* ⟶ v^*g^*` followed by `v^*` of the base-change map and the
chart isomorphism at `v` is `h^*` of the chart isomorphism at `u` followed by the map of
conormal algebras of the square of sections `k'_v`, `k_u` over `h`. -/
theorem sectionConormalTargetBaseChangeHom_paste_comparison (hu : IsEtale B S hS u)
    (hv : IsEtale B S hS v) :
    (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫
        eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g =
        yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
        (modulePullbackCompIso B S hS (pointHom v) g).symm).hom.app (conormalModuleOfImmersion B S
        hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫
              ((modulePullback B S hS (pointHom v)).map (X :=
              (modulePullback B S hS g).obj (conormalModuleOfImmersion B S hS
              (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) (Y :=
              (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X' ((modulePullback B
              S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2
              X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
              (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm)) ≫
              (sectionConormalChartIso X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
              hv).hom =
      (modulePullback B S hS (yonedaSpaceMap h)).map (sectionConormalChartIso X E hE hb σ hσ T u
          hu).hom ≫ (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap h) (yonedaSpaceMap
          (sectionFibreLift X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v))
          (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T u)) (yonedaSpaceMap
          (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh))
          (yonedaSpaceMap_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v
          h hvh σ hσ σ' hσ' comm) 1) :=
  CategoryTheory.comp_eq_of_comp_comp_comp_eq_id ((modulePullbackCompIso B S hS (yonedaSpaceMap h)
      (pointHom u) ≪≫ eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh :
      pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
      (modulePullbackCompIso B S hS (pointHom v) g).symm).hom.app (conormalModuleOfImmersion B S hS
      (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
    ((modulePullbackCompIso B S hS (pointHom v) g).hom.app (conormalModuleOfImmersion B S hS
        (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
    (eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶
        X => (modulePullback B S hS k).obj (conormalModuleOfImmersion B S hS
        (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) (ObjectProperty.hom_ext
              _ hvh : pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u)))
    ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u)).inv.app
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
    ((modulePullback B S hS (yonedaSpaceMap h)).map (sectionConormalChartIso X E hE hb σ hσ T u
        hu).hom ≫ (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap h) (yonedaSpaceMap
        (sectionFibreLift X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v))
        (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T u)) (yonedaSpaceMap
        (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh))
        (yonedaSpaceMap_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v h
        hvh σ hσ σ' hσ' comm) 1)) (((modulePullback B S hS (pointHom v)).map (X :=
        (modulePullback B S hS g).obj (conormalModuleOfImmersion B S hS
        (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) (Y :=
              (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X' ((modulePullback B
              S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2
              X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
              (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm)) ≫
              (sectionConormalChartIso X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
              hv).hom)
    (CategoryTheory.Iso.trans_eqToIso_symm_hom_app_comp
      (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u))
      (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g =
          yonedaSpaceMap h ≫ pointHom u).symm) (modulePullbackCompIso B S hS (pointHom v) g)
          (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))
      (congrArg (fun k : yonedaSpace B S hS T' ⟶
          X => (modulePullback B S hS k).obj (conormalModuleOfImmersion B S hS
          (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) (ObjectProperty.hom_ext
              _ hvh : pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u)))
    (sectionConormalTargetBaseChangeHom_paste_chartIso X E hE hb g hb' u v h hvh σ hσ σ' hσ' comm hu
        hv)

/-- **The base change of a glued conormal isomorphism at a chart of the source** (for arbitrary
sources `K` on `X`, `K'` on `X'` and a base-change map `sB : g^*K ⟶ K'`): let `φ` read at the
étale point `u` of `X` as the chart isomorphism through `s`, `θ`, `F`, and `φ'` at the étale point
`v` of `X'` as the chart isomorphism through `s'`, `θ'`, `F'`, with `v ≫ g = u ∘ h`.  Given the
compatibility `hpt` of `s`, `θ`, `F` and `s'`, `θ'`, `F'` along `h`, the Zariski readings of
`v^*(g^*φ ≫ (g^*𝒞_σ ⟶ 𝒞_{σ'}))` and of `v^*(sB ≫ φ')` agree. -/
theorem zariskiReading_conormal_baseChange_chart (hu : IsEtale B S hS u) (hv : IsEtale B S hS v)
    {K : Modules.{u, u} B S hS X.1 X.2} (hK : K.IsQuasicoherentOnSite)
    {K' : Modules.{u, u} B S hS X'.1 X'.2} (φ : K ⟶
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) (φ' : K' ⟶
              (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X' ((modulePullback B
              S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2
              X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
    (sB : (modulePullback B S hS g).obj K ⟶ K')
    {a₁ a₂ : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    {b₁ b₂ : ((BigFppfOver.toScheme B S hS).obj T').Modules}
    (s : (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom u)).obj K) ⟶ a₁)
    (hs : IsIso s) (θ : a₁ ≅ a₂)
    (F : haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
      a₂ ≅ Stacks.Conormal.conormalSheaf (Z := (BigFppfOver.toScheme B S hS).obj T)
        (X := (BigFppfOver.toScheme B S hS).obj ((projectiveBundleSituation X E hE
            hb).relativeProjPoints.fibre T u))
        ((BigFppfOver.toScheme B S hS).map (sectionFibreLift X E hE hb σ hσ T u)))
    (s' : (zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom v)).obj K') ⟶ b₁)
    (hs' : IsIso s') (θ' : b₁ ≅ b₂)
    (F' : haveI := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
      b₂ ≅ Stacks.Conormal.conormalSheaf (Z := (BigFppfOver.toScheme B S hS).obj T')
        (X := (BigFppfOver.toScheme B S hS).obj ((projectiveBundleSituation X' ((modulePullback B S
            hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.fibre T' v))
        ((BigFppfOver.toScheme B S hS).map (sectionFibreLift X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)))
    (hφu : haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
      (zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom u)).map φ) =
      (@asIso _ _ _ _ s hs ≪≫ θ ≪≫ F ≪≫
          (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T u)).symm ≪≫
        ((zariskiReadingFunctor T).mapIso (sectionConormalChartIso X E hE hb σ hσ T u
            hu)).symm).hom)
    (hφv : haveI := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
      (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map φ') =
      (@asIso _ _ _ _ s' hs' ≪≫ θ' ≪≫ F' ≪≫
          (zariskiReadingConormalIso (sectionFibreLift X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)).symm ≪≫
        ((zariskiReadingFunctor T').mapIso (sectionConormalChartIso X' ((modulePullback B S hS
            g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T'
            v hv)).symm).hom)
    (hpt : haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
    haveI := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
    (CategoryTheory.Functor.conormalGlueComparison (Scheme.Modules.pullback ((BigFppfOver.toScheme B
        S hS).map h)) (zariskiReadingFunctor T) (zariskiReadingFunctor T') (Ku :=
        ((modulePullback B S hS (pointHom u)).obj K)) (Kx :=
        ((modulePullback B S hS (pointHom v)).obj ((modulePullback B S hS g).obj K))) (N :=
        ((modulePullback B S hS (yonedaSpaceMap h)).obj ((modulePullback B S hS (pointHom u)).obj
        K))) ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫
        eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g =
        yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
        (modulePullbackCompIso B S hS (pointHom v) g).symm).inv.app K) (zariskiReadingPullbackIso h
        ((modulePullback B S hS (pointHom u)).obj K)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u) K
        hK)).inv) ≫ (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map s ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map θ.hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map F.hom ≫
        (Stacks.Conormal.conormalBaseChangeMap
        (toScheme_map_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v h
        hvh σ hσ σ' hσ' comm)) =
    (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map sB) ≫ s' ≫
    θ'.hom ≫ F'.hom) :
    (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map ((modulePullback B S hS
        g).map φ)) ≫
        (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map (X :=
            (modulePullback B S hS g).obj (conormalModuleOfImmersion B S hS
            (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) (Y :=
              (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X' ((modulePullback B
              S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2
              X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
              (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm)) =
      (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map sB) ≫
        (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map φ') := by
  have := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
  have := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
  exact CategoryTheory.Functor.conormalGlue_baseChange (Scheme.Modules.pullback
      ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
    (zariskiReadingFunctor T') (modulePullback B S hS (yonedaSpaceMap h))
    ((modulePullback B S hS (pointHom u)).map φ)
    ((modulePullback B S hS (pointHom v)).map ((modulePullback B S hS g).map φ))
        (sectionConormalChartIso X E hE hb σ hσ T u hu) ((modulePullback B S hS (pointHom v)).map
        (X := (modulePullback B S hS g).obj (conormalModuleOfImmersion B S hS
        (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) (Y :=
              (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X' ((modulePullback B
              S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2
              X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
              (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm))
              (sectionConormalChartIso X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v hv)
    (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T u)) (zariskiReadingConormalIso
        (sectionFibreLift X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v))
    s hs θ F ((modulePullback B S hS (pointHom v)).map sB) ((modulePullback B S hS (pointHom v)).map
        φ') s' hs'
    θ' F' (CategoryTheory.Functor.conormalGlueComparison (Scheme.Modules.pullback
        ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T) (zariskiReadingFunctor T')
        (Ku := ((modulePullback B S hS (pointHom u)).obj K)) (Kx :=
        ((modulePullback B S hS (pointHom v)).obj ((modulePullback B S hS g).obj K))) (N :=
        ((modulePullback B S hS (yonedaSpaceMap h)).obj ((modulePullback B S hS (pointHom u)).obj
        K))) ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫
        eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g =
        yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
        (modulePullbackCompIso B S hS (pointHom v) g).symm).inv.app K) (zariskiReadingPullbackIso h
        ((modulePullback B S hS (pointHom u)).obj K)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u) K
        hK)).inv) ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom u)).obj K))
    ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫
        eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g =
        yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
        (modulePullbackCompIso B S hS (pointHom v) g).symm).hom.app K) ((zariskiReadingPullbackHom
        h).app ((modulePullback B S hS (pointHom u)).obj (conormalModuleOfImmersion B S hS
        (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))))
    ((zariskiReadingPullbackHom h).app ((conormalAlgebra B S hS (yonedaSpaceMap (sectionFibreLift X
        E hE hb σ hσ T u))).piece 1))
    ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫
        eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g =
        yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
        (modulePullbackCompIso B S hS (pointHom v) g).symm).hom.app (conormalModuleOfImmersion B S
        hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
              (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap h) (yonedaSpaceMap
              (sectionFibreLift X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v))
              (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T u)) (yonedaSpaceMap
              (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh))
              (yonedaSpaceMap_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb'
              u v h hvh σ hσ σ' hσ' comm) 1) (Stacks.Conormal.conormalBaseChangeMap
              (toScheme_map_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u
              v h hvh σ hσ σ' hσ' comm)) hφu hφv
    (CategoryTheory.Functor.conormalGlue_baseChange_hcK (Scheme.Modules.pullback
        ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
      (zariskiReadingFunctor T') (modulePullback B S hS (yonedaSpaceMap h)) (Ku :=
          ((modulePullback B S hS (pointHom u)).obj K)) (Kx :=
          ((modulePullback B S hS (pointHom v)).obj ((modulePullback B S hS g).obj K)))
      ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫
          eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g =
          yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
          (modulePullbackCompIso B S hS (pointHom v) g).symm).inv.app K) ((modulePullbackCompIso B S
          hS (yonedaSpaceMap h) (pointHom u) ≪≫
          eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g =
          yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
          (modulePullbackCompIso B S hS (pointHom v) g).symm).hom.app K) ((modulePullbackCompIso B S
          hS (yonedaSpaceMap h) (pointHom u) ≪≫
          eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g =
          yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
          (modulePullbackCompIso B S hS (pointHom v) g).symm).inv_hom_id_app K)
      (zariskiReadingPullbackIso h ((modulePullback B S hS (pointHom u)).obj K)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u) K
          hK)).inv ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom u)).obj K))
      (zariskiReadingPullbackIso h ((modulePullback B S hS (pointHom u)).obj K)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u) K
          hK)).inv_hom_id) hpt
    (zariskiReadingPullbackHom_naturality_yonedaSpaceMap h ((modulePullback B S hS (pointHom u)).map
        φ))
    (zariskiReadingPullbackHom_naturality_yonedaSpaceMap h (sectionConormalChartIso X E hE hb σ hσ T
        u hu).hom)
    (CategoryTheory.NatTrans.naturality_comp_comp (modulePullback B S hS (pointHom u))
      (modulePullback B S hS (yonedaSpaceMap h)) (modulePullback B S hS g)
      (modulePullback B S hS (pointHom v)) (modulePullbackCompIso B S hS (yonedaSpaceMap h)
          (pointHom u) ≪≫ eqToIso (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh :
          pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
          (modulePullbackCompIso B S hS (pointHom v) g).symm).hom φ)
    (sectionConormalTargetBaseChangeHom_paste_comparison X E hE hb g hb' u v h hvh σ hσ σ' hσ' comm
        hu hv)
    (zariskiReadingConormalIso_naturality_of_comm (sectionFibreLift X E hE hb σ hσ T u)
        (sectionFibreLift X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v) h
        (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh)
        (yonedaSpaceMap_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v h
        hvh σ hσ σ' hσ' comm) (toScheme_map_sectionFibreLift_comp_sectionFibreBaseChangeComparison X
        E hE hb g hb' u v h hvh σ hσ σ' hσ' comm))

end AlgebraicGeometry.Space

end
