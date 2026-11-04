module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionQhComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality

/-!
# Left derived functors of functors isomorphic to exact ones, and composition

Let `L₁`, `L₂`, `L₃` be left derived functors of `K(F₁) ⋙ Q_h`, `K(F₂) ⋙ Q_h`, `K(F₃) ⋙ Q_h`,
related by `c : L₁ ⋙ L₂ ≅ L₃` over `u : F₁ ⋙ F₂ ≅ F₃`, and let `eᵢ : Fᵢ ≅ Gᵢ` with `Gᵢ` exact,
compatible with `u` and `v : G₁ ⋙ G₂ ≅ G₃`. Then the identifications `Lᵢ ≅ D(Gᵢ)` of
`Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso` carry `c` to the composition
isomorphism `D(G₁) ⋙ D(G₂) ≅ D(G₃)` induced by `v`.

## Main results

* `Stacks.Homology.mapHomotopyCategory_comp_coherence`: the homotopy-category form.
* `Stacks.Homology.mapHomotopyCategoryCompIso_trans_hom`: composites of comparisons.
* `Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso_comp`: the derived form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Homology

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] in
/-- The homotopy-category form of a coherence of three comparisons `eᵢ : Fᵢ ≅ Gᵢ` with two
composition isomorphisms `u : F₁ ⋙ F₂ ≅ F₃` and `v : G₁ ⋙ G₂ ≅ G₃`. -/
theorem mapHomotopyCategory_comp_coherence (F₁ G₁ : A ⥤ B) (F₂ G₂ : B ⥤ C) (F₃ G₃ : A ⥤ C)
    [F₁.Additive] [G₁.Additive] [F₂.Additive] [G₂.Additive] [F₃.Additive] [G₃.Additive]
    (e₁ : F₁ ≅ G₁) (e₂ : F₂ ≅ G₂) (e₃ : F₃ ≅ G₃) (u : F₁ ⋙ F₂ ≅ F₃) (v : G₁ ⋙ G₂ ≅ G₃)
    (h : u.hom ≫ e₃.hom = Functor.whiskerRight e₁.hom F₂ ≫ Functor.whiskerLeft G₁ e₂.hom ≫ v.hom)
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (G₂.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((mapHomotopyCategoryIso e₁.symm (ComplexShape.up ℤ)).hom.app K) ≫
      (mapHomotopyCategoryIso e₂.symm (ComplexShape.up ℤ)).hom.app
        ((F₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (Functor.mapHomotopyCategoryCompIso u (ComplexShape.up ℤ)).hom.app K =
      (Functor.mapHomotopyCategoryCompIso v (ComplexShape.up ℤ)).hom.app K ≫
        (mapHomotopyCategoryIso e₃.symm (ComplexShape.up ℤ)).hom.app K := by
  have hM : ∀ M : A, G₂.map (e₁.inv.app M) ≫ e₂.inv.app (F₁.obj M) ≫ u.hom.app M =
      v.hom.app M ≫ e₃.inv.app M := by
    intro M
    have hM := NatTrans.congr_app h M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hM
    rw [← cancel_mono (e₃.hom.app M), Category.assoc, Category.assoc, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id, hM]
    have hn := e₂.inv.naturality (e₁.hom.app M)
    rw [← Category.assoc (e₂.inv.app (F₁.obj M)), ← hn, Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  obtain ⟨K⟩ := K
  have key : (G₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e₁.inv _).app K) ≫
      (NatTrans.mapHomologicalComplex e₂.inv _).app ((F₁.mapHomologicalComplex _).obj K) ≫
        (NatTrans.mapHomologicalComplex u.hom _).app K =
      (NatTrans.mapHomologicalComplex v.hom _).app K ≫
        (NatTrans.mapHomologicalComplex e₃.inv _).app K := by
    ext n
    simpa using hM (K.X n)
  have h' := congrArg (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map key
  simp only [Functor.map_comp] at h'
  exact h'

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] in
/-- The comparison of homotopy categories induced by a composite `u ≪≫ w` is the one induced by
`u` followed by the one induced by `w`. -/
theorem mapHomotopyCategoryCompIso_trans_hom (F₁ : A ⥤ B) (F₂ : B ⥤ C) (F₃ F₄ : A ⥤ C)
    [F₁.Additive] [F₂.Additive] [F₃.Additive] [F₄.Additive] (u : F₁ ⋙ F₂ ≅ F₃) (w : F₃ ≅ F₄) :
    (Functor.mapHomotopyCategoryCompIso (u ≪≫ w) (ComplexShape.up ℤ)).hom =
      (Functor.mapHomotopyCategoryCompIso u (ComplexShape.up ℤ)).hom ≫
        (mapHomotopyCategoryIso w (ComplexShape.up ℤ)).hom := by
  ext ⟨K⟩
  exact (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_comp
    ((NatTrans.mapHomologicalComplex u.hom (ComplexShape.up ℤ)).app K)
    ((NatTrans.mapHomologicalComplex w.hom (ComplexShape.up ℤ)).app K)

/-- The comparison `mapDerivedCategoryComparisonOfIso` at `K` is the factorization for `G`
followed by `e⁻¹` on homotopy categories. -/
private theorem mapDerivedCategoryComparisonOfIso_hom_app_eq (F G : A ⥤ B) [F.Additive]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapDerivedCategoryComparisonOfIso F G e).hom.app K =
      G.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryIso e.symm (ComplexShape.up ℤ)).hom.app K) :=
  rfl

/-- **The identification of a left derived functor with the functor an exact functor induces is
compatible with composition**, for left derived functors `L₁`, `L₂`, `L₃` of `K(F₁)`, `K(F₂)`,
`K(F₃)` related by `c : L₁ ⋙ L₂ ≅ L₃` over `u : F₁ ⋙ F₂ ≅ F₃`, and exact `Gᵢ ≅ Fᵢ` related by
`v : G₁ ⋙ G₂ ≅ G₃` compatibly with `u`. -/
theorem leftDerivedIsoMapDerivedCategoryOfIso_comp (F₁ G₁ : A ⥤ B) (F₂ G₂ : B ⥤ C)
    (F₃ G₃ : A ⥤ C)
    [F₁.Additive] [G₁.Additive] [F₂.Additive] [G₂.Additive] [F₃.Additive] [G₃.Additive]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    [PreservesFiniteLimits G₃] [PreservesFiniteColimits G₃]
    (L₁ : DerivedCategory A ⥤ DerivedCategory B)
    (α₁ : DerivedCategory.Qh ⋙ L₁ ⟶ F₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L₁.IsLeftDerivedFunctor α₁ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (L₂ : DerivedCategory B ⥤ DerivedCategory C)
    (α₂ : DerivedCategory.Qh ⋙ L₂ ⟶ F₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L₂.IsLeftDerivedFunctor α₂ (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    (L₃ : DerivedCategory A ⥤ DerivedCategory C)
    (α₃ : DerivedCategory.Qh ⋙ L₃ ⟶ F₃.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L₃.IsLeftDerivedFunctor α₃ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (e₁ : F₁ ≅ G₁) (e₂ : F₂ ≅ G₂) (e₃ : F₃ ≅ G₃) (u : F₁ ⋙ F₂ ≅ F₃) (v : G₁ ⋙ G₂ ≅ G₃)
    (h : u.hom ≫ e₃.hom = Functor.whiskerRight e₁.hom F₂ ≫ Functor.whiskerLeft G₁ e₂.hom ≫ v.hom)
    (c : L₁ ⋙ L₂ ≅ L₃)
    (hc : ∀ K, c.hom.app (DerivedCategory.Qh.obj K) ≫ α₃.app K =
      L₂.map (α₁.app K) ≫ α₂.app ((F₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso u (ComplexShape.up ℤ)).hom.app K)) :
    c.hom ≫ (leftDerivedIsoMapDerivedCategoryOfIso F₃ G₃ L₃ α₃ e₃).hom =
      Functor.whiskerRight (leftDerivedIsoMapDerivedCategoryOfIso F₁ G₁ L₁ α₁ e₁).hom L₂ ≫
        Functor.whiskerLeft G₁.mapDerivedCategory
          (leftDerivedIsoMapDerivedCategoryOfIso F₂ G₂ L₂ α₂ e₂).hom ≫
        (mapDerivedCategoryCompIso G₁ G₂ G₃ v).hom := by
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G₃.mapDerivedCategory
    (mapDerivedCategoryComparisonOfIso F₃ G₃ e₃)
  refine Functor.leftDerived_ext G₃.mapDerivedCategory
    (mapDerivedCategoryComparisonOfIso F₃ G₃ e₃).hom
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  have h₁ := leftDerivedIsoMapDerivedCategoryOfIso_hom_app F₁ G₁ L₁ α₁ e₁ K
  have h₂ := leftDerivedIsoMapDerivedCategoryOfIso_hom_app F₂ G₂ L₂ α₂ e₂
    ((F₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have h₃ := leftDerivedIsoMapDerivedCategoryOfIso_hom_app F₃ G₃ L₃ α₃ e₃ K
  have hcomp := mapDerivedCategoryCompIso_hom_app G₁ G₂ G₃ v K
  have hnat := G₂.mapDerivedCategoryFactorsh.hom.naturality
    ((mapHomotopyCategoryIso e₁.symm (ComplexShape.up ℤ)).hom.app K)
  simp only [Functor.comp_map] at hnat
  have hhot := congrArg DerivedCategory.Qh.map
    (mapHomotopyCategory_comp_coherence F₁ G₁ F₂ G₂ F₃ G₃ e₁ e₂ e₃ u v h K)
  simp only [Functor.map_comp] at hhot
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [Category.assoc, h₃, hc, ← h₁, ← h₂, mapDerivedCategoryComparisonOfIso_hom_app_eq,
    mapDerivedCategoryComparisonOfIso_hom_app_eq, mapDerivedCategoryComparisonOfIso_hom_app_eq]
  simp only [Category.assoc]
  rw [reassoc_of% hcomp, L₂.map_comp, L₂.map_comp]
  simp only [Functor.comp_obj, Category.assoc, NatTrans.naturality_assoc]
  rw [reassoc_of% hnat, hhot]

/-- `Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso_comp` when the composition
isomorphism of the `Fᵢ` is given in two steps `u₁ ≪≫ u₂`. -/
theorem leftDerivedIsoMapDerivedCategoryOfIso_comp_of_trans (F₁ G₁ : A ⥤ B) (F₂ G₂ : B ⥤ C)
    (F₃' F₃ G₃ : A ⥤ C)
    [F₁.Additive] [G₁.Additive] [F₂.Additive] [G₂.Additive] [F₃'.Additive] [F₃.Additive]
    [G₃.Additive]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    [PreservesFiniteLimits G₃] [PreservesFiniteColimits G₃]
    (L₁ : DerivedCategory A ⥤ DerivedCategory B)
    (α₁ : DerivedCategory.Qh ⋙ L₁ ⟶ F₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L₁.IsLeftDerivedFunctor α₁ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (L₂ : DerivedCategory B ⥤ DerivedCategory C)
    (α₂ : DerivedCategory.Qh ⋙ L₂ ⟶ F₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L₂.IsLeftDerivedFunctor α₂ (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    (L₃ : DerivedCategory A ⥤ DerivedCategory C)
    (α₃ : DerivedCategory.Qh ⋙ L₃ ⟶ F₃.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L₃.IsLeftDerivedFunctor α₃ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (e₁ : F₁ ≅ G₁) (e₂ : F₂ ≅ G₂) (e₃ : F₃ ≅ G₃) (u₁ : F₁ ⋙ F₂ ≅ F₃') (u₂ : F₃' ≅ F₃)
    (v : G₁ ⋙ G₂ ≅ G₃)
    (h : (u₁ ≪≫ u₂).hom ≫ e₃.hom =
      Functor.whiskerRight e₁.hom F₂ ≫ Functor.whiskerLeft G₁ e₂.hom ≫ v.hom)
    (c : L₁ ⋙ L₂ ≅ L₃)
    (hc : ∀ K, c.hom.app (DerivedCategory.Qh.obj K) ≫ α₃.app K =
      L₂.map (α₁.app K) ≫ α₂.app ((F₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map (((Functor.mapHomotopyCategoryCompIso u₁ (ComplexShape.up ℤ)) ≪≫
          mapHomotopyCategoryIso u₂ (ComplexShape.up ℤ)).hom.app K)) :
    c.hom ≫ (leftDerivedIsoMapDerivedCategoryOfIso F₃ G₃ L₃ α₃ e₃).hom =
      Functor.whiskerRight (leftDerivedIsoMapDerivedCategoryOfIso F₁ G₁ L₁ α₁ e₁).hom L₂ ≫
        Functor.whiskerLeft G₁.mapDerivedCategory
          (leftDerivedIsoMapDerivedCategoryOfIso F₂ G₂ L₂ α₂ e₂).hom ≫
        (mapDerivedCategoryCompIso G₁ G₂ G₃ v).hom :=
  leftDerivedIsoMapDerivedCategoryOfIso_comp F₁ G₁ F₂ G₂ F₃ G₃ L₁ α₁ L₂ α₂ L₃ α₃ e₁ e₂ e₃
    (u₁ ≪≫ u₂) v h c fun K => (hc K).trans (by
      rw [Iso.trans_hom, ← mapHomotopyCategoryCompIso_trans_hom F₁ F₂ F₃' F₃ u₁ u₂])

/-- `Stacks.Homology.mapDerivedCategoryIsoOfIso` on the image of `Q_h`, followed by the
factorization for `G`: the factorization for `F`, then `e` on homotopy categories. -/
theorem mapDerivedCategoryIsoOfIso_hom_app_comp_factorsh (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapDerivedCategoryIsoOfIso F G e).hom.app (DerivedCategory.Qh.obj X) ≫
      G.mapDerivedCategoryFactorsh.hom.app X =
      F.mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryIso e (ComplexShape.up ℤ)).hom.app X) := by
  have hQh := mapDerivedCategoryIsoOfIso_hom_app F G e X
  rw [mapDerivedCategoryComparisonOfIso_hom_app_eq] at hQh
  have hinv : (mapHomotopyCategoryIso e.symm (ComplexShape.up ℤ)).hom.app X ≫
      (mapHomotopyCategoryIso e (ComplexShape.up ℤ)).hom.app X = 𝟙 _ :=
    Iso.inv_hom_id_app (mapHomotopyCategoryIso e (ComplexShape.up ℤ)) X
  rw [← hQh, Category.assoc, Category.assoc, ← DerivedCategory.Qh.map_comp, hinv,
    DerivedCategory.Qh.map_id]
  simp

/-- `Stacks.Homology.mapDerivedCategoryIsoOfIso` on the image of `Q`: the factorization for `F`,
then `e` applied degreewise, then the factorization for `G` read backwards. -/
theorem mapDerivedCategoryIsoOfIso_hom_app_Q (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (P : CochainComplex A ℤ) :
    (mapDerivedCategoryIsoOfIso F G e).hom.app (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategoryFactors.hom.app P =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) := by
  let X := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P
  let ιP := (DerivedCategory.quotientCompQhIso A).hom.app P
  have hnat : F.mapDerivedCategory.map ιP ≫ (mapDerivedCategoryIsoOfIso F G e).hom.app
      (DerivedCategory.Q.obj P) = (mapDerivedCategoryIsoOfIso F G e).hom.app
        (DerivedCategory.Qh.obj X) ≫ G.mapDerivedCategory.map ιP :=
    (mapDerivedCategoryIsoOfIso F G e).hom.naturality ιP
  have hG : G.mapDerivedCategory.map ιP ≫ G.mapDerivedCategoryFactors.hom.app P =
      G.mapDerivedCategoryFactorsh.hom.app X ≫ (DerivedCategory.quotientCompQhIso B).hom.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    (Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso G P).symm
  have hF : F.mapDerivedCategory.map ιP ≫ F.mapDerivedCategoryFactors.hom.app P =
      F.mapDerivedCategoryFactorsh.hom.app X ≫ (DerivedCategory.quotientCompQhIso B).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    (Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso F P).symm
  have hι : DerivedCategory.Qh.map ((mapHomotopyCategoryIso e (ComplexShape.up ℤ)).hom.app X) ≫
      (DerivedCategory.quotientCompQhIso B).hom.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) :=
    (DerivedCategory.quotientCompQhIso B).hom.naturality
      ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P)
  have hQh' := mapDerivedCategoryIsoOfIso_hom_app_comp_factorsh F G e X
  refine (cancel_epi (F.mapDerivedCategory.map ιP)).1 ?_
  calc F.mapDerivedCategory.map ιP ≫ (mapDerivedCategoryIsoOfIso F G e).hom.app
          (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategoryFactors.hom.app P
      _ = (mapDerivedCategoryIsoOfIso F G e).hom.app (DerivedCategory.Qh.obj X) ≫
          (G.mapDerivedCategory.map ιP ≫ G.mapDerivedCategoryFactors.hom.app P) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ G.mapDerivedCategoryFactors.hom.app P) hnat).trans
            (Category.assoc _ _ _))
      _ = (mapDerivedCategoryIsoOfIso F G e).hom.app (DerivedCategory.Qh.obj X) ≫
          (G.mapDerivedCategoryFactorsh.hom.app X ≫ (DerivedCategory.quotientCompQhIso B).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
        congrArg (fun t => (mapDerivedCategoryIsoOfIso F G e).hom.app
          (DerivedCategory.Qh.obj X) ≫ t) hG
      _ = (F.mapDerivedCategoryFactorsh.hom.app X ≫
          DerivedCategory.Qh.map ((mapHomotopyCategoryIso e (ComplexShape.up ℤ)).hom.app X)) ≫
            (DerivedCategory.quotientCompQhIso B).hom.app
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ (DerivedCategory.quotientCompQhIso B).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) hQh')
      _ = F.mapDerivedCategoryFactorsh.hom.app X ≫
          ((DerivedCategory.quotientCompQhIso B).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P)) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => F.mapDerivedCategoryFactorsh.hom.app X ≫ t) hι)
      _ = F.mapDerivedCategory.map ιP ≫ F.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P)) hF.symm).trans
            (Category.assoc _ _ _))

section CompQ

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- The composition isomorphism induced by `v : G₁ ⋙ G₂ ≅ G₃` is the comparison of the
composite of the induced functors with the functor induced by `G₁ ⋙ G₂`, followed by the change
of functor along `v`. -/
theorem mapDerivedCategoryCompIso_eq_trans (G₁ : A ⥤ B) (G₂ : B ⥤ C) (G₃ : A ⥤ C)
    [G₁.Additive] [G₂.Additive] [G₃.Additive]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    [PreservesFiniteLimits G₃] [PreservesFiniteColimits G₃] (v : G₁ ⋙ G₂ ≅ G₃) :
    mapDerivedCategoryCompIso G₁ G₂ G₃ v =
      Stacks.DerivedFunctor.mapDerivedCategoryCompIso G₁ G₂ ≪≫
        mapDerivedCategoryIsoOfIso (G₁ ⋙ G₂) G₃ v := by
  refine Iso.ext (Functor.leftDerived_ext G₃.mapDerivedCategory
    G₃.mapDerivedCategoryFactorsh.hom (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_)
  ext M
  have h₁ := mapDerivedCategoryCompIso_hom_app G₁ G₂ G₃ v M
  have h₂ := Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Qh G₁ G₂ M
  have h₃ := mapDerivedCategoryIsoOfIso_hom_app_comp_factorsh (G₁ ⋙ G₂) G₃ v M
  have h₄ : (Functor.mapHomotopyCategoryCompIso v (ComplexShape.up ℤ)).hom.app M =
      (mapHomotopyCategoryIso v (ComplexShape.up ℤ)).hom.app M := by
    obtain ⟨K⟩ := M
    rfl
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app, Iso.trans_hom]
  refine h₁.trans ?_
  calc _ = G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app M) ≫
          G₂.mapDerivedCategoryFactorsh.hom.app
            ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
            DerivedCategory.Qh.map ((mapHomotopyCategoryIso v (ComplexShape.up ℤ)).hom.app M) :=
        congrArg (fun t => G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app M) ≫
          G₂.mapDerivedCategoryFactorsh.hom.app
            ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
            DerivedCategory.Qh.map t) h₄
    _ = (G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app M) ≫
          G₂.mapDerivedCategoryFactorsh.hom.app
            ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
            (G₁ ⋙ G₂).mapDerivedCategoryFactorsh.inv.app M) ≫
          ((G₁ ⋙ G₂).mapDerivedCategoryFactorsh.hom.app M ≫
            DerivedCategory.Qh.map ((mapHomotopyCategoryIso v (ComplexShape.up ℤ)).hom.app M)) :=
        ((Category.assoc _ _ _).trans (congrArg (fun t =>
          G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app M) ≫ t)
          ((Category.assoc _ _ _).trans (congrArg (fun t =>
            G₂.mapDerivedCategoryFactorsh.hom.app
              ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫ t)
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun t => t ≫ DerivedCategory.Qh.map
                ((mapHomotopyCategoryIso v (ComplexShape.up ℤ)).hom.app M))
                (Iso.inv_hom_id_app (G₁ ⋙ G₂).mapDerivedCategoryFactorsh M)).trans
                (Category.id_comp _))))))).symm
    _ = _ := by
        rw [← h₂, ← h₃, Category.assoc]

/-- `Stacks.Homology.mapDerivedCategoryCompIso` on the image of `Q`, followed by the factorization
for `G₃`: the factorizations for `G₁` and `G₂`, then `v` applied degreewise. -/
theorem mapDerivedCategoryCompIso_hom_app_Q (G₁ : A ⥤ B) (G₂ : B ⥤ C) (G₃ : A ⥤ C)
    [G₁.Additive] [G₂.Additive] [G₃.Additive]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    [PreservesFiniteLimits G₃] [PreservesFiniteColimits G₃] (v : G₁ ⋙ G₂ ≅ G₃)
    (P : CochainComplex A ℤ) :
    (mapDerivedCategoryCompIso G₁ G₂ G₃ v).hom.app (DerivedCategory.Q.obj P) ≫
        G₃.mapDerivedCategoryFactors.hom.app P =
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
        G₂.mapDerivedCategoryFactors.hom.app
          ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso v (ComplexShape.up ℤ)).hom.app P) := by
  have h₁ := Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Q G₁ G₂ P
  have h₂ := mapDerivedCategoryIsoOfIso_hom_app_Q (G₁ ⋙ G₂) G₃ v P
  rw [mapDerivedCategoryCompIso_eq_trans, Iso.trans_hom, NatTrans.comp_app, Category.assoc, h₂,
    h₁]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

end CompQ

end Stacks.Homology

end
