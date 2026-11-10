module

public import StacksFrontier.Homology.TensorComplex.ExactFunctor.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensoring on the right commutes with mapping cones

The cone-commutation isomorphism `Tot(C(φ) ⊗ G) ≅ C(Tot(φ ⊗ id_G))`, the resulting
isomorphisms of mapping-cone triangles at the cochain level and in `K(C)`, and the consequence
that `Tright G` sends distinguished triangles to distinguished triangles.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
  CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [∀ (K₁ K₂ : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) (ComplexShape.up ℤ)]

/-- **Θ.hom** (the right cone-commutation map). -/
noncomputable def TrightCochain_mappingCone_hom (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    (TrightCochain G).obj (CochainComplex.mappingCone φ) ⟶
      CochainComplex.mappingCone ((TrightCochain G).map φ) := by
  let aCoch : CochainComplex.HomComplex.Cochain
      ((TrightCochain G).obj (CochainComplex.mappingCone φ))
      ((TrightCochain G).obj K) 1 :=
    CochainComplex.HomComplex.Cochain.mk (fun n n' _ =>
      HomologicalComplex.mapBifunctorDesc (fun p q (_ : p + q = n) =>
        ((curriedTensor C).map
            ((CochainComplex.mappingCone.fst φ).1.v p (p+1) (by omega))).app (G.X q) ≫
          HomologicalComplex.ιMapBifunctor K G (curriedTensor C) (ComplexShape.up ℤ) (p+1) q n'
            (by change (p+1) + q = n'; omega)))
  let bCoch : CochainComplex.HomComplex.Cochain
      ((TrightCochain G).obj (CochainComplex.mappingCone φ))
      ((TrightCochain G).obj L) 0 :=
    CochainComplex.HomComplex.Cochain.mk (fun n n' _ =>
      HomologicalComplex.mapBifunctorDesc (fun p q (_ : p + q = n) =>
        ((curriedTensor C).map
            ((CochainComplex.mappingCone.snd φ).v p p (by omega))).app (G.X q) ≫
          HomologicalComplex.ιMapBifunctor L G (curriedTensor C) (ComplexShape.up ℤ) p q n'
            (by change p + q = n'; omega)))
  have ha : CochainComplex.HomComplex.δ 1 2 aCoch = 0 := by
    ext n n' h
    subst h
    rw [CochainComplex.HomComplex.δ_v 1 2 (by omega) aCoch n (n+2) (by omega) (n+1) (n+1)
      (by omega) (by omega)]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpqn : p + q = n := hpq
    rw [Preadditive.comp_add, ← Category.assoc]
    simp only [aCoch, CochainComplex.HomComplex.Cochain.mk_v, HomologicalComplex.ι_mapBifunctorDesc,
       Linear.comp_units_smul, Category.assoc]
    have dK : ((TrightCochain G).obj K).d (n+1) (n+2)
        = HomologicalComplex.mapBifunctor.D₁ K G (curriedTensor C) (ComplexShape.up ℤ) (n+1) (n+2)
          + HomologicalComplex.mapBifunctor.D₂ K G (curriedTensor C) (ComplexShape.up ℤ) (n+1)
            (n+2) :=
      HomologicalComplex.mapBifunctor.d_eq K G (curriedTensor C) (ComplexShape.up ℤ) (n+1) (n+2)
    have dX : ((TrightCochain G).obj (CochainComplex.mappingCone φ)).d n (n+1)
        = HomologicalComplex.mapBifunctor.D₁ (CochainComplex.mappingCone φ) G (curriedTensor C)
            (ComplexShape.up ℤ) n (n+1)
          + HomologicalComplex.mapBifunctor.D₂ (CochainComplex.mappingCone φ) G (curriedTensor C)
            (ComplexShape.up ℤ) n (n+1) :=
      HomologicalComplex.mapBifunctor.d_eq (CochainComplex.mappingCone φ) G (curriedTensor C)
        (ComplexShape.up ℤ) n (n+1)
    rw [dK, dX]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq K G (curriedTensor C) (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel (p+1) (p+1+1) by rw [ComplexShape.up_Rel]) q (n+2)
        (by change (p+1+1)+q=n+2; omega),
      HomologicalComplex.mapBifunctor.d₂_eq K G (curriedTensor C) (ComplexShape.up ℤ) (p+1)
        (show (ComplexShape.up ℤ).Rel q (q+1) by rw [ComplexShape.up_Rel]) (n+2)
        (by change (p+1)+(q+1)=n+2; omega),
      HomologicalComplex.mapBifunctor.d₁_eq (CochainComplex.mappingCone φ) G (curriedTensor C)
        (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p+1) by rw [ComplexShape.up_Rel]) q (n+1)
        (by change (p+1)+q=n+1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq (CochainComplex.mappingCone φ) G (curriedTensor C)
        (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel q (q+1) by rw [ComplexShape.up_Rel]) (n+1)
        (by change p+(q+1)=n+1; omega)]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [show (0 : CochainComplex.HomComplex.Cochain
        ((TrightCochain G).obj (CochainComplex.mappingCone φ))
        ((TrightCochain G).obj K) 2).v n (n+2) (by omega) = 0 from rfl, comp_zero]
    rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p+1, q) = 1 from rfl,
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p+1, q)
        = (p+1:ℤ).negOnePow from rfl,
      show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 1 from rfl,
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q)
        = (p:ℤ).negOnePow from rfl]
    rw [← NatTrans.comp_app_assoc ((curriedTensor C).map ((CochainComplex.mappingCone φ).d p (p+1)))
        ((curriedTensor C).map ((CochainComplex.mappingCone.fst φ).1.v (p+1) (p+1+1) (by omega))),
      ← Functor.map_comp,
      CochainComplex.mappingCone.d_fst_v φ p (p+1) (p+1+1) (by omega) (by omega)]
    have e2 : (2 : ℤ).negOnePow = 1 := by decide
    have ep : (p + 1 : ℤ).negOnePow = - (p:ℤ).negOnePow := by rw [Int.negOnePow_succ]
    rw [e2, ep]
    rw [NatTrans.naturality_assoc
        ((curriedTensor C).map ((CochainComplex.mappingCone.fst φ).1.v p (p+1) (by omega)))
        (G.d q (q+1))]
    simp only [one_smul, Functor.map_neg, Functor.map_comp, Preadditive.neg_comp,
       Category.assoc, Units.neg_smul, smul_add,
      smul_smul, one_mul, NatTrans.app_neg,
      NatTrans.comp_app]
    abel
  have hab : CochainComplex.HomComplex.δ 0 1 bCoch +
      (aCoch).comp (CochainComplex.HomComplex.Cochain.ofHom ((TrightCochain G).map φ)) (by omega)
      = 0 := by
    ext n n' h
    subst h
    rw [CochainComplex.HomComplex.Cochain.add_v,
      CochainComplex.HomComplex.δ_v 0 1 (by omega) bCoch n (n+1) (by omega) n (n+1)
        (by omega) (by omega),
      CochainComplex.HomComplex.Cochain.comp_v aCoch
        (CochainComplex.HomComplex.Cochain.ofHom ((TrightCochain G).map φ)) (by omega) n (n+1) (n+1)
        (by omega) (by omega),
      CochainComplex.HomComplex.Cochain.ofHom_v]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpqn : p + q = n := hpq
    rw [Preadditive.comp_add, Preadditive.comp_add]
    have dL : ((TrightCochain G).obj L).d n (n+1)
        = HomologicalComplex.mapBifunctor.D₁ L G (curriedTensor C) (ComplexShape.up ℤ) n (n+1)
          + HomologicalComplex.mapBifunctor.D₂ L G (curriedTensor C) (ComplexShape.up ℤ) n (n+1) :=
      HomologicalComplex.mapBifunctor.d_eq L G (curriedTensor C) (ComplexShape.up ℤ) n (n+1)
    have dX : ((TrightCochain G).obj (CochainComplex.mappingCone φ)).d n (n+1)
        = HomologicalComplex.mapBifunctor.D₁ (CochainComplex.mappingCone φ) G (curriedTensor C)
            (ComplexShape.up ℤ) n (n+1)
          + HomologicalComplex.mapBifunctor.D₂ (CochainComplex.mappingCone φ) G (curriedTensor C)
            (ComplexShape.up ℤ) n (n+1) :=
      HomologicalComplex.mapBifunctor.d_eq (CochainComplex.mappingCone φ) G (curriedTensor C)
        (ComplexShape.up ℤ) n (n+1)
    have hTφ : ((TrightCochain G).map φ)
        = HomologicalComplex.mapBifunctorMap φ (𝟙 G) (curriedTensor C) (ComplexShape.up ℤ) := rfl
    rw [hTφ]
    rw [← Category.assoc (HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G
        (curriedTensor C) (ComplexShape.up ℤ) p q n hpq),
      ← Category.assoc
        (HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G (curriedTensor C)
          (ComplexShape.up ℤ) p q n hpq)
        _
        ((HomologicalComplex.mapBifunctorMap φ (𝟙 G) (curriedTensor C)
            (ComplexShape.up ℤ)).f (n+1))]
    simp only [bCoch, aCoch, CochainComplex.HomComplex.Cochain.mk_v,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [dL, dX]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc,
      Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
      Linear.comp_units_smul, Preadditive.comp_add]
    rw [HomologicalComplex.mapBifunctor.d₁_eq L G (curriedTensor C) (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p+1) by rw [ComplexShape.up_Rel]) q (n+1)
        (by change (p+1)+q=n+1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq L G (curriedTensor C) (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel q (q+1) by rw [ComplexShape.up_Rel]) (n+1)
        (by change p+(q+1)=n+1; omega),
      HomologicalComplex.mapBifunctor.d₁_eq (CochainComplex.mappingCone φ) G (curriedTensor C)
        (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p+1) by rw [ComplexShape.up_Rel]) q (n+1)
        (by change (p+1)+q=n+1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq (CochainComplex.mappingCone φ) G (curriedTensor C)
        (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel q (q+1) by rw [ComplexShape.up_Rel]) (n+1)
        (by change p+(q+1)=n+1; omega)]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [show (0 : CochainComplex.HomComplex.Cochain
        ((TrightCochain G).obj (CochainComplex.mappingCone φ))
        ((TrightCochain G).obj L) 1).v n (n+1) (by omega) = 0 from rfl, comp_zero]
    rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 1 from rfl,
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q)
        = (p:ℤ).negOnePow from rfl]
    rw [← NatTrans.comp_app_assoc ((curriedTensor C).map ((CochainComplex.mappingCone φ).d p (p+1)))
        ((curriedTensor C).map ((CochainComplex.mappingCone.snd φ).v (p+1) (p+1) (by omega))),
      ← Functor.map_comp,
      CochainComplex.mappingCone.d_snd_v φ p (p+1) (by omega)]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
      Category.id_comp, Functor.map_add, Functor.map_comp, Preadditive.add_comp,
      Category.assoc, one_smul, Int.negOnePow_one, Units.neg_smul, smul_add, smul_smul,
       one_mul, neg_mul,
      NatTrans.comp_app, Functor.map_comp, Preadditive.add_comp,
      NatTrans.app_add]
    rw [NatTrans.naturality_assoc
        ((curriedTensor C).map ((CochainComplex.mappingCone.snd φ).v p p (by omega))) (G.d q (q+1))]
    abel
  exact CochainComplex.mappingCone.lift ((TrightCochain G).map φ)
    (CochainComplex.HomComplex.Cocycle.mk aCoch 2 (by omega) ha) bCoch hab

/-- **Θ.inv** (the backward cone-commutation map, right version). -/
noncomputable def TrightCochain_mappingCone_inv (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    CochainComplex.mappingCone ((TrightCochain G).map φ) ⟶
      (TrightCochain G).obj (CochainComplex.mappingCone φ) := by
  let alphaPrime : CochainComplex.HomComplex.Cochain ((TrightCochain G).obj K)
      ((TrightCochain G).obj (CochainComplex.mappingCone φ)) (-1) :=
    CochainComplex.HomComplex.Cochain.mk (fun n n' _ =>
      HomologicalComplex.mapBifunctorDesc (fun p q (_ : p + q = n) =>
        ((curriedTensor C).map
            ((CochainComplex.mappingCone.inl φ).v p (p-1) (by omega))).app (G.X q) ≫
          HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G (curriedTensor C)
            (ComplexShape.up ℤ) (p-1) q n'
            (by change (p-1) + q = n'; omega)))
  have hTφ : ((TrightCochain G).map φ)
      = HomologicalComplex.mapBifunctorMap φ (𝟙 G) (curriedTensor C) (ComplexShape.up ℤ) := rfl
  have hαβ : CochainComplex.HomComplex.δ (-1) 0 alphaPrime
      = CochainComplex.HomComplex.Cochain.ofHom
          ((TrightCochain G).map φ ≫ (TrightCochain G).map (CochainComplex.mappingCone.inr φ)) := by
    ext n
    rw [CochainComplex.HomComplex.δ_v (-1) 0 (by omega) alphaPrime n n (by omega) (n-1) (n+1)
        (by omega) (by omega),
      CochainComplex.HomComplex.Cochain.ofHom_v]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpqn : p + q = n := hpq
    rw [Preadditive.comp_add, ← Category.assoc]
    simp only [alphaPrime, CochainComplex.HomComplex.Cochain.mk_v,
      HomologicalComplex.ι_mapBifunctorDesc,
       Linear.comp_units_smul, Category.assoc]
    have dK : ((TrightCochain G).obj K).d n (n+1)
        = HomologicalComplex.mapBifunctor.D₁ K G (curriedTensor C) (ComplexShape.up ℤ) n (n+1)
          + HomologicalComplex.mapBifunctor.D₂ K G (curriedTensor C) (ComplexShape.up ℤ) n (n+1) :=
      HomologicalComplex.mapBifunctor.d_eq K G (curriedTensor C) (ComplexShape.up ℤ) n (n+1)
    have dXc : ((TrightCochain G).obj (CochainComplex.mappingCone φ)).d (n-1) n
        = HomologicalComplex.mapBifunctor.D₁ (CochainComplex.mappingCone φ) G (curriedTensor C)
            (ComplexShape.up ℤ) (n-1) n
          + HomologicalComplex.mapBifunctor.D₂ (CochainComplex.mappingCone φ) G (curriedTensor C)
            (ComplexShape.up ℤ) (n-1) n :=
      HomologicalComplex.mapBifunctor.d_eq (CochainComplex.mappingCone φ) G (curriedTensor C)
        (ComplexShape.up ℤ) (n-1) n
    rw [dK, dXc]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq (CochainComplex.mappingCone φ) G (curriedTensor C)
        (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel (p-1) p by rw [ComplexShape.up_Rel]; omega) q n
        (by change p+q=n; omega),
      HomologicalComplex.mapBifunctor.d₂_eq (CochainComplex.mappingCone φ) G (curriedTensor C)
        (ComplexShape.up ℤ) (p-1)
        (show (ComplexShape.up ℤ).Rel q (q+1) by rw [ComplexShape.up_Rel]) n
        (by change (p-1)+(q+1)=n; omega),
      HomologicalComplex.mapBifunctor.d₁_eq K G (curriedTensor C) (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p+1) by rw [ComplexShape.up_Rel]) q (n+1)
        (by change (p+1)+q=n+1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq K G (curriedTensor C) (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel q (q+1) by rw [ComplexShape.up_Rel]) (n+1)
        (by change p+(q+1)=n+1; omega)]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [hTφ]
    simp only [HomologicalComplex.comp_f]
    rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p-1, q) = 1 from rfl,
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p-1, q)
        = (p-1:ℤ).negOnePow from rfl,
      show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 1 from rfl,
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q)
        = (p:ℤ).negOnePow from rfl]
    rw [← NatTrans.comp_app_assoc
        ((curriedTensor C).map ((CochainComplex.mappingCone.inl φ).v p (p-1) (by omega)))
        ((curriedTensor C).map ((CochainComplex.mappingCone φ).d (p-1) p)),
      ← Functor.map_comp,
      CochainComplex.mappingCone.inl_v_d φ p (p-1) (p+1) (by omega) (by omega)]
    have ep : (p - 1 : ℤ).negOnePow = - (p:ℤ).negOnePow := by
      have h := Int.negOnePow_succ (p-1)
      rw [show (p-1+1:ℤ) = p from by omega] at h
      rw [h, neg_neg]
    rw [ep]
    have hTinr : (TrightCochain G).map (CochainComplex.mappingCone.inr φ)
        = HomologicalComplex.mapBifunctorMap (CochainComplex.mappingCone.inr φ) (𝟙 G)
            (curriedTensor C) (ComplexShape.up ℤ) := rfl
    rw [hTinr]
    rw [← Category.assoc (HomologicalComplex.ιMapBifunctor K G (curriedTensor C)
      (ComplexShape.up ℤ) p q n hpq)]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    have hT4 :
        ((curriedTensor C).map (K.d p (p + 1))).app (G.X q) ≫
            ((curriedTensor C).map
                ((CochainComplex.mappingCone.inl φ).v (p + 1) (p + 1 - 1) (by omega))).app
              (G.X q) ≫
              HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G (curriedTensor C)
                (ComplexShape.up ℤ)
                (p + 1 - 1) q n (by change (p+1-1)+q=n; omega)
          = ((curriedTensor C).map (K.d p (p + 1))).app (G.X q) ≫
            ((curriedTensor C).map ((CochainComplex.mappingCone.inl φ).v (p + 1) p (by omega))).app
              (G.X q) ≫
              HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G (curriedTensor C)
                (ComplexShape.up ℤ)
                p q n (by omega) := by
      congr! 4
      all_goals first | omega | (congr 1; (try omega); (try exact proof_irrel_heq _ _))
    simp only [Functor.map_sub, Functor.map_comp, Preadditive.sub_comp,
       Category.assoc,
      one_smul, Units.neg_smul, smul_add, smul_sub, smul_smul,
       NatTrans.comp_app,
      NatTrans.app_sub, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
      Category.id_comp]
    rw [hT4]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    rw [NatTrans.naturality_assoc
        ((curriedTensor C).map ((CochainComplex.mappingCone.inl φ).v p (p-1) (by omega)))
        (G.d q (q+1))]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
      Category.id_comp, Int.negOnePow_zero, one_smul, one_mul]
    abel
  exact CochainComplex.mappingCone.desc ((TrightCochain G).map φ) alphaPrime
    ((TrightCochain G).map (CochainComplex.mappingCone.inr φ)) hαβ

omit [HasZeroObject C] in
/-- The composite `TrightCochain_mappingCone_hom G φ ≫ TrightCochain_mappingCone_inv G φ` is the
identity. -/
theorem TrightCochain_mappingCone_hom_inv (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    TrightCochain_mappingCone_hom G φ ≫ TrightCochain_mappingCone_inv G φ = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  unfold TrightCochain_mappingCone_hom TrightCochain_mappingCone_inv
  rw [CochainComplex.mappingCone.lift_desc_f _ _ _ _ _ _ _ n (n+1) (by omega)]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hpqn : p + q = n := hpq
  simp only [CochainComplex.HomComplex.Cocycle.mk_coe,
    CochainComplex.HomComplex.Cochain.mk_v]
  rw [Preadditive.comp_add]
  -- K-term
  rw [← Category.assoc (HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G
      (curriedTensor C) (ComplexShape.up ℤ) p q n hpq),
    HomologicalComplex.ι_mapBifunctorDesc]
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  -- L-term
  have hTinr : (TrightCochain G).map (CochainComplex.mappingCone.inr φ)
      = HomologicalComplex.mapBifunctorMap (CochainComplex.mappingCone.inr φ) (𝟙 G)
          (curriedTensor C) (ComplexShape.up ℤ) := rfl
  rw [hTinr, ← Category.assoc (HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G
      (curriedTensor C) (ComplexShape.up ℤ) p q n hpq),
    HomologicalComplex.ι_mapBifunctorDesc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    Category.id_comp]
  -- Normalize the K-term index `p+1-1` to `p`.
  have hcancel :
      ((curriedTensor C).map
          ((CochainComplex.mappingCone.inl φ).v (p + 1) (p + 1 - 1) (by omega))).app (G.X q) ≫
          HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G (curriedTensor C)
            (ComplexShape.up ℤ)
            (p + 1 - 1) q n (by change (p+1-1)+q=n; omega)
        = ((curriedTensor C).map ((CochainComplex.mappingCone.inl φ).v (p + 1) p (by omega))).app
            (G.X q) ≫
          HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G (curriedTensor C)
            (ComplexShape.up ℤ)
            p q n (by omega) := by
      congr! 3
      all_goals first | omega | (congr 1; (try omega); (try exact proof_irrel_heq _ _))
  rw [hcancel]
  rw [← NatTrans.comp_app_assoc
      ((curriedTensor C).map ((CochainComplex.mappingCone.fst φ).1.v p (p+1) (by omega)))
      ((curriedTensor C).map ((CochainComplex.mappingCone.inl φ).v (p+1) p (by omega))),
    ← Functor.map_comp]
  rw [← NatTrans.comp_app_assoc
      ((curriedTensor C).map ((CochainComplex.mappingCone.snd φ).v p p (by omega)))
      ((curriedTensor C).map ((CochainComplex.mappingCone.inr φ).f p)),
    ← Functor.map_comp]
  rw [← Preadditive.add_comp, ← NatTrans.app_add, ← Functor.map_add,
    CochainComplex.mappingCone.id_X φ p (p+1) (by omega),
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm

omit [HasZeroObject C] in
/-- The composite `TrightCochain_mappingCone_inv G φ ≫ TrightCochain_mappingCone_hom G φ` is the
identity. -/
theorem TrightCochain_mappingCone_inv_hom (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    TrightCochain_mappingCone_inv G φ ≫ TrightCochain_mappingCone_hom G φ = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  unfold TrightCochain_mappingCone_inv TrightCochain_mappingCone_hom
  apply CochainComplex.mappingCone.ext_from ((TrightCochain G).map φ) (n+1) n (by omega)
  · rw [← Category.assoc, CochainComplex.mappingCone.inl_v_desc_f]
    rw [Category.comp_id]
    simp only [CochainComplex.HomComplex.Cochain.mk_v]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpqn : p + q = n + 1 := hpq
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    rw [CochainComplex.mappingCone.lift_f ((TrightCochain G).map φ) _ _ _ n (n+1) (by omega)]
    simp only [CochainComplex.HomComplex.Cocycle.mk_coe,
      CochainComplex.HomComplex.Cochain.mk_v]
    rw [Preadditive.comp_add]
    -- Expand both aCoch (K via fst) and bCoch (L via snd) summands.
    simp only [Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc_assoc]
    -- merge map(inl φ) ≫ map(snd φ) = 0
    have hsnd : (CochainComplex.mappingCone.inl φ).v p (p-1) (by omega) ≫
        (CochainComplex.mappingCone.snd φ).v (p-1) (p-1) (by omega) = 0 :=
      CochainComplex.mappingCone.inl_v_snd_v φ p (p-1) (by omega)
    rw [← NatTrans.comp_app_assoc
        ((curriedTensor C).map ((CochainComplex.mappingCone.inl φ).v p (p-1) (by omega)))
        ((curriedTensor C).map ((CochainComplex.mappingCone.snd φ).v (p-1) (p-1) (by omega))),
      ← Functor.map_comp, hsnd]
    simp only [CategoryTheory.Functor.map_zero, Limits.zero_app, Limits.zero_comp, add_zero]
    rw [← NatTrans.comp_app_assoc
        ((curriedTensor C).map ((CochainComplex.mappingCone.inl φ).v p (p-1) (by omega)))
        ((curriedTensor C).map ((CochainComplex.mappingCone.fst φ).1.v (p-1) (p-1+1) (by omega))),
      ← Functor.map_comp]
    -- K-term: normalize the inner index p-1+1 → p so inl;fst collapses to 𝟙
    have hcancel :
        ((curriedTensor C).map
              ((CochainComplex.mappingCone.inl φ).v p (p-1) (by omega) ≫
                (CochainComplex.mappingCone.fst φ).1.v (p-1) (p-1+1) (by omega))).app (G.X q) ≫
            HomologicalComplex.ιMapBifunctor K G (curriedTensor C) (ComplexShape.up ℤ) (p-1+1) q
              (n+1) (by change (p-1+1) + q = n+1; omega) ≫
            (CochainComplex.mappingCone.inl ((TrightCochain G).map φ)).v (n+1) n (by omega)
          = ((curriedTensor C).map
              ((CochainComplex.mappingCone.inl φ).v p (p-1) (by omega) ≫
                (CochainComplex.mappingCone.fst φ).1.v (p-1) p (by omega))).app (G.X q) ≫
            HomologicalComplex.ιMapBifunctor K G (curriedTensor C) (ComplexShape.up ℤ) p q (n+1)
              hpq ≫
            (CochainComplex.mappingCone.inl ((TrightCochain G).map φ)).v (n+1) n (by omega) := by
      congr! 4
      all_goals first | omega | (congr 1; (try omega); (try exact proof_irrel_heq _ _))
    rw [hcancel, CochainComplex.mappingCone.inl_v_fst_v φ p (p-1) (by omega),
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  · rw [← Category.assoc, CochainComplex.mappingCone.inr_f_desc_f]
    rw [Category.comp_id]
    have hTinr : (TrightCochain G).map (CochainComplex.mappingCone.inr φ)
        = HomologicalComplex.mapBifunctorMap (CochainComplex.mappingCone.inr φ) (𝟙 G)
            (curriedTensor C) (ComplexShape.up ℤ) := rfl
    rw [hTinr]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpqn : p + q = n := hpq
    rw [← Category.assoc (HomologicalComplex.ιMapBifunctor L G (curriedTensor C)
        (ComplexShape.up ℤ) p q n hpq),
      HomologicalComplex.ι_mapBifunctorMap]
    rw [CochainComplex.mappingCone.lift_f ((TrightCochain G).map φ) _ _ _ n (n+1) (by omega)]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.assoc]
    simp only [CochainComplex.HomComplex.Cocycle.mk_coe,
      CochainComplex.HomComplex.Cochain.mk_v]
    rw [Preadditive.comp_add]
    -- K-term (aCoch via fst): inr φ ≫ fst φ = 0 ;  L-term (bCoch via snd): inr φ ≫ snd φ = 𝟙
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc]
    rw [Preadditive.comp_add]
    rw [Category.assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
      CochainComplex.mappingCone.inr_f_fst_v φ p (p+1) (by omega)]
    simp only [CategoryTheory.Functor.map_zero, Limits.zero_app, Limits.zero_comp, zero_add]
    rw [Category.assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
      CochainComplex.mappingCone.inr_f_snd_v φ p,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- The isomorphism of cochain complexes `Tot(C(φ) ⊗ G) ≅ C(Tot(φ ⊗ id_G))` between the image under
`TrightCochain G` of the mapping cone of `φ` and the mapping cone of `(TrightCochain G).map φ`. -/
noncomputable def TrightCochain_mappingCone_iso (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    (TrightCochain G).obj (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone ((TrightCochain G).map φ) where
  hom := TrightCochain_mappingCone_hom G φ
  inv := TrightCochain_mappingCone_inv G φ
  hom_inv_id := TrightCochain_mappingCone_hom_inv G φ
  inv_hom_id := TrightCochain_mappingCone_inv_hom G φ

omit [HasZeroObject C] in
/-- The image under `TrightCochain G` of the mapping-cone triangle of `φ` is isomorphic to the
mapping-cone triangle of `(TrightCochain G).map φ`. -/
theorem TrightCochain_mapTriangle_triangle_iso (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    letI : (TrightCochain G).CommShift ℤ := by unfold TrightCochain; infer_instance
    Nonempty ((TrightCochain G).mapTriangle.obj (CochainComplex.mappingCone.triangle φ) ≅
      CochainComplex.mappingCone.triangle ((TrightCochain G).map φ)) := by
  let : (TrightCochain G).CommShift ℤ := by unfold TrightCochain; infer_instance
  have hinr : CochainComplex.mappingCone.inr ((TrightCochain G).map φ) ≫
      (TrightCochain_mappingCone_iso G φ).inv
      = (TrightCochain G).map (CochainComplex.mappingCone.inr φ) := by
    simp only [TrightCochain_mappingCone_iso]
    unfold TrightCochain_mappingCone_inv
    rw [CochainComplex.mappingCone.inr_desc]
  refine ⟨CategoryTheory.Pretriangulated.Triangle.isoMk _ _
    (Iso.refl _) (Iso.refl _) (TrightCochain_mappingCone_iso G φ) ?_ ?_ ?_⟩
  · -- `Functor.mapTriangle_obj` no longer rewrites here (the `Iso.refl _` objects make the
    -- rewrite motive ill-typed under the stricter transparency), so we finish via defeq `rfl`.
    simp only [CochainComplex.mappingCone.triangle_mor₁,
      Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [CochainComplex.mappingCone.triangle_mor₂, Iso.refl_hom, Category.id_comp]
    -- expose the (defeq) reduced form of `(mapTriangle.obj _).mor₂`
    change (TrightCochain G).map (CochainComplex.mappingCone.inr φ)
        ≫ (TrightCochain_mappingCone_iso G φ).hom
      = CochainComplex.mappingCone.inr ((TrightCochain G).map φ)
    rw [← hinr, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id]
    -- expose the (defeq) reduced form of `(mapTriangle.obj _).mor₃`
    change (TrightCochain G).map (CochainComplex.mappingCone.triangle φ).mor₃
        ≫ (Functor.commShiftIso (TrightCochain G) 1).hom.app
            (CochainComplex.mappingCone.triangle φ).obj₁
      = (TrightCochain_mappingCone_iso G φ).hom
        ≫ (CochainComplex.mappingCone.triangle ((TrightCochain G).map φ)).mor₃
    rw [← Iso.inv_comp_eq]
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    apply CochainComplex.mappingCone.ext_from ((TrightCochain G).map φ) (n+1) n rfl
    · rw [CochainComplex.mappingCone.inl_v_triangle_mor₃_f]
      rw [← Category.assoc
        ((CochainComplex.mappingCone.inl ((TrightCochain G).map φ)).v (n+1) n (by omega))]
      have hinl : (CochainComplex.mappingCone.inl ((TrightCochain G).map φ)).v (n+1) n (by omega)
            ≫ (TrightCochain_mappingCone_iso G φ).inv.f n
          = HomologicalComplex.mapBifunctorDesc (fun p q (_ : p + q = (n+1)) =>
              ((curriedTensor C).map
                ((CochainComplex.mappingCone.inl φ).v p (p-1) (by omega))).app (G.X q) ≫
              HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G (curriedTensor C)
                (ComplexShape.up ℤ) (p-1) q n
                (by change (p-1) + q = n; omega)) := by
        simp only [TrightCochain_mappingCone_iso]
        unfold TrightCochain_mappingCone_inv
        rw [CochainComplex.mappingCone.inl_v_desc_f]
        rfl
      rw [hinl]
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q hpq
      have hpqn : p + q = n + 1 := hpq
      rw [← Category.assoc, ← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
      have hTδ : ((TrightCochain G).map (CochainComplex.mappingCone.triangle φ).mor₃)
          = HomologicalComplex.mapBifunctorMap (CochainComplex.mappingCone.triangle φ).mor₃ (𝟙 G)
              (curriedTensor C) (ComplexShape.up ℤ) := rfl
      rw [hTδ]
      simp only [Category.assoc]
      rw [← Category.assoc (HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone φ) G
        (curriedTensor C) (ComplexShape.up ℤ) (p-1) q n (by change (p-1)+q=n; omega))]
      simp only [HomologicalComplex.ι_mapBifunctorMap]
      simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.assoc]
      have hcs : ((Functor.commShiftIso (TrightCochain G) 1).hom.app
            (CochainComplex.mappingCone.triangle φ).obj₁)
          = (CochainComplex.mapBifunctorShift₁Iso (CochainComplex.mappingCone.triangle φ).obj₁ G
              (curriedTensor C) 1).hom := rfl
      rw [hcs,
        CochainComplex.ι_mapBifunctorShift₁Iso_hom_f (CochainComplex.mappingCone.triangle φ).obj₁ G
          (curriedTensor C) 1 (p-1) q n
          (by show (p-1) + q = n; omega) p (n+1) (by omega) (by omega)]
      rw [← NatTrans.comp_app_assoc
          ((curriedTensor C).map ((CochainComplex.mappingCone.inl φ).v p (p-1) (by omega)))
          ((curriedTensor C).map ((CochainComplex.mappingCone.triangle φ).mor₃.f (p-1))),
        ← Functor.map_comp,
        CochainComplex.mappingCone.inl_v_triangle_mor₃_f φ p (p-1) (by omega)]
      have hih : (K.shiftFunctorObjXIso 1 (p - 1) p (by omega)).inv ≫
          ((CochainComplex.mappingCone.triangle φ).obj₁.shiftFunctorObjXIso 1 (p - 1) p
            (by omega)).hom
          = 𝟙 _ := Iso.inv_hom_id _
      rw [CategoryTheory.Functor.map_neg, NatTrans.app_neg, Preadditive.neg_comp]
      rw [← NatTrans.comp_app_assoc
          ((curriedTensor C).map (K.shiftFunctorObjXIso 1 (p-1) p (by omega)).inv)
          ((curriedTensor C).map
            ((CochainComplex.mappingCone.triangle φ).obj₁.shiftFunctorObjXIso 1 (p - 1) p
              (by omega)).hom),
        ← Functor.map_comp, hih, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
      rw [Preadditive.comp_neg]
      rfl
    · rw [CochainComplex.mappingCone.inr_f_triangle_mor₃_f]
      rw [← Category.assoc, ← Category.assoc, ← HomologicalComplex.comp_f, hinr]
      rw [← HomologicalComplex.comp_f, ← Functor.map_comp]
      have h0 : (CochainComplex.mappingCone.inr φ) ≫
          (CochainComplex.mappingCone.triangle φ).mor₃ = 0 := by
        apply HomologicalComplex.hom_ext
        intro m
        rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
          CochainComplex.mappingCone.inr_f_triangle_mor₃_f]
      rw [h0, CategoryTheory.Functor.map_zero, HomologicalComplex.zero_f, Limits.zero_comp]

omit [HasZeroObject C] in
/-- The image under `Tright G` of the triangle `triangleh φ` of the homotopy category is isomorphic
to `triangleh ((TrightCochain G).map φ)`. -/
theorem Tright_mapTriangle_triangleh_iso (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    letI := TrightCommShift G
    Nonempty ((Tright G).mapTriangle.obj (CochainComplex.mappingCone.triangleh φ) ≅
      CochainComplex.mappingCone.triangleh ((TrightCochain G).map φ)) := by
  let := TrightCommShift G
  let hcs : (TrightCochain G).CommShift ℤ := by unfold TrightCochain; infer_instance
  obtain ⟨Φ⟩ := TrightCochain_mapTriangle_triangle_iso G φ
  refine ⟨?_⟩
  refine ?_ ≪≫ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.mapIso Φ
  refine (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫ ?_ ≪≫ (Functor.mapTriangleCompIso _ _).app _
  change ((HomotopyCategory.quotient C (ComplexShape.up ℤ)) ⋙ Tright G).mapTriangle.obj _ ≅
       ((TrightCochain G) ⋙ (HomotopyCategory.quotient C (ComplexShape.up ℤ))).mapTriangle.obj _
  let : (TrightCochain G ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ)).CommShift ℤ :=
    inferInstance
  let hlift : (HomotopyCategory.quotient C (ComplexShape.up ℤ)) ⋙ Tright G ≅
      (TrightCochain G) ⋙ (HomotopyCategory.quotient C (ComplexShape.up ℤ)) :=
    CategoryTheory.Quotient.lift.isLift (homotopic C (ComplexShape.up ℤ))
      (TrightCochain G ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (fun _ _ _ _ h => CategoryTheory.Quotient.sound _ (TrightCochain_preservesHomotopyRel G h))
  have : NatTrans.CommShift hlift.hom ℤ :=
    CategoryTheory.Quotient.liftCommShift_compatibility
      (TrightCochain G ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (homotopic C (ComplexShape.up ℤ)) ℤ _
  exact (Functor.mapTriangleIso hlift).app _

/-- **Triangle preservation (right version).**  Mirror of `Tleft_mapTriangle_distinguished`,
using the cone-commutation iso `Tot(C(φ) ⊗ G) ≅ C(Tot(φ ⊗ id_G))` and `mapBifunctorShift₁Iso`
(sign-free on the first variable). -/
@[sga "4 XVII 7.3.3" "special case"]
theorem Tright_mapTriangle_distinguished (G : CochainComplex C ℤ)
    (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ))) :
    letI := TrightCommShift G
    (Tright G).mapTriangle.obj T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) := by
  let := TrightCommShift G
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT
  obtain ⟨ι⟩ := Tright_mapTriangle_triangleh_iso G φ
  exact ⟨_, _, _, ⟨(Tright G).mapTriangle.mapIso e ≪≫ ι⟩⟩
