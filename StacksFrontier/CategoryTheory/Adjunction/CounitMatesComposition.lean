module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Homology.Additive
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# Composing mates of adjunctions, read through the counits

For adjunctions `fp ⊣ fs`, `gp ⊣ gs`, `cp ⊣ cs`, `hp ⊣ hs`, a compositor `pm : cp ≅ gp ⋙ fp` that
is the mate of a compositor `pc : cs ≅ fs ⋙ gs`, and a transport `T : cp ≅ hp` that is the mate of
`tp : cs ≅ hs`, the composite `pm⁻¹ ≪≫ T` is the mate of `pc⁻¹ ≪≫ tp`. These are stated through
the counits, at abstract binders, so that they can be instantiated at concrete adjunctions
without unfolding them.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_hom_app_comp_counit`: the uniqueness
  isomorphism of left adjoints attached to a replacement `tp` of the right adjoint is the mate
  of `tp`.
* `CategoryTheory.Adjunction.counit_mates_trans`: composing mates.
* `CategoryTheory.Adjunction.counit_comp_of_conjugateEquiv`: the counit form of a mates
  identity `conjugateEquiv (ag.comp af) ac pm.hom = pc.inv`.
* `CategoryTheory.Adjunction.mapHomologicalComplex_counit_mates`: composing mates on cochain
  complexes, degreewise.
* `CategoryTheory.Adjunction.mapHomotopyCategory_counit_mates_of_eq`: the same on homotopy
  categories, for homotopy-level adjunctions and composition isomorphisms given together with
  their identifications with the images of the degreewise data.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

section Mates

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- The left adjoint uniqueness isomorphism attached to a replacement `tp` of the right adjoint is
the mate of `tp`, read through the two counits. -/
theorem leftAdjointUniq_ofNatIsoRight_hom_app_comp_counit {F F' : D ⥤ C} {G G' : C ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G') (tp : G ≅ G') (A : C) :
    F.map (tp.inv.app A) ≫ adj₁.counit.app A =
      (adj₁.leftAdjointUniq (adj₂.ofNatIsoRight tp.symm)).hom.app (G'.obj A) ≫
        adj₂.counit.app A := by
  have h := Adjunction.leftAdjointUniq_hom_app_counit adj₁ (adj₂.ofNatIsoRight tp.symm) A
  have hn := (adj₁.leftAdjointUniq (adj₂.ofNatIsoRight tp.symm)).hom.naturality (tp.inv.app A)
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Iso.symm_inv] at h
  rw [← h, ← Category.assoc, hn, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Composing mates.** If the compositor `pm` of left adjoints is the mate of the compositor
`pc` of right adjoints (`k`), and `T` is the mate of `tp` (`ht`), then `pm⁻¹ ≪≫ T` is the mate
of `c = pc⁻¹ ≪≫ tp`, read through the counits. -/
theorem counit_mates_trans {fs : C ⥤ D} {gs : D ⥤ E} {cs hs : C ⥤ E} {fp : D ⥤ C}
    {gp : E ⥤ D} {cp hp : E ⥤ C} (af : fp ⊣ fs) (ag : gp ⊣ gs) (ac : cp ⊣ cs) (ah : hp ⊣ hs)
    (pc : cs ≅ fs ⋙ gs) (pm : cp ≅ gp ⋙ fp) (tp : cs ≅ hs) (T : cp ≅ hp)
    (c : fs ⋙ gs ≅ hs) (hc : c = pc.symm ≪≫ tp)
    (k : ∀ A, fp.map (gp.map (pc.hom.app A) ≫ ag.counit.app (fs.obj A)) ≫ af.counit.app A =
      pm.inv.app (cs.obj A) ≫ ac.counit.app A)
    (ht : ∀ A, cp.map (tp.inv.app A) ≫ ac.counit.app A = T.hom.app (hs.obj A) ≫ ah.counit.app A)
    (A : C) :
    fp.map (gp.map (c.inv.app A) ≫ ag.counit.app (fs.obj A)) ≫ af.counit.app A =
      pm.inv.app (hs.obj A) ≫ T.hom.app (hs.obj A) ≫ ah.counit.app A := by
  subst hc
  have kA := k A
  have hn := pm.inv.naturality (tp.inv.app A)
  simp only [Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at kA
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rw [kA, reassoc_of% hn, ht]

/-- The counit form of a mates identity `conjugateEquiv (ag.comp af) ac pm.hom = pc.inv`. -/
theorem counit_comp_of_conjugateEquiv {fs : C ⥤ D} {gs : D ⥤ E} {cs : C ⥤ E} {fp : D ⥤ C}
    {gp : E ⥤ D} {cp : E ⥤ C} (af : fp ⊣ fs) (ag : gp ⊣ gs) (ac : cp ⊣ cs) (pm : cp ≅ gp ⋙ fp)
    (pc : cs ≅ fs ⋙ gs) (h : conjugateEquiv (ag.comp af) ac pm.hom = pc.inv) (A : C) :
    fp.map (gp.map (pc.hom.app A) ≫ ag.counit.app (fs.obj A)) ≫ af.counit.app A =
      pm.inv.app (cs.obj A) ≫ ac.counit.app A := by
  have he : conjugateIsoEquiv (ag.comp af) ac pm = pc.symm := Iso.ext h
  have h1 : (conjugateEquiv ac (ag.comp af)).symm pc.hom = pm.inv :=
    (Equiv.symm_apply_eq _).2 (congrArg Iso.inv he).symm
  have h2 := conjugateEquiv_counit_symm ac (ag.comp af) pc.hom A
  rw [h1] at h2
  simpa [Adjunction.comp_counit_app] using h2

/-- The counit form of a compositor of left adjoints defined as a uniqueness isomorphism:
if `pm = leftAdjointUniq (ac.ofNatIsoRight pc) (ag.comp af)`, then `pm` is the mate of `pc`. -/
theorem counit_comp_of_eq_leftAdjointUniq {fs : C ⥤ D} {gs : D ⥤ E} {cs : C ⥤ E} {fp : D ⥤ C}
    {gp : E ⥤ D} {cp : E ⥤ C} (af : fp ⊣ fs) (ag : gp ⊣ gs) (ac : cp ⊣ cs) (pm : cp ≅ gp ⋙ fp)
    (pc : cs ≅ fs ⋙ gs) (hpm : pm = (ac.ofNatIsoRight pc).leftAdjointUniq (ag.comp af))
    (A : C) :
    fp.map (gp.map (pc.hom.app A) ≫ ag.counit.app (fs.obj A)) ≫ af.counit.app A =
      pm.inv.app (cs.obj A) ≫ ac.counit.app A := by
  subst hpm
  exact counit_comp_of_conjugateEquiv af ag ac _ pc
    (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom ac pc (ag.comp af)) A

/-- `leftAdjointUniq_ofNatIsoRight_hom_app_comp_counit` for an isomorphism `T` given together with
its identification `hT` with the uniqueness isomorphism. -/
theorem counit_comp_of_eq_leftAdjointUniq_ofNatIsoRight {F F' : D ⥤ C} {G G' : C ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G') (tp : G ≅ G') (T : F ≅ F')
    (hT : T = adj₁.leftAdjointUniq (adj₂.ofNatIsoRight tp.symm)) (A : C) :
    F.map (tp.inv.app A) ≫ adj₁.counit.app A = T.hom.app (G'.obj A) ≫ adj₂.counit.app A := by
  subst hT
  exact leftAdjointUniq_ofNatIsoRight_hom_app_comp_counit adj₁ adj₂ tp A

end Mates

section Complexes

variable {V W U : Type*} [Category* V] [Preadditive V] [Category* W] [Preadditive W]
  [Category* U] [Preadditive U]

/-- `counit_mates_trans` on cochain complexes, degreewise. -/
theorem mapHomologicalComplex_counit_mates {fs : V ⥤ W} {gs : W ⥤ U} {cs hs : V ⥤ U}
    {fp : W ⥤ V} {gp : U ⥤ W} {cp hp : U ⥤ V} [hfs : fs.Additive] [hgs : gs.Additive]
    [hhs : hs.Additive] [hfp : fp.Additive] [hgp : gp.Additive] [hhp : hp.Additive]
    (af : fp ⊣ fs) (ag : gp ⊣ gs) (ac : cp ⊣ cs) (ah : hp ⊣ hs)
    (pc : cs ≅ fs ⋙ gs) (pm : cp ≅ gp ⋙ fp) (tp : cs ≅ hs) (T : cp ≅ hp)
    (c : fs ⋙ gs ≅ hs) (hc : c = pc.symm ≪≫ tp)
    (k : ∀ A, fp.map (gp.map (pc.hom.app A) ≫ ag.counit.app (fs.obj A)) ≫ af.counit.app A =
      pm.inv.app (cs.obj A) ≫ ac.counit.app A)
    (ht : ∀ A, cp.map (tp.inv.app A) ≫ ac.counit.app A = T.hom.app (hs.obj A) ≫ ah.counit.app A)
    (K : CochainComplex V ℤ) :
    (fp.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((gp.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((Functor.mapHomologicalComplexCompIso c (ComplexShape.up ℤ)).inv.app K) ≫
          (NatTrans.mapHomologicalComplex ag.counit (ComplexShape.up ℤ)).app
            ((fs.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (NatTrans.mapHomologicalComplex af.counit (ComplexShape.up ℤ)).app K =
      (Functor.mapHomologicalComplexCompIso (pm.symm ≪≫ T) (ComplexShape.up ℤ)).hom.app
          ((hs.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (NatTrans.mapHomologicalComplex ah.counit (ComplexShape.up ℤ)).app K := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have h := counit_mates_trans af ag ac ah pc pm tp T c hc k ht (K.X n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.symm_hom, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc] at h ⊢
  exact h

end Complexes

section Homotopy

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- **The mates identity on homotopy categories, with all data abstract.** The homotopy-level
adjunctions `AF`, `AG`, `AH` and the composition isomorphism `e'` are given together with their
identifications `hAF`, `hAG`, `hAH`, `he'` with the images of the degreewise data, so that at a
concrete instance the identifications are supplied as hypotheses and no two elaborations of the
same object have to be compared. -/
theorem mapHomotopyCategory_counit_mates_of_eq {V : Type u₁} {W : Type u₂} {U : Type u₃}
    {cV : Category.{v₁} V} {cW : Category.{v₂} W} {cU : Category.{v₃} U}
    {pV : Preadditive V} {pW : Preadditive W} {pU : Preadditive U}
    {fs : V ⥤ W} {gs : W ⥤ U} {cs hs : V ⥤ U} {fp : W ⥤ V} {gp : U ⥤ W} {cp hp : U ⥤ V}
    {hfs : fs.Additive} {hgs : gs.Additive} {hhs : hs.Additive} {hfp : fp.Additive}
    {hgp : gp.Additive} {hcp : cp.Additive} {hhp : hp.Additive}
    {af : fp ⊣ fs} {ag : gp ⊣ gs} {ac : cp ⊣ cs} {ah : hp ⊣ hs}
    {pc : cs ≅ fs ⋙ gs} {pm : cp ≅ gp ⋙ fp} {tp : cs ≅ hs} {T : cp ≅ hp}
    {c : fs ⋙ gs ≅ hs} (hc : c = pc.symm ≪≫ tp)
    (k : ∀ A, fp.map (gp.map (pc.hom.app A) ≫ ag.counit.app (fs.obj A)) ≫ af.counit.app A =
      pm.inv.app (cs.obj A) ≫ ac.counit.app A)
    (ht : ∀ A, cp.map (tp.inv.app A) ≫ ac.counit.app A = T.hom.app (hs.obj A) ≫ ah.counit.app A)
    {AF : fp.mapHomotopyCategory (ComplexShape.up ℤ) ⊣ fs.mapHomotopyCategory (ComplexShape.up ℤ)}
    {AG : gp.mapHomotopyCategory (ComplexShape.up ℤ) ⊣ gs.mapHomotopyCategory (ComplexShape.up ℤ)}
    {AH : hp.mapHomotopyCategory (ComplexShape.up ℤ) ⊣ hs.mapHomotopyCategory (ComplexShape.up ℤ)}
    (hAF : AF = af.mapHomotopyCategory (ComplexShape.up ℤ))
    (hAG : AG = ag.mapHomotopyCategory (ComplexShape.up ℤ))
    (hAH : AH = ah.mapHomotopyCategory (ComplexShape.up ℤ))
    {e' : gp.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ fp.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      hp.mapHomotopyCategory (ComplexShape.up ℤ)}
    (he' : e' = Functor.mapHomotopyCategoryCompIso pm.symm (ComplexShape.up ℤ) ≪≫
      Stacks.Homology.mapHomotopyCategoryIso T (ComplexShape.up ℤ))
    (K : HomotopyCategory V (ComplexShape.up ℤ)) :
    (fp.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((gp.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso c (ComplexShape.up ℤ)).inv.app K) ≫
          AG.counit.app ((fs.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        AF.counit.app K =
      e'.hom.app ((hs.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫ AH.counit.app K := by
  subst hAF hAG hAH he'
  rw [Stacks.Homology.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso]
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  exact (congrArg (HomotopyCategory.quotient V (ComplexShape.up ℤ)).map
    (mapHomologicalComplex_counit_mates af ag ac ah pc pm tp T c hc k ht K)).trans
    ((HomotopyCategory.quotient V (ComplexShape.up ℤ)).map_comp _ _)

end Homotopy

end CategoryTheory.Adjunction
