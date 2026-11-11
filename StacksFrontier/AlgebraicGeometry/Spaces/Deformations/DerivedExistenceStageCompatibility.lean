module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceLimitProjectionCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfToposHomUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIsoComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryFactorshQuotient
public import StacksFrontier.CategoryTheory.Adjunction.CounitMatesComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback

/-!
# The composition isomorphisms of the tower of Situation 0DIK are conjugate

In Situation [Stacks, Tag 0DIK] the tower `Rjₙ,* Kₙ` of [Stacks, Tag 0DIL] is built from the exact
direct images `Rjₙ,*`, `Riₙ,*` and their composition isomorphism `Riₙ,* ⋙ Rjₙ₊₁,* ≅ Rjₙ,*`, while
the derived pullbacks compose by `smallEtaleDerivedModulePullbackCompIso` (Stacks 0D6D).
This file develops the comparison of the two: the abstract transposition argument recognising a
composition isomorphism of right adjoints as the conjugate of one of left adjoints through the
units, the degreewise mates identities on homotopy categories, and the counit compatibilities of
the exact adjunctions `Ljₙ^* ⊣ Rjₙ,*`.

## Main results

* `AlgebraicGeometry.Space.conjugateEquiv_eq_inv_of_compUnit`: a composition isomorphism `Dpf`
  of right adjoints carrying the composite unit to the unit is the conjugate of the composition
  isomorphism `Dpb` of left adjoints.
* `AlgebraicGeometry.Space.compUnit_comp_mapDerivedCategoryCompNatIso_hom_app`: the unit property
  of `RingTheory.TorIndependence.mapDerivedCategoryCompNatIso` over the homotopy category.
* `AlgebraicGeometry.Space.mapHomotopyCategory_counit_mates`,
  `AlgebraicGeometry.Space.comparison_leftAdjointUniq`: the degreewise mates identities.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.stageAdjunction_counit_fac`: the counit
  of
  `Ljₙ^* ⊣ Rjₙ,*` is induced by the degreewise counit (Stacks 0FPI).

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

section Abstract

/-- Conjugation along adjunctions whose right adjoints are replaced by isomorphic functors. -/
theorem conjugateEquiv_ofNatIsoRight_ofNatIsoRight {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₁' R₂ R₂' : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β₁ : R₁ ≅ R₁') (β₂ : R₂ ≅ R₂') (α : L₂ ⟶ L₁) :
    conjugateEquiv (adj₁.ofNatIsoRight β₁) (adj₂.ofNatIsoRight β₂) α =
      β₁.inv ≫ conjugateEquiv adj₁ adj₂ α ≫ β₂.hom := by
  ext Y
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_unit_app,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Category.assoc,
    Functor.map_comp, Functor.whiskerRight_app]
  rw [← Functor.map_comp_assoc R₂' (α.app _), ← α.naturality, Functor.map_comp_assoc,
    ← β₂.hom.naturality_assoc, adj₂.unit_naturality_assoc]
  rw [β₂.hom.naturality, β₂.hom.naturality_assoc]

/-- The defining property of `rightDerivedIsoOfFactors`: the derivation unit of `RF` followed by
the isomorphism is the inverse of the factorization of `RF'`. -/
theorem rightDerivedIsoOfFactors_hom_app {C D H : Type*} [Category* C] [Category* D]
    [Category* H] (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] {F : C ⥤ H}
    (RF RF' : D ⥤ H) (α : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor α W] (e : L ⋙ RF' ≅ F)
    (X : C) :
    α.app X ≫ (rightDerivedIsoOfFactors L W RF RF' α e).hom.app (L.obj X) = e.inv.app X := by
  have := Functor.isRightDerivedFunctor_of_inverts W RF' e
  simp [rightDerivedIsoOfFactors]

/-- An adjunction compatible with an underived adjunction through a unit `η'` and a comparison
`ε` stays so after its right adjoint is replaced along an isomorphism `β`, for the unit `η'`
followed by `β`. -/
theorem counit_ofNatIsoRight_fac {KX KY DX DY : Type*} [Category* KX] [Category* KY]
    [Category* DX] [Category* DY] {QX : KX ⥤ DX} {QY : KY ⥤ DY} {p : KX ⥤ KY} {pp : KY ⥤ KX}
    (a : pp ⊣ p) {L : DY ⥤ DX} {R' R : DX ⥤ DY} (A : L ⊣ R') (β : R' ≅ R)
    {η' : p ⋙ QY ⟶ QX ⋙ R'} {η : p ⋙ QY ⟶ QX ⋙ R} {ε : QY ⋙ L ⟶ pp ⋙ QX}
    (hβ : ∀ K, η'.app K ≫ β.hom.app (QX.obj K) = η.app K)
    (h : ∀ K, L.map (η'.app K) ≫ A.counit.app (QX.obj K) =
      ε.app (p.obj K) ≫ QX.map (a.counit.app K)) (K : KX) :
    L.map (η.app K) ≫ (A.ofNatIsoRight β).counit.app (QX.obj K) =
      ε.app (p.obj K) ≫ QX.map (a.counit.app K) := by
  rw [← hβ, ← h]
  simp [← Functor.map_comp_assoc]

variable {KX : Type*} [Category* KX] {KY : Type*} [Category* KY]
  {KZ : Type*} [Category* KZ] {DX : Type*} [Category* DX]
  {DY : Type*} [Category* DY] {DZ : Type*} [Category* DZ]
  {QX : KX ⥤ DX} {QY : KY ⥤ DY} {QZ : KZ ⥤ DZ}
  {pf : KX ⥤ KY} {pg : KY ⥤ KZ} {pgf : KX ⥤ KZ}
  {ppf : KY ⥤ KX} {ppg : KZ ⥤ KY} {ppgf : KZ ⥤ KX}
  {Rf : DX ⥤ DY} {Rg : DY ⥤ DZ} {Rgf : DX ⥤ DZ}
  {Lf : DY ⥤ DX} {Lg : DZ ⥤ DY} {Lgf : DZ ⥤ DX}
  (af : ppf ⊣ pf) (ag : ppg ⊣ pg) (agf : ppgf ⊣ pgf)
  (Af : Lf ⊣ Rf) (Ag : Lg ⊣ Rg) (Agf : Lgf ⊣ Rgf)
  {ηf : pf ⋙ QY ⟶ QX ⋙ Rf} {ηg : pg ⋙ QZ ⟶ QY ⋙ Rg} {ηgf : pgf ⋙ QZ ⟶ QX ⋙ Rgf}
  {εf : QY ⋙ Lf ⟶ ppf ⋙ QX} {εg : QZ ⋙ Lg ⟶ ppg ⋙ QY} {εgf : QZ ⋙ Lgf ⟶ ppgf ⋙ QX}
  (c : pf ⋙ pg ≅ pgf) (d : ppg ⋙ ppf ≅ ppgf)
  (Dpb : Lg ⋙ Lf ≅ Lgf) (Dpf : Rf ⋙ Rg ≅ Rgf)

/-- **Conjugate composition isomorphisms, recognized through the units.**  In the setting of
`Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions`, with the
units `ηf`, `ηg` invertible and `QX` a localization: if a composition isomorphism `Dpf` of the
right adjoints carries the composite unit to `ηgf`, then it is the conjugate of the composition
isomorphism `Dpb` of the left adjoints. -/
theorem conjugateEquiv_eq_inv_of_compUnit (W : MorphismProperty KX) [QX.IsLocalization W]
    [IsIso ηf] [IsIso ηg]
    (hf : ∀ K : KX, Lf.map (ηf.app K) ≫ Af.counit.app (QX.obj K) =
      εf.app (pf.obj K) ≫ QX.map (af.counit.app K))
    (hg : ∀ M : KY, Lg.map (ηg.app M) ≫ Ag.counit.app (QY.obj M) =
      εg.app (pg.obj M) ≫ QY.map (ag.counit.app M))
    (hgf : ∀ K : KX, Lgf.map (ηgf.app K) ≫ Agf.counit.app (QX.obj K) =
      εgf.app (pgf.obj K) ≫ QX.map (agf.counit.app K))
    (hDpb : ∀ W : KZ, Dpb.hom.app (QZ.obj W) ≫ εgf.app W =
      Lf.map (εg.app W) ≫ εf.app (ppg.obj W) ≫ QX.map (d.hom.app W))
    (hdeg : ∀ K : KX, ppf.map (ppg.map (c.inv.app K) ≫ ag.counit.app (pf.obj K)) ≫
      af.counit.app K = d.hom.app (pgf.obj K) ≫ agf.counit.app K)
    (hDpf : ∀ K : KX, (QZ.map (c.inv.app K) ≫ ηg.app (pf.obj K) ≫ Rg.map (ηf.app K)) ≫
      Dpf.hom.app (QX.obj K) = ηgf.app K) :
    conjugateEquiv Agf (Ag.comp Af) Dpb.hom = Dpf.inv := by
  let ψ : Rf ⋙ Rg ≅ Rgf := (conjugateIsoEquiv Agf (Ag.comp Af) Dpb).symm
  have hψinv : ψ.inv = conjugateEquiv Agf (Ag.comp Af) Dpb.hom := rfl
  have hψ : ∀ (M : DZ) (N : DX) (φ : Lgf.obj M ⟶ N),
      Ag.homEquiv _ _ (Af.homEquiv _ _ (Dpb.hom.app M ≫ φ)) ≫ ψ.hom.app N =
        Agf.homEquiv M N φ := by
    intro M N φ
    have h := homEquiv_symm_comp_conjugateEquiv_app Agf (Ag.comp Af) Dpb.hom
      (Agf.homEquiv M N φ)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_eq, Adjunction.comp_homEquiv,
      Equiv.trans_apply, ← hψinv] at h
    rw [← h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have key := Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions
    af ag agf Af Ag Agf c d Dpb ψ hf hg hgf hDpb hψ hdeg
  have happ : ∀ K : KX, ψ.hom.app (QX.obj K) = Dpf.hom.app (QX.obj K) := fun K => by
    rw [← cancel_epi (QZ.map (c.inv.app K) ≫ ηg.app (pf.obj K) ≫ Rg.map (ηf.app K)), key K,
      hDpf K]
  have hψD : ψ = Dpf := Iso.ext (Localization.natTrans_ext QX W happ)
  rw [← hψinv, hψD]

end Abstract

section ExactComposition

variable {C D E : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Abelian D] [HasDerivedCategory D]
  [Category* E] [Abelian E] [HasDerivedCategory E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The composite unit of `F.mapDerivedCategory ⋙ G.mapDerivedCategory` (built from the
factorizations `Functor.mapDerivedCategoryFactorsh` and the composition isomorphism on homotopy
categories), followed by `RingTheory.TorIndependence.mapDerivedCategoryCompNatIso`, is the unit
of `H.mapDerivedCategory`. -/
theorem compUnit_comp_mapDerivedCategoryCompNatIso_hom_app (e : F ⋙ G ≅ H)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app K) ≫
        G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app K)) ≫
      (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso F G H e).hom.app
        (DerivedCategory.Qh.obj K) =
      H.mapDerivedCategoryFactorsh.inv.app K := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have h1 := (F.mapDerivedCategoryFactorsh_inv_app_quotient_obj P).symm
  have h2 : G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) = _ :=
    (G.mapDerivedCategoryFactorsh_inv_app_quotient_obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm
  have h3 := (H.mapDerivedCategoryFactorsh_inv_app_quotient_obj P).symm
  have h4 : DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) =
      (DerivedCategory.quotientCompQhIso E).hom.app
          ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app P) ≫
          (DerivedCategory.quotientCompQhIso E).inv.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    Functor.Qh_map_quotient_map _
  have hn := (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso F G H e).hom.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app P)
  have h5 : (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso F G H e).hom.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) =
      G.mapDerivedCategory.map (F.mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso C).hom.app P)) ≫
        (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app P) ≫
          H.mapDerivedCategoryFactors.inv.app P) ≫
        H.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app P) :=
    ((Iso.eq_comp_inv (H.mapDerivedCategory.mapIso
      ((DerivedCategory.quotientCompQhIso C).app P))).2 hn.symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ · ≫ _)
          (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso_hom_app_Q F G H e P)))
  rw [h1, h2, h3, h4, h5]
  have hclean :
      (((DerivedCategory.quotientCompQhIso E).hom.app
                  ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
                DerivedCategory.Q.map
                  ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app P) ≫
                  (DerivedCategory.quotientCompQhIso E).inv.app
                    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
              ((DerivedCategory.quotientCompQhIso E).hom.app
                    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
                  G.mapDerivedCategoryFactors.inv.app
                    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
                    G.mapDerivedCategory.map
                      ((DerivedCategory.quotientCompQhIso D).inv.app
                        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
                G.mapDerivedCategory.map
                  ((DerivedCategory.quotientCompQhIso D).hom.app
                      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
                    F.mapDerivedCategoryFactors.inv.app P ≫
                      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app P))) ≫
            G.mapDerivedCategory.map
                (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app P)) ≫
              (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
                  G.mapDerivedCategoryFactors.hom.app
                    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
                    DerivedCategory.Q.map
                      ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app P) ≫
                      H.mapDerivedCategoryFactors.inv.app P) ≫
                H.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app P) =
          (DerivedCategory.quotientCompQhIso E).hom.app
              ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
            H.mapDerivedCategoryFactors.inv.app P ≫
              H.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app P) := by
    simp
  exact hclean

end ExactComposition



section AbstractHomotopyMates

variable {V W U : Type*} [Category* V] [Preadditive V] [Category* W] [Preadditive W]
  [Category* U] [Preadditive U]

/-- **The mates identity on homotopy categories**, for a family of adjunctions indexed by `ι`
and an equality `k₀ = k₁` of indices along which the composite is transported. -/
theorem mapHomotopyCategory_counit_mates {ι : Sort*} {fs : V ⥤ W} {gs : W ⥤ U} {cs : V ⥤ U}
    {fp : W ⥤ V} {gp : U ⥤ W} {cp : U ⥤ V} {PS : ι → (V ⥤ U)} {PP : ι → (U ⥤ V)}
    [hfs : fs.Additive] [hgs : gs.Additive] [hfp : fp.Additive] [hgp : gp.Additive]
    [hPS : ∀ k, (PS k).Additive] [hPP : ∀ k, (PP k).Additive]
    (af : fp ⊣ fs) (ag : gp ⊣ gs) (ac : cp ⊣ cs) (adj : ∀ k, PP k ⊣ PS k) {k₀ k₁ : ι}
    (w : k₀ = k₁) (pc : cs ≅ fs ⋙ gs) (pm : cp ≅ gp ⋙ fp) (tp : cs ≅ PS k₀) (T : cp ≅ PP k₀)
    (c : fs ⋙ gs ≅ PS k₀) (hc : c = pc.symm ≪≫ tp)
    (k : ∀ A, fp.map (gp.map (pc.hom.app A) ≫ ag.counit.app (fs.obj A)) ≫ af.counit.app A =
      pm.inv.app (cs.obj A) ≫ ac.counit.app A)
    (ht : ∀ A, cp.map (tp.inv.app A) ≫ ac.counit.app A =
      T.hom.app ((PS k₀).obj A) ≫ (adj k₀).counit.app A)
    (K : HomotopyCategory V (ComplexShape.up ℤ)) :
    (fp.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((gp.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso (c ≪≫ eqToIso (congrArg PS w))
              (ComplexShape.up ℤ)).inv.app K) ≫
          (ag.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app
            ((fs.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        (af.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K =
      (Functor.mapHomotopyCategoryCompIso ((pm.symm ≪≫ T) ≪≫ eqToIso (congrArg PP w))
          (ComplexShape.up ℤ)).hom.app
          (((PS k₁).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        ((adj k₁).mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K := by
  subst w
  simp only [eqToIso_refl, Iso.trans_refl]
  obtain ⟨K⟩ := K
  exact congrArg (HomotopyCategory.quotient V (ComplexShape.up ℤ)).map
    (Adjunction.mapHomologicalComplex_counit_mates af ag ac (adj k₀) pc pm tp T c hc k ht K)

/-- **Transporting the 0D6D characterization along an equality of indices.** -/
theorem comparison_eqToIso_transport {DX DY DZ : Type*} [Category* DX] [Category* DY]
    [Category* DZ] {ι : Sort*}
    {QX : HomotopyCategory V (ComplexShape.up ℤ) ⥤ DX}
    {QY : HomotopyCategory W (ComplexShape.up ℤ) ⥤ DY}
    {QZ : HomotopyCategory U (ComplexShape.up ℤ) ⥤ DZ} {Lf : DY ⥤ DX} {Lg : DZ ⥤ DY}
    {LH : ι → (DZ ⥤ DX)} {fp : W ⥤ V} {gp : U ⥤ W} {cp : U ⥤ V} {PP : ι → (U ⥤ V)}
    [hfp : fp.Additive] [hgp : gp.Additive] [hcp : cp.Additive] [hPP : ∀ k, (PP k).Additive]
    (εf : QY ⋙ Lf ⟶ fp.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QX)
    (εg : QZ ⋙ Lg ⟶ gp.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QY)
    (εh : ∀ k, QZ ⋙ LH k ⟶ (PP k).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QX)
    {k₀ k₁ : ι} (w : k₀ = k₁) (Dpb : Lg ⋙ Lf ≅ LH k₀) (pm : gp ⋙ fp ≅ cp) (T : cp ≅ PP k₀)
    (h : ∀ W, Dpb.hom.app (QZ.obj W) ≫ (εh k₀).app W =
      Lf.map (εg.app W) ≫ εf.app ((gp.mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
        QX.map ((Functor.mapHomotopyCategoryCompIso pm (ComplexShape.up ℤ) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso T (ComplexShape.up ℤ)).hom.app W))
    (W : HomotopyCategory U (ComplexShape.up ℤ)) :
    (Dpb ≪≫ eqToIso (congrArg LH w)).hom.app (QZ.obj W) ≫ (εh k₁).app W =
      Lf.map (εg.app W) ≫ εf.app ((gp.mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
        QX.map ((Functor.mapHomotopyCategoryCompIso ((pm ≪≫ T) ≪≫ eqToIso (congrArg PP w))
          (ComplexShape.up ℤ)).hom.app W) := by
  subst w
  simp only [eqToIso_refl, Iso.trans_refl]
  rw [← Stacks.Homology.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso]
  simpa using h W

/-- An isomorphism of left adjoints of the same functor that is compatible with the two counits
is the uniqueness isomorphism. -/
theorem eq_leftAdjointUniq_of_counit {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (δ : F ≅ F')
    (h : ∀ x, δ.hom.app (G.obj x) ≫ adj2.counit.app x = adj1.counit.app x) :
    δ = Adjunction.leftAdjointUniq adj1 adj2 := by
  have key : ∀ α : F ⟶ F', (∀ x, α.app (G.obj x) ≫ adj2.counit.app x = adj1.counit.app x) →
      conjugateEquiv adj2 adj1 α = 𝟙 _ := by
    intro α hα
    ext d
    apply (adj1.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, conjugateEquiv_counit, hα]
    simp
  apply Iso.ext
  apply (conjugateEquiv adj2 adj1).injective
  rw [key _ h, key _ (Adjunction.leftAdjointUniq_hom_app_counit adj1 adj2)]

/-- **The 0D6D characterization, read through the uniqueness isomorphism of left adjoints.**
Combining `comparison_eqToIso_transport` and `mapHomotopyCategory_counit_mates`: the degreewise
composition isomorphism of pullbacks occurring in the characterization of `Dpb` is the
uniqueness isomorphism of the left adjoints of `pgf` attached to the composition isomorphism `c`
of direct images. -/
theorem comparison_leftAdjointUniq {DX DY DZ : Type*} [Category* DX] [Category* DY]
    [Category* DZ] {ι : Sort*}
    {QX : HomotopyCategory V (ComplexShape.up ℤ) ⥤ DX}
    {QY : HomotopyCategory W (ComplexShape.up ℤ) ⥤ DY}
    {QZ : HomotopyCategory U (ComplexShape.up ℤ) ⥤ DZ} {Lf : DY ⥤ DX} {Lg : DZ ⥤ DY}
    {LH : ι → (DZ ⥤ DX)} {fs : V ⥤ W} {gs : W ⥤ U} {cs : V ⥤ U}
    {fp : W ⥤ V} {gp : U ⥤ W} {cp : U ⥤ V} {PS : ι → (V ⥤ U)} {PP : ι → (U ⥤ V)}
    [hfs : fs.Additive] [hgs : gs.Additive] [hfp : fp.Additive] [hgp : gp.Additive]
    [hcp : cp.Additive] [hPS : ∀ k, (PS k).Additive] [hPP : ∀ k, (PP k).Additive]
    (af : fp ⊣ fs) (ag : gp ⊣ gs) (ac : cp ⊣ cs) (adj : ∀ k, PP k ⊣ PS k) {k₀ k₁ : ι}
    (w : k₀ = k₁) (pc : cs ≅ fs ⋙ gs) (pm : cp ≅ gp ⋙ fp) (tp : cs ≅ PS k₀) (T : cp ≅ PP k₀)
    (c : fs ⋙ gs ≅ PS k₀) (hc : c = pc.symm ≪≫ tp)
    (k : ∀ A, fp.map (gp.map (pc.hom.app A) ≫ ag.counit.app (fs.obj A)) ≫ af.counit.app A =
      pm.inv.app (cs.obj A) ≫ ac.counit.app A)
    (ht : ∀ A, cp.map (tp.inv.app A) ≫ ac.counit.app A =
      T.hom.app ((PS k₀).obj A) ≫ (adj k₀).counit.app A)
    (εf : QY ⋙ Lf ⟶ fp.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QX)
    (εg : QZ ⋙ Lg ⟶ gp.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QY)
    (εh : ∀ k, QZ ⋙ LH k ⟶ (PP k).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QX)
    (Dpb : Lg ⋙ Lf ≅ LH k₀)
    (h0 : ∀ W, Dpb.hom.app (QZ.obj W) ≫ (εh k₀).app W =
      Lf.map (εg.app W) ≫ εf.app ((gp.mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
        QX.map ((Functor.mapHomotopyCategoryCompIso pm.symm (ComplexShape.up ℤ) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso T (ComplexShape.up ℤ)).hom.app W))
    (W : HomotopyCategory U (ComplexShape.up ℤ)) :
    (Dpb ≪≫ eqToIso (congrArg LH w)).hom.app (QZ.obj W) ≫ (εh k₁).app W =
      Lf.map (εg.app W) ≫ εf.app ((gp.mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
        QX.map ((Adjunction.leftAdjointUniq
          (((ag.mapHomotopyCategory (ComplexShape.up ℤ)).comp
            (af.mapHomotopyCategory (ComplexShape.up ℤ))).ofNatIsoRight
            (Functor.mapHomotopyCategoryCompIso (c ≪≫ eqToIso (congrArg PS w))
              (ComplexShape.up ℤ)))
          ((adj k₁).mapHomotopyCategory (ComplexShape.up ℤ))).hom.app W) := by
  have hδ := eq_leftAdjointUniq_of_counit
    (((ag.mapHomotopyCategory (ComplexShape.up ℤ)).comp
      (af.mapHomotopyCategory (ComplexShape.up ℤ))).ofNatIsoRight
      (Functor.mapHomotopyCategoryCompIso (c ≪≫ eqToIso (congrArg PS w)) (ComplexShape.up ℤ)))
    ((adj k₁).mapHomotopyCategory (ComplexShape.up ℤ))
    (Functor.mapHomotopyCategoryCompIso ((pm.symm ≪≫ T) ≪≫ eqToIso (congrArg PP w))
      (ComplexShape.up ℤ)) (fun x => by
        rw [← mapHomotopyCategory_counit_mates af ag ac adj w pc pm tp T c hc k ht x]
        simp only [Adjunction.ofNatIsoRight_counit, Adjunction.comp_counit_app,
          NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map,
          Category.assoc, CategoryTheory.Functor.map_comp])
  rw [← hδ]
  exact comparison_eqToIso_transport εf εg εh w Dpb pm.symm T h0 W

end AbstractHomotopyMates


section Mates

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- `AlgebraicGeometry.Space.modulePushforwardCompIso'` is the inverse of the compositor of the
direct images along the composite of the two morphisms of ringed topoi, followed by the
transport `pushforwardModulesCompTransport`. -/
theorem modulePushforwardCompIso'_eq_trans (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforwardCompIso' B S hS f g =
      (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).symm ≪≫
        pushforwardModulesCompTransport B S hS f g := by
  rw [pushforwardModulesCompTransport_eq]
  rfl

end Mates

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian


namespace SeparatedDerivedExistenceSystem

open Stacks.Cohomology.DerivedPushforward (pullbackMapHomotopy pushforwardMapHomotopy
  pullbackAdjPushforwardMapHomotopy)

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- The counit of `Ljₙ^* ⊣ Rjₙ,*` (exact form) is induced by the degreewise counit. -/
theorem stageAdjunction_counit_fac (n : ℕ)
    (K : HomotopyCategory (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) :
    (D.stageDerivedPullback n).map ((D.stagePushforwardFactorsh n).inv.app K) ≫
      (D.stageAdjunction n).counit.app ((D.stageQh n).obj K) =
      (smallEtaleDerivedModulePullbackComparison D.B (limitBase D.system) D.containsLimitBase
          (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).app
          ((pushforwardMapHomotopy.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
              (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))).obj K) ≫
        (D.stageQh n).map ((pullbackAdjPushforwardMapHomotopy.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
            (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
              n))).counit.app K) :=
  counit_ofNatIsoRight_fac _ (D.stageToposDerivedAdjunction n) (D.stageToposDerivedPushforwardIso n)
    (rightDerivedIsoOfFactors_hom_app (D.stageQh n)
      (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) _ _
      (D.stageToposUnit n) (D.stagePushforwardFactorsh n))
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction_counit_fac.{u, u + 1, u, u,
      u + 1, u}
      (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))) K

end SeparatedDerivedExistenceSystem


end AlgebraicGeometry.Space

end
