module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtaleModulesComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomCompCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRestrictionComp
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointCompIsoUniq

/-!
# Composition of étale inverse images on the spaces-étale models, read as restriction

For an étale morphism `j` of algebraic spaces, the inverse image of modules along the morphism of
spaces-étale models `AlgebraicGeometry.Space.spacesEtaleModelHom j` is identified with restriction
along postcomposition with `j` by
`AlgebraicGeometry.Space.spacesEtaleModelPullbackIsoPushforward`, both being left adjoint to the
direct image. This file carries the composition isomorphism of inverse images
`AlgebraicGeometry.Space.spacesEtaleModelPullbackComp` through these identifications: it becomes
the composition isomorphism of the left adjoints `restriction along postcomposition` of the direct
images, induced by `AlgebraicGeometry.Space.spacesEtaleModelPushforwardComp`.

This is the first step towards the compatibility of the identifications of Stacks 03G1 of
étale inverse images on the models with the small étale ones
(`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackOfEtaleTransportIso`) with composition,
which the transport of Stacks 08HB to the models needs.

## Main definitions

* `AlgebraicGeometry.Space.smallModelPostcompComp`: postcomposition on the small models composes.
* `AlgebraicGeometry.Space.smallModelPostcompPushforwardComp`: the composition isomorphism of
  restrictions along postcomposition, as left adjoints of the direct images.
* `SheafOfModules.restrictionSquareIso`: restriction of modules along a square of continuous
  functors filled by an isomorphism.
* `AlgebraicGeometry.Space.smallEtaleModelPostcompComp`,
  `AlgebraicGeometry.Space.smallEtaleModelPushforwardComp`: the same on the small models of the
  small étale sites.

## Main results

* `CategoryTheory.conjugateEquiv_comp_equivalence_toAdjunction`: conjugate composition
  isomorphisms stay conjugate after transport of the adjunctions along equivalences.
* `CategoryTheory.inverse_map_comp_transport_of_comp_coherence`: compatibility with composition
  passes from comparisons of functors to their transports along inverse equivalences.
* `AlgebraicGeometry.Space.conjugateEquiv_smallModelPostcompComp_hom`: on the small models, the
  composition isomorphism of postcompositions is conjugate to the one of base changes.
* `SheafOfModules.leftAdjointCompIso_pushforwardPushforwardAdj_hom_app_val_app`: for restrictions
  along left adjoint functors of sites, the composition isomorphism of the left adjoints induced
  by a composition isomorphism of the right adjoints is, on sections, restriction along the
  conjugate.
* `AlgebraicGeometry.Space.smallModelPostcompPushforwardComp_hom_app_val_app`: its instance for
  postcomposition on the spaces-étale models.
* `AlgebraicGeometry.Space.spacesEtaleModelPullbackComp_trans_pullbackIsoPushforward`.
* `SheafOfModules.restrictionSquareIso_comp`: the restriction comparisons along squares of
  continuous functors are compatible with composition.
* `AlgebraicGeometry.Space.smallEtaleModelPostcompSharp_comp`: the structure maps of restriction
  along postcomposition on the small étale models compose.
* `AlgebraicGeometry.Space.smallEtaleModelModuleRestrictionPostcompIso_comp`: the restriction
  comparisons on the small étale models are compatible with composition.
* `AlgebraicGeometry.Space.smallEtaleModelModulesEquivInversePostcompIso_comp`: so are their
  transports along the Comparison Lemma.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₁ w₂ w₃ t₁ t₂ t₃ u

namespace CategoryTheory

section TransportConjugate

variable {A B C A' B' C' : Type*} [Category* A] [Category* B] [Category* C] [Category* A']
  [Category* B'] [Category* C'] (eA : A ≌ A') (eB : B ≌ B') (eC : C ≌ C')
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : A ⥤ C} {R₃ : C ⥤ A}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)

/-- **Conjugates of composition isomorphisms survive transport along equivalences.** If adjunctions
`L_i ⊣ R_i` are transported along equivalences `A ≌ A'`, `B ≌ B'`, `C ≌ C'` (to
`A'.inverse ⋙ L ⋙ B'.functor ⊣ B'.inverse ⋙ R ⋙ A'.functor`) and `β : L₁ ⋙ L₂ ⟶ L₃` is conjugate
to `γ : R₃ ⟶ R₂ ⋙ R₁`, then the transport of `β` (through the unit of `B ≌ B'`) is conjugate to
the transport of `γ`. -/
theorem conjugateEquiv_comp_equivalence_toAdjunction (β : L₁ ⋙ L₂ ⟶ L₃) (γ : R₃ ⟶ R₂ ⋙ R₁)
    (h : conjugateEquiv a₃ (a₁.comp a₂) β = γ)
    (τ : (eA.inverse ⋙ L₁ ⋙ eB.functor) ⋙ (eB.inverse ⋙ L₂ ⋙ eC.functor) ⟶
      eA.inverse ⋙ L₃ ⋙ eC.functor)
    (hτ : ∀ V, τ.app V = eC.functor.map (L₂.map (eB.unitIso.inv.app (L₁.obj (eA.inverse.obj V))) ≫
      β.app (eA.inverse.obj V)))
    (σ : eC.inverse ⋙ R₃ ⋙ eA.functor ⟶ (eC.inverse ⋙ R₂ ⋙ eB.functor) ⋙
          (eB.inverse ⋙ R₁ ⋙ eA.functor))
    (hσ : ∀ W, σ.app W = eA.functor.map (γ.app (eC.inverse.obj W) ≫
      R₁.map (eB.unitIso.hom.app (R₂.obj (eC.inverse.obj W))))) :
    conjugateEquiv (eA.symm.toAdjunction.comp (a₃.comp eC.toAdjunction))
      ((eA.symm.toAdjunction.comp (a₁.comp eB.toAdjunction)).comp
        (eB.symm.toAdjunction.comp (a₂.comp eC.toAdjunction))) τ = σ := by
  ext W
  rw [conjugateEquiv_apply_app, hσ, ← h, conjugateEquiv_apply_app, hτ]
  simp only [Adjunction.comp_unit_app, Adjunction.comp_counit_app, Equivalence.toAdjunction_unit,
    Equivalence.toAdjunction_counit, Functor.comp_map, Functor.comp_obj, Equivalence.symm_functor,
    Equivalence.symm_inverse, Equivalence.symm_unit, Equivalence.symm_counit, Category.assoc,
    Equivalence.counitInv_app_functor, ← Functor.map_comp]
  congr 1
  have hC : ∀ {Y : C} {W' : C'} (φ : Y ⟶ eC.inverse.obj W'),
      eC.unit.app Y ≫ eC.inverse.map (eC.functor.map φ ≫ eC.counit.app W') = φ := by
    intro Y W' φ
    simp
  have hB : ∀ {Y Y' : B} (φ : Y ⟶ Y'),
      eB.unit.app Y ≫ eB.inverse.map (eB.functor.map φ) = φ ≫ eB.unit.app Y' := by
    intro Y Y' φ
    simp
  simp only [← Functor.map_comp_assoc, Category.assoc]
  rw [hC, hB]
  simp only [Functor.map_comp, Category.assoc]
  set X := R₃.obj (eC.inverse.obj W)
  have key : L₂.map (L₁.map (eA.unit.app X)) ≫ L₂.map (eB.unit.app _) ≫
      L₂.map (eB.unitIso.inv.app _) ≫ β.app _ ≫ L₃.map (eA.unitInv.app X) = β.app X := by
    rw [← Functor.map_comp_assoc L₂ (eB.unit.app _)]
    simp only [Equivalence.unit, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
    have h3 : L₂.map (L₁.map (eA.unitIso.hom.app X)) ≫ β.app ((eA.functor ⋙ eA.inverse).obj X) =
        β.app X ≫ L₃.map (eA.unitIso.hom.app X) := β.naturality _
    rw [← Category.assoc, h3, Category.assoc, ← Functor.map_comp, Equivalence.unitInv,
      Iso.hom_inv_id_app]
    exact (congrArg (β.app X ≫ ·) (L₃.map_id _)).trans (Category.comp_id _)
  rw [← a₁.unit_naturality_assoc]
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  rw [← a₂.unit_naturality_assoc, ← a₂.unit_naturality_assoc]
  congr 1
  rw [← key]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end TransportConjugate

end CategoryTheory

namespace CategoryTheory

section TransportInverse

variable {AX AY AZ BX BY BZ : Type*} [Category* AX] [Category* AY] [Category* AZ] [Category* BX]
  [Category* BY] [Category* BZ] (EX : AX ≌ BX) (EY : AY ≌ BY) (EZ : AZ ≌ BZ)
  {Ff : AY ⥤ AX} {Fg : AZ ⥤ AY} {Ffg : AZ ⥤ AX} {Gf : BY ⥤ BX} {Gg : BZ ⥤ BY} {Gfg : BZ ⥤ BX}

/-- **Composition isomorphisms pass to the transports along inverse equivalences.** Let
`E_X, E_Y, E_Z` be equivalences, `F_•` functors on the sources and `G_•` on the targets with
comparisons `c : F_g ⋙ F_f ⟶ F_{fg}` and `c' : G_g ⋙ G_f ⟶ G_{fg}`, and let isomorphisms
`R_• : F_• ⋙ E.functor ≅ E.functor ⋙ G_•` be compatible with `c` and `c'`. Then the transports
`D_• : G_• ⋙ E.inverse ⟶ E.inverse ⋙ F_•` of the `R_•` (through the units and counits) are
compatible with `c'` and `c`. -/
theorem inverse_map_comp_transport_of_comp_coherence (c : Fg ⋙ Ff ⟶ Ffg) (c' : Gg ⋙ Gf ⟶ Gfg)
    (Rf : Ff ⋙ EX.functor ≅ EY.functor ⋙ Gf) (Rg : Fg ⋙ EY.functor ≅ EZ.functor ⋙ Gg)
    (Rfg : Ffg ⋙ EX.functor ≅ EZ.functor ⋙ Gfg)
    (hR : ∀ P, EX.functor.map (c.app P) ≫ Rfg.hom.app P =
      Rf.hom.app (Fg.obj P) ≫ Gf.map (Rg.hom.app P) ≫ c'.app (EZ.functor.obj P))
    (Df : Gf ⋙ EX.inverse ⟶ EY.inverse ⋙ Ff) (Dg : Gg ⋙ EY.inverse ⟶ EZ.inverse ⋙ Fg)
    (Dfg : Gfg ⋙ EX.inverse ⟶ EZ.inverse ⋙ Ffg)
    (hDf : ∀ N, Df.app N = 𝟙 _ ≫ EX.inverse.map (Gf.map (EY.counitInv.app N)) ≫
      EX.inverse.map (Rf.inv.app (EY.inverse.obj N)) ≫
        EX.unitInv.app (Ff.obj (EY.inverse.obj N)) ≫ 𝟙 _)
    (hDg : ∀ N, Dg.app N = 𝟙 _ ≫ EY.inverse.map (Gg.map (EZ.counitInv.app N)) ≫
      EY.inverse.map (Rg.inv.app (EZ.inverse.obj N)) ≫
        EY.unitInv.app (Fg.obj (EZ.inverse.obj N)) ≫ 𝟙 _)
    (hDfg : ∀ N, Dfg.app N = 𝟙 _ ≫ EX.inverse.map (Gfg.map (EZ.counitInv.app N)) ≫
      EX.inverse.map (Rfg.inv.app (EZ.inverse.obj N)) ≫
        EX.unitInv.app (Ffg.obj (EZ.inverse.obj N)) ≫
        𝟙 _)
    (N : BZ) :
    EX.inverse.map (c'.app N) ≫ Dfg.app N =
      Df.app (Gg.obj N) ≫ Ff.map (Dg.app N) ≫ c.app (EZ.inverse.obj N) := by
  simp only [Category.id_comp, Category.comp_id] at hDf hDg hDfg
  set P := EZ.inverse.obj N
  have key : c'.app (EZ.functor.obj P) ≫ Rfg.inv.app P =
      Gf.map (Rg.inv.app P) ≫ Rf.inv.app (Fg.obj P) ≫ EX.functor.map (c.app P) := by
    calc c'.app (EZ.functor.obj P) ≫ Rfg.inv.app P =
        (Gf.map (Rg.inv.app P) ≫ Rf.inv.app (Fg.obj P)) ≫
          (Rf.hom.app _ ≫ Gf.map (Rg.hom.app P) ≫ c'.app _) ≫ Rfg.inv.app P := by
          simp [← Functor.map_comp_assoc]
      _ = (Gf.map (Rg.inv.app P) ≫ Rf.inv.app (Fg.obj P)) ≫
          (EX.functor.map (c.app P) ≫ Rfg.hom.app P) ≫ Rfg.inv.app P := by rw [hR]
      _ = _ := by simp
  have hc' : c'.app N ≫ Gfg.map (EZ.counitInv.app N) =
      Gf.map (Gg.map (EZ.counitInv.app N)) ≫ c'.app (EZ.functor.obj P) := (c'.naturality _).symm
  rw [hDf, hDg, hDfg, ← Functor.map_comp_assoc, hc', Functor.map_comp_assoc,
    ← Functor.map_comp_assoc EX.inverse (c'.app _), key]
  simp only [Functor.map_comp, Category.assoc]
  have hu := EX.unitInv.naturality (c.app P)
  simp only [Functor.comp_map, Functor.id_map] at hu
  rw [hu]
  let h := EY.inverse.map (Gg.map (EZ.counitInv.app N)) ≫ EY.inverse.map (Rg.inv.app P) ≫
    EY.unitInv.app (Fg.obj P)
  have e1 : EX.unitInv.app (Ff.obj (EY.inverse.obj (Gg.obj N))) ≫ Ff.map h =
      EX.inverse.map (EX.functor.map (Ff.map h)) ≫ EX.unitInv.app (Ff.obj (Fg.obj P)) :=
    (EX.unitInv.naturality (Ff.map h)).symm
  have e2 : Rf.inv.app (EY.inverse.obj (Gg.obj N)) ≫ EX.functor.map (Ff.map h) =
      Gf.map (EY.functor.map h) ≫ Rf.inv.app (Fg.obj P) := (Rf.inv.naturality h).symm
  have e3 : EY.counitInv.app (Gg.obj N) ≫ EY.functor.map h =
      Gg.map (EZ.counitInv.app N) ≫ Rg.inv.app P := by
    simp [h]
  have e4 : Ff.map (EY.inverse.map (Gg.map (EZ.counitInv.app N))) ≫
      Ff.map (EY.inverse.map (Rg.inv.app P)) ≫ Ff.map (EY.unitInv.app (Fg.obj P)) ≫ c.app P =
      Ff.map h ≫ c.app P := by
    simp [h]
  have e2' : EX.inverse.map (Rf.inv.app (EY.inverse.obj (Gg.obj N))) ≫
      EX.inverse.map (EX.functor.map (Ff.map h)) =
      EX.inverse.map (Gf.map (EY.functor.map h)) ≫ EX.inverse.map (Rf.inv.app (Fg.obj P)) := by
    rw [← Functor.map_comp, e2, Functor.map_comp]
  have e3' : EX.inverse.map (Gf.map (EY.counitInv.app (Gg.obj N))) ≫
      EX.inverse.map (Gf.map (EY.functor.map h)) =
      EX.inverse.map (Gf.map (Gg.map (EZ.counitInv.app N))) ≫
        EX.inverse.map (Gf.map (Rg.inv.app P)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, e3, Functor.map_comp, Functor.map_comp]
  rw [e4, reassoc_of% e1, reassoc_of% e2', reassoc_of% e3']
  rfl

end TransportInverse

section ThreeSquares

variable {AX AY AZ MX MY MZ RX RY RZ EX EY EZ : Type*} [Category* AX] [Category* AY]
  [Category* AZ] [Category* MX] [Category* MY] [Category* MZ] [Category* RX] [Category* RY]
  [Category* RZ] [Category* EX] [Category* EY] [Category* EZ]
  {aF : AY ⥤ AX} {aG : AZ ⥤ AY} {aFG : AZ ⥤ AX} {bF : MY ⥤ MX} {bG : MZ ⥤ MY} {bFG : MZ ⥤ MX}
  {cF : RY ⥤ RX} {cG : RZ ⥤ RY} {cFG : RZ ⥤ RX} {dF : EY ⥤ EX} {dG : EZ ⥤ EY} {dFG : EZ ⥤ EX}
  {mX : AX ⥤ MX} {mY : AY ⥤ MY} {mZ : AZ ⥤ MZ} {rX : MX ⥤ RX} {rY : MY ⥤ RY} {rZ : MZ ⥤ RZ}
  {iX : RX ⥤ EX} {iY : RY ⥤ EY} {iZ : RZ ⥤ EZ}

/-- **Compatibility with composition passes to pasted squares.** Let `e_V = m_V ⋙ r_V ⋙ i_V` for
`V = X, Y, Z`, and let `α`, `β`, `γ` be isomorphisms filling the squares of `m`, `r`, `i` with
functors `a`, `b`, `c`, `d` along `f`, `g` and `f ≫ g`, each compatible with comparisons
`c_A, c_B, c_C, c_D` of the composites (`hA`, `hC`, `hD`). Then the pasted squares `Φ`, read
through `e_V = m_V ⋙ r_V ⋙ i_V`, are compatible with `c_A` and `c_D`. -/
theorem comp_coherence_of_three_squares {eX : AX ⥤ EX} {eY : AY ⥤ EY} {eZ : AZ ⥤ EZ}
    (hX : eX = mX ⋙ rX ⋙ iX) (hY : eY = mY ⋙ rY ⋙ iY) (hZ : eZ = mZ ⋙ rZ ⋙ iZ)
    (cA : aG ⋙ aF ⟶ aFG) (cB : bG ⋙ bF ⟶ bFG) (cC : cG ⋙ cF ⟶ cFG) (cD : dG ⋙ dF ⟶ dFG)
    (αF : aF ⋙ mX ≅ mY ⋙ bF) (αG : aG ⋙ mY ≅ mZ ⋙ bG) (αFG : aFG ⋙ mX ≅ mZ ⋙ bFG)
    (βF : bF ⋙ rX ≅ rY ⋙ cF) (βG : bG ⋙ rY ≅ rZ ⋙ cG) (βFG : bFG ⋙ rX ≅ rZ ⋙ cFG)
    (γF : cF ⋙ iX ≅ iY ⋙ dF) (γG : cG ⋙ iY ≅ iZ ⋙ dG) (γFG : cFG ⋙ iX ≅ iZ ⋙ dFG)
    (hA : ∀ M, mX.map (cA.app M) ≫ αFG.hom.app M =
      αF.hom.app (aG.obj M) ≫ bF.map (αG.hom.app M) ≫ cB.app (mZ.obj M))
    (hC : ∀ N, rX.map (cB.app N) ≫ βFG.hom.app N =
      βF.hom.app (bG.obj N) ≫ cF.map (βG.hom.app N) ≫ cC.app (rZ.obj N))
    (hD : ∀ P, iX.map (cC.app P) ≫ γFG.hom.app P =
      γF.hom.app (cG.obj P) ≫ dF.map (γG.hom.app P) ≫ cD.app (iZ.obj P))
    (ΦF : aF ⋙ eX ≅ eY ⋙ dF) (ΦG : aG ⋙ eY ≅ eZ ⋙ dG) (ΦFG : aFG ⋙ eX ≅ eZ ⋙ dFG)
    (hΦF : ΦF = Functor.isoWhiskerLeft aF (eqToIso hX) ≪≫ (Functor.associator _ _ _).symm ≪≫
      (Functor.isoWhiskerRight αF (rX ⋙ iX) ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft mY ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight βF iX ≪≫ Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft rY γF)) ≪≫
      (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso ((Functor.assoc _ _ _).trans hY.symm)) dF)
    (hΦG : ΦG = Functor.isoWhiskerLeft aG (eqToIso hY) ≪≫ (Functor.associator _ _ _).symm ≪≫
      (Functor.isoWhiskerRight αG (rY ⋙ iY) ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft mZ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight βG iY ≪≫ Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft rZ γG)) ≪≫
      (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso ((Functor.assoc _ _ _).trans hZ.symm)) dG)
    (hΦFG : ΦFG = Functor.isoWhiskerLeft aFG (eqToIso hX) ≪≫ (Functor.associator _ _ _).symm ≪≫
      (Functor.isoWhiskerRight αFG (rX ⋙ iX) ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft mZ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight βFG iX ≪≫ Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft rZ γFG)) ≪≫
      (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso ((Functor.assoc _ _ _).trans hZ.symm)) dFG)
    (M : AZ) :
    eX.map (cA.app M) ≫ ΦFG.hom.app M =
      ΦF.hom.app (aG.obj M) ≫ dF.map (ΦG.hom.app M) ≫ cD.app (eZ.obj M) := by
  subst hΦF hΦG hΦFG hX hY hZ
  have h1 := congrArg (fun k => iX.map (rX.map k)) (hA M)
  have h2 := congrArg iX.map (hC (mZ.obj M))
  have h3 := hD (rZ.obj (mZ.obj M))
  have n1 := congrArg iX.map (βF.hom.naturality (αG.hom.app M))
  have n2 := γF.hom.naturality (rY.map (αG.hom.app M) ≫ βG.hom.app (mZ.obj M))
  simp only [Functor.comp_map, Functor.map_comp, Functor.comp_obj] at h1 h2 n1 n2 ⊢
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    eqToIso_refl, Iso.refl_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.id_app, Functor.comp_obj, Functor.comp_map, Functor.map_id, Category.id_comp,
    Category.comp_id, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, h3, reassoc_of% n1, reassoc_of% n2]

end ThreeSquares

section TransportAlongIso

variable {AX AY AZ EX EY EZ : Type*} [Category* AX] [Category* AY] [Category* AZ]
  [Category* EX] [Category* EY] [Category* EZ]
  {lF pF : AY ⥤ AX} {lG pG : AZ ⥤ AY} {lFG pFG : AZ ⥤ AX} {eX : AX ⥤ EX} {eY : AY ⥤ EY}
  {eZ : AZ ⥤ EZ} {dF : EY ⥤ EX} {dG : EZ ⥤ EY} {dFG : EZ ⥤ EX}

/-- **Compatibility with composition passes along isomorphisms of the horizontal functors.** If
`θ_j : l_j ≅ p_j` carry the comparison `c_l` of the composites of the `l` to the comparison `c_p`
of the composites of the `p` (`h`), and the squares `Φ_j : p_j ⋙ e_X ≅ e_Y ⋙ d_j` are compatible
with `c_p` and `c_D`, then so are the squares `θ_j ⋙ Φ_j` with `c_l` and `c_D`. -/
theorem comp_coherence_isoWhiskerRight_trans (θF : lF ≅ pF) (θG : lG ≅ pG) (θFG : lFG ≅ pFG)
    (cl : lG ⋙ lF ⟶ lFG) (cp : pG ⋙ pF ⟶ pFG) (cD : dG ⋙ dF ⟶ dFG)
    (h : ∀ K, cl.app K ≫ θFG.hom.app K =
      lF.map (θG.hom.app K) ≫ θF.hom.app (pG.obj K) ≫ cp.app K)
    (ΦF : pF ⋙ eX ≅ eY ⋙ dF) (ΦG : pG ⋙ eY ≅ eZ ⋙ dG) (ΦFG : pFG ⋙ eX ≅ eZ ⋙ dFG)
    (hΦ : ∀ K, eX.map (cp.app K) ≫ ΦFG.hom.app K =
      ΦF.hom.app (pG.obj K) ≫ dF.map (ΦG.hom.app K) ≫ cD.app (eZ.obj K)) (K : AZ) :
    eX.map (cl.app K) ≫ (Functor.isoWhiskerRight θFG eX ≪≫ ΦFG).hom.app K =
      (Functor.isoWhiskerRight θF eX ≪≫ ΦF).hom.app (lG.obj K) ≫
        dF.map ((Functor.isoWhiskerRight θG eY ≪≫ ΦG).hom.app K) ≫ cD.app (eZ.obj K) := by
  have h1 := congrArg eX.map (h K)
  have n1 := congrArg eX.map (θF.hom.naturality (θG.hom.app K))
  have n2 := ΦF.hom.naturality (θG.hom.app K)
  simp only [Functor.map_comp, Functor.comp_map] at h1 n1 n2
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, hΦ, reassoc_of% n1, reassoc_of% n2]

end TransportAlongIso

end CategoryTheory

namespace CategoryTheory

/-- The image under `e'.inverse ∘ e'.functor ∘ G` of the unit of `e` at `A`, followed by the
inverse units, is the inverse unit of `e'` at `G A`. -/
theorem Equivalence.inverse_map_functor_map_unit_comp {C D C' D' : Type*} [Category* C]
    [Category* D] [Category* C'] [Category* D'] (e : C ≌ D) (G : C ⥤ C') (e' : C' ≌ D') (A : C) :
    e'.inverse.map (e'.functor.map (G.map (e.unitIso.hom.app A))) ≫
        e'.unitIso.inv.app (G.obj (e.inverse.obj (e.functor.obj A))) ≫
          G.map (e.unitIso.inv.app A) =
      e'.unitIso.inv.app (G.obj A) := by
  have hn := e'.unitIso.inv.naturality (G.map (e.unitIso.hom.app A))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [reassoc_of% hn, ← Functor.map_comp, Iso.hom_inv_id_app]
  exact (congrArg (_ ≫ ·) (G.map_id _)).trans (Category.comp_id _)

end CategoryTheory

namespace SheafOfModules

section LeftAdjointComp

variable {A : Type t₁} [Category.{w₁} A] {B : Type t₂} [Category.{w₂} B] {C : Type t₃}
    [Category.{w₃} C]
  {JA : GrothendieckTopology A} {JB : GrothendieckTopology B} {JC : GrothendieckTopology C}
  {RA : Sheaf JA RingCat.{u}} {RB : Sheaf JB RingCat.{u}} {RC : Sheaf JC RingCat.{u}}
  {u₁ : A ⥤ B} {v₁ : B ⥤ A} {u₂ : B ⥤ C} {v₂ : C ⥤ B} {u₃ : A ⥤ C} {v₃ : C ⥤ A}
  [u₁.IsContinuous JA JB] [v₁.IsContinuous JB JA] [u₂.IsContinuous JB JC] [v₂.IsContinuous JC JB]
  [u₃.IsContinuous JA JC] [v₃.IsContinuous JC JA]
  (adj₁ : u₁ ⊣ v₁) (adj₂ : u₂ ⊣ v₂) (adj₃ : u₃ ⊣ v₃)
  (φ₁ : RA ⟶ (u₁.sheafPushforwardContinuous RingCat.{u} JA JB).obj RB)
  (φ₂ : RB ⟶ (u₂.sheafPushforwardContinuous RingCat.{u} JB JC).obj RC)
  (φ₃ : RA ⟶ (u₃.sheafPushforwardContinuous RingCat.{u} JA JC).obj RC)
  (ψ₁ : RB ⟶ (v₁.sheafPushforwardContinuous RingCat.{u} JB JA).obj RA)
  (ψ₂ : RC ⟶ (v₂.sheafPushforwardContinuous RingCat.{u} JC JB).obj RB)
  (ψ₃ : RC ⟶ (v₃.sheafPushforwardContinuous RingCat.{u} JC JA).obj RA)
  (H₁ : Functor.whiskerRight (NatTrans.op adj₁.counit) RB.obj = ψ₁.hom ≫ v₁.op.whiskerLeft φ₁.hom)
  (H₁' : φ₁.hom ≫ u₁.op.whiskerLeft ψ₁.hom ≫
        Functor.whiskerRight (NatTrans.op adj₁.unit) RA.obj = 𝟙 RA.obj)
  (H₂ : Functor.whiskerRight (NatTrans.op adj₂.counit) RC.obj = ψ₂.hom ≫ v₂.op.whiskerLeft φ₂.hom)
  (H₂' : φ₂.hom ≫ u₂.op.whiskerLeft ψ₂.hom ≫
        Functor.whiskerRight (NatTrans.op adj₂.unit) RB.obj = 𝟙 RB.obj)
  (H₃ : Functor.whiskerRight (NatTrans.op adj₃.counit) RC.obj = ψ₃.hom ≫ v₃.op.whiskerLeft φ₃.hom)
  (H₃' : φ₃.hom ≫ u₃.op.whiskerLeft ψ₃.hom ≫
        Functor.whiskerRight (NatTrans.op adj₃.unit) RA.obj = 𝟙 RA.obj)

/-- **Composition isomorphisms of restrictions along left adjoints of functors of sites, on
sections.** For adjunctions `u_i ⊣ v_i` of continuous functors of sites inducing adjunctions of
restrictions of sheaves of modules (`SheafOfModules.pushforwardPushforwardAdj`), if an
isomorphism `e` of the composite of the restrictions along the right adjoints with the
restriction along `v₃` is, on sections, restriction along `η : v₂ ⋙ v₁ ⟶ v₃`, then the induced
composition isomorphism of the restrictions along the left adjoints is, on sections, restriction
along the conjugate of `η`. -/
theorem leftAdjointCompIso_pushforwardPushforwardAdj_hom_app_val_app
    (e : SheafOfModules.pushforward.{u} ψ₁ ⋙ SheafOfModules.pushforward.{u} ψ₂ ≅
      SheafOfModules.pushforward.{u} ψ₃)
    (η : v₂ ⋙ v₁ ⟶ v₃)
    (he : ∀ (M : SheafOfModules.{u} RA) U x, (e.inv.app M).val.app U x =
          M.val.map (η.app U.unop).op x)
    (M : SheafOfModules.{u} RC) (V : Aᵒᵖ) (x) :
    ((Adjunction.leftAdjointCompIso (SheafOfModules.pushforwardPushforwardAdj adj₂ φ₂ ψ₂ H₂ H₂')
      (SheafOfModules.pushforwardPushforwardAdj adj₁ φ₁ ψ₁ H₁ H₁')
      (SheafOfModules.pushforwardPushforwardAdj adj₃ φ₃ ψ₃ H₃ H₃') e).hom.app M).val.app V x =
      M.val.map (((conjugateEquiv (adj₁.comp adj₂) adj₃).symm η).app V.unop).op x := by
  rw [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans_app,
    conjugateEquiv_symm_apply_app]
  let N := (SheafOfModules.pushforward φ₃).obj M
  let W := u₂.obj (u₁.obj V.unop)
  let P := M.val.presheaf
  have h := he N (op W) (P.map (adj₃.counit.app W).op x)
  change (P.map (u₃.map (v₁.map (adj₂.unit.app (u₁.obj V.unop)))).op ≫
    P.map (u₃.map (adj₁.unit.app V.unop)).op) ((e.inv.app N).val.app (op W)
      (P.map (adj₃.counit.app W).op x)) = _
  rw [h]
  change (P.map (adj₃.counit.app W).op ≫ P.map (u₃.map (η.app W)).op ≫
    P.map (u₃.map (v₁.map (adj₂.unit.app (u₁.obj V.unop)))).op ≫
    P.map (u₃.map (adj₁.unit.app V.unop)).op) x = _
  change _ = (P.map ((u₃.map ((adj₁.comp adj₂).unit.app V.unop) ≫ u₃.map (η.app W) ≫
    adj₃.counit.app W).op)) x
  rw [Adjunction.comp_unit_app]
  have key : u₃.map (adj₁.unit.app V.unop ≫ v₁.map (adj₂.unit.app (u₁.obj V.unop)) ≫ η.app W) ≫
      adj₃.counit.app W = u₃.map (adj₁.unit.app V.unop ≫ v₁.map (adj₂.unit.app (u₁.obj V.unop))) ≫
      u₃.map (η.app W) ≫ adj₃.counit.app W := by
    simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp, ← op_comp, Category.assoc]
  rw [key]

end LeftAdjointComp

end SheafOfModules

namespace SheafOfModules

section RestrictionSquare

variable {CX CY DX DY : Type*} [Category* CX] [Category* CY] [Category* DX] [Category* DY]
  {JCX : GrothendieckTopology CX} {JCY : GrothendieckTopology CY}
  {JDX : GrothendieckTopology DX} {JDY : GrothendieckTopology DY}
  {OX : Sheaf JDX RingCat.{u}} {OY : Sheaf JDY RingCat.{u}}
  {eX : CX ⥤ DX} {eY : CY ⥤ DY} [eX.IsContinuous JCX JDX] [eY.IsContinuous JCY JDY]
  {p : DX ⥤ DY} {q : CX ⥤ CY} [p.IsContinuous JDX JDY] [q.IsContinuous JCX JCY]
  [(eX ⋙ p).IsContinuous JCX JDY] [(q ⋙ eY).IsContinuous JCX JDY]

/-- **Restriction of modules along a square of continuous functors.** An isomorphism
`α : e_X ⋙ p ≅ q ⋙ e_Y` filling a square of continuous functors, with structure maps `ι_X`, `ι_Y`
(along `e_X`, `e_Y`), `ρ` (along `p`) and `σ` (along `q`) of sheaves of rings which are compatible
(`h`), identifies restriction along `p` then `e_X` with restriction along `e_Y` then `q`. -/
def restrictionSquareIso {RX : Sheaf JCX RingCat.{u}} {RY : Sheaf JCY RingCat.{u}}
    (ιX : RX ⟶ (eX.sheafPushforwardContinuous RingCat.{u} JCX JDX).obj OX)
    (ιY : RY ⟶ (eY.sheafPushforwardContinuous RingCat.{u} JCY JDY).obj OY)
    (ρ : OX ⟶ (p.sheafPushforwardContinuous RingCat.{u} JDX JDY).obj OY)
    (σ : RX ⟶ (q.sheafPushforwardContinuous RingCat.{u} JCX JCY).obj RY)
    (α : eX ⋙ p ≅ q ⋙ eY)
    (h : (ιX ≫ (eX.sheafPushforwardContinuous RingCat.{u} JCX JDX).map ρ) ≫
      (Functor.sheafPushforwardContinuousNatTrans α.symm.hom RingCat.{u} JCX JDY).app OY =
      σ ≫ (q.sheafPushforwardContinuous RingCat.{u} JCX JCY).map ιY) :
    pushforward.{u} ρ ⋙ pushforward.{u} ιX ≅ pushforward.{u} ιY ⋙ pushforward.{u} σ :=
  pushforwardComp (F := eX) (G := p) ιX ρ ≪≫ pushforwardCongr₂ _ α.symm h ≪≫
    (pushforwardComp (F := q) (G := eY) σ ιY).symm

end RestrictionSquare

section RestrictionSquareComp

variable {CX CY CZ DX DY DZ : Type*} [Category* CX] [Category* CY] [Category* CZ]
  [Category* DX] [Category* DY] [Category* DZ]
  {JCX : GrothendieckTopology CX} {JCY : GrothendieckTopology CY} {JCZ : GrothendieckTopology CZ}
  {JDX : GrothendieckTopology DX} {JDY : GrothendieckTopology DY} {JDZ : GrothendieckTopology DZ}
  {OX : Sheaf JDX RingCat.{u}} {OY : Sheaf JDY RingCat.{u}} {OZ : Sheaf JDZ RingCat.{u}}
  {eX : CX ⥤ DX} {eY : CY ⥤ DY} {eZ : CZ ⥤ DZ} [eX.IsContinuous JCX JDX] [eY.IsContinuous JCY JDY]
  [eZ.IsContinuous JCZ JDZ]
  {pf : DX ⥤ DY} {pg : DY ⥤ DZ} [pf.IsContinuous JDX JDY] [pg.IsContinuous JDY JDZ]
  {qf : CX ⥤ CY} {qg : CY ⥤ CZ} {qfg : CX ⥤ CZ} [qf.IsContinuous JCX JCY]
  [qg.IsContinuous JCY JCZ] [qfg.IsContinuous JCX JCZ]

/-- **Restriction comparisons along squares of continuous functors compose.** Let
`α_f : e_X ⋙ p_f ≅ q_f ⋙ e_Y`, `α_g`, `α_{fg} : e_X ⋙ p_{fg} ≅ q_{fg} ⋙ e_Z` be isomorphisms
filling squares of continuous functors, `c : p_g^* ⋙ p_f^* ≅ p_{fg}^*` a comparison of restrictions
which on sections is restriction along `γ : p_{fg} U ⟶ p_g (p_f U)` (`hc`), and
`β : q_f ⋙ q_g ≅ q_{fg}`, compatible on objects (`hm`). Then the comparisons
`SheafOfModules.restrictionSquareIso` they induce are compatible with `c` and with the composition
isomorphism of restrictions along `q_f, q_g` (through `β`). -/
theorem restrictionSquareIso_comp {pfg : DX ⥤ DZ} [pfg.IsContinuous JDX JDZ]
    {RX : Sheaf JCX RingCat.{u}} {RY : Sheaf JCY RingCat.{u}} {RZ : Sheaf JCZ RingCat.{u}}
    (ιX : RX ⟶ (eX.sheafPushforwardContinuous RingCat.{u} JCX JDX).obj OX)
    (ιY : RY ⟶ (eY.sheafPushforwardContinuous RingCat.{u} JCY JDY).obj OY)
    (ιZ : RZ ⟶ (eZ.sheafPushforwardContinuous RingCat.{u} JCZ JDZ).obj OZ)
    (ρf : OX ⟶ (pf.sheafPushforwardContinuous RingCat.{u} JDX JDY).obj OY)
    (ρg : OY ⟶ (pg.sheafPushforwardContinuous RingCat.{u} JDY JDZ).obj OZ)
    (ρfg : OX ⟶ (pfg.sheafPushforwardContinuous RingCat.{u} JDX JDZ).obj OZ)
    (c : pushforward.{u} ρg ⋙ pushforward.{u} ρf ≅ pushforward.{u} ρfg)
    (γ : ∀ U, pfg.obj U ⟶ pg.obj (pf.obj U))
    (hc : ∀ (M : SheafOfModules.{u} OZ) (U : DXᵒᵖ) (x), (c.hom.app M).val.app U x =
      M.val.presheaf.map (γ U.unop).op x)
    (σf : RX ⟶ (qf.sheafPushforwardContinuous RingCat.{u} JCX JCY).obj RY)
    (σg : RY ⟶ (qg.sheafPushforwardContinuous RingCat.{u} JCY JCZ).obj RZ)
    (σfg : RX ⟶ (qfg.sheafPushforwardContinuous RingCat.{u} JCX JCZ).obj RZ)
    (αf : eX ⋙ pf ≅ qf ⋙ eY) (αg : eY ⋙ pg ≅ qg ⋙ eZ) (αfg : eX ⋙ pfg ≅ qfg ⋙ eZ)
    (β : qf ⋙ qg ≅ qfg)
    [(eX ⋙ pf).IsContinuous JCX JDY] [(qf ⋙ eY).IsContinuous JCX JDY]
    [(eY ⋙ pg).IsContinuous JCY JDZ] [(qg ⋙ eZ).IsContinuous JCY JDZ]
    [(eX ⋙ pfg).IsContinuous JCX JDZ]
    [(qfg ⋙ eZ).IsContinuous JCX JDZ] [(qf ⋙ qg).IsContinuous JCX JCZ]
    (hf : (ιX ≫ (eX.sheafPushforwardContinuous RingCat.{u} JCX JDX).map ρf) ≫
      (Functor.sheafPushforwardContinuousNatTrans αf.symm.hom RingCat.{u} JCX JDY).app OY =
      σf ≫ (qf.sheafPushforwardContinuous RingCat.{u} JCX JCY).map ιY)
    (hg : (ιY ≫ (eY.sheafPushforwardContinuous RingCat.{u} JCY JDY).map ρg) ≫
      (Functor.sheafPushforwardContinuousNatTrans αg.symm.hom RingCat.{u} JCY JDZ).app OZ =
      σg ≫ (qg.sheafPushforwardContinuous RingCat.{u} JCY JCZ).map ιZ)
    (hfg : (ιX ≫ (eX.sheafPushforwardContinuous RingCat.{u} JCX JDX).map ρfg) ≫
      (Functor.sheafPushforwardContinuousNatTrans αfg.symm.hom RingCat.{u} JCX JDZ).app OZ =
      σfg ≫ (qfg.sheafPushforwardContinuous RingCat.{u} JCX JCZ).map ιZ)
    (hβ : (σf ≫ (qf.sheafPushforwardContinuous RingCat.{u} JCX JCY).map σg) ≫
      (Functor.sheafPushforwardContinuousNatTrans β.symm.hom RingCat.{u} JCX JCZ).app RZ = σfg)
    (hm : ∀ T, eZ.map (β.inv.app T) ≫ αg.inv.app (qf.obj T) ≫ pg.map (αf.inv.app T) =
      αfg.inv.app T ≫ γ (eX.obj T))
    (M : SheafOfModules.{u} OZ) :
    (pushforward.{u} ιX).map (c.hom.app M) ≫
        (restrictionSquareIso ιX ιZ ρfg σfg αfg hfg).hom.app M =
    (restrictionSquareIso ιX ιY ρf σf αf hf).hom.app ((pushforward.{u} ρg).obj M) ≫
      (pushforward.{u} σf).map ((restrictionSquareIso ιY ιZ ρg σg αg hg).hom.app M) ≫
      (pushforwardComp (F := qf) (G := qg) σf σg ≪≫ pushforwardCongr₂ _ β.symm hβ).hom.app
        ((pushforward.{u} ιZ).obj M) := by
  ext U x
  let P := M.val.presheaf
  change P.map (αfg.inv.app U.unop).op ((c.hom.app M).val.app (Opposite.op (eX.obj U.unop)) x) =
    (P.map (pg.map (αf.inv.app U.unop)).op ≫ P.map (αg.inv.app (qf.obj U.unop)).op ≫
      P.map (eZ.map (β.inv.app U.unop)).op) x
  refine (congrArg (fun y => P.map (αfg.inv.app U.unop).op y)
    (hc M (Opposite.op (eX.obj U.unop)) x)).trans ?_
  change (P.map (γ (eX.obj U.unop)).op ≫ P.map (αfg.inv.app U.unop).op) x = _
  rw [← P.map_comp, ← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, ← op_comp, Category.assoc,
    hm]

end RestrictionSquareComp

end SheafOfModules

namespace CategoryTheory.Functor

section SharpConj

variable {CX CY CZ A : Type*} [Category* CX] [Category* CY] [Category* CZ] [Category* A]
  {JCX : GrothendieckTopology CX} {JCY : GrothendieckTopology CY} {JCZ : GrothendieckTopology CZ}
  {qf : CX ⥤ CY} {qg : CY ⥤ CZ} {qfg : CX ⥤ CZ} [qf.IsContinuous JCX JCY]
  [qg.IsContinuous JCY JCZ] [qfg.IsContinuous JCX JCZ] [(qf ⋙ qg).IsContinuous JCX JCZ]

/-- **Structure maps conjugate to composable ones compose.** If the structure maps `σ` of
restriction along `q_f`, `q_g`, `q_{fg}` are conjugate, through isomorphisms `i` of the sheaves,
to maps `τ` which compose along `β : q_f ⋙ q_g ≅ q_{fg}`, then so do the `σ`. -/
theorem sheafPushforwardContinuous_comp_eq_of_conj (β : qf ⋙ qg ≅ qfg)
    {RX R'X : Sheaf JCX A} {RY R'Y : Sheaf JCY A} {RZ R'Z : Sheaf JCZ A}
    (iX : RX ≅ R'X) (iY : RY ≅ R'Y) (iZ : RZ ≅ R'Z)
    (σf : RX ⟶ (qf.sheafPushforwardContinuous A JCX JCY).obj RY)
    (σg : RY ⟶ (qg.sheafPushforwardContinuous A JCY JCZ).obj RZ)
    (σfg : RX ⟶ (qfg.sheafPushforwardContinuous A JCX JCZ).obj RZ)
    (τf : R'X ⟶ (qf.sheafPushforwardContinuous A JCX JCY).obj R'Y)
    (τg : R'Y ⟶ (qg.sheafPushforwardContinuous A JCY JCZ).obj R'Z)
    (τfg : R'X ⟶ (qfg.sheafPushforwardContinuous A JCX JCZ).obj R'Z)
    (hf : σf ≫ (qf.sheafPushforwardContinuous A JCX JCY).map iY.hom = iX.hom ≫ τf)
    (hg : σg ≫ (qg.sheafPushforwardContinuous A JCY JCZ).map iZ.hom = iY.hom ≫ τg)
    (hfg : σfg ≫ (qfg.sheafPushforwardContinuous A JCX JCZ).map iZ.hom = iX.hom ≫ τfg)
    (hτ : (τf ≫ (qf.sheafPushforwardContinuous A JCX JCY).map τg) ≫
      (sheafPushforwardContinuousNatTrans β.symm.hom A JCX JCZ).app R'Z = τfg) :
    (σf ≫ (qf.sheafPushforwardContinuous A JCX JCY).map σg) ≫
      (sheafPushforwardContinuousNatTrans β.symm.hom A JCX JCZ).app RZ = σfg := by
  have hn := (sheafPushforwardContinuousNatTrans β.symm.hom A JCX JCZ).naturality iZ.hom
  have e1 : σf ≫ (qf.sheafPushforwardContinuous A JCX JCY).map
      (σg ≫ (qg.sheafPushforwardContinuous A JCY JCZ).map iZ.hom) =
      iX.hom ≫ τf ≫ (qf.sheafPushforwardContinuous A JCX JCY).map τg := by
    rw [hg, Functor.map_comp, reassoc_of% hf]
  rw [← cancel_mono ((qfg.sheafPushforwardContinuous A JCX JCZ).map iZ.hom), hfg, ← hτ]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => (σf ≫ (qf.sheafPushforwardContinuous A JCX JCY).map σg) ≫ t)
    hn.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ (sheafPushforwardContinuousNatTrans β.symm.hom A JCX JCZ).app R'Z)
    ((Category.assoc _ _ _).trans ((congrArg (fun t => σf ≫ t)
      ((qf.sheafPushforwardContinuous A JCX JCY).map_comp σg
        ((qg.sheafPushforwardContinuous A JCY JCZ).map iZ.hom)).symm).trans e1))).trans ?_
  exact Category.assoc _ _ _

end SharpConj

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsEtale B S hS f.hom)
  (hg : IsEtale B S hS g.hom) (hfg : IsEtale B S hS (f ≫ g).hom)

/-- **Postcomposition on the models composes**: postcomposition with `f` followed by
postcomposition with `g`, on the small models of the spaces-étale sites, is postcomposition with
`f ≫ g` (`AlgebraicGeometry.Space.spacesEtalePostcompComp` transported to the small models). -/
def smallModelPostcompComp :
    smallModelPostcomp B S hS f hf ⋙ smallModelPostcomp B S hS g hg ≅
      smallModelPostcomp B S hS (f ≫ g) hfg :=
  NatIso.ofComponents (fun V =>
    (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.mapIso
      ((spacesEtalePostcomp B S hS g hg).mapIso
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.app _).symm ≪≫
        (spacesEtalePostcompComp B S hS f hf g hg).app _)) (by
    intro V W k
    have h1 := (equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.naturality
      ((spacesEtalePostcomp B S hS f hf).map
        ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map k))
    have h2 := (spacesEtalePostcompComp B S hS f hf g hg).hom.naturality
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map k)
    simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at h1 h2
    dsimp [smallModelPostcomp]
    simp only [← Functor.map_comp, Category.assoc]
    congr 1
    rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc, h2])

/-- **On the models, the conjugate of the composition isomorphism of postcompositions is the one
of base changes**: `AlgebraicGeometry.Space.conjugateEquiv_spacesEtalePostcompComp` transported
to the small models. -/
theorem conjugateEquiv_smallModelPostcompComp_hom :
    conjugateEquiv (smallModelPostcompAdjunction B S hS (f ≫ g) hfg)
        ((smallModelPostcompAdjunction B S hS f hf).comp (smallModelPostcompAdjunction B S hS g hg))
        (smallModelPostcompComp B S hS f g hf hg hfg).hom =
      (smallModelBaseChangeComp B S hS f g).inv :=
  conjugateEquiv_comp_equivalence_toAdjunction _ _ _ _ _ _ _ _
    (conjugateEquiv_spacesEtalePostcompComp B S hS f hf g hg) _ (fun _ => rfl) _ (fun _ => by
      simp [smallModelBaseChangeComp])

/-- The conjugate of the composition isomorphism of base changes on the models is the inverse of
the composition isomorphism of postcompositions. -/
theorem conjugateEquiv_symm_smallModelBaseChangeComp_hom :
    (conjugateEquiv ((smallModelPostcompAdjunction B S hS f hf).comp
        (smallModelPostcompAdjunction B S hS g hg))
        (smallModelPostcompAdjunction B S hS (f ≫ g) hfg)).symm
        (smallModelBaseChangeComp B S hS f g).hom =
      (smallModelPostcompComp B S hS f g hf hg hfg).inv := by
  rw [Equiv.symm_apply_eq, ← conjugateIsoEquiv_apply_inv]
  have h : conjugateIsoEquiv (smallModelPostcompAdjunction B S hS (f ≫ g) hfg)
      ((smallModelPostcompAdjunction B S hS f hf).comp (smallModelPostcompAdjunction B S hS g hg))
      (smallModelPostcompComp B S hS f g hf hg hfg) = (smallModelBaseChangeComp B S hS f g).symm :=
    Iso.ext (by rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_smallModelPostcompComp_hom]; rfl)
  rw [h]
  rfl

/-- **Restrictions along postcomposition with étale morphisms compose**, on the spaces-étale
models: the composition isomorphism of the left adjoints
`AlgebraicGeometry.Space.smallModelPostcompPushforwardAdjunction` of the direct images induced by
`AlgebraicGeometry.Space.spacesEtaleModelPushforwardComp`. -/
def smallModelPostcompPushforwardComp :
    SheafOfModules.pushforward (smallModelPostcompSharp B S hS g hg) ⋙
        SheafOfModules.pushforward (smallModelPostcompSharp B S hS f hf) ≅
      SheafOfModules.pushforward (smallModelPostcompSharp B S hS (f ≫ g) hfg) :=
  Adjunction.leftAdjointCompIso (smallModelPostcompPushforwardAdjunction B S hS g hg)
    (smallModelPostcompPushforwardAdjunction B S hS f hf)
    (smallModelPostcompPushforwardAdjunction B S hS (f ≫ g) hfg)
    (spacesEtaleModelPushforwardComp B S hS f g)

/-- The inverse of the composition isomorphism of the direct images on the models is, on
sections, restriction along the composition isomorphism of the base changes. -/
theorem spacesEtaleModelPushforwardComp_inv_app_val_app
    (M : SheafOfModules.{u} (J := smallModelTopology B S hS X)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS X).O))
        (U : (SmallModel.{u} (SpacesEtale B S hS Z))ᵒᵖ) (x) :
    ((spacesEtaleModelPushforwardComp B S hS f g).inv.app M).val.app U x =
      M.val.map ((smallModelBaseChangeComp B S hS f g).hom.app U.unop).op x :=
  rfl

/-- **Restrictions along postcomposition compose, on sections**: the composition isomorphism
`AlgebraicGeometry.Space.smallModelPostcompPushforwardComp` is restriction along the conjugate of
the composition isomorphism of the base changes on the models. -/
theorem smallModelPostcompPushforwardComp_hom_app_val_app
    (M : SheafOfModules.{u} (J := smallModelTopology B S hS Z)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Z).O))
    (V : (SmallModel.{u} (SpacesEtale B S hS X))ᵒᵖ) (x) :
    ((smallModelPostcompPushforwardComp B S hS f g hf hg hfg).hom.app M).val.app V x =
      M.val.map ((smallModelPostcompComp B S hS f g hf hg hfg).inv.app V.unop).op x := by
  rw [← conjugateEquiv_symm_smallModelBaseChangeComp_hom]
  let Af := smallModelPostcompPushforwardAdjunction B S hS f hf
  let Ag := smallModelPostcompPushforwardAdjunction B S hS g hg
  let Afg := smallModelPostcompPushforwardAdjunction B S hS (f ≫ g) hfg
  have h1 := (congrArg (fun t => t.app M) (Adjunction.leftAdjointCompIso_hom Ag Af Afg
    (spacesEtaleModelPushforwardComp B S hS f g))).trans
    (Adjunction.leftAdjointCompNatTrans_app Ag Af Afg
      (spacesEtaleModelPushforwardComp B S hS f g).inv M)
  have h2 := conjugateEquiv_symm_apply_app
      ((smallModelPostcompAdjunction B S hS f hf).comp (smallModelPostcompAdjunction B S hS g hg))
      (smallModelPostcompAdjunction B S hS (f ≫ g) hfg) (smallModelBaseChangeComp B S hS f g).hom
      V.unop
  rw [h2]
  refine (congrArg (fun t => t.val.app V x) h1).trans ?_
  let W := (smallModelPostcomp B S hS g hg).obj ((smallModelPostcomp B S hS f hf).obj V.unop)
  let P := M.val.presheaf
  change (P.map ((smallModelPostcompAdjunction B S hS (f ≫ g) hfg).counit.app W).op ≫
    P.map ((smallModelPostcomp B S hS (f ≫ g) hfg).map
      ((smallModelBaseChangeComp B S hS f g).hom.app W)).op ≫
    P.map ((smallModelPostcomp B S hS (f ≫ g) hfg).map ((smallModelBaseChange B S hS f).map
      ((smallModelPostcompAdjunction B S hS g hg).unit.app
        ((smallModelPostcomp B S hS f hf).obj V.unop)))).op ≫
    P.map ((smallModelPostcomp B S hS (f ≫ g) hfg).map
      ((smallModelPostcompAdjunction B S hS f hf).unit.app V.unop)).op) x =
    (P.map (((smallModelPostcomp B S hS (f ≫ g) hfg).map
      (((smallModelPostcompAdjunction B S hS f hf).comp
        (smallModelPostcompAdjunction B S hS g hg)).unit.app V.unop) ≫
      (smallModelPostcomp B S hS (f ≫ g) hfg).map
        ((smallModelBaseChangeComp B S hS f g).hom.app W) ≫
      (smallModelPostcompAdjunction B S hS (f ≫ g) hfg).counit.app W).op)) x
  rw [Adjunction.comp_unit_app]
  simp only [← Functor.map_comp, ← op_comp, Category.assoc]
  congr 3
  simp only [Functor.map_comp, Category.assoc]

/-- **The composition isomorphism of étale inverse images on the models is the composition
isomorphism of restrictions along postcomposition**, through the identifications
`AlgebraicGeometry.Space.spacesEtaleModelPullbackIsoPushforward` of the inverse images with the
restrictions. -/
theorem spacesEtaleModelPullbackComp_trans_pullbackIsoPushforward :
    spacesEtaleModelPullbackComp B S hS f g ≪≫
        spacesEtaleModelPullbackIsoPushforward B S hS (f ≫ g) hfg =
      Functor.isoWhiskerRight (spacesEtaleModelPullbackIsoPushforward B S hS g hg) _ ≪≫
        Functor.isoWhiskerLeft _ (spacesEtaleModelPullbackIsoPushforward B S hS f hf) ≪≫
        smallModelPostcompPushforwardComp B S hS f g hf hg hfg := by
  rw [spacesEtaleModelPullbackComp_eq_leftAdjointCompIso]
  exact Adjunction.leftAdjointCompIso_trans_leftAdjointUniq _ _ _ _ _ _ _

/-! ### Composition on the small étale models -/

/-- **Postcomposition on the small étale models composes**: postcomposition of étale charts with
`f` followed by postcomposition with `g` is postcomposition with `f ≫ g` on the charts, and on the
small models of the small étale sites the two differ by the unit of the model of `Y`. -/
def smallEtaleModelPostcompComp :
    smallEtaleModelPostcomp B S hS f hf ⋙ smallEtaleModelPostcomp B S hS g hg ≅
      smallEtaleModelPostcomp B S hS (f ≫ g) hfg :=
  Functor.isoWhiskerLeft ((smallEtaleModelEquiv B S hS X).inverse ⋙ smallEtalePostcomp B S hS f hf)
    (Functor.isoWhiskerRight (smallEtaleModelEquiv B S hS Y).unitIso.symm
        (smallEtalePostcomp B S hS g hg ⋙ (smallEtaleModelEquiv B S hS Z).functor) ≪≫
      Functor.leftUnitor _)

/-- The two morphisms of charts of `Z` along which restriction along a composite of
postcompositions on the small étale models is compared agree: the inverse of
`AlgebraicGeometry.Space.smallEtaleModelPostcompComp` read on the site, followed by the inverse
units, is the inverse unit. -/
theorem smallEtaleModelPostcompComp_inv_app_op_comp (T : SmallModel.{u} (SmallEtale B S hS X.1)) :
    ((smallEtalePostcomp B S hS g hg).map ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
        ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))).op ≫
      ((smallEtaleModelEquiv B S hS Z).unitIso.inv.app ((smallEtalePostcomp B S hS g hg).obj
        ((smallEtaleModelEquiv B S hS Y).inverse.obj ((smallEtaleModelEquiv B S hS Y).functor.obj
          ((smallEtalePostcomp B S hS f hf).obj
              ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))).op ≫
      ((smallEtaleModelEquiv B S hS Z).inverse.map
        ((smallEtaleModelPostcompComp B S hS f g hf hg hfg).inv.app T)).op =
      ((smallEtaleModelEquiv B S hS Z).unitIso.inv.app ((smallEtalePostcomp B S hS g hg).obj
        ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))).op := by
  apply Quiver.Hom.unop_inj
  simp only [smallEtaleModelPostcompComp, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app, unop_comp, Quiver.Hom.unop_op,
    Functor.comp_map, Functor.comp_obj, Category.id_comp, Category.assoc]
  exact Equivalence.inverse_map_functor_map_unit_comp _ _ _ _

/-- Morphisms of sheaves of rings which agree on all sections are equal. -/
private theorem sheaf_ringCat_hom_ext {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F G : Sheaf J RingCat.{u}} {f g : F ⟶ G} (h : ∀ U r, f.hom.app U r = g.hom.app U r) :
    f = g :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => RingCat.hom_ext (RingHom.ext (h U))))

/-- The structure maps of restriction along postcomposition on the small étale models compose:
the one of `f` followed by the direct image of the one of `g`, transported along
`AlgebraicGeometry.Space.smallEtaleModelPostcompComp`, is the one of `f ≫ g`. -/
theorem smallEtaleModelPostcompSharp_comp :
    haveI : (smallEtaleModelPostcomp B S hS f hf ⋙ smallEtaleModelPostcomp B S hS g hg).IsContinuous
        (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Z.1) :=
      Functor.isContinuous_comp _ _ _ (smallEtaleModelTopology B S hS Y.1) _
    (smallEtaleModelPostcompSharp B S hS f hf ≫
        ((smallEtaleModelPostcomp B S hS f hf).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Y.1)).map
          (smallEtaleModelPostcompSharp B S hS g hg)) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (smallEtaleModelPostcompComp B S hS f g hf hg hfg).symm.hom RingCat.{u}
          (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Z.1)).app
        (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleModelTopology B S hS Z.1)
            (SmallEtale.topology B S hS Z.1)
          (smallEtaleModelEquiv B S hS Z).inverse (structureRingSheaf B S hS Z)) =
      smallEtaleModelPostcompSharp B S hS (f ≫ g) hfg :=
  sheaf_ringCat_hom_ext (fun T r => by
    let O := (structureRingSheaf B S hS Z).obj
    let A := (smallEtalePostcomp B S hS f hf).obj
        ((smallEtaleModelEquiv B S hS X).inverse.obj T.unop)
    have hm := smallEtaleModelPostcompComp_inv_app_op_comp B S hS f g hf hg hfg T.unop
    change (O.map ((smallEtalePostcomp B S hS g hg).map
        ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app A)).op ≫
      O.map ((smallEtaleModelEquiv B S hS Z).unitIso.inv.app ((smallEtalePostcomp B S hS g hg).obj
        ((smallEtaleModelEquiv B S hS Y).inverse.obj
            ((smallEtaleModelEquiv B S hS Y).functor.obj A)))).op ≫
      O.map ((smallEtaleModelEquiv B S hS Z).inverse.map
        ((smallEtaleModelPostcompComp B S hS f g hf hg hfg).inv.app T.unop)).op) r =
      O.map ((smallEtaleModelEquiv B S hS Z).unitIso.inv.app
        ((smallEtalePostcomp B S hS g hg).obj A)).op r
    rw [← O.map_comp, ← O.map_comp, hm]
    rfl)

/-- **Restrictions along postcomposition compose on the small étale models**: restriction of
modules along `AlgebraicGeometry.Space.smallEtaleModelPostcomp` of `g` and then of `f` is
restriction along the one of `f ≫ g`, through
`AlgebraicGeometry.Space.smallEtaleModelPostcompComp`. -/
def smallEtaleModelPushforwardComp :
    SheafOfModules.pushforward.{u} (smallEtaleModelPostcompSharp B S hS g hg) ⋙
        SheafOfModules.pushforward.{u} (smallEtaleModelPostcompSharp B S hS f hf) ≅
      SheafOfModules.pushforward.{u} (smallEtaleModelPostcompSharp B S hS (f ≫ g) hfg) :=
  haveI : (smallEtaleModelPostcomp B S hS f hf ⋙ smallEtaleModelPostcomp B S hS g hg).IsContinuous
      (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Z.1) :=
    Functor.isContinuous_comp _ _ _ (smallEtaleModelTopology B S hS Y.1) _
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (smallEtaleModelPostcompComp B S hS f g hf hg hfg).symm
      (smallEtaleModelPostcompSharp_comp B S hS f g hf hg hfg)

section RestrictionPostcompComp

/-- Postcomposition of étale charts composes on the nose, object by object. -/
theorem smallEtalePostcomp_obj_smallEtalePostcomp_obj (U : SmallEtale B S hS X.1) :
    (smallEtalePostcomp B S hS g hg).obj ((smallEtalePostcomp B S hS f hf).obj U) =
    (smallEtalePostcomp B S hS (f ≫ g) hfg).obj U := rfl

/-- On sections, the composition isomorphism of étale restrictions is restriction along the
identity of the composite chart. -/
theorem etaleModulePullbackComp_hom_app_val_app_eq_map_eqToHom (M : Modules.{u, u} B S hS Z.1 Z.2)
    (U : SmallEtale B S hS X.1) (x) :
    ((etaleModulePullbackComp B S hS f g hf hg hfg).hom.app M).val.app (Opposite.op U) x =
      M.val.presheaf.map
        (eqToHom
          (smallEtalePostcomp_obj_smallEtalePostcomp_obj B S hS f g hf hg hfg U).symm).op x := by
  rw [show eqToHom
        (smallEtalePostcomp_obj_smallEtalePostcomp_obj B S hS f g hf hg hfg U).symm = 𝟙 _ from rfl]
  exact (etaleModulePullbackComp_hom_app_val_app B S hS f g hf hg hfg (M := M) (U := U)
        (m := x)).trans
    (ConcreteCategory.congr_hom (M.val.presheaf.map_id
      (Opposite.op ((smallEtalePostcomp B S hS (f ≫ g) hfg).obj U))) x).symm

/-- The comparisons of the small étale sites with their models are compatible with
`AlgebraicGeometry.Space.smallEtaleModelPostcompComp`, chart by chart. -/
theorem smallEtaleModelPostcompComp_inv_app_comp_inversePostcompIso
    (T : SmallModel.{u} (SmallEtale B S hS X.1)) :
    (smallEtaleModelEquiv B S hS Z).inverse.map
        ((smallEtaleModelPostcompComp B S hS f g hf hg hfg).inv.app T) ≫
      (smallEtaleModelInversePostcompIso B S hS g hg).inv.app
        ((smallEtaleModelPostcomp B S hS f hf).obj T) ≫
        (smallEtalePostcomp B S hS g hg).map
          ((smallEtaleModelInversePostcompIso B S hS f hf).inv.app T) =
    (smallEtaleModelInversePostcompIso B S hS (f ≫ g) hfg).inv.app T ≫
      eqToHom (smallEtalePostcomp_obj_smallEtalePostcomp_obj B S hS f g hf hg hfg
          ((smallEtaleModelEquiv B S hS X).inverse.obj T)).symm := by
  have h := congrArg Quiver.Hom.unop
    (smallEtaleModelPostcompComp_inv_app_op_comp B S hS f g hf hg hfg T)
  simp only [unop_comp, Quiver.Hom.unop_op, Category.assoc] at h
  rw [show eqToHom (smallEtalePostcomp_obj_smallEtalePostcomp_obj B S hS f g hf hg hfg
          ((smallEtaleModelEquiv B S hS X).inverse.obj T)).symm =
    𝟙 _ from rfl]
  exact h.trans (Category.comp_id _).symm

-- The structure sheaves and the small models never need to be unfolded below: keeping them
-- sealed keeps the unification of the comparisons below cheap.
attribute [local irreducible] equivSmallModel smallEtalePostcomp
  AlgebraicGeometry.Space.structureSheaf
  AlgebraicGeometry.Space.structureSheaf' AlgebraicGeometry.Space.structurePresheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

/-- Postcomposition on the small étale models along two étale morphisms is continuous. -/
instance isContinuous_smallEtaleModelPostcomp_comp_smallEtaleModelPostcomp :
    (smallEtaleModelPostcomp B S hS f hf ⋙ smallEtaleModelPostcomp B S hS g hg).IsContinuous
      (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Z.1) :=
  Functor.isContinuous_comp _ _ _ (smallEtaleModelTopology B S hS Y.1) _

/-- **The restriction comparisons on the small étale models are compatible with composition**:
`AlgebraicGeometry.Space.smallEtaleModelModuleRestrictionPostcompIso` for `f`, `g` and `f ≫ g`
is compatible with `AlgebraicGeometry.Space.etaleModulePullbackComp` and
`AlgebraicGeometry.Space.smallEtaleModelPushforwardComp`. -/
theorem smallEtaleModelModuleRestrictionPostcompIso_comp (P : Modules.{u, u} B S hS Z.1 Z.2) :
    (smallEtaleModelModuleRestriction B S hS X).map
        ((etaleModulePullbackComp B S hS f g hf hg hfg).hom.app P) ≫
      (smallEtaleModelModuleRestrictionPostcompIso B S hS (f ≫ g) hfg).hom.app P =
    (smallEtaleModelModuleRestrictionPostcompIso B S hS f hf).hom.app
        ((etaleModulePullback.{u, u} B S hS g hg).obj P) ≫
      (SheafOfModules.pushforward.{u} (smallEtaleModelPostcompSharp B S hS f hf)).map
        ((smallEtaleModelModuleRestrictionPostcompIso B S hS g hg).hom.app P) ≫
      (smallEtaleModelPushforwardComp B S hS f g hf hg hfg).hom.app
        ((smallEtaleModelModuleRestriction B S hS Z).obj P) := by
  have H := SheafOfModules.restrictionSquareIso_comp
    (eX := (smallEtaleModelEquiv B S hS X).inverse) (eY := (smallEtaleModelEquiv B S hS Y).inverse)
    (eZ := (smallEtaleModelEquiv B S hS Z).inverse) (pf := smallEtalePostcomp B S hS f hf)
    (pg := smallEtalePostcomp B S hS g hg) (pfg := smallEtalePostcomp B S hS (f ≫ g) hfg)
    (qf := smallEtaleModelPostcomp B S hS f hf)
    (qg := smallEtaleModelPostcomp B S hS g hg) (qfg := smallEtaleModelPostcomp B S hS (f ≫ g) hfg)
    (𝟙 (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleModelTopology B S hS X.1)
            (SmallEtale.topology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse
            (structureRingSheaf B S hS X)))
        (𝟙 (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleModelTopology B S hS Y.1)
            (SmallEtale.topology B S hS Y.1) (smallEtaleModelEquiv B S hS Y).inverse
            (structureRingSheaf B S hS Y)))
        (𝟙 (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleModelTopology B S hS Z.1)
            (SmallEtale.topology B S hS Z.1) (smallEtaleModelEquiv B S hS Z).inverse
            (structureRingSheaf B S hS Z)))
    (etaleRestrictionRingMap B S hS f hf) (etaleRestrictionRingMap B S hS g hg)
    (etaleRestrictionRingMap B S hS (f ≫ g) hfg) (etaleModulePullbackComp B S hS f g hf hg hfg)
    (fun U => eqToHom (smallEtalePostcomp_obj_smallEtalePostcomp_obj B S hS f g hf hg hfg U).symm)
    (fun M U x => etaleModulePullbackComp_hom_app_val_app_eq_map_eqToHom B S hS f g hf hg
          hfg M U.unop x)
    (smallEtaleModelPostcompSharp B S hS f hf)
    (smallEtaleModelPostcompSharp B S hS g hg) (smallEtaleModelPostcompSharp B S hS (f ≫ g) hfg)
    (smallEtaleModelInversePostcompIso B S hS f hf) (smallEtaleModelInversePostcompIso B S hS g hg)
    (smallEtaleModelInversePostcompIso B S hS (f ≫ g) hfg)
    (smallEtaleModelPostcompComp B S hS f g hf hg hfg)
    (sheaf_ringCat_hom_ext fun _ _ => rfl)
    (sheaf_ringCat_hom_ext fun _ _ => rfl)
    (sheaf_ringCat_hom_ext fun _ _ => rfl)
    (smallEtaleModelPostcompSharp_comp B S hS f g hf hg hfg)
        (smallEtaleModelPostcompComp_inv_app_comp_inversePostcompIso B S hS f g hf hg hfg) P
  exact H

/-- **Step D is compatible with composition**: the transports of the étale pullbacks to the small
étale models (`AlgebraicGeometry.Space.smallEtaleModelModulesEquivInversePostcompIso`) are
compatible with `AlgebraicGeometry.Space.smallEtaleModelPushforwardComp` and
`AlgebraicGeometry.Space.etaleModulePullbackComp`. -/
theorem smallEtaleModelModulesEquivInversePostcompIso_comp (N) :
    (smallEtaleModelModulesEquiv B S hS X).inverse.map
        ((smallEtaleModelPushforwardComp B S hS f g hf hg hfg).hom.app N) ≫
      (smallEtaleModelModulesEquivInversePostcompIso B S hS (f ≫ g) hfg).hom.app N =
    (smallEtaleModelModulesEquivInversePostcompIso B S hS f hf).hom.app
        ((SheafOfModules.pushforward.{u} (smallEtaleModelPostcompSharp B S hS g hg)).obj N) ≫
      (etaleModulePullback.{u, u} B S hS f hf).map
        ((smallEtaleModelModulesEquivInversePostcompIso B S hS g hg).hom.app N) ≫
      (etaleModulePullbackComp B S hS f g hf hg hfg).hom.app
        ((smallEtaleModelModulesEquiv B S hS Z).inverse.obj N) :=
  inverse_map_comp_transport_of_comp_coherence (smallEtaleModelModulesEquiv B S hS X)
    (smallEtaleModelModulesEquiv B S hS Y) (smallEtaleModelModulesEquiv B S hS Z)
    (etaleModulePullbackComp B S hS f g hf hg hfg).hom
    (smallEtaleModelPushforwardComp B S hS f g hf hg hfg).hom
    (smallEtaleModelModuleRestrictionPostcompIso B S hS f hf)
    (smallEtaleModelModuleRestrictionPostcompIso B S hS g hg)
    (smallEtaleModelModuleRestrictionPostcompIso B S hS (f ≫ g) hfg)
    (smallEtaleModelModuleRestrictionPostcompIso_comp B S hS f g hf hg hfg)
    (smallEtaleModelModulesEquivInversePostcompIso B S hS f hf).hom
    (smallEtaleModelModulesEquivInversePostcompIso B S hS g hg).hom
    (smallEtaleModelModulesEquivInversePostcompIso B S hS (f ≫ g) hfg).hom
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl) N

end RestrictionPostcompComp

section ModelRestrictionPostcompComp

/-- The composition isomorphism of postcompositions is the identity on (the image of) an étale
chart. -/
theorem spacesEtalePostcompComp_inv_app_comparisonFunctor_obj (U : SmallEtale B S hS X.1) :
    (spacesEtalePostcompComp B S hS f hf g hg).inv.app
        ((comparisonFunctor B S hS X).obj U) = 𝟙 _ := rfl

/-- The comparison functor commutes on the nose with postcomposition. -/
theorem comparisonFunctor_map_smallEtalePostcomp_map {U V : SmallEtale B S hS Y.1} (k : U ⟶ V) :
    (comparisonFunctor B S hS Z).map ((smallEtalePostcomp B S hS g hg).map k) =
        (spacesEtalePostcomp B S hS g hg).map ((comparisonFunctor B S hS Y).map k) := rfl

/-- `AlgebraicGeometry.Space.spacesEtaleModelComparisonPostcompIso_inv_app_comp` on the
spaces-étale site of `Z`, written out in terms of the units of the small models. -/
theorem spacesEtaleModelComparisonPostcompIso_inv_app_comp_of_units
    (T : SmallModel.{u} (SmallEtale B S hS X.1)) :
    (comparisonFunctor B S hS Z).map
        ((smallEtaleModelEquiv B S hS Z).inverse.map
          ((smallEtaleModelEquiv B S hS Z).functor.map
            ((smallEtalePostcomp B S hS g hg).map
            ((smallEtaleModelEquiv B S hS Y).unitIso.hom.app
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) ≫
      (comparisonFunctor B S hS Z).map
        ((smallEtaleModelEquiv B S hS Z).unitIso.inv.app
          ((smallEtalePostcomp B S hS g hg).obj
            ((smallEtaleModelEquiv B S hS Y).inverse.obj
            ((smallEtaleModelEquiv B S hS Y).functor.obj
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) ≫
      (spacesEtalePostcomp B S hS g hg).map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
          ((comparisonFunctor B S hS Y).obj
            ((smallEtaleModelEquiv B S hS Y).inverse.obj
            ((smallEtaleModelEquiv B S hS Y).functor.obj
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) ≫
      (spacesEtalePostcomp B S hS g hg).map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.map
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).functor.map
            ((comparisonFunctor B S hS Y).map
            ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫
        (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor.map
          ((spacesEtalePostcomp B S hS f hf).map
            ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
              ((comparisonFunctor B S hS X).obj
              ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) =
    (comparisonFunctor B S hS Z).map
        ((smallEtaleModelEquiv B S hS Z).unitIso.inv.app
          ((smallEtalePostcomp B S hS (f ≫ g) hfg).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T))) ≫
      (spacesEtalePostcomp B S hS (f ≫ g) hfg).map
        ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
          ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T))) ≫
        (spacesEtalePostcompComp B S hS f hf g hg).inv.app
        ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.obj
            ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫
      (spacesEtalePostcomp B S hS g hg).map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
          ((spacesEtalePostcomp B S hS f hf).obj
            ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
            ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.obj
            ((comparisonFunctor B S hS X).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) := by
  have hn1 :=
      (smallEtaleModelEquiv B S hS Z).unitIso.inv.naturality
      ((smallEtalePostcomp B S hS g hg).map
        ((smallEtaleModelEquiv B S hS Y).unitIso.hom.app
          ((smallEtalePostcomp B S hS f hf).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T))))
  have hn2 :=
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.naturality
      (((comparisonFunctor B S hS Y).map
          ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
          ((smallEtalePostcomp B S hS f hf).obj
          ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫
        ((spacesEtalePostcomp B S hS f hf).map
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
          ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))
  have hn3 :=
      (spacesEtalePostcompComp B S hS f hf g hg).inv.naturality
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
        ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T)))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn1 hn2 hn3
  rw [spacesEtalePostcompComp_inv_app_comparisonFunctor_obj] at hn3
  replace hn3 := hn3.trans (Category.id_comp _)
  have h45 : (spacesEtalePostcomp B S hS g hg).map
      ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
        ((comparisonFunctor B S hS Y).obj
          ((smallEtaleModelEquiv B S hS Y).inverse.obj
          ((smallEtaleModelEquiv B S hS Y).functor.obj
          ((smallEtalePostcomp B S hS f hf).obj
          ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) ≫
      (spacesEtalePostcomp B S hS g hg).map
      ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).functor.map
          ((comparisonFunctor B S hS Y).map
          ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
          ((smallEtalePostcomp B S hS f hf).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor.map
        ((spacesEtalePostcomp B S hS f hf).map
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
            ((comparisonFunctor B S hS X).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) =
        (spacesEtalePostcomp B S hS g hg).map
        ((((comparisonFunctor B S hS Y).map
          ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫
        ((spacesEtalePostcomp B S hS f hf).map
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
            ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T))))) ≫
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
        ((spacesEtalePostcomp B S hS f hf).obj
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
            ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.obj
            ((comparisonFunctor B S hS X).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T))))))) :=
    ((spacesEtalePostcomp B S hS g hg).map_comp _ _).symm.trans
        (congrArg (fun k => (spacesEtalePostcomp B S hS g hg).map k)
      ((congrArg
            (fun k => ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
            ((comparisonFunctor B S hS Y).obj
            ((smallEtaleModelEquiv B S hS Y).inverse.obj
            ((smallEtaleModelEquiv B S hS Y).functor.obj
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) ≫
            (equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.map k)
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).functor.map_comp
            ((comparisonFunctor B S hS Y).map
              ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
              ((smallEtalePostcomp B S hS f hf).obj
              ((smallEtaleModelEquiv B S hS X).inverse.obj T))))
            ((spacesEtalePostcomp B S hS f hf).map
              ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
              ((comparisonFunctor B S hS X).obj
              ((smallEtaleModelEquiv B S hS X).inverse.obj T))))).symm).trans hn2.symm))
  have hcu : (comparisonFunctor B S hS Y).map
      ((smallEtaleModelEquiv B S hS Y).unitIso.hom.app
        ((smallEtalePostcomp B S hS f hf).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T))) ≫
      ((comparisonFunctor B S hS Y).map
        ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
          ((smallEtalePostcomp B S hS f hf).obj
          ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) = 𝟙 _ :=
    ((comparisonFunctor B S hS Y).map_comp _ _).symm.trans
        ((congrArg (fun k => (comparisonFunctor B S hS Y).map k)
      ((smallEtaleModelEquiv B S hS Y).unitIso.hom_inv_id_app
          ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))).trans
        ((comparisonFunctor B S hS Y).map_id _))
  have h6 : (spacesEtalePostcomp B S hS g hg).map
      ((comparisonFunctor B S hS Y).map
        ((smallEtaleModelEquiv B S hS Y).unitIso.hom.app
          ((smallEtalePostcomp B S hS f hf).obj
          ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫
      (spacesEtalePostcomp B S hS g hg).map
      ((((comparisonFunctor B S hS Y).map
          ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
          ((smallEtalePostcomp B S hS f hf).obj
          ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫
          ((spacesEtalePostcomp B S hS f hf).map
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
          ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T))))) ≫
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
          ((spacesEtalePostcomp B S hS f hf).obj
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.obj
          ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T))))))) =
      (spacesEtalePostcomp B S hS g hg).map
        ((spacesEtalePostcomp B S hS f hf).map
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
            ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫
        (spacesEtalePostcomp B S hS g hg).map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
          ((spacesEtalePostcomp B S hS f hf).obj
            ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
            ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.obj
            ((comparisonFunctor B S hS X).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) :=
    ((spacesEtalePostcomp B S hS g hg).map_comp _ _).symm.trans
        ((congrArg (fun k => (spacesEtalePostcomp B S hS g hg).map k)
      ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫
            ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
            ((spacesEtalePostcomp B S hS f hf).obj
            ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
            ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.obj
            ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))))
        ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫
              ((spacesEtalePostcomp B S hS f hf).map
              ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
              ((comparisonFunctor B S hS X).obj
              ((smallEtaleModelEquiv B S hS X).inverse.obj T))))) hcu).trans
          (Category.id_comp _)))))).trans ((spacesEtalePostcomp B S hS g hg).map_comp _ _))
  have hl : (comparisonFunctor B S hS Z).map
      ((smallEtaleModelEquiv B S hS Z).inverse.map
        ((smallEtaleModelEquiv B S hS Z).functor.map
          ((smallEtalePostcomp B S hS g hg).map
          ((smallEtaleModelEquiv B S hS Y).unitIso.hom.app
          ((smallEtalePostcomp B S hS f hf).obj
          ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) ≫
      (comparisonFunctor B S hS Z).map
        ((smallEtaleModelEquiv B S hS Z).unitIso.inv.app
          ((smallEtalePostcomp B S hS g hg).obj
            ((smallEtaleModelEquiv B S hS Y).inverse.obj
            ((smallEtaleModelEquiv B S hS Y).functor.obj
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))))) =
      (comparisonFunctor B S hS Z).map
        ((smallEtaleModelEquiv B S hS Z).unitIso.inv.app
          ((smallEtalePostcomp B S hS g hg).obj
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫
        (spacesEtalePostcomp B S hS g hg).map
        ((comparisonFunctor B S hS Y).map
          ((smallEtaleModelEquiv B S hS Y).unitIso.hom.app
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) :=
    (Functor.map_comp _ _ _).symm.trans
        ((congrArg (fun k => (comparisonFunctor B S hS Z).map k) hn1).trans
      (Functor.map_comp _ _ _))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ _) hl).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg
        (fun k => (comparisonFunctor B S hS Z).map
          ((smallEtaleModelEquiv B S hS Z).unitIso.inv.app
          ((smallEtalePostcomp B S hS g hg).obj
          ((smallEtalePostcomp B S hS f hf).obj
          ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫ k)
    ((congrArg
            (fun k => (spacesEtalePostcomp B S hS g hg).map
            ((comparisonFunctor B S hS Y).map
            ((smallEtaleModelEquiv B S hS Y).unitIso.hom.app
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) ≫ k) h45).trans h6)).trans ?_
  exact congrArg
      (fun k => (comparisonFunctor B S hS Z).map
        ((smallEtaleModelEquiv B S hS Z).unitIso.inv.app
          ((smallEtalePostcomp B S hS (f ≫ g) hfg).obj
          ((smallEtaleModelEquiv B S hS X).inverse.obj T))) ≫ k) ((reassoc_of% hn3) _).symm

/-- The inverse of `AlgebraicGeometry.Space.smallEtaleModelPostcompComp` at `T`: the image of the
unit of the small model of `Y`. -/
theorem smallEtaleModelPostcompComp_inv_app (T : SmallModel.{u} (SmallEtale B S hS X.1)) :
    (smallEtaleModelPostcompComp B S hS f g hf hg hfg).inv.app T =
      (smallEtaleModelEquiv B S hS Z).functor.map
        ((smallEtalePostcomp B S hS g hg).map
          ((smallEtaleModelEquiv B S hS Y).unitIso.hom.app
            ((smallEtalePostcomp B S hS f hf).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj T)))) := by
  simp [smallEtaleModelPostcompComp]
  rfl

/-- **The comparisons of the small models carry the composition of postcompositions to
composition**: `AlgebraicGeometry.Space.spacesEtaleModelComparisonPostcompIso` for `f`, `g` and
`f ≫ g` are compatible with `AlgebraicGeometry.Space.smallEtaleModelPostcompComp` and
`AlgebraicGeometry.Space.smallModelPostcompComp`, object by object. -/
theorem spacesEtaleModelComparisonPostcompIso_inv_app_comp
    (T : SmallModel.{u} (SmallEtale B S hS X.1)) :
    (spacesEtaleModelComparison B S hS Z).map
        ((smallEtaleModelPostcompComp B S hS f g hf hg hfg).inv.app T) ≫
      (spacesEtaleModelComparisonPostcompIso B S hS g hg).inv.app
        ((smallEtaleModelPostcomp B S hS f hf).obj T) ≫
        (smallModelPostcomp B S hS g hg).map
          ((spacesEtaleModelComparisonPostcompIso B S hS f hf).inv.app T) =
    (spacesEtaleModelComparisonPostcompIso B S hS (f ≫ g) hfg).inv.app T ≫
      (smallModelPostcompComp B S hS f g hf hg hfg).inv.app
        ((spacesEtaleModelComparison B S hS X).obj T) := by
  rw [smallEtaleModelPostcompComp_inv_app]
  refine Eq.trans ?_
      ((congrArg (fun k => (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map k)
          (spacesEtaleModelComparisonPostcompIso_inv_app_comp_of_units B S hS f g hf hg
          hfg T)).trans ?_)
  · refine Eq.trans ?_ (((equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map_comp _ _).trans
          (congrArg (fun k => (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map _ ≫ k)
      (((equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map_comp _ _).trans
          (congrArg (fun k => (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map _ ≫ k)
            ((equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map_comp _ _))))).symm
    exact congrArg (fun k => (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map _ ≫ k)
        (Category.assoc _ _ _)
  · refine (((equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map_comp _ _).trans
          (congrArg (fun k => (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map _ ≫ k)
      (((equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map_comp _ _).trans
          (congrArg (fun k => (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map _ ≫ k)
            ((equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map_comp _ _))))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (fun k => _ ≫ k)
        ((equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.map_comp _ _).symm

-- The structure sheaves and the small models never need to be unfolded below.
attribute [local irreducible] equivSmallModel smallEtalePostcomp
  AlgebraicGeometry.Space.structureSheaf
  AlgebraicGeometry.Space.structureSheaf' AlgebraicGeometry.Space.structurePresheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

/-- **The restricted structure maps of postcomposition compose**:
`AlgebraicGeometry.Space.spacesEtaleModelRestrictedPostcompSharp` for `f` followed by the direct
image of the one for `g`, transported along
`AlgebraicGeometry.Space.smallEtaleModelPostcompComp`, is the one for `f ≫ g` (they are conjugate
to the structure maps on the small étale models, which compose). -/
theorem spacesEtaleModelRestrictedPostcompSharp_comp :
    (spacesEtaleModelRestrictedPostcompSharp B S hS f hf ≫
        ((smallEtaleModelPostcomp B S hS f hf).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Y.1)).map
          (spacesEtaleModelRestrictedPostcompSharp B S hS g hg)) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (smallEtaleModelPostcompComp B S hS f g hf hg hfg).symm.hom RingCat.{u}
          (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Z.1)).app
        (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleModelTopology B S hS Z.1)
            (smallModelTopology B S hS Z) (spacesEtaleModelComparison B S hS Z)
            (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Z))) =
      spacesEtaleModelRestrictedPostcompSharp B S hS (f ≫ g) hfg :=
  Functor.sheafPushforwardContinuous_comp_eq_of_conj
      (smallEtaleModelPostcompComp B S hS f g hf hg hfg)
    (spacesEtaleModelRingRestrictionIso B S hS X) (spacesEtaleModelRingRestrictionIso B S hS Y)
    (spacesEtaleModelRingRestrictionIso B S hS Z) _ _ _ _ _ _
    (spacesEtaleModelRestrictedPostcompSharp_comp_ringRestrictionIso B S hS f hf)
    (spacesEtaleModelRestrictedPostcompSharp_comp_ringRestrictionIso B S hS g hg)
    (spacesEtaleModelRestrictedPostcompSharp_comp_ringRestrictionIso B S hS (f ≫ g) hfg)
    (smallEtaleModelPostcompSharp_comp B S hS f g hf hg hfg)

-- Neither do the comparison functors and the shrunk structure presheaves.
attribute [local irreducible] comparisonFunctor chartFunctor globalFunctionsPresheaf
  spacesEtalePostcomp shrinkCommRingPresheaf

/-- The square of structure maps underlying
`AlgebraicGeometry.Space.moduleRestrictionPostcompIso`. -/
theorem spacesEtaleModelRestrictedPostcompSharp_square (j : X ⟶ Y) (hj : IsEtale B S hS j.hom) :
    ((𝟙 (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleModelTopology B S hS X.1)
            (smallModelTopology B S hS X) (spacesEtaleModelComparison B S hS X)
            (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)))) ≫
          ((spacesEtaleModelComparison B S hS X).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)).map
        (smallModelPostcompSharp B S hS j hj)) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (spacesEtaleModelComparisonPostcompIso B S hS j hj).symm.hom RingCat.{u}
        (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS Y)).app
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Y).O) =
      spacesEtaleModelRestrictedPostcompSharp B S hS j hj ≫
        ((smallEtaleModelPostcomp B S hS j hj).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Y.1)).map
          (𝟙 (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleModelTopology B S hS Y.1)
                (smallModelTopology B S hS Y) (spacesEtaleModelComparison B S hS Y)
                (Stacks.SheafOfModules.Tensor.ringSheaf
                (spacesEtaleModelStructureSheaf B S hS Y)))) :=
            (sheaf_ringCat_hom_ext fun _ _ => rfl)

/-- `AlgebraicGeometry.Space.moduleRestrictionPostcompIso` is the restriction comparison
`SheafOfModules.restrictionSquareIso` of its square. -/
theorem moduleRestrictionPostcompIso_eq_restrictionSquareIso (j : X ⟶ Y)
    (hj : IsEtale B S hS j.hom) :
    moduleRestrictionPostcompIso B S hS j hj =
      SheafOfModules.restrictionSquareIso
        (JCX := smallEtaleModelTopology B S hS X.1) (JCY := smallEtaleModelTopology B S hS Y.1)
        (JDX := smallModelTopology B S hS X) (JDY := smallModelTopology B S hS Y)
        (OX := Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS X).O)
        (OY := Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Y).O)
        (eX := spacesEtaleModelComparison B S hS X) (eY := spacesEtaleModelComparison B S hS Y)
        (p := smallModelPostcomp B S hS j hj) (q := smallEtaleModelPostcomp B S hS j hj)
        (𝟙 (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleModelTopology B S hS X.1)
              (smallModelTopology B S hS X) (spacesEtaleModelComparison B S hS X)
              (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))))
          (𝟙 (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleModelTopology B S hS Y.1)
              (smallModelTopology B S hS Y) (spacesEtaleModelComparison B S hS Y)
              (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Y))))
          (smallModelPostcompSharp B S hS j hj)
        (spacesEtaleModelRestrictedPostcompSharp B S hS j hj)
        (spacesEtaleModelComparisonPostcompIso B S hS j hj)
          (spacesEtaleModelRestrictedPostcompSharp_square B S hS j hj) := rfl

/-- **Restrictions along postcomposition compose on the restricted structure sheaves**, through
`AlgebraicGeometry.Space.smallEtaleModelPostcompComp`. -/
def spacesEtaleModelRestrictedPushforwardComp :
    SheafOfModules.pushforward.{u} (spacesEtaleModelRestrictedPostcompSharp B S hS g hg) ⋙
        SheafOfModules.pushforward.{u} (spacesEtaleModelRestrictedPostcompSharp B S hS f hf) ≅
      SheafOfModules.pushforward.{u} (spacesEtaleModelRestrictedPostcompSharp B S hS (f ≫ g) hfg) :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (smallEtaleModelPostcompComp B S hS f g hf hg hfg).symm
      (spacesEtaleModelRestrictedPostcompSharp_comp B S hS f g hf hg hfg)

/-- `AlgebraicGeometry.Space.spacesEtaleModelComparisonPostcompIso_inv_app_comp` read through a
presheaf of abelian groups on the spaces-étale model of `Z`. -/
theorem spacesEtaleModelComparisonPostcompIso_inv_app_comp_apply
    (P : (SmallModel.{u} (SpacesEtale B S hS Z))ᵒᵖ ⥤ AddCommGrpCat.{u})
    (T : SmallModel.{u} (SmallEtale B S hS X.1)) (x) :
    P.map ((spacesEtaleModelComparison B S hS Z).map
        ((smallEtaleModelPostcompComp B S hS f g hf hg hfg).inv.app T)).op
      (P.map ((spacesEtaleModelComparisonPostcompIso B S hS g hg).inv.app
          ((smallEtaleModelPostcomp B S hS f hf).obj T)).op
        (P.map ((smallModelPostcomp B S hS g hg).map
          ((spacesEtaleModelComparisonPostcompIso B S hS f hf).inv.app T)).op x)) =
    P.map ((spacesEtaleModelComparisonPostcompIso B S hS (f ≫ g) hfg).inv.app T).op
      (P.map ((smallModelPostcompComp B S hS f g hf hg hfg).inv.app
        ((spacesEtaleModelComparison B S hS X).obj T)).op x) := by
  have h := congrArg (fun k => P.map k.op x)
    (spacesEtaleModelComparisonPostcompIso_inv_app_comp B S hS f g hf hg hfg T)
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at h
  exact h

/-- **Step A is compatible with composition**: the comparisons
`AlgebraicGeometry.Space.moduleRestrictionPostcompIso` for `f`, `g` and `f ≫ g` are compatible with
`AlgebraicGeometry.Space.smallModelPostcompPushforwardComp` and
`AlgebraicGeometry.Space.spacesEtaleModelRestrictedPushforwardComp`. On sections all of them are
restrictions, along morphisms that agree by
`AlgebraicGeometry.Space.spacesEtaleModelComparisonPostcompIso_inv_app_comp`. -/
theorem moduleRestrictionPostcompIso_comp (M : SheafOfModules.{u} (J := smallModelTopology B S hS Z)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Z).O)) :
    (Stacks.DenseSubsiteModules.moduleRestriction (smallEtaleModelTopology B S hS X.1)
        (smallModelTopology B S hS X) (spacesEtaleModelComparison B S hS X)
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))).map
        ((smallModelPostcompPushforwardComp B S hS f g hf hg hfg).hom.app M) ≫
      (moduleRestrictionPostcompIso B S hS (f ≫ g) hfg).hom.app M =
    (moduleRestrictionPostcompIso B S hS f hf).hom.app
        ((SheafOfModules.pushforward.{u} (smallModelPostcompSharp B S hS g hg)).obj M) ≫
      (SheafOfModules.pushforward.{u} (spacesEtaleModelRestrictedPostcompSharp B S hS f hf)).map
        ((moduleRestrictionPostcompIso B S hS g hg).hom.app M) ≫
      (spacesEtaleModelRestrictedPushforwardComp B S hS f g hf hg hfg).hom.app
        ((Stacks.DenseSubsiteModules.moduleRestriction (smallEtaleModelTopology B S hS Z.1)
          (smallModelTopology B S hS Z) (spacesEtaleModelComparison B S hS Z)
          (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS Z))).obj M) := by
  ext U x
  have e2 := smallModelPostcompPushforwardComp_hom_app_val_app B S hS f g hf hg hfg M
    (op ((spacesEtaleModelComparison B S hS X).obj U.unop)) x
  refine (congrArg
        (fun y => ((moduleRestrictionPostcompIso B S hS (f ≫ g) hfg).hom.app M).val.app U
          y) e2).trans ?_
  exact (spacesEtaleModelComparisonPostcompIso_inv_app_comp_apply B S hS f g hf hg hfg
    M.val.presheaf U.unop x).symm

/-- **Step C is compatible with composition**: the comparisons
`AlgebraicGeometry.Space.restrictScalarsRingRestrictionPostcompIso` (the identity on sections) for
`f`, `g` and `f ≫ g` are compatible with
`AlgebraicGeometry.Space.spacesEtaleModelRestrictedPushforwardComp` and
`AlgebraicGeometry.Space.smallEtaleModelPushforwardComp`. -/
theorem restrictScalarsRingRestrictionPostcompIso_comp
    (N : SheafOfModules.{u} (J := smallEtaleModelTopology B S hS Z.1)
      (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleModelTopology B S hS Z.1)
        (smallModelTopology B S hS Z) (spacesEtaleModelComparison B S hS Z)
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Z)))) :
    (SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS X).inv).map
        ((spacesEtaleModelRestrictedPushforwardComp B S hS f g hf hg hfg).hom.app N) ≫
      (restrictScalarsRingRestrictionPostcompIso B S hS (f ≫ g) hfg).hom.app N =
    (restrictScalarsRingRestrictionPostcompIso B S hS f hf).hom.app
        ((SheafOfModules.pushforward.{u}
              (spacesEtaleModelRestrictedPostcompSharp B S hS g hg)).obj N) ≫
      (SheafOfModules.pushforward.{u} (smallEtaleModelPostcompSharp B S hS f hf)).map
        ((restrictScalarsRingRestrictionPostcompIso B S hS g hg).hom.app N) ≫
      (smallEtaleModelPushforwardComp B S hS f g hf hg hfg).hom.app
        ((SheafOfModules.restrictScalars.{u}
              (spacesEtaleModelRingRestrictionIso B S hS Z).inv).obj N) := by
  ext U x
  rfl

/-- **The étale pullback on the spaces-étale models is compatible with composition**: the
identifications `AlgebraicGeometry.Space.spacesEtaleModelModulesEquivPostcompIso` of restriction
along postcomposition on the models with the étale pullback on the small étale sites, for `f`, `g`
and `f ≫ g`, are compatible with `AlgebraicGeometry.Space.smallModelPostcompPushforwardComp` and
`AlgebraicGeometry.Space.etaleModulePullbackComp`. -/
theorem spacesEtaleModelModulesEquivPostcompIso_comp
    (M : SheafOfModules.{u} (J := smallModelTopology B S hS Z)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Z).O)) :
    (spacesEtaleModelModulesEquiv B S hS X).functor.map
        ((smallModelPostcompPushforwardComp B S hS f g hf hg hfg).hom.app M) ≫
      (spacesEtaleModelModulesEquivPostcompIso B S hS (f ≫ g) hfg).hom.app M =
    (spacesEtaleModelModulesEquivPostcompIso B S hS f hf).hom.app
        ((SheafOfModules.pushforward.{u} (smallModelPostcompSharp B S hS g hg)).obj M) ≫
      (etaleModulePullback.{u, u} B S hS f hf).map
        ((spacesEtaleModelModulesEquivPostcompIso B S hS g hg).hom.app M) ≫
      (etaleModulePullbackComp B S hS f g hf hg hfg).hom.app
        ((spacesEtaleModelModulesEquiv B S hS Z).functor.obj M) :=
  comp_coherence_of_three_squares (spacesEtaleModelModulesEquiv_functor_eq B S hS X)
    (spacesEtaleModelModulesEquiv_functor_eq B S hS Y)
    (spacesEtaleModelModulesEquiv_functor_eq B S hS Z)
    (smallModelPostcompPushforwardComp B S hS f g hf hg hfg).hom
    (spacesEtaleModelRestrictedPushforwardComp B S hS f g hf hg hfg).hom
    (smallEtaleModelPushforwardComp B S hS f g hf hg hfg).hom
    (etaleModulePullbackComp B S hS f g hf hg hfg).hom
    (moduleRestrictionPostcompIso B S hS f hf) (moduleRestrictionPostcompIso B S hS g hg)
    (moduleRestrictionPostcompIso B S hS (f ≫ g) hfg)
    (restrictScalarsRingRestrictionPostcompIso B S hS f hf)
    (restrictScalarsRingRestrictionPostcompIso B S hS g hg)
    (restrictScalarsRingRestrictionPostcompIso B S hS (f ≫ g) hfg)
    (smallEtaleModelModulesEquivInversePostcompIso B S hS f hf)
    (smallEtaleModelModulesEquivInversePostcompIso B S hS g hg)
    (smallEtaleModelModulesEquivInversePostcompIso B S hS (f ≫ g) hfg)
    (moduleRestrictionPostcompIso_comp B S hS f g hf hg hfg)
    (restrictScalarsRingRestrictionPostcompIso_comp B S hS f g hf hg hfg)
    (smallEtaleModelModulesEquivInversePostcompIso_comp B S hS f g hf hg hfg)
    (spacesEtaleModelModulesEquivPostcompIso B S hS f hf)
    (spacesEtaleModelModulesEquivPostcompIso B S hS g hg)
    (spacesEtaleModelModulesEquivPostcompIso B S hS (f ≫ g) hfg) rfl rfl rfl M

/-- **The étale inverse images on the spaces-étale models are compatible with composition under
the identifications of Stacks 03G1**: the identifications of `j^*` on the models with the étale
pullback on the small étale sites (`AlgebraicGeometry.Space.spacesEtaleModelPullbackIsoPushforward`
followed by `AlgebraicGeometry.Space.spacesEtaleModelModulesEquivPostcompIso`), for `f`, `g` and
`f ≫ g`, are compatible with `AlgebraicGeometry.Space.spacesEtaleModelPullbackComp` and
`AlgebraicGeometry.Space.etaleModulePullbackComp`. -/
theorem spacesEtaleModelPullbackIsoPushforward_trans_modulesEquivPostcompIso_comp
    (M : SheafOfModules.{u} (J := smallModelTopology B S hS Z)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Z).O)) :
    (spacesEtaleModelModulesEquiv B S hS X).functor.map
        ((spacesEtaleModelPullbackComp B S hS f g).hom.app M) ≫
      (Functor.isoWhiskerRight (spacesEtaleModelPullbackIsoPushforward B S hS (f ≫ g) hfg)
          (spacesEtaleModelModulesEquiv B S hS X).functor ≪≫
        spacesEtaleModelModulesEquivPostcompIso B S hS (f ≫ g) hfg).hom.app M =
    (Functor.isoWhiskerRight (spacesEtaleModelPullbackIsoPushforward B S hS f hf)
          (spacesEtaleModelModulesEquiv B S hS X).functor ≪≫
        spacesEtaleModelModulesEquivPostcompIso B S hS f hf).hom.app
        ((spacesEtaleModelHom B S hS g).pullbackTopos.obj M) ≫
      (etaleModulePullback.{u, u} B S hS f hf).map
        ((Functor.isoWhiskerRight (spacesEtaleModelPullbackIsoPushforward B S hS g hg)
          (spacesEtaleModelModulesEquiv B S hS Y).functor ≪≫
        spacesEtaleModelModulesEquivPostcompIso B S hS g hg).hom.app M) ≫
      (etaleModulePullbackComp B S hS f g hf hg hfg).hom.app
        ((spacesEtaleModelModulesEquiv B S hS Z).functor.obj M) :=
  comp_coherence_isoWhiskerRight_trans (spacesEtaleModelPullbackIsoPushforward B S hS f hf)
    (spacesEtaleModelPullbackIsoPushforward B S hS g hg)
    (spacesEtaleModelPullbackIsoPushforward B S hS (f ≫ g) hfg)
    (spacesEtaleModelPullbackComp B S hS f g).hom
    (smallModelPostcompPushforwardComp B S hS f g hf hg hfg).hom
    (etaleModulePullbackComp B S hS f g hf hg hfg).hom
    (fun K => congrArg (fun e => e.hom.app K)
      (spacesEtaleModelPullbackComp_trans_pullbackIsoPushforward B S hS f g hf hg hfg))
    (spacesEtaleModelModulesEquivPostcompIso B S hS f hf)
    (spacesEtaleModelModulesEquivPostcompIso B S hS g hg)
    (spacesEtaleModelModulesEquivPostcompIso B S hS (f ≫ g) hfg)
    (spacesEtaleModelModulesEquivPostcompIso_comp B S hS f g hf hg hfg) M

end ModelRestrictionPostcompComp

end AlgebraicGeometry.Space

end
