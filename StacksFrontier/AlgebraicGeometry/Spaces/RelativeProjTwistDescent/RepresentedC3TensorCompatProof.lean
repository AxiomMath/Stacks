module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedSquareRightAdjointCompat
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ZariskiPullbackTensor

/-!
# The compatibility (b) of Stacks 084D: readings on the small étale site

Let `g : V ⟶ U` be a morphism of the big fppf site over `S` and `M`, `N` quasi-coherent modules
on the scheme underlying `U`. The compatibility `AlgebraicGeometry.Space.RepresentedC3TensorCompat`
of the identification `(M ⊗ N)_{yoneda U} ≅ M_{yoneda U} ⊗ N_{yoneda U}` with inverse images is
reduced here to identities on the small étale sites of the underlying schemes.

The identification `g^*(M_{yoneda U}) ≅ (g^*M)_{yoneda V}` of
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso` is defined by reflection from
the scheme underlying `V`; this file computes it on the small étale site: after the comparison of
the two factorizations of the square of `g`
(`AlgebraicGeometry.Space.representedSquareModulePullbackIso`) it is the comparison
`(r^*M)^a ≅ ε_g^*(M^a)` of Stacks 03LC (1) read on `yoneda.obj V`.

## Main results

* `representedSquareModulePullbackIso_hom_app_comp_modulePullbackRepresentedQuasicoherentIso_hom`:
  the identification `g^*(M^a) ≅ (g^*M)^a` on the small étale site.
* `AlgebraicGeometry.Space.tensorCompat_of_readings`: the abstract shape of the compatibility (b),
  at variables, from Stacks 03EL round the square of `g` and round the square of the underlying
  morphism of schemes.
* `AlgebraicGeometry.Space.pullbackModulesReindexIso_eq_representedReindexPullbackIso`: the two
  identifications of the pullback along the reindexing of Stacks 04M0 agree.
* `AlgebraicGeometry.Space.representedSquare_pullbackTensorIsoTransport_representedSquareMate`:
  Stacks 03EL round the square of `g` with the comparison of the two factorizations written as the
  inverse mate `AlgebraicGeometry.Space.representedSquareMate`, and
  `representedSquareMate_app_comp_modulePullbackRepresentedQuasicoherentIso_hom`: the
  identification `g^*(M^a) ≅ (g^*M)^a` read through the same mate.
* `AlgebraicGeometry.Space.tensorCompat_core_of_readings`: the core of the compatibility (b) at
  variables.

## Implementation notes

Every computation is an abstract lemma at variables, instantiated once with the base spellings:
`AlgebraicGeometry.Space.comp_eq_of_reading` for the identification on the small étale site
(the comparison of the factorizations entering as the inverse mate of
`AlgebraicGeometry.Space.representedModulePullbackIso`, at the spelling of
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`), and
`AlgebraicGeometry.Space.tensorSquare_inv_of_hom` for Stacks 03EL round the square of schemes
solved for the inverse of the comparison of the two routes.

The inverse mate enters every concrete statement as the single constant
`AlgebraicGeometry.Space.representedSquareMate`, typed as the comparison of the factorizations:
comparing two spellings of a component `θ.app X` makes the kernel evaluate the mate.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

section Abstract

/-- A square of comparisons with tensor products through a natural isomorphism `e`, solved
for the inverse of `e` (given in a second spelling `e'`). -/
theorem tensorSquare_inv_of_hom {C D : Type*} [Category C] [Category D] (T : D ⥤ D ⥤ D)
    {P Q : C ⥤ D} (e e' : P ≅ Q) (he : e = e') (F G K : C) {X₁ Y₁ : D}
    (a : P.obj K ⟶ X₁) (b : X₁ ⟶ (T.obj (P.obj F)).obj (P.obj G)) (c : Q.obj K ⟶ Y₁)
    (d : Y₁ ⟶ (T.obj (Q.obj F)).obj (Q.obj G))
    (h : a ≫ b ≫ (T.map (e.hom.app F)).app (P.obj G) ≫ (T.obj (Q.obj F)).map (e.hom.app G) =
      e.hom.app K ≫ c ≫ d) :
    c ≫ d ≫ (T.map (e'.inv.app F)).app (Q.obj G) ≫ (T.obj (P.obj F)).map (e'.inv.app G) =
      e'.inv.app K ≫ a ≫ b := by
  subst he
  have h' : c ≫ d = e.inv.app K ≫ a ≫ b ≫ (T.map (e.hom.app F)).app (P.obj G) ≫
      (T.obj (Q.obj F)).map (e.hom.app G) := by
    rw [h, Iso.inv_hom_id_app_assoc]
  have n : (T.obj (Q.obj F)).map (e.hom.app G) ≫ (T.map (e.inv.app F)).app (Q.obj G) =
      (T.map (e.inv.app F)).app (P.obj G) ≫ (T.obj (P.obj F)).map (e.hom.app G) :=
    (T.map (e.inv.app F)).naturality (e.hom.app G)
  rw [reassoc_of% h', reassoc_of% n, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Composing two pairs of arrows through a bifunctor `T`, in each variable, is `T` of the
composites. -/
private theorem map_app_comp_map_comp {D : Type*} [Category D] (T : D ⥤ D ⥤ D) {A B C A' B' C' : D}
    (f : A ⟶ B) (f' : B ⟶ C) (g : A' ⟶ B') (g' : B' ⟶ C') :
    (T.map f).app A' ≫ (T.obj B).map g ≫ (T.map f').app B' ≫ (T.obj C).map g' =
      (T.map (f ≫ f')).app A' ≫ (T.obj C).map (g ≫ g') := by
  rw [(T.map f').naturality_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    ← Functor.map_comp]

/-- The abstract shape of the compatibility (b), at variables. -/
theorem tensorCompat_of_readings {CX CY DU DV : Type*} [Category CX] [Category CY] [Category DU]
    [Category DV] (TX : CX ⥤ CX ⥤ CX) (TV : DV ⥤ DV ⥤ DV) (E : CX ⥤ DV) (EU : CY ⥤ DU)
    (Ac : CY ⥤ CX) (Phi : DU ⥤ DV) (θ : Ac ⋙ E ⟶ EU ⋙ Phi) [IsIso θ]
    {FY GY KY FGY : CY} (PY : KY ≅ FGY) {UT O0 : DU} (PU : EU.obj FGY ≅ UT) (wU : O0 ≅ UT)
    (TU : EU.obj KY ≅ O0) (hTU : TU = EU.mapIso PY ≪≫ PU ≪≫ wU.symm)
    {O1 : DV} (wV : O1 ≅ (TV.obj (Phi.obj (EU.obj FY))).obj (Phi.obj (EU.obj GY)))
    (pφ : Phi.obj UT ⟶ (TV.obj (Phi.obj (EU.obj FY))).obj (Phi.obj (EU.obj GY)))
    (f2 : Phi.obj O0 ⟶ O1) (hf2 : f2 = Phi.map wU.hom ≫ pφ ≫ wV.inv)
    (bct : Ac.obj FGY ⟶ (TX.obj (Ac.obj FY)).obj (Ac.obj GY))
    (pV : E.obj ((TX.obj (Ac.obj FY)).obj (Ac.obj GY)) ⟶
      (TV.obj (E.obj (Ac.obj FY))).obj (E.obj (Ac.obj GY)))
    (pU : EU.obj FGY ⟶ UT) (hpU : PU.hom = pU)
    (pφ' : Phi.obj UT ⟶ (TV.obj (Phi.obj (EU.obj FY))).obj (Phi.obj (EU.obj GY)))
    (hpφ : pφ' = pφ)
    (θ' : Ac ⋙ E ⟶ EU ⋙ Phi) (hθθ' : θ = θ')
    (hKF1 : E.map bct ≫ pV ≫ (TV.map (θ'.app FY)).app (E.obj (Ac.obj GY)) ≫
        (TV.obj (Phi.obj (EU.obj FY))).map (θ'.app GY) = θ'.app FGY ≫ Phi.map pU ≫ pφ')
    {xM xN xMN xMN' : CX} (mM : Ac.obj FY ⟶ xM) (mN : Ac.obj GY ⟶ xN) (mMN : Ac.obj KY ⟶ xMN)
    (cM : Phi.obj (EU.obj FY) ⟶ E.obj xM) (cN : Phi.obj (EU.obj GY) ⟶ E.obj xN)
    (cMN : Phi.obj (EU.obj KY) ⟶ E.obj xMN)
    (hcM : θ.app FY ≫ cM = E.map mM) (hcN : θ.app GY ≫ cN = E.map mN)
    (hcMN : θ.app KY ≫ cMN = E.map mMN)
    {O2 : DV} (wX : O2 ≅ (TV.obj (E.obj xM)).obj (E.obj xN)) (f3 : O1 ⟶ O2)
    (hf3 : f3 ≫ wX.hom = wV.hom ≫ (TV.map cM).app _ ≫ (TV.obj (E.obj xM)).map cN)
    (q : xMN ⟶ xMN') (g2 : E.obj xMN ⟶ E.obj xMN') (hg2 : g2 = E.map q)
    (PX : xMN' ≅ (TX.obj xM).obj xN)
    (PV2 : E.obj ((TX.obj xM).obj xN) ≅ (TV.obj (E.obj xM)).obj (E.obj xN))
    (TV' : E.obj xMN' ≅ O2) (hTV : TV' = E.mapIso PX ≪≫ PV2 ≪≫ wX.symm)
    (pV2 : E.obj ((TX.obj xM).obj xN) ⟶ (TV.obj (E.obj xM)).obj (E.obj xN))
    (hpV2 : PV2.hom = pV2)
    (hpV : E.map ((TX.map mM).app (Ac.obj GY) ≫ (TX.obj xM).map mN) ≫ pV2 =
      pV ≫ (TV.map (E.map mM)).app (E.obj (Ac.obj GY)) ≫ (TV.obj (E.obj xM)).map (E.map mN))
    (hKF2 : Ac.map PY.hom ≫ bct ≫ (TX.map mM).app (Ac.obj GY) ≫ (TX.obj xM).map mN =
      mMN ≫ q ≫ PX.hom) :
    Phi.map TU.hom ≫ f2 ≫ f3 = cMN ≫ g2 ≫ TV'.hom := by
  subst hTU hf2 hpU hpφ hg2 hTV hpV2 hθθ'
  replace hf3 : wV.inv ≫ f3 = (TV.map cM).app _ ≫ (TV.obj (E.obj xM)).map cN ≫ wX.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% hf3, Iso.hom_inv_id, Category.comp_id]
  rw [← cancel_epi (θ.app KY)]
  have h3 : θ.app KY ≫ Phi.map (EU.map PY.hom) = E.map (Ac.map PY.hom) ≫ θ.app FGY :=
    (θ.naturality PY.hom).symm
  have hb := map_app_comp_map_comp TV (θ.app FY) cM (θ.app GY) cN
  rw [hcM, hcN] at hb
  have hKF2' := congrArg E.map hKF2
  simp only [Functor.map_comp] at hKF2'
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% h3, hf3, ← reassoc_of% hKF1, reassoc_of% hb, ← reassoc_of% hpV,
    reassoc_of% hcMN]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hKF2']


/-- The core of the compatibility (b), at variables: Stacks 03EL round the square of `g`
(`hKF1`) and round the square of the underlying morphism of schemes (`hKF2`), joined through the
identifications `θ.app _ ≫ c = E.map m` of `g^*(M^a) ≅ (g^*M)^a` on the small étale site. -/
theorem tensorCompat_core_of_readings {CX CY DU DV : Type*} [Category CX] [Category CY]
    [Category DU] [Category DV] (TX : CX ⥤ CX ⥤ CX) (TV : DV ⥤ DV ⥤ DV) (E : CX ⥤ DV) (EU : CY ⥤ DU)
    (Ac : CY ⥤ CX) (Phi : DU ⥤ DV) (θ : Ac ⋙ E ⟶ EU ⋙ Phi) (hθiso : IsIso θ)
    {FY GY FGY : CY} {UT : DU}
    (bct : Ac.obj FGY ⟶ (TX.obj (Ac.obj FY)).obj (Ac.obj GY))
    (pV : E.obj ((TX.obj (Ac.obj FY)).obj (Ac.obj GY)) ⟶
      (TV.obj (E.obj (Ac.obj FY))).obj (E.obj (Ac.obj GY)))
    (pU : EU.obj FGY ⟶ UT)
    (pφ' : Phi.obj UT ⟶ (TV.obj (Phi.obj (EU.obj FY))).obj (Phi.obj (EU.obj GY)))
    (hKF1 : E.map bct ≫ pV ≫ (TV.map (θ.app FY)).app (E.obj (Ac.obj GY)) ≫
        (TV.obj (Phi.obj (EU.obj FY))).map (θ.app GY) = θ.app FGY ≫ Phi.map pU ≫ pφ')
    {KY : CY} (PY : KY ≅ FGY)
    {xM xN xMN xMN' : CX} (mM : Ac.obj FY ⟶ xM) (mN : Ac.obj GY ⟶ xN) (mMN : Ac.obj KY ⟶ xMN)
    (cM : Phi.obj (EU.obj FY) ⟶ E.obj xM) (cN : Phi.obj (EU.obj GY) ⟶ E.obj xN)
    (cMN : Phi.obj (EU.obj KY) ⟶ E.obj xMN)
    (hcM : θ.app FY ≫ cM = E.map mM) (hcN : θ.app GY ≫ cN = E.map mN)
    (hcMN : θ.app KY ≫ cMN = E.map mMN)
    (q : xMN ⟶ xMN') (PX : xMN' ≅ (TX.obj xM).obj xN)
    (pV2 : E.obj ((TX.obj xM).obj xN) ⟶ (TV.obj (E.obj xM)).obj (E.obj xN))
    (hpV : E.map ((TX.map mM).app (Ac.obj GY) ≫ (TX.obj xM).map mN) ≫ pV2 =
      pV ≫ (TV.map (E.map mM)).app (E.obj (Ac.obj GY)) ≫ (TV.obj (E.obj xM)).map (E.map mN))
    (hKF2 : Ac.map PY.hom ≫ bct ≫ (TX.map mM).app (Ac.obj GY) ≫ (TX.obj xM).map mN =
      mMN ≫ q ≫ PX.hom) :
    Phi.map (EU.map PY.hom) ≫ Phi.map pU ≫ pφ' ≫ (TV.map cM).app _ ≫
      (TV.obj (E.obj xM)).map cN = cMN ≫ E.map q ≫ E.map PX.hom ≫ pV2 := by
  have := hθiso
  rw [← cancel_epi (θ.app KY)]
  have h3 : θ.app KY ≫ Phi.map (EU.map PY.hom) = E.map (Ac.map PY.hom) ≫ θ.app FGY :=
    (θ.naturality PY.hom).symm
  have hb := map_app_comp_map_comp TV (θ.app FY) cM (θ.app GY) cN
  rw [hcM, hcN] at hb
  simp only [Functor.comp_obj] at hb
  have hKF2' := congrArg E.map hKF2
  simp only [Functor.map_comp] at hKF2'
  rw [reassoc_of% h3, ← reassoc_of% hKF1, hb, ← hpV, reassoc_of% hcMN]
  simp only [Category.assoc, Functor.map_comp]
  rw [reassoc_of% hKF2']

/-- The abstract shape of the description of the identification `g^*(M^a) ≅ (g^*M)^a` on
the small étale site, at variables. -/
theorem comp_eq_of_reading {ZX ZY CX CY DU DV : Type*} [Category ZX] [Category ZY]
    [Category CX] [Category CY] [Category DU] [Category DV]
    {εX : ZX ⥤ CX} {ρX : CX ⥤ ZX} (aX : εX ⊣ ρX) {εY : ZY ⥤ CY} {ρY : CY ⥤ ZY} (aY : εY ⊣ ρY)
    (eV : CX ≌ DV) (eU : CY ≌ DU) (Rz : ZY ⥤ ZX) (Ac : CY ⥤ CX) (Phi : DU ⥤ DV)
    (m : Rz ⋙ εX ≅ εY ⋙ Ac) (μ : Phi ⋙ eV.inverse ≅ eU.inverse ⋙ Ac) (M : ZY)
    [IsIso (aY.unit.app M)] [IsIso (aX.unit.app (Rz.obj M))]
    (C3 : Phi.obj (eU.functor.obj (εY.obj M)) ≅ eV.functor.obj (εX.obj (Rz.obj M)))
    (hinj : Function.Injective (fun ψ : eV.functor.obj (Ac.obj (εY.obj M)) ⟶
      eV.functor.obj (εX.obj (Rz.obj M)) => ρX.map (eV.inverse.map ψ)))
    (I1 : Rz.obj (ρY.obj (eU.inverse.obj (eU.functor.obj (εY.obj M)))) ≅
      ρX.obj (eV.inverse.obj (Phi.obj (eU.functor.obj (εY.obj M)))))
    (c1 : Rz.obj (ρY.obj (eU.inverse.obj (eU.functor.obj (εY.obj M)))) ≅
      ρX.obj (Ac.obj (eU.inverse.obj (eU.functor.obj (εY.obj M)))))
    (hI1 : I1 = c1 ≪≫ ρX.mapIso (μ.app (eU.functor.obj (εY.obj M))).symm)
    (hc1 : c1.hom = aX.unit.app _ ≫ ρX.map (m.hom.app (ρY.obj (eU.inverse.obj
      (eU.functor.obj (εY.obj M)))) ≫ Ac.map (aY.counit.app _)))
    (c0 : Rz.obj (ρY.obj (εY.obj M)) ≅ ρX.obj (Ac.obj (εY.obj M)))
    (hc0 : c0.hom = aX.unit.app _ ≫ ρX.map (m.hom.app (ρY.obj (εY.obj M)) ≫
      Ac.map (aY.counit.app _)))
    (I2 : ρY.obj (eU.inverse.obj (eU.functor.obj (εY.obj M))) ≅ M)
    (hI2 : I2 = ρY.mapIso (eU.unitIso.app (εY.obj M)).symm ≪≫ (asIso (aY.unit.app M)).symm)
    (I3 : ρX.obj (eV.inverse.obj (eV.functor.obj (εX.obj (Rz.obj M)))) ≅ Rz.obj M)
    (hI3 : I3 = ρX.mapIso (eV.unitIso.app (εX.obj (Rz.obj M))).symm ≪≫
      (asIso (aX.unit.app (Rz.obj M))).symm)
    (hC3 : ρX.mapIso (eV.inverse.mapIso C3) = I1.symm ≪≫ Rz.mapIso I2 ≪≫ I3.symm)
    (θ : Ac ⋙ eV.functor ⟶ eU.functor ⋙ Phi)
    (hθ : θ = (mateEquiv eU.toAdjunction eV.toAdjunction).symm μ.inv) :
    θ.app (εY.obj M) ≫ C3.hom = eV.functor.map (m.inv.app M) := by
  subst hI2 hI3 hθ
  have hθ : ((mateEquiv eU.toAdjunction eV.toAdjunction).symm μ.inv).app (εY.obj M) =
      eV.functor.map (Ac.map (eU.unit.app (εY.obj M))) ≫
        eV.functor.map (μ.inv.app (eU.functor.obj (εY.obj M))) ≫
          eV.counit.app (Phi.obj (eU.functor.obj (εY.obj M))) := by
    simp [mateEquiv]
  -- the étale identity
  have hα : eV.inverse.map (((mateEquiv eU.toAdjunction eV.toAdjunction).symm μ.inv).app
        (εY.obj M)) ≫ μ.hom.app (eU.functor.obj (εY.obj M)) ≫
        Ac.map (eU.unitIso.inv.app (εY.obj M)) = eV.unitIso.inv.app (Ac.obj (εY.obj M)) := by
    rw [hθ]
    simp only [Functor.map_comp, Category.assoc]
    have n1 := eV.unitInv.naturality (μ.inv.app (eU.functor.obj (εY.obj M)))
    have n2 := eV.unitInv.naturality (Ac.map (eU.unit.app (εY.obj M)))
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at n1 n2
    rw [← Equivalence.unitInv_app_inverse, reassoc_of% n1, reassoc_of% n2]
    simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp]
    simp
  -- the Zariski identity
  have hβ : Rz.map (aY.unit.app M) ≫ c0.hom ≫ ρX.map (m.inv.app M) = aX.unit.app (Rz.obj M) := by
    have n1 : aX.unit.app (Rz.obj M) ≫ ρX.map (εX.map (Rz.map (aY.unit.app M))) =
        Rz.map (aY.unit.app M) ≫ aX.unit.app _ :=
      (aX.unit.naturality (Rz.map (aY.unit.app M))).symm
    have hcx : εX.map (Rz.map (aY.unit.app M)) ≫ (m.hom.app (ρY.obj (εY.obj M)) ≫
        Ac.map (aY.counit.app _)) ≫ m.inv.app M = 𝟙 _ := by
      have hm := m.hom.naturality (aY.unit.app M)
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at hm
      simp only [← Category.assoc]
      rw [hm]
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc, aY.left_triangle_components, CategoryTheory.Functor.map_id,
        Category.id_comp, Iso.hom_inv_id_app]
      rfl
    rw [hc0, Category.assoc, ← reassoc_of% n1, ← Functor.map_comp, ← Functor.map_comp, hcx]
    simp
  -- naturality of the comparison
  have hγ : Rz.map (ρY.map (eU.unitIso.inv.app (εY.obj M))) ≫ c0.hom =
      c1.hom ≫ ρX.map (Ac.map (eU.unitIso.inv.app (εY.obj M))) := by
    have n2 : aX.unit.app _ ≫ ρX.map (εX.map (Rz.map (ρY.map (eU.unitIso.inv.app (εY.obj M))))) =
        Rz.map (ρY.map (eU.unitIso.inv.app (εY.obj M))) ≫ aX.unit.app _ :=
      (aX.unit.naturality (Rz.map (ρY.map (eU.unitIso.inv.app (εY.obj M))))).symm
    have hcx : εX.map (Rz.map (ρY.map (eU.unitIso.inv.app (εY.obj M)))) ≫
        (m.hom.app (ρY.obj (εY.obj M)) ≫ Ac.map (aY.counit.app _)) =
        (m.hom.app (ρY.obj (eU.inverse.obj (eU.functor.obj (εY.obj M)))) ≫
          Ac.map (aY.counit.app _)) ≫ Ac.map (eU.unitIso.inv.app (εY.obj M)) := by
      have hm := m.hom.naturality (ρY.map (eU.unitIso.inv.app (εY.obj M)))
      have hk := aY.counit_naturality (eU.unitIso.inv.app (εY.obj M))
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at hm hk
      rw [reassoc_of% hm, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hk]
    rw [hc0, hc1, ← reassoc_of% n2, Category.assoc, ← Functor.map_comp, hcx, Functor.map_comp]
  have hfin : eV.inverse.map (((mateEquiv eU.toAdjunction eV.toAdjunction).symm μ.inv).app
        (εY.obj M)) ≫ μ.hom.app (eU.functor.obj (εY.obj M)) ≫
        Ac.map (eU.unitIso.inv.app (εY.obj M)) ≫ m.inv.app M ≫
          eV.unitIso.hom.app (εX.obj (Rz.obj M)) =
      eV.inverse.map (eV.functor.map (m.inv.app M)) := by
    have n3 := eV.unitIso.hom.naturality (m.inv.app M)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, Functor.comp_map] at n3
    rw [n3, reassoc_of% hα, Iso.inv_hom_id_app_assoc]
  have hC3' := congrArg Iso.hom hC3
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, asIso_hom, asIso_inv, Iso.app_hom, Iso.app_inv] at hC3'
  have hI1' : I1.inv = ρX.map (μ.hom.app (eU.functor.obj (εY.obj M))) ≫ c1.inv := by
    rw [hI1]
    simp
  have hγ' : c1.inv ≫ Rz.map (ρY.map (eU.unitIso.inv.app (εY.obj M))) =
      ρX.map (Ac.map (eU.unitIso.inv.app (εY.obj M))) ≫ c0.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hγ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hβ' : c0.inv ≫ Rz.map (inv (aY.unit.app M)) ≫ aX.unit.app (Rz.obj M) =
      ρX.map (m.inv.app M) := by
    rw [← hβ, ← Functor.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_assoc]
  apply hinj
  dsimp only
  rw [← hfin, Functor.map_comp, Functor.map_comp, hC3', hI1']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hγ', reassoc_of% hβ']

end Abstract

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A comparison read through the identity identification, written out, is the comparison. -/
theorem transport_refl_hom {C D : Type*} [Category C] [Category D] (T : D ⥤ D ⥤ D) (L : C ⥤ D)
    (G G' X : C) (e : L.obj X ≅ (T.obj (L.obj G)).obj (L.obj G')) :
    ((Iso.refl L).symm.app X ≪≫ e ≪≫ (T.mapIso ((Iso.refl L).app G)).app (L.obj G') ≪≫
      (T.obj (L.obj G)).mapIso ((Iso.refl L).app G')).hom = e.hom := by
  simp

/-- Stacks 03EL for a morphism of algebraic spaces, transported along the identity, is Stacks
03EL. -/
theorem pullbackTensorIsoTransport_refl_hom_space {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G G' : Modules.{u, u} B S hS Y.1 Y.2) :
    (Stacks.SheafOfModules.pullbackTensorIsoTransport (smallEtaleRingedToposModulesHom B S hS f)
          (Iso.refl _) G G').hom =
      ((Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS f)).app
        (G, G')).hom :=
  transport_refl_hom _ _ _ _ _ _

/-- The two identifications of the pullback along the reindexing of Stacks 04M0 with the functor
of the comparison agree: both are comparisons of left adjoints of the same direct image. -/
theorem pullbackModulesReindexIso_eq_representedReindexPullbackIso (U : BigFppfOver B S hS) :
    Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U) =
    representedReindexPullbackIso B S hS U :=
  Iso.ext (Adjunction.leftAdjointUniq_trans _ _ _)

/-- Reading on the scheme underlying `V` is injective on morphisms out of the module attached to
the small étale pullback of `M^a`. -/
theorem injective_representedZariski_map_modulePullback {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    Function.Injective (fun ψ : (representedSmallEtaleModuleEquivalence B S hS V).functor.obj
        ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M.obj)) ⟶
        (representedSmallEtaleModuleEquivalence B S hS V).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj
            ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) g.left)).obj M.obj)) =>
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map ψ)) :=
  (QuasiCoherentDescent.bijective_representedZariski_map B S hS _ _
    ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS V _).2
      (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
        (associatedBigEtaleSite B) g.left _
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
          U.left.property).functor.obj M).property))).1


/-- `AlgebraicGeometry.Space.representedSquareModulePullbackIso_hom_eq` with the comparisons of
Stacks 04M0 and Stacks 03LU in the spelling of their definitions. -/
theorem representedSquareModulePullbackIso_hom_eq_mateEquiv {V U : BigFppfOver B S hS}
    (g : V ⟶ U) :
    (representedSquareModulePullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)).hom =
      (mateEquiv (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction
        (representedSmallEtaleModuleEquivalence B S hS V).toAdjunction).symm
        (representedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)).inv :=
  representedSquareModulePullbackIso_hom_eq B S hS g (relativelyRepresentable_yoneda_map B S hS g)

/-- **The identification `g^*(M_{yoneda U}) ≅ (g^*M)_{yoneda V}` on the small étale site.**  After
the comparison of the two factorizations of the square of `g`, the identification
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso` is the comparison
`(r^*M)^a ≅ ε_g^*(M^a)` of Stacks 03LC (1), inverted, read on `yoneda.obj V`. -/
theorem
    representedSquareModulePullbackIso_hom_app_comp_modulePullbackRepresentedQuasicoherentIso_hom
    {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (representedSquareModulePullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)).hom.app
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M.obj) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom =
    (representedSmallEtaleModuleEquivalence B S hS V).functor.map
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
        (associatedBigEtaleSite B) g.left).inv.app M.obj) := by
  have := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property M
  have : IsIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj V) V.left.property).unit.app
      ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) g.left)).obj M.obj)) :=
    _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property (quasicoherentPullbackObj B S hS g M)
  have hq : ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M.obj).IsQuasicoherentOnSite :=
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence' (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).functor.obj M).property
  have hF : ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
            M.obj)).IsQuasicoherentOnSite :=
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property
  refine comp_eq_of_reading
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedSmallEtaleModuleEquivalence B S hS V)
    (representedSmallEtaleModuleEquivalence B S hS U)
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) g.left))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g))
    (modulePullback B S hS (representedSpaceMap B S hS g))
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso (associatedBigEtaleSite B)
      g.left)
    (representedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
    M.obj (modulePullbackRepresentedQuasicoherentIso B S hS g M) ?hinj
    (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
      ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M.obj)) hF)
    (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso (associatedBigEtaleSite B)
      g.left _ (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS U _ hF))
    rfl ?hc1
    (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso (associatedBigEtaleSite B)
      g.left _ hq) ?hc0
    (representedZariskiModuleQuasicoherentSchemeIso B S hS U M) ?hI2
    (representedZariskiModuleQuasicoherentSchemeIso B S hS V (quasicoherentPullbackObj B S hS g M))
    ?hI3 ?hC3 _ (representedSquareModulePullbackIso_hom_eq_mateEquiv B S hS g)
  case hinj => exact injective_representedZariski_map_modulePullback B S hS g M
  case hc1 => exact rfl
  case hc0 => exact rfl
  case hI2 => exact rfl
  case hI3 => exact rfl
  case hC3 => exact representedZariski_mapIso_modulePullbackRepresentedQuasicoherentIso B S hS g M



/-- The inverse mate of `AlgebraicGeometry.Space.representedModulePullbackIso` along the
equivalences of Stacks 04M0, with its type spelled as that of the comparison of the two
factorizations of the square of `g` (`Stacks.SheafOfModules.factorizationPullbackIso`), so that
it enters the statements about that comparison without a change of spelling. -/
def representedSquareMate {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of% (Stacks.SheafOfModules.factorizationPullbackIso
    (representedReindexHom B S hS V) (representedSchemeBaseChangeHom B S hS g)
    (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
    (representedReindexHom B S hS U) (representedSquareHom B S hS g) (Iso.refl _)
    (fSharpSetComp_representedSquareHom B S hS g)
    (representedSquareDirectImageIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
    (fSharpSetComp_representedSquareDirectImageIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g))
    (representedReindexPullbackIso B S hS V)
    (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
    (representedReindexPullbackIso B S hS U)).hom :=
  ((mateEquiv (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction
        (representedSmallEtaleModuleEquivalence B S hS V).toAdjunction).symm
        (representedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)).inv)

/-- The comparison of the two factorizations of the square of `g` is
`AlgebraicGeometry.Space.representedSquareMate`. -/
theorem factorizationPullbackIso_hom_eq_representedSquareMate {V U : BigFppfOver B S hS}
    (g : V ⟶ U) :
    (Stacks.SheafOfModules.factorizationPullbackIso
    (representedReindexHom B S hS V) (representedSchemeBaseChangeHom B S hS g)
    (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
    (representedReindexHom B S hS U) (representedSquareHom B S hS g) (Iso.refl _)
    (fSharpSetComp_representedSquareHom B S hS g)
    (representedSquareDirectImageIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
    (fSharpSetComp_representedSquareDirectImageIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g))
    (representedReindexPullbackIso B S hS V)
    (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
    (representedReindexPullbackIso B S hS U)).hom = representedSquareMate B S hS g :=
  representedSquareModulePullbackIso_hom_eq_mateEquiv B S hS g

/-- Stacks 03EL round the square of `g`, with the comparison of the two factorizations written as
`AlgebraicGeometry.Space.representedSquareMate`. -/
theorem representedSquare_pullbackTensorIsoTransport_representedSquareMate
    {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    type_of%
      (Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso_of_hom_eq
      (representedReindexHom B S hS V) (representedSchemeBaseChangeHom B S hS g)
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
      (representedReindexHom B S hS U) (representedSquareHom B S hS g) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS g)
      (representedSquareDirectImageIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
      (fSharpSetComp_representedSquareDirectImageIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g))
      (representedReindexPullbackIso B S hS V)
      (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
      (representedReindexPullbackIso B S hS U)
      (representedSquareMate B S hS g)
      (factorizationPullbackIso_hom_eq_representedSquareMate B S hS g) M N) :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso_of_hom_eq
      (representedReindexHom B S hS V) (representedSchemeBaseChangeHom B S hS g)
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
      (representedReindexHom B S hS U) (representedSquareHom B S hS g) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS g)
      (representedSquareDirectImageIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
      (fSharpSetComp_representedSquareDirectImageIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g))
      (representedReindexPullbackIso B S hS V)
      (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
      (representedReindexPullbackIso B S hS U)
      (representedSquareMate B S hS g)
      (factorizationPullbackIso_hom_eq_representedSquareMate B S hS g) M N

/-- `AlgebraicGeometry.Space.representedSquareModulePullbackIso` is
`AlgebraicGeometry.Space.representedSquareMate`. -/
theorem representedSquareModulePullbackIso_hom_eq_representedSquareMate
    {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    (representedSquareModulePullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)).hom =
      representedSquareMate B S hS g :=
  factorizationPullbackIso_hom_eq_representedSquareMate B S hS g

/-- `AlgebraicGeometry.Space.representedSquareMate` is an isomorphism. -/
theorem isIso_representedSquareMate {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    IsIso (representedSquareMate B S hS g) := by
  have := Iso.isIso_hom
    (representedSquareModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
  rw [representedSquareModulePullbackIso_hom_eq_representedSquareMate] at this
  exact this

/-- The identification `g^*(M^a) ≅ (g^*M)^a` on the small étale site, after
`AlgebraicGeometry.Space.representedSquareMate`. -/
theorem representedSquareMate_app_comp_modulePullbackRepresentedQuasicoherentIso_hom
    {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (representedSquareMate B S hS g).app
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M.obj) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom =
    (representedSmallEtaleModuleEquivalence B S hS V).functor.map
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
        (associatedBigEtaleSite B) g.left).inv.app M.obj) := by
  have h :=
    representedSquareModulePullbackIso_hom_app_comp_modulePullbackRepresentedQuasicoherentIso_hom
      B S hS g M
  rw [representedSquareModulePullbackIso_hom_eq_representedSquareMate] at h
  exact h

/-- The comparison of Stacks 03EL for the reindexing of `U`, read through
`Stacks.SheafOfModules.pullbackModulesReindexIso`, is the one read through
`AlgebraicGeometry.Space.representedReindexPullbackIso`. -/
theorem pullbackTensorIsoTransport_pullbackModulesReindexIso_hom (U : BigFppfOver B S hS)
    (F G : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    (Stacks.SheafOfModules.pullbackTensorIsoTransport
      (Stacks.SheafOfModules.reindexRingedToposModulesHom
        (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U))
      (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U)) F G).hom =
    (Stacks.SheafOfModules.pullbackTensorIsoTransport (representedReindexHom B S hS U)
      (representedReindexPullbackIso B S hS U) F G).hom := by
  rw [pullbackModulesReindexIso_eq_representedReindexPullbackIso]
  rfl

end AlgebraicGeometry.Space

end
