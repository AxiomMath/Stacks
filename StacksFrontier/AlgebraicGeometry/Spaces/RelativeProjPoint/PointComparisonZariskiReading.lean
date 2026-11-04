module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PullRestrictionTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.RestrictionIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModule

/-!
# The scheme restriction maps of Stacks 084A are the Zariski readings of Stacks 03LU

For a morphism `τ : T' ⟶ T` of the site and a scheme point `f` of an algebraic space `X` at `T`,
the comparison `τ^*(f^*𝒜) ⟶ (f ∘ τ)^*𝒜` of restricted algebras
(`AlgebraicGeometry.Space.pointComparison`) is the adjoint transpose of the Zariski reading of an
étale restriction map.  On the other hand the inverse image along the represented morphism `φ` of
a quasi-coherent `𝒪`-module `N` on `yoneda.obj T`, read on the scheme of `T'`, is compared with
the pullback of the reading of `N` by the base comparison
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`.  This file relates the two.

The comparisons are mates: the comparison of restricted algebras is the mate of the identification
`AlgebraicGeometry.Space.zariskiDirectImageNatTrans` of the Zariski reading of a direct image, and
the base comparison is assembled from the comparison
`AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso` of restriction with pullback — whose
transpose is computed here
(`AlgebraicGeometry.SmallEtale.homEquiv_restrictModulePullbackObjIso_hom`) — and the identification
`AlgebraicGeometry.Space.representedModulePullbackIso` of the small étale sites.  The relation is
reduced to an identity of comparisons of direct images by an abstract mate computation
(`CategoryTheory.Adjunction.comp_homEquiv_symm_eq_of_rightAdjointSquare`).

## Main results

* `CategoryTheory.Adjunction.homEquiv_unit_comp_map_leftAdjointUniq_comp_counit`: the transpose of
  the Beck–Chevalley comparison built from a comparison of composite left adjoints.
* `CategoryTheory.Adjunction.comp_homEquiv_symm_eq_of_rightAdjointSquare`: the abstract mate
  computation.
* `AlgebraicGeometry.SmallEtale.homEquiv_restrictModulePullbackObjIso_hom`: **the transpose of
  `r^*(𝒢|_{Y_Zar}) ≅ (ε_a^*𝒢)|_{X_Zar}` along `r^* ⊣ r_*`** is the restriction of the unit of
  `ε_a^* ⊣ ε_{a*}` followed by the comparison of the two routes of direct images.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Adjunction

section Mates

variable {Zy Zx Ey Ex : Type*} [Category* Zy] [Category* Zx] [Category* Ey] [Category* Ex]
  {Fa : Zy ⥤ Zx} {Ga : Zx ⥤ Zy} {Fb : Zx ⥤ Ex} {Gb : Ex ⥤ Zx} {Fc : Zy ⥤ Ey} {Gc : Ey ⥤ Zy}
  {Fd : Ey ⥤ Ex} {Gd : Ex ⥤ Ey}

/-- **The transpose of the Beck–Chevalley comparison of a square of left adjoints.**  Let the two
routes `Fa ⋙ Fb` and `Fc ⋙ Fd` round a square of left adjoints be identified as the left adjoints
of the two routes of right adjoints, these being identified by `ρ`.  The comparison
`Fa (Gc G) ⟶ Gb (Fd G)` built from the unit of `Fb ⊣ Gb`, the identification of the left adjoints
and the counit of `Fc ⊣ Gc` is, transposed along `Fa ⊣ Ga`, the image under `Gc` of the unit of
`Fd ⊣ Gd` followed by `ρ`. -/
theorem homEquiv_unit_comp_map_leftAdjointUniq_comp_counit (aa : Fa ⊣ Ga) (ab : Fb ⊣ Gb)
    (ac : Fc ⊣ Gc) (ad : Fd ⊣ Gd) (ρ : Gd ⋙ Gc ≅ Gb ⋙ Ga) (G : Ey) :
    aa.homEquiv _ _ (ab.unit.app (Fa.obj (Gc.obj G)) ≫
        Gb.map ((leftAdjointUniq (aa.comp ab) ((ac.comp ad).ofNatIsoRight ρ)).hom.app
          (Gc.obj G) ≫ Fd.map (ac.counit.app G))) =
      Gc.map (ad.unit.app G) ≫ ρ.hom.app (Fd.obj G) := by
  have hu := unit_leftAdjointUniq_hom_app (aa.comp ab) ((ac.comp ad).ofNatIsoRight ρ) (Gc.obj G)
  have hou : ((ac.comp ad).ofNatIsoRight ρ).unit.app (Gc.obj G) =
      (ac.comp ad).unit.app (Gc.obj G) ≫ ρ.hom.app _ := by
    simp [Adjunction.ofNatIsoRight]
  rw [hou, comp_unit_app, comp_unit_app] at hu
  have hu' : aa.unit.app (Gc.obj G) ≫ Ga.map (ab.unit.app (Fa.obj (Gc.obj G))) ≫
      Ga.map (Gb.map ((leftAdjointUniq (aa.comp ab) ((ac.comp ad).ofNatIsoRight ρ)).hom.app
        (Gc.obj G))) =
      ac.unit.app (Gc.obj G) ≫ Gc.map (ad.unit.app (Fc.obj (Gc.obj G))) ≫
        ρ.hom.app (Fd.obj (Fc.obj (Gc.obj G))) := by
    simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj] using hu
  have hn : Gc.map (Gd.map (Fd.map (ac.counit.app G))) ≫ ρ.hom.app (Fd.obj G) =
      ρ.hom.app (Fd.obj (Fc.obj (Gc.obj G))) ≫ Ga.map (Gb.map (Fd.map (ac.counit.app G))) := by
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] using
      ρ.hom.naturality (Fd.map (ac.counit.app G))
  rw [homEquiv_unit, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  calc aa.unit.app (Gc.obj G) ≫ Ga.map (ab.unit.app (Fa.obj (Gc.obj G))) ≫
        Ga.map (Gb.map ((leftAdjointUniq (aa.comp ab) ((ac.comp ad).ofNatIsoRight ρ)).hom.app
          (Gc.obj G))) ≫ Ga.map (Gb.map (Fd.map (ac.counit.app G)))
      = (ac.unit.app (Gc.obj G) ≫ Gc.map (ad.unit.app (Fc.obj (Gc.obj G))) ≫
          ρ.hom.app (Fd.obj (Fc.obj (Gc.obj G)))) ≫
          Ga.map (Gb.map (Fd.map (ac.counit.app G))) := by
        rw [← hu']; simp only [Category.assoc]
    _ = ac.unit.app (Gc.obj G) ≫ Gc.map (ad.unit.app (Fc.obj (Gc.obj G)) ≫
          Gd.map (Fd.map (ac.counit.app G))) ≫ ρ.hom.app (Fd.obj G) := by
        rw [Functor.map_comp, Category.assoc, Category.assoc, Category.assoc, hn]
    _ = Gc.map (ad.unit.app G) ≫ ρ.hom.app (Fd.obj G) := by simp

end Mates

section RightAdjointSquare

variable {M M' Ec Ec' Z Z' : Type*} [Category* M] [Category* M'] [Category* Ec] [Category* Ec']
  [Category* Z] [Category* Z']
  {φs : M ⥤ M'} {φp : M' ⥤ M} {gs : Ec ⥤ Ec'} {gp : Ec' ⥤ Ec} {τs : Z ⥤ Z'} {τp : Z' ⥤ Z}
  {Ei : M ⥤ Ec} {Ef : Ec ⥤ M} {Ei' : M' ⥤ Ec'} {zR : M ⥤ Z} {zR' : M' ⥤ Z'}

/-- **The abstract mate computation behind the Zariski reading of the comparisons of restricted
algebras.**  Let `φs ⊣ φp`, `gs ⊣ gp` and `τs ⊣ τp` be adjunctions, `Ei ⊣ Ef` a further one, and
`zR ≅ Ei ⋙ r`, `zR' ≅ Ei' ⋙ r'` two readings.  Let `zDI : φp ⋙ zR ⟶ zR' ⋙ τp` be a comparison of
the readings of direct images and `R1 : gp ⋙ r ≅ r' ⋙ τp` a comparison of the two routes of
direct images, compatible with `zDI` through `Q` (hypothesis `hH`).  Then the mate of `zDI` at
`N`, read through `ι`, is any comparison `c` whose transpose is `r` of the unit of `gs ⊣ gp`
followed by `R1` (hypothesis `hA`), followed by any `μ` whose `Ei ⊣ Ef`-transpose, after the unit
of `gs ⊣ gp`, is the unit of `φs ⊣ φp` followed by `Q` (hypothesis `hII`). -/
theorem comp_homEquiv_symm_eq_of_rightAdjointSquare (aφ : φs ⊣ φp) (ag : gs ⊣ gp)
    (aτ : τs ⊣ τp) (aE : Ei ⊣ Ef) (r : Ec ⥤ Z) (r' : Ec' ⥤ Z') (ι : Ei ⋙ r ≅ zR)
    (ι' : Ei' ⋙ r' ≅ zR') (zDI : φp ⋙ zR ⟶ zR' ⋙ τp) (R1 : gp ⋙ r ≅ r' ⋙ τp)
    (Q : ∀ M₀ : M', φp.obj M₀ ⟶ Ef.obj (gp.obj (Ei'.obj M₀)))
    (hH : ∀ M₀ : M', ι.hom.app (φp.obj M₀) ≫ zDI.app M₀ =
      r.map (Ei.map (Q M₀) ≫ aE.counit.app (gp.obj (Ei'.obj M₀))) ≫
        R1.hom.app (Ei'.obj M₀) ≫ τp.map (ι'.hom.app M₀))
    (N : M) (c : τs.obj (r.obj (Ei.obj N)) ⟶ r'.obj (gs.obj (Ei.obj N)))
    (hA : aτ.homEquiv _ _ c = r.map (ag.unit.app (Ei.obj N)) ≫ R1.hom.app (gs.obj (Ei.obj N)))
    (μ : gs.obj (Ei.obj N) ⟶ Ei'.obj (φs.obj N))
    (hII : aE.unit.app N ≫ Ef.map (ag.unit.app (Ei.obj N) ≫ gp.map μ) =
      aφ.unit.app N ≫ Q (φs.obj N)) :
    τs.map (ι.hom.app N) ≫
        (aτ.homEquiv _ _).symm (zR.map (aφ.unit.app N) ≫ zDI.app (φs.obj N)) =
      c ≫ r'.map μ ≫ ι'.hom.app (φs.obj N) := by
  apply (aτ.homEquiv _ _).injective
  rw [homEquiv_naturality_left, Equiv.apply_symm_apply, homEquiv_naturality_right]
  have hA' : aτ.homEquiv ((Ei ⋙ r).obj N) _ c =
      r.map (ag.unit.app (Ei.obj N)) ≫ R1.hom.app (gs.obj (Ei.obj N)) := hA
  have hX : ag.unit.app (Ei.obj N) ≫ gp.map μ =
      Ei.map (aφ.unit.app N ≫ Q (φs.obj N)) ≫ aE.counit.app _ := by
    rw [← (aE.homEquiv _ _).symm_apply_apply (ag.unit.app (Ei.obj N) ≫ gp.map μ),
      aE.homEquiv_unit, hII, aE.homEquiv_counit]
  have e1 : ι.hom.app N ≫ zR.map (aφ.unit.app N) ≫ zDI.app (φs.obj N) =
      r.map (Ei.map (aφ.unit.app N ≫ Q (φs.obj N)) ≫ aE.counit.app _) ≫
        R1.hom.app _ ≫ τp.map (ι'.hom.app (φs.obj N)) := by
    rw [← Category.assoc, ← ι.hom.naturality, Category.assoc,
      show ι.hom.app ((φs ⋙ φp).obj N) ≫ zDI.app (φs.obj N) = _ from hH (φs.obj N)]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  have hR : R1.hom.app (gs.obj (Ei.obj N)) ≫ τp.map (r'.map μ) =
      r.map (gp.map μ) ≫ R1.hom.app (Ei'.obj (φs.obj N)) := by
    simpa only [Functor.comp_map] using (R1.hom.naturality μ).symm
  have e2 : (r.map (ag.unit.app (Ei.obj N)) ≫ R1.hom.app (gs.obj (Ei.obj N))) ≫
      τp.map (r'.map μ ≫ ι'.hom.app (φs.obj N)) =
      r.map (ag.unit.app (Ei.obj N) ≫ gp.map μ) ≫ R1.hom.app _ ≫
        τp.map (ι'.hom.app (φs.obj N)) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, ← Category.assoc (R1.hom.app _), hR,
      Category.assoc, Category.assoc]
  rw [hA', e1, e2, hX]

/-- The adjunct square of a comparison `ρ : φs ⋙ Ei' ≅ Ei ⋙ gs` of two composite left adjoints,
read at one object: the unit of `Ei ⊣ Ef`, followed by the image of the unit of `gs ⊣ gp` and of
`gp ρ⁻¹`, is the unit of `φs ⊣ φpm` followed by the image of the unit of `Ei' ⊣ Ef'` and the
inverse of the comparison `P` of the two composite right adjoints. -/
theorem unit_comp_map_unit_comp_map_eq_of_unit_comp_whiskerRight {Ef' : Ec' ⥤ M'} {φpm : M' ⥤ M}
    (aE : Ei ⊣ Ef) (ag : gs ⊣ gp) (aφm : φs ⊣ φpm) (aE' : Ei' ⊣ Ef')
    (P : gp ⋙ Ef ≅ Ef' ⋙ φpm) (ρ : φs ⋙ Ei' ≅ Ei ⋙ gs)
    (h : ((aE.comp ag).ofNatIsoRight P).unit ≫ whiskerRight ρ.inv (Ef' ⋙ φpm) =
      (aφm.comp aE').unit) (N : M) :
    aE.unit.app N ≫ Ef.map (ag.unit.app (Ei.obj N) ≫ gp.map (ρ.inv.app N)) =
      aφm.unit.app N ≫ φpm.map (aE'.unit.app (φs.obj N)) ≫ P.inv.app (Ei'.obj (φs.obj N)) := by
  have h' := NatTrans.congr_app h N
  have hou : ((aE.comp ag).ofNatIsoRight P).unit.app N =
      (aE.comp ag).unit.app N ≫ P.hom.app _ := by
    simp [Adjunction.ofNatIsoRight]
  simp only [NatTrans.comp_app, hou, comp_unit_app, Functor.whiskerRight_app,
    Functor.comp_map, Category.assoc] at h'
  have hP := P.hom.naturality (ρ.inv.app N)
  simp only [Functor.comp_map] at hP
  rw [← Category.assoc (aφm.unit.app N), ← h']
  simp only [Functor.map_comp, Category.assoc]
  have hP' : P.hom.app ((Ei ⋙ gs).obj N) ≫ φpm.map (Ef'.map (ρ.inv.app N)) =
      Ef.map (gp.map (ρ.inv.app N)) ≫ P.hom.app _ := hP.symm
  rw [← Category.assoc (P.hom.app _), hP', Category.assoc]
  simp

/-- The unit of an adjunction retyped along a composite isomorphism of right adjoints. -/
theorem ofNatIsoRight_trans_unit_app {L : M ⥤ Ec} {R R' R'' : Ec ⥤ M} (adj : L ⊣ R) (i : R ≅ R')
    (j : R' ≅ R'') (N : M) :
    (adj.ofNatIsoRight (i ≪≫ j)).unit.app N =
      (adj.ofNatIsoRight i).unit.app N ≫ j.hom.app (L.obj N) := by
  simp [Adjunction.ofNatIsoRight]

/-- The compatibility of a comparison `zDI` of readings of direct images with the comparison `R1`
of two routes of direct images, through `k`, the unit of `Ei' ⊣ Ef'` and a comparison `P` of
composite right adjoints: the hypothesis of
`CategoryTheory.Adjunction.comp_homEquiv_symm_eq_of_leftAdjointUniq`. -/
def RightAdjointSquareCompat {Ef' : Ec' ⥤ M'} {φpm : M' ⥤ M}
    (k : ∀ M₀ : M', φp.obj M₀ ⟶ φpm.obj M₀) (aE : Ei ⊣ Ef) (aE' : Ei' ⊣ Ef')
    (P : gp ⋙ Ef ≅ Ef' ⋙ φpm) (r : Ec ⥤ Z) (r' : Ec' ⥤ Z') (ι : Ei ⋙ r ≅ zR)
    (ι' : Ei' ⋙ r' ≅ zR') (zDI : φp ⋙ zR ⟶ zR' ⋙ τp) (R1 : gp ⋙ r ≅ r' ⋙ τp) : Prop :=
  ∀ M₀ : M', ι.hom.app (φp.obj M₀) ≫ zDI.app M₀ =
    r.map (Ei.map (k M₀ ≫ φpm.map (aE'.unit.app M₀) ≫ P.inv.app (Ei'.obj M₀)) ≫
      aE.counit.app (gp.obj (Ei'.obj M₀))) ≫ R1.hom.app (Ei'.obj M₀) ≫ τp.map (ι'.hom.app M₀)

/-- **The mate computation with the comparison of composite left adjoints `ρ`.**
`CategoryTheory.Adjunction.comp_homEquiv_symm_eq_of_rightAdjointSquare` with `μ = ρ⁻¹` at `N`, the
hypothesis on `μ` supplied by the adjunct square `h` of `ρ` and by the comparison `k` of the two
right adjoints `φp`, `φpm` of `φs`. -/
theorem comp_homEquiv_symm_eq_of_leftAdjointUniq {Ef' : Ec' ⥤ M'} {φpm : M' ⥤ M}
    (aφ : φs ⊣ φp) (aφm : φs ⊣ φpm) (k : ∀ M₀ : M', φp.obj M₀ ⟶ φpm.obj M₀)
    (hφ : ∀ N : M, aφm.unit.app N = aφ.unit.app N ≫ k (φs.obj N)) (ag : gs ⊣ gp)
    (aτ : τs ⊣ τp) (aE : Ei ⊣ Ef) (aE' : Ei' ⊣ Ef') (P : gp ⋙ Ef ≅ Ef' ⋙ φpm)
    (ρ : φs ⋙ Ei' ≅ Ei ⋙ gs)
    (h : ((aE.comp ag).ofNatIsoRight P).unit ≫ whiskerRight ρ.inv (Ef' ⋙ φpm) =
      (aφm.comp aE').unit)
    (r : Ec ⥤ Z) (r' : Ec' ⥤ Z') (ι : Ei ⋙ r ≅ zR) (ι' : Ei' ⋙ r' ≅ zR')
    (zDI : φp ⋙ zR ⟶ zR' ⋙ τp) (R1 : gp ⋙ r ≅ r' ⋙ τp)
    (hH : RightAdjointSquareCompat k aE aE' P r r' ι ι' zDI R1)
    (N : M) (c : τs.obj (r.obj (Ei.obj N)) ⟶ r'.obj (gs.obj (Ei.obj N)))
    (hA : aτ.homEquiv _ _ c = r.map (ag.unit.app (Ei.obj N)) ≫ R1.hom.app (gs.obj (Ei.obj N))) :
    τs.map (ι.hom.app N) ≫
        (aτ.homEquiv _ _).symm (zR.map (aφ.unit.app N) ≫ zDI.app (φs.obj N)) =
      c ≫ r'.map (ρ.inv.app N) ≫ ι'.hom.app (φs.obj N) := by
  refine comp_homEquiv_symm_eq_of_rightAdjointSquare aφ ag aτ aE r r' ι ι' zDI R1
    (fun M₀ => k M₀ ≫ φpm.map (aE'.unit.app M₀) ≫ P.inv.app (Ei'.obj M₀)) hH N c hA
    (ρ.inv.app N) ?_
  rw [unit_comp_map_unit_comp_map_eq_of_unit_comp_whiskerRight aE ag aφm aE' P ρ h N, hφ,
    Category.assoc]

end RightAdjointSquare

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.SmallEtale

universe u

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The transpose of the comparison of restriction with pullback.**  For `a : X ⟶ Y` of a big
étale site, `r` its morphism of schemes and `ε_a` its morphism of small étale ringed sites, the
comparison `r^*(𝒢|_{Y_Zar}) ≅ (ε_a^*𝒢)|_{X_Zar}` of
`AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso`, transposed along `r^* ⊣ r_*`, is the
restriction to `Y_Zar` of the unit `𝒢 ⟶ ε_{a*} ε_a^* 𝒢`, followed by the comparison
`SheafOfModules.pushforwardSquareIso` of the two routes of direct images, which on sections is
restriction along `AlgebraicGeometry.SmallEtale.baseChangeOpensIso`. -/
theorem homEquiv_restrictModulePullbackObjIso_hom
    (N : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (hN : N.IsQuasicoherentOnSite) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (schemeHom B a).toRingCatSheafHom).homEquiv
        _ _ (restrictModulePullbackObjIso B a N hN).hom =
      (restrictModule B Y.obj Y.property).map
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B a)).unit.app N) ≫
        (SheafOfModules.pushforwardSquareIso.{u} (schemeHom B a).toRingCatSheafHom
          (structureMap B X.obj X.property) (structureMap B Y.obj Y.property)
          (smallEtaleStructureMapRing B a) (baseChangeOpensIso B a)
          (structureMap_comp_baseChangeOpensIso B a)).hom.app
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N) :=
  Adjunction.homEquiv_unit_comp_map_leftAdjointUniq_comp_counit
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (schemeHom B a).toRingCatSheafHom)
    (associatedModuleAdjunction B X.obj X.property)
    (associatedModuleAdjunction B Y.obj Y.property)
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B a))
    (SheafOfModules.pushforwardSquareIso.{u} (schemeHom B a).toRingCatSheafHom
      (structureMap B X.obj X.property) (structureMap B Y.obj Y.property)
      (smallEtaleStructureMapRing B a) (baseChangeOpensIso B a)
      (structureMap_comp_baseChangeOpensIso B a)) N

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

universe u

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (τ : T' ⟶ T)

/-- The unit of the inverse-image adjunction of Stacks 03LU is the unit of the adjunction of the
morphism of small étale ringed topoi followed by the identification of the two direct images. -/
theorem modulePullbackAdjunction_unit_app {P X : AlgebraicSpaces B S hS} (f : P ⟶ X)
    (N : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackAdjunction B S hS f).unit.app N =
      (etaleModuleAdjunction f).unit.app N ≫
        (pushforwardModulesIsoModulePushforward B S hS f).hom.app _ :=
  Adjunction.ofNatIsoRight_trans_unit_app _ _ _ N

/-- **The identification of the Zariski reading of a direct image is the composite of the two
comparisons of routes of direct images.**  For `τ : T' ⟶ T` of the site and every `𝒪`-module `M₀`
on `yoneda.obj T'`, the identification `AlgebraicGeometry.Space.zariskiDirectImageNatTrans` of the
Zariski reading of `φ_* M₀` (read through `AlgebraicGeometry.Space.zariskiReadingIso`) is the
comparison of the small étale sites with direct images
(`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, transported along the
identification of the two small étale sites and the identification of the two direct images of
Stacks 03LU), followed by the comparison of restriction to the Zariski sites with direct images
(`SheafOfModules.pushforwardSquareIso`). -/
def ZariskiReadingDirectImageCompat : Prop :=
  Adjunction.RightAdjointSquareCompat
    (fun M₀ =>
      (pushforwardModulesIsoModulePushforward B S hS (representedSpaceMap B S hS τ)).hom.app M₀)
    ((representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction :
      (representedSmallEtaleModuleEquivalence B S hS T).inverse ⊣
        (representedSmallEtaleModuleEquivalence B S hS T).functor)
    ((representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction :
      (representedSmallEtaleModuleEquivalence B S hS T').inverse ⊣
        (representedSmallEtaleModuleEquivalence B S hS T').functor)
    (representedModulePushforwardSquareIso B S hS τ (relativelyRepresentable_yoneda_map B S hS τ))
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (zariskiReadingIso T) (zariskiReadingIso T') (zariskiDirectImageNatTrans τ)
    (SheafOfModules.pushforwardSquareIso.{u}
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        τ.left).toRingCatSheafHom
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
        T'.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
        T.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
        τ.left)
      (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B) τ.left)
      (_root_.AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso
        (associatedBigEtaleSite B) τ.left))

/-- **The mate of the identification of the Zariski reading of a direct image is the base
comparison `AlgebraicGeometry.Space.representedZariskiModulePullbackIso`**, granted the
compatibility `AlgebraicGeometry.Space.ZariskiReadingDirectImageCompat` of the comparisons of
direct images. -/
theorem pullback_map_zariskiReadingIso_hom_comp_homEquiv_symm_of_compat
    (hH : ZariskiReadingDirectImageCompat τ)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
        ((zariskiReadingIso T).hom.app N) ≫
      ((Stacks.RingedSpace.pullbackAdjunction
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
            ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N) ≫
          (zariskiDirectImageNatTrans τ).app
            ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)) =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso (associatedBigEtaleSite B)
          τ.left ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj N)
          (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T N hN)).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
          ((representedModulePullbackIso B S hS τ
            (relativelyRepresentable_yoneda_map B S hS τ)).inv.app N) ≫
        (zariskiReadingIso T').hom.app
          ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N) := by
  have key := Adjunction.comp_homEquiv_symm_eq_of_leftAdjointUniq
    (etaleModuleAdjunction (representedSpaceMap B S hS τ))
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS τ))
    (fun M₀ =>
      (pushforwardModulesIsoModulePushforward B S hS (representedSpaceMap B S hS τ)).hom.app M₀)
    (modulePullbackAdjunction_unit_app (representedSpaceMap B S hS τ))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (representedSchemeStructureMapRing B S hS τ))
    (Stacks.RingedSpace.pullbackAdjunction (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)))
    ((representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction :
      (representedSmallEtaleModuleEquivalence B S hS T).inverse ⊣
        (representedSmallEtaleModuleEquivalence B S hS T).functor)
    ((representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction :
      (representedSmallEtaleModuleEquivalence B S hS T').inverse ⊣
        (representedSmallEtaleModuleEquivalence B S hS T').functor)
    (representedModulePushforwardSquareIso B S hS τ (relativelyRepresentable_yoneda_map B S hS τ))
    (representedModulePullbackIso B S hS τ (relativelyRepresentable_yoneda_map B S hS τ))
    (unit_comp_representedModulePullbackIso_inv B S hS τ
      (relativelyRepresentable_yoneda_map B S hS τ))
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (zariskiReadingIso T) (zariskiReadingIso T') (zariskiDirectImageNatTrans τ)
    (SheafOfModules.pushforwardSquareIso.{u}
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        τ.left).toRingCatSheafHom
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
        T'.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
        T.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
        τ.left)
      (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B) τ.left)
      (_root_.AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso
        (associatedBigEtaleSite B) τ.left))
    hH N _
    (_root_.AlgebraicGeometry.SmallEtale.homEquiv_restrictModulePullbackObjIso_hom
      (associatedBigEtaleSite B) τ.left _
      (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T N hN))
  exact key

end AlgebraicGeometry.Space



end
