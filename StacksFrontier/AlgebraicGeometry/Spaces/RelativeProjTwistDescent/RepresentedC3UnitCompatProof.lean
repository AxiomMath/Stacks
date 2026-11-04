module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleUnitPullback

/-!
# Toward the compatibility of the unit identification of Stacks 03DX (2) with inverse images

Let `g : V ⟶ U` be a morphism of the big fppf site over `S`.  The compatibility
`AlgebraicGeometry.Space.RepresentedC3UnitCompat` of the identification
`(𝒪_U)_{yoneda U} ≅ 𝒪_{yoneda U}` of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso` with inverse images along `g` is
reduced here to identities in the modules on `yoneda.obj V`.

After the comparison `θ` of the two factorizations of the square of `g`
(`AlgebraicGeometry.Space.representedSquareModulePullbackIso`), the identification
`g^*((𝒪_U)_{yoneda U}) ≅ (g^*𝒪_U)_{yoneda V}` is the comparison of Stacks 03LC (1)
(`representedSquareModulePullbackIso_hom_app_comp_modulePullbackRepresentedQuasicoherentIso_hom`);
Stacks 03LU round the square of `g` and round the square of the underlying morphism of schemes
between étale and Zariski sites, together with the naturality of `θ`, give the two sides after
`θ`, and `θ` is cancelled.  This file proves that argument at variables and the readings of the
factors that enter it.

## Main results

* `AlgebraicGeometry.Space.unitCompat_of_readings`: the abstract shape of the compatibility, at
  variables.
* `AlgebraicGeometry.Space.representedSquare_pullbackUnitIsoTransport_representedSquareMate`:
  Stacks 03LU round the square of `g`, with the comparison of the factorizations written as the
  inverse mate `AlgebraicGeometry.Space.representedSquareMate`.
* `AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso_eq_representedReindexPullbackIso`:
  the identification of the structure sheaf with its second factor read through
  `AlgebraicGeometry.Space.representedReindexPullbackIso`.
* `representedQuasicoherentSchemeEquivalence_map_quasicoherentPullbackUnitIso_hom`:
  the attached morphism of Stacks 03LU on schemes.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section Abstract

/-- The abstract shape of `AlgebraicGeometry.Space.representedC3UnitCompat`, at variables.  An
identification `u = E(p₁) ≫ p₂` on each side, the comparison `θ` of two factorizations, a
comparison `β` of two routes to the middle, the description `hC` of `c` after `θ`, and the two
squares `hKF1`, `hKF2` of the two identifications `p₂`, `p₁` give the compatibility of `u` with
`Φ`.  The square `hKF1` is taken through factors `kᵢ` equal to the expected ones, so that it may be
given in another spelling. -/
theorem unitCompat_of_readings {ZU ZV CU CV DU DV : Type*} [Category ZU] [Category ZV]
    [Category CU] [Category CV] [Category DU] [Category DV]
    {Ac : CU ⥤ CV} {EU : CU ⥤ DU} {EV : CV ⥤ DV} {Phi : DU ⥤ DV} (θ : Ac ⋙ EV ⟶ EU ⋙ Phi)
    (hθ : IsIso θ) {OCU : CU} {OCV : CV} {ODU : DU} {ODV : DV}
    (k₁ : EV.obj (Ac.obj OCU) ⟶ EV.obj OCV) (k₂ : EV.obj OCV ⟶ ODV)
    (k₃ : EV.obj (Ac.obj OCU) ⟶ Phi.obj (EU.obj OCU)) (k₄ : Phi.obj (EU.obj OCU) ⟶ Phi.obj ODU)
    (k₅ : Phi.obj ODU ⟶ ODV) (hKF1 : k₁ ≫ k₂ = k₃ ≫ k₄ ≫ k₅)
    (q : Ac.obj OCU ⟶ OCV) (hk₁ : k₁ = EV.map q) (p₂U : EU.obj OCU ≅ ODU) (p₂V : EV.obj OCV ≅ ODV)
    (hk₂ : k₂ = p₂V.hom) (hk₃ : k₃ = θ.app OCU) (hk₄ : k₄ = Phi.map p₂U.hom)
    (mU : Phi.obj ODU ⟶ ODV) (hk₅ : k₅ = mU)
    (LU : ZU ⥤ CU) (LV : ZV ⥤ CV) (Rz : ZU ⥤ ZV) (β : Rz ⋙ LV ≅ LU ⋙ Ac) {OZU : ZU} {OZV : ZV}
    (p₁U : LU.obj OZU ≅ OCU) (uU : EU.obj (LU.obj OZU) ≅ ODU) (huU : uU = EU.mapIso p₁U ≪≫ p₂U)
    (p₁V : LV.obj OZV ≅ OCV) (uV : EV.obj (LV.obj OZV) ≅ ODV) (huV : uV = EV.mapIso p₁V ≪≫ p₂V)
    (pb pb₀ : Rz.obj OZU ⟶ OZV) (hpb : pb₀ = pb)
    (c : Phi.obj (EU.obj (LU.obj OZU)) ⟶ EV.obj (LV.obj (Rz.obj OZU)))
    (mid : EV.obj (LV.obj (Rz.obj OZU)) ⟶ EV.obj (LV.obj OZV)) (hmid : mid = EV.map (LV.map pb))
    (hC : θ.app (LU.obj OZU) ≫ c = EV.map (β.inv.app OZU))
    (hKF2 : LV.map pb₀ ≫ p₁V.hom = β.hom.app OZU ≫ Ac.map p₁U.hom ≫ q) :
    Phi.map uU.hom ≫ mU = c ≫ mid ≫ uV.hom := by
  have := hθ
  subst huU huV hmid hpb hk₁ hk₂ hk₃ hk₄ hk₅
  refine (cancel_epi (θ.app (LU.obj OZU))).1 ?_
  have n := θ.naturality p₁U.hom
  simp only [Functor.comp_map] at n
  have h3' : β.inv.app OZU ≫ LV.map pb₀ ≫ p₁V.hom = Ac.map p₁U.hom ≫ q := by
    rw [hKF2, Iso.inv_hom_id_app_assoc]
  have h3 := congrArg EV.map h3'
  simp only [Functor.map_comp] at h3
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hC, reassoc_of% h3, ← reassoc_of% n, ← hKF1]

end Abstract

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Stacks 03LU round the square of `g`, with the comparison of the two factorizations written as
the inverse mate `AlgebraicGeometry.Space.representedSquareMate`: the unit companion of
`AlgebraicGeometry.Space.representedSquare_pullbackTensorIsoTransport_representedSquareMate`. -/
theorem representedSquare_pullbackUnitIsoTransport_representedSquareMate
    {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of%
      (Stacks.SheafOfModules.pullbackUnitIsoTransport_square_factorizationPullbackIso_of_hom_eq
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
        (factorizationPullbackIso_hom_eq_representedSquareMate B S hS g)) :=
  Stacks.SheafOfModules.pullbackUnitIsoTransport_square_factorizationPullbackIso_of_hom_eq
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
      (factorizationPullbackIso_hom_eq_representedSquareMate B S hS g)

/-- `AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso` with its second factor read
through `AlgebraicGeometry.Space.representedReindexPullbackIso`, as an equality of
isomorphisms. -/
theorem representedQuasicoherentSchemeUnitIso_eq_representedReindexPullbackIso
    (U : BigFppfOver B S hS) :
    representedQuasicoherentSchemeUnitIso B S hS U =
      (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
        (Stacks.SheafOfModules.pullbackUnitIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)) ≪≫
      Stacks.SheafOfModules.pullbackUnitIsoTransport (representedReindexHom B S hS U)
        (representedReindexPullbackIso B S hS U) :=
  (representedQuasicoherentSchemeUnitIso_eq B S hS U).trans
    (congrArg (fun e => (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
        (Stacks.SheafOfModules.pullbackUnitIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)) ≪≫ e)
      (pullbackUnitIsoTransport_pullbackModulesReindexIso_eq_representedReindexPullbackIso
        B S hS U))

/-- The attached morphism of Stacks 03LU on schemes along `g` is the image under the comparison of
Stacks 04M0 of the associated module of Stacks 03LU for the morphism of ringed spaces. -/
theorem representedQuasicoherentSchemeEquivalence_map_quasicoherentPullbackUnitIso_hom
    {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackUnitIso B S hS g).hom).hom =
    (representedSmallEtaleModuleEquivalence B S hS V).functor.map
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
          (Stacks.PullbackAlgebra.pullbackUnitIso (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) g.left).toLRSHom.toShHom).hom) :=
  rfl

end AlgebraicGeometry.Space

end
