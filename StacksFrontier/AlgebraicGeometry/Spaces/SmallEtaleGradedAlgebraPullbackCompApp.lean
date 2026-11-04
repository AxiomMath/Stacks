module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackCompApp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStepTwo
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtaleCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompTransport

/-!
# The graded composition comparison of algebraic spaces is the one of Stacks 03LU, degreewise

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces,
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso` is the comparison
`(f ≫ g)^* ≅ g^* ∘ f^*` of pullbacks of sheaves of **graded** algebras, and
`AlgebraicGeometry.Space.modulePullbackCompIso` is the comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of
pullbacks of sheaves of modules of Stacks 03LU.  This file proves that **the homogeneous
components of the first are the inverse of the second**: the multiplicative comparison is the
module comparison in every degree.

The two are built over different spellings of the direct image of modules —
`AlgebraicGeometry.RingedToposHom.pushforwardModules` for the graded one,
`AlgebraicGeometry.Space.modulePushforward` for the module one — which agree by
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`; the comparison of the
direct images along a composite of the second spelling is the one of the first transported along
those equalities (`AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr`).  So the
identification is uniqueness of left adjoints together with the observation that transporting
all the right adjoints along equalities changes nothing, which
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_eqToIso` records at variable functors,
where the equalities can be eliminated.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_eqToIso`: the comparison of left
  adjoints is unchanged when the right adjoints are transported along equalities.
* `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso_hom_app_app`: **the degree-`n`
  component of the graded comparison at `𝒜` is the inverse of the module comparison of Stacks
  03LU at `𝒜_n`.**

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  {Lg : C₀ ⥤ C₁} {Lf : C₁ ⥤ C₂} {Lfg : C₀ ⥤ C₂}
  {Rg Pg Qg : C₁ ⥤ C₀} {Rf Pf Qf : C₂ ⥤ C₁} {Rfg Pfg Qfg : C₂ ⥤ C₀}

/-- The unit of an adjunction transported along an isomorphism of right adjoints: the unit
followed by the isomorphism. -/
theorem ofNatIsoRight_unit_app_eq_comp {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) (M : C) :
    (adj.ofNatIsoRight iso).unit.app M = adj.unit.app M ≫ iso.hom.app (F.obj M) := by
  rw [← homEquiv_id, homEquiv_ofNatIsoRight_apply, homEquiv_id]

/-- **Transporting all the right adjoints along equalities does not change the comparison of
left adjoints.**  Given adjunctions `Lg ⊣ Rg`, `Lf ⊣ Rf`, `Lfg ⊣ Rfg`, identifications
`pk : Rk ≅ Pk` and a comparison `τ : Pf ⋙ Pg ≅ Pfg`, transporting the `Pk` further along
equalities `Pk = Qk` — and `τ` along with them — leaves the comparison of `Lg ⋙ Lf` with `Lfg`
unchanged. -/
theorem leftAdjointUniq_ofNatIsoRight_eqToIso (bg : Lg ⊣ Rg) (bf : Lf ⊣ Rf) (bfg : Lfg ⊣ Rfg)
    (pg : Rg ≅ Pg) (pf : Rf ≅ Pf) (pfg : Rfg ≅ Pfg) (τ : Pf ⋙ Pg ≅ Pfg)
    (eg : Pg = Qg) (ef : Pf = Qf) (efg : Pfg = Qfg) (M : C₀) :
    (leftAdjointUniq ((bfg.ofNatIsoRight pfg).ofNatIsoRight τ.symm)
        ((bg.ofNatIsoRight pg).comp (bf.ofNatIsoRight pf))).hom.app M =
      (leftAdjointUniq (bfg.ofNatIsoRight (pfg ≪≫ eqToIso efg))
        (((bg.ofNatIsoRight (pg ≪≫ eqToIso eg)).comp
          (bf.ofNatIsoRight (pf ≪≫ eqToIso ef))).ofNatIsoRight
            (Functor.compIsoCongr ef eg efg τ))).hom.app M := by
  subst eg ef efg
  apply ((bfg.ofNatIsoRight (pfg ≪≫ eqToIso rfl)).homEquiv _ _).injective
  rw [homEquiv_leftAdjointUniq_hom_app, homEquiv_ofNatIsoRight_apply,
    ofNatIsoRight_unit_app_eq_comp, comp_unit_app, ofNatIsoRight_unit_app_eq_comp,
    ofNatIsoRight_unit_app_eq_comp, Functor.compIsoCongr_eq]
  have key := homEquiv_leftAdjointUniq_hom_app ((bfg.ofNatIsoRight pfg).ofNatIsoRight τ.symm)
    ((bg.ofNatIsoRight pg).comp (bf.ofNatIsoRight pf)) M
  rw [homEquiv_ofNatIsoRight_apply, homEquiv_ofNatIsoRight_apply, comp_unit_app,
    ofNatIsoRight_unit_app_eq_comp, ofNatIsoRight_unit_app_eq_comp] at key
  have key' : bfg.homEquiv _ _ ((leftAdjointUniq ((bfg.ofNatIsoRight pfg).ofNatIsoRight τ.symm)
      ((bg.ofNatIsoRight pg).comp (bf.ofNatIsoRight pf))).hom.app M) ≫ pfg.hom.app _ =
      ((bg.unit.app M ≫ pg.hom.app _) ≫ Pg.map (bf.unit.app _ ≫ pf.hom.app _)) ≫
        τ.hom.app _ := by
    rw [← key]
    simp
  simp only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans]
  rw [key']
  simp

/-- `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_eqToIso` with the transported
isomorphisms given as variables equal to the transports, and the comparison read in the opposite
direction.  This is the form in which it applies to adjunctions *defined* through isomorphisms of
right adjoints which are only propositionally equal to the transports. -/
theorem leftAdjointUniq_ofNatIsoRight_eqToIso_inv (bg : Lg ⊣ Rg) (bf : Lf ⊣ Rf) (bfg : Lfg ⊣ Rfg)
    (pg : Rg ≅ Pg) (pf : Rf ≅ Pf) (pfg : Rfg ≅ Pfg) (τ : Pf ⋙ Pg ≅ Pfg)
    (eg : Pg = Qg) (ef : Pf = Qf) (efg : Pfg = Qfg)
    (κg : Rg ≅ Qg) (κf : Rf ≅ Qf) (κfg : Rfg ≅ Qfg) (μ : Qf ⋙ Qg ≅ Qfg)
    (hκg : κg = pg ≪≫ eqToIso eg) (hκf : κf = pf ≪≫ eqToIso ef)
    (hκfg : κfg = pfg ≪≫ eqToIso efg) (hμ : μ = Functor.compIsoCongr ef eg efg τ) (M : C₀) :
    (leftAdjointUniq ((bfg.ofNatIsoRight pfg).ofNatIsoRight τ.symm)
        ((bg.ofNatIsoRight pg).comp (bf.ofNatIsoRight pf))).hom.app M =
      (leftAdjointUniq (((bg.ofNatIsoRight κg).comp (bf.ofNatIsoRight κf)).ofNatIsoRight μ)
        (bfg.ofNatIsoRight κfg)).inv.app M := by
  subst hκg hκf hκfg hμ
  exact leftAdjointUniq_ofNatIsoRight_eqToIso bg bf bfg pg pf pfg τ eg ef efg M

/-- `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_eqToIso_inv` as an equation of
isomorphisms of functors. -/
theorem leftAdjointUniq_ofNatIsoRight_eqToIso_symm (bg : Lg ⊣ Rg) (bf : Lf ⊣ Rf)
    (bfg : Lfg ⊣ Rfg) (pg : Rg ≅ Pg) (pf : Rf ≅ Pf) (pfg : Rfg ≅ Pfg) (τ : Pf ⋙ Pg ≅ Pfg)
    (eg : Pg = Qg) (ef : Pf = Qf) (efg : Pfg = Qfg)
    (κg : Rg ≅ Qg) (κf : Rf ≅ Qf) (κfg : Rfg ≅ Qfg) (μ : Qf ⋙ Qg ≅ Qfg)
    (hκg : κg = pg ≪≫ eqToIso eg) (hκf : κf = pf ≪≫ eqToIso ef)
    (hκfg : κfg = pfg ≪≫ eqToIso efg) (hμ : μ = Functor.compIsoCongr ef eg efg τ) :
    leftAdjointUniq ((bfg.ofNatIsoRight pfg).ofNatIsoRight τ.symm)
        ((bg.ofNatIsoRight pg).comp (bf.ofNatIsoRight pf)) =
      (leftAdjointUniq (((bg.ofNatIsoRight κg).comp (bf.ofNatIsoRight κf)).ofNatIsoRight μ)
        (bfg.ofNatIsoRight κfg)).symm := by
  ext M
  exact leftAdjointUniq_ofNatIsoRight_eqToIso_inv bg bf bfg pg pf pfg τ eg ef efg κg κf κfg μ
    hκg hκf hκfg hμ M

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- The comparison of left adjoints of the Stacks 03D7 adjunctions for the morphisms of small
étale ringed topoi, read through `AlgebraicGeometry.Space.pushforwardModulesCompAt`, is the inverse
of the composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU. -/
theorem leftAdjointUniq_viaComparison_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    Adjunction.leftAdjointUniq
        (Adjunction.ofNatIsoRight
          (smallEtaleRingedToposHom B S hS (f ≫ g)).pullbackAdjPushforwardModulesViaComparison
          (pushforwardModulesCompAt B S hS f g).symm)
        ((smallEtaleRingedToposHom B S hS g).pullbackAdjPushforwardModulesViaComparison.comp
          (smallEtaleRingedToposHom B S hS f).pullbackAdjPushforwardModulesViaComparison) =
      (modulePullbackCompIso B S hS f g).symm :=
  Adjunction.leftAdjointUniq_ofNatIsoRight_eqToIso_symm
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS g).toRingedToposModulesHom)
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom)
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS (f ≫ g)).toRingedToposModulesHom)
    (smallEtaleRingedToposHom B S hS g).pushforwardModulesIso
    (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso
    (smallEtaleRingedToposHom B S hS (f ≫ g)).pushforwardModulesIso
    (pushforwardModulesCompAt B S hS f g)
    (pushforwardModules_eq_modulePushforward B S hS g)
    (pushforwardModules_eq_modulePushforward B S hS f)
    (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))
    (modulePushforwardIso B S hS g) (modulePushforwardIso B S hS f)
    (modulePushforwardIso B S hS (f ≫ g)) (modulePushforwardCompIso B S hS f g)
    (modulePushforwardIso_eq_eqToIso B S hS g) (modulePushforwardIso_eq_eqToIso B S hS f)
    (modulePushforwardIso_eq_eqToIso B S hS (f ≫ g))
    (modulePushforwardCompIso_eq_compIsoCongr B S hS f g)

/-- **The graded composition comparison is the module composition comparison of Stacks 03LU, in
every degree.**  The degree-`n` component of `(f ≫ g)^*𝒜 ≅ f^*(g^*𝒜)` is the inverse of
`AlgebraicGeometry.Space.modulePullbackCompIso` at the degree-`n` piece of `𝒜`. -/
theorem gradedAlgebraPullbackCompIso_hom_app_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (𝒜 : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O)) (n : ℤ) :
    ((gradedAlgebraPullbackCompIso B S hS f g).hom.app 𝒜).app n =
      (modulePullbackCompIso B S hS f g).inv.app (𝒜.piece n) := by
  have e0 : gradedAlgebraPullbackCompIso B S hS f g =
      gradedPullbackCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS (f ≫ g))
        (gradedAlgebraPushforwardCompIso B S hS f g) := rfl
  rw [e0]
  have h1 : ((gradedPullbackCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS (f ≫ g))
        (gradedAlgebraPushforwardCompIso B S hS f g)).hom.app 𝒜).app n =
      (Adjunction.leftAdjointUniq
        (Adjunction.ofNatIsoRight
          (smallEtaleRingedToposHom B S hS (f ≫ g)).pullbackAdjPushforwardModulesViaComparison
          (pushforwardModulesCompAt B S hS f g).symm)
        ((smallEtaleRingedToposHom B S hS g).pullbackAdjPushforwardModulesViaComparison.comp
          (smallEtaleRingedToposHom B S hS f).pullbackAdjPushforwardModulesViaComparison)).hom.app
        (𝒜.piece n) :=
    gradedPullbackCompIso_hom_app_app (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS (f ≫ g))
      (gradedAlgebraPushforwardCompIso B S hS f g) (pushforwardModulesCompAt B S hS f g)
      (fun A n => gradedAlgebraPushforwardCompIso_hom_app_app B S hS f g A n) 𝒜 n
  exact h1.trans (congrArg (fun e => e.hom.app (𝒜.piece n))
    (leftAdjointUniq_viaComparison_eq B S hS f g))

end AlgebraicGeometry.Space

end
