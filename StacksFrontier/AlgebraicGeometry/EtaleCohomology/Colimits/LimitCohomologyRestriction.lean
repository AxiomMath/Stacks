module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitCohomologyTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitPostcompSections
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.ColimitSite
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitInverseImageSystem

/-!
# Restriction on étale cohomology along a limit of affine schemes

Let `I` be a directed set, `(X_i)` an inverse system of schemes over `I` with affine transition
morphisms and limit `X`, and let `G` be an abelian sheaf on `X_⊥` for a least index `⊥`.
`Stacks.EtaleCohomology.LimitSiteBridge` reads the cohomology of the inverse images `f_i⁻¹G` on
the sites of Stacks 0EYL and identifies the transitions and the legs of the colimit of Stacks
09YP with restriction on étale cohomology followed by comparisons
`levelComparison : h⁻¹(f_i⁻¹G) ⟶ f_j⁻¹G` and `limitComparison : f_i⁻¹(f_{i⊥}⁻¹G) ⟶ f_⊥⁻¹G`
defined through the universal property of the system of inverse images.

This file shows that these comparisons are the canonical comparisons of inverse images along a
composite (`levelComparison_eq`, `limitComparison_eq`), hence isomorphisms, and deduces the
injectivity and surjectivity halves of Stacks 09YQ for étale cohomology, for affine levels and
from an arbitrary index `i₀` (`exists_le_restriction_eq_zero`, `exists_le_restriction_eq`).

## Main results

* `levelComparison_eq`, `limitComparison_eq`: the comparisons are the canonical ones.
* `exists_le_restriction_eq`: every class on `X` comes from some `X_i`, `i ≥ i₀`.
* `exists_le_restriction_eq_zero`: a class on `X_{i₀}` that restricts to zero on `X` restricts to
  zero on some `X_i`, `i ≥ i₀`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.WeakSites.PullbackSystem

universe u

namespace Stacks.EtaleCohomology.LimitSiteBridge

open Stacks.EtaleCohomology.AffineLimitCohomology

attribute [local instance] abelianSheafSmallEtale hasSheafifySmallEtale

/-- A map `g : L₁₂(L₀₁ X) ⟶ L₀₂ X` whose adjoint along the composite adjunction is the unit of
`L₀₂ ⊣ R₂₀`, read through `e : R₂₁ ⋙ R₁₀ ≅ R₂₀`, is the component of the comparison of left
adjoints attached to `e`. -/
theorem eq_leftAdjointCompIso_hom_app {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁]
    [Category C₂] {L₀₁ : C₀ ⥤ C₁} {L₁₂ : C₁ ⥤ C₂} {L₀₂ : C₀ ⥤ C₂} {R₁₀ : C₁ ⥤ C₀}
    {R₂₁ : C₂ ⥤ C₁} {R₂₀ : C₂ ⥤ C₀} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₀₂ : L₀₂ ⊣ R₂₀) (e : R₂₁ ⋙ R₁₀ ≅ R₂₀) (X : C₀) (g : L₁₂.obj (L₀₁.obj X) ⟶ L₀₂.obj X)
    (hg : adj₀₂.unit.app X =
      adj₀₁.unit.app X ≫ R₁₀.map (adj₁₂.unit.app _ ≫ R₂₁.map g) ≫ e.hom.app _) :
    g = (Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).hom.app X := by
  apply ((adj₀₁.comp adj₁₂).homEquiv _ _).injective
  have h1 := unit_conjugateEquiv_symm adj₀₂ (adj₀₁.comp adj₁₂) e.inv X
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change _ = (adj₀₁.comp adj₁₂).unit.app X ≫ (R₂₁ ⋙ R₁₀).map
    (((conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)).symm e.inv).app X)
  rw [← h1, hg]
  simp [Adjunction.comp_unit_app]

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} {B : BigEtaleSite.{u}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt} {hc : IsLimit c}
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] [OrderBot I]

/-- The components of `levelPushforwardIso`: restriction along the transition comparison. -/
theorem levelPushforwardIso_hom_app_hom_app (i : (sys D c B hD hX hc).I)
    (M : Sheaf (lvl.{u, u} D c B hD hX hc i).smallEtaleTopology Ab.{u + 1})
    (V : ((sys D c B hD hX hc).C (bottom D c B hD hX hc))ᵒᵖ) :
    ((levelPushforwardIso.{u, u} D c B hD hX hc Ab.{u + 1} i).hom.app M).hom.app V =
      M.obj.map ((transitionBaseChangeIso D c B hD hX hc
        ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V.unop).op := by
  simp only [levelPushforwardIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousComp, Iso.refl_hom,
    Iso.refl_inv]
  simp only [Functor.comp_obj, Functor.sheafPushforwardContinuousNatTrans, NatTrans.op_id,
    ObjectProperty.ι_obj, Functor.whiskerRight_id', Iso.symm_inv, Functor.whiskerRight_app,
    Functor.op_obj, NatTrans.op_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- In a category, given the stated commutation relations and that `mτj` is an isomorphism, `ηj`
equals `ηi ≫ un ≫ γ ≫ mm`. -/
theorem chase_aux {𝒜 : Type*} [Category 𝒜] {GW LiW LiV' LhW LhV' LjW LjV'' LjU LjT LjS : 𝒜}
    {ei : GW ⟶ LiV'} {ej : GW ⟶ LjS} {ψ : LiV' ⟶ LjU} {eq : LjS ⟶ LjU}
    {ηi : GW ⟶ LiW} {mk : LiW ⟶ LiV'} {ηj : GW ⟶ LjT} {mτj : LjT ⟶ LjS}
    {un : LiW ⟶ LhW} {un' : LiV' ⟶ LhV'} {mkh : LhW ⟶ LhV'} {γ : LhW ⟶ LjW}
    {γ' : LhV' ⟶ LjV''} {mkj : LjW ⟶ LjV''} {mτa : LjV'' ⟶ LjU} {mm : LjW ⟶ LjT}
    {eq' : LjU ⟶ LjS}
    (hA : ei ≫ ψ = ej ≫ eq) (hi : ei = ηi ≫ mk) (hj : ej = ηj ≫ mτj)
    (hB : ψ = un' ≫ γ' ≫ mτa) (hC : mk ≫ un' = un ≫ mkh) (hD : mkh ≫ γ' = γ ≫ mkj)
    (hT : mm ≫ mτj = mkj ≫ mτa ≫ eq') (hE : eq ≫ eq' = 𝟙 _) (hm : IsIso mτj) :
    ηj = ηi ≫ un ≫ γ ≫ mm := by
  rw [← cancel_mono mτj]
  subst hi hj hB
  simp only [Category.assoc] at hA ⊢
  rw [hT, ← reassoc_of% hD, ← reassoc_of% hC, reassoc_of% hA, hE, Category.comp_id]

/-- Restriction on `Ext` out of `ℤ` followed by `g` is restriction on étale cohomology followed
by composition with `g`. -/
theorem extRestrictionMap_apply {X Y : Scheme.{u}} (h : Y ⟶ X)
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology Ab.{u + 1})]
    {P : Sheaf X.smallEtaleTopology Ab.{u + 1}} {Q : Sheaf Y.smallEtaleTopology Ab.{u + 1}}
    (g : (etaleAbelianInverseImage.{u, 0} h).obj P ⟶ Q) (n : ℕ)
    (y : (extFunctorObj (zSheaf X) n).obj P) :
    extRestrictionMap h g n y =
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} h P n y).comp (Ext.mk₀ g) (add_zero n) :=
  rfl

/-- A transport followed by the restriction along the image of a transport is the identity. -/
theorem eqToHom_comp_map_map_eqToHom {𝒞 𝒟 𝒜 : Type*} [Category 𝒞] [Category 𝒟] [Category 𝒜]
    (F : 𝒞 ⥤ 𝒟) (M : 𝒟ᵒᵖ ⥤ 𝒜) {X Y : 𝒞} (q : X = Y)
    (p : M.obj (op (F.obj X)) = M.obj (op (F.obj Y))) :
    eqToHom p ≫ M.map (F.map (eqToHom q)).op = 𝟙 _ := by
  subst q
  simp

section Comparison

attribute [local instance] toLimitSmall_isContinuous

/-- The transition comparison of the terminal level, along a composite through a transition. -/
theorem transitionBaseChangeIso_from_comp {i j : (sys D c B hD hX hc).I} (a : j ⟶ i)
    (V : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (transitionBaseChangeIso D c B hD hX hc ((bottom_isTerminal D c B hD hX hc).from j)).hom.app V ≫
        (smallEtaleBaseChangeComp' (lvlMap D c B hD hX hc a) (toBottom D c B hD hX hc i)
          (toBottom D c B hD hX hc j) (toBottom_comp a)).hom.app
            ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V) =
      (levelToEtale D c B hD hX hc j).map (eqToHom (Functor.congr_obj
          (u_from_comp (sys D c B hD hX hc) (bottom_isTerminal D c B hD hX hc) a) V)) ≫
        (transitionBaseChangeIso D c B hD hX hc a).hom.app
          (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj V) ≫
        (smallEtaleBaseChange (lvlMap D c B hD hX hc a)).map
          ((transitionBaseChangeIso D c B hD hX hc
            ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V) := by
  have key : ∀ (b : j ⟶ bottom D c B hD hX hc)
      (hb : a ≫ (bottom_isTerminal D c B hD hX hc).from i = b),
      (transitionBaseChangeIso D c B hD hX hc b).hom.app V ≫
        (smallEtaleBaseChangeComp' (lvlMap D c B hD hX hc a) (toBottom D c B hD hX hc i)
          (lvlMap D c B hD hX hc b) (hb ▸ lvlMap_comp D c B hD hX hc _ _)).hom.app
            ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V) =
      (levelToEtale D c B hD hX hc j).map (eqToHom (hb ▸ Functor.congr_obj
          ((sys D c B hD hX hc).comp a ((bottom_isTerminal D c B hD hX hc).from i)) V)) ≫
        (transitionBaseChangeIso D c B hD hX hc a).hom.app
          (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj V) ≫
        (smallEtaleBaseChange (lvlMap D c B hD hX hc a)).map
          ((transitionBaseChangeIso D c B hD hX hc
            ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V) := by
    intro b hb
    subst hb
    rw [transitionBaseChangeIso_comp D c B hD hX hc a _ V]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rfl
  exact key _ ((bottom_isTerminal D c B hD hX hc).hom_ext _ _)

variable
    (G : Sheaf (lvl.{u, u} D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology Ab.{u + 1})

/-- The unit at `G` of the inverse-image–direct-image adjunction along `f_j : X_j ⟶ X_⊥` is the
unit along `f_i` followed by the direct image under `f_i` of the unit along `h : X_j ⟶ X_i`
composed with `levelComparison G a`, read through the comparison of direct images along
`f_j = h ≫ f_i`. -/
theorem unit_toBottom_eq {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (toBottom D c B hD hX hc j)).unit.app G =
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} (toBottom D c B hD hX hc i)).unit.app G ≫
        (etaleAbelianDirectImage.{u, 0} (toBottom D c B hD hX hc i)).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (lvlMap D c B hD hX hc a)).unit.app
              (levelInverseImage G i) ≫
            (etaleAbelianDirectImage.{u, 0} (lvlMap D c B hD hX hc a)).map (levelComparison G a)) ≫
        (etaleAbelianDirectImageCompIso'.{u, 0} (lvlMap D c B hD hX hc a)
          (toBottom D c B hD hX hc i) (toBottom D c B hD hX hc j) (toBottom_comp a)).hom.app
            (levelInverseImage G j) := by
  apply (levelRestrict.{u, u} D c B hD hX hc Ab.{u + 1} (bottom D c B hD hX hc)).map_injective
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  have e1 := congrArg (fun φ => φ.app V) (ψ_spec (sys D c B hD hX hc)
    (bottom_isTerminal D c B hD hX hc) (levelε G) (isUniversalArrow_levelε G) a)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] at e1
  have e2 : (levelε G i).app V =
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (toBottom D c B hD hX hc i)).unit.app
          G).hom.app (op ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V.unop)) ≫
        (levelInverseImage G i).obj.map ((transitionBaseChangeIso D c B hD hX hc
          ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V.unop).op :=
    congrArg (fun t => _ ≫ t) (levelPushforwardIso_hom_app_hom_app i (levelInverseImage G i) V)
  have e3 : (levelε G j).app V =
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (toBottom D c B hD hX hc j)).unit.app
          G).hom.app (op ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V.unop)) ≫
        (levelInverseImage G j).obj.map ((transitionBaseChangeIso D c B hD hX hc
          ((bottom_isTerminal D c B hD hX hc).from j)).hom.app V.unop).op :=
    congrArg (fun t => _ ≫ t) (levelPushforwardIso_hom_app_hom_app j (levelInverseImage G j) V)
  have e4 := (congrArg (fun φ => φ.app ((sys D c B hD hX hc).u
    ((bottom_isTerminal D c B hD hX hc).from i) |>.op.obj V)) (levelComparison_spec G a)).symm
  have e5 := ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (lvlMap D c B hD hX hc a)).unit.app
    (levelInverseImage G i)).hom.naturality ((transitionBaseChangeIso D c B hD hX hc
      ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V.unop).op
  have e6 := (levelComparison G a).hom.naturality ((smallEtaleBaseChange
    (lvlMap D c B hD hX hc a)).map ((transitionBaseChangeIso D c B hD hX hc
      ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V.unop)).op
  have e7 := congrArg (fun f => (levelInverseImage G j).obj.map f.op)
    (transitionBaseChangeIso_from_comp a V.unop)
  simp only [op_comp, Functor.map_comp] at e7
  have e9 : ((etaleAbelianDirectImageCompIso'.{u, 0} (lvlMap D c B hD hX hc a)
      (toBottom D c B hD hX hc i) (toBottom D c B hD hX hc j) (toBottom_comp a)).hom.app
        (levelInverseImage G j)).hom.app
          (op ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V.unop)) =
      (levelInverseImage G j).obj.map ((smallEtaleBaseChangeComp' (lvlMap D c B hD hX hc a)
        (toBottom D c B hD hX hc i) (toBottom D c B hD hX hc j) (toBottom_comp a)).hom.app
          ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V.unop)).op :=
    smallEtalePushforwardComp'_hom_app_hom_app _ _ _ _ _ _ _
  rw [← e9] at e7
  have e8 : ∀ p, eqToHom p ≫ (levelInverseImage G j).obj.map ((levelToEtale D c B hD hX hc j).map
      (eqToHom (Functor.congr_obj (u_from_comp (sys D c B hD hX hc)
        (bottom_isTerminal D c B hD hX hc) a) V.unop))).op = 𝟙 _ :=
    fun p => eqToHom_comp_map_map_eqToHom _ _ _ p
  have hiso : IsIso ((levelInverseImage G j).obj.map ((transitionBaseChangeIso D c B hD hX hc
      ((bottom_isTerminal D c B hD hX hc).from j)).hom.app V.unop).op) :=
    Iso.isIso_hom ((levelInverseImage G j).obj.mapIso ((transitionBaseChangeIso D c B hD hX hc
      ((bottom_isTerminal D c B hD hX hc).from j)).app V.unop).op)
  have key := chase_aux e1 e2 e3 e4 e5 e6 e7 (e8 _) hiso
  exact key

/-- **The transition comparison of inverse images is the canonical one**: `levelComparison`
along `h : X_j ⟶ X_i` is the comparison `h⁻¹(f_i⁻¹G) ≅ f_j⁻¹G` of inverse images along
`f_j = h ≫ f_i`. -/
theorem levelComparison_eq {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    levelComparison G a = (etaleAbelianInverseImageCompIso'.{u, 0} (lvlMap D c B hD hX hc a)
      (toBottom D c B hD hX hc i) (toBottom D c B hD hX hc j) (toBottom_comp a)).inv.app G :=
  eq_leftAdjointCompIso_hom_app _ _ _ _ G _ (unit_toBottom_eq G a)

/-- The transition comparison `levelComparison G a : h⁻¹(f_i⁻¹G) ⟶ f_j⁻¹G` is an
isomorphism. -/
instance isIso_levelComparison {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    IsIso (levelComparison G a) := by
  rw [levelComparison_eq]
  infer_instance

/-- The components of `limitPushforwardIso`: restriction along the comparison of the functor
from the bottom level to the site of the limit with base change. -/
theorem limitPushforwardIso_hom_app_hom_app
    (M : Sheaf c.pt.smallEtaleTopology Ab.{u + 1})
    (V : ((sys D c B hD hX hc).C (bottom D c B hD hX hc))ᵒᵖ) :
    ((limitPushforwardIso.{u, u} D c B hD hX hc Ab.{u + 1}).hom.app M).hom.app V =
      M.obj.map ((toLimitBaseChangeIso.{u, u} D c B hD hX hc
        (bottom D c B hD hX hc)).hom.app V.unop).op := by
  simp only [limitPushforwardIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousComp, Iso.refl_hom,
    Iso.refl_inv]
  simp only [Functor.comp_obj, Functor.sheafPushforwardContinuousNatTrans, NatTrans.op_id,
    ObjectProperty.ι_obj, Functor.whiskerRight_id', Iso.symm_inv, Functor.whiskerRight_app,
    Functor.op_obj, NatTrans.op_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The projection `f_⊥ : X ⟶ X_⊥` is the projection `f_i : X ⟶ X_i` followed by
`f_{i⊥} : X_i ⟶ X_⊥`. -/
theorem lvlπ_bottom_eq (i : (sys D c B hD hX hc).I) :
    lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc) =
      lvlπ.{u, u} D c B hD hX hc i ≫ toBottom D c B hD hX hc i :=
  (c.w _).symm

/-- The comparison of the functor from the bottom level to the site of the limit with base
change, through a level. -/
theorem toLimitBaseChangeIso_bottom (i : (sys D c B hD hX hc).I)
    (V : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (toLimitBaseChangeIso.{u, u} D c B hD hX hc (bottom D c B hD hX hc)).hom.app V =
      (limitToEtale.{u, u} D c B hX).map (eqToHom (Functor.congr_obj
          (toLimitSmall_transition.{u, u} D c B hD hX hc
            ((bottom_isTerminal D c B hD hX hc).from i)) V).symm) ≫
        (toLimitBaseChangeIso.{u, u} D c B hD hX hc i).hom.app
          (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj V) ≫
        (smallEtaleBaseChange (lvlπ.{u, u} D c B hD hX hc i)).map
          ((transitionBaseChangeIso D c B hD hX hc
            ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V) ≫
        (smallEtaleBaseChangeComp' (lvlπ.{u, u} D c B hD hX hc i) (toBottom D c B hD hX hc i)
          (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc)) (lvlπ_bottom_eq i)).inv.app
            ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V) := by
  apply smallEtaleBaseChange_hom_ext
  have hc' := (affineEtaleSiteColimit D c B hD hX hc).toLimitFst_transition
    ((bottom_isTerminal D c B hD hX hc).from i) V
  have h1 := ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback
    (bottom D c B hD hX hc) V).isoPullback_hom_fst
  have h2' : ((toLimitBaseChangeIso.{u, u} D c B hD hX hc i).hom.app
        (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj V)).left ≫
      pullback.fst ((levelToEtale D c B hD hX hc i).obj
        (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj V)).hom
        (lvlπ.{u, u} D c B hD hX hc i) =
      ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst i).app
        (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj V) :=
    ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i
      (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj V)
      ).isoPullback_hom_fst
  have h3' : ((transitionBaseChangeIso D c B hD hX hc
        ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V).left ≫
      pullback.fst ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V).hom
        (toBottom D c B hD hX hc i) =
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst
        ((bottom_isTerminal D c B hD hX hc).from i)).app V :=
    ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback
      ((bottom_isTerminal D c B hD hX hc).from i) V).isoPullback_hom_fst
  have h4 := smallEtaleBaseChangeComp'_fst_fst (lvlπ.{u, u} D c B hD hX hc i)
    (toBottom D c B hD hX hc i) (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc))
    (lvlπ_bottom_eq i) ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V)
  have h4' : ((smallEtaleBaseChangeComp' (lvlπ.{u, u} D c B hD hX hc i)
      (toBottom D c B hD hX hc i) (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc))
      (lvlπ_bottom_eq i)).inv.app
        ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V)).left ≫
      pullback.fst ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V).hom
        (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc)) =
      pullback.fst ((smallEtaleBaseChange (toBottom D c B hD hX hc i)).obj
          ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V)).hom
          (lvlπ.{u, u} D c B hD hX hc i) ≫
        pullback.fst ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V).hom
          (toBottom D c B hD hX hc i) := by
    rw [← h4]
    have hih := congrArg (fun φ => φ.left)
      ((smallEtaleBaseChangeComp' (lvlπ.{u, u} D c B hD hX hc i) (toBottom D c B hD hX hc i)
        (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc)) (lvlπ_bottom_eq i)).inv_hom_id_app
          ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hih).trans (Category.id_comp _))
  have h5 := smallEtaleBaseChange_map_left_fst (lvlπ.{u, u} D c B hD hX hc i)
    ((transitionBaseChangeIso D c B hD hX hc ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V)
  refine h1.trans (hc'.trans ?_)
  refine Eq.trans ?_ (chain_aux _ _ _ _ _ _ _ _ _ _ _ h4' h5 h2' h3').symm
  congr 1

/-- The unit at `G` of the inverse-image–direct-image adjunction along `f_⊥ : X ⟶ X_⊥` is the
unit along `f_{i⊥}` followed by the direct image under `f_{i⊥}` of the unit along `f_i : X ⟶ X_i`
composed with `limitComparison G i`, read through the comparison of direct images along
`f_⊥ = f_i ≫ f_{i⊥}`. -/
theorem unit_lvlπ_eq (i : (sys D c B hD hX hc).I) :
    (etaleAbelianInverseImageDirectImageAdj.{u, 0}
        (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc))).unit.app G =
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} (toBottom D c B hD hX hc i)).unit.app G ≫
        (etaleAbelianDirectImage.{u, 0} (toBottom D c B hD hX hc i)).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (lvlπ.{u, u} D c B hD hX hc i)).unit.app
              (levelInverseImage G i) ≫
            (etaleAbelianDirectImage.{u, 0} (lvlπ.{u, u} D c B hD hX hc i)).map
              (limitComparison G i)) ≫
        (etaleAbelianDirectImageCompIso'.{u, 0} (lvlπ.{u, u} D c B hD hX hc i)
          (toBottom D c B hD hX hc i) (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc))
          (lvlπ_bottom_eq i)).hom.app (limitInverseImage G) := by
  apply (levelRestrict.{u, u} D c B hD hX hc Ab.{u + 1} (bottom D c B hD hX hc)).map_injective
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  have e1 := congrArg (fun φ => φ.app V) (ι_spec (sys D c B hD hX hc)
    (bottom_isTerminal D c B hD hX hc) (levelε G) (isUniversalArrow_levelε G)
    (toLimitSmall.{u, u} D c B hD hX hc) (toLimitSmall_transition.{u, u} D c B hD hX hc)
    (limitSitePrecoverage.{u, u} D c B hX).toGrothendieck (limitε G) i)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] at e1
  have e2 : (levelε G i).app V =
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (toBottom D c B hD hX hc i)).unit.app
          G).hom.app (op ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V.unop)) ≫
        (levelInverseImage G i).obj.map ((transitionBaseChangeIso D c B hD hX hc
          ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V.unop).op :=
    congrArg (fun t => _ ≫ t) (levelPushforwardIso_hom_app_hom_app i (levelInverseImage G i) V)
  have e3 : (limitε G).app V =
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0}
          (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc))).unit.app
          G).hom.app (op ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V.unop)) ≫
        (limitInverseImage G).obj.map ((toLimitBaseChangeIso.{u, u} D c B hD hX hc
          (bottom D c B hD hX hc)).hom.app V.unop).op :=
    congrArg (fun t => _ ≫ t) (limitPushforwardIso_hom_app_hom_app (limitInverseImage G) V)
  have e4 := (congrArg (fun φ => φ.app ((sys D c B hD hX hc).u
    ((bottom_isTerminal D c B hD hX hc).from i) |>.op.obj V)) (limitComparison_spec G i)).symm
  have e5 := ((etaleAbelianInverseImageDirectImageAdj.{u, 0}
    (lvlπ.{u, u} D c B hD hX hc i)).unit.app
      (levelInverseImage G i)).hom.naturality ((transitionBaseChangeIso D c B hD hX hc
        ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V.unop).op
  have e6 := (limitComparison G i).hom.naturality ((smallEtaleBaseChange
    (lvlπ.{u, u} D c B hD hX hc i)).map ((transitionBaseChangeIso D c B hD hX hc
      ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V.unop)).op
  have hT : (toLimitBaseChangeIso.{u, u} D c B hD hX hc (bottom D c B hD hX hc)).hom.app V.unop ≫
      (smallEtaleBaseChangeComp' (lvlπ.{u, u} D c B hD hX hc i) (toBottom D c B hD hX hc i)
          (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc)) (lvlπ_bottom_eq i)).hom.app
            ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V.unop) =
      (limitToEtale.{u, u} D c B hX).map (eqToHom (Functor.congr_obj
          (toLimitSmall_transition.{u, u} D c B hD hX hc
            ((bottom_isTerminal D c B hD hX hc).from i)) V.unop).symm) ≫
        (toLimitBaseChangeIso.{u, u} D c B hD hX hc i).hom.app
          (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj V.unop) ≫
        (smallEtaleBaseChange (lvlπ.{u, u} D c B hD hX hc i)).map
          ((transitionBaseChangeIso D c B hD hX hc
            ((bottom_isTerminal D c B hD hX hc).from i)).hom.app V.unop) := by
    rw [toLimitBaseChangeIso_bottom i V.unop]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  have e7 := congrArg (fun f => (limitInverseImage G).obj.map f.op) hT
  simp only [op_comp, Functor.map_comp] at e7
  have e9 : ((etaleAbelianDirectImageCompIso'.{u, 0} (lvlπ.{u, u} D c B hD hX hc i)
      (toBottom D c B hD hX hc i) (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc))
      (lvlπ_bottom_eq i)).hom.app (limitInverseImage G)).hom.app
          (op ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V.unop)) =
      (limitInverseImage G).obj.map ((smallEtaleBaseChangeComp' (lvlπ.{u, u} D c B hD hX hc i)
        (toBottom D c B hD hX hc i) (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc))
        (lvlπ_bottom_eq i)).hom.app
          ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj V.unop)).op :=
    smallEtalePushforwardComp'_hom_app_hom_app _ _ _ _ _ _ _
  rw [← e9] at e7
  have e8 : ∀ p, eqToHom p ≫ (limitInverseImage G).obj.map ((limitToEtale.{u, u} D c B hX).map
      (eqToHom (Functor.congr_obj (toLimitSmall_transition.{u, u} D c B hD hX hc
        ((bottom_isTerminal D c B hD hX hc).from i)) V.unop).symm)).op = 𝟙 _ :=
    fun p => eqToHom_comp_map_map_eqToHom _ _ _ p
  have hiso : IsIso ((limitInverseImage G).obj.map ((toLimitBaseChangeIso.{u, u} D c B hD hX hc
      (bottom D c B hD hX hc)).hom.app V.unop).op) :=
    Iso.isIso_hom ((limitInverseImage G).obj.mapIso ((toLimitBaseChangeIso.{u, u} D c B hD hX hc
      (bottom D c B hD hX hc)).app V.unop).op)
  have key := chase_aux e1 e2 e3 e4 e5 e6 e7 (e8 _) hiso
  exact key

/-- **The comparison of inverse images to the limit is the canonical one**: `limitComparison`
along the projection `f_i : X ⟶ X_i` is the comparison `f_i⁻¹(f_{i⊥}⁻¹G) ≅ f_⊥⁻¹G` of inverse
images along `f_⊥ = f_i ≫ f_{i⊥}`. -/
theorem limitComparison_eq (i : (sys D c B hD hX hc).I) :
    limitComparison G i = (etaleAbelianInverseImageCompIso'.{u, 0}
      (lvlπ.{u, u} D c B hD hX hc i) (toBottom D c B hD hX hc i)
      (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc)) (lvlπ_bottom_eq i)).inv.app G :=
  eq_leftAdjointCompIso_hom_app _ _ _ _ G _ (unit_lvlπ_eq G i)

/-- The comparison `limitComparison G i : f_i⁻¹(f_{i⊥}⁻¹G) ⟶ f_⊥⁻¹G` is an isomorphism. -/
instance isIso_limitComparison (i : (sys D c B hD hX hc).I) :
    IsIso (limitComparison G i) := by
  rw [limitComparison_eq]
  infer_instance

section Restriction

variable [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
  [∀ i : (sys D c B hD hX hc).I,
    HasExt.{u + 1} (Sheaf (lvl.{u, u} D c B hD hX hc i).smallEtaleTopology Ab.{u + 1})]
  [HasExt.{u + 1} (Sheaf c.pt.smallEtaleTopology Ab.{u + 1})]

/-- **A class of the bottom level that vanishes on the limit vanishes on some level**, for
affine levels. -/
theorem exists_toBottom_restriction_eq_zero (q : ℕ) (ξ : Sheaf.H.{u + 1} G q)
    (hξ : etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc)) G q ξ = 0) :
    ∃ j : (sys D c B hD hX hc).I,
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (toBottom D c B hD hX hc j) G q ξ = 0 := by
  have hy : extRestrictionMap (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc))
      (limitComparison G (bottom D c B hD hX hc)) q
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (toBottom D c B hD hX hc
        (bottom D c B hD hX hc)) G q ξ) = 0 := by
    refine (extRestrictionMap_apply _ _ _ _).trans ?_
    rw [etaleCohomologyRestrictionMap_restrict
      (toBottom D c B hD hX hc (bottom D c B hD hX hc))
      (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc))
      (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc)) (lvlπ_bottom_eq _), hξ,
      Ext.zero_comp, Ext.zero_comp]
    rfl
  obtain ⟨A', f, hf⟩ := exists_extRestrictionMap_levelComparison_eq_zero G q
    (Over.mk (𝟙 (bottom D c B hD hX hc))) _ hy
  refine ⟨A'.left, ?_⟩
  replace hf := (extRestrictionMap_apply _ _ _ _).symm.trans hf
  dsimp only [Over.mk_left] at hf
  rwa [levelComparison_eq, etaleCohomologyRestrictionMap_restrict
    (toBottom D c B hD hX hc (bottom D c B hD hX hc)) (lvlMap D c B hD hX hc f.left)
    (toBottom D c B hD hX hc A'.left) (toBottom_comp f.left),
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id_app,
    Ext.comp_mk₀_id] at hf

/-- **Every class on the limit comes from some level**, for affine levels: a class of
`H^q(X, f_⊥⁻¹G)` is the restriction of a class of some `H^q(X_j, f_j⁻¹G)`, read through the
canonical comparison `f_j'⁻¹f_j⁻¹G ≅ f_⊥⁻¹G` of inverse images along `X ⟶ X_j ⟶ X_⊥`. -/
theorem exists_toBottom_restriction_eq (q : ℕ) (x : Sheaf.H.{u + 1} (limitInverseImage G) q) :
    ∃ (j : (sys D c B hD hX hc).I) (y : Sheaf.H.{u + 1} (levelInverseImage G j) q),
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (lvlπ.{u, u} D c B hD hX hc j)
          (levelInverseImage G j) q y).comp
        (Ext.mk₀ ((etaleAbelianInverseImageCompIso'.{u, 0} (lvlπ.{u, u} D c B hD hX hc j)
          (toBottom D c B hD hX hc j) (lvlπ.{u, u} D c B hD hX hc (bottom D c B hD hX hc))
          (lvlπ_bottom_eq j)).inv.app G)) (add_zero q) = x := by
  obtain ⟨A, y, hy⟩ := exists_extRestrictionMap_limitComparison_eq G q x
  refine ⟨A.left, y, ?_⟩
  rw [← limitComparison_eq]
  exact (extRestrictionMap_apply _ _ _ _).symm.trans hy

end Restriction

end Comparison

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- Both halves of Stacks 09YQ, after passing to the levels `i ≥ i₀`, which form a directed set
with least element `i₀`. -/
private theorem exists_le_restriction_eq_and_eq_zero {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] [∀ i, IsAffine (D.obj i)] (c : Cone D)
    (hc : IsLimit c) (i₀ : I) (G : Sheaf (D.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (∀ (q : ℕ) (ξ : Sheaf.H.{u + 1} G q),
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (c.π.app (op i₀)) G q ξ = 0 →
      ∃ (i : I) (h : i₀ ≤ i),
        etaleCohomologyRestrictionMap.{u, 0, u + 1} (D.map (homOfLE h).op) G q ξ = 0) ∧
    ∀ (q : ℕ)
      (x : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (c.π.app (op i₀))).obj G) q),
      ∃ (i : I) (h : i₀ ≤ i)
        (y : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (D.map (homOfLE h).op)).obj G) q),
        (etaleCohomologyRestrictionMap.{u, 0, u + 1} (c.π.app (op i)) _ q y).comp
          (Ext.mk₀ ((etaleAbelianInverseImageCompIso'.{u, 0} (c.π.app (op i))
            (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).inv.app G))
          (add_zero q) = x := by
  let J := {i : I // i₀ ≤ i}
  let : OrderBot J := { bot := ⟨i₀, le_rfl⟩, bot_le := fun a => a.2 }
  have : IsDirected J (· ≤ ·) := ⟨fun a b => by
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩⟩
  have : Nonempty J := ⟨⊥⟩
  let incl : J ⥤ I := (Subtype.mono_coe (fun i : I => i₀ ≤ i)).functor
  have : incl.Final := by
    refine Functor.final_of_exists_of_isFiltered _ (fun a => ?_) (fun {d c} f g => ?_)
    · obtain ⟨b, hab, hb⟩ := directed_of (· ≤ ·) a i₀
      exact ⟨⟨b, hb⟩, ⟨homOfLE hab⟩⟩
    · exact ⟨c, 𝟙 _, Subsingleton.elim _ _⟩
  let D' : Jᵒᵖ ⥤ Scheme.{u} := incl.op ⋙ D
  have : ∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (D'.map a) := fun a =>
    inferInstanceAs (IsAffineHom (D.map _))
  have : ∀ i : Jᵒᵖ, IsAffine (D'.obj i) := fun i => inferInstanceAs (IsAffine (D.obj _))
  let c' : Cone D' := c.whisker incl.op
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv incl.op c).symm hc
  let S₀ : Set Scheme.{u} := insert c.pt (Set.range D'.obj)
  let B := BigEtaleSite.ofSet S₀
  have hD : ∀ i, B.Contains (D'.obj i) := fun i =>
    BigEtaleSite.contains_ofSet S₀ (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  have hX : B.Contains c'.pt := BigEtaleSite.contains_ofSet S₀ (Set.mem_insert _ _)
  refine ⟨fun q ξ hξ => ?_, fun q x => ?_⟩
  · obtain ⟨j, hj⟩ := exists_toBottom_restriction_eq_zero (D := D') (c := c') (B := B) (hD := hD)
      (hX := hX) (hc := hc') G q ξ hξ
    refine ⟨(idx D' c' B hD hX hc' j).unop.1, (idx D' c' B hD hX hc' j).unop.2, ?_⟩
    rwa [show D.map (homOfLE (idx D' c' B hD hX hc' j).unop.2).op = toBottom D' c' B hD hX hc' j
      from congrArg D.map (Subsingleton.elim _ _)]
  · obtain ⟨j, y, hy⟩ := exists_toBottom_restriction_eq (D := D') (c := c') (B := B) (hD := hD)
      (hX := hX) (hc := hc') G q x
    refine ⟨(idx D' c' B hD hX hc' j).unop.1, (idx D' c' B hD hX hc' j).unop.2, ?_⟩
    have key : ∀ (f : D.obj (op (idx D' c' B hD hX hc' j).unop.1) ⟶ D.obj (op i₀))
        (hf : f = toBottom D' c' B hD hX hc' j)
        (hπ : c.π.app (op i₀) = c.π.app (op (idx D' c' B hD hX hc' j).unop.1) ≫ f),
        ∃ y : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} f).obj G) q,
          (etaleCohomologyRestrictionMap.{u, 0, u + 1}
              (c.π.app (op (idx D' c' B hD hX hc' j).unop.1)) _ q y).comp
            (Ext.mk₀ ((etaleAbelianInverseImageCompIso'.{u, 0}
              (c.π.app (op (idx D' c' B hD hX hc' j).unop.1)) f (c.π.app (op i₀)) hπ).inv.app G))
            (add_zero q) = x := by
      intro f hf hπ
      subst hf
      exact ⟨y, hy⟩
    exact key _ (congrArg D.map (Subsingleton.elim _ _)) _

/-- **Stacks 09YQ, injectivity, on mainstream étale cohomology, for affine levels.** Let `I` be a
directed set, `(X_i)` an inverse system of affine schemes over `I` with affine transition
morphisms and limit `X`, `i₀ ∈ I`, `G` an abelian sheaf on `X_{i₀}` and `ξ ∈ H^q(X_{i₀}, G)`.
If `ξ` restricts to zero on `X`, it restricts to zero on some `X_i` with `i ≥ i₀`. -/
theorem exists_le_restriction_eq_zero {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (ξ : Sheaf.H.{u + 1} G q)
    (hξ : etaleCohomologyRestrictionMap.{u, 0, u + 1} (c.π.app (op i₀)) G q ξ = 0) :
    ∃ (i : I) (h : i₀ ≤ i),
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (D.map (homOfLE h).op) G q ξ = 0 :=
  (exists_le_restriction_eq_and_eq_zero D c hc i₀ G).1 q ξ hξ

/-- **Stacks 09YQ, surjectivity, on mainstream étale cohomology, for affine levels.** Let `I` be
a directed set, `(X_i)` an inverse system of affine schemes over `I` with affine transition
morphisms and limit `X`, `i₀ ∈ I` and `G` an abelian sheaf on `X_{i₀}`. Every class of
`H^q(X, f_{i₀}⁻¹G)` is the restriction of a class of `H^q(X_i, f_{ii₀}⁻¹G)` for some `i ≥ i₀`,
read through the canonical comparison `f_i⁻¹f_{ii₀}⁻¹G ≅ f_{i₀}⁻¹G`. -/
theorem exists_le_restriction_eq {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (c.π.app (op i₀))).obj G) q) :
    ∃ (i : I) (h : i₀ ≤ i)
      (y : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (D.map (homOfLE h).op)).obj G) q),
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (c.π.app (op i)) _ q y).comp
        (Ext.mk₀ ((etaleAbelianInverseImageCompIso'.{u, 0} (c.π.app (op i))
          (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).inv.app G))
        (add_zero q) = x :=
  (exists_le_restriction_eq_and_eq_zero D c hc i₀ G).2 q x

end Stacks.EtaleCohomology.LimitSiteBridge

