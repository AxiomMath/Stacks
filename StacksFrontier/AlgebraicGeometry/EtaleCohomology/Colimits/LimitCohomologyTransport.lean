module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitInverseImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
-- the degree-zero shape of the cohomology maps of Stacks 09YP, used inside a proof only
import all StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites

/-!
# Étale cohomology of the levels of a limit, read on the sites of Stacks 0EYL

Let `D` be an inverse system of schemes with affine transition morphisms and limit `X`, and let
`(sys D c B hD hX hc)` be the inverse system of small affine étale sites of Stacks 0EYL. Each level
`i` of that system is a dense subsite of Mathlib's small étale site of the scheme `X_i` it models,
so restriction `R_i` of abelian sheaves to it is an equivalence. This file identifies the
cohomology `H^p(X_i, P) = Ext^p(ℤ, P)` of an abelian sheaf `P` on `X_i` with the right derived
functor of sections over a terminal object `V` of the level, applied to `R_i P`:

`H^p(X_i, P) ≅ R^p Γ(V, -)(R_i P)`.

It is the composite of the identification of `Ext` out of `ℤ` with the right derived functors of
sections over a terminal object (`ModuleSheafCohomology.extFunctorObjIsoRightDerived`), and of the
invariance of right derived functors under precomposition with an exact functor preserving
injectives (`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`).

## Main definitions

* `Stacks.EtaleCohomology.LimitSiteBridge.denseCohomologyIso` — the identification above, for any
  dense subsite.
* `Stacks.EtaleCohomology.LimitSiteBridge.levelComparison` — the comparison `h⁻¹(f_i⁻¹G) ⟶ f_j⁻¹G`
  along a transition whose adjoint is the transition map of the system of inverse images.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open ModuleSheafCohomology Stacks.Cohomology.CompositeRightDerived Stacks.WeakSites.PullbackSystem

universe u

namespace Stacks.EtaleCohomology.LimitSiteBridge

open Stacks.EtaleCohomology.AffineLimitCohomology

/-- Abelian sheaves on Mathlib's small étale site, with coefficients one universe above the
scheme universe, form an abelian category. Mathlib's instance for this site is stated at the
coefficient universe of the site's morphisms, and instance search reaches it and gets stuck on a
goal at this universe rather than backtracking, so the statement is restated here. -/
@[instance_reducible]
def abelianSheafSmallEtale (X : Scheme.{u}) :
    Abelian (Sheaf X.smallEtaleTopology Ab.{u + 1}) :=
  CategoryTheory.sheafIsAbelian

/-- Sheafification of abelian presheaves on Mathlib's small étale site, with coefficients one
universe above the scheme universe; restated for the same reason as `abelianSheafSmallEtale`. -/
theorem hasSheafifySmallEtale (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology Ab.{u + 1} :=
  inferInstance

attribute [local instance] abelianSheafSmallEtale hasSheafifySmallEtale

/-! ### Restriction along a composite -/

/-- **Restriction on étale cohomology along a composite**: restricting along `a` and then along
`b` is restricting along `ba = b ≫ a`, followed by the comparison `(ba)⁻¹ ≅ b⁻¹a⁻¹`. -/
theorem etaleCohomologyRestrictionMap_restrict {X Y Z : Scheme.{u}} (a : Y ⟶ X) (b : Z ⟶ Y)
    (ba : Z ⟶ X) (hba : ba = b ≫ a)
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology Ab.{u + 1})]
    [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology Ab.{u + 1})]
    (P : Sheaf X.smallEtaleTopology Ab.{u + 1}) (n : ℕ) (ξ : Sheaf.H.{u + 1} P n) :
    etaleCohomologyRestrictionMap.{u, 0, u + 1} b ((etaleAbelianInverseImage.{u, 0} a).obj P) n
        (etaleCohomologyRestrictionMap.{u, 0, u + 1} a P n ξ) =
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} ba P n ξ).comp
        (Ext.mk₀ ((etaleAbelianInverseImageCompIso'.{u, 0} b a ba hba).hom.app P))
        (add_zero n) := by
  have : EnoughInjectives (Sheaf X.smallEtaleTopology Ab.{u + 1}) := by
    have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
    infer_instance
  let κ := etaleAbelianInverseImageCompIso'.{u, 0} b a ba hba
  let Zx := (constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))
  have h1 : ξ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} a ⋙
      etaleAbelianInverseImage.{u, 0} b) = (Ext.mk₀ (κ.inv.app Zx)).comp
        ((ξ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} ba)).comp
          (Ext.mk₀ (κ.hom.app P)) (add_zero n)) (zero_add n) := by
    rw [← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor κ.hom Zx n ξ, Ext.mk₀_comp_mk₀_assoc,
      ← NatTrans.comp_app, κ.inv_hom_id, NatTrans.id_app, Ext.mk₀_id_comp]
  have hc := etaleAbelianInverseImageConstantIso_comp.{u, 0} a b ba hba
    (AddCommGrpCat.of (ULift ℤ))
  have hc' : ((etaleAbelianInverseImageConstantIso.{u, 0} b).app
        (AddCommGrpCat.of (ULift ℤ))).inv ≫
      (etaleAbelianInverseImage.{u, 0} b).map
        ((etaleAbelianInverseImageConstantIso.{u, 0} a).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
      κ.inv.app Zx =
      ((etaleAbelianInverseImageConstantIso.{u, 0} ba).app (AddCommGrpCat.of (ULift ℤ))).inv := by
    have e : ((etaleAbelianInverseImage.{u, 0} b).mapIso
          ((etaleAbelianInverseImageConstantIso.{u, 0} a).app (AddCommGrpCat.of (ULift ℤ))) ≪≫
        (etaleAbelianInverseImageConstantIso.{u, 0} b).app (AddCommGrpCat.of (ULift ℤ))).inv =
        (κ.symm.app Zx ≪≫
          (etaleAbelianInverseImageConstantIso.{u, 0} ba).app (AddCommGrpCat.of (ULift ℤ))).inv :=
      congrArg Iso.inv (Iso.ext hc)
    simp only [Iso.trans_inv, Functor.mapIso_inv] at e
    rw [← Category.assoc, e, Category.assoc]
    simp
  simp only [etaleCohomologyRestrictionMap_apply]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor, h1, Ext.mk₀_comp_mk₀_assoc,
    Ext.mk₀_comp_mk₀_assoc, Category.assoc, hc', Ext.comp_assoc_of_third_deg_zero]

/-! ### Cohomology read on a dense subsite, and the maps between such readings -/

section Generic

variable {X Y : Scheme.{u}} (h : Y ⟶ X)
  {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C) (ι : C ⥤ X.Etale)
  [ι.IsDenseSubsite J X.smallEtaleTopology]
  {C' : Type (u + 1)} [SmallCategory C'] (J' : GrothendieckTopology C') (ι' : C' ⥤ Y.Etale)
  [ι'.IsDenseSubsite J' Y.smallEtaleTopology]

/-- Restriction of abelian sheaves to a dense subsite is additive. -/
instance denseRestrict_additive :
    (ι.sheafPushforwardContinuous Ab.{u + 1} J X.smallEtaleTopology).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction of abelian sheaves to a dense subsite preserves injective objects: it is an
equivalence. -/
instance denseRestrict_preservesInjectiveObjects :
    (ι.sheafPushforwardContinuous Ab.{u + 1} J X.smallEtaleTopology).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ι.sheafPushforwardContinuous Ab.{u + 1} J X.smallEtaleTopology).asEquivalence.symm.toAdjunction

variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology Ab.{u + 1})]

/-- **The cohomology of an abelian sheaf on a scheme, read on a dense subsite.** For a dense
subsite `ι : C ⥤ X_étale`, an object `V` of `C` whose image is terminal and an abelian sheaf `P`
on `X`, `H^p(X, P) ≅ R^p Γ(V, -)(P|_C)`: `Ext` out of `ℤ` is the right derived functor of
sections over a terminal object, and right derived functors do not change under precomposition
with the restriction, which is an equivalence. -/
def denseCohomologyIso (V : C) (hT : IsTerminal (ι.obj V))
    (P : Sheaf X.smallEtaleTopology Ab.{u + 1}) (p : ℕ) :
    (extFunctorObj (zSheaf X) p).obj P ≅
      (((sheafSections J Ab.{u + 1}).obj (op V)).rightDerived p).obj
        ((ι.sheafPushforwardContinuous Ab.{u + 1} J X.smallEtaleTopology).obj P) :=
  (extFunctorObjIsoRightDerived (sectionsOver (ι.obj V)) (zSheaf X)
      (sectionsCorepresentation hT) p).app P ≪≫
    (injectiveResolution P).isoRightDerivedObj (sectionsOver (ι.obj V)) p ≪≫
    ((mapInjRes (ι.sheafPushforwardContinuous Ab.{u + 1} J X.smallEtaleTopology)
      (injectiveResolution P)).isoRightDerivedObj ((sheafSections J Ab.{u + 1}).obj (op V)) p).symm

open Stacks.WeakSites.ColimitSiteCohomology in
/-- `denseCohomologyIso` at equal objects, through the identification of the cohomology over
equal objects. -/
theorem denseCohomologyIso_hom_comp_cohomologyCongr {V V' : C} (e : V = V')
    (hT : IsTerminal (ι.obj V)) (hT' : IsTerminal (ι.obj V'))
    (P : Sheaf X.smallEtaleTopology Ab.{u + 1}) (p : ℕ) :
    (denseCohomologyIso J ι V hT P p).hom ≫ cohomologyCongr.{u + 1, 0} J p e
        ((ι.sheafPushforwardContinuous Ab.{u + 1} J X.smallEtaleTopology).obj P) =
      (denseCohomologyIso J ι V' hT' P p).hom := by
  subst e
  rw [Subsingleton.elim hT hT']
  simp [cohomologyCongr]

variable (v : C ⥤ C') [v.IsContinuous J J'] (τ : v ⋙ ι' ≅ ι ⋙ smallEtaleBaseChange h)

/-- **Direct image along `h`, restricted to the dense subsites**, is the direct image along
`v : C ⥤ C'` of the restriction, when `v` covers base change along `h`. -/
def densePushforwardIso :
    etaleAbelianDirectImage.{u, 0} h ⋙ ι.sheafPushforwardContinuous Ab.{u + 1} J _ ≅
      ι'.sheafPushforwardContinuous Ab.{u + 1} J' _ ⋙
        v.sheafPushforwardContinuous Ab.{u + 1} J J' :=
  let := Functor.isContinuous_comp ι (smallEtaleBaseChange h) J X.smallEtaleTopology
    Y.smallEtaleTopology
  let := Functor.isContinuous_comp v ι' J J' Y.smallEtaleTopology
  Functor.sheafPushforwardContinuousIso τ.symm Ab.{u + 1} _ _

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology Ab.{u + 1})] in
/-- The components of `densePushforwardIso`: restriction along `τ`. -/
theorem densePushforwardIso_hom_app_hom_app (M : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    (W : Cᵒᵖ) :
    ((densePushforwardIso h J ι J' ι' v τ).hom.app M).hom.app W =
      M.obj.map (τ.hom.app W.unop).op := by
  rfl

/-- The degreewise datum `IsCohomologyMap` asks for, from a cochain map into a direct image. -/
def denseComplexComponent {I : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf Y.smallEtaleTopology Ab.{u + 1}) ℕ}
    (ζ : I ⟶ ((etaleAbelianDirectImage.{u, 0} h).mapHomologicalComplex _).obj K) (n : ℕ) :
    ((ι.sheafPushforwardContinuous Ab.{u + 1} J _).obj (I.X n)).obj ⟶
      v.op ⋙ ((ι'.sheafPushforwardContinuous Ab.{u + 1} J' _).obj (K.X n)).obj :=
  ((ι.sheafPushforwardContinuous Ab.{u + 1} J _).map (ζ.f n) ≫
    (densePushforwardIso h J ι J' ι' v τ).hom.app (K.X n)).hom

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology Ab.{u + 1})] in
/-- The components `denseComplexComponent` commute with the differentials of the restricted
complexes. -/
theorem denseComplexComponent_comm {I : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf Y.smallEtaleTopology Ab.{u + 1}) ℕ}
    (ζ : I ⟶ ((etaleAbelianDirectImage.{u, 0} h).mapHomologicalComplex _).obj K) (n n' : ℕ)
    (_ : (ComplexShape.up ℕ).Rel n n') :
    ((((ι.sheafPushforwardContinuous Ab.{u + 1} J _).mapHomologicalComplex _).obj I).d n n').hom ≫
        denseComplexComponent h J ι J' ι' v τ ζ n' =
      denseComplexComponent h J ι J' ι' v τ ζ n ≫ Functor.whiskerLeft v.op
        ((((ι'.sheafPushforwardContinuous Ab.{u + 1} J' _).mapHomologicalComplex _).obj K).d
          n n').hom := by
  have hc := ζ.comm n n'
  have hn := (densePushforwardIso h J ι J' ι' v τ).hom.naturality (K.d n n')
  have key : (ι.sheafPushforwardContinuous Ab.{u + 1} J _).map (I.d n n') ≫
      (ι.sheafPushforwardContinuous Ab.{u + 1} J _).map (ζ.f n') ≫
        (densePushforwardIso h J ι J' ι' v τ).hom.app (K.X n') =
      ((ι.sheafPushforwardContinuous Ab.{u + 1} J _).map (ζ.f n) ≫
        (densePushforwardIso h J ι J' ι' v τ).hom.app (K.X n)) ≫
        (v.sheafPushforwardContinuous Ab.{u + 1} J J').map
          ((ι'.sheafPushforwardContinuous Ab.{u + 1} J' _).map (K.d n n')) := by
    rw [← Functor.map_comp_assoc, ← hc, Functor.map_comp_assoc, Category.assoc]
    exact congrArg (_ ≫ ·) hn
  exact congrArg (fun t => t.hom) key


/-- Conjugating by composites `x ≪≫ y ≪≫ z⁻¹` of three isomorphisms. -/
theorem conj_trans_trans_symm {𝒜 : Type*} [Category 𝒜] {A B C D A' B' C' D' : 𝒜}
    (x : A ≅ B) (y : B ≅ C) (z : D ≅ C) (x' : A' ≅ B') (y' : B' ≅ C') (z' : D' ≅ C')
    (E : A ⟶ A') (M : C ⟶ C')
    (hM : y.inv ≫ x.inv ≫ E ≫ x'.hom ≫ y'.hom = M) :
    (x ≪≫ y ≪≫ z.symm).inv ≫ E ≫ (x' ≪≫ y' ≪≫ z'.symm).hom = z.hom ≫ M ≫ z'.inv := by
  subst hM
  simp

/-- Transporting a square through isomorphisms, after cancelling an isomorphism on the right. -/
theorem trans_symm_comp_eq_of_comp_eq {𝒜 : Type*} [Category 𝒜] {H H' D D' R R' R'' : 𝒜}
    (θ' : H' ≅ R') (o' : D' ≅ R') (θ : H ≅ R) (o : D ≅ R) (d : D' ⟶ D) (M : H' ⟶ H)
    (k : R ⟶ R'') [hk : IsIso k]
    (h : o'.inv ≫ d ≫ o.hom ≫ k = θ'.inv ≫ M ≫ θ.hom ≫ k) :
    (θ' ≪≫ o'.symm).hom ≫ d = M ≫ (θ ≪≫ o.symm).hom := by
  simp only [← Category.assoc] at h
  have h' := (cancel_mono k).1 h
  simp only [Category.assoc] at h'
  have h'' := congrArg (fun t => θ'.hom ≫ t ≫ o.inv) h'
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] at h''
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using h''

/-- Transporting a triangle through isomorphisms, after cancelling an isomorphism on the right. -/
theorem trans_symm_comp_eq_of_comp_eq' {𝒜 : Type*} [Category 𝒜] {H H' D R R' R'' : 𝒜}
    (θ : H ≅ R) (o : D ≅ R) (Ψ : H' ≅ R') (l : D ⟶ R') (L : H ⟶ H') (k : R' ⟶ R'')
    [hk : IsIso k] (h : o.inv ≫ l ≫ k = θ.inv ≫ L ≫ Ψ.hom ≫ k) :
    (θ ≪≫ o.symm).hom ≫ l = L ≫ Ψ.hom := by
  simp only [← Category.assoc] at h
  have h' := (cancel_mono k).1 h
  simp only [Category.assoc] at h'
  have h'' := congrArg (fun t => θ.hom ≫ t) h'
  simp only [Iso.hom_inv_id_assoc] at h''
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using h''

/-- The image of an injective resolution under an exact functor preserving injectives, in
degree zero: its augmentation is the image of the augmentation. -/
theorem mapInjRes_ι_f_zero {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ]
    (L : 𝒜 ⥤ ℬ) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.PreservesInjectiveObjects] {Z : 𝒜} (I : InjectiveResolution Z) :
    (mapInjRes L I).ι.f 0 = L.map (I.ι.f 0) := by
  dsimp [mapInjRes]
  simp

/-- A composite through conjugation by composites `x ≪≫ y ≪≫ z⁻¹`, from the three pieces. -/
theorem comp_conj_trans_trans_symm {𝒜 : Type*} [Category 𝒜] {A B C D A' B' C' D' W W' : 𝒜}
    (x : A ≅ B) (y : B ≅ C) (z : D ≅ C) (x' : A' ≅ B') (y' : B' ≅ C') (z' : D' ≅ C')
    (E : A ⟶ A') (t : W ⟶ D) (t' : W' ⟶ D') (s : W ⟶ B) (s' : W' ⟶ B') (r : W ⟶ W')
    (ha : t ≫ z.hom ≫ y.inv = s) (hb : s ≫ x.inv ≫ E ≫ x'.hom = r ≫ s')
    (hc : t' ≫ z'.hom ≫ y'.inv = s') :
    t ≫ (x ≪≫ y ≪≫ z.symm).inv ≫ E ≫ (x' ≪≫ y' ≪≫ z'.symm).hom = r ≫ t' := by
  subst ha hc
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc] at hb ⊢
  rw [reassoc_of% hb]
  simp

/-- **Restriction on étale cohomology in degree zero** is restriction of sections: under the
identifications `H⁰ = R⁰Γ(T, -)` with sections over terminal objects, restriction along `h`
followed by `g : h⁻¹P ⟶ Q` is the unit `P ⟶ h_*h⁻¹P` over `T`, restriction along
`k : T' ⟶ T ×_X Y`, then `g`. -/
theorem extRestrictionMap_zero_comm {T : X.Etale} (hT : IsTerminal T) {T' : Y.Etale}
    (hT' : IsTerminal T') (k : T' ⟶ (smallEtaleBaseChange h).obj T)
    {P : Sheaf X.smallEtaleTopology Ab.{u + 1}} {Q : Sheaf Y.smallEtaleTopology Ab.{u + 1}}
    (g : (etaleAbelianInverseImage.{u, 0} h).obj P ⟶ Q) :
    (sectionsOver T).toRightDerivedZero.app P ≫
        (extFunctorObjIsoRightDerived (sectionsOver T) (zSheaf X) (sectionsCorepresentation hT)
          0).inv.app P ≫ extRestrictionMap h g 0 ≫
        (extFunctorObjIsoRightDerived (sectionsOver T') (zSheaf Y) (sectionsCorepresentation hT')
          0).hom.app Q =
      (sectionsRestriction h k).app P ≫ g.hom.app (op T') ≫
        (sectionsOver T').toRightDerivedZero.app Q := by
  have hA := NatTrans.congr_app (Stacks.Cohomology.ExtComparison.extMapComp_conj_zero
    (etaleAbelianInverseImage.{u, 0} h) (sectionsOver T') (zSheaf Y)
    (sectionsCorepresentation hT') (sectionsOver T) (zSheaf X) (sectionsCorepresentation hT)
    (zComparison h)) P
  rw [derivedSectionsMap_eq_sectionsRestriction h hT hT' k] at hA
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hA
  have hnat := (extFunctorObjIsoRightDerived (sectionsOver T') (zSheaf Y)
    (sectionsCorepresentation hT') 0).hom.naturality g
  have hz := (sectionsOver T').toRightDerivedZero.naturality g
  simp only [extRestrictionMap, Category.assoc]
  rw [hnat, reassoc_of% hA, Functor.rightDerivedZeroIsoSelf_inv_hom_id_app_assoc]
  exact congrArg (_ ≫ ·) hz.symm

/-- The degree-zero comparison `G ⟶ R⁰G` is unchanged by precomposition with an exact functor
preserving injectives, read on the transported resolution. -/
theorem toRightDerivedZero_mapInjRes {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    [Abelian 𝒜] [Abelian ℬ] [Abelian 𝒞] [HasInjectiveResolutions 𝒜] [HasInjectiveResolutions ℬ]
    (L : 𝒜 ⥤ ℬ) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.PreservesInjectiveObjects] (G : ℬ ⥤ 𝒞) [G.Additive] {Z : 𝒜} (I : InjectiveResolution Z) :
    G.toRightDerivedZero.app (L.obj Z) ≫ ((mapInjRes L I).isoRightDerivedObj G 0).hom ≫
        (I.isoRightDerivedObj (L ⋙ G) 0).inv =
      (L ⋙ G).toRightDerivedZero.app Z := by
  have h' : (mapInjRes L I).toRightDerivedZero' G = I.toRightDerivedZero' (L ⋙ G) :=
    (cancel_mono (HomologicalComplex.iCycles
      ((G.mapHomologicalComplex _).obj (mapInjRes L I).cocomplex) 0)).1
      (((mapInjRes L I).toRightDerivedZero'_comp_iCycles G).trans
        ((congrArg G.map (mapInjRes_ι_f_zero L I)).trans
          (I.toRightDerivedZero'_comp_iCycles (L ⋙ G)).symm))
  rw [(mapInjRes L I).toRightDerivedZero_eq G, I.toRightDerivedZero_eq (L ⋙ G)]
  exact (Category.assoc _ _ _).trans ((congrArg ((mapInjRes L I).toRightDerivedZero' G ≫ ·)
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _)))).trans
    (congrArg (· ≫ (CochainComplex.isoHomologyπ₀
      (((L ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).hom ≫
        (I.isoRightDerivedObj (L ⋙ G) 0).inv) h'))

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology Ab.{u + 1})] in
open Stacks.WeakSites.ColimitSiteCohomology in
/-- **A cochain map into a direct image computes a cohomology map on the dense subsites.** Given
injective resolutions `I` of `P` and `K` of `Q` and a cochain map `ζ : I ⟶ h_*K` extending
`ξ : P ⟶ h_*Q`, the map induced on the cohomology of the sections over `V` of the restricted
resolutions is the cohomology map of Stacks 09YP determined by the restriction of `ξ`. -/
theorem isCohomologyMap_dense {P : Sheaf X.smallEtaleTopology Ab.{u + 1}}
    {Q : Sheaf Y.smallEtaleTopology Ab.{u + 1}} (I : InjectiveResolution P)
    (K : InjectiveResolution Q)
    (ζ : I.cocomplex ⟶ ((etaleAbelianDirectImage.{u, 0} h).mapHomologicalComplex _).obj K.cocomplex)
    (ξ : P ⟶ (etaleAbelianDirectImage.{u, 0} h).obj Q)
    (hζ : I.ι.f 0 ≫ ζ.f 0 = ξ ≫ (etaleAbelianDirectImage.{u, 0} h).map (K.ι.f 0))
    (V : C) (p : ℕ) :
    IsCohomologyMap.{u + 1, 0} J J' v
      ((ι.sheafPushforwardContinuous Ab.{u + 1} J _).map ξ ≫
        (densePushforwardIso h J ι J' ι' v τ).hom.app Q).hom V p
      (((mapInjRes (ι.sheafPushforwardContinuous Ab.{u + 1} J _) I).isoRightDerivedObj
          ((sheafSections J Ab.{u + 1}).obj (op V)) p).hom ≫
        HomologicalComplex.homologyMap
          (sectionsComplexMap.{u + 1, 0} v _ _ (denseComplexComponent h J ι J' ι' v τ ζ)
            (denseComplexComponent_comm h J ι J' ι' v τ ζ) V) p ≫
        ((mapInjRes (ι'.sheafPushforwardContinuous Ab.{u + 1} J' _) K).isoRightDerivedObj
          ((sheafSections J' Ab.{u + 1}).obj (op (v.obj V))) p).inv) := by
  refine ⟨mapInjRes (ι.sheafPushforwardContinuous Ab.{u + 1} J _) I,
    mapInjRes (ι'.sheafPushforwardContinuous Ab.{u + 1} J' _) K,
    denseComplexComponent h J ι J' ι' v τ ζ, denseComplexComponent_comm h J ι J' ι' v τ ζ, ?_, rfl⟩
  have hn := (densePushforwardIso h J ι J' ι' v τ).hom.naturality (K.ι.f 0)
  have key : (ι.sheafPushforwardContinuous Ab.{u + 1} J _).map (I.ι.f 0) ≫
      (ι.sheafPushforwardContinuous Ab.{u + 1} J _).map (ζ.f 0) ≫
        (densePushforwardIso h J ι J' ι' v τ).hom.app (K.cocomplex.X 0) =
      ((ι.sheafPushforwardContinuous Ab.{u + 1} J _).map ξ ≫
        (densePushforwardIso h J ι J' ι' v τ).hom.app Q) ≫
        (v.sheafPushforwardContinuous Ab.{u + 1} J J').map
          ((ι'.sheafPushforwardContinuous Ab.{u + 1} J' _).map (K.ι.f 0)) := by
    have e1 := congrArg (fun t => (ι.sheafPushforwardContinuous Ab.{u + 1} J _).map t ≫
      (densePushforwardIso h J ι J' ι' v τ).hom.app (K.cocomplex.X 0)) hζ
    have e2 := (ι.sheafPushforwardContinuous Ab.{u + 1} J _).map_comp (I.ι.f 0) (ζ.f 0)
    have e3 := (ι.sheafPushforwardContinuous Ab.{u + 1} J _).map_comp ξ
      ((etaleAbelianDirectImage.{u, 0} h).map (K.ι.f 0))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e2.symm).trans (e1.trans
      ((congrArg (· ≫ _) e3).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hn).trans (Category.assoc _ _ _).symm)))))
  have k2 := congrArg (fun t => t.hom) key
  rw [mapInjRes_ι_f_zero, mapInjRes_ι_f_zero]
  exact k2

/-- The cochain map `I ⟶ h_*K` adjoint to a cochain map `h⁻¹I ⟶ K`: degreewise the unit of the
adjunction followed by the direct image. -/
def etaleAdjunctComplex (I : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℕ)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology Ab.{u + 1}) ℕ)
    (χ : ((etaleAbelianInverseImage.{u, 0} h).mapHomologicalComplex _).obj I ⟶ K) :
    I ⟶ ((etaleAbelianDirectImage.{u, 0} h).mapHomologicalComplex _).obj K where
  f n := (etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.app (I.X n) ≫
    (etaleAbelianDirectImage.{u, 0} h).map (χ.f n)
  comm' n n' _ := by
    have hc := χ.comm n n'
    have hu := (etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.naturality (I.d n n')
    dsimp at hc hu ⊢
    rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp, hc, Functor.map_comp,
      Category.assoc]

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **Restriction on étale cohomology, read on dense subsites, in positive degree.** Under the
identifications `denseCohomologyIso`, restriction along `h` followed by `g : h⁻¹P ⟶ Q` is the map
induced on the sections over `V` of the restricted resolutions by the cochain map adjoint to a
comparison `h⁻¹I_P ⟶ I_Q` over `g`. -/
theorem denseCohomologyIso_conj_succ (V : C) (hT : IsTerminal (ι.obj V))
    (hT' : IsTerminal (ι'.obj (v.obj V))) {P : Sheaf X.smallEtaleTopology Ab.{u + 1}}
    {Q : Sheaf Y.smallEtaleTopology Ab.{u + 1}}
    (g : (etaleAbelianInverseImage.{u, 0} h).obj P ⟶ Q) (n : ℕ)
    (χ₀ : ((etaleAbelianInverseImage.{u, 0} h).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution P).cocomplex ⟶
      (injectiveResolution ((etaleAbelianInverseImage.{u, 0} h).obj P)).cocomplex)
    (hχ₀ : (etaleAbelianInverseImage.{u, 0} h).map ((injectiveResolution P).ι.f 0) ≫ χ₀.f 0 =
      (injectiveResolution ((etaleAbelianInverseImage.{u, 0} h).obj P)).ι.f 0)
    (g' : (injectiveResolution ((etaleAbelianInverseImage.{u, 0} h).obj P)).cocomplex ⟶
      (injectiveResolution Q).cocomplex)
    (hg' : (injectiveResolution ((etaleAbelianInverseImage.{u, 0} h).obj P)).ι ≫ g' =
      (CochainComplex.single₀ _).map g ≫ (injectiveResolution Q).ι) :
    (denseCohomologyIso J ι V hT P (n + 1)).inv ≫ extRestrictionMap h g (n + 1) ≫
        (denseCohomologyIso J' ι' (v.obj V) hT' Q (n + 1)).hom =
      ((mapInjRes (ι.sheafPushforwardContinuous Ab.{u + 1} J _)
          (injectiveResolution P)).isoRightDerivedObj
          ((sheafSections J Ab.{u + 1}).obj (op V)) (n + 1)).hom ≫
        HomologicalComplex.homologyMap
          (sectionsComplexMap.{u + 1, 0} v _ _ (denseComplexComponent h J ι J' ι' v τ
              (etaleAdjunctComplex h _ _ (χ₀ ≫ g')))
            (denseComplexComponent_comm h J ι J' ι' v τ
              (etaleAdjunctComplex h _ _ (χ₀ ≫ g'))) V) (n + 1) ≫
        ((mapInjRes (ι'.sheafPushforwardContinuous Ab.{u + 1} J' _)
          (injectiveResolution Q)).isoRightDerivedObj
          ((sheafSections J' Ab.{u + 1}).obj (op (v.obj V))) (n + 1)).inv := by
  have key := extRestrictionMap_succ_conj h hT hT' (τ.hom.app V) g n χ₀ hχ₀ g' hg'
  have hcm : sectionsComplexMap.{u + 1, 0} (JA := J) (JB := J') v
        (((ι.sheafPushforwardContinuous Ab.{u + 1} J _).mapHomologicalComplex _).obj
          (injectiveResolution P).cocomplex)
        (((ι'.sheafPushforwardContinuous Ab.{u + 1} J' _).mapHomologicalComplex _).obj
          (injectiveResolution Q).cocomplex) (denseComplexComponent h J ι J' ι' v τ
          (etaleAdjunctComplex h _ _ (χ₀ ≫ g')))
        (denseComplexComponent_comm h J ι J' ι' v τ
          (etaleAdjunctComplex h _ _ (χ₀ ≫ g'))) V =
      (NatTrans.mapHomologicalComplex (sectionsRestriction h (τ.hom.app V))
        (ComplexShape.up ℕ)).app (injectiveResolution P).cocomplex ≫
      ((sectionsOver (ι'.obj (v.obj V))).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (χ₀ ≫ g') := by
    ext k : 1
    have hk := ((χ₀ ≫ g').f k).hom.naturality (τ.hom.app V).op
    simp only [HomologicalComplex.comp_f, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app] at hk
    simp only [Functor.mapHomologicalComplex_obj_X, Functor.flip_obj_obj, ObjectProperty.ι_obj,
      sectionsComplexMap, denseComplexComponent, Functor.comp_obj, etaleAdjunctComplex,
      HomologicalComplex.comp_f, Functor.map_comp, Category.assoc,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      Functor.sheafPushforwardContinuous_map_hom_app, densePushforwardIso_hom_app_hom_app,
      sectionsRestriction, Functor.id_obj, Functor.op_obj, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, Functor.flip_obj_map, ObjectProperty.ι_map]
    exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans hk.symm)).trans
      (Category.assoc _ _ _).symm
  rw [← hcm] at key
  refine conj_trans_trans_symm _ _ _ _ _ _ _ _ ?_
  simp only [Iso.app_inv, Iso.app_hom]
  rw [reassoc_of% key]
  simp only [Iso.inv_hom_id_assoc]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
    (Category.comp_id _))

omit [v.IsContinuous J J'] in
/-- **Restriction on étale cohomology, read on dense subsites, in degree zero**: after the
degree-zero comparison `Γ(V, -) ⟶ R⁰Γ(V, -)` it is restriction of sections along `τ`. -/
theorem denseCohomologyIso_zero_comm (V : C) (hT : IsTerminal (ι.obj V))
    (hT' : IsTerminal (ι'.obj (v.obj V))) {P : Sheaf X.smallEtaleTopology Ab.{u + 1}}
    {Q : Sheaf Y.smallEtaleTopology Ab.{u + 1}}
    (g : (etaleAbelianInverseImage.{u, 0} h).obj P ⟶ Q) :
    ((sheafSections J Ab.{u + 1}).obj (op V)).toRightDerivedZero.app
        ((ι.sheafPushforwardContinuous Ab.{u + 1} J _).obj P) ≫
        (denseCohomologyIso J ι V hT P 0).inv ≫ extRestrictionMap h g 0 ≫
        (denseCohomologyIso J' ι' (v.obj V) hT' Q 0).hom =
      (sectionsRestriction h (τ.hom.app V)).app P ≫ g.hom.app (op (ι'.obj (v.obj V))) ≫
        ((sheafSections J' Ab.{u + 1}).obj (op (v.obj V))).toRightDerivedZero.app
          ((ι'.sheafPushforwardContinuous Ab.{u + 1} J' _).obj Q) := by
  have a1 : ((sheafSections J Ab.{u + 1}).obj (op V)).toRightDerivedZero.app
        ((ι.sheafPushforwardContinuous Ab.{u + 1} J _).obj P) ≫
        ((mapInjRes (ι.sheafPushforwardContinuous Ab.{u + 1} J X.smallEtaleTopology)
          (injectiveResolution P)).isoRightDerivedObj
            ((sheafSections J Ab.{u + 1}).obj (op V)) 0).hom ≫
        ((injectiveResolution P).isoRightDerivedObj (sectionsOver (ι.obj V)) 0).inv =
      (sectionsOver (ι.obj V)).toRightDerivedZero.app P :=
    toRightDerivedZero_mapInjRes (ι.sheafPushforwardContinuous Ab.{u + 1} J X.smallEtaleTopology)
      ((sheafSections J Ab.{u + 1}).obj (op V)) (injectiveResolution P)
  have a2 : ((sheafSections J' Ab.{u + 1}).obj (op (v.obj V))).toRightDerivedZero.app
        ((ι'.sheafPushforwardContinuous Ab.{u + 1} J' _).obj Q) ≫
        ((mapInjRes (ι'.sheafPushforwardContinuous Ab.{u + 1} J' Y.smallEtaleTopology)
          (injectiveResolution Q)).isoRightDerivedObj
            ((sheafSections J' Ab.{u + 1}).obj (op (v.obj V))) 0).hom ≫
        ((injectiveResolution Q).isoRightDerivedObj (sectionsOver (ι'.obj (v.obj V))) 0).inv =
      (sectionsOver (ι'.obj (v.obj V))).toRightDerivedZero.app Q :=
    toRightDerivedZero_mapInjRes (ι'.sheafPushforwardContinuous Ab.{u + 1} J' Y.smallEtaleTopology)
      ((sheafSections J' Ab.{u + 1}).obj (op (v.obj V))) (injectiveResolution Q)
  exact (comp_conj_trans_trans_symm _ _ _ _ _ _ _ _ _ _ _
    ((sectionsRestriction h (τ.hom.app V)).app P ≫ g.hom.app (op (ι'.obj (v.obj V)))) a1
    ((Category.assoc _ _ _).trans ((extRestrictionMap_zero_comm h hT hT' (τ.hom.app V) g).trans
      (Category.assoc _ _ _).symm)) a2).trans
    (Category.assoc _ _ _)

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **Restriction on étale cohomology is the cohomology map of Stacks 09YP on dense subsites.**
Under the identifications `denseCohomologyIso`, restriction along `h` followed by
`g : h⁻¹P ⟶ Q` is, in every degree, the cohomology map determined by the restriction to the
dense subsites of the adjoint `P ⟶ h_*Q` of `g`. -/
theorem isCohomologyMap_denseCohomologyIso (V : C) (hT : IsTerminal (ι.obj V))
    (hT' : IsTerminal (ι'.obj (v.obj V))) {P : Sheaf X.smallEtaleTopology Ab.{u + 1}}
    {Q : Sheaf Y.smallEtaleTopology Ab.{u + 1}}
    (g : (etaleAbelianInverseImage.{u, 0} h).obj P ⟶ Q) (p : ℕ) :
    IsCohomologyMap.{u + 1, 0} J J' v
      ((ι.sheafPushforwardContinuous Ab.{u + 1} J _).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).homEquiv P Q g) ≫
        (densePushforwardIso h J ι J' ι' v τ).hom.app Q).hom V p
      ((denseCohomologyIso J ι V hT P p).inv ≫ extRestrictionMap h g p ≫
        (denseCohomologyIso J' ι' (v.obj V) hT' Q p).hom) := by
  obtain ⟨χ₀, hχ₀⟩ := Stacks.Cohomology.ModuleComparison.exists_mapResolutionComparison
    (etaleAbelianInverseImage.{u, 0} h) (injectiveResolution P)
    (injectiveResolution ((etaleAbelianInverseImage.{u, 0} h).obj P))
  let g' := InjectiveResolution.desc g (injectiveResolution Q)
    (injectiveResolution ((etaleAbelianInverseImage.{u, 0} h).obj P))
  let ξ := (etaleAbelianInverseImageDirectImageAdj.{u, 0} h).homEquiv P Q g
  have hζ : (injectiveResolution P).ι.f 0 ≫ (etaleAdjunctComplex h _ _ (χ₀ ≫ g')).f 0 =
      ξ ≫ (etaleAbelianDirectImage.{u, 0} h).map ((injectiveResolution Q).ι.f 0) := by
    have hu := (etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.naturality
      ((injectiveResolution P).ι.f 0)
    have h0 : (etaleAbelianInverseImage.{u, 0} h).map ((injectiveResolution P).ι.f 0) ≫
        (χ₀ ≫ g').f 0 = g ≫ (injectiveResolution Q).ι.f 0 := by
      rw [HomologicalComplex.comp_f, reassoc_of% hχ₀]
      exact InjectiveResolution.desc_commutes_zero _ _ _
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hu)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        (((etaleAbelianDirectImage.{u, 0} h).map_comp _ _).symm.trans
          ((congrArg (etaleAbelianDirectImage.{u, 0} h).map h0).trans
            ((etaleAbelianDirectImage.{u, 0} h).map_comp _ _)))))
  have hm := isCohomologyMap_dense h J ι J' ι' v τ (injectiveResolution P) (injectiveResolution Q)
    (etaleAdjunctComplex h _ _ (χ₀ ≫ g')) ξ hζ V p
  cases p with
  | succ n =>
    rwa [denseCohomologyIso_conj_succ h J ι J' ι' v τ V hT hT' g n χ₀ hχ₀ g'
      (InjectiveResolution.desc_commutes _ _ _)]
  | zero =>
    convert hm using 1
    rw [← cancel_epi (((sheafSections J Ab.{u + 1}).obj (op V)).toRightDerivedZero.app
      ((ι.sheafPushforwardContinuous Ab.{u + 1} J _).obj P)),
      denseCohomologyIso_zero_comm h J ι J' ι' v τ V hT hT' g,
      Stacks.WeakSites.ColimitSiteCohomology.isCohomologyMap_zero_comm _ _ _ hm]
    have key : (sectionsRestriction h (τ.hom.app V)).app P ≫ g.hom.app (op (ι'.obj (v.obj V))) =
        ((ι.sheafPushforwardContinuous Ab.{u + 1} J _).map ξ ≫
          (densePushforwardIso h J ι J' ι' v τ).hom.app Q).hom.app (op V) := by
      rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
        densePushforwardIso_hom_app_hom_app]
      exact (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (g.hom.naturality (τ.hom.app V).op)).trans (Category.assoc _ _ _).symm)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) key)

end Generic

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
  (B : BigEtaleSite.{u})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-! ### Terminal objects -/

/-- An étale `X`-scheme whose structure morphism is an isomorphism is terminal in `X.Etale`. -/
def etale_isTerminal_of_isIso {X : Scheme.{u}} (T : X.Etale) (h : IsIso T.hom) : IsTerminal T :=
  (finalObj_isTerminal X).ofIso (MorphismProperty.Over.isoMk (asIso T.hom).symm
    (IsIso.inv_hom_id T.hom))

section Terminal

variable [∀ i : Iᵒᵖ, IsAffine (D.obj i)]

/-- A terminal object of a level is terminal in Mathlib's small étale site of the level. -/
def levelToEtale_isTerminal (i : (sys D c B hD hX hc).I) (V : (sys D c B hD hX hc).C i)
    (hV : IsTerminal V) : IsTerminal ((levelToEtale D c B hD hX hc i).obj V) :=
  etale_isTerminal_of_isIso _ (isIso_structureMorphism_of_isTerminal D c B hD hX hc i V hV)

/-- The image in the site of the limit of a terminal object of a level is terminal in Mathlib's
small étale site of the limit. -/
def limitToEtale_isTerminal (i : (sys D c B hD hX hc).I) (V : (sys D c B hD hX hc).C i)
    (hV : IsTerminal V) :
    IsTerminal ((limitToEtale D c B hX).obj ((toLimitSmall D c B hD hX hc i).obj V)) :=
  etale_isTerminal_of_isIso _
    (((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i V).isIso_snd_of_isIso
      (isIso_structureMorphism_of_isTerminal D c B hD hX hc i V hV))

end Terminal

/-! ### The transitions of the system of inverse images, on cohomology -/

section Transition

variable {D c B hD hX hc}

/-- Direct image along a transition, restricted to the levels. -/
abbrev transitionPushforwardIso' {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :=
  let := (sys D c B hD hX hc).continuous a
  densePushforwardIso (lvlMap D c B hD hX hc a) ((sys D c B hD hX hc).J i)
    (levelToEtale D c B hD hX hc i) ((sys D c B hD hX hc).J j) (levelToEtale D c B hD hX hc j)
    ((sys D c B hD hX hc).u a) (transitionBaseChangeIso D c B hD hX hc a)

attribute [local instance] toLimitSmall_isContinuous

variable [OrderBot I]
  (G : Sheaf (lvl.{u, u} D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology Ab.{u + 1})

/-- **The transition comparison of inverse images** `h⁻¹(f_i⁻¹G) ⟶ f_j⁻¹G` along the transition
morphism `h : X_j ⟶ X_i`: the map whose adjoint, restricted to the levels, is the transition map
of the system of Stacks 0EXZ of the inverse images of `G`. -/
def levelComparison {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    (etaleAbelianInverseImage.{u, 0} (lvlMap D c B hD hX hc a)).obj (levelInverseImage G i) ⟶
      levelInverseImage G j :=
  ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (lvlMap D c B hD hX hc a)).homEquiv _ _).symm
    ((levelRestrict.{u, u} D c B hD hX hc Ab.{u + 1} i).preimage
      (ObjectProperty.homMk (ψ (sys D c B hD hX hc) (bottom_isTerminal D c B hD hX hc)
          (levelε G) (isUniversalArrow_levelε G) a) ≫
        (transitionPushforwardIso' a).inv.app (levelInverseImage G j)))

/-- The adjoint of `levelComparison`, restricted to the levels through `transitionPushforwardIso'`,
is the transition map `ψ` of the system of inverse images. -/
theorem levelComparison_spec {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    ((levelRestrict.{u, u} D c B hD hX hc Ab.{u + 1} i).map
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (lvlMap D c B hD hX hc a)).unit.app
            (levelInverseImage G i) ≫
          (etaleAbelianDirectImage.{u, 0} (lvlMap D c B hD hX hc a)).map (levelComparison G a)) ≫
        (transitionPushforwardIso' a).hom.app (levelInverseImage G j)).hom =
      ψ (sys D c B hD hX hc) (bottom_isTerminal D c B hD hX hc) (levelε G)
        (isUniversalArrow_levelε G) a := by
  have hu := (Adjunction.homEquiv_unit
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (lvlMap D c B hD hX hc a)) _ _
    (levelComparison G a)).symm
  rw [hu, levelComparison, Equiv.apply_symm_apply, Functor.map_preimage,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **The transitions of the system of inverse images, on cohomology, are the cohomology maps of
Stacks 09YP.** Read on the levels through `denseCohomologyIso`, restriction along a transition
`h : X_j ⟶ X_i` followed by the comparison `levelComparison` is the cohomology map of the weak
Stacks 09YP attached to the transition map of the system, over any object `V` of the level `i`
whose image and whose transition image are terminal. -/
theorem isCohomologyMap_levelComparison
    [∀ i : (sys D c B hD hX hc).I,
      HasExt.{u + 1} (Sheaf (lvl.{u, u} D c B hD hX hc i).smallEtaleTopology Ab.{u + 1})]
    {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) (V : (sys D c B hD hX hc).C i)
    (hT : IsTerminal ((levelToEtale D c B hD hX hc i).obj V))
    (hT' : IsTerminal ((levelToEtale D c B hD hX hc j).obj ((sys D c B hD hX hc).u a |>.obj V)))
    (p : ℕ) :
    IsCohomologyMap.{u + 1, 0} ((sys D c B hD hX hc).J i) ((sys D c B hD hX hc).J j)
      ((sys D c B hD hX hc).u a)
      (ψ (sys D c B hD hX hc) (bottom_isTerminal D c B hD hX hc) (levelε G)
        (isUniversalArrow_levelε G) a) V p
      ((denseCohomologyIso ((sys D c B hD hX hc).J i) (levelToEtale D c B hD hX hc i) V hT
          (levelInverseImage G i) p).inv ≫
        extRestrictionMap (lvlMap D c B hD hX hc a) (levelComparison G a) p ≫
        (denseCohomologyIso ((sys D c B hD hX hc).J j) (levelToEtale D c B hD hX hc j) _ hT'
          (levelInverseImage G j) p).hom) := by
  let := (sys D c B hD hX hc).continuous a
  have hm := isCohomologyMap_denseCohomologyIso (lvlMap D c B hD hX hc a)
    ((sys D c B hD hX hc).J i) (levelToEtale D c B hD hX hc i) ((sys D c B hD hX hc).J j)
    (levelToEtale D c B hD hX hc j) ((sys D c B hD hX hc).u a)
    (transitionBaseChangeIso D c B hD hX hc a) V hT hT' (levelComparison G a) p
  rw [Adjunction.homEquiv_unit] at hm
  rw [← levelComparison_spec G a]
  exact hm

/-- Direct image along a projection of the limit, restricted to the level and to the site of the
limit. -/
abbrev limitPushforwardIso' (i : (sys D c B hD hX hc).I) :=
  densePushforwardIso (lvlπ.{u, u} D c B hD hX hc i) ((sys D c B hD hX hc).J i)
    (levelToEtale D c B hD hX hc i) (limitSitePrecoverage.{u, u} D c B hX).toGrothendieck
    (limitToEtale.{u, u} D c B hX) (toLimitSmall.{u, u} D c B hD hX hc i)
    (toLimitBaseChangeIso.{u, u} D c B hD hX hc i)

/-- **The comparison of inverse images to the limit** `f_i⁻¹(f_{i⊥}⁻¹G) ⟶ f_⊥⁻¹G` along the
projection `f_i : X ⟶ X_i`: the map whose adjoint, restricted to the level and to the site of
the limit, is the structure map of the colimit of Stacks 0EXZ. -/
def limitComparison (i : (sys D c B hD hX hc).I) :
    (etaleAbelianInverseImage.{u, 0} (lvlπ.{u, u} D c B hD hX hc i)).obj (levelInverseImage G i) ⟶
      limitInverseImage G :=
  ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (lvlπ.{u, u} D c B hD hX hc i)).homEquiv _ _).symm
    ((levelRestrict.{u, u} D c B hD hX hc Ab.{u + 1} i).preimage
      (ObjectProperty.homMk (limitι G i) ≫
        (limitPushforwardIso' i).inv.app (limitInverseImage G)))

/-- The adjoint of `limitComparison`, restricted to the level and to the site of the limit through
`limitPushforwardIso'`, is the structure map `limitι G i`. -/
theorem limitComparison_spec (i : (sys D c B hD hX hc).I) :
    ((levelRestrict.{u, u} D c B hD hX hc Ab.{u + 1} i).map
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (lvlπ.{u, u} D c B hD hX hc i)).unit.app
            (levelInverseImage G i) ≫
          (etaleAbelianDirectImage.{u, 0} (lvlπ.{u, u} D c B hD hX hc i)).map
            (limitComparison G i)) ≫
        (limitPushforwardIso' i).hom.app (limitInverseImage G)).hom =
      limitι G i := by
  have hu := (Adjunction.homEquiv_unit
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (lvlπ.{u, u} D c B hD hX hc i)) _ _
    (limitComparison G i)).symm
  rw [hu, limitComparison, Equiv.apply_symm_apply, Functor.map_preimage,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **Restriction to the limit, on cohomology, is the cohomology map of Stacks 09YP of the
structure map of the colimit**, read on the level and on the site of the limit through
`denseCohomologyIso`. -/
theorem isCohomologyMap_limitComparison
    [∀ i : (sys D c B hD hX hc).I,
      HasExt.{u + 1} (Sheaf (lvl.{u, u} D c B hD hX hc i).smallEtaleTopology Ab.{u + 1})]
    [HasExt.{u + 1} (Sheaf c.pt.smallEtaleTopology Ab.{u + 1})]
    (i : (sys D c B hD hX hc).I) (V : (sys D c B hD hX hc).C i)
    (hT : IsTerminal ((levelToEtale D c B hD hX hc i).obj V))
    (hT' : IsTerminal
      ((limitToEtale.{u, u} D c B hX).obj ((toLimitSmall.{u, u} D c B hD hX hc i).obj V)))
    (p : ℕ) :
    IsCohomologyMap.{u + 1, 0} ((sys D c B hD hX hc).J i)
      (limitSitePrecoverage.{u, u} D c B hX).toGrothendieck (toLimitSmall.{u, u} D c B hD hX hc i)
      (limitι G i) V p
      ((denseCohomologyIso ((sys D c B hD hX hc).J i) (levelToEtale D c B hD hX hc i) V hT
          (levelInverseImage G i) p).inv ≫
        extRestrictionMap (lvlπ.{u, u} D c B hD hX hc i) (limitComparison G i) p ≫
        (denseCohomologyIso (limitSitePrecoverage.{u, u} D c B hX).toGrothendieck
          (limitToEtale.{u, u} D c B hX) _ hT' (limitInverseImage G) p).hom) := by
  have hm := isCohomologyMap_denseCohomologyIso (lvlπ.{u, u} D c B hD hX hc i)
    ((sys D c B hD hX hc).J i) (levelToEtale D c B hD hX hc i)
    (limitSitePrecoverage.{u, u} D c B hX).toGrothendieck (limitToEtale.{u, u} D c B hX)
    (toLimitSmall.{u, u} D c B hD hX hc i) (toLimitBaseChangeIso.{u, u} D c B hD hX hc i) V hT hT'
    (limitComparison G i) p
  rw [Adjunction.homEquiv_unit] at hm
  rw [← limitComparison_spec G i]
  exact hm


section Assembly

open Stacks.WeakSites.ColimitSiteCohomology

variable [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
  [∀ i : (sys D c B hD hX hc).I,
    HasExt.{u + 1} (Sheaf (lvl.{u, u} D c B hD hX hc i).smallEtaleTopology Ab.{u + 1})]
  [HasExt.{u + 1} (Sheaf c.pt.smallEtaleTopology Ab.{u + 1})]

/-- The canonical cohomology cocone of the weak Stacks 09YP for the system of inverse images of
`G`, over the terminal object of the bottom level. -/
abbrev levelCocone (p : ℕ) :=
  cohomologyCocone.{u, u, u + 1} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) (toLimitSmall_obj_descends D c B hD hX hc)
    (toLimitSmall_hom_descends D c B hD hX hc) (toLimitSmall_hom_eventually_eq D c B hD hX hc)
    (limitSitePrecoverage D c B hX) (mem_limitSitePrecoverage_iff D c B hD hX hc)
    (levelSystem G) (limitSheaf G) (limitι G) (isColimitPresentation_levelSystem G)
    (bottom D c B hD hX hc) (levelTerminal D c B hD hX hc (bottom D c B hD hX hc)) p

/-- The transition image at `A : j ⟶ ⊥` of the terminal object of the bottom level is terminal in
the small étale site of `X_j`. -/
def levelObj_isTerminal (A : Over (bottom D c B hD hX hc)) :
    IsTerminal ((levelToEtale D c B hD hX hc A.left).obj (((sys D c B hD hX hc).u A.hom).obj
      (levelTerminal D c B hD hX hc (bottom D c B hD hX hc)))) :=
  levelToEtale_isTerminal D c B hD hX hc _ _ (transitionImage_isTerminal D c B hD hX hc A.hom _
    (levelTerminal_isTerminal D c B hD hX hc _))

/-- **The identification of the diagram of Stacks 09YP with the étale cohomology of the
levels**: `H^p(X_j, f_j⁻¹G)` is the value at `A : j ⟶ ⊥` of the cohomology diagram. -/
def levelCoconeIso (p : ℕ) (A : Over (bottom D c B hD hX hc)) :
    (extFunctorObj (zSheaf (lvl.{u, u} D c B hD hX hc A.left)) p).obj (levelInverseImage G A.left) ≅
      (levelCocone G p).diagram.obj (op A) :=
  denseCohomologyIso ((sys D c B hD hX hc).J A.left) (levelToEtale D c B hD hX hc A.left) _
      (levelObj_isTerminal A) (levelInverseImage G A.left) p ≪≫
    ((levelCocone G p).objIso A).symm

omit [HasExt.{u + 1} (Sheaf c.pt.smallEtaleTopology Ab.{u + 1})] in
/-- **The transition maps of the cohomology diagram of Stacks 09YP are restriction on étale
cohomology**, read through `levelCoconeIso`. -/
theorem levelCocone_map (p : ℕ) {A A' : Over (bottom D c B hD hX hc)} (f : A ⟶ A') :
    (levelCoconeIso G p A').hom ≫ (levelCocone G p).diagram.map f.op =
      extRestrictionMap (lvlMap D c B hD hX hc f.left) (levelComparison G f.left) p ≫
        (levelCoconeIso G p A).hom := by
  let := (sys D c B hD hX hc).continuous f.left
  let := Stacks.WeakSites.ColimitSiteCohomology.restriction_preservesInjectiveObjects.{u + 1, 0}
    ((sys D c B hD hX hc).u f.left) ((sys D c B hD hX hc).isMorphismOfSites f.left)
  have hT'' : IsTerminal ((levelToEtale D c B hD hX hc A.left).obj
      (((sys D c B hD hX hc).u f.left).obj (((sys D c B hD hX hc).u A'.hom).obj
        (levelTerminal D c B hD hX hc (bottom D c B hD hX hc))))) :=
    levelToEtale_isTerminal D c B hD hX hc _ _ (transitionImage_isTerminal D c B hD hX hc f.left _
      (transitionImage_isTerminal D c B hD hX hc A'.hom _
        (levelTerminal_isTerminal D c B hD hX hc _)))
  have h1 := (levelCocone G p).map_eq f
  rw [transition_abelianSystem] at h1
  have h2 := isCohomologyMap_levelComparison G f.left _ (levelObj_isTerminal A') hT'' p
  have h3 := Stacks.WeakSites.ColimitSiteCohomology.isCohomologyMap_unique _ _ _ _ h1 h2
  rw [← denseCohomologyIso_hom_comp_cohomologyCongr ((sys D c B hD hX hc).J A.left)
    (levelToEtale D c B hD hX hc A.left) (uObj_eq (sys D c B hD hX hc) f
      (levelTerminal D c B hD hX hc (bottom D c B hD hX hc)))
    (levelObj_isTerminal A) hT''] at h3
  exact trans_symm_comp_eq_of_comp_eq _ _ _ _ _ _ _
    (hk := Stacks.WeakSites.ColimitSiteCohomology.cohomologyCongr_isIso _ _ _ _) h3

/-- The identification of the vertex of the cohomology cocone of Stacks 09YP with the étale
cohomology of the limit. -/
abbrev limitCoconeIso (p : ℕ) :=
  denseCohomologyIso (limitSitePrecoverage D c B hX).toGrothendieck (limitToEtale D c B hX) _
    (limitToEtale_isTerminal D c B hD hX hc (bottom D c B hD hX hc)
      (levelTerminal D c B hD hX hc (bottom D c B hD hX hc))
      (levelTerminal_isTerminal D c B hD hX hc (bottom D c B hD hX hc)))
    (limitInverseImage G) p

/-- **The legs of the cohomology cocone of Stacks 09YP are restriction to the limit on étale
cohomology**, read through `levelCoconeIso` and `limitCoconeIso`. -/
theorem levelCocone_leg (p : ℕ) (A : Over (bottom D c B hD hX hc)) :
    (levelCoconeIso G p A).hom ≫ (levelCocone G p).leg.app (op A) =
      extRestrictionMap (lvlπ D c B hD hX hc A.left) (limitComparison G A.left) p ≫
        (limitCoconeIso G p).hom := by
  let := Stacks.WeakSites.ColimitSiteCohomology.restriction_preservesInjectiveObjects.{u + 1, 0}
    (toLimitSmall D c B hD hX hc A.left)
    (Stacks.WeakSites.ColimitSiteCohomology.isMorphismOfSites_colimitSite.{u, u, u + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (toLimitSmall_obj_descends D c B hD hX hc)
      (toLimitSmall_hom_descends D c B hD hX hc) (toLimitSmall_hom_eventually_eq D c B hD hX hc)
      (limitSitePrecoverage D c B hX) (mem_limitSitePrecoverage_iff D c B hD hX hc) A.left)
  have hT' := limitToEtale_isTerminal D c B hD hX hc A.left _
    (transitionImage_isTerminal D c B hD hX hc A.hom _ (levelTerminal_isTerminal D c B hD hX hc _))
  have h1 := (levelCocone G p).leg_eq A
  have h2 := isCohomologyMap_limitComparison G A.left _ (levelObj_isTerminal A) hT' p
  have h3 := Stacks.WeakSites.ColimitSiteCohomology.isCohomologyMap_unique _ _ _ _ h1 h2
  rw [← denseCohomologyIso_hom_comp_cohomologyCongr (limitSitePrecoverage D c B hX).toGrothendieck
    (limitToEtale D c B hX) (uLeg_eq (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) A
      (levelTerminal D c B hD hX hc (bottom D c B hD hX hc)))
    (limitToEtale_isTerminal D c B hD hX hc (bottom D c B hD hX hc)
      (levelTerminal D c B hD hX hc (bottom D c B hD hX hc))
      (levelTerminal_isTerminal D c B hD hX hc (bottom D c B hD hX hc)))
    hT'] at h3
  exact trans_symm_comp_eq_of_comp_eq' _ _ _ _ _ _
    (hk := Stacks.WeakSites.ColimitSiteCohomology.cohomologyCongr_isIso _ _ _ _) h3

/-- The cohomology cocone of Stacks 09YP for the system of inverse images is a colimit. -/
def levelCocone_isColimit (p : ℕ) : IsColimit (levelCocone G p).cocone :=
  AffineLimitCohomology.etaleCohomologyColimit_isColimit_of_affine.{u, u} D c B hD hX hc
    (levelSystem G) (limitSheaf G) (limitι G) (isColimitPresentation_levelSystem G)
    (bottom D c B hD hX hc) p (levelCocone G p)

/-- The leg of `levelCocone` at `A`, read through `levelCoconeIso` and `limitCoconeIso`, sends a
class `y` to its restriction `extRestrictionMap` along the projection and `limitComparison`. -/
theorem levelCocone_leg_apply (p : ℕ) (A : Over (bottom D c B hD hX hc))
    (y : (extFunctorObj (zSheaf (lvl.{u, u} D c B hD hX hc A.left)) p).obj
      (levelInverseImage G A.left)) :
    (levelCocone G p).leg.app (op A) ((levelCoconeIso G p A).hom y) =
      (limitCoconeIso G p).hom
        (extRestrictionMap (lvlπ D c B hD hX hc A.left) (limitComparison G A.left) p y) :=
  ConcreteCategory.congr_hom (levelCocone_leg G p A) y

/-- **Every class on the limit comes from a level**, for the system of inverse images of a sheaf
on the bottom level with affine levels: Stacks 09YQ, surjectivity. -/
theorem exists_extRestrictionMap_limitComparison_eq (p : ℕ)
    (x : (extFunctorObj (zSheaf c.pt) p).obj (limitInverseImage G)) :
    ∃ (A : Over (bottom D c B hD hX hc))
      (y : (extFunctorObj (zSheaf (lvl.{u, u} D c B hD hX hc A.left)) p).obj
        (levelInverseImage G A.left)),
      extRestrictionMap (lvlπ D c B hD hX hc A.left) (limitComparison G A.left) p y = x := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep _ (levelCocone_isColimit G p)
    ((limitCoconeIso G p).hom x)
  refine ⟨j.unop, (levelCoconeIso G p j.unop).inv y, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (limitCoconeIso G p).hom).1
  rw [← levelCocone_leg_apply]
  refine Eq.trans ?_ hy
  exact congrArg ((levelCocone G p).leg.app j) ((levelCoconeIso G p j.unop).inv_hom_id_apply y)

/-- **A class of a level that vanishes on the limit vanishes on a later level**, for the system of
inverse images of a sheaf on the bottom level with affine levels: Stacks 09YQ, injectivity. -/
theorem exists_extRestrictionMap_levelComparison_eq_zero (p : ℕ) (A : Over (bottom D c B hD hX hc))
    (y : (extFunctorObj (zSheaf (lvl.{u, u} D c B hD hX hc A.left)) p).obj
      (levelInverseImage G A.left))
    (hy : extRestrictionMap (lvlπ D c B hD hX hc A.left) (limitComparison G A.left) p y = 0) :
    ∃ (A' : Over (bottom D c B hD hX hc)) (f : A' ⟶ A),
      extRestrictionMap (lvlMap D c B hD hX hc f.left) (levelComparison G f.left) p y = 0 := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have h0 : (levelCocone G p).cocone.ι.app (op A) ((levelCoconeIso G p A).hom y) =
      (levelCocone G p).cocone.ι.app (op A) 0 := by
    change (levelCocone G p).leg.app (op A) _ = (levelCocone G p).leg.app (op A) 0
    rw [levelCocone_leg_apply, hy, map_zero, map_zero]
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq _ (levelCocone_isColimit G p) _ _ h0
  refine ⟨k.unop, f.unop, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (levelCoconeIso G p k.unop).hom).1
  rw [map_zero, ← ConcreteCategory.comp_apply, ← levelCocone_map]
  simpa using hfg

end Assembly

end Transition

end Stacks.EtaleCohomology.LimitSiteBridge
