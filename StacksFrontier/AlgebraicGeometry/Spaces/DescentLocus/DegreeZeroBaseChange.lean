module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded
public import StacksFrontier.Algebra.Homology.RightExactHomologyComparison
public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeLocalizationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DegreeZeroPushforward

/-!
# The degree-zero base change map from the derived one

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a commutative square of algebraic spaces and `G` an `𝒪_X`-module. The derived base change
map of Stacks 0CTM, part (2), `Lg^*Rf_*G[0] ⟶ Rf'_*L(g')^*G[0] ⟶ Rf'_*((g')^*G)[0]`
(`AlgebraicGeometry.Space.smallEtaleDerivedBaseChangeComp` at the comparison
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackQComparison`), and the underived one,
`g^*f_*G ⟶ f'_*(g')^*G` (`AlgebraicGeometry.Space.moduleBaseChangeMap`), are tied in degree zero:
if the derived map is an isomorphism and `g^*` commutes with `H⁰` on `Rf_*G[0]`, the underived
map is an isomorphism.

## Main results

* `DescentStratum.isIso_moduleBaseChangeMap_app_of_isIso_homology_map_unit`: the model-free form,
  with the degree-zero comparison read on `Lg^*` of the unit `f_*G[0] ⟶ Rf_*G[0]`.
* `DescentStratum.isIso_moduleBaseChangeMap_app_of_isIso_homologyComparison`: the form through a
  K-flat model `P ≅ Rf_*G[0]`, with the comparison `g^*H⁰(P) ⟶ H⁰(g^*P)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pullbackMapHomotopy
  pushforwardMapHomotopy pushforwardOnHomotopy sourceQuasiIso)

universe u

namespace Stacks.CategoryTheory.BaseChange.DegreeZeroBaseChange

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

variable {DY : Type u₁} {DX : Type u₂} {DY' : Type u₃} {DX' : Type u₄}
  [Category.{v₁} DY] [Category.{v₂} DX] [Category.{v₃} DY'] [Category.{v₄} DX']
  {HY : Type u₅} {HX : Type u₆} {HY' : Type u₇} {HX' : Type u₈}
  [Category.{v₅} HY] [Category.{v₆} HX] [Category.{v₇} HY'] [Category.{v₈} HX']
  {QY : HY ⥤ DY} {QX : HX ⥤ DX} {QY' : HY' ⥤ DY'} {QX' : HX' ⥤ DX'}
  {pf : HY ⥤ HX} {qf : HX ⥤ HY} {pf' : HY' ⥤ HX'} {qf' : HX' ⥤ HY'}
  {pg : HY ⥤ HY'} {pg' : HX ⥤ HX'}
  (a : pf ⊣ qf) (a' : pf' ⊣ qf')
  {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
  {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
  (cf : QY ⋙ Lf ⟶ pf ⋙ QX) (cf' : QY' ⋙ Lf' ⟶ pf' ⋙ QX')
  (cg : QY ⋙ Lg ⟶ pg ⋙ QY') (cg' : QX ⋙ Lg' ⟶ pg' ⋙ QX')
  (uf : qf ⋙ QY ⟶ QX ⋙ Rf) (uf' : qf' ⋙ QY' ⟶ QX' ⋙ Rf')

/-- The identity of `Stacks.CategoryTheory.BaseChange.map_comparison` for a family of derived
and underived pullbacks with comparisons, the two composites around the square being identified
with the members at two equal indices. -/
private theorem map_comparison_of_eq {T : Sort*} (Λ : T → (DY ⥤ DX')) (π : T → (HY ⥤ HX'))
    (cmp : ∀ t, QY ⋙ Λ t ⟶ π t ⋙ QX') {t₁ t₂ : T} (h : t₁ = t₂)
    (eg₂ : Lg ⋙ Lf' ≅ Λ t₂) (ef₁ : Lf ⋙ Lg' ≅ Λ t₁)
    (eg₀ : pg ⋙ pf' ≅ π t₂) (ef₁₀ : pf ⋙ pg' ≅ π t₁)
    (hf : ∀ K : HX, Lf.map (uf.app K) ≫ adjf.counit.app (QX.obj K) =
      cf.app (qf.obj K) ≫ QX.map (a.counit.app K))
    (hf' : ∀ K : HX', Lf'.map (uf'.app K) ≫ adjf'.counit.app (QX'.obj K) =
      cf'.app (qf'.obj K) ≫ QX'.map (a'.counit.app K))
    (hg : ∀ M : HY, eg₂.hom.app (QY.obj M) ≫ (cmp t₂).app M =
      Lf'.map (cg.app M) ≫ cf'.app (pg.obj M) ≫ QX'.map (eg₀.hom.app M))
    (hg₁ : ∀ M : HY, ef₁.hom.app (QY.obj M) ≫ (cmp t₁).app M =
      Lg'.map (cf.app M) ≫ cg'.app (pf.obj M) ≫ QX'.map (ef₁₀.hom.app M))
    (K : HX) :
    Lg.map (uf.app K) ≫ map adjf adjf' eg₂ (ef₁ ≪≫ eqToIso (congrArg Λ h)) (QX.obj K) ≫
        Rf'.map (cg'.app K) =
      cg.app (qf.obj K) ≫ QY'.map (map a a' eg₀ (ef₁₀ ≪≫ eqToIso (congrArg π h)) K) ≫
        uf'.app (pg'.obj K) := by
  subst h
  refine map_comparison a a' (eg₀.hom ≫ (ef₁₀ ≪≫ eqToIso rfl).inv)
    (twoSquare a a' eg₀ (ef₁₀ ≪≫ eqToIso rfl)) adjf adjf' eg₂ (ef₁ ≪≫ eqToIso rfl)
    cf cf' cg cg' uf uf' (fun K => ?_) hf hf' (fun M => ?_) K
  · exact (homEquiv_symm_map a a' eg₀ _ K).trans (by rw [NatTrans.comp_app, Category.assoc])
  · have h₂ : Lg'.map (cf.app M) ≫ cg'.app (pf.obj M) =
        ef₁.hom.app (QY.obj M) ≫ (cmp t₁).app M ≫ QX'.map (ef₁₀.inv.app M) := by
      rw [reassoc_of% (hg₁ M), ← QX'.map_comp, Iso.hom_inv_id_app]
      simp
    simp only [eqToIso_refl, Iso.trans_refl]
    rw [h₂, Iso.inv_hom_id_app_assoc, reassoc_of% (hg M), NatTrans.comp_app, QX'.map_comp]

section DerivedHomology

attribute [local instance] HasDerivedCategory.standard

variable {C : Type*} [Category C] [Abelian C]

/-- Degree-zero cohomology of the image of a map of complexes in the derived category, through
the homotopy category, is the map induced on degree-zero cohomology. -/
private theorem isIso_homology_Qh_map_quotient_map_iff {A A' : CochainComplex C ℤ} (φ : A ⟶ A') :
    IsIso ((DerivedCategory.homologyFunctor C 0).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ))) ↔
      IsIso (HomologicalComplex.homologyMap φ 0) :=
  NatIso.isIso_map_iff (Functor.isoWhiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
    (DerivedCategory.homologyFunctorFactorsh C 0) ≪≫
      HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) 0) φ

/-- The image in the derived category, through the homotopy category, of a quasi-isomorphism is
an isomorphism. -/
private theorem isIso_Qh_map_quotient_map {A A' : CochainComplex C ℤ} (φ : A ⟶ A')
    [QuasiIso φ] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ)) :=
  (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) φ).2 inferInstance

/-- In a commutative square `a ≫ b = c ≫ d`, a functor inverting `a`, `c` and `d` inverts `b`. -/
private theorem isIso_map_of_comm_of_isIso {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z} (h : a ≫ b = c ≫ d)
    (ha : IsIso (F.map a)) (hc : IsIso (F.map c)) (hd : IsIso (F.map d)) : IsIso (F.map b) := by
  have e : F.map b = inv (F.map a) ≫ F.map c ≫ F.map d := by
    rw [← F.map_comp, ← h, F.map_comp, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- In a commutative diagram `a ≫ b = r ≫ s ≫ t`, a functor inverting `a`, `b`, `r` and `t`
inverts `s`. -/
private theorem isIso_map_of_comm₃_of_isIso {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Z Y₁ Y₂ : C} {a : W ⟶ X} {b : X ⟶ Z} {r : W ⟶ Y₁} {s : Y₁ ⟶ Y₂} {t : Y₂ ⟶ Z}
    (h : a ≫ b = r ≫ s ≫ t) (ha : IsIso (F.map a)) (hb : IsIso (F.map b))
    (hr : IsIso (F.map r)) (ht : IsIso (F.map t)) : IsIso (F.map s) := by
  have := isIso_map_of_comm_of_isIso F h.symm hr ha hb
  rw [F.map_comp] at this
  exact IsIso.of_isIso_comp_right _ (F.map t)

/-- In a commutative square `a ≫ b = c ≫ d`, a functor inverting `b`, `c` and `d` inverts `a`. -/
private theorem isIso_map_of_comm_of_isIso' {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z} (h : a ≫ b = c ≫ d)
    (hb : IsIso (F.map b)) (hc : IsIso (F.map c)) (hd : IsIso (F.map d)) : IsIso (F.map a) :=
  isIso_map_of_comm₃_of_isIso F (r := 𝟙 W) (by rw [h, Category.id_comp]) hc hd inferInstance hb

/-- If `H(L(u ≫ φ))` is invertible for an isomorphism `φ`, so is `H(L(u))`. -/
private theorem isIso_map_map_of_isIso_map_map_comp {C D E : Type*} [Category C] [Category D]
    [Category E] (L : C ⥤ D) (H : D ⥤ E) {a b c : C} (u : a ⟶ b) (φ : b ⟶ c) [IsIso φ]
    (h : IsIso (H.map (L.map (u ≫ φ)))) : IsIso (H.map (L.map u)) := by
  rw [L.map_comp, H.map_comp] at h
  exact IsIso.of_isIso_comp_right _ (H.map (L.map φ))

/-- If `H(u)` is invertible, so is `H(u ≫ φ)` for an isomorphism `φ`. -/
private theorem isIso_map_comp_of_isIso_map {C E : Type*} [Category C] [Category E]
    (H : C ⥤ E) {a b c : C} (u : a ⟶ b) (φ : b ⟶ c) [IsIso φ] (h : IsIso (H.map u)) :
    IsIso (H.map (u ≫ φ)) := by
  rw [H.map_comp]
  infer_instance

/-- `((a ≫ b ≫ c) ≫ d) ≫ (d⁻¹ ≫ c⁻¹) = a ≫ b`. -/
private theorem comp_hom_comp_trans_symm_hom {C : Type*} [Category C] {P Q R S T : C}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ≅ S) (d : S ≅ T) :
    ((a ≫ b ≫ c.hom) ≫ d.hom) ≫ (d.symm ≪≫ c.symm).hom = a ≫ b := by
  simp

/-- A map `Q(M) ⟶ Q(P)` out of a complex vanishing in positive degrees is, up to an isomorphism
of its source, the image of a map of complexes out of a complex vanishing in positive degrees. -/
private theorem exists_eq_comp_Qh_map_quotient_map {M P : CochainComplex C ℤ} [M.IsStrictlyLE 0]
    (y : DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) :
    ∃ (X' : CochainComplex C ℤ) (_ : X'.IsStrictlyLE 0)
      (ι : DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X'))
      (_ : IsIso ι) (g₁ : X' ⟶ P),
      y = ι ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g₁) := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨X', hX', s, hs, g₁, hy⟩ :=
    DerivedCategory.right_fac_of_isStrictlyLE (e.inv.app M ≫ y ≫ e.hom.app P) 0
  refine ⟨X', hX', e.hom.app M ≫ inv (DerivedCategory.Q.map s) ≫ e.inv.app X', inferInstance,
    g₁, ?_⟩
  have h₁ := e.inv.naturality g₁
  simp only [Functor.comp_map] at h₁
  have h₂ : inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g₁ ≫ e.inv.app P =
      e.inv.app M ≫ y := by
    rw [← Category.assoc, ← hy]
    simp
  rw [Category.assoc, Category.assoc, ← h₁, h₂]
  simp

end DerivedHomology

section Unit

universe w₀ v₀ u₀ v₉ u₉

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u₀} [Category.{v₀} A] [Abelian A] [IsGrothendieckAbelian.{w₀} A]
  {B : Type u₉} [Category.{v₉} B] [Abelian B]

/-- **`R⁰w = w` for a left exact functor out of a Grothendieck abelian category**: the unit of a
right derived functor of `w` on the unbounded derived category is an isomorphism on degree-zero
cohomology at every object placed in degree zero. -/
private theorem isIso_homology_unit_app_single (w : A ⥤ B) [w.Additive] [PreservesFiniteLimits w]
    (Rw : DerivedCategory A ⥤ DerivedCategory B)
    (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rw)
    [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] (M : A) :
    IsIso ((DerivedCategory.homologyFunctor B 0).map
      (α.app ((HomotopyCategory.singleFunctor A 0).obj M))) := by
  let := Functor.IsRightDerivedFunctor.commShift Rw α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  have : Rw.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor w Rw α
  have : EnoughInjectives A := IsGrothendieckAbelian.enoughInjectives.{w₀}
  have hK : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := fun I hI =>
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh Rw α I hI
  exact Stacks.DerivedFunctor.isIso_singleUnitHomology_app w Rw α
    (fun X => Stacks.SmallDerivedCategory.isGE_obj_of_isGE w Rw α hK _ 0 inferInstance)
    (fun J hJ => Stacks.DerivedFunctor.isIso_unit_app_single_of_injective w Rw α
      Stacks.Injectives.exists_kInjective_resolution_of_grothendieck J hJ) M

end Unit

section Mates

universe t

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
  {L₂ L₅ : A ⥤ B'} {R₂ R₅ : B' ⥤ A} {ι : Type t} {Lk : ι → (A ⥤ B')} {Rk : ι → (B' ⥤ A)}
  {Rg : A' ⥤ A} {Rg' : B' ⥤ B}

/-- **The converse of `Stacks.CategoryTheory.BaseChange.isIso_map_of_isIso_mateEquiv_symm_app`.**
In its situation, if the base change map is invertible at `K`, so is the component at `K` of the
mate across the other adjunctions `bg`, `bg'`: the two differ by the comparisons of left
adjoints. -/
private theorem isIso_mateEquiv_symm_app_of_isIso_map (ag : Lg ⊣ Rg) (ag' : Lg' ⊣ Rg')
    (a₂ : L₂ ⊣ R₂) (a₅ : L₅ ⊣ R₅) (ak : ∀ k, Lk k ⊣ Rk k) {k₁ k₂ : ι} (hk : k₁ = k₂)
    (pc : R₂ ≅ Rf' ⋙ Rg) (tc : R₂ ≅ Rk k₂) (pc' : R₅ ≅ Rg' ⋙ Rf) (tc' : R₅ ≅ Rk k₁)
    {Mg : A ⥤ A'} {Sg : A' ⥤ A} {Mg' : B ⥤ B'} {Sg' : B' ⥤ B} {Tf : B ⥤ A} {Tf' : B' ⥤ A'}
    {Nk : ι → (B' ⥤ A)} (bg : Mg ⊣ Sg) (bg' : Mg' ⊣ Sg') (hg : Rg = Sg) (hg' : Rg' = Sg')
    (hf : Rf = Tf) (hf' : Rf' = Tf') (hk' : ∀ k, Rk k = Nk k)
    (h₃ : Tf' ⋙ Sg = Rf' ⋙ Rg) (h₄ : Sg' ⋙ Tf = Rg' ⋙ Rf)
    (mc : Tf' ⋙ Sg ≅ Nk k₂) (mc' : Sg' ⋙ Tf ≅ Nk k₁)
    (hmc : mc = eqToIso h₃ ≪≫ pc.symm ≪≫ tc ≪≫ eqToIso (hk' k₂))
    (hmc' : mc' = eqToIso h₄ ≪≫ pc'.symm ≪≫ tc' ≪≫ eqToIso (hk' k₁))
    (β : Tf ⋙ Mg ⟶ Mg' ⋙ Tf')
    (hβ : β = (mateEquiv bg' bg).symm
      (TwoSquare.mk _ _ _ _ (mc'.hom ≫ eqToHom (congrArg Nk hk) ≫ mc.inv)))
    (K : B)
    (hK : IsIso (map adjf adjf'
      ((Adjunction.leftAdjointUniq (a₂.ofNatIsoRight pc) (ag.comp adjf')).symm ≪≫
        Adjunction.leftAdjointUniq a₂ ((ak k₂).ofNatIsoRight tc.symm))
      (((Adjunction.leftAdjointUniq (a₅.ofNatIsoRight pc') (adjf.comp ag')).symm ≪≫
        Adjunction.leftAdjointUniq a₅ ((ak k₁).ofNatIsoRight tc'.symm)) ≪≫
          eqToIso (congrArg Lk hk)) K)) :
    IsIso (β.app K) := by
  have key : IsIso ((twoSquare adjf adjf'
      ((Adjunction.leftAdjointUniq (a₂.ofNatIsoRight pc) (ag.comp adjf')).symm ≪≫
        Adjunction.leftAdjointUniq a₂ ((ak k₂).ofNatIsoRight tc.symm))
      (((Adjunction.leftAdjointUniq (a₅.ofNatIsoRight pc') (adjf.comp ag')).symm ≪≫
        Adjunction.leftAdjointUniq a₅ ((ak k₁).ofNatIsoRight tc'.symm)) ≪≫
          eqToIso (congrArg Lk hk))).app K) := hK
  rw [twoSquare_eq_mateEquiv_symm_conjugateEquiv _ _ _ _ ag ag',
    conjugateEquiv_pullbackComparison_leftAdjointUniq adjf adjf' ag ag' a₂ a₅ ak hk] at key
  subst hβ
  refine isIso_mateEquiv_symm_app_of_eq bg ag bg' ag' hg.symm hg'.symm hf.symm hf'.symm _ _
    h₄.symm h₃ ?_ K key
  subst hmc hmc' hk
  simp

end Mates

section Single

attribute [local instance] HasDerivedCategory.standard

variable {VY VX VY' VX' : Type*} [Category* VY] [Category* VX] [Category* VY'] [Category* VX']
  [Abelian VY] [Abelian VX] [Abelian VY'] [Abelian VX']
  {pf : VY ⥤ VX} {qf : VX ⥤ VY} {pf' : VY' ⥤ VX'} {qf' : VX' ⥤ VY'}
  {pg : VY ⥤ VY'} {pg' : VX ⥤ VX'}
  [pf.Additive] [qf.Additive] [pf'.Additive] [qf'.Additive] [pg.Additive] [pg'.Additive]

/-- **The underived base change map at a module from the one on homotopy categories in degree
zero.** If the base change map on homotopy categories, at the complex `M[0]`, is an isomorphism on
degree-zero cohomology in the derived category, then the base change map of the underlying
functors is invertible at `M`. -/
private theorem isIso_map_of_isIso_homology_map_mapHomotopyCategory_single {T : Sort*}
    (P : T → (VY ⥤ VX')) [∀ t, (P t).Additive] {t₁ t₂ : T} (h : t₁ = t₂)
    {pcg pcf : VY ⥤ VX'} [pcg.Additive] [pcf.Additive] (a : pf ⊣ qf) (a' : pf' ⊣ qf')
    (eg₀ : pg ⋙ pf' ≅ pcg) (eg₁ : pcg ≅ P t₂) (ef₀ : pf ⋙ pg' ≅ pcf) (ef₁ : pcf ≅ P t₁) (M : VX)
    (h0 : IsIso ((DerivedCategory.homologyFunctor VY' 0).map (DerivedCategory.Qh.map
      (map (a.mapHomotopyCategory (ComplexShape.up ℤ)) (a'.mapHomotopyCategory (ComplexShape.up ℤ))
        (Functor.mapHomotopyCategoryCompIso eg₀ (ComplexShape.up ℤ) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso eg₁ (ComplexShape.up ℤ))
        ((Functor.mapHomotopyCategoryCompIso ef₀ (ComplexShape.up ℤ) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso ef₁ (ComplexShape.up ℤ)) ≪≫
            eqToIso (congrArg (fun t => (P t).mapHomotopyCategory (ComplexShape.up ℤ)) h))
        ((HomotopyCategory.quotient VX (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single VX (ComplexShape.up ℤ) 0).obj M)))))) :
    IsIso (map a a' (eg₀ ≪≫ eg₁) ((ef₀ ≪≫ ef₁) ≪≫ eqToIso (congrArg P h)) M) := by
  subst h
  simp only [eqToIso_refl, Iso.trans_refl] at h0 ⊢
  rw [mapHomotopyCategoryCompIso_trans, mapHomotopyCategoryCompIso_trans,
    map_mapHomotopyCategory_quotient_obj] at h0
  exact (isIso_map_iff_of_iso a a' (eg₀ ≪≫ eg₁) (ef₀ ≪≫ ef₁)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)).1
    ((HomologicalComplex.isIso_homologyMap_zero_iff
      ((NatTrans.mapHomologicalComplex (twoSquare a a' (eg₀ ≪≫ eg₁) (ef₀ ≪≫ ef₁))
        (ComplexShape.up ℤ)).app ((HomologicalComplex.single VX (ComplexShape.up ℤ) 0).obj M))
      (fun n hn => pg.map_isZero
        (qf.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)))
      (fun n hn => qf'.map_isZero
        (pg'.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)))).1
      ((isIso_homology_Qh_map_quotient_map_iff _).1 h0))

end Single

end Stacks.CategoryTheory.BaseChange.DegreeZeroBaseChange

namespace AlgebraicGeometry.Space.DescentStratum

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard

open AlgebraicGeometry.Space Stacks.CategoryTheory.BaseChange.DegreeZeroBaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Degree-zero cohomology of complexes and the comparison of a right exact functor -/

section Homology

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- The comparison `G(H⁰(A)) ⟶ H⁰(G(A))` of a right exact functor is an isomorphism when the
complex `A` vanishes in positive degrees. -/
private theorem isIso_homologyComparison_zero_of_isStrictlyLE (G : C ⥤ D) [G.Additive]
    [PreservesFiniteColimits G] (A : CochainComplex C ℤ) [A.IsStrictlyLE 0] :
    IsIso (G.homologyComparisonRightExactHomologyComparison A 0) := by
  have hA : IsZero (A.X 1) := A.isZero_of_isStrictlyLE 0 1 (by omega)
  have hd : A.d 0 1 = 0 := hA.eq_of_tgt _ _
  have hd' : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj A).d 0 1 = 0 :=
    (G.map_isZero hA).eq_of_tgt _ _
  have := A.isIso_iCycles 0 1 (by simp) hd
  have := ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj A).isIso_iCycles 0 1 (by simp) hd'
  have : IsIso (G.cyclesComparisonRightExactHomologyComparison A 0 ≫
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj A).iCycles 0) := by
    rw [Functor.cyclesComparisonRightExactHomologyComparison, HomologicalComplex.liftCycles_i]
    infer_instance
  have : IsIso (G.cyclesComparisonRightExactHomologyComparison A 0) :=
    IsIso.of_isIso_comp_right _ (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj A).iCycles 0)
  exact G.isIso_homologyComparison_of_isIso_cyclesComparison_rightExactHomologyComparison A 0

/-- A right exact functor carries a map of complexes inducing an isomorphism on `H⁰` to one, as
soon as the comparisons `G(H⁰) ⟶ H⁰(G)` at both complexes are isomorphisms. -/
private theorem isIso_homologyMap_map_zero (G : C ⥤ D) [G.Additive] [PreservesFiniteColimits G]
    {A A' : CochainComplex C ℤ} (h : A ⟶ A')
    (hA : IsIso (G.homologyComparisonRightExactHomologyComparison A 0))
    (hA' : IsIso (G.homologyComparisonRightExactHomologyComparison A' 0))
    (hh : IsIso (HomologicalComplex.homologyMap h 0)) :
    IsIso (HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map h) 0) := by
  have e := G.homologyComparison_naturality_rightExactHomologyComparison 0 h
  have : IsIso (G.homologyComparisonRightExactHomologyComparison A 0 ≫
      HomologicalComplex.homologyMap ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map h) 0) := by
    rw [← e]
    infer_instance
  exact IsIso.of_isIso_comp_left (G.homologyComparisonRightExactHomologyComparison A 0) _

/-- The comparison `G(H⁰) ⟶ H⁰(G)` is invariant under an isomorphism of right exact functors. -/
private theorem isIso_homologyComparison_of_natIso {G G' : C ⥤ D} [G.Additive] [G'.Additive]
    [PreservesFiniteColimits G] [PreservesFiniteColimits G'] (e : G ≅ G')
    (A : CochainComplex C ℤ) (n : ℤ)
    (h : IsIso (G.homologyComparisonRightExactHomologyComparison A n)) :
    IsIso (G'.homologyComparisonRightExactHomologyComparison A n) := by
  have := h
  have : IsIso ((𝟭 D).homologyComparisonRightExactHomologyComparison
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) n) :=
    (𝟭 D).isIso_homologyComparison_of_preservesFiniteLimits_rightExactHomologyComparison _ n
  exact Functor.isIso_homologyComparison_of_comp_rightExactHomologyComparison G (𝟭 D) G'
    (Functor.rightUnitor G ≪≫ e) A n

end Homology

/-! ### The comparison `Lg^*(Q A) ⟶ Q(g^* A)` in degree zero -/


section Pullback

variable {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)

/-- The pullback of modules along the morphism of small étale ringed topoi is right exact: it is a
left adjoint. -/
private instance preservesFiniteColimits_smallEtalePullbackModules :
    PreservesFiniteColimits ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules) :=
  haveI := (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
    (X := smallEtaleRingedTopos B S hS Y') (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS g)).isLeftAdjoint
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- A complex of `𝒪_Y`-modules vanishing in positive degrees receives a quasi-isomorphism from a
K-flat complex with flat terms vanishing in positive degrees. -/
private theorem exists_quasiIso_kFlat_of_isStrictlyLE
    (A : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    [A.IsStrictlyLE 0] :
    ∃ (R : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
      (r : R ⟶ A), QuasiIso r ∧ R.IsStrictlyLE 0 ∧
        smallEtaleModuleKFlat B S hS Y
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) := by
  let Pflat : ObjectProperty (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
    fun M => AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) M
  have hz : IsZero (A.X 1) := A.isZero_of_isStrictlyLE 0 1 (by omega)
  let _ : Pflat.ContainsZero := ⟨⟨A.X 1, hz, isFlat_of_isZero B S hS hz⟩⟩
  have hcover : ∀ M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      ∃ (N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (_ : Pflat N)
        (p : N ⟶ M), Epi p := by
    intro M
    obtain ⟨N, p, hN, hp⟩ :=
      Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize
        (smallEtaleRingedTopos B S hS Y).O M
    exact ⟨N, hN, p, hp⟩
  obtain ⟨R, r, -, hr, hflat, hLE⟩ := (CochainComplex.exists_quasiIso_prop Pflat hcover 0).1 A
  exact ⟨R, r, hr, hLE, smallEtaleModuleKFlat_of_isStrictlyLE B S hS Y R 0 hflat⟩

/-- Degreewise pullback of a map of complexes inducing an isomorphism on `H⁰`, between complexes
on which `g^*` commutes with `H⁰`, induces an isomorphism on `H⁰`. -/
private theorem isIso_homology_pullbackOnHomotopy_map_quotient_map
    {A A' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (h : A ⟶ A')
    (hA : IsIso ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules
      |>.homologyComparisonRightExactHomologyComparison A 0))
    (hA' : IsIso ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules
      |>.homologyComparisonRightExactHomologyComparison A' 0))
    (hh : IsIso (HomologicalComplex.homologyMap h 0)) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((pullbackOnHomotopy (smallEtaleRingedToposHom B S hS g)).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map h))) := by
  rw [Functor.comp_map, Functor.mapHomotopyCategory_map]
  exact (isIso_homology_Qh_map_quotient_map_iff _).2 (isIso_homologyMap_map_zero _ h hA hA' hh)

/-- **`Tor₀` is the pullback.** For a complex `A` of `𝒪_Y`-modules vanishing in positive
degrees, the comparison `Lg^*A ⟶ g^*A` is an isomorphism on degree-zero cohomology. -/
private theorem isIso_homology_smallEtaleDerivedModulePullbackComparison_app_of_isStrictlyLE
    (A : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    [A.IsStrictlyLE 0] :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((smallEtaleDerivedModulePullbackComparison B S hS g).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj A))) := by
  obtain ⟨R, r, hr, hLE, hR⟩ := exists_quasiIso_kFlat_of_isStrictlyLE A
  have := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS g _ hR
  have := isIso_Qh_map_quotient_map r
  exact isIso_map_of_comm_of_isIso (DerivedCategory.homologyFunctor _ 0)
    ((smallEtaleDerivedModulePullbackComparison B S hS g).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map r))
    (Functor.map_isIso _ ((smallEtaleDerivedModulePullback B S hS g).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map r))))
    inferInstance
    (isIso_homology_pullbackOnHomotopy_map_quotient_map g r
      (isIso_homologyComparison_zero_of_isStrictlyLE _ R)
      (isIso_homologyComparison_zero_of_isStrictlyLE _ A)
      inferInstance)

/-- The derived pullback of a map of complexes inducing an isomorphism on `H⁰` induces an
isomorphism on `H⁰`, when the comparison `Lg^* ⟶ g^*` is an isomorphism on `H⁰` at the source
and an isomorphism at the target, and `g^*` commutes with `H⁰` on both complexes. -/
private theorem isIso_homology_map_smallEtaleDerivedModulePullback_map
    {A A' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (h : A ⟶ A')
    (hA : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((smallEtaleDerivedModulePullbackComparison B S hS g).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj A))))
    (hA' : IsIso ((smallEtaleDerivedModulePullbackComparison B S hS g).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj A')))
    (hcA : IsIso ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules
      |>.homologyComparisonRightExactHomologyComparison A 0))
    (hcA' : IsIso ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules
      |>.homologyComparisonRightExactHomologyComparison A' 0))
    (hh : IsIso (HomologicalComplex.homologyMap h 0)) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((DerivedCategory.Qh ⋙ smallEtaleDerivedModulePullback B S hS g).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map h))) :=
  isIso_map_of_comm_of_isIso' (DerivedCategory.homologyFunctor _ 0)
    ((smallEtaleDerivedModulePullbackComparison B S hS g).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map h))
    (Functor.map_isIso _ _) hA
    (isIso_homology_pullbackOnHomotopy_map_quotient_map g h hcA hcA' hh)

/-- **`H⁰(Lg^* y)` for a map `y : M ⟶ P` inducing an isomorphism on `H⁰`**, with `M` vanishing in
positive degrees and `P` K-flat with `g^*` commuting with `H⁰(P)`, is an isomorphism. -/
private theorem isIso_homology_map_smallEtaleDerivedModulePullback_map_of_kFlat
    {M P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    [M.IsStrictlyLE 0]
    (hP : smallEtaleModuleKFlat B S hS Y ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (hcP : IsIso ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules
      |>.homologyComparisonRightExactHomologyComparison P 0))
    (y : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (hy : IsIso ((DerivedCategory.homologyFunctor _ 0).map y)) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((smallEtaleDerivedModulePullback B S hS g).map y)) := by
  obtain ⟨X', hX', ι, hι, g₁, rfl⟩ := exists_eq_comp_Qh_map_quotient_map y
  have hg₁ : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g₁))) := by
    rw [Functor.map_comp] at hy
    exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor _ 0).map ι) _
  have hL := isIso_homology_map_smallEtaleDerivedModulePullback_map g g₁
    (isIso_homology_smallEtaleDerivedModulePullbackComparison_app_of_isStrictlyLE g X')
    (isIso_smallEtaleDerivedModulePullbackComparison_app B S hS g _ hP)
    (isIso_homologyComparison_zero_of_isStrictlyLE _ X')
    hcP ((isIso_homology_Qh_map_quotient_map_iff g₁).1 hg₁)
  rw [Functor.map_comp, Functor.map_comp]
  exact IsIso.comp_isIso' inferInstance hL

end Pullback


section DirectImage

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **`R⁰f_* = f_*`.** The unit `f_*N[0] ⟶ Rf_*N[0]` of the derived direct image is an
isomorphism on degree-zero cohomology, `f_*` being left exact. -/
private theorem isIso_homology_totalRightDerivedUnit_app_single
    (N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit
          DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS X))).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N)))) := by
  have := (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f)).isRightAdjoint
  have : PreservesFiniteLimits (AlgebraicGeometry.RingedToposHom.pushforwardModules
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f)) :=
    PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  exact isIso_homology_unit_app_single _ _ _ N

end DirectImage

section Topos

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- The base change map of Stacks 03LU is invertible at a module as soon as the base change map
of modules of the small étale ringed topoi is invertible there: the converse of
`AlgebraicGeometry.Space.isIso_smallEtaleModuleBaseChangeMap_of_isIso_moduleBaseChangeMap_app`. -/
private theorem isIso_moduleBaseChangeMap_app_of_isIso_smallEtaleModuleBaseChangeMap
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (h : IsIso (smallEtaleModuleBaseChangeMap B S hS f g f' g' w M)) :
    IsIso ((moduleBaseChangeMap f g f' g' w).app M) :=
  isIso_mateEquiv_symm_app_of_isIso_map
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f))
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y') (smallEtaleRingedToposHom B S hS f'))
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS Y')
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS g))
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g'))
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHomComp B S hS f' g))
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHomComp B S hS g' f))
    (fun k : X' ⟶ Y => RingedToposHom.pullbackAdjPushforwardModules
      (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS k)) w
    (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f')
      (smallEtaleRingedToposHom B S hS g))
    (pushforwardModulesCompTransport B S hS f' g)
    (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS g')
      (smallEtaleRingedToposHom B S hS f))
    (pushforwardModulesCompTransport B S hS g' f)
    (modulePullbackAdjunction B S hS g) (modulePullbackAdjunction B S hS g')
    (pushforwardModules_eq_modulePushforward B S hS g)
    (pushforwardModules_eq_modulePushforward B S hS g')
    (pushforwardModules_eq_modulePushforward B S hS f)
    (pushforwardModules_eq_modulePushforward B S hS f')
    (fun k => pushforwardModules_eq_modulePushforward B S hS k)
    (modulePushforward_comp_eq B S hS f' g) (modulePushforward_comp_eq B S hS g' f)
    (modulePushforwardCompIso B S hS f' g) (modulePushforwardCompIso B S hS g' f)
    (modulePushforwardCompIso.eq_1 B S hS f' g) (modulePushforwardCompIso.eq_1 B S hS g' f)
    (moduleBaseChangeMap f g f' g' w) (moduleBaseChangeMap.eq_1 f g f' g' w) M h

/-- The base change map of modules of the small étale ringed topoi is invertible at `G` as soon
as the underived base change map on homotopy categories at `G[0]` is an isomorphism on
degree-zero cohomology. -/
private theorem isIso_smallEtaleModuleBaseChangeMap_of_isIso_homology
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (h0 : IsIso ((DerivedCategory.homologyFunctor _ 0).map (DerivedCategory.Qh.map
      (smallEtaleUnderivedBaseChangeMap B S hS f g f' g' w
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))))) :
    IsIso (smallEtaleModuleBaseChangeMap B S hS f g f' g' w G) :=
  have := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS f' g)
  have := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g' f)
  isIso_map_of_isIso_homology_map_mapHomotopyCategory_single
    (fun k : X' ⟶ Y => Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS k).toModulesHom) w
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f))
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y') (smallEtaleRingedToposHom B S hS f'))
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f')
        (smallEtaleRingedToposHom B S hS g)).symm (pullbackModulesCompTransport B S hS f' g)
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS g')
        (smallEtaleRingedToposHom B S hS f)).symm (pullbackModulesCompTransport B S hS g' f)
    G h0

/-- `R⁰f'_*` at `(g')^*G[0]`, read on the homotopy category. -/
private theorem isIso_homology_totalRightDerivedUnit_app_pullbackMapHomotopy_single
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X')
        (Y := smallEtaleRingedTopos B S hS Y')
        (smallEtaleRingedToposHom B S hS f')).totalRightDerivedUnit
          DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS X'))).app
        ((smallEtalePullbackMapHomotopy B S hS g').obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))))) := by
  let F' := (smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules
  let e : (smallEtalePullbackMapHomotopy B S hS g').obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) ≅
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (F'.obj G)) :=
    (HomotopyCategory.quotient _ _).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F' (ComplexShape.up ℤ) 0).app G)
  exact (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight
    ((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X')
        (Y := smallEtaleRingedTopos B S hS Y')
        (smallEtaleRingedToposHom B S hS f')).totalRightDerivedUnit
          DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS X')))
    (DerivedCategory.homologyFunctor _ 0)) e).2
    (isIso_homology_totalRightDerivedUnit_app_single f' (F'.obj G))

/-- The direct image of `G[0]` vanishes in positive degrees. -/
private theorem isStrictlyLE_pushforwardModules_single
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    CochainComplex.IsStrictlyLE
      (((AlgebraicGeometry.RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun _ hi =>
    (AlgebraicGeometry.RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ (ne_of_gt hi))

/-- `Tor₀` at `f_*G[0]`: the comparison `Lg^*(f_*G[0]) ⟶ g^*(f_*G[0])` is an isomorphism on
degree-zero cohomology. -/
private theorem isIso_homology_smallEtaleDerivedModulePullbackComparison_app_pushforward_single
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((smallEtaleDerivedModulePullbackComparison B S hS g).app
        ((smallEtalePushforwardMapHomotopy B S hS f).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))))) :=
  have := isStrictlyLE_pushforwardModules_single f G
  isIso_homology_smallEtaleDerivedModulePullbackComparison_app_of_isStrictlyLE g
    (((AlgebraicGeometry.RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))

/-- The identification of `(g')^*A` computed with `AlgebraicGeometry.Space.modulePullback` with
`(g')^*A` computed with the pullback of the morphism of ringed topoi, read in the derived category
through the homotopy category. -/
private def pullbackQIso
    (A : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    DerivedCategory.Q.obj (((modulePullback B S hS g').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((((smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj A)) :=
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS g').toModulesHom
  let G' : type_of% F := modulePullback B S hS g'
  haveI : G'.Additive := modulePullback_additive g'
  (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (F := F) (G := G')
    (pullbackModulesIsoModulePullback B S hS g') (ComplexShape.up ℤ)).app A)).symm ≪≫
    ((DerivedCategory.quotientCompQhIso _).app _).symm

/-- The comparison `L(g')^*(Q A) ⟶ Q((g')^* A)` followed by `pullbackQIso` is the comparison of
the derived pullback on the homotopy category. -/
private theorem smallEtaleDerivedModulePullbackQComparison_comp_pullbackQIso
    (A : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    smallEtaleDerivedModulePullbackQComparison g' A ≫ (pullbackQIso g' A).hom =
      (smallEtaleDerivedModulePullback B S hS g').map
          ((DerivedCategory.quotientCompQhIso _).inv.app A) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS g').app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj A) := by
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS g').toModulesHom
  let G' : type_of% F := modulePullback B S hS g'
  have : G'.Additive := modulePullback_additive g'
  exact comp_hom_comp_trans_symm_hom
    ((smallEtaleDerivedModulePullback B S hS g').map
      ((DerivedCategory.quotientCompQhIso _).inv.app A))
    ((smallEtaleDerivedModulePullbackComparison B S hS g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj A))
    ((DerivedCategory.quotientCompQhIso _).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A))
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (F := F) (G := G')
      (pullbackModulesIsoModulePullback B S hS g') (ComplexShape.up ℤ)).app A))

end Topos

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- The identification `Rf_*(G[0]) ≅ P` of the target of the unit `f_*G[0] ⟶ Rf_*G[0]` with a
model `P`, through the homotopy category. -/
private def unitTargetIso (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (e : DerivedCategory.Q.obj P ≅ (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))) :
    (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) :=
  (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _) ≪≫ e.symm ≪≫
    ((DerivedCategory.quotientCompQhIso _).app P).symm

/-- `H⁰(Lg^*(f_*G[0] ⟶ Rf_*G[0]))` is an isomorphism when `Rf_*G[0]` is represented by a K-flat
complex `P` with `g^*H⁰(P) = H⁰(g^*P)`. -/
private theorem isIso_homology_map_smallEtaleDerivedModulePullback_map_totalRightDerivedUnit
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hP : smallEtaleModuleKFlat B S hS Y ((HomotopyCategory.quotient _ _).obj P))
    (e : DerivedCategory.Q.obj P ≅ (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))
    (hcP : IsIso ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules
      |>.homologyComparisonRightExactHomologyComparison P 0)) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((smallEtaleDerivedModulePullback B S hS g).map
        (((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit DerivedCategory.Qh
            (sourceQuasiIso (smallEtaleRingedTopos B S hS X))).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))))) :=
  have := isStrictlyLE_pushforwardModules_single f G
  isIso_map_map_of_isIso_map_map_comp _ _ _ (unitTargetIso f G P e).hom
    (isIso_homology_map_smallEtaleDerivedModulePullback_map_of_kFlat g
      (M := ((AlgebraicGeometry.RingedToposHom.pushforwardModules
        (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))
      hP hcP _
      (isIso_map_comp_of_isIso_map _ _ (unitTargetIso f G P e).hom
        (isIso_homology_totalRightDerivedUnit_app_single f G)))

/-- The comparison `g^*H⁰(P) ⟶ H⁰(g^*P)` is invertible for the pullback of modules of the
morphism of small étale ringed topoi as soon as it is for
`AlgebraicGeometry.Space.modulePullback`. -/
private theorem isIso_homologyComparison_pullbackModules
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hcmp : IsIso ((modulePullback B S hS g).homologyComparisonRightExactHomologyComparison P 0)) :
    IsIso (((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules
      ).homologyComparisonRightExactHomologyComparison P 0) := by
  let F := (smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules
  let G' : type_of% F := modulePullback B S hS g
  have : G'.Additive := modulePullback_additive g
  have : PreservesFiniteColimits G' :=
    preservesFiniteColimits_of_natIso (F := F) (G := G') (pullbackModulesIsoModulePullback B S hS g)
  exact isIso_homologyComparison_of_natIso (G := G') (G' := F)
    (pullbackModulesIsoModulePullback B S hS g).symm P 0 hcmp

/-- The base change map followed by `Rf'_*` of the comparison, at `G[0]` read on the homotopy
category, is invertible when the composite of Stacks 0CTM, part (2) is. -/
private theorem isIso_smallEtaleDerivedBaseChangeComp_Qh_single
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hbc : IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))
      _ (smallEtaleDerivedModulePullbackQComparison g'
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))) _
      ((smallEtaleDerivedModulePullbackComparison B S hS g').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))) :=
  (isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS f g f' g' w _ _ _ _ _ _
    ((DerivedCategory.quotientCompQhIso _).app _).symm
    (pullbackQIso g' ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))
    (smallEtaleDerivedModulePullbackQComparison_comp_pullbackQIso g' _).symm).1 hbc

/-- The identity of `Stacks.CategoryTheory.BaseChange.map_comparison` for a square of
algebraic spaces: the derived base change map at a complex `K`, read through the unit of `Rf_*`
and the comparison of `L(g')^*`, is the comparison of `Lg^*` followed by the underived base
change map and the unit of `Rf'_*`. -/
private theorem derivedBaseChangeMap_comparison
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullback B S hS g).map
        (((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit DerivedCategory.Qh
            (sourceQuasiIso (smallEtaleRingedTopos B S hS X))).app K) ≫
      smallEtaleDerivedBaseChangeComp B S hS f g f' g' w (DerivedCategory.Qh.obj K) _
        ((smallEtaleDerivedModulePullbackComparison B S hS g').app K) =
    (smallEtaleDerivedModulePullbackComparison B S hS g).app
        ((smallEtalePushforwardMapHomotopy B S hS f).obj K) ≫
      DerivedCategory.Qh.map (smallEtaleUnderivedBaseChangeMap B S hS f g f' g' w K) ≫
      ((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X')
          (Y := smallEtaleRingedTopos B S hS Y')
          (smallEtaleRingedToposHom B S hS f')).totalRightDerivedUnit DerivedCategory.Qh
            (sourceQuasiIso (smallEtaleRingedTopos B S hS X'))).app
        ((smallEtalePullbackMapHomotopy B S hS g').obj K) :=
  map_comparison_of_eq
    (smallEtaleMapHomotopyAdjunction B S hS f) (smallEtaleMapHomotopyAdjunction B S hS f')
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackComparison B S hS f)
    (smallEtaleDerivedModulePullbackComparison B S hS f')
    (smallEtaleDerivedModulePullbackComparison B S hS g)
    (smallEtaleDerivedModulePullbackComparison B S hS g') _ _
    (fun f ↦ smallEtaleDerivedModulePullback B S hS f) (smallEtalePullbackMapHomotopy B S hS)
    (fun f ↦ smallEtaleDerivedModulePullbackComparison B S hS f) w
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackCompIso B S hS g' f)
    (smallEtaleUnderivedPullbackCompIso B S hS f' g)
    (smallEtaleUnderivedPullbackCompIso B S hS g' f)
    (smallEtaleDerivedModuleAdjunction_counit_fac B S hS f)
    (smallEtaleDerivedModuleAdjunction_counit_fac B S hS f')
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS f' g)
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS g' f) K

/-- **The degree-zero base change map from the derived one, with the degree-zero comparison
read on the unit of `Rf_*`.**

Let `g' ≫ f = f' ≫ g` be a commutative square of algebraic spaces and `G` an `𝒪_X`-module.
Suppose that

* `Lg^*` of the unit `f_*G[0] ⟶ Rf_*G[0]` of the derived direct image is an isomorphism on
  degree-zero cohomology: since `H⁰(Lg^*(f_*G[0])) = g^*f_*G` (`Tor₀` is the pullback), this says
  that the comparison `g^*H⁰(Rf_*G[0]) ⟶ H⁰(Lg^*Rf_*G[0])` is an isomorphism, `Rf_*G[0]` lying in
  degrees `≥ 0` with `H⁰ = f_*G`;
* the composite `Lg^*Rf_*G[0] ⟶ Rf'_*L(g')^*G[0] ⟶ Rf'_*((g')^*G)[0]` of Stacks 0CTM, part (2)
  (`AlgebraicGeometry.Space.smallEtaleDerivedBaseChangeComp` at the comparison
  `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackQComparison`) is an isomorphism.

Then the base change map `g^*f_*G ⟶ f'_*(g')^*G` of
`AlgebraicGeometry.Space.moduleBaseChangeMap` is an isomorphism. -/
theorem isIso_moduleBaseChangeMap_app_of_isIso_homology_map_unit
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hu : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((smallEtaleDerivedModulePullback B S hS g).map
        (((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit DerivedCategory.Qh
            (sourceQuasiIso (smallEtaleRingedTopos B S hS X))).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))))))
    (hbc : IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))
      _ (smallEtaleDerivedModulePullbackQComparison g'
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))) :
    IsIso ((moduleBaseChangeMap f g f' g' w).app G) :=
  isIso_moduleBaseChangeMap_app_of_isIso_smallEtaleModuleBaseChangeMap f g f' g' w G
    (isIso_smallEtaleModuleBaseChangeMap_of_isIso_homology f g f' g' w G
      (isIso_map_of_comm₃_of_isIso (DerivedCategory.homologyFunctor _ 0)
        (derivedBaseChangeMap_comparison f g f' g' w _) hu
        (by
          have := isIso_smallEtaleDerivedBaseChangeComp_Qh_single f g f' g' w G hbc
          exact Functor.map_isIso _ _)
        (isIso_homology_smallEtaleDerivedModulePullbackComparison_app_pushforward_single f g G)
        (isIso_homology_totalRightDerivedUnit_app_pullbackMapHomotopy_single f' g' G)))

/-- **The degree-zero base change map from the derived one, through a K-flat model on the base.**

Let `g' ≫ f = f' ≫ g` be a commutative square of algebraic spaces, `G` an `𝒪_X`-module, and `P` a
K-flat complex of `𝒪_Y`-modules with flat terms together with `e : P ≅ Rf_*G[0]` in `D(𝒪_Y)`.
If the comparison `g^*H⁰(P) ⟶ H⁰(g^*P)` of the right exact `g^*` is an isomorphism and the
composite `Lg^*Rf_*G[0] ⟶ Rf'_*((g')^*G)[0]` of Stacks 0CTM, part (2) is an isomorphism, then the
base change map `g^*f_*G ⟶ f'_*(g')^*G` of `AlgebraicGeometry.Space.moduleBaseChangeMap` is an
isomorphism. -/
theorem isIso_moduleBaseChangeMap_app_of_isIso_homologyComparison
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hP : smallEtaleModuleKFlat B S hS Y ((HomotopyCategory.quotient _ _).obj P))
    (e : DerivedCategory.Q.obj P ≅ (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))
    (hcmp : IsIso ((modulePullback B S hS g).homologyComparisonRightExactHomologyComparison P 0))
    (hbc : IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))
      _ (smallEtaleDerivedModulePullbackQComparison g'
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))) :
    IsIso ((moduleBaseChangeMap f g f' g' w).app G) :=
  isIso_moduleBaseChangeMap_app_of_isIso_homology_map_unit f g f' g' w G
    (isIso_homology_map_smallEtaleDerivedModulePullback_map_totalRightDerivedUnit f g G P hP e
      (isIso_homologyComparison_pullbackModules g P hcmp)) hbc

end Square

end AlgebraicGeometry.Space.DescentStratum

end
