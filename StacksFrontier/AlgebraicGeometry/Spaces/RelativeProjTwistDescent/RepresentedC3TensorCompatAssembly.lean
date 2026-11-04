module

public import
    StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedC3TensorCompatProof

/-!
# The compatibility (b) of Stacks 084D

For a morphism `g : V ⟶ U` of the big fppf site and quasi-coherent modules `M`, `N` on the scheme
underlying `U`, the identification `(M ⊗ N)_{yoneda U} ≅ M_{yoneda U} ⊗ N_{yoneda U}` of Stacks
03DX (2) is compatible with inverse images along `g`
(`AlgebraicGeometry.Space.RepresentedC3TensorCompat`).

## Main results

* `AlgebraicGeometry.Space.representedC3TensorCompat`: the compatibility (b).
* `AlgebraicGeometry.Space.tensorCompat_of_readings_of_heq`: its abstract shape, at variables.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u uC vC uD vD uX vX

namespace AlgebraicGeometry.Space

section Abstract

/-- Heterogeneously equal isomorphisms between equal objects have heterogeneously equal
underlying morphisms. -/
theorem heq_hom_of_heq {C : Type*} [Category C] {A B A₂ B₂ : C} (hA : A₂ = A) (hB : B₂ = B)
    {i₂ : A₂ ≅ B₂} {i : A ≅ B} (hi : HEq i₂ i) : HEq i₂.hom i.hom := by
  subst hA hB
  obtain rfl := eq_of_heq hi
  rfl

/-- A functor equal to a second one sends heterogeneously equal morphisms between equal objects to
heterogeneously equal morphisms. -/
theorem heq_map_of_heq {C D : Type*} [Category C] [Category D] {L L₂ : C ⥤ D} (hL : L₂ = L)
    {A B A₂ B₂ : C} (hA : A₂ = A) (hB : B₂ = B) {f₂ : A₂ ⟶ B₂} {f : A ⟶ B} (hf : HEq f₂ f) :
    HEq (L₂.map f₂) (L.map f) := by
  subst hL hA hB
  obtain rfl := eq_of_heq hf
  rfl

/-- An equation `c ≫ d ≫ (T.map m).app G ≫ (T.obj xM).map n = r ≫ a ≫ b` transported along
equalities of the objects and heterogeneous equalities of the morphisms. -/
theorem bifunctor_comp_eq_of_heq {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {K₂ Y₂ F₂ G₂ xM₂ xN₂ R₂ X₂ K Y F G xM xN R X : C}
    (hK : K₂ = K) (hY : Y₂ = Y) (hF : F₂ = F) (hG : G₂ = G) (hxM : xM₂ = xM) (hxN : xN₂ = xN)
    (hR : R₂ = R) (hX : X₂ = X)
    {c₂ : K₂ ⟶ Y₂} {d₂ : Y₂ ⟶ (T.obj F₂).obj G₂} {m₂ : F₂ ⟶ xM₂} {n₂ : G₂ ⟶ xN₂}
    {r₂ : K₂ ⟶ R₂} {a₂ : R₂ ⟶ X₂} {b₂ : X₂ ⟶ (T.obj xM₂).obj xN₂}
    {c : K ⟶ Y} {d : Y ⟶ (T.obj F).obj G} {m : F ⟶ xM} {n : G ⟶ xN} {r : K ⟶ R} {a : R ⟶ X}
    {b : X ⟶ (T.obj xM).obj xN}
    (hc : HEq c₂ c) (hd : HEq d₂ d) (hm : HEq m₂ m) (hn : HEq n₂ n) (hr : HEq r₂ r)
    (ha : HEq a₂ a) (hb : HEq b₂ b)
    (h : c₂ ≫ d₂ ≫ (T.map m₂).app G₂ ≫ (T.obj xM₂).map n₂ = r₂ ≫ a₂ ≫ b₂) :
    c ≫ d ≫ (T.map m).app G ≫ (T.obj xM).map n = r ≫ a ≫ b := by
  subst hK hY hF hG hxM hxN hR hX
  simp only [heq_eq_eq] at hc hd hm hn hr ha hb
  subst hc hd hm hn hr ha hb
  exact h

/-- `AlgebraicGeometry.Space.heq_hom_of_heq` across two equal categories. -/
theorem heq_hom_of_heq_of_heq {C C₂ : Type uC} [iC : Category.{vC} C] [iC₂ : Category.{vC} C₂]
    (hC : C₂ = C) (hiC : HEq iC₂ iC) {A B : C} {A₂ B₂ : C₂} (hA : HEq A₂ A) (hB : HEq B₂ B)
    {i : A ≅ B} {i₂ : A₂ ≅ B₂} (hi : HEq i₂ i) : HEq i₂.hom i.hom := by
  subst hC
  simp only [heq_eq_eq] at hiC hA hB hi
  subst hiC hA hB hi
  rfl

/-- `AlgebraicGeometry.Space.heq_map_of_heq` across two pairs of equal categories. -/
theorem heq_map_of_heq_of_heq {C C₂ : Type uC} {D D₂ : Type uD} [iC : Category.{vC} C]
    [iC₂ : Category.{vC} C₂] [iD : Category.{vD} D] [iD₂ : Category.{vD} D₂] (hC : C₂ = C)
    (hiC : HEq iC₂ iC) (hD : D₂ = D) (hiD : HEq iD₂ iD) {L : C ⥤ D} {L₂ : C₂ ⥤ D₂}
    (hL : HEq L₂ L) {A B : C} {A₂ B₂ : C₂} (hA : HEq A₂ A) (hB : HEq B₂ B) {f : A ⟶ B}
    {f₂ : A₂ ⟶ B₂} (hf : HEq f₂ f) : HEq (L₂.map f₂) (L.map f) := by
  subst hC hD
  simp only [heq_eq_eq] at hiC hiD hL hA hB hf
  subst hiC hiD hL hA hB hf
  rfl

/-- `AlgebraicGeometry.Space.tensorCompat_of_readings` with Stacks 03EL round the square of schemes
(`h₂`) taken in its own category `CX₂` and in its own spelling, linked to the slots of the
compatibility by equalities of categories and objects and heterogeneous equalities of morphisms,
and with the naturality of Stacks 03EL (`hpV`) at its own objects. -/
theorem tensorCompat_of_readings_of_heq {CX : Type uX} {CY DU DV : Type*}
    [instCX : Category.{vX} CX] [Category CY] [Category DU] [Category DV] (TX : CX ⥤ CX ⥤ CX)
    (TV : DV ⥤ DV ⥤ DV) (E : CX ⥤ DV)
    (EU : CY ⥤ DU) (Ac : CY ⥤ CX) (Phi : DU ⥤ DV) (θ : Ac ⋙ E ⟶ EU ⋙ Phi) (hθiso : IsIso θ)
    (FY GY FGY : CY) (UT : DU)
    (bct : Ac.obj FGY ⟶ (TX.obj (Ac.obj FY)).obj (Ac.obj GY))
    (pV : E.obj ((TX.obj (Ac.obj FY)).obj (Ac.obj GY)) ⟶
      (TV.obj (E.obj (Ac.obj FY))).obj (E.obj (Ac.obj GY)))
    (pU : EU.obj FGY ⟶ UT)
    (pφ' : Phi.obj UT ⟶ (TV.obj (Phi.obj (EU.obj FY))).obj (Phi.obj (EU.obj GY)))
    (hKF1 : E.map bct ≫ pV ≫ (TV.map (θ.app FY)).app (E.obj (Ac.obj GY)) ≫
        (TV.obj (Phi.obj (EU.obj FY))).map (θ.app GY) = θ.app FGY ≫ Phi.map pU ≫ pφ')
    (xM : CX) (mM : Ac.obj FY ⟶ xM) (cM : Phi.obj (EU.obj FY) ⟶ E.obj xM)
    (hcM : θ.app FY ≫ cM = E.map mM)
    (xN : CX) (mN : Ac.obj GY ⟶ xN) (cN : Phi.obj (EU.obj GY) ⟶ E.obj xN)
    (hcN : θ.app GY ≫ cN = E.map mN)
    (KY : CY) (xMN : CX) (mMN : Ac.obj KY ⟶ xMN) (cMN : Phi.obj (EU.obj KY) ⟶ E.obj xMN)
    (hcMN : θ.app KY ≫ cMN = E.map mMN)
    (A₃ C₃ : CX) (mM₃ : A₃ ⟶ xM) (mN₃ : C₃ ⟶ xN)
    (pV₃ : E.obj ((TX.obj A₃).obj C₃) ≅ (TV.obj (E.obj A₃)).obj (E.obj C₃))
    (pV2 : E.obj ((TX.obj xM).obj xN) ⟶ (TV.obj (E.obj xM)).obj (E.obj xN))
    (hpV : E.map ((TX.map mM₃).app C₃ ≫ (TX.obj xM).map mN₃) ≫ pV2 =
      pV₃.hom ≫ (TV.map (E.map mM₃)).app (E.obj C₃) ≫ (TV.obj (E.obj xM)).map (E.map mN₃))
    (hA₃ : A₃ = Ac.obj FY) (hC₃ : C₃ = Ac.obj GY) (hmM₃ : HEq mM₃ mM) (hmN₃ : HEq mN₃ mN)
    (hpV₃ : HEq pV₃.hom pV)
    (Z : Type*) (instZ : Category Z) (Y₁c : Type*) (instY₁ : Category Y₁c) (Y₂c : Type*)
    (instY₂ : Category Y₂c) (CX₂ : Type uX) (instCX₂ : Category.{vX} CX₂) (Lψ₁ : Z ⥤ Y₁c)
    (Lφ₁ : Y₁c ⥤ CX₂) (Lψ₂ : Z ⥤ Y₂c) (Lφ₂ : Y₂c ⥤ CX₂)
    (e₂ : Lψ₁ ⋙ Lφ₁ ≅ Lψ₂ ⋙ Lφ₂) (T₂ : CX₂ ⥤ CX₂ ⥤ CX₂) (F₂ G₂ K₂ : Z)
    (X₁ Y₁ : CX₂) (a₂ : Lφ₁.obj (Lψ₁.obj K₂) ⟶ X₁)
    (b₂ : X₁ ⟶ (T₂.obj (Lφ₁.obj (Lψ₁.obj F₂))).obj (Lφ₁.obj (Lψ₁.obj G₂)))
    (c₂ : Lφ₂.obj (Lψ₂.obj K₂) ⟶ Y₁)
    (d₂ : Y₁ ⟶ (T₂.obj (Lφ₂.obj (Lψ₂.obj F₂))).obj (Lφ₂.obj (Lψ₂.obj G₂)))
    (h₂ : a₂ ≫ b₂ ≫ (T₂.map (e₂.hom.app F₂)).app (Lφ₁.obj (Lψ₁.obj G₂)) ≫
        (T₂.obj (Lφ₂.obj (Lψ₂.obj F₂))).map (e₂.hom.app G₂) = e₂.hom.app K₂ ≫ c₂ ≫ d₂)
    (e'₂ : Lψ₁ ⋙ Lφ₁ ≅ Lψ₂ ⋙ Lφ₂) (he₂ : e₂ = e'₂)
    (hCX : CX₂ = CX) (hinst : HEq instCX₂ instCX) (hT : HEq T₂ TX) (K₁ : Z) (hK : K₂ = K₁)
    (hQK : HEq (Lφ₂.obj (Lψ₂.obj K₁)) (Ac.obj KY)) (hY : HEq Y₁ (Ac.obj FGY))
    (hQF : HEq (Lφ₂.obj (Lψ₂.obj F₂)) (Ac.obj FY)) (hQG : HEq (Lφ₂.obj (Lψ₂.obj G₂)) (Ac.obj GY))
    (hPF : HEq (Lφ₁.obj (Lψ₁.obj F₂)) xM) (hPG : HEq (Lφ₁.obj (Lψ₁.obj G₂)) xN)
    (hPK : HEq (Lφ₁.obj (Lψ₁.obj K₁)) xMN)
    (PY : KY ≅ FGY) (hc : HEq c₂ (Ac.map PY.hom)) (hd : HEq d₂ bct)
    (hmM : HEq (e'₂.inv.app F₂) mM) (hmN : HEq (e'₂.inv.app G₂) mN)
    (hmMN : HEq (e'₂.inv.app K₁) mMN)
    (xMN' : CX) (q : xMN ⟶ xMN') (PX : xMN' ≅ (TX.obj xM).obj xN) (ha : HEq a₂ q)
    (hb : HEq b₂ PX.hom) (hX : HEq X₁ xMN')
    (O0 : DU) (PU : EU.obj FGY ≅ UT) (wU : O0 ≅ UT)
    (TU : EU.obj KY ≅ O0) (hTU : TU = EU.mapIso PY ≪≫ PU ≪≫ wU.symm)
    (O1 : DV) (wV : O1 ≅ (TV.obj (Phi.obj (EU.obj FY))).obj (Phi.obj (EU.obj GY)))
    (pφ : Phi.obj UT ⟶ (TV.obj (Phi.obj (EU.obj FY))).obj (Phi.obj (EU.obj GY)))
    (f2 : Phi.obj O0 ⟶ O1) (hf2 : f2 = Phi.map wU.hom ≫ pφ ≫ wV.inv)
    (hpU : PU.hom = pU) (hpφ : pφ' = pφ)
    (O2 : DV) (wX : O2 ≅ (TV.obj (E.obj xM)).obj (E.obj xN)) (f3 : O1 ⟶ O2)
    (hf3 : f3 ≫ wX.hom = wV.hom ≫ (TV.map cM).app _ ≫ (TV.obj (E.obj xM)).map cN)
    (g2 : E.obj xMN ⟶ E.obj xMN') (hg2 : g2 = E.map q)
    (PV2 : E.obj ((TX.obj xM).obj xN) ≅ (TV.obj (E.obj xM)).obj (E.obj xN))
    (hpV2 : PV2.hom = pV2)
    (TV' : E.obj xMN' ≅ O2) (hTV : TV' = E.mapIso PX ≪≫ PV2 ≪≫ wX.symm) :
    Phi.map TU.hom ≫ f2 ≫ f3 = cMN ≫ g2 ≫ TV'.hom := by
  have := hθiso
  subst hA₃ hC₃
  obtain rfl := eq_of_heq hmM₃
  obtain rfl := eq_of_heq hmN₃
  obtain rfl := eq_of_heq hpV₃
  have h := tensorSquare_inv_of_hom T₂ e₂ e'₂ he₂ F₂ G₂ K₂ a₂ b₂ c₂ d₂ h₂
  subst hCX
  obtain rfl := eq_of_heq hinst
  obtain rfl := eq_of_heq hT
  subst hK
  exact tensorCompat_of_readings _ _ E EU Ac Phi θ PY PU wU TU hTU wV pφ f2 hf2 bct _ pU hpU
    pφ' hpφ θ rfl hKF1 _ _ mMN cM cN cMN hcM hcN hcMN wX f3 hf3 q g2 hg2 PX PV2 TV' hTV pV2
    hpV2 hpV (bifunctor_comp_eq_of_heq _ (eq_of_heq hQK) (eq_of_heq hY) (eq_of_heq hQF)
      (eq_of_heq hQG) (eq_of_heq hPF) (eq_of_heq hPG) (eq_of_heq hPK) (eq_of_heq hX) hc hd hmM hmN
      hmMN ha hb h)

end Abstract

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of Stacks 03EL for the Zariski morphism of the small étale site of the scheme
underlying `U`, at the two spellings `U.left.obj` and `(BigFppfOver.toScheme B S hS).obj U` of
that scheme. -/
theorem heq_pullbackTensorIsoTransport_toZariski (U : BigFppfOver B S hS)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    HEq (Stacks.SheafOfModules.pullbackTensorIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B) U.left.obj U.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
          (associatedBigEtaleSite B) U.left.obj U.left.property) M.obj N.obj)
      (Stacks.SheafOfModules.pullbackTensorIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        M.obj N.obj) :=
  HEq.rfl

/-- The comparison of Stacks 03EL for the small étale base change along the scheme morphism
underlying `g`, read on the modules attached to `M` and `N` at the two spellings of the scheme
underlying `U`. -/
theorem heq_pullbackTensorIsoTransport_baseChange {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    HEq (Stacks.SheafOfModules.pullbackTensorIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.baseChangeRingedToposModulesHom
          (associatedBigEtaleSite B) g.left)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesBaseChangeIso
          (associatedBigEtaleSite B) g.left)
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          U.left.obj U.left.property).obj M.obj)
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          U.left.obj U.left.property).obj N.obj))
      (Stacks.SheafOfModules.pullbackTensorIsoTransport
        (representedSchemeBaseChangeHom B S hS g)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesBaseChangeIso
          (associatedBigEtaleSite B) g.left)
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M.obj)
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj N.obj)) :=
  HEq.rfl

/-- The comparison `g^*(M ⊗ N) ≅ g^*M ⊗ g^*N` of Stacks 01CD read on the small étale site of the
scheme underlying `V`, at the two spellings of the scheme morphism underlying `g`. -/
theorem heq_associatedModule_map_pullbackTensorIso {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    HEq ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          V.left.obj V.left.property).map
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)
          M.obj N.obj).hom)
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
        (quasicoherentPullbackTensorIso B S hS g M N).hom.hom) :=
  heq_map_of_heq rfl rfl rfl ((heq_hom_of_heq rfl rfl HEq.rfl).trans (heq_of_eq rfl))

/-- The comparison of Stacks 03EL for the Zariski morphism of the small étale site of the scheme
underlying `V`, read on `g^*M` and `g^*N`, at the two spellings of that scheme and of `g^*`. -/
theorem heq_pullbackTensorIsoTransport_toZariski_pullback {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    HEq (Stacks.SheafOfModules.pullbackTensorIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B) V.left.obj V.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
          (associatedBigEtaleSite B) V.left.obj V.left.property)
        ((Stacks.RingedSpace.pullbackFunctor (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)))).obj
          M.obj)
        ((Stacks.RingedSpace.pullbackFunctor (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)))).obj
          N.obj))
      (Stacks.SheafOfModules.pullbackTensorIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
        (quasicoherentPullbackObj B S hS g M).obj (quasicoherentPullbackObj B S hS g N).obj) :=
  HEq.rfl

/-- `Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality` for the reindexing of Stacks
04M0 of `V`. -/
theorem pullbackTensorIsoTransport_representedReindex_hom_naturality (V : BigFppfOver B S hS)
    {M M' N N' : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS V)} (a : M ⟶ M')
    (b : N ⟶ N') :
    type_of% (Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality
      (representedReindexHom B S hS V) (representedReindexPullbackIso B S hS V) a b) :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality
    (representedReindexHom B S hS V) (representedReindexPullbackIso B S hS V) a b

/-- The statement of `tensorCompat_of_readings_of_heq` with the comparison of the two
factorizations of the square of `g` and Stacks 03EL round that square supplied. -/
theorem representedC3TensorCompat_reduction_square {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (tensorCompat_of_readings_of_heq _ _ _ _ _ _ (representedSquareMate B S hS g)
      (isIso_representedSquareMate B S hS g) _ _ _ _ _ _ _ _
      (representedSquare_pullbackTensorIsoTransport_representedSquareMate B S hS g
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M.obj)
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj N.obj))) :=
  tensorCompat_of_readings_of_heq _ _ _ _ _ _ (representedSquareMate B S hS g)
      (isIso_representedSquareMate B S hS g) _ _ _ _ _ _ _ _
      (representedSquare_pullbackTensorIsoTransport_representedSquareMate B S hS g
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M.obj)
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj N.obj))

/-- The statement of `representedC3TensorCompat_reduction_square` with the identification
`g^*(M^a) ≅ (g^*M)^a` on the small étale site supplied. -/
theorem representedC3TensorCompat_reduction_readingLeft {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_square B S hS g M N ((Scheme.Modules.pullback
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) ⋙
        _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B) V.left.obj
        V.left.property).obj M.obj) _ _
        (representedSquareMate_app_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS g M))
        :=
  representedC3TensorCompat_reduction_square B S hS g M N ((Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) ⋙
      _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B) V.left.obj
      V.left.property).obj M.obj) _ _
      (representedSquareMate_app_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS g M)

/-- The statement of `representedC3TensorCompat_reduction_readingLeft` with the identification
`g^*(N^a) ≅ (g^*N)^a` on the small étale site supplied. -/
theorem representedC3TensorCompat_reduction_readingRight {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_readingLeft B S hS g M N ((Scheme.Modules.pullback
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) ⋙
        _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B) V.left.obj
        V.left.property).obj N.obj) _ _
        (representedSquareMate_app_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS g N))
        :=
  representedC3TensorCompat_reduction_readingLeft B S hS g M N ((Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) ⋙
      _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B) V.left.obj
      V.left.property).obj N.obj) _ _
      (representedSquareMate_app_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS g N)

/-- The statement of `representedC3TensorCompat_reduction_readingRight` with the identification
`g^*((M ⊗ N)^a) ≅ (g^*(M ⊗ N))^a` on the small étale site supplied. -/
theorem representedC3TensorCompat_reduction_readingTensor {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_readingRight B S hS g M N _
        ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) g.left) ⋙ _root_.AlgebraicGeometry.SmallEtale.associatedModule
        (associatedBigEtaleSite B) V.left.obj V.left.property).obj (quasicoherentTensorObj B S hS U
        M N).obj) _ _ (representedSquareMate_app_comp_modulePullbackRepresentedQuasicoherentIso_hom
        B S hS g (quasicoherentTensorObj B S hS U M N))) :=
  representedC3TensorCompat_reduction_readingRight B S hS g M N _ ((Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) ⋙
      _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B) V.left.obj
      V.left.property).obj (quasicoherentTensorObj B S hS U M N).obj) _ _
      (representedSquareMate_app_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS g
      (quasicoherentTensorObj B S hS U M N))

/-- The statement of `representedC3TensorCompat_reduction_readingTensor` with the naturality of
Stacks 03EL for the reindexing of `V` supplied. -/
theorem representedC3TensorCompat_reduction_naturality {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_readingTensor B S hS g M N _ _ _ _ _ _
        (pullbackTensorIsoTransport_representedReindex_hom_naturality B S hS V
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso (associatedBigEtaleSite
        B) g.left).inv.app M.obj)
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso (associatedBigEtaleSite
        B) g.left).inv.app N.obj))) :=
  representedC3TensorCompat_reduction_readingTensor B S hS g M N _ _ _ _ _ _
      (pullbackTensorIsoTransport_representedReindex_hom_naturality B S hS V
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso (associatedBigEtaleSite B)
      g.left).inv.app M.obj) ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
      (associatedBigEtaleSite B) g.left).inv.app N.obj))

/-- The statement of `representedC3TensorCompat_reduction_naturality` with the naturality of Stacks
03EL linked to the square of `g`. -/
theorem representedC3TensorCompat_reduction_naturality_heq {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_naturality B S hS g M N rfl rfl HEq.rfl HEq.rfl
        (heq_hom_of_heq rfl rfl HEq.rfl)) :=
  representedC3TensorCompat_reduction_naturality B S hS g M N rfl rfl HEq.rfl HEq.rfl
      (heq_hom_of_heq rfl rfl HEq.rfl)

/-- The statement of `representedC3TensorCompat_reduction_naturality_heq` with Stacks 03EL round
the square of the scheme morphism underlying `g` supplied. -/
theorem representedC3TensorCompat_reduction_zariskiSquare {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_naturality_heq B S hS g M N _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.zariskiSquare_pullbackTensorIso
        (associatedBigEtaleSite B) g.left M.obj N.obj)) :=
  representedC3TensorCompat_reduction_naturality_heq B S hS g M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.zariskiSquare_pullbackTensorIso
      (associatedBigEtaleSite B) g.left M.obj N.obj)

/-- The statement of `representedC3TensorCompat_reduction_zariskiSquare` with the comparison of the
two routes round the square of schemes identified with Stacks 03LC (1). -/
theorem representedC3TensorCompat_reduction_zariskiSquare_comparison {V U : BigFppfOver B S hS}
    (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_zariskiSquare B S hS g M N _
        (_root_.AlgebraicGeometry.SmallEtale.factorizationTransportIso_zariskiSquare
        (associatedBigEtaleSite B) g.left)) :=
  representedC3TensorCompat_reduction_zariskiSquare B S hS g M N _
      (_root_.AlgebraicGeometry.SmallEtale.factorizationTransportIso_zariskiSquare
      (associatedBigEtaleSite B) g.left)

/-- The statement of `representedC3TensorCompat_reduction_zariskiSquare_comparison` with the
categories and objects of the square of schemes identified with those of the compatibility. -/
theorem representedC3TensorCompat_reduction_zariskiSquare_objects {V U : BigFppfOver B S hS}
    (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_zariskiSquare_comparison B S hS g M N rfl HEq.rfl
        HEq.rfl (quasicoherentTensorObj B S hS U M N).obj rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
        HEq.rfl HEq.rfl HEq.rfl) :=
  representedC3TensorCompat_reduction_zariskiSquare_comparison B S hS g M N rfl HEq.rfl HEq.rfl
      (quasicoherentTensorObj B S hS U M N).obj rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl

/-- The statement of `representedC3TensorCompat_reduction_zariskiSquare_objects` with the morphisms
on `U` of the square of schemes identified with those of the compatibility. -/
theorem representedC3TensorCompat_reduction_zariskiSquare_heqU {V U : BigFppfOver B S hS}
    (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_zariskiSquare_objects B S hS g M N _
        (heq_map_of_heq_of_heq rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
        (heq_hom_of_heq_of_heq rfl HEq.rfl HEq.rfl HEq.rfl (heq_pullbackTensorIsoTransport_toZariski
        B S hS U M N))) (heq_hom_of_heq_of_heq rfl HEq.rfl HEq.rfl HEq.rfl
        (heq_pullbackTensorIsoTransport_baseChange B S hS g M N))) :=
  representedC3TensorCompat_reduction_zariskiSquare_objects B S hS g M N _ (heq_map_of_heq_of_heq
      rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl (heq_hom_of_heq_of_heq rfl HEq.rfl HEq.rfl
      HEq.rfl (heq_pullbackTensorIsoTransport_toZariski B S hS U M N))) (heq_hom_of_heq_of_heq rfl
      HEq.rfl HEq.rfl HEq.rfl (heq_pullbackTensorIsoTransport_baseChange B S hS g M N))

/-- The statement of `representedC3TensorCompat_reduction_zariskiSquare_heqU` with the components
of Stacks 03LC (1) identified with those of the identifications `g^*(M^a) ≅ (g^*M)^a`. -/
theorem representedC3TensorCompat_reduction_zariskiSquare_heqReading {V U : BigFppfOver B S hS}
    (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_zariskiSquare_heqU B S hS g M N HEq.rfl HEq.rfl
        HEq.rfl) :=
  representedC3TensorCompat_reduction_zariskiSquare_heqU B S hS g M N HEq.rfl HEq.rfl HEq.rfl

/-- The statement of `representedC3TensorCompat_reduction_zariskiSquare_heqReading` with the
morphisms on `V` of the square of schemes identified with those of the compatibility. -/
theorem representedC3TensorCompat_reduction_zariskiSquare_heqV {V U : BigFppfOver B S hS}
    (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_zariskiSquare_heqReading B S hS g M N _ _ _
        (heq_associatedModule_map_pullbackTensorIso B S hS g M N) (heq_hom_of_heq_of_heq rfl HEq.rfl
        HEq.rfl HEq.rfl (heq_pullbackTensorIsoTransport_toZariski_pullback B S hS g M N)) HEq.rfl)
        :=
  representedC3TensorCompat_reduction_zariskiSquare_heqReading B S hS g M N _ _ _
      (heq_associatedModule_map_pullbackTensorIso B S hS g M N) (heq_hom_of_heq_of_heq rfl HEq.rfl
      HEq.rfl HEq.rfl (heq_pullbackTensorIsoTransport_toZariski_pullback B S hS g M N)) HEq.rfl

/-- The statement of `representedC3TensorCompat_reduction_zariskiSquare_heqV` with the
identification `(M ⊗ N)_{yoneda U} ≅ M_{yoneda U} ⊗ N_{yoneda U}` written out. -/
theorem representedC3TensorCompat_reduction_tensorIsoU {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_zariskiSquare_heqV B S hS g M N _ _ _ _
        (representedQuasicoherentSchemeTensorIso_eq B S hS U M N)) :=
  representedC3TensorCompat_reduction_zariskiSquare_heqV B S hS g M N _ _ _ _
      (representedQuasicoherentSchemeTensorIso_eq B S hS U M N)

/-- The statement of `representedC3TensorCompat_reduction_tensorIsoU` with Stacks 03EL for the
morphism of algebraic spaces written out. -/
theorem representedC3TensorCompat_reduction_pullbackTensorIso {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_tensorIsoU B S hS g M N _ (modulesTensorObjIso B S
        hS _ _
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj)
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj))
    _ _ rfl (pullbackTensorIsoTransport_pullbackModulesReindexIso_hom B S hS U _ _)
    (pullbackTensorIsoTransport_refl_hom_space B S hS _ _ _)) :=
  representedC3TensorCompat_reduction_tensorIsoU B S hS g M N _ (modulesTensorObjIso B S hS _ _
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj)
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj))
    _ _ rfl (pullbackTensorIsoTransport_pullbackModulesReindexIso_hom B S hS U _ _)
    (pullbackTensorIsoTransport_refl_hom_space B S hS _ _ _)

/-- The statement of `representedC3TensorCompat_reduction_pullbackTensorIso` with the tensor
product of the identifications `g^*(M^a) ≅ (g^*M)^a` and `g^*(N^a) ≅ (g^*N)^a` written out. -/
theorem representedC3TensorCompat_reduction_tensorHom {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_pullbackTensorIso B S hS g M N _ _ _
        (modulesTensorObjIso_hom_naturality B S hS _ _)) :=
  representedC3TensorCompat_reduction_pullbackTensorIso B S hS g M N _ _ _
      (modulesTensorObjIso_hom_naturality B S hS _ _)

/-- The statement of `representedC3TensorCompat_reduction_tensorHom` with Stacks 03EL for the
scheme morphism underlying `g`, read on the small étale site of `V`, written out. -/
theorem representedC3TensorCompat_reduction_pullbackTensorIsoReading {V U : BigFppfOver B S hS}
    (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_tensorHom B S hS g M N _
        (representedQuasicoherentSchemeEquivalence_functor_map_hom B S hS V
        (quasicoherentPullbackTensorIso B S hS g M N).hom)) :=
  representedC3TensorCompat_reduction_tensorHom B S hS g M N _
      (representedQuasicoherentSchemeEquivalence_functor_map_hom B S hS V
      (quasicoherentPullbackTensorIso B S hS g M N).hom)

/-- The statement of `representedC3TensorCompat_reduction_pullbackTensorIsoReading` with the
identification `(g^*M ⊗ g^*N)_{yoneda V} ≅ (g^*M)_{yoneda V} ⊗ (g^*N)_{yoneda V}` written out. -/
theorem representedC3TensorCompat_reduction_tensorIsoV {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    type_of% (representedC3TensorCompat_reduction_pullbackTensorIsoReading B S hS g M N _
        (pullbackTensorIsoTransport_pullbackModulesReindexIso_hom B S hS V _ _) _
        (representedQuasicoherentSchemeTensorIso_eq B S hS V _ _)) :=
  representedC3TensorCompat_reduction_pullbackTensorIsoReading B S hS g M N _
      (pullbackTensorIsoTransport_pullbackModulesReindexIso_hom B S hS V _ _) _
      (representedQuasicoherentSchemeTensorIso_eq B S hS V _ _)

/-- The identification of Stacks 03DX (2) of the module attached to a tensor product is compatible
with inverse images: for a morphism `g : V ⟶ U` of the big fppf site and quasi-coherent modules
`M`, `N` on the scheme underlying `U`, the two identifications
`g^*((M ⊗ N)_{yoneda U}) ≅ (g^*M)_{yoneda V} ⊗ (g^*N)_{yoneda V}` of
`AlgebraicGeometry.Space.RepresentedC3TensorCompat` agree. -/
theorem representedC3TensorCompat {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    RepresentedC3TensorCompat B S hS g M N :=
  representedC3TensorCompat_reduction_tensorIsoV B S hS g M N

end AlgebraicGeometry.Space

end
