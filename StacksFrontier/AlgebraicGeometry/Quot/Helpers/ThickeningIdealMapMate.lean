module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ThickeningIdealGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeCompExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIsoComparison

/-!
# The map of pulled-back ideals `λ_g` as the mate of `𝒥₁ ⟶ g_*𝒥₂`

Let `t₁ : U ⟶ U'₁` and `t₂ : U ⟶ U'₂` be affine first order thickenings with ideals
`𝒥₁ ⊂ 𝒪_{U'₁}` and `𝒥₂ ⊂ 𝒪_{U'₂}`, and `g : U'₂ ⟶ U'₁` a morphism under `U`. The structure map
`g^♯` carries `𝒥₁` into `g_*𝒥₂`, which gives the natural map of ideal sheaves
`κ_g : 𝒥₁ ⟶ g_*𝒥₂` (and its adjoint `δ_g : g^*𝒥₁ ⟶ 𝒥₂`). This file shows that the map of
pulled-back ideals `λ_g : t₁^*𝒥₁ ⟶ t₂^*𝒥₂` of `AlgebraicGeometry.Space.thickeningIdealMap`,
built from the map of kernels `J₁ ⟶ J₂` through `t_k^*𝒥_k ≅ J_k^~`, is the mate of `κ_g`:

`λ_g = (t₁^* ≅ t₂^* g^*) ≫ t₂^* δ_g`, and so `λ_g ↦ κ_g ≫ g_*(η) ≫ (g_* t₂_* ≅ t₁_*)`
under `t₁^* ⊣ t₁_*`.

The identity is checked on the generators `ā`, `a ∈ J₁`, of `t₁^*𝒥₁`
(`AlgebraicGeometry.Space.representedThickeningIdealSection_hom_ext`): both sides send `ā` to
`\overline{g^♯ a}`.
On the side of `δ_g` this comes down to the fact that `g^*` carries multiplication by `a` on
`𝒪_{U'₁}` to multiplication by `g^♯ a` on `𝒪_{U'₂}`, read through the base change of associated
modules, and to the compatibility of `𝒪 ≅ f^*𝒪` with the composition law of pullbacks.

These results concern the functoriality, along morphisms of thickenings, of the deformation
theory of `Coh_{X/Y}` (Stacks 08WA).

Statements are in the spelling of the represented spaces
(`AlgebraicGeometry.Space.representedSpaceMap`, `AlgebraicGeometry.Space.affineThickeningIdeal`)
in which the sections `ā` are defined; mixing it with the `schemeSpaceFunctor` spelling inside one
statement is very slow to elaborate.

## Main definitions

* `Deformation.ToposThickening.IdealOfThickening.pullbackIdealMap`: `δ : j^*I₁ ⟶ I₂` for
  thickenings `i₁`, `i₂` and `j` with `j^* ⋙ i₂^* ≅ i₁^*`.
* `AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq`: `f_* ⋙ g_* ≅ k_*` for `f ≫ g = k`.
* `AlgebraicGeometry.Space.thickeningIdealPullbackMap`, `thickeningIdealPushforwardMap`: `δ_g`
  and `κ_g`.

## Main results

* `Deformation.ToposThickening.homEquiv_eq_homEquiv_comp_map_unit_comp_of_eq`: a map which is
  `L ≅ L₁ ⋙ L₂` followed by `L₂ δ` is the mate of the adjoint of `δ`.
* `AlgebraicGeometry.Space.thickeningIdealPushforwardMap_comp_map_incl`: `κ_g` is `g^♯` on `𝒥₁`.
* `AlgebraicGeometry.Space.thickeningIdealMap_eq_pullbackComp`: the pullback form of the mate.
* `AlgebraicGeometry.Space.homEquiv_thickeningIdealMap`: `λ_g` is the mate of `κ_g`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules (pullbackModulesObjUnitIso)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

namespace Deformation.ToposThickening

open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.RingedToposHom (unitStructureMap pullbackUnitStructureMap
  pushforwardModules pullbackAdjPushforwardModules)

universe v u' w v' u'' w' v'' u''' w''

section IdealMapOfComp

variable {X : RingedTopos.{v, u', w}} {Y₁ : RingedTopos.{v', u'', w'}}
  {Y₂ : RingedTopos.{v'', u''', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w'})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y₂.J AddCommGrpCat.{w''}] [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (j : RingedToposHom Y₂ Y₁)
  (hI₁ : IdealOfThickening i₁) (hI₂ : IdealOfThickening i₂)
  (c : j.toModulesHom.pullbackModules ⋙ i₂.toModulesHom.pullbackModules ≅
    i₁.toModulesHom.pullbackModules)

omit [HasWeakSheafify Y₂.J AddCommGrpCat.{w''}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The pullback of the inclusion of the defining ideal of a thickening vanishes. -/
theorem IdealOfThickening.pullbackModules_map_incl_eq_zero :
    (i₁.toModulesHom.pullbackModules).map hI₁.incl = 0 :=
  (pullbackModules_map_eq_zero_iff_comp_unitStructureMap i₁ hI₁.incl).2
    hI₁.incl_comp_unitStructureMap

include c in
/-- For thickenings `i₁ : X ⟶ Y₁`, `i₂ : X ⟶ Y₂` and `j : Y₂ ⟶ Y₁` with `j^* ⋙ i₂^* ≅ i₁^*`, the
composite `j^*I₁ ⟶ j^*𝒪_{Y₁} ⟶ 𝒪_{Y₂}` is killed by the structure map of `i₂`. -/
theorem IdealOfThickening.pullbackModules_map_incl_comp_unitStructureMap_eq_zero :
    ((j.toModulesHom.pullbackModules).map hI₁.incl ≫ pullbackUnitStructureMap j) ≫
      unitStructureMap i₂ = 0 := by
  refine (pullbackModules_map_eq_zero_iff_comp_unitStructureMap i₂ _).1 ?_
  have hn := NatIso.naturality_2 c hI₁.incl
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, ← hn, hI₁.pullbackModules_map_incl_eq_zero]
  simp only [zero_comp, comp_zero]

/-- **The map of defining ideals `δ : j^*I₁ ⟶ I₂`** for thickenings `i₁ : X ⟶ Y₁`,
`i₂ : X ⟶ Y₂` and `j : Y₂ ⟶ Y₁` with `j^* ⋙ i₂^* ≅ i₁^*`: the factorisation through `I₂` of
`j^*I₁ ⟶ j^*𝒪_{Y₁} ⟶ 𝒪_{Y₂}`. It depends on the comparison `c` only through its existence. -/
def IdealOfThickening.pullbackIdealMap : (j.toModulesHom.pullbackModules).obj hI₁.I ⟶ hI₂.I :=
  (hI₂.exists_factor_of_comp_unitStructureMap_eq_zero _
    (IdealOfThickening.pullbackModules_map_incl_comp_unitStructureMap_eq_zero j hI₁ c)).choose

/-- `δ` followed by the inclusion of `I₂` is `j^*` of the inclusion of `I₁` followed by
`j^*𝒪_{Y₁} ⟶ 𝒪_{Y₂}`. -/
theorem IdealOfThickening.pullbackIdealMap_comp_incl :
    IdealOfThickening.pullbackIdealMap j hI₁ hI₂ c ≫ hI₂.incl =
      (j.toModulesHom.pullbackModules).map hI₁.incl ≫ pullbackUnitStructureMap j :=
  (hI₂.exists_factor_of_comp_unitStructureMap_eq_zero _
    (IdealOfThickening.pullbackModules_map_incl_comp_unitStructureMap_eq_zero j hI₁ c)).choose_spec

end IdealMapOfComp

section MateOfComp

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R₁) {L₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁}
  (adj₂ : L₂ ⊣ R₂) {L : C₀ ⥤ C₂} {R : C₂ ⥤ C₀} (adj : L ⊣ R) (e : R₂ ⋙ R₁ ≅ R)

/-- **A map `q : L X ⟶ L₂ Y` which is `L ≅ L₁ ⋙ L₂` followed by `L₂ δ` is the mate of the adjoint
of `δ`**: for the composition law of left adjoints adjoint to `e : R₂ ⋙ R₁ ≅ R`, `q` corresponds
under `L ⊣ R` to `δ^♭ ≫ R₁(η₂) ≫ e`, where `δ^♭ : X ⟶ R₁ Y` is the adjoint of `δ : L₁ X ⟶ Y`. -/
theorem homEquiv_eq_homEquiv_comp_map_unit_comp_of_eq {X : C₀} {Y : C₁} (δ : L₁.obj X ⟶ Y)
    (q : L.obj X ⟶ L₂.obj Y)
    (hq : q = (Adjunction.leftAdjointCompIso adj₁ adj₂ adj e).inv.app X ≫ L₂.map δ) :
    adj.homEquiv X (L₂.obj Y) q =
      adj₁.homEquiv X Y δ ≫ R₁.map (adj₂.unit.app Y) ≫ e.hom.app (L₂.obj Y) := by
  rw [Adjunction.homEquiv_eq_leftAdjointCompIso adj₁ adj₂ adj e q, hq, Iso.hom_inv_id_app_assoc]
  have h₂ : adj₂.homEquiv _ _ (L₂.map δ) = δ ≫ adj₂.unit.app Y := by
    rw [Adjunction.homEquiv_unit]
    exact (adj₂.unit.naturality δ).symm
  rw [h₂, Adjunction.homEquiv_naturality_right, Category.assoc]

end MateOfComp

end Deformation.ToposThickening

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section CompOfEq

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` at the level of the morphisms of ringed topoi is the
comparison of Stacks 03LU in the `RingedToposHom.pushforwardModules` presentation. -/
theorem pushforwardModulesCompAt_eq_modulePushforwardCompIso' (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardModulesCompAt B S hS f g = modulePushforwardCompIso' B S hS f g :=
  congrArg (fun t ↦ (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g)).symm ≪≫ t)
    (pushforwardModulesCompTransport_eq B S hS f g)

/-- **The comparison `f_* ⋙ g_* ≅ k_*` of direct images of modules for `f ≫ g = k`**: Stacks
03LU for the composite (`AlgebraicGeometry.Space.modulePushforwardCompIso'`), followed by the
identification of the direct images along the equal morphisms `f ≫ g` and `k`. -/
def modulePushforwardCompIsoOfEq (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) :
    (smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS g).pushforwardModules ≅
      (smallEtaleRingedToposHom B S hS k).pushforwardModules :=
  modulePushforwardCompIso' B S hS f g ≪≫
    eqToIso (congrArg (fun m ↦ (smallEtaleRingedToposHom B S hS m).pushforwardModules) hk)

/-- **The identification `𝒪 ≅ k^*𝒪` is compatible with the composition law of pullbacks** for
`f ≫ g = k`, the composition law being adjoint to
`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq`. -/
theorem pullbackModulesObjUnitIso_hom_comp_leftAdjointCompIso_modulePushforwardCompIsoOfEq
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) :
    (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS k).toModulesHom).hom =
      (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS f).toModulesHom).hom ≫
        ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).map
          (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS g).toModulesHom).hom ≫
        (Adjunction.leftAdjointCompIso
          (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS g))
          (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f))
          (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS k))
          (modulePushforwardCompIsoOfEq f g k hk)).hom.app _ := by
  subst hk
  have e : modulePushforwardCompIsoOfEq f g (f ≫ g) rfl = pushforwardModulesCompAt B S hS f g := by
    rw [pushforwardModulesCompAt_eq_modulePushforwardCompIso', modulePushforwardCompIsoOfEq,
      eqToIso_refl, Iso.trans_refl]
  rw [e, ← smallEtaleModulePullbackCompIso_eq_leftAdjointCompIso]
  exact pullbackModulesObjUnitIso_hom_comp_smallEtaleModulePullbackCompIso B S hS f g

end CompOfEq

section GenericSmul

/-- The bookkeeping behind
`AlgebraicGeometry.Space.pullbackModulesObjUnitIso_hom_comp_map_tildeSmul_comp_inv`, in arbitrary
categories: if `P : F ⋙ Pb ≅ extendScalars ρ ⋙ F'` is normalized at the ring through
`ε : oD ≅ Pb oC`, `u : F R ≅ oC` and `u' : F' R' ≅ oD`, then `Pb` carries multiplication by `y`
on `oC` to multiplication by `ρ y` on `oD`. -/
theorem generic_map_smul_conj {R R' : Type u} [CommRing R] [CommRing R'] (ρ : R →+* R')
    {C D : Type*} [Category* C] [Category* D]
    (F : ModuleCat.{u} R ⥤ C) (F' : ModuleCat.{u} R' ⥤ D) (Pb : C ⥤ D)
    (P : F ⋙ Pb ≅ ModuleCat.extendScalars ρ ⋙ F') {oC : C} {oD : D}
    (ε : oD ≅ Pb.obj oC) (u : F.obj (ModuleCat.of R R) ≅ oC) (u' : F'.obj (ModuleCat.of R' R') ≅ oD)
    (hP : P.hom.app (ModuleCat.of R R) ≫ F'.map (ModuleCat.ExtendScalars.objSelfIso ρ).hom =
      Pb.map u.hom ≫ ε.inv ≫ u'.inv) (y : R) :
    ε.hom ≫ Pb.map (u.inv ≫ F.map (y • 𝟙 (ModuleCat.of R R)) ≫ u.hom) ≫ ε.inv =
      u'.inv ≫ F'.map (ρ y • 𝟙 (ModuleCat.of R' R')) ≫ u'.hom := by
  have hQ : Pb.map u.hom ≫ ε.inv =
      P.hom.app (ModuleCat.of R R) ≫ F'.map
          (ModuleCat.ExtendScalars.objSelfIso ρ).hom ≫ u'.hom := by
    rw [reassoc_of% hP, Iso.inv_hom_id, Category.comp_id]
  have hn := P.hom.naturality (y • 𝟙 (ModuleCat.of R R))
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hQ, reassoc_of% hn, ← F'.map_comp_assoc,
    ModuleCat.ExtendScalars.map_smul_id_comp_objSelfIso_hom, F'.map_comp_assoc, reassoc_of% hP]
  simp only [Iso.map_inv_hom_id_assoc, Iso.hom_inv_id_assoc]

end GenericSmul

section GenericKey

/-- The bookkeeping behind
`Space.pullbackModulesObjUnitIso_hom_comp_map_generator_comp_thickeningIdealPullbackMap`, in
arbitrary categories: a map `m₁` into a subobject `I₁ ⊂ O₁`, pulled back along `P`, read through
`ε : O₂ ≅ P O₁` and followed by a map `δ : P I₁ ⟶ I₂` into a subobject `I₂ ⊂ O₂` compatible with
the inclusions, is the map `m₂` with the conjugated composite into `O₂`. -/
theorem generic_unitIso_comp_map_comp_eq {C D : Type*} [Category* C] [Category* D] (P : C ⥤ D)
    {O₁ I₁ : C} {O₂ I₂ : D} (ε : O₂ ≅ P.obj O₁) (m₁ : O₁ ⟶ I₁) (incl₁ : I₁ ⟶ O₁) (x₁ : O₁ ⟶ O₁)
    (δ : P.obj I₁ ⟶ I₂) (incl₂ : I₂ ⟶ O₂) (m₂ : O₂ ⟶ I₂) (x₂ : O₂ ⟶ O₂) (ν : P.obj O₁ ⟶ O₂)
    (hc : ∀ {f f' : O₂ ⟶ I₂}, f ≫ incl₂ = f' ≫ incl₂ → f = f')
    (hδ : δ ≫ incl₂ = P.map incl₁ ≫ ν) (hν : ν = ε.inv) (e₁ : m₁ ≫ incl₁ = x₁)
    (hs : ε.hom ≫ P.map x₁ ≫ ε.inv = x₂) (e₂ : m₂ ≫ incl₂ = x₂) :
    ε.hom ≫ P.map m₁ ≫ δ = m₂ :=
  hc (by rw [Category.assoc, Category.assoc, hδ, ← P.map_comp_assoc, e₁, hν, hs, e₂])

/-- The bookkeeping behind
`AlgebraicGeometry.Space.representedThickeningIdealSection_comp_thickeningIdealPullbackMap`, in
arbitrary categories: a section `u ≅ F₁ O₁ ⟶ F₁ I₁` carried along a composition law
`Pγ ⋙ F₂ ≅ F₁` compatible with the trivializations `U₁`, `U₂`, `Uγ`, and then along `F₂ δ`. -/
theorem generic_unitIso_comp_map_comp_compIso_inv {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂]
    [Category* D] (Pγ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ D) (F₁ : C₁ ⥤ D) (Cmp : Pγ ⋙ F₂ ≅ F₁) {u : D}
    {O₁ I₁ : C₁} {O₂ I₂ : C₂} (U₁ : u ≅ F₁.obj O₁) (U₂ : u ≅ F₂.obj O₂) (Uγ : O₂ ≅ Pγ.obj O₁)
    (hu : U₁.hom = U₂.hom ≫ F₂.map Uγ.hom ≫ Cmp.hom.app O₁) (m₁ : O₁ ⟶ I₁)
    (δ : Pγ.obj I₁ ⟶ I₂) (m₂ : O₂ ⟶ I₂) (h : Uγ.hom ≫ Pγ.map m₁ ≫ δ = m₂) :
    (U₁.hom ≫ F₁.map m₁) ≫ Cmp.inv.app I₁ ≫ F₂.map δ = U₂.hom ≫ F₂.map m₂ := by
  have hn := Cmp.inv.naturality m₁
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, reassoc_of% hn, hu]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← F₂.map_comp, ← F₂.map_comp, h]

/-- Testing `P₁⁻¹ ≫ λ ≫ P₂` on a section `s₁`: if `λ` carries `s₁ ≫ P₁⁻¹` to `s₂ ≫ P₂⁻¹` and `X`
carries `s₁` to `s₂`, then the two agree on `s₁`. -/
theorem generic_comp_inv_comp_comp_hom_eq {C : Type*} [Category* C] {u A₁ A₂ B₁ B₂ : C}
    (s₁ : u ⟶ B₁) (P₁ : A₁ ≅ B₁) (P₂ : A₂ ≅ B₂) (lam : A₁ ⟶ A₂) (s₂ : u ⟶ B₂) {X : B₁ ⟶ B₂}
    (T : (s₁ ≫ P₁.inv) ≫ lam = s₂ ≫ P₂.inv) (K : s₁ ≫ X = s₂) :
    s₁ ≫ P₁.inv ≫ lam ≫ P₂.hom = s₁ ≫ X := by
  rw [reassoc_of% T, Iso.inv_hom_id, Category.comp_id, K]

end GenericKey

/-- The factorisation `t₁ = t₂ ≫ g` of the represented spaces, as an equality of morphisms. -/
private theorem representedSpaceMap_comp_eq {U U'₁ U'₂ : BigFppfOver B S hS} (h₁ : U ⟶ U'₁)
    (h₂ : U ⟶ U'₂) (g : U'₂ ⟶ U'₁) (hg : h₂ ≫ g = h₁) :
    representedSpaceMap B S hS h₂ ≫ representedSpaceMap B S hS g = representedSpaceMap B S hS h₁ :=
  (representedSpaceMap_comp B S hS h₂ g).trans (congrArg (representedSpaceMap B S hS) hg)

section AffineSmul

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)

/-- **The pullback along `g : U' ⟶ U` of multiplication by `y ∈ Γ(U)` on `𝒪_U` is
multiplication by `g^♯ y` on `𝒪_{U'}`**, through `𝒪_{U'} ≅ g^*𝒪_U`, in the spelling of the small
étale ringed topoi. -/
theorem pullbackModulesObjUnitIso_hom_comp_map_tildeSmul_comp_inv
    (y : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (pullbackModulesObjUnitIso
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom).hom ≫
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS g)).toModulesHom.pullbackModules).map
        ((toposAssociatedUnitIso U).inv ≫
          (toposAssociatedFunctor U).map
            (y • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) ≫
          (toposAssociatedUnitIso U).hom) ≫
      (pullbackModulesObjUnitIso
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom).inv =
    (toposAssociatedUnitIso U').inv ≫
      (toposAssociatedFunctor U').map
        ((representedAffineCommRingCatHom B S hS g).hom y •
          𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) ≫
      (toposAssociatedUnitIso U').hom :=
  generic_map_smul_conj (representedAffineCommRingCatHom B S hS g).hom
    (toposAssociatedFunctor U) (toposAssociatedFunctor U')
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom.pullbackModules
    (representedAffineAssociatedPullbackIso B S hS g)
    (pullbackModulesObjUnitIso
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom)
    (toposAssociatedUnitIso U) (toposAssociatedUnitIso U')
    (representedAffineAssociatedPullbackIso_hom_app_self B S hS g) y

end AffineSmul

section ToposGenerator

variable {U U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (h : U ⟶ U')
  (hiso : IsIso (Subfunctor.toRange (representedSpaceMap B S hS h).hom))
  (hfo : IsFirstOrderThickening B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩
    (Subfunctor.range (representedSpaceMap B S hS h).hom))
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h))

/-- `AlgebraicGeometry.Space.representedThickeningIdealGenerator_comp_incl` in the spelling of the
small étale ringed topos of `U'` used by
`AlgebraicGeometry.Space.representedThickeningIdealSection`: the generator of `𝒥` attached to
`a ∈ J` followed by the inclusion is multiplication by `a`. -/
theorem toposThickeningIdealGenerator_comp_incl
    (a : RingHom.ker (representedAffineCommRingCatHom B S hS h).hom) :
    ((toposAssociatedUnitIso U').inv ≫ (toposAssociatedFunctor U').map (homFromSelfOfElement _ a) ≫
        (toposThickeningIdealTildeIso h hiso hfo).inv) ≫ (affineThickeningIdeal h hiso hfo).incl =
      (toposAssociatedUnitIso U').inv ≫
        (toposAssociatedFunctor U').map
          ((a : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) •
            𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) ≫
        (toposAssociatedUnitIso U').hom :=
  representedThickeningIdealGenerator_comp_incl h hiso hfo a

/-- The global section `ā` of `t^*𝒥` is `𝒪_U ≅ t^*𝒪_{U'}` followed by the pullback of the
generator of `𝒥` attached to `a`, in the spelling of the small étale ringed topoi. -/
theorem representedThickeningIdealSection_eq
    (a : RingHom.ker (representedAffineCommRingCatHom B S hS h).hom) :
    representedThickeningIdealSection h hiso hfo a =
      (pullbackModulesObjUnitIso
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).toModulesHom).hom ≫
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h)).toModulesHom.pullbackModules).map
        ((toposAssociatedUnitIso U').inv ≫ (toposAssociatedFunctor U').map
          (homFromSelfOfElement _ a) ≫
          (toposThickeningIdealTildeIso h hiso hfo).inv) :=
  rfl

include hh in
/-- **Maps out of `t^*𝒥` are determined by the global sections `ā`, `a ∈ J`**, in the spelling of
`AlgebraicGeometry.Space.representedThickeningIdealSection`. -/
theorem representedThickeningIdealSection_hom_ext
    {X : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)}
    {φ ψ : ((smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toModulesHom.pullbackModules).obj
        (affineThickeningIdeal h hiso hfo).I ⟶ X}
    (H : ∀ a, representedThickeningIdealSection h hiso hfo a ≫ φ =
      representedThickeningIdealSection h hiso hfo a ≫ ψ) :
    φ = ψ := by
  have : PreservesColimitsOfSize.{u, u} (toposAssociatedFunctor U) :=
    (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  exact hom_ext_of_preservesColimits_sections (toposAssociatedFunctor U) (𝟭 _)
    (representedThickeningIdealTildeIsoAux h hiso hfo hh) (toposAssociatedUnitIso U)
    (representedThickeningIdealSection h hiso hfo)
    (representedThickeningIdealSection_comp_tildeIsoAux_hom h hiso hfo hh) H

end ToposGenerator

section IdealMapMate

variable {U U'₁ U'₂ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₁)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₂)]
  (h₁ : U ⟶ U'₁) (h₂ : U ⟶ U'₂) (g : U'₂ ⟶ U'₁) (hg : h₂ ≫ g = h₁)
  (hiso₁ : IsIso (Subfunctor.toRange ((schemeSpaceFunctor B S hS).map h₁).hom))
  (hfo₁ : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj U'₁)
    (Subfunctor.range ((schemeSpaceFunctor B S hS).map h₁).hom))
  (hiso₂ : IsIso (Subfunctor.toRange ((schemeSpaceFunctor B S hS).map h₂).hom))
  (hfo₂ : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj U'₂)
    (Subfunctor.range ((schemeSpaceFunctor B S hS).map h₂).hom))
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂))

/-- **The map of ideals `δ_g : g^*𝒥₁ ⟶ 𝒥₂`** of a morphism `g : U'₂ ⟶ U'₁` of affine first
order thickenings of `U`: the factorisation through `𝒥₂` of `g^*𝒥₁ ⟶ g^*𝒪_{U'₁} ⟶ 𝒪_{U'₂}`. -/
def thickeningIdealPullbackMap :
    ((smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS g)).toModulesHom.pullbackModules).obj
        (affineThickeningIdeal h₁ hiso₁ hfo₁).I ⟶
      (affineThickeningIdeal h₂ hiso₂ hfo₂).I :=
  Deformation.ToposThickening.IdealOfThickening.pullbackIdealMap
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
    (affineThickeningIdeal h₁ hiso₁ hfo₁)
    (affineThickeningIdeal h₂ hiso₂ hfo₂)
    (Adjunction.leftAdjointCompIso
      (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))
      (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₂)))
      (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₁)))
      (modulePushforwardCompIsoOfEq (representedSpaceMap B S hS h₂)
        (representedSpaceMap B S hS g) (representedSpaceMap B S hS h₁)
        ((representedSpaceMap_comp B S hS h₂ g).trans
          (congrArg (representedSpaceMap B S hS) hg))))

/-- **The natural map of ideal sheaves `κ_g : 𝒥₁ ⟶ g_*𝒥₂`** of a morphism `g : U'₂ ⟶ U'₁` of
affine first order thickenings of `U`, the adjoint of `δ_g`; it is `g^♯` on `𝒥₁`
(`AlgebraicGeometry.Space.thickeningIdealPushforwardMap_comp_map_incl`). -/
def thickeningIdealPushforwardMap :
    (affineThickeningIdeal h₁ hiso₁ hfo₁).I ⟶
      (RingedToposHom.pushforwardModules
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))).obj
        (affineThickeningIdeal h₂ hiso₂ hfo₂).I :=
  (RingedToposHom.pullbackAdjPushforwardModules
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))).homEquiv _ _
    (thickeningIdealPullbackMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₁)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₂)] in
/-- `δ_g` followed by the inclusion of `𝒥₂` is `g^*` of the inclusion of `𝒥₁` followed by
`g^*𝒪_{U'₁} ⟶ 𝒪_{U'₂}`. -/
theorem thickeningIdealPullbackMap_comp_incl :
    thickeningIdealPullbackMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ ≫
        (affineThickeningIdeal h₂ hiso₂ hfo₂).incl =
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS g)).toModulesHom.pullbackModules).map
          (affineThickeningIdeal h₁ hiso₁ hfo₁).incl ≫
        RingedToposHom.pullbackUnitStructureMap
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)) :=
  Deformation.ToposThickening.IdealOfThickening.pullbackIdealMap_comp_incl
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
    (affineThickeningIdeal h₁ hiso₁ hfo₁) (affineThickeningIdeal h₂ hiso₂ hfo₂)
    (Adjunction.leftAdjointCompIso _ _ _
      (modulePushforwardCompIsoOfEq _ _ _ (representedSpaceMap_comp_eq h₁ h₂ g hg)))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₁)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₂)] in
/-- **`κ_g` is `g^♯` on `𝒥₁`**: `κ_g ≫ g_*(𝒥₂ ⟶ 𝒪_{U'₂}) = (𝒥₁ ⟶ 𝒪_{U'₁}) ≫ g^♯`. This
characterizes `κ_g`, `g_*` of the inclusion being a monomorphism. -/
theorem thickeningIdealPushforwardMap_comp_map_incl :
    thickeningIdealPushforwardMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ ≫
        (RingedToposHom.pushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))).map
          (affineThickeningIdeal h₂ hiso₂ hfo₂).incl =
      (affineThickeningIdeal h₁ hiso₁ hfo₁).incl ≫
        RingedToposHom.unitStructureMap
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)) :=
  ((RingedToposHom.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))).homEquiv_naturality_right
      (thickeningIdealPullbackMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂)
      (affineThickeningIdeal h₂ hiso₂ hfo₂).incl).symm.trans
    ((congrArg (fun m ↦ (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))).homEquiv _ _ m)
      (thickeningIdealPullbackMap_comp_incl h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂)).trans
      (RingedToposHom.homEquiv_map_comp_pullbackUnitStructureMap
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
        (affineThickeningIdeal h₁ hiso₁ hfo₁).incl))

/-- **`δ_g` on generators**: through `𝒪_{U'₂} ≅ g^*𝒪_{U'₁}`, the pullback of the generator of
`𝒥₁` attached to `a ∈ J₁` followed by `δ_g` is the generator of `𝒥₂` attached to any `b ∈ J₂`
with `b = g^♯ a`. -/
theorem pullbackModulesObjUnitIso_hom_comp_map_generator_comp_thickeningIdealPullbackMap
    (a : RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map h₁)).hom)
    (b : RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map h₂)).hom)
    (hb : (b : Γ((BigFppfOver.toScheme B S hS).obj U'₂, ⊤)) =
      (representedAffineCommRingCatHom B S hS g).hom
        (a : Γ((BigFppfOver.toScheme B S hS).obj U'₁, ⊤))) :
    (pullbackModulesObjUnitIso
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom).hom ≫
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS g)).toModulesHom.pullbackModules).map
        ((toposAssociatedUnitIso U'₁).inv ≫ (toposAssociatedFunctor U'₁).map
          (homFromSelfOfElement _ a) ≫
          (toposThickeningIdealTildeIso h₁ hiso₁ hfo₁).inv) ≫
      (thickeningIdealPullbackMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂) =
    ((toposAssociatedUnitIso U'₂).inv ≫ (toposAssociatedFunctor U'₂).map
      (homFromSelfOfElement _ b) ≫
          (toposThickeningIdealTildeIso h₂ hiso₂ hfo₂).inv) := by
  have e₂ : ((toposAssociatedUnitIso U'₂).inv ≫
        (toposAssociatedFunctor U'₂).map (homFromSelfOfElement _ b) ≫
          (toposThickeningIdealTildeIso h₂ hiso₂ hfo₂).inv) ≫
        (affineThickeningIdeal h₂ hiso₂ hfo₂).incl =
      ((toposAssociatedUnitIso U'₂).inv ≫
        (toposAssociatedFunctor U'₂).map
          ((representedAffineCommRingCatHom B S hS g).hom
              (a : Γ((BigFppfOver.toScheme B S hS).obj U'₁, ⊤)) •
            𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U'₂, ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj U'₂, ⊤))) ≫
        (toposAssociatedUnitIso U'₂).hom) :=
    (toposThickeningIdealGenerator_comp_incl h₂ hiso₂ hfo₂ b).trans
      (congrArg
        (fun y : Γ((BigFppfOver.toScheme B S hS).obj U'₂, ⊤) ↦ (toposAssociatedUnitIso U'₂).inv ≫
        (toposAssociatedFunctor U'₂).map
          (y • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U'₂, ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj U'₂, ⊤))) ≫
        (toposAssociatedUnitIso U'₂).hom) hb)
  have hδ := thickeningIdealPullbackMap_comp_incl h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂
  have hν := (Iso.hom_comp_eq_id _).1
      (RingedToposHom.pullbackModulesObjUnitIso_hom_comp_pullbackUnitStructureMap
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))
  have e₁ := toposThickeningIdealGenerator_comp_incl h₁ hiso₁ hfo₁ a
  have hs := pullbackModulesObjUnitIso_hom_comp_map_tildeSmul_comp_inv g
    (a : Γ((BigFppfOver.toScheme B S hS).obj U'₁, ⊤))
  have hc : ∀ {f f' : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U'₂, isAlgebraicSpace_yoneda B S hS U'₂⟩).O) ⟶
        (affineThickeningIdeal h₂ hiso₂ hfo₂).I},
      f ≫ (affineThickeningIdeal h₂ hiso₂ hfo₂).incl = f' ≫
          (affineThickeningIdeal h₂ hiso₂ hfo₂).incl →
        f = f' := fun h ↦
    Deformation.ToposThickening.IdealOfThickening.cancel_incl
        (affineThickeningIdeal h₂ hiso₂ hfo₂) h
  exact generic_unitIso_comp_map_comp_eq _ _ _ _ _ _ _ _ _ _ hc hδ hν e₁ hs e₂

/-- **The key identity on generators**: the global section `ā` of `t₁^*𝒥₁`, carried to
`t₂^*g^*𝒥₁` by the composition law of pullbacks and then by `t₂^*δ_g`, is the global section `b̄`
of `t₂^*𝒥₂` for any `b ∈ J₂` with `b = g^♯ a`. -/
theorem representedThickeningIdealSection_comp_thickeningIdealPullbackMap
    (a : RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map h₁)).hom)
    (b : RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map h₂)).hom)
    (hb : (b : Γ((BigFppfOver.toScheme B S hS).obj U'₂, ⊤)) =
      (representedAffineCommRingCatHom B S hS g).hom
        (a : Γ((BigFppfOver.toScheme B S hS).obj U'₁, ⊤))) :
    representedThickeningIdealSection h₁ hiso₁ hfo₁ a ≫
      (Adjunction.leftAdjointCompIso
        (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))
        (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₂)))
        (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₁)))
        (modulePushforwardCompIsoOfEq (representedSpaceMap B S hS h₂)
          (representedSpaceMap B S hS g) (representedSpaceMap B S hS h₁)
          ((representedSpaceMap_comp B S hS h₂ g).trans
          (congrArg (representedSpaceMap B S hS) hg)))).inv.app
        (affineThickeningIdeal h₁ hiso₁ hfo₁).I ≫
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h₂)).toModulesHom.pullbackModules).map
        (thickeningIdealPullbackMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂) =
    representedThickeningIdealSection h₂ hiso₂ hfo₂ b := by
  have hu := pullbackModulesObjUnitIso_hom_comp_leftAdjointCompIso_modulePushforwardCompIsoOfEq
    (representedSpaceMap B S hS h₂) (representedSpaceMap B S hS g) (representedSpaceMap B S hS h₁)
    ((representedSpaceMap_comp B S hS h₂ g).trans (congrArg (representedSpaceMap B S hS) hg))
  have K := generic_unitIso_comp_map_comp_compIso_inv _ _ _ _ _ _ _ hu _ _ _
    (pullbackModulesObjUnitIso_hom_comp_map_generator_comp_thickeningIdealPullbackMap h₁ h₂ g hg
      hiso₁ hfo₁ hiso₂ hfo₂ a b hb)
  exact K

/-- `λ_g` and its pullback form agree on the global section `ā` of `t₁^*𝒥₁`, given the value
`b̄` of `λ_g` on `ā`. -/
theorem representedThickeningIdealSection_comp_thickeningIdealMap_eq
    (a : RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map h₁)).hom)
    (b : RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map h₂)).hom)
    (hb : (b : Γ((BigFppfOver.toScheme B S hS).obj U'₂, ⊤)) =
      (representedAffineCommRingCatHom B S hS g).hom
        (a : Γ((BigFppfOver.toScheme B S hS).obj U'₁, ⊤)))
    (T : (representedThickeningIdealSection h₁ hiso₁ hfo₁ a ≫
      (representedThickeningIdealPullbackSpellingIso h₁ hiso₁ hfo₁).inv) ≫
      thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂ =
    representedThickeningIdealSection h₂ hiso₂ hfo₂ b ≫
      (representedThickeningIdealPullbackSpellingIso h₂ hiso₂ hfo₂).inv) :
    representedThickeningIdealSection h₁ hiso₁ hfo₁ a ≫
      (representedThickeningIdealPullbackSpellingIso h₁ hiso₁ hfo₁).inv ≫
        thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂ ≫
        (representedThickeningIdealPullbackSpellingIso h₂ hiso₂ hfo₂).hom =
    representedThickeningIdealSection h₁ hiso₁ hfo₁ a ≫
      (Adjunction.leftAdjointCompIso
        (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))
        (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₂)))
        (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₁)))
        (modulePushforwardCompIsoOfEq (representedSpaceMap B S hS h₂)
          (representedSpaceMap B S hS g) (representedSpaceMap B S hS h₁)
          ((representedSpaceMap_comp B S hS h₂ g).trans
          (congrArg (representedSpaceMap B S hS) hg)))).inv.app
        (affineThickeningIdeal h₁ hiso₁ hfo₁).I ≫
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h₂)).toModulesHom.pullbackModules).map
        (thickeningIdealPullbackMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂) :=
  generic_comp_inv_comp_comp_hom_eq _ _ _ _ _ T
    (representedThickeningIdealSection_comp_thickeningIdealPullbackMap h₁ h₂ g hg hiso₁ hfo₁
      hiso₂ hfo₂ a b hb)

/-- **`λ_g` in the pullback form of the mate**: read in the pullback spelling of the adjunction
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`, `λ_g : t₁^*𝒥₁ ⟶ t₂^*𝒥₂` is the
composition law `t₁^* ≅ t₂^* g^*` (adjoint to
`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq`) followed by `t₂^*δ_g`. -/
theorem thickeningIdealMap_eq_pullbackComp :
    ((representedThickeningIdealPullbackSpellingIso h₁ hiso₁ hfo₁).inv ≫
        thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂ ≫
        (representedThickeningIdealPullbackSpellingIso h₂ hiso₂ hfo₂).hom) =
      (Adjunction.leftAdjointCompIso
        (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))
        (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₂)))
        (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₁)))
        (modulePushforwardCompIsoOfEq (representedSpaceMap B S hS h₂)
          (representedSpaceMap B S hS g) (representedSpaceMap B S hS h₁)
          ((representedSpaceMap_comp B S hS h₂ g).trans
          (congrArg (representedSpaceMap B S hS) hg)))).inv.app
        (affineThickeningIdeal h₁ hiso₁ hfo₁).I ≫
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h₂)).toModulesHom.pullbackModules).map
        (thickeningIdealPullbackMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂) := by
  refine representedThickeningIdealSection_hom_ext h₁ hiso₁ hfo₁ hh₁ (fun a ↦ ?_)
  exact representedThickeningIdealSection_comp_thickeningIdealMap_eq h₁ h₂ g hg hiso₁ hfo₁ hiso₂
      hfo₂
    hh₁ hh₂ a ((thickeningKerMapOf h₁ h₂ g hg hh₁ hh₂).hom a)
    (thickeningKerMap_apply hh₁ hh₂ ((BigFppfOver.toScheme B S hS).map g)
      (toScheme_map_comp_map_eq_of_comp_eq h₁ h₂ g hg) a)
    (thickeningIdealSection_comp_thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂ a)

/-- **`λ_g` is the mate of the natural map of ideal sheaves `κ_g : 𝒥₁ ⟶ g_*𝒥₂`.** Read in the
pullback spelling of the adjunction
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` (through the identifications
`AlgebraicGeometry.Space.representedThickeningIdealPullbackSpellingIso`),
`λ_g : t₁^*𝒥₁ ⟶ t₂^*𝒥₂` corresponds under `t₁^* ⊣ t₁_*` to
`𝒥₁ ⟶ g_*𝒥₂ ⟶ g_*t₂_*t₂^*𝒥₂ ≅ t₁_*t₂^*𝒥₂`, the comparison being
`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq`. -/
theorem homEquiv_thickeningIdealMap :
    (RingedToposHom.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₁))).homEquiv _ _
        ((representedThickeningIdealPullbackSpellingIso h₁ hiso₁ hfo₁).inv ≫
        thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂ ≫
        (representedThickeningIdealPullbackSpellingIso h₂ hiso₂ hfo₂).hom) =
      thickeningIdealPushforwardMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ ≫
        (RingedToposHom.pushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))).map
          ((RingedToposHom.pullbackAdjPushforwardModules
              (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₂))).unit.app
            (affineThickeningIdeal h₂ hiso₂ hfo₂).I) ≫
        (modulePushforwardCompIsoOfEq (representedSpaceMap B S hS h₂)
          (representedSpaceMap B S hS g) (representedSpaceMap B S hS h₁)
          ((representedSpaceMap_comp B S hS h₂ g).trans
          (congrArg (representedSpaceMap B S hS) hg))).hom.app _ :=
  Deformation.ToposThickening.homEquiv_eq_homEquiv_comp_map_unit_comp_of_eq
    (RingedToposHom.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))
    (RingedToposHom.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₂)))
    (RingedToposHom.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h₁)))
    (modulePushforwardCompIsoOfEq (representedSpaceMap B S hS h₂)
      (representedSpaceMap B S hS g) (representedSpaceMap B S hS h₁)
      ((representedSpaceMap_comp B S hS h₂ g).trans
          (congrArg (representedSpaceMap B S hS) hg)))
    (thickeningIdealPullbackMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂) _
    (thickeningIdealMap_eq_pullbackComp h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂)

end IdealMapMate

end AlgebraicGeometry.Space

end
