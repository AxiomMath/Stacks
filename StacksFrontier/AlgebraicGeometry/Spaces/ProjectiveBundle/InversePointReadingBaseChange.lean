module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.ConormalSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceTensorPointPaste

/-!
# Base change of the inverse-line factor of the conormal source at scheme points

Let `q : ℰ ⟶ ℒ` be an invertible quotient on an algebraic space `X`, `x : T ⟶ X` a scheme point
and `h : T' ⟶ T` a morphism of test objects.  The inverse-line factor
`i_x : R_T(x^*(ℒ^{⊗ -1})) ≅ R_T(x^*ℒ)^{⊗ -1}` of the conormal source read at `x` is
characterised by its evaluation.  Since a map into a tensor inverse is determined by its
evaluation, `i_x` and `i_{x ∘ h}` are intertwined by the identification of the point readings and
the inverse-line base change of Stacks 0B3V as soon as that identification is monoidal at
`(ℒ^{⊗ -1}, ℒ)` and compatible with the identifications of the structure sheaves.

## Main results

* `CategoryTheory.Functor.bifunctor_baseChange_inverse_of_objects`: the base change of a tensor
  inverse is forced by the evaluation, stated at objects.
* `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso_hom_naturality`: naturality of the
  identification of the point readings.
* `AlgebraicGeometry.Space.inversePointReadingIso_baseChange_of_squares`: the inverse-line square,
  given the tensor and unit squares.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u w

namespace Stacks.SheafOfModules.Invertible

attribute [local implicit_reducible] TensorSheafification.structureSheaf
  TensorSheafification.sheafify Tensor.sheafTensor

section Uniqueness

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Maps into a module are determined by their tensor product with an invertible module
followed by an isomorphism**: tensoring on the right by an invertible module is faithful. -/
theorem map_app_injective_of_comp_iso
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible O hO L)
    {M N U : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO)}
    (ev : ((Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj L ≅ U)
    (α β : M ⟶ N)
    (hαβ : ((Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map α).app L ≫
        ev.hom = ((Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map β).app L ≫
        ev.hom) : α = β :=
  have := hL
  ((Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).map_injective ((Iso.cancel_iso_hom_right _ _ ev).mp hαβ)

end Uniqueness

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (Q : InvertibleQuotient X E)

/-- **The base change of a tensor inverse is forced by the evaluation**
(`CategoryTheory.Functor.bifunctor_baseChange_inverse`), with the readings `ρ`, `ρ'` replaced by
their values at the four objects involved, and their values at the trivialisation `e` by
isomorphisms `r`, `r'`. -/
theorem _root_.CategoryTheory.Functor.bifunctor_baseChange_inverse_of_objects {𝒞₀ 𝒞₁ : Type*}
    [i₀ : Category 𝒞₀] [i₁ : Category 𝒞₁] (F₀ : 𝒞₀ ⥤ 𝒞₀ ⥤ 𝒞₀) (F₁ : 𝒞₁ ⥤ 𝒞₁ ⥤ 𝒞₁)
    (P : 𝒞₀ ⥤ 𝒞₁) {AΛ AL AΛL AU : 𝒞₀} {A'Λ A'L A'ΛL A'U : 𝒞₁} {Λ₀ : 𝒞₀} {Λ₁ : 𝒞₁}
    {U₀ : 𝒞₀} {U₁ : 𝒞₁}
    (cΛ : A'Λ ⟶ P.obj AΛ) (cL : A'L ≅ P.obj AL) (cΛL : A'ΛL ⟶ P.obj AΛL) (cU : A'U ⟶ P.obj AU)
    (μ : AΛL ≅ (F₀.obj AΛ).obj AL) (μ' : A'ΛL ≅ (F₁.obj A'Λ).obj A'L)
    (κ : ∀ X Y : 𝒞₀, P.obj ((F₀.obj X).obj Y) ⟶ (F₁.obj (P.obj X)).obj (P.obj Y))
    (hκ : ∀ {X X' Y Y' : 𝒞₀} (f : X ⟶ X') (g : Y ⟶ Y'),
      P.map ((F₀.map f).app Y ≫ (F₀.obj X').map g) ≫ κ X' Y' =
        κ X Y ≫ ((F₁.map (P.map f)).app (P.obj Y) ≫ (F₁.obj (P.obj X')).map (P.map g)))
    (hT : cΛL ≫ P.map μ.hom ≫ κ AΛ AL =
      μ'.hom ≫ ((F₁.map cΛ).app A'L ≫ (F₁.obj (P.obj AΛ)).map cL.hom))
    (r : AΛL ≅ AU) (r' : A'ΛL ≅ A'U) (hc : r'.hom ≫ cU = cΛL ≫ P.map r.hom)
    (u : AU ≅ U₀) (u' : A'U ≅ U₁) (ν : P.obj U₀ ⟶ U₁)
    (hU : cU ≫ P.map u.hom ≫ ν = u'.hom)
    (i : AΛ ⟶ Λ₀) (b : P.obj Λ₀ ⟶ Λ₁) (i' : A'Λ ⟶ Λ₁)
    (ev₀ : (F₀.obj Λ₀).obj AL ≅ U₀) (ev₁ : (F₁.obj Λ₁).obj A'L ≅ U₁)
    (hi₀ : (F₀.map i).app AL ≫ ev₀.hom = μ.inv ≫ r.hom ≫ u.hom)
    (hi₁ : (F₁.map i').app A'L ≫ ev₁.hom = μ'.inv ≫ r'.hom ≫ u'.hom)
    (hb : κ Λ₀ AL ≫ ((F₁.map b).app (P.obj AL) ≫ (F₁.obj Λ₁).map cL.inv) ≫ ev₁.hom =
      P.map ev₀.hom ≫ ν)
    (huniq : ∀ α β : A'Λ ⟶ Λ₁,
      (F₁.map α).app A'L ≫ ev₁.hom = (F₁.map β).app A'L ≫ ev₁.hom → α = β) :
    cΛ ≫ P.map i ≫ b = i' := by
  refine huniq _ _ ?_
  rw [hi₁]
  have hsplit : (F₁.map (cΛ ≫ P.map i ≫ b)).app A'L =
      ((F₁.map cΛ).app A'L ≫ (F₁.obj (P.obj AΛ)).map cL.hom) ≫
        ((F₁.map (P.map i)).app (P.obj AL) ≫ (F₁.obj (P.obj Λ₀)).map (P.map (𝟙 _))) ≫
        ((F₁.map b).app (P.obj AL) ≫ (F₁.obj Λ₁).map cL.inv) := by
    rw [CategoryTheory.Functor.bifunctor_map_app_comp_obj_map,
      CategoryTheory.Functor.bifunctor_map_app_comp_obj_map]
    simp
  have hP : P.map (μ.hom ≫ (F₀.map i).app AL ≫ ev₀.hom) = P.map r.hom ≫ P.map u.hom := by
    rw [hi₀, Iso.hom_inv_id_assoc, P.map_comp]
  rw [hsplit]
  have h1 := hκ i (𝟙 AL)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h1
  calc _ = μ'.inv ≫ (cΛL ≫ P.map μ.hom ≫ κ AΛ AL) ≫
        ((F₁.map (P.map i)).app (P.obj AL) ≫
          (F₁.obj (P.obj Λ₀)).map (P.map (𝟙 _))) ≫
        ((F₁.map b).app (P.obj AL) ≫ (F₁.obj Λ₁).map cL.inv) ≫ ev₁.hom := by
          rw [hT]; simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = μ'.inv ≫ cΛL ≫ P.map (μ.hom ≫ (F₀.map i).app AL ≫ ev₀.hom) ≫ ν := by
          simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
          simp only [Category.assoc] at hb
          rw [← reassoc_of% h1, hb]
          simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = μ'.inv ≫ r'.hom ≫ u'.hom := by
          rw [hP, ← hU, Category.assoc, reassoc_of% hc]

/-- An evaluation `(i ⊗ 1) ≫ ev = z⁻¹ ≫ R(t⁻¹ ≫ G(s) ≫ m) ≫ w` between isomorphisms, read on
forward maps with `R ∘ G` applied to `s`. -/
theorem _root_.CategoryTheory.Functor.mapIso_app_trans_hom_eq {𝒜 𝒜' ℬ : Type*} [Category 𝒜]
    [Category 𝒜'] [Category ℬ] (F : ℬ ⥤ ℬ ⥤ ℬ) (G : 𝒜 ⥤ 𝒜') (R : 𝒜' ⥤ ℬ) {A U : 𝒜}
    {Y W : 𝒜'} {X₀ Λ₀ Lo V : ℬ} (i : X₀ ≅ Λ₀) (ev : (F.obj Λ₀).obj Lo ≅ V) (t : G.obj A ≅ Y)
    (z : R.obj Y ≅ (F.obj X₀).obj Lo) (s : A ≅ U) (m : G.obj U ≅ W) (w : R.obj W ≅ V)
    (h : (F.mapIso i).app Lo ≪≫ ev = z.symm ≪≫ R.mapIso (t.symm ≪≫ G.mapIso s ≪≫ m) ≪≫ w) :
    (F.map i.hom).app Lo ≫ ev.hom =
      (R.mapIso t ≪≫ z).inv ≫ ((G ⋙ R).mapIso s).hom ≫ (R.mapIso m ≪≫ w).hom := by
  have h' := congrArg Iso.hom h
  simp only [Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom] at h'
  rw [h']
  simp [CategoryTheory.Functor.map_comp]

/-- Removing identities in disguise from an evaluation: if `r, q, r', q'` are identities and
`tp = tp'`, then `Ps ≫ r ≫ q ≫ ν = κ ≫ tp ≫ s' ≫ r' ≫ q'` gives `κ ≫ tp' ≫ s' = Ps ≫ ν`. -/
theorem _root_.CategoryTheory.comp_eq_of_comp_id_eq {𝒟 : Type*} {_ : Category 𝒟}
    {A B C U PU : 𝒟} (κ : A ⟶ B) (tp tp' : B ⟶ C) (s' : C ⟶ U) (Ps : A ⟶ PU)
    (ν : PU ⟶ U) (Pr Pq : PU ⟶ PU) (r' q' : U ⟶ U) (hPr : Pr = 𝟙 PU) (hPq : Pq = 𝟙 PU)
    (hr' : r' = 𝟙 U) (hq' : q' = 𝟙 U) (htp : tp = tp')
    (h0 : Ps ≫ Pr ≫ Pq ≫ ν = κ ≫ tp ≫ s' ≫ r' ≫ q') :
    κ ≫ tp' ≫ s' = Ps ≫ ν := by
  subst hPr hPq hr' hq' htp
  simpa using h0.symm

/-- **Naturality of the identification of the Zariski readings of the two pullbacks**
`(x'^*ℳ)_Zar ≅ τ^*(x^*ℳ)_Zar` in the quasi-coherent module `ℳ`. -/
theorem pointZariskiModuleBaseChangeIso_hom_naturality {T T' : BigFppfOver B S hS}
    (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) {M N : SheafOfModules.{u} (structureRingSheaf B S hS X)}
    (e : M ≅ N) (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    ((modulePullback B S hS (pointHom (yoneda.map h ≫ x)) ⋙ zariskiReadingFunctor T').mapIso e).hom
        ≫
        (pointZariskiModuleBaseChangeIso X N hN x h).hom =
      (pointZariskiModuleBaseChangeIso X M hM x h).hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          ((modulePullback B S hS (pointHom x) ⋙ zariskiReadingFunctor T).mapIso e).hom := by
  have k := map_comp_map_inv_app_comp_inv_eq (modulePullback B S hS (pointHom x)) rfl
    (modulePullback B S hS (pointHom (yoneda.map h ≫ x))) rfl
    (modulePullbackCompIso B S hS
      (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T) (pointHom x))
    (zariskiReadingPullbackHom h) e.hom
    (isIso_zariskiReadingPullbackHom_app h _ (isQuasicoherentOnSite_pointPullback X M hM T x))
    (isIso_zariskiReadingPullbackHom_app h _ (isQuasicoherentOnSite_pointPullback X N hN T x))
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at k
  exact k

/-- The unit square `c_𝒪 ≫ P(u) ≫ ν = u'` of
`CategoryTheory.Functor.bifunctor_baseChange_inverse_of_objects`, as a proposition. -/
abbrev _root_.CategoryTheory.Functor.BaseChangeUnitSquare {𝒞₀ 𝒞₁ : Type*} [i₀ : Category 𝒞₀]
    [i₁ : Category 𝒞₁] (P : 𝒞₀ ⥤ 𝒞₁) {AU : 𝒞₀} {A'U : 𝒞₁} {U₀ : 𝒞₀} {U₁ : 𝒞₁}
    (cU : A'U ⟶ P.obj AU) (u : AU ≅ U₀) (u' : A'U ≅ U₁) (ν : P.obj U₀ ⟶ U₁) : Prop :=
  cU ≫ P.map u.hom ≫ ν = u'.hom

/-- The monoidality square `c_{Λ ⊗ L} ≫ P(μ) ≫ κ = μ' ≫ (c_Λ ⊗ c_L)` of
`CategoryTheory.Functor.bifunctor_baseChange_inverse_of_objects`, as a proposition. -/
abbrev _root_.CategoryTheory.Functor.BaseChangeTensorSquare {𝒞₀ 𝒞₁ : Type*} [i₀ : Category 𝒞₀]
    [i₁ : Category 𝒞₁] (F₀ : 𝒞₀ ⥤ 𝒞₀ ⥤ 𝒞₀) (F₁ : 𝒞₁ ⥤ 𝒞₁ ⥤ 𝒞₁) (P : 𝒞₀ ⥤ 𝒞₁)
    {AΛ AL AΛL : 𝒞₀} {A'Λ A'L A'ΛL : 𝒞₁}
    (cΛ : A'Λ ⟶ P.obj AΛ) (cL : A'L ≅ P.obj AL) (cΛL : A'ΛL ⟶ P.obj AΛL)
    (μ : AΛL ≅ (F₀.obj AΛ).obj AL) (μ' : A'ΛL ≅ (F₁.obj A'Λ).obj A'L)
    (κ : ∀ X Y : 𝒞₀, P.obj ((F₀.obj X).obj Y) ⟶ (F₁.obj (P.obj X)).obj (P.obj Y)) : Prop :=
  cΛL ≫ P.map μ.hom ≫ κ AΛ AL =
    μ'.hom ≫ ((F₁.map cΛ).app A'L ≫ (F₁.obj (P.obj AΛ)).map cL.hom)

/-- **The inverse-line factors of the conormal source at `x` and at `x ∘ h` are intertwined**
by the identification of the point readings and the inverse-line base change
`Stacks.Divisors.inverseQuotientBaseChange` of Stacks 0B3V, given the monoidality of the
identification of the point readings at `(ℒ^{⊗ -1}, ℒ)` and its compatibility with the
identifications of the structure sheaves. -/
theorem inversePointReadingIso_baseChange_of_squares
    [hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L]
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T)
    (hTh : CategoryTheory.Functor.BaseChangeTensorSquare (𝒞₀ := ((BigFppfOver.toScheme B S hS).obj
        T).Modules) (𝒞₁ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
        (i₀ := Scheme.Modules.instCategory) (i₁ := Scheme.Modules.instCategory)
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
        (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
        (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
        (pointZariskiModuleBaseChangeIso X (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)) x h).hom
        (sectionPointQuotientBaseChangeL X E hE Q x h) (pointZariskiModuleBaseChangeIso X _
        (SheafOfModules.IsQuasicoherentOnSite.of_iso
        (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1)).symm
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L _)) x h).hom ((zariskiReadingFunctor
        T).mapIso (modulePullbackTensorComparison (pointHom x) Q.L
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))) ≪≫ zariskiReadingTensorIso T _ _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))
        (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T) _
        (isInvertible_modulePullback_obj B S hS (pointHom x) Q.L hQ))) ((zariskiReadingFunctor
        T').mapIso (modulePullbackTensorComparison (pointHom (yoneda.map h ≫ x)) Q.L
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))) ≪≫ zariskiReadingTensorIso T' _ _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (pointHom (yoneda.map h ≫ x)) _ (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))
        (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T') _
        (isInvertible_modulePullback_obj B S hS (pointHom (yoneda.map h ≫ x)) Q.L hQ)))
        (fun X Y => (Stacks.RingedSpace.comparisonBifunctorIso ((BigFppfOver.toScheme B S hS).map
        h).toLRSHom.toShHom).hom.app (X, Y)))
    (hUh : CategoryTheory.Functor.BaseChangeUnitSquare (𝒞₀ := ((BigFppfOver.toScheme B S hS).obj
        T).Modules) (𝒞₁ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
        (i₀ := Scheme.Modules.instCategory) (i₁ := Scheme.Modules.instCategory)
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
        (pointZariskiModuleBaseChangeIso X _ (isQuasicoherentOnSite_invertibleTensorPower X Q.L 0) x
        h).hom ((zariskiReadingFunctor T).mapIso (modulePullbackUnitIso B S hS (pointHom x)) ≪≫
        zariskiReadingUnitIso T) ((zariskiReadingFunctor T').mapIso (modulePullbackUnitIso B S hS
        (pointHom (yoneda.map h ≫ x))) ≪≫ zariskiReadingUnitIso T')
        (_root_.SheafOfModules.pullbackObjUnitToUnit (RingedSpaceModuleAdjunction.structureSheafHom
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom))) :
    (pointZariskiModuleBaseChangeIso X (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)) x h).hom ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        (inversePointReadingIso X T x Q.L).hom ≫
      (Stacks.Divisors.inverseQuotientBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (sectionPointQuotient X E hE Q T x)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)).hom =
      (inversePointReadingIso X T' (yoneda.map h ≫ x) Q.L).hom := by
  have inv := fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) =>
    isInvertible_zariskiReading T ((modulePullback B S hS (pointHom x)).obj Q.L)
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
        (isInvertible_modulePullback_obj B S hS (pointHom x) Q.L hQ))
  have := inv T x
  have := inv T' (yoneda.map h ≫ x)
  refine CategoryTheory.Functor.bifunctor_baseChange_inverse_of_objects
      (𝒞₀ := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (𝒞₁ := ((BigFppfOver.toScheme B S hS).obj T').Modules) (i₀ := Scheme.Modules.instCategory)
      (i₁ := Scheme.Modules.instCategory)
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
        (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
        (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
    (pointZariskiModuleBaseChangeIso X (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)) x h).hom
        (sectionPointQuotientBaseChangeL X E hE Q x h) (pointZariskiModuleBaseChangeIso X _
        (SheafOfModules.IsQuasicoherentOnSite.of_iso
        (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1)).symm
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L _)) x h).hom
        (pointZariskiModuleBaseChangeIso X _ (isQuasicoherentOnSite_invertibleTensorPower X Q.L 0) x
        h).hom ((zariskiReadingFunctor T).mapIso (modulePullbackTensorComparison (pointHom x) Q.L
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))) ≪≫ zariskiReadingTensorIso T _ _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))
        (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T) _
        (isInvertible_modulePullback_obj B S hS (pointHom x) Q.L hQ))) ((zariskiReadingFunctor
        T').mapIso (modulePullbackTensorComparison (pointHom (yoneda.map h ≫ x)) Q.L
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))) ≪≫ zariskiReadingTensorIso T' _ _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (pointHom (yoneda.map h ≫ x)) _ (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))
        (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T') _
        (isInvertible_modulePullback_obj B S hS (pointHom (yoneda.map h ≫ x)) Q.L hQ)))
        (fun X Y => (Stacks.RingedSpace.comparisonBifunctorIso ((BigFppfOver.toScheme B S hS).map
        h).toLRSHom.toShHom).hom.app (X, Y)) ?hk ?hT
    ((modulePullback B S hS (pointHom x) ⋙ zariskiReadingFunctor T).mapIso
        (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))) ((modulePullback B S hS
        (pointHom (yoneda.map h ≫ x)) ⋙ zariskiReadingFunctor T').mapIso
        (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))) ?hc
    ((zariskiReadingFunctor T).mapIso (modulePullbackUnitIso B S hS (pointHom x)) ≪≫
        zariskiReadingUnitIso T) ((zariskiReadingFunctor T').mapIso (modulePullbackUnitIso B S hS
        (pointHom (yoneda.map h ≫ x))) ≪≫ zariskiReadingUnitIso T')
        (_root_.SheafOfModules.pullbackObjUnitToUnit (RingedSpaceModuleAdjunction.structureSheafHom
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom)) ?hU
    (inversePointReadingIso X T x Q.L).hom (Stacks.Divisors.inverseQuotientBaseChange
        ((BigFppfOver.toScheme B S hS).map h) (pointZariskiModule X E T x) (pointZariskiModule X E
        T' (yoneda.map h ≫ x)) (sectionPointQuotient X E hE Q T x) (sectionPointQuotient X E hE Q T'
        (yoneda.map h ≫ x)) (sectionPointQuotientBaseChangeL X E hE Q x h)).hom
        (inversePointReadingIso X T' (yoneda.map h ≫ x) Q.L).hom
        (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso ((BigFppfOver.toScheme B S hS).obj
        T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 ((zariskiReadingFunctor
        T).obj ((modulePullback B S hS (pointHom x)).obj Q.L)) (-1))
        (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso ((BigFppfOver.toScheme B S hS).obj
        T').presheaf ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2 ((zariskiReadingFunctor
        T').obj ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj Q.L)) (-1))
    ?hi ?hi2 ?hb ?hu
  case hk =>
    intro X₁ X₂ Y₁ Y₂ f g
    exact (Stacks.RingedSpace.comparisonBifunctorIso ((BigFppfOver.toScheme B S hS).map
        h).toLRSHom.toShHom).hom.naturality (X := (X₁, Y₁)) (Y := (X₂, Y₂)) (f, g)
  case hT =>
    exact hTh
  case hc =>
    exact pointZariskiModuleBaseChangeIso_hom_naturality X x h _ _ _
  case hU =>
    exact hUh
  case hi =>
    exact CategoryTheory.Functor.mapIso_app_trans_hom_eq _ _ _ _ _ _ _ _ _ _
        (inversePointReadingIso_evaluation X T x Q.L)
  case hi2 =>
    exact CategoryTheory.Functor.mapIso_app_trans_hom_eq _ _ _ _ _ _ _ _ _ _
        (inversePointReadingIso_evaluation X T' (yoneda.map h ≫ x) Q.L)
  case hb =>
    refine CategoryTheory.comp_eq_of_comp_id_eq _ _ _ _ _ _ _ _ _ _ ?_ ?_ rfl rfl ?_
        (Stacks.Divisors.inverseQuotientBaseChange_evaluation ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (sectionPointQuotient X E hE Q T x) (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h))
    · exact (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map_id _
    · exact (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map_id _
    · exact (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ _ _).symm
  case hu =>
    exact fun α β hαβ => Stacks.SheafOfModules.Invertible.map_app_injective_of_comp_iso _ _ _
      (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x)).invertible _ α β hαβ



end AlgebraicGeometry.Space

end
