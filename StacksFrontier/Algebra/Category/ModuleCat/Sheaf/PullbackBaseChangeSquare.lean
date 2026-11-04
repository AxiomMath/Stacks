module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeSheafification

/-!
# A morphism of two pullbacks of sheaves of modules is the sheafified objectwise base change

Let `φ : S ⟶ R` and `φ' : S ⟶ R'` be morphisms of sheaves of rings over a continuous functor
of sites, let `α : R₀ ⟶ R` and `α' : R₀' ⟶ R'` be locally bijective morphisms of presheaves of
rings, and let `ν : S ⟶ R₀`, `δ : S ⟶ R₀'` lift `φ` and `φ'`. Suppose `ρ : R₀ ⟶ R₀'` satisfies
`ν ≫ ρ = δ`.

Then a morphism `ℓ` from the pullback of `𝒢` along `φ`, pushed forward, to the pullback along
`φ'`, pushed forward, which carries the unit of the first pullback adjunction to the unit of the
second and which is `ρ`-semilinear, becomes, on the underlying abelian sheaves and through
`Stacks.SheafOfModules.pullbackCompToSheafIso`, the sheafification of the objectwise base change
`Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo`.

## Main results

* `Stacks.SheafOfModules.unit_comp_map_sheafificationHomEquiv_comp`: the unit of extension of
  scalars along `ν`, followed by the comparison with the pullback and by `ℓ`, is the unit of
  extension of scalars along `δ` followed by the comparison with the pullback along `φ'`.
* `Stacks.SheafOfModules.toSheaf_map_comp_baseChangeTo`: a morphism of the underlying abelian
  sheaves of two pullbacks which respects the units and is `ρ`-semilinear is the sheafification
  of the objectwise base change.
* `Stacks.SheafOfModules.toSheaf_map_comp_baseChangeTo_of_pushforward`: the same for a morphism
  of sheaves of `R`-modules into a pushforward along `ψ` which respects the units.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ u v₂ u₂ v₃ u₃

namespace CategoryTheory

/-- If `f = g ≫ eqToHom h`, then `g = f ≫ eqToHom h.symm`. -/
lemma eq_comp_eqToHom_symm {D : Type u₂} [Category.{v₂} D] {X Y Z : D} {f : X ⟶ Z} {g : X ⟶ Y}
    (h : Y = Z) (hfg : f = g ≫ eqToHom h) : g = f ≫ eqToHom h.symm := by
  subst h
  simpa using hfg.symm

/-- The image under `Φ` of `eqToHom h`, followed by an `eqToHom`, is an `eqToHom`. -/
lemma Functor.map_eqToHom_comp_eqToHom_eq {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
    [Category.{v₃} E] (Φ : D ⥤ E) {X Y : D} (h : X = Y) {Z : E} (h' : Φ.obj Y = Z)
    (h'' : Φ.obj X = Z) :
    Φ.map (eqToHom h) ≫ eqToHom h' = eqToHom h'' := by
  subst h
  rw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]

/-- An `eqToHom` followed by the image under `Φ` of `eqToHom h'` is an `eqToHom`. -/
lemma Functor.eqToHom_comp_map_eqToHom_eq {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
    [Category.{v₃} E] (Φ : D ⥤ E) {W : E} {X Y : D} (h : W = Φ.obj X) (h' : X = Y)
    (h'' : W = Φ.obj Y) :
    eqToHom h ≫ Φ.map (eqToHom h') = eqToHom h'' := by
  subst h'
  rw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]

end CategoryTheory

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {F : C ⥤ C} [Functor.IsContinuous F J J]
  {S R R' : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J J).obj R)
  [(PresheafOfModules.pushforward.{u} φ.hom).IsRightAdjoint]
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  (ν : S.obj ⟶ R₀)
  (hres : (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α) ⋙
      PresheafOfModules.restrictScalars.{u} ν =
    (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
      PresheafOfModules.pushforward.{u} φ.hom)
  (φ' : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J J).obj R')
  [(PresheafOfModules.pushforward.{u} φ'.hom).IsRightAdjoint]
  {R₀' : Cᵒᵖ ⥤ RingCat.{u}} (α' : R₀' ⟶ R'.obj)
  [Presheaf.IsLocallyInjective J α'] [Presheaf.IsLocallySurjective J α']
  (δ : S.obj ⟶ R₀')
  (hres' : (_root_.SheafOfModules.forget R' ⋙ PresheafOfModules.restrictScalars α') ⋙
      PresheafOfModules.restrictScalars.{u} δ =
    (_root_.SheafOfModules.forget R' ⋙ PresheafOfModules.restrictScalars (𝟙 R'.obj)) ⋙
      PresheafOfModules.pushforward.{u} φ'.hom)
  (ρ : R₀ ⟶ R₀') (hδ : ν ≫ ρ = δ) (G : _root_.SheafOfModules.{u} S)

/-- **The abelian sheaf underlying the pullback of `𝒢` along `φ`, read at the single object
`𝒢`**: it is the sheafification of the abelian presheaf of `V ↦ R₀(V) ⊗_{S(V)} 𝒢(V)`, with that
presheaf spelled `Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj`. -/
noncomputable def pullbackObjToSheafIso :
    (_root_.SheafOfModules.toSheaf R).obj ((_root_.SheafOfModules.pullback.{u} φ).obj G) ≅
      (presheafToSheaf J AddCommGrpCat.{u}).obj
        ((PresheafOfModules.toPresheaf S.obj).obj
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj ν G.val)) :=
  (pullbackCompToSheafIso φ α ν hres).app G

section Given

variable (ℓ : (_root_.SheafOfModules.pushforward.{u} φ).obj
      ((_root_.SheafOfModules.pullback.{u} φ).obj G) ⟶
    (_root_.SheafOfModules.pushforward.{u} φ').obj
      ((_root_.SheafOfModules.pullback.{u} φ').obj G))
  (hℓ : (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G ≫ ℓ =
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ').unit.app G)
  (g : (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).obj
      ((_root_.SheafOfModules.pullback.{u} φ).obj G) ⟶
    (PresheafOfModules.restrictScalars ρ).obj
      ((_root_.SheafOfModules.forget R' ⋙ PresheafOfModules.restrictScalars α').obj
        ((_root_.SheafOfModules.pullback.{u} φ').obj G)))
  (hlin : eqToHom (Functor.congr_obj hres
        ((_root_.SheafOfModules.pullback.{u} φ).obj G)).symm ≫
      (PresheafOfModules.restrictScalars ν).map g =
    (_root_.SheafOfModules.forget S).map ℓ ≫
      eqToHom ((Functor.congr_obj hres'
          ((_root_.SheafOfModules.pullback.{u} φ').obj G)).symm.trans
        (congrArg (fun f ↦ (PresheafOfModules.restrictScalars f).obj
          ((_root_.SheafOfModules.forget R' ⋙ PresheafOfModules.restrictScalars α').obj
            ((_root_.SheafOfModules.pullback.{u} φ').obj G))) hδ.symm)))

include hres hres' hδ hℓ hlin

/-- The unit of extension of scalars along `ν`, followed by the comparison with the pullback and
by `ℓ`, is the unit of extension of scalars along `δ` followed by the comparison with the pullback
along `φ'`. -/
theorem unit_comp_map_sheafificationHomEquiv_comp :
    (Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} ν).unit.app G.val ≫
        (PresheafOfModules.restrictScalars ν).map
          (PresheafOfModules.sheafificationHomEquiv α
            ((pullbackIsoExtendScalars φ α ν hres).inv.app G) ≫ g) =
      ((Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} δ).unit.app G.val ≫
          (PresheafOfModules.restrictScalars δ).map
            (PresheafOfModules.sheafificationHomEquiv α'
              ((pullbackIsoExtendScalars φ' α' δ hres').inv.app G))) ≫
        eqToHom (congrArg (fun f ↦ (PresheafOfModules.restrictScalars f).obj
          ((_root_.SheafOfModules.forget R' ⋙
            PresheafOfModules.restrictScalars α').obj
              ((_root_.SheafOfModules.pullback.{u} φ').obj G))) hδ.symm) := by
  have s0 := eq_comp_eqToHom_symm _
    (forget_map_pullbackPushforwardAdjunction_unit_app φ α ν hres G)
  have hA2' := forget_map_pullbackPushforwardAdjunction_unit_app φ' α' δ hres' G
  have hstep : (_root_.SheafOfModules.forget S).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G) ≫
      (_root_.SheafOfModules.forget S).map ℓ =
    (_root_.SheafOfModules.forget S).map
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ').unit.app G) :=
    (CategoryTheory.Functor.map_comp (_root_.SheafOfModules.forget S) _ ℓ).symm.trans
      (congrArg (_root_.SheafOfModules.forget S).map hℓ)
  refine Eq.trans (congrArg (fun q ↦
      (Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} ν).unit.app G.val ≫ q)
    (CategoryTheory.Functor.map_comp (PresheafOfModules.restrictScalars ν) _ g)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun q ↦ q ≫ (PresheafOfModules.restrictScalars ν).map g) s0) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun q ↦ (_root_.SheafOfModules.forget S).map
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G) ≫ q) hlin) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun q ↦ q ≫ _) hstep) ?_
  refine Eq.trans (congrArg (fun q ↦ q ≫ _) hA2') ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun q ↦
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} δ).unit.app G.val ≫
      (PresheafOfModules.restrictScalars δ).map
        (PresheafOfModules.sheafificationHomEquiv α'
          ((pullbackIsoExtendScalars φ' α' δ hres').inv.app G))) ≫ q) (eqToHom_trans _ _)

variable (m : (_root_.SheafOfModules.toSheaf R).obj
    ((_root_.SheafOfModules.pullback.{u} φ).obj G) ⟶
  (_root_.SheafOfModules.toSheaf R').obj ((_root_.SheafOfModules.pullback.{u} φ').obj G))
  (hm : (PresheafOfModules.toPresheaf R₀).map g = m.hom)

include hm

/-- **A morphism of the underlying abelian sheaves of two pullbacks of `𝒢` which respects the
units and is `ρ`-semilinear is the sheafification of the objectwise base change.** -/
theorem toSheaf_map_comp_baseChangeTo :
    m ≫ (_root_.SheafOfModules.toSheaf R').map
        ((pullbackIsoExtendScalars φ' α' δ hres').app G).hom =
      (_root_.SheafOfModules.toSheaf R).map ((pullbackIsoExtendScalars φ α ν hres).app G).hom ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf S.obj).map
            (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo ν ρ G.val δ hδ)) :=
  toSheaf_comp_baseChangeTo α α' ν ρ G.val δ hδ _ _
    ((pullbackIsoExtendScalars φ α ν hres).app G)
    ((pullbackIsoExtendScalars φ' α' δ hres').app G) m g hm
    (unit_comp_map_sheafificationHomEquiv_comp φ α ν hres φ' α' δ hres' ρ hδ G ℓ hℓ g hlin)

end Given

section Pushforward

variable (ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J J).obj R')
  (hψres : (_root_.SheafOfModules.forget R' ⋙ PresheafOfModules.restrictScalars α') ⋙
      PresheafOfModules.restrictScalars.{u} ρ =
    ((_root_.SheafOfModules.forget R' ⋙ PresheafOfModules.restrictScalars (𝟙 R'.obj)) ⋙
        PresheafOfModules.pushforward.{u} ψ.hom) ⋙ PresheafOfModules.restrictScalars α)
  (hpush : _root_.SheafOfModules.pushforward.{u} ψ ⋙ _root_.SheafOfModules.pushforward.{u} φ =
    _root_.SheafOfModules.pushforward.{u} φ')
  (htoSheaf : _root_.SheafOfModules.pushforward.{u} ψ ⋙ _root_.SheafOfModules.toSheaf R =
    _root_.SheafOfModules.toSheaf R')
  (t : (_root_.SheafOfModules.pullback.{u} φ).obj G ⟶
    (_root_.SheafOfModules.pushforward.{u} ψ).obj
      ((_root_.SheafOfModules.pullback.{u} φ').obj G))
  (hunit : (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app G ≫
      ((_root_.SheafOfModules.pushforward.{u} φ).map t ≫
        eqToHom (Functor.congr_obj hpush ((_root_.SheafOfModules.pullback.{u} φ').obj G))) =
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ').unit.app G)

include hres hres' hδ hψres hpush htoSheaf hunit

/-- **A morphism of sheaves of `R`-modules from the pullback of `𝒢` along `φ` to the pushforward
along `ψ` of its pullback along `φ'`, which respects the units, becomes the sheafification of the
objectwise base change.** -/
theorem toSheaf_map_comp_baseChangeTo_of_pushforward :
    ((_root_.SheafOfModules.toSheaf R).map t ≫
          eqToHom (Functor.congr_obj htoSheaf
            ((_root_.SheafOfModules.pullback.{u} φ').obj G))) ≫
        (_root_.SheafOfModules.toSheaf R').map
          ((pullbackIsoExtendScalars φ' α' δ hres').app G).hom =
      (_root_.SheafOfModules.toSheaf R).map
          ((pullbackIsoExtendScalars φ α ν hres).app G).hom ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf S.obj).map
            (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo ν ρ G.val δ hδ)) := by
  have hbig := (Functor.congr_obj hres.symm
      ((_root_.SheafOfModules.pushforward.{u} ψ).obj
        ((_root_.SheafOfModules.pullback.{u} φ').obj G))).trans
    (congrArg (PresheafOfModules.restrictScalars ν).obj
      (Functor.congr_obj hψres ((_root_.SheafOfModules.pullback.{u} φ').obj G)).symm)
  have hcore : eqToHom (Functor.congr_obj hres.symm
          ((_root_.SheafOfModules.pushforward.{u} ψ).obj
            ((_root_.SheafOfModules.pullback.{u} φ').obj G))) ≫
        (PresheafOfModules.restrictScalars ν).map (eqToHom (Functor.congr_obj hψres
          ((_root_.SheafOfModules.pullback.{u} φ').obj G)).symm) =
      (_root_.SheafOfModules.forget S).map (eqToHom (Functor.congr_obj hpush
          ((_root_.SheafOfModules.pullback.{u} φ').obj G))) ≫
        eqToHom ((Functor.congr_obj hres'
            ((_root_.SheafOfModules.pullback.{u} φ').obj G)).symm.trans
          (congrArg (fun f ↦ (PresheafOfModules.restrictScalars f).obj
            ((_root_.SheafOfModules.forget R' ⋙ PresheafOfModules.restrictScalars α').obj
              ((_root_.SheafOfModules.pullback.{u} φ').obj G))) hδ.symm)) :=
    (CategoryTheory.Functor.eqToHom_comp_map_eqToHom_eq
        (PresheafOfModules.restrictScalars ν) _ _ hbig).trans
      (CategoryTheory.Functor.map_eqToHom_comp_eqToHom_eq (_root_.SheafOfModules.forget S)
        (Functor.congr_obj hpush ((_root_.SheafOfModules.pullback.{u} φ').obj G))
        _ hbig).symm
  refine toSheaf_map_comp_baseChangeTo φ α ν hres φ' α' δ hres' ρ hδ G
    ((_root_.SheafOfModules.pushforward.{u} φ).map t ≫
      eqToHom (Functor.congr_obj hpush ((_root_.SheafOfModules.pullback.{u} φ').obj G)))
    hunit
    ((_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).map t ≫
      eqToHom (Functor.congr_obj hψres ((_root_.SheafOfModules.pullback.{u} φ').obj G)).symm)
    ?_ _ ?_
  · conv_rhs => rw [CategoryTheory.Functor.map_comp, Category.assoc, ← hcore]
    refine Eq.trans (congrArg (fun q ↦ eqToHom (Functor.congr_obj hres
        ((_root_.SheafOfModules.pullback.{u} φ).obj G)).symm ≫ q)
      (CategoryTheory.Functor.map_comp (PresheafOfModules.restrictScalars ν) _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun q ↦ q ≫ (PresheafOfModules.restrictScalars ν).map
        (eqToHom (Functor.congr_obj hψres
          ((_root_.SheafOfModules.pullback.{u} φ').obj G)).symm))
      (Functor.eqToHom_comp_map hres.symm t)) ?_
    exact Category.assoc _ _ _
  · refine Eq.trans (CategoryTheory.Functor.map_comp
      (PresheafOfModules.toPresheaf R₀) _ _) ?_
    refine Eq.trans (congrArg (fun q ↦ (PresheafOfModules.toPresheaf R₀).map
        ((_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).map t) ≫ q)
      (eqToHom_map (PresheafOfModules.toPresheaf R₀) _)) ?_
    refine Eq.trans ?_ (congrArg (fun q ↦ ((_root_.SheafOfModules.toSheaf R).map t).hom ≫ q)
      (eqToHom_map (sheafToPresheaf J AddCommGrpCat.{u})
        (Functor.congr_obj htoSheaf ((_root_.SheafOfModules.pullback.{u} φ').obj G)))).symm
    rfl

/-- `Stacks.SheafOfModules.toSheaf_map_comp_baseChangeTo_of_pushforward` with the two
comparisons spelled as `Stacks.SheafOfModules.pullbackCompToSheafIso`, so that both sides of the
square land in the sheafification of an abelian presheaf. -/
theorem pullbackCompToSheafIso_comp_baseChangeTo_of_pushforward :
    ((_root_.SheafOfModules.toSheaf R).map t ≫
          eqToHom (Functor.congr_obj htoSheaf
            ((_root_.SheafOfModules.pullback.{u} φ').obj G))) ≫
        (pullbackCompToSheafIso φ' α' δ hres').hom.app G =
      (pullbackCompToSheafIso φ α ν hres).hom.app G ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf S.obj).map
            (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo ν ρ G.val δ hδ)) := by
  rw [pullbackCompToSheafIso_hom_app, pullbackCompToSheafIso_hom_app]
  exact toSheaf_map_comp_baseChangeTo_of_pushforward φ α ν hres φ' α' δ hres' ρ hδ G ψ hψres
    hpush htoSheaf t hunit

/-- `Stacks.SheafOfModules.pullbackCompToSheafIso_comp_baseChangeTo_of_pushforward` with both
comparisons read at `𝒢` through `Stacks.SheafOfModules.pullbackObjToSheafIso`, so that both
sides of the square land in the sheafification of
`Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj`. -/
theorem pullbackObjToSheafIso_comp_baseChangeTo_of_pushforward :
    ((_root_.SheafOfModules.toSheaf R).map t ≫
          eqToHom (Functor.congr_obj htoSheaf
            ((_root_.SheafOfModules.pullback.{u} φ').obj G))) ≫
        (pullbackObjToSheafIso φ' α' δ hres' G).hom =
      (pullbackObjToSheafIso φ α ν hres G).hom ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf S.obj).map
            (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo ν ρ G.val δ hδ)) :=
  pullbackCompToSheafIso_comp_baseChangeTo_of_pushforward φ α ν hres φ' α' δ hres' ρ hδ G ψ
    hψres hpush htoSheaf t hunit

end Pushforward

end Stacks.SheafOfModules

end
