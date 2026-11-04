module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedSections
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineBaseChange

/-!
# The small étale direct image along a quasi-compact quasi-separated morphism

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site whose underlying morphism of
schemes `r` is quasi-compact and quasi-separated, let `ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` be
the morphism of small étale ringed sites of Stacks 070R (2), and let `𝓕` be a quasi-coherent
`𝒪_X`-module.  This file proves

`(ε_a)_* (𝓕^a) ≅ (r_* 𝓕)^a`,

which is Descent, Lemma 071N in degree zero, and that `(ε_a)_* (𝓕^a)` is quasi-coherent on the
site.  The case of an affine morphism is
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso`.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_isBaseChange`: a restriction map of
  a presheaf of modules which is a base change is cartesian.
* `AlgebraicGeometry.exists_isBaseChange_pullbackSectionsMap`: the restriction map of the
  pullback-sections presheaf of Stacks 03DS along a flat base change of a quasi-compact
  quasi-separated scheme over an affine base is a base change.
* `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_associatedModule_of_isPullback`:
  the same for `𝓕^a` on the small étale site.
* `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_pushforward_of_qcqs`: `(ε_a)_*(𝓕^a)` is
  cartesian between affine objects.
* `AlgebraicGeometry.SmallEtale.isIso_counit_pushforward_of_qcqs` and
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward_associatedModule_of_qcqs`.
* `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIsoOfQcqs`:
  **`(ε_a)_*(𝓕^a) ≅ (r_*𝓕)^a`**.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v₁ u₁ r m

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- **A restriction map which is a base change is cartesian.**  If the restriction map of a
presheaf of modules along `f : X ⟶ Y`, read as a linear map over `R X`, is a base change along
`R X ⟶ R Y`, then the comparison `R Y ⊗_{R X} M X ⟶ M Y` is bijective. -/
theorem bijective_restrictionBaseChange_of_isBaseChange
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat.{r}))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    letI : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
    letI : Module (R.obj X) (M.obj X) := inferInstanceAs
      (Module ((R ⋙ forget₂ CommRingCat RingCat.{r}).obj X) (M.obj X))
    letI : Module (R.obj Y) (M.obj Y) := inferInstanceAs
      (Module ((R ⋙ forget₂ CommRingCat RingCat.{r}).obj Y) (M.obj Y))
    letI : Module (R.obj X) (M.obj Y) := Module.compHom _ (R.map f).hom
    haveI : IsScalarTower (R.obj X) (R.obj Y) (M.obj Y) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∀ (g : M.obj X →ₗ[R.obj X] M.obj Y), (∀ x, g x = M.map f x) →
      IsBaseChange (R.obj Y) g → Function.Bijective (restrictionBaseChange (R := R) M f) := by
  intro g hg h
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let : Module (R.obj X) (M.obj X) := inferInstanceAs
    (Module ((R ⋙ forget₂ CommRingCat RingCat.{r}).obj X) (M.obj X))
  let : Module (R.obj Y) (M.obj Y) := inferInstanceAs
    (Module ((R ⋙ forget₂ CommRingCat RingCat.{r}).obj Y) (M.obj Y))
  let : Module (R.obj X) (M.obj Y) := Module.compHom _ (R.map f).hom
  have : IsScalarTower (R.obj X) (R.obj Y) (M.obj Y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have key : ∀ x, restrictionBaseChange (R := R) M f x = h.equiv x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul s mm =>
      refine (restrictionBaseChange_tmul (R := R) M f s mm).trans ?_
      refine Eq.trans ?_ (h.equiv_tmul (show R.obj Y from s) mm).symm
      exact congrArg (fun z : M.obj Y => (show R.obj Y from s) • z) (hg mm).symm
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  rw [show ⇑(restrictionBaseChange (R := R) M f) = ⇑h.equiv from funext key]
  exact h.equiv.bijective

end Stacks.PresheafOfModules

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.SectionsBaseChange

universe u

/-- **Degree-zero flat base change for the pullback-sections presheaf.**  Let `g : W ⟶ W'` be a
morphism of schemes over `S` whose underlying morphism is the base change of a flat morphism
`q : T ⟶ T'` of affine schemes along `W' ⟶ T'`, with `W'` quasi-compact and quasi-separated, and
let `F` be a quasi-coherent `𝒪_S`-module.  Then the restriction map
`Γ(W', W'⁺F) ⟶ Γ(W, W⁺F)` of the presheaf of Stacks 03DS is a base change along
`Γ(W', 𝒪) ⟶ Γ(W, 𝒪)`. -/
theorem exists_isBaseChange_pullbackSectionsMap {S : Scheme.{u}} (F : S.Modules)
    [F.IsQuasicoherent] {W W' : Over S} (g : W ⟶ W')
    {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] {q : T ⟶ T'} [Flat q]
    {k : W.left ⟶ T} {i : W'.left ⟶ T'} (H : IsPullback g.left k i q)
    [CompactSpace W'.left] [QuasiSeparatedSpace W'.left] :
    letI : Algebra Γ(W'.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    letI : Module Γ(W'.left, ⊤) Γ((Scheme.Modules.pullback W.hom).obj F, ⊤) :=
      Module.compHom _ g.left.appTop.hom
    haveI : IsScalarTower Γ(W'.left, ⊤) Γ(W.left, ⊤)
        Γ((Scheme.Modules.pullback W.hom).obj F, ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∃ ρ : Γ((Scheme.Modules.pullback W'.hom).obj F, ⊤) →ₗ[Γ(W'.left, ⊤)]
        Γ((Scheme.Modules.pullback W.hom).obj F, ⊤),
      (∀ x, ρ x = pullbackSectionsMap F g x) ∧ IsBaseChange Γ(W.left, ⊤) ρ := by
  let G := (Scheme.Modules.pullback W'.hom).obj F
  let p := g.left
  let : Algebra Γ(W'.left, ⊤) Γ(W.left, ⊤) := p.appTop.hom.toAlgebra
  let : Module Γ(W'.left, ⊤) Γ((Scheme.Modules.pullback p).obj G, ⊤) :=
    Module.compHom _ p.appTop.hom
  have : IsScalarTower Γ(W'.left, ⊤) Γ(W.left, ⊤) Γ((Scheme.Modules.pullback p).obj G, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let ρ : Γ(G, ⊤) →ₗ[Γ(W'.left, ⊤)] Γ((Scheme.Modules.pullback p).obj G, ⊤) :=
    { toFun := fun a => pullbackUnitSections p G ⊤ a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => pullbackUnitSections_smul p G ⊤ r a }
  have hρ : IsBaseChange Γ(W.left, ⊤) ρ :=
    isBaseChange_appTop_pullbackSections H G
      (fun r => congrArg (fun φ : Γ(W'.left, ⊤) ⟶ Γ(W.left, ⊤) => φ.hom r)
        (Scheme.Hom.appLE_eq_app p (U := ⊤)).symm)
      ρ (fun a => (pullbackSectionsHom_top p G a).symm)
  let e : Γ((Scheme.Modules.pullback p).obj G, ⊤) ≃ₗ[Γ(W.left, ⊤)]
      Γ((Scheme.Modules.pullback W.hom).obj F, ⊤) :=
    sectionsLinearEquivOfIso (Stacks.Sites.pullbackSectionsComparison F g) ⊤
  let : Module Γ(W'.left, ⊤) Γ((Scheme.Modules.pullback W.hom).obj F, ⊤) :=
    Module.compHom _ p.appTop.hom
  have : IsScalarTower Γ(W'.left, ⊤) Γ(W.left, ⊤)
      Γ((Scheme.Modules.pullback W.hom).obj F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine ⟨(e.restrictScalars Γ(W'.left, ⊤)).toLinearMap ∘ₗ ρ, fun x => ?_, ?_⟩
  · refine Eq.trans ?_ (Stacks.Sites.pullbackSectionsComparison_pullbackSection F g
      (le_preimage_top p ⊤) x)
    exact congrArg e (pullbackSection_eq_pullbackUnitSections p G ⊤ x).symm
  · exact IsBaseChange.of_equiv (hρ.equiv ≪≫ₗ e) fun x => by
      show e (hρ.equiv (1 ⊗ₜ x)) = e (ρ x)
      rw [hρ.equiv_tmul, one_smul]

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

universe u

open Stacks.PresheafOfModules

section Sections

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The pullback-sections sheaf on the small étale site is cartesian along a flat base change
of a quasi-compact quasi-separated object.**  For a morphism `g : W ⟶ W'` of the small étale site
of `S` whose underlying morphism of schemes is the base change of a flat morphism of affine
schemes `T ⟶ T'` along `W' ⟶ T'`, with `W'` quasi-compact and quasi-separated, the comparison
`Γ(W) ⊗_{Γ(W')} 𝓕^a(W') ⟶ 𝓕^a(W)` is bijective for the sections sheaf of a quasi-coherent
`𝓕`. -/
theorem bijective_restrictionBaseChange_sectionsPresheafOfModules_of_isPullback
    (F : S.Modules) [F.IsQuasicoherent] {W W' : SmallEtale B S hS} (g : W ⟶ W')
    {T T' : Scheme.{u}} [AlgebraicGeometry.IsAffine T] [AlgebraicGeometry.IsAffine T']
    {q : T ⟶ T'} [Flat q]
    {k : (toScheme B S hS).obj W ⟶ T} {i : (toScheme B S hS).obj W' ⟶ T'}
    (H : IsPullback ((toScheme B S hS).map g) k i q)
    [CompactSpace ((toScheme B S hS).obj W')]
    [QuasiSeparatedSpace ((toScheme B S hS).obj W')] :
    Function.Bijective (restrictionBaseChange
      (R := commStructurePresheaf B S hS) (sectionsPresheafOfModules B S hS F) g.op) := by
  have : CompactSpace ((toOver B S hS).obj W').left :=
    inferInstanceAs (CompactSpace ((toScheme B S hS).obj W'))
  have : QuasiSeparatedSpace ((toOver B S hS).obj W').left :=
    inferInstanceAs (QuasiSeparatedSpace ((toScheme B S hS).obj W'))
  obtain ⟨ρ, hρ, hbc⟩ := exists_isBaseChange_pullbackSectionsMap F ((toOver B S hS).map g) H
  exact bijective_restrictionBaseChange_of_isBaseChange
    (R := commStructurePresheaf B S hS) (sectionsPresheafOfModules B S hS F) g.op ρ hρ hbc

/-- The associated module `𝓕^a` of a quasi-coherent module on the small étale site is cartesian
along a flat base change of a quasi-compact quasi-separated object. -/
theorem bijective_restrictionBaseChange_associatedModule_of_isPullback
    (F : S.Modules) [F.IsQuasicoherent] {W W' : SmallEtale B S hS} (g : W ⟶ W')
    {T T' : Scheme.{u}} [AlgebraicGeometry.IsAffine T] [AlgebraicGeometry.IsAffine T']
    {q : T ⟶ T'} [Flat q]
    {k : (toScheme B S hS).obj W ⟶ T} {i : (toScheme B S hS).obj W' ⟶ T'}
    (H : IsPullback ((toScheme B S hS).map g) k i q)
    [CompactSpace ((toScheme B S hS).obj W')]
    [QuasiSeparatedSpace ((toScheme B S hS).obj W')] :
    Function.Bijective (restrictionBaseChange
      (R := commStructurePresheaf B S hS) ((associatedModule B S hS).obj F).val g.op) := by
  have : IsIso (restrictionBaseChange (R := commStructurePresheaf B S hS)
      ((SheafOfModules.forget _).obj (associatedSectionsSheaf B S hS F)) g.op) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_restrictionBaseChange_sectionsPresheafOfModules_of_isPullback B S hS F g H)
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_restrictionBaseChange_of_iso (R := commStructurePresheaf B S hS)
      ((SheafOfModules.forget _).mapIso (associatedModuleIsoSectionsSheaf B S hS F).symm) g.op)

end Sections

section Pushforward

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- A morphism property stable under base change holds for the first projection of the pullback of
an object of the small étale site of `Y` along `a`, if it holds for `a`. -/
private theorem inclusion_map_fst_of_schemeHom (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (T : SmallEtale B Y.obj Y.property) (h : P (schemeHom B a)) :
    P (B.inclusion.map (pullback.fst T.obj.hom a)) :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback T.obj.hom a).map B.inclusion).flip h

/-- The base change along a quasi-compact `a` of an object of the small étale site of `Y` with
quasi-compact underlying scheme has quasi-compact underlying scheme. -/
theorem compactSpace_toScheme_smallEtaleBaseChange [QuasiCompact (schemeHom B a)]
    (T : SmallEtale B Y.obj Y.property) [CompactSpace ((toScheme B Y.obj Y.property).obj T)] :
    CompactSpace ((toScheme B X.obj X.property).obj ((smallEtaleBaseChange B a).obj T)) := by
  have hc : CompactSpace (B.inclusion.obj T.obj.left) :=
    inferInstanceAs (CompactSpace ((toScheme B Y.obj Y.property).obj T))
  have hq : QuasiCompact (B.inclusion.map (pullback.fst T.obj.hom a)) :=
    inclusion_map_fst_of_schemeHom B a (@QuasiCompact) T inferInstance
  exact @QuasiCompact.compactSpace_of_compactSpace _ _ _ hq hc

/-- The base change along a quasi-separated `a` of an object of the small étale site of `Y`
with quasi-separated underlying scheme has quasi-separated underlying scheme. -/
theorem quasiSeparatedSpace_toScheme_smallEtaleBaseChange [QuasiSeparated (schemeHom B a)]
    (T : SmallEtale B Y.obj Y.property)
    [QuasiSeparatedSpace ((toScheme B Y.obj Y.property).obj T)] :
    QuasiSeparatedSpace
      ((toScheme B X.obj X.property).obj ((smallEtaleBaseChange B a).obj T)) := by
  have hc : QuasiSeparatedSpace (B.inclusion.obj T.obj.left) :=
    inferInstanceAs (QuasiSeparatedSpace ((toScheme B Y.obj Y.property).obj T))
  have hq : QuasiSeparated (B.inclusion.map (pullback.fst T.obj.hom a)) :=
    inclusion_map_fst_of_schemeHom B a (@QuasiSeparated) T inferInstance
  exact @quasiSeparatedSpace_of_quasiSeparated _ _ _ hc hq

/-- **The small étale direct image along a quasi-compact quasi-separated morphism of the
associated module of a quasi-coherent module is cartesian between affine objects.** -/
theorem bijective_restrictionBaseChange_pushforward_of_qcqs
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent]
    {T T' : SmallEtale B Y.obj Y.property} (f : T ⟶ T')
    (hT : AlgebraicGeometry.IsAffine ((toScheme B Y.obj Y.property).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B Y.obj Y.property).obj T')) :
    Function.Bijective (restrictionBaseChange (R := commStructurePresheaf B Y.obj Y.property)
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        ((associatedModule B X.obj X.property).obj 𝓕)).val f.op) := by
  have := compactSpace_toScheme_smallEtaleBaseChange B a T'
  have := quasiSeparatedSpace_toScheme_smallEtaleBaseChange B a T'
  have H := isPullback_toScheme_smallEtaleBaseChange B a f
  refine Stacks.PresheafOfModules.bijective_restrictionBaseChange_pushforward
    (structureSharp B a).hom ((associatedModule B X.obj X.property).obj 𝓕).val f.op ?_
    (bijective_restrictionBaseChange_associatedModule_of_isPullback B X.obj X.property 𝓕
      ((smallEtaleBaseChange B a).map f) H)
  have := isPushout_appTop_of_flat H
  exact this

/-- **The small étale direct image along a quasi-compact quasi-separated morphism is cartesian
between affine objects** at the associated module of a quasi-coherent module, read as
`AlgebraicGeometry.SmallEtale.IsCartesianOnAffines`. -/
theorem isCartesianOnAffines_pushforward_of_qcqs
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    IsCartesianOnAffines B Y.obj Y.property
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        ((associatedModule B X.obj X.property).obj 𝓕)) :=
  fun f hT hT' => bijective_restrictionBaseChange_pushforward_of_qcqs B a 𝓕 f hT hT'

/-- The Zariski restriction of the small étale direct image along a quasi-compact quasi-separated
morphism of the associated module of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_restrictModule_pushforward_of_qcqs
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    SheafOfModules.IsQuasicoherent (R := Y.obj.ringCatSheaf)
      ((restrictModule B Y.obj Y.property).obj
        ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
          ((associatedModule B X.obj X.property).obj 𝓕))) := by
  have h𝓕 : SheafOfModules.IsQuasicoherent (R := X.obj.ringCatSheaf) 𝓕 := inferInstance
  have hu : IsIso ((associatedModuleAdjunction B X.obj X.property).unit.app 𝓕) :=
    unitIsoOnQuasicoherent B X.obj X.property ⟨𝓕, h𝓕⟩
  have hr : SheafOfModules.IsQuasicoherent (R := X.obj.ringCatSheaf)
      ((restrictModule B X.obj X.property).obj ((associatedModule B X.obj X.property).obj 𝓕)) :=
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.obj.ringCatSheaf)
      (@asIso _ _ _ _ ((associatedModuleAdjunction B X.obj X.property).unit.app 𝓕) hu) h𝓕
  exact ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent Y.obj.ringCatSheaf)
    (restrictModulePushforwardObjIso B a ((associatedModule B X.obj X.property).obj 𝓕)).symm
    (@pushforward_isQuasicoherent _ _ (schemeHom B a) _ _ _ hr)

/-- **The counit of the associated-module adjunction of `Y_étale` is an isomorphism at the small
étale direct image along a quasi-compact quasi-separated morphism of the associated module of a
quasi-coherent module.** -/
theorem isIso_counit_pushforward_of_qcqs
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    IsIso ((associatedModuleAdjunction B Y.obj Y.property).counit.app
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        ((associatedModule B X.obj X.property).obj 𝓕))) :=
  isIso_counit_of_isCartesianOnAffines B Y.obj Y.property _
    (isCartesianOnAffines_pushforward_of_qcqs B a 𝓕)
    (isQuasicoherent_restrictModule_pushforward_of_qcqs B a 𝓕)

/-- **The small étale direct image along a quasi-compact quasi-separated morphism of the
associated module of a quasi-coherent module is quasi-coherent on the site.** -/
theorem isQuasicoherentOnSite_pushforward_associatedModule_of_qcqs
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
      ((associatedModule B X.obj X.property).obj 𝓕)).IsQuasicoherentOnSite := by
  have := isIso_counit_pushforward_of_qcqs B a 𝓕
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (asIso ((associatedModuleAdjunction B Y.obj Y.property).counit.app
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        ((associatedModule B X.obj X.property).obj 𝓕))))
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B Y.obj Y.property _
      (isQuasicoherent_restrictModule_pushforward_of_qcqs B a 𝓕))

/-- **Descent, Lemma 071N in degree zero: `(ε_a)_*(𝓕^a) ≅ (r_*𝓕)^a`** for a quasi-compact
quasi-separated morphism of schemes `r` underlying `a` and a quasi-coherent `𝒪_X`-module
`𝓕`. -/
def pushforwardAssociatedModuleIsoOfQcqs
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        ((associatedModule B X.obj X.property).obj 𝓕) ≅
      (associatedModule B Y.obj Y.property).obj
        ((Scheme.Modules.pushforward (schemeHom B a)).obj 𝓕) :=
  haveI : IsIso ((associatedModuleAdjunction B X.obj X.property).unit.app 𝓕) :=
    unitIsoOnQuasicoherent B X.obj X.property ⟨𝓕, inferInstance⟩
  haveI := isIso_counit_pushforward_of_qcqs B a 𝓕
  (asIso ((associatedModuleAdjunction B Y.obj Y.property).counit.app
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        ((associatedModule B X.obj X.property).obj 𝓕)))).symm ≪≫
    (associatedModule B Y.obj Y.property).mapIso
      (restrictModulePushforwardObjIso B a ((associatedModule B X.obj X.property).obj 𝓕) ≪≫
        (Scheme.Modules.pushforward (schemeHom B a)).mapIso
          (asIso ((associatedModuleAdjunction B X.obj X.property).unit.app 𝓕)).symm)

end Pushforward

end AlgebraicGeometry.SmallEtale
