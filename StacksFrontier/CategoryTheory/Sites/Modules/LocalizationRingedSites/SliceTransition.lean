module

public import StacksFrontier.CategoryTheory.Adjunction.MateCompatibility
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitTranspose
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedPullbackMate
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos

/-!
# Transitions of restrictions of modules, localized at a slice

Let `f : X ⟶ Y` be a morphism of ringed sites given by `u : Y.C ⥤ X.C`, let `T` be a site with a
sheaf of rings `R`, and let `G : X.C ⥤ T`, `G' : Y.C ⥤ T` be continuous functors with ring maps
`O_X ⟶ G^s R`, `O_Y ⟶ G'^s R` and a transformation `τ : u ⋙ G ⟶ G'` compatible with the
structure map of `f`. Restriction of modules along `G` and `G'` is then related by a transition
`ρ_{G'} ⟶ ρ_G ⋙ f_*` (on sections, the restriction maps of a module along `τ`).

For `V : Y.C` the same data localize: `q = Over.post G' : Y.C/V ⥤ T/G'(V)` and
`p = Over.post G ⋙ Over.map τ_V : X.C/u(V) ⥤ T/G'(V)`, with the transformation
`Over.post u ⋙ p ⟶ q` given by `τ`, give a transition `q^* ⟶ p^* ⋙ f'_*` of restrictions of
modules on the slice `T/G'(V)`, `f'` the localized morphism of Stacks 04J0.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.siteTransition`: the transition `ρ_{G'} ⟶ ρ_G ⋙ f_*`.
* `AlgebraicGeometry.RingedSite.Hom.sliceTransition`: its localization `q^* ⟶ p^* ⋙ f'_*`.
* `AlgebraicGeometry.RingedSite.Hom.siteTransitionPullback`: the transpose `f^*ρ_{G'} ⟶ ρ_G`.
* `AlgebraicGeometry.RingedSite.Hom.localizedPullbackMate_comp_siteTransition`: the transposed
  transition commutes with localization, through the localization mate of
  `AlgebraicGeometry.RingedSite.Hom.localizedPullbackMate`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.RingedSite.Hom

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable {T : Type u} [SmallCategory T] {JT : GrothendieckTopology T} (R : Sheaf JT RingCat.{u})
  {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) {G : X.C ⥤ T} {G' : Y.C ⥤ T}
  [hG : G.IsContinuous X.J JT] [hG' : G'.IsContinuous Y.J JT] (τ : f.u ⋙ G ⟶ G') (V : Y.C)

/-- The transformation `Over.post u ⋙ p ⟶ q` of functors `Y.C/V ⥤ T/G'(V)` induced by
`τ : u ⋙ G ⟶ G'`. -/
@[simps]
def sliceTransitionNatTrans :
    Over.post (X := V) f.u ⋙ Over.post (X := f.u.obj V) G ⋙ Over.map (τ.app V) ⟶
      Over.post (X := V) G' where
  app W := Over.homMk (τ.app W.left) (τ.naturality W.hom).symm
  naturality _ _ g := Over.OverMorphism.ext (τ.naturality g.left)

variable (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) ⟶
    (G.sheafPushforwardContinuous RingCat.{u} X.J JT).obj R)
  (ψ' : (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O) ⟶
    (G'.sheafPushforwardContinuous RingCat.{u} Y.J JT).obj R)

/-- The compatibility of the ring maps `O_X ⟶ G^s R`, `O_Y ⟶ G'^s R` with the structure map of
`f` and with `τ`: both ways of mapping `O_Y` to `(u ⋙ G)^s R` agree. -/
abbrev RingCompatible : Prop :=
  haveI := f.isMorphismOfSites.isContinuous
  haveI := f.toRingedToposSiteHom.isContinuous
  haveI := Functor.isContinuous_comp f.u G Y.J X.J JT
  ψ' ≫ (Functor.sheafPushforwardContinuousNatTrans τ RingCat.{u} Y.J JT).app R =
    f.toRingedToposSiteHom.fSharpRing ≫ (f.u.sheafPushforwardContinuous RingCat.{u} Y.J X.J).map ψ

/-- **The transition of restrictions of modules.** For a module `M` over `R`, the map
`ρ_{G'}M ⟶ f_*(ρ_G M)` which on sections over `W` is the restriction of `M` along
`τ_W : G(u W) ⟶ G'(W)`. -/
noncomputable def siteTransition (hτ : f.RingCompatible R τ ψ ψ') :
    SheafOfModules.pushforward.{u} (F := G') ψ' ⟶
      SheafOfModules.pushforward.{u} (F := G) ψ ⋙ f.ringedToposHom.pushforwardModules :=
  haveI := f.isMorphismOfSites.isContinuous
  haveI := f.toRingedToposSiteHom.isContinuous
  haveI := Functor.isContinuous_comp f.u G Y.J X.J JT
  SheafOfModules.pushforwardNatTrans ψ' τ ≫ (SheafOfModules.pushforwardCongr hτ).hom ≫
    (SheafOfModules.pushforwardComp f.toRingedToposSiteHom.fSharpRing ψ).inv ≫
    Functor.whiskerLeft _ f.pushforwardToposIso.inv

/-- The restriction of `R` to the slice `T/G'(V)`. -/
noncomputable abbrev sliceRing : Sheaf (JT.over (G'.obj V)) RingCat.{u} :=
  ((Over.forget (G'.obj V)).sheafPushforwardContinuous RingCat.{u} (JT.over (G'.obj V)) JT).obj R

/-- `q = Over.post G'` is continuous for the localized topologies. -/
theorem isContinuous_sliceLeft :
    (Over.post (X := V) G').IsContinuous (Y.over V).J (JT.over (G'.obj V)) :=
  Functor.isContinuous_overPost_of_isContinuous Y.J JT G' V

/-- `p = Over.post G ⋙ Over.map τ_V` is continuous for the localized topologies. -/
theorem isContinuous_sliceRight :
    (Over.post (X := f.u.obj V) G ⋙ Over.map (τ.app V)).IsContinuous (X.over (f.u.obj V)).J
      (JT.over (G'.obj V)) :=
  inferInstanceAs ((Over.post (X := f.u.obj V) G ⋙ Over.map (τ.app V)).IsContinuous
    (X.J.over (f.u.obj V)) (JT.over (G'.obj V)))

attribute [local instance] isContinuous_sliceLeft isContinuous_sliceRight

/-- The ring map `O_{Y/V} ⟶ q^s(R|_{G'(V)})` obtained by restricting `ψ'`. -/
noncomputable abbrev sliceRingMapLeft :
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := (Y.over V).J) (Y.over V).O) ⟶
      ((Over.post (X := V) G').sheafPushforwardContinuous RingCat.{u} (Y.over V).J
        (JT.over (G'.obj V))).obj (sliceRing R V) :=
  (Y.J.overPullback RingCat.{u} V).map ψ'

/-- The ring map `O_{X/u(V)} ⟶ p^s(R|_{G'(V)})` obtained by restricting `ψ`. -/
noncomputable abbrev sliceRingMapRight :
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.over (f.u.obj V)).J) (X.over (f.u.obj V)).O) ⟶
      ((Over.post (X := f.u.obj V) G ⋙ Over.map (τ.app V)).sheafPushforwardContinuous RingCat.{u}
        (X.over (f.u.obj V)).J (JT.over (G'.obj V))).obj (sliceRing R V) :=
  (X.J.overPullback RingCat.{u} (f.u.obj V)).map ψ

/-- The ring compatibility localizes: the restricted ring maps are compatible with the localized
morphism `f'` and the transformation `Over.post u ⋙ p ⟶ q` induced by `τ`. -/
theorem ringCompatible_localized (hτ : f.RingCompatible R τ ψ ψ') :
    (f.localized V).RingCompatible (hG := f.isContinuous_sliceRight τ V)
      (hG' := isContinuous_sliceLeft V) (sliceRing R V) (f.sliceTransitionNatTrans τ V)
      (f.sliceRingMapRight R τ V ψ) (sliceRingMapLeft R V ψ') :=
  Sheaf.hom_ext (NatTrans.ext (funext fun W : (Over V)ᵒᵖ ↦
    congrArg (fun g : (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O) ⟶ _ ↦
      g.hom.app (Opposite.op W.unop.left)) hτ))

/-- **The localized transition.** The transition of restrictions of modules on the slice
`T/G'(V)`: `q^*M ⟶ f'_*(p^*M)`, on sections over `W` the restriction of `M` along `τ_W`. -/
noncomputable def sliceTransition (hτ : f.RingCompatible R τ ψ ψ') :
    haveI := isContinuous_sliceLeft (G' := G') (hG' := hG') V
    haveI := f.isContinuous_sliceRight (hG := hG) τ V
    SheafOfModules.pushforward.{u} (F := Over.post (X := V) G') (J := (Y.over V).J)
        (K := JT.over (G'.obj V)) (sliceRingMapLeft R V ψ') ⟶
      SheafOfModules.pushforward.{u} (F := Over.post (X := f.u.obj V) G ⋙ Over.map (τ.app V))
          (J := (X.over (f.u.obj V)).J) (K := JT.over (G'.obj V))
          (f.sliceRingMapRight R τ V ψ) ⋙
        (f.localized V).ringedToposHom.pushforwardModules :=
  (f.localized V).siteTransition (hG := f.isContinuous_sliceRight τ V)
    (hG' := isContinuous_sliceLeft V) (sliceRing R V) (f.sliceTransitionNatTrans τ V) _ _
    (f.ringCompatible_localized R τ V ψ ψ' hτ)

section Pullback

variable [hXs : HasWeakSheafify X.J AddCommGrpCat.{u}]
  [hXw : X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The transpose of the transition along `f^* ⊣ f_*`: the transformation
`f^*(ρ_{G'}M) ⟶ ρ_G M`. -/
noncomputable def siteTransitionPullback (hτ : f.RingCompatible R τ ψ ψ') :
    SheafOfModules.pushforward.{u} (F := G') ψ' ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
          f.ringedToposHom.toModulesHom ⟶
      SheafOfModules.pushforward.{u} (F := G) ψ :=
  Functor.whiskerRight (f.siteTransition R τ ψ ψ' hτ) _ ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f.ringedToposHom).counit ≫
    (Functor.rightUnitor _).hom

/-- The component of the transposed transition is the transpose of the component. -/
theorem siteTransitionPullback_app (hτ : f.RingCompatible R τ ψ ψ')
    (M : SheafOfModules.{u} R) :
    (f.siteTransitionPullback R τ ψ ψ' hτ).app M =
      ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f.ringedToposHom).homEquiv
        _ _).symm ((f.siteTransition R τ ψ ψ' hτ).app M) := by
  rw [Adjunction.homEquiv_counit]
  simp [siteTransitionPullback]

/-- The transposed transition at a module is invertible exactly when the transpose, along an
equal morphism of ringed topoi, of a map with the same underlying sheaf map is. -/
theorem isIso_siteTransitionPullback_app_iff (hτ : f.RingCompatible R τ ψ ψ')
    (M : SheafOfModules.{u} R) {g : RingedToposHom (ringedTopos X) (ringedTopos Y)}
    (hg : f.ringedToposHom = g)
    {A : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))}
    (hA : (SheafOfModules.pushforward.{u} (F := G') ψ').obj M = A)
    {B : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
    (hB : (SheafOfModules.pushforward.{u} (F := G) ψ).obj M = B)
    (β : A ⟶ g.pushforwardModules.obj B)
    (h : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        ((f.siteTransition R τ ψ ψ' hτ).app M) ≍
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map β) :
    IsIso ((f.siteTransitionPullback R τ ψ ψ' hτ).app M) ↔
      IsIso ((g.pullbackAdjPushforwardModules.homEquiv A B).symm β) := by
  rw [siteTransitionPullback_app]
  exact RingedToposHom.isIso_homEquiv_symm_iff_of_eq _ hg hA hB _ β h

variable [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restricting `ρ_{G'}M` to `Y.C/V` is restricting `M|_{G'(V)}` along `q`, on the nose. -/
theorem sliceLeft_obj_restriction (M : SheafOfModules.{u} R) :
    haveI := isContinuous_sliceLeft (G' := G') (hG' := hG') V
    (SheafOfModules.pushforward.{u} (F := Over.post (X := V) G') (J := (Y.over V).J)
        (K := JT.over (G'.obj V)) (sliceRingMapLeft R V ψ')).obj
      ((restrictionModules (JT.over (G'.obj V)) JT (Over.forget (G'.obj V)) R).obj M) =
    (Y.overRestrictionModules V).obj ((SheafOfModules.pushforward.{u} (F := G') ψ').obj M) :=
  rfl

omit hXs hXw [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restricting `ρ_G M` to `X.C/u(V)` is restricting `M|_{G'(V)}` along `p`, on the nose. -/
theorem sliceRight_obj_restriction (M : SheafOfModules.{u} R) :
    haveI := f.isContinuous_sliceRight (hG := hG) τ V
    (SheafOfModules.pushforward.{u} (F := Over.post (X := f.u.obj V) G ⋙ Over.map (τ.app V))
        (J := (X.over (f.u.obj V)).J) (K := JT.over (G'.obj V))
        (f.sliceRingMapRight R τ V ψ)).obj
      ((restrictionModules (JT.over (G'.obj V)) JT (Over.forget (G'.obj V)) R).obj M) =
    (X.overRestrictionModules (f.u.obj V)).obj
      ((SheafOfModules.pushforward.{u} (F := G) ψ).obj M) :=
  rfl

omit hXs hXw [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- On sections, the localized transition at `M|_{G'(V)}` is the restriction to the slice of
the transition at `M`: both are the restriction maps of `M` along `τ`. -/
theorem sliceTransition_app_restriction (hτ : f.RingCompatible R τ ψ ψ')
    (M : SheafOfModules.{u} R) :
    (f.sliceTransition R τ V ψ ψ' hτ).app
          ((restrictionModules (JT.over (G'.obj V)) JT (Over.forget (G'.obj V)) R).obj M) ≫
        (f.localized V).ringedToposHom.pushforwardModules.map
          (eqToHom (f.sliceRight_obj_restriction R τ V ψ M)) =
      eqToHom (sliceLeft_obj_restriction R V ψ' M) ≫
        (Y.overRestrictionModules V).map ((f.siteTransition R τ ψ ψ' hτ).app M) ≫
          (f.localizedPushforwardSquare V).app
            ((SheafOfModules.pushforward.{u} (F := G) ψ).obj M) := by
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  apply Sheaf.hom_ext_sections
  intro W x
  rfl

omit [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The transition commutes with localization** (the compatibility in the proof of
Stacks 0D7M). For a module `M` over `R`, the localization mate
`f'^*((ρ_{G'}M)|_V) ⟶ (f^*ρ_{G'}M)|_{u(V)}` followed by the restriction of the transposed
transition `f^*ρ_{G'}M ⟶ ρ_G M` is the transposed localized transition at `M|_{G'(V)}`, read
through the identifications of restrictions above. -/
theorem localizedPullbackMate_comp_siteTransition (hτ : f.RingCompatible R τ ψ ψ')
    (M : SheafOfModules.{u} R) :
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        ((f.localized V).ringedToposHom).toModulesHom).map
        (eqToHom (sliceLeft_obj_restriction R V ψ' M)) ≫
      (f.localizedPullbackMate V).app ((SheafOfModules.pushforward.{u} (F := G') ψ').obj M) ≫
        (X.overRestrictionModules (f.u.obj V)).map
          (((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
            f.ringedToposHom).homEquiv _ _).symm ((f.siteTransition R τ ψ ψ' hτ).app M)) =
      ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        (f.localized V).ringedToposHom).homEquiv _ _).symm
          ((f.sliceTransition R τ V ψ ψ' hτ).app
            ((restrictionModules (JT.over (G'.obj V)) JT (Over.forget (G'.obj V)) R).obj M)) ≫
        eqToHom (f.sliceRight_obj_restriction R τ V ψ M) := by
  have h := Stacks.CategoryTheory.mate_compat
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f.ringedToposHom)
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
      (f.localized V).ringedToposHom)
    (f.localizedPushforwardSquare V) (f.siteTransition R τ ψ ψ' hτ)
    (f.sliceTransition R τ V ψ ψ' hτ)
    (restrictionModules (JT.over (G'.obj V)) JT (Over.forget (G'.obj V)) R) M
    (eqToIso (sliceLeft_obj_restriction R V ψ' M))
    (eqToIso (f.sliceRight_obj_restriction R τ V ψ M))
    (f.sliceTransition_app_restriction R τ V ψ ψ' hτ M)
  exact h

end Pullback

end AlgebraicGeometry.RingedSite.Hom
