module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartTilde
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverBaseChangeAlgebraIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FlatIdealTensorVanishing

/-!
# The scheme-side `β` of Stacks 08BD is an isomorphism

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces, `V` an affine étale chart of
`Y` with Noetherian ring of functions, and `g : V ×_Y X ⟶ V` the base-change morphism of chart
schemes.  `AlgebraicGeometry.Space.chartBetaSystem` transposes the sections over `V` of the maps
`γ_n : 𝓖_n ⟶ f_*(𝓕/𝓘 ⁿ⁺¹𝓕)` of Stacks 08BD to morphisms `g^*𝓖̃_n ⟶ 𝓕̄^∧_n` on the chart's scheme
of `V ×_Y X`.  These are isomorphisms on the sections over every affine open.

## Main results

* `AlgebraicGeometry.Space.chartBetaSystem_pullbackSection` — the value of the scheme-side `β`
  on the pullback of a section of `𝓖_n` over `V`.
* `AlgebraicGeometry.Space.bijective_chartBetaSystem_app` — **the scheme-side `β` is bijective
  on the sections over every affine open.**

## References

* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

section TensorCongr

variable {R R' S S' M M' : Type*} [CommRing R] [CommRing R']
    [AddCommGroup S] [AddCommGroup S'] [AddCommGroup M] [AddCommGroup M'] [Module R M]
    [Module R' M'] [Module R S] [Module R' S'] (eR : R ≃+* R') (eS : S ≃+ S') (u : M ≃+ M')
    (hS : ∀ (r : R) (s : S), eS (r • s) = eR r • eS s)
    (hu : ∀ (r : R) (m : M), u (r • m) = eR r • u m)

/-- The additive map `S ⊗[R] M → S' ⊗[R'] M'`, `s ⊗ m ↦ eS s ⊗ u m`, of compatible additive maps
along a ring isomorphism. -/
def _root_.TensorProduct.mapOfRingEquiv : TensorProduct R S M →+ TensorProduct R' S' M' :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun m => eS s ⊗ₜ[R'] u m)
      (fun a b => by rw [map_add, TensorProduct.tmul_add]))
      (fun a b => by ext m; simp only [map_add, TensorProduct.add_tmul, AddMonoidHom.mk'_apply,
        AddMonoidHom.add_apply]))
    (fun r s m => by
      simp only [AddMonoidHom.mk'_apply, hS, hu, TensorProduct.smul_tmul])

/-- `TensorProduct.mapOfRingEquiv` on a pure tensor. -/
theorem _root_.TensorProduct.mapOfRingEquiv_tmul (s : S) (m : M) :
    TensorProduct.mapOfRingEquiv eR eS u hS hu (s ⊗ₜ m) = eS s ⊗ₜ u m := rfl

/-- Additive maps out of a tensor product agreeing on pure tensors agree. -/
private theorem tensor_addMonoidHom_ext {P : Type*} [AddCommGroup P]
    (f g : TensorProduct R S M →+ P)
    (h : ∀ (s : S) (m : M), f (s ⊗ₜ[R] m) = g (s ⊗ₜ[R] m)) : f = g := by
  ext w
  induction w using TensorProduct.inductionOn with
  | tmul s m => exact h s m
  | add a b ha hb =>
    exact (map_add f a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add g a b).symm)

/-- `TensorProduct.mapOfRingEquiv` along the inverse isomorphisms undoes it. -/
theorem _root_.TensorProduct.mapOfRingEquiv_symm_comp (w : TensorProduct R S M) :
    TensorProduct.mapOfRingEquiv eR.symm eS.symm u.symm
      (fun r s => by
        obtain ⟨r, rfl⟩ := eR.surjective r
        obtain ⟨s, rfl⟩ := eS.surjective s
        rw [← hS, RingEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply])
      (fun r m => by
        obtain ⟨r, rfl⟩ := eR.surjective r
        obtain ⟨m, rfl⟩ := u.surjective m
        rw [← hu, RingEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply])
      (TensorProduct.mapOfRingEquiv eR eS u hS hu w) = w := by
  generalize_proofs h₁ h₂
  exact DFunLike.congr_fun (tensor_addMonoidHom_ext
    ((TensorProduct.mapOfRingEquiv eR.symm eS.symm u.symm h₁ h₂).comp
      (TensorProduct.mapOfRingEquiv eR eS u hS hu)) (AddMonoidHom.id _) fun s m =>
        congrArg₂ (fun a b => a ⊗ₜ[R] b) (eS.symm_apply_apply s) (u.symm_apply_apply m)) w

/-- Additive maps out of an extension of scalars agreeing on pure tensors agree. -/
theorem _root_.ModuleCat.ExtendScalars.addMonoidHom_ext {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M : ModuleCat.{u} R} {P : Type*} [AddCommGroup P]
    (f g : (ModuleCat.extendScalars φ.hom).obj M →+ P)
    (h : ∀ (s : S) (m : M), f (s ⊗ₜ[R,φ.hom] m) = g (s ⊗ₜ[R,φ.hom] m)) : f = g :=
  tensor_addMonoidHom_ext f g h

/-- **Base change along compatible ring isomorphisms.**  An isomorphism `R ≃ R'` of the rings and
additive isomorphisms `S ≃ S'`, `M ≃ M'`, compatible with the scalar actions, give an additive
isomorphism `S ⊗[R] M ≃ S' ⊗[R'] M'`. -/
def _root_.TensorProduct.congrOfRingEquiv : TensorProduct R S M ≃+ TensorProduct R' S' M' :=
  have hS' : ∀ (r : R') (s : S'), eS.symm (r • s) = eR.symm r • eS.symm s := fun r s => by
    obtain ⟨r, rfl⟩ := eR.surjective r
    obtain ⟨s, rfl⟩ := eS.surjective s
    rw [← hS, RingEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  have hu' : ∀ (r : R') (m : M'), u.symm (r • m) = eR.symm r • u.symm m := fun r m => by
    obtain ⟨r, rfl⟩ := eR.surjective r
    obtain ⟨m, rfl⟩ := u.surjective m
    rw [← hu, RingEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  { TensorProduct.mapOfRingEquiv eR eS u hS hu with
    invFun := TensorProduct.mapOfRingEquiv eR.symm eS.symm u.symm hS' hu'
    left_inv := TensorProduct.mapOfRingEquiv_symm_comp eR eS u hS hu
    right_inv := TensorProduct.mapOfRingEquiv_symm_comp eR.symm eS.symm u.symm hS' hu' }

/-- `TensorProduct.congrOfRingEquiv` on a pure tensor. -/
theorem _root_.TensorProduct.congrOfRingEquiv_tmul (s : S) (m : M) :
    TensorProduct.congrOfRingEquiv eR eS u hS hu (s ⊗ₜ m) = eS s ⊗ₜ u m := rfl

end TensorCongr

/-- A linear map carries `t • w` to `t • z` when it carries `w` to `z`. -/
theorem _root_.LinearMap.map_smul_of_eq {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (φ : M →ₗ[R] N) (t : R) {w : M} {z : N}
    (h : φ w = z) : φ (t • w) = t • z :=
  (φ.map_smul t w).trans (congrArg _ h)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restricting to an open the global section of the chart restriction attached to a section over
the chart is the section restricted to the chart the open cuts out. -/
theorem chartRestrictionSheaf_map_topEquiv (Z : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Z.1 Z.2)
    (A : SmallEtale B S hS Z.1) (O : (chartScheme A).Opens) (y : M.val.obj (op A)) :
    (chartRestrictionSheaf B S hS Z M A).val.map (homOfLE le_top : O ⟶ ⊤).op
        (chartRestrictionSheafTopEquiv B S hS Z M A y) =
      ULift.up (M.val.map (chartOpensHom B S hS Z A O).op y) := by
  change ULift.up (M.val.map ((chartOpens B S hS A).map (homOfLE (le_top : O ≤ ⊤))).op
      (M.val.map (chartOpensTopHom B S hS Z A).op y)) = _
  refine congrArg ULift.up ?_
  have h1 := PresheafOfModules.map_comp_apply M.val (chartOpensTopHom B S hS Z A).op
    ((chartOpens B S hS A).map (homOfLE (le_top : O ≤ ⊤))).op y
  have h2 : (chartOpensTopHom B S hS Z A).op ≫
      ((chartOpens B S hS A).map (homOfLE (le_top : O ≤ ⊤))).op =
      (chartOpensHom B S hS Z A O).op :=
    congrArg Quiver.Hom.op (chartOpens_map_comp_chartOpensTopHom B S hS Z A O)
  exact h1.symm.trans (PresheafOfModules.congr_map_apply M.val h2 y)

/-- A morphism of modules on a scheme commutes with restricting global sections to an open. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.hom_app_top_restrict {T : Scheme.{u}}
    {M N : T.Modules}
    (φ : M ⟶ N) (O : T.Opens) (z : Γ(M, ⊤)) :
    N.val.map (homOfLE (le_top : O ≤ ⊤)).op (φ.val.app (op ⊤) z) =
      φ.val.app (op O) (M.val.map (homOfLE (le_top : O ≤ ⊤)).op z) :=
  (PresheafOfModules.naturality_apply φ.val (homOfLE (le_top : O ≤ ⊤)).op z).symm

/-- A morphism of modules on an algebraic space commutes with restriction of sections. -/
theorem val_map_hom_val_app {Z : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (φ : M ⟶ N) {A A' : SmallEtale B S hS Z.1} (i : A' ⟶ A) (z : M.val.obj (op A)) :
    N.val.map i.op (φ.val.app (op A) z) = φ.val.app (op A') (M.val.map i.op z) :=
  (PresheafOfModules.naturality_apply φ.val i.op z).symm

/-- The restriction to an open `O` of a section of a direct image over the whole target is the
restriction of the same section, read over the whole source. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.map_homOfLE_preimage_top {T T' : Scheme.{u}}
    (g : T' ⟶ T) (N : T'.Modules) (O : T'.Opens) (h : O ≤ g ⁻¹ᵁ ⊤)
    (z : ((Scheme.Modules.pushforward g).obj N).val.obj (op ⊤)) :
    N.val.map (homOfLE h).op z = N.val.map (homOfLE (le_top : O ≤ ⊤)).op (show Γ(N, ⊤) from z) :=
  rfl

/-- The functions on a Zariski open act on the sections of the chart restriction through the
functions on the chart that open cuts out. -/
theorem chartRestrictionSheaf_smul_up_chartRestrictionRingHom (Z : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Z.1 Z.2)
    (A : SmallEtale B S hS Z.1) (O : (chartScheme A).Opens)
    (t : (chartScheme A).ringCatSheaf.obj.obj (op O))
    (y : M.val.obj (op ((chartOpens B S hS A).obj O))) :
    t • (show (chartRestrictionSheaf B S hS Z M A).val.obj (op O) from ULift.up y) =
      ULift.up ((show chartRing B S hS Z.1 Z.2 ((chartOpens B S hS A).obj O) from
        ((chartRestrictionRingHom B S hS Z.2 A).app (op O)).hom t) • y) :=
  rfl

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)

/-- The chart diagram of a Zariski open of the chart's scheme of `V ×_Y X` over `V`. -/
abbrev baseChangeOpenChartDiagram (V : SmallEtale B S hS Y.1)
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) :
    ChartDiagram B S hS X.1 Y.1 f.hom where
  U := (chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O
  V := V
  g := (SmallEtale.toOver B S hS X.1).map (chartOpensHom B S hS X _ O) ≫
    (smallBaseChangeProjection B S hS f hf).app V
  comm := (Category.assoc _ _ _).trans ((congrArg
    (yoneda.map (chartOpenOverι B S hS ((smallBaseChange B S hS f hf).obj V) O) ≫ ·)
      (baseChangeChartDiagram B S hS f hf V).comm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ V.1.hom) (yoneda.map_comp _ _).symm)))

/-- The coefficient map of the chart diagram of a Zariski open `O` of the chart's scheme of
`V ×_Y X` is pullback of functions along the base-change morphism to `O`, read through
`O.topIso`. -/
theorem chartDiagramRestrict_baseChangeOpenChartDiagram (V : SmallEtale B S hS Y.1)
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (h : O ≤ chartBaseChangeMorphism B S hS f hf V ⁻¹ᵁ ⊤) (r : Γ(chartScheme V, ⊤)) :
    chartDiagramRestrict B S hS f (baseChangeOpenChartDiagram B S hS f hf V O) r =
      O.topIso.inv.hom (((chartBaseChangeMorphism B S hS f hf V).appLE ⊤ O h).hom r) :=
  (congrArg (fun φ => φ r)
    (appLE_top_comp_topIso_inv (chartBaseChangeMorphism B S hS f hf V) O h)).symm

/-- The chart section of `f^*M` over the chart cut out by an open of the chart's scheme of
`V ×_Y X` is the restriction of the chart section over `V ×_Y X`. -/
theorem modulePullbackChartSection_baseChangeOpenChartDiagram (V : SmallEtale B S hS Y.1)
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (x : M.val.obj (op V)) :
    modulePullbackChartSection B S hS f M (baseChangeOpenChartDiagram B S hS f hf V O) x =
      ((modulePullback B S hS f).obj M).val.map (chartOpensHom B S hS X _ O).op
        (modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf V) x) := by
  have h := modulePullbackChartSection_naturality B S hS f M
    (baseChangeChartDiagram B S hS f hf V) (baseChangeOpenChartDiagram B S hS f hf V O)
    (chartOpensHom B S hS X _ O) (𝟙 V)
    ((Category.comp_id _).symm.trans
      (congrArg (_ ≫ ·) ((SmallEtale.toOver B S hS Y.1).map_id V).symm)) x
  refine Eq.trans ?_ h
  exact congrArg _ (congrArg (fun φ => φ.hom x) (M.val.presheaf.map_id _)).symm

section ChartBeta

variable (J : (SheafOfModules.unit.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (V : SmallEtale B S hS Y.1) [hV : IsAffine (chartScheme V)]
    (G : CoherentAdicSystems B S hS Y.1 Y.2 J)
    (hIcart : IsCartesianOnAffineCharts (hF := X.2)
      (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules)
    [hXloc : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hIq : (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules.IsQuasicoherentOnSite)
    [hWN : IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (β : G.obj ⋙ modulePullback B S hS f ≅
      ((completionFunctor B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J) hIq).obj
        ⟨F, hF⟩).obj)

/-- The `n`-th term of the completion of the chart restriction of `𝓕` to `V ×_Y X`. -/
abbrev chartCompletionTerm (n : ℕ) : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Modules :=
  ((Stacks.Algebraization.completionFunctor (chartScheme ((smallBaseChange B S hS f hf).obj V))
    (chartBaseChangeIdeal B S hS f hf J V)).obj
    (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V))).obj.obj (op n)

omit hXloc in
/-- The comparison of completions commutes with restricting global sections to an open. -/
theorem chartBaseChangeCompletionIso_restrict (n : ℕ)
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (y : (idealPowerQuotient B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J) (n + 1) F).val.obj
      (op ((smallBaseChange B S hS f hf).obj V))) :
    (chartCompletionTerm B S hS f hf J V F hF n).val.map (homOfLE (le_top : O ≤ ⊤)).op
        ((chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom.val.app (op ⊤)
          (chartRestrictionSheafTopEquiv B S hS X _ ((smallBaseChange B S hS f hf).obj V) y)) =
      (chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom.val.app (op O)
        (ULift.up ((idealPowerQuotient B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J)
          (n + 1) F).val.map
          (chartOpensHom B S hS X ((smallBaseChange B S hS f hf).obj V) O).op y)) := by
  have h1 := Scheme.Modules.hom_app_top_restrict
    (chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom O
    (chartRestrictionSheafTopEquiv B S hS X _ ((smallBaseChange B S hS f hf).obj V) y)
  have h2 := chartRestrictionSheaf_map_topEquiv B S hS X _ ((smallBaseChange B S hS f hf).obj V) O y
  exact h1.trans (congrArg _ h2)

/-- **The restriction to a Zariski open of the value of `γ_n` on the chart.** -/
theorem chartGammaTower_restrict (n : ℕ)
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (x : (G.obj.obj (op n)).val.obj (op V)) :
    (chartCompletionTerm B S hS f hf J V F hF n).val.map (homOfLE (le_top : O ≤ ⊤)).op
        (show Γ(chartCompletionTerm B S hS f hf J V F hF n, ⊤) from
          (chartGammaTower B S hS J hJ V G f hf hIcart hIq F hF β).app (op n) x) =
      (chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom.val.app (op O)
        (ULift.up ((β.hom.app (op n)).val.app
          (op ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O))
          (modulePullbackChartSection B S hS f (G.obj.obj (op n))
            (baseChangeOpenChartDiagram B S hS f hf V O) x))) := by
  refine (chartBaseChangeCompletionIso_restrict B S hS f hf J hJ V hIcart F hF n O
    ((β.hom.app (op n)).val.app (op ((smallBaseChange B S hS f hf).obj V))
          (modulePullbackChartSection B S hS f (G.obj.obj (op n))
            (baseChangeChartDiagram B S hS f hf V) x))).trans ?_
  refine congrArg _ (congrArg ULift.up ?_)
  refine (val_map_hom_val_app B S hS (β.hom.app (op n))
    (chartOpensHom B S hS X ((smallBaseChange B S hS f hf).obj V) O) _).trans ?_
  exact congrArg _ (modulePullbackChartSection_baseChangeOpenChartDiagram B S hS f hf V O
    (G.obj.obj (op n)) x).symm

variable [hVN : IsNoetherianRing Γ(chartScheme V, ⊤)]

/-- **The value of the scheme-side `β` on the pullback of a section.** -/
theorem chartBetaSystem_pullbackSection (n : ℕ)
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (h : O ≤ chartBaseChangeMorphism B S hS f hf V ⁻¹ᵁ ⊤)
    (x : (G.obj.obj (op n)).val.obj (op V)) :
    ((chartBetaSystem B S hS J hJ V G f hf hIcart hIq F hF β).app (op n)).val.app (op O)
        (Scheme.Modules.pullbackSection (chartBaseChangeMorphism B S hS f hf V)
          ((chartTildeSystem B S hS J hJ V G).obj.obj (op n)) ⊤ O h
          (((affineTildeChartGlobalSectionsAdjunction B S hS V).unit.app
            ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op n))) x)) =
      (chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom.val.app (op O)
        (ULift.up ((β.hom.app (op n)).val.app
          (op ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O))
          (modulePullbackChartSection B S hS f (G.obj.obj (op n))
            (baseChangeOpenChartDiagram B S hS f hf V O) x))) := by
  have h1 := homEquiv_symm_pullbackSection (chartBaseChangeMorphism B S hS f hf V)
    (((affineTildeChartGlobalSectionsAdjunction B S hS V).homEquiv _ _).symm
      ((chartGammaTower B S hS J hJ V G f hf hIcart hIq F hF β).app (op n))) ⊤ O h
    (((affineTildeChartGlobalSectionsAdjunction B S hS V).unit.app
            ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op n))) x)
  have h2 := congrArg (fun φ => φ x) (congrArg (fun ψ => ψ.hom)
    ((affineTildeChartGlobalSectionsAdjunction B S hS V).unit_comp_map_homEquiv_symm
      ((chartGammaTower B S hS J hJ V G f hf hIcart hIq F hF β).app (op n))))
  refine h1.trans ?_
  refine (congrArg _ h2).trans ?_
  refine (Scheme.Modules.map_homOfLE_preimage_top _ _ O h _).trans ?_
  exact chartGammaTower_restrict B S hS f hf J hJ V G hIcart hIq F hF β n O x

/-- The functions on the chart cut out by an open `O` of the chart's scheme of `V ×_Y X` are the
functions on `O`. -/
def chartOpensBaseChangeRingEquiv (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) :
    Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), O) ≃+*
      chartRing B S hS X.1 X.2 ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O) :=
  O.topIso.symm.commRingCatIsoToRingEquiv

/-- The target side of the comparison: the base change description of `f^*𝓖_n` on the chart cut
out by `O`, followed by `β_n` and the comparison of completions. -/
def chartBetaTargetMap (n : ℕ) (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) :
    letI := chartDiagramAlgebra B S hS f (baseChangeOpenChartDiagram B S hS f hf V O)
    TensorProduct (chartRing B S hS Y.1 Y.2 V)
      (chartRing B S hS X.1 X.2 ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O))
      ((G.obj.obj (op n)).val.obj (op V)) →+
      Γ(chartCompletionTerm B S hS f hf J V F hF n, O) :=
  letI := chartDiagramAlgebra B S hS f (baseChangeOpenChartDiagram B S hS f hf V O)
  { toFun w := (chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom.val.app (op O)
      (ULift.up ((β.hom.app (op n)).val.app
        (op ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O))
        (modulePullbackChartBaseChange B S hS f (G.obj.obj (op n))
          (baseChangeOpenChartDiagram B S hS f hf V O) w)))
    map_zero' := by
      refine Eq.trans ?_ (map_zero ((chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF
        n).hom.val.app (op O)).hom)
      exact congrArg _ (congrArg ULift.up ((congrArg _ (map_zero _)).trans (map_zero _)))
    map_add' a b := by
      refine Eq.trans ?_ (map_add _ _ _)
      exact congrArg ((chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom.val.app
        (op O)) (congrArg ULift.up ((congrArg _ (map_add _ a b)).trans (map_add _ _ _))) }

omit hVN in
/-- `AlgebraicGeometry.Space.chartBetaTargetMap` on a pure tensor. -/
theorem chartBetaTargetMap_tmul (n : ℕ)
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (s : chartRing B S hS X.1 X.2 ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O))
    (x : (G.obj.obj (op n)).val.obj (op V)) :
    letI := chartDiagramAlgebra B S hS f (baseChangeOpenChartDiagram B S hS f hf V O)
    chartBetaTargetMap B S hS f hf J hJ V G hIcart hIq F hF β n O
        (s ⊗ₜ[chartRing B S hS Y.1 Y.2 V] x) =
      (chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom.val.app (op O)
        (ULift.up ((β.hom.app (op n)).val.app
          (op ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O))
          (s • modulePullbackChartSection B S hS f (G.obj.obj (op n))
            (baseChangeOpenChartDiagram B S hS f hf V O) x))) :=
  rfl

omit hVN in
/-- The target-side comparison is bijective. -/
theorem bijective_chartBetaTargetMap (n : ℕ)
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).affineOpens) :
    Function.Bijective (chartBetaTargetMap B S hS f hf J hJ V G hIcart hIq F hF β n O.1) := by
  let := chartDiagramAlgebra B S hS f (baseChangeOpenChartDiagram B S hS f hf V O.1)
  have hbc := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS f
    (G.obj.obj (op n)) (G.property.1 n).toIsQuasicoherentOnSite
    (baseChangeOpenChartDiagram B S hS f hf V O.1) O.2 hV
  exact (SheafOfModules.bijective_hom_val_app_of_iso
      (chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n) (op O.1)).comp
      (Equiv.ulift.symm.bijective.comp ((SheafOfModules.bijective_hom_val_app_of_iso
        (β.app (op n)) _).comp hbc))

omit hVN in
/-- The unit of `affineTilde ⊣ Γ` is bijective on the sections of `𝓖_n` over `V`. -/
theorem bijective_chartTildeAdjunction_unit_app (n : ℕ) :
    Function.Bijective ((affineTildeChartGlobalSectionsAdjunction B S hS V).unit.app
      ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op n))).hom := by
  have hfull : (Stacks.Coherent.affineTilde (chartScheme V)).Full := inferInstanceAs
    (tilde.functor _ ⋙ (Stacks.Coherent.affineRestrictionEquivalence (chartScheme V)).functor).Full
  have hfaith : (Stacks.Coherent.affineTilde (chartScheme V)).Faithful := inferInstanceAs
    (tilde.functor _ ⋙
      (Stacks.Coherent.affineRestrictionEquivalence (chartScheme V)).functor).Faithful
  exact (ConcreteCategory.isIso_iff_bijective _).mp
    (NatIso.isIso_app_of_isIso (affineTildeChartGlobalSectionsAdjunction B S hS V).unit _)

/-- The sections of the tilde of the sections over `V` are the sections over `V`. -/
def chartTildeUnitAddEquiv (n : ℕ) :
    ((G.obj.obj (op n)).val.obj (op V) : Type u) ≃+
      (Γ((chartTildeSystem B S hS J hJ V G).obj.obj (op n), ⊤) : Type u) :=
  AddEquiv.ofBijective ((affineTildeChartGlobalSectionsAdjunction B S hS V).unit.app
    ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op n))).hom
    (bijective_chartTildeAdjunction_unit_app B S hS J V G n)

/-- The source side of the comparison: the base change of the sections of `𝓖̃_n` along the
functions on `O` is the base change of the sections of `𝓖_n` over `V` along the functions on the
chart cut out by `O`. -/
def chartBetaSourceEquiv (n : ℕ) (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (h : O ≤ chartBaseChangeMorphism B S hS f hf V ⁻¹ᵁ ⊤) :
    letI := chartDiagramAlgebra B S hS f (baseChangeOpenChartDiagram B S hS f hf V O)
    (ModuleCat.extendScalars ((chartBaseChangeMorphism B S hS f hf V).appLE ⊤ O h).hom).obj
        (ModuleCat.of Γ(chartScheme V, ⊤)
          Γ((chartTildeSystem B S hS J hJ V G).obj.obj (op n), ⊤)) ≃+
      TensorProduct (chartRing B S hS Y.1 Y.2 V)
        (chartRing B S hS X.1 X.2 ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O))
        ((G.obj.obj (op n)).val.obj (op V)) :=
  letI := chartDiagramAlgebra B S hS f (baseChangeOpenChartDiagram B S hS f hf V O)
  let ue := chartTildeUnitAddEquiv B S hS J hJ V G n
  let eR : Γ(chartScheme V, ⊤) ≃+* chartRing B S hS Y.1 Y.2 V := RingEquiv.refl _
  let eS : (ModuleCat.restrictScalars ((chartBaseChangeMorphism B S hS f hf V).appLE ⊤ O h).hom).obj
        (ModuleCat.of _ Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), O)) ≃+
      chartRing B S hS X.1 X.2 ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O) :=
    (chartOpensBaseChangeRingEquiv B S hS f hf V O).toAddEquiv
  TensorProduct.congrOfRingEquiv eR eS ue.symm
    (fun r t => (map_mul (chartOpensBaseChangeRingEquiv B S hS f hf V O) _ _).trans
      (congrArg (· * _) (chartDiagramRestrict_baseChangeOpenChartDiagram B S hS f hf V O h r).symm))
    (fun r a => by
      obtain ⟨m, rfl⟩ := ue.surjective a
      refine (congrArg ue.symm (((affineTildeChartGlobalSectionsAdjunction B S hS V).unit.app
        ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op n))).hom.map_smul r m).symm).trans ?_
      exact (ue.symm_apply_apply _).trans (congrArg (r • ·) (ue.symm_apply_apply m).symm))

include hJ in
/-- On pure tensors, the scheme-side `β` read through the base change of the source is the
target-side comparison read through `AlgebraicGeometry.Space.chartBetaSourceEquiv`. -/
theorem chartBetaSystem_baseChangeIso_tmul (n : ℕ)
    [hq : ((chartTildeSystem B S hS J hJ V G).obj.obj (op n)).IsQuasicoherent]
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).affineOpens)
    (h : O.1 ≤ chartBaseChangeMorphism B S hS f hf V ⁻¹ᵁ ⊤)
    (t : Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), O.1))
    (a : Γ((chartTildeSystem B S hS J hJ V G).obj.obj (op n), ⊤)) :
    haveI : ((chartTildeSystem B S hS J hJ V G).obj.obj (op n)).IsQuasicoherent :=
      Stacks.Coherent.affineTilde_quasicoherent (chartScheme V) _
    ((chartBetaSystem B S hS J hJ V G f hf hIcart hIq F hF β).app (op n)).val.app (op O.1)
        ((affinePullbackSectionsBaseChangeIso (chartBaseChangeMorphism B S hS f hf V)
          ((chartTildeSystem B S hS J hJ V G).obj.obj (op n)) (isAffineOpen_top (chartScheme V))
          O.2 h).hom
          (t ⊗ₜ[Γ(chartScheme V, ⊤), ((chartBaseChangeMorphism B S hS f hf V).appLE ⊤ O.1 h).hom]
            a)) =
      chartBetaTargetMap B S hS f hf J hJ V G hIcart hIq F hF β n O.1
        (chartBetaSourceEquiv B S hS f hf J hJ V G n O.1 h
          (t ⊗ₜ[Γ(chartScheme V, ⊤), ((chartBaseChangeMorphism B S hS f hf V).appLE ⊤ O.1 h).hom]
            a)) := by
  have h1 := affinePullbackSectionsBaseChangeIso_tmul (chartBaseChangeMorphism B S hS f hf V)
    ((chartTildeSystem B S hS J hJ V G).obj.obj (op n)) (isAffineOpen_top (chartScheme V)) O.2 h t a
  have h2 := affinePullbackSectionsBaseChangeIso_one_tmul (chartBaseChangeMorphism B S hS f hf V)
    ((chartTildeSystem B S hS J hJ V G).obj.obj (op n)) (isAffineOpen_top (chartScheme V)) O.2 h a
  have hx : chartTildeUnitAddEquiv B S hS J hJ V G n
      ((chartTildeUnitAddEquiv B S hS J hJ V G n).symm a)
      = a := AddEquiv.apply_symm_apply _ a
  have h3 := (congrArg (fun a' =>
    ((chartBetaSystem B S hS J hJ V G f hf hIcart hIq F hF β).app (op n)).val.app (op O.1)
      (Scheme.Modules.pullbackSection (chartBaseChangeMorphism B S hS f hf V)
        ((chartTildeSystem B S hS J hJ V G).obj.obj (op n)) ⊤ O.1 h a')) hx).symm.trans
    (chartBetaSystem_pullbackSection B S hS f hf J hJ V G hIcart hIq F hF β n O.1 h
      ((chartTildeUnitAddEquiv B S hS J hJ V G n).symm a))
  refine (congrArg (((chartBetaSystem B S hS J hJ V G f hf hIcart hIq F hF β).app (op n)).val.app
    (op O.1)).hom (h1.trans (congrArg (t • ·) h2))).trans ?_
  refine ((((chartBetaSystem B S hS J hJ V G f hf hIcart hIq F hF β).app (op n)).val.app
    (op O.1)).hom.map_smul_of_eq t h3).trans ?_
  let : Module Γ(chartScheme V, ⊤) Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), O.1) :=
    Module.compHom _ ((chartBaseChangeMorphism B S hS f hf V).appLE ⊤ O.1 h).hom
  let := chartDiagramAlgebra B S hS f (baseChangeOpenChartDiagram B S hS f hf V O.1)
  have hE : chartBetaSourceEquiv B S hS f hf J hJ V G n O.1 h
      (t ⊗ₜ[Γ(chartScheme V, ⊤), ((chartBaseChangeMorphism B S hS f hf V).appLE ⊤ O.1 h).hom] a) =
      chartOpensBaseChangeRingEquiv B S hS f hf V O.1 t ⊗ₜ[chartRing B S hS Y.1 Y.2 V]
        (chartTildeUnitAddEquiv B S hS J hJ V G n).symm a := rfl
  refine Eq.trans ?_ (congrArg (chartBetaTargetMap B S hS f hf J hJ V G hIcart hIq F hF β n O.1)
    hE).symm
  refine (((chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom.val.app
    (op O.1)).hom.map_smul_of_eq t rfl).symm.trans ?_
  refine (congrArg ((chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom.val.app
    (op O.1))
      (chartRestrictionSheaf_smul_up_chartRestrictionRingHom B S hS X _ _ O.1 t _)).trans ?_
  refine Eq.trans ?_ (chartBetaTargetMap_tmul B S hS f hf J hJ V G hIcart hIq F hF β n O.1 _ _).symm
  exact congrArg ((chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n).hom.val.app
    (op O.1)) (congrArg ULift.up (((β.hom.app (op n)).val.app
      (op ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O.1))).hom.map_smul
        ((chartOpensBaseChangeRingEquiv B S hS f hf V O.1) t) _).symm)

include hJ in
/-- **The scheme-side `β` is an isomorphism on the sections over every affine open.** -/
theorem bijective_chartBetaSystem_app (n : ℕ)
    [hq : ((chartTildeSystem B S hS J hJ V G).obj.obj (op n)).IsQuasicoherent]
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).affineOpens) :
    Function.Bijective
      (((chartBetaSystem B S hS J hJ V G f hf hIcart hIq F hF β).app (op n)).val.app
        (op O.1)).hom := by
  have h : O.1 ≤ chartBaseChangeMorphism B S hS f hf V ⁻¹ᵁ ⊤ := le_top
  have hf1 := ModuleCat.ExtendScalars.addMonoidHom_ext
    ((chartBaseChangeMorphism B S hS f hf V).appLE ⊤ O.1 h)
    ((((chartBetaSystem B S hS J hJ V G f hf hIcart hIq F hF β).app (op n)).val.app
      (op O.1)).hom.toAddMonoidHom.comp
      (affinePullbackSectionsBaseChangeIso (chartBaseChangeMorphism B S hS f hf V)
          ((chartTildeSystem B S hS J hJ V G).obj.obj (op n)) (isAffineOpen_top (chartScheme V))
          O.2 h).hom.hom.toAddMonoidHom)
    ((chartBetaTargetMap B S hS f hf J hJ V G hIcart hIq F hF β n O.1).comp
      (chartBetaSourceEquiv B S hS f hf J hJ V G n O.1 h).toAddMonoidHom)
    (fun t a => chartBetaSystem_baseChangeIso_tmul B S hS f hf J hJ V G hIcart hIq F hF β n O h t a)
  have hLb : Function.Bijective (affinePullbackSectionsBaseChangeIso
      (chartBaseChangeMorphism B S hS f hf V) ((chartTildeSystem B S hS J hJ V G).obj.obj (op n))
      (isAffineOpen_top (chartScheme V)) O.2 h).hom.hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  refine (Function.Bijective.of_comp_iff _ hLb).mp ?_
  have hc : (((chartBetaSystem B S hS J hJ V G f hf hIcart hIq F hF β).app (op n)).val.app
      (op O.1)).hom ∘ (affinePullbackSectionsBaseChangeIso
      (chartBaseChangeMorphism B S hS f hf V) ((chartTildeSystem B S hS J hJ V G).obj.obj (op n))
      (isAffineOpen_top (chartScheme V)) O.2 h).hom.hom =
      chartBetaTargetMap B S hS f hf J hJ V G hIcart hIq F hF β n O.1 ∘
        chartBetaSourceEquiv B S hS f hf J hJ V G n O.1 h :=
    funext fun w => DFunLike.congr_fun hf1 w
  exact (congrArg Function.Bijective hc).mpr
    ((bijective_chartBetaTargetMap B S hS f hf J hJ V G hIcart hIq F hF β n O).comp
      (chartBetaSourceEquiv B S hS f hf J hJ V G n O.1 h).bijective)

end ChartBeta

end AlgebraicGeometry.Space
