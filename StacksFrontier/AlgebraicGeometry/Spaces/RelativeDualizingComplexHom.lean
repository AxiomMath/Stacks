module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedHomLocal
import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectHomWindow

/-!
# Morphisms of relative dualizing complexes of algebraic spaces after base change

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces of finite presentation with two pairs
`(ω₁, τ₁)`, `(ω₂, τ₂)` of `Y`-perfect complexes and maps `Rf_* ω_j ⟶ 𝒪_Y`, as in a relative
dualizing complex (Stacks 0E5X), and let `g' ≫ f = f' ≫ g` be a cartesian square. A morphism
of pairs over `Y'` is a map `φ : L(g')^* ω₁ ⟶ L(g')^* ω₂` compatible with the base changed traces
(Stacks 0E6C). Over an affine `Y'` over which both pairs are `(a'(𝒪_{Y'}), Tr)` there is exactly
one, and it is an isomorphism; morphisms of pairs pull back along further cartesian squares; and
a morphism `ω₁ ⟶ ω₂` is compatible with the traces as soon as it is so after base change to the
affine étale charts of `Y`, provided `Rf_* ω₁` lies in `D^{≤ 0}`.

## Main results

* `AlgebraicGeometry.Space.RelativeDualizingPair.existsUnique_baseChange_hom`.
* `AlgebraicGeometry.Space.RelativeDualizingPair.isIso_of_baseChange_hom`.
* `AlgebraicGeometry.Space.RelativeDualizingPair.baseChange_hom`.
* `AlgebraicGeometry.Space.RelativeDualizingPair.baseChange_hom_of_isPullback`.
* `AlgebraicGeometry.Space.RelativeDualizingPair.hom_of_forall_baseChange_hom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

/-- The structure sheaf of an algebraic space lies in `D^{≥ 0}`. -/
theorem isGE_derivedStructureSheaf (Y : AlgebraicSpaces B S hS) :
    (derivedStructureSheaf B S hS Y.1 Y.2).obj.IsGE 0 := by
  change ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj _).IsGE 0
  infer_instance

namespace RelativeDualizingPair

section Aux

variable {C : Type*} [Category* C]

/-- The diagram chase behind `map_comp_baseChangeTrace`, in an arbitrary category. -/
theorem hom_comp_trace_aux {P Q R T U V : C} {a : P ⟶ Q} {b₁ : P ⟶ R} {b₂ : Q ⟶ T}
    {x : R ⟶ T} {t₂ : T ⟶ U} {s₂ : Q ⟶ V} {u : V ⟶ U} {c : P ⟶ V}
    (hn : a ≫ b₂ = b₁ ≫ x) (h2 : b₂ ≫ t₂ = s₂ ≫ u) (hc : c = a ≫ s₂) :
    b₁ ≫ x ≫ t₂ = c ≫ u := by
  rw [← reassoc_of% hn, h2, hc, Category.assoc]

/-- Cancelling an isomorphism on the left, with the isomorphism hypothesis passed explicitly. -/
theorem cancel_iso_aux {P Q R : C} {b : P ⟶ Q} (hb : IsIso b) {x y : Q ⟶ R}
    (h : b ≫ x = b ≫ y) : x = y := by
  have := hb
  exact (cancel_epi b).1 h

/-- The diagram chase behind `baseChange_hom`, in an arbitrary category. -/
theorem baseChange_hom_aux {P Q R U V : C} {b₁ : P ⟶ Q} (hb : IsIso b₁) {x : Q ⟶ R}
    {t₂ : R ⟶ U} {t₁ : Q ⟶ U} {c c₁ : P ⟶ V} {u : V ⟶ U}
    (h1 : b₁ ≫ x ≫ t₂ = c ≫ u) (hc : c = c₁) (h3 : b₁ ≫ t₁ = c₁ ≫ u) : x ≫ t₂ = t₁ :=
  cancel_iso_aux hb (h1.trans ((eq_whisker hc u).trans h3.symm))

/-- Morphisms into a common target through a functor and a fixed map, in an arbitrary
category: `F φ ≫ t₂ = t₁` exactly when `φ ≫ e₂ = e₁`, if `t_j = F e_j ≫ T` and `a ↦ F a ≫ T` is
injective. -/
theorem map_comp_eq_iff_aux {D : Type*} [Category* D] (F : C ⥤ D) {P P' Q : C} {U : D}
    {e₁ : P ⟶ Q} {e₂ : P' ⟶ Q} {T : F.obj Q ⟶ U} {t₁ : F.obj P ⟶ U} {t₂ : F.obj P' ⟶ U}
    (h₁ : t₁ = F.map e₁ ≫ T) (h₂ : t₂ = F.map e₂ ≫ T)
    (inj : ∀ a b : P ⟶ Q, F.map a ≫ T = F.map b ≫ T → a = b) (φ : P ⟶ P') :
    F.map φ ≫ t₂ = t₁ ↔ φ ≫ e₂ = e₁ := by
  subst h₁ h₂
  exact ⟨fun h => inj _ _ (by rwa [Functor.map_comp, Category.assoc]),
    fun h => by rw [← h, Functor.map_comp, Category.assoc]⟩

/-- The last step of `baseChange_baseChangeTrace`, in an arbitrary category. -/
theorem baseChange_baseChangeTrace_aux {P Q R U V : C} {b : P ⟶ Q} (hb : IsIso b)
    {T : Q ⟶ U} {y z : P ⟶ U} {m : Q ⟶ R} {n : R ⟶ V} {a : V ⟶ U}
    (h1 : b ≫ T = y) (hy : y = z) (key : z = b ≫ m ≫ n ≫ 𝟙 V ≫ a) : T = m ≫ n ≫ a := by
  exact cancel_iso_aux hb (by rw [h1, hy, key, Category.id_comp])

/-- The diagram chase behind `baseChange_hom_paste`, in an arbitrary category. -/
theorem baseChange_hom_paste_aux {D : Type*} [Category* D] (F : C ⥤ D) {P P' Q Q' : C}
    {U V : D} {a : U ⟶ V} (ha : IsIso a) {c₁ : P ⟶ Q} {c₁i : Q ⟶ P} (hc₁ : c₁i ≫ c₁ = 𝟙 Q)
    {c₂ : P' ⟶ Q'} {x : P ⟶ P'} {t₁ : F.obj Q ⟶ U} {t₂ : F.obj Q' ⟶ U} {T₁ : F.obj P ⟶ V}
    {T₂ : F.obj P' ⟶ V} (h₁ : T₁ = F.map c₁ ≫ t₁ ≫ a) (h₂ : T₂ = F.map c₂ ≫ t₂ ≫ a)
    (hR : F.map x ≫ T₂ = T₁) : F.map (c₁i ≫ x ≫ c₂) ≫ t₂ = t₁ := by
  have := ha
  rw [← cancel_mono a]
  subst h₁ h₂
  simp only [Functor.map_comp, Category.assoc]
  rw [hR, ← Functor.map_comp_assoc, hc₁, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The diagram chase behind `hom_of_forall_baseChange_hom`, in an arbitrary category. -/
theorem hom_of_forall_aux {P Q R U V : C} {b : P ⟶ Q} {x : Q ⟶ R} {t₂ : R ⟶ U} {t₁ : Q ⟶ U}
    {c c' : P ⟶ V} {u : V ⟶ U} (hu : IsIso u) (h1 : b ≫ x ≫ t₂ = c ≫ u) (hx : x ≫ t₂ = t₁)
    (h3 : b ≫ t₁ = c' ≫ u) : c = c' := by
  have := hu
  rw [← cancel_mono u, ← h1, hx, h3]

end Aux

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}
  (D₁ D₂ : RelativeDualizingPair f hfl hfp)
  {X' Y' : AlgebraicSpaces B S hS} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g)

/-- The base change of `Rf_* φ ≫ τ₂` for a morphism `φ : ω₁ ⟶ ω₂`, read through the base change
map of `ω₁`, is `Rf'_* L(g')^* φ` followed by the base changed trace of `ω₂`. -/
theorem map_comp_baseChangeTrace (φ : D₁.ω ⟶ D₂.ω) :
    smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w D₁.ω ≫
        (derivedModulePushforward B S hS f').map
          ((smallEtaleDerivedModulePullback B S hS g').map φ) ≫ D₂.baseChangeTrace sq =
      (smallEtaleDerivedModulePullback B S hS g).map
          ((derivedModulePushforward B S hS f).map φ ≫ D₂.τ) ≫
        (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g).hom :=
  hom_comp_trace_aux (smallEtaleDerivedModuleBaseChangeMap_naturality B S hS f g f' g' sq.w φ)
    (D₂.smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace sq) (Functor.map_comp _ _ _)

/-- **Morphisms of pairs pull back**: if `φ : ω₁ ⟶ ω₂` is compatible with the traces, then
`L(g')^* φ` is compatible with the base changed traces. -/
theorem baseChange_hom (φ : D₁.ω ⟶ D₂.ω)
    (hφ : (derivedModulePushforward B S hS f).map φ ≫ D₂.τ = D₁.τ) :
    (derivedModulePushforward B S hS f').map ((smallEtaleDerivedModulePullback B S hS g').map φ) ≫
        D₂.baseChangeTrace sq = D₁.baseChangeTrace sq :=
  baseChange_hom_aux (D₁.isIso_smallEtaleDerivedBaseChangeMap sq)
    (map_comp_baseChangeTrace D₁ D₂ sq φ)
    (congrArg (smallEtaleDerivedModulePullback B S hS g).map hφ)
    (D₁.smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace sq)

/-- Over an affine `Y'` the base changed trace is the trace map, read through an isomorphism
`L(g')^* ω ≅ a'(𝒪_{Y'})`. -/
theorem exists_baseChangeTrace_eq (D : RelativeDualizingPair f hfl hfp)
    (hY' : IsAffineSpace B S hS Y'.1) (hD : IsAffineBaseChangePair hZ sq hfp hY' D.ω D.τ) :
    ∃ e : (smallEtaleDerivedModulePullback B S hS g').obj D.ω ≅
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj,
      D.baseChangeTrace sq =
        (derivedModulePushforward B S hS f').map e.hom ≫ affineBaseChangeTrace hZ sq hfp hY' := by
  obtain ⟨e, he⟩ := hD
  exact ⟨e, cancel_iso_aux (D.isIso_smallEtaleDerivedBaseChangeMap sq)
    ((D.smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace sq).trans he)⟩

/-- Over an affine `Y'`, morphisms of base changed pairs are the morphisms `φ` with
`φ ≫ e₂ = e₁` for the isomorphisms `e_j : L(g')^* ω_j ≅ a'(𝒪_{Y'})` of pairs. -/
theorem exists_baseChange_hom_iff (hY' : IsAffineSpace B S hS Y'.1)
    (h₁ : IsAffineBaseChangePair hZ sq hfp hY' D₁.ω D₁.τ)
    (h₂ : IsAffineBaseChangePair hZ sq hfp hY' D₂.ω D₂.τ) :
    ∃ (e₁ : (smallEtaleDerivedModulePullback B S hS g').obj D₁.ω ≅
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj)
      (e₂ : (smallEtaleDerivedModulePullback B S hS g').obj D₂.ω ≅
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj),
      ∀ φ : (smallEtaleDerivedModulePullback B S hS g').obj D₁.ω ⟶
          (smallEtaleDerivedModulePullback B S hS g').obj D₂.ω,
        (derivedModulePushforward B S hS f').map φ ≫ D₂.baseChangeTrace sq =
            D₁.baseChangeTrace sq ↔ φ ≫ e₂.hom = e₁.hom := by
  obtain ⟨e₁, h₁⟩ := D₁.exists_baseChangeTrace_eq sq hY' h₁
  obtain ⟨e₂, h₂⟩ := D₂.exists_baseChangeTrace_eq sq hY' h₂
  exact ⟨e₁, e₂, map_comp_eq_iff_aux (derivedModulePushforward B S hS f') h₁ h₂
    (fun a b h => affineBaseChangeTrace_comp_injective hZ sq hfp hY'
      ⟨_, (D₁.baseChange sq).qcohDerived_ω⟩ h)⟩

/-- **Over an affine base there is a unique morphism of base changed pairs** (the uniqueness in
the discussion after Stacks 0E5X): it is `e₁ ≫ e₂⁻¹`. -/
theorem existsUnique_baseChange_hom (hY' : IsAffineSpace B S hS Y'.1)
    (h₁ : IsAffineBaseChangePair hZ sq hfp hY' D₁.ω D₁.τ)
    (h₂ : IsAffineBaseChangePair hZ sq hfp hY' D₂.ω D₂.τ) :
    ∃! φ : (smallEtaleDerivedModulePullback B S hS g').obj D₁.ω ⟶
        (smallEtaleDerivedModulePullback B S hS g').obj D₂.ω,
      (derivedModulePushforward B S hS f').map φ ≫ D₂.baseChangeTrace sq =
        D₁.baseChangeTrace sq := by
  obtain ⟨e₁, e₂, key⟩ := exists_baseChange_hom_iff D₁ D₂ sq hY' h₁ h₂
  exact ⟨e₁.hom ≫ e₂.inv, (key _).2 ((Category.assoc _ _ _).trans
    ((whisker_eq e₁.hom e₂.inv_hom_id).trans (Category.comp_id _))),
    fun φ hφ => (Iso.eq_comp_inv e₂).2 ((key φ).1 hφ)⟩

/-- Over an affine base a morphism of base changed pairs is an isomorphism. -/
theorem isIso_of_baseChange_hom (hY' : IsAffineSpace B S hS Y'.1)
    (h₁ : IsAffineBaseChangePair hZ sq hfp hY' D₁.ω D₁.τ)
    (h₂ : IsAffineBaseChangePair hZ sq hfp hY' D₂.ω D₂.τ)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj D₁.ω ⟶
      (smallEtaleDerivedModulePullback B S hS g').obj D₂.ω)
    (hφ : (derivedModulePushforward B S hS f').map φ ≫ D₂.baseChangeTrace sq =
      D₁.baseChangeTrace sq) : IsIso φ := by
  obtain ⟨e₁, e₂, key⟩ := exists_baseChange_hom_iff D₁ D₂ sq hY' h₁ h₂
  obtain rfl : φ = (e₁ ≪≫ e₂.symm).hom := (Iso.eq_comp_inv e₂).2 ((key φ).1 hφ)
  exact Iso.isIso_hom _

section Paste

variable {X'' Y'' : AlgebraicSpaces B S hS} {f'' : X'' ⟶ Y''} {h : Y'' ⟶ Y'} {g'' : X'' ⟶ X'}
  (sq₂ : IsPullback g'' f'' f' h)

/-- **Base change of the base changed trace**: the trace of `((ω, τ)|_{X'})|_{X''}` is that of
`(ω, τ)|_{X''}` through `L(g'')^* L(g')^* ≅ L(g'' ≫ g')^*`, up to an automorphism of
`𝒪_{Y''}` which does not depend on `(ω, τ)`. -/
theorem baseChange_baseChangeTrace (D : RelativeDualizingPair f hfl hfp) :
    (D.baseChange sq).baseChangeTrace sq₂ =
      (derivedModulePushforward B S hS f'').map
          ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').hom.app D.ω) ≫
        D.baseChangeTrace (sq₂.paste_horiz sq) ≫
          (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) (h ≫ g)).inv ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS h g).inv.app
              (derivedStructureSheaf B S hS Y.1 Y.2).obj ≫
              (smallEtaleDerivedModulePullback B S hS h).map
                (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g).hom ≫
                (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) h).hom := by
  let β := @asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w D.ω)
    (D.isIso_smallEtaleDerivedBaseChangeMap sq)
  let c := smallEtaleDerivedModulePullbackCompIso B S hS h g
  let ug := smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g
  let uh := smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) h
  let uhg := smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) (h ≫ g)
  let Lh := smallEtaleDerivedModulePullback B S hS h
  have key := relativeDualizingPair_paste_aux
    (C := DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y'')))
    (Lh.map β.hom) (Lh.map β.inv) (Lh.mapIso β).inv_hom_id
    (c.hom.app ((derivedModulePushforward B S hS f).obj D.ω))
    (c.inv.app ((derivedModulePushforward B S hS f).obj D.ω))
    (c.hom_inv_id_app _)
    (Lh.map ((smallEtaleDerivedModulePullback B S hS g).map D.τ)) (Lh.map ug.hom) uh.hom
    ((smallEtaleDerivedModulePullback B S hS (h ≫ g)).map D.τ)
    (c.inv.app (derivedStructureSheaf B S hS Y.1 Y.2).obj) uhg.hom uhg.inv uhg.hom_inv_id
    (smallEtaleDerivedModuleBaseChangeMap B S hS f' h f'' g'' sq₂.w
      ((smallEtaleDerivedModulePullback B S hS g').obj D.ω))
    ((derivedModulePushforward B S hS f'').map
      ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').hom.app D.ω))
    (smallEtaleDerivedModuleBaseChangeMap B S hS f (h ≫ g) f'' (g'' ≫ g') (sq₂.paste_horiz sq).w
      D.ω)
    (D.baseChangeTrace (sq₂.paste_horiz sq)) (𝟙 _)
    (smallEtaleDerivedBaseChangeMap_horizontal B S hS f f' f'' g' g'' g h sq.w sq₂.w D.ω)
    ((D.smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace (sq₂.paste_horiz sq)).symm.trans
      (whisker_eq _ (Category.comp_id _).symm))
    (c.inv.naturality D.τ)
  exact baseChange_baseChangeTrace_aux ((D.baseChange sq).isIso_smallEtaleDerivedBaseChangeMap sq₂)
    ((D.baseChange sq).smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace sq₂)
    ((Functor.map_comp_assoc Lh _ _ _).trans (whisker_eq _ (Functor.map_comp_assoc Lh _ _ _)))
    key

/-- **Morphisms of pairs pull back along a further cartesian square**: if `φ` is a morphism of
the pairs base changed to `X'`, then `L(g'')^* φ`, read through `L(g'')^* L(g')^* ≅ L(g'' ≫ g')^*`,
is a morphism of the pairs base changed to `X''`. -/
theorem baseChange_hom_paste
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj D₁.ω ⟶
      (smallEtaleDerivedModulePullback B S hS g').obj D₂.ω)
    (hφ : (derivedModulePushforward B S hS f').map φ ≫ D₂.baseChangeTrace sq =
      D₁.baseChangeTrace sq) :
    (derivedModulePushforward B S hS f'').map
        ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').inv.app D₁.ω ≫
          (smallEtaleDerivedModulePullback B S hS g'').map φ ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS g'' g').hom.app D₂.ω) ≫
        D₂.baseChangeTrace (sq₂.paste_horiz sq) = D₁.baseChangeTrace (sq₂.paste_horiz sq) :=
  baseChange_hom_paste_aux (derivedModulePushforward B S hS f'') (Iso.isIso_hom
      ((smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) (h ≫ g)).symm ≪≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS h g).app
          (derivedStructureSheaf B S hS Y.1 Y.2).obj).symm ≪≫
        (smallEtaleDerivedModulePullback B S hS h).mapIso
          (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g) ≪≫
        smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) h))
    ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').inv_hom_id_app D₁.ω)
    (baseChange_baseChangeTrace sq sq₂ D₁) (baseChange_baseChangeTrace sq sq₂ D₂)
    (baseChange_hom (D₁.baseChange sq) (D₂.baseChange sq) sq₂ φ hφ)

end Paste

/-- **Morphisms of pairs pull back along a morphism of cartesian squares.** Let `sq₁` be a
cartesian square over `g₁ : Y₁ ⟶ Y` mapping to `sq` by `m : X₁ ⟶ X'` over `n : Y₁ ⟶ Y'`. If `φ` is
a morphism of the pairs base changed to `X'`, then `L m^* φ`, read through
`L m^* L(g')^* ≅ L(g'₁)^*`, is a morphism of the pairs base changed to `X₁`. -/
theorem baseChange_hom_of_isPullback {X₁ Y₁ : AlgebraicSpaces B S hS} {f₁ : X₁ ⟶ Y₁}
    {g₁ : Y₁ ⟶ Y} {g'₁ : X₁ ⟶ X} (sq₁ : IsPullback g'₁ f₁ f g₁) (m : X₁ ⟶ X') (n : Y₁ ⟶ Y')
    (hm : m ≫ g' = g'₁) (hn : n ≫ g = g₁) (hw : m ≫ f' = f₁ ≫ n)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj D₁.ω ⟶
      (smallEtaleDerivedModulePullback B S hS g').obj D₂.ω)
    (hφ : (derivedModulePushforward B S hS f').map φ ≫ D₂.baseChangeTrace sq =
      D₁.baseChangeTrace sq) :
    (derivedModulePushforward B S hS f₁).map
        ((smallEtaleDerivedModulePullbackCompIso B S hS m g' ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hm).inv.app D₁.ω ≫
          (smallEtaleDerivedModulePullback B S hS m).map φ ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS m g' ≪≫
              smallEtaleDerivedModulePullbackCongr B S hS hm).hom.app D₂.ω) ≫
        D₂.baseChangeTrace sq₁ = D₁.baseChangeTrace sq₁ := by
  subst hm hn
  simpa only [smallEtaleDerivedModulePullbackCongr, eqToIso_refl, Iso.trans_refl] using
    baseChange_hom_paste D₁ D₂ sq (IsPullback.of_right sq₁ hw sq) φ hφ

/-- **Compatibility with the traces is étale local on `Y`.** If `Rf_* ω₁` lies in `D^{≤ 0}` and
the base change of `φ : ω₁ ⟶ ω₂` to `X ×_Y V` is a morphism of pairs for every affine étale chart
`V` of `Y`, then `Rf_* φ ≫ τ₂ = τ₁`. -/
theorem hom_of_forall_baseChange_hom
    (hle : ((derivedModulePushforward B S hS f).obj D₁.ω).IsLE 0) (φ : D₁.ω ⟶ D₂.ω)
    (h : ∀ V : {U : SmallEtale B S hS Y.1 // IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS Y.1).obj U))},
      (derivedModulePushforward B S hS (pullback.snd f (chartToSpace B S hS Y V.1))).map
          ((smallEtaleDerivedModulePullback B S hS
            (pullback.fst f (chartToSpace B S hS Y V.1))).map φ) ≫
        D₂.baseChangeTrace (IsPullback.of_hasPullback f (chartToSpace B S hS Y V.1)) =
      D₁.baseChangeTrace (IsPullback.of_hasPullback f (chartToSpace B S hS Y V.1))) :
    (derivedModulePushforward B S hS f).map φ ≫ D₂.τ = D₁.τ := by
  have hKL := isGE_smallEtaleDerivedSheafHom_of_isLE_of_isGE B S hS Y
    ((derivedModulePushforward B S hS f).obj D₁.ω) (derivedStructureSheaf B S hS Y.1 Y.2).obj
    0 0 hle (isGE_derivedStructureSheaf Y)
  rw [sub_self] at hKL
  refine eq_of_smallEtaleDerivedModulePullback_map_eq B S hS hKL
    (SmallEtale.coversTop_affineCharts B S hS Y.1) fun V => ?_
  have sqV := IsPullback.of_hasPullback f (chartToSpace B S hS Y V.1)
  exact hom_of_forall_aux (Iso.isIso_hom (smallEtaleDerivedModulePullbackUnitIso (B := B)
      (S := S) (hS := hS) (chartToSpace B S hS Y V.1)))
    (map_comp_baseChangeTrace D₁ D₂ sqV φ) (h V)
    (D₁.smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace sqV)

end RelativeDualizingPair

end AlgebraicGeometry.Space

end
