module

public import StacksFrontier.AlgebraicGeometry.Quot.TrivializationPresheaf
public import StacksFrontier.AlgebraicGeometry.Quot.StructureModuleEndomorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.MultiplicativeGroupChart
public import StacksFrontier.AlgebraicGeometry.Quot.InvertibleModuleTrivializingChart
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource

/-!
# The trivialisations of an invertible module form a `𝔾_m`-torsor

Let `N` be an invertible module on a scheme `U` of the big fppf site of `S`.  The trivialisations
`𝒪_V ≅ (V ⟶ U)^*N` over the schemes `V` over `U` form a presheaf on the big fppf site of `U`
(`AlgebraicGeometry.Space.trivializationsSliceFunctor`, shrunk to `Type u` as
`AlgebraicGeometry.Space.trivializationsSitePresheaf`).  Over an étale chart trivialising `N`, a
trivialisation is the same as a unit, so the presheaf is represented there by the multiplicative
group chart `𝔾_m` over the chart
(`AlgebraicGeometry.Space.isPullback_torsorChartToTrivializations`).
Effective descent of affine morphisms along surjective étale coverings then shows that, as soon as
the presheaf is a sheaf, it is represented by a scheme smooth, surjective and affine over `U`
(`AlgebraicGeometry.Space.exists_iso_yoneda_trivializationsSitePresheaf_of_isSheaf`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Iso

/-- Precomposing with an automorphism `u` sends `β` to `α` exactly when `u = α ≪≫ β⁻¹`. -/
theorem trans_eq_iff_eq_trans_symm {C : Type*} [Category* C] {X Y : C} (u : X ≅ X)
    (α β : X ≅ Y) : u ≪≫ β = α ↔ u = α ≪≫ β.symm := by
  constructor
  · rintro rfl
    rw [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  · rintro rfl
    rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

end CategoryTheory.Iso

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section TransLeft

variable {V W Z : AlgebraicSpaces B S hS} (N : Modules.{u, u} B S hS Z.1 Z.2)

/-- The inverse image of a trivialisation twisted by an automorphism of `𝒪` is the inverse image
of the trivialisation twisted by the conjugated automorphism. -/
theorem trivializationPullback_trans_left {a : V ⟶ Z} {b : W ⟶ Z} (q : W ⟶ V)
    (h : q ≫ a = b) (e : structureModule V ≅ structureModule V)
    (α : structureModule V ≅ (modulePullback B S hS a).obj N) :
    trivializationPullback N q h (e ≪≫ α) =
      (structureModulePullbackIso q ≪≫ (modulePullback B S hS q).mapIso e ≪≫
        (structureModulePullbackIso q).symm) ≪≫ trivializationPullback N q h α := by
  ext1
  simp only [trivializationPullback, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

end TransLeft

/-- The conjugate of the automorphism of `𝒪` attached to a unit is the automorphism attached to
its inverse image. -/
theorem conj_structureModuleAutEquiv_symm {V V' : BigFppfOver B S hS} (g : V' ⟶ V)
    (a : (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))ˣ) :
    structureModulePullbackIso ((schemeSpaceFunctor B S hS).map g) ≪≫
        (modulePullback B S hS ((schemeSpaceFunctor B S hS).map g)).mapIso
          ((structureModuleAutEquiv V).symm a) ≪≫
        (structureModulePullbackIso ((schemeSpaceFunctor B S hS).map g)).symm =
      (structureModuleAutEquiv V').symm
        (Units.map ((BigFppfOver.toScheme B S hS).map g).appTop.hom.toMonoidHom a) := by
  rw [Equiv.eq_symm_apply, structureModuleAutEquiv_conj, Equiv.apply_symm_apply]

/-- The inverse image of a trivialisation twisted by the unit `a` is the inverse image of the
trivialisation twisted by the inverse image of `a`. -/
theorem trivializationPullback_autEquiv {V V' : BigFppfOver B S hS} {Z : AlgebraicSpaces B S hS}
    (N : Modules.{u, u} B S hS Z.1 Z.2) {a : (schemeSpaceFunctor B S hS).obj V ⟶ Z}
    {b : (schemeSpaceFunctor B S hS).obj V' ⟶ Z} (g : V' ⟶ V)
    (h : (schemeSpaceFunctor B S hS).map g ≫ a = b)
    (x : (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))ˣ)
    (α : structureModule ((schemeSpaceFunctor B S hS).obj V) ≅ (modulePullback B S hS a).obj N) :
    trivializationPullback N ((schemeSpaceFunctor B S hS).map g) h
        ((structureModuleAutEquiv V).symm x ≪≫ α) =
      (structureModuleAutEquiv V').symm
          (Units.map ((BigFppfOver.toScheme B S hS).map g).appTop.hom.toMonoidHom x) ≪≫
        trivializationPullback N ((schemeSpaceFunctor B S hS).map g) h α := by
  rw [trivializationPullback_trans_left, conj_structureModuleAutEquiv_symm]

/-- The scheme morphism underlying the image of a morphism of the site of `U` in the site of
`S` is the scheme morphism underlying the original. -/
theorem toScheme_map_iteratedSliceBackward_map_left (U : BigFppfOver B S hS)
    {V V' : BigFppfOver B U.left.1 U.left.2} (k : V ⟶ V') :
    (BigFppfOver.toScheme B S hS).map (U.iteratedSliceBackward.map k).left =
      (BigFppfOver.toScheme B U.left.1 U.left.2).map k :=
  rfl

section Slice

variable (U : BigFppfOver B S hS)
  (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
    ((schemeSpaceFunctor B S hS).obj U).2)

/-- The trivialisations of `N`, as a presheaf on the big fppf site of `U`: over `V ⟶ U` the
trivialisations `𝒪_V ≅ (V ⟶ U)^*N`. -/
def trivializationsSliceFunctor : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type (u + 1) where
  obj V := structureModule
      ((schemeSpaceFunctor B S hS).obj (U.iteratedSliceBackward.obj V.unop).left) ≅
    (modulePullback B S hS ((schemeSpaceFunctor B S hS).map
      (U.iteratedSliceBackward.obj V.unop).hom)).obj N
  map {V₁ V₂} k := TypeCat.ofHom fun α ↦
    trivializationPullback N
      ((schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.map k.unop).left)
      (by rw [← Functor.map_comp, Over.w (U.iteratedSliceBackward.map k.unop)]) α
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro α
    exact (trivializationPullback_congr N
      (by rw [unop_id, CategoryTheory.Functor.map_id, Over.id_left,
        CategoryTheory.Functor.map_id]) _
      (by rw [Category.id_comp]) α).trans (trivializationPullback_id N _ α)
  map_comp {V₁ V₂ V₃} f g := by
    apply ConcreteCategory.hom_ext
    intro α
    exact (trivializationPullback_congr N
      (by rw [unop_comp, CategoryTheory.Functor.map_comp, Over.comp_left,
        CategoryTheory.Functor.map_comp]) _
      (by rw [Category.assoc, ← Functor.map_comp, Over.w (U.iteratedSliceBackward.map f.unop),
        ← Functor.map_comp, Over.w (U.iteratedSliceBackward.map g.unop)]) α).trans
      (trivializationPullback_comp N _ _ _ _ _ α)

/-- The trivialisations of `N` over a scheme over `U` form a `u`-small type. -/
instance (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) :
    Small.{u} ((trivializationsSliceFunctor U N).obj T) :=
  small_structureModule_iso _ _

/-- The trivialisations of `N`, as a presheaf on the big fppf site of `U` with values in the
universe of the site. -/
def trivializationsSitePresheaf : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u :=
  shrinkSitePresheaf (trivializationsSliceFunctor U N)

end Slice

section Chart

variable (U : BigFppfOver B S hS)
  (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
    ((schemeSpaceFunctor B S hS).obj U).2)
  {c₀ : BigFppfOver B S hS} (q₀ : c₀ ⟶ U)

/-- A scheme `c₀` over `U`, read as an object of the big fppf site of `U`. -/
abbrev sliceChart : BigFppfOver B U.left.1 U.left.2 := Over.mk q₀.left

/-- The scheme over `U` attached to `sliceChart U q₀` is `c₀`. -/
def sliceChartComparison : (U.iteratedSliceBackward.obj (sliceChart U q₀)).left ⟶ c₀ :=
  Over.homMk (𝟙 c₀.left) (by
    change 𝟙 c₀.left ≫ c₀.hom = q₀.left ≫ U.hom
    rw [Category.id_comp]
    exact (Over.w q₀).symm)

/-- The comparison of the slice charts is compatible with composition. -/
@[reassoc]
theorem sliceChartComparison_comp :
    sliceChartComparison U q₀ ≫ q₀ = (U.iteratedSliceBackward.obj (sliceChart U q₀)).hom := by
  apply Over.OverMorphism.ext
  show 𝟙 c₀.left ≫ q₀.left = q₀.left
  exact Category.id_comp _

/-- A trivialisation of `q₀^*N`, read at `sliceChart U q₀`. -/
def sliceChartTrivialization
    (τ₀ : structureModule ((schemeSpaceFunctor B S hS).obj c₀) ≅
      (modulePullback B S hS ((schemeSpaceFunctor B S hS).map q₀)).obj N) :
    (trivializationsSliceFunctor U N).obj (op (sliceChart U q₀)) :=
  trivializationPullback N ((schemeSpaceFunctor B S hS).map (sliceChartComparison U q₀))
    (by rw [← Functor.map_comp, sliceChartComparison_comp]) τ₀

/-- The `𝐆_m`-torsor chart over `sliceChart U q₀`. -/
abbrev torsorChart : BigFppfOver B U.left.1 U.left.2 :=
  multiplicativeGroupChart (sliceChart U q₀)

/-- **The universal trivialisation over `𝐆_m × c`**: the pulled-back trivialisation twisted by
the coordinate. -/
def universalTrivialization
    (τ₀ : structureModule ((schemeSpaceFunctor B S hS).obj c₀) ≅
      (modulePullback B S hS ((schemeSpaceFunctor B S hS).map q₀)).obj N) :
    (trivializationsSliceFunctor U N).obj (op (torsorChart U q₀)) :=
  (structureModuleAutEquiv (U.iteratedSliceBackward.obj (torsorChart U q₀)).left).symm
      (multiplicativeGroupChartCoordinate (sliceChart U q₀)) ≪≫
    (trivializationsSliceFunctor U N).map (multiplicativeGroupChartHom (sliceChart U q₀)).op
      (sliceChartTrivialization U N q₀ τ₀)

variable (τ₀ : structureModule ((schemeSpaceFunctor B S hS).obj c₀) ≅
      (modulePullback B S hS ((schemeSpaceFunctor B S hS).map q₀)).obj N)

/-- Restriction in the presheaf of trivialisations is the inverse image of trivialisations. -/
theorem trivializationsSliceFunctor_map_apply {V V' : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ}
    (k : V ⟶ V') (x : (trivializationsSliceFunctor U N).obj V) :
    (trivializationsSliceFunctor U N).map k x =
      trivializationPullback N
        ((schemeSpaceFunctor B S hS).map (U.iteratedSliceBackward.map k.unop).left)
        (by rw [← CategoryTheory.Functor.map_comp, Over.w (U.iteratedSliceBackward.map k.unop)])
        x := by
  dsimp only [trivializationsSliceFunctor]
  exact TypeCat.ofHom_apply _ x

/-- The restriction of the universal trivialisation along `k : V ⟶ 𝐆_m × c` is the restriction
of the chart trivialisation along `k ≫ π`, twisted by the unit `k^*t`. -/
theorem map_universalTrivialization {V : BigFppfOver B U.left.1 U.left.2}
    (k : V ⟶ torsorChart U q₀) :
    (trivializationsSliceFunctor U N).map k.op (universalTrivialization U N q₀ τ₀) =
      (structureModuleAutEquiv (U.iteratedSliceBackward.obj V).left).symm
          (Units.map ((BigFppfOver.toScheme B S hS).map
            (U.iteratedSliceBackward.map k).left).appTop.hom.toMonoidHom
            (multiplicativeGroupChartCoordinate (sliceChart U q₀))) ≪≫
        (trivializationsSliceFunctor U N).map (k ≫ multiplicativeGroupChartHom _).op
          (sliceChartTrivialization U N q₀ τ₀) := by
  have hcomp : (trivializationsSliceFunctor U N).map (k ≫ multiplicativeGroupChartHom _).op
      (sliceChartTrivialization U N q₀ τ₀) = (trivializationsSliceFunctor U N).map k.op
        ((trivializationsSliceFunctor U N).map (multiplicativeGroupChartHom _).op
          (sliceChartTrivialization U N q₀ τ₀)) := by
    rw [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply]
  rw [hcomp, universalTrivialization]
  refine (trivializationsSliceFunctor_map_apply U N k.op _).trans ?_
  refine (trivializationPullback_autEquiv N _ _ _ _).trans ?_
  rw [trivializationsSliceFunctor_map_apply U N k.op]
  simp only [Quiver.Hom.unop_op, Opposite.unop_op]

/-- **The universal property of the universal trivialisation.**  Every trivialisation over a
scheme `V` with a morphism `g : V ⟶ c` is the restriction of the universal trivialisation along a
unique lift of `g` to `𝐆_m × c`. -/
theorem existsUnique_lift_universalTrivialization {V : BigFppfOver B U.left.1 U.left.2}
    (g : V ⟶ sliceChart U q₀) (α : (trivializationsSliceFunctor U N).obj (op V)) :
    ∃! k : V ⟶ torsorChart U q₀, k ≫ multiplicativeGroupChartHom (sliceChart U q₀) = g ∧
      (trivializationsSliceFunctor U N).map k.op (universalTrivialization U N q₀ τ₀) = α := by
  obtain ⟨a, ha⟩ : ∃ a, a = structureModuleAutEquiv (U.iteratedSliceBackward.obj V).left
      (α ≪≫ ((trivializationsSliceFunctor U N).map g.op
        (sliceChartTrivialization U N q₀ τ₀)).symm) :=
    ⟨_, rfl⟩
  have key : ∀ k : V ⟶ torsorChart U q₀, k ≫ multiplicativeGroupChartHom _ = g →
      ((trivializationsSliceFunctor U N).map k.op (universalTrivialization U N q₀ τ₀) = α ↔
        ((BigFppfOver.toScheme B U.left.1 U.left.2).map k).appTop
          (multiplicativeGroupChartCoordinate (sliceChart U q₀)).val = a.val) := by
    intro k hk
    rw [map_universalTrivialization, hk]
    refine (Iso.trans_eq_iff_eq_trans_symm _ _ _).trans ?_
    refine (Equiv.symm_apply_eq _).trans ?_
    rw [← ha, Units.ext_iff]
    exact Iff.rfl
  obtain ⟨k, ⟨hk1, hk2⟩, huniq⟩ := existsUnique_multiplicativeGroupChart_lift (sliceChart U q₀) g a
  exact ⟨k, ⟨hk1, (key k hk1).2 hk2⟩, fun k' ⟨h1, h2⟩ ↦ huniq k' ⟨h1, (key k' h1).1 h2⟩⟩

end Chart

section Square

variable (U : BigFppfOver B S hS)
  (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
    ((schemeSpaceFunctor B S hS).obj U).2)

/-- Restriction in the small presheaf of trivialisations, on a shrunk trivialisation. -/
theorem trivializationsSitePresheaf_map_equivShrink {V V' : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ}
    (k : V ⟶ V') (x : (trivializationsSliceFunctor U N).obj V) :
    (trivializationsSitePresheaf U N).map k (equivShrink _ x) =
      equivShrink _ ((trivializationsSliceFunctor U N).map k x) := by
  show equivShrink _ ((trivializationsSliceFunctor U N).map k
    ((equivShrink _).symm (equivShrink _ x))) = _
  rw [Equiv.symm_apply_apply]

/-- The sections of the small presheaf of trivialisations are the trivialisations. -/
def trivializationsSiteEquiv (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) :
    (trivializationsSitePresheaf U N).obj V ≃ (trivializationsSliceFunctor U N).obj V :=
  (equivShrink ((trivializationsSliceFunctor U N).obj V)).symm

/-- `AlgebraicGeometry.Space.trivializationsSiteEquiv` is compatible with restriction. -/
theorem trivializationsSiteEquiv_map {V V' : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ} (k : V ⟶ V')
    (x : (trivializationsSitePresheaf U N).obj V) :
    trivializationsSiteEquiv U N V' ((trivializationsSitePresheaf U N).map k x) =
      (trivializationsSliceFunctor U N).map k (trivializationsSiteEquiv U N V x) := by
  obtain ⟨y, rfl⟩ := (equivShrink ((trivializationsSliceFunctor U N).obj V)).surjective x
  exact (congrArg (equivShrink _).symm (trivializationsSitePresheaf_map_equivShrink U N k y)).trans
    ((Equiv.symm_apply_apply _ _).trans
      (congrArg _ (Equiv.symm_apply_apply _ _).symm))

/-- The final object `𝟙 : U ⟶ U` of the big fppf site of `U`. -/
abbrev sliceTerminal : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)

/-- The map from the presheaf of trivialisations to the final presheaf. -/
def trivializationsToTerminal :
    trivializationsSitePresheaf U N ⟶ yoneda.obj (sliceTerminal U) where
  app V := TypeCat.ofHom fun _ ↦ Over.mkIdTerminal.from V.unop
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun _ ↦ Over.mkIdTerminal.hom_ext _ _

variable {c₀ : BigFppfOver B S hS} (q₀ : c₀ ⟶ U)
  (τ₀ : structureModule ((schemeSpaceFunctor B S hS).obj c₀) ≅
      (modulePullback B S hS ((schemeSpaceFunctor B S hS).map q₀)).obj N)

/-- The morphism `h_{𝐆_m × c} ⟶ Isom(𝒪, N)` classifying the universal trivialisation. -/
def torsorChartToTrivializations :
    yoneda.obj (torsorChart U q₀) ⟶ trivializationsSitePresheaf U N :=
  yonedaEquiv.symm (show (trivializationsSitePresheaf U N).obj (op (torsorChart U q₀)) from
    equivShrink _ (universalTrivialization U N q₀ τ₀))

/-- The components of `AlgebraicGeometry.Space.torsorChartToTrivializations`. -/
theorem torsorChartToTrivializations_app {V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ}
    (k : V.unop ⟶ torsorChart U q₀) :
    (torsorChartToTrivializations U N q₀ τ₀).app V k =
      equivShrink _ ((trivializationsSliceFunctor U N).map k.op
        (universalTrivialization U N q₀ τ₀)) :=
  (yonedaEquiv_symm_app_apply _ V k).trans (trivializationsSitePresheaf_map_equivShrink U N k.op _)

/-- **The base change of `Isom(𝒪, N) ⟶ U` along `c ⟶ U` is `𝐆_m × c`**, for a chart `c` over
which `N` is trivial. -/
theorem isPullback_torsorChartToTrivializations :
    IsPullback (torsorChartToTrivializations U N q₀ τ₀)
      (yoneda.map (multiplicativeGroupChartHom (sliceChart U q₀)))
      (trivializationsToTerminal U N)
      (yoneda.map (Over.mkIdTerminal.from (sliceChart U q₀)) ≫ 𝟙 _) := by
  refine IsPullback.of_forall_isPullback_app fun V ↦ ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro _
    exact Over.mkIdTerminal.hom_ext _ _
  · rintro k k' ⟨h₁, h₂⟩
    rw [torsorChartToTrivializations_app, torsorChartToTrivializations_app] at h₁
    have hπ : k ≫ multiplicativeGroupChartHom (sliceChart U q₀) =
        k' ≫ multiplicativeGroupChartHom (sliceChart U q₀) := h₂
    obtain ⟨_, _, huniq⟩ := existsUnique_lift_universalTrivialization U N q₀ τ₀
      (k ≫ multiplicativeGroupChartHom (sliceChart U q₀))
      ((trivializationsSliceFunctor U N).map k.op (universalTrivialization U N q₀ τ₀))
    exact (huniq k ⟨rfl, rfl⟩).trans (huniq k' ⟨hπ.symm, ((equivShrink _).injective h₁).symm⟩).symm
  · intro x g _
    obtain ⟨k, ⟨hk1, hk2⟩, -⟩ := existsUnique_lift_universalTrivialization U N q₀ τ₀ g
      ((equivShrink _).symm x)
    refine ⟨k, ?_, hk1⟩
    rw [torsorChartToTrivializations_app, hk2]
    exact Equiv.apply_symm_apply (equivShrink _) x

end Square

section Representability

variable (U : BigFppfOver B S hS)
  (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
    ((schemeSpaceFunctor B S hS).obj U).2)

/-- **The trivialisations of an invertible module are represented by a scheme smooth, surjective
and affine over the base**, granted that they form an fppf sheaf. -/
theorem exists_iso_yoneda_trivializationsSitePresheaf_of_isSheaf
    (hN : IsInvertibleModule ((schemeSpaceFunctor B S hS).obj U) N)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B U.left.1 U.left.2)
      (trivializationsSitePresheaf U N)) :
    ∃ (W : BigFppfOver B U.left.1 U.left.2) (_ : trivializationsSitePresheaf U N ≅ yoneda.obj W),
      Smooth ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) ∧
      Surjective ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) ∧
      _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) := by
  obtain ⟨c₀, q₀, hsurj, het, ⟨τ₀⟩⟩ :=
    exists_surjective_etale_modulePullback_iso_structureModule U N hN
  set T₀ := sliceTerminal U
  set c := sliceChart U q₀
  set q : c ⟶ T₀ := Over.homMk q₀.left (by simp [c, T₀])
  set π := multiplicativeGroupChartHom c
  have hqs : Surjective ((BigFppfOver.toScheme B U.left.1 U.left.2).map q) := hsurj
  have hqe : Etale ((BigFppfOver.toScheme B U.left.1 U.left.2).map q) := het
  have hq : Over.mkIdTerminal.from c = q := Over.mkIdTerminal.hom_ext _ _
  have hpb := isPullback_torsorChartToTrivializations U N q₀ τ₀
  rw [hq] at hpb
  have hr : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B U.left.1 U.left.2)).presheaf (yoneda.map π) :=
    presheaf_yoneda_map_of_inverseImage B U.left.1 U.left.2
      _root_.AlgebraicGeometry.isAffineHom_isStableUnderBaseChange π
      (isAffineHom_multiplicativeGroupChartHom c)
  obtain ⟨hrep, hP⟩ := isEffectiveDescentAlongSurjectiveEtale_isAffineHom B U.left.1 U.left.2
    (trivializationsToTerminal U N) hX (BigFppfOver.isSheaf_yoneda_obj B U.left.1 U.left.2 T₀)
    (𝟙 _) q hqs hqe _ _ hpb hr
  obtain ⟨W, snd, fst, hW⟩ := hrep (𝟙 (yoneda.obj T₀))
  have hsnd : snd = Over.mkIdTerminal.from W := Over.mkIdTerminal.hom_ext _ _
  subst hsnd
  have hfst : IsIso fst := hW.isIso_fst_of_isIso
  let e : trivializationsSitePresheaf U N ≅ yoneda.obj W :=
    (asIso (pullback.fst (trivializationsToTerminal U N) (𝟙 (yoneda.obj T₀)))).symm ≪≫
      (asIso fst).symm
  refine ⟨W, e, ?_⟩
  have he : (trivializationsToTerminal U N) = e.hom ≫ yoneda.map (Over.mkIdTerminal.from W) := by
    ext V x
    exact Over.mkIdTerminal.hom_ext _ _
  have hpb' : IsPullback (torsorChartToTrivializations U N q₀ τ₀ ≫ e.hom) (yoneda.map π)
      (yoneda.map (Over.mkIdTerminal.from W)) (yoneda.map q) :=
    hpb.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp)
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by rw [he, Iso.refl_hom, Category.comp_id]) (by simp)
  obtain ⟨j, hj⟩ : ∃ j, yoneda.map j = torsorChartToTrivializations U N q₀ τ₀ ≫ e.hom :=
    ⟨_, yoneda.map_preimage _⟩
  rw [← hj] at hpb'
  have hsite : IsPullback j π (Over.mkIdTerminal.from W) q :=
    IsPullback.of_map_of_faithful yoneda hpb'
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B U.left.1 U.left.2) :=
    comp_preservesLimitsOfShape _ _
  have hsch := hsite.map (BigFppfOver.toScheme B U.left.1 U.left.2)
  have hjs : Surjective ((BigFppfOver.toScheme B U.left.1 U.left.2).map j) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) hsch.flip hqs
  have hje : Etale ((BigFppfOver.toScheme B U.left.1 U.left.2).map j) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hsch.flip hqe
  have hw := hsch.w
  refine ⟨?_, ?_, hP (𝟙 _) fst _ hW⟩
  · rw [Smooth.isEtaleLocalOnSourceAndTarget.iff_forall_exists_etale_neighborhood]
    intro x
    obtain ⟨y, hy⟩ := hjs.surj x
    exact ⟨_, _, _, _, _, y, hje, hqe, hy, hw.symm, smooth_multiplicativeGroupChartHom c⟩
  · have : Surjective ((BigFppfOver.toScheme B U.left.1 U.left.2).map j ≫
        (BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) := by
      rw [hw]
      infer_instance
    exact Surjective.of_comp ((BigFppfOver.toScheme B U.left.1 U.left.2).map j) _

end Representability

end AlgebraicGeometry.Space
