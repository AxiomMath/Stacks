module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TargetPairsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentRightAdjointUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# The right adjoint of the forgetful functor on quasi-coherent modules on a groupoid

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces with `s` flat, quasi-compact and
quasi-separated.  For a quasi-coherent `𝒪_U`-module `𝒢` the module `s_*t^*𝒢` carries a canonical
transition morphism making it a quasi-coherent module on `(U, R, s, t, c)`, and the functor
`𝒢 ↦ (s_*t^*𝒢, α)` so obtained is right adjoint to the forgetful functor `(ℱ, β) ↦ ℱ`.

Following the proof of Stacks 0GPP, the functor is the composite of `𝒢 ↦ (t^*𝒢, can)`, from
quasi-coherent `𝒪_U`-modules to quasi-coherent modules on the groupoid
`(R, R ×_{t, U, t} R, pr₁, pr₀, pr₀₂)` of pairs of arrows with a common target, with the direct
image of Stacks 0GPM along the morphism `f = (s, (r₀, r₁) ↦ r₀⁻¹ ∘ r₁)` from that groupoid to
`(U, R, s, t, c)`.  The adjunction is the adjunction `f^* ⊣ f_*` of Stacks 0GPM, read through the
isomorphism `f^*(ℱ, β) ≅ (t^*ℱ, can)` given by `β⁻¹` and through the full faithfulness of
`𝒢 ↦ (t^*𝒢, can)`.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentModule.forgetQuasicoherent`: the forgetful functor
  `(ℱ, β) ↦ ℱ` to the quasi-coherent `𝒪_U`-modules.
* `AlgebraicGeometry.Space.QuasicoherentModule.cofree`: the functor `𝒢 ↦ (s_*t^*𝒢, α)`.
* `AlgebraicGeometry.Space.QuasicoherentModule.forgetAdjunction`: **Stacks 0GPP**, the adjunction
  between the two.

## Main results

* `AlgebraicGeometry.Space.QuasicoherentModule.hom_ext_of_section`: on a groupoid `(U, R, s, t, c)`
  with a morphism `σ : U ⟶ R` such that `σ ≫ s = 𝟙` and `σ ≫ t` factors through `e : V ⟶ U`,
  a morphism of quasi-coherent modules is determined by its inverse image along `e`.
* `AlgebraicGeometry.Space.fullyFaithfulTargetPairs`: `𝒢 ↦ (t^*𝒢, can)` is fully faithful, the
  section being the unit `e : U ⟶ R` and `σ = (e ∘ t, 1)`.
* `AlgebraicGeometry.Space.QuasicoherentModule.forgetAdjunction_unit_app_hom`: the unit of the
  adjunction at `(ℱ, β)` is `ℱ ⟶ s_*s^*ℱ ⟶ s_*t^*ℱ`, the unit of `s^* ⊣ s_*` followed by the
  direct image of `β⁻¹`.

## References

* [Stacks Project, Tag 0GPP](https://stacks.math.columbia.edu/tag/0GPP)
* [Stacks Project, Tag 0GPM](https://stacks.math.columbia.edu/tag/0GPM)
* [Stacks Project, Tag 077W](https://stacks.math.columbia.edu/tag/077W)
-/





@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism which agrees with another after conjugation by two isomorphisms is equal to it. -/
theorem eq_of_comp_isIso_eq {C : Type*} [Category C] {W X Y Z : C} (a : W ⟶ X) (d : Y ⟶ Z)
    [IsIso a] [IsIso d] {x y : X ⟶ Y} (h : a ≫ x ≫ d = a ≫ y ≫ d) : x = y := by
  simpa using congrArg (fun z => inv a ≫ z ≫ inv d) h

/-- The inverse image of a morphism of modules along a composite `k ≫ e`, read through the
comparison of iterated inverse images of Stacks 03LU. -/
theorem modulePullback_map_comp_eq {X Y Z : AlgebraicSpaces B S hS} (k : X ⟶ Y) (e : Y ⟶ Z)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (x : M ⟶ N) :
    (modulePullback B S hS (k ≫ e)).map x =
      (modulePullbackCompIso B S hS k e).inv.app M ≫
        (modulePullback B S hS k).map ((modulePullback B S hS e).map x) ≫
        (modulePullbackCompIso B S hS k e).hom.app N := by
  rw [← Functor.comp_map, ← NatTrans.naturality_assoc, Iso.inv_hom_id_app,
    Category.comp_id]

/-- Two morphisms of modules with equal inverse images along `f` have equal inverse images along
every morphism equal to `f`. -/
theorem modulePullback_map_eq_of_eq {X Y : AlgebraicSpaces B S hS} {f g : X ⟶ Y} (hfg : f = g)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} {x y : M ⟶ N}
    (h : (modulePullback B S hS f).map x = (modulePullback B S hS f).map y) :
    (modulePullback B S hS g).map x = (modulePullback B S hS g).map y := by
  subst hfg
  exact h

namespace QuasicoherentModule

attribute [local instance] isIso_alpha

/-- **A morphism of quasi-coherent modules on a groupoid with a section is determined by its
inverse image along the section.**  Let `(U, R, s, t, c)` be a groupoid in algebraic spaces, let
`e : V ⟶ U` and `k : U ⟶ V` be morphisms and `σ : U ⟶ R` a morphism with `σ ≫ s = 𝟙` and
`σ ≫ t = k ≫ e`.  Two morphisms `θ₁, θ₂ : (ℱ, β) ⟶ (𝒢, γ)` of quasi-coherent modules with
`e^*θ₁ = e^*θ₂` are equal.

Indeed `σ^*` of the compatibility of `θ` with the transition morphisms reads
`σ^*β ∘ (σ ≫ s)^*θ = (σ ≫ t)^*θ ∘ σ^*γ` up to the comparisons of iterated inverse images; the
transition morphisms are invertible by Stacks 077W, `(σ ≫ s)^*θ` is `θ` and `(σ ≫ t)^*θ` is
`k^*e^*θ`. -/
theorem hom_ext_of_section {A : AlgebraicSpaces B S hS} {H : GroupoidInAlgebraicSpaces B S hS A}
    {V : AlgebraicSpaces B S hS} (e : V ⟶ H.objects) (k : H.objects ⟶ V)
    (σ : H.objects ⟶ H.arrows) (hσs : σ ≫ H.source = 𝟙 H.objects) (hσt : σ ≫ H.target = k ≫ e)
    {M N : QuasicoherentModule B S hS H} {θ₁ θ₂ : M ⟶ N}
    (h : (modulePullback B S hS e).map θ₁.hom = (modulePullback B S hS e).map θ₂.hom) :
    θ₁ = θ₂ := by
  have hke : (modulePullback B S hS (k ≫ e)).map θ₁.hom =
      (modulePullback B S hS (k ≫ e)).map θ₂.hom := by
    rw [modulePullback_map_comp_eq, modulePullback_map_comp_eq, h]
  have ht : (modulePullback B S hS (σ ≫ H.target)).map θ₁.hom =
      (modulePullback B S hS (σ ≫ H.target)).map θ₂.hom :=
    modulePullback_map_eq_of_eq hσt.symm hke
  have hσ : ∀ θ : M ⟶ N,
      (modulePullback B S hS σ).map M.alpha ≫ (modulePullbackCompIso B S hS σ H.source).hom.app _ ≫
          (modulePullback B S hS (σ ≫ H.source)).map θ.hom ≫
          (modulePullbackCompIso B S hS σ H.source).inv.app _ =
        (modulePullbackCompIso B S hS σ H.target).hom.app _ ≫
          (modulePullback B S hS (σ ≫ H.target)).map θ.hom ≫
          (modulePullbackCompIso B S hS σ H.target).inv.app _ ≫
          (modulePullback B S hS σ).map N.alpha := fun θ => by
    rw [modulePullback_map_comp_eq, modulePullback_map_comp_eq]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id]
    rw [← Functor.map_comp, ← Functor.map_comp, θ.comm]
  have hs : (modulePullback B S hS (σ ≫ H.source)).map θ₁.hom =
      (modulePullback B S hS (σ ≫ H.source)).map θ₂.hom := by
    have h₁ := hσ θ₁
    rw [ht, ← hσ θ₂] at h₁
    exact eq_of_comp_isIso_eq ((modulePullback B S hS σ).map M.alpha ≫
      (modulePullbackCompIso B S hS σ H.source).hom.app _)
      ((modulePullbackCompIso B S hS σ H.source).inv.app _)
      (by simpa only [Category.assoc] using h₁)
  have hid := modulePullback_map_eq_of_eq hσs hs
  refine Hom.ext ?_
  have hnat : ∀ θ : M ⟶ N, θ.hom = (modulePullbackIdIso B S hS H.objects).inv.app _ ≫
      (modulePullback B S hS (𝟙 H.objects)).map θ.hom ≫
      (modulePullbackIdIso B S hS H.objects).hom.app _ := fun θ => by
    rw [NatTrans.naturality, Iso.inv_hom_id_app_assoc, Functor.id_map]
  rw [hnat θ₁, hnat θ₂, hid]

end QuasicoherentModule


section Section

variable {A : AlgebraicSpaces B S hS} (H : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS}

/-- The inverse image along a section `e` of `φ` of the inverse image along `φ` is the
identity, since `e ≫ φ = 𝟙`. -/
def modulePullbackSectionIso {Y : AlgebraicSpaces B S hS} (φ : Y ⟶ X) (e : X ⟶ Y)
    (he : e ≫ φ = 𝟙 X) :
    modulePullback B S hS φ ⋙ modulePullback B S hS e ≅ 𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  modulePullbackCompIso B S hS e φ ≪≫
    eqToIso (congrArg (fun k : X ⟶ X => modulePullback B S hS k) he) ≪≫
    modulePullbackIdIso B S hS X

/-- The inverse image along a morphism with a section is faithful. -/
theorem faithful_modulePullback_of_section {Y : AlgebraicSpaces B S hS} (φ : Y ⟶ X)
    (e : X ⟶ Y) (he : e ≫ φ = 𝟙 X) : (modulePullback B S hS φ).Faithful where
  map_injective {M N} x y hxy := by
    have hnat : ∀ z : M ⟶ N, z = (modulePullbackSectionIso φ e he).inv.app M ≫
        (modulePullback B S hS φ ⋙ modulePullback B S hS e).map z ≫
        (modulePullbackSectionIso φ e he).hom.app N := fun z => by
      rw [NatTrans.naturality, Iso.inv_hom_id_app_assoc, Functor.id_map]
    rw [hnat x, hnat y, Functor.comp_map, Functor.comp_map, hxy]

/-- **The functor `𝒢 ↦ (φ^*𝒢, can)` is faithful when `φ` has a section.** -/
theorem faithful_quasicoherentFromSpaceBase_of_section (φ : H.objects ⟶ X)
    (hφ : H.target ≫ φ = H.source ≫ φ) (e : X ⟶ H.objects) (he : e ≫ φ = 𝟙 X) :
    (quasicoherentFromSpaceBase B S hS H φ hφ).Faithful :=
  have := faithful_modulePullback_of_section φ e he
  faithful_quasicoherentFromSpaceBase B S hS H φ hφ

/-- The inverse image along `e` of the underlying morphism of the image of `g` under
`𝒢 ↦ (φ^*𝒢, can)` is `e^*φ^*g`. -/
theorem modulePullback_map_quasicoherentFromSpaceBase_map (φ : H.objects ⟶ X)
    (hφ : H.target ≫ φ = H.source ≫ φ) (e : X ⟶ H.objects)
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (g : M ⟶ N) :
    (modulePullback B S hS e).map ((quasicoherentFromSpaceBase B S hS H φ hφ).map g).hom =
      (modulePullback B S hS φ ⋙ modulePullback B S hS e).map g.hom :=
  rfl

/-- The functor `(ℱ, β) ↦ e^*ℱ` from the quasi-coherent modules on the groupoid to the
`𝒪_X`-modules, for a morphism `e : X ⟶ U` to the space of objects. -/
abbrev sectionForget (e : X ⟶ H.objects) :
    QuasicoherentModule B S hS H ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  QuasicoherentModule.forget H ⋙ modulePullback B S hS e

/-- `(ℱ, β) ↦ e^*ℱ` is faithful when the groupoid has a morphism `σ : U ⟶ R` with `σ ≫ s = 𝟙`
and `σ ≫ t = φ ≫ e`: this is
`AlgebraicGeometry.Space.QuasicoherentModule.hom_ext_of_section`. -/
theorem faithful_sectionForget (φ : H.objects ⟶ X) (e : X ⟶ H.objects)
    (σ : H.objects ⟶ H.arrows) (hσs : σ ≫ H.source = 𝟙 H.objects)
    (hσt : σ ≫ H.target = φ ≫ e) : (sectionForget H e).Faithful where
  map_injective h := QuasicoherentModule.hom_ext_of_section e φ σ hσs hσt h

/-- Composing `𝒢 ↦ (φ^*𝒢, can)` with `(ℱ, β) ↦ e^*ℱ` gives `𝒢 ↦ e^*φ^*𝒢`. -/
def quasicoherentFromSpaceBaseCompSectionForgetIso (φ : H.objects ⟶ X)
    (hφ : H.target ≫ φ = H.source ≫ φ) (e : X ⟶ H.objects) :
    quasicoherentFromSpaceBase B S hS H φ hφ ⋙ sectionForget H e ≅
      ObjectProperty.ι _ ⋙ (modulePullback B S hS φ ⋙ modulePullback B S hS e) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun g =>
    (Category.comp_id _).trans
      ((modulePullback_map_quasicoherentFromSpaceBase_map H φ hφ e g).trans
        (Category.id_comp _).symm))

/-- **The functor `𝒢 ↦ (φ^*𝒢, can)` is full when `φ` has a section `e` and the groupoid has a
morphism `σ : U ⟶ R` with `σ ≫ s = 𝟙` and `σ ≫ t = φ ≫ e`.**  Its composite with the faithful
functor `(ℱ, β) ↦ e^*ℱ` is `𝒢 ↦ e^*φ^*𝒢`, which is isomorphic to the inclusion of the
quasi-coherent modules, since `e ≫ φ = 𝟙`. -/
theorem full_quasicoherentFromSpaceBase_of_section (φ : H.objects ⟶ X)
    (hφ : H.target ≫ φ = H.source ≫ φ) (e : X ⟶ H.objects) (he : e ≫ φ = 𝟙 X)
    (σ : H.objects ⟶ H.arrows)
    (hσs : σ ≫ H.source = 𝟙 H.objects) (hσt : σ ≫ H.target = φ ≫ e) :
    (quasicoherentFromSpaceBase B S hS H φ hφ).Full :=
  have := faithful_sectionForget H φ e σ hσs hσt
  Functor.Full.of_comp_faithful_iso
    (quasicoherentFromSpaceBaseCompSectionForgetIso H φ hφ e ≪≫
      Functor.isoWhiskerLeft (ObjectProperty.ι _) (modulePullbackSectionIso φ e he) ≪≫
      Functor.rightUnitor _)

end Section

section TargetPairs

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)

/-- The morphism `R ⟶ R ×_{t, U, t} R`, `r ↦ (e(t(r)), r)`: a section of the source `pr₁` of the
groupoid of pairs of arrows with a common target whose composite with the target `pr₀` is
`e ∘ t`. -/
def targetPairsSection : (targetPairsGroupoid G).objects ⟶ (targetPairsGroupoid G).arrows :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G.target G.target).lift
    (G.target ≫ identityArrow G) (𝟙 G.arrows) (by
      rw [Category.assoc, identityArrow_comp_target, Category.comp_id, Category.id_comp])

/-- `σ` is a section of the source `pr₁`. -/
theorem targetPairsSection_source :
    targetPairsSection G ≫ (targetPairsGroupoid G).source = 𝟙 (targetPairsGroupoid G).objects :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G.target G.target).lift_snd _ _ _

/-- The target `pr₀` of `σ` is `e ∘ t`. -/
theorem targetPairsSection_target :
    targetPairsSection G ≫ (targetPairsGroupoid G).target =
      (G.target : (targetPairsGroupoid G).objects ⟶ G.objects) ≫
        (identityArrow G : G.objects ⟶ (targetPairsGroupoid G).objects) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G.target G.target).lift_fst _ _ _

/-- The functor `𝒢 ↦ (t^*𝒢, can)` from the quasi-coherent `𝒪_U`-modules to the quasi-coherent
modules on the groupoid `(R, R ×_{t, U, t} R, pr₁, pr₀, pr₀₂)` of pairs of arrows with a common
target. -/
abbrev targetPairsBase :
    QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property ⥤
      QuasicoherentModule B S hS (targetPairsGroupoid G) :=
  quasicoherentFromSpaceBase B S hS (targetPairsGroupoid G) G.target
    (targetPairsFst_comp_target G)

/-- **`𝒢 ↦ (t^*𝒢, can)` is fully faithful**: the target `t : R ⟶ U` has the unit `e` as a section,
and `σ = (e ∘ t, 1)` is a section of the source `pr₁` with `pr₀ ∘ σ = e ∘ t`. -/
def fullyFaithfulTargetPairs : (targetPairsBase G).FullyFaithful :=
  haveI := faithful_quasicoherentFromSpaceBase_of_section (targetPairsGroupoid G) G.target
    (targetPairsFst_comp_target G)
    (identityArrow G : G.objects ⟶ (targetPairsGroupoid G).objects) (identityArrow_comp_target G)
  haveI := full_quasicoherentFromSpaceBase_of_section (targetPairsGroupoid G) G.target
    (targetPairsFst_comp_target G)
    (identityArrow G : G.objects ⟶ (targetPairsGroupoid G).objects) (identityArrow_comp_target G)
    (targetPairsSection G) (targetPairsSection_source G) (targetPairsSection_target G)
  Functor.FullyFaithful.ofFullyFaithful _

end TargetPairs

section Cofree

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)

attribute [local instance] QuasicoherentModule.isIso_alpha

/-- The inverse `β` of `β⁻¹` intertwines the canonical descent datum of `t^*ℱ` with the
transition morphism of the inverse image `f^*(ℱ, β)`. -/
theorem targetPairsAlpha_compatible (M : QuasicoherentModule B S hS G) :
    spaceBaseDescent B S hS (targetPairsGroupoid G) G.target (targetPairsFst_comp_target G)
        M.F.obj ≫
        (modulePullback B S hS (targetPairsGroupoid G).source).map (targetPairsAlpha G M) =
      (modulePullback B S hS (targetPairsGroupoid G).target).map (targetPairsAlpha G M) ≫
        groupoidModulePullbackTransition B S hS (targetPairsHom G) M.F.obj M.alpha := by
  have h := groupoidModulePullbackTransition_targetPairsHom G M
  have hs : (modulePullback B S hS (targetPairsGroupoid G).source).map (targetPairsAlphaInv G M) ≫
      (modulePullback B S hS (targetPairsGroupoid G).source).map (targetPairsAlpha G M) = 𝟙 _ := by
    rw [← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  have ht : (modulePullback B S hS (targetPairsGroupoid G).target).map (targetPairsAlpha G M) ≫
      (modulePullback B S hS (targetPairsGroupoid G).target).map (targetPairsAlphaInv G M) =
        𝟙 _ := by
    rw [← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [← Category.id_comp (spaceBaseDescent B S hS _ _ _ _), ← ht]
  simp only [Category.assoc]
  rw [← reassoc_of% h, hs, Category.comp_id]

/-- `β⁻¹ : s^*ℱ ⟶ t^*ℱ`, read as a morphism from the underlying module of the inverse image
`f^*(ℱ, β)` to that of `(t^*ℱ, can)`. -/
def targetPairsPullbackHom (M : QuasicoherentModule B S hS G) :
    ((groupoidQuasicoherentPullback B S hS (targetPairsHom G)).obj M).F.obj ⟶
      ((targetPairsBase G).obj M.F).F.obj :=
  targetPairsAlphaInv G M

/-- `β : t^*ℱ ⟶ s^*ℱ`, read as a morphism from the underlying module of `(t^*ℱ, can)` to that
of the inverse image `f^*(ℱ, β)`. -/
def targetPairsPullbackInv (M : QuasicoherentModule B S hS G) :
    ((targetPairsBase G).obj M.F).F.obj ⟶
      ((groupoidQuasicoherentPullback B S hS (targetPairsHom G)).obj M).F.obj :=
  targetPairsAlpha G M

/-- The transition morphism of the inverse image `f^*(ℱ, β)` is `f^*β`. -/
theorem targetPairsPullback_alpha (M : QuasicoherentModule B S hS G) :
    ((groupoidQuasicoherentPullback B S hS (targetPairsHom G)).obj M).alpha =
      groupoidModulePullbackTransition B S hS (targetPairsHom G) M.F.obj M.alpha :=
  groupoidQuasicoherentPullbackObj_alpha B S hS (targetPairsHom G) M

/-- The transition morphism of `(t^*𝒢, can)` is the canonical descent datum. -/
theorem targetPairsBase_alpha
    (M : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property) :
    ((targetPairsBase G).obj M).alpha =
      spaceBaseDescent B S hS (targetPairsGroupoid G) G.target (targetPairsFst_comp_target G)
        M.obj :=
  spaceBaseObj_alpha B S hS (targetPairsGroupoid G) G.target (targetPairsFst_comp_target G) M

/-- `β⁻¹` intertwines the transition morphism of `f^*(ℱ, β)` with the canonical descent datum. -/
theorem targetPairsPullbackHom_compatible (M : QuasicoherentModule B S hS G) :
    QuasicoherentModule.Compatible (targetPairsPullbackHom G M) := by
  unfold QuasicoherentModule.Compatible
  rw [targetPairsPullback_alpha, targetPairsBase_alpha]
  exact groupoidModulePullbackTransition_targetPairsHom G M

/-- `β` intertwines the canonical descent datum with the transition morphism of `f^*(ℱ, β)`. -/
theorem targetPairsPullbackInv_compatible (M : QuasicoherentModule B S hS G) :
    QuasicoherentModule.Compatible (targetPairsPullbackInv G M) := by
  unfold QuasicoherentModule.Compatible
  rw [targetPairsPullback_alpha, targetPairsBase_alpha]
  exact targetPairsAlpha_compatible G M

/-- **The inverse image `f^*(ℱ, β)` is `(t^*ℱ, can)`**, by the isomorphism
`β⁻¹ : s^*ℱ ⟶ t^*ℱ`. -/
def targetPairsPullbackIso (M : QuasicoherentModule B S hS G) :
    (groupoidQuasicoherentPullback B S hS (targetPairsHom G)).obj M ≅ (targetPairsBase G).obj M.F
    where
  hom := QuasicoherentModule.homMk _ (targetPairsPullbackHom_compatible G M)
  inv := QuasicoherentModule.homMk _ (targetPairsPullbackInv_compatible G M)
  hom_inv_id := QuasicoherentModule.Hom.ext (IsIso.inv_hom_id (targetPairsAlpha G M))
  inv_hom_id := QuasicoherentModule.Hom.ext (IsIso.hom_inv_id (targetPairsAlpha G M))

/-- `β⁻¹ : s^*ℱ ⟶ t^*ℱ` is natural in the quasi-coherent module `(ℱ, β)`, in any typing of the
source and target morphisms of the groupoid. -/
theorem inv_alpha_naturality {M N : QuasicoherentModule B S hS G} (g : M ⟶ N)
    {Y : AlgebraicSpaces B S hS} (hY : Y = G.arrows) (s t : Y ⟶ G.objects)
    (hs : HEq s G.source) (ht : HEq t G.target)
    (αM : (modulePullback B S hS t).obj M.F.obj ⟶ (modulePullback B S hS s).obj M.F.obj)
    (αN : (modulePullback B S hS t).obj N.F.obj ⟶ (modulePullback B S hS s).obj N.F.obj)
    (hαM : HEq αM M.alpha) (hαN : HEq αN N.alpha) [IsIso αM] [IsIso αN] :
    (modulePullback B S hS s).map g.hom ≫ inv αN =
      inv αM ≫ (modulePullback B S hS t).map g.hom := by
  subst hY
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq hαM
  obtain rfl := eq_of_heq hαN
  rw [IsIso.eq_inv_comp, ← Category.assoc, g.comm, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

end Cofree

namespace QuasicoherentModule

/-- **The forgetful functor** `(ℱ, β) ↦ ℱ` from the quasi-coherent modules on a groupoid in
algebraic spaces `(U, R, s, t, c)` to the quasi-coherent `𝒪_U`-modules: the functor
`AlgebraicGeometry.Space.QuasicoherentModule.forget`, which keeps the underlying module, with its
values recorded as quasi-coherent. -/
def forgetQuasicoherent {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A) :
    QuasicoherentModule B S hS G ⥤
      QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property :=
  ObjectProperty.lift _ (forget G) fun M => M.F.property

end QuasicoherentModule

section Cofree

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)

attribute [local instance] QuasicoherentModule.isIso_alpha

/-- `AlgebraicGeometry.Space.targetPairsPullbackIso`, with the forgetful functor followed by
`𝒢 ↦ (t^*𝒢, can)` as target. -/
def targetPairsPullbackIso' (M : QuasicoherentModule B S hS G) :
    (groupoidQuasicoherentPullback B S hS (targetPairsHom G)).obj M ≅
      (QuasicoherentModule.forgetQuasicoherent G ⋙ targetPairsBase G).obj M :=
  targetPairsPullbackIso G M

/-- The underlying morphism of `f^*(ℱ, β) ≅ (t^*ℱ, can)` is `β⁻¹`. -/
theorem targetPairsPullbackIso'_hom_hom (M : QuasicoherentModule B S hS G) :
    (targetPairsPullbackIso' G M).hom.hom = targetPairsAlphaInv G M :=
  rfl

/-- The isomorphism `f^*(ℱ, β) ≅ (t^*ℱ, can)` is natural in `(ℱ, β)`. -/
theorem targetPairsPullbackIso_naturality {M N : QuasicoherentModule B S hS G}
    (g : @Quiver.Hom _ CategoryStruct.toQuiver M N) :
    (groupoidQuasicoherentPullback B S hS (targetPairsHom G)).map g ≫
        (targetPairsPullbackIso' G N).hom =
      (targetPairsPullbackIso' G M).hom ≫
        (QuasicoherentModule.forgetQuasicoherent G ⋙ targetPairsBase G).map g := by
  refine QuasicoherentModule.Hom.ext ?_
  show (modulePullback B S hS (targetPairsHom G).objectsMap).map g.hom ≫ targetPairsAlphaInv G N =
    targetPairsAlphaInv G M ≫
      (@modulePullback B S hS (targetPairsGroupoid G).objects G.objects G.target).map g.hom
  exact inv_alpha_naturality G g (Y := (targetPairsGroupoid G).objects) rfl
    (targetPairsHom G).objectsMap (G.target : (targetPairsGroupoid G).objects ⟶ G.objects)
    HEq.rfl HEq.rfl (targetPairsAlpha G M) (targetPairsAlpha G N) HEq.rfl HEq.rfl

/-- The isomorphisms `f^*(ℱ, β) ≅ (t^*ℱ, can)` assemble to a natural isomorphism. -/
theorem exists_targetPairsPullbackNatIso :
    ∃ e : groupoidQuasicoherentPullback B S hS (targetPairsHom G) ≅
        QuasicoherentModule.forgetQuasicoherent G ⋙ targetPairsBase G,
      ∀ M, e.hom.app M = (targetPairsPullbackIso' G M).hom :=
  ⟨NatIso.ofComponents (targetPairsPullbackIso' G) (targetPairsPullbackIso_naturality G),
    fun _ => rfl⟩

/-- **The inverse image along `f = (s, (r₀, r₁) ↦ r₀⁻¹ ∘ r₁)` is the forgetful functor followed
by `𝒢 ↦ (t^*𝒢, can)`**, by `β⁻¹`. -/
def targetPairsPullbackNatIso :
    groupoidQuasicoherentPullback B S hS (targetPairsHom G) ≅
      QuasicoherentModule.forgetQuasicoherent G ⋙ targetPairsBase G :=
  Classical.choose (exists_targetPairsPullbackNatIso G)

/-- The components of `AlgebraicGeometry.Space.targetPairsPullbackNatIso` are the isomorphisms
`f^*(ℱ, β) ≅ (t^*ℱ, can)` given by `β⁻¹`. -/
theorem targetPairsPullbackNatIso_hom_app (M : QuasicoherentModule B S hS G) :
    (targetPairsPullbackNatIso G).hom.app M = (targetPairsPullbackIso' G M).hom :=
  Classical.choose_spec (exists_targetPairsPullbackNatIso G) M

end Cofree

/-- `ℱ ⟶ s_*s^*ℱ ⟶ s_*t^*ℱ` in any typing of the source and target morphisms of the groupoid. -/
theorem sourceUnitInvAlpha_heq {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}
    (M : QuasicoherentModule B S hS G) {Y : AlgebraicSpaces B S hS} (hY : Y = G.arrows)
    (s t : Y ⟶ G.objects) (hs : HEq s G.source) (ht : HEq t G.target)
    (α' : (modulePullback B S hS t).obj M.F.obj ⟶ (modulePullback B S hS s).obj M.F.obj)
    [IsIso α'] (hα : HEq α' M.alpha) :
    HEq ((modulePullbackAdjunction B S hS s).unit.app M.F.obj ≫
      (modulePushforward B S hS s).map (inv α')) (QuasicoherentModule.sourceUnitInvAlpha M) := by
  subst hY
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq hα
  rfl

section UnitHom

variable {A : AlgebraicSpaces B S hS} {G G' : GroupoidInAlgebraicSpaces B S hS A}

/-- The unit of the adjunction of Stacks 0GPM followed by the direct image of a morphism and a
further morphism, read on the spaces of objects. -/
theorem groupoidQuasicoherentPullbackPushforwardAdjunction_unit_app_comp_hom (φ : Hom G G')
    (hqc : IsQuasiCompact B S hS φ.objectsMap.hom) (hqs : IsQuasiSeparated B S hS φ.objectsMap.hom)
    (hpb : IsPullback φ.arrowsMap G.target G'.target φ.objectsMap)
    (hsflat : IsFlat B S hS G'.source.hom) (N : QuasicoherentModule B S hS G')
    {M : QuasicoherentModule B S hS G} {P : QuasicoherentModule B S hS G'}
    (x : (groupoidQuasicoherentPullback B S hS φ).obj N ⟶ M)
    (y : (groupoidQuasicoherentPushforward B S hS φ hqc hqs hpb hsflat).obj M ⟶ P) :
    ((groupoidQuasicoherentPullbackPushforwardAdjunction B S hS φ hqc hqs hpb hsflat).unit.app N ≫
        (groupoidQuasicoherentPushforward B S hS φ hqc hqs hpb hsflat).map x ≫ y).hom =
      (modulePullbackAdjunction B S hS φ.objectsMap).unit.app N.F.obj ≫
        (modulePushforward B S hS φ.objectsMap).map x.hom ≫ y.hom := by
  rw [QuasicoherentModule.comp_hom, QuasicoherentModule.comp_hom,
    groupoidQuasicoherentPullbackPushforwardAdjunction_unit_app_hom,
    groupoidQuasicoherentPushforward_map, groupoidQuasicoherentPushforwardHom_hom]
  rfl

end UnitHom

namespace QuasicoherentModule

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  (hsflat : IsFlat B S hS G.source.hom) (hsqc : IsQuasiCompact B S hS G.source.hom)
  (hsqs : IsQuasiSeparated B S hS G.source.hom)

/-- **The right adjoint of the forgetful functor**: the functor `𝒢 ↦ (s_*t^*𝒢, α)` from the
quasi-coherent `𝒪_U`-modules to the quasi-coherent modules on `(U, R, s, t, c)`.  It is the
functor `𝒢 ↦ (t^*𝒢, can)` to the groupoid `(R, R ×_{t, U, t} R, pr₁, pr₀, pr₀₂)` followed by the
direct image of Stacks 0GPM along `f = (s, (r₀, r₁) ↦ r₀⁻¹ ∘ r₁)`, whose map on objects is
`s`; its transition morphism `α` is the transition morphism of that direct image, which is
invertible by Stacks 077W. -/
def cofree :
    QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property ⥤
      QuasicoherentModule B S hS G :=
  targetPairsBase G ⋙ groupoidQuasicoherentPushforward B S hS (targetPairsHom G) hsqc hsqs
    (isPullback_targetPairsHom G) hsflat

/-- **Stacks 0GPP.**  Let `(U, R, s, t, c)` be a groupoid in algebraic spaces with `s` (and hence
`t = s ∘ i`) flat, quasi-compact and quasi-separated.  For a quasi-coherent `𝒪_U`-module `𝒢` the
module `s_*t^*𝒢` carries a canonical isomorphism `α : t^*s_*t^*𝒢 ⟶ s^*s_*t^*𝒢` making
`(s_*t^*𝒢, α)` a quasi-coherent module on `(U, R, s, t, c)`; this defines the functor
`AlgebraicGeometry.Space.QuasicoherentModule.cofree`, and it is right adjoint to the forgetful
functor `(ℱ, β) ↦ ℱ`. -/
@[stacks 0GPP]
def forgetAdjunction : forgetQuasicoherent G ⊣ cofree G hsflat hsqc hsqs :=
  (groupoidQuasicoherentPullbackPushforwardAdjunction B S hS (targetPairsHom G) hsqc hsqs
      (isPullback_targetPairsHom G) hsflat).restrictFullyFaithful
    (Functor.FullyFaithful.id _) (fullyFaithfulTargetPairs G)
    (Functor.leftUnitor _ ≪≫ targetPairsPullbackNatIso G) (Functor.rightUnitor _).symm

/-- The unit of the adjunction at `(ℱ, β)`, read on the space of objects, before simplification. -/
theorem forgetAdjunction_unit_app_hom_aux (M : QuasicoherentModule B S hS G) :
    ((forgetAdjunction G hsflat hsqc hsqs).unit.app M).hom =
      (modulePullbackAdjunction B S hS (targetPairsHom G).objectsMap).unit.app
          ((𝟭 (QuasicoherentModule B S hS G)).obj M).F.obj ≫
        (modulePushforward B S hS (targetPairsHom G).objectsMap).map
          ((Functor.leftUnitor _ ≪≫ targetPairsPullbackNatIso G).hom.app M).hom ≫
        ((Functor.rightUnitor (cofree G hsflat hsqc hsqs)).symm.hom.app
          ((forgetQuasicoherent G).obj M)).hom :=
  (congrArg Hom.hom (Adjunction.map_restrictFullyFaithful_unit_app
    (groupoidQuasicoherentPullbackPushforwardAdjunction B S hS (targetPairsHom G) hsqc hsqs
      (isPullback_targetPairsHom G) hsflat)
    (Functor.FullyFaithful.id _) (fullyFaithfulTargetPairs G)
    (Functor.leftUnitor _ ≪≫ targetPairsPullbackNatIso G) (Functor.rightUnitor _).symm M)).trans
  (groupoidQuasicoherentPullbackPushforwardAdjunction_unit_app_comp_hom (targetPairsHom G) hsqc
    hsqs (isPullback_targetPairsHom G) hsflat _ _ _)

attribute [local instance] isIso_alpha in
/-- **The unit of the adjunction of Stacks 0GPP** at `(ℱ, β)` is `ℱ ⟶ s_*s^*ℱ ⟶ s_*t^*ℱ`, the unit
of `s^* ⊣ s_*` followed by the direct image of `β⁻¹`. -/
theorem forgetAdjunction_unit_app_hom (M : QuasicoherentModule B S hS G) :
    ((forgetAdjunction G hsflat hsqc hsqs).unit.app M).hom = sourceUnitInvAlpha M := by
  rw [forgetAdjunction_unit_app_hom_aux]
  simp -proj only [Iso.trans_hom, NatTrans.comp_app, comp_hom, Functor.leftUnitor_hom_app, id_hom,
    targetPairsPullbackNatIso_hom_app, targetPairsPullbackIso'_hom_hom, Iso.symm_hom,
    Functor.rightUnitor_inv_app, Functor.id_obj]
  have e₁ : @CategoryStruct.comp (Modules.{u, u} B S hS (targetPairsGroupoid G).objects.1
        (targetPairsGroupoid G).objects.2) _
      ((𝟭 (QuasicoherentModule B S hS G) ⋙
        groupoidQuasicoherentPullback B S hS (targetPairsHom G)).obj M).F.obj
      ((groupoidQuasicoherentPullback B S hS (targetPairsHom G)).obj M).F.obj
      ((forgetQuasicoherent G ⋙ targetPairsBase G).obj M).F.obj
      (𝟙 ((groupoidQuasicoherentPullback B S hS (targetPairsHom G)).obj M).F.obj)
      (targetPairsAlphaInv G M) = targetPairsAlphaInv G M :=
    Category.id_comp _
  rw [e₁]
  have e₂ : @CategoryStruct.comp (Modules.{u, u} B S hS G.objects.1 G.objects.2) _
      ((modulePullback B S hS (targetPairsHom G).objectsMap ⋙
        modulePushforward B S hS (targetPairsHom G).objectsMap).obj M.F.obj)
      ((modulePushforward B S hS (targetPairsHom G).objectsMap).obj
        ((forgetQuasicoherent G ⋙ targetPairsBase G).obj M).F.obj)
      (((cofree G hsflat hsqc hsqs ⋙ 𝟭 (QuasicoherentModule B S hS G)).obj
        ((forgetQuasicoherent G).obj M)).F.obj)
      ((modulePushforward B S hS (targetPairsHom G).objectsMap).map (targetPairsAlphaInv G M))
      (𝟙 ((cofree G hsflat hsqc hsqs).obj ((forgetQuasicoherent G).obj M)).F.obj) =
      (modulePushforward B S hS (targetPairsHom G).objectsMap).map (targetPairsAlphaInv G M) :=
    Category.comp_id _
  rw [e₂]
  have h := sourceUnitInvAlpha_heq M (Y := (targetPairsGroupoid G).objects) rfl
    (targetPairsHom G).objectsMap (G.target : (targetPairsGroupoid G).objects ⟶ G.objects)
    HEq.rfl HEq.rfl (targetPairsAlpha G M) HEq.rfl
  exact eq_of_heq h

end QuasicoherentModule

end AlgebraicGeometry.Space

end
