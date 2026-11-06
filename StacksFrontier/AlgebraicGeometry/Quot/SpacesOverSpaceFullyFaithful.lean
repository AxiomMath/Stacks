module

public import StacksFrontier.AlgebraicGeometry.Quot.SpacesOverSpaceEssSurj

/-!
# Full faithfulness of base change along the points of an algebraic space

Let `T` be an algebraic space over the base scheme `S` of a big fppf site and `P` a property of
morphisms of algebraic spaces stable under base change. The base-change functor
`AlgebraicGeometry.SpacesOverSpace.baseChangeFunctor`, from algebraic spaces over `T` with property
`P` (and isomorphisms over `T`) to functors over the site from the points of `T` to the families
with property `P`, is fully faithful.

A morphism of presheaves out of `X` is determined by its values on the points `s : h_W ⟶ X`, and
such a point is the section, over the point `s ≫ (X ⟶ T)` of `T`, of the base change of `X`; so a
2-morphism between two base-change functors determines a morphism over `T`, and two isomorphisms
over `T` with the same base changes agree. The morphism so determined is an isomorphism because
its base change along every point of `T` is.

## Main results

* `AlgebraicGeometry.SpacesOverSpace.isIso_of_isIso_baseChangeCommaHom`: a morphism over `T` all
  of whose base changes along points of `T` are isomorphisms is an isomorphism.
* `AlgebraicGeometry.SpacesOverSpace.baseChangeFunctor_faithful`,
  `AlgebraicGeometry.SpacesOverSpace.baseChangeFunctor_full`: the base-change functor is faithful
  and full.

## References

* [Stacks Project, Tag 0E93](https://stacks.math.columbia.edu/tag/0E93)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SpacesOverSpace

universe u

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor
  AlgebraicSpaces.fiberProduct schemeSpace Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat MorphismProperty

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {P : MorphismProperty (AlgebraicSpaces B S hS)} {T : AlgebraicSpaces B S hS}

-- Instance search for presheaf pullbacks on the big fppf site needs more than the default budget.
set_option synthInstance.maxHeartbeats 400000

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_spacesOverSpaceFullyFaithful :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_spacesOverSpaceFullyFaithful
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Sections

variable (X : Over T)

/-- The point of `T` under a point `s` of `X` with values in a scheme `W`. -/
abbrev ptOf {W : BigFppfOver B S hS} (s : yoneda.obj W ⟶ X.left.obj) :
    (pointsCategory B S hS T).obj :=
  pt W (yonedaEquiv (s ≫ X.hom.hom))

/-- The point of `T` under `s` is the composite of `s` with the structure morphism of `X`. -/
theorem pointMap_ptOf {W : BigFppfOver B S hS} (s : yoneda.obj W ⟶ X.left.obj) :
    (pointMap (ptOf X s)).hom = s ≫ X.hom.hom :=
  yonedaEquiv.symm_apply_apply _

/-- The section over `W` of the base change of `X` along the point of `T` under `s`, named by
`s`. -/
def secOf {W : BigFppfOver B S hS} (s : yoneda.obj W ⟶ X.left.obj) :
    yoneda.obj W ⟶ Limits.pullback (pointMap (ptOf X s)).hom X.hom.hom :=
  pullback.lift (𝟙 _) s (by rw [Category.id_comp, pointMap_ptOf])

/-- The section `secOf X s` composed with the first projection is the identity. -/
@[reassoc]
theorem secOf_fst {W : BigFppfOver B S hS} (s : yoneda.obj W ⟶ X.left.obj) :
    secOf X s ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The section `secOf X s` composed with the second projection is `s`. -/
@[reassoc]
theorem secOf_snd {W : BigFppfOver B S hS} (s : yoneda.obj W ⟶ X.left.obj) :
    secOf X s ≫ pullback.snd _ _ = s :=
  pullback.lift_snd _ _ _

/-- Every point of a base change of `X` along a point `a` of `T` is a section named by a point of
`X`, transported along a morphism of points of `T` into `a`. -/
theorem exists_eq_secOf_comp {W : BigFppfOver B S hS} {a : (pointsCategory B S hS T).obj}
    (p : yoneda.obj W ⟶ Limits.pullback (pointMap a).hom X.hom.hom) (q : yoneda.obj W ⟶ X.left.obj)
    (hq : p ≫ pullback.snd _ _ = q) :
    ∃ v : ptOf X q ⟶ a, p = secOf X q ≫ (baseChangeCommaMap X v).left.hom := by
  subst hq
  let g₀ : W ⟶ a.base := Yoneda.fullyFaithful.preimage (p ≫ pullback.fst _ _)
  have hg₀ : yoneda.map g₀ = p ≫ pullback.fst _ _ := Yoneda.fullyFaithful.map_preimage _
  have h : yonedaEquiv ((p ≫ pullback.snd _ _) ≫ X.hom.hom) = T.obj.map g₀.op a.fiber.as := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← hg₀]
    show yonedaEquiv (yoneda.map g₀ ≫ yonedaEquiv.symm a.fiber.as) = _
    rw [yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
  refine ⟨toPoint g₀ h, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeCommaMap_left_fst, secOf_fst_assoc]
    exact hg₀.symm
  · rw [Category.assoc, baseChangeCommaMap_left_snd, secOf_snd]

end Sections

/-- A morphism over `T` whose base change along every point of `T` is an isomorphism is an
isomorphism of the underlying presheaves. -/
theorem isIso_of_isIso_baseChangeCommaHom {X Y : Over T} (φ : X ⟶ Y)
    (h : ∀ a : (pointsCategory B S hS T).obj, IsIso (baseChangeCommaHom φ a).left.hom) :
    IsIso φ.left.hom := by
  suffices hW : ∀ W, IsIso (φ.left.hom.app W) from NatIso.isIso_of_isIso_app _
  rintro ⟨W⟩
  rw [isIso_iff_bijective]
  constructor
  · intro x₁ x₂ hx
    let s₁ := yonedaEquiv.symm x₁
    let s₂ := yonedaEquiv.symm x₂
    have hs : s₁ ≫ φ.left.hom = s₂ ≫ φ.left.hom := by
      simp only [s₁, s₂, yonedaEquiv_symm_naturality_right]
      exact congrArg _ hx
    have hT : s₂ ≫ X.hom.hom = s₁ ≫ X.hom.hom := by
      have hw : φ.left.hom ≫ Y.hom.hom = X.hom.hom := congrArg (fun k => k.hom) (Over.w φ)
      rw [← hw, ← Category.assoc, ← hs, Category.assoc]
    let σ₂ : yoneda.obj W ⟶ Limits.pullback (pointMap (ptOf X s₁)).hom X.hom.hom :=
      pullback.lift (𝟙 _) s₂ (by rw [Category.id_comp, pointMap_ptOf, hT])
    have key : secOf X s₁ ≫ (baseChangeCommaHom φ (ptOf X s₁)).left.hom =
        σ₂ ≫ (baseChangeCommaHom φ (ptOf X s₁)).left.hom := by
      apply pullback.hom_ext (f := (pointMap (ptOf X s₁)).hom) (g := Y.hom.hom)
      · rw [Category.assoc, Category.assoc, baseChangeCommaHom_left_fst, secOf_fst]
        exact (pullback.lift_fst _ _ _).symm
      · rw [Category.assoc, Category.assoc, baseChangeCommaHom_left_snd, secOf_snd_assoc, hs,
          pullback.lift_snd_assoc]
    have hσ : secOf X s₁ = σ₂ := by
      have := h (ptOf X s₁)
      exact (cancel_mono (baseChangeCommaHom φ (ptOf X s₁)).left.hom).1 key
    have h₁₂ : s₁ = s₂ := by
      rw [← secOf_snd X s₁, hσ]
      exact pullback.lift_snd _ _ _
    exact yonedaEquiv.symm.injective h₁₂
  · intro y
    let s := yonedaEquiv.symm y
    let a := ptOf Y s
    have := h a
    refine ⟨yonedaEquiv ((secOf Y s ≫ inv (baseChangeCommaHom φ a).left.hom) ≫
      pullback.snd (pointMap a).hom X.hom.hom), ?_⟩
    rw [← yonedaEquiv_comp, Category.assoc, Category.assoc, ← baseChangeCommaHom_left_snd φ a,
      IsIso.inv_hom_id_assoc, secOf_snd]
    exact Equiv.apply_symm_apply _ _

/-- Two transports along mutually inverse equalities of objects around an identity cancel. -/
theorem eqToHom_comp_id_comp_eqToHom {C : Type*} [Category* C] {X Y : C} (h₁ : X = Y)
    (h₂ : Y = X) : eqToHom h₁ ≫ 𝟙 Y ≫ eqToHom h₂ = 𝟙 X := by
  subst h₁
  simp

section Based

variable [P.IsStableUnderBaseChange] {X Y : SpacesOver B S hS P T}
  (η : baseChangeBased X ⟶ baseChangeBased Y)

/-- The base of each component of a 2-morphism between base-change functors is the identity. -/
theorem app_right_eq (a : (pointsCategory B S hS T).obj) :
    (η.app a).hom.hom.right = 𝟙 a.base := by
  have : (cartesianProjection B S hS P).IsHomLift (𝟙 a.base) (η.app a) := η.isHomLift' a
  have h := IsHomLift.fac' (cartesianProjection B S hS P) (𝟙 a.base) (η.app a)
  change (η.app a).hom.hom.right = _ at h
  rw [h]
  exact eqToHom_comp_id_comp_eqToHom _ _

/-- The map of base changes underlying a component of a 2-morphism between base-change
functors. -/
abbrev appLeft (a : (pointsCategory B S hS T).obj) :
    Limits.pullback (pointMap a).hom X.1.of.hom.hom ⟶ Limits.pullback (pointMap a).hom Y.1.of.hom.hom :=
  (η.app a).hom.hom.left.hom

/-- The map `appLeft η a` commutes with the first projections to the point `a`. -/
@[reassoc]
theorem appLeft_fst (a : (pointsCategory B S hS T).obj) :
    appLeft η a ≫ pullback.fst (pointMap a).hom Y.1.of.hom.hom =
      pullback.fst (pointMap a).hom X.1.of.hom.hom := by
  have w := (η.app a).hom.hom.w
  rw [app_right_eq] at w
  exact (w.trans (congrArg (fun k => _ ≫ k) (yoneda.map_id a.base))).trans (Category.comp_id _)

/-- The maps `appLeft η a` commute with the transition maps of base changes along a morphism of
points of `T`. -/
theorem appLeft_naturality {a' a : (pointsCategory B S hS T).obj} (v : a' ⟶ a) :
    (baseChangeCommaMap X.1.of v).left.hom ≫ appLeft η a =
      appLeft η a' ≫ (baseChangeCommaMap Y.1.of v).left.hom :=
  congrArg (fun k => k.hom.hom.left.hom) (η.naturality v)

/-- The image of a point of `X` under the morphism determined by `η`. -/
def phiYoneda {W : BigFppfOver B S hS} (s : yoneda.obj W ⟶ X.1.of.left.obj) :
    yoneda.obj W ⟶ Y.1.of.left.obj :=
  secOf X.1.of s ≫ appLeft η (ptOf X.1.of s) ≫ pullback.snd _ _

/-- The image `phiYoneda η s` lies over the same point of `T` as `s`. -/
theorem phiYoneda_comp_hom {W : BigFppfOver B S hS} (s : yoneda.obj W ⟶ X.1.of.left.obj) :
    phiYoneda η s ≫ Y.1.of.hom.hom = s ≫ X.1.of.hom.hom := by
  rw [phiYoneda, Category.assoc, Category.assoc, ← pullback.condition, appLeft_fst_assoc,
    secOf_fst_assoc, pointMap_ptOf]

/-- The construction `phiYoneda η` is natural in the scheme `W`. -/
theorem phiYoneda_naturality {W W' : BigFppfOver B S hS} (g : W' ⟶ W)
    (s : yoneda.obj W ⟶ X.1.of.left.obj) :
    yoneda.map g ≫ phiYoneda η s = phiYoneda η (yoneda.map g ≫ s) := by
  obtain ⟨v, hv⟩ := exists_eq_secOf_comp X.1.of (yoneda.map g ≫ secOf X.1.of s)
    (yoneda.map g ≫ s) (by rw [Category.assoc, secOf_snd])
  rw [phiYoneda, ← Category.assoc, hv, Category.assoc,
    ← Category.assoc (baseChangeCommaMap _ v).left.hom, appLeft_naturality, Category.assoc,
    baseChangeCommaMap_left_snd]
  rfl

/-- The morphism of presheaves determined by a 2-morphism between base-change functors. -/
def phi : X.1.of.left.obj ⟶ Y.1.of.left.obj where
  app W := ↾fun x => yonedaEquiv (phiYoneda η (yonedaEquiv.symm x))
  naturality {W W'} f := by
    apply ConcreteCategory.hom_ext
    intro x
    change yonedaEquiv (phiYoneda η (yonedaEquiv.symm (X.1.of.left.obj.map f x))) =
      Y.1.of.left.obj.map f (yonedaEquiv (phiYoneda η (yonedaEquiv.symm x)))
    rw [yonedaEquiv_naturality', phiYoneda_naturality, yonedaEquiv_symm_map]

/-- Composing a point `s` of `X` with `phi η` gives `phiYoneda η s`. -/
theorem comp_phi {W : BigFppfOver B S hS} (s : yoneda.obj W ⟶ X.1.of.left.obj) :
    s ≫ phi η = phiYoneda η s := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  show yonedaEquiv (phiYoneda η (yonedaEquiv.symm (yonedaEquiv s))) =
    yonedaEquiv (phiYoneda η s)
  rw [Equiv.symm_apply_apply]

/-- The morphism over `T` determined by a 2-morphism between base-change functors. -/
def phiOver : X.1.of ⟶ Y.1.of :=
  Over.homMk (ObjectProperty.homMk (phi η)) (by
    apply ObjectProperty.hom_ext
    apply hom_ext_yoneda
    intro W s
    change s ≫ phi η ≫ Y.1.of.hom.hom = s ≫ X.1.of.hom.hom
    rw [← Category.assoc, comp_phi, phiYoneda_comp_hom])

/-- The underlying morphism of presheaves of `phiOver η` is `phi η`. -/
theorem phiOver_left_hom : (phiOver η).left.hom = phi η :=
  rfl

/-- The base changes of the morphism determined by `η` are the components of `η`. -/
theorem baseChangeCommaHom_phiOver (a : (pointsCategory B S hS T).obj) :
    (baseChangeCommaHom (phiOver η) a).left.hom = appLeft η a := by
  apply hom_ext_yoneda
  intro W p
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, baseChangeCommaHom_left_fst, appLeft_fst]
  · rw [Category.assoc, Category.assoc, baseChangeCommaHom_left_snd, phiOver_left_hom,
      ← Category.assoc, comp_phi]
    obtain ⟨v, hv⟩ := exists_eq_secOf_comp X.1.of p (p ≫ pullback.snd _ _) rfl
    conv_rhs => rw [hv]
    rw [Category.assoc, ← Category.assoc (baseChangeCommaMap _ v).left.hom, appLeft_naturality,
      Category.assoc, baseChangeCommaMap_left_snd]
    rfl

/-- Each component of a 2-morphism between base-change functors is an isomorphism. -/
theorem isIso_appLeft (a : (pointsCategory B S hS T).obj) : IsIso (appLeft η a) := by
  have hc : (spacesProjection B S hS).IsStronglyCartesian
      ((spacesProjection B S hS).map (η.app a).hom.hom) (η.app a).hom.hom := (η.app a).property
  have hb : IsIso ((spacesProjection B S hS).map (η.app a).hom.hom) := by
    show IsIso (η.app a).hom.hom.right
    rw [app_right_eq]
    exact ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩
  have hiso : IsIso (η.app a).hom.hom :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (spacesProjection B S hS)
      (f := (spacesProjection B S hS).map (η.app a).hom.hom) (η.app a).hom.hom
  have : IsIso (η.app a).hom.hom.left :=
    inferInstanceAs (IsIso ((Comma.fst _ _).map (η.app a).hom.hom))
  exact inferInstanceAs (IsIso ((ObjectProperty.ι _).map (η.app a).hom.hom.left))

/-- The morphism over `T` determined by a 2-morphism between base-change functors is an
isomorphism. -/
theorem isIso_phiOver : IsIso (phiOver η) := by
  have h : IsIso (phiOver η).left.hom := isIso_of_isIso_baseChangeCommaHom (phiOver η) fun a => by
    rw [baseChangeCommaHom_phiOver]
    exact isIso_appLeft η a
  have h' : IsIso ((ObjectProperty.ι _).map (phiOver η).left) := h
  have : IsIso (phiOver η).left := isIso_of_reflects_iso _ (ObjectProperty.ι _)
  have h'' : IsIso ((Over.forget T).map (phiOver η)) := this
  exact isIso_of_reflects_iso _ (Over.forget T)

end Based

section FullyFaithful

variable [P.IsStableUnderBaseChange]

/-- **Faithfulness in Stacks 0E93.** Two isomorphisms over `T` with the same base changes along
every point of `T` agree. -/
instance baseChangeFunctor_faithful :
    (baseChangeFunctor (B := B) (S := S) (hS := hS) (P := P) (T := T)).Faithful where
  map_injective {X Y} {e₁ e₂} h := by
    apply ObjectProperty.hom_ext
    apply Core.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply hom_ext_yoneda
    intro W s
    have hh : (baseChangeCommaHom e₁.hom.iso.hom (ptOf X.1.of s)).left.hom =
        (baseChangeCommaHom e₂.hom.iso.hom (ptOf X.1.of s)).left.hom :=
      congrArg (fun η => (η.app (ptOf X.1.of s)).hom.hom.left.hom) h
    rw [← secOf_snd X.1.of s, Category.assoc, Category.assoc,
      ← baseChangeCommaHom_left_snd e₁.hom.iso.hom (ptOf X.1.of s),
      ← baseChangeCommaHom_left_snd e₂.hom.iso.hom (ptOf X.1.of s), hh]

/-- **Fullness in Stacks 0E93.** Every 2-morphism between base-change functors is induced by an
isomorphism over `T`. -/
instance baseChangeFunctor_full :
    (baseChangeFunctor (B := B) (S := S) (hS := hS) (P := P) (T := T)).Full where
  map_surjective {X Y} η := by
    have := isIso_phiOver η
    refine ⟨ObjectProperty.homMk ⟨asIso (phiOver η)⟩, ?_⟩
    apply BasedNatTrans.ext
    ext a
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · apply ObjectProperty.hom_ext
      exact baseChangeCommaHom_phiOver η a
    · exact (app_right_eq η a).symm

end FullyFaithful

end AlgebraicGeometry.SpacesOverSpace

end
