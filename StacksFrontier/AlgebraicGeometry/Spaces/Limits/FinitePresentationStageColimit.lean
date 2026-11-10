module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLocalRingGlueing

/-!
# The filtered `2`-colimit of the categories of finite-presentation spaces over a system

Let `Z : I ⥤ BigFppfOver B S hS` be a diagram of stages indexed by a cofiltered category `I`.
Base change along the transition morphisms makes `i ↦ FP_{Z i}` a system of categories indexed by
`Iᵒᵖ`, which is filtered, and this file constructs its `2`-colimit
`AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit`: an object is a stage `i` together
with an algebraic space of finite presentation over `Z i`, and a morphism is a *germ*, that is an
equivalence class of morphisms `X|_{Z k} ⟶ Y|_{Z k}` over a stage `k` below the two stages, two of
them being identified when they agree after base change to a still earlier stage.

Base change is only pseudofunctorial, so germs are restricted through the comparison isomorphisms
`AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeFactorIso` of a factorisation.

## Main definitions

* `AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit`: the objects of the `2`-colimit.
* `AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit.push`: the restriction to an
  earlier stage of a morphism between base changes.
* `AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit.Rep` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit.Rel`: a representative of a germ,
  and the identification of two representatives.

## Main results

* `AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit.push_push`: restricting twice
  restricts along the composite.
* `AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit.rel_push`: a representative and its
  restriction define the same germ.
* `AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit.rel_compRepAt`: **the germ of a
  composite is well defined** — it depends neither on the stage at which the composition is
  performed nor on the representatives of the two germs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FinitePresentationSpacesOver

/-! ### Two elementary lemmas -/

/-- The image under a functor of a factorisation is a factorisation. -/
theorem map_comp_eq {C : Type*} [Category C] {I : Type*} [Category I] (Z : I ⥤ C) {l k m : I}
    {c : l ⟶ k} {d : k ⟶ m} {e : l ⟶ m} (h : c ≫ d = e) : Z.map c ≫ Z.map d = Z.map e := by
  rw [← Z.map_comp, h]

/-- A commuting square of isomorphisms read backwards along three of its sides. -/
theorem iso_hom_comp_inv_comp_inv {C : Type*} [Category C] {P Q R T : C} (α : P ≅ Q) (β : Q ≅ T)
    (γ : P ≅ R) (δ : R ≅ T) (h : α.hom ≫ β.hom = γ.hom ≫ δ.hom) :
    δ.hom ≫ β.inv ≫ α.inv = γ.inv := by
  rw [← Category.assoc, Iso.comp_inv_eq, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact h.symm

/-! ### Comparison of base changes along a factorisation -/

section Shift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Conjugating a morphism of base changes by the comparison isomorphisms of a factorisation.**
Out of a morphism between the base changes of two objects along `e₁` and `e₂` it produces one
between their base changes along the composites `c ≫ e₁` and `c ≫ e₂`. -/
noncomputable def shift {T₁ T₂ P R : BigFppfOver B S hS}
    (Xo : FinitePresentationSpacesOver B S hS T₁) (Yo : FinitePresentationSpacesOver B S hS T₂)
    {e₁ : R ⟶ T₁} {e₂ : R ⟶ T₂} (c : P ⟶ R) {d₁ : P ⟶ T₁} {d₂ : P ⟶ T₂}
    (h₁ : c ≫ e₁ = d₁) (h₂ : c ≫ e₂ = d₂)
    (f : (baseChange B S hS e₁).obj Xo ⟶ (baseChange B S hS e₂).obj Yo) :
    (baseChange B S hS d₁).obj Xo ⟶ (baseChange B S hS d₂).obj Yo :=
  (baseChangeFactorIso B S hS h₁).hom.app Xo ≫ (baseChange B S hS c).map f ≫
    (baseChangeFactorIso B S hS h₂).inv.app Yo

/-- The comparison depends on the morphism it is taken along, not on the proofs that the
composites are the prescribed ones. -/
theorem shift_congr {T₁ T₂ P R : BigFppfOver B S hS}
    (Xo : FinitePresentationSpacesOver B S hS T₁) (Yo : FinitePresentationSpacesOver B S hS T₂)
    {e₁ : R ⟶ T₁} {e₂ : R ⟶ T₂} {c c' : P ⟶ R} {d₁ : P ⟶ T₁} {d₂ : P ⟶ T₂}
    (h₁ : c ≫ e₁ = d₁) (h₂ : c ≫ e₂ = d₂) (h₁' : c' ≫ e₁ = d₁) (h₂' : c' ≫ e₂ = d₂)
    (h : c = c')
    (f : (baseChange B S hS e₁).obj Xo ⟶ (baseChange B S hS e₂).obj Yo) :
    shift B S hS Xo Yo c h₁ h₂ f = shift B S hS Xo Yo c' h₁' h₂' f := by
  subst h
  rfl

/-- Two morphisms with the same base change along `c` have the same comparison. -/
theorem shift_congr_hom {T₁ T₂ P R : BigFppfOver B S hS}
    (Xo : FinitePresentationSpacesOver B S hS T₁) (Yo : FinitePresentationSpacesOver B S hS T₂)
    {e₁ : R ⟶ T₁} {e₂ : R ⟶ T₂} (c : P ⟶ R) {d₁ : P ⟶ T₁} {d₂ : P ⟶ T₂}
    (h₁ : c ≫ e₁ = d₁) (h₂ : c ≫ e₂ = d₂)
    {f g : (baseChange B S hS e₁).obj Xo ⟶ (baseChange B S hS e₂).obj Yo}
    (h : (baseChange B S hS c).map f = (baseChange B S hS c).map g) :
    shift B S hS Xo Yo c h₁ h₂ f = shift B S hS Xo Yo c h₁ h₂ g := by
  change (baseChangeFactorIso B S hS h₁).hom.app Xo ≫ (baseChange B S hS c).map f ≫
      (baseChangeFactorIso B S hS h₂).inv.app Yo =
    (baseChangeFactorIso B S hS h₁).hom.app Xo ≫ (baseChange B S hS c).map g ≫
      (baseChangeFactorIso B S hS h₂).inv.app Yo
  rw [h]

/-- The comparison of a morphism determines its base change along `c`. -/
theorem baseChange_map_eq_of_shift_eq {T₁ T₂ P R : BigFppfOver B S hS}
    (Xo : FinitePresentationSpacesOver B S hS T₁) (Yo : FinitePresentationSpacesOver B S hS T₂)
    {e₁ : R ⟶ T₁} {e₂ : R ⟶ T₂} (c : P ⟶ R) {d₁ : P ⟶ T₁} {d₂ : P ⟶ T₂}
    (h₁ : c ≫ e₁ = d₁) (h₂ : c ≫ e₂ = d₂)
    {f g : (baseChange B S hS e₁).obj Xo ⟶ (baseChange B S hS e₂).obj Yo}
    (h : shift B S hS Xo Yo c h₁ h₂ f = shift B S hS Xo Yo c h₁ h₂ g) :
    (baseChange B S hS c).map f = (baseChange B S hS c).map g := by
  have h' : (baseChangeFactorIso B S hS h₁).hom.app Xo ≫ (baseChange B S hS c).map f ≫
        (baseChangeFactorIso B S hS h₂).inv.app Yo =
      (baseChangeFactorIso B S hS h₁).hom.app Xo ≫ (baseChange B S hS c).map g ≫
        (baseChangeFactorIso B S hS h₂).inv.app Yo := h
  exact (((baseChangeFactorIso B S hS h₂).app Yo).cancel_iso_inv_right _ _).mp
    ((((baseChangeFactorIso B S hS h₁).app Xo).cancel_iso_hom_left _ _).mp h')

/-- **The comparison of a composite is the composite of the comparisons.** -/
theorem shift_comp {T₁ T₂ T₃ P R : BigFppfOver B S hS}
    (Xo : FinitePresentationSpacesOver B S hS T₁) (Yo : FinitePresentationSpacesOver B S hS T₂)
    (Wo : FinitePresentationSpacesOver B S hS T₃) {e₁ : R ⟶ T₁} {e₂ : R ⟶ T₂} {e₃ : R ⟶ T₃}
    (c : P ⟶ R) {d₁ : P ⟶ T₁} {d₂ : P ⟶ T₂} {d₃ : P ⟶ T₃} (h₁ : c ≫ e₁ = d₁)
    (h₂ : c ≫ e₂ = d₂) (h₃ : c ≫ e₃ = d₃)
    (f : (baseChange B S hS e₁).obj Xo ⟶ (baseChange B S hS e₂).obj Yo)
    (g : (baseChange B S hS e₂).obj Yo ⟶ (baseChange B S hS e₃).obj Wo) :
    shift B S hS Xo Wo c h₁ h₃ (f ≫ g) =
      shift B S hS Xo Yo c h₁ h₂ f ≫ shift B S hS Yo Wo c h₂ h₃ g := by
  simp only [shift, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- **The comparison of an identity is the identity.** -/
theorem shift_id {T₁ P R : BigFppfOver B S hS}
    (Xo : FinitePresentationSpacesOver B S hS T₁) {e₁ : R ⟶ T₁} (c : P ⟶ R) {d₁ : P ⟶ T₁}
    (h₁ : c ≫ e₁ = d₁) :
    shift B S hS Xo Xo c h₁ h₁ (𝟙 ((baseChange B S hS e₁).obj Xo)) =
      𝟙 ((baseChange B S hS d₁).obj Xo) := by
  have hmap : (baseChange B S hS c).map (𝟙 ((baseChange B S hS e₁).obj Xo)) =
      𝟙 ((baseChange B S hS e₁ ⋙ baseChange B S hS c).obj Xo) :=
    CategoryTheory.Functor.map_id _ _
  change (baseChangeFactorIso B S hS h₁).hom.app Xo ≫
      (baseChange B S hS c).map (𝟙 ((baseChange B S hS e₁).obj Xo)) ≫
        (baseChangeFactorIso B S hS h₁).inv.app Xo = 𝟙 ((baseChange B S hS d₁).obj Xo)
  rw [hmap, Category.id_comp, Iso.hom_inv_id_app]

/-- **Comparing twice compares along the composite.** -/
theorem shift_shift {T₁ T₂ P Q R : BigFppfOver B S hS}
    (Xo : FinitePresentationSpacesOver B S hS T₁) (Yo : FinitePresentationSpacesOver B S hS T₂)
    {e₁ : R ⟶ T₁} {e₂ : R ⟶ T₂} (c : Q ⟶ R) (c' : P ⟶ Q) {d₁ : Q ⟶ T₁} {d₂ : Q ⟶ T₂}
    (h₁ : c ≫ e₁ = d₁) (h₂ : c ≫ e₂ = d₂) {g₁ : P ⟶ T₁} {g₂ : P ⟶ T₂} (k₁ : c' ≫ d₁ = g₁)
    (k₂ : c' ≫ d₂ = g₂) (m₁ : (c' ≫ c) ≫ e₁ = g₁) (m₂ : (c' ≫ c) ≫ e₂ = g₂)
    (f : (baseChange B S hS e₁).obj Xo ⟶ (baseChange B S hS e₂).obj Yo) :
    shift B S hS Xo Yo c' k₁ k₂ (shift B S hS Xo Yo c h₁ h₂ f) =
      shift B S hS Xo Yo (c' ≫ c) m₁ m₂ f := by
  have hc : c' ≫ c = c' ≫ c := rfl
  have hsrc := baseChangeFactorIso_assoc B S hS hc h₁ k₁ m₁ Xo
  have htgt := baseChangeFactorIso_assoc B S hS hc h₂ k₂ m₂ Yo
  have hnat := (baseChangeFactorIso B S hS hc).hom.naturality f
  have hcancel := iso_hom_comp_inv_comp_inv
    (Iso.app (baseChangeFactorIso B S hS k₂) Yo)
    ((baseChange B S hS c').mapIso (Iso.app (baseChangeFactorIso B S hS h₂) Yo))
    (Iso.app (baseChangeFactorIso B S hS m₂) Yo)
    (Iso.app (baseChangeFactorIso B S hS hc) ((baseChange B S hS e₂).obj Yo)) htgt
  simp only [Iso.app_hom, Iso.app_inv, Functor.mapIso_inv] at hcancel
  simp only [shift, Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map] at hnat
  rw [reassoc_of% hsrc, ← reassoc_of% hnat, hcancel]

end Shift

/-! ### Refinements in a cofiltered index category -/

section Cofiltered

variable {I : Type u} [Category.{u} I] [IsCofiltered I]

/-- Two parallel morphisms of a cofiltered category become equal after a refinement. -/
theorem exists_eq_comp {n₀ j : I} (f g : n₀ ⟶ j) : ∃ (n : I) (e : n ⟶ n₀), e ≫ f = e ≫ g :=
  ⟨_, IsCofiltered.eqHom f g, IsCofiltered.eq_condition f g⟩

/-- Four pairs of parallel morphisms of a cofiltered category become equal after a single
refinement. -/
theorem exists_eq_comp₄ {n₀ j₁ j₂ j₃ j₄ : I} (f₁ g₁ : n₀ ⟶ j₁) (f₂ g₂ : n₀ ⟶ j₂)
    (f₃ g₃ : n₀ ⟶ j₃) (f₄ g₄ : n₀ ⟶ j₄) :
    ∃ (n : I) (e : n ⟶ n₀), e ≫ f₁ = e ≫ g₁ ∧ e ≫ f₂ = e ≫ g₂ ∧ e ≫ f₃ = e ≫ g₃ ∧
      e ≫ f₄ = e ≫ g₄ := by
  obtain ⟨n₁, e₁, h₁⟩ := exists_eq_comp f₁ g₁
  obtain ⟨n₂, e₂, h₂⟩ := exists_eq_comp (e₁ ≫ f₂) (e₁ ≫ g₂)
  obtain ⟨n₃, e₃, h₃⟩ := exists_eq_comp (e₂ ≫ e₁ ≫ f₃) (e₂ ≫ e₁ ≫ g₃)
  obtain ⟨n₄, e₄, h₄⟩ := exists_eq_comp (e₃ ≫ e₂ ≫ e₁ ≫ f₄) (e₃ ≫ e₂ ≫ e₁ ≫ g₄)
  refine ⟨n₄, e₄ ≫ e₃ ≫ e₂ ≫ e₁, ?_, ?_, ?_, ?_⟩
  · simp only [Category.assoc, h₁]
  · simp only [Category.assoc, h₂]
  · simp only [Category.assoc, h₃]
  · simp only [Category.assoc, h₄]

end Cofiltered

/-! ### The objects of the colimit -/

section Defs

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {I : Type u}
  [Category.{u} I] (Z : I ⥤ BigFppfOver B S hS)

/-- **An object of the filtered `2`-colimit of the categories `FP_{Z i}`**: a stage of the system
together with an algebraic space of finite presentation over it. -/
structure StageColimit where
  /-- The stage the object lives over. -/
  idx : I
  /-- The algebraic space of finite presentation over that stage. -/
  obj : FinitePresentationSpacesOver B S hS (Z.obj idx)

end Defs

namespace StageColimit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {I : Type u}
  [Category.{u} I] {Z : I ⥤ BigFppfOver B S hS}

/-! ### Restriction of a morphism over a stage to an earlier stage -/

/-- **The restriction to an earlier stage of a morphism between the base changes of two objects
of the colimit**, along a transition `c` with prescribed composites `a` and `b`. -/
noncomputable def push (X Y : StageColimit B S hS Z) {k l : I} (A : k ⟶ X.idx) (Bb : k ⟶ Y.idx)
    (c : l ⟶ k) {a : l ⟶ X.idx} {b : l ⟶ Y.idx} (ha : c ≫ A = a) (hb : c ≫ Bb = b)
    (f : (baseChange B S hS (Z.map A)).obj X.obj ⟶ (baseChange B S hS (Z.map Bb)).obj Y.obj) :
    (baseChange B S hS (Z.map a)).obj X.obj ⟶ (baseChange B S hS (Z.map b)).obj Y.obj :=
  shift B S hS X.obj Y.obj (Z.map c) (map_comp_eq Z ha) (map_comp_eq Z hb) f

/-- Restriction depends on the transition it is taken along, not on the proofs that the
composites are the prescribed transitions. -/
theorem push_congr (X Y : StageColimit B S hS Z) {k l : I} (A : k ⟶ X.idx) (Bb : k ⟶ Y.idx)
    {c c' : l ⟶ k} {a : l ⟶ X.idx} {b : l ⟶ Y.idx} (ha : c ≫ A = a) (hb : c ≫ Bb = b)
    (ha' : c' ≫ A = a) (hb' : c' ≫ Bb = b) (h : c = c')
    (f : (baseChange B S hS (Z.map A)).obj X.obj ⟶ (baseChange B S hS (Z.map Bb)).obj Y.obj) :
    push X Y A Bb c ha hb f = push X Y A Bb c' ha' hb' f := by
  subst h
  rfl

/-- **Restricting a composite restricts the two factors**, through the base change of the object
over the intermediate stage. -/
theorem push_comp (X Y W : StageColimit B S hS Z) {k l : I} (A : k ⟶ X.idx) (M : k ⟶ Y.idx)
    (C : k ⟶ W.idx) (c : l ⟶ k) {a : l ⟶ X.idx} {m : l ⟶ Y.idx} {cc : l ⟶ W.idx}
    (ha : c ≫ A = a) (hm : c ≫ M = m) (hc : c ≫ C = cc)
    (f : (baseChange B S hS (Z.map A)).obj X.obj ⟶ (baseChange B S hS (Z.map M)).obj Y.obj)
    (g : (baseChange B S hS (Z.map M)).obj Y.obj ⟶ (baseChange B S hS (Z.map C)).obj W.obj) :
    push X W A C c ha hc (f ≫ g) = push X Y A M c ha hm f ≫ push Y W M C c hm hc g :=
  shift_comp B S hS X.obj Y.obj W.obj (Z.map c) (map_comp_eq Z ha) (map_comp_eq Z hm)
    (map_comp_eq Z hc) f g

/-- Restricting an identity morphism along a transition gives the identity. -/
theorem push_id (X : StageColimit B S hS Z) {k l : I} (A : k ⟶ X.idx) (c : l ⟶ k)
    {a : l ⟶ X.idx} (ha : c ≫ A = a) :
    push X X A A c ha ha (𝟙 ((baseChange B S hS (Z.map A)).obj X.obj)) =
      𝟙 ((baseChange B S hS (Z.map a)).obj X.obj) :=
  shift_id B S hS X.obj (Z.map c) (map_comp_eq Z ha)

/-- **Restricting twice restricts along the composite transition.** -/
theorem push_push (X Y : StageColimit B S hS Z) {k l m : I} (A : k ⟶ X.idx) (Bb : k ⟶ Y.idx)
    (c : l ⟶ k) (c' : m ⟶ l) {a : l ⟶ X.idx} {b : l ⟶ Y.idx} (ha : c ≫ A = a) (hb : c ≫ Bb = b)
    {a' : m ⟶ X.idx} {b' : m ⟶ Y.idx} (ha' : c' ≫ a = a') (hb' : c' ≫ b = b')
    (ha'' : (c' ≫ c) ≫ A = a') (hb'' : (c' ≫ c) ≫ Bb = b')
    (f : (baseChange B S hS (Z.map A)).obj X.obj ⟶ (baseChange B S hS (Z.map Bb)).obj Y.obj) :
    push X Y a b c' ha' hb' (push X Y A Bb c ha hb f) = push X Y A Bb (c' ≫ c) ha'' hb'' f := by
  refine (shift_shift B S hS X.obj Y.obj (Z.map c) (Z.map c') (map_comp_eq Z ha)
    (map_comp_eq Z hb) (map_comp_eq Z ha') (map_comp_eq Z hb')
    (by rw [Category.assoc, map_comp_eq Z ha, map_comp_eq Z ha'])
    (by rw [Category.assoc, map_comp_eq Z hb, map_comp_eq Z hb']) f).trans ?_
  exact shift_congr B S hS X.obj Y.obj _ _ (map_comp_eq Z ha'') (map_comp_eq Z hb'')
    (map_comp_eq Z rfl) f

/-- Restricting twice along two factorisations of the same transition gives the same result. -/
private theorem push_push_congr (X Y : StageColimit B S hS Z) {k l l' m : I} (A : k ⟶ X.idx)
    (Bb : k ⟶ Y.idx) (c : l ⟶ k) (c' : l' ⟶ k) (d : m ⟶ l) (d' : m ⟶ l') {a : l ⟶ X.idx}
    {b : l ⟶ Y.idx} {a' : l' ⟶ X.idx} {b' : l' ⟶ Y.idx} {x : m ⟶ X.idx} {y : m ⟶ Y.idx}
    (ha : c ≫ A = a) (hb : c ≫ Bb = b) (ha' : c' ≫ A = a') (hb' : c' ≫ Bb = b')
    (hx : d ≫ a = x) (hy : d ≫ b = y) (hx' : d' ≫ a' = x) (hy' : d' ≫ b' = y)
    (h : d ≫ c = d' ≫ c')
    (f : (baseChange B S hS (Z.map A)).obj X.obj ⟶ (baseChange B S hS (Z.map Bb)).obj Y.obj) :
    push X Y a b d hx hy (push X Y A Bb c ha hb f) =
      push X Y a' b' d' hx' hy' (push X Y A Bb c' ha' hb' f) := by
  rw [push_push X Y A Bb c d ha hb hx hy (by rw [Category.assoc, ha, hx])
      (by rw [Category.assoc, hb, hy]) f,
    push_push X Y A Bb c' d' ha' hb' hx' hy' (by rw [Category.assoc, ha', hx'])
      (by rw [Category.assoc, hb', hy']) f]
  exact push_congr X Y A Bb _ _ _ _ h f

/-! ### Germs -/

/-- **A representative of a morphism of the filtered `2`-colimit**: a stage below the stages of
the source and of the target, together with a morphism of the base changes of the two objects
to it. -/
structure Rep (X Y : StageColimit B S hS Z) where
  /-- The stage at which the morphism is given. -/
  idx : I
  /-- The transition from that stage to the stage of the source. -/
  toSrc : idx ⟶ X.idx
  /-- The transition from that stage to the stage of the target. -/
  toTgt : idx ⟶ Y.idx
  /-- The morphism of the two base changes. -/
  hom : (baseChange B S hS (Z.map toSrc)).obj X.obj ⟶
    (baseChange B S hS (Z.map toTgt)).obj Y.obj

variable {X Y W V : StageColimit B S hS Z}

/-- Two representatives over the same stage with the same transitions and the same morphism are
equal. -/
theorem Rep.mk_eq_mk {l : I} {a : l ⟶ X.idx} {b : l ⟶ Y.idx}
    {f g : (baseChange B S hS (Z.map a)).obj X.obj ⟶ (baseChange B S hS (Z.map b)).obj Y.obj}
    (h : f = g) : (Rep.mk l a b f : Rep X Y) = Rep.mk l a b g := by
  rw [h]

/-- The restriction of a representative to an earlier stage, as a representative. -/
noncomputable def Rep.pushTo (r : Rep X Y) {l : I} (c : l ⟶ r.idx) {a : l ⟶ X.idx}
    {b : l ⟶ Y.idx} (ha : c ≫ r.toSrc = a) (hb : c ≫ r.toTgt = b) : Rep X Y :=
  ⟨l, a, b, push X Y r.toSrc r.toTgt c ha hb r.hom⟩

/-- **Two representatives define the same morphism of the colimit** when they agree after
restriction to a common earlier stage. -/
def Rel (r r' : Rep X Y) : Prop :=
  ∃ (l : I) (u : l ⟶ r.idx) (v : l ⟶ r'.idx) (a : l ⟶ X.idx) (b : l ⟶ Y.idx)
    (hu : u ≫ r.toSrc = a) (hv : u ≫ r.toTgt = b) (hu' : v ≫ r'.toSrc = a)
    (hv' : v ≫ r'.toTgt = b),
    push X Y r.toSrc r.toTgt u hu hv r.hom = push X Y r'.toSrc r'.toTgt v hu' hv' r'.hom

/-- Every representative is related to itself. -/
theorem Rel.refl (r : Rep X Y) : Rel r r :=
  ⟨r.idx, 𝟙 _, 𝟙 _, r.toSrc, r.toTgt, Category.id_comp _, Category.id_comp _,
    Category.id_comp _, Category.id_comp _, rfl⟩

/-- The relation `Rel` on representatives is symmetric. -/
theorem Rel.symm {r r' : Rep X Y} (h : Rel r r') : Rel r' r := by
  obtain ⟨l, u, v, a, b, hu, hv, hu', hv', h⟩ := h
  exact ⟨l, v, u, a, b, hu', hv', hu, hv, h.symm⟩

variable [IsCofiltered I]

omit [IsCofiltered I] in
/-- **A representative and its restriction define the same morphism of the colimit.** -/
theorem rel_push (r : Rep X Y) {l : I} (c : l ⟶ r.idx) {a : l ⟶ X.idx} {b : l ⟶ Y.idx}
    (ha : c ≫ r.toSrc = a) (hb : c ≫ r.toTgt = b) : Rel (r.pushTo c ha hb) r := by
  refine ⟨l, 𝟙 l, c, a, b, Category.id_comp _, Category.id_comp _, ha, hb, ?_⟩
  refine (push_push X Y r.toSrc r.toTgt c (𝟙 l) ha hb (Category.id_comp a) (Category.id_comp b)
    (by rw [Category.id_comp, ha]) (by rw [Category.id_comp, hb]) r.hom).trans ?_
  exact push_congr X Y r.toSrc r.toTgt _ _ ha hb (Category.id_comp c) r.hom

/-- The relation `Rel` on representatives is transitive. -/
theorem Rel.trans {r r' r'' : Rep X Y} (h : Rel r r') (h' : Rel r' r'') : Rel r r'' := by
  obtain ⟨l, u, v, a, b, hu, hv, hu', hv', he⟩ := h
  obtain ⟨l', u', v', a', b', hp, hq, hp', hq', he'⟩ := h'
  obtain ⟨m₀, p₀, q₀, -⟩ := IsCofilteredOrEmpty.cone_objs (C := I) l l'
  obtain ⟨m, t, ht⟩ := exists_eq_comp (p₀ ≫ v) (q₀ ≫ u')
  have key : (t ≫ p₀) ≫ v = (t ≫ q₀) ≫ u' := by
    simpa only [Category.assoc] using ht
  have hA : (t ≫ p₀) ≫ a = (t ≫ q₀) ≫ a' := by
    rw [← hu', ← hp, ← Category.assoc, ← Category.assoc, key]
  have hBb : (t ≫ p₀) ≫ b = (t ≫ q₀) ≫ b' := by
    rw [← hv', ← hq, ← Category.assoc, ← Category.assoc, key]
  refine ⟨m, (t ≫ p₀) ≫ u, (t ≫ q₀) ≫ v', (t ≫ p₀) ≫ a, (t ≫ p₀) ≫ b,
    by rw [Category.assoc, hu], by rw [Category.assoc, hv],
    by rw [Category.assoc, hp', hA], by rw [Category.assoc, hq', hBb], ?_⟩
  have e₁ := push_push X Y r.toSrc r.toTgt u (t ≫ p₀) hu hv rfl rfl
    (by rw [Category.assoc, hu]) (by rw [Category.assoc, hv]) r.hom
  have e₂ := push_push X Y r'.toSrc r'.toTgt v (t ≫ p₀) hu' hv' rfl rfl
    (by rw [Category.assoc, hu']) (by rw [Category.assoc, hv']) r'.hom
  have e₃ := push_push X Y r'.toSrc r'.toTgt u' (t ≫ q₀) hp hq hA.symm hBb.symm
    (by rw [Category.assoc, hp, hA]) (by rw [Category.assoc, hq, hBb]) r'.hom
  have e₄ := push_push X Y r''.toSrc r''.toTgt v' (t ≫ q₀) hp' hq' hA.symm hBb.symm
    (by rw [Category.assoc, hp', hA]) (by rw [Category.assoc, hq', hBb]) r''.hom
  rw [← e₁, he, e₂, push_congr X Y r'.toSrc r'.toTgt (by rw [Category.assoc, hu'])
      (by rw [Category.assoc, hv']) (by rw [Category.assoc, hp, ← hA])
      (by rw [Category.assoc, hq, ← hBb]) key r'.hom, ← e₃, he', e₄]

/-- The equivalence relation `Rel` on representatives of morphisms `X ⟶ Y`. -/
instance setoid (X Y : StageColimit B S hS Z) : Setoid (Rep X Y) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-! ### Composition of germs -/

/-- **The composite of two representatives, taken at a prescribed common stage** below the two,
at which the two transitions to the stage of the middle object agree. -/
noncomputable def compRepAt (r : Rep X Y) (r' : Rep Y W) {n : I} (p : n ⟶ r.idx) (q : n ⟶ r'.idx)
    {A : n ⟶ X.idx} {M : n ⟶ Y.idx} {C : n ⟶ W.idx} (hA : p ≫ r.toSrc = A)
    (hM : p ≫ r.toTgt = M) (hM' : q ≫ r'.toSrc = M) (hC : q ≫ r'.toTgt = C) : Rep X W :=
  ⟨n, A, C, push X Y r.toSrc r.toTgt p hA hM r.hom ≫ push Y W r'.toSrc r'.toTgt q hM' hC r'.hom⟩

/-- **The germ of a composite is well defined**: it depends neither on the stage at which the
composition is performed, nor on the representatives of the two germs. -/
theorem rel_compRepAt {r₁ r₂ : Rep X Y} {r'₁ r'₂ : Rep Y W} (h : Rel r₁ r₂) (h' : Rel r'₁ r'₂)
    {n₁ : I} (p₁ : n₁ ⟶ r₁.idx) (q₁ : n₁ ⟶ r'₁.idx) {A₁ : n₁ ⟶ X.idx} {M₁ : n₁ ⟶ Y.idx}
    {C₁ : n₁ ⟶ W.idx} (hA₁ : p₁ ≫ r₁.toSrc = A₁) (hM₁ : p₁ ≫ r₁.toTgt = M₁)
    (hM₁' : q₁ ≫ r'₁.toSrc = M₁) (hC₁ : q₁ ≫ r'₁.toTgt = C₁)
    {n₂ : I} (p₂ : n₂ ⟶ r₂.idx) (q₂ : n₂ ⟶ r'₂.idx) {A₂ : n₂ ⟶ X.idx} {M₂ : n₂ ⟶ Y.idx}
    {C₂ : n₂ ⟶ W.idx} (hA₂ : p₂ ≫ r₂.toSrc = A₂) (hM₂ : p₂ ≫ r₂.toTgt = M₂)
    (hM₂' : q₂ ≫ r'₂.toSrc = M₂) (hC₂ : q₂ ≫ r'₂.toTgt = C₂) :
    Rel (compRepAt r₁ r'₁ p₁ q₁ hA₁ hM₁ hM₁' hC₁) (compRepAt r₂ r'₂ p₂ q₂ hA₂ hM₂ hM₂' hC₂) := by
  obtain ⟨l, u, v, a, b, hu, hv, hu', hv', he⟩ := h
  obtain ⟨l', u', v', a', b', hp, hq, hp', hq', he'⟩ := h'
  obtain ⟨n₁₂, E₁, E₂, -⟩ := IsCofilteredOrEmpty.cone_objs (C := I) n₁ n₂
  obtain ⟨nll, T, T', -⟩ := IsCofilteredOrEmpty.cone_objs (C := I) l l'
  obtain ⟨n₀, F, G, -⟩ := IsCofilteredOrEmpty.cone_objs (C := I) n₁₂ nll
  obtain ⟨n, e, k₁, k₂, k₃, k₄⟩ := exists_eq_comp₄
    ((F ≫ E₁) ≫ p₁) ((G ≫ T) ≫ u) ((F ≫ E₂) ≫ p₂) ((G ≫ T) ≫ v)
    ((F ≫ E₁) ≫ q₁) ((G ≫ T') ≫ u') ((F ≫ E₂) ≫ q₂) ((G ≫ T') ≫ v')
  have i₁ : (e ≫ F ≫ E₁) ≫ p₁ = (e ≫ G ≫ T) ≫ u := by
    simpa only [Category.assoc] using k₁
  have i₂ : (e ≫ F ≫ E₂) ≫ p₂ = (e ≫ G ≫ T) ≫ v := by
    simpa only [Category.assoc] using k₂
  have i₃ : (e ≫ F ≫ E₁) ≫ q₁ = (e ≫ G ≫ T') ≫ u' := by
    simpa only [Category.assoc] using k₃
  have i₄ : (e ≫ F ≫ E₂) ≫ q₂ = (e ≫ G ≫ T') ≫ v' := by
    simpa only [Category.assoc] using k₄
  have hsrc₁ : (e ≫ F ≫ E₁) ≫ A₁ = (e ≫ G ≫ T) ≫ a := by
    rw [← hA₁, ← hu, ← Category.assoc, i₁, Category.assoc]
  have hsrc₂ : (e ≫ F ≫ E₂) ≫ A₂ = (e ≫ G ≫ T) ≫ a := by
    rw [← hA₂, ← hu', ← Category.assoc, i₂, Category.assoc]
  have hmid₁ : (e ≫ F ≫ E₁) ≫ M₁ = (e ≫ G ≫ T) ≫ b := by
    rw [← hM₁, ← hv, ← Category.assoc, i₁, Category.assoc]
  have hmid₂ : (e ≫ F ≫ E₂) ≫ M₂ = (e ≫ G ≫ T) ≫ b := by
    rw [← hM₂, ← hv', ← Category.assoc, i₂, Category.assoc]
  have hmidt : (e ≫ G ≫ T') ≫ a' = (e ≫ G ≫ T) ≫ b := by
    rw [← hp, ← Category.assoc, ← i₃, Category.assoc, hM₁', hmid₁]
  have htgt₁ : (e ≫ F ≫ E₁) ≫ C₁ = (e ≫ G ≫ T') ≫ b' := by
    rw [← hC₁, ← hq, ← Category.assoc, i₃, Category.assoc]
  have htgt₂ : (e ≫ F ≫ E₂) ≫ C₂ = (e ≫ G ≫ T') ≫ b' := by
    rw [← hC₂, ← hq', ← Category.assoc, i₄, Category.assoc]
  refine ⟨n, e ≫ F ≫ E₁, e ≫ F ≫ E₂, (e ≫ G ≫ T) ≫ a, (e ≫ G ≫ T') ≫ b',
    hsrc₁, htgt₁, hsrc₂, htgt₂, ?_⟩
  change push X W A₁ C₁ (e ≫ F ≫ E₁) hsrc₁ htgt₁
      (push X Y r₁.toSrc r₁.toTgt p₁ hA₁ hM₁ r₁.hom ≫
        push Y W r'₁.toSrc r'₁.toTgt q₁ hM₁' hC₁ r'₁.hom) =
    push X W A₂ C₂ (e ≫ F ≫ E₂) hsrc₂ htgt₂
      (push X Y r₂.toSrc r₂.toTgt p₂ hA₂ hM₂ r₂.hom ≫
        push Y W r'₂.toSrc r'₂.toTgt q₂ hM₂' hC₂ r'₂.hom)
  rw [push_comp X Y W A₁ M₁ C₁ (e ≫ F ≫ E₁) hsrc₁ hmid₁ htgt₁,
    push_comp X Y W A₂ M₂ C₂ (e ≫ F ≫ E₂) hsrc₂ hmid₂ htgt₂]
  congr 1
  · rw [push_push_congr X Y r₁.toSrc r₁.toTgt p₁ u (e ≫ F ≫ E₁) (e ≫ G ≫ T) hA₁ hM₁ hu hv hsrc₁
        hmid₁ rfl rfl i₁ r₁.hom, he,
      push_push_congr X Y r₂.toSrc r₂.toTgt p₂ v (e ≫ F ≫ E₂) (e ≫ G ≫ T) hA₂ hM₂ hu' hv' hsrc₂
        hmid₂ rfl rfl i₂ r₂.hom]
  · rw [push_push_congr Y W r'₁.toSrc r'₁.toTgt q₁ u' (e ≫ F ≫ E₁) (e ≫ G ≫ T') hM₁' hC₁ hp hq
        hmid₁ htgt₁ hmidt rfl i₃ r'₁.hom, he',
      push_push_congr Y W r'₂.toSrc r'₂.toTgt q₂ v' (e ≫ F ≫ E₂) (e ≫ G ≫ T') hM₂' hC₂ hp' hq'
        hmid₂ htgt₂ hmidt rfl i₄ r'₂.hom]

/-! ### The colimit as a category -/

/-- A stage below the stages of two representatives at which their transitions to the stage of
the middle object agree, so that the two morphisms may be composed there. -/
structure Cospan (r : Rep X Y) (r' : Rep Y W) where
  /-- The stage both representatives are restricted to. -/
  idx : I
  /-- The transition to the stage of the first representative. -/
  fst : idx ⟶ r.idx
  /-- The transition to the stage of the second representative. -/
  snd : idx ⟶ r'.idx
  /-- The two transitions to the stage of the middle object agree. -/
  w : fst ≫ r.toTgt = snd ≫ r'.toSrc

/-- Two composable representatives have a common stage at which the two transitions to the
stage of the middle object agree. -/
theorem nonempty_cospan (r : Rep X Y) (r' : Rep Y W) : Nonempty (Cospan r r') := by
  obtain ⟨n₀, p₀, q₀, -⟩ := IsCofilteredOrEmpty.cone_objs (C := I) r.idx r'.idx
  obtain ⟨n, e, he⟩ := exists_eq_comp (p₀ ≫ r.toTgt) (q₀ ≫ r'.toSrc)
  refine ⟨⟨n, e ≫ p₀, e ≫ q₀, ?_⟩⟩
  simpa only [Category.assoc] using he

/-- A choice of stage at which two representatives are composed. -/
noncomputable def compStage (r : Rep X Y) (r' : Rep Y W) : Cospan r r' :=
  (nonempty_cospan r r').some

/-- The composite of two representatives. -/
noncomputable def compRep (r : Rep X Y) (r' : Rep Y W) : Rep X W :=
  compRepAt r r' (compStage r r').fst (compStage r r').snd rfl rfl (compStage r r').w.symm rfl

/-- The composite of two representatives is, as a germ, their composite taken at any common
stage. -/
theorem rel_compRep_compRepAt (r : Rep X Y) (r' : Rep Y W) {n : I} (p : n ⟶ r.idx)
    (q : n ⟶ r'.idx) {A : n ⟶ X.idx} {M : n ⟶ Y.idx} {C : n ⟶ W.idx}
    (hA : p ≫ r.toSrc = A) (hM : p ≫ r.toTgt = M) (hM' : q ≫ r'.toSrc = M)
    (hC : q ≫ r'.toTgt = C) : Rel (compRep r r') (compRepAt r r' p q hA hM hM' hC) :=
  rel_compRepAt (Rel.refl r) (Rel.refl r') (compStage r r').fst (compStage r r').snd rfl rfl
    (compStage r r').w.symm rfl p q hA hM hM' hC

/-- Composition of germs is well defined. -/
theorem rel_compRep {r₁ r₂ : Rep X Y} {r'₁ r'₂ : Rep Y W} (h : Rel r₁ r₂) (h' : Rel r'₁ r'₂) :
    Rel (compRep r₁ r'₁) (compRep r₂ r'₂) :=
  rel_compRepAt h h' (compStage r₁ r'₁).fst (compStage r₁ r'₁).snd rfl rfl
    (compStage r₁ r'₁).w.symm rfl (compStage r₂ r'₂).fst (compStage r₂ r'₂).snd rfl rfl
    (compStage r₂ r'₂).w.symm rfl

/-- The identity germ of an object of the colimit. -/
noncomputable def idRep (X : StageColimit B S hS Z) : Rep X X :=
  ⟨X.idx, 𝟙 X.idx, 𝟙 X.idx, 𝟙 ((baseChange B S hS (Z.map (𝟙 X.idx))).obj X.obj)⟩

/-- The composite of a representative with the identity germ is related to the representative. -/
theorem rel_comp_id (r : Rep X Y) : Rel (compRep r (idRep Y)) r := by
  refine Rel.trans (rel_compRep_compRepAt r (idRep Y) (𝟙 r.idx) r.toTgt (Category.id_comp _)
    (Category.id_comp _) (Category.comp_id _) (Category.comp_id _)) ?_
  have key : compRepAt r (idRep Y) (𝟙 r.idx) r.toTgt (Category.id_comp _) (Category.id_comp _)
        (Category.comp_id _) (Category.comp_id _) =
      r.pushTo (𝟙 r.idx) (Category.id_comp _) (Category.id_comp _) := by
    refine Rep.mk_eq_mk ?_
    change push X Y r.toSrc r.toTgt (𝟙 r.idx) (Category.id_comp _) (Category.id_comp _) r.hom ≫
        push Y Y (𝟙 Y.idx) (𝟙 Y.idx) r.toTgt (Category.comp_id _) (Category.comp_id _)
          (𝟙 ((baseChange B S hS (Z.map (𝟙 Y.idx))).obj Y.obj)) =
      push X Y r.toSrc r.toTgt (𝟙 r.idx) (Category.id_comp _) (Category.id_comp _) r.hom
    rw [push_id Y (𝟙 Y.idx) r.toTgt (Category.comp_id _), Category.comp_id]
  rw [key]
  exact rel_push r (𝟙 r.idx) (Category.id_comp _) (Category.id_comp _)

/-- The composite of the identity germ with a representative is related to the representative. -/
theorem rel_id_comp (r : Rep X Y) : Rel (compRep (idRep X) r) r := by
  refine Rel.trans (rel_compRep_compRepAt (idRep X) r r.toSrc (𝟙 r.idx) (Category.comp_id _)
    (Category.comp_id _) (Category.id_comp _) (Category.id_comp _)) ?_
  have key : compRepAt (idRep X) r r.toSrc (𝟙 r.idx) (Category.comp_id _) (Category.comp_id _)
        (Category.id_comp _) (Category.id_comp _) =
      r.pushTo (𝟙 r.idx) (Category.id_comp _) (Category.id_comp _) := by
    refine Rep.mk_eq_mk ?_
    change push X X (𝟙 X.idx) (𝟙 X.idx) r.toSrc (Category.comp_id _) (Category.comp_id _)
          (𝟙 ((baseChange B S hS (Z.map (𝟙 X.idx))).obj X.obj)) ≫
        push X Y r.toSrc r.toTgt (𝟙 r.idx) (Category.id_comp _) (Category.id_comp _) r.hom =
      push X Y r.toSrc r.toTgt (𝟙 r.idx) (Category.id_comp _) (Category.id_comp _) r.hom
    rw [push_id X (𝟙 X.idx) r.toSrc (Category.comp_id _), Category.id_comp]
  rw [key]
  exact rel_push r (𝟙 r.idx) (Category.id_comp _) (Category.id_comp _)

/-- Three representatives can be restricted to a single stage at which both middle transitions
agree. -/
theorem exists_triple (r : Rep X Y) (r' : Rep Y W) (r'' : Rep W V) :
    ∃ (n : I) (p : n ⟶ r.idx) (q : n ⟶ r'.idx) (s : n ⟶ r''.idx),
      p ≫ r.toTgt = q ≫ r'.toSrc ∧ q ≫ r'.toTgt = s ≫ r''.toSrc := by
  obtain ⟨n₁, P₀, Q₀, -⟩ := IsCofilteredOrEmpty.cone_objs (C := I) r.idx r'.idx
  obtain ⟨n₂, R₀, S₀, -⟩ := IsCofilteredOrEmpty.cone_objs (C := I) n₁ r''.idx
  obtain ⟨n, e, k₁, k₂, -, -⟩ := exists_eq_comp₄
    ((R₀ ≫ P₀) ≫ r.toTgt) ((R₀ ≫ Q₀) ≫ r'.toSrc) ((R₀ ≫ Q₀) ≫ r'.toTgt) (S₀ ≫ r''.toSrc)
    (𝟙 n₂) (𝟙 n₂) (𝟙 n₂) (𝟙 n₂)
  refine ⟨n, e ≫ R₀ ≫ P₀, e ≫ R₀ ≫ Q₀, e ≫ S₀, ?_, ?_⟩
  · simpa only [Category.assoc] using k₁
  · simpa only [Category.assoc] using k₂

/-- Composition of representatives is associative up to `Rel`. -/
theorem rel_assoc (r : Rep X Y) (r' : Rep Y W) (r'' : Rep W V) :
    Rel (compRep (compRep r r') r'') (compRep r (compRep r' r'')) := by
  obtain ⟨n, p, q, s, w₁, w₂⟩ := exists_triple r r' r''
  have hL : Rel (compRep (compRep r r') r'')
      (compRepAt (compRepAt r r' p q rfl w₁ rfl rfl) r'' (𝟙 n) s (Category.id_comp _)
        (Category.id_comp _) w₂.symm rfl) :=
    rel_compRepAt (rel_compRep_compRepAt r r' p q rfl w₁ rfl rfl) (Rel.refl r'')
      (compStage (compRep r r') r'').fst (compStage (compRep r r') r'').snd rfl rfl
      (compStage (compRep r r') r'').w.symm rfl (𝟙 n) s (Category.id_comp _)
      (Category.id_comp _) w₂.symm rfl
  have hR : Rel (compRepAt r (compRepAt r' r'' q s rfl rfl w₂.symm rfl) p (𝟙 n) rfl w₁
        (Category.id_comp _) (Category.id_comp _)) (compRep r (compRep r' r'')) :=
    rel_compRepAt (Rel.refl r) (rel_compRep_compRepAt r' r'' q s rfl rfl w₂.symm rfl).symm
      p (𝟙 n) rfl w₁ (Category.id_comp _) (Category.id_comp _)
      (compStage r (compRep r' r'')).fst (compStage r (compRep r' r'')).snd rfl rfl
      (compStage r (compRep r' r'')).w.symm rfl
  have key : compRepAt (compRepAt r r' p q rfl w₁ rfl rfl) r'' (𝟙 n) s (Category.id_comp _)
        (Category.id_comp _) w₂.symm rfl =
      compRepAt r (compRepAt r' r'' q s rfl rfl w₂.symm rfl) p (𝟙 n) rfl w₁
        (Category.id_comp _) (Category.id_comp _) := by
    refine Rep.mk_eq_mk ?_
    change push X W (p ≫ r.toSrc) (q ≫ r'.toTgt) (𝟙 n) (Category.id_comp _) (Category.id_comp _)
          (push X Y r.toSrc r.toTgt p rfl w₁ r.hom ≫
            push Y W r'.toSrc r'.toTgt q rfl rfl r'.hom) ≫
        push W V r''.toSrc r''.toTgt s w₂.symm rfl r''.hom =
      push X Y r.toSrc r.toTgt p rfl w₁ r.hom ≫
        push Y V (q ≫ r'.toSrc) (s ≫ r''.toTgt) (𝟙 n) (Category.id_comp _)
          (Category.id_comp _) (push Y W r'.toSrc r'.toTgt q rfl rfl r'.hom ≫
            push W V r''.toSrc r''.toTgt s w₂.symm rfl r''.hom)
    rw [push_comp X Y W (p ≫ r.toSrc) (q ≫ r'.toSrc) (q ≫ r'.toTgt) (𝟙 n)
        (Category.id_comp _) (Category.id_comp _) (Category.id_comp _),
      push_comp Y W V (q ≫ r'.toSrc) (q ≫ r'.toTgt) (s ≫ r''.toTgt) (𝟙 n)
        (Category.id_comp _) (Category.id_comp _) (Category.id_comp _),
      push_push X Y r.toSrc r.toTgt p (𝟙 n) rfl w₁ (Category.id_comp _) (Category.id_comp _)
        (by rw [Category.id_comp]) (by rw [Category.id_comp, w₁]) r.hom,
      push_push Y W r'.toSrc r'.toTgt q (𝟙 n) rfl rfl (Category.id_comp _) (Category.id_comp _)
        (by rw [Category.id_comp]) (by rw [Category.id_comp]) r'.hom,
      push_push W V r''.toSrc r''.toTgt s (𝟙 n) w₂.symm rfl (Category.id_comp _)
        (Category.id_comp _) (by rw [Category.id_comp, w₂]) (by rw [Category.id_comp]) r''.hom,
      push_congr X Y r.toSrc r.toTgt (by rw [Category.id_comp]) (by rw [Category.id_comp, w₁])
        rfl w₁ (Category.id_comp p) r.hom,
      push_congr Y W r'.toSrc r'.toTgt (by rw [Category.id_comp]) (by rw [Category.id_comp])
        rfl rfl (Category.id_comp q) r'.hom,
      push_congr W V r''.toSrc r''.toTgt (by rw [Category.id_comp, w₂])
        (by rw [Category.id_comp]) w₂.symm rfl (Category.id_comp s) r''.hom,
      Category.assoc]
  exact hL.trans (key ▸ hR)

/-- **The filtered `2`-colimit of the categories of algebraic spaces of finite presentation over
the stages of a cofiltered system**: an object is a space over a stage, and a morphism is a germ
of morphisms over the stages below. -/
noncomputable instance instCategory : Category (StageColimit B S hS Z) where
  Hom X Y := Quotient (setoid X Y)
  id X := Quotient.mk _ (idRep X)
  comp f g := Quotient.map₂ compRep (fun _ _ hr _ _ hr' ↦ rel_compRep hr hr') f g
  id_comp f := Quotient.inductionOn f fun r ↦ Quotient.sound (rel_id_comp r)
  comp_id f := Quotient.inductionOn f fun r ↦ Quotient.sound (rel_comp_id r)
  assoc f g h :=
    Quotient.inductionOn₃ f g h fun r r' r'' ↦ Quotient.sound (rel_assoc r r' r'')

/-- **The morphism of the colimit defined by a representative**, that is its germ. -/
def germ (r : Rep X Y) : X ⟶ Y := Quotient.mk (setoid X Y) r

/-- Two representatives have the same germ if and only if they are related by `Rel`. -/
theorem germ_eq_germ_iff {r r' : Rep X Y} : germ r = germ r' ↔ Rel r r' :=
  Quotient.eq_iff_equiv

/-- Every morphism of the colimit is the germ of a representative. -/
theorem exists_germ_eq (f : X ⟶ Y) : ∃ r : Rep X Y, germ r = f := Quotient.exists_rep f

/-- The composite of two germs is the germ of the composite of the representatives. -/
@[simp]
theorem germ_comp (r : Rep X Y) (r' : Rep Y W) : germ r ≫ germ r' = germ (compRep r r') := rfl

/-- The germ of the identity representative is the identity morphism. -/
@[simp]
theorem germ_idRep (X : StageColimit B S hS Z) : germ (idRep X) = 𝟙 X := rfl

end StageColimit

end AlgebraicGeometry.FinitePresentationSpacesOver

end
