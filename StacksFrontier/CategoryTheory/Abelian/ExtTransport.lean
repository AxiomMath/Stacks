module

public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# Transporting `Ext` classes along exact functors

For an exact functor `F : C ⥤ D`, maps `a : A' ⟶ F A` and `b : F B ⟶ B'` turn a class
`x ∈ Ext^n(A, B)` into `a ∘ F(x) ∘ b ∈ Ext^n(A', B')`. Restriction maps on étale cohomology along
a morphism of schemes, read through comparisons of inverse images, are of this form. This file
records the calculus of such transports and two criteria for bijectivity.

## Main definitions

* `Stacks.ExtTransport.sandwich`: `x ↦ a ∘ x ∘ b` for maps of degree zero.
* `Stacks.ExtTransport.transport`: `x ↦ a ∘ F(x) ∘ b`.

## Main results

* `Stacks.ExtTransport.transport_transport`: two transports compose to the transport along the
  composite functor, read through an isomorphism `F ≅ F₁ ⋙ F₂`.
* `Stacks.ExtTransport.bijective_transport_of_isIso`: for an adjunction `L ⊣ R` of exact functors,
  if the adjoint `L A ⟶ P` of `a : A ⟶ R P` is an isomorphism, then `x ↦ a ∘ R(x)` is a bijection
  `Ext^n(P, N) → Ext^n(A, R N)`.
* `Stacks.ExtTransport.isIso_homEquiv_symm_of_isIso_map`: the adjoint of a unit-type map stays an
  isomorphism after base change along a square whose base change map is invertible.
-/

@[expose] public noncomputable section

universe w w' w'' v v' v'' v''' u u' u'' u'''

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Stacks.ExtTransport

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]

section Sandwich

variable [HasExt.{w} C]

/-- `x ↦ a ∘ x ∘ b` for maps `a : A' ⟶ A` and `b : B ⟶ B'`. -/
def sandwich {A A' B B' : C} (a : A' ⟶ A) (b : B ⟶ B') (n : ℕ) :
    Ext.{w} A B n →+ Ext.{w} A' B' n :=
  ((Ext.mk₀ a).precomp B' (zero_add n)).comp ((Ext.mk₀ b).postcomp A (add_zero n))

/-- `sandwich a b n x` is the composite `a ∘ x ∘ b` of `Ext` classes. -/
theorem sandwich_apply {A A' B B' : C} (a : A' ⟶ A) (b : B ⟶ B') (n : ℕ) (x : Ext.{w} A B n) :
    sandwich a b n x = (Ext.mk₀ a).comp (x.comp (Ext.mk₀ b) (add_zero n)) (zero_add n) :=
  rfl

/-- Two successive sandwiches are the sandwich by the composite maps. -/
theorem sandwich_sandwich {A A' A'' B B' B'' : C} (a : A' ⟶ A) (b : B ⟶ B') (a' : A'' ⟶ A')
    (b' : B' ⟶ B'') (n : ℕ) (x : Ext.{w} A B n) :
    sandwich a' b' n (sandwich a b n x) = sandwich (a' ≫ a) (b ≫ b') n x := by
  simp only [sandwich_apply, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]

/-- The sandwich by identity maps is the identity. -/
theorem sandwich_id {A B : C} (n : ℕ) (x : Ext.{w} A B n) :
    sandwich (𝟙 A) (𝟙 B) n x = x := by
  rw [sandwich_apply, Ext.comp_mk₀_id, Ext.mk₀_id_comp]

/-- A sandwich with identity on the right is precomposition with the class of the map. -/
private theorem sandwich_id_right {A A' B : C} (u : A' ⟶ A) (n : ℕ) (x : Ext.{w} A B n) :
    sandwich u (𝟙 B) n x = (Ext.mk₀ u).comp x (zero_add n) := by
  rw [sandwich_apply, Ext.comp_mk₀_id]

/-- A sandwich with identity on the left is postcomposition with the class of the map. -/
private theorem sandwich_id_left {A B B' : C} (c : B ⟶ B') (n : ℕ) (x : Ext.{w} A B n) :
    sandwich (𝟙 A) c n x = x.comp (Ext.mk₀ c) (add_zero n) := by
  rw [sandwich_apply, Ext.mk₀_id_comp]

/-- The sandwich by isomorphisms is a bijection. -/
theorem sandwich_bijective {A A' B B' : C} (a : A' ⟶ A) (b : B ⟶ B') [IsIso a] [IsIso b]
    (n : ℕ) : Function.Bijective (sandwich a b n : Ext.{w} A B n → Ext.{w} A' B' n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨sandwich (inv a) (inv b) n, fun x => ?_,
    fun x => ?_⟩ <;> simp [sandwich_sandwich, sandwich_id]

/-- A sandwich by a map of short exact sequences passes through their classes. -/
theorem sandwich_extClass_comp {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) {B B' : C} (b : B ⟶ B') (n : ℕ)
    (y : Ext.{w} S₂.X₁ B n) :
    sandwich φ.τ₃ b (n + 1) (h₂.extClass.comp y (add_comm 1 n)) =
      h₁.extClass.comp (sandwich φ.τ₁ b n y) (add_comm 1 n) := by
  rw [sandwich_apply, sandwich_apply, Ext.comp_assoc_of_third_deg_zero,
    ← Ext.comp_assoc (a₁ := 0) (a₂ := 1) (a₃ := n) (a₁₂ := 1) (a₂₃ := n + 1) (a := n + 1) _ _ _
      (by lia) (by lia) (by lia),
    ← h₁.extClass_naturality h₂ φ,
    Ext.comp_assoc (a₁ := 1) (a₂ := 0) (a₃ := n) (a₁₂ := 1) (a₂₃ := n) (a := n + 1) _ _ _
      (by lia) (by lia) (by lia)]

/-- If `f ≫ g = 0`, then `f ∘ g ∘ y = 0` for every `Ext` class `y`. -/
theorem mk₀_comp_mk₀_comp_eq_zero {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0)
    {n : ℕ} (y : Ext.{w} Z W n) :
    (Ext.mk₀ f).comp ((Ext.mk₀ g).comp y (zero_add n)) (zero_add n) = 0 := by
  rw [Ext.mk₀_comp_mk₀_assoc, hfg, Ext.mk₀_zero, Ext.zero_comp]

/-- For a short exact sequence `S`, the class `S.f ∘ S.g ∘ y` vanishes for every `y`. -/
theorem mk₀_f_comp_mk₀_g_comp {S : ShortComplex C} (_hS : S.ShortExact) {W : C} {n : ℕ}
    (y : Ext.{w} S.X₃ W n) :
    (Ext.mk₀ S.f).comp ((Ext.mk₀ S.g).comp y (zero_add n)) (zero_add n) = 0 :=
  mk₀_comp_mk₀_comp_eq_zero _ _ S.zero y

/-- Postcomposition with the class of an isomorphism is injective on `Ext`. -/
theorem comp_mk₀_injective {A B B' : C} (e : B ≅ B') (n : ℕ) :
    Function.Injective (fun x : Ext.{w} A B n => x.comp (Ext.mk₀ e.hom) (add_zero n)) := by
  intro x y h
  have := congrArg (fun z => sandwich (𝟙 A) e.inv n z) h
  simpa [sandwich_sandwich, sandwich_apply, Ext.comp_mk₀_id, Ext.mk₀_id_comp] using this

/-- Postcomposition with the class of an isomorphism vanishes exactly on the zero class. -/
theorem comp_mk₀_eq_zero_iff {A B B' : C} (e : B ≅ B') {n : ℕ} (x : Ext.{w} A B n) :
    x.comp (Ext.mk₀ e.hom) (add_zero n) = 0 ↔ x = 0 := by
  refine ⟨fun h => comp_mk₀_injective e n
    (h.trans (Ext.zero_comp A n (Ext.mk₀ e.hom) n (add_zero n)).symm), fun h => ?_⟩
  rw [h, Ext.zero_comp]

end Sandwich

section Transport

variable [HasExt.{w} C] [HasExt.{w'} D] [HasExt.{w''} E]

/-- `x ↦ a ∘ F(x) ∘ b` for an exact functor `F` and maps `a : A' ⟶ F A`, `b : F B ⟶ B'`. -/
def transport (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A B : C} {A' B' : D} (a : A' ⟶ F.obj A) (b : F.obj B ⟶ B') (n : ℕ) :
    Ext.{w} A B n →+ Ext.{w'} A' B' n :=
  (sandwich a b n).comp (F.mapExtAddHom A B n)

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- `transport F a b n x` is the sandwich of `F(x)` by `a` and `b`. -/
theorem transport_apply {A B : C} {A' B' : D} (a : A' ⟶ F.obj A) (b : F.obj B ⟶ B') (n : ℕ)
    (x : Ext.{w} A B n) :
    transport F a b n x = sandwich a b n (x.mapExactFunctor F) :=
  rfl

/-- A sandwich of a transport is the transport along the composite maps. -/
theorem sandwich_transport {A B : C} {A' A'' B' B'' : D} (a : A' ⟶ F.obj A) (b : F.obj B ⟶ B')
    (a' : A'' ⟶ A') (b' : B' ⟶ B'') (n : ℕ) (x : Ext.{w} A B n) :
    sandwich a' b' n (transport F a b n x) = transport F (a' ≫ a) (b ≫ b') n x :=
  sandwich_sandwich _ _ _ _ _ _

/-- The transport of a sandwich by `a₀` and `b₀` is the transport along `a ≫ F a₀` and
`F b₀ ≫ b`. -/
theorem transport_sandwich {A A₀ B B₀ : C} {A' B' : D} (a₀ : A₀ ⟶ A) (b₀ : B ⟶ B₀)
    (a : A' ⟶ F.obj A₀) (b : F.obj B₀ ⟶ B') (n : ℕ) (x : Ext.{w} A B n) :
    transport F a b n (sandwich a₀ b₀ n x) = transport F (a ≫ F.map a₀) (F.map b₀ ≫ b) n x := by
  rw [transport_apply, transport_apply, sandwich_apply a₀ b₀, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]
  rw [← sandwich_apply, sandwich_sandwich]

/-- The transport of `u ∘ x` along `a` is the transport of `x` along `a ≫ F u`. -/
theorem transport_mk₀_comp {A A₁ B : C} {A' B' : D} (u : A₁ ⟶ A) (a : A' ⟶ F.obj A₁)
    (b : F.obj B ⟶ B') (n : ℕ) (x : Ext.{w} A B n) :
    transport F a b n ((Ext.mk₀ u).comp x (zero_add n)) = transport F (a ≫ F.map u) b n x := by
  rw [← sandwich_id_right, transport_sandwich, F.map_id, Category.id_comp]

/-- The transport along `c ≫ a` is `c` composed with the transport along `a`. -/
theorem transport_comp_left {A B : C} {A' A'' B' : D} (c : A'' ⟶ A') (a : A' ⟶ F.obj A)
    (b : F.obj B ⟶ B') (n : ℕ) (x : Ext.{w} A B n) :
    transport F (c ≫ a) b n x = (Ext.mk₀ c).comp (transport F a b n x) (zero_add n) := by
  rw [← sandwich_id_right, sandwich_transport, Category.comp_id]

/-- The transport along `b ≫ c` is the transport along `b` composed with `c`. -/
theorem transport_comp_right {A B : C} {A' B' B'' : D} (a : A' ⟶ F.obj A) (b : F.obj B ⟶ B')
    (c : B' ⟶ B'') (n : ℕ) (x : Ext.{w} A B n) :
    transport F a (b ≫ c) n x = (transport F a b n x).comp (Ext.mk₀ c) (add_zero n) := by
  rw [← sandwich_id_left, sandwich_transport, Category.id_comp]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- **Two transports compose to one.** -/
theorem transport_transport [EnoughInjectives C] (F₁ : C ⥤ D) [F₁.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁] (F₂ : D ⥤ E) [F₂.Additive]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂] (F : C ⥤ E) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : F ≅ F₁ ⋙ F₂) {A B : C}
    {A₁ B₁ : D} {A₂ B₂ : E} (a₁ : A₁ ⟶ F₁.obj A) (b₁ : F₁.obj B ⟶ B₁) (a₂ : A₂ ⟶ F₂.obj A₁)
    (b₂ : F₂.obj B₁ ⟶ B₂) (n : ℕ) (x : Ext.{w} A B n) :
    transport F₂ a₂ b₂ n (transport F₁ a₁ b₁ n x) =
      transport F (a₂ ≫ F₂.map a₁ ≫ K.inv.app A) (K.hom.app B ≫ F₂.map b₁ ≫ b₂) n x := by
  rw [transport_apply F₂, transport_apply F₁, transport_apply F]
  have h1 : sandwich a₁ b₁ n (x.mapExactFunctor F₁) =
      (Ext.mk₀ a₁).comp ((x.mapExactFunctor F₁).comp (Ext.mk₀ b₁) (add_zero n)) (zero_add n) :=
    rfl
  rw [h1, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_mk₀, Stacks.ExtFunctorial.mapExactFunctor_comp_functor F₁ F₂ A n x]
  have hK := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor K.hom A n x
  have hx : x.mapExactFunctor (F₁ ⋙ F₂) =
      sandwich (K.inv.app A) (K.hom.app B) n (x.mapExactFunctor F) := by
    rw [sandwich_apply, ← hK, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      ← NatTrans.comp_app, K.inv_hom_id, NatTrans.id_app, Ext.mk₀_id_comp]
  rw [hx, ← sandwich_apply (F₂.map a₁) (F₂.map b₁), sandwich_sandwich, sandwich_sandwich]
  simp only [Category.assoc]

end Transport

section Adjunction

variable [HasExt.{w} C] [HasExt.{w'} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Precomposing `R(y)` with the unit is a left inverse of the adjunction map. -/
theorem unit_comp_mapExactFunctor_extMap [EnoughInjectives C] (A : C) (N : D) (n : ℕ)
    (e : Ext.{w} A (R.obj N) n) :
    (Ext.mk₀ (adj.unit.app A)).comp
        ((Stacks.ExtAdjunction.extMap adj A N n e).mapExactFunctor R) (zero_add n) = e := by
  rw [Stacks.ExtAdjunction.extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor L R A n e,
    ← Ext.comp_assoc_of_third_deg_zero,
    Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor adj.unit A n e,
    Stacks.ExtFunctorial.mapExactFunctor_id A n e, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀]
  have := adj.right_triangle_components N
  simp only [Functor.id_obj] at this ⊢
  rw [this, Ext.comp_mk₀_id]

/-- **Bijectivity across an adjunction.** If the adjoint `L A ⟶ P` of `a : A ⟶ R P` is an
isomorphism, then `x ↦ a ∘ R(x)` is a bijection `Ext^n(P, N) → Ext^n(A, R N)`. -/
theorem bijective_transport_of_isIso [EnoughInjectives C] [EnoughInjectives D] {A : C} {P : D}
    (a : A ⟶ R.obj P) (ha : IsIso ((adj.homEquiv A P).symm a)) (N : D) (n : ℕ) :
    Function.Bijective
      (transport R a (𝟙 (R.obj N)) n : Ext.{w'} P N n → Ext.{w} A (R.obj N) n) := by
  set σ := (adj.homEquiv A P).symm a
  have hσ : a = adj.unit.app A ≫ R.map σ :=
    (Equiv.apply_symm_apply (adj.homEquiv A P) a).symm.trans (adj.homEquiv_unit A P σ)
  let Ψ : Ext.{w'} (L.obj A) N n → Ext.{w} A (R.obj N) n := fun y =>
    (Ext.mk₀ (adj.unit.app A)).comp (y.mapExactFunctor R) (zero_add n)
  have hΨ : Function.Bijective Ψ := by
    have hb := Stacks.ExtAdjunction.extMap_bijective adj A N n
    have hl : ∀ e, Ψ (Stacks.ExtAdjunction.extMap adj A N n e) = e :=
      fun e => unit_comp_mapExactFunctor_extMap adj A N n e
    refine ⟨fun y₁ y₂ h => ?_, fun x => ⟨_, hl x⟩⟩
    obtain ⟨x₁, rfl⟩ := hb.2 y₁
    obtain ⟨x₂, rfl⟩ := hb.2 y₂
    rw [hl, hl] at h
    rw [h]
  have hfac : (transport R a (𝟙 (R.obj N)) n : Ext.{w'} P N n → Ext.{w} A (R.obj N) n) =
      Ψ ∘ (sandwich σ (𝟙 N) n) := by
    funext x
    have e1 : Ψ (sandwich σ (𝟙 N) n x) =
        transport R (adj.unit.app A) (𝟙 _) n (sandwich σ (𝟙 N) n x) := by
      simp only [Ψ, transport_apply, sandwich_apply, Ext.comp_mk₀_id]
    rw [Function.comp_apply, e1, transport_sandwich, R.map_id, Category.id_comp, ← hσ]
  rw [hfac]
  exact hΨ.comp (sandwich_bijective σ (𝟙 N) n)

end Adjunction

section BaseChange

variable {𝒳 : Type u} {𝒳' : Type u'} {𝒲 : Type u''} {𝒲' : Type u'''} [Category.{v} 𝒳]
  [Category.{v'} 𝒳'] [Category.{v''} 𝒲] [Category.{v'''} 𝒲']
  {Lg : 𝒳 ⥤ 𝒳'} {Rg : 𝒳' ⥤ 𝒳} {Le : 𝒲 ⥤ 𝒲'} {Re : 𝒲' ⥤ 𝒲} {J : 𝒲 ⥤ 𝒳} {Lj : 𝒳 ⥤ 𝒲}
  {J' : 𝒲' ⥤ 𝒳'} {Lj' : 𝒳' ⥤ 𝒲'} {Lc : 𝒳 ⥤ 𝒲'}
  (adjg : Lg ⊣ Rg) (adje : Le ⊣ Re) (adjj : J ⊣ Lj) (adjj' : J' ⊣ Lj')
  (eg : Lj ⋙ Le ≅ Lc) (ef : Lg ⋙ Lj' ≅ Lc)

/-- **Base change of a unit-type map.** Consider a square of left adjoints `Lj ⋙ Le ≅ Lg ⋙ Lj'`
whose base change map `Lj ⋙ Rg ⟶ Re ⋙ Lj'` (the mate along `Lg ⊣ Rg` and `Le ⊣ Re`) is invertible,
and adjunctions `J ⊣ Lj`, `J' ⊣ Lj'`. If `η : A ⟶ Lj Q` has invertible adjoint `J A ⟶ Q`, then
the base changed map `Le η` followed by the comparison has invertible adjoint `J' (Le A) ⟶ Lg Q`.

In the geometric reading (`J = j_!`, `Lj = j⁻¹` for an open immersion `j`, `Lg = g⁻¹`), this says
that the inverse image along `g` of the extension by zero `j_! A` is the extension by zero of the
inverse image of `A`, in the form needed to compute `Ext` out of it. -/
theorem isIso_homEquiv_symm_of_isIso_map
    (hbc : IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjg adje eg ef).natTrans)
    {Q : 𝒳} {A : 𝒲}
    (η : A ⟶ Lj.obj Q) (hη : IsIso ((adjj.homEquiv A Q).symm η)) :
    IsIso ((adjj'.homEquiv (Le.obj A) (Lg.obj Q)).symm
      (Le.map η ≫ eg.hom.app Q ≫ ef.inv.app Q)) := by
  set a := Le.map η ≫ eg.hom.app Q ≫ ef.inv.app Q
  set σ := (adjj.homEquiv A Q).symm η
  rw [isIso_iff_coyoneda_map_bijective]
  intro N
  have h₂ : Function.Bijective (fun φ : Q ⟶ Rg.obj N => η ≫ Lj.map φ) := by
    have e : (fun φ : Q ⟶ Rg.obj N => η ≫ Lj.map φ) =
        (adjj.homEquiv A (Rg.obj N)) ∘ (fun φ => σ ≫ φ) := by
      funext φ
      simp only [Function.comp_apply, Adjunction.homEquiv_naturality_right, σ,
        Equiv.apply_symm_apply]
    rw [e]
    exact (adjj.homEquiv A (Rg.obj N)).bijective.comp
      ((isIso_iff_coyoneda_map_bijective σ).1 hη _)
  have h₃ : Function.Bijective (fun ψ : A ⟶ Lj.obj (Rg.obj N) =>
      ψ ≫ Stacks.CategoryTheory.BaseChange.map adjg adje eg ef N) :=
    (isIso_iff_yoneda_map_bijective _).1
      (inferInstanceAs
        (IsIso ((Stacks.CategoryTheory.BaseChange.twoSquare adjg adje eg ef).natTrans.app N))) A
  have key : ∀ f : Q ⟶ Rg.obj N, a ≫ Lj'.map ((adjg.homEquiv Q N).symm f) =
      (adje.homEquiv A (Lj'.obj N)).symm
        (η ≫ Lj.map f ≫ Stacks.CategoryTheory.BaseChange.map adjg adje eg ef N) := by
    intro f
    rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
      Stacks.CategoryTheory.BaseChange.homEquiv_symm_map, Adjunction.homEquiv_counit]
    have n1 := eg.hom.naturality f
    have n2 := ef.inv.naturality f
    simp only [Functor.comp_map] at n1 n2
    simp only [a, Category.assoc, Functor.map_comp, reassoc_of% n1, reassoc_of% n2]
  have hmain : Function.Bijective (fun f : Lg.obj Q ⟶ N => a ≫ Lj'.map f) := by
    have e : (fun f : Lg.obj Q ⟶ N => a ≫ Lj'.map f) =
        (adje.homEquiv A (Lj'.obj N)).symm ∘
          (fun ψ => ψ ≫ Stacks.CategoryTheory.BaseChange.map adjg adje eg ef N) ∘
            (fun φ => η ≫ Lj.map φ) ∘ (adjg.homEquiv Q N) := by
      funext f
      have := key (adjg.homEquiv Q N f)
      rw [Equiv.symm_apply_apply] at this
      simp only [Function.comp_apply, this, Category.assoc]
    rw [e]
    exact (adje.homEquiv A (Lj'.obj N)).symm.bijective.comp
      (h₃.comp (h₂.comp (adjg.homEquiv Q N).bijective))
  have e : (fun f : Lg.obj Q ⟶ N => (adjj'.homEquiv (Le.obj A) (Lg.obj Q)).symm a ≫ f) =
      (adjj'.homEquiv (Le.obj A) N).symm ∘ (fun f : Lg.obj Q ⟶ N => a ≫ Lj'.map f) := by
    funext f
    simp only [Function.comp_apply]
    rw [← Adjunction.homEquiv_naturality_right_symm]
  rw [e]
  exact (adjj'.homEquiv (Le.obj A) N).symm.bijective.comp hmain

end BaseChange

end Stacks.ExtTransport
