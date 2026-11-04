module

public import StacksFrontier.CategoryTheory.Sites.Stack.Setoid
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaDiagonal
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaSquare
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inertia of a stack

Let `(𝒞, J)` be a site, let `p : 𝒮 ⥤ 𝒞` and `p' : 𝒮' ⥤ 𝒞` be stacks over `𝒞` and let
`F : 𝒮 ⥤ 𝒮'` be a 1-morphism of stacks over `𝒞`. This file records two facts about the
relative inertia `I_{𝒮/𝒮'} = CategoryTheory.RelativeInertia F` and the absolute inertia
`I_𝒮 = CategoryTheory.AbsoluteInertia p`, which is the case `𝒮' = 𝒞`, `F = p`, `p' = 𝟭 𝒞` of
the relative one.

* the inertia is again a stack, and is a stack in groupoids resp. in setoids as soon as `𝒮`
  is (Stacks 036Y);
* for a stack in groupoids `𝒮`, the forgetful 1-morphism `π : I_𝒮 ⥤ 𝒮` is an equivalence if
  and only if `𝒮` is a stack in setoids (Stacks 04ZM).

## Main results

* `CategoryTheory.RelativeInertia.isStack`, `.isStack_and_fiber_isGroupoid`, `.isStackInSetoids`
* `CategoryTheory.RelativeInertia.π_isEquivalence_iff`

## Implementation notes

Part (1) of Stacks 036Y is **not proved here**: only its fibredness half is, from Stacks 034H
(2), and the two descent conditions of Definition 026F for the inertia are hypotheses
`hmor` and `heff` of `RelativeInertia.isStack`. In the source they come from the closure of
stacks under 2-fibre products (Stacks 026G, 02ZL, 0434) together with the equivalence of
Stacks 034H (1); the pinned Mathlib has neither the 2-fibre product of categories over a base
as a stack nor the invariance of the stack condition under an equivalence over the base, and
this file adds no unproved statement in their place. Parts (2) and (3) are proved in full,
granting part (1): the content beyond part (1) is that the fibres of the inertia are groupoids
resp. thin whenever the fibres of `p` are, and that is what is proved.

Stacks 04ZM is proved in full, and in a form slightly stronger than the source: `π` is not
only an equivalence of categories but an isomorphism of categories over `𝒞`, the neutral
section `x ↦ (x, 𝟙)` being a strict two-sided inverse.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  {𝒮' : Type u₃} [Category.{v₃} 𝒮']

namespace Functor

/-- A morphism of `𝒮` lying over an identity of `𝒞` is invertible as soon as the fibre it lies
in is a groupoid. -/
lemma isIso_of_fiber_isGroupoid {p : 𝒮 ⥤ 𝒞} {U : 𝒞} (hg : IsGroupoid (p.Fiber U)) {a b : 𝒮}
    (φ : a ⟶ b) (h : p.IsHomLift (𝟙 U) φ) : IsIso φ := by
  have := h
  have : IsIso (Fiber.homMk p U φ) := hg.all_isIso _
  have h' : IsIso (Fiber.fiberInclusion.map (Fiber.homMk p U φ)) := inferInstance
  rwa [Fiber.fiberInclusion_homMk] at h'

/-- Every morphism of `𝒞` is strongly cartesian for the identity functor: `𝒞` is fibred over
itself with discrete fibres. -/
@[sga "1 VI 5.2" "more general"]
lemma isStronglyCartesian_id {R T : 𝒞} (f : R ⟶ T) {a b : 𝒞} (φ : a ⟶ b)
    (h : (𝟭 𝒞).IsHomLift f φ) : (𝟭 𝒞).IsStronglyCartesian f φ := by
  have := h
  obtain rfl : a = R := IsHomLift.domain_eq (𝟭 𝒞) f φ
  obtain rfl : b = T := IsHomLift.codomain_eq (𝟭 𝒞) f φ
  obtain rfl : f = φ := by simpa using (IsHomLift.fac' (𝟭 𝒞) f φ).symm
  refine ⟨fun {a'} g φ' hφ' => ?_⟩
  have := hφ'
  have hg : (𝟭 𝒞).IsHomLift g g := by simpa using IsHomLift.map (p := 𝟭 𝒞) g
  obtain rfl : φ' = g ≫ f := by simpa using IsHomLift.fac' (𝟭 𝒞) (g ≫ f) φ'
  refine ⟨g, ⟨hg, rfl⟩, ?_⟩
  rintro χ ⟨hχ, -⟩
  have := hχ
  simpa using IsHomLift.fac' (𝟭 𝒞) g χ

/-- The structure functor `p : 𝒮 ⥤ 𝒞` of a category over `𝒞` is a 1-morphism of fibred
categories from `p` to `𝒞` fibred over itself. -/
lemma isFibredOneMorphism_id (p : 𝒮 ⥤ 𝒞) : p.IsFibredOneMorphism (𝟭 𝒞) p where
  comp_eq := rfl
  map_isStronglyCartesian := by
    intro _ _ f _ _ φ hφ
    have := hφ.toIsHomLift
    exact isStronglyCartesian_id f (p.map φ)
      (isHomLift_map_of_comp_eq (p := p) (q := 𝟭 𝒞) (G := p) rfl f φ)

end Functor

namespace RelativeInertia

/-! ## The fibres of the inertia -/

/-- If the fibre of `p` over `U` is a groupoid, so is the fibre of the relative inertia over
`U`: the inverse of the underlying morphism again commutes with the automorphisms. -/
lemma fiber_isGroupoid (F : 𝒮 ⥤ 𝒮') (p : 𝒮 ⥤ 𝒞) (U : 𝒞) (hg : IsGroupoid (p.Fiber U)) :
    IsGroupoid ((RelativeInertia.π F ⋙ p).Fiber U) where
  all_isIso {A B} ψ := by
    have hlift : p.IsHomLift (𝟙 U) ψ.val.hom :=
      (RelativeInertia.isHomLift_π_comp_iff (𝟙 U) ψ.val).mp ψ.2
    have : IsIso ψ.val.hom := Functor.isIso_of_fiber_isGroupoid hg _ hlift
    have := hlift
    have hinv : p.IsHomLift (𝟙 U) (inv ψ.val.hom) :=
      IsHomLift.lift_id_inv_isIso p U ψ.val.hom
    refine ⟨⟨⟨⟨inv ψ.val.hom, ?_⟩, (RelativeInertia.isHomLift_π_comp_iff (𝟙 U) _).mpr hinv⟩,
      ?_, ?_⟩⟩
    · rw [IsIso.inv_comp_eq, ← Category.assoc, ψ.val.comm, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    all_goals refine Functor.Fiber.hom_ext (RelativeInertiaHom.ext ?_)
    all_goals simp [Functor.Fiber.fiberInclusion]

/-- If the fibre of `p` over `U` is thin, so is the fibre of the relative inertia over `U`:
a morphism of the inertia is determined by its underlying morphism. -/
lemma fiber_isThin (F : 𝒮 ⥤ 𝒮') (p : 𝒮 ⥤ 𝒞) (U : 𝒞) (ht : Quiver.IsThin (p.Fiber U)) :
    Quiver.IsThin ((RelativeInertia.π F ⋙ p).Fiber U) := fun A B ↦ ⟨by
  intro ψ₁ ψ₂
  refine Functor.Fiber.hom_ext (RelativeInertiaHom.ext ?_)
  have h₁ := (RelativeInertia.isHomLift_π_comp_iff (𝟙 U) ψ₁.val).mp ψ₁.2
  have h₂ := (RelativeInertia.isHomLift_π_comp_iff (𝟙 U) ψ₂.val).mp ψ₂.2
  dsimp only [Functor.Fiber.fiberInclusion]
  simpa using congrArg Functor.Fiber.fiberInclusion.map
    ((ht _ _).allEq (Functor.Fiber.homMk p U ψ₁.val.hom) (Functor.Fiber.homMk p U ψ₂.val.hom))⟩

/-! ## The inertia is a stack (Stacks 036Y) -/

variable {F : 𝒮 ⥤ 𝒮'} {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {J : GrothendieckTopology 𝒞}

/-- The relative inertia `I_{𝒮/𝒮'}` of a 1-morphism `F` of stacks over the site `(𝒞, J)`, with its
structure functor `π ⋙ p`, is a stack over `𝒞`; taking `F = p` and `p' = 𝟭 𝒞`, so is the absolute
inertia `I_𝒮`.

Only the fibredness half of the conclusion is proved, from Stacks 034H (2); the descent of
morphisms and the effectivity of descent for the inertia are the hypotheses `hmor` and
`heff`. -/
@[stacks 036Y "(1)"]
theorem isStack (hp : p.IsStack J) (_hp' : p'.IsStack J) (hF : p.IsFibredOneMorphism p' F)
    (hmor : haveI : (RelativeInertia.π F ⋙ p).IsFibered :=
        RelativeInertia.isFibered F p p' hp.isFibered hF
      ∀ (U : 𝒞) (x y : (RelativeInertia.π F ⋙ p).Fiber U),
        Functor.IsMorSheaf (RelativeInertia.π F ⋙ p) J U x y)
    (heff : haveI : (RelativeInertia.π F ⋙ p).IsFibered :=
        RelativeInertia.isFibered F p p' hp.isFibered hF
      Functor.HasEffectiveDescent (RelativeInertia.π F ⋙ p) J) :
    Functor.IsStack (RelativeInertia.π F ⋙ p) J where
  isFibered := RelativeInertia.isFibered F p p' hp.isFibered hF
  isMorSheaf := hmor
  hasEffectiveDescent := heff

/-- If `𝒮` and `𝒮'` are stacks in groupoids over the site `(𝒞, J)`, then so is the relative inertia
`I_{𝒮/𝒮'}`; taking `F = p` and `p' = 𝟭 𝒞`, so is the absolute inertia `I_𝒮`.

Being a stack in groupoids is written out as being a stack with groupoid fibres; the stack
condition on the inertia is the hypothesis `hst`, which is part (1), and what is proved here is
the remaining content, that the fibres of the inertia are groupoids. -/
@[stacks 036Y "(2)"]
theorem isStack_and_fiber_isGroupoid (_hp : p.IsStack J) (hgp : ∀ U, IsGroupoid (p.Fiber U))
    (_hp' : p'.IsStack J) (_hgp' : ∀ U, IsGroupoid (p'.Fiber U))
    (hst : Functor.IsStack (RelativeInertia.π F ⋙ p) J) :
    Functor.IsStack (RelativeInertia.π F ⋙ p) J ∧
      ∀ U, IsGroupoid ((RelativeInertia.π F ⋙ p).Fiber U) :=
  ⟨hst, fun U ↦ fiber_isGroupoid F p U (hgp U)⟩

/-- If `𝒮` and `𝒮'` are stacks in setoids over the site `(𝒞, J)`, then so is the relative inertia
`I_{𝒮/𝒮'}`; taking `F = p` and `p' = 𝟭 𝒞`, so is the absolute inertia `I_𝒮`.

The stack condition on the inertia is the hypothesis `hst`, which is part (1); what is proved
here is the remaining content, that the fibres of the inertia are setoids. -/
@[stacks 036Y "(3)"]
theorem isStackInSetoids (hp : p.IsStackInSetoids J) (_hp' : p'.IsStackInSetoids J)
    (hst : Functor.IsStack (RelativeInertia.π F ⋙ p) J) :
    (RelativeInertia.π F ⋙ p).IsStackInSetoids J where
  isStack := hst
  fiber_isGroupoid U := fiber_isGroupoid F p U (hp.fiber_isGroupoid U)
  fiber_isThin U := fiber_isThin F p U (hp.fiber_isThin U)

/-! ## The forgetful 1-morphism `π : I_𝒮 ⥤ 𝒮` (Stacks 04ZM) -/


variable (p : 𝒮 ⥤ 𝒞) (J)

/-- Let `(𝒞, J)` be a site and let `𝒮` be a stack in groupoids over `𝒞`, written out as a stack
with groupoid fibres. The forgetful 1-morphism `π : I_𝒮 ⥤ 𝒮` of the absolute inertia is an
equivalence if and only if `𝒮` is a stack in setoids. -/
@[stacks 04ZM]
theorem π_isEquivalence_iff (hp : p.IsStack J) (hg : ∀ U, IsGroupoid (p.Fiber U)) :
    (RelativeInertia.π p).IsEquivalence ↔ p.IsStackInSetoids J where
  mp h :=
    { isStack := hp
      fiber_isGroupoid := hg
      fiber_isThin := fiber_isThin_of_π_full p hg h.full }
  mpr h := have := π_full_of_fiber_isThin p h.fiber_isThin; .mk

-- The `eqToHom`s produced by `Functor.ext` are indexed by an object equality whose two sides,
-- `((neutralSection p).obj A.obj).obj` and `A.obj`, agree only after unfolding `neutralSection`.
set_option backward.isDefEq.respectTransparency false in
/-- For a stack in setoids the neutral section `x ↦ (x, 𝟙)` is a strict two-sided inverse of `π`,
so `π` is an isomorphism of categories over `𝒞` and in particular an equivalence in the 2-category
of stacks over `𝒞`, not merely an equivalence of categories. -/
@[stacks 04ZM]
theorem π_comp_neutralSection_eq_id (h : p.IsStackInSetoids J) :
    RelativeInertia.π p ⋙ RelativeInertia.neutralSection p = 𝟭 (AbsoluteInertia p) := by
  refine CategoryTheory.Functor.ext (fun A ↦ ?_) (fun A B ψ ↦ ?_)
  · exact RelativeInertia.obj_ext rfl (by simp [auto_eq_id_of_fiber_isThin p h.fiber_isThin])
  · refine RelativeInertiaHom.ext ?_
    simp [RelativeInertia.neutralSection]

/-- The neutral section is a strict section of `π` on the nose. -/
theorem neutralSection_comp_π_eq_id :
    RelativeInertia.neutralSection p ⋙ RelativeInertia.π p = 𝟭 𝒮 := rfl

end RelativeInertia

end CategoryTheory
