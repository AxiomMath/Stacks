module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Canonical comparisons between pullbacks of modules along equal morphisms

For morphisms of schemes `k₁ k₂ : Z ⟶ Y`, a natural transformation
`α : pullback k₂ ⟶ pullback k₁` between the pullback functors of sheaves of modules is
**canonical** when its conjugate `pushforward k₁ ⟶ pushforward k₂` (under the adjunctions
`pullback ⊣ pushforward`) acts on every module by a restriction map of its sections. Since the
morphisms between two opens of `Z` form a subsingleton, two canonical natural transformations
with the same source and target are equal (`AlgebraicGeometry.Scheme.Modules.IsCanonical.ext`).

The class of canonical transformations contains the identities and the comparisons
`pullbackCongr` along equalities of morphisms, and is closed under composition and under
transport along the comparison isomorphisms `pullbackComp` after whiskering with a further
pullback on either side. This turns every coherence question about composites of
`pullbackComp`, `pullbackCongr` and their whiskerings — the coherence of the pseudofunctor of
modules on schemes — into a membership check.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.IsRestrictionMap`: a natural transformation between
  pushforwards acting by restriction of sections.
* `AlgebraicGeometry.Scheme.Modules.IsCanonical`: the left-adjoint form.

## Main results

* `AlgebraicGeometry.Scheme.Modules.IsCanonical.ext`: uniqueness.
* `AlgebraicGeometry.Scheme.Modules.isCanonical_comp`, `isCanonical_id`,
  `isCanonical_pullbackCongr`, `isCanonical_whiskerRight`, `isCanonical_whiskerLeft`: closure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {Z Y : Scheme.{u}}

/-- The conjugate of `pullbackComp`: its `hom` is conjugate to the inverse of `pushforwardComp`. -/
lemma conjugateEquiv_pullbackComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackComp f g).hom = (pushforwardComp f g).inv := by
  rw [← cancel_mono (pushforwardComp f g).hom, ← conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_comp, Iso.inv_hom_id, conjugateEquiv_id]
  rw [conjugateEquiv_pullbackComp_inv]
  exact (pushforwardComp f g).inv_hom_id.symm

/-- A natural transformation between two pushforward functors **acts by restriction of
sections**: on every module and every open its component is a restriction map. -/
def IsRestrictionMap {a b : Z ⟶ Y} (τ : pushforward a ⟶ pushforward b) : Prop :=
  ∀ (M : Z.Modules) (U : Y.Opens), ∃ i : b ⁻¹ᵁ U ⟶ a ⁻¹ᵁ U,
    (τ.app M).app U = M.presheaf.map i.op

/-- **Two natural transformations between pushforwards acting by restriction of sections are
equal**, because the morphisms between two opens form a subsingleton. -/
lemma IsRestrictionMap.ext {a b : Z ⟶ Y} {τ τ' : pushforward a ⟶ pushforward b}
    (h : IsRestrictionMap τ) (h' : IsRestrictionMap τ') : τ = τ' := by
  ext M U
  obtain ⟨i, hi⟩ := h M U
  obtain ⟨i', hi'⟩ := h' M U
  rw [hi, hi', Subsingleton.elim i i']

/-- A natural transformation `pullback k₂ ⟶ pullback k₁` is **canonical** when its conjugate
`pushforward k₁ ⟶ pushforward k₂` acts by restriction of sections. -/
def IsCanonical {k₁ k₂ : Z ⟶ Y} (α : pullback k₂ ⟶ pullback k₁) : Prop :=
  IsRestrictionMap (conjugateEquiv (pullbackPushforwardAdjunction k₁)
    (pullbackPushforwardAdjunction k₂) α)

/-- **Two canonical natural transformations with the same source and target are equal.** -/
lemma IsCanonical.ext {k₁ k₂ : Z ⟶ Y} {α β : pullback k₂ ⟶ pullback k₁}
    (hα : IsCanonical α) (hβ : IsCanonical β) : α = β :=
  (conjugateEquiv _ _).injective (IsRestrictionMap.ext hα hβ)

/-- The identity is canonical. -/
lemma isCanonical_id (k : Z ⟶ Y) : IsCanonical (𝟙 (pullback k)) := by
  intro M U
  refine ⟨𝟙 _, ?_⟩
  rw [conjugateEquiv_id]
  simp

/-- **Canonical transformations compose.** -/
lemma isCanonical_comp {k₁ k₂ k₃ : Z ⟶ Y} {α : pullback k₃ ⟶ pullback k₂}
    {β : pullback k₂ ⟶ pullback k₁} (hα : IsCanonical α) (hβ : IsCanonical β) :
    IsCanonical (α ≫ β) := by
  intro M U
  obtain ⟨i, hi⟩ := hα M U
  obtain ⟨j, hj⟩ := hβ M U
  refine ⟨i ≫ j, ?_⟩
  have key : conjugateEquiv (pullbackPushforwardAdjunction k₁) (pullbackPushforwardAdjunction k₃)
      (α ≫ β) = conjugateEquiv (pullbackPushforwardAdjunction k₁)
        (pullbackPushforwardAdjunction k₂) β ≫ conjugateEquiv (pullbackPushforwardAdjunction k₂)
        (pullbackPushforwardAdjunction k₃) α :=
    (conjugateEquiv_comp _ _ _ β α).symm
  rw [key, NatTrans.comp_app, Hom.comp_app, hj, hi, op_comp, Functor.map_comp]
  rfl

/-- **The comparison along an equality of morphisms is canonical.** -/
lemma isCanonical_pullbackCongr {k₁ k₂ : Z ⟶ Y} (h : k₂ = k₁) :
    IsCanonical (pullbackCongr h).hom := by
  subst h
  exact isCanonical_id _

/-- The inverse comparison along an equality of morphisms is canonical. -/
lemma isCanonical_pullbackCongr_inv {k₁ k₂ : Z ⟶ Y} (h : k₁ = k₂) :
    IsCanonical (pullbackCongr h).inv :=
  isCanonical_pullbackCongr h.symm

/-- **Whiskering on the right by a pullback, transported along `pullbackComp`, preserves
canonicity.** -/
lemma isCanonical_whiskerRight {T : Scheme.{u}} {k₁ k₂ : Z ⟶ Y} {α : pullback k₂ ⟶ pullback k₁}
    (hα : IsCanonical α) (v : T ⟶ Z) :
    IsCanonical ((pullbackComp v k₂).inv ≫ Functor.whiskerRight α (pullback v) ≫
      (pullbackComp v k₁).hom) := by
  intro M U
  obtain ⟨i, hi⟩ := hα ((pushforward v).obj M) U
  refine ⟨(TopologicalSpace.Opens.map v.base).map i, ?_⟩
  have key : conjugateEquiv (pullbackPushforwardAdjunction (v ≫ k₁))
      (pullbackPushforwardAdjunction (v ≫ k₂))
      ((pullbackComp v k₂).inv ≫ Functor.whiskerRight α (pullback v) ≫
        (pullbackComp v k₁).hom) =
      (pushforwardComp v k₁).inv ≫
        Functor.whiskerLeft (pushforward v) (conjugateEquiv (pullbackPushforwardAdjunction k₁)
          (pullbackPushforwardAdjunction k₂) α) ≫ (pushforwardComp v k₂).hom := by
    rw [← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction k₂).comp
      (pullbackPushforwardAdjunction v)),
      ← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction k₁).comp
        (pullbackPushforwardAdjunction v)),
      conjugateEquiv_pullbackComp_hom, conjugateEquiv_whiskerRight,
      conjugateEquiv_pullbackComp_inv, Category.assoc]
  rw [key]
  simp only [NatTrans.comp_app, Hom.comp_app, Functor.whiskerLeft_app,
    pushforwardComp_inv_app_app, pushforwardComp_hom_app_app]
  rw [hi]
  rfl

/-- **Whiskering on the left by a pullback, transported along `pullbackComp`, preserves
canonicity.** -/
lemma isCanonical_whiskerLeft {W : Scheme.{u}} {k₁ k₂ : Z ⟶ Y} {α : pullback k₂ ⟶ pullback k₁}
    (hα : IsCanonical α) (a : Y ⟶ W) :
    IsCanonical ((pullbackComp k₂ a).inv ≫ Functor.whiskerLeft (pullback a) α ≫
      (pullbackComp k₁ a).hom) := by
  intro M U
  obtain ⟨i, hi⟩ := hα M (a ⁻¹ᵁ U)
  refine ⟨i, ?_⟩
  have key : conjugateEquiv (pullbackPushforwardAdjunction (k₁ ≫ a))
      (pullbackPushforwardAdjunction (k₂ ≫ a))
      ((pullbackComp k₂ a).inv ≫ Functor.whiskerLeft (pullback a) α ≫
        (pullbackComp k₁ a).hom) =
      (pushforwardComp k₁ a).inv ≫
        Functor.whiskerRight (conjugateEquiv (pullbackPushforwardAdjunction k₁)
          (pullbackPushforwardAdjunction k₂) α) (pushforward a) ≫ (pushforwardComp k₂ a).hom := by
    rw [← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction a).comp
      (pullbackPushforwardAdjunction k₂)),
      ← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction a).comp
        (pullbackPushforwardAdjunction k₁)),
      conjugateEquiv_pullbackComp_hom, conjugateEquiv_whiskerLeft,
      conjugateEquiv_pullbackComp_inv, Category.assoc]
  rw [key]
  simp only [NatTrans.comp_app, Hom.comp_app, Functor.whiskerRight_app,
    pushforwardComp_inv_app_app, pushforwardComp_hom_app_app, pushforward_map_app]
  exact hi

/-- A transformation which is an `eqToHom` between pullbacks along equal morphisms is
canonical. -/
lemma isCanonical_eqToHom {k₁ k₂ : Z ⟶ Y} (e : k₂ = k₁) (h : pullback k₂ = pullback k₁) :
    IsCanonical (eqToHom h) := by
  have : eqToHom h = (pullbackCongr e).hom := rfl
  rw [this]
  exact isCanonical_pullbackCongr e

/-- **The associativity comparison of the pullback pseudofunctor is canonical** (it is an
`eqToHom` by `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity`). -/
lemma isCanonical_assoc {X W T : Scheme.{u}} (f : X ⟶ W) (g : W ⟶ Z) (h : Z ⟶ T) :
    IsCanonical ((pullbackComp f (g ≫ h)).inv ≫
      Functor.whiskerRight (pullbackComp g h).inv _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom) := by
  rw [pseudofunctor_associativity]
  exact isCanonical_eqToHom (Category.assoc f g h).symm _

/-- A canonical transformation between pullbacks along equal morphisms is the comparison
`pullbackCongr`. -/
lemma IsCanonical.eq_pullbackCongr_hom {k₁ k₂ : Z ⟶ Y} (h : k₂ = k₁)
    {α : pullback k₂ ⟶ pullback k₁} (hα : IsCanonical α) : α = (pullbackCongr h).hom :=
  hα.ext (isCanonical_pullbackCongr h)

/-- **A right inverse of a canonical transformation between pullbacks along equal morphisms is
canonical.** -/
lemma isCanonical_of_comp_eq_id {k₁ k₂ : Z ⟶ Y} (h : k₂ = k₁) {α : pullback k₂ ⟶ pullback k₁}
    {β : pullback k₁ ⟶ pullback k₂} (hα : IsCanonical α) (hαβ : α ≫ β = 𝟙 _) :
    IsCanonical β := by
  have e := hα.eq_pullbackCongr_hom h
  subst e
  have hβ : β = (pullbackCongr h).inv := by
    rw [← cancel_epi (pullbackCongr h).hom, hαβ, Iso.hom_inv_id]
  rw [hβ]
  exact isCanonical_pullbackCongr_inv h

end AlgebraicGeometry.Scheme.Modules

end
