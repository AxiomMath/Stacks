module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Morphisms multiplicative in one variable, in a cartesian monoidal category

Let `C` be a cartesian monoidal category, `T` an object and `A`, `B` monoid objects of `C`. A
morphism `β : T ⊗ A ⟶ B` is *multiplicative in its second variable* when
`β (t, a a') = β (t, a) β (t, a')`, written as an equation between morphisms
`T ⊗ (A ⊗ A) ⟶ B`. For sheaves of sets and abelian group objects this says that a map
`T × 𝒢 ⟶ ℱ` is additive in `𝒢` section by section; for `G`-sets it is additivity in the second
argument.

The condition is carried along a monoidal functor `F : C ⥤ D` between cartesian monoidal
categories: `β` is sent to `μ ≫ F.map β : F T ⊗ F A ⟶ F B`, and `F A`, `F B` carry the monoid
structures of `CategoryTheory.Functor.monObjObj`. If `F` is faithful, the condition holds for
`μ ≫ F.map β` exactly when it holds for `β`.

## Main definitions

* `CategoryTheory.IsMulRight` — `β : T ⊗ A ⟶ B` is multiplicative in its second variable.

## Main results

* `CategoryTheory.Functor.isMulRight_μ_comp_map_iff` — for a monoidal functor `F`, the condition
  for `μ ≫ F.map β` is the image under `F` of the condition for `β`.
* `CategoryTheory.Functor.isMulRight_μ_comp_map_iff_of_faithful` — for `F` faithful, the condition
  is preserved and reflected.
* `CategoryTheory.isMulRight_functorToTypes_iff` — in a category of functors to types, the
  condition is the identity `β (t, a a') = β (t, a) β (t, a')` at every object.
* `CategoryTheory.Functor.FullyFaithful.mulRightEquiv` — for `F` fully faithful and monoidal,
  `β ↦ μ ≫ F.map β` is a bijection between the morphisms multiplicative in the second variable,
  natural in the first variable (`CategoryTheory.Functor.FullyFaithful.mulRightEquiv_comp`).
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

/-- **`β : T ⊗ A ⟶ B` is multiplicative in its second variable**:
`β (t, a a') = β (t, a) β (t, a')`,
as an equation between morphisms `T ⊗ (A ⊗ A) ⟶ B`. -/
def IsMulRight {T A B : C} [MonObj A] [MonObj B] (β : T ⊗ A ⟶ B) : Prop :=
  T ◁ μ[A] ≫ β = lift (T ◁ fst A A ≫ β) (T ◁ snd A A ≫ β) ≫ μ[B]

/-- Unfolding `IsMulRight β` to the equation `T ◁ μ ≫ β = lift (T ◁ fst ≫ β) (T ◁ snd ≫ β) ≫ μ`. -/
lemma isMulRight_iff {T A B : C} [MonObj A] [MonObj B] (β : T ⊗ A ⟶ B) :
    IsMulRight β ↔ T ◁ μ[A] ≫ β = lift (T ◁ fst A A ≫ β) (T ◁ snd A A ≫ β) ≫ μ[B] :=
  Iff.rfl

/-- The condition only depends on the two multiplications. -/
lemma isMulRight_congr {T A B : C} (iA iA' : MonObj A) (iB iB' : MonObj B)
    (hA : iA.mul = iA'.mul) (hB : iB.mul = iB'.mul) (β : T ⊗ A ⟶ B) :
    @IsMulRight C _ _ T A B iA iB β ↔ @IsMulRight C _ _ T A B iA' iB' β := by
  unfold IsMulRight
  rw [hA, hB]

/-- Precomposing in the first variable keeps the condition. -/
lemma IsMulRight.whiskerRight_comp {T' T A B : C} [MonObj A] [MonObj B] (h : T' ⟶ T)
    {β : T ⊗ A ⟶ B} (hβ : IsMulRight β) : IsMulRight (h ▷ A ≫ β) := by
  rw [isMulRight_iff] at hβ ⊢
  have e0 : T' ◁ μ[A] ≫ h ▷ A = h ▷ (A ⊗ A) ≫ T ◁ μ[A] := whisker_exchange _ _
  have e1 : T' ◁ fst A A ≫ h ▷ A = h ▷ (A ⊗ A) ≫ T ◁ fst A A := whisker_exchange _ _
  have e2 : T' ◁ snd A A ≫ h ▷ A = h ▷ (A ⊗ A) ≫ T ◁ snd A A := whisker_exchange _ _
  rw [← Category.assoc, e0, Category.assoc, hβ, ← Category.assoc, comp_lift, ← Category.assoc,
    ← Category.assoc, ← e1, ← e2, Category.assoc, Category.assoc]

/-- **`β : T ⊗ A ⟶ B` is multiplicative in its first variable**:
`β (t t', a) = β (t, a) β (t', a)`, as an equation between morphisms `(T ⊗ T) ⊗ A ⟶ B`. -/
def IsMulLeft {T A B : C} [MonObj T] [MonObj B] (β : T ⊗ A ⟶ B) : Prop :=
  μ[T] ▷ A ≫ β = lift (fst T T ▷ A ≫ β) (snd T T ▷ A ≫ β) ≫ μ[B]

/-- Unfolding `IsMulLeft β` to the equation `μ ▷ A ≫ β = lift (fst ▷ A ≫ β) (snd ▷ A ≫ β) ≫ μ`. -/
lemma isMulLeft_iff {T A B : C} [MonObj T] [MonObj B] (β : T ⊗ A ⟶ B) :
    IsMulLeft β ↔ μ[T] ▷ A ≫ β = lift (fst T T ▷ A ≫ β) (snd T T ▷ A ≫ β) ≫ μ[B] :=
  Iff.rfl

/-- The condition only depends on the two multiplications. -/
lemma isMulLeft_congr {T A B : C} (iT iT' : MonObj T) (iB iB' : MonObj B)
    (hT : iT.mul = iT'.mul) (hB : iB.mul = iB'.mul) (β : T ⊗ A ⟶ B) :
    @IsMulLeft C _ _ T A B iT iB β ↔ @IsMulLeft C _ _ T A B iT' iB' β := by
  unfold IsMulLeft
  rw [hT, hB]

variable {D : Type*} [Category* D] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal]

namespace Functor

/-- The common prefix `F T ⊗ (F A ⊗ F A) ⟶ F (T ⊗ (A ⊗ A))` of the two sides, an isomorphism. -/
private abbrev mulRightPrefix (T A : C) : F.obj T ⊗ (F.obj A ⊗ F.obj A) ⟶ F.obj (T ⊗ (A ⊗ A)) :=
  F.obj T ◁ LaxMonoidal.μ F A A ≫ LaxMonoidal.μ F T (A ⊗ A)

/-- Pushing a projection-like map `k` through `mulRightPrefix`. -/
private lemma mulRightPrefix_comp_map_whiskerLeft_comp {T A B : C} (k : A ⊗ A ⟶ A)
    (k' : F.obj A ⊗ F.obj A ⟶ F.obj A) (hk : LaxMonoidal.μ F A A ≫ F.map k = k')
    (β : T ⊗ A ⟶ B) : mulRightPrefix F T A ≫ F.map (T ◁ k ≫ β) =
      F.obj T ◁ k' ≫ LaxMonoidal.μ F T A ≫ F.map β := by
  rw [F.map_comp, mulRightPrefix, Category.assoc, ← μ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hk]

/-- **The multiplicativity condition, transported along a monoidal functor.** For
`β : T ⊗ A ⟶ B`, the morphism `μ ≫ F.map β : F T ⊗ F A ⟶ F B` is multiplicative in its second
variable exactly when `F` identifies the two sides of the condition for `β`. -/
theorem isMulRight_μ_comp_map_iff {T A B : C} [MonObj A] [MonObj B] (β : T ⊗ A ⟶ B) :
    IsMulRight (LaxMonoidal.μ F T A ≫ F.map β) ↔
      F.map (T ◁ μ[A] ≫ β) = F.map (lift (T ◁ fst A A ≫ β) (T ◁ snd A A ≫ β) ≫ μ[B]) := by
  have hL : F.obj T ◁ μ[F.obj A] ≫ LaxMonoidal.μ F T A ≫ F.map β =
      mulRightPrefix F T A ≫ F.map (T ◁ μ[A] ≫ β) := by
    rw [obj.μ_def, MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc,
      F.map_comp, mulRightPrefix, Category.assoc]
  have e1 := mulRightPrefix_comp_map_whiskerLeft_comp F (fst A A) _ (Monoidal.μ_fst F A A) β
  have e2 := mulRightPrefix_comp_map_whiskerLeft_comp F (snd A A) _ (Monoidal.μ_snd F A A) β
  have hR : lift (F.obj T ◁ fst (F.obj A) (F.obj A) ≫ LaxMonoidal.μ F T A ≫ F.map β)
        (F.obj T ◁ snd (F.obj A) (F.obj A) ≫ LaxMonoidal.μ F T A ≫ F.map β) ≫ μ[F.obj B] =
      mulRightPrefix F T A ≫ F.map (lift (T ◁ fst A A ≫ β) (T ◁ snd A A ≫ β) ≫ μ[B]) := by
    rw [F.map_comp, ← Monoidal.lift_μ, obj.μ_def, ← e1, ← e2, ← comp_lift]
    simp only [Category.assoc]
  rw [isMulRight_iff, hL, hR]
  have : IsIso (mulRightPrefix F T A) := by unfold mulRightPrefix; infer_instance
  exact cancel_epi _

/-- **A faithful monoidal functor preserves and reflects multiplicativity in the second
variable.** -/
theorem isMulRight_μ_comp_map_iff_of_faithful [F.Faithful] {T A B : C} [MonObj A] [MonObj B]
    (β : T ⊗ A ⟶ B) : IsMulRight (LaxMonoidal.μ F T A ≫ F.map β) ↔ IsMulRight β :=
  (isMulRight_μ_comp_map_iff F β).trans ⟨fun h ↦ F.map_injective h, fun h ↦ congrArg F.map h⟩

/-- The common prefix `(F T ⊗ F T) ⊗ F A ⟶ F ((T ⊗ T) ⊗ A)` of the two sides of the left
condition, an isomorphism. -/
private abbrev mulLeftPrefix (T A : C) : (F.obj T ⊗ F.obj T) ⊗ F.obj A ⟶ F.obj ((T ⊗ T) ⊗ A) :=
  LaxMonoidal.μ F T T ▷ F.obj A ≫ LaxMonoidal.μ F (T ⊗ T) A

/-- Pushing a projection-like map `k` through `mulLeftPrefix`. -/
private lemma mulLeftPrefix_comp_map_whiskerRight_comp {T A B : C} (k : T ⊗ T ⟶ T)
    (k' : F.obj T ⊗ F.obj T ⟶ F.obj T) (hk : LaxMonoidal.μ F T T ≫ F.map k = k')
    (β : T ⊗ A ⟶ B) : mulLeftPrefix F T A ≫ F.map (k ▷ A ≫ β) =
      k' ▷ F.obj A ≫ LaxMonoidal.μ F T A ≫ F.map β := by
  rw [F.map_comp, mulLeftPrefix, Category.assoc, ← μ_natural_left_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc, hk]

/-- **The left multiplicativity condition, transported along a monoidal functor.** -/
theorem isMulLeft_μ_comp_map_iff {T A B : C} [MonObj T] [MonObj B] (β : T ⊗ A ⟶ B) :
    IsMulLeft (LaxMonoidal.μ F T A ≫ F.map β) ↔
      F.map (μ[T] ▷ A ≫ β) = F.map (lift (fst T T ▷ A ≫ β) (snd T T ▷ A ≫ β) ≫ μ[B]) := by
  have hL : μ[F.obj T] ▷ F.obj A ≫ LaxMonoidal.μ F T A ≫ F.map β =
      mulLeftPrefix F T A ≫ F.map (μ[T] ▷ A ≫ β) := by
    rw [obj.μ_def, MonoidalCategory.comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      F.map_comp, mulLeftPrefix, Category.assoc]
  have e1 := mulLeftPrefix_comp_map_whiskerRight_comp F (fst T T) _ (Monoidal.μ_fst F T T) β
  have e2 := mulLeftPrefix_comp_map_whiskerRight_comp F (snd T T) _ (Monoidal.μ_snd F T T) β
  have hR : lift (fst (F.obj T) (F.obj T) ▷ F.obj A ≫ LaxMonoidal.μ F T A ≫ F.map β)
        (snd (F.obj T) (F.obj T) ▷ F.obj A ≫ LaxMonoidal.μ F T A ≫ F.map β) ≫ μ[F.obj B] =
      mulLeftPrefix F T A ≫ F.map (lift (fst T T ▷ A ≫ β) (snd T T ▷ A ≫ β) ≫ μ[B]) := by
    rw [F.map_comp, ← Monoidal.lift_μ, obj.μ_def, ← e1, ← e2, ← comp_lift]
    simp only [Category.assoc]
  rw [isMulLeft_iff, hL, hR]
  have : IsIso (mulLeftPrefix F T A) := by unfold mulLeftPrefix; infer_instance
  exact cancel_epi _

/-- **A faithful monoidal functor preserves and reflects multiplicativity in the first
variable.** -/
theorem isMulLeft_μ_comp_map_iff_of_faithful [F.Faithful] {T A B : C} [MonObj T] [MonObj B]
    (β : T ⊗ A ⟶ B) : IsMulLeft (LaxMonoidal.μ F T A ≫ F.map β) ↔ IsMulLeft β :=
  (isMulLeft_μ_comp_map_iff F β).trans ⟨fun h ↦ F.map_injective h, fun h ↦ congrArg F.map h⟩

/-- **Multiplicativity in the second variable, along a fully faithful monoidal functor**:
`β ↦ μ ≫ F.map β` is a bijection between the morphisms `T ⊗ A ⟶ B` and `F T ⊗ F A ⟶ F B`
multiplicative in the second variable. -/
noncomputable def FullyFaithful.mulRightEquiv {F : C ⥤ D} [F.Monoidal] (hF : F.FullyFaithful)
    (T A B : C)
    [MonObj A] [MonObj B] :
    {β : T ⊗ A ⟶ B // IsMulRight β} ≃
      {β' : F.obj T ⊗ F.obj A ⟶ F.obj B // IsMulRight β'} :=
  letI := hF.faithful
  { toFun β := ⟨LaxMonoidal.μ F T A ≫ F.map β.1,
      (isMulRight_μ_comp_map_iff_of_faithful F β.1).mpr β.2⟩
    invFun β' := ⟨hF.preimage (CategoryTheory.inv (LaxMonoidal.μ F T A) ≫ β'.1), by
      rw [← isMulRight_μ_comp_map_iff_of_faithful F, hF.map_preimage, IsIso.hom_inv_id_assoc]
      exact β'.2⟩
    left_inv β := Subtype.ext (by
      change hF.preimage (CategoryTheory.inv (LaxMonoidal.μ F T A) ≫ LaxMonoidal.μ F T A ≫
        F.map β.1) = β.1
      rw [IsIso.inv_hom_id_assoc, hF.preimage_map])
    right_inv β' := Subtype.ext (by
      change LaxMonoidal.μ F T A ≫
        F.map (hF.preimage (CategoryTheory.inv (LaxMonoidal.μ F T A) ≫ β'.1)) = β'.1
      rw [hF.map_preimage, IsIso.hom_inv_id_assoc]) }

/-- The bijection `mulRightEquiv` sends `β` to `μ ≫ F.map β`. -/
lemma FullyFaithful.mulRightEquiv_apply {F : C ⥤ D} [F.Monoidal] (hF : F.FullyFaithful)
    {T A B : C} [MonObj A] [MonObj B] (β : {β : T ⊗ A ⟶ B // IsMulRight β}) :
    (hF.mulRightEquiv T A B β).1 = LaxMonoidal.μ F T A ≫ F.map β.1 :=
  rfl

/-- The bijection `mulRightEquiv` is natural in the first variable. -/
lemma FullyFaithful.mulRightEquiv_comp {F : C ⥤ D} [F.Monoidal] (hF : F.FullyFaithful)
    {T' T A B : C} [MonObj A] [MonObj B] (h : T' ⟶ T) (β : {β : T ⊗ A ⟶ B // IsMulRight β}) :
    (hF.mulRightEquiv T' A B ⟨h ▷ A ≫ β.1, β.2.whiskerRight_comp h⟩).1 =
      F.map h ▷ F.obj A ≫ (hF.mulRightEquiv T A B β).1 := by
  rw [mulRightEquiv_apply, mulRightEquiv_apply, F.map_comp, ← Category.assoc,
    ← μ_natural_left, Category.assoc]

/-- The transport `β ↦ μ ≫ F.map β` commutes with precomposition in the first variable. -/
lemma μ_comp_map_whiskerRight_comp {T' T A B : C} (h : T' ⟶ T) (β : T ⊗ A ⟶ B) :
    LaxMonoidal.μ F T' A ≫ F.map (h ▷ A ≫ β) =
      F.map h ▷ F.obj A ≫ LaxMonoidal.μ F T A ≫ F.map β := by
  rw [F.map_comp, ← Category.assoc, ← μ_natural_left, Category.assoc]

/-- The transport `β ↦ μ ≫ F.map β` commutes with precomposition in the second variable. -/
lemma μ_comp_map_whiskerLeft_comp {T A' A B : C} (k : A' ⟶ A) (β : T ⊗ A ⟶ B) :
    LaxMonoidal.μ F T A' ≫ F.map (T ◁ k ≫ β) =
      F.obj T ◁ F.map k ≫ LaxMonoidal.μ F T A ≫ F.map β := by
  rw [F.map_comp, ← Category.assoc, ← μ_natural_right, Category.assoc]

end Functor

section FunctorToTypes

universe w

variable {K : Type*} [Category* K]

/-- **Multiplicativity in the second variable, for functors to types**: it is the identity
`β (t, a a') = β (t, a) β (t, a')` at every object, the products of functors to types being
computed objectwise. -/
theorem isMulRight_functorToTypes_iff {T A B : K ⥤ Type w} {iA : MonObj A} {iB : MonObj B}
    (β : T ⊗ A ⟶ B) :
    IsMulRight β ↔ ∀ (k : K) (t : T.obj k) (a a' : A.obj k),
      β.app k (t, μ[A].app k (a, a')) = μ[B].app k (β.app k (t, a), β.app k (t, a')) := by
  rw [isMulRight_iff]
  constructor
  · intro h k t a a'
    exact congrArg (fun φ : T ⊗ (A ⊗ A) ⟶ B ↦ φ.app k (t, (a, a'))) h
  · intro h
    ext k ⟨t, a, a'⟩
    exact h k t a a'

/-- **Multiplicativity in the first variable, for functors to types.** -/
theorem isMulLeft_functorToTypes_iff {T A B : K ⥤ Type w} {iT : MonObj T} {iB : MonObj B}
    (β : T ⊗ A ⟶ B) :
    IsMulLeft β ↔ ∀ (k : K) (t t' : T.obj k) (a : A.obj k),
      β.app k (μ[T].app k (t, t'), a) = μ[B].app k (β.app k (t, a), β.app k (t', a)) := by
  rw [isMulLeft_iff]
  constructor
  · intro h k t t' a
    exact congrArg (fun φ : (T ⊗ T) ⊗ A ⟶ B ↦ φ.app k ((t, t'), a)) h
  · intro h
    ext k ⟨⟨t, t'⟩, a⟩
    exact h k t t' a

end FunctorToTypes

end CategoryTheory

end
