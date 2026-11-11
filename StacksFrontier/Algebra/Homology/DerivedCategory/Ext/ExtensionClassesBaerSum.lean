module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Abelian.Refinements
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ExtensionClasses

/-!
# The Baer sum on the Ext-group of an abelian category

Let `C` be an abelian category. For an extension `E` of `B` by `A`, a map `β : B' → B` and a
map `α : A → A'`, the pullback `E ×_B B'` is an extension of `B'` by `A` and the pushout
`A' ⨿_A E` is an extension of `B` by `A'`. These operations pass to the isomorphism classes
`Ext_C(B, A)` (Stacks 010K, `CategoryTheory.Abelian.YonedaExt`) and make
`(A, B) ↦ Ext_C(B, A)` a functor. The *Baer sum* of two
extensions `E₁`, `E₂` of `B` by `A` is obtained from the extension `E₁ ⊕ E₂` of `B ⊕ B` by
`A ⊕ A` by pushing out along the sum map `A ⊕ A → A` and pulling back along the diagonal
`B → B ⊕ B`. Stacks 010L: the Baer sum is a commutative group law on `Ext_C(B, A)`, functorial
in both variables.

## Main definitions

* `CategoryTheory.Abelian.Extension.isIso`: every morphism of extensions is an isomorphism
  (five lemma), so `CategoryTheory.Abelian.YonedaExt.mk_eq_mk_of_hom` holds.
* `CategoryTheory.Abelian.Extension.pullback`, `CategoryTheory.Abelian.Extension.pushout`,
  `CategoryTheory.Abelian.Extension.directSum`: pullback, pushout and direct sum of
  extensions.
* `CategoryTheory.Abelian.YonedaExt.pullback`, `CategoryTheory.Abelian.YonedaExt.pushout`:
  the induced maps on `Ext_C(B, A)`.
* `CategoryTheory.Abelian.YonedaExt.instAddCommGroup`: the Baer sum group law.
* `CategoryTheory.Abelian.YonedaExt.functor`: the bifunctor `Cᵒᵖ ⥤ C ⥤ AddCommGrpCat`,
  `(B, A) ↦ Ext_C(B, A)`, acting by pullback and pushout.

## References

* [Stacks Project, Tag 010L](https://stacks.math.columbia.edu/tag/010L)
-/

@[expose] public section

universe v u

namespace CategoryTheory.Abelian

open Limits hiding pullback pushout

attribute [local simp] Limits.pullback.lift_fst Limits.pullback.lift_snd
  Limits.pullback.lift_fst_assoc Limits.pullback.lift_snd_assoc Limits.pushout.inl_desc
  Limits.pushout.inr_desc Limits.pushout.inl_desc_assoc Limits.pushout.inr_desc_assoc

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Extension

variable {A A' A'' B B' B'' : C}

/-! ### Morphisms of extensions are isomorphisms -/

/-- A morphism of extensions as a morphism of the underlying short complexes, with the
identities on the end terms. -/
@[simps]
def homToShortComplex {E F : Extension B A} (φ : E ⟶ F) :
    E.toShortComplex ⟶ F.toShortComplex where
  τ₁ := 𝟙 A
  τ₂ := φ.hom
  τ₃ := 𝟙 B
  comm₁₂ := by simp
  comm₂₃ := by simp

/-- The map of middle terms of a morphism of extensions is an isomorphism (five lemma). -/
lemma isIso_hom {E F : Extension B A} (φ : E ⟶ F) : IsIso φ.hom :=
  ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' (homToShortComplex φ) E.shortExact
    F.shortExact (inferInstanceAs (IsIso (𝟙 A))) (inferInstanceAs (IsIso (𝟙 B)))

/-- Every morphism of extensions is an isomorphism. -/
instance isIso {E F : Extension B A} (φ : E ⟶ F) : IsIso φ := by
  have := isIso_hom φ
  exact (isoMk (asIso φ.hom) φ.comm_f φ.comm_g).isIso_hom

/-! ### Pullback, pushout and direct sum of extensions -/

/-- The *pullback* `E ×_B B'` of an extension `E` of `B` by `A` along `β : B' → B`, an
extension of `B'` by `A`. -/
@[simps]
noncomputable abbrev pullback (E : Extension B A) (β : B' ⟶ B) : Extension B' A where
  X := Limits.pullback E.g β
  f := Limits.pullback.lift E.f 0 (E.zero.trans zero_comp.symm)
  g := Limits.pullback.snd E.g β
  zero := Limits.pullback.lift_snd _ _ _
  shortExact' := by
    have : Mono (Limits.pullback.lift (f := E.g) (g := β) E.f 0 (E.zero.trans zero_comp.symm)) :=
      mono_of_mono_fac (Limits.pullback.lift_fst _ _ _)
    refine ShortComplex.ShortExact.mk' ?_ this inferInstance
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T k hk
    dsimp at hk
    have hk' : (k ≫ Limits.pullback.fst E.g β) ≫ E.g = 0 := by
      rw [Category.assoc, Limits.pullback.condition, reassoc_of% hk, zero_comp]
    refine ⟨T, 𝟙 T, inferInstance, E.shortExact.exact.lift _ hk', ?_⟩
    dsimp
    apply Limits.pullback.hom_ext
    · simp only [Category.id_comp, Category.assoc, Limits.pullback.lift_fst]
      exact (E.shortExact.exact.lift_f _ hk').symm
    · simp only [Category.id_comp, Category.assoc, hk, Limits.pullback.lift_snd, comp_zero]

/-- The *pushout* `A' ⨿_A E` of an extension `E` of `B` by `A` along `α : A → A'`, an
extension of `B` by `A'`. -/
@[simps]
noncomputable abbrev pushout (E : Extension B A) (α : A ⟶ A') : Extension B A' where
  X := Limits.pushout E.f α
  f := Limits.pushout.inr E.f α
  g := Limits.pushout.desc E.g 0 (E.zero.trans comp_zero.symm)
  zero := Limits.pushout.inr_desc _ _ _
  shortExact' := by
    have : Epi (Limits.pushout.desc (f := E.f) (g := α) E.g 0 (E.zero.trans comp_zero.symm)) :=
      epi_of_epi_fac (Limits.pushout.inl_desc _ _ _)
    refine ShortComplex.ShortExact.mk' ?_ inferInstance this
    refine ShortComplex.exact_of_g_is_cokernel _
      (CokernelCofork.IsColimit.ofπ' _ _ fun {T} k hk => ?_)
    dsimp at hk
    have hk' : E.f ≫ Limits.pushout.inl E.f α ≫ k = 0 := by
      rw [Limits.pushout.condition_assoc, hk, comp_zero]
    refine ⟨E.shortExact.exact.desc (Limits.pushout.inl E.f α ≫ k) hk', ?_⟩
    apply Limits.pushout.hom_ext
    · simp only [Limits.pushout.inl_desc_assoc]
      exact E.shortExact.exact.g_desc _ hk'
    · simp only [Limits.pushout.inr_desc_assoc, zero_comp, hk]

/-- The *direct sum* `E₁ ⊕ E₂` of an extension `E₁` of `B₁` by `A₁` and an extension `E₂` of
`B₂` by `A₂`, an extension of `B₁ ⊕ B₂` by `A₁ ⊕ A₂`. -/
@[simps]
noncomputable abbrev directSum {A₁ A₂ B₁ B₂ : C} (E₁ : Extension B₁ A₁) (E₂ : Extension B₂ A₂) :
    Extension (B₁ ⊞ B₂) (A₁ ⊞ A₂) where
  X := E₁.X ⊞ E₂.X
  f := biprod.map E₁.f E₂.f
  g := biprod.map E₁.g E₂.g
  zero := by ext <;> simp
  shortExact' := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    dsimp at hx
    have h₁ : (x ≫ biprod.fst) ≫ E₁.g = 0 := by simpa using hx =≫ biprod.fst
    have h₂ : (x ≫ biprod.snd) ≫ E₂.g = 0 := by simpa using hx =≫ biprod.snd
    refine ⟨T, 𝟙 T, inferInstance, biprod.lift (E₁.shortExact.exact.lift _ h₁)
      (E₂.shortExact.exact.lift _ h₂), ?_⟩
    dsimp
    apply biprod.hom_ext
    · simp only [Category.id_comp, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
      exact (E₁.shortExact.exact.lift_f _ h₁).symm
    · simp only [Category.id_comp, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
      exact (E₂.shortExact.exact.lift_f _ h₂).symm

/-- The *trivial* (split) extension `0 → A → A ⊕ B → B → 0`. -/
@[simps]
noncomputable abbrev trivial (B A : C) : Extension B A where
  X := A ⊞ B
  f := biprod.inl
  g := biprod.snd
  zero := biprod.inl_snd
  shortExact' := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact

/-- A map `g : E → F` from an extension of `B'` by `A` to an extension of `B` by `A`, lying over
`𝟙 A` and `β : B' → B`, factors through the pullback `F ×_B B'`. -/
@[simps]
noncomputable def toPullback {E : Extension B' A} {F : Extension B A} {β : B' ⟶ B}
    (g : E.X ⟶ F.X) (h₁ : E.f ≫ g = F.f) (h₂ : g ≫ F.g = E.g ≫ β) : E ⟶ F.pullback β where
  hom := Limits.pullback.lift g E.g h₂
  comm_f := by apply Limits.pullback.hom_ext <;> simp [h₁]
  comm_g := by simp

/-- A map `g : E → F` from an extension of `B` by `A` to an extension of `B` by `A'`, lying over
`α : A → A'` and `𝟙 B`, factors through the pushout `A' ⨿_A E`. -/
@[simps]
noncomputable def fromPushout {E : Extension B A} {F : Extension B A'} {α : A ⟶ A'}
    (g : E.X ⟶ F.X) (h₁ : E.f ≫ g = α ≫ F.f) (h₂ : g ≫ F.g = E.g) : E.pushout α ⟶ F where
  hom := Limits.pushout.desc g F.f h₁
  comm_f := by simp
  comm_g := by apply Limits.pushout.hom_ext <;> simp [h₂]

/-- A map `g : E → F` from an extension of `B` by `A` to an extension of `B'` by `A'`, lying over
`α : A → A'` and `β : B → B'`, induces a morphism of extensions `A' ⨿_A E → F ×_{B'} B` of `B`
by `A'`. -/
@[simps]
noncomputable def pushoutToPullback {E : Extension B A} {F : Extension B' A'} {α : A ⟶ A'}
    {β : B ⟶ B'} (g : E.X ⟶ F.X) (h₁ : E.f ≫ g = α ≫ F.f) (h₂ : g ≫ F.g = E.g ≫ β) :
    E.pushout α ⟶ F.pullback β where
  hom := Limits.pullback.lift (Limits.pushout.desc g F.f h₁) (E.pushout α).g (by
    apply Limits.pushout.hom_ext <;> simp [h₂])
  comm_f := by apply Limits.pullback.hom_ext <;> simp
  comm_g := by simp

/-- A morphism of extensions of `B` by `A` induces a morphism of their pullbacks along
`β : B' → B`. -/
noncomputable def pullbackMap {E F : Extension B A} (f : E ⟶ F) (β : B' ⟶ B) :
    E.pullback β ⟶ F.pullback β :=
  toPullback (Limits.pullback.fst E.g β ≫ f.hom) (by simp)
    (by simp [Limits.pullback.condition])

/-- A morphism of extensions of `B` by `A` induces a morphism of their pushouts along
`α : A → A'`. -/
noncomputable def pushoutMap {E F : Extension B A} (f : E ⟶ F) (α : A ⟶ A') :
    E.pushout α ⟶ F.pushout α :=
  fromPushout (f.hom ≫ Limits.pushout.inl F.f α) (by simp [Limits.pushout.condition])
    (by simp)

/-- Morphisms of extensions induce a morphism of their direct sums. -/
@[simps]
noncomputable def directSumMap {A₁ A₂ B₁ B₂ : C} {E₁ F₁ : Extension B₁ A₁}
    {E₂ F₂ : Extension B₂ A₂} (f₁ : E₁ ⟶ F₁) (f₂ : E₂ ⟶ F₂) :
    E₁.directSum E₂ ⟶ F₁.directSum F₂ where
  hom := biprod.map f₁.hom f₂.hom
  comm_f := by ext <;> simp
  comm_g := by ext <;> simp

end Extension

namespace YonedaExt

variable {A A' A'' B B' B'' : C}

/-- Two extensions have the same class if and only if there is a morphism of extensions between
them. -/
lemma mk_eq_mk_iff_nonempty_hom {E F : Extension B A} : mk E = mk F ↔ Nonempty (E ⟶ F) :=
  mk_eq_mk_iff.trans ⟨fun ⟨e⟩ => ⟨e.hom⟩, fun ⟨φ⟩ => ⟨asIso φ⟩⟩

lemma mk_eq_mk_of_hom {E F : Extension B A} (φ : E ⟶ F) : mk E = mk F :=
  mk_eq_mk_iff_nonempty_hom.2 ⟨φ⟩

/-- Induction principle on `Ext_C(B, A)`. -/
@[elab_as_elim]
lemma induction_on {motive : YonedaExt B A → Prop} (x : YonedaExt B A)
    (h : ∀ E, motive (mk E)) : motive x :=
  _root_.Quotient.inductionOn x h

/-- A function on extensions which takes the same value on extensions related by a morphism
of extensions descends to `Ext_C(B, A)`. -/
def lift {X : Sort*} (f : Extension B A → X) (hf : ∀ E F, (E ⟶ F) → f E = f F) :
    YonedaExt B A → X :=
  _root_.Quotient.lift f fun E F (h : IsIsomorphic E F) => h.elim fun e => hf E F e.hom

@[simp]
lemma lift_mk {X : Sort*} (f : Extension B A → X) (hf : ∀ E F, (E ⟶ F) → f E = f F)
    (E : Extension B A) : lift f hf (mk E) = f E :=
  rfl

/-- The map `Ext_C(B, A) → Ext_C(B', A)` induced by `β : B' → B`, the class of the pullback. -/
noncomputable def pullback (β : B' ⟶ B) : YonedaExt B A → YonedaExt B' A :=
  lift (fun E => mk (E.pullback β)) fun _ _ f => mk_eq_mk_of_hom (Extension.pullbackMap f β)

/-- The map `Ext_C(B, A) → Ext_C(B, A')` induced by `α : A → A'`, the class of the pushout. -/
noncomputable def pushout (α : A ⟶ A') : YonedaExt B A → YonedaExt B A' :=
  lift (fun E => mk (E.pushout α)) fun _ _ f => mk_eq_mk_of_hom (Extension.pushoutMap f α)

/-- The class of the direct sum of two extensions. -/
noncomputable def directSum {A₁ A₂ B₁ B₂ : C} (x : YonedaExt B₁ A₁) (y : YonedaExt B₂ A₂) :
    YonedaExt (B₁ ⊞ B₂) (A₁ ⊞ A₂) :=
  lift (fun E => lift (fun F => mk (E.directSum F))
      (fun _ _ g => mk_eq_mk_of_hom (Extension.directSumMap (𝟙 E) g)) y)
    (fun _ _ f => induction_on y fun _ => mk_eq_mk_of_hom (Extension.directSumMap f (𝟙 _))) x

@[simp]
lemma pullback_mk (β : B' ⟶ B) (E : Extension B A) : pullback β (mk E) = mk (E.pullback β) :=
  rfl

@[simp]
lemma pushout_mk (α : A ⟶ A') (E : Extension B A) : pushout α (mk E) = mk (E.pushout α) :=
  rfl

@[simp]
lemma directSum_mk {A₁ A₂ B₁ B₂ : C} (E₁ : Extension B₁ A₁) (E₂ : Extension B₂ A₂) :
    directSum (mk E₁) (mk E₂) = mk (E₁.directSum E₂) :=
  rfl

/-- If a map `g : E → F` of extensions lies over `𝟙 A` and `β`, then `E` is the pullback of
`F` along `β`. -/
lemma mk_eq_pullback {E : Extension B' A} {F : Extension B A} {β : B' ⟶ B} (g : E.X ⟶ F.X)
    (h₁ : E.f ≫ g = F.f) (h₂ : g ≫ F.g = E.g ≫ β) : mk E = pullback β (mk F) :=
  mk_eq_mk_of_hom (Extension.toPullback g h₁ h₂)

/-- If a map `g : E → F` of extensions lies over `α` and `𝟙 B`, then `F` is the pushout of `E`
along `α`. -/
lemma pushout_eq_mk {E : Extension B A} {F : Extension B A'} {α : A ⟶ A'} (g : E.X ⟶ F.X)
    (h₁ : E.f ≫ g = α ≫ F.f) (h₂ : g ≫ F.g = E.g) : pushout α (mk E) = mk F :=
  mk_eq_mk_of_hom (Extension.fromPushout g h₁ h₂)

/-- If a map `g : E → F` of extensions lies over `α` and `β`, then the pushout of `E` along `α`
is the pullback of `F` along `β`. -/
lemma pushout_eq_pullback {E : Extension B A} {F : Extension B' A'} {α : A ⟶ A'}
    {β : B ⟶ B'} (g : E.X ⟶ F.X) (h₁ : E.f ≫ g = α ≫ F.f) (h₂ : g ≫ F.g = E.g ≫ β) :
    pushout α (mk E) = pullback β (mk F) :=
  mk_eq_mk_of_hom (Extension.pushoutToPullback g h₁ h₂)

/-! ### Functoriality of pullback and pushout -/

@[simp]
lemma pullback_id (x : YonedaExt B A) : pullback (𝟙 B) x = x :=
  induction_on x fun E => (mk_eq_pullback (𝟙 E.X) (by simp) (by simp)).symm

lemma pullback_comp (f : B'' ⟶ B') (g : B' ⟶ B) (x : YonedaExt B A) :
    pullback (f ≫ g) x = pullback f (pullback g x) :=
  induction_on x fun E => (mk_eq_pullback (E := (E.pullback g).pullback f) (F := E)
    (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _) (by simp) (by
      simp only [Extension.pullback_X, Extension.pullback_g, Category.assoc]
      rw [Limits.pullback.condition, Limits.pullback.condition_assoc])).symm

@[simp]
lemma pushout_id (x : YonedaExt B A) : pushout (𝟙 A) x = x :=
  induction_on x fun E => pushout_eq_mk (𝟙 E.X) (by simp) (by simp)

lemma pushout_comp (f : A ⟶ A') (g : A' ⟶ A'') (x : YonedaExt B A) :
    pushout (f ≫ g) x = pushout g (pushout f x) :=
  induction_on x fun E => pushout_eq_mk (E := E) (F := (E.pushout f).pushout g)
    (Limits.pushout.inl _ _ ≫ Limits.pushout.inl _ _) (by
      simp only [Extension.pushout_X, Extension.pushout_f, Category.assoc]
      rw [Limits.pushout.condition_assoc, Limits.pushout.condition]) (by simp)

/-- Pushout and pullback commute: `A' ⨿_A (E ×_B B') ≅ (A' ⨿_A E) ×_B B'`. -/
lemma pushout_pullback (α : A ⟶ A') (β : B' ⟶ B) (x : YonedaExt B A) :
    pushout α (pullback β x) = pullback β (pushout α x) :=
  induction_on x fun E => pushout_eq_pullback (E := E.pullback β) (F := E.pushout α)
    (Limits.pullback.fst _ _ ≫ Limits.pushout.inl _ _)
    (by simp [Limits.pushout.condition]) (by simp [Limits.pullback.condition])

/-! ### Compatibilities with direct sums -/

lemma pushout_directSum {A₁ A₂ A₁' A₂' B₁ B₂ : C} (α₁ : A₁ ⟶ A₁') (α₂ : A₂ ⟶ A₂')
    (x : YonedaExt B₁ A₁) (y : YonedaExt B₂ A₂) :
    pushout (biprod.map α₁ α₂) (directSum x y) = directSum (pushout α₁ x) (pushout α₂ y) :=
  induction_on x fun E₁ => induction_on y fun E₂ =>
    pushout_eq_mk (E := E₁.directSum E₂) (F := (E₁.pushout α₁).directSum (E₂.pushout α₂))
      (biprod.map (Limits.pushout.inl _ _) (Limits.pushout.inl _ _))
      (by ext <;> simp [Limits.pushout.condition]) (by ext <;> simp)

lemma pullback_directSum {A₁ A₂ B₁ B₂ B₁' B₂' : C} (β₁ : B₁' ⟶ B₁) (β₂ : B₂' ⟶ B₂)
    (x : YonedaExt B₁ A₁) (y : YonedaExt B₂ A₂) :
    pullback (biprod.map β₁ β₂) (directSum x y) = directSum (pullback β₁ x) (pullback β₂ y) :=
  induction_on x fun E₁ => induction_on y fun E₂ =>
    (mk_eq_pullback (E := (E₁.pullback β₁).directSum (E₂.pullback β₂)) (F := E₁.directSum E₂)
      (biprod.map (Limits.pullback.fst _ _) (Limits.pullback.fst _ _))
      (by ext <;> simp) (by ext <;> simp [Limits.pullback.condition])).symm

lemma pushout_directSum_associator {A₁ A₂ A₃ B₁ B₂ B₃ : C} (x : YonedaExt B₁ A₁)
    (y : YonedaExt B₂ A₂) (z : YonedaExt B₃ A₃) :
    pushout (biprod.associator A₁ A₂ A₃).hom (directSum (directSum x y) z) =
      pullback (biprod.associator B₁ B₂ B₃).hom (directSum x (directSum y z)) :=
  induction_on x fun E₁ => induction_on y fun E₂ => induction_on z fun E₃ =>
    pushout_eq_pullback (E := (E₁.directSum E₂).directSum E₃) (F := E₁.directSum (E₂.directSum E₃))
      (biprod.associator _ _ _).hom (biprod.associator_natural _ _ _)
      (biprod.associator_natural _ _ _).symm

lemma pushout_directSum_braiding {A₁ A₂ B₁ B₂ : C} (x : YonedaExt B₁ A₁)
    (y : YonedaExt B₂ A₂) :
    pushout (biprod.braiding A₁ A₂).hom (directSum x y) =
      pullback (biprod.braiding B₁ B₂).hom (directSum y x) :=
  induction_on x fun E₁ => induction_on y fun E₂ =>
    pushout_eq_pullback (E := E₁.directSum E₂) (F := E₂.directSum E₁)
      (biprod.braiding _ _).hom (biprod.braid_natural _ _) (biprod.braid_natural _ _).symm

lemma pushout_fst_directSum {A₁ A₂ B₁ B₂ : C} (x : YonedaExt B₁ A₁) (y : YonedaExt B₂ A₂) :
    pushout biprod.fst (directSum x y) = pullback biprod.fst x :=
  induction_on x fun E₁ => induction_on y fun E₂ =>
    pushout_eq_pullback (E := E₁.directSum E₂) (F := E₁) biprod.fst (by simp) (by simp)

lemma pushout_lift_id_id (x : YonedaExt B A) :
    pushout (biprod.lift (𝟙 A) (𝟙 A)) x = pullback (biprod.lift (𝟙 B) (𝟙 B)) (directSum x x) :=
  induction_on x fun E =>
    pushout_eq_pullback (E := E) (F := E.directSum E) (biprod.lift (𝟙 E.X) (𝟙 E.X))
      (by ext <;> simp) (by ext <;> simp)

/-! ### The zero class and negation -/

/-- The class of the trivial extension `0 → A → A ⊕ B → B → 0`. -/
noncomputable def zero (B A : C) : YonedaExt B A :=
  mk (Extension.trivial B A)

lemma pullback_zero (x : YonedaExt B A) : pullback (0 : B' ⟶ B) x = zero B' A :=
  induction_on x fun E => (mk_eq_pullback (E := Extension.trivial B' A) (F := E)
    (biprod.desc E.f 0) (by simp) (by ext <;> simp)).symm

lemma pushout_zero (x : YonedaExt B A) : pushout (0 : A ⟶ A') x = zero B A' :=
  induction_on x fun E => pushout_eq_mk (E := E) (F := Extension.trivial B A')
    (biprod.lift 0 E.g) (by ext <;> simp) (by simp)

lemma pushout_neg_id (x : YonedaExt B A) : pushout (-𝟙 A) x = pullback (-𝟙 B) x :=
  induction_on x fun E => pushout_eq_pullback (E := E) (F := E) (-𝟙 E.X) (by simp) (by simp)

/-! ### The Baer sum -/

/-- The *Baer sum* `E₁ + E₂`: push out `E₁ ⊕ E₂` along the sum map `A ⊕ A → A` and pull back
along the diagonal `B → B ⊕ B`. -/
noncomputable instance : Add (YonedaExt B A) where
  add x y := pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A)) (directSum x y))

noncomputable instance : Zero (YonedaExt B A) where
  zero := zero B A

/-- The negative of a class: the pullback along `-𝟙 B`. -/
noncomputable instance : Neg (YonedaExt B A) where
  neg x := pullback (-𝟙 B) x

lemma add_def (x y : YonedaExt B A) :
    x + y = pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
      (directSum x y)) :=
  rfl

lemma zero_def : (0 : YonedaExt B A) = zero B A :=
  rfl

lemma neg_def (x : YonedaExt B A) : -x = pullback (-𝟙 B) x :=
  rfl

/-- The Baer sum of two extensions, as the class of the extension
`(A ⨿_{A ⊕ A} (E₁ ⊕ E₂)) ×_{B ⊕ B} B`. -/
lemma mk_add_mk (E₁ E₂ : Extension B A) :
    mk E₁ + mk E₂ = mk (((E₁.directSum E₂).pushout (biprod.desc (𝟙 A) (𝟙 A))).pullback
      (biprod.lift (𝟙 B) (𝟙 B))) :=
  rfl

lemma baerSum_comm (x y : YonedaExt B A) : x + y = y + x := by
  have h₁ : (biprod.braiding A A).hom ≫ biprod.desc (𝟙 A) (𝟙 A) = biprod.desc (𝟙 A) (𝟙 A) := by
    ext <;> simp
  have h₂ : biprod.lift (𝟙 B) (𝟙 B) ≫ (biprod.braiding B B).hom = biprod.lift (𝟙 B) (𝟙 B) := by
    ext <;> simp
  calc x + y = pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
        (pushout (biprod.braiding A A).hom (directSum x y))) := by
        rw [← pushout_comp, h₁, add_def]
    _ = pullback (biprod.lift (𝟙 B) (𝟙 B) ≫ (biprod.braiding B B).hom)
        (pushout (biprod.desc (𝟙 A) (𝟙 A)) (directSum y x)) := by
        rw [pushout_directSum_braiding, pushout_pullback, pullback_comp]
    _ = y + x := by rw [h₂, add_def]

lemma baerSum_zero (x : YonedaExt B A) : x + 0 = x := by
  have h : biprod.map (𝟙 A) (0 : A ⟶ A) ≫ biprod.desc (𝟙 A) (𝟙 A) = biprod.fst := by
    ext <;> simp
  calc x + 0 = pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
        (directSum (pushout (𝟙 A) x) (pushout (0 : A ⟶ A) x))) := by
        rw [pushout_id, pushout_zero, add_def, zero_def]
    _ = pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
        (pushout (biprod.map (𝟙 A) (0 : A ⟶ A)) (directSum x x))) := by
        rw [pushout_directSum]
    _ = pullback (biprod.lift (𝟙 B) (𝟙 B)) (pullback biprod.fst x) := by
        rw [← pushout_comp, h, pushout_fst_directSum]
    _ = x := by rw [← pullback_comp, biprod.lift_fst, pullback_id]

lemma baerSum_neg (x : YonedaExt B A) : x + -x = 0 := by
  have h : biprod.lift (𝟙 A) (𝟙 A) ≫ biprod.map (𝟙 A) (-𝟙 A) ≫ biprod.desc (𝟙 A) (𝟙 A) = 0 := by
    simp [biprod.lift_eq]
  calc x + -x = pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
        (directSum (pushout (𝟙 A) x) (pushout (-𝟙 A) x))) := by
        rw [pushout_id, pushout_neg_id, add_def, neg_def]
    _ = pullback (biprod.lift (𝟙 B) (𝟙 B))
        (pushout (biprod.map (𝟙 A) (-𝟙 A) ≫ biprod.desc (𝟙 A) (𝟙 A)) (directSum x x)) := by
        rw [pushout_comp, pushout_directSum]
    _ = pushout (biprod.map (𝟙 A) (-𝟙 A) ≫ biprod.desc (𝟙 A) (𝟙 A))
        (pushout (biprod.lift (𝟙 A) (𝟙 A)) x) := by
        rw [pushout_lift_id_id, pushout_pullback]
    _ = 0 := by rw [← pushout_comp, h, pushout_zero, zero_def]

/-- The two ways of bracketing the Baer sum of three classes, written in terms of the triple
direct sum. -/
private lemma baerSum_add_add (x y z : YonedaExt B A) :
    x + y + z = pullback (biprod.lift (𝟙 B) (𝟙 B) ≫ biprod.map (biprod.lift (𝟙 B) (𝟙 B)) (𝟙 B))
      (pushout (biprod.map (biprod.desc (𝟙 A) (𝟙 A)) (𝟙 A) ≫ biprod.desc (𝟙 A) (𝟙 A))
        (directSum (directSum x y) z)) := by
  calc x + y + z = pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
        (directSum (pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
          (directSum x y))) (pullback (𝟙 B) (pushout (𝟙 A) z)))) := by
        rw [pullback_id, pushout_id, add_def, add_def]
    _ = pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
        (pullback (biprod.map (biprod.lift (𝟙 B) (𝟙 B)) (𝟙 B))
          (pushout (biprod.map (biprod.desc (𝟙 A) (𝟙 A)) (𝟙 A))
            (directSum (directSum x y) z)))) := by
        rw [pushout_directSum, pullback_directSum]
    _ = _ := by
        rw [pullback_comp (biprod.lift (𝟙 B) (𝟙 B)), pushout_comp _ (biprod.desc (𝟙 A) (𝟙 A)),
          pushout_pullback]

private lemma baerSum_add_add' (x y z : YonedaExt B A) :
    x + (y + z) = pullback (biprod.lift (𝟙 B) (𝟙 B) ≫ biprod.map (𝟙 B) (biprod.lift (𝟙 B) (𝟙 B)))
      (pushout (biprod.map (𝟙 A) (biprod.desc (𝟙 A) (𝟙 A)) ≫ biprod.desc (𝟙 A) (𝟙 A))
        (directSum x (directSum y z))) := by
  calc x + (y + z) = pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
        (directSum (pullback (𝟙 B) (pushout (𝟙 A) x))
          (pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
            (directSum y z))))) := by
        rw [pullback_id, pushout_id, add_def, add_def]
    _ = pullback (biprod.lift (𝟙 B) (𝟙 B)) (pushout (biprod.desc (𝟙 A) (𝟙 A))
        (pullback (biprod.map (𝟙 B) (biprod.lift (𝟙 B) (𝟙 B)))
          (pushout (biprod.map (𝟙 A) (biprod.desc (𝟙 A) (𝟙 A)))
            (directSum x (directSum y z))))) := by
        rw [pushout_directSum, pullback_directSum]
    _ = _ := by
        rw [pullback_comp (biprod.lift (𝟙 B) (𝟙 B)), pushout_comp _ (biprod.desc (𝟙 A) (𝟙 A)),
          pushout_pullback]

lemma baerSum_assoc (x y z : YonedaExt B A) : x + y + z = x + (y + z) := by
  have h₁ : (biprod.lift (𝟙 B) (𝟙 B) ≫ biprod.map (𝟙 B) (biprod.lift (𝟙 B) (𝟙 B))) ≫
      (biprod.associator B B B).inv =
        biprod.lift (𝟙 B) (𝟙 B) ≫ biprod.map (biprod.lift (𝟙 B) (𝟙 B)) (𝟙 B) := by
    ext <;> simp
  have h₂ : (biprod.associator A A A).hom ≫ biprod.map (𝟙 A) (biprod.desc (𝟙 A) (𝟙 A)) ≫
      biprod.desc (𝟙 A) (𝟙 A) =
        biprod.map (biprod.desc (𝟙 A) (𝟙 A)) (𝟙 A) ≫ biprod.desc (𝟙 A) (𝟙 A) := by
    ext <;> simp [biprod.lift_eq]
  have h₃ : directSum x (directSum y z) = pullback (biprod.associator B B B).inv
      (pushout (biprod.associator A A A).hom (directSum (directSum x y) z)) := by
    rw [pushout_directSum_associator, ← pullback_comp, Iso.inv_hom_id, pullback_id]
  rw [baerSum_add_add, baerSum_add_add', h₃, pushout_pullback,
    ← pullback_comp (biprod.lift (𝟙 B) (𝟙 B) ≫ biprod.map (𝟙 B) (biprod.lift (𝟙 B) (𝟙 B))),
    ← pushout_comp (biprod.associator A A A).hom, h₁, h₂]

/-- **Stacks 010L**, the group law. The Baer sum `(E₁, E₂) ↦ E₁ + E₂` (push out `E₁ ⊕ E₂` along
the sum map `A ⊕ A → A`, pull back along the diagonal `B → B ⊕ B`) is a commutative group law
on `Ext_C(B, A)`, with zero the class of the split extension `A ⊕ B` and negation the pullback
along `-𝟙 B`. -/
@[stacks 010L "the commutative group law: the Baer sum on the isomorphism classes of extensions \
of `B` by `A`, in an arbitrary abelian category"]
noncomputable instance instAddCommGroup : AddCommGroup (YonedaExt B A) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc := baerSum_assoc
  zero_add x := (baerSum_comm _ _).trans (baerSum_zero x)
  add_zero := baerSum_zero
  neg_add_cancel x := (baerSum_comm _ _).trans (baerSum_neg x)
  add_comm := baerSum_comm
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### Functoriality of the group law -/

lemma pullback_add (β : B' ⟶ B) (x y : YonedaExt B A) :
    pullback β (x + y) = pullback β x + pullback β y := by
  have h : β ≫ biprod.lift (𝟙 B) (𝟙 B) = biprod.lift (𝟙 B') (𝟙 B') ≫ biprod.map β β := by
    ext <;> simp
  rw [add_def x y, ← pullback_comp, h, pullback_comp, ← pushout_pullback, pullback_directSum,
    add_def (pullback β x)]

lemma pushout_add (α : A ⟶ A') (x y : YonedaExt B A) :
    pushout α (x + y) = pushout α x + pushout α y := by
  have h : biprod.desc (𝟙 A) (𝟙 A) ≫ α = biprod.map α α ≫ biprod.desc (𝟙 A') (𝟙 A') := by
    ext <;> simp
  rw [add_def x y, pushout_pullback, ← pushout_comp, h, pushout_comp, pushout_directSum,
    add_def (pushout α x)]

/-- The pullback along `β : B' → B` as a group homomorphism `Ext_C(B, A) → Ext_C(B', A)`. -/
noncomputable def pullbackAddHom (β : B' ⟶ B) : YonedaExt B A →+ YonedaExt B' A :=
  AddMonoidHom.mk' (pullback β) (pullback_add β)

@[simp]
lemma pullbackAddHom_apply (β : B' ⟶ B) (x : YonedaExt B A) :
    pullbackAddHom β x = pullback β x :=
  rfl

/-- The pushout along `α : A → A'` as a group homomorphism `Ext_C(B, A) → Ext_C(B, A')`. -/
noncomputable def pushoutAddHom (α : A ⟶ A') : YonedaExt B A →+ YonedaExt B A' :=
  AddMonoidHom.mk' (pushout α) (pushout_add α)

@[simp]
lemma pushoutAddHom_apply (α : A ⟶ A') (x : YonedaExt B A) :
    pushoutAddHom α x = pushout α x :=
  rfl

variable (C) in
/-- **Stacks 010L**, functoriality. With the Baer sum, `(B, A) ↦ Ext_C(B, A)` is a functor
`Cᵒᵖ ⥤ C ⥤ AddCommGrpCat`: a map `α : A → A'` acts by pushout along `α`, a map `β : B' → B`
acts by pullback along `β`, these maps are group homomorphisms, compatible with identities and
composition, and pushouts commute with pullbacks. -/
@[stacks 010L "functoriality in both variables: pushout and pullback are group homomorphisms, \
functorial and commuting with each other"]
noncomputable def functor : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{max u v} where
  obj B :=
    { obj A := AddCommGrpCat.of (YonedaExt B.unop A)
      map α := AddCommGrpCat.ofHom (pushoutAddHom α)
      map_id A := by ext x; exact pushout_id x
      map_comp f g := by ext x; exact pushout_comp f g x }
  map β :=
    { app A := AddCommGrpCat.ofHom (pullbackAddHom β.unop)
      naturality A A' α := by ext x; exact (pushout_pullback α β.unop x).symm }
  map_id B := by ext A x; exact pullback_id x
  map_comp f g := by ext A x; exact pullback_comp g.unop f.unop x

end YonedaExt

end CategoryTheory.Abelian
