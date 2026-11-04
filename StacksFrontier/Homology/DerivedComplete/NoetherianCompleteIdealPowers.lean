module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphism
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimHom
public import StacksFrontier.Homology.DerivedComplete.AdicDerivedCompletion
public import StacksFrontier.Homology.DerivedComplete.NoetherianKoszulProIso
public import StacksFrontier.RingTheory.Noetherian.ULift
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Naive derived completion over a Noetherian ring

Let `I` be an ideal of a Noetherian ring `A`. The derived inverse limit of the derived tensor
products `K ⊗ᴸ[A] A/Iⁿ` computes derived completion with respect to `I`; functorially, this
construction is left adjoint to the inclusion of the derived-complete objects into `D(A)`.

## Main definitions

* `NoetherianAdicCompletion.idealPowerQuotientSystem` is the inverse system in `D(A)` formed by
  the quotients by the positive powers of an ideal.
* `NoetherianAdicCompletion.derivedReductionMap` is the natural map induced by `A → A/Iⁿ`.
* `NoetherianAdicCompletion.IsDerivedLimitWithProjections` retains the projections in the
  distinguished triangle defining a derived limit.
* `NoetherianAdicCompletion.HasEventualInverses` is the form in which a natural map of inverse
  systems is a pro-isomorphism without reindexing the source.

## Main results

* `NoetherianAdicCompletion.idealPowerDerivedLimit_isLeftAdjoint` identifies naive derived
  completion over a Noetherian ring with the derived-completion reflector.
* `NoetherianAdicCompletion.isIso_unit_app_of_isDerivedComplete` identifies an already
  derived-complete object with its reflection by the adjunction unit.
* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_map_succ` is the cone identity
  satisfied by the projections of a derived limit.
* `NoetherianAdicCompletion.exists_isDerivedLimitWithProjections` and
  `NoetherianAdicCompletion.derivedLimitProjections` extract projections from the
  derived-limit property, the latter by a choice.
* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.ofIso` transports a derived limit with
  projections along an isomorphism of the limit object.

## Implementation notes

Positive powers are indexed by `n : ℕ` using the exponent `n + 1`. The ring and its modules
have independent universes. The reflector and its unit live in the original derived category;
only the tensor formula uses `ULift` to accommodate the same-universe tensor API of Tag 0BYI.
The statement is valid for any derived tensor product carrying that structure.

A derived-limit object alone does not specify its projections or the comparison map from the
original object. Here the projections are natural in that object, occur in the distinguished
triangle, and their composites with the adjunction unit are the canonical reduction maps.
This records the natural map introduced in the source's section and used in the proof of 0922.
It does not assert ordinary completeness for every derived-complete module: the finiteness
hypothesis and the additional completion results in 09BA are needed for that conclusion.

## References

* [The Stacks Project, Tag 0922](https://stacks.math.columbia.edu/tag/0922)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v w x

namespace NoetherianAdicCompletion

attribute [local instance] HasDerivedCategory.standard

/-! ### The tower of quotients by the powers of an ideal -/

/-- The transition map from the quotient by `I^(m+1)` to the quotient by `I^(n+1)`, for
`n ≤ m`. -/
public noncomputable def idealPowerQuotientTransition
    {A : Type u} [CommRing A] (I : Ideal A) (m n : ℕ) (h : n ≤ m) :
    ModuleCat.of A (A ⧸ I ^ (m + 1)) ⟶ ModuleCat.of A (A ⧸ I ^ (n + 1)) :=
  ModuleCat.ofHom ((Ideal.Quotient.factorₐ A
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).toLinearMap)

/-- The inverse system in `D(A)` formed by the quotients by the positive powers of `I`. -/
public noncomputable def idealPowerQuotientSystem
    {A : Type u} [CommRing A] (I : Ideal A) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Functor.ofOpSequence (X := fun n ↦ DerivedCategory.Q.obj
    (((ChainComplex.single₀ (ModuleCat.{u} A)).obj
      (ModuleCat.of A (A ⧸ I ^ (n + 1)))).extend ComplexShape.embeddingDownNat))
    (fun n ↦ DerivedCategory.Q.map
      (HomologicalComplex.extendMap
        ((ChainComplex.single₀ (ModuleCat.{u} A)).map
          (idealPowerQuotientTransition I (n + 1) n (Nat.le_succ n)))
        ComplexShape.embeddingDownNat))

/-- The `n`-th term of `idealPowerQuotientSystem I` is `(A/I^(n+1))[0]`. -/
@[simp]
public theorem idealPowerQuotientSystem_obj
    {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    (idealPowerQuotientSystem I).obj ⟨n⟩ = DerivedCategory.Q.obj
      (((ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ I ^ (n + 1)))).extend ComplexShape.embeddingDownNat) := rfl

/-- The quotient map `A[0] → (A/I^(n+1))[0]`, with the target represented by the
corresponding term of `idealPowerQuotientSystem`. -/
public noncomputable def idealPowerQuotientMap
    {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      (idealPowerQuotientSystem I).obj ⟨n⟩ :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
      (ModuleCat.ofHom (I ^ (n + 1)).mkQ) ≫
    DerivedCategory.Q.map
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (ModuleCat.of A (A ⧸ I ^ (n + 1))) 0 0 (by simp)).inv

/-- The canonical natural map `K → K ⊗ᴸ[A] A/I^(n+1)`, induced by the quotient map
and the right unit of the derived tensor product. -/
public noncomputable def derivedReductionMap
    {A : Type u} [CommRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A) (n : ℕ) :
    𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      T.tensor.flip.obj ((idealPowerQuotientSystem I).obj ⟨n⟩) :=
  T.rightUnitor.inv ≫ T.tensor.flip.map (idealPowerQuotientMap I n)

/-! ### Derived limits with specified projections -/

/-- A derived limit with specified projections: their product is the first map in the
distinguished triangle whose middle map is the Milnor difference map. -/
public def IsDerivedLimitWithProjections
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (K : D) (π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩) : Prop :=
  ∃ δ : (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ⟶ K⟦(1 : ℤ)⟧,
    Triangle.mk (Pi.lift π)
      (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang D

/-- Forgetting the specified projections gives the usual derived-limit predicate. -/
public theorem IsDerivedLimitWithProjections.isDerivedLimit
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    {K : D} {π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩}
    (h : IsDerivedLimitWithProjections F K π) : IsDerivedLimit F K := by
  obtain ⟨δ, hδ⟩ := h
  exact ⟨Pi.lift π, δ, hδ⟩

/-- The projections of a derived limit are compatible with the transition maps of the system:
this is the vanishing of the composite of the two first maps of the defining triangle, read off
one factor of the product at a time. -/
public theorem IsDerivedLimitWithProjections.comp_map_succ
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    {K : D} {π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩}
    (h : IsDerivedLimitWithProjections F K π) (n : ℕ) :
    π (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = π n := by
  obtain ⟨δ, hδ⟩ := h
  have h0 := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hδ
  have h1 := congrArg (· ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) h0
  simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, Category.assoc, limit.lift_π, Fan.mk_π_app,
    Preadditive.comp_sub, zero_comp] at h1
  rw [← Category.assoc] at h1
  simp only [limit.lift_π, Fan.mk_π_app] at h1
  exact (sub_eq_zero.1 h1).symm

/-- Any derived limit carries projections: the components of the first map of some defining
triangle. -/
public theorem exists_isDerivedLimitWithProjections
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] {K : D} (h : IsDerivedLimit F K) :
    ∃ π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩, IsDerivedLimitWithProjections F K π := by
  obtain ⟨p, δ, hδ⟩ := h
  refine ⟨fun n ↦ p ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n, δ, ?_⟩
  have : (Pi.lift fun n : ℕ ↦ p ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) = p :=
    Pi.hom_ext _ _ fun n ↦ by simp
  simpa only [this] using hδ

/-- A choice of projections for a derived limit. The choice is arbitrary: a derived limit is
unique only up to non-unique isomorphism, and different defining triangles have different first
maps, so a statement that is to pin the projections down must say which ones it means. -/
public noncomputable def derivedLimitProjections
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] {K : D} (h : IsDerivedLimit F K) :
    ∀ n : ℕ, K ⟶ F.obj ⟨n⟩ :=
  (exists_isDerivedLimitWithProjections h).choose

/-- The chosen projections `derivedLimitProjections h` are projections of the derived
limit `h`. -/
public theorem isDerivedLimitWithProjections_derivedLimitProjections
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] {K : D} (h : IsDerivedLimit F K) :
    IsDerivedLimitWithProjections F K (derivedLimitProjections h) :=
  (exists_isDerivedLimitWithProjections h).choose_spec

/-- Transporting a derived limit with projections along an isomorphism of the limit object. -/
public theorem IsDerivedLimitWithProjections.ofIso
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    {K K' : D} {π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩}
    (h : IsDerivedLimitWithProjections F K π) (e : K ≅ K') :
    IsDerivedLimitWithProjections F K' (fun n ↦ e.inv ≫ π n) := by
  obtain ⟨δ, hδ⟩ := h
  refine ⟨δ ≫ e.hom⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ hδ _ (Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_)
  · refine (Category.comp_id _).trans (Pi.hom_ext _ _ fun n ↦ ?_)
    simp
  · simp
  · dsimp
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]

/-! ### Pro-isomorphisms without reindexing -/

/-- A natural map of inverse systems has eventual inverses when, for every level `n`, some later
level maps back so that both composites are the transition maps. This is the form of the
pro-isomorphisms of Stacks 0921. -/
public def HasEventualInverses {C : Type u} [Category.{v} C] {F G : ℕᵒᵖ ⥤ C} (φ : F ⟶ G) :
    Prop :=
  ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (s : G.obj (op m) ⟶ F.obj (op n)),
    φ.app (op m) ≫ s = F.map (homOfLE h).op ∧ s ≫ φ.app (op n) = G.map (homOfLE h).op

private theorem map_homOfLE_comp {C : Type u} [Category.{v} C] (F : ℕᵒᵖ ⥤ C)
    {a b c : ℕ} (h₁ : b ≤ a) (h₂ : c ≤ b) :
    F.map (homOfLE h₁).op ≫ F.map (homOfLE h₂).op = F.map (homOfLE (h₂.trans h₁)).op := by
  rw [← F.map_comp]
  rfl

/-- Two transition maps of an inverse system indexed by `ℕᵒᵖ` compose to the transition map
along the composite inequality. -/
public alias map_homOfLE_op_comp := map_homOfLE_comp

private theorem map_homOfLE_comp_assoc {C : Type u} [Category.{v} C] (F : ℕᵒᵖ ⥤ C)
    {a b c : ℕ} (h₁ : b ≤ a) (h₂ : c ≤ b) {Z : C} (g : F.obj (op c) ⟶ Z) :
    F.map (homOfLE h₁).op ≫ F.map (homOfLE h₂).op ≫ g =
      F.map (homOfLE (h₂.trans h₁)).op ≫ g := by
  rw [← Category.assoc, map_homOfLE_comp]

private noncomputable def eventualLevel {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) (n : ℕ) : ℕ :=
  (hφ n).choose

private theorem le_eventualLevel {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) (n : ℕ) :
    n ≤ eventualLevel hφ n :=
  (hφ n).choose_spec.choose

private noncomputable def eventualInverse {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) (n : ℕ) :
    G.obj (op (eventualLevel hφ n)) ⟶ F.obj (op n) :=
  (hφ n).choose_spec.choose_spec.choose

private theorem app_eventualInverse {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) (n : ℕ) :
    φ.app (op (eventualLevel hφ n)) ≫ eventualInverse hφ n =
      F.map (homOfLE (le_eventualLevel hφ n)).op :=
  (hφ n).choose_spec.choose_spec.choose_spec.1

private theorem eventualInverse_app {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) (n : ℕ) :
    eventualInverse hφ n ≫ φ.app (op n) =
      G.map (homOfLE (le_eventualLevel hφ n)).op :=
  (hφ n).choose_spec.choose_spec.choose_spec.2

private theorem eq_of_app_comp_eq {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) {k m : ℕ}
    {a b : G.obj (op k) ⟶ F.obj (op m)} (hab : φ.app (op k) ≫ a = φ.app (op k) ≫ b) :
    G.map (homOfLE (le_eventualLevel hφ k)).op ≫ a =
      G.map (homOfLE (le_eventualLevel hφ k)).op ≫ b := by
  rw [← eventualInverse_app, Category.assoc, Category.assoc, hab]

private noncomputable def boundLevel {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup (eventualLevel hφ)

private theorem eventualLevel_le_boundLevel {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) {j n : ℕ} (h : j ≤ n) :
    eventualLevel hφ j ≤ boundLevel hφ n :=
  Finset.le_sup (f := eventualLevel hφ) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

private noncomputable def inverseLevel {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup fun j ↦ eventualLevel hφ (boundLevel hφ j)

private theorem inverseLevel_mono {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) :
    Monotone (inverseLevel hφ) := fun _ _ h ↦
  Finset.sup_mono (Finset.range_subset_range.mpr (Nat.succ_le_succ h))

private theorem eventualLevel_boundLevel_le {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) (n : ℕ) :
    eventualLevel hφ (boundLevel hφ n) ≤ inverseLevel hφ n :=
  Finset.le_sup (f := fun j ↦ eventualLevel hφ (boundLevel hφ j))
    (Finset.mem_range.mpr (Nat.lt_succ_self n))

private theorem eventualLevel_le_inverseLevel {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} {φ : F ⟶ G} (hφ : HasEventualInverses φ) (n : ℕ) :
    eventualLevel hφ n ≤ inverseLevel hφ n :=
  (eventualLevel_le_boundLevel hφ le_rfl).trans
    ((le_eventualLevel hφ _).trans (eventualLevel_boundLevel_le hφ n))

/-- A natural map with eventual inverses is a pro-isomorphism whose forward
representative is the given natural map, without reindexing. -/
private noncomputable def proIsoOfHasEventualInverses {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} (φ : F ⟶ G) (hφ : HasEventualInverses φ) : InverseSequence.ProIso F G where
  α := fun n ↦ n
  β := inverseLevel hφ
  αmono := fun _ _ h ↦ h
  βmono := inverseLevel_mono hφ
  αle := fun _ ↦ le_rfl
  βle := fun n ↦ (le_eventualLevel hφ n).trans (eventualLevel_le_inverseLevel hφ n)
  φ := fun n ↦ φ.app (op n)
  ψ := fun n ↦ G.map (homOfLE (eventualLevel_le_inverseLevel hφ n)).op ≫ eventualInverse hφ n
  φnat := by
    intro m m' h
    exact φ.naturality (homOfLE h).op
  ψnat := by
    intro m m' h
    simp only [InverseSequence.tr]
    let k := boundLevel hφ m'
    have hk₁ : eventualLevel hφ m ≤ k := eventualLevel_le_boundLevel hφ h
    have hk₂ : eventualLevel hφ m' ≤ k := eventualLevel_le_boundLevel hφ le_rfl
    have hk₃ : eventualLevel hφ k ≤ inverseLevel hφ m' := eventualLevel_boundLevel_le hφ m'
    have key := eq_of_app_comp_eq hφ (k := k)
      (a := G.map (homOfLE hk₁).op ≫ eventualInverse hφ m)
      (b := G.map (homOfLE hk₂).op ≫ eventualInverse hφ m' ≫ F.map (homOfLE h).op) (by
        rw [← Category.assoc, ← φ.naturality, Category.assoc, app_eventualInverse,
          ← Category.assoc, ← φ.naturality, Category.assoc, reassoc_of% app_eventualInverse,
          map_homOfLE_comp, map_homOfLE_comp, map_homOfLE_comp])
    have split₁ : G.map (homOfLE (((eventualLevel_le_inverseLevel hφ m).trans
        (inverseLevel_mono hφ h)) : eventualLevel hφ m ≤ inverseLevel hφ m')).op ≫
          eventualInverse hφ m =
        G.map (homOfLE hk₃).op ≫
          G.map (homOfLE (le_eventualLevel hφ k)).op ≫ G.map (homOfLE hk₁).op ≫
            eventualInverse hφ m := by
      simp only [map_homOfLE_comp_assoc]
    have split₂ : G.map (homOfLE (eventualLevel_le_inverseLevel hφ m')).op ≫
        eventualInverse hφ m' =
        G.map (homOfLE hk₃).op ≫
          G.map (homOfLE (le_eventualLevel hφ k)).op ≫ G.map (homOfLE hk₂).op ≫
            eventualInverse hφ m' := by
      simp only [map_homOfLE_comp_assoc]
    rw [map_homOfLE_comp_assoc, split₁, split₂, key]
    simp only [Category.assoc]
  ψφ := by
    intro m
    simp only [InverseSequence.tr]
    rw [← Category.assoc, ← φ.naturality, Category.assoc, app_eventualInverse,
      map_homOfLE_comp]
  φψ := by
    intro m
    simp only [InverseSequence.tr, Category.assoc, eventualInverse_app, map_homOfLE_comp]

/-- A composite of natural maps with eventual inverses has eventual inverses. -/
public theorem HasEventualInverses.comp {C : Type u} [Category.{v} C] {F G H : ℕᵒᵖ ⥤ C}
    {φ : F ⟶ G} {ψ : G ⟶ H} (hφ : HasEventualInverses φ) (hψ : HasEventualInverses ψ) :
    HasEventualInverses (φ ≫ ψ) := by
  intro n
  obtain ⟨m₁, h₁, s₁, hs₁, ht₁⟩ := hφ n
  obtain ⟨m₂, h₂, s₂, hs₂, ht₂⟩ := hψ m₁
  refine ⟨m₂, h₁.trans h₂, s₂ ≫ s₁, ?_, ?_⟩
  · have := φ.naturality (homOfLE h₂).op
    rw [NatTrans.comp_app, Category.assoc, reassoc_of% hs₂, ← reassoc_of% this, hs₁,
      map_homOfLE_comp]
  · have := ψ.naturality (homOfLE h₁).op
    rw [NatTrans.comp_app, Category.assoc, reassoc_of% ht₁, this, reassoc_of% ht₂,
      map_homOfLE_comp]

/-- Applying a functor levelwise preserves eventual inverses. -/
public theorem HasEventualInverses.whiskerRight {C : Type u} [Category.{v} C]
    {E : Type w} [Category E] {F G : ℕᵒᵖ ⥤ C}
    {φ : F ⟶ G} (hφ : HasEventualInverses φ) (L : C ⥤ E) :
    HasEventualInverses (Functor.whiskerRight φ L) := by
  intro n
  obtain ⟨m, h, s, hs, ht⟩ := hφ n
  refine ⟨m, h, L.map s, ?_, ?_⟩
  · simp only [Functor.whiskerRight_app, Functor.comp_map, ← L.map_comp, hs]
  · simp only [Functor.whiskerRight_app, Functor.comp_map, ← L.map_comp, ht]

/-- The sequential representative of a natural map with the identity reindexing. -/
private noncomputable def levelwiseRep {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} (φ : F ⟶ G) (H : C ⥤ Ab.{w}) :
    Rlim.Pro.SequentialRep (F ⋙ H) (G ⋙ H) where
  index n := n
  index_strict := strictMono_id
  index_le _ := le_rfl
  component n := H.map (φ.app (op n))
  naturality h := by
    simp only [Functor.comp_map, ← H.map_comp]
    exact congrArg H.map (φ.naturality (homOfLE h).op)

private theorem levelwiseRep_productSecond {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} (φ : F ⟶ G) (H : C ⥤ Ab.{w}) :
    (levelwiseRep φ H).productSecond = (levelwiseRep φ H).productFirst := by
  apply Pi.hom_ext
  intro n
  have hid : (F ⋙ H).map (homOfLE (le_refl n)).op = 𝟙 _ := by
    rw [show (homOfLE (le_refl n)).op = 𝟙 (op n) from rfl]
    exact (F ⋙ H).map_id _
  simp [Rlim.Pro.SequentialRep.productSecond, Rlim.Pro.SequentialRep.productFirst,
    levelwiseRep]

private theorem comparison_levelwiseRep {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (φ : F ⟶ G) (H : C ⥤ Ab.{w}) :
    piComparison H (fun n : ℕ => F.obj (op n)) ≫ (levelwiseRep φ H).productFirst =
      H.map (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) ≫
        piComparison H (fun n : ℕ => G.obj (op n)) := by
  apply Pi.hom_ext
  intro n
  simp only [Rlim.Pro.SequentialRep.productFirst, levelwiseRep, Category.assoc,
    Pi.map'_comp_π]
  exact (congrArg (· ≫ H.map (φ.app (op n)))
      (piComparison_comp_π H (fun n : ℕ => F.obj (op n)) n)).trans
    ((congrArg (H.map _ ≫ ·) (piComparison_comp_π H (fun n : ℕ => G.obj (op n)) n)).trans
      (by rw [← H.map_comp, ← H.map_comp, Limits.Pi.map_π])).symm

private theorem levelwiseRep_represents {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} (φ : F ⟶ G) (hφ : HasEventualInverses φ) (H : C ⥤ Ab.{w})
    (ρ : Rlim.Pro.proYoneda (G ⋙ H) ⟶ Rlim.Pro.proYoneda (F ⋙ H))
    (hρ : Rlim.Pro.proIsoRepresents
      (proIsoOfHasEventualInverses (Functor.whiskerRight φ H) (hφ.whiskerRight H)) ρ) :
    (levelwiseRep φ H).Represents ρ :=
  hρ

private theorem productMap_delta {D : Type u} [Category.{v} D] [Preadditive D]
    {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (φ : F ⟶ G) :
    Rlim.Hom.systemDelta F ≫ (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) =
      (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) ≫ Rlim.Hom.systemDelta G := by
  apply Pi.hom_ext
  intro n
  simp only [Rlim.Hom.systemDelta, Category.assoc, Pi.map_π, Pi.lift_π, Pi.lift_π_assoc,
    Preadditive.sub_comp, Preadditive.comp_sub, Pi.map_π_assoc, NatTrans.naturality]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_levelwise_milnor_maps {D : Type u} [Category.{v} D]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (φ : F ⟶ G) (hφ : HasEventualInverses φ) (L : D) :
    ∃ (b : limit (Rlim.Hom.homSystem L F) ⟶ limit (Rlim.Hom.homSystem L G))
      (hδ : Rlim.delta (Rlim.Hom.shiftedHomSystem L F) ≫
          Rlim.Hom.shiftedHomProductMap L F G (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) =
        Rlim.Hom.shiftedHomProductMap L F G (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) ≫
          Rlim.delta (Rlim.Hom.shiftedHomSystem L G)),
      IsIso b ∧
      IsIso (cokernel.map (Rlim.delta (Rlim.Hom.shiftedHomSystem L F))
        (Rlim.delta (Rlim.Hom.shiftedHomSystem L G))
        (Rlim.Hom.shiftedHomProductMap L F G (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)))
        (Rlim.Hom.shiftedHomProductMap L F G (Limits.Pi.map fun n : ℕ ↦ φ.app (op n))) hδ) ∧
      Rlim.limitToProduct (Rlim.Hom.homSystem L F) ≫
          Rlim.Hom.homProductMap L F G (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) =
        b ≫ Rlim.limitToProduct (Rlim.Hom.homSystem L G) := by
  let H := preadditiveCoyoneda.obj (op L)
  let J := shiftFunctor D (-1 : ℤ) ⋙ H
  have : PreservesLimitsOfSize.{0, 0} H := preservesSmallestLimits_of_preservesLimits H
  have : PreservesLimitsOfSize.{0, 0} J := preservesSmallestLimits_of_preservesLimits J
  have e₀ : (levelwiseRep φ H).productFirst =
      Rlim.Hom.homProductMap L F G (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) := by
    dsimp [Rlim.Hom.homProductMap, Rlim.Hom.homProductComparison]
    rw [← comparison_levelwiseRep, IsIso.inv_hom_id_assoc]
  have e₁ : (levelwiseRep φ J).productFirst =
      Rlim.Hom.shiftedHomProductMap L F G (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) := by
    show _ = inv (piComparison J _) ≫ J.map _ ≫ piComparison J _
    rw [← comparison_levelwiseRep, IsIso.inv_hom_id_assoc]
  have e₂ : (levelwiseRep φ J).productSecond =
      Rlim.Hom.shiftedHomProductMap L F G (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) := by
    rw [levelwiseRep_productSecond, e₁]
  obtain ⟨mapLim, mapR1lim, _, _, _, _, _, _, _, _, _, _, _, hiso, hcompat⟩ :=
    Rlim.Pro.exists_map_lim_and_cokernel_delta.{v, u}
  obtain ⟨φ₀, hφ₀, _, hb, _⟩ := hiso (F ⋙ H) (G ⋙ H)
    (proIsoOfHasEventualInverses (Functor.whiskerRight φ H) (hφ.whiskerRight H))
  obtain ⟨φ₁, hφ₁, _, _, hc⟩ := hiso (F ⋙ J) (G ⋙ J)
    (proIsoOfHasEventualInverses (Functor.whiskerRight φ J) (hφ.whiskerRight J))
  obtain ⟨hδ, hlim, hcoker⟩ := hcompat F G L _ _ φ₀ φ₁ (levelwiseRep φ H) (levelwiseRep φ J)
    (levelwiseRep_represents φ hφ H φ₀ hφ₀) (levelwiseRep_represents φ hφ J φ₁ hφ₁) e₀ e₁ e₂
  exact ⟨mapLim _ _ φ₀, hδ, hb, hcoker ▸ hc, hlim⟩

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of derived-limit triangles whose middle and last maps are the levelwise
product map of a natural map with eventual inverses is an isomorphism on derived limits. -/
private theorem isIso_hom₁_of_hasEventualInverses {D : Type u} [Category.{v} D]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (φ : F ⟶ G) (hφ : HasEventualInverses φ)
    {K M : D} (tK : Rlim.Hom.DerivedLimitTriangle F K)
    (tM : Rlim.Hom.DerivedLimitTriangle G M)
    (f : tK.triangle ⟶ tM.triangle)
    (hf₂ : f.hom₂ = Limits.Pi.map fun n : ℕ ↦ φ.app (op n))
    (hf₃ : f.hom₃ = Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) :
    IsIso f.hom₁ := by
  apply isIso_of_yoneda_map_bijective
  intro L
  let H := preadditiveCoyoneda.obj (op L)
  obtain ⟨s, S, hS⟩ := Rlim.Hom.hom_into_isDerivedLimit_shortExact F K L
    ⟨tK.inclusion, tK.connecting, tK.distinguished⟩
  obtain ⟨e, he₂, he₃⟩ := Rlim.Pro.triangle_morphism s.distinguished tK.distinguished
    (𝟙 _) (𝟙 _) (by simp)
  have : IsIso e.hom₁ := isIso₁_of_isIso₂₃ e s.distinguished tK.distinguished
    (he₂ ▸ inferInstance) (he₃ ▸ inferInstance)
  let g : s.triangle ⟶ tM.triangle := e ≫ f
  have hg₂ : g.hom₂ = Limits.Pi.map fun n : ℕ ↦ φ.app (op n) := by simp [g, he₂, hf₂]
  have hg₃ : g.hom₃ = Limits.Pi.map fun n : ℕ ↦ φ.app (op n) := by simp [g, he₃, hf₃]
  obtain ⟨b, hδ, hb, hc, hlim⟩ := exists_levelwise_milnor_maps φ hφ L
  obtain ⟨SG, hδ', hi, hp⟩ := hS G M tM g b (by simpa only [hg₂] using hlim)
  let c := cokernel.map (Rlim.delta (Rlim.Hom.shiftedHomSystem L F))
    (Rlim.delta (Rlim.Hom.shiftedHomSystem L G))
    (Rlim.Hom.shiftedHomProductMap L F G g.hom₂)
    (Rlim.Hom.shiftedHomProductMap L F G g.hom₃) hδ'
  have hc' : IsIso c := by simpa only [c, hg₂, hg₃] using hc
  let ψ : ShortComplex.mk S.inclusion S.projection S.zero ⟶
      ShortComplex.mk SG.inclusion SG.projection SG.zero :=
    ⟨c, H.map g.hom₁, b, hi, hp.symm⟩
  have : IsIso (H.map g.hom₁) :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' ψ S.shortExact SG.shortExact hc' hb
  have : IsIso (H.map f.hom₁) := by
    have : IsIso (H.map e.hom₁ ≫ H.map f.hom₁) := by
      simpa only [g, Pretriangulated.comp_hom₁, Functor.map_comp] using
        (inferInstance : IsIso (H.map g.hom₁))
    exact IsIso.of_isIso_comp_left (H.map e.hom₁) (H.map f.hom₁)
  exact ConcreteCategory.bijective_of_isIso (H.map f.hom₁)

/-- **Normalized product-difference triangle comparison.** If `φ : F ⟶ G` has eventual
inverses, then a derived limit of `F` with projections `p` is a derived limit of `G` with the
composite projections `p n ≫ φₙ`. The comparison of defining triangles uses the levelwise
product map of `φ` in both product slots, so no unnormalized cone lift is chosen. -/
public theorem IsDerivedLimitWithProjections.comp_of_hasEventualInverses
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] [HasProduct fun n : ℕ ↦ G.obj ⟨n⟩]
    (φ : F ⟶ G) (hφ : HasEventualInverses φ) {K : D} {p : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩}
    (hK : IsDerivedLimitWithProjections F K p) :
    IsDerivedLimitWithProjections G K (fun n ↦ p n ≫ φ.app ⟨n⟩) := by
  obtain ⟨δ, hδ⟩ := hK
  let tK : Rlim.Hom.DerivedLimitTriangle F K := ⟨Pi.lift p, δ, hδ⟩
  obtain ⟨M, i, δM, hM⟩ := exists_isDerivedLimit G
  let tM : Rlim.Hom.DerivedLimitTriangle G M := ⟨i, δM, hM⟩
  obtain ⟨f, hf₂, hf₃⟩ := Rlim.Pro.triangle_morphism tK.distinguished tM.distinguished
    (Limits.Pi.map fun n : ℕ ↦ φ.app (op n)) (Limits.Pi.map fun n : ℕ ↦ φ.app (op n))
    (productMap_delta φ)
  have : IsIso f.hom₁ := isIso_hom₁_of_hasEventualInverses φ hφ tK tM f hf₂ hf₃
  refine ⟨δM ≫ (inv f.hom₁)⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ tM.distinguished _ ?_
  refine Triangle.isoMk _ _ (asIso f.hom₁) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · have h₁ := f.comm₁
    rw [hf₂] at h₁
    dsimp [tK, tM] at h₁ ⊢
    rw [Category.comp_id, ← h₁]
    apply Pi.hom_ext
    intro n
    simp
  · dsimp
    simp only [Category.id_comp, Category.comp_id]
    rfl
  · dsimp
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

/-- **Transport along an isomorphism of towers.** A derived limit of `F` with projections `p` is
a derived limit of an isomorphic tower with the composite projections. An isomorphism has
eventual inverses at every level, so this is a special case of the normalized comparison and no
cone lift is chosen. -/
public theorem IsDerivedLimitWithProjections.ofNatIso
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] [HasProduct fun n : ℕ ↦ G.obj ⟨n⟩]
    (e : F ≅ G) {K : D} {p : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩}
    (hK : IsDerivedLimitWithProjections F K p) :
    IsDerivedLimitWithProjections G K (fun n ↦ p n ≫ e.hom.app ⟨n⟩) :=
  hK.comp_of_hasEventualInverses e.hom fun n ↦
    ⟨n, le_rfl, e.inv.app ⟨n⟩, by simp, by simp⟩

/-- **Reflecting a derived limit with specified projections along an exact equivalence.** If an
exact equivalence `U` sends the maps `p` to projections exhibiting `U.obj X` as a derived limit
of `F ⋙ U`, then `p` already exhibits `X` as a derived limit of `F`.

The projections are what makes this usable: the projection-free reflection has to choose a
preimage of the first map of the given triangle, and the choice is only determined up to an
automorphism of the limit, so nothing downstream can identify the resulting projections. Here
the first map of the reflected triangle is the product of the given `p` on the nose. -/
public theorem isDerivedLimitWithProjections_of_map_of_equivalence
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (U : C ⥤ D) [U.IsEquivalence] [U.CommShift ℤ] [U.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) U]
    (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (F ⋙ U).obj ⟨n⟩]
    (X : C) (p : ∀ n : ℕ, X ⟶ F.obj ⟨n⟩)
    (h : IsDerivedLimitWithProjections (F ⋙ U) (U.obj X) fun n ↦ U.map (p n)) :
    IsDerivedLimitWithProjections F X p := by
  let P := ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩
  let Q := ∏ᶜ fun n : ℕ ↦ (F ⋙ U).obj ⟨n⟩
  let pr (n : ℕ) : U.obj P ⟶ U.obj (F.obj ⟨n⟩) :=
    U.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n)
  have hp : IsLimit (Fan.mk (U.obj P) pr) :=
    Fan.isLimitMapConeEquiv U _ _ (isLimitOfPreserves U (productIsProduct _))
  have hq : IsLimit (Fan.mk Q (fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ (F ⋙ U).obj ⟨n⟩) n)) :=
    productIsProduct _
  let e : U.obj P ≅ Q := hp.conePointUniqueUpToIso hq
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = pr n :=
    hp.conePointUniqueUpToIso_hom_comp hq ⟨n⟩
  obtain ⟨δ, ha⟩ := h
  let dF : P ⟶ P := Pi.lift fun n : ℕ ↦
    Pi.π _ n - Pi.π _ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let dG : Q ⟶ Q := Pi.lift fun n : ℕ ↦
    Pi.π _ n - Pi.π _ (n + 1) ≫ (F ⋙ U).map (homOfLE (Nat.le_succ n)).op
  have hd : U.map dF ≫ e.hom = e.hom ≫ dG := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he n, Category.assoc, Pi.lift_π,
      Preadditive.comp_sub, he n, ← Category.assoc, he (n + 1)]
    dsimp only [pr, dF]
    rw [← U.map_comp, Pi.lift_π, U.map_sub, U.map_comp]
    rfl
  let a : U.obj X ⟶ Q := Pi.lift fun n : ℕ ↦ U.map (p n)
  have hf : U.map (Pi.lift p) ≫ e.hom = a := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he n]
    dsimp only [a]
    rw [Pi.lift_π]
    dsimp only [pr]
    rw [← U.map_comp, Pi.lift_π]
  let g : P ⟶ X⟦(1 : ℤ)⟧ := U.preimage
    (e.hom ≫ δ ≫ (U.commShiftIso (1 : ℤ)).inv.app X)
  have hg : e.hom ≫ δ = U.map g ≫ (U.commShiftIso (1 : ℤ)).hom.app X := by
    rw [U.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  refine ⟨g, ?_⟩
  apply (U.map_distinguished_iff (Triangle.mk (Pi.lift p) dF g)).1
  refine Pretriangulated.isomorphic_distinguished (Triangle.mk a dG δ) ha _
    (Triangle.isoMk _ _ (Iso.refl _) e e ?_ ?_ ?_)
  · show U.map (Pi.lift p) ≫ e.hom = 𝟙 _ ≫ _
    simpa using hf
  · show U.map dF ≫ e.hom = e.hom ≫ dG
    exact hd
  · show (U.map g ≫ (U.commShiftIso (1 : ℤ)).hom.app X) ≫
      (shiftFunctor D 1).map (𝟙 _) = e.hom ≫ δ
    simpa using hg.symm

/-- A family of maps `X m ⟶ X n` for `n ≤ m` that is the identity on the diagonal and is
compatible with the successor maps `f` is the action of `Functor.ofOpSequence f`. -/
public theorem ofOpSequence_map_eq {C : Type u} [Category.{v} C] {X : ℕ → C}
    (f : ∀ n, X (n + 1) ⟶ X n) (c : ∀ m n : ℕ, n ≤ m → (X m ⟶ X n))
    (hid : ∀ n, c n n le_rfl = 𝟙 _)
    (hsucc : ∀ m n (h : n ≤ m), c (m + 1) n (h.trans m.le_succ) = f m ≫ c m n h) :
    ∀ m n (h : n ≤ m), (Functor.ofOpSequence f).map (homOfLE h).op = c m n h := by
  have diag : ∀ (k n : ℕ) (h : n ≤ k), n = k →
      (Functor.ofOpSequence f).map (homOfLE h).op = c k n h := by
    rintro k n h rfl
    rw [show (homOfLE h).op = 𝟙 (op n) from rfl, CategoryTheory.Functor.map_id, hid]
    rfl
  intro m
  induction m with
  | zero => exact fun n h ↦ diag 0 n h (by omega)
  | succ m ih =>
    intro n h
    rcases Nat.lt_or_ge m n with hmn | hmn
    · exact diag _ n h (by omega)
    · rw [show (homOfLE h).op = (homOfLE m.le_succ).op ≫ (homOfLE hmn).op from rfl,
        Functor.map_comp, Functor.ofOpSequence_map_homOfLE_succ, ih n hmn, hsucc m n hmn]
      rfl

/-! ### Comparison of the Koszul tower with the ideal-power tower -/

section QuotientMaps

variable {R : Type u} [CommRing R]

/-- The canonical map between quotients of `R` by comparable ideals. -/
public noncomputable def quotientFactor {K K' : Ideal R} (h : K ≤ K') :
    ModuleCat.of R (R ⧸ K) ⟶ ModuleCat.of R (R ⧸ K') :=
  ModuleCat.ofHom (Ideal.Quotient.factorₐ R h).toLinearMap

/-- Two maps out of `R/K` agree once they agree after the quotient map `R → R/K`. -/
public theorem quotient_hom_ext {K : Ideal R} {M : ModuleCat.{u} R}
    {a b : ModuleCat.of R (R ⧸ K) ⟶ M}
    (hab : ModuleCat.ofHom K.mkQ ≫ a = ModuleCat.ofHom K.mkQ ≫ b) : a = b := by
  apply ModuleCat.hom_ext
  apply Submodule.linearMap_qext
  exact congrArg ModuleCat.Hom.hom hab

/-- The quotient map `R → R/K` followed by `quotientFactor` is the quotient map
`R → R/K'`. -/
public theorem mkQ_comp_quotientFactor {K K' : Ideal R} (h : K ≤ K') :
    ModuleCat.ofHom K.mkQ ≫ quotientFactor h = ModuleCat.ofHom K'.mkQ := by
  apply ModuleCat.hom_ext
  ext
  rfl

/-- The canonical maps between quotients compose. -/
public theorem quotientFactor_comp {K K' K'' : Ideal R} (h : K ≤ K') (h' : K' ≤ K'') :
    quotientFactor h ≫ quotientFactor h' = quotientFactor (h.trans h') := by
  apply quotient_hom_ext
  rw [reassoc_of% mkQ_comp_quotientFactor, mkQ_comp_quotientFactor, mkQ_comp_quotientFactor]

/-- The canonical map from `R/K` to itself is the identity. -/
public theorem quotientFactor_refl (K : Ideal R) : quotientFactor (le_refl K) = 𝟙 _ := by
  apply quotient_hom_ext
  rw [mkQ_comp_quotientFactor, Category.comp_id]

/-- The object `(R/K)[0]` of `D(R)`. -/
public noncomputable abbrev derivedQuotient (K : Ideal R) : DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q.obj (((ChainComplex.single₀ (ModuleCat.{u} R)).obj
    (ModuleCat.of R (R ⧸ K))).extend ComplexShape.embeddingDownNat)

/-- The map `(R/K)[0] ⟶ (R/K')[0]` in `D(R)` for `K ≤ K'`. -/
public noncomputable def derivedQuotientFactor {K K' : Ideal R} (h : K ≤ K') :
    derivedQuotient K ⟶ derivedQuotient K' :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap
    ((ChainComplex.single₀ (ModuleCat.{u} R)).map (quotientFactor h))
    ComplexShape.embeddingDownNat)

/-- The maps `derivedQuotientFactor` compose. -/
public theorem derivedQuotientFactor_comp {K K' K'' : Ideal R} (h : K ≤ K') (h' : K' ≤ K'') :
    derivedQuotientFactor h ≫ derivedQuotientFactor h' = derivedQuotientFactor (h.trans h') := by
  simp only [derivedQuotientFactor, ← Functor.map_comp, ← HomologicalComplex.extendMap_comp,
    quotientFactor_comp]

/-- The map `derivedQuotientFactor` from `(R/K)[0]` to itself is the identity. -/
public theorem derivedQuotientFactor_refl (K : Ideal R) :
    derivedQuotientFactor (le_refl K) = 𝟙 _ := by
  simp only [derivedQuotientFactor, quotientFactor_refl, CategoryTheory.Functor.map_id,
    HomologicalComplex.extendMap_id]

/-- The transition maps of `idealPowerQuotientSystem J` are the maps `derivedQuotientFactor`
between the quotients by the powers of `J`. -/
public theorem idealPowerQuotientSystem_map (J : Ideal R) {m n : ℕ} (h : n ≤ m) :
    (idealPowerQuotientSystem J).map (homOfLE h).op =
      derivedQuotientFactor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1) :
        J ^ (m + 1) ≤ J ^ (n + 1)) := by
  refine ofOpSequence_map_eq _ (fun m n h ↦ derivedQuotientFactor
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1) : J ^ (m + 1) ≤ J ^ (n + 1)))
    (fun n ↦ derivedQuotientFactor_refl _) ?_ m n h
  intro m n h
  exact (derivedQuotientFactor_comp _ _).symm

/-- The ideals generated by the `(n+1)`-st powers of the elements `g i` decrease with `n`. -/
public theorem powerSpan_antitone {r : ℕ} (g : Fin r → R) {m n : ℕ} (h : n ≤ m) :
    Ideal.span (Set.range fun i ↦ g i ^ (m + 1)) ≤
      Ideal.span (Set.range fun i ↦ g i ^ (n + 1)) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  show g i ^ (m + 1) ∈ _
  rw [show m + 1 = (m - n) + (n + 1) by omega, pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The transition maps of the tower of quotients by the powers of the generators are the
canonical maps between quotients. -/
public theorem quotientPowerTransition_eq {r : ℕ} (g : Fin r → R) {m n : ℕ} (h : n ≤ m) :
    NoetherianKoszulProIso.quotientPowerTransition g m n h =
      quotientFactor (powerSpan_antitone g h) := by
  apply quotient_hom_ext
  rw [NoetherianKoszulProIso.quotientPowerTransition_comp_mkQ, mkQ_comp_quotientFactor]

/-- The transition maps of `NoetherianKoszulProIso.quotientPowerSystem g` are the maps
`derivedQuotientFactor`. -/
public theorem quotientPowerSystem_map {r : ℕ} (g : Fin r → R) {m n : ℕ} (h : n ≤ m) :
    (NoetherianKoszulProIso.quotientPowerSystem g).map (homOfLE h).op =
      derivedQuotientFactor (powerSpan_antitone g h) := by
  refine ofOpSequence_map_eq _ (fun m n h ↦ derivedQuotientFactor (powerSpan_antitone g h))
    (fun n ↦ derivedQuotientFactor_refl _) ?_ m n h
  intro m n h
  rw [quotientPowerTransition_eq]
  exact (derivedQuotientFactor_comp (powerSpan_antitone g m.le_succ) _).symm

private theorem generatorPowers_le_idealPower
    {A : Type*} [CommRing A] {size : ℕ} (generators : Fin size → A) (level : ℕ) :
    Ideal.span (Set.range (fun index ↦ generators index ^ (level + 1))) ≤
      (Ideal.span (Set.range generators)) ^ (level + 1) := by
  apply Ideal.span_le.mpr
  rintro element ⟨index, rfl⟩
  have member : generators index ∈ Ideal.span (Set.range generators) :=
    Ideal.subset_span ⟨index, rfl⟩
  exact Ideal.pow_mem_pow member (level + 1)

private theorem exists_later_idealPower_le_generatorPowers
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {size : ℕ} (generators : Fin size → A) (level : ℕ) :
    ∃ later : ℕ, level ≤ later ∧
      (Ideal.span (Set.range generators)) ^ (later + 1) ≤
        Ideal.span (Set.range (fun index ↦ generators index ^ (level + 1))) := by
  have radicalBound : Ideal.span (Set.range generators) ≤
      (Ideal.span (Set.range (fun index ↦ generators index ^ (level + 1)))).radical :=
    Ideal.span_le.mpr <| by
      rintro _ ⟨index, rfl⟩
      exact ⟨level + 1, Ideal.subset_span ⟨index, rfl⟩⟩
  obtain ⟨exponent, bound⟩ := Ideal.exists_pow_le_of_le_radical_of_fg radicalBound
    (Ideal.span (Set.range generators)).fg_of_isNoetherianRing
  refine ⟨max exponent level, Nat.le_max_right _ _, ?_⟩
  exact (Ideal.pow_le_pow_right (by omega : exponent ≤ max exponent level + 1)).trans bound

/-- The ideal generated by the `(n+1)`-st powers of the generators `g i` of `J` lies in
`J^(n+1)`. -/
public theorem powerSpan_le_idealPower {r : ℕ} (g : Fin r → R) {J : Ideal R}
    (hJ : J = Ideal.span (Set.range g)) (n : ℕ) :
    Ideal.span (Set.range fun i ↦ g i ^ (n + 1)) ≤ J ^ (n + 1) :=
  hJ ▸ generatorPowers_le_idealPower g n

/-- The canonical comparison from the quotients by the ideals generated by powers of the
generators to the quotients by the powers of the ideal they generate. -/
public noncomputable def quotientIdealPowerComparison {r : ℕ} (g : Fin r → R) (J : Ideal R)
    (hJ : J = Ideal.span (Set.range g)) :
    NoetherianKoszulProIso.quotientPowerSystem g ⟶ idealPowerQuotientSystem J :=
  NatTrans.ofOpSequence (fun n ↦ derivedQuotientFactor (powerSpan_le_idealPower g hJ n))
    (fun n ↦ by
      rw [quotientPowerSystem_map, idealPowerQuotientSystem_map]
      exact (derivedQuotientFactor_comp _ _).trans (derivedQuotientFactor_comp _ _).symm)

private theorem quotientIdealPowerComparison_hasEventualInverses [IsNoetherianRing R]
    {r : ℕ} (g : Fin r → R) (J : Ideal R) (hJ : J = Ideal.span (Set.range g)) :
    HasEventualInverses (quotientIdealPowerComparison g J hJ) := by
  intro n
  obtain ⟨m, h, hm⟩ := exists_later_idealPower_le_generatorPowers g n
  refine ⟨m, h, derivedQuotientFactor (hJ ▸ hm), ?_, ?_⟩
  · rw [quotientPowerSystem_map]
    exact derivedQuotientFactor_comp _ _
  · rw [idealPowerQuotientSystem_map]
    exact derivedQuotientFactor_comp _ _

/-- The canonical comparison from the specified Koszul-power tower of `g` to the ideal-power
quotient tower of `J = (g)`: the Koszul augmentation of Stacks 0921 followed by the quotient
maps. It is natural for the pinned 0BKC transitions. -/
public noncomputable def koszulIdealPowerComparison {r : ℕ} (g : Fin r → R) (J : Ideal R)
    (hJ : J = Ideal.span (Set.range g)) :
    NoetherianKoszulProIso.koszulPowerSystem g ⟶ idealPowerQuotientSystem J :=
  NoetherianKoszulProIso.koszulQuotientComparison g ≫ quotientIdealPowerComparison g J hJ

/-- Over a Noetherian ring, the comparison from the Koszul-power tower of `g` to the ideal-power
quotient tower of `J = (g)` has eventual inverses. -/
public theorem koszulIdealPowerComparison_hasEventualInverses [IsNoetherianRing R]
    {r : ℕ} (g : Fin r → R) (J : Ideal R) (hJ : J = Ideal.span (Set.range g)) :
    HasEventualInverses (koszulIdealPowerComparison g J hJ) :=
  HasEventualInverses.comp
    (NoetherianKoszulProIso.koszulPowerSystem_proIso_quotientPowerSystem g)
    (quotientIdealPowerComparison_hasEventualInverses g J hJ)

/-- **The pro-isomorphism of [Stacks, Tag 0H3D] at a general ideal, over a Noetherian ring.**
The tower of Koszul complexes on the positive powers of a finite generating sequence `g` of `J`
and the tower of quotients by the positive powers of `J` are pro-isomorphic in `D(R)`, in the
explicit up-to-refinement form in which [Stacks, Tag 0H3D] is stated.

For `r = 1` the Koszul tower is the tower of two-term complexes `R --g₀^(n+1)--> R` and the
quotient tower is `R/(g₀^(n+1))`, so this is [Stacks, Tag 0H3D] for multiplication by `g₀` on
`R`. At a general ideal no stabilization of power torsion is assumed, and none would suffice:
the pro-vanishing that has to be proved is of the Koszul homologies in all the degrees
`-r, …, -1`, not of a torsion submodule of `R`, and what supplies it is the Noetherian
hypothesis through the Artin--Rees lemma inside
`NoetherianKoszulProIso.koszulPowerSystem_proIso_quotientPowerSystem`. -/
public theorem nonempty_proIso_koszulPowerSystem_idealPowerQuotientSystem [IsNoetherianRing R]
    {r : ℕ} (g : Fin r → R) (J : Ideal R) (hJ : J = Ideal.span (Set.range g)) :
    Nonempty (InverseSequence.ProIso (NoetherianKoszulProIso.koszulPowerSystem g)
      (idealPowerQuotientSystem J)) :=
  ⟨proIsoOfHasEventualInverses _ (koszulIdealPowerComparison_hasEventualInverses g J hJ)⟩

/-- **The general-ideal pro-isomorphism is carried along every functor out of `D(R)`.** A
pro-isomorphism is a finite diagram of morphisms and equations, so any functor transports it;
this is the form in which a consumer sitting over `D(R)` — derived tensoring with a complex, or
derived sections — receives the comparison of the two towers.

What this does *not* give is the general-ideal pro-isomorphism for a module or a sheaf against
its honest quotient tower: `L` carries the quotient tower of `R` to the *derived* reductions
`L(R/J^(n+1))`, and replacing those by the honest reductions is the separate Tor step, which
over a Noetherian ring is [Stacks, Tag 0G9M]
(`Stacks.AdicSystem.DerivedReductionProIso.derivedReduction_proIsomorphic_adicReduction`) for a
bounded complex of finite modules. -/
public theorem nonempty_proIso_koszulPowerSystem_idealPowerQuotientSystem_comp
    [IsNoetherianRing R] {r : ℕ} (g : Fin r → R) (J : Ideal R)
    (hJ : J = Ideal.span (Set.range g)) {E : Type w} [Category E]
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ E) :
    Nonempty (InverseSequence.ProIso (NoetherianKoszulProIso.koszulPowerSystem g ⋙ L)
      (idealPowerQuotientSystem J ⋙ L)) :=
  ⟨proIsoOfHasEventualInverses _
    ((koszulIdealPowerComparison_hasEventualInverses g J hJ).whiskerRight L)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The pinned unit of Stacks 091Z followed by the Koszul augmentation is the quotient map
`R ⟶ R/(gᵢ^(n+1))`, in degree zero. -/
private theorem koszulPowerUnitChain_comp_augmentation {r : ℕ} (g : Fin r → R) (n : ℕ) :
    (AdicKoszul.koszulPowerUnitChain g n).f 0 ≫
        (Koszul.koszulAugmentation (fun i ↦ g i ^ (n + 1))).f 0 =
      ModuleCat.ofHom (Ideal.span (Set.range fun i ↦ g i ^ (n + 1))).mkQ := by
  have hchain : ∀ (m : ℕ) (a : R), (AdicKoszul.koszulPowerUnitChain g m).f 0 a =
      a • ⟨ExteriorAlgebra.ιMulti R 0 (fun i ↦ Fin.elim0 i),
        Koszul.ιMulti_mem 0 (fun i ↦ Fin.elim0 i)⟩ := by
    intro m a
    unfold AdicKoszul.koszulPowerUnitChain
    rcases Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec (_root_.koszulPowerComplexes_form_inverseSystem g)))) with
      ⟨hid, hcomp, hsid, hscomp, hformula, hη, hητ, hσ, he, hlast⟩
    exact hη m a
  rw [Koszul.koszulAugmentation_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  show (Ideal.span (Set.range fun i ↦ g i ^ (n + 1))).mkQ
      (exteriorPower.zeroEquiv R (Fin r → R)
        ((AdicKoszul.koszulPowerUnitChain g n).f 0 a)) = _
  rw [hchain, map_smul]
  have hg : exteriorPower.zeroEquiv R (Fin r → R)
      ⟨ExteriorAlgebra.ιMulti R 0 (fun i ↦ Fin.elim0 i),
        Koszul.ιMulti_mem 0 (fun i ↦ Fin.elim0 i)⟩ = 1 := by
    apply Koszul.zeroEquiv_eq_of_coe
    simp [ExteriorAlgebra.ιMulti]
  rw [hg, smul_eq_mul, mul_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The pinned 091Z unit `R[0] ⟶ Kₙ` followed by the Koszul/ideal-power comparison is the
canonical quotient map `R[0] ⟶ (R/J^(n+1))[0]`. -/
public theorem koszulPowerUnit_comp_koszulIdealPowerComparison {r : ℕ} (g : Fin r → R)
    (J : Ideal R) (hJ : J = Ideal.span (Set.range g)) (n : ℕ) :
    DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit g n) ≫
        (koszulIdealPowerComparison g J hJ).app (op n) =
      idealPowerQuotientMap J n := by
  simp only [koszulIdealPowerComparison, NatTrans.comp_app, quotientIdealPowerComparison,
    NatTrans.ofOpSequence_app, NoetherianKoszulProIso.koszulQuotientComparison_app,
    derivedQuotientFactor, idealPowerQuotientMap]
  rw [← Functor.map_comp, ← Functor.map_comp]
  show _ = DerivedCategory.Q.map ((HomologicalComplex.single _ _ 0).map _) ≫ _
  rw [← Functor.map_comp]
  congr 1
  apply HomologicalComplex.from_single_hom_ext
  have hq := koszulPowerUnitChain_comp_augmentation g n
  have hf := mkQ_comp_quotientFactor (powerSpan_le_idealPower g hJ n)
  simp only [HomologicalComplex.comp_f, AdicKoszul.koszulPowerUnit,
    HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl),
    HomologicalComplex.extendSingleIso_inv_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]
  have hself (X : ModuleCat.{u} R) :
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X).hom = 𝟙 _ := rfl
  rw [hself, Category.id_comp, reassoc_of% hq, reassoc_of% hf]

end QuotientMaps

/-- The ideal of `ULift A` corresponding to `I` is generated by the lifted generators. -/
public theorem comap_uliftRingEquiv_eq_span {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (I : Ideal A) (hf : Ideal.span (Set.range f) = I) :
    I.comap (ULift.ringEquiv.{u, v} (R := A)).toRingHom =
      Ideal.span (Set.range fun i ↦ (ULift.up (f i) : ULift.{v} A)) := by
  subst hf
  show Ideal.comap (ULift.ringEquiv.{u, v} (R := A)).symm.symm _ = _
  rw [← Ideal.map_comap_of_equiv, Ideal.map_span, ← Set.range_comp]
  rfl

/-- **Cone comparison for Stacks 0922.** Let `C` be a Koszul completion of Stacks 091Z for
generators `f` of `I`. Composing its natural projections with the canonical comparison from
the pinned Koszul-power tower to the ideal-power quotient tower gives natural projections
exhibiting the same object as the derived limit of `K ⊗ᴸ A/Iⁿ⁺¹`, and the unit of `C`
followed by these projections is the canonical reduction map at every level. -/
public theorem koszulPowerCompletion_idealPowerCone
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {r : ℕ} (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A))
    (C : AdicKoszul.KoszulPowerCompletion f T) :
    let U := AdicKoszul.derivedUniverseLift.{u, v} A
    let J := I.comap ULift.ringEquiv.toRingHom
    ∃ π : ∀ n : ℕ, C.functor ⋙ U ⟶ U ⋙ T.tensor.flip.obj ((idealPowerQuotientSystem J).obj ⟨n⟩),
      (∀ n, π n = C.projection n ≫ Functor.whiskerLeft U (T.tensor.flip.map
        ((koszulIdealPowerComparison (fun i ↦ (ULift.up (f i) : ULift.{v} A)) J
          (comap_uliftRingEquiv_eq_span f I hf)).app ⟨n⟩))) ∧
      (∀ K, IsDerivedLimitWithProjections
        (idealPowerQuotientSystem J ⋙ T.tensor.obj (U.obj K))
        (U.obj (C.functor.obj K)) (fun n ↦ (π n).app K)) ∧
      ∀ K n, U.map (C.unit.app K) ≫ (π n).app K = (derivedReductionMap J T n).app (U.obj K) := by
  intro U J
  let g : Fin r → ULift.{v} A := fun i ↦ ULift.up (f i)
  have hJ : J = Ideal.span (Set.range g) := comap_uliftRingEquiv_eq_span f I hf
  let φ := koszulIdealPowerComparison g J hJ
  refine ⟨fun n ↦ C.projection n ≫ Functor.whiskerLeft U (T.tensor.flip.map (φ.app ⟨n⟩)),
    fun n ↦ rfl, ?_, ?_⟩
  · intro K
    obtain ⟨δ, hδ⟩ := C.milnor K
    have hK : IsDerivedLimitWithProjections (AdicKoszul.tensorKoszulPowerSystem f T K)
        (U.obj (C.functor.obj K)) (fun n ↦ (C.projection n).app K) := ⟨δ, hδ⟩
    exact hK.comp_of_hasEventualInverses
      (Functor.whiskerRight φ (T.tensor.obj (U.obj K)))
      ((koszulIdealPowerComparison_hasEventualInverses g J hJ).whiskerRight _)
  · intro K n
    show U.map (C.unit.app K) ≫ (C.projection n).app K ≫
        (T.tensor.obj (U.obj K)).map (φ.app ⟨n⟩) = _
    rw [reassoc_of% C.unit_projection K n]
    simp only [AdicKoszul.derivedTensorKoszulPowerUnit, derivedReductionMap, Category.assoc,
      NatTrans.comp_app, Functor.flip_map_app]
    congr 1
    exact ((T.tensor.obj (U.obj K)).map_comp _ _).symm.trans
      (congrArg (T.tensor.obj (U.obj K)).map
        (koszulPowerUnit_comp_koszulIdealPowerComparison g J hJ n))

/-- The unit of a derived-completion reflection is an isomorphism on every derived-complete
object, in particular on a derived-complete module concentrated in degree zero. -/
public theorem isIso_unit_app_of_isDerivedComplete
    (A : Type u) [CommRing A] (I : Ideal A) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun K ↦ IsDerivedComplete I K
    ∀ (L : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory)
      (adj : L ⊣ P.ι) (K : DerivedCategory (ModuleCat.{v} A)),
      IsDerivedComplete I K → IsIso (adj.unit.app K) := by
  intro P L adj K hK
  exact adj.isIso_unit_app_of_iso (X := ⟨K, hK⟩) (Iso.refl K)

end NoetherianAdicCompletion

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace NoetherianAdicCompletion

attribute [local instance] HasDerivedCategory.standard

/-- Over a Noetherian ring, derived completion is the derived limit of the quotient-power
tower, with its canonical projections and reduction maps. -/
public theorem idealPowerDerivedLimitSolution
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun K ↦ IsDerivedComplete I K
    let U := AdicKoszul.derivedUniverseLift.{u, v} A
    let J := I.comap ULift.ringEquiv.toRingHom
    ∃ L : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory,
      ∃ adj : L ⊣ P.ι,
        ∃ π : ∀ n : ℕ, (L ⋙ P.ι) ⋙ U ⟶
            U ⋙ T.tensor.flip.obj ((idealPowerQuotientSystem J).obj ⟨n⟩),
          (∀ K : DerivedCategory (ModuleCat.{v} A), IsDerivedLimitWithProjections
            (idealPowerQuotientSystem J ⋙ T.tensor.obj (U.obj K))
            (U.obj ((L ⋙ P.ι).obj K)) (fun n ↦ (π n).app K)) ∧
          ∀ (K : DerivedCategory (ModuleCat.{v} A)) (n : ℕ),
            U.map (adj.unit.app K) ≫ (π n).app K =
              (derivedReductionMap J T n).app (U.obj K) := by
  dsimp
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  have hf' : Ideal.span (Set.range f) = I := hf
  set C := KoszulCompletion.completionData f T with hC
  have complete : ∀ K, IsDerivedComplete I (C.functor.obj K) := by
    intro K
    rw [← hf']
    exact _root_.koszulPowerCompletion_complete A f T C K
  have isIso_unit : ∀ K, IsDerivedComplete I K → IsIso (C.unit.app K) := by
    intro K hK
    rw [← hf'] at hK
    exact (_root_.canonicalCompletion_criterion f T K).mp hK
  have isIso_map_unit : ∀ K, IsIso (C.functor.map (C.unit.app K)) := by
    intro K
    exact _root_.canonicalCompletion_map_unit_isIso f T K
  set P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
    fun K ↦ IsDerivedComplete I K with hP
  -- the reflection attached to the completion functor and its unit
  have hbij : ∀ (X : DerivedCategory (ModuleCat.{v} A)) (Y : P.FullSubcategory),
      Function.Bijective
        (fun m : C.functor.obj X ⟶ Y.obj ↦ C.unit.app X ≫ m) := by
    intro X Y
    have := isIso_unit Y.obj Y.property
    have := isIso_map_unit X
    have nat {X' : DerivedCategory (ModuleCat.{v} A)} (m : X' ⟶ Y.obj) :
        m ≫ C.unit.app Y.obj = C.unit.app X' ≫ C.functor.map m := by
      simpa using C.unit.naturality m
    constructor
    · intro a b hab
      have hmap : C.functor.map a = C.functor.map b := by
        apply (cancel_epi (C.functor.map (C.unit.app X))).1
        simpa only [Functor.map_comp] using congrArg C.functor.map hab
      apply (cancel_mono (C.unit.app Y.obj)).1
      rw [nat a, nat b, hmap]
    · intro m
      refine ⟨C.functor.map m ≫ inv (C.unit.app Y.obj), ?_⟩
      show C.unit.app X ≫ (C.functor.map m ≫ inv (C.unit.app Y.obj)) = m
      rw [← Category.assoc, show C.unit.app X ≫ C.functor.map m = m ≫ C.unit.app Y.obj from
        (nat m).symm]
      simp
  set L : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory :=
    P.lift C.functor complete with hL
  set homEquiv : ∀ (X : DerivedCategory (ModuleCat.{v} A)) (Y : P.FullSubcategory),
      (L.obj X ⟶ Y) ≃ (X ⟶ P.ι.obj Y) := fun X Y =>
    (ObjectProperty.fullyFaithfulι P).homEquiv.trans
      (Equiv.ofBijective _ (hbij X Y)) with hhomEquiv
  have homEquiv_apply : ∀ (X : DerivedCategory (ModuleCat.{v} A)) (Y : P.FullSubcategory)
      (a : L.obj X ⟶ Y), homEquiv X Y a = C.unit.app X ≫ a.hom := fun _ _ _ => rfl
  set adj : L ⊣ P.ι := Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro X' X Y a b
        rw [Equiv.symm_apply_eq]
        conv_lhs => rw [← (homEquiv X Y).apply_symm_apply b]
        simp only [homEquiv_apply]
        rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, ← Category.assoc]
        congr 1
        exact C.unit.naturality a
      homEquiv_naturality_right := by
        intro X Y Y' a b
        rw [homEquiv_apply, homEquiv_apply]
        simp } with hadj
  obtain ⟨π, hπ, hlim, hunit⟩ :=
    koszulPowerCompletion_idealPowerCone A I f hf' T C
  refine ⟨L, adj, π, hlim, fun K n ↦ ?_⟩
  have hunitEq : adj.unit.app K = C.unit.app K :=
    (homEquiv_apply K (L.obj K) (𝟙 (L.obj K))).trans (Category.comp_id _)
  rw [hunitEq]
  exact hunit K n

end NoetherianAdicCompletion

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace NoetherianAdicCompletion

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0922.** Over a Noetherian ring, derived completion is left adjoint to the
inclusion of derived-complete objects and is computed by `R lim (K ⊗ᴸ[A] A/Iⁿ)`.
The adjunction unit induces the canonical reduction map at every level of the tower.
The projections are natural in `K` and are the actual projections of the derived limit.

The reflector acts on `ModuleCat.{v} A` for an independent module universe `v`. In the
tensor formula only, the exact functor `U` lifts to modules over `ULift.{v} A`; `J` is the
same ideal transported along `ULift.ringEquiv`. -/
@[stacks 0922]
public theorem idealPowerDerivedLimit_isLeftAdjoint
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun K ↦ IsDerivedComplete I K
    let U := AdicKoszul.derivedUniverseLift.{u, v} A
    let J := I.comap ULift.ringEquiv.toRingHom
    ∃ L : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory,
      ∃ adj : L ⊣ P.ι,
        ∃ π : ∀ n : ℕ, (L ⋙ P.ι) ⋙ U ⟶
            U ⋙ T.tensor.flip.obj ((idealPowerQuotientSystem J).obj ⟨n⟩),
          (∀ K, IsDerivedLimitWithProjections
            (idealPowerQuotientSystem J ⋙ T.tensor.obj (U.obj K))
            (U.obj ((L ⋙ P.ι).obj K)) (fun n ↦ (π n).app K)) ∧
          ∀ K n, U.map (adj.unit.app K) ≫ (π n).app K =
            (derivedReductionMap J T n).app (U.obj K) :=
  idealPowerDerivedLimitSolution A I T

end NoetherianAdicCompletion

end
