module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PrincipalDivisor
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition

/-!
# Purity classes along flags of principal smooth divisors

A *purity class* of degree `c` for an exact functor `P : Mod(T) ⥤ Mod(X)` of étale sheaves of
`Λ = ℤ/ℓ`-modules is a class `γ ∈ Ext^c_X(P Λ_T, Λ_X)` such that `y ↦ P(y) ∘ γ` is a bijection
`Ext^q_T(G, Λ_T) ≅ Ext^{q+c}_X(P G, Λ_X)` for all `G` and `q`, and `Ext^q_X(P G, Λ_X) = 0` for
`q < c`. For `P = i_*` along a closed immersion this is cohomological purity, `Ri^! Λ ≅ Λ[-c]`.

Purity classes compose (`IsPurityClassFun.comp`): if `γ` is one for `P` and `δ` one for `Q`,
then `Q(γ) ∘ δ` is one for `P ⋙ Q`. This is the transitivity of Gysin classes. Along a flag
`T = T_c ⊆ ⋯ ⊆ T_0 = X` of principal smooth divisors the iterated composite of the classes of
`Stacks.EtaleCohomology.Purity.exists_ext_purity_principalDivisor` is therefore a purity class of
degree `2c` for the closed immersion `T ⟶ X` (`exists_purityClass_of_isPrincipalFlag`).

## Main definitions

* `Stacks.EtaleCohomology.Purity.IsPurityClassFun`.
* `Stacks.EtaleCohomology.Purity.IsPrincipalFlag`.

## Main results

* `Stacks.EtaleCohomology.Purity.IsPurityClassFun.comp`: transitivity.
* `Stacks.EtaleCohomology.Purity.exists_purityClass_of_isPrincipalFlag`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology.Purity

variable (ℓ : ℕ)

/-- **A purity class of degree `c`** for an exact functor `P` of étale sheaves of `ℤ/ℓ`-modules:
`y ↦ P(y) ∘ γ` is bijective in every degree and `Ext^q(P G, A) = 0` below `c`. -/
def IsPurityClassFun {T X : Scheme.{u}} (P : EtaleModules.{u, 0} (ZMod ℓ) T ⥤
    EtaleModules.{u, 0} (ZMod ℓ) X) [P.Additive] [PreservesFiniteLimits P]
    [PreservesFiniteColimits P] (A : EtaleModules.{u, 0} (ZMod ℓ) X) {c : ℕ}
    (γ : Ext (P.obj (unitSheaf (X := T) ℓ)) A c) : Prop :=
  (∀ (G : EtaleModules.{u, 0} (ZMod ℓ) T) (q q' : ℕ) (h : q + c = q'), Function.Bijective
    (fun y : Ext G (unitSheaf (X := T) ℓ) q => (y.mapExactFunctor P).comp γ h)) ∧
  (∀ (G : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ), q < c → Subsingleton (Ext (P.obj G) A q))

variable {ℓ}

/-- A purity class in the `rfl`-normalized form is a purity class. -/
theorem isPurityClassFun_of_rfl {T X : Scheme.{u}} (P : EtaleModules.{u, 0} (ZMod ℓ) T ⥤
    EtaleModules.{u, 0} (ZMod ℓ) X) [P.Additive] [PreservesFiniteLimits P]
    [PreservesFiniteColimits P] (A : EtaleModules.{u, 0} (ZMod ℓ) X) {c : ℕ}
    (γ : Ext (P.obj (unitSheaf (X := T) ℓ)) A c)
    (h₁ : ∀ (G : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ), Function.Bijective
      (fun y : Ext G (unitSheaf (X := T) ℓ) q => (y.mapExactFunctor P).comp γ
        (show q + c = q + c from rfl)))
    (h₂ : ∀ (G : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ), q < c →
      Subsingleton (Ext (P.obj G) A q)) : IsPurityClassFun ℓ P A γ :=
  ⟨fun G q q' h => by subst h; exact h₁ G q, h₂⟩

/-- **Transitivity of purity classes**: if `γ` is a purity class of degree `n` for `P` and `δ` one
of degree `m` for `Q`, then `Q(γ) ∘ δ` is a purity class of degree `n + m` for `P ⋙ Q`. -/
theorem IsPurityClassFun.comp {T Y X : Scheme.{u}}
    {P : EtaleModules.{u, 0} (ZMod ℓ) T ⥤ EtaleModules.{u, 0} (ZMod ℓ) Y} [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {Q : EtaleModules.{u, 0} (ZMod ℓ) Y ⥤ EtaleModules.{u, 0} (ZMod ℓ) X} [Q.Additive]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q] {n m : ℕ}
    {γ : Ext (P.obj (unitSheaf (X := T) ℓ)) (unitSheaf (X := Y) ℓ) n}
    {δ : Ext (Q.obj (unitSheaf (X := Y) ℓ)) (unitSheaf (X := X) ℓ) m}
    (hγ : IsPurityClassFun ℓ P (unitSheaf (X := Y) ℓ) γ)
    (hδ : IsPurityClassFun ℓ Q (unitSheaf (X := X) ℓ) δ) :
    IsPurityClassFun ℓ (P ⋙ Q) (unitSheaf (X := X) ℓ)
      ((γ.mapExactFunctor Q).comp δ (rfl : n + m = n + m)) := by
  refine ⟨fun G q q' h => ?_, fun G q hq => ?_⟩
  · have e : (fun y : Ext G (unitSheaf (X := T) ℓ) q =>
        (y.mapExactFunctor (P ⋙ Q)).comp ((γ.mapExactFunctor Q).comp δ rfl) h) =
        (fun z : Ext (P.obj G) (unitSheaf (X := Y) ℓ) (q + n) =>
          (z.mapExactFunctor Q).comp δ (by omega : q + n + m = q')) ∘
        (fun y : Ext G (unitSheaf (X := T) ℓ) q => (y.mapExactFunctor P).comp γ rfl) := by
      funext y
      simp only [Function.comp_apply]
      rw [← Stacks.ExtFunctorial.mapExactFunctor_comp_functor P Q G q y, Ext.mapExactFunctor_comp,
        Ext.comp_assoc _ _ _ rfl rfl (by omega)]
    rw [e]
    exact (hδ.1 (P.obj G) (q + n) q' (by omega)).comp (hγ.1 G q (q + n) rfl)
  · by_cases hqm : q < m
    · exact hδ.2 (P.obj G) q hqm
    · obtain ⟨q₀, rfl⟩ : ∃ q₀, q = q₀ + m := ⟨q - m, by omega⟩
      have := hγ.2 G q₀ (by omega)
      exact (hδ.1 (P.obj G) q₀ (q₀ + m) rfl).2.subsingleton

/-- Yoneda product with an isomorphism in degree zero, on the left, is bijective. -/
theorem bijective_mk₀_comp_iso {C : Type*} [Category C] [Abelian C] [HasExt.{u + 1} C]
    {A A' B : C} (e : A ≅ A') (n : ℕ) :
    Function.Bijective (fun z : Ext A' B n => (Ext.mk₀ e.hom).comp z (zero_add n)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun z => (Ext.mk₀ e.inv).comp z (zero_add n),
    fun z => ?_, fun z => ?_⟩
  · show (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp z (zero_add n)) (zero_add n) = z
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  · show (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp z (zero_add n)) (zero_add n) = z
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]

/-- **Purity classes transport along an isomorphism of functors**, by composition with the
isomorphism at `Λ_T`. -/
theorem IsPurityClassFun.ofIso {T X : Scheme.{u}}
    {P P' : EtaleModules.{u, 0} (ZMod ℓ) T ⥤ EtaleModules.{u, 0} (ZMod ℓ) X} [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] [P'.Additive]
    [PreservesFiniteLimits P'] [PreservesFiniteColimits P'] (e : P ≅ P') {c : ℕ}
    {γ : Ext (P.obj (unitSheaf (X := T) ℓ)) (unitSheaf (X := X) ℓ) c}
    (hγ : IsPurityClassFun ℓ P (unitSheaf (X := X) ℓ) γ) :
    IsPurityClassFun ℓ P' (unitSheaf (X := X) ℓ)
      ((Ext.mk₀ (e.inv.app (unitSheaf (X := T) ℓ))).comp γ (zero_add c)) := by
  refine ⟨fun G q q' h => ?_, fun G q hq => ?_⟩
  · subst h
    have hfun : (fun y : Ext G (unitSheaf (X := T) ℓ) q =>
        (y.mapExactFunctor P').comp ((Ext.mk₀ (e.inv.app (unitSheaf (X := T) ℓ))).comp γ
          (zero_add c)) rfl) =
        (fun z => (Ext.mk₀ (e.inv.app G)).comp z (zero_add (q + c))) ∘
        (fun y : Ext G (unitSheaf (X := T) ℓ) q => (y.mapExactFunctor P).comp γ rfl) := by
      funext y
      simp only [Function.comp_apply]
      rw [← Ext.comp_assoc _ _ _ rfl (zero_add c) rfl,
        ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor e.inv G q y,
        Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega)]
    rw [hfun]
    exact (bijective_mk₀_comp_iso (asIso (e.inv.app G)) (q + c)).comp (hγ.1 G q (q + c) rfl)
  · have := hγ.2 G q hq
    exact (bijective_mk₀_comp_iso (asIso (e.hom.app G)) q).1.subsingleton

variable (k : Type u) [Field k]

/-- **A flag of principal smooth divisors** `T = T_c ⊆ ⋯ ⊆ T_0 = X` of length `c ≥ 1`: each step
`T_{a+1} ⟶ T_a` is the fibre over the origin of a smooth morphism `T_a ⟶ 𝐀¹_k`. -/
inductive IsPrincipalFlag : {T X : Scheme.{u}} → (T ⟶ X) → ℕ → Prop
  | single {T X : Scheme.{u}} (i : T ⟶ X) (φ : X ⟶ affineLine k) (ψ : T ⟶ Spec (.of k))
      (hφ : Smooth φ) (hT : IsPullback i ψ φ (origin k)) : IsPrincipalFlag i 1
  | cons {T Y X : Scheme.{u}} (i' : T ⟶ Y) (i : Y ⟶ X) {c : ℕ} (h : IsPrincipalFlag i' c)
      (φ : X ⟶ affineLine k) (ψ : Y ⟶ Spec (.of k)) (hφ : Smooth φ)
      (hT : IsPullback i ψ φ (origin k)) : IsPrincipalFlag (i' ≫ i) (c + 1)

variable {k}

/-- The fibre over the origin of a morphism to `𝐀¹_k` is a closed immersion. -/
private theorem isClosedImmersion_of_isPullback_origin {T X : Scheme.{u}} {i : T ⟶ X}
    {φ : X ⟶ affineLine k} {ψ : T ⟶ Spec (.of k)} (hT : IsPullback i ψ φ (origin k)) :
    IsClosedImmersion i :=
  have := isClosedImmersion_origin k
  MorphismProperty.of_isPullback hT.flip inferInstance

/-- The composite of a flag of principal divisors is a closed immersion. -/
theorem IsPrincipalFlag.isClosedImmersion {T X : Scheme.{u}} {ι : T ⟶ X} {c : ℕ}
    (hf : IsPrincipalFlag k ι c) : IsClosedImmersion ι := by
  induction hf with
  | single i φ ψ hφ hT => exact isClosedImmersion_of_isPullback_origin hT
  | cons i' i h φ ψ hφ hT ih =>
    have := isClosedImmersion_of_isPullback_origin hT
    have := ih
    infer_instance

variable [IsAlgClosed k] (hℓ : IsUnit (ℓ : k))

include hℓ in
/-- **Purity along a flag of principal smooth divisors**: for `ι : T ⟶ X` the composite of a flag
of length `c`, there is a purity class of degree `2c` for `ι_*`, namely the iterated composite of
the classes of the divisors (transitivity of Gysin classes). -/
theorem exists_purityClass_of_isPrincipalFlag {T X : Scheme.{u}} {ι : T ⟶ X} {c : ℕ}
    (hf : IsPrincipalFlag k ι c) [IsClosedImmersion ι] :
    ∃ γ : Ext ((etaleModuleDirectImage (ZMod ℓ) ι).obj (unitSheaf (X := T) ℓ))
        (unitSheaf (X := X) ℓ) (2 * c),
      IsPurityClassFun ℓ (etaleModuleDirectImage (ZMod ℓ) ι) (unitSheaf (X := X) ℓ) γ := by
  revert ‹IsClosedImmersion ι›
  induction hf with
  | single i φ ψ hφ hT =>
    intro _
    obtain ⟨γ, h₁, h₂⟩ := exists_ext_purity_principalDivisor hℓ φ i ψ hT
    exact ⟨γ, isPurityClassFun_of_rfl _ _ γ h₁ h₂⟩
  | cons i' i h φ ψ hφ hT ih =>
    intro _
    have := isClosedImmersion_of_isPullback_origin hT
    have : IsClosedImmersion i' := h.isClosedImmersion
    obtain ⟨γ', hγ'⟩ := ih
    obtain ⟨δ, h₁, h₂⟩ := exists_ext_purity_principalDivisor hℓ φ i ψ hT
    have hδ := isPurityClassFun_of_rfl _ _ δ h₁ h₂
    exact ⟨_, (hγ'.comp hδ).ofIso
      (etaleModuleDirectImageComp (ZMod ℓ) i' i (i' ≫ i) rfl)⟩

end Stacks.EtaleCohomology.Purity

end
