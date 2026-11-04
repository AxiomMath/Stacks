module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedOfSplitting

/-!
# The Künneth map for the derived functor of an exact functor out of vector spaces

Let `k` be a field, let `T : Mod(k) ⥤ 𝓑` be an exact functor into an abelian category with
enough injectives and let `E : 𝓑 ⥤ Mod(k)` be additive. Write `Ξ = RE ∘ RT : D⁺(k) ⥤ D⁺(k)` and
`M_b = Rᵇ E(T k)`. For `K ∈ D⁺(k)` this file constructs the canonical `k`-linear map

`⨁_{a + b = n} Hᵃ(K) ⊗_k M_b ⟶ Hⁿ(Ξ K)`

and proves that it is an isomorphism when `K` has bounded cohomology, `T ⋙ Rᵇ E` commutes with
direct sums and `Rᵇ E ∘ T` is `k`-linear on scalars.

This is the algebraic core of the proof of [Stacks, Tag 0BEF]: there `K = RΓ(X, F)`,
`T(V) = G ⊗_k V` on `Y`, `E = Γ(Y, -)`, and `Ξ K = RΓ(Y, G ⊗_k RΓ(X, F))`; the steps "up to
homotopy `K` is the sum of its shifted cohomology modules" and "cohomology commutes with direct
sums" of the source are the two halves of the proof of `isIso_kunnethNatTrans_app` below.

## The map

A class `x ∈ Hᵃ(K)` is a morphism `x̂ : k[-a] ⟶ K` in `D⁺(k)`, the module `k` being projective
(`DerivedCategory.Plus.homologyFromSingleAddEquiv`). Applying `Ξ` gives `Ξ(k[-a]) ⟶ Ξ K`, and
`Hⁿ(Ξ(k[-a])) ≅ M_{n - a}` (`DerivedCategory.Plus.singleDerivedHomologyIso`). The map sends
`x ⊗ y` to `Hⁿ(Ξ x̂)(y)`. It involves no choice.

## Main definitions

* `Stacks.KunnethOverField.homologyClass`: the morphism `k[-a] ⟶ K` representing a class.
* `Stacks.KunnethOverField.kunnethPairing`: the bilinear pairing `Hᵃ(K) × M_b ⟶ Hⁿ(Ξ K)`.
* `Stacks.KunnethOverField.kunnethSource`: the functor `K ↦ ⨁_{a + b = n} Hᵃ(K) ⊗_k M_b`.
* `Stacks.KunnethOverField.kunnethNatTrans`: **the Künneth map**, natural in `K`.

## Main results

* `Stacks.KunnethOverField.isIso_kunnethNatTrans_app`: the Künneth map is an isomorphism at
  every `K` with bounded cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped DirectSum TensorProduct

universe u v w

attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

namespace Stacks.KunnethOverField

/-! ### Natural transformations, biproducts and coproducts

The three criteria below are private copies of
`Stacks.AffineProjectionFormula.isIso_app_biproduct`, `Stacks.EilenbergWatts.isIso_app_of_iso` and
`Stacks.EilenbergWatts.isIso_app_of_isColimit`: importing the scheme-theoretic modules that hold
those makes the instance search for the `k`-linear structure on `Mod(k)` used in
`AlgebraicGeometry.KunnethQcqs` stall on a universe constraint. -/

section Generic

variable {C D : Type*} [Category* C] [Category* D]

/-- A natural transformation between additive functors which is invertible at every summand of a
finite biproduct is invertible at the biproduct. -/
private theorem isIso_app_biproduct [Preadditive C] [Preadditive D] {F G : C ⥤ D} [F.Additive]
    [G.Additive] (α : F ⟶ G) {J : Type} [Finite J] (f : J → C) [HasBiproduct f]
    (h : ∀ j, IsIso (α.app (f j))) : IsIso (α.app (⨁ f)) := by
  have := Fintype.ofFinite J
  refine ⟨∑ j, G.map (biproduct.π f j) ≫ inv (α.app (f j)) ≫ F.map (biproduct.ι f j), ?_, ?_⟩
  · rw [Preadditive.comp_sum, ← F.map_id, ← biproduct.total, F.map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← α.naturality_assoc, IsIso.hom_inv_id_assoc, F.map_comp]
  · rw [Preadditive.sum_comp, ← G.map_id, ← biproduct.total, G.map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Category.assoc, Category.assoc, α.naturality, IsIso.inv_hom_id_assoc, G.map_comp]

/-- Invertibility of a component of a natural transformation transports along isomorphisms. -/
private theorem isIso_app_of_iso {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) [IsIso (α.app X)] :
    IsIso (α.app Y) := by
  have : α.app Y = F.map e.inv ≫ α.app X ≫ G.map e.hom := by
    rw [α.naturality_assoc, ← G.map_comp, e.inv_hom_id, G.map_id, Category.comp_id]
  rw [this]
  infer_instance

/-- A natural transformation between functors preserving a colimit is invertible at the colimit
as soon as it is invertible on the diagram. -/
private theorem isIso_app_of_isColimit {I : Type*} [Category* I] {F G : C ⥤ D} (α : F ⟶ G)
    {K : I ⥤ C} {c : Cocone K} (hc : IsColimit c) [PreservesColimit K F] [PreservesColimit K G]
    (h : ∀ i, IsIso (α.app (K.obj i))) : IsIso (α.app c.pt) := by
  let hF := isColimitOfPreserves F hc
  let hG := isColimitOfPreserves G hc
  let w : K ⋙ F ≅ K ⋙ G := NatIso.ofComponents (fun i ↦ asIso (α.app (K.obj i)))
    (fun f ↦ α.naturality (K.map f))
  have : α.app c.pt = (hF.coconePointsIsoOfNatIso hG w).hom := by
    refine hF.hom_ext fun i ↦ ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact α.naturality (c.ι.app i)
  rw [this]
  infer_instance

/-- In a direct sum all of whose summands but one are zero, the inclusion of that summand is
bijective. -/
theorem bijective_lof_of_subsingleton {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → Subsingleton (M i)) :
    Function.Bijective (DirectSum.lof R ι M i₀) := by
  refine ⟨DirectSum.of_injective i₀, fun x ↦ ⟨x i₀, ?_⟩⟩
  ext i
  by_cases hi : i = i₀
  · subst hi
    simp [DirectSum.lof_eq_of]
  · have := h i hi
    exact Subsingleton.elim _ _

end Generic

section Element

variable {k : Type u} [Field k]

/-- The map `k ⟶ V` sending `1` to `v`. -/
abbrev elementHom {V : ModuleCat.{u} k} (v : V) : ModuleCat.of k k ⟶ V :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton k V v)

/-- Composing `elementHom v` with `g` gives `elementHom (g v)`. -/
theorem elementHom_comp {V W : ModuleCat.{u} k} (v : V) (g : V ⟶ W) :
    elementHom v ≫ g = elementHom (g v) := by
  ext
  simp

/-- `elementHom` is additive in the vector. -/
theorem elementHom_add {V : ModuleCat.{u} k} (v v' : V) :
    elementHom (v + v') = elementHom v + elementHom v' := by
  ext
  simp

/-- `elementHom (c • v)` is multiplication by `c` on `k` followed by `elementHom v`. -/
theorem elementHom_smul {V : ModuleCat.{u} k} (c : k) (v : V) :
    elementHom (c • v) = (c • 𝟙 (ModuleCat.of k k)) ≫ elementHom v := by
  ext
  simp

end Element

variable {k : Type u} [Field k] {B : Type v} [Category.{u} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ModuleCat.{u} k)]
  (T : ModuleCat.{u} k ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  (E : B ⥤ ModuleCat.{u} k) [E.Additive]

/-- The right derived functor `Rᵇ E` is additive. -/
instance (b : ℤ) : (E.rightDerivedPlus b).Additive := by
  unfold Functor.rightDerivedPlus
  infer_instance

/-- Every vector space over a field is a projective module. -/
instance (M : ModuleCat.{u} k) : Projective M :=
  ModuleCat.projective_of_free (Module.Free.chooseBasis k M)

/-- The composite `Ξ = RE ∘ RT` of the two right derived functors. -/
abbrev Ξ : DerivedCategory.Plus (ModuleCat.{u} k) ⥤ DerivedCategory.Plus (ModuleCat.{u} k) :=
  T.rightDerivedFunctorPlus ⋙ E.rightDerivedFunctorPlus

/-- The coefficient module `M_b = Rᵇ E(T k)`. -/
abbrev coeff (b : ℤ) : ModuleCat.{u} k :=
  (E.rightDerivedPlus b).obj (T.obj (ModuleCat.of k k))

/-! ### Classes as morphisms out of `k[-a]` -/

section Class

variable (K : DerivedCategory.Plus (ModuleCat.{u} k)) (a : ℤ)

/-- **The morphism `k[-a] ⟶ K` representing a class `x ∈ Hᵃ(K)`**: the unique one sending the
generator of `Hᵃ(k[-a]) = k` to `x` (`DerivedCategory.Plus.homologyFromSingleAddEquiv`). -/
def homologyClass (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K) :
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) a).obj (ModuleCat.of k k) ⟶ K :=
  (DerivedCategory.Plus.homologyFromSingleAddEquiv (ModuleCat.of k k) K a).symm (elementHom x)

/-- The morphism `homologyClass K a x` sends the generator of `Hᵃ(k[-a])` to `x`. -/
theorem homologyFromSingleAddEquiv_homologyClass
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K) :
    DerivedCategory.Plus.homologyFromSingleAddEquiv (ModuleCat.of k k) K a (homologyClass K a x) =
      elementHom x :=
  AddEquiv.apply_symm_apply _ _

/-- A morphism `f : k[-a] ⟶ K` is the class of `x` exactly when it sends the generator to `x`. -/
theorem eq_homologyClass_iff {x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K}
    (f : (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) a).obj (ModuleCat.of k k) ⟶ K) :
    f = homologyClass K a x ↔
      DerivedCategory.Plus.homologyFromSingleAddEquiv (ModuleCat.of k k) K a f = elementHom x := by
  rw [← homologyFromSingleAddEquiv_homologyClass K a x]
  exact (DerivedCategory.Plus.homologyFromSingleAddEquiv (ModuleCat.of k k) K a).injective.eq_iff
    |>.symm

variable {K} in
/-- The class of `x` followed by `φ : K ⟶ K'` is the class of `Hᵃ(φ)(x)`. -/
theorem homologyClass_comp {K' : DerivedCategory.Plus (ModuleCat.{u} k)} (φ : K ⟶ K')
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K) :
    homologyClass K a x ≫ φ =
      homologyClass K' a ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).map φ x) := by
  rw [eq_homologyClass_iff, DerivedCategory.Plus.homologyFromSingleAddEquiv_comp,
    homologyFromSingleAddEquiv_homologyClass, elementHom_comp]

/-- `homologyClass` is additive. -/
theorem homologyClass_add (x y : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K) :
    homologyClass K a (x + y) = homologyClass K a x + homologyClass K a y := by
  rw [homologyClass, elementHom_add, map_add]
  rfl

/-- The class of `c • x` is `(c • 𝟙 k)[-a]` followed by the class of `x`. -/
theorem homologyClass_smul (c : k)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K) :
    homologyClass K a (c • x) =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) a).map (c • 𝟙 _) ≫
        homologyClass K a x := by
  refine ((eq_homologyClass_iff K a _).2 ?_).symm
  rw [DerivedCategory.Plus.homologyFromSingleAddEquiv_apply, Functor.map_comp, ← Category.assoc,
    ← Functor.comp_map, ← NatTrans.naturality, Category.assoc,
    ← DerivedCategory.Plus.homologyFromSingleAddEquiv_apply,
    homologyFromSingleAddEquiv_homologyClass, elementHom_smul]
  rfl

end Class

/-! ### The pairing -/

section Pairing

variable (K : DerivedCategory.Plus (ModuleCat.{u} k)) (a b n : ℤ) (h : a + b = n)

/-- The map `M_b ⟶ Hⁿ(Ξ K)` attached to a class `x ∈ Hᵃ(K)`: `Hⁿ(Ξ x̂)` read through
`Hⁿ(Ξ(k[-a])) ≅ M_b`. -/
def pairingHom (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K) :
    coeff T E b ⟶ (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).obj ((Ξ T E).obj K) :=
  (DerivedCategory.Plus.singleDerivedHomologyIso E T a b n h).inv.app (ModuleCat.of k k) ≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).map
      ((Ξ T E).map (homologyClass K a x))

/-- `pairingHom` is additive in the class. -/
theorem pairingHom_add (x y : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K) :
    pairingHom T E K a b n h (x + y) = pairingHom T E K a b n h x + pairingHom T E K a b n h y := by
  rw [pairingHom, pairingHom, pairingHom, homologyClass_add, Functor.map_add, Functor.map_add,
    Preadditive.comp_add]

variable (hlin : ∀ (b : ℤ) (c : k),
  (E.rightDerivedPlus b).map (T.map (c • 𝟙 (ModuleCat.of k k))) = c • 𝟙 _)

include hlin in
/-- `pairingHom` is `k`-linear in the class when `Rᵇ E ∘ T` is `k`-linear on scalars. -/
theorem pairingHom_smul (c : k)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K) :
    pairingHom T E K a b n h (c • x) = c • pairingHom T E K a b n h x := by
  rw [pairingHom, pairingHom, homologyClass_smul, Functor.map_comp, Functor.map_comp,
    ← Category.assoc]
  have hnat := (DerivedCategory.Plus.singleDerivedHomologyIso E T a b n h).inv.naturality
    (c • 𝟙 (ModuleCat.of k k))
  simp only [Functor.comp_map] at hnat ⊢
  rw [← hnat, hlin b c]
  simp only [Functor.comp_obj, Linear.smul_comp, Category.id_comp]

/-- **The Künneth pairing** `Hᵃ(K) × M_b ⟶ Hⁿ(Ξ K)`, `k`-bilinear. -/
def kunnethPairing :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K →ₗ[k] coeff T E b →ₗ[k]
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).obj ((Ξ T E).obj K) :=
  LinearMap.mk₂ k (fun x y ↦ pairingHom T E K a b n h x y)
    (fun x x' y ↦ by rw [pairingHom_add]; rfl)
    (fun c x y ↦ by rw [pairingHom_smul T E K a b n h hlin]; rfl)
    (fun x y y' ↦ map_add _ y y')
    (fun c x y ↦ map_smul _ c y)

/-- The Künneth pairing evaluated at `x` and `y` is `pairingHom` of `x` applied to `y`. -/
theorem kunnethPairing_apply (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K)
    (y : coeff T E b) :
    kunnethPairing T E K a b n h hlin x y = pairingHom T E K a b n h x y :=
  rfl

variable {K} in
/-- The pairing is natural in `K`. -/
theorem pairingHom_naturality {K' : DerivedCategory.Plus (ModuleCat.{u} k)} (φ : K ⟶ K')
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).obj K) :
    pairingHom T E K' a b n h ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) a).map φ x) =
      pairingHom T E K a b n h x ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).map ((Ξ T E).map φ) := by
  rw [pairingHom, pairingHom, ← homologyClass_comp, Functor.map_comp, Functor.map_comp,
    Category.assoc]

end Pairing

/-! ### The Künneth map -/

section Map

variable (n : ℤ)

/-- The index set `{(a, b) | a + b = n}` of the Künneth decomposition. -/
abbrev Pairs := {ab : ℤ × ℤ // ab.1 + ab.2 = n}

/-- The underlying module `⨁_{a + b = n} Hᵃ(K) ⊗_k M_b` of the source of the Künneth map. -/
abbrev Source (K : DerivedCategory.Plus (ModuleCat.{u} k)) : Type u :=
  ⨁ ab : Pairs n,
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) ab.1.1).obj K ⊗[k] coeff T E ab.1.2

/-- The map induced on `Source` by a morphism of `D⁺(k)`. -/
def sourceMap {K K' : DerivedCategory.Plus (ModuleCat.{u} k)} (φ : K ⟶ K') :
    Source T E n K →ₗ[k] Source T E n K' :=
  DirectSum.lmap fun ab ↦
    TensorProduct.map ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) ab.1.1).map φ).hom
      LinearMap.id

omit [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- `sourceMap φ` sends `x ⊗ y` in the summand `ab` to `Hᵃ(φ)(x) ⊗ y` in the same summand. -/
theorem sourceMap_lof {K K' : DerivedCategory.Plus (ModuleCat.{u} k)} (φ : K ⟶ K') (ab : Pairs n)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) ab.1.1).obj K)
    (y : coeff T E ab.1.2) :
    sourceMap T E n φ (DirectSum.lof k _ _ ab (x ⊗ₜ y)) =
      DirectSum.lof k _ _ ab
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) ab.1.1).map φ x ⊗ₜ y) := by
  simp [sourceMap]

omit [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- `sourceMap` sends the identity to the identity. -/
theorem sourceMap_id (K : DerivedCategory.Plus (ModuleCat.{u} k)) :
    sourceMap T E n (𝟙 K) = LinearMap.id :=
  DirectSum.linearMap_ext k fun ab ↦ TensorProduct.ext' fun x y ↦ by
    simp [sourceMap_lof]

omit [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- `sourceMap` sends a composite to the composite. -/
theorem sourceMap_comp {K K' K'' : DerivedCategory.Plus (ModuleCat.{u} k)} (φ : K ⟶ K')
    (ψ : K' ⟶ K'') : sourceMap T E n (φ ≫ ψ) = sourceMap T E n ψ ∘ₗ sourceMap T E n φ :=
  DirectSum.linearMap_ext k fun ab ↦ TensorProduct.ext' fun x y ↦ by
    simp [sourceMap_lof]

omit [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- `sourceMap` is additive in the morphism. -/
theorem sourceMap_add {K K' : DerivedCategory.Plus (ModuleCat.{u} k)} (φ ψ : K ⟶ K') :
    sourceMap T E n (φ + ψ) = sourceMap T E n φ + sourceMap T E n ψ :=
  DirectSum.linearMap_ext k fun ab ↦ TensorProduct.ext' fun x y ↦ by
    simp [sourceMap_lof, TensorProduct.add_tmul]

/-- **The source of the Künneth map**, `K ↦ ⨁_{a + b = n} Hᵃ(K) ⊗_k M_b`, as a functor. -/
def kunnethSource : DerivedCategory.Plus (ModuleCat.{u} k) ⥤ ModuleCat.{u} k where
  obj K := ModuleCat.of k (Source T E n K)
  map φ := ModuleCat.ofHom (sourceMap T E n φ)
  map_id K := by
    rw [sourceMap_id]
    rfl
  map_comp φ ψ := by
    rw [sourceMap_comp]
    rfl

/-- The functor `kunnethSource` is additive. -/
instance : (kunnethSource T E n).Additive where
  map_add {_ _} {φ ψ} := by
    change ModuleCat.ofHom (sourceMap T E n (φ + ψ)) = _
    rw [sourceMap_add]
    rfl

variable (hlin : ∀ (b : ℤ) (c : k),
  (E.rightDerivedPlus b).map (T.map (c • 𝟙 (ModuleCat.of k k))) = c • 𝟙 _)

/-- The Künneth map on modules. -/
def kunnethLinearMap (K : DerivedCategory.Plus (ModuleCat.{u} k)) :
    Source T E n K →ₗ[k]
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).obj ((Ξ T E).obj K) :=
  DirectSum.toModule k _ _ fun ab ↦
    TensorProduct.lift (kunnethPairing T E K ab.1.1 ab.1.2 n ab.2 hlin)

/-- On `x ⊗ y` in the summand `(a, b)`, the Künneth map is `pairingHom` of `x` applied to `y`. -/
theorem kunnethLinearMap_lof (K : DerivedCategory.Plus (ModuleCat.{u} k)) (ab : Pairs n)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) ab.1.1).obj K)
    (y : coeff T E ab.1.2) :
    kunnethLinearMap T E n hlin K (DirectSum.lof k _ _ ab (x ⊗ₜ y)) =
      pairingHom T E K ab.1.1 ab.1.2 n ab.2 x y := by
  simp only [kunnethLinearMap, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  rfl

/-- The Künneth map on modules is natural in `K`. -/
theorem kunnethLinearMap_naturality {K K' : DerivedCategory.Plus (ModuleCat.{u} k)} (φ : K ⟶ K') :
    kunnethLinearMap T E n hlin K' ∘ₗ sourceMap T E n φ =
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).map ((Ξ T E).map φ)).hom ∘ₗ
        kunnethLinearMap T E n hlin K :=
  DirectSum.linearMap_ext k fun ab ↦ TensorProduct.ext' fun x y ↦ by
    simp only [LinearMap.comp_apply, sourceMap_lof, kunnethLinearMap_lof, pairingHom_naturality]
    rfl

/-- **The Künneth map** `⨁_{a + b = n} Hᵃ(K) ⊗_k M_b ⟶ Hⁿ(Ξ K)`, natural in `K`: on the summand
`(a, b)` it is the pairing `x ⊗ y ↦ Hⁿ(Ξ x̂)(y)`. -/
def kunnethNatTrans :
    kunnethSource T E n ⟶ Ξ T E ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n where
  app K := ModuleCat.ofHom (kunnethLinearMap T E n hlin K)
  naturality {_ _} φ := ModuleCat.hom_ext (kunnethLinearMap_naturality T E n hlin φ)

end Map

/-! ### Cohomology commutes with tensoring by a vector space -/

section Coefficients

variable (b : ℤ) (hlin : ∀ (b : ℤ) (c : k),
  (E.rightDerivedPlus b).map (T.map (c • 𝟙 (ModuleCat.of k k))) = c • 𝟙 _)

/-- The canonical map `V ⊗_k M_b ⟶ Rᵇ E(T V)`, `v ⊗ y ↦ Rᵇ E(T(v̂))(y)` for `v̂ : k ⟶ V`. -/
def coeffLinearMap (V : ModuleCat.{u} k) :
    V ⊗[k] coeff T E b →ₗ[k] (E.rightDerivedPlus b).obj (T.obj V) :=
  TensorProduct.lift (LinearMap.mk₂ k
    (fun v y ↦ (E.rightDerivedPlus b).map (T.map (elementHom v)) y)
    (fun v v' y ↦ by rw [elementHom_add, T.map_add, Functor.map_add]; rfl)
    (fun c v y ↦ by
      rw [elementHom_smul, T.map_comp, Functor.map_comp, hlin b c]
      simp)
    (fun v y y' ↦ map_add _ y y')
    (fun c v y ↦ map_smul _ c y))

omit [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- `coeffLinearMap` sends `v ⊗ y` to `Rᵇ E(T(v̂))(y)`. -/
theorem coeffLinearMap_tmul (V : ModuleCat.{u} k) (v : V) (y : coeff T E b) :
    coeffLinearMap T E b hlin V (v ⊗ₜ y) = (E.rightDerivedPlus b).map (T.map (elementHom v)) y :=
  rfl

/-- **The canonical map `V ⊗_k M_b ⟶ Rᵇ E(T V)`**, natural in `V`. -/
def coeffNatTrans : tensorRight (coeff T E b) ⟶ T ⋙ E.rightDerivedPlus b where
  app V := ModuleCat.ofHom (coeffLinearMap T E b hlin V)
  naturality {V V'} g := by
    ext1
    refine TensorProduct.ext' fun v y ↦ ?_
    change coeffLinearMap T E b hlin V' (g v ⊗ₜ y) =
      (E.rightDerivedPlus b).map (T.map g) (coeffLinearMap T E b hlin V (v ⊗ₜ y))
    rw [coeffLinearMap_tmul, coeffLinearMap_tmul, ← elementHom_comp, T.map_comp, Functor.map_comp]
    rfl

/-- At `V = k` the map `k ⊗_k M_b ⟶ Rᵇ E(T k)` is an isomorphism. -/
instance isIso_coeffNatTrans_app_self :
    IsIso ((coeffNatTrans T E b hlin).app (ModuleCat.of k k)) := by
  have : coeffLinearMap T E b hlin (ModuleCat.of k k) =
      (TensorProduct.lid k (coeff T E b)).toLinearMap := by
    refine TensorProduct.ext' fun c y ↦ ?_
    rw [coeffLinearMap_tmul, show elementHom c = c • 𝟙 (ModuleCat.of k k) by ext; simp, hlin b c]
    rfl
  change IsIso (ModuleCat.ofHom (coeffLinearMap T E b hlin (ModuleCat.of k k)))
  rw [this]
  exact (TensorProduct.lid k (coeff T E b)).toModuleIso.isIso_hom

variable (hsum : ∀ (b : ℕ) (J : Type u),
  PreservesColimitsOfShape (Finset (Discrete J)) (T ⋙ E.rightDerivedPlus (b : ℤ)))

omit [PreservesFiniteLimits T] in
include hsum in
/-- **Cohomology commutes with tensoring by a vector space**: `V ⊗_k M_b ⟶ Rᵇ E(T V)` is an
isomorphism for every `V`. -/
theorem isIso_coeffNatTrans_app (V : ModuleCat.{u} k) :
    IsIso ((coeffNatTrans T E b hlin).app V) := by
  rcases lt_or_ge b 0 with hb | hb
  · have h₁ : IsZero ((tensorRight (coeff T E b)).obj V) := by
      have := ModuleCat.isZero_iff_subsingleton.mp
        (Functor.isZero_rightDerivedPlus_of_neg E (T.obj (ModuleCat.of k k)) b hb)
      exact ModuleCat.isZero_iff_subsingleton.mpr
        (inferInstanceAs (Subsingleton (V ⊗[k] coeff T E b)))
    exact ⟨⟨0, h₁.eq_of_src _ _,
      (Functor.isZero_rightDerivedPlus_of_neg E (T.obj V) b hb).eq_of_src _ _⟩⟩
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  let J := Module.Free.ChooseBasisIndex k V
  have := hsum b J
  have : PreservesColimitsOfShape (Finset (Discrete J)) (tensorRight (coeff T E b)) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  let f : J → ModuleCat.{u} k := fun _ ↦ ModuleCat.of k k
  have e : V ≅ ∐ f :=
    ((Module.Free.chooseBasis k V).repr ≪≫ₗ (finsuppLEquivDirectSum k k J)).toModuleIso ≪≫
      (ModuleCat.coprodIsoDirectSum f).symm
  have hfin : ∀ S : Finset (Discrete J), IsIso ((coeffNatTrans T E b hlin).app
      ((CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor f)).obj S)) := fun S ↦
    isIso_app_of_isColimit (coeffNatTrans T E b hlin)
      (colimit.isColimit (Discrete.functor fun x : S ↦ f x.1.as)) fun _ ↦
        isIso_coeffNatTrans_app_self T E b hlin
  have : IsIso ((coeffNatTrans T E b hlin).app (∐ f)) :=
    isIso_app_of_isColimit (coeffNatTrans T E b hlin)
      (K := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor f))
      (c := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone f)
      (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone f) hfin
  exact isIso_app_of_iso _ e.symm

end Coefficients

/-! ### The Künneth map is an isomorphism -/

section Iso

variable (hlin : ∀ (b : ℤ) (c : k),
  (E.rightDerivedPlus b).map (T.map (c • 𝟙 (ModuleCat.of k k))) = c • 𝟙 _)
  (hsum : ∀ (b : ℕ) (J : Type u),
    PreservesColimitsOfShape (Finset (Discrete J)) (T ⋙ E.rightDerivedPlus (b : ℤ)))

/-- The class of `v ∈ V = Hᵃ(V[-a])` is `v̂[-a]`. -/
theorem homologyClass_single (a : ℤ) (V : ModuleCat.{u} k) (v : V) :
    homologyClass ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) a).obj V) a
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := ModuleCat.{u} k) a).inv.app
        V v) =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) a).map (elementHom v) := by
  refine ((eq_homologyClass_iff _ a _).2 ?_).symm
  rw [DerivedCategory.Plus.homologyFromSingleAddEquiv_apply, ← Functor.comp_map,
    ← NatTrans.naturality, Functor.id_map, elementHom_comp]

include hsum in
/-- **The Künneth map is an isomorphism on a single complex** `V[-a]`. -/
theorem isIso_kunnethNatTrans_app_single (n a : ℤ) (V : ModuleCat.{u} k) :
    IsIso ((kunnethNatTrans T E n hlin).app
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) a).obj V)) := by
  let K := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) a).obj V
  let ab₀ : Pairs n := ⟨(a, n - a), by simp⟩
  let e := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := ModuleCat.{u} k) a).app V
  have := isIso_coeffNatTrans_app T E (n - a) hlin hsum V
  have hcoeff : Function.Bijective (coeffLinearMap T E (n - a) hlin V) :=
    (ConcreteCategory.isIso_iff_bijective ((coeffNatTrans T E (n - a) hlin).app V)).1 inferInstance
  have hinv : Function.Bijective ((DerivedCategory.Plus.singleDerivedHomologyIso E T a (n - a) n
      (by omega)).inv.app V) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hlof : Function.Bijective (DirectSum.lof k (Pairs n) (fun ab ↦
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) ab.1.1).obj K ⊗[k]
        coeff T E ab.1.2) ab₀) := by
    refine bijective_lof_of_subsingleton _ ab₀ fun ab hab ↦ ?_
    have hz : IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) ab.1.1).obj K) :=
      DerivedCategory.Plus.isZero_homologyFunctor_singleFunctor_obj _ fun h ↦ hab (Subtype.ext
        (Prod.ext h (by have := ab.2; dsimp only [ab₀]; omega)))
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance
  have he : Function.Bijective (TensorProduct.map e.inv.hom (LinearMap.id (R := k)
      (M := coeff T E (n - a)))) :=
    (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl k _)).bijective
  have hcomp : kunnethLinearMap T E n hlin K ∘ₗ DirectSum.lof k _ _ ab₀ ∘ₗ
      TensorProduct.map e.inv.hom LinearMap.id =
        ((DerivedCategory.Plus.singleDerivedHomologyIso E T a (n - a) n
          (by omega)).inv.app V).hom ∘ₗ
          coeffLinearMap T E (n - a) hlin V := by
    refine TensorProduct.ext' fun v y ↦ ?_
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      kunnethLinearMap_lof]
    dsimp only [ab₀, e, Iso.app_inv]
    rw [pairingHom, homologyClass_single]
    have hnat := (DerivedCategory.Plus.singleDerivedHomologyIso E T a (n - a) n
      (by omega)).inv.naturality (elementHom v)
    simp only [Functor.comp_map] at hnat
    rw [coeffLinearMap_tmul, ← ModuleCat.comp_apply]
    exact (ConcreteCategory.congr_hom hnat y).symm
  have hbij : Function.Bijective (kunnethLinearMap T E n hlin K) := by
    have h2 := hinv.comp hcoeff
    rw [← LinearMap.coe_comp, ← hcomp, LinearMap.coe_comp, LinearMap.coe_comp] at h2
    exact (Function.Bijective.of_comp_iff _ (hlof.comp he)).1 h2
  exact (ConcreteCategory.isIso_iff_bijective _).2 hbij

include hsum in
/-- **The Künneth map is an isomorphism** at every `K ∈ D⁺(k)` whose cohomology vanishes outside
a finite set `I` of degrees. -/
theorem isIso_kunnethNatTrans_app (n : ℤ) (K : DerivedCategory.Plus (ModuleCat.{u} k))
    (I : Finset ℤ)
    (hZ : ∀ q, q ∉ I → IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) q).obj K)) :
    IsIso ((kunnethNatTrans T E n hlin).app K) := by
  have e := DerivedCategory.Plus.homologySplitting K I (fun _ _ ↦ inferInstance) hZ
  have : IsIso ((kunnethNatTrans T E n hlin).app
      (⨁ DerivedCategory.Plus.homologySummand K I)) :=
    isIso_app_biproduct _ _ fun q ↦ isIso_kunnethNatTrans_app_single T E hlin hsum n q _
  exact isIso_app_of_iso _ e.symm

end Iso

end Stacks.KunnethOverField
