module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RingHom.OpenImmersion
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PureSpreadoutQuotient

/-!
# Chart base changes

A *chart base change* is the ring-theoretic shape of a morphism `b/a : Y'/X' → Y/X` of the
category of Stacks, Section 0FKB, read on compatible affine charts `Spec A ⊆ X`, `Spec B ⊆ Y`,
`Spec A' ⊆ X'`, `Spec B' ⊆ Y'`: the coordinate ring `B'` is a principal localization of the base
change `A' ⊗_A B`, compatibly with the two given maps `A' → B'` and `B → B'`.

## Main definitions

* `Stacks.TateMap.ChartBaseChange A B A' B'`: an algebra structure of `B'` over `A' ⊗_A B`
  extending the maps `A' → B'` and `B → B'`, together with an element away from which `B'` is
  the localization of `A' ⊗_A B`.
* `Stacks.TateMap.ChartBaseChange.refl`: the identity of `A → B`.
* `Stacks.TateMap.ChartBaseChange.comp`: the composite of two chart base changes; its
  localization element is chosen, and nothing built from a chart base change should depend on
  that choice.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.TateMap

/-- A chart base change from `A → B` to `A' → B'`: `B'` is the localization of `A' ⊗_A B` away
from one element, for an `A' ⊗_A B`-algebra structure on `B'` extending the given maps
`A' → B'` and `B → B'`. The algebra structure is determined by `base_left` and `base_right`. -/
structure ChartBaseChange (A B A' B' : Type*) [CommRing A] [CommRing B] [CommRing A']
    [CommRing B'] [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] where
  /-- The algebra structure of `B'` over the base change. -/
  algebra : Algebra (A' ⊗[A] B) B'
  /-- It extends the map of bases. -/
  base_left : ∀ y : A',
    letI := algebra
    algebraMap (A' ⊗[A] B) B' (y ⊗ₜ[A] (1 : B)) = algebraMap A' B' y
  /-- It extends the map of sources. -/
  base_right : ∀ x : B,
    letI := algebra
    algebraMap (A' ⊗[A] B) B' ((1 : A') ⊗ₜ[A] x) = algebraMap B B' x
  /-- The element away from which `B'` is a localization of the base change. -/
  elt : A' ⊗[A] B
  /-- `B'` is the localization of the base change away from `elt`. -/
  isLocalization :
    letI := algebra
    IsLocalization.Away elt B'

namespace ChartBaseChange

variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B']

/-- The square of a chart base change commutes. -/
theorem algebraMap_comm (D : ChartBaseChange A B A' B') (a : A) :
    algebraMap B B' (algebraMap A B a) = algebraMap A' B' (algebraMap A A' a) := by
  let := D.algebra
  rw [← D.base_right, ← D.base_left]
  congr 1
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

/-- The identity of `A → B` is a chart base change. -/
def refl (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : ChartBaseChange A B A B where
  algebra := (Algebra.TensorProduct.lid A B).toRingHom.toAlgebra
  base_left y := by
    change Algebra.TensorProduct.lid A B (y ⊗ₜ[A] (1 : B)) = _
    simp [Algebra.algebraMap_eq_smul_one]
  base_right x := by
    change Algebra.TensorProduct.lid A B ((1 : A) ⊗ₜ[A] x) = _
    simp
  elt := 1
  isLocalization := by
    let : Algebra (A ⊗[A] B) B := (Algebra.TensorProduct.lid A B).toRingHom.toAlgebra
    exact IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (Algebra.TensorProduct.lid A B).bijective

/-- A commutative square whose two maps `A → A'` and `B → B'` are bijective is a chart base
change; this is how a chart base change is transported along isomorphisms of coordinate rings. -/
def ofBijective (hA : Function.Bijective (algebraMap A A'))
    (hB : Function.Bijective (algebraMap B B'))
    (hcomm : ∀ a : A, algebraMap B B' (algebraMap A B a) = algebraMap A' B' (algebraMap A A' a)) :
    ChartBaseChange A B A' B' :=
  letI : Algebra A B' := ((algebraMap A' B').comp (algebraMap A A')).toAlgebra
  haveI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun a ↦ (hcomm a).symm
  let φ : A' ⊗[A] B →ₐ[A'] B' :=
    Algebra.TensorProduct.lift (Algebra.ofId A' B') (IsScalarTower.toAlgHom A B B')
      (fun _ _ ↦ Commute.all _ _)
  have hφ : Function.Bijective φ := by
    have hsurj : Function.Surjective φ := fun z ↦ by
      obtain ⟨x, rfl⟩ := hB.2 z
      exact ⟨1 ⊗ₜ x, by simp [φ]⟩
    refine ⟨fun z w h ↦ ?_, hsurj⟩
    have key : ∀ z : A' ⊗[A] B, ∃ x : B, z = 1 ⊗ₜ x := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul y x =>
        obtain ⟨a, rfl⟩ := hA.2 y
        exact ⟨algebraMap A B a * x, by
          rw [Algebra.algebraMap_eq_smul_one (A := A'), TensorProduct.smul_tmul,
            Algebra.smul_def]⟩
      | add z w hz hw =>
        obtain ⟨x, rfl⟩ := hz
        obtain ⟨x', rfl⟩ := hw
        exact ⟨x + x', by rw [TensorProduct.tmul_add]⟩
    obtain ⟨x, rfl⟩ := key z
    obtain ⟨x', rfl⟩ := key w
    have : algebraMap B B' x = algebraMap B B' x' := by simpa [φ] using h
    rw [hB.1 this]
  { algebra := φ.toRingHom.toAlgebra
    base_left := fun y ↦ by
      change φ (y ⊗ₜ[A] (1 : B)) = _
      simp [φ]
    base_right := fun x ↦ by
      change φ ((1 : A') ⊗ₜ[A] x) = _
      simp [φ]
    elt := 1
    isLocalization := by
      let : Algebra (A' ⊗[A] B) B' := φ.toRingHom.toAlgebra
      exact IsLocalization.away_of_isUnit_of_bijective _ isUnit_one hφ }

/-- The algebra map `A' ⊗_A B → B'` determined by a commutative square. -/
def lift
    (hcomm : ∀ a : A, algebraMap B B' (algebraMap A B a) = algebraMap A' B' (algebraMap A A' a)) :
    A' ⊗[A] B →+* B' :=
  letI : Algebra A B' := ((algebraMap A' B').comp (algebraMap A A')).toAlgebra
  haveI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun a ↦ (hcomm a).symm
  (Algebra.TensorProduct.lift (Algebra.ofId A' B') (IsScalarTower.toAlgHom A B B')
    (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- The map `lift hcomm` sends `y ⊗ x` to the product of the images of `y` and `x` in `B'`. -/
theorem lift_tmul (hcomm : ∀ a : A,
    algebraMap B B' (algebraMap A B a) = algebraMap A' B' (algebraMap A A' a)) (y : A') (x : B) :
    lift hcomm (y ⊗ₜ x) = algebraMap A' B' y * algebraMap B B' x := by
  simp [lift]

/-- If `S` is a localization of `R` at `M`, the elements of `M` become units in `T`, and `T` is
a principal localization of `R`, then `T` is a principal localization of `S`. -/
private theorem isStandardOpenImmersion_of_isLocalization_aux {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid R) [IsLocalization M S] (hM : ∀ m ∈ M, IsUnit (algebraMap R T m))
    [Algebra.IsStandardOpenImmersion R T] : Algebra.IsStandardOpenImmersion S T := by
  have hunit : Algebra.algebraMapSubmonoid T M ≤ IsUnit.submonoid T := by
    rintro _ ⟨m, hm, rfl⟩
    exact hM m hm
  have : IsLocalization (Algebra.algebraMapSubmonoid T M) T := IsLocalization.of_le_isUnit hunit
  have : Algebra.IsPushout R T S T :=
    (Algebra.isLocalization_iff_isPushout M S (T := T) (B := T)).mp inferInstance
  exact Algebra.IsStandardOpenImmersion.of_isPushout R T S T

/-- In a square of principal localizations `A → A_a`, `B → B_b` in which `a` becomes a unit in
`B_b`, the ring `B_b` is a principal localization of `A_a ⊗_A B`. -/
theorem exists_away_lift (a : A) [IsLocalization.Away a A'] (b : B) [IsLocalization.Away b B']
    (hcomm : ∀ x : A,
      algebraMap B B' (algebraMap A B x) = algebraMap A' B' (algebraMap A A' x)) :
    ∃ e : A' ⊗[A] B, letI := (lift hcomm).toAlgebra; IsLocalization.Away e B' := by
  let : Algebra (A' ⊗[A] B) B' := (lift hcomm).toAlgebra
  let : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B (A' ⊗[A] B) B' :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap B B' x = lift hcomm ((1 : A') ⊗ₜ[A] x)
      rw [lift_tmul, map_one, one_mul]
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)) (A' ⊗[A] B) :=
    IsLocalization.tensorRight (S := B) (A := A') (Submonoid.powers a)
  have : Algebra.IsStandardOpenImmersion B B' := ⟨b, inferInstance⟩
  exact (isStandardOpenImmersion_of_isLocalization_aux (S := A' ⊗[A] B)
    (Algebra.algebraMapSubmonoid B (Submonoid.powers a)) (by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      change IsUnit (algebraMap B B' (algebraMap A B (a ^ n)))
      rw [hcomm]
      exact (IsLocalization.map_units A' (⟨a ^ n, n, rfl⟩ : Submonoid.powers a)).map
        (algebraMap A' B'))).exists_away

/-- A square of principal localizations `A → A_a`, `B → B_b`, in which `a` becomes a unit in
`B_b`, is a chart base change. This is the shape of a restriction of an affine chart to principal
opens of the source and the base. -/
def ofAway (a : A) [IsLocalization.Away a A'] (b : B) [IsLocalization.Away b B']
    (hcomm : ∀ x : A,
      algebraMap B B' (algebraMap A B x) = algebraMap A' B' (algebraMap A A' x)) :
    ChartBaseChange A B A' B' where
  algebra := (lift hcomm).toAlgebra
  base_left := fun y ↦ by
    change lift hcomm (y ⊗ₜ[A] (1 : B)) = _
    rw [lift_tmul, map_one, mul_one]
  base_right := fun x ↦ by
    change lift hcomm ((1 : A') ⊗ₜ[A] x) = _
    rw [lift_tmul, map_one, one_mul]
  elt := (exists_away_lift a b hcomm).choose
  isLocalization := (exists_away_lift a b hcomm).choose_spec

/-- **Cancellation of localizations.** If `S` is a localization of `R` at `M`, the elements of
`M` become units in `T`, and `T` is a principal localization of `R`, then `T` is a principal
localization of `S`. -/
theorem isStandardOpenImmersion_of_isLocalization {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid R) [IsLocalization M S] (hM : ∀ m ∈ M, IsUnit (algebraMap R T m))
    [Algebra.IsStandardOpenImmersion R T] : Algebra.IsStandardOpenImmersion S T := by
  exact isStandardOpenImmersion_of_isLocalization_aux M hM

/-- **Shrinking the source chart of a chart base change.** If `D` is a chart base change from
`A → B` to `A' → B'` and `B → B'` factors through a principal localization `B₀` of `B`, then `D`
induces a chart base change from `A → B₀` to `A' → B'`. -/
def ofSourceAway {B₀ : Type*} [CommRing B₀] [Algebra B B₀] [Algebra A B₀] [IsScalarTower A B B₀]
    [Algebra B₀ B'] [IsScalarTower B B₀ B'] (D : ChartBaseChange A B A' B') (b : B)
    [IsLocalization.Away b B₀] : ChartBaseChange A B₀ A' B' :=
  have hcomm : ∀ a : A, algebraMap B₀ B' (algebraMap A B₀ a) =
      algebraMap A' B' (algebraMap A A' a) := fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B B₀, ← IsScalarTower.algebraMap_apply B B₀ B',
      D.algebraMap_comm]
  have hex : ∃ e : A' ⊗[A] B₀, letI := (lift hcomm).toAlgebra; IsLocalization.Away e B' := by
    let := D.algebra
    let : Algebra (A' ⊗[A] B₀) B' := (lift hcomm).toAlgebra
    let : Algebra (A' ⊗[A] B) (A' ⊗[A] B₀) :=
      (Algebra.TensorProduct.map (AlgHom.id A A')
        (IsScalarTower.toAlgHom A B B₀)).toRingHom.toAlgebra
    have : IsScalarTower (A' ⊗[A] B) (A' ⊗[A] B₀) B' := IsScalarTower.of_algebraMap_eq fun z ↦ by
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]
      | tmul y x =>
        change algebraMap (A' ⊗[A] B) B' (y ⊗ₜ x) = lift hcomm (y ⊗ₜ algebraMap B B₀ x)
        have : (y ⊗ₜ[A] x : A' ⊗[A] B) = (y ⊗ₜ[A] (1 : B)) * ((1 : A') ⊗ₜ[A] x) := by simp
        rw [this, map_mul, D.base_left, D.base_right, lift_tmul,
          ← IsScalarTower.algebraMap_apply]
    have : Algebra.IsStandardOpenImmersion (A' ⊗[A] B) B' := ⟨D.elt, D.isLocalization⟩
    let : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    have : IsScalarTower B (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq fun x ↦
      (D.base_right x).symm
    let : Algebra B₀ (A' ⊗[A] B₀) := Algebra.TensorProduct.rightAlgebra
    let : Algebra B (A' ⊗[A] B₀) :=
      ((Algebra.TensorProduct.includeRight (R := A) (A := A')).toRingHom.comp
        (algebraMap B B₀)).toAlgebra
    have : IsScalarTower B B₀ (A' ⊗[A] B₀) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : IsScalarTower B (A' ⊗[A] B) (A' ⊗[A] B₀) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ by
        change (1 : A') ⊗ₜ[A] algebraMap B B₀ x = Algebra.TensorProduct.map (AlgHom.id A A')
          (IsScalarTower.toAlgHom A B B₀) ((1 : A') ⊗ₜ[A] x)
        simp
    have : IsScalarTower A B₀ (A' ⊗[A] B₀) := IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap A (A' ⊗[A] B₀) x = (1 : A') ⊗ₜ[A] algebraMap A B₀ x
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one x, TensorProduct.smul_tmul]
    have : IsScalarTower A B (A' ⊗[A] B) := IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap A (A' ⊗[A] B) x = (1 : A') ⊗ₜ[A] algebraMap A B x
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one x, TensorProduct.smul_tmul]
    have : IsScalarTower A (A' ⊗[A] B) (A' ⊗[A] B₀) := IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap A (A' ⊗[A] B₀) x = Algebra.TensorProduct.map (AlgHom.id A A')
        (IsScalarTower.toAlgHom A B B₀) (algebraMap A (A' ⊗[A] B) x)
      rw [AlgHom.commutes]
    have : IsScalarTower A' (A' ⊗[A] B) (A' ⊗[A] B₀) := IsScalarTower.of_algebraMap_eq fun y ↦ by
      change algebraMap A' (A' ⊗[A] B₀) y = Algebra.TensorProduct.map (AlgHom.id A A')
        (IsScalarTower.toAlgHom A B B₀) (algebraMap A' (A' ⊗[A] B) y)
      simp [Algebra.TensorProduct.algebraMap_apply]
    have : Algebra.IsPushout A B A' (A' ⊗[A] B) := inferInstance
    have : Algebra.IsPushout A B₀ A' (A' ⊗[A] B₀) := inferInstance
    have : Algebra.IsPushout B B₀ (A' ⊗[A] B) (A' ⊗[A] B₀) :=
      (Algebra.IsPushout.comp_iff A B A' (A' ⊗[A] B) (T := B₀) (T' := A' ⊗[A] B₀)).mp
        inferInstance
    have : IsLocalization (Algebra.algebraMapSubmonoid (A' ⊗[A] B) (Submonoid.powers b))
        (A' ⊗[A] B₀) :=
      (Algebra.isLocalization_iff_isPushout (Submonoid.powers b) B₀ (T := A' ⊗[A] B)
        (B := A' ⊗[A] B₀)).mpr (Algebra.IsPushout.symm inferInstance)
    have := isStandardOpenImmersion_of_isLocalization (R := A' ⊗[A] B) (S := A' ⊗[A] B₀) (T := B')
      (Algebra.algebraMapSubmonoid (A' ⊗[A] B) (Submonoid.powers b)) (by
        rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
        dsimp only
        rw [← IsScalarTower.algebraMap_apply B (A' ⊗[A] B) B',
          IsScalarTower.algebraMap_apply B B₀ B', map_pow, map_pow]
        exact ((IsLocalization.Away.algebraMap_isUnit b).map (algebraMap B₀ B')).pow n)
    exact this.exists_away
  { algebra := (lift hcomm).toAlgebra
    base_left := fun y ↦ by
      change lift hcomm (y ⊗ₜ[A] (1 : B₀)) = _
      rw [lift_tmul, map_one, mul_one]
    base_right := fun x ↦ by
      change lift hcomm ((1 : A') ⊗ₜ[A] x) = _
      rw [lift_tmul, map_one, one_mul]
    elt := hex.choose
    isLocalization := hex.choose_spec }

/-- Localizing the source of `A → B` away from an element `b` is a chart base change from `A → B`
to `A → B_b`, the base being unchanged. -/
def ofLocalizationSource {A B B₀ : Type*} [CommRing A] [CommRing B] [CommRing B₀] [Algebra A B]
    [Algebra B B₀] [Algebra A B₀] [IsScalarTower A B B₀] (b : B) [IsLocalization.Away b B₀] :
    ChartBaseChange A B A B₀ :=
  haveI : IsLocalization.Away (1 : A) A :=
    IsLocalization.away_of_isUnit_of_bijective A isUnit_one Function.bijective_id
  ofAway 1 b fun x ↦ by
    rw [← IsScalarTower.algebraMap_apply]
    rfl

section comp

variable {A'' B'' : Type*} [CommRing A''] [CommRing B''] [Algebra A' A''] [Algebra A'' B'']
  [Algebra B' B''] [Algebra A A''] [IsScalarTower A A' A''] [Algebra B B'']
  [IsScalarTower B B' B'']

open Algebra.TensorProduct

omit [Algebra A'' B''] [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B''] in
/-- The comparison `A'' ⊗_A B → A'' ⊗_{A'} B'`, `y ⊗ x ↦ y ⊗ x`, underlying the composite of
two chart base changes. -/
def compAux (D₁ : ChartBaseChange A B A' B') : A'' ⊗[A] B →+* A'' ⊗[A'] B' :=
  (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A A'' (A'' ⊗[A'] B'))
    { toRingHom := (Algebra.TensorProduct.includeRight (R := A') (A := A'')).toRingHom.comp
        (algebraMap B B')
      commutes' := fun a ↦ by
        change (1 : A'') ⊗ₜ[A'] algebraMap B B' (algebraMap A B a) =
          algebraMap A'' (A'' ⊗[A'] B') (algebraMap A A'' a)
        rw [D₁.algebraMap_comm, Algebra.TensorProduct.algebraMap_apply,
          IsScalarTower.algebraMap_apply A A' A'',
          Algebra.algebraMap_eq_smul_one (algebraMap A A' a),
          Algebra.algebraMap_eq_smul_one (algebraMap A A' a), TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
        rfl }
    (fun _ _ ↦ Commute.all _ _)).toRingHom

omit [Algebra A'' B''] [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B''] in
/-- The map `compAux D₁` sends `y ⊗ x` to `y ⊗ x`, with `x` mapped into `B'`. -/
@[simp]
theorem compAux_tmul (D₁ : ChartBaseChange A B A' B') (y : A'') (x : B) :
    compAux (A'' := A'') D₁ (y ⊗ₜ[A] x) = y ⊗ₜ[A'] algebraMap B B' x := by
  simp [compAux]

omit [Algebra A'' B''] [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B''] in
/-- The base change `A'' ⊗_{A'} B'` is a principal localization of `A'' ⊗_A B`. -/
theorem exists_isLocalization_compAux (D₁ : ChartBaseChange A B A' B') :
    ∃ e : A'' ⊗[A] B,
      letI := (compAux (A'' := A'') D₁).toAlgebra
      IsLocalization.Away e (A'' ⊗[A'] B') := by
  let := D₁.algebra
  let := Stacks.Flatness.algebraBaseChangeTower A A' A'' B
  let : Algebra (A'' ⊗[A] B) (A'' ⊗[A'] B') := (compAux D₁).toAlgebra
  let : Algebra (A' ⊗[A] B) (A'' ⊗[A'] B') :=
    ((compAux D₁).comp (algebraMap (A' ⊗[A] B) (A'' ⊗[A] B))).toAlgebra
  let : Algebra B' (A'' ⊗[A'] B') := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower (A' ⊗[A] B) (A'' ⊗[A] B) (A'' ⊗[A'] B') :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (A' ⊗[A] B) B' (A'' ⊗[A'] B') := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    induction r using TensorProduct.inductionOn with
    | add r s hr hs => rw [map_add, map_add, hr, hs, map_add]
    | tmul y x =>
      change (compAux D₁) (Stacks.Flatness.baseChangeTowerAlgHom A A' A'' B (y ⊗ₜ x)) =
        (1 : A'') ⊗ₜ[A'] algebraMap (A' ⊗[A] B) B' (y ⊗ₜ[A] x)
      have : (y ⊗ₜ[A] x : A' ⊗[A] B) = (y ⊗ₜ[A] (1 : B)) * ((1 : A') ⊗ₜ[A] x) := by simp
      simp only [this, map_mul, D₁.base_left, D₁.base_right,
        Stacks.Flatness.baseChangeTowerAlgHom, Algebra.TensorProduct.map_tmul, compAux_tmul,
        AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      rw [map_one, map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        Algebra.algebraMap_eq_smul_one (A := A''), TensorProduct.smul_tmul, Algebra.smul_def]
  have : IsScalarTower A' B' (A'' ⊗[A'] B') := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A' (A'' ⊗[A'] B') a = (1 : A'') ⊗ₜ[A'] algebraMap A' B' a
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have : IsScalarTower A' (A'' ⊗[A] B) (A'' ⊗[A'] B') := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A' (A'' ⊗[A'] B') a = compAux D₁ (algebraMap A' A'' a ⊗ₜ[A] (1 : B))
    simp [Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower A'' (A'' ⊗[A] B) (A'' ⊗[A'] B') :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A'' (A'' ⊗[A'] B') a = compAux D₁ (a ⊗ₜ[A] (1 : B))
      simp [Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower A' (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply, D₁.base_left]
    rfl
  have := Stacks.Flatness.isScalarTower_baseChangeTower_left A A' A'' B
  have := (Stacks.Flatness.isPushout_baseChangeTower A A' A'' B).symm
  have : Algebra.IsPushout (A' ⊗[A] B) B' (A'' ⊗[A] B) (A'' ⊗[A'] B') :=
    (Algebra.IsPushout.comp_iff A' (A' ⊗[A] B) A'' (A'' ⊗[A] B) (T := B')
      (T' := A'' ⊗[A'] B')).mp inferInstance
  have : Algebra.IsStandardOpenImmersion (A' ⊗[A] B) B' := ⟨D₁.elt, D₁.isLocalization⟩
  exact (Algebra.IsStandardOpenImmersion.of_isPushout (A' ⊗[A] B) B' (A'' ⊗[A] B)
    (A'' ⊗[A'] B')).exists_away

omit [Algebra B B''] [IsScalarTower B B' B''] in
/-- The composite of two chart base changes is a principal localization of the base change. -/
theorem exists_isLocalization_comp (D₂ : ChartBaseChange A' B' A'' B'')
    (D₁ : ChartBaseChange A B A' B') :
    ∃ e : A'' ⊗[A] B,
      letI := D₂.algebra
      letI : Algebra (A'' ⊗[A] B) B'' :=
        ((algebraMap (A'' ⊗[A'] B') B'').comp (compAux D₁)).toAlgebra
      IsLocalization.Away e B'' := by
  let := D₂.algebra
  let : Algebra (A'' ⊗[A] B) (A'' ⊗[A'] B') := (compAux D₁).toAlgebra
  let : Algebra (A'' ⊗[A] B) B'' :=
    ((algebraMap (A'' ⊗[A'] B') B'').comp (compAux D₁)).toAlgebra
  have : IsScalarTower (A'' ⊗[A] B) (A'' ⊗[A'] B') B'' :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsStandardOpenImmersion (A'' ⊗[A] B) (A'' ⊗[A'] B') :=
    ⟨exists_isLocalization_compAux D₁⟩
  have : Algebra.IsStandardOpenImmersion (A'' ⊗[A'] B') B'' := ⟨D₂.elt, D₂.isLocalization⟩
  exact (Algebra.IsStandardOpenImmersion.trans (A'' ⊗[A] B) (A'' ⊗[A'] B') B'').exists_away

/-- The composite of two chart base changes. -/
def comp (D₂ : ChartBaseChange A' B' A'' B'') (D₁ : ChartBaseChange A B A' B') :
    ChartBaseChange A B A'' B'' :=
  letI := D₂.algebra
  { algebra := ((algebraMap (A'' ⊗[A'] B') B'').comp (compAux D₁)).toAlgebra
    base_left := fun y ↦ by
      change algebraMap (A'' ⊗[A'] B') B'' (compAux D₁ (y ⊗ₜ[A] (1 : B))) = _
      rw [compAux_tmul, map_one, D₂.base_left]
    base_right := fun x ↦ by
      change algebraMap (A'' ⊗[A'] B') B'' (compAux D₁ ((1 : A'') ⊗ₜ[A] x)) = _
      rw [compAux_tmul, D₂.base_right, ← IsScalarTower.algebraMap_apply]
    elt := (exists_isLocalization_comp D₂ D₁).choose
    isLocalization := (exists_isLocalization_comp D₂ D₁).choose_spec }

end comp

end ChartBaseChange

end Stacks.TateMap
