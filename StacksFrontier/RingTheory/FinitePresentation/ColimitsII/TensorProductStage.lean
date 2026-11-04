module

public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII.DirectedDescent

/-!
# Colimits and maps of finite presentation, II: Lemma 0C33

**Lemma 0C33.** Let `A = colim_i A_i` be a directed colimit of rings and `B₀ → C₀` a map of
`A₀`-algebras with `C₀` of finite presentation over `B₀`. If `A ⊗_{A₀} B₀ → A ⊗_{A₀} C₀` is
syntomic, resp. a relative global complete intersection, then so is
`A_i ⊗_{A₀} B₀ → A_i ⊗_{A₀} C₀` for some `i`. Both statements are deduced from the descent
theorems of `StacksFrontier.RingTheory.FinitePresentation.ColimitsII.DirectedDescent`,
applied to the directed system `(A_i ⊗_{A₀} B₀ → A_i ⊗_{A₀} C₀)`.

## Main results

* `Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_tensorProduct`,
  `Algebra.Syntomic.exists_stage_tensorProduct`: Lemma 0C33.

## Implementation notes

In Lemma 0C33 the colimit `A` is an arbitrary ring `R` with a cocone `ρ` of the system, given
elementwise: every element of `R` comes from a stage, and an element of a stage vanishing in `R`
vanishes at a later stage. The maps `A_i ⊗_{A₀} B₀ → A_i ⊗_{A₀} C₀` are
`Algebra.TensorProduct.map id φ₀`. The source proves the relative global complete intersection
case by descending a relative global complete intersection to a finite type `ℤ`-algebra
(Lemma 00SU) and appealing to Lemma 0C32; here the presentation is descended directly and the
dimension of the fibres is controlled by the openness argument of `DirectedDescent`, which needs
neither Lemma 00SU nor a Noetherian base.

## References

* [Stacks Project, Tag 0C33](https://stacks.math.columbia.edu/tag/0C33)
-/

@[expose] public section

universe u v

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- For `R`-algebras `A` and `B → C`, the square `B → C`, `A ⊗_R B → A ⊗_R C` is a pushout:
`A ⊗_R C = (A ⊗_R B) ⊗_B C`. -/
theorem Algebra.IsPushout.tensorProduct_map_id {R A B C : Type*} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra B C]
    [IsScalarTower R B C] [Algebra (A ⊗[R] B) (A ⊗[R] C)]
    (H : ∀ x, algebraMap (A ⊗[R] B) (A ⊗[R] C) x =
      Algebra.TensorProduct.map (AlgHom.id R A) (IsScalarTower.toAlgHom R B C) x)
    [Algebra B (A ⊗[R] C)] [IsScalarTower B C (A ⊗[R] C)] [IsScalarTower B (A ⊗[R] B) (A ⊗[R] C)] :
    Algebra.IsPushout B C (A ⊗[R] B) (A ⊗[R] C) := by
  have : IsScalarTower R (A ⊗[R] B) (A ⊗[R] C) := .of_algebraMap_eq fun r => by
    rw [H]; simp [Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower A (A ⊗[R] B) (A ⊗[R] C) := .of_algebraMap_eq fun r => by
    rw [H]; simp [Algebra.TensorProduct.algebraMap_apply]
  exact (Algebra.IsPushout.comp_iff R B A (T := C) (S' := A ⊗[R] B) (T' := A ⊗[R] C)).mp
    inferInstance


/-- Applying `map g id` after `map f id` on `X ⊗ P` is `map h id` when `g ∘ f = h`. -/
private theorem map_id_apply_map_id {S P X Y Z : Type*} [CommSemiring S] [CommSemiring P]
    [CommSemiring X] [CommSemiring Y] [CommSemiring Z] [Algebra S P] [Algebra S X] [Algebra S Y]
    [Algebra S Z] (f : X →ₐ[S] Y) (g : Y →ₐ[S] Z) (h : X →ₐ[S] Z) (hgf : ∀ x, g (f x) = h x)
    (x : X ⊗[S] P) :
    Algebra.TensorProduct.map g (AlgHom.id S P) (Algebra.TensorProduct.map f (AlgHom.id S P) x) =
      Algebra.TensorProduct.map h (AlgHom.id S P) x := by
  obtain rfl : g.comp f = h := AlgHom.ext hgf
  exact (AlgHom.congr_fun
    (Algebra.TensorProduct.map_comp g f (AlgHom.id S P) (AlgHom.id S P)) x).symm

/-- The squares `X ⊗ B → X ⊗ C`, `X → Y` commute: `map f id` commutes with `map id φ`. -/
private theorem map_id_comp_map_comm {S X Y B C : Type*} [CommSemiring S] [CommSemiring B]
    [CommSemiring C] [CommSemiring X] [CommSemiring Y] [Algebra S B] [Algebra S C] [Algebra S X]
    [Algebra S Y] (f : X →ₐ[S] Y) (φ : B →ₐ[S] C) :
    (Algebra.TensorProduct.map f (AlgHom.id S C)).toRingHom.comp
        (Algebra.TensorProduct.map (AlgHom.id S X) φ).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id S Y) φ).toRingHom.comp
        (Algebra.TensorProduct.map f (AlgHom.id S B)).toRingHom := by
  have := (Algebra.TensorProduct.map_comp f (AlgHom.id S X) (AlgHom.id S C) φ).symm.trans
    (Algebra.TensorProduct.map_comp (AlgHom.id S Y) f φ (AlgHom.id S B))
  exact RingHom.ext fun x => AlgHom.congr_fun this x

open Module.Flat.DirectedModel in
/-- Both parts of Lemma 0C33 at once: the base changes `A_i ⊗_{A₀} B₀ → A_i ⊗_{A₀} C₀`,
`i ≥ i₀`, form a directed system with cartesian transition squares and colimit
`A ⊗_{A₀} B₀ → A ⊗_{A₀} C₀`, to which the descent theorems apply. -/
theorem Algebra.TensorProduct.exists_stage_of_directed_aux
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    {A : ι → Type u} [∀ i, CommRing (A i)] (a : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A fun i j h => a i j h] {R : Type*} [CommRing R] (ρ : ∀ i, A i →+* R)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x) (hρs : ∀ r, ∃ i x, ρ i x = r)
    (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0)
    {i₀ : ι} {B₀ C₀ : Type v} [CommRing B₀] [CommRing C₀] [Algebra (A i₀) B₀] [Algebra (A i₀) C₀]
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation) :
    letI := (ρ i₀).toAlgebra
    letI := (Algebra.TensorProduct.map (AlgHom.id (A i₀) R) φ₀).toRingHom.toAlgebra
    (Algebra.IsRelativeGlobalCompleteIntersection (R ⊗[A i₀] B₀) (R ⊗[A i₀] C₀) →
      ∃ i, ∃ h : i₀ ≤ i, letI := (a i₀ i h).toAlgebra
        letI := (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A i)) φ₀).toRingHom.toAlgebra
        Algebra.IsRelativeGlobalCompleteIntersection (A i ⊗[A i₀] B₀) (A i ⊗[A i₀] C₀)) ∧
    (Algebra.Syntomic (R ⊗[A i₀] B₀) (R ⊗[A i₀] C₀) →
      ∃ i, ∃ h : i₀ ≤ i, letI := (a i₀ i h).toAlgebra
        letI := (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A i)) φ₀).toRingHom.toAlgebra
        Algebra.Syntomic (A i ⊗[A i₀] B₀) (A i ⊗[A i₀] C₀)) := by
  classical
  let _ : Algebra (A i₀) R := (ρ i₀).toAlgebra
  let _ : Algebra (R ⊗[A i₀] B₀) (R ⊗[A i₀] C₀) :=
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) R) φ₀).toRingHom.toAlgebra
  let J := Tail i₀
  let _ (j : J) : Algebra (A i₀) (A j.1) := (a i₀ j.1 j.2).toAlgebra
  let fA (j k : J) (h : j ≤ k) : A j.1 →ₐ[A i₀] A k.1 :=
    { a j.1 k.1 h with
      commutes' := fun x => DirectedSystem.map_map' (fun i j h => a i j h) j.2 h x }
  have : DirectedSystem (fun j : J => A j.1) fun j k h => fA j k h :=
    ⟨fun _ x => DirectedSystem.map_self' (fun i j h => a i j h) x,
      fun _ _ _ hjk hkl x => DirectedSystem.map_map' (fun i j h => a i j h) hjk hkl x⟩
  let _ (j : J) : Algebra (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀) :=
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀).toRingHom.toAlgebra
  let aJ (j k : J) (h : j ≤ k) : A j.1 ⊗[A i₀] B₀ →+* A k.1 ⊗[A i₀] B₀ :=
    (Algebra.TensorProduct.map (fA j k h) (AlgHom.id (A i₀) B₀)).toRingHom
  let bJ (j k : J) (h : j ≤ k) : A j.1 ⊗[A i₀] C₀ →+* A k.1 ⊗[A i₀] C₀ :=
    (Algebra.TensorProduct.map (fA j k h) (AlgHom.id (A i₀) C₀)).toRingHom
  have hself (P : Type v) [CommRing P] [Algebra (A i₀) P] (j : J) (x : A j.1 ⊗[A i₀] P) :
      Algebra.TensorProduct.map (fA j j le_rfl) (AlgHom.id (A i₀) P) x = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [fA, DirectedSystem.map_self' (fun i j h => a i j h)]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcomp (P : Type v) [CommRing P] [Algebra (A i₀) P] (j k l : J) (hjk : j ≤ k) (hkl : k ≤ l)
      (x : A j.1 ⊗[A i₀] P) :
      Algebra.TensorProduct.map (fA k l hkl) (AlgHom.id (A i₀) P)
        (Algebra.TensorProduct.map (fA j k hjk) (AlgHom.id (A i₀) P) x) =
      Algebra.TensorProduct.map (fA j l (hjk.trans hkl)) (AlgHom.id (A i₀) P) x :=
    map_id_apply_map_id _ _ _ (fun x => DirectedSystem.map_map' (fun i j h => a i j h) hjk hkl x) x
  have : DirectedSystem (fun j : J => A j.1 ⊗[A i₀] B₀) fun j k h => aJ j k h :=
    ⟨fun j x => hself B₀ j x, fun _ _ _ hjk hkl x => hcomp B₀ _ _ _ hjk hkl x⟩
  have : DirectedSystem (fun j : J => A j.1 ⊗[A i₀] C₀) fun j k h => bJ j k h :=
    ⟨fun j x => hself C₀ j x, fun _ _ _ hjk hkl x => hcomp C₀ _ _ _ hjk hkl x⟩
  have hab (j k : J) (h : j ≤ k) :
      (bJ j k h).comp (algebraMap (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀)) =
        (algebraMap (A k.1 ⊗[A i₀] B₀) (A k.1 ⊗[A i₀] C₀)).comp (aJ j k h) := by
    exact map_id_comp_map_comm _ _
  -- the legs to the colimit
  let gA (j : J) : A j.1 →ₐ[A i₀] R := { ρ j.1 with commutes' := fun x => hρ i₀ j.1 j.2 x }
  let ρJ (j : J) : A j.1 ⊗[A i₀] B₀ →+* R ⊗[A i₀] B₀ :=
    (Algebra.TensorProduct.map (gA j) (AlgHom.id (A i₀) B₀)).toRingHom
  let σJ (j : J) : A j.1 ⊗[A i₀] C₀ →+* R ⊗[A i₀] C₀ :=
    (Algebra.TensorProduct.map (gA j) (AlgHom.id (A i₀) C₀)).toRingHom
  have hleg (P : Type v) [CommRing P] [Algebra (A i₀) P] (j k : J) (h : j ≤ k)
      (x : A j.1 ⊗[A i₀] P) :
      Algebra.TensorProduct.map (gA k) (AlgHom.id (A i₀) P)
        (Algebra.TensorProduct.map (fA j k h) (AlgHom.id (A i₀) P) x) =
      Algebra.TensorProduct.map (gA j) (AlgHom.id (A i₀) P) x :=
    map_id_apply_map_id _ _ _ (fun x => hρ j.1 k.1 h x) x
  have hρσJ (j : J) : (σJ j).comp (algebraMap (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀)) =
      (algebraMap (R ⊗[A i₀] B₀) (R ⊗[A i₀] C₀)).comp (ρJ j) := by
    exact map_id_comp_map_comm _ _
  -- the colimit conditions, from "tensor products commute with directed colimits"
  let _ (j : J) : Algebra (A j.1) R := (ρ j.1).toAlgebra
  have _ (j : J) : IsScalarTower (A i₀) (A j.1) R :=
    .of_algebraMap_eq fun x => (hρ i₀ j.1 j.2 x).symm
  have hcol (P : Type v) [CommRing P] [Algebra (A i₀) P] :=
    Stacks.ColimitPresentation.FPModules.isModuleColimit (J := J) (fun j k h => fA j k h)
      (R := R) (fun j k h x => hρ j.1 k.1 h x)
      (fun r => let ⟨j, hj, x, hx⟩ := exists_ge_rep a ρ hρ hρs i₀ r; ⟨⟨j, hj⟩, x, hx⟩)
      (fun j x hx => let ⟨k, hk, hk'⟩ := hρz j.1 x hx; ⟨⟨k, j.2.trans hk⟩, hk, hk'⟩) P
  have hcan (P : Type v) [CommRing P] [Algebra (A i₀) P] (j : J) (y : A j.1 ⊗[A i₀] P) :
      Stacks.FinitePresentation.ColimitDescent.canonMod (fun j : J => IsScalarTower.toAlgHom (A i₀)
        (A j.1) R) P j y =
        Algebra.TensorProduct.map (gA j) (AlgHom.id (A i₀) P) y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have htrans (P : Type v) [CommRing P] [Algebra (A i₀) P] (j k : J) (h : j ≤ k)
      (y : A j.1 ⊗[A i₀] P) :
      Stacks.FinitePresentation.ColimitDescent.transMod (fun j k (h : j ≤ k) => fA j k h) P h y =
        Algebra.TensorProduct.map (fA j k h) (AlgHom.id (A i₀) P) y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hs (P : Type v) [CommRing P] [Algebra (A i₀) P] (r : R ⊗[A i₀] P) :
      ∃ (j : J) (x : A j.1 ⊗[A i₀] P),
        Algebra.TensorProduct.map (gA j) (AlgHom.id (A i₀) P) x = r := by
    obtain ⟨j, y, hy⟩ := (hcol P).jointly_surjective r
    exact ⟨j, y, (hcan P j y).symm.trans hy⟩
  have hz (P : Type v) [CommRing P] [Algebra (A i₀) P] (j : J) (x : A j.1 ⊗[A i₀] P)
      (hx : Algebra.TensorProduct.map (gA j) (AlgHom.id (A i₀) P) x = 0) :
      ∃ (k : J) (h : j ≤ k), Algebra.TensorProduct.map (fA j k h) (AlgHom.id (A i₀) P) x = 0 := by
    obtain ⟨k, h, hk⟩ := (hcol P).exists_eq_of_canonMod_eq j x 0 (by
      rw [hcan, hcan, hx, map_zero])
    exact ⟨k, h, by rw [← htrans, hk, map_zero]⟩
  -- base change squares
  let _ : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  have : IsScalarTower (A i₀) B₀ C₀ := .of_algebraMap_eq fun x => (φ₀.commutes x).symm
  let _ (j : J) : Algebra B₀ (A j.1 ⊗[A i₀] B₀) := Algebra.TensorProduct.rightAlgebra
  let _ (j : J) : Algebra C₀ (A j.1 ⊗[A i₀] C₀) := Algebra.TensorProduct.rightAlgebra
  let _ (j : J) : Algebra B₀ (A j.1 ⊗[A i₀] C₀) :=
    ((algebraMap C₀ (A j.1 ⊗[A i₀] C₀)).comp (algebraMap B₀ C₀)).toAlgebra
  have _ (j : J) : IsScalarTower B₀ C₀ (A j.1 ⊗[A i₀] C₀) := .of_algebraMap_eq fun _ => rfl
  have _ (j : J) : IsScalarTower B₀ (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀) :=
    .of_algebraMap_eq fun x => by
      show (1 : A j.1) ⊗ₜ[A i₀] φ₀ x = Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀
        ((1 : A j.1) ⊗ₜ[A i₀] x)
      simp
  have hbc (j : J) : Algebra.IsPushout B₀ C₀ (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀) :=
    Algebra.IsPushout.tensorProduct_map_id fun _ => rfl
  have hfpJ (j : J) : Algebra.FinitePresentation (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀) := by
    have : Algebra.IsPushout B₀ (A j.1 ⊗[A i₀] B₀) C₀ (A j.1 ⊗[A i₀] C₀) := (hbc j).symm
    have : Algebra.FinitePresentation B₀ C₀ := hfp
    exact Algebra.FinitePresentation.equiv
      (Algebra.IsPushout.equiv B₀ (A j.1 ⊗[A i₀] B₀) C₀ (A j.1 ⊗[A i₀] C₀))
  have hpushJ (j k : J) (h : j ≤ k) : CategoryTheory.IsPushout
      (CommRingCat.ofHom (aJ j k h))
      (CommRingCat.ofHom (algebraMap (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀)))
      (CommRingCat.ofHom (algebraMap (A k.1 ⊗[A i₀] B₀) (A k.1 ⊗[A i₀] C₀)))
      (CommRingCat.ofHom (bJ j k h)) := by
    let : Algebra (A j.1 ⊗[A i₀] B₀) (A k.1 ⊗[A i₀] B₀) := (aJ j k h).toAlgebra
    let : Algebra (A j.1 ⊗[A i₀] C₀) (A k.1 ⊗[A i₀] C₀) := (bJ j k h).toAlgebra
    let : Algebra (A j.1 ⊗[A i₀] B₀) (A k.1 ⊗[A i₀] C₀) :=
      ((bJ j k h).comp (algebraMap (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀))).toAlgebra
    have : IsScalarTower (A j.1 ⊗[A i₀] B₀) (A k.1 ⊗[A i₀] B₀) (A k.1 ⊗[A i₀] C₀) :=
      .of_algebraMap_eq' (hab j k h)
    have : IsScalarTower (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀) (A k.1 ⊗[A i₀] C₀) :=
      .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower B₀ (A j.1 ⊗[A i₀] C₀) (A k.1 ⊗[A i₀] C₀) := .of_algebraMap_eq fun x => by
      show (1 : A k.1) ⊗ₜ[A i₀] φ₀ x = bJ j k h ((1 : A j.1) ⊗ₜ[A i₀] φ₀ x)
      simp [bJ]
    have : IsScalarTower C₀ (A j.1 ⊗[A i₀] C₀) (A k.1 ⊗[A i₀] C₀) := .of_algebraMap_eq fun x => by
      show (1 : A k.1) ⊗ₜ[A i₀] x = bJ j k h ((1 : A j.1) ⊗ₜ[A i₀] x)
      simp [bJ]
    have : IsScalarTower B₀ (A j.1 ⊗[A i₀] B₀) (A k.1 ⊗[A i₀] B₀) := .of_algebraMap_eq fun x => by
      show (1 : A k.1) ⊗ₜ[A i₀] x = aJ j k h ((1 : A j.1) ⊗ₜ[A i₀] x)
      simp [aJ]
    have : Algebra.IsPushout B₀ (A j.1 ⊗[A i₀] B₀) C₀ (A j.1 ⊗[A i₀] C₀) := (hbc j).symm
    have h1 : Algebra.IsPushout (A j.1 ⊗[A i₀] B₀) (A k.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀)
        (A k.1 ⊗[A i₀] C₀) :=
      (Algebra.IsPushout.comp_iff B₀ (A j.1 ⊗[A i₀] B₀) C₀ (T := A k.1 ⊗[A i₀] B₀)
        (S' := A j.1 ⊗[A i₀] C₀) (T' := A k.1 ⊗[A i₀] C₀)).mp (hbc k).symm
    exact CommRingCat.isPushout_iff_isPushout.mpr h1
  refine ⟨fun hR => ?_, fun hR => ?_⟩
  · obtain ⟨j, hj⟩ := Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_of_directed
      (A := fun j : J => A j.1 ⊗[A i₀] B₀) (B := fun j : J => A j.1 ⊗[A i₀] C₀) aJ bJ hab
      (R := R ⊗[A i₀] B₀) (S := R ⊗[A i₀] C₀) ρJ σJ (fun j k h x => hleg B₀ j k h x)
      (fun j k h x => hleg C₀ j k h x) hρσJ (hs B₀) (hz B₀) (hs C₀) (hz C₀) hpushJ hfpJ
    exact ⟨j.1, j.2, hj⟩
  · obtain ⟨j, hj⟩ := Algebra.Syntomic.exists_stage_of_directed
      (A := fun j : J => A j.1 ⊗[A i₀] B₀) (B := fun j : J => A j.1 ⊗[A i₀] C₀) aJ bJ hab
      (R := R ⊗[A i₀] B₀) (S := R ⊗[A i₀] C₀) ρJ σJ (fun j k h x => hleg B₀ j k h x)
      (fun j k h x => hleg C₀ j k h x) hρσJ (hs B₀) (hz B₀) (hs C₀) (hz C₀) hpushJ hfpJ
    exact ⟨j.1, j.2, hj⟩

/-- **Stacks 0C33, relative global complete intersections.** Let `A = colim_i A_i` be a directed
colimit of rings, let `0 ≤ i` be an index and `φ₀ : B₀ → C₀` a map of `A₀`-algebras with `C₀` of
finite presentation over `B₀`. If `A ⊗_{A₀} B₀ → A ⊗_{A₀} C₀` is a relative global complete
intersection, then so is `A_i ⊗_{A₀} B₀ → A_i ⊗_{A₀} C₀` for some `i ≥ 0`. -/
@[stacks 0C33 "The relative global complete intersection case. The colimit `A` is the ring `R`
with the cocone `ρ`, given elementwise: every element of `R` comes from a stage, and an element of
a stage dying in `R` dies at a later stage. The maps `A_i ⊗ B₀ → A_i ⊗ C₀` are
`Algebra.TensorProduct.map id φ₀`."]
theorem Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_tensorProduct
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    {A : ι → Type u} [∀ i, CommRing (A i)] (a : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A fun i j h => a i j h] {R : Type*} [CommRing R] (ρ : ∀ i, A i →+* R)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x) (hρs : ∀ r, ∃ i x, ρ i x = r)
    (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0)
    {i₀ : ι} {B₀ C₀ : Type v} [CommRing B₀] [CommRing C₀] [Algebra (A i₀) B₀] [Algebra (A i₀) C₀]
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation)
    (h : letI := (ρ i₀).toAlgebra
      letI := (Algebra.TensorProduct.map (AlgHom.id (A i₀) R) φ₀).toRingHom.toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection (R ⊗[A i₀] B₀) (R ⊗[A i₀] C₀)) :
    ∃ i, ∃ h : i₀ ≤ i, letI := (a i₀ i h).toAlgebra
      letI := (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A i)) φ₀).toRingHom.toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection (A i ⊗[A i₀] B₀) (A i ⊗[A i₀] C₀) :=
  (Algebra.TensorProduct.exists_stage_of_directed_aux a ρ hρ hρs hρz φ₀ hfp).1 h

/-- **Stacks 0C33, syntomic ring maps.** Let `A = colim_i A_i` be a directed colimit of rings,
let `0 ≤ i` be an index and `φ₀ : B₀ → C₀` a map of `A₀`-algebras with `C₀` of finite
presentation over `B₀`. If `A ⊗_{A₀} B₀ → A ⊗_{A₀} C₀` is syntomic, then so is
`A_i ⊗_{A₀} B₀ → A_i ⊗_{A₀} C₀` for some `i ≥ 0`. -/
@[stacks 0C33 "The syntomic case, with the conventions of the relative global complete
intersection case."]
theorem Algebra.Syntomic.exists_stage_tensorProduct
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    {A : ι → Type u} [∀ i, CommRing (A i)] (a : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A fun i j h => a i j h] {R : Type*} [CommRing R] (ρ : ∀ i, A i →+* R)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x) (hρs : ∀ r, ∃ i x, ρ i x = r)
    (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0)
    {i₀ : ι} {B₀ C₀ : Type v} [CommRing B₀] [CommRing C₀] [Algebra (A i₀) B₀] [Algebra (A i₀) C₀]
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation)
    (h : letI := (ρ i₀).toAlgebra
      letI := (Algebra.TensorProduct.map (AlgHom.id (A i₀) R) φ₀).toRingHom.toAlgebra
      Algebra.Syntomic (R ⊗[A i₀] B₀) (R ⊗[A i₀] C₀)) :
    ∃ i, ∃ h : i₀ ≤ i, letI := (a i₀ i h).toAlgebra
      letI := (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A i)) φ₀).toRingHom.toAlgebra
      Algebra.Syntomic (A i ⊗[A i₀] B₀) (A i ⊗[A i₀] C₀) :=
  (Algebra.TensorProduct.exists_stage_of_directed_aux a ρ hρ hρs hρz φ₀ hfp).2 h
