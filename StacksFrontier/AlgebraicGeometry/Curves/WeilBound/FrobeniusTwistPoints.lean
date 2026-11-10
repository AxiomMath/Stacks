module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.WeilBound.FixedFieldPoints

/-!
# The Frobenius twist of the base change to an algebraically closed field

Let `X` be a scheme over a finite field `k` with `q = p ^ e` elements, `Ω` an algebraically
closed extension of `k` and `σ = (a ↦ a ^ q)` the `q`-Frobenius of `Ω`, a `k`-automorphism.
On `X_Ω = X ×_k Spec Ω` the automorphism `Ψ = 𝟙_X × Spec σ` is `q`-semilinear:
`Ψ ≫ g = g ≫ Spec σ` for the structure morphism `g : X_Ω ⟶ Spec Ω`. When `X` is locally of
finite type over `k`, the closed points of `X_Ω` fixed by `Ψ ^ m` are counted by the points of
`X` over an extension `K` of `k` of degree `m`:

`#{x ∈ X_Ω closed | Ψ^m x = x} = #X(K)`.

A closed point `x` of `X_Ω` is the image of a unique section `s_x` of `g`, and `x ↦ s_x ≫ pr₁`
identifies the closed points of `X_Ω` with `X(Ω)`. Under this identification `Ψ` becomes
precomposition with `Spec σ⁻¹`, so the fixed points of `Ψ ^ m` are the points of `X(Ω)` fixed by
`σ^{-m}`. The elements of `Ω` fixed by `σ^m` are the roots of `a ^ (q ^ m) = a`, which form the
image of any `k`-embedding `K → Ω`, and `AlgebraicGeometry.fixedFieldValuedPointsEquiv`
concludes.

## Main definitions

* `AlgebraicGeometry.WeilBound.frobeniusAlgEquiv`: `σ` as a `k`-algebra automorphism of `Ω`.
* `AlgebraicGeometry.WeilBound.frobeniusTwist`: `Ψ`.

## Main results

* `AlgebraicGeometry.WeilBound.frobeniusTwist_hom_comp_snd`: `Ψ ≫ g = g ≫ Spec σ`.
* `AlgebraicGeometry.WeilBound.natCard_fixed_frobeniusTwist`: the count of fixed points.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.WeilBound

open Stacks.EtaleCohomology

variable {k : Type u} [Field k] [Fintype k] (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
  (p : ℕ) [Fact p.Prime] [CharP Ω p] (e : ℕ) (hq : Fintype.card k = p ^ e)

/-- The `q`-Frobenius `a ↦ a ^ q` of `Ω`, `q = #k = p ^ e`, as a `k`-algebra automorphism. -/
def frobeniusAlgEquiv : Ω ≃ₐ[k] Ω :=
  { iterateFrobeniusEquiv Ω p e with
    commutes' := fun c => by
      change iterateFrobenius Ω p e (algebraMap k Ω c) = algebraMap k Ω c
      rw [iterateFrobenius_def, ← map_pow, ← hq, FiniteField.pow_card] }

/-- The Frobenius `σ` sends `a` to `a ^ p ^ e`. -/
theorem frobeniusAlgEquiv_apply (a : Ω) : frobeniusAlgEquiv Ω p e hq a = a ^ p ^ e := rfl

/-- As a ring homomorphism, `σ` is the iterated Frobenius `iterateFrobenius Ω p e`. -/
theorem frobeniusAlgEquiv_toRingHom :
    (frobeniusAlgEquiv Ω p e hq : Ω →+* Ω) = iterateFrobenius Ω p e := rfl

/-- The powers of the Frobenius: `σ ^ m` is `a ↦ a ^ (q ^ m)`. -/
theorem frobeniusAlgEquiv_pow_apply (m : ℕ) (a : Ω) :
    (frobeniusAlgEquiv Ω p e hq ^ m) a = a ^ (Fintype.card k) ^ m := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, AlgEquiv.mul_apply, frobeniusAlgEquiv_apply, ih, ← pow_mul, pow_succ, hq,
      ← pow_mul, mul_comm (p ^ e)]

/-- `σ⁻ᵐ` fixes `a` exactly when `a ^ (q ^ m) = a`. -/
private theorem frobeniusAlgEquiv_symm_pow_apply_eq_self_iff (m : ℕ) (a : Ω) :
    ((frobeniusAlgEquiv Ω p e hq).symm ^ m) a = a ↔ a ^ (Fintype.card k) ^ m = a := by
  rw [← AlgEquiv.aut_inv, inv_pow, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, eq_comm,
    frobeniusAlgEquiv_pow_apply]

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The structure morphism `Spec Ω ⟶ Spec k`. -/
abbrev baseMap (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] : Spec (.of Ω) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k Ω))

/-- `Spec σ` commutes with the structure morphism `Spec Ω ⟶ Spec k`. -/
theorem specMap_frobenius_comp_baseMap :
    baseMap k Ω ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom (frobeniusAlgEquiv Ω p e hq : Ω →+* Ω)) ≫ baseMap k Ω := by
  simp only [baseMap, Category.comp_id, ← Spec.map_comp]
  congr 1
  ext c
  exact ((frobeniusAlgEquiv Ω p e hq).commutes c).symm

/-- **The Frobenius twist** `Ψ = 𝟙_X × Spec σ` of `X_Ω = X ×_k Spec Ω`. -/
def frobeniusTwist : pullback f (baseMap k Ω) ≅ pullback f (baseMap k Ω) :=
  haveI : IsIso (Spec.map (CommRingCat.ofHom (frobeniusAlgEquiv Ω p e hq : Ω →+* Ω))) :=
    inferInstanceAs (IsIso (Spec.map
      ((frobeniusAlgEquiv Ω p e hq).toRingEquiv.toCommRingCatIso).hom))
  asIso (pullback.map f (baseMap k Ω) f (baseMap k Ω) (𝟙 X)
    (Spec.map (CommRingCat.ofHom (frobeniusAlgEquiv Ω p e hq : Ω →+* Ω))) (𝟙 _)
    (by simp) (specMap_frobenius_comp_baseMap Ω p e hq))

/-- `Ψ` commutes with the projection `X_Ω ⟶ X`. -/
@[reassoc (attr := simp)]
theorem frobeniusTwist_hom_comp_fst :
    (frobeniusTwist Ω p e hq f).hom ≫ pullback.fst f (baseMap k Ω) =
      pullback.fst f (baseMap k Ω) := by
  simp only [frobeniusTwist, asIso_hom, pullback.map]
  exact pullback.lift_fst _ _ _

/-- **`Ψ` is `q`-semilinear**: `Ψ ≫ g = g ≫ Spec σ`. -/
@[reassoc]
theorem frobeniusTwist_hom_comp_snd :
    (frobeniusTwist Ω p e hq f).hom ≫ pullback.snd f (baseMap k Ω) =
      pullback.snd f (baseMap k Ω) ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p e)) := by
  simp only [frobeniusTwist, asIso_hom, pullback.map, frobeniusAlgEquiv_toRingHom]
  exact pullback.lift_snd _ _ _

/-- `X(Ω)` is the set of sections of `X_Ω ⟶ Spec Ω`. -/
def sectionsEquiv :
    {s : Spec (.of Ω) ⟶ pullback f (baseMap k Ω) // s ≫ pullback.snd f (baseMap k Ω) = 𝟙 _} ≃
      fieldValuedPoints f Ω where
  toFun s := ⟨s.1 ≫ pullback.fst f (baseMap k Ω), by
    rw [Category.assoc, pullback.condition, ← Category.assoc, s.2, Category.id_comp]⟩
  invFun t := ⟨pullback.lift t.1 (𝟙 _) (by rw [t.2, Category.id_comp]), pullback.lift_snd _ _ _⟩
  left_inv s := Subtype.ext <| pullback.hom_ext (pullback.lift_fst _ _ _)
    ((pullback.lift_snd _ _ _).trans s.2.symm)
  right_inv t := Subtype.ext (pullback.lift_fst _ _ _)

/-- The base change `X_Ω = X ×_k Spec Ω`. -/
abbrev geometricBaseChange : Scheme.{u} := pullback f (baseMap k Ω)

variable [LocallyOfFiniteType f]

/-- The closed points of `X_Ω` are `X(Ω)`: a closed point is the image of a unique section. -/
def closedPointsEquiv : closedPoints (geometricBaseChange Ω f) ≃ fieldValuedPoints f Ω :=
  (pointEquivClosedPoint (pullback.snd f (baseMap k Ω))).symm.trans (sectionsEquiv Ω f)

omit [Fintype k] in
/-- The point of `X(Ω)` attached to a closed point `x` of `X_Ω` is `s_x ≫ pr₁`, where `s_x` is
the section of `X_Ω ⟶ Spec Ω` with image `x`. -/
theorem closedPointsEquiv_apply (x : closedPoints (geometricBaseChange Ω f)) :
    (closedPointsEquiv Ω f x).1 =
      pointOfClosedPoint (pullback.snd f (baseMap k Ω)) x.1 x.2 ≫ pullback.fst f (baseMap k Ω) :=
  rfl

omit [LocallyOfFiniteType f] in
/-- `Ψ` maps closed points of `X_Ω` to closed points. -/
theorem isClosed_frobeniusTwist (x : closedPoints (geometricBaseChange Ω f)) :
    (frobeniusTwist Ω p e hq f).hom.base x.1 ∈ closedPoints (geometricBaseChange Ω f) := by
  rw [mem_closedPoints_iff]
  simpa [Set.image_singleton] using (frobeniusTwist Ω p e hq f).hom.homeomorph.isClosedMap _ x.2

/-- On `X(Ω)`, the Frobenius twist is precomposition with `Spec σ⁻¹`. -/
theorem closedPointsEquiv_frobeniusTwist (x : closedPoints (geometricBaseChange Ω f)) :
    closedPointsEquiv Ω f ⟨_, isClosed_frobeniusTwist Ω p e hq f x⟩ =
      fieldValuedPointsPrecomp f (frobeniusAlgEquiv Ω p e hq).symm.toAlgHom
        (closedPointsEquiv Ω f x) := by
  have hs := pointOfClosedPoint_comp (pullback.snd f (baseMap k Ω)) x.1 x.2
  have hs' : (Spec.map (CommRingCat.ofHom ((frobeniusAlgEquiv Ω p e hq).symm : Ω →+* Ω)) ≫
      pointOfClosedPoint (pullback.snd f (baseMap k Ω)) x.1 x.2 ≫
        (frobeniusTwist Ω p e hq f).hom) ≫ pullback.snd f (baseMap k Ω) = 𝟙 _ := by
    rw [Category.assoc, Category.assoc, frobeniusTwist_hom_comp_snd,
      ← frobeniusAlgEquiv_toRingHom Ω p e hq, reassoc_of% hs, ← Spec.map_comp,
      ← Spec.map_id]
    congr 1
    ext a
    exact (frobeniusAlgEquiv Ω p e hq).symm_apply_apply a
  have heq : Spec.map (CommRingCat.ofHom ((frobeniusAlgEquiv Ω p e hq).symm : Ω →+* Ω)) ≫
      pointOfClosedPoint (pullback.snd f (baseMap k Ω)) x.1 x.2 ≫
        (frobeniusTwist Ω p e hq f).hom =
      pointOfClosedPoint (pullback.snd f (baseMap k Ω)) _
        (isClosed_frobeniusTwist Ω p e hq f x) :=
    ext_of_apply_closedPoint_eq (pullback.snd f (baseMap k Ω)) hs'
      (pointOfClosedPoint_comp _ _ _)
      ((congrArg (fun y => (frobeniusTwist Ω p e hq f).hom.base y)
        (pointOfClosedPoint_apply _ x.1 x.2 _)).trans
        (pointOfClosedPoint_apply _ _ (isClosed_frobeniusTwist Ω p e hq f x) _).symm)
  apply Subtype.ext
  simp only [fieldValuedPointsPrecomp, closedPointsEquiv_apply]
  rw [← heq]
  simp only [Category.assoc, frobeniusTwist_hom_comp_fst]
  rfl

omit [LocallyOfFiniteType f] in
/-- Every iterate `Ψ ^ m` maps closed points of `X_Ω` to closed points. -/
theorem isClosed_frobeniusTwist_iterate (m : ℕ) (x : closedPoints (geometricBaseChange Ω f)) :
    (frobeniusTwist Ω p e hq f).hom.base^[m] x.1 ∈ closedPoints (geometricBaseChange Ω f) := by
  induction m with
  | zero => exact x.2
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact isClosed_frobeniusTwist Ω p e hq f ⟨_, ih⟩

/-- The `m`-th iterate of the Frobenius twist on closed points, read on `X(Ω)`: precomposition
with `Spec σ^{-m}`. -/
theorem closedPointsEquiv_frobeniusTwist_iterate (m : ℕ)
    (x : closedPoints (geometricBaseChange Ω f)) :
    closedPointsEquiv Ω f ⟨_, isClosed_frobeniusTwist_iterate Ω p e hq f m x⟩ =
      fieldValuedPointsPrecomp f ((frobeniusAlgEquiv Ω p e hq).symm ^ m : Ω ≃ₐ[k] Ω).toAlgHom
        (closedPointsEquiv Ω f x) := by
  induction m with
  | zero =>
    apply Subtype.ext
    simp only [fieldValuedPointsPrecomp, pow_zero]
    change _ = Spec.map (𝟙 _) ≫ _
    rw [Spec.map_id, Category.id_comp]
    rfl
  | succ m ih =>
    have hpt : (⟨_, isClosed_frobeniusTwist_iterate Ω p e hq f (m + 1) x⟩ :
        closedPoints (geometricBaseChange Ω f)) =
        ⟨_, isClosed_frobeniusTwist Ω p e hq f
          ⟨_, isClosed_frobeniusTwist_iterate Ω p e hq f m x⟩⟩ :=
      Subtype.ext (Function.iterate_succ_apply' _ _ _)
    rw [hpt, closedPointsEquiv_frobeniusTwist, ih]
    apply Subtype.ext
    simp only [fieldValuedPointsPrecomp, ← Category.assoc, ← Spec.map_comp]
    congr 3
    ext a
    rw [pow_succ']
    rfl

/-- **The closed points of `X_Ω` fixed by `Ψ ^ m` are counted by `X(K)`**, for any extension
`K` of `k` of degree `m`. -/
theorem natCard_fixed_frobeniusTwist (K : Type u) [Field K] [Finite K] [Algebra k K]
    (m : ℕ) (hm : Module.finrank k K = m) :
    Nat.card {x : geometricBaseChange Ω f | IsClosed ({x} : Set (geometricBaseChange Ω f)) ∧
        (frobeniusTwist Ω p e hq f).hom.base^[m] x = x} =
      Nat.card (fieldValuedPoints f K) := by
  have := Fintype.ofFinite K
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let j : K →ₐ[k] Ω := IsAlgClosed.lift
  set σ := frobeniusAlgEquiv Ω p e hq
  have hcardK : Fintype.card K = Fintype.card k ^ m := by
    rw [← hm]
    exact Module.card_eq_pow_finrank
  have hj : ∀ c : K, (σ.symm ^ m) (j c) = j c := fun c =>
    (frobeniusAlgEquiv_symm_pow_apply_eq_self_iff Ω p e hq m _).2
      (by rw [← map_pow, ← hcardK, FiniteField.pow_card])
  have hτ : ∀ a : Ω, (σ.symm ^ m).toAlgHom a = a → a ∈ Set.range j := fun a ha =>
    mem_range_of_pow_card_eq j.toRingHom (by
      rw [hcardK]
      exact (frobeniusAlgEquiv_symm_pow_apply_eq_self_iff Ω p e hq m a).1 ha)
  rw [Nat.card_congr (fixedFieldValuedPointsEquiv f j (σ.symm ^ m).toAlgHom hj hτ)]
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨closedPointsEquiv Ω f ⟨x.1, x.2.1⟩, ?_⟩
      invFun := fun t => ⟨((closedPointsEquiv Ω f).symm t.1).1,
        ((closedPointsEquiv Ω f).symm t.1).2, ?_⟩
      left_inv := fun x => by simp
      right_inv := fun t => Subtype.ext ((congrArg (closedPointsEquiv Ω f)
        (Subtype.coe_eta _ _)).trans (Equiv.apply_symm_apply _ _)) }
  · rw [← closedPointsEquiv_frobeniusTwist_iterate Ω p e hq f m
      ⟨x.1, mem_closedPoints_iff.2 x.2.1⟩]
    congr 2
    exact x.2.2
  · set y := (closedPointsEquiv Ω f).symm t.1
    have h := closedPointsEquiv_frobeniusTwist_iterate Ω p e hq f m y
    rw [Equiv.apply_symm_apply, t.2] at h
    exact congrArg Subtype.val ((closedPointsEquiv Ω f).injective
      (h.trans (Equiv.apply_symm_apply _ _).symm))

end AlgebraicGeometry.WeilBound

end
