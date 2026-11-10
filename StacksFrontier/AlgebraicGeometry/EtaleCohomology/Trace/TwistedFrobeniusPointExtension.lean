module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkPointEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageStalkEnd
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPointExtension

/-!
# Twisted traces of Frobenius at a point above a point

Let `g : X' ⟶ X`, `F` an ℓ-adic sheaf on `X` and `ψ` an endomorphism of `F`. The identification of
the stalk of `g⁻¹F` at `ȳ` with the stalk of `F` at `g(ȳ)` is natural in `F`, so it carries
`g⁻¹ψ` to `ψ`. If `y` lies over `x = g(y)` with `#κ(y) = #κ(x) ^ (e + 1)`, then

`Tr(g⁻¹ψ ∘ π_yᵏ | (g⁻¹F)_ȳ ⊗ ℚ_ℓ) = Tr(ψ ∘ π_x^{(e + 1) k} | F_x̄ ⊗ ℚ_ℓ)`,

the twisted form of `LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow`.

## Main results

* `inverseImageStalkEquiv_stalkMap`
* `LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkFrobenius_inverseImage`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- If `L` intertwines `A` with `A'` and `B` with `B'`, it intertwines `A ∘ Bᵏ` with `A' ∘ B'ᵏ`. -/
public theorem comp_pow_comp_of_comm {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (L : V →ₗ[R] W) (A B : V →ₗ[R] V) (A' B' : W →ₗ[R] W)
    (hA : L ∘ₗ A = A' ∘ₗ L) (hB : L ∘ₗ B = B' ∘ₗ L) (k : ℕ) :
    L ∘ₗ (A ∘ₗ B ^ k) = (A' ∘ₗ B' ^ k) ∘ₗ L := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero, Module.End.one_eq_id, Module.End.one_eq_id, LinearMap.comp_id,
        LinearMap.comp_id, hA]
  | succ k ih =>
      refine LinearMap.ext fun v => ?_
      have h1 := LinearMap.congr_fun ih (B v)
      have h2 := LinearMap.congr_fun hB v
      simp only [LinearMap.comp_apply, pow_succ, Module.End.mul_apply] at h1 h2 ⊢
      rw [h1, h2]

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- **The stalk of the inverse image is natural in the sheaf.** -/
public theorem inverseImageStalkEquiv_stalkMap {F G : LAdicSheaf B Y ℓ} (φ : F ⟶ G)
    (x : GeometricPoint X.obj) (v : LAdicSheaf.stalk B X ℓ (LAdicSheaf.inverseImage f F) x) :
    inverseImageStalkEquiv B f G x
        (LAdicSheaf.stalkMap (LAdicSheaf.inverseImageMap f φ) x v) =
      LAdicSheaf.stalkMap φ (x.map (B.inclusion.map f)) (inverseImageStalkEquiv B f F x v) :=
  let : ∀ n : ℕ, HasProducts.{u} (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :=
    fun _ _ => ModuleCat.hasLimitsOfShape
  Subtype.ext (funext fun n => congrArg (fun g => g.hom (v.1 n))
    ((smallEtalePullbackSheafFiberIso B f x (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).hom.naturality
      (φ.app n)))

/-- The rational stalks of `f⁻¹F` and of `F` intertwine `f⁻¹φ` and `φ`. -/
public theorem rationalInverseImageStalkEquiv_rationalStalkMap {F G : LAdicSheaf B Y ℓ}
    (φ : F ⟶ G) (x : GeometricPoint X.obj) :
    (rationalInverseImageStalkEquiv B f G x).toLinearMap ∘ₗ
        LAdicSheaf.rationalStalkMap (LAdicSheaf.inverseImageMap f φ) x =
      LAdicSheaf.rationalStalkMap φ (x.map (B.inclusion.map f)) ∘ₗ
        (rationalInverseImageStalkEquiv B f F x).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun c v => ?_
  change (rationalInverseImageStalkEquiv B f G x) (c ⊗ₜ LAdicSheaf.stalkMap
      (LAdicSheaf.inverseImageMap f φ) x v) = c ⊗ₜ LAdicSheaf.stalkMap φ _
        (inverseImageStalkEquiv B f F x v)
  exact congrArg (c ⊗ₜ ·) (inverseImageStalkEquiv_stalkMap B f φ x v)

/-- **The twisted trace of Frobenius at a point above a point.** If `y` is a point of `X` with
finite residue field over `f(y)`, with `#κ(y) = #κ(f(y)) ^ (e + 1)`, then
`Tr(f⁻¹ψ ∘ π_yᵏ | (f⁻¹F)_ȳ ⊗ ℚ_ℓ) = Tr(ψ ∘ π_{f(y)}^{(e + 1) k} | F ⊗ ℚ_ℓ)`. -/
public theorem LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkFrobenius_inverseImage
    (F : LAdicSheaf.{u, u + 1} B Y ℓ) (ψ : F ⟶ F) (y : X.obj) (hy : Finite (X.obj.residueField y))
    (hx : Finite (Y.obj.residueField ((B.inclusion.map f).base y))) (e : ℕ)
    (he : Nat.card (X.obj.residueField y) =
      Nat.card (Y.obj.residueField ((B.inclusion.map f).base y)) ^ (e + 1)) (k : ℕ) :
    LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkMap (LAdicSheaf.inverseImageMap f ψ) (geometricPointAt X.obj y) ∘ₗ
          LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.inverseImage f F) y hy ^ k) =
      LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkMap ψ (geometricPointAt Y.obj ((B.inclusion.map f).base y)) ∘ₗ
          LAdicSheaf.rationalStalkFrobenius B Y ℓ F ((B.inclusion.map f).base y) hx ^
            ((e + 1) * k)) := by
  have := hy
  have := hx
  have : Finite ((B.inclusion.obj X).residueField y) := hy
  have : Finite ((B.inclusion.obj Y).residueField ((B.inclusion.map f).base y)) := hx
  let R := rationalInverseImageStalkEquiv B f F (geometricPointAt X.obj y)
  have h₁ := trace_eq_of_linearEquiv_comm R _ _
    (comp_pow_comp_of_comm R.toLinearMap _ _ _ _
      (rationalInverseImageStalkEquiv_rationalStalkMap B f ψ (geometricPointAt X.obj y))
      (rationalInverseImageStalkEquiv_rationalStalkEnd B f F (geometricPointAt X.obj y)
        (frobeniusPointHom X.obj y)) k)
  change LinearMap.trace ℚ_[ℓ] _ (_ ∘ₗ LAdicSheaf.rationalStalkEnd B X ℓ
      (LAdicSheaf.inverseImage f F) (frobeniusPointHom X.obj y) ^ k) = LinearMap.trace ℚ_[ℓ] _
    (_ ∘ₗ LAdicSheaf.rationalStalkEnd B Y ℓ F
      (frobeniusPointHom Y.obj ((B.inclusion.map f).base y)) ^ ((e + 1) * k))
  refine h₁.trans ((LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkEnd_eq_of_comm B Y ℓ F
    (residueClosurePointHom (B.inclusion.map f) y) ψ _ _
    (frobeniusPointHom_iterate_comm (B.inclusion.map f) y e he) k).trans ?_)
  rw [LAdicSheaf.rationalStalkEnd_iterate, ← pow_mul]
  rfl

/-- `LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkFrobenius_inverseImage` with the exponent
on `Y` given by an equation `(e + 1) * k = p`. -/
public theorem LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkFrobenius_inverseImage_of_eq
    (F : LAdicSheaf.{u, u + 1} B Y ℓ) (ψ : F ⟶ F) (y : X.obj) (hy : Finite (X.obj.residueField y))
    (hx : Finite (Y.obj.residueField ((B.inclusion.map f).base y))) (e : ℕ)
    (he : Nat.card (X.obj.residueField y) =
      Nat.card (Y.obj.residueField ((B.inclusion.map f).base y)) ^ (e + 1)) (k p : ℕ)
    (hp : (e + 1) * k = p) :
    LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkMap (LAdicSheaf.inverseImageMap f ψ) (geometricPointAt X.obj y) ∘ₗ
          LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.inverseImage f F) y hy ^ k) =
      LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkMap ψ (geometricPointAt Y.obj ((B.inclusion.map f).base y)) ∘ₗ
          LAdicSheaf.rationalStalkFrobenius B Y ℓ F ((B.inclusion.map f).base y) hx ^ p) := by
  subst hp
  exact LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkFrobenius_inverseImage B f F ψ y hy hx
    e he k

end Stacks.EtaleCohomology

end
