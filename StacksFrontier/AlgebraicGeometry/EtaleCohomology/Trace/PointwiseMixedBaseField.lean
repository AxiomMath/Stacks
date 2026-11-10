module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedSheaf

/-!
# Pointwise mixedness over a finite extension of the base field

Let `X` be a scheme of finite type over a finite field `k'`, viewed also over a subfield `k` with
`[k' : k] = d`. A closed point `x` has `[κ(x) : k] = d · [κ(x) : k']`, so with `q' = q ^ d` the
absolute values `q' ^ (deg_{k'} x · w / 2)` and `q ^ (deg_k x · w / 2)` agree: an ℓ-adic sheaf is
pointwise `ι`-mixed of weights `≤ w` over `k` exactly when it is so over `k'`. This is how the
weights of the fibre `X_y` of a morphism over a closed point `y` (a scheme over `κ(y)`) are
compared with the weights over `k` in the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) to curves.

## Main results

* `Stacks.EtaleCohomology.fieldToResidue_comp_specMap`.
* `Stacks.EtaleCohomology.residueDegree_comp_specMap`.
* `Stacks.EtaleCohomology.LAdicSheaf.IsPointwiseMixedOfWeightLE.of_comp_specMap`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- The map from the base field `k` to a residue field of `X`, along `f' ≫ Spec.map φ`, is `φ`
followed by the map from `k'`. -/
theorem fieldToResidue_comp_specMap {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    (f' : X ⟶ Spec (.of k')) (φ : CommRingCat.of k ⟶ CommRingCat.of k') (x : X) :
    fieldToResidue (f' ≫ Spec.map φ) x = φ ≫ fieldToResidue f' x := by
  unfold fieldToResidue fieldToStalk
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  rw [← Category.assoc (Scheme.ΓSpecIso _).inv (Scheme.Hom.appTop (Spec.map φ)),
    ← Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc]

/-- **The degree of a closed point over a subfield**: `[κ(x) : k] = [k' : k] · [κ(x) : k']`. -/
theorem residueDegree_comp_specMap {k k' : Type u} [Field k] [Field k'] [Finite k']
    [Algebra k k'] {X : Scheme.{u}} (f' : X ⟶ Spec (.of k'))
    [LocallyOfFiniteType f'] (x : X) (hx : IsClosed ({x} : Set X)) :
    residueDegree (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) x =
      Module.finrank k k' * residueDegree f' x := by
  let : Algebra k' (X.residueField x) := (fieldToResidue f' x).hom.toAlgebra
  let : Algebra k (X.residueField x) :=
    (fieldToResidue (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) x).hom.toAlgebra
  have : IsScalarTower k k' (X.residueField x) := IsScalarTower.of_algebraMap_eq fun c => by
    change (fieldToResidue (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) x).hom c =
      (fieldToResidue f' x).hom (algebraMap k k' c)
    rw [fieldToResidue_comp_specMap]
    rfl
  have := finite_residueField f' x hx
  have : Module.Finite k' (X.residueField x) := Module.Finite.of_finite
  exact (Module.finrank_mul_finrank k k' (X.residueField x)).symm

section LAdic

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- **Pointwise mixedness over a finite extension of the base field.** If `X` is locally of finite
type over `k'` and over `k`, and `F` is pointwise `ι`-mixed of weights `≤ w` over `k` (with `q`
elements), then `F` is pointwise `ι`-mixed of weights `≤ w` over `k'`, with `q ^ [k' : k]`
elements. -/
theorem LAdicSheaf.IsPointwiseMixedOfWeightLE.of_comp_specMap {k k' : Type u} [Field k]
    [Finite k] [Field k'] [Finite k'] [Algebra k k'] (f' : X.1 ⟶ Spec (.of k'))
    [LocallyOfFiniteType f']
    [LocallyOfFiniteType (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))]
    {F : LAdicSheaf B X ℓ} {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {w : ℤ}
    (hF : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ
      (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) F q ι w) :
    LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f' F (q ^ Module.finrank k k') ι w := by
  intro y z hz
  obtain ⟨w', hw', hz'⟩ := hF y z hz
  refine ⟨w', hw', hz'.trans ?_⟩
  rw [residueDegree_comp_specMap f' y.1 y.2]
  push_cast
  rw [← Real.rpow_natCast (q : ℝ), ← Real.rpow_mul (Nat.cast_nonneg q)]
  ring_nf

end LAdic

end Stacks.EtaleCohomology
