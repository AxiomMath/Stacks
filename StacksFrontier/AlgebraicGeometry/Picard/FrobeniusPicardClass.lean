module

public import StacksFrontier.AlgebraicGeometry.Frobenius
public import StacksFrontier.AlgebraicGeometry.Picard.FirstCohomologyNaturality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive

/-!
# Pullback along the absolute Frobenius is multiplication by `p` on the Picard group

Let `X` be a scheme in characteristic `p` and let `F : X ⟶ X` be its absolute Frobenius. Then
pullback along `F` is multiplication by `p` on `Pic(X)`; this is the Picard-group form of the
isomorphism `F^* L ≅ L ^ ⊗ p`. Under the identification of `Pic(X)` with the first cohomology of
the sheaf of units ([Stacks, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)), this follows
from the fact that on the sheaf of units the absolute Frobenius induces `p` times the map induced
by the identity.

## Main results

* `Stacks.Picard.unitsPushforwardMap_absoluteFrobenius`: on the sheaf of units, the absolute
  Frobenius induces `p` times the map induced by the identity.
* `Stacks.Picard.schemePullbackClass_absoluteFrobenius`: pullback along the absolute Frobenius
  is multiplication by `p` on the Picard group.

## References

* [Stacks Project, Tag 03SM](https://stacks.math.columbia.edu/tag/03SM)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.Frobenius
open Stacks.Cohomology.Generators (unitsSheaf)
open Stacks.Cohomology.LerayLowDegree (abelianCohomology abelianEdgeMap)
open Stacks.Picard.FirstCohomology (h1UnitsAddEquivPicard h1UnitsAddEquivPicard_naturality)
open Stacks.GlueSquishUnits (unitsPushforwardMap unitsPushforwardMap_app)

universe u

namespace Stacks.Picard

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **On the sheaf of units, the absolute Frobenius induces `p` times the map induced by the
identity.** Both maps land in the pushforward of the sheaf of units along the identity of the
underlying space, and on sections over `U` they are `s ↦ s ^ p` and `s ↦ s`. -/
theorem unitsPushforwardMap_absoluteFrobenius :
    unitsPushforwardMap (absoluteFrobenius X p hX) = (p : ℤ) • unitsPushforwardMap (𝟙 X) := by
  apply Sheaf.hom_ext
  ext U s
  have hF := unitsPushforwardMap_app (absoluteFrobenius X p hX) U.unop (Additive.toMul s)
  have hI := unitsPushforwardMap_app (𝟙 X) U.unop (Additive.toMul s)
  refine hF.trans (Eq.trans ?_ (congrArg ((p : ℤ) • ·) hI).symm)
  change _ = ((p : ℤ) • Additive.ofMul (Units.map ((𝟙 X : X ⟶ X).app U.unop).hom.toMonoidHom
    (Additive.toMul s)) : Additive (Γ(X, U.unop))ˣ)
  rw [← ofMul_zpow]
  apply congrArg Additive.ofMul
  ext
  simp only [zpow_natCast, Units.val_pow_eq_pow_val, Units.coe_map, Scheme.Hom.id_app]
  exact absoluteFrobenius_app_apply X p hX _ _

/-- **Pullback along the absolute Frobenius is multiplication by `p` on the Picard group.**

This is the Picard-group form of the isomorphism `F^* L ≅ L ^ ⊗ p`. -/
theorem schemePullbackClass_absoluteFrobenius (x : ofScheme X) :
    schemePullbackClass (absoluteFrobenius X p hX) x = (p : ℤ) • x := by
  obtain ⟨c, rfl⟩ := (h1UnitsAddEquivPicard X).surjective x
  have hF := h1UnitsAddEquivPicard_naturality (absoluteFrobenius X p hX) c
  have hI := h1UnitsAddEquivPicard_naturality (𝟙 X) c
  have hm : (abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap (absoluteFrobenius X p hX)) =
      (p : ℤ) • (abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap (𝟙 X)) :=
    (congrArg (fun g => (abelianCohomology.{u, u} (X : TopCat) ⊤ 1).map g)
      (unitsPushforwardMap_absoluteFrobenius X p hX)).trans (Functor.map_zsmul _)
  have key : (abelianEdgeMap.{u, u} (absoluteFrobenius X p hX).base 1).app
        (unitsSheaf X.toRingedSpace)
        ((abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap (absoluteFrobenius X p hX)) c) =
      (p : ℤ) • (abelianEdgeMap.{u, u} (𝟙 X : X ⟶ X).base 1).app (unitsSheaf X.toRingedSpace)
        ((abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap (𝟙 X)) c) := by
    rw [hm]
    exact map_zsmul ((abelianEdgeMap.{u, u} (𝟙 X : X ⟶ X).base 1).app
      (unitsSheaf X.toRingedSpace)).hom (p : ℤ) _
  change schemePullbackClassHom (absoluteFrobenius X p hX) _ = _
  rw [← hF, key, map_zsmul, hI]
  exact congrArg _ (schemePullbackClass_id X _)

end Stacks.Picard

end
