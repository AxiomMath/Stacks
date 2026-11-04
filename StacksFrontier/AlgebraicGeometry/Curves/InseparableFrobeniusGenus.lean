module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFrobeniusChainAssembly
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion

/-!
# Smoothness, global functions and genus under a purely inseparable morphism of curves

Let `k` be a field of characteristic `p > 0` and let `f : X ⟶ Y` be a nonconstant morphism of
proper nonsingular curves over `k`.  **Stacks 0CD0** asserts that if `X` is smooth, the global
regular functions on `X` are the constants and the extension of function fields `k(X)/k(Y)` is
purely inseparable, then `Y` is smooth, the global regular functions on `Y` are again the
constants, and `Y` has the same genus as `X`.

The proof is the one of the source.  By [Stacks, Tag 0CCZ] the target is the `n`-fold Frobenius
twist of `X`, that is, the base change of `X` along the `n`-fold absolute Frobenius of
`Spec k`; smoothness is then stable under base change, and the global functions and the genus
are preserved by an extension of the ground field, which is [Stacks, Tag 0BY9].

## Main results

* `AlgebraicGeometry.smooth_of_isPurelyInseparable_residueFieldMap`: the target is smooth.
* `AlgebraicGeometry.isIso_globalSections_of_isPurelyInseparable_residueFieldMap`: the global
  regular functions on the target are the constants.
* `AlgebraicGeometry.genus_eq_of_isPurelyInseparable_residueFieldMap`: the genera agree.

## Implementation notes

The extension of function fields is expressed by the homomorphism of residue fields at the
generic point of `X`, which for a dominant morphism of integral schemes is the extension of
function fields; `AlgebraicGeometry.isPurelyInseparable_functionFieldMap_iff_residueFieldMap`
identifies the two readings.  "The global regular functions are the constants" says that the
canonical homomorphism from the ground field to the global sections of the structure sheaf is an
isomorphism, the spelling of [Stacks, Tag 0BY9].  The three conclusions of the source are stated
separately, and the two that do not need it are stated without the hypothesis on the global
functions on `X`.

## References

* [Stacks Project, Tag 0CD0](https://stacks.math.columbia.edu/tag/0CD0)
* [Stacks Project, Tag 0CCZ](https://stacks.math.columbia.edu/tag/0CCZ)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- The target of a nonconstant purely inseparable morphism from a smooth proper nonsingular
curve over `k` to a proper nonsingular curve over `k` is the base change of the source along an
endomorphism of `k`, namely a power of the Frobenius.  This is the geometric content of
[Stacks, Tag 0CCZ] in the form in which Stacks 0CD0 uses it. -/
private theorem exists_isPullback_specMap_of_isPurelyInseparable
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY] [Smooth pX]
    (hXreg : IsRegular X) (hYreg : IsRegular Y)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (hnonconstant : (Set.range f).Nontrivial)
    (hpure : (f.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable) :
    ∃ (_ : Algebra k k) (g : Y ⟶ X),
      IsPullback g pY pX (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
  have hS : IsInCharacteristic (Spec (.of k)) p :=
    isInCharacteristic_spec k p (CharP.cast_eq_zero k p)
  obtain ⟨n, ⟨e, -, -⟩, -⟩ := existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist p hS pX pY
    hXreg hYreg f hf hnonconstant hpure
  let q := absoluteFrobeniusPow (Spec (.of k)) p hS n
  let φ : CommRingCat.of k ⟶ CommRingCat.of k := (Spec.fullyFaithful.preimage q).unop
  have hq : Spec.map φ = q := by simp [φ]
  have heiso : IsIso e.hom.left := by
    simpa using Functor.map_isIso (Over.forget (Spec (.of k))) e.hom
  let eX : (nFoldFrobeniusTwist (Spec (.of k)) p hS n (Over.mk pX)).left ≅ Y := asIso e.hom.left
  have hpbY : IsPullback (eX.inv ≫ pullback.fst pX q) pY pX (Spec.map φ) := by
    rw [hq]
    apply (IsPullback.of_hasPullback pX q).of_iso eX (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simpa [q, nFoldFrobeniusTwist, CategoryTheory.Over.pullback, eX] using (Over.w e.hom).symm
    · simp
    · simp
  let _ : Algebra k k := φ.hom.toAlgebra
  have halg : CommRingCat.ofHom (algebraMap k k) = φ := by ext; rfl
  exact ⟨_, eX.inv ≫ pullback.fst pX q, by rwa [halg]⟩

/-- **Stacks Project, Tag 0CD0, the smoothness of the target.** Let `f : X ⟶ Y` be a nonconstant
morphism of proper nonsingular curves over a field `k` of characteristic `p`.  If `X` is smooth
and the extension of function fields is purely inseparable, then `Y` is smooth: by
[Stacks, Tag 0CCZ] it is a base change of `X` along an endomorphism of the ground field, and
smoothness is stable under base change. -/
@[stacks 0CD0 "the smoothness of the target"]
theorem smooth_of_isPurelyInseparable_residueFieldMap
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY] [Smooth pX]
    (hXreg : IsRegular X) (hYreg : IsRegular Y)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (hnonconstant : (Set.range f).Nontrivial)
    (hpure : (f.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable) :
    Smooth pY := by
  obtain ⟨_, g, hpb⟩ := exists_isPullback_specMap_of_isPurelyInseparable p pX pY hXreg hYreg
    f hf hnonconstant hpure
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb inferInstance

/-- **Stacks Project, Tag 0CD0, the global regular functions on the target.** Let `f : X ⟶ Y` be
a nonconstant morphism of proper nonsingular curves over a field `k` of characteristic `p`.  If
`X` is smooth, the global regular functions on `X` are the constants, and the extension of
function fields is purely inseparable, then the global regular functions on `Y` are again the
constants. -/
@[stacks 0CD0 "the global regular functions on the target"]
theorem isIso_globalSections_of_isPurelyInseparable_residueFieldMap
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY] [Smooth pX]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop)]
    (hXreg : IsRegular X) (hYreg : IsRegular Y)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (hnonconstant : (Set.range f).Nontrivial)
    (hpure : (f.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop) := by
  obtain ⟨_, g, hpb⟩ := exists_isPullback_specMap_of_isPurelyInseparable p pX pY hXreg hYreg
    f hf hnonconstant hpure
  exact isIso_globalSections_baseChange k k g pY pX hpb

/-- **Stacks Project, Tag 0CD0, the genus of the target.** Let `f : X ⟶ Y` be a nonconstant
morphism of proper nonsingular curves over a field `k` of characteristic `p`.  If `X` is smooth
and the extension of function fields is purely inseparable, then `Y` has the same genus as `X`:
it is a base change of `X` along an extension of the ground field, and the genus is invariant
under such a base change. -/
@[stacks 0CD0 "the genus of the target"]
theorem genus_eq_of_isPurelyInseparable_residueFieldMap
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY] [Smooth pX]
    (hXreg : IsRegular X) (hYreg : IsRegular Y)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (hnonconstant : (Set.range f).Nontrivial)
    (hpure : (f.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable) :
    genus pY = genus pX := by
  obtain ⟨_, g, hpb⟩ := exists_isPullback_specMap_of_isPurelyInseparable p pX pY hXreg hYreg
    f hf hnonconstant hpure
  exact genus_baseChange k k g pY pX hpb

end AlgebraicGeometry

end
