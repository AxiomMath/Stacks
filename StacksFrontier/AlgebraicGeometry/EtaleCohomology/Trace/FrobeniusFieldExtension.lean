module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion

/-!
# The geometric Frobenius over a finite extension of the base field

Let `k` be a finite field with `q = p ^ f` elements, `Y` a scheme over `k`, `k'` an extension of
`k` with `q ^ m` elements and `k̄` an extension of `k'`.  The base change `Y' = Y ×_k k'` is a
scheme over `k'`, and its geometric fibre `Y'_{k̄} = Y' ×_{k'} k̄` is canonically the geometric
fibre `Y_{k̄} = Y ×_k k̄` of `Y`: two cartesian squares paste to one.  Under this identification
the base change `π̄_{Y'} = π_{Y'} × id` of the geometric Frobenius of `Y'` over `k'` is the `m`-th
power of `π̄_Y = π_Y × id`: both are the `f m`-fold absolute Frobenius on the first factor and the
identity on the second.

This is the scheme-theoretic input to the proof of [Stacks, Tag 03V0], which applies the trace
formula of Tag 03V2 to `X ×_k k_n` over the extension `k_n` of degree `n`, where `π_{X}^n` is the
Frobenius of the extension.

## Main definitions

* `Stacks.EtaleCohomology.extensionOver`: `Y' = Y ×_k k'` as a scheme over `k'`.
* `Stacks.EtaleCohomology.fieldBaseChangeExtensionIso`: `Y'_{k̄} ≅ Y_{k̄}`.
* `Stacks.EtaleCohomology.geometricFrobeniusBaseChangePow`: the `m`-th power of `π̄_Y`.

## Main results

* `Stacks.EtaleCohomology.geometricFrobeniusBaseChange_extension_comp_hom`: under
  `Y'_{k̄} ≅ Y_{k̄}`, the Frobenius `π̄_{Y'}` of `Y'` over `k'` is the `m`-th power of `π̄_Y`.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
* [Stacks Project, Tag 03SQ](https://stacks.math.columbia.edu/tag/03SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Extension

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (k' : Type u) [Field k'] [Algebra k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]

/-- The base change `Y' = Y ×_k k'` of a scheme over `k`, as a scheme over `k'`. -/
abbrev extensionOver : Over (Spec (.of k')) :=
  Over.mk (pullback.snd Y.hom (specAlgebraMap k k'))

/-- The projection `Y' = Y ×_k k' ⟶ Y`. -/
abbrev extensionProj : (extensionOver Y k').left ⟶ Y.left :=
  pullback.fst Y.hom (specAlgebraMap k k')

omit [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar] in
include kbar in
/-- `Spec k̄ ⟶ Spec k' ⟶ Spec k` is the structure morphism of `k̄` over `k`. -/
lemma specAlgebraMap_comp_specAlgebraMap [Algebra k kbar] [Algebra k' kbar]
    [IsScalarTower k k' kbar] :
    specAlgebraMap k' kbar ≫ specAlgebraMap k k' = specAlgebraMap k kbar := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The two cartesian squares `Y'_{k̄} → Y' → Y` over `Spec k̄ → Spec k' → Spec k` paste to the
cartesian square defining `Y_{k̄}`. -/
lemma isPullback_extension :
    IsPullback (pullback.fst (extensionOver Y k').hom (specAlgebraMap k' kbar) ≫
        extensionProj Y k') (pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar))
      Y.hom (specAlgebraMap k kbar) := by
  have h := IsPullback.paste_horiz
    (IsPullback.of_hasPullback (extensionOver Y k').hom (specAlgebraMap k' kbar))
    (IsPullback.of_hasPullback Y.hom (specAlgebraMap k k'))
  rwa [specAlgebraMap_comp_specAlgebraMap k' kbar] at h

/-- **`Y'_{k̄} ≅ Y_{k̄}`**: the geometric fibre of `Y' = Y ×_k k'` over `k'` is the geometric fibre
of `Y` over `k`. -/
def fieldBaseChangeExtensionIso :
    fieldBaseChange (extensionOver Y k') kbar ≅ fieldBaseChange Y kbar :=
  (isPullback_extension Y k' kbar).isoPullback

/-- The isomorphism `Y'_{k̄} ≅ Y_{k̄}` followed by the projection `Y_{k̄} ⟶ Y` is the projection
`Y'_{k̄} ⟶ Y'` followed by `Y' ⟶ Y`. -/
@[reassoc (attr := simp)]
lemma fieldBaseChangeExtensionIso_hom_fst :
    (fieldBaseChangeExtensionIso Y k' kbar).hom ≫ pullback.fst Y.hom (specAlgebraMap k kbar) =
      pullback.fst (extensionOver Y k').hom (specAlgebraMap k' kbar) ≫ extensionProj Y k' :=
  IsPullback.isoPullback_hom_fst _

/-- The isomorphism `Y'_{k̄} ≅ Y_{k̄}` commutes with the structure morphisms to `Spec k̄`. -/
@[reassoc (attr := simp)]
lemma fieldBaseChangeExtensionIso_hom_snd :
    (fieldBaseChangeExtensionIso Y k' kbar).hom ≫ pullback.snd Y.hom (specAlgebraMap k kbar) =
      pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar) :=
  IsPullback.isoPullback_hom_snd _

end Extension

section Frobenius

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The `m`-th power `π̄_Y ^ m` of the base change `π̄_Y = π_Y × id` of the geometric Frobenius. -/
abbrev geometricFrobeniusBaseChangePow (m : ℕ) : fieldBaseChange Y kbar ⟶ fieldBaseChange Y kbar :=
  End.asHom ((End.of (geometricFrobeniusBaseChange Y kbar p q hcard)) ^ m)

/-- `π̄_Y ^ (m + 1) = π̄_Y ≫ π̄_Y ^ m`. -/
lemma geometricFrobeniusBaseChangePow_succ (m : ℕ) :
    geometricFrobeniusBaseChangePow Y kbar p q hcard (m + 1) =
      geometricFrobeniusBaseChange Y kbar p q hcard ≫
        geometricFrobeniusBaseChangePow Y kbar p q hcard m := by
  simp only [pow_succ, End.mul_def]

/-- `π̄_Y ^ m` lies over the `q m`-fold absolute Frobenius of `Y`. -/
@[reassoc]
lemma geometricFrobeniusBaseChangePow_fst (m : ℕ) :
    geometricFrobeniusBaseChangePow Y kbar p q hcard m ≫
        pullback.fst Y.hom (specAlgebraMap k kbar) =
      pullback.fst Y.hom (specAlgebraMap k kbar) ≫
        absoluteFrobeniusPow Y.left p (isInCharacteristic_of_over Y) (q * m) := by
  induction m with
  | zero =>
      rw [Nat.mul_zero, absoluteFrobeniusPow_zero]
      simp only [pow_zero]
      rfl
  | succ m ih =>
      rw [geometricFrobeniusBaseChangePow_succ, Category.assoc, ih,
        geometricFrobeniusBaseChange_comp_fst_assoc, geometricFrobenius_left, Nat.mul_succ]
      simp only [absoluteFrobeniusPow, pow_add, End.mul_def]

/-- `π̄_Y ^ m` is the identity on the second factor. -/
@[reassoc]
lemma geometricFrobeniusBaseChangePow_snd (m : ℕ) :
    geometricFrobeniusBaseChangePow Y kbar p q hcard m ≫
        pullback.snd Y.hom (specAlgebraMap k kbar) =
      pullback.snd Y.hom (specAlgebraMap k kbar) := by
  induction m with
  | zero =>
      simp only [pow_zero]
      rfl
  | succ m ih =>
      rw [geometricFrobeniusBaseChangePow_succ, Category.assoc, ih,
        geometricFrobeniusBaseChange_comp_snd]

variable (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [CharP k' p] [Algebra k' kbar]
  [IsScalarTower k k' kbar] (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * m))

/-- **The Frobenius of the extension is the `m`-th power of the Frobenius.**  Under
`Y'_{k̄} ≅ Y_{k̄}`, the base change `π̄_{Y'}` of the geometric Frobenius of `Y' = Y ×_k k'` over
the field `k'` with `q ^ m` elements is `π̄_Y ^ m`. -/
theorem geometricFrobeniusBaseChange_extension_comp_hom :
    geometricFrobeniusBaseChange (extensionOver Y k') kbar p (q * m) hcard' ≫
        (fieldBaseChangeExtensionIso Y k' kbar).hom =
      (fieldBaseChangeExtensionIso Y k' kbar).hom ≫
        geometricFrobeniusBaseChangePow Y kbar p q hcard m := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, fieldBaseChangeExtensionIso_hom_fst,
      geometricFrobeniusBaseChangePow_fst, fieldBaseChangeExtensionIso_hom_fst_assoc,
      geometricFrobeniusBaseChange_comp_fst_assoc, geometricFrobenius_left]
    congr 1
    exact absoluteFrobeniusPow_naturality (extensionProj Y k') p _ _ (q * m)
  · rw [Category.assoc, Category.assoc, fieldBaseChangeExtensionIso_hom_snd,
      geometricFrobeniusBaseChangePow_snd, fieldBaseChangeExtensionIso_hom_snd,
      geometricFrobeniusBaseChange_comp_snd]

end Frobenius

end Stacks.EtaleCohomology

end
