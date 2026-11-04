module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.RationalIntersectionRing
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.Factorization
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin map of a morphism of smooth schemes as a map of rational Chow rings

Let `k` be a field and let `f : X ⟶ Y` be a morphism of schemes over `k`, smooth, separated and
quasi-compact over `k`. Then `X` and `Y` are as in Stacks 0FEY (Noetherian, regular, with affine
diagonal and bounded `δ`), so `CH^*(X) ⊗ 𝐐` and `CH^*(Y) ⊗ 𝐐` carry the intersection products of
Section 0FEX (`Stacks.Chow.RationalIntersectionRing`), the Gysin map `f^!` of Stacks 0FF3 exists
(Stacks 0FFB) and Stacks 0FF9 says that it is multiplicative. This file packages `f^!` as a ring
homomorphism and records the compatibility of Chern classes with it that Stacks 0FF8 gives,

  `f^!(ch(α) ∩ [Y]) = ch(f^*α) ∩ [X]`   for `α ∈ K_0(Vect(Y)) ⊗ 𝐐`.

## Main definitions

* `Stacks.Chow.smoothGysinRingHom` — `f^! : CH^*(Y) ⊗ 𝐐 ⟶ CH^*(X) ⊗ 𝐐` as a ring homomorphism.

## Main results

* `Stacks.Chow.isNoetherian_of_quasiCompact_fieldChowSituation`,
  `Stacks.Chow.isAffineHom_diagonal_of_isSeparated_fieldChowSituation` — the hypotheses of
  Stacks 0FEY for a scheme quasi-compact and separated over `k`.
* `Stacks.Chow.smoothGysinRingHom_rationalChernCharacterCap` — `f^!(ch(α) ∩ [Y]) = ch(f^*α) ∩ [X]`.

## References

* [Stacks Project, Tag 0FF9](https://stacks.math.columbia.edu/tag/0FF9)
* [Stacks Project, Tag 0FF8](https://stacks.math.columbia.edu/tag/0FF8)
* [Stacks Project, Tag 0FFB](https://stacks.math.columbia.edu/tag/0FFB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

section Hypotheses

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)

/-- A scheme locally of finite type and quasi-compact over a field is Noetherian. -/
theorem isNoetherian_of_quasiCompact_fieldChowSituation [LocallyOfFiniteType sX]
    [QuasiCompact sX] : IsNoetherian X := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace sX).mp inferInstance
  exact isNoetherian_of_compactSpace sX

/-- A scheme separated over a field has affine diagonal: `X ⟶ Spec k ⟶ Spec 𝐙` is separated, so
its diagonal is a closed immersion. -/
theorem isAffineHom_diagonal_of_isSeparated_fieldChowSituation [IsSeparated sX] :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  have hsep : IsSeparated (terminal.from X) := by
    have : IsSeparated (sX ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa using this
  infer_instance

end Hypotheses

section Gysin

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
  [Smooth sX] [Smooth sY] [IsNoetherian X] [IsNoetherian Y]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))]
  {f : X ⟶ Y} [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

omit [LocallyOfFiniteType sY] [AlgebraicGeometry.IsNoetherian X]
  [AlgebraicGeometry.IsNoetherian Y]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] [LocallyOfFiniteType f] in
include sX sY hf in
/-- The local complete intersection property of a morphism of smooth schemes over `k`
(Stacks 0E9K, through Stacks 0FF9). -/
theorem isLocalCompleteIntersectionMorphism_of_smooth_fieldChowSituation :
    IsLocalCompleteIntersectionMorphism f :=
  isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf
    (isRegular_of_smooth_over_field sX) (isRegular_of_smooth_over_field sY)

/-- The rational Chow ring `CH^*(X) ⊗ 𝐐` of a scheme smooth over `k` (and Noetherian with affine
diagonal), with the product of Section 0FEX. -/
abbrev smoothRationalChowRing : Type u :=
  RationalIntersectionRing (isRegular_of_smooth_over_field sX)
    (exists_bounds_relativeDimension_fieldChowSituation k sX)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- The identity `CH_*(X) ⊗ 𝐐 ≃ CH^*(X) ⊗ 𝐐` onto the rational Chow ring. -/
abbrev smoothChowEquiv :
    (DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) ≃ₗ[ℚ]
      smoothRationalChowRing sX :=
  RationalIntersectionRing.equiv _ _

/-- The rational Gysin map `f^! : CH_*(Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐` of Stacks 0FF3 of a morphism of
smooth schemes over `k`; it exists by Stacks 0FFB. -/
abbrev smoothGysinRational :
    (DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sY j) →ₗ[ℚ]
      DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j :=
  lciGysinRational (fieldChowSituation k) sX sY hf
    (isLocalCompleteIntersectionMorphism_of_smooth_fieldChowSituation sX sY hf)
    (GysinMapExists.of_smooth_source f sY sX hf)

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] in
/-- The rational Gysin map of a morphism of smooth schemes over `k` sends the fundamental class
`[Y]` to `[X]`. -/
theorem smoothGysinRational_rationalFundamentalClass :
    smoothGysinRational sX sY hf (rationalFundamentalClass (fieldChowSituation k) sY) =
      rationalFundamentalClass (fieldChowSituation k) sX :=
  lciGysinRational_rationalFundamentalClass_of_isRegular _ sX sY hf _ _
    (isRegular_of_smooth_over_field sX) (isRegular_of_smooth_over_field sY)

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] in
/-- **Chern classes commute with the Gysin map (Stacks 0FF8) on `ch(α) ∩ [Y]`**:
`f^!(ch(α) ∩ [Y]) = ch(f^*α) ∩ [X]` for `α ∈ K_0(Vect(Y)) ⊗ 𝐐`, `f^*` being pullback of finite
locally free modules. -/
theorem smoothGysinRational_rationalChernCharacterCap (a : ℚ ⊗[ℤ] VectorBundleKZero Y)
    (β : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sY j) :
    smoothGysinRational sX sY hf (rationalChernCharacterCap (fieldChowSituation k) sY a β) =
      rationalChernCharacterCap (fieldChowSituation k) sX
        ((VectorBundleKZero.pullback f).toIntLinearMap.baseChange ℚ a)
        (smoothGysinRational sX sY hf β) := by
  have : Finite (_root_.ConnectedComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_connectedComponents X
  obtain ⟨loX, _, hbX⟩ := exists_bounds_relativeDimension_fieldChowSituation k sX
  obtain ⟨loY, _, hbY⟩ := exists_bounds_relativeDimension_fieldChowSituation k sY
  exact lciGysinRational_rationalChernCharacterCap _ sX sY hf _ _
    ⟨loX, by rintro _ ⟨x, rfl⟩; exact (hbX x).1⟩ ⟨loY, by rintro _ ⟨x, rfl⟩; exact (hbY x).1⟩ a β

/-- **The Gysin map `f^! : CH^*(Y) ⊗ 𝐐 ⟶ CH^*(X) ⊗ 𝐐` of a morphism of smooth schemes over `k`, as
a ring homomorphism** for the products of Section 0FEX: it exists by Stacks 0FFB, is
multiplicative by Stacks 0FF9 and sends `[Y]` to `[X]` by Stacks 0FF7. -/
def smoothGysinRingHom : smoothRationalChowRing sY →+* smoothRationalChowRing sX where
  toFun α := smoothChowEquiv sX (smoothGysinRational sX sY hf ((smoothChowEquiv sY).symm α))
  map_zero' := by simp
  map_add' α β := by simp
  map_one' := by
    rw [RationalIntersectionRing.one_eq, LinearEquiv.symm_apply_apply,
      smoothGysinRational_rationalFundamentalClass, RationalIntersectionRing.one_eq]
  map_mul' α β := by
    have hX := isRegular_of_smooth_over_field sX
    have hY := isRegular_of_smooth_over_field sY
    obtain ⟨α, rfl⟩ := (RationalIntersectionRing.equiv hY
      (exists_bounds_relativeDimension_fieldChowSituation k sY)).surjective α
    obtain ⟨β, rfl⟩ := (RationalIntersectionRing.equiv hY
      (exists_bounds_relativeDimension_fieldChowSituation k sY)).surjective β
    obtain ⟨a, rfl⟩ := (bijective_flip_rationalChernCharacterCap hY
      (exists_bounds_relativeDimension_fieldChowSituation k sY)).2 α
    rw [RationalIntersectionRing.equiv_mul_equiv, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
      RationalIntersectionRing.equiv_mul_equiv, LinearMap.flip_apply,
      rationalIntersectionProduct_rationalChernCharacterCap,
      smoothGysinRational_rationalChernCharacterCap, smoothGysinRational_rationalChernCharacterCap,
      smoothGysinRational_rationalFundamentalClass,
      rationalIntersectionProduct_rationalChernCharacterCap]

/-- `smoothGysinRingHom` is the rational Gysin map of Stacks 0FF3. -/
theorem smoothGysinRingHom_equiv
    (α : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sY j) :
    smoothGysinRingHom sX sY hf (smoothChowEquiv sY α) =
      smoothChowEquiv sX (smoothGysinRational sX sY hf α) := by
  show smoothChowEquiv sX (smoothGysinRational sX sY hf
    ((smoothChowEquiv sY).symm (smoothChowEquiv sY α))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- **Chern classes commute with the Gysin map (Stacks 0FF8)**, read on the rational Chow rings
through the isomorphisms `α' ↦ ch(α') ∩ [X]` of Section 0FEX:
`f^!(ch(α') ∩ [Y]) = ch(f^*α') ∩ [X]`. -/
theorem smoothGysinRingHom_rationalChernCharacterAlgEquiv (a : ℚ ⊗[ℤ] VectorBundleKZero Y) :
    smoothGysinRingHom sX sY hf (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field sY)
        (exists_bounds_relativeDimension_fieldChowSituation k sY) a) =
      rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field sX)
        (exists_bounds_relativeDimension_fieldChowSituation k sX)
        ((VectorBundleKZero.pullback f).toIntLinearMap.baseChange ℚ a) := by
  rw [rationalChernCharacterAlgEquiv_apply, rationalChernCharacterAlgEquiv_apply,
    smoothGysinRingHom_equiv, smoothGysinRational_rationalChernCharacterCap,
    smoothGysinRational_rationalFundamentalClass]

end Gysin

end Stacks.Chow

end
