module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
import all StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence

/-!
# Symmetry of the exterior product

Let `X` and `Y` be schemes locally of finite type over the base `S` of chapter 42 of the Stacks
Project, and let `σ : X ×_S Y ⟶ Y ×_S X` be the isomorphism exchanging the two factors. For
integral closed subschemes `X' ⊆ X` and `Y' ⊆ Y` the isomorphism `σ` carries `X' ×_S Y'` onto
`Y' ×_S X'`, so on generators of the cycle groups `σ_*([X'] × [Y']) = [Y'] × [X']`. By
bilinearity the exterior product of cycles of Stacks 0FBV is symmetric,

  `σ_*(α × β) = β × α`   in `Z_{n+m}(Y ×_S X)`,   for `α ∈ Z_n(X)` and `β ∈ Z_m(Y)`,

and, pushforward along an isomorphism preserving rational equivalence, so is the exterior product
on Chow groups: `σ_*(α × β) = β × α` in `CH_{n+m}(Y ×_S X)` for `α ∈ CH_n(X)` and
`β ∈ CH_m(Y)`. In terms of the map `× : CH_n(X) ⊗ CH_m(Y) ⟶ CH_{n+m}(X ×_S Y)` this says that
`σ_* ∘ ×` is the exterior product `CH_m(Y) ⊗ CH_n(X) ⟶ CH_{m+n}(Y ×_S X)` precomposed with the
exchange of the two tensor factors.

## Main results

* `Stacks.Chow.exteriorProductCoeff_pullbackSymmetry_hom` — the coefficient of `α × β` at a point
  `z` of `X ×_S Y` is the coefficient of `β × α` at `σ z`.
* `Stacks.Chow.properPushforward_pullbackSymmetry_exteriorProduct`,
  `Stacks.Chow.val_properPushforward_pullbackSymmetry_exteriorProduct` — the symmetry of the
  exterior product of cycles, `σ_*(α × β) = β × α`.
* `Stacks.Chow.chowPushforwardOfIso_pullbackSymmetry_chowExteriorProduct_tmul` — the symmetry of
  the exterior product on Chow groups on a pure tensor.
* `Stacks.Chow.chowPushforwardOfIso_pullbackSymmetry_chowExteriorProduct` — the same on an
  arbitrary element of the tensor product, through the exchange `TensorProduct.comm`.
* `Stacks.Chow.chowPushforwardOfIso_pullbackSymmetry_comp_chowExteriorProduct` — the same as an
  equality of homomorphisms `CH_n(X) ⊗ CH_m(Y) ⟶ CH_{n+m}(Y ×_S X)`.

## Implementation notes

The exterior product `β × α` of an `m`-cycle and an `n`-cycle lies in degree `m + n`, while the
pushforward of `α × β` lies in degree `n + m`. The two groups are equal but not syntactically, so
the symmetry is stated through the transport along `add_comm m n`: on cycles the cast, which does
not change the coefficient function (`Stacks.Chow.val_cycleGroup_cast`), and on Chow groups
`Stacks.Chow.chowGroupDegreeEquiv`. The cycle-level symmetry is also recorded as an equality of
coefficient functions, where no transport is needed.

The cycle-level statements hold over an arbitrary base; only the Chow-level statements, which
use `Stacks.Chow.chowExteriorProduct`, carry its hypotheses that the base is the spectrum of a
field.

## References

* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (pullbackSymmetry_hom_comp_base)

/-- **Stacks 0FBV, symmetry on coefficients.** The coefficient of the exterior product `α × β` at
a point `z` of `X ×_S Y` is the coefficient of `β × α` at the image of `z` under the isomorphism
`X ×_S Y ≅ Y ×_S X` exchanging the two factors. -/
theorem exteriorProductCoeff_pullbackSymmetry_hom (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (n m : ℤ)
    (α : CycleGroup C sX n) (β : CycleGroup C sY m) (z : (pullback sX sY : Scheme.{u})) :
    exteriorProductCoeff C sY sX m n β α ((pullbackSymmetry sX sY).hom.base z) =
      exteriorProductCoeff C sX sY n m α β z := by
  have h := exteriorProductCoeff_pullbackSymmetry C sX sY n m α β
    ((pullbackSymmetry sX sY).hom.base z)
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id] at h
  exact h.symm

/-- **Stacks 0FBV, symmetry on cycles.** For `α ∈ Z_n(X)` and `β ∈ Z_m(Y)` the pushforward of the
exterior product `α × β` along the isomorphism `X ×_S Y ≅ Y ×_S X` exchanging the two factors is
the exterior product `β × α`, read in degree `n + m`. -/
theorem properPushforward_pullbackSymmetry_exteriorProduct (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (n m : ℤ) (α : CycleGroup C sX n) (β : CycleGroup C sY m) :
    properPushforward C (pullback.fst sX sY ≫ sX) (pullback.fst sY sX ≫ sY)
        (pullbackSymmetry sX sY).hom (pullbackSymmetry_hom_comp_base sX sY) (n + m)
        (exteriorProduct C sX sY n m α β) =
      (add_comm m n ▸ exteriorProduct C sY sX m n β α :
        CycleGroup C (pullback.fst sY sX ≫ sY) (n + m)) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun w ↦ ?_)
  obtain ⟨z, rfl⟩ := (Scheme.homeoOfIso (pullbackSymmetry sX sY)).surjective w
  change (properPushforward C (pullback.fst sX sY ≫ sX) (pullback.fst sY sX ≫ sY)
      (pullbackSymmetry sX sY).hom (pullbackSymmetry_hom_comp_base sX sY) (n + m)
      (exteriorProduct C sX sY n m α β)).1 ((pullbackSymmetry sX sY).hom.base z) =
    (add_comm m n ▸ exteriorProduct C sY sX m n β α :
      CycleGroup C (pullback.fst sY sX ≫ sY) (n + m)).1 ((pullbackSymmetry sX sY).hom.base z)
  rw [properPushforward_apply_of_isIso, val_cycleGroup_cast]
  exact (exteriorProductCoeff_pullbackSymmetry_hom C sX sY n m α β z).symm

/-- **Stacks 0FBV, symmetry on cycles**, on coefficient functions: the pushforward of `α × β`
along the isomorphism `X ×_S Y ≅ Y ×_S X` exchanging the two factors has the coefficient function
of `β × α`. -/
theorem val_properPushforward_pullbackSymmetry_exteriorProduct (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (n m : ℤ) (α : CycleGroup C sX n) (β : CycleGroup C sY m) :
    (properPushforward C (pullback.fst sX sY ≫ sX) (pullback.fst sY sX ≫ sY)
        (pullbackSymmetry sX sY).hom (pullbackSymmetry_hom_comp_base sX sY) (n + m)
        (exteriorProduct C sX sY n m α β)).1 =
      (exteriorProduct C sY sX m n β α).1 := by
  rw [properPushforward_pullbackSymmetry_exteriorProduct, val_cycleGroup_cast]

/-- **Stacks 0FBV, symmetry on Chow groups.** For `α ∈ CH_n(X)` and `β ∈ CH_m(Y)` the
pushforward of the exterior product `α × β` along the isomorphism `X ×_S Y ≅ Y ×_S X` exchanging
the two factors is the exterior product `β × α`, read in degree `n + m`. -/
theorem chowPushforwardOfIso_pullbackSymmetry_chowExteriorProduct_tmul (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (n m : ℤ) (α : chowGroup C sX n) (β : chowGroup C sY m) :
    chowPushforwardOfIso C (pullback.fst sX sY ≫ sX) (pullback.fst sY sX ≫ sY)
        (pullbackSymmetry sX sY).hom (pullbackSymmetry_hom_comp_base sX sY) (n + m)
        (chowExteriorProduct C hδ sX sY n m (α ⊗ₜ[ℤ] β)) =
      chowGroupDegreeEquiv C (pullback.fst sY sX ≫ sY) (add_comm m n)
        (chowExteriorProduct C hδ sY sX m n (β ⊗ₜ[ℤ] α)) := by
  induction α using QuotientAddGroup.induction_on with | H a => ?_
  induction β using QuotientAddGroup.induction_on with | H b => ?_
  rw [chowExteriorProduct_tmul_mk, chowExteriorProduct_tmul_mk]
  refine (chowPushforwardOfIso_mk C (pullback.fst sX sY ≫ sX) (pullback.fst sY sX ≫ sY)
    (pullbackSymmetry sX sY).hom (pullbackSymmetry_hom_comp_base sX sY) (n + m)
    (exteriorProduct C sX sY n m a b)).trans ?_
  refine (chowGroupDegreeEquiv_mk_eq_mk_of_val C (pullback.fst sY sX ≫ sY) (add_comm m n) _ _
    ?_).symm
  exact (val_properPushforward_pullbackSymmetry_exteriorProduct C sX sY n m a b).symm

/-- **Stacks 0FBV, symmetry on Chow groups.** For every element `t` of `CH_n(X) ⊗ CH_m(Y)` the
pushforward of its exterior product along the isomorphism `X ×_S Y ≅ Y ×_S X` exchanging the two
factors is the exterior product of its image in `CH_m(Y) ⊗ CH_n(X)` under the exchange of the
tensor factors, read in degree `n + m`. -/
theorem chowPushforwardOfIso_pullbackSymmetry_chowExteriorProduct (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (n m : ℤ) (t : chowGroup C sX n ⊗[ℤ] chowGroup C sY m) :
    chowPushforwardOfIso C (pullback.fst sX sY ≫ sX) (pullback.fst sY sX ≫ sY)
        (pullbackSymmetry sX sY).hom (pullbackSymmetry_hom_comp_base sX sY) (n + m)
        (chowExteriorProduct C hδ sX sY n m t) =
      chowGroupDegreeEquiv C (pullback.fst sY sX ≫ sY) (add_comm m n)
        (chowExteriorProduct C hδ sY sX m n (TensorProduct.comm ℤ _ _ t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul α β =>
    rw [TensorProduct.comm_tmul]
    exact chowPushforwardOfIso_pullbackSymmetry_chowExteriorProduct_tmul C hδ sX sY n m α β
  | add s t hs ht => simp only [map_add, hs, ht]

/-- **Stacks 0FBV, symmetry on Chow groups**, as an equality of homomorphisms
`CH_n(X) ⊗ CH_m(Y) ⟶ CH_{n+m}(Y ×_S X)`: the exterior product followed by pushforward along the
isomorphism `X ×_S Y ≅ Y ×_S X` exchanging the two factors is the exchange of the tensor factors
followed by the exterior product `CH_m(Y) ⊗ CH_n(X) ⟶ CH_{m+n}(Y ×_S X)` and the identification of
degrees `m + n = n + m`. -/
theorem chowPushforwardOfIso_pullbackSymmetry_comp_chowExteriorProduct (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (n m : ℤ) :
    (chowPushforwardOfIso C (pullback.fst sX sY ≫ sX) (pullback.fst sY sX ≫ sY)
        (pullbackSymmetry sX sY).hom (pullbackSymmetry_hom_comp_base sX sY) (n + m)).comp
        (chowExteriorProduct C hδ sX sY n m) =
      ((chowGroupDegreeEquiv C (pullback.fst sY sX ≫ sY) (add_comm m n)).toAddMonoidHom.comp
        (chowExteriorProduct C hδ sY sX m n)).comp
        (TensorProduct.comm ℤ (chowGroup C sX n) (chowGroup C sY m)).toLinearMap.toAddMonoidHom :=
  AddMonoidHom.ext fun t ↦
    chowPushforwardOfIso_pullbackSymmetry_chowExteriorProduct C hδ sX sY n m t

end Stacks.Chow

end
