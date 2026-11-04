module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationTop
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem

/-!
# The two Gysin maps of a regular immersion of smooth schemes agree

Let `i : Y ⟶ X` be a regular closed immersion of schemes smooth over a field `k`. The library has
two descriptions of the Gysin map `i^!` of Stacks 0FF3 on Chow groups:

* `Stacks.Chow.codimensionGysin`, for morphisms of smooth schemes, on classes graded by
  codimension, defined piece by piece over the pieces `Y_{d,e} = Y_d ∩ i⁻¹(X_e)` by restricting
  the Gysin class of `i` along `X_e ⟶ X` and then to the open piece `Y_{d,e} ⊆ Y ×_X X_e`;
* `Stacks.Chow.regularImmersionPartGysin`, for regular immersions, on the parts `X_e`: the Gysin
  class of `i` restricted along `X_e ⟶ X`, with values on `Y ×_X X_e`.

Both are built from the same bivariant class `lciGysinMapComponent` of `i` (only the proofs of
its side conditions differ). This file proves that they agree: on the piece `Y_{d,e}`, the
restriction of `i^!θ` is the restriction of `i^!(θ_e)` from `Y ×_X X_e`
(`chowGroupRestrict_codimensionGysin_eq_regularImmersionPartGysin`).

## Main results

* `Stacks.Chow.chowGroupRestrict_codimensionGysin_eq_regularImmersionPartGysin`.

## References

* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase)

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (i : Y ⟶ X) [IsClosedImmersion i]
  (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i) [Smooth (i ≫ sX)]

/-- **The two Gysin maps of a regular immersion of smooth schemes agree.** For
`θ ∈ CH^q(X)`, the restriction of `i^!θ ∈ CH^q(Y)` (`codimensionGysin`) to the piece
`Y_{d,e} = Y_d ∩ i⁻¹(X_e)` is the restriction, along the open immersion
`Y_{d,e} ⟶ Y ×_X X_e`, of `i^!(θ_e)` computed on the part `X_e`
(`regularImmersionPartGysin`). -/
theorem chowGroupRestrict_codimensionGysin_eq_regularImmersionPartGysin (q : ℤ)
    (θ : codimensionChowGroup k sX q) (d e : ℕ) :
    chowGroupRestrict (fieldChowSituation k) (partBase (i ≫ sX) d)
        (dimPartPieceBase (i ≫ sX) sX i d e) (dimPartPiece (i ≫ sX) sX i d e).ι rfl (d - q)
        (codimensionGysin (i ≫ sX) sX rfl q θ d) =
      chowGroupRestrict (fieldChowSituation k) (pullback.fst i (dimPart sX e).ι ≫ i ≫ sX)
        (dimPartPieceBase (i ≫ sX) sX i d e) (dimPartPieceToPullback (i ≫ sX) sX i d e)
        (dimPartPieceToPullback_comp_base (i ≫ sX) sX i d e) (d - q)
        (regularImmersionPartGysin sX i hreg d e q (θ e)) := by
  rw [chowGroupRestrict_codimensionGysin]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
    ((dimPartPieceGysinClass_capTarget_heq (i ≫ sX) sX rfl d e _ (θ e)).trans ?_))
  refine chowGroupRestrict_heq_of_eq _ _ _ rfl rfl rfl _ _ (by ring) _ _ ?_
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm
  rw [BivariantClass.capTargetHom_apply, regularImmersionPartGysinClass,
    bivariantRestriction_capTarget (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _)]

/-- Pushing forward the restriction of a class along an isomorphism `u` composed with `g` is
pushing forward the class along `g`. -/
theorem properChowPushforward_comp_chowGroupRestrict_of_isIso {C : ChowSituation.{u}}
    {A B W : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (u : B ⟶ A) [IsIso u]
    (hu : u ≫ sA = sB) (g : A ⟶ W) [IsProper g] (hg : g ≫ sW = sA) (k : ℤ)
    (x : chowGroup C sA k) :
    properChowPushforward C sB sW (u ≫ g) (by rw [Category.assoc, hg, hu]) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (chowGroupRestrict C sA sB u hu k x) =
      properChowPushforward C sA sW g hg k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _) x := by
  rw [properChowPushforward_comp_apply C sB sA sW u g (u ≫ g) rfl hu hg _ k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _),
    properChowPushforward_eq_chowPushforwardOfIso C sB sA u hu,
    chowPushforwardOfIso_eq_chowGroupRestrict C sB sA u hu (inv u) (IsIso.inv_hom_id u),
    chowGroupRestrict_comp, chowGroupRestrict_congr C sA sA _ _ k (𝟙 A) (IsIso.inv_hom_id u)
      (Category.id_comp sA), chowGroupRestrict_id]

/-- An open immersion all of whose points lie in its image is an isomorphism. -/
theorem isIso_of_isOpenImmersion_of_surjective {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
    (h : Function.Surjective f) : IsIso f := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  exact ⟨inferInstance, ⟨h⟩⟩

variable {sX i} in
omit [Smooth (i ≫ sX)] in
/-- **`π_*(i^!θ)` through either Gysin map**, for `X` and `Y` equidimensional of dimensions
`m + 1` and `m`: pushing forward `(i^!θ)_m ∈ CH_{m-q}(Y)` along a proper `π : Y ⟶ Z` is pushing
forward `i^!(θ_{m+1}) ∈ CH_{m-q}(Y ×_X X_{m+1})` along `Y ×_X X_{m+1} ⟶ Y ⟶ Z`. -/
theorem properChowPushforward_codimensionGysin_eq {Z : Scheme.{u}}
    (sZ : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sZ]
    (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY] (hi : i ≫ sX = sY) (π : Y ⟶ Z) [IsProper π]
    (hπ : π ≫ sZ = sY) {m : ℕ} (hallX : ∀ x : X, x ∈ dimPart sX (m + 1))
    (hallY : ∀ y : Y, y ∈ dimPart sY m)
    (q : ℤ) (θ : codimensionChowGroup k sX q) :
    haveI := (Stacks.WeilCohomology.isClopenDecomposition_dimPart sY).isProper_ι m
    haveI := (Stacks.WeilCohomology.isClopenDecomposition_dimPart sX).isProper_ι (m + 1)
    properChowPushforward (fieldChowSituation k) (partBase sY m) sZ ((dimPart sY m).ι ≫ π)
        (by rw [Category.assoc, hπ]) (m - q)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (codimensionGysin sY sX hi q θ m) =
      properChowPushforward (fieldChowSituation k) (pullback.fst i (dimPart sX (m + 1)).ι ≫ i ≫ sX)
        sZ (pullback.fst i (dimPart sX (m + 1)).ι ≫ π) (by rw [Category.assoc, hπ, hi]) (m - q)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (regularImmersionPartGysin sX i hreg m (m + 1) q (θ (m + 1))) := by
  subst hi
  have := (Stacks.WeilCohomology.isClopenDecomposition_dimPart (i ≫ sX)).isProper_ι m
  have := (Stacks.WeilCohomology.isClopenDecomposition_dimPart sX).isProper_ι (m + 1)
  have hιX : IsIso (dimPart sX (m + 1)).ι :=
    isIso_of_isOpenImmersion_of_surjective _ fun x ↦ ⟨⟨x, hallX x⟩, rfl⟩
  have hιY : IsIso (dimPart (i ≫ sX) m).ι :=
    isIso_of_isOpenImmersion_of_surjective _ fun y ↦ ⟨⟨y, hallY y⟩, rfl⟩
  have hu : IsIso (dimPartPiece (i ≫ sX) sX i m (m + 1)).ι :=
    isIso_of_isOpenImmersion_of_surjective _ fun a ↦ ⟨⟨a, hallX _⟩, rfl⟩
  have hv : IsIso (dimPartPieceToPullback (i ≫ sX) sX i m (m + 1)) := by
    have : IsIso (dimPartPieceToPullback (i ≫ sX) sX i m (m + 1) ≫
        pullback.fst i (dimPart sX (m + 1)).ι) := by
      rw [dimPartPieceToPullback_fst]; infer_instance
    exact IsIso.of_isIso_comp_right _ (pullback.fst i (dimPart sX (m + 1)).ι)
  have h := chowGroupRestrict_codimensionGysin_eq_regularImmersionPartGysin sX i hreg q θ m (m + 1)
  rw [← properChowPushforward_comp_chowGroupRestrict_of_isIso _ _ _
      (dimPartPiece (i ≫ sX) sX i m (m + 1)).ι rfl, h,
    ← properChowPushforward_comp_chowGroupRestrict_of_isIso _ _ _
      (dimPartPieceToPullback (i ≫ sX) sX i m (m + 1))
      (dimPartPieceToPullback_comp_base (i ≫ sX) sX i m (m + 1))]
  exact properChowPushforward_congr_hom _ _ _
    (by
      have h := dimPartPieceToPullback_fst (i ≫ sX) sX i m (m + 1)
      simp only [← Category.assoc, h]) _ _ _ _ _ _

end Stacks.Chow

end
