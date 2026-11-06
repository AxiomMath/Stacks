module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CompositionAction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionAssoc

/-!
# Correspondences of mixed dimension with the base point

Let `k` be a field and let `X` be a smooth scheme over `k`, decomposed as `X = ∐_d X_d` into its
open and closed parts of constant dimension `d`. Section 0FFZ of the Stacks Project defines the
correspondences `Corrʳ(X, Y) = ⊕_d ⊕_e CH_{e-r}(X_d × Y_e) ⊗ ℚ`, and Stacks 0FG0 (2) and (3)
identify the correspondences having `Spec k` as a factor with rational Chow groups:

* `CH_{-r}(X) ⊗ ℚ = Corrʳ(X, Spec k)`, compatibly with pullback by correspondences, which
  becomes composition;
* `CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)`, compatibly with pushforward by correspondences, which
  becomes composition.

The equidimensional case is `Stacks.WeilCohomology.correspondenceToPointEquiv` and
`Stacks.WeilCohomology.correspondenceFromPointEquiv`, with their compatibilities in
`Stacks.WeilCohomology.correspondenceToPointEquiv_correspondencePullback` and
`Stacks.WeilCohomology.correspondenceFromPointEquiv_correspondencePushforward`. This file
assembles the general case from the pieces. Three facts enter.

1. `Spec k` has relative dimension `0` over itself, so its part of dimension `0` is everything
   and its other parts are empty; the Chow groups of an empty scheme vanish, so only the part of
   dimension `0` contributes. That part is an open subscheme of `Spec k` isomorphic to it, not
   equal to it.
2. Composition of correspondences is natural with respect to isomorphisms of the three factors
   over `k`, for a family of diagonal classes whose intersection products are transported by
   isomorphisms (`Stacks.WeilCohomology.chowPushforwardOfIso_compositionInt`). This carries the
   equidimensional statements across the isomorphism between `Spec k` and its part of
   dimension `0`.
3. For `X` proper over `k` only finitely many parts `X_d` are nonempty, as `X` is quasi-compact,
   and `CH_m(X) ⊗ ℚ = ⊕_d CH_m(X_d) ⊗ ℚ` through restriction to and pushforward from the parts
   (`Stacks.WeilCohomology.rationalChowPartsEquiv`). The codimension-graded group
   `CH^r(X) ⊗ ℚ` of a scheme of mixed dimension is by definition the direct sum over the parts,
   `Stacks.WeilCohomology.CodimChow`, and needs no finiteness.

## Main definitions

* `Stacks.WeilCohomology.prodHom`: the morphism `X' ×_S Y' ⟶ X ×_S Y` induced by morphisms over
  `S`.
* `Stacks.WeilCohomology.correspondenceEquivOfIso`: transport of correspondences along
  isomorphisms of both factors over the base.
* `Stacks.WeilCohomology.directSumEquivSummand`: a direct sum all of whose summands but one are
  trivial is that summand.
* `Stacks.WeilCohomology.correspondenceToPointEquivOfIso`,
  `Stacks.WeilCohomology.correspondenceFromPointEquivOfIso`: the equidimensional identifications
  of Stacks 0FG0 (2) and (3) for a point isomorphic to `Spec k`.
* `Stacks.WeilCohomology.restrictParts`, `Stacks.WeilCohomology.rationalChowPartsEquiv`:
  `CH_m(X) ⊗ ℚ = ⊕_d CH_m(X_d) ⊗ ℚ` for `X` smooth over `k` and quasi-compact.
* `Stacks.WeilCohomology.corrToPointEquiv`: **Stacks 0FG0 (2)**, the canonical isomorphism
  `CH_{-r}(X) ⊗ ℚ = Corrʳ(X, Spec k)` for `X` smooth and proper over `k`.
* `Stacks.WeilCohomology.corrFromPointEquiv`: **Stacks 0FG0 (3)**, the canonical isomorphism
  `CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)` for `X` smooth over `k`.

## Main results

* `Stacks.WeilCohomology.dimPart_zero_eq_top`, `Stacks.WeilCohomology.isEmpty_dimPart_of_ne_zero`:
  the parts of a smooth morphism of relative dimension `0`.
* `Stacks.WeilCohomology.finite_setOf_nonempty_dimPart`: a quasi-compact scheme smooth over `S`
  has only finitely many nonempty parts.
* `Stacks.WeilCohomology.chowPushforwardOfIso_compositionInt`,
  `Stacks.WeilCohomology.correspondenceEquivOfIso_composition`: composition of correspondences
  is natural with respect to isomorphisms over `k`.
* `Stacks.WeilCohomology.correspondenceToPointEquivOfIso_correspondencePullback`,
  `Stacks.WeilCohomology.correspondenceFromPointEquivOfIso_correspondencePushforward`: the
  equidimensional compatibilities for a point isomorphic to `Spec k`.
* `Stacks.WeilCohomology.corrToPointEquiv_pullback`: the second half of Stacks 0FG0 (2),
  `c^*(β) = β ∘ c`.
* `Stacks.WeilCohomology.corrFromPointEquiv_pushforward`: the second half of Stacks 0FG0 (3),
  `c_*(α) = c ∘ α`.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.BasePointComposition`, the
intersection products are formed with an arbitrary family `Δ` of diagonal classes; the
compatibilities hold for every family which is invariant under isomorphisms
(`Stacks.WeilCohomology.DiagonalClassFamily.IsoInvariant`) and, for the pushforward, symmetric
(`Stacks.WeilCohomology.DiagonalClassFamily.IsSymmetric`). The degree `-r - s` of `c^*(β)` and
the degree `-(s + r)` of the identification of `Corr^{s+r}(X', Spec k)` are compared through the
base change to `ℚ` of `Stacks.Chow.chowGroupDegreeEquiv`.

## References

* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- Pushing a Chow class forward from an open and closed subscheme `V` and restricting it back to
`V` returns the class. -/
theorem chowGroupRestrict_properChowPushforward_opens_self (V : X.Opens) [IsProper V.ι] (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (V.ι ≫ sX) sX V.ι rfl k)
    (α : chowGroup C (V.ι ≫ sX) k) :
    chowGroupRestrict C sX (V.ι ≫ sX) V.ι rfl k (properChowPushforward C _ sX V.ι rfl k hfac α) =
      α := by
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C (V.ι ≫ sX) k))
      (Subtype.ext (opensRestrictCycle_properPushforward_self C sX V k c))

/-- Pushing a Chow class forward from an open and closed subscheme `V` and restricting it to an
open subscheme `W` disjoint from `V` gives zero. -/
theorem chowGroupRestrict_properChowPushforward_opens_of_disjoint (V W : X.Opens) [IsProper V.ι]
    (hVW : Disjoint V W) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (V.ι ≫ sX) sX V.ι rfl k)
    (α : chowGroup C (V.ι ≫ sX) k) :
    chowGroupRestrict C sX (W.ι ≫ sX) W.ι rfl k (properChowPushforward C _ sX V.ι rfl k hfac α) =
      0 := by
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    exact (congrArg (QuotientAddGroup.mk' (rationalEquivalences C (W.ι ≫ sX) k))
      (Subtype.ext (opensRestrictCycle_properPushforward_of_disjoint C sX V W hVW k c))).trans
      (map_zero _)

end Stacks.Chow

namespace Stacks.WeilCohomology

/-! ### The parts of a smooth morphism of relative dimension zero -/

section Parts

variable {X S : Scheme.{u}} (sX : X ⟶ S) [Smooth sX] [IsSeparated sX]

omit [IsSeparated sX] in
/-- A point of a part `X_e` of a smooth morphism of relative dimension `0` forces `e = 0`: the
part is then of relative dimension both `e` and `0`, with a nonempty fibre. -/
theorem eq_zero_of_mem_dimPart (h : RelativeDimension sX 0) {e : ℕ} {x : X}
    (hx : x ∈ dimPart sX e) : e = 0 := by
  let y : (dimPart sX e).toScheme := ⟨x, hx⟩
  have : LocallyQuasiFinite sX := (locallyQuasiFinite_iff_relativeDimension_zero sX).mpr h
  have h0 : RelativeDimension (partBase sX e) 0 :=
    (locallyQuasiFinite_iff_relativeDimension_zero _).mp inferInstance
  have hy := ((relativeDimension_partBase sX e) _ ⟨(partBase sX e).asFiber y⟩).2.symm.trans
    (h0 _ ⟨(partBase sX e).asFiber y⟩).2
  exact_mod_cast hy

omit [IsSeparated sX] in
/-- For a smooth morphism of relative dimension `0`, the parts of nonzero dimension are empty. -/
theorem dimPart_eq_bot_of_ne_zero (h : RelativeDimension sX 0) {e : ℕ} (he : e ≠ 0) :
    dimPart sX e = ⊥ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  exact fun hx ↦ he (eq_zero_of_mem_dimPart sX h hx)

omit [IsSeparated sX] in
/-- For a smooth morphism of relative dimension `0`, the part of dimension `0` is everything. -/
theorem dimPart_zero_eq_top (h : RelativeDimension sX 0) : dimPart sX 0 = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  obtain ⟨d, hd⟩ := (isClopenDecomposition_dimPart sX).exists_mem x
  rwa [eq_zero_of_mem_dimPart sX h hd] at hd

omit [IsSeparated sX] in
/-- For a smooth morphism of relative dimension `0`, the parts of nonzero dimension are empty
schemes. -/
theorem isEmpty_dimPart_of_ne_zero (h : RelativeDimension sX 0) {e : ℕ} (he : e ≠ 0) :
    IsEmpty (dimPart sX e).toScheme :=
  ⟨fun y ↦ he (eq_zero_of_mem_dimPart sX h y.2)⟩

omit [IsSeparated sX] in
/-- For a smooth morphism of relative dimension `0`, the inclusion of the part of dimension `0`
is an isomorphism. -/
theorem isIso_dimPart_zero_ι (h : RelativeDimension sX 0) : IsIso (dimPart sX 0).ι := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Scheme.Opens.opensRange_ι, dimPart_zero_eq_top sX h]

omit [IsSeparated sX] in
/-- A quasi-compact scheme smooth over `S` has only finitely many nonempty parts: the parts form a
locally finite family, being disjoint and open. -/
theorem finite_setOf_nonempty_dimPart [CompactSpace X] :
    {d | (dimPart sX d : Set X).Nonempty}.Finite :=
  (Stacks.Topology.locallyFinite_of_disjoint_open_cover _ (fun d ↦ (dimPart sX d).2)
    (isClopenDecomposition_dimPart sX).exists_mem fun _ _ hij ↦
      TopologicalSpace.Opens.coe_disjoint.2
        ((isClopenDecomposition_dimPart sX).disjoint _ _ hij)).finite_nonempty_of_compact

end Parts

/-! ### Correspondences with an empty factor -/

section Empty

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]

/-- Correspondences out of an empty scheme vanish. -/
theorem subsingleton_correspondence_of_isEmpty_left [IsEmpty X] (e r : ℤ) :
    Subsingleton (Correspondence C sX sY e r) := by
  have : IsEmpty (Limits.pullback sX sY : Scheme.{u}) :=
    ⟨fun z ↦ isEmptyElim ((Limits.pullback.fst sX sY).base z)⟩
  have := subsingleton_chowGroup_of_isEmpty C (prodBase sX sY) (e - r)
  infer_instance

/-- Correspondences into an empty scheme vanish. -/
theorem subsingleton_correspondence_of_isEmpty_right [IsEmpty Y] (e r : ℤ) :
    Subsingleton (Correspondence C sX sY e r) := by
  have : IsEmpty (Limits.pullback sX sY : Scheme.{u}) :=
    ⟨fun z ↦ isEmptyElim ((Limits.pullback.snd sX sY).base z)⟩
  have := subsingleton_chowGroup_of_isEmpty C (prodBase sX sY) (e - r)
  infer_instance

end Empty

/-! ### Direct sums with a single nontrivial summand -/

section Summand

variable {R ι : Type*} [Semiring R] [DecidableEq ι] {M : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- A direct sum all of whose summands other than `M i₀` are trivial is `M i₀`, through the
projection to that summand. -/
def directSumEquivSummand (i₀ : ι) (h : ∀ i, i ≠ i₀ → Subsingleton (M i)) :
    (DirectSum ι M) ≃ₗ[R] M i₀ :=
  LinearEquiv.ofLinear (DirectSum.component R ι M i₀) (DirectSum.lof R ι M i₀)
    (LinearMap.ext fun x ↦ by simp)
    (DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ by
      by_cases hi : i = i₀
      · subst hi
        simp
      · have := h i hi
        simp [Subsingleton.elim x 0])

/-- The identification of a direct sum with its only nontrivial summand is evaluation at that
summand. -/
@[simp]
theorem directSumEquivSummand_apply (i₀ : ι) (h : ∀ i, i ≠ i₀ → Subsingleton (M i))
    (x : DirectSum ι M) : directSumEquivSummand (R := R) i₀ h x = x i₀ :=
  (DirectSum.apply_eq_component R x i₀).symm

/-- The inverse of the identification of a direct sum with its only nontrivial summand is the
inclusion of that summand. -/
@[simp]
theorem directSumEquivSummand_symm_apply (i₀ : ι) (h : ∀ i, i ≠ i₀ → Subsingleton (M i))
    (x : M i₀) : (directSumEquivSummand (R := R) i₀ h).symm x = DirectSum.lof R ι M i₀ x :=
  rfl

end Summand

/-! ### Naturality of composition with respect to isomorphisms -/

section ProdHom

variable {S X Y X' Y' : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sX' : X' ⟶ S) (sY' : Y' ⟶ S)
  (φX : X' ⟶ X) (φY : Y' ⟶ Y) (hφX : φX ≫ sX = sX') (hφY : φY ≫ sY = sY')

/-- The morphism `φX ×_S φY : X' ×_S Y' ⟶ X ×_S Y` induced by morphisms over `S`. -/
abbrev prodHom : Limits.pullback sX' sY' ⟶ Limits.pullback sX sY :=
  Limits.pullback.map sX' sY' sX sY φX φY (𝟙 S) (by simp [hφX]) (by simp [hφY])

/-- `φX ×_S φY` is a morphism over `S`. -/
theorem prodHom_comp_prodBase :
    prodHom sX sY sX' sY' φX φY hφX hφY ≫ prodBase sX sY = prodBase sX' sY' := by
  simp [prodBase, hφX]

/-- `𝟙 ×_S 𝟙` is the identity. -/
theorem prodHom_id : prodHom sX sY sX sY (𝟙 X) (𝟙 Y) (Category.id_comp _) (Category.id_comp _) =
    𝟙 _ := by
  ext <;> simp

end ProdHom

section Transport

variable (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}} (sX : X ⟶ C.S) (sY : Y ⟶ C.S)
  (sX' : X' ⟶ C.S) (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
  [LocallyOfFiniteType sX'] [LocallyOfFiniteType sY'] (φX : X' ⟶ X) [IsIso φX] (φY : Y' ⟶ Y)
  [IsIso φY] (hφX : φX ≫ sX = sX') (hφY : φY ≫ sY = sY')

/-- Transport of correspondences along isomorphisms `φX : X' ≅ X` and `φY : Y' ≅ Y` over the
base, `Corrʳ(X', Y') ≃ Corrʳ(X, Y)`: pushforward along `φX ×_S φY`. -/
def correspondenceEquivOfIso (e r : ℤ) :
    Correspondence C sX' sY' e r ≃ₗ[ℚ] Correspondence C sX sY e r :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
    (chowGroupEquivOfIso C (prodBase sX' sY') (prodBase sX sY)
      (prodHom sX sY sX' sY' φX φY hφX hφY) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
      (e - r)).toIntLinearEquiv

/-- Transport of correspondences along isomorphisms on pure tensors. -/
@[simp]
theorem correspondenceEquivOfIso_tmul (e r : ℤ) (q : ℚ)
    (c : chowGroup C (prodBase sX' sY') (e - r)) :
    correspondenceEquivOfIso C sX sY sX' sY' φX φY hφX hφY e r (q ⊗ₜ[ℤ] c) =
      q ⊗ₜ[ℤ] chowPushforwardOfIso C (prodBase sX' sY') (prodBase sX sY)
        (prodHom sX sY sX' sY' φX φY hφX hφY) (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (e - r) c :=
  rfl

omit [LocallyOfFiniteType sX'] [LocallyOfFiniteType sY'] [IsIso φX] [IsIso φY] in
/-- Transport of correspondences along the identities is the identity. -/
@[simp]
theorem correspondenceEquivOfIso_id (e r : ℤ) (c : Correspondence C sX sY e r) :
    correspondenceEquivOfIso C sX sY sX sY (𝟙 X) (𝟙 Y) (Category.id_comp _)
      (Category.id_comp _) e r c = c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul q c =>
    rw [correspondenceEquivOfIso_tmul, chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _)
      (prodHom_id sX sY) _ (Category.id_comp _), chowPushforwardOfIso_id]
  | add x y hx hy => rw [map_add, hx, hy]

end Transport

variable (k : Type u) [Field k] (Δ : DiagonalClassFamily k)

section Naturality

variable {X Y Z X' Y' Z' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY' : Y' ⟶ (fieldChowSituation k).S) (sZ' : Z' ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
  [LocallyOfFiniteType sX'] [LocallyOfFiniteType sY'] [LocallyOfFiniteType sZ']
  [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [Smooth sZ] [IsSeparated sZ]
  [Smooth sX'] [IsSeparated sX'] [Smooth sY'] [IsSeparated sY'] [Smooth sZ'] [IsSeparated sZ']
  (φX : X' ⟶ X) [IsIso φX] (φY : Y' ⟶ Y) [IsIso φY] (φZ : Z' ⟶ Z) [IsIso φZ]
  (hφX : φX ≫ sX = sX') (hφY : φY ≫ sY = sY') (hφZ : φZ ≫ sZ = sZ')

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] [IsSeparated sX'] [IsSeparated sY']
    [IsSeparated sZ'] in
/-- **Composition of correspondences is natural with respect to isomorphisms over `k`**, on
integral Chow groups: for isomorphisms `φX : X' ≅ X`, `φY : Y' ≅ Y`, `φZ : Z' ≅ Z` over `k`,
`(φX × φZ)_*(c' ∘ c) = (φY × φZ)_* c' ∘ (φX × φY)_* c`, for an iso-invariant family of diagonal
classes. The triple product is transported along `φX × φY × φZ`, which carries the three
projections to the three projections, and the product along it by iso-invariance. -/
theorem chowPushforwardOfIso_compositionInt (hΔ : Δ.IsoInvariant) [IsProper sY] [IsProper sY']
    {d e f : ℕ} (hX : RelativeDimension sX d) (hY : RelativeDimension sY e)
    (hZ : RelativeDimension sZ f) (hX' : RelativeDimension sX' d)
    (hY' : RelativeDimension sY' e) (hZ' : RelativeDimension sZ' f) (r s : ℤ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX' sY') ((e : ℤ) - r))
    (c' : chowGroup (fieldChowSituation k) (prodBase sY' sZ') ((f : ℤ) - s)) :
    chowPushforwardOfIso _ (prodBase sX' sZ') (prodBase sX sZ)
        (prodHom sX sZ sX' sZ' φX φZ hφX hφZ) (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _
        (compositionInt k sX' sY' sZ' Δ hX' hY' hZ' r s c c') =
      compositionInt k sX sY sZ Δ hX hY hZ r s
        (chowPushforwardOfIso _ _ _ (prodHom sX sY sX' sY' φX φY hφX hφY)
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _ c)
        (chowPushforwardOfIso _ _ _ (prodHom sY sZ sY' sZ' φY φZ hφY hφZ)
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _ c') := by
  let Ψ : tripleProduct sX' sY' sZ' ⟶ tripleProduct sX sY sZ :=
    prodHom (prodBase sX sY) sZ (prodBase sX' sY') sZ' (prodHom sX sY sX' sY' φX φY hφX hφY) φZ
      (prodHom_comp_prodBase _ _ _ _ _ _ _ _) hφZ
  have hΨ : Ψ ≫ tripleBase sX sY sZ = tripleBase sX' sY' sZ' :=
    prodHom_comp_prodBase _ _ _ _ _ _ _ _
  have h12 : pr₁₂ sX' sY' sZ' ≫ prodHom sX sY sX' sY' φX φY hφX hφY = Ψ ≫ pr₁₂ sX sY sZ :=
    (Limits.pullback.lift_fst _ _ _).symm
  have h23 : pr₂₃ sX' sY' sZ' ≫ prodHom sY sZ sY' sZ' φY φZ hφY hφZ = Ψ ≫ pr₂₃ sX sY sZ := by
    ext <;> simp [Ψ]
  have h13 : pr₁₃ sX' sY' sZ' ≫ prodHom sX sZ sX' sZ' φX φZ hφX hφZ = Ψ ≫ pr₁₃ sX sY sZ := by
    ext <;> simp [Ψ]
  simp only [compositionInt, compositionCycle, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    AddMonoidHom.coe_toIntLinearMap, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv]
  rw [flatPullbackChow_chowPushforwardOfIso (fieldChowSituation k) (prodBase sX' sY')
      (tripleBase sX' sY' sZ') (prodBase sX sY) (tripleBase sX sY sZ) _
      (prodHom_comp_prodBase _ _ _ _ _ _ _ _) Ψ hΨ (pr₁₂ sX' sY' sZ') (pr₁₂_comp_prodBase _ _ _)
      (pr₁₂ sX sY sZ) (pr₁₂_comp_prodBase _ _ _) h12 f (relativeDimension_pr₁₂ k _ _ _ hZ')
      (relativeDimension_pr₁₂ k _ _ _ hZ) _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c,
    flatPullbackChow_chowPushforwardOfIso (fieldChowSituation k) (prodBase sY' sZ')
      (tripleBase sX' sY' sZ') (prodBase sY sZ) (tripleBase sX sY sZ) _
      (prodHom_comp_prodBase _ _ _ _ _ _ _ _) Ψ hΨ (pr₂₃ sX' sY' sZ') (pr₂₃_comp_prodBase _ _ _)
      (pr₂₃ sX sY sZ) (pr₂₃_comp_prodBase _ _ _) h23 d (relativeDimension_pr₂₃ k _ _ _ hX')
      (relativeDimension_pr₂₃ k _ _ _ hX) _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c']
  set a := flatPullbackChow (fieldChowSituation k) (tripleBase sX' sY' sZ') (prodBase sX' sY')
    (pr₁₂ sX' sY' sZ') (pr₁₂_comp_prodBase _ _ _) f (relativeDimension_pr₁₂ k _ _ _ hZ') _
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c
  set b := flatPullbackChow (fieldChowSituation k) (tripleBase sX' sY' sZ') (prodBase sY' sZ')
    (pr₂₃ sX' sY' sZ') (pr₂₃_comp_prodBase _ _ _) d (relativeDimension_pr₂₃ k _ _ _ hX') _
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c'
  have key := hΔ (tripleBase sX sY sZ) (tripleBase sX' sY' sZ') Ψ hΨ (f + (e + d))
    (relativeDimension_tripleBase k sX sY sZ hX hY hZ)
    (relativeDimension_tripleBase k sX' sY' sZ' hX' hY' hZ') _ _ a b
  rw [← (chowGroupEquivOfIso (fieldChowSituation k) _ _ Ψ hΨ _).apply_symm_apply
    (selfIntersectionProduct _ _ _ _ _ _ _ _ (chowPushforwardOfIso _ _ _ Ψ hΨ _ a)
      (chowPushforwardOfIso _ _ _ Ψ hΨ _ b))]
  show _ = (properChowPushforward _ _ _ _ _ _ _) ((chowGroupDegreeEquiv _ _ _)
    (chowPushforwardOfIso _ _ _ Ψ hΨ _ (chowPushforwardOfIso _ _ _ (inv Ψ)
      (by rw [IsIso.inv_comp_eq, hΨ]) _ _)))
  rw [← key, chowGroupDegreeEquiv_chowPushforwardOfIso]
  exact (properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ (pr₁₃ sX' sY' sZ')
      (prodHom sX sZ sX' sZ' φX φZ hφX hφZ) _ rfl (pr₁₃_comp_prodBase _ _ _)
      (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (by rw [Category.assoc, prodHom_comp_prodBase,
        pr₁₃_comp_prodBase]) _
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
      (properPushforwardDescends _ _ _ _ _ _) _).symm.trans
    (properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ Ψ (pr₁₃ sX sY sZ) _
      h13.symm hΨ (pr₁₃_comp_prodBase _ _ _) _ _
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
      (properPushforwardDescends _ _ _ _ _ _) _)

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] [IsSeparated sX'] [IsSeparated sY']
    [IsSeparated sZ'] in
/-- **Composition of correspondences is natural with respect to isomorphisms over `k`**: for
isomorphisms `φX : X' ≅ X`, `φY : Y' ≅ Y`, `φZ : Z' ≅ Z` over `k`, the transport of `c' ∘ c` is
the composition of the transports, for an iso-invariant family of diagonal classes. -/
theorem correspondenceEquivOfIso_composition (hΔ : Δ.IsoInvariant) [IsProper sY] [IsProper sY']
    {d e f : ℕ} (hX : RelativeDimension sX d) (hY : RelativeDimension sY e)
    (hZ : RelativeDimension sZ f) (hX' : RelativeDimension sX' d)
    (hY' : RelativeDimension sY' e) (hZ' : RelativeDimension sZ' f) (r s : ℤ)
    (c : Correspondence (fieldChowSituation k) sX' sY' e r)
    (c' : Correspondence (fieldChowSituation k) sY' sZ' f s) :
    correspondenceEquivOfIso _ sX sZ sX' sZ' φX φZ hφX hφZ f (r + s)
        (composition k sX' sY' sZ' Δ hX' hY' hZ' r s c c') =
      composition k sX sY sZ Δ hX hY hZ r s
        (correspondenceEquivOfIso _ sX sY sX' sY' φX φY hφX hφY e r c)
        (correspondenceEquivOfIso _ sY sZ sY' sZ' φY φZ hφY hφZ f s c') := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul q c =>
    induction c' using TensorProduct.induction_on with
    | zero => simp
    | tmul q' c' =>
      rw [composition_tmul, correspondenceEquivOfIso_tmul, correspondenceEquivOfIso_tmul,
        correspondenceEquivOfIso_tmul, composition_tmul,
        chowPushforwardOfIso_compositionInt k Δ sX sY sZ sX' sY' sZ' φX φY φZ hφX hφY hφZ hΔ]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end Naturality

/-! ### A point isomorphic to the base -/

section IsoPoint

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [IsIso sP] [LocallyOfFiniteType sP]

/-- Stacks 0FG0 (2) for a point `P` isomorphic to the base: `CH_{-r}(X) ⊗ ℚ = Corrʳ(X, P)`, the
identification `Stacks.WeilCohomology.correspondenceToPointEquiv` transported along
`X ×_S P ≅ X ×_S S`. -/
def correspondenceToPointEquivOfIso (r : ℤ) :
    TensorProduct ℤ ℚ (chowGroup C sX (-r)) ≃ₗ[ℚ] Correspondence C sX sP ((0 : ℕ) : ℤ) r :=
  (correspondenceToPointEquiv C sX r).trans
    (correspondenceEquivOfIso C sX (𝟙 C.S) sX sP (𝟙 X) sP (Category.id_comp _)
      (Category.comp_id _) ((0 : ℕ) : ℤ) r).symm

/-- Stacks 0FG0 (3) for a point `P` isomorphic to the base: `CH^r(X) ⊗ ℚ = Corrʳ(P, X)`, the
identification `Stacks.WeilCohomology.correspondenceFromPointEquiv` transported along
`P ×_S X ≅ S ×_S X`. -/
def correspondenceFromPointEquivOfIso (d r : ℤ) :
    TensorProduct ℤ ℚ (chowGroup C sX (d - r)) ≃ₗ[ℚ] Correspondence C sP sX d r :=
  (correspondenceFromPointEquiv C sX d r).trans
    (correspondenceEquivOfIso C (𝟙 C.S) sX sP sX sP (𝟙 X) (Category.comp_id _)
      (Category.id_comp _) d r).symm

end IsoPoint

section IsoPointComposition

variable {X X' Y P : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sX' : X' ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sP : P ⟶ (fieldChowSituation k).S) [IsIso sP]
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] [LocallyOfFiniteType sY]
  [LocallyOfFiniteType sP] [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY]
  [IsSeparated sY] [Smooth sP] [IsSeparated sP]

omit [IsSeparated sP] in
/-- The second half of Stacks 0FG0 (2) for a point `P` isomorphic to the base: for
`c ∈ Corrˢ(X', X)` and `β ∈ CH_{-r}(X) ⊗ ℚ`, the identification
`CH_{-(s+r)}(X') ⊗ ℚ = Corr^{s+r}(X', P)` carries `c^*(β)` to `β ∘ c`. -/
theorem correspondenceToPointEquivOfIso_correspondencePullback (hΔ : Δ.IsoInvariant)
    [IsProper sX] {a b : ℕ} (hX' : RelativeDimension sX' a) (hX : RelativeDimension sX b)
    (hP : RelativeDimension sP 0) (s r : ℤ)
    (c : Correspondence (fieldChowSituation k) sX' sX b s)
    (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (-r))) :
    correspondenceToPointEquivOfIso _ sX' sP (s + r)
        ((chowGroupDegreeEquiv _ sX' (show -r - s = -(s + r) by ring)).toIntLinearEquiv.baseChange
            ℤ ℚ _ _ (correspondencePullback k sX' sX Δ hX' hX s (-r) c β)) =
      composition k sX' sX sP Δ hX' hX hP s r c (correspondenceToPointEquivOfIso _ sX sP r β) := by
  apply (correspondenceEquivOfIso _ sX' (𝟙 _) sX' sP (𝟙 X') sP (Category.id_comp _)
    (Category.comp_id _) ((0 : ℕ) : ℤ) (s + r)).injective
  rw [correspondenceEquivOfIso_composition k Δ sX' sX (𝟙 _) sX' sX sP (𝟙 X') (𝟙 X) sP
    (Category.id_comp _) (Category.id_comp _) (Category.comp_id _) hΔ hX' hX
    (relativeDimension_identity _) hX' hX hP, correspondenceEquivOfIso_id]
  simp only [correspondenceToPointEquivOfIso, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact correspondenceToPointEquiv_correspondencePullback sX' sX hΔ hX' hX s r c β

omit [IsSeparated sP] in
/-- The second half of Stacks 0FG0 (3) for a point `P` isomorphic to the base: for
`c ∈ Corrˢ(X, Y)` and `α ∈ CH^i(X) ⊗ ℚ`, the identification
`CH^{i+s}(Y) ⊗ ℚ = Corr^{i+s}(P, Y)` carries `c_*(α)` to `c ∘ α`. -/
theorem correspondenceFromPointEquivOfIso_correspondencePushforward (hΔ : Δ.IsoInvariant)
    (hΔs : Δ.IsSymmetric) [IsProper sX] {a b : ℕ} (hX : RelativeDimension sX a)
    (hY : RelativeDimension sY b) (hP : RelativeDimension sP 0) (i s : ℤ)
    (c : Correspondence (fieldChowSituation k) sX sY b s)
    (α : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX ((a : ℤ) - i))) :
    correspondenceFromPointEquivOfIso _ sY sP b (i + s)
        (correspondencePushforward k sX sY Δ hX hY s i c α) =
      composition k sP sX sY Δ hP hX hY i s (correspondenceFromPointEquivOfIso _ sX sP a i α)
        c := by
  apply (correspondenceEquivOfIso _ (𝟙 _) sY sP sY sP (𝟙 Y) (Category.comp_id _)
    (Category.id_comp _) b (i + s)).injective
  rw [correspondenceEquivOfIso_composition k Δ (𝟙 _) sX sY sP sX sY sP (𝟙 X) (𝟙 Y)
    (Category.comp_id _) (Category.id_comp _) (Category.id_comp _) hΔ
    (relativeDimension_identity _) hX hY hP hX hY, correspondenceEquivOfIso_id]
  simp only [correspondenceFromPointEquivOfIso, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact correspondenceFromPointEquiv_correspondencePushforward sX sY hΔ hΔs hX hY i s c α

end IsoPointComposition

/-- The integral Chow groups of an empty part vanish. -/
private theorem subsingleton_chowGroup_part {X : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] {d : ℕ}
    (hd : ¬ (dimPart sX d : Set X).Nonempty) (m : ℤ) :
    Subsingleton (chowGroup (fieldChowSituation k) (partBase sX d) m) :=
  have : IsEmpty (dimPart sX d).toScheme := ⟨fun y ↦ hd ⟨y.1, y.2⟩⟩
  subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) (partBase sX d) m

/-! ### Rational Chow groups of the parts -/

section ChowParts

variable {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX]

omit [IsSeparated sX] in
/-- Restricting to a part what was pushed forward from it is the identity. -/
@[simp]
theorem restrictPart_includePart (d : ℕ) (m : ℤ)
    (y : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) m)) :
    restrictPart k sX d m (includePart k sX d m y) = y := by
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul q α =>
    simp only [restrictPart, includePart, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap]
    rw [chowGroupRestrict_properChowPushforward_opens_self]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [IsSeparated sX] in
/-- Restricting to a part what was pushed forward from another part gives zero. -/
theorem restrictPart_includePart_of_ne {d d' : ℕ} (h : d ≠ d') (m : ℤ)
    (y : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) m)) :
    restrictPart k sX d' m (includePart k sX d m y) = 0 := by
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul q α =>
    simp only [restrictPart, includePart, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap]
    rw [chowGroupRestrict_properChowPushforward_opens_of_disjoint _ _ _ _
      ((isClopenDecomposition_dimPart sX).disjoint d d' h), TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

omit [IsSeparated sX] in
/-- The Chow groups of an empty part vanish. -/
theorem subsingleton_rationalChow_part {d : ℕ} (hd : ¬ (dimPart sX d : Set X).Nonempty)
    (m : ℤ) :
    Subsingleton (TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) m)) := by
  have := subsingleton_chowGroup_part k sX hd m
  infer_instance

omit [IsSeparated sX] in
/-- The parts of `X` decompose its Chow groups: a class is the sum over the nonempty parts of the
pushforwards of its restrictions. -/
theorem sum_includePart_restrictPart [CompactSpace X] (m : ℤ)
    (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX m)) :
    ∑ d ∈ (finite_setOf_nonempty_dimPart sX).toFinset,
      includePart k sX d m (restrictPart k sX d m β) = β := by
  set T := (finite_setOf_nonempty_dimPart sX).toFinset
  have hZ : ∀ α : chowGroup (fieldChowSituation k) sX m,
      ∑ d ∈ T, (have := (isClopenDecomposition_dimPart sX).isProper_ι d
        properChowPushforward (fieldChowSituation k) (partBase sX d) sX (dimPart sX d).ι rfl m
          (properPushforwardDescends _ _ _ _ _ _)
          (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m
            α)) = α := by
    intro α
    rw [← sub_eq_zero]
    refine eq_zero_of_chowGroupRestrict_eq_zero (fieldChowSituation k) sX
      (fun i : ULift.{u} ℕ ↦ partBase sX i.down) (fun i ↦ (dimPart sX i.down).ι) (fun _ ↦ rfl)
      ⟨fun i j hij ↦ by
        simpa only [Scheme.Opens.opensRange_ι] using
          (isClopenDecomposition_dimPart sX).disjoint i.down j.down
            fun h ↦ hij (ULift.ext h), by
        simp only [Scheme.Opens.opensRange_ι]
        exact (ULift.down_surjective.iSup_comp (dimPart sX)).trans
          (isClopenDecomposition_dimPart sX).iSup_eq_top⟩ m _ fun i ↦ ?_
    rw [map_sub, map_sum, sub_eq_zero]
    by_cases hi : i.down ∈ T
    · rw [Finset.sum_eq_single i.down]
      · have := (isClopenDecomposition_dimPart sX).isProper_ι i.down
        exact chowGroupRestrict_properChowPushforward_opens_self _ _ _ _ _ _
      · intro d _ hd
        have := (isClopenDecomposition_dimPart sX).isProper_ι d
        exact chowGroupRestrict_properChowPushforward_opens_of_disjoint _ _ _ _
          ((isClopenDecomposition_dimPart sX).disjoint d i.down hd) _ _ _
      · exact fun h ↦ (h hi).elim
    · have := subsingleton_chowGroup_part k sX
        (fun h ↦ hi ((Set.Finite.mem_toFinset _).2 h)) m
      exact Subsingleton.elim _ _
  induction β using TensorProduct.inductionOn with
  | tmul q α =>
    simp only [restrictPart, includePart, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap]
    rw [← TensorProduct.tmul_sum]
    exact congrArg (q ⊗ₜ[ℤ] ·) (hZ α)
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]

/-- Restriction to all the parts at once, `CH_m(X) ⊗ ℚ ⟶ ⊕_d CH_m(X_d) ⊗ ℚ`, for `X`
quasi-compact, so that only finitely many parts are nonempty. -/
def restrictParts [CompactSpace X] (m : ℤ) :
    TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX m) →ₗ[ℚ]
      DirectSum ℕ fun d ↦ TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) m) :=
  ∑ d ∈ (finite_setOf_nonempty_dimPart sX).toFinset,
    DirectSum.lof ℚ ℕ (fun d ↦ TensorProduct ℤ ℚ
      (chowGroup (fieldChowSituation k) (partBase sX d) m)) d ∘ₗ restrictPart k sX d m

omit [IsSeparated sX] in
/-- The components of the restriction to all the parts are the restrictions to the parts. -/
@[simp]
theorem restrictParts_apply [CompactSpace X] (m : ℤ)
    (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX m)) (d : ℕ) :
    restrictParts k sX m β d = restrictPart k sX d m β := by
  simp only [restrictParts, LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
    DirectSum.sum_apply]
  by_cases hd : d ∈ (finite_setOf_nonempty_dimPart sX).toFinset
  · rw [Finset.sum_eq_single d (fun d' _ hd' ↦ by
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hd')])
      (fun h ↦ (h hd).elim)]
    exact DirectSum.lof_apply ℚ _ _
  · have := subsingleton_rationalChow_part k sX
      (fun h ↦ hd ((Set.Finite.mem_toFinset _).2 h)) m
    exact Subsingleton.elim _ _

omit [IsSeparated sX] in
/-- Restricting to all the parts what was pushed forward from one part recovers it in that
part. -/
@[simp]
theorem restrictParts_includePart [CompactSpace X] (d : ℕ) (m : ℤ)
    (y : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) m)) :
    restrictParts k sX m (includePart k sX d m y) = DirectSum.lof ℚ ℕ _ d y := by
  refine DirectSum.ext fun d' ↦ ?_
  rw [restrictParts_apply]
  by_cases h : d = d'
  · subst h
    rw [restrictPart_includePart, DirectSum.lof_apply]
  · rw [restrictPart_includePart_of_ne k sX h, DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]

/-- **`CH_m(X) ⊗ ℚ = ⊕_d CH_m(X_d) ⊗ ℚ`** for a smooth scheme `X` over `k` which is
quasi-compact, through restriction to the parts and pushforward from them; only finitely many
parts are nonempty. -/
def rationalChowPartsEquiv [CompactSpace X] (m : ℤ) :
    TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX m) ≃ₗ[ℚ]
      DirectSum ℕ fun d ↦ TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) m) :=
  LinearEquiv.ofLinear (restrictParts k sX m)
    (DirectSum.toModule ℚ ℕ _ fun d ↦ includePart k sX d m)
    (DirectSum.linearMap_ext ℚ fun i ↦ LinearMap.ext fun y ↦ by simp)
    (LinearMap.ext fun β ↦ by
      simp only [restrictParts, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply,
        map_sum, DirectSum.toModule_lof, LinearMap.id_apply]
      exact sum_includePart_restrictPart k sX m β)

omit [IsSeparated sX] in
/-- `CH_m(X) ⊗ ℚ = ⊕_d CH_m(X_d) ⊗ ℚ` is restriction to all the parts. -/
@[simp]
theorem rationalChowPartsEquiv_apply [CompactSpace X] (m : ℤ)
    (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX m)) :
    rationalChowPartsEquiv k sX m β = restrictParts k sX m β :=
  rfl

omit [IsSeparated sX] in
/-- The inverse of `CH_m(X) ⊗ ℚ = ⊕_d CH_m(X_d) ⊗ ℚ` is pushforward from the parts. -/
@[simp]
theorem rationalChowPartsEquiv_symm_apply [CompactSpace X] (m : ℤ)
    (x : DirectSum ℕ fun d ↦
      TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) m)) :
    (rationalChowPartsEquiv k sX m).symm x =
      DirectSum.toModule ℚ ℕ _ (fun d ↦ includePart k sX d m) x :=
  rfl

end ChowParts

/-! ### Stacks 0FG0 (2) and (3) for schemes of mixed dimension -/

/-- The part of dimension `0` of `S` over itself is all of `S`. -/
instance isIso_partBase_id_zero (S : Scheme.{u}) : IsIso (partBase (𝟙 S) 0) :=
  haveI := isIso_dimPart_zero_ι (𝟙 S) (relativeDimension_identity S)
  inferInstance

/-- Correspondences into a part of `Spec k` of nonzero dimension vanish. -/
theorem subsingleton_correspondence_partBase_id_right {Y : Scheme.{u}}
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY] {e : ℕ} (he : e ≠ 0)
    (d r : ℤ) :
    Subsingleton (Correspondence (fieldChowSituation k) sY (partBase (𝟙 _) e) d r) :=
  have := isEmpty_dimPart_of_ne_zero (𝟙 (fieldChowSituation k).S)
    (relativeDimension_identity _) he
  subsingleton_correspondence_of_isEmpty_right _ _ _ _ _

/-- Correspondences out of a part of `Spec k` of nonzero dimension vanish. -/
theorem subsingleton_correspondence_partBase_id_left {Y : Scheme.{u}}
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY] {e : ℕ} (he : e ≠ 0)
    (d r : ℤ) :
    Subsingleton (Correspondence (fieldChowSituation k) (partBase (𝟙 _) e) sY d r) :=
  have := isEmpty_dimPart_of_ne_zero (𝟙 (fieldChowSituation k).S)
    (relativeDimension_identity _) he
  subsingleton_correspondence_of_isEmpty_left _ _ _ _ _

section Blocks

variable {X Y Z : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sZ : Z ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [Smooth sZ] [IsSeparated sZ]

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- Composition of a pure block `c ∈ Corrʳ(X_d, Y_e)` with a correspondence `c'` whose
`e`-component is the pure block `y ∈ Corrˢ(Y_e, Z_f)`: the equidimensional composition `y ∘ c`,
in the block `(d, f)`. -/
theorem comp_lof_lof_of_apply_eq_lof [IsProper sY] (r s : ℤ) (d e f : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (c' : Corr k sY sZ s)
    (y : Correspondence (fieldChowSituation k) (partBase sY e) (partBase sZ f) f s)
    (hy : c' e = DirectSum.lof ℚ ℕ _ f y) :
    comp k sX sY sZ Δ r s (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c)) c' =
      DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ f
        (composition k (partBase sX d) (partBase sY e) (partBase sZ f) Δ
          (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
          (relativeDimension_partBase sZ f) r s c y)) := by
  have : DirectSum.component ℚ ℕ _ e c' = DirectSum.lof ℚ ℕ _ f y := by
    rw [← DirectSum.apply_eq_component]
    exact hy
  simp [comp, compBlock, this]

omit [IsSeparated sX] in
/-- Pushforward from a part commutes with the transport of rational Chow classes along an
equality of degrees. -/
theorem baseChange_chowGroupDegreeEquiv_includePart (d : ℕ) {m m' : ℤ} (h : m = m')
    (x : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) m)) :
    (chowGroupDegreeEquiv _ sX h).toIntLinearEquiv.baseChange ℤ ℚ _ _ (includePart k sX d m x) =
      includePart k sX d m'
        ((chowGroupDegreeEquiv _ (partBase sX d) h).toIntLinearEquiv.baseChange ℤ ℚ _ _ x) := by
  subst h
  rw [baseChange_chowGroupDegreeEquiv_self, baseChange_chowGroupDegreeEquiv_self]

omit [IsSeparated sX] [IsSeparated sY] in
/-- Pullback by a pure block `c ∈ Corrʳ(X_d, Y_e)`: `c^*(β|_{Y_e})` pushed forward from `X_d`. -/
theorem pullback_lof_lof [IsProper sX] [IsProper sY] (r m : ℤ) (d e : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sY m)) :
    pullback k sX sY Δ r m (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c)) β =
      includePart k sX d (m - r)
        (correspondencePullback k (partBase sX d) (partBase sY e) Δ
          (relativeDimension_partBase sX d) (relativeDimension_partBase sY e) r m c
          (restrictPart k sY e m β)) := by
  simp [pullback]

omit [IsSeparated sX] [IsSeparated sY] in
/-- Pushforward by a pure block `c ∈ Corrʳ(X_d, Y_e)` of a class supported on `X_d`. -/
theorem pushforward_lof_lof_lof [IsProper sX] (r i : ℤ) (d e : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (a : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))) :
    pushforward k sX sY Δ r i (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c))
        (DirectSum.lof ℚ ℕ _ d a) =
      DirectSum.lof ℚ ℕ _ e
        (correspondencePushforward k (partBase sX d) (partBase sY e) Δ
          (relativeDimension_partBase sX d) (relativeDimension_partBase sY e) r i c a) := by
  simp [pushforward]

omit [IsSeparated sX] [IsSeparated sY] in
/-- Pushforward by a pure block `c ∈ Corrʳ(X_d, Y_e)` of a class supported on another part
vanishes. -/
theorem pushforward_lof_lof_lof_of_ne [IsProper sX] (r i : ℤ) {d d' : ℕ} (h : d' ≠ d) (e : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (a : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d') ((d' : ℤ) - i))) :
    pushforward k sX sY Δ r i (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c))
        (DirectSum.lof ℚ ℕ _ d' a) = 0 := by
  simp [pushforward, DirectSum.component.of, h]

end Blocks

section MixedPoint

variable {X X' Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sX' : X' ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]

/-- **Stacks Project, Tag 0FG0 (2)**, for a smooth proper scheme `X` over `k` of arbitrary,
not necessarily constant, dimension: the canonical `ℚ`-linear isomorphism

  `CH_{-r}(X) ⊗ ℚ = Corrʳ(X, Spec k)`.

It decomposes `CH_{-r}(X) ⊗ ℚ = ⊕_d CH_{-r}(X_d) ⊗ ℚ` over the finitely many nonempty parts
of `X`, and identifies each summand with `Corrʳ(X_d, Spec k)` by
`Stacks.WeilCohomology.correspondenceToPointEquiv`, transported to the part of dimension `0` of
`Spec k`; the other parts of `Spec k` are empty. -/
def corrToPointEquiv [IsProper sX] (r : ℤ) :
    TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (-r)) ≃ₗ[ℚ]
      Corr k sX (𝟙 (fieldChowSituation k).S) r :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  (rationalChowPartsEquiv k sX (-r)).trans
    ((DirectSum.congrLinearEquiv fun d ↦
        correspondenceToPointEquivOfIso _ (partBase sX d) (partBase (𝟙 _) 0) r).trans
      (DirectSum.congrLinearEquiv fun d ↦ (directSumEquivSummand 0 fun _ he ↦
        subsingleton_correspondence_partBase_id_right k (partBase sX d) he _ r).symm))

omit [IsSeparated sX] in
/-- The components of the identification `CH_{-r}(X) ⊗ ℚ = Corrʳ(X, Spec k)`: the class of
`β|_{X_d}` in `Corrʳ(X_d, Spec k)`. -/
theorem corrToPointEquiv_apply [IsProper sX] (r : ℤ)
    (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (-r))) (d : ℕ) :
    corrToPointEquiv k sX r β d = DirectSum.lof ℚ ℕ _ 0
      (correspondenceToPointEquivOfIso _ (partBase sX d) (partBase (𝟙 _) 0) r
        (restrictPart k sX d (-r) β)) := by
  simp [corrToPointEquiv, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_apply]

omit [IsSeparated sX] in
/-- The identification `CH_{-r}(X) ⊗ ℚ = Corrʳ(X, Spec k)` on a class pushed forward from a
part `X_d`. -/
theorem corrToPointEquiv_includePart [IsProper sX] (r : ℤ) (d : ℕ)
    (w : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) (-r))) :
    corrToPointEquiv k sX r (includePart k sX d (-r) w) = DirectSum.lof ℚ ℕ _ d
      (DirectSum.lof ℚ ℕ _ 0
        (correspondenceToPointEquivOfIso _ (partBase sX d) (partBase (𝟙 _) 0) r w)) := by
  simp [corrToPointEquiv, DirectSum.coe_congrLinearEquiv]

omit [IsSeparated sX] in
/-- The correspondences out of a part of `Spec k` of nonzero dimension vanish. -/
theorem subsingleton_corr_partBase_id_left {d : ℕ} (hd : d ≠ 0) (r : ℤ) :
    Subsingleton (DirectSum ℕ fun e : ℕ ↦
      Correspondence (fieldChowSituation k) (partBase (𝟙 _) d) (partBase sX e) e r) :=
  ⟨fun _ _ ↦ DirectSum.ext fun e ↦
    (subsingleton_correspondence_partBase_id_left k (partBase sX e) hd _ r).elim _ _⟩

/-- **Stacks Project, Tag 0FG0 (3)**, for a smooth scheme `X` over `k` of arbitrary, not
necessarily constant, dimension: the canonical `ℚ`-linear isomorphism

  `CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)`,

where `CH^r(X) ⊗ ℚ = ⊕_e CH_{e-r}(X_e) ⊗ ℚ`. Each summand is identified with
`Corrʳ(Spec k, X_e)` by `Stacks.WeilCohomology.correspondenceFromPointEquiv`, transported to the
part of dimension `0` of `Spec k`; the other parts of `Spec k` are empty. -/
def corrFromPointEquiv (r : ℤ) :
    CodimChow k sX r ≃ₗ[ℚ] Corr k (𝟙 (fieldChowSituation k).S) sX r :=
  (DirectSum.congrLinearEquiv fun e ↦
      correspondenceFromPointEquivOfIso _ (partBase sX e) (partBase (𝟙 _) 0) e r).trans
    (directSumEquivSummand (M := fun d : ℕ ↦ DirectSum ℕ fun e : ℕ ↦
        Correspondence (fieldChowSituation k) (partBase (𝟙 _) d) (partBase sX e) e r) 0
      fun _ hd ↦ subsingleton_corr_partBase_id_left k sX hd r).symm

omit [IsSeparated sX] in
/-- The identification `CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)` on a class supported on a part `X_e`. -/
theorem corrFromPointEquiv_lof (r : ℤ) (e : ℕ)
    (a : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX e) ((e : ℤ) - r))) :
    corrFromPointEquiv k sX r (DirectSum.lof ℚ ℕ _ e a) = DirectSum.lof ℚ ℕ _ 0
      (DirectSum.lof ℚ ℕ _ e
        (correspondenceFromPointEquivOfIso _ (partBase sX e) (partBase (𝟙 _) 0) e r a)) := by
  simp [corrFromPointEquiv, DirectSum.coe_congrLinearEquiv]

/-- **Stacks Project, Tag 0FG0 (2), second half**, for smooth proper schemes `X'`, `X` over `k`
of arbitrary dimension: pullback by correspondences corresponds to composition. For
`c ∈ Corrˢ(X', X)` and `β ∈ CH_{-r}(X) ⊗ ℚ`, the identification
`CH_{-(s+r)}(X') ⊗ ℚ = Corr^{s+r}(X', Spec k)` carries `c^*(β)` to `β ∘ c`, for an iso-invariant
family of diagonal classes. -/
theorem corrToPointEquiv_pullback (hΔ : Δ.IsoInvariant) [IsProper sX'] [IsProper sX] (s r : ℤ)
    (c : Corr k sX' sX s) (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (-r))) :
    corrToPointEquiv k sX' (s + r)
        ((chowGroupDegreeEquiv _ sX' (show -r - s = -(s + r) by ring)).toIntLinearEquiv.baseChange
          ℤ ℚ _ _ (pullback k sX' sX Δ s (-r) c β)) =
      comp k sX' sX (𝟙 _) Δ s r c (corrToPointEquiv k sX r β) := by
  induction c using Corr.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | lof d' d c =>
    rw [pullback_lof_lof, baseChange_chowGroupDegreeEquiv_includePart, corrToPointEquiv_includePart,
      comp_lof_lof_of_apply_eq_lof k Δ sX' sX (𝟙 _) s r d' d 0 c _ _
        (corrToPointEquiv_apply k sX r β d)]
    have h2 := correspondenceToPointEquivOfIso_correspondencePullback k Δ (partBase sX d)
      (partBase sX' d') (partBase (𝟙 _) 0) hΔ (relativeDimension_partBase sX' d')
      (relativeDimension_partBase sX d) (relativeDimension_partBase (𝟙 _) 0) s r c
      (restrictPart k sX d (-r) β)
    exact congrArg (DirectSum.lof ℚ ℕ _ d') (congrArg (DirectSum.lof ℚ ℕ _ 0) h2)

/-- The second half of Stacks 0FG0 (3) on a pure block `c ∈ Corrˢ(X_d, Y_e)` and a class
`a ∈ CH^i(X_{d'}) ⊗ ℚ`. -/
theorem corrFromPointEquiv_pushforward_lof_lof_lof (hΔ : Δ.IsoInvariant) (hΔs : Δ.IsSymmetric)
    [IsProper sX] (i s : ℤ) (d e : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e s) (d' : ℕ)
    (a : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d') ((d' : ℤ) - i))) :
    corrFromPointEquiv k sY (i + s) (pushforward k sX sY Δ s i
        (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c)) (DirectSum.lof ℚ ℕ _ d' a)) =
      comp k (𝟙 _) sX sY Δ i s (corrFromPointEquiv k sX i (DirectSum.lof ℚ ℕ _ d' a))
        (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c)) := by
  rw [corrFromPointEquiv_lof k sX i d' a]
  by_cases h : d' = d
  · subst h
    rw [pushforward_lof_lof_lof, corrFromPointEquiv_lof k sY (i + s) e, comp_lof_lof_lof_lof]
    exact congrArg (DirectSum.lof ℚ ℕ _ 0) (congrArg (DirectSum.lof ℚ ℕ _ e)
      (correspondenceFromPointEquivOfIso_correspondencePushforward k Δ (partBase sX d')
        (partBase sY e) (partBase (𝟙 _) 0) hΔ hΔs (relativeDimension_partBase sX d')
        (relativeDimension_partBase sY e) (relativeDimension_partBase (𝟙 _) 0) i s c a))
  · rw [pushforward_lof_lof_lof_of_ne k Δ sX sY s i h e c a, map_zero,
      comp_lof_lof_lof_of_ne k (𝟙 _) sX sY Δ i s 0 d' d h]

set_option maxHeartbeats 1000000 in
/-- **Stacks Project, Tag 0FG0 (3), second half**, for smooth schemes `X`, `Y` over `k` of
arbitrary dimension, `X` proper: pushforward by correspondences corresponds to composition. For
`c ∈ Corrˢ(X, Y)` and `α ∈ CH^i(X) ⊗ ℚ`, the identification
`CH^{i+s}(Y) ⊗ ℚ = Corr^{i+s}(Spec k, Y)` carries `c_*(α)` to `c ∘ α`, for an iso-invariant and
symmetric family of diagonal classes. -/
theorem corrFromPointEquiv_pushforward (hΔ : Δ.IsoInvariant) (hΔs : Δ.IsSymmetric)
    [IsProper sX] (i s : ℤ) (c : Corr k sX sY s) (α : CodimChow k sX i) :
    corrFromPointEquiv k sY (i + s) (pushforward k sX sY Δ s i c α) =
      comp k (𝟙 _) sX sY Δ i s (corrFromPointEquiv k sX i α) c := by
  induction c using Corr.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | lof d e c =>
    induction α using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [LinearMap.map_add (pushforward k sX sY Δ s i _), LinearEquiv.map_add, hx, hy,
        LinearEquiv.map_add, LinearMap.map_add₂]
    | of d' a =>
      exact corrFromPointEquiv_pushforward_lof_lof_lof k Δ sX sY hΔ hΔs i s d e c d' a

end MixedPoint

end Stacks.WeilCohomology
