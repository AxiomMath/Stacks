module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Truncated isomorphisms in a derived category, read off homology

Let `C` be an abelian category with a derived category and let `φ : K ⟶ L` be a morphism of
`D(C)`. The morphism `τ_{≤a}φ` obtained by applying the truncation functor of the canonical
t-structure is invertible exactly when `H^i(φ)` is invertible for every `i ≤ a`; and when `φ` is
the first map of a distinguished triangle `K ⟶ L ⟶ N ⟶ K[1]`, that condition is sandwiched
between the vanishing of `H^i(N)` for `i ≤ a` and its vanishing for `i ≤ a - 1`.

Both bounds are sharp and the gap of one degree between them is the whole subtlety of the
criteria of [Stacks, Tag 0GEJ] and [Stacks, Tag 0GEK], where `φ` is the unit
`E ⟶ Rj_*(E|_U)` of a derived pullback–pushforward adjunction along an open immersion:
truncation is not exact, so only the two one-sided implications above are available.

For [Stacks, Tag 0GEJ] the published summary reads "(2) implies (1) and (1) implies (2) with
`a` replaced by `a + 1`". Whether `a + 1` is the sharp
index for 0GEJ is a separate question, a **possible erratum**, and is
not settled here, so no claim is made below that 0GEJ is sharp as published. **For [Stacks,
Tag 0GEK] the published summary is not correct, and the direction it gets wrong is the first
one.** Writing `P a` for 0GEK's statement (1) and `Q a` for its statement (2), the sandwich above
gives `Q a ↔ τ_{≤a-1}N = 0` together with `τ_{≤a}N = 0 → P a → τ_{≤a-1}N = 0`, so `Q a` supplies
strictly less than `P a` needs and `Q a → P a` does not follow. The sharp pair is instead

  `P a → Q a`  and  `Q (a+1) → P a`,

which is what `Stacks.Koszul.Truncation.hom_koszul_eq_zero_of_truncLE_restriction` and
`Stacks.Koszul.Truncation.truncLE_restriction_of_hom_koszul_eq_zero` prove. Both indices are
sharp, by two counterexamples over `A = k[x]` with `f = (x)`, `U = D(x)` and `K` the Koszul
complex on `x`: for `E = 𝒪_X` one has `Q 0` but not `P 0`, since `Rj_*𝒪_U = A[1/x]` and
`A → A[1/x]` is not invertible while `Hom(K⟦m⟧, 𝒪_X) = 0` for every `m ≥ 0`; and for `E` the
structure sheaf of the origin one has `P (-1)` but not `Q 0`, since `E|_U = 0` while
`K ↠ H^0(K) = A/x = E` is nonzero, which rules out strengthening the first implication to
`P a → Q (a+1)`.

The lemmas in this file are stated and used in the sharp form, and are unaffected; it was only
the characterisation of 0GEK in this paragraph that was wrong.

## Main results

* `Stacks.DerivedTruncation.isIso_homologyMap_truncLEι` — the comparison
  `(τ_{≤a}K) ⟶ K` is a homology isomorphism in every degree `i ≤ a`.
* `Stacks.DerivedTruncation.isZero_homology_truncLE_obj` — and `τ_{≤a}K` has no homology above
  `a`.
* `Stacks.DerivedTruncation.isIso_truncLE_map_iff_forall_isIso_homologyMap` — `τ_{≤a}φ` is
  invertible if and only if `H^i(φ)` is invertible for all `i ≤ a`.
* `Stacks.DerivedTruncation.isIso_truncLE_map_of_isZero_homology_obj₃` and
  `Stacks.DerivedTruncation.isZero_homology_obj₃_of_isIso_truncLE_map` — the two one-sided
  implications relating invertibility of `τ_{≤a}(T.mor₁)` to the vanishing of the homology of
  the third vertex of a distinguished triangle.
* `Stacks.DerivedTruncation.subsingleton_hom_rightAdjoint_obj_of_isZero` — a source killed by a
  left adjoint sees nothing in the image of the right adjoint.

## Implementation notes

Everything here is stated for an arbitrary `[HasDerivedCategory.{w} C]`, never for
`CategoryTheory.HasDerivedCategory.standard`. The canonical t-structure
`CategoryTheory.DerivedCategory.TStructure.t` and the homology sequence of a distinguished
triangle are both model-agnostic in Mathlib, so there is nothing to gain by fixing a model and
something to lose: a statement proved at the standard model says nothing about the locally
small one of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, the two derived
categories being equivalent and not equal.

`isIso_homologyMap_truncLEι` exists twice in this repository as a `private` declaration —
`StacksFrontier/Homology/DerivedComplete/CompletionSequencesComparison.lean` has it for
`HasDerivedCategory C` behind two `backward.*` transparency options, and a proof
of [Stacks, Tag 09IR] re-derives it for `D(𝒪_{Spec A})`. The form proved here is the common
generalisation and needs no transparency option: the reason the options are wanted is the
`change` step identifying `T.mor₁` of the truncation triangle with `(τ_{≤a}ι).app K`, and
naming the triangle with `triangleLEGE a (a + 1) rfl`, whose `mor₁` is that natural
transformation by construction, removes it.

## References

* [Stacks Project, Tag 0GEK](https://stacks.math.columbia.edu/tag/0GEK)
* [Stacks Project, Tag 0GEJ](https://stacks.math.columbia.edu/tag/0GEJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace Stacks.DerivedTruncation

universe w v u

section Truncation

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If `H^{i-1}` and `H^i` of the third vertex of a distinguished triangle vanish, then `H^i` of
its first map is invertible. -/
private theorem isIso_homologyMap_mor₁_of_isZero (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (i : ℤ)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor C (i - 1)).obj T.obj₃))
    (h₂ : IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 (h₂.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2
      (h₁.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- **The truncation comparison is a homology isomorphism in low degrees.** For `K` an object of
`D(C)` and `i ≤ a`, the map `H^i((τ_{≤a}K)) ⟶ H^i(K)` induced by the canonical morphism
`τ_{≤a}K ⟶ K` is invertible.

The truncation triangle `τ_{≤a}K ⟶ K ⟶ τ_{≥a+1}K ⟶` has third vertex with no homology in
degrees `< a + 1`, so the homology sequence forces the first map to be both mono and epi in
degree `i`. -/
theorem isIso_homologyMap_truncLEι (K : DerivedCategory C) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLEι a).app K)) := by
  let T := (DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj K
  have hT : T ∈ distTriang (DerivedCategory C) :=
    DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl K
  have hge : T.obj₃.IsGE (a + 1) :=
    inferInstanceAs (((DerivedCategory.TStructure.t.truncGE (a + 1)).obj K).IsGE (a + 1))
  exact isIso_homologyMap_mor₁_of_isZero T hT i
    (DerivedCategory.isZero_of_isGE T.obj₃ (a + 1) (i - 1) (by omega))
    (DerivedCategory.isZero_of_isGE T.obj₃ (a + 1) i (by omega))

/-- **A truncated morphism is invertible exactly when it is a homology isomorphism in every
degree below the truncation.** This is the bridge that turns the derived-category condition
appearing in [Stacks, Tag 0GEK] — "the canonical map `τ_{≤a}E ⟶ τ_{≤a}Rj_*(E|_U)` is an
isomorphism" — into a statement about cohomology sheaves, where the Koszul criterion can be
applied. -/
theorem isIso_truncLE_map_iff_forall_isIso_homologyMap {K L : DerivedCategory C} (φ : K ⟶ L)
    (a : ℤ) :
    IsIso ((DerivedCategory.TStructure.t.truncLE a).map φ) ↔
      ∀ i : ℤ, i ≤ a → IsIso ((DerivedCategory.homologyFunctor C i).map φ) := by
  have hsq : ∀ i : ℤ,
      (DerivedCategory.homologyFunctor C i).map
          ((DerivedCategory.TStructure.t.truncLE a).map φ) ≫
        (DerivedCategory.homologyFunctor C i).map
          ((DerivedCategory.TStructure.t.truncLEι a).app L) =
      (DerivedCategory.homologyFunctor C i).map
          ((DerivedCategory.TStructure.t.truncLEι a).app K) ≫
        (DerivedCategory.homologyFunctor C i).map φ := by
    intro i
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLEι a).naturality φ)
  refine ⟨fun h i hi => ?_, fun h => ?_⟩
  · have := isIso_homologyMap_truncLEι K a i hi
    have := isIso_homologyMap_truncLEι L a i hi
    exact IsIso.of_isIso_fac_left (hsq i).symm
  · rw [DerivedCategory.isIso_iff]
    intro i
    by_cases hi : i ≤ a
    · have := isIso_homologyMap_truncLEι K a i hi
      have := isIso_homologyMap_truncLEι L a i hi
      have := h i hi
      exact IsIso.of_isIso_fac_right (hsq i)
    · exact (DerivedCategory.isZero_of_isLE _ a i (by omega)).isIso
        (DerivedCategory.isZero_of_isLE _ a i (by omega)) _

/-- **Vanishing homology of the cone up to `a` makes the truncated map invertible.** For a
distinguished triangle `T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃ ⟶ T.obj₁[1]`, if `H^i(T.obj₃) = 0` for every
`i ≤ a` then `τ_{≤a}(T.mor₁)` is an isomorphism.

This is the implication "(2) implies (1)" of [Stacks, Tag 0GEK], stripped of its geometry. -/
theorem isIso_truncLE_map_of_isZero_homology_obj₃ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (a : ℤ)
    (h : ∀ i : ℤ, i ≤ a → IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃)) :
    IsIso ((DerivedCategory.TStructure.t.truncLE a).map T.mor₁) := by
  rw [isIso_truncLE_map_iff_forall_isIso_homologyMap]
  intro i hi
  exact isIso_homologyMap_mor₁_of_isZero T hT i (h (i - 1) (by omega)) (h i hi)

/-- **An invertible truncated map kills the homology of the cone up to `a - 1`, and no
further.** For a distinguished triangle `T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃ ⟶ T.obj₁[1]` with
`τ_{≤a}(T.mor₁)` an isomorphism, `H^i(T.obj₃) = 0` for every `i` with `i + 1 ≤ a`.

This is the implication "(1) implies (2) with `a` replaced by `a - 1`" of
[Stacks, Tag 0GEK], stripped of its geometry. The lost degree is real: invertibility of
`H^a(T.mor₁)` only makes `H^a(T.obj₃)` the kernel of `H^{a+1}(T.mor₁)`, about which the
hypothesis says nothing. -/
theorem isZero_homology_obj₃_of_isIso_truncLE_map (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (a : ℤ)
    (h : IsIso ((DerivedCategory.TStructure.t.truncLE a).map T.mor₁)) (i : ℤ) (hi : i + 1 ≤ a) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃) := by
  rw [isIso_truncLE_map_iff_forall_isIso_homologyMap] at h
  have h₂ : (DerivedCategory.homologyFunctor C i).map T.mor₂ = 0 := by
    rw [← DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    have := h i (by omega)
    infer_instance
  have h₃ : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := by
    rw [← DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1) rfl]
    have := h (i + 1) hi
    infer_instance
  exact (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl).isZero_of_both_zeros h₂ h₃

end Truncation

section Adjunction

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

/-- **A source killed by the left adjoint sees nothing in the image of the right adjoint.** If
`L ⊣ R` and `L.obj X` is a zero object, then `X ⟶ R.obj Y` has at most one element for every
`Y`.

This is the step `Hom(K[-n], Rj_*(E|_U)) = 0` of [Stacks, Tag 0GEK] and [Stacks, Tag 0GEJ]: the
Koszul complex restricts to zero on the open complement of the zero locus of its sequence, so
the adjunction makes every map from it into a derived pushforward from that open vanish. -/
theorem subsingleton_hom_rightAdjoint_obj_of_isZero {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R)
    {X : D} (hX : IsZero (L.obj X)) (Y : E) : Subsingleton (X ⟶ R.obj Y) :=
  ⟨fun _f _g => (adj.homEquiv X Y).symm.injective (hX.eq_of_src _ _)⟩

end Adjunction

end Stacks.DerivedTruncation

end
