module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Curves.Pushout
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic
public import StacksFrontier.AlgebraicGeometry.Pushout.FiniteType
public import StacksFrontier.AlgebraicGeometry.Pushout.Separation

/-!
# Pushouts of curves over a field

Let `k` be a field and consider a solid diagram of schemes over `k`

```
  Z ---i--> X
  |
  j
  |
  v
  Y
```

subject to the four conditions of [Stacks Project, Tag 0E35]:

* (a) `X` is separated of finite type over `k` of dimension `≤ 1`;
* (b) `i : Z ⟶ X` is a closed immersion;
* (c) `Z` and `Y` are finite over `Spec k`;
* (d) `j : Z ⟶ Y` is surjective.

Against the notation of [Stacks Project, Tag 0E35] the translation is `Z = Z'`, `X = X'` and
`Y = Z`; the source's `i : Z ⟶ X` is the map `b : Y ⟶ P` here and its `a : X' ⟶ X` is
`a : X ⟶ P`.

This file proves every conclusion the section draws: every finite set of points of `X` lies in
an affine open ([Stacks Project, Tag 09NN]); the pushout `P = Y ⨿_Z X` exists in the category of
schemes ([Stacks Project, Tag 0E25], via `AlgebraicGeometry.curvePushoutSituation`); `b` is a
closed immersion; `a` is integral and surjective; `P` is separated
([Stacks Project, Tag 0E26]) and of finite type ([Stacks Project, Tag 0E27]) over `k`; `a` is
finite ([Stacks Project, Tags 01WJ, 01T8]); and `P` is proper over `k` when `X` is
([Stacks Project, Tag 03GN]).

## Main results

* `AlgebraicGeometry.exists_pushout_of_curve`: [Stacks Project, Tag 0E35].

## References

* [Stacks Project, Tag 0E35](https://stacks.math.columbia.edu/tag/0E35)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- In the situation of [Stacks Project, Tag 0ECI], if `j : Z ⟶ Y` is surjective then the
canonical map `X ⟶ Y ⨿_Z X` is surjective: the two canonical maps jointly cover the pushout, and
every point in the image of `Y` comes from `Z`, hence from `X`. -/
theorem pushoutInl_surjective_of_surjective
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    [Surjective s.j] : Surjective (pushoutInl s) := by
  refine ⟨fun p ↦ ?_⟩
  obtain ⟨w, rfl⟩ := (pushoutCoprodDesc_surjective s).surj p
  obtain ⟨(y | x), rfl⟩ := (coprodMk s.Y s.X).surjective w
  · obtain ⟨z, rfl⟩ := ‹Surjective s.j›.surj y
    refine ⟨s.i z, ?_⟩
    have hw := (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
    rw [coprodMk_inl, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      coprod.inl_desc]
    exact congrArg (fun f : s.Z ⟶ pushoutScheme s ↦ f z) hw
  · refine ⟨x, ?_⟩
    rw [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_desc]

/-- In the situation of [Stacks Project, Tag 0ECI] over a field `k`, with `X` separated of finite
type over `k`, `Y` and `Z` finite over `k`, and `j` surjective, the pushout `Y ⨿_Z X` is
separated and of finite type over `k`, the map `X ⟶ Y ⨿_Z X` is finite and surjective, and the
pushout is proper over `k` when `X` is. -/
theorem pushout_properties_of_field (k : Type u) [Field k]
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (hS : s.S = Spec (.of k))
    [IsSeparated s.pX] [LocallyOfFiniteType s.pX] [QuasiCompact s.pX]
    [IsFinite s.pY] [IsFinite s.pZ] [Surjective s.j] :
    Surjective (pushoutInl s) ∧ IsSeparated (pushoutToBase s) ∧
      (LocallyOfFiniteType (pushoutToBase s) ∧ QuasiCompact (pushoutToBase s)) ∧
      IsFinite (pushoutInl s) ∧ (IsProper s.pX → IsProper (pushoutToBase s)) := by
  have hinl : pushoutInl s ≫ pushoutToBase s = s.pX :=
    (pushoutAlongClosedImmersionAndIntegral s).isPushout.inl_desc _ _ _
  have : IsLocallyNoetherian s.S := by rw [hS]; infer_instance
  have : CompactSpace s.S := by rw [hS]; infer_instance
  have : QuasiSeparatedSpace s.S := by rw [hS]; infer_instance
  have hsurj := pushoutInl_surjective_of_surjective s
  have hlftInl : LocallyOfFiniteType (pushoutInl s) := by
    have : LocallyOfFiniteType (pushoutInl s ≫ pushoutToBase s) := by
      rw [hinl]; infer_instance
    exact locallyOfFiniteType_of_comp _ (pushoutToBase s)
  have hqc : QuasiCompact (pushoutToBase s) := by
    have : CompactSpace s.X := (quasiCompact_iff_compactSpace s.pX).mp inferInstance
    have : CompactSpace (pushoutScheme s) := hsurj.surj.compactSpace (pushoutInl s).continuous
    exact (quasiCompact_iff_compactSpace _).mpr this
  refine ⟨hsurj, inferInstance, ⟨inferInstance, hqc⟩,
    IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _ |>.mpr ⟨inferInstance, hlftInl⟩,
    fun hP ↦ ?_⟩
  have : LocallyOfFiniteType (pushoutToBase s) := inferInstance
  exact isProper_of_isProper_of_surjective (pushoutInl s) (pushoutToBase s) s.pX hinl

/-- **Stacks Project, Tag 0E35.** Let `k` be a field, `X` separated of finite type over `k` of
dimension `≤ 1`, `i : Z ⟶ X` a closed immersion, `Z` and `Y` finite over `Spec k` and
`j : Z ⟶ Y` surjective, all over `k`.  Then every finite set of points of `X` lies in an affine
open, and there is a scheme `P` over `k` with maps `a : X ⟶ P`, `b : Y ⟶ P` over `k` such that

1. the square `i, j, a, b` is a pushout in the category of schemes;
2. `b` is a closed immersion;
3. `a` is integral and surjective;
4. `P` is separated over `k`;
5. `P` is of finite type (locally of finite type and quasi-compact) over `k`;
6. `a` is finite;
7. if `X` is proper over `k`, then so is `P`.

The pushout is the one of [Stacks Project, Tag 0E25] for the situation
`AlgebraicGeometry.curvePushoutSituation`; (2) and the integrality in (3) are part of 0E25,
(4) is [Stacks Project, Tag 0E26] and the local finite type in (5) is
[Stacks Project, Tag 0E27]. -/
@[stacks 0E35]
theorem exists_pushout_of_curve
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    (∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
    ∃ (P : Scheme.{u}) (a : X ⟶ P) (b : Y ⟶ P) (pP : P ⟶ Spec (.of k)),
      IsPushout i j a b ∧ a ≫ pP = pX ∧ b ≫ pP = pY ∧
      IsClosedImmersion b ∧ (IsIntegralHom a ∧ Surjective a) ∧
      IsSeparated pP ∧ (LocallyOfFiniteType pP ∧ QuasiCompact pP) ∧ IsFinite a ∧
      (IsProper pX → IsProper pP) := by
  refine ⟨fun F ↦ ?_, ?_⟩
  · have : Scheme.IsSeparated X := Scheme.IsSeparated.of_isSeparated pX
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
    have hcomp : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
      intro U hU
      have : CompactSpace U := isCompact_iff_compactSpace.mp hU
      have : IsNoetherian U.toScheme := ⟨⟩
      exact finite_irreducibleComponents_of_isNoetherian
    obtain ⟨U, hU, hmem⟩ :=
      exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components
        X hcomp (fun x : F ↦ x.1) (fun _ ↦ inferInstance) (fun x ↦
          krullDimLE_of_coheight_le (n := 1)
            (by exact_mod_cast (coheight_le_topologicalKrullDim x.1).trans hdim))
    exact ⟨U, hU, fun x hx ↦ hmem ⟨x, hx⟩⟩
  let s := curvePushoutSituation k pX pY pZ i j hi hj hdim
  have hPO : IsPushout i j (pushoutInl s) (pushoutInr s) :=
    (pushoutAlongClosedImmersionAndIntegral s).isPushout
  have : IsSeparated s.pX := inferInstanceAs (IsSeparated pX)
  have : LocallyOfFiniteType s.pX := inferInstanceAs (LocallyOfFiniteType pX)
  have : QuasiCompact s.pX := inferInstanceAs (QuasiCompact pX)
  have : IsFinite s.pY := inferInstanceAs (IsFinite pY)
  have : IsFinite s.pZ := inferInstanceAs (IsFinite pZ)
  have : Surjective s.j := inferInstanceAs (Surjective j)
  obtain ⟨hsurj, hsep, hft, hfin, hprop⟩ := pushout_properties_of_field k s rfl
  exact ⟨pushoutScheme s, pushoutInl s, pushoutInr s, pushoutToBase s, hPO,
    hPO.inl_desc _ _ _, hPO.inr_desc _ _ _, pushoutInr_isClosedImmersion s,
    ⟨pushoutInl_isIntegralHom s, hsurj⟩, hsep, hft, hfin, hprop⟩

end AlgebraicGeometry

end
