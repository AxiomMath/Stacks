module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassIntegral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilThreeAxioms
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupExcess
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIdempotent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ScalarExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `γ([Z]) ∪ a = 0` when `a|_Z = 0`: the argument of Lemma 0FII

Let data (D0), (D1), (D2') satisfy (A1), (A3), (A4) and (A7), and let `γ` be the cycle class map
of Tag 0FIF. For a closed immersion `i : Z ⟶ X` of smooth projective schemes over `k` with
nowhere dense image, let `b : X' ⟶ X` be the blowing up in `Z`, with exceptional divisor `E`.
If `b^![Z] = [E] · θ` in `CH^r(X')` for some `θ ∈ CH^{r-1}(X')` (the first relation of Lemma
0FIH), then `γ([Z]) ∪ a = 0` for every `a ∈ H^*(X)` with `a|_Z = 0`.

This is the proof of Lemma 0FII: by (A7) it suffices that `b^*(γ([Z]) ∪ a) = 0`, and
`b^*γ([Z]) = γ(b^![Z]) = γ([E]) ∪ γ(θ) = c₁^H(𝒪_{X'}(E)) ∪ γ(θ)`, while `b^*a` restricts to `0`
on `E`, so `b^*a ∪ c₁^H(𝒪_{X'}(E)) = 0` by (A4).

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.exceptionalDivisor`: the ideal sheaf of the
  exceptional divisor `E ⊂ X'`, an effective Cartier divisor.

## Main results

* `cup_codimensionCycleClass_eq_zero_of_isOpenImmersion`: the case of codimension `0`, `Z` open
  and closed in `X`, from (A1): `γ([Z])` restricts to `0` on the complement of `Z`.
* `cup_codimensionCycleClass_eq_zero_of_blowup` (namespace
  `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter`): the vanishing,
  granted the relation `b^![Z] = [E] · θ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

/-- **The exceptional divisor `E ⊂ X'`** of the blowing up `b : X' ⟶ X` in `Z`, as an ideal sheaf
of `X'`: the inverse image of the ideal of `Z`. It is an effective Cartier divisor
(`isEffectiveCartierDivisor_exceptionalIdeal`) whose closed subscheme is `E`
(`exceptionalToSubscheme`). -/
@[sga "7 XVIII 2.1"]
abbrev exceptionalDivisor : (blowupObj i).obj.left.IdealSheafData :=
  i.hom.left.ker.comap (Stacks.Blowup.blowUpToBase i.hom.left.ker)

/-- **`[E] = [D]`**: the class of the exceptional divisor `j : E ⟶ X'` is the class of the closed
subscheme of `X'` cut out by `exceptionalDivisor i`, since `j` factors through it by an
isomorphism. -/
theorem closedSubschemeClass_exceptionalHom (c : ℤ) :
    closedSubschemeClass (blowupObj i).obj.hom (exceptionalHom i).hom.left c =
      closedSubschemeClass (blowupObj i).obj.hom (exceptionalDivisor i).subschemeι c := by
  have hiso : IsIso (exceptionalToSubscheme i) := inferInstance
  funext e
  rw [closedSubschemeClass_apply, closedSubschemeClass_apply,
    cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation k) _
      (exceptionalHom i).hom.left (exceptionalDivisor i).subschemeι
      (@asIso _ _ _ _ (exceptionalToSubscheme i) hiso) (exceptionalToSubscheme_subschemeι i)]

end SmoothProjectiveScheme

namespace FirstChernClassData.IsCohomologicalChernCharacter

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch)

/-- **`γ([Z]) ∪ a = 0` for `a|_Z = 0`, granted `b^![Z] = [E] · θ`** (the proof of Lemma 0FII).
Here `i : Z ⟶ X` is a closed immersion of smooth projective schemes with nowhere dense image,
`b : X' ⟶ X` the blowing up in `Z`, `[E] ∈ CH^1(X')` the class of the exceptional divisor, and
the relation is the first relation of Lemma 0FIH, in `CH^r(X')` for `r = 1 + s` (the two sides
lie in `CH^r(X')` and `CH^{1+s}(X')`, hence the heterogeneous equality). -/
theorem cup_codimensionCycleClass_eq_zero_of_blowup (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA7 : 𝔇.BlowupAxiom)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    (hnd : IsNowhereDense (Set.range i.hom.left.base)) (r s : ℕ) (hr : r = 1 + s)
    (θ : codimensionChowGroup k (blowupObj i).obj.hom s)
    (hrel : codimensionGysin (blowupObj i).obj.hom X.obj.hom (w (blowupHom i)) (r : ℤ)
        (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ)) ≍
      codimensionIntersectionProduct k (blowupObj i).obj.hom 1 s
        (closedSubschemeClass (blowupObj i).obj.hom (exceptionalHom i).hom.left 1) θ)
    (a : 𝔇.H X) (ha : 𝔇.pull i a = 0) :
    tateCupLeft (𝔇.cup X) (r : ℤ) a
      (h.codimensionCycleClass X r (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ))) = 0 := by
  subst hr
  replace hrel := eq_of_heq hrel
  have : Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalDivisor i) :=
    isEffectiveCartierDivisor_exceptionalIdeal i
  have hiso : IsIso (exceptionalToSubscheme i) := inferInstance
  set c := tateLineCoordinate 𝔇.finrank_tate
  set b := blowupHom i
  rw [closedSubschemeClass_exceptionalHom] at hrel
  refine (tateTwistCoordinates c ((1 + s : ℕ) : ℤ)).injective ?_
  rw [map_zero, tateTwistCoordinates_tateCupLeft]
  refine hA7 Z X i hnd ?_
  rw [map_zero, LinearMap.mul_apply', map_mul]
  -- `b^*γ([Z]) = γ(b^![Z]) = γ([E]) ∪ γ(θ)`
  have hpull : 𝔇.pull b (tateTwistCoordinates c ((1 + s : ℕ) : ℤ)
      (h.codimensionCycleClass X (1 + s)
        (closedSubschemeClass X.obj.hom i.hom.left ((1 + s : ℕ) : ℤ)))) =
      tateTwistCoordinates c 1 (h.codimensionCycleClass (blowupObj i) 1
          (closedSubschemeClass (blowupObj i).obj.hom (exceptionalDivisor i).subschemeι 1)) *
        tateTwistCoordinates c s (h.codimensionCycleClass (blowupObj i) s θ) := by
    have h1 := congrArg (tateTwistCoordinates c ((1 + s : ℕ) : ℤ))
      (h.codimensionCycleClass_codimensionGysin b (1 + s)
        (closedSubschemeClass X.obj.hom i.hom.left ((1 + s : ℕ) : ℤ)))
    have h2 := h.codimensionCycleClass_codimensionIntersectionProduct hA1 hA3 (blowupObj i) 1 s
      (closedSubschemeClass (blowupObj i).obj.hom (exceptionalDivisor i).subschemeι 1) θ
    rw [tateTwistCoordinates_map, hrel] at h1
    refine Eq.trans h1.symm ?_
    exact (congrArg (tateTwistCoordinates c _) h2).trans
      (tateTwistCoordinates_tateCup _ _ _ _ _ _ _ _)
  rw [hpull, ← mul_assoc, h.codimensionCycleClass_divisor hA1 hA3]
  -- `b^*a ∪ c₁^H(𝒪_{X'}(E)) = 0` by (A4), since `b^*a` restricts to `0` on `E`
  have hE := hA4 (blowupObj i) (exceptionalObj i) (exceptionalHom i) (exceptionalDivisor i)
    (isEffectiveCartierDivisor_exceptionalIdeal i)
    (@asIso _ _ _ _ (exceptionalToSubscheme i) hiso)
    (exceptionalToSubscheme_subschemeι i) (𝔇.pull b a) (by
      rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, exceptionalHom_comp_blowupHom, 𝔇.pull_comp,
        AlgHom.comp_apply, ha, map_zero])
  have hE' := congrArg (tateTwistCoordinates c 1) hE
  rw [tateTwistCoordinates_tateCupLeft, map_zero] at hE'
  rw [LinearMap.mul_apply'] at hE'
  rw [hE', zero_mul]

/-- **`γ([Z]) ∪ a = 0` for `a|_Z = 0`, `Z` open and closed in `X`** (Lemma 0FII in codimension
`0`). By (A1) `H^*(X) = H^*(Z) × H^*(W)` for the complement `W` of `Z`; `γ([Z]) ∪ a` restricts to
`0` on `Z` because `a` does, and to `0` on `W` because `[Z]` does. -/
theorem cup_codimensionCycleClass_eq_zero_of_isOpenImmersion (hA1 : 𝔇.CoproductAxiom)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    [IsOpenImmersion i.hom.left] (a : 𝔇.H X) (ha : 𝔇.pull i a = 0) :
    tateCupLeft (𝔇.cup X) ((0 : ℕ) : ℤ) a
      (h.codimensionCycleClass X 0 (closedSubschemeClass X.obj.hom i.hom.left ((0 : ℕ) : ℤ))) =
      0 := by
  set c := tateLineCoordinate 𝔇.finrank_tate
  set ι := complementι X i.hom.left
  have hcs : Nonempty (IsColimit (BinaryCofan.mk ((toScheme k).map i) ((toScheme k).map ι))) :=
    nonempty_isColimit_rangeComplement i.hom.left
  have hc : IsColimit (BinaryCofan.mk i ι) :=
    SmoothProjectiveScheme.isColimitOfIsColimitMapCofan hcs.some
  refine (tateTwistCoordinates c ((0 : ℕ) : ℤ)).injective ?_
  rw [map_zero, tateTwistCoordinates_tateCupLeft, LinearMap.mul_apply']
  refine (hA1.2 Z (complementObj X i.hom.left) X i ι hcs).1 ?_
  simp only [map_mul, map_zero, Prod.mk.injEq]
  refine ⟨by rw [ha, zero_mul], ?_⟩
  have h0 := congrArg (tateTwistCoordinates c ((0 : ℕ) : ℤ))
    (h.codimensionCycleClass_codimensionGysin ι 0
      (closedSubschemeClass X.obj.hom i.hom.left ((0 : ℕ) : ℤ)))
  have hz : codimensionGysin (complementObj X i.hom.left).obj.hom X.obj.hom (w ι) ((0 : ℕ) : ℤ)
      (closedSubschemeClass X.obj.hom i.hom.left ((0 : ℕ) : ℤ)) = 0 :=
    codimensionGysin_closedSubschemeClass_of_disjoint hc
  rw [tateTwistCoordinates_map, hz, map_zero, map_zero] at h0
  exact (congrArg (𝔇.pull ι a * ·) h0.symm).trans (mul_zero _)

end FirstChernClassData.IsCohomologicalChernCharacter

end Stacks.WeilCohomology

end
