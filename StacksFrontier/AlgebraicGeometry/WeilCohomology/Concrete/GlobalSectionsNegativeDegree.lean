module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Stacks 0FI1: nonzero negative cohomology breaks the criterion of Stacks 0FI0

Assume given (D0), (D1), (D2) and (D3) satisfying (A), (B) and (C)
(`Stacks.WeilCohomology.WeilData`, over the actual category of smooth projective schemes over
`k`, `F` of characteristic zero). Stacks 0FI1 says: if some smooth projective `Y` over `k` has
`H^i(Y) ≠ 0` for some `i < 0`, then there is an equidimensional smooth projective `X` over `k`
for which the equivalent conditions of Stacks 0FI0 fail.

## The proof

* `Y` may be taken equidimensional: it is a retract of an equidimensional smooth projective
  scheme `Y'` (`SmoothProjectiveScheme.exists_retraction_relativeDimension`, the device of
  the proof of Stacks 0FHJ), so `H^i(Y) → H^i(Y')` is injective.
* Pick `0 ≠ a ∈ H^i(Y)`. In place of the source's case distinction on the parity of `i` we always
  pass to `Y × Y`, where `pr₁^*a ∪ pr₂^*a ∈ H^{2i}(Y × Y)` is nonzero by (B)(a). With `m = -i`
  and `Z = (𝐏¹_k)^m`, Poincaré duality (A) and `1 ≠ 0` in `H^0(Z)` (Stacks 0FHF) give
  `0 ≠ b ∈ H^{2m}(Z)`, and `X = (Y × Y) × Z` carries the class
  `c = pr₁^*(pr₁^*a ∪ pr₂^*a) ∪ pr₂^*b ∈ H^0(X)`, nonzero by (B)(a) again.
* Condition (1) of Stacks 0FI0 fails for `X`: for a closed point `x ∈ X` with separable residue
  field, `x^*c` is a product with the factor `(pr₁ pr₁ x)^*a ∈ H^i(x)`, which vanishes because
  `H^i(x) = 0` for `i ≠ 0` (Stacks 0FHQ (1)). Hence `c ≠ 0` lies in the kernel of
  `H^0(X) → ⊕ H^0(xⱼ)` for every finite family of such points. The source instead checks that
  (2) fails; the two are equivalent by Stacks 0FI0, which also gives the failure of (3).

## Main results

* `Stacks.WeilCohomology.WeilData.exists_relativeDimension_grade_ne_bot`: a nonzero
  `H^i` on some smooth projective scheme gives one on an equidimensional one.
* `Stacks.WeilCohomology.WeilData.grade_top_ne_bot`: `H^{2d}(X) ≠ 0` for `X` nonempty
  equidimensional of dimension `d`.
* `Stacks.WeilCohomology.WeilData.exists_not_globalSections_criterion`: **Stacks 0FI1**.

## References

* [Stacks Project, Tag 0FI1](https://stacks.math.columbia.edu/tag/0FI1)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k]

namespace WeilData

variable {F : Type w} [Field F] {W : WeilData k F}

/-- Pulling back a class of degree `i` along any morphism into a scheme with `H^i = 0` gives `0`. -/
private theorem pull_eq_zero_of_grade_eq_bot {P Q : (SmoothProjectiveScheme k).FullSubcategory}
    {i : ℤ} (h : W.grade Q i = ⊥) (g : Q ⟶ P) {a : W.H P} (ha : a ∈ W.grade P i) :
    W.pull g a = 0 := by
  simpa [h] using W.pull_grade g i a ha

/-- **A nonzero `H^i` can be moved to an equidimensional scheme**: if `H^i(Y) ≠ 0` for a smooth
projective `Y` over `k`, then `H^i(Y') ≠ 0` for some equidimensional smooth projective `Y'`. Any
`Y` is a retract `s ≫ g = 𝟙` of an equidimensional `Y'`
(`SmoothProjectiveScheme.exists_retraction_relativeDimension`), and `s^* ∘ g^* = id`. -/
theorem exists_relativeDimension_grade_ne_bot
    {Y : (SmoothProjectiveScheme k).FullSubcategory} {i : ℤ} (hY : W.grade Y i ≠ ⊥) :
    ∃ (Y' : (SmoothProjectiveScheme k).FullSubcategory) (e : ℕ), RelativeDimension Y'.obj.hom e ∧
      W.grade Y' i ≠ ⊥ := by
  obtain ⟨e, Y', g, s, hsg, he⟩ := exists_retraction_relativeDimension Y
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  refine ⟨Y', e, he, fun h ↦ ha0 ?_⟩
  have := congrArg (W.pull s) (pull_eq_zero_of_grade_eq_bot h g ha)
  rwa [map_zero, ← AlgHom.comp_apply, ← W.pull_comp, hsg, W.pull_id, AlgHom.id_apply] at this

/-- **`H^{2d}(X) ≠ 0`** for `X` nonempty and equidimensional of dimension `d`: by (A)(b) the
pairing `H^0(X) × H^{2d}(X)(d) → F` is perfect, and `1 ≠ 0` in `H^0(X)` (Stacks 0FHF). -/
theorem grade_top_ne_bot [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) : W.grade X (2 * d) ≠ ⊥ := by
  intro h
  have := hX.nonempty
  have := nontrivial_of_nonempty hA hB hC X
  have : Subsingleton (W.grade X (2 * d)) :=
    ⟨fun x y ↦ Subtype.ext (by
      rw [(Submodule.eq_bot_iff _).mp h x x.2, (Submodule.eq_bot_iff _).mp h y y.2])⟩
  have : Subsingleton (W.Tw X (2 * d) d) := (W.twCoord X _ _).toEquiv.subsingleton
  have hperf := hA.perfectPairing X d hX 0 (2 * d) (zero_add _)
  have h1 : (⟨1, SetLike.GradedOne.one_mem⟩ : W.grade X 0) = 0 :=
    hperf.bijective_left.1 (LinearMap.ext fun v ↦ by
      simp only [Subsingleton.elim v 0, map_zero])
  exact one_ne_zero (congrArg Subtype.val h1)

/-- Under (B), the Künneth map sends a pure tensor of nonzero classes to a nonzero class. -/
theorem kunnethMap_tmul_ne_zero (hB : W.Kunneth)
    {P Q : (SmoothProjectiveScheme k).FullSubcategory} {p : W.H P} {q : W.H Q}
    (hp : p ≠ 0) (hq : q ≠ 0) : W.kunnethMap P Q (p ⊗ₜ q) ≠ 0 := fun h ↦ hp <|
  FirstChernClassData.injective_tmul_right_of_ne_zero hq <|
    (hB.kunnethIsomorphism P Q).1 (h.trans (map_zero _).symm) |>.trans
      (TensorProduct.zero_tmul _ _).symm

/-- The Künneth map sends a pure tensor of classes of degrees `i` and `j` to a class of degree
`i + j`. -/
theorem kunnethMap_tmul_mem_grade {P Q : (SmoothProjectiveScheme k).FullSubcategory}
    {p : W.H P} {q : W.H Q} {i j : ℤ} (hp : p ∈ W.grade P i) (hq : q ∈ W.grade Q j) :
    W.kunnethMap P Q (p ⊗ₜ q) ∈ W.grade (prod P Q) (i + j) := by
  rw [kunnethMap_tmul]
  exact SetLike.GradedMul.mul_mem (W.pull_grade _ i p hp) (W.pull_grade _ j q hq)

/-- **Stacks Project, Tag 0FI1.** Assume given (D0), (D1), (D2) and (D3) satisfying (A), (B) and
(C). If there exists a smooth projective scheme `Y` over `k` such that `H^i(Y)` is nonzero for
some `i < 0`, then there exists an equidimensional smooth projective scheme `X` over `k` such
that the equivalent conditions of Stacks 0FI0 fail for `X`: (1) no finite family of closed points
with separable residue fields detects `H^0(X)` (`SeparablePointsDetectH0`), (2) the map
`H^0(Spec Γ(X, 𝒪_X)) → H^0(X)` is not an isomorphism, and (3) the classes of closed points do not
generate `H^{2d}(X)(d)` as an `H^0(X)`-module (`PointClassesGenerate`), `d` the dimension of `X`.
The scheme `X` is moreover nonempty. -/
@[stacks 0FI1 "H^i(Y) ≠ 0 for some smooth projective Y and i < 0 gives a nonempty \
equidimensional smooth projective X for which conditions (1), (2), (3) of 0FI0 all fail, on the \
actual Weil data (D0)-(D3) satisfying (A), (B), (C) over the actual category of smooth projective \
k-schemes"]
theorem exists_not_globalSections_criterion [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    (hneg : ∃ (Y : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ), i < 0 ∧ W.grade Y i ≠ ⊥) :
    ∃ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ), IsNonemptyEquidimensional X d ∧
      ¬ W.SeparablePointsDetectH0 X ∧
      ¬ Function.Bijective (W.pullDeg (toSpecGlobalSections X) 0) ∧
      ¬ W.PointClassesGenerate X d := by
  obtain ⟨Y₀, i, hi, hY₀⟩ := hneg
  obtain ⟨Y, e, he, hY⟩ := exists_relativeDimension_grade_ne_bot hY₀
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  set m : ℕ := (-i).toNat
  have hm : (m : ℤ) = -i := Int.toNat_of_nonneg (by omega)
  let Z := projectiveLinePow (k := k) m
  have hZ : IsNonemptyEquidimensional Z m :=
    ⟨⟨(projectiveLinePowPoint m).hom.left.base isNonemptyEquidimensional_point.nonempty.some⟩,
      relativeDimension_projectiveLinePow m⟩
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (grade_top_ne_bot hA hB hC hZ)
  let X := prod (prod Y Y) Z
  have hXd : RelativeDimension X.obj.hom (m + (e + e)) :=
    relativeDimension_prodBase k _ _ (relativeDimension_prodBase k _ _ he he) hZ.relativeDimension
  let c : W.H X := W.kunnethMap (prod Y Y) Z (W.kunnethMap Y Y (a ⊗ₜ a) ⊗ₜ b)
  have hc : c ∈ W.grade X 0 := by
    have := kunnethMap_tmul_mem_grade (kunnethMap_tmul_mem_grade ha ha) hb
    rwa [show i + i + 2 * (m : ℤ) = 0 by omega] at this
  have hc0 : c ≠ 0 := kunnethMap_tmul_ne_zero hB (kunnethMap_tmul_ne_zero hB ha0 ha0) hb0
  have hX : IsNonemptyEquidimensional X (m + (e + e)) := by
    refine ⟨?_, hXd⟩
    by_contra hne
    have : IsEmpty X.obj.left := not_nonempty_iff.mp hne
    have := W.subsingleton_of_isEmpty hB.kunnethIsomorphism hC.pullback hC.mul hC.point X
    exact hc0 (Subsingleton.elim _ _)
  have h1 : ¬ W.SeparablePointsDetectH0 X := by
    rintro ⟨r, x, hx, hs, hinj⟩
    refine hc0 (congrArg Subtype.val (hinj (a₁ := ⟨c, hc⟩) (a₂ := 0) (funext fun j ↦ ?_)))
    apply Subtype.ext
    dsimp only
    rw [map_zero, coe_pullDeg, ZeroMemClass.coe_zero]
    have hpt : W.grade (closedPointObj (hx j) (hs j)) i = ⊥ :=
      grade_eq_bot_of_dimension_zero hA hB hC
        (topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional
          (isNonemptyEquidimensional_closedPointObj (hx j) (hs j))) hi.ne
    have hz : W.pull (closedPointHom (hx j) (hs j))
        (W.pull (fst (prod Y Y) Z) (W.pull (fst Y Y) a)) = 0 := by
      rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← W.pull_comp, ← W.pull_comp]
      exact pull_eq_zero_of_grade_eq_bot hpt _ ha
    simp only [c, kunnethMap_tmul, map_mul, hz, zero_mul]
  have hcrit := globalSections_criterion hA hB hC X
  exact ⟨X, m + (e + e), hX, h1, fun h2 ↦ h1 (hcrit.1.mpr h2),
    fun h3 ↦ h1 ((hcrit.2.2 _ hXd).mpr h3)⟩

end WeilData

end Stacks.WeilCohomology

end
