module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDisjointUnion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.RankOne
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationTop

/-!
# The cohomology class of a closed subscheme

Let `i : X ⟶ Y` be a closed immersion of nonempty equidimensional smooth projective schemes over
`k`, of dimensions `d` and `e`, and `c = e - d`. Stacks 0FHG says that the cohomology class of
`[X] ∈ CH^c(Y)` is `i_*1 ∈ H^{2c}(Y)(c)`. The proof is the source's: `[X] = i_*[X]` is the proper
pushforward of the fundamental class of `X`, so axiom (C)(b) gives `γ([X]) = i_*γ([X])`, and
`γ([X]) = 1` in `H^0(X)` by Stacks 0FHF.

## Main results

* `Stacks.WeilCohomology.equidimensionalPushforward_fundamentalClass`: `i_*[X] = [X]` in
  `CH^c(Y)`, on the actual Chow groups.
* `Stacks.WeilCohomology.WeilData.cycleClass_closedSubschemeClass`: `γ([X]) = i_*γ([X]_X)`,
  from axiom (C)(b).
* `Stacks.WeilCohomology.WeilData.cycleClass_closedSubschemeClass_eq_pushforward_one`:
  **Stacks 0FHG**, `γ([X]) = i_*1`; `cycleClass_diagonal_eq_pushforward_one` is the diagonal case.
* `Stacks.WeilCohomology.WeilData.pushforward_unitTw_of_isIso`,
  `Stacks.WeilCohomology.WeilData.trace_pullTw_of_isIso`: for an isomorphism `φ`, `φ_*1 = 1` and
  `∫_X φ^*a = ∫_Z a`.

## References

* [Stacks Project, Tag 0FHG](https://stacks.math.columbia.edu/tag/0FHG)
* [Stacks Project, Tag 0FHF](https://stacks.math.columbia.edu/tag/0FHF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- **`i_*[X] = [X]` in `CH^c(Y)`.** For a closed immersion `i : X ⟶ Y` of nonempty
equidimensional smooth projective schemes over `k`, of dimensions `d` and `e`, the proper
pushforward of the fundamental class of `X` is the class of the closed subscheme `X` of `Y`, of
codimension `c = e - d`. -/
theorem equidimensionalPushforward_fundamentalClass
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (i : X ⟶ Y)
    [IsClosedImmersion i.hom.left] {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (c : ℤ) (hc : c = 0 + e - d) :
    equidimensionalPushforward i d e 0 c hc (fundamentalClass X) =
      closedSubschemeClass Y.obj.hom i.hom.left c := by
  funext e'
  by_cases he : e' = e
  · subst he
    have := isIso_dimPart_self_ι X.obj.hom hX.relativeDimension
    have : IsClosedImmersion ((dimPart X.obj.hom d).ι ≫ i.hom.left) := inferInstance
    simp only [equidimensionalPushforward, AddMonoidHom.pi_apply, closedSubschemeClass_apply]
    refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
    simp only [AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
    refine chowGroupRestrict_heq_of_eq _ _ _ rfl rfl rfl _ _
      (show (d : ℤ) - 0 = e' - c by omega) _ _ ?_
    rw [fundamentalClass]
    refine (properChowPushforward_heq_congr _ _ _ _ _ (by omega) _
      (properPushforwardDescends _ _ _ _ _ _) _ _ (chowGroupDegreeEquiv_heq _ _ _ _)).trans ?_
    rw [fundamentalChowClass, fundamentalCycle, properChowPushforward_mk,
      properPushforward_cycleAssociatedToClosedSubscheme_id,
      cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation k) Y.obj.hom
        ((dimPart X.obj.hom d).ι ≫ i.hom.left) i.hom.left (asIso (dimPart X.obj.hom d).ι) rfl]
    exact Stacks.Chow.mk_cycleAssociatedToClosedSubscheme_heq _ _ _ (by omega)
  · have := isEmpty_dimPart_of_ne Y.obj.hom hY.relativeDimension he
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

/-- The diagonal `Δ : X ⟶ X × X` of a smooth projective scheme over `k` is a closed immersion,
`X` being separated over `k`. -/
instance isClosedImmersion_diag_left (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsClosedImmersion (SmoothProjectiveScheme.diag X).hom.left := by
  rw [SmoothProjectiveScheme.diag_left]
  exact IsSeparated.isClosedImmersion_diagonal

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

/-- **`γ([X]) = i_*γ([X]_X)`**, from axiom (C)(b): for a closed immersion `i : X ⟶ Y` of nonempty
equidimensional smooth projective schemes over `k`, of dimensions `d` and `e`, the cohomology
class of the closed subscheme `X` of `Y`, of codimension `c = e - d`, is the pushforward of the
cohomology class of the fundamental class of `X`. -/
theorem cycleClass_closedSubschemeClass (hA : W.PerfectPairing)
    (hCb : W.CycleClassPushforward hA) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
        (i : X ⟶ Y)
    [IsClosedImmersion i.hom.left] {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (c : ℤ) (hc : c = 0 + e - d) :
    W.cycleClass Y c (closedSubschemeClass Y.obj.hom i.hom.left c) =
      W.pushforward hA i hX hY (2 * 0) 0 (2 * c) c (by omega) (by omega)
        (W.cycleClass X 0 (fundamentalClass X)) := by
  rw [← equidimensionalPushforward_fundamentalClass i hX hY c hc]
  exact hCb i d e hX hY 0 c hc (fundamentalClass X)

/-- **`γ([X]) = i_*1`, granted `γ([X]_X) = 1`.** For a closed immersion `i : X ⟶ Y` of nonempty
equidimensional smooth projective schemes over `k`, of dimensions `d` and `e`, and
`c = e - d`: if the fundamental class of `X` has cohomology class `1 ∈ H^0(X)` (Stacks 0FHF),
then the cohomology class of the closed subscheme `X` of `Y` is `i_*1 ∈ H^{2c}(Y)(c)`. -/
theorem cycleClass_closedSubschemeClass_eq_pushforward_unitTw (hA : W.PerfectPairing)
    (hCb : W.CycleClassPushforward hA) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
        (i : X ⟶ Y)
    [IsClosedImmersion i.hom.left] {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (c : ℤ) (hc : c = e - d)
    (hone : W.cycleClass X 0 (fundamentalClass X) = W.unitTw X 0 0 rfl) :
    W.cycleClass Y c (closedSubschemeClass Y.obj.hom i.hom.left c) =
      W.pushforward hA i hX hY 0 0 (2 * c) c (by omega) (by omega) (W.unitTw X 0 0 rfl) := by
  rw [W.cycleClass_closedSubschemeClass hA hCb i hX hY c (by omega), hone]
  rfl

/-- **`γ([Δ]) = Δ_*1`, granted `γ([X]) = 1`**: the case of the diagonal `Δ : X ⟶ X × X` of a
nonempty smooth projective scheme `X` equidimensional of dimension `d`, for which
`[Δ] ∈ CH^d(X × X)` is the class of the closed subscheme `Δ`. -/
theorem cycleClass_diagonal_eq_pushforward_unitTw (hA : W.PerfectPairing)
    (hCb : W.CycleClassPushforward hA) {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d)
    (hXX : IsNonemptyEquidimensional (SmoothProjectiveScheme.prod X X) (d + d))
    (hone : W.cycleClass X 0 (fundamentalClass X) = W.unitTw X 0 0 rfl) :
    W.cycleClass (SmoothProjectiveScheme.prod X X) d
        (closedSubschemeClass (SmoothProjectiveScheme.prod X X).obj.hom
          (SmoothProjectiveScheme.diag X).hom.left d) =
      W.pushforward hA (SmoothProjectiveScheme.diag X) hX hXX 0 0 (2 * d) d (by omega) (by omega)
        (W.unitTw X 0 0 rfl) :=
  W.cycleClass_closedSubschemeClass_eq_pushforward_unitTw hA hCb _ hX hXX d (by push_cast; ring)
    hone

/-- **Stacks 0FHG.** Assume given (D0), (D1), (D2), (D3) satisfying (A), (B) and (C). Let
`i : X ⟶ Y` be a closed immersion of nonempty smooth projective equidimensional schemes over
`k`, of dimensions `d` and `e`. Then `γ([X]) = i_*1` in `H^{2c}(Y)(c)`, `c = dim(Y) - dim(X)`.

`[X] ∈ CH^c(Y)` is the class of the closed subscheme `X` (`closedSubschemeClass`), `i_*` the
pushforward of (A) and `1 ∈ H^0(X)` the unit. As in the source: `1 = γ([X])` in `H^0(X)` by
Stacks 0FHF (`WeilData.cycleClass_fundamentalClass`), and axiom (C)(b) applies to
`i_*[X]_X = [X]`. -/
@[stacks 0FHG "γ([X]) = i_*1 for a closed immersion of nonempty equidimensional smooth \
  projective schemes, on the actual category of smooth projective schemes over k with the actual \
  CH^c(Y), the data (D0)-(D3) and axioms (A), (B), (C) as the source states them"]
theorem cycleClass_closedSubschemeClass_eq_pushforward_one (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
        {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (i : X ⟶ Y) [IsClosedImmersion i.hom.left] {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (c : ℤ) (hc : c = e - d) :
    W.cycleClass Y c (closedSubschemeClass Y.obj.hom i.hom.left c) =
      W.pushforward hA.perfectPairing i hX hY 0 0 (2 * c) c (by omega) (by omega)
        (W.unitTw X 0 0 rfl) :=
  W.cycleClass_closedSubschemeClass_eq_pushforward_unitTw hA.perfectPairing hC.pushforward i hX
    hY c hc (W.cycleClass_fundamentalClass hB.kunnethIsomorphism hC.pullback hC.mul hC.point X)

/-- **Stacks 0FHG for the diagonal**: `γ([Δ]) = Δ_*1` in `H^{2d}(X × X)(d)` for `X` nonempty
equidimensional of dimension `d`. -/
theorem cycleClass_diagonal_eq_pushforward_one (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X : (SmoothProjectiveScheme k).FullSubcategory}
        {d : ℕ}
    (hX : IsNonemptyEquidimensional X d)
    (hXX : IsNonemptyEquidimensional (SmoothProjectiveScheme.prod X X) (d + d)) :
    W.cycleClass (SmoothProjectiveScheme.prod X X) d
        (closedSubschemeClass (SmoothProjectiveScheme.prod X X).obj.hom
          (SmoothProjectiveScheme.diag X).hom.left d) =
      W.pushforward hA.perfectPairing (SmoothProjectiveScheme.diag X) hX hXX 0 0 (2 * d) d
        (by omega) (by omega) (W.unitTw X 0 0 rfl) :=
  W.cycleClass_closedSubschemeClass_eq_pushforward_one hA hB hC _ hX hXX d (by push_cast; ring)

/-! ### Isomorphisms -/

/-- For `Z` equidimensional of dimension `d`, the class of the closed subscheme `Z ⊆ Z` given
by an isomorphism `φ : X ⟶ Z` is the fundamental class of `Z`. -/
theorem closedSubschemeClass_of_isIso {X Z : (SmoothProjectiveScheme k).FullSubcategory} (φ : X ⟶ Z)
    [IsIso φ.hom.left] {d : ℕ} (hZ : RelativeDimension Z.obj.hom d) :
    closedSubschemeClass Z.obj.hom φ.hom.left 0 = fundamentalClass Z := by
  funext e
  by_cases he : e = d
  · subst he
    rw [closedSubschemeClass_apply, fundamentalClass,
      cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation k) Z.obj.hom φ.hom.left
        (𝟙 Z.obj.left) (asIso φ.hom.left) (Category.comp_id _)]
    refine eq_of_heq ((chowGroupRestrict_heq_of_eq (fieldChowSituation k)
      (dimPart Z.obj.hom e).ι (dimPart Z.obj.hom e).ι rfl rfl rfl rfl rfl (sub_zero (e : ℤ)) _ _
      (Stacks.Chow.mk_cycleAssociatedToClosedSubscheme_heq (fieldChowSituation k) Z.obj.hom
        (𝟙 Z.obj.left) (sub_zero (e : ℤ)))).trans ?_)
    exact HEq.trans (heq_of_eq (chowGroupRestrict_fundamentalChowClass (fieldChowSituation k)
      Z.obj.hom (partBase Z.obj.hom e) (dimPart Z.obj.hom e).ι rfl e
      (schemeDeltaDimension_le_of_relativeDimension _ hZ))) (chowGroupDegreeEquiv_heq _ _ _ _).symm
  · have := isEmpty_dimPart_of_ne Z.obj.hom hZ he
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

/-- Cup product on the right with a class of coordinate `1` is the identity. -/
theorem cupTw_eq_self_of_coe_twCoord_eq_one_right (X : (SmoothProjectiveScheme k).FullSubcategory)
    (i j : ℤ)
    (h : i + j = i) (s t : ℤ) (h' : s + t = s) (x : W.Tw X i s) (y : W.Tw X j t)
    (hy : (W.twCoord X j t y : W.H X) = 1) :
    W.cupTw X i j i h s t s h' x y = x := by
  apply (W.twCoord X i s).injective
  rw [twCoord_cupTw]
  exact Subtype.ext (by rw [coe_cup, hy, mul_one])

/-- **`φ_*1 = 1` for an isomorphism** `φ : X ⟶ Z` of nonempty smooth projective schemes,
equidimensional of dimension `d`: by Stacks 0FHG, `φ_*1 = γ([X ⊆ Z]) = γ([Z]) = 1`, the last
equality being Stacks 0FHF. -/
theorem pushforward_unitTw_of_isIso (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Z : (SmoothProjectiveScheme k).FullSubcategory}
        (φ : X ⟶ Z)
    [IsIso φ.hom.left] {d : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hZ : IsNonemptyEquidimensional Z d) :
    W.pushforward hA.perfectPairing φ hX hZ 0 0 0 0 rfl rfl (W.unitTw X 0 0 rfl) =
      W.unitTw Z 0 0 rfl := by
  have h := W.cycleClass_closedSubschemeClass_eq_pushforward_one hA hB hC φ hX hZ 0 (by simp)
  rw [closedSubschemeClass_of_isIso φ hZ.relativeDimension,
    W.cycleClass_fundamentalClass hB.kunnethIsomorphism hC.pullback hC.mul hC.point Z] at h
  exact h.symm

/-- **Iso-invariance of the trace map**: for an isomorphism `φ : X ⟶ Z` of nonempty smooth
projective schemes over `k`, equidimensional of dimension `d`, `∫_X φ^*a = ∫_Z a` for
`a ∈ H^{2d}(Z)(d)`. By the trace equation `∫_X φ^*a ∪ 1 = ∫_Z a ∪ φ_*1`, and `φ_*1 = 1`. -/
theorem trace_pullTw_of_isIso (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Z : (SmoothProjectiveScheme k).FullSubcategory}
        (φ : X ⟶ Z)
    [IsIso φ.hom.left] {d : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hZ : IsNonemptyEquidimensional Z d) (a : W.Tw Z (2 * d) d) :
    W.trace X d hX (W.pullTw φ (2 * d) d a) = W.trace Z d hZ a := by
  have key := pushforward_trace' hA.perfectPairing φ hX hZ 0 0 0 0 rfl rfl (2 * d) d
    (by ring) (by ring) (by ring) (by ring) a (W.unitTw X 0 0 rfl)
  rwa [W.pushforward_unitTw_of_isIso hA hB hC φ hX hZ, pairingTw_apply, pairingTw_apply,
    W.cupTw_eq_self_of_coe_twCoord_eq_one_right X _ _ _ _ _ _ _ _
      (W.coe_twCoord_unitTw X _ _ rfl),
    W.cupTw_eq_self_of_coe_twCoord_eq_one_right Z _ _ _ _ _ _ _ _
      (W.coe_twCoord_unitTw Z _ _ rfl)] at key

end WeilData

end Stacks.WeilCohomology

end
