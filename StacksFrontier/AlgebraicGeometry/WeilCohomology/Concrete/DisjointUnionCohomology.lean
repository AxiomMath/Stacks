module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.ClosedSubschemeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.GysinChernCharacter
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassFundamental
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of a disjoint union

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) over the actual category of smooth projective
schemes over `k`, satisfying (A), (B) and (C), and let `X`, `Y` be smooth projective schemes over
`k` with disjoint union `Z = X ⨿ Y` and coprojections `i`, `j`. This file proves Stacks 0FHJ:
`H^*(Z) → H^*(X) × H^*(Y)`, `a ↦ (i^*a, j^*a)`, is an isomorphism.

## The decomposition `a = i_*(i^*a) + j_*(j^*a)`

For `X` and `Y` nonempty and equidimensional of the same dimension `d` the source's first step is
that `1 = γ([Z]) = γ([X]) + γ([Y]) = i_*1 + j_*1` in `H^0(Z)`. Here `[X], [Y] ∈ CH^0(Z)` are the
classes of the open and closed subschemes `X` and `Y`, and `[Z] = [X] + [Y]` because the
coprojections are open and closed immersions with complementary images
(`Stacks.WeilCohomology.fundamentalClass_pt_eq_add`). The equalities `γ([Z]) = 1` and
`γ([X]) = i_*1` are Stacks 0FHF and Stacks 0FHG. With the projection formula this gives
`a = i_*(i^*a) + j_*(j^*a)` (`Stacks.WeilCohomology.WeilData.eq_pushforward_pullTw_add`). It is
proved here by pairing with an arbitrary class, which reduces it to the additivity of the trace,
`∫_Z x = ∫_Z x ∪ (i_*1 + j_*1) = ∫_X i^*x + ∫_Y j^*x`.

## References

* [Stacks Project, Tag 0FHJ](https://stacks.math.columbia.edu/tag/0FHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

open SmoothProjectiveScheme

section Chow

variable {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {i : X ⟶ Z} {j : Y ⟶ Z}

/-- The first coprojection of a coproduct cofan `BinaryCofan.mk i j` is a closed immersion. -/
theorem isClosedImmersion_left_of_isColimit (hc : IsColimit (BinaryCofan.mk i j)) :
    IsClosedImmersion i.hom.left :=
  isClosedImmersion_inl hc

/-- The second coprojection of a coproduct cofan `BinaryCofan.mk i j` is a closed immersion. -/
theorem isClosedImmersion_right_of_isColimit (hc : IsColimit (BinaryCofan.mk i j)) :
    IsClosedImmersion j.hom.left :=
  isClosedImmersion_inr hc

/-- The first coprojection of a coproduct cofan `BinaryCofan.mk i j` is an open immersion. -/
theorem isOpenImmersion_left_of_isColimit (hc : IsColimit (BinaryCofan.mk i j)) :
    IsOpenImmersion i.hom.left :=
  isOpenImmersion_inl hc

/-- The second coprojection of a coproduct cofan `BinaryCofan.mk i j` is an open immersion. -/
theorem isOpenImmersion_right_of_isColimit (hc : IsColimit (BinaryCofan.mk i j)) :
    IsOpenImmersion j.hom.left :=
  isOpenImmersion_inr hc

/-- The images of the coprojections of a coproduct cofan `BinaryCofan.mk i j` are
complementary. -/
theorem isCompl_range_of_isColimit (hc : IsColimit (BinaryCofan.mk i j)) :
    IsCompl (Set.range i.hom.left) (Set.range j.hom.left) :=
  isCompl_range_inl_inr hc

/-- **`[X ⨿ Y] = [X] + [Y]` in `CH^0(X ⨿ Y)`**: the fundamental class of a disjoint union is the
sum of the classes of the two open and closed subschemes. -/
theorem fundamentalClass_pt_eq_add (hc : IsColimit (BinaryCofan.mk i j)) :
    haveI := isClosedImmersion_left_of_isColimit hc
    haveI := isClosedImmersion_right_of_isColimit hc
    fundamentalClass Z = closedSubschemeClass Z.obj.hom i.hom.left 0 +
      closedSubschemeClass Z.obj.hom j.hom.left 0 := by
  have := isClosedImmersion_left_of_isColimit hc
  have := isClosedImmersion_right_of_isColimit hc
  have := isOpenImmersion_left_of_isColimit hc
  have := isOpenImmersion_right_of_isColimit hc
  have hcompl := isCompl_range_of_isColimit hc
  funext e
  rw [Pi.add_apply, closedSubschemeClass_apply, closedSubschemeClass_apply, ← map_add,
    ← QuotientAddGroup.mk_add,
    ← cycleAssociatedToClosedSubscheme_eq_add_of_isOpenImmersion_pieces (fieldChowSituation k)
      Z.obj.hom (𝟙 _) i.hom.left j.hom.left i.hom.left j.hom.left
      (Category.comp_id _) (Category.comp_id _) hcompl.disjoint hcompl.sup_eq_top ((e : ℤ) - 0)]
  have h := chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion (fieldChowSituation k)
    Z.obj.hom (partBase Z.obj.hom e) (dimPart Z.obj.hom e).ι rfl ((e : ℤ) - 0)
  rw [fundamentalChowClass, fundamentalCycle] at h
  refine eq_of_heq (HEq.trans ?_ (heq_of_eq h.symm))
  exact (chowGroupDegreeEquiv_heq _ _ _ _).trans (fundamentalChowClass_heq _ _ (by ring))

end Chow

namespace WeilData

variable {F : Type w} [Field F] {W : WeilData k F}

/-- Cup product on the right with the unit is the identity. -/
private theorem cupTw_unitTw_right (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (h : i + j = i)
    (s t : ℤ) (h' : s + t = s) (hj : j = 0) (x : W.Tw X i s) :
    W.cupTw X i j i h s t s h' x (W.unitTw X j t hj) = x := by
  apply (W.twCoord X i s).injective
  rw [twCoord_cupTw]
  exact Subtype.ext (by rw [coe_cup, coe_twCoord_unitTw, mul_one])

variable {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {i : X ⟶ Z} {j : Y ⟶ Z}

/-- **`1 = i_*1 + j_*1` in `H^0(X ⨿ Y)`**, for `X` and `Y` nonempty and equidimensional of the same
dimension as `X ⨿ Y`: `1 = γ([X ⨿ Y]) = γ([X]) + γ([Y])` by Stacks 0FHF and
`Stacks.WeilCohomology.fundamentalClass_pt_eq_add`, and `γ([X]) = i_*1` by Stacks 0FHG. -/
theorem unitTw_eq_add (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (hc : IsColimit (BinaryCofan.mk i j)) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y d)
    (hZ : IsNonemptyEquidimensional Z d) :
    W.unitTw Z (2 * 0) 0 (by simp) =
      W.pushforward hA.perfectPairing i hX hZ 0 0 (2 * 0) 0 (by omega) (by omega)
          (W.unitTw X 0 0 rfl) +
        W.pushforward hA.perfectPairing j hY hZ 0 0 (2 * 0) 0 (by omega) (by omega)
          (W.unitTw Y 0 0 rfl) := by
  have := isClosedImmersion_left_of_isColimit hc
  have := isClosedImmersion_right_of_isColimit hc
  have hone := fun T ↦ cycleClass_fundamentalClass hB.kunnethIsomorphism hC.pullback hC.mul
    hC.point T
  rw [← W.cycleClass_closedSubschemeClass_eq_pushforward_unitTw hA.perfectPairing hC.pushforward
      i hX hZ 0 (by simp) (hone X),
    ← W.cycleClass_closedSubschemeClass_eq_pushforward_unitTw hA.perfectPairing hC.pushforward
      j hY hZ 0 (by simp) (hone Y), ← map_add]
  have hZ1 : W.cycleClass Z 0 (fundamentalClass Z) = W.unitTw Z (2 * 0) 0 (by simp) := by
    apply (W.twCoord Z (2 * 0) 0).injective
    apply Subtype.ext
    rw [coe_twCoord_unitTw]
    exact (congrArg (fun y ↦ (W.twCoord Z (2 * 0) 0 y : W.H Z)) (hone Z)).trans
      (W.coe_twCoord_unitTw Z 0 0 rfl)
  rw [← hZ1]
  exact congrArg _ (fundamentalClass_pt_eq_add hc)

/-- **The trace is additive on a disjoint union**, `∫_{X ⨿ Y} x = ∫_X i^*x + ∫_Y j^*x`, for `X` and
`Y` nonempty and equidimensional of the same dimension `d`. This is
`∫_{X ⨿ Y} x ∪ 1 = ∫_{X ⨿ Y} x ∪ i_*1 + ∫_{X ⨿ Y} x ∪ j_*1` and the trace equation defining the
pushforward. -/
theorem trace_eq_add (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (hc : IsColimit (BinaryCofan.mk i j)) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y d)
    (hZ : IsNonemptyEquidimensional Z d) (x : W.Tw Z (2 * d) d) :
    W.trace Z d hZ x = W.trace X d hX (W.pullTw i _ _ x) + W.trace Y d hY (W.pullTw j _ _ x) := by
  have h1 : W.trace Z d hZ x = W.pairingTw Z d hZ (2 * d) (2 * 0) (by ring) d 0 (by ring) x
      (W.unitTw Z (2 * 0) 0 (by simp)) := by
    rw [pairingTw_apply, cupTw_unitTw_right Z (2 * d) (2 * 0) (by ring) d 0 (by ring) (by simp) x]
  have hX' := pushforward_trace' hA.perfectPairing i hX hZ 0 0 (2 * 0) 0 (by omega)
    (by omega) (2 * d) d (by ring) (by ring) (by ring) (by ring) x (W.unitTw X 0 0 rfl)
  have hY' := pushforward_trace' hA.perfectPairing j hY hZ 0 0 (2 * 0) 0 (by omega)
    (by omega) (2 * d) d (by ring) (by ring) (by ring) (by ring) x (W.unitTw Y 0 0 rfl)
  rw [pairingTw_apply, cupTw_unitTw_right X (2 * d) 0 (by ring) d 0 (by ring) rfl] at hX'
  rw [pairingTw_apply, cupTw_unitTw_right Y (2 * d) 0 (by ring) d 0 (by ring) rfl] at hY'
  rw [h1, unitTw_eq_add hA hB hC hc hX hY hZ, map_add, ← hX', ← hY']

/-- **The decomposition `a = i_*(i^*a) + j_*(j^*a)`** of a class on a disjoint union `X ⨿ Y` of
nonempty smooth projective schemes equidimensional of the same dimension `d`, in every degree and
twist. This is the first step of the source's proof of Stacks 0FHJ; it is proved by pairing with
an arbitrary class, the trace equation of the pushforward, and the additivity of the trace
(`Stacks.WeilCohomology.WeilData.trace_eq_add`). -/
theorem eq_pushforward_pullTw_add_of_isColimit (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (hc : IsColimit (BinaryCofan.mk i j)) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y d)
    (hZ : IsNonemptyEquidimensional Z d) (n m : ℤ) (a : W.Tw Z n m) :
    a = W.pushforward hA.perfectPairing i hX hZ n m n m (by ring) (by ring) (W.pullTw i n m a) +
      W.pushforward hA.perfectPairing j hY hZ n m n m (by ring) (by ring) (W.pullTw j n m a) := by
  refine eq_of_pairingTw_eq hA.perfectPairing hZ (2 * d - n) n (by ring) (d - m) m (by ring)
    fun b ↦ ?_
  rw [map_add, ← pushforward_trace' hA.perfectPairing i hX hZ n m n m (by ring) (by ring)
      (2 * d - n) (d - m) (by ring) (by ring) (by ring) (by ring),
    ← pushforward_trace' hA.perfectPairing j hY hZ n m n m (by ring) (by ring)
      (2 * d - n) (d - m) (by ring) (by ring) (by ring) (by ring),
    pairingTw_apply, pairingTw_apply, pairingTw_apply, ← W.pullTw_cupTw, ← W.pullTw_cupTw]
  exact trace_eq_add hA hB hC hc hX hY hZ _

/-- A coproduct cofan is the cofan of its two coprojections. -/
def isColimitMkOfIsColimit {X Y : (SmoothProjectiveScheme k).FullSubcategory} {c : BinaryCofan X Y}
    (hc : IsColimit c) : IsColimit (BinaryCofan.mk (P := c.pt) c.inl c.inr) :=
  hc.ofIsoColimit (Cocone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩ <;> exact Category.comp_id _))

/-- **The decomposition `a = i_*(i^*a) + j_*(j^*a)`** on an arbitrary coproduct `c` of `X` and `Y`,
for `X`, `Y` nonempty and equidimensional of the same dimension `d`. -/
theorem eq_pushforward_pullTw_add (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {c : BinaryCofan X Y} (hc : IsColimit c) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y d)
    (hZ : IsNonemptyEquidimensional c.pt d) (n m : ℤ) (a : W.Tw c.pt n m) :
    a = W.pushforward hA.perfectPairing (Y := c.pt) c.inl hX hZ n m n m (by ring) (by ring)
          (W.pullTw (Y := c.pt) c.inl n m a) +
        W.pushforward hA.perfectPairing (Y := c.pt) c.inr hY hZ n m n m (by ring) (by ring)
          (W.pullTw (Y := c.pt) c.inr n m a) :=
  eq_pushforward_pullTw_add_of_isColimit hA hB hC (isColimitMkOfIsColimit hc) hX hY hZ n m a

/-- The decomposition `a = i_*(i^*a) + j_*(j^*a)` for the chosen disjoint union
`Stacks.WeilCohomology.SmoothProjectiveScheme.coprodObj`. -/
theorem eq_pushforward_pullTw_add_coprodObj (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y d)
    (hZ : IsNonemptyEquidimensional (coprodObj X Y) d)
    (n m : ℤ) (a : W.Tw (coprodObj X Y) n m) :
    a = W.pushforward hA.perfectPairing (coprodInl X Y) hX hZ n m n m (by ring) (by ring)
          (W.pullTw (coprodInl X Y) n m a) +
        W.pushforward hA.perfectPairing (coprodInr X Y) hY hZ n m n m (by ring) (by ring)
          (W.pullTw (coprodInr X Y) n m a) :=
  eq_pushforward_pullTw_add_of_isColimit hA hB hC (isColimitCoprodCofan X Y) hX hY hZ n m a

end WeilData

end Stacks.WeilCohomology

end
