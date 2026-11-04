module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FibreCardinality
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Point fibres of a morphism with universally bounded fibres

Let `U` be an object of the big fppf site over a scheme `S` and let `f : h_U ⟶ X` be a
morphism to a presheaf on that site. If the fibres of `f` are universally bounded, then one
natural number bounds the number of points of `|h_U|` above each point of `|X|`; in
particular every such fibre is finite.

## Main results

* `AlgebraicGeometry.Space.cardinalMk_pointFiber_le_of_hasUniversallyBoundedFibers`:
  **Stacks 03JQ**, the uniform cardinality bound.
* `AlgebraicGeometry.Space.finite_pointFiber_of_hasUniversallyBoundedFibers`: the resulting
  finiteness of each fibre, which is the form the conditions of Stacks 03JX ask for.

## Implementation notes

The bound of Stacks 03JL is an integer and the bound produced here is its truncation to a
natural number, which is the same bound because a degree is a natural number. Stating the
conclusion as a bound on `Cardinal.mk` of the fibre rather than on the cardinality of a
finite type asserts finiteness of the fibre at the same time, and needs no finiteness
instance to be stated.

The source assumes that `X` is an algebraic space. That hypothesis is not used: the point
set of Stacks 03BU and the cartesian squares defining universally bounded fibres make sense
for an arbitrary presheaf, so the statement is proved at that generality.

The three ingredients are the surjectivity of the comparison map of a cartesian square on
points, `AlgebraicGeometry.Space.exists_points_of_isPullback` of Stacks 03H4, which realises
the fibre above a point as the image of the points of the fibre product; the identification
`AlgebraicGeometry.Space.pointsEquivScheme` of the points of a represented presheaf with the
points of the representing scheme; and `AlgebraicGeometry.cardinalMk_pullback_le_of_degree_le`
of Stacks 03J5, which bounds the number of points of a scheme that is finite locally free of
bounded degree over the spectrum of a field. Only the last needs the degree bound, and it
needs it after an arbitrary field-valued base change, which is available because the rank of
a finite locally free morphism is stable under base change.

## References

* [Stacks Project, Tag 03JQ](https://stacks.math.columbia.edu/tag/03JQ)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X)

/-- A scheme finite locally free of rank `r` over the spectrum of a field has at most `r`
points. -/
private theorem cardinalMk_le_of_isFiniteLocallyFreeOfRank {Y T : Scheme.{u}} (g : Y ⟶ T) (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g r] {k : Type u} [Field k]
    (e : T ≅ Spec (CommRingCat.of k)) : Cardinal.mk Y ≤ (r : Cardinal.{u}) := by
  have hdeg : ∀ (k' : Type u) [Field k'] (g' : Spec (CommRingCat.of k') ⟶ T),
      ∃ s ≤ r, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g' g) s := fun _ _ g' ↦
    ⟨r, le_rfl, Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback g' g).flip⟩
  have : IsIso (pullback.snd e.inv g) := (IsPullback.of_hasPullback e.inv g).isIso_snd_of_isIso
  exact (Cardinal.mk_congr (Scheme.homeoOfIso (asIso (pullback.snd e.inv g)).symm).toEquiv).trans_le
    (cardinalMk_pullback_le_of_degree_le g r hdeg k e.inv)

/-- **Stacks 03JQ.** If the fibres of a morphism `f : h_U ⟶ X` from a represented presheaf
are universally bounded, then one natural number bounds the number of points of `|h_U|`
lying above each point of `|X|`. -/
@[stacks 03JQ]
theorem cardinalMk_pointFiber_le_of_hasUniversallyBoundedFibers
    (hf : HasUniversallyBoundedFibers B S hS U f) :
    ∃ n : ℕ, ∀ x : points B S hS X,
      Cardinal.mk (pointsMap B S hS (yoneda.obj U) f ⁻¹' {x}) ≤ (n : Cardinal) := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨N.toNat, fun x ↦ ?_⟩
  obtain ⟨q, hq⟩ := Quot.exists_rep x
  have hqx : q.class B S hS X = x := hq
  -- The field-valued representative `q` of `x` presents it by a morphism out of the
  -- presheaf represented by the spectrum of its field of definition.
  have hT : (BigFppfOver.toScheme B S hS).obj (q.siteObject B S hS X) ≅
      Spec (CommRingCat.of q.carrier) := Iso.refl _
  obtain ⟨P, p, i, r, hr, hrank, hpb⟩ :=
    hN q.carrier (q.siteObject B S hS X) hT (fieldMorphism B S hS X q)
  have : Subsingleton (points B S hS (yoneda.obj (q.siteObject B S hS X))) :=
    subsingleton_points_yoneda_fieldSpec B S hS q.carrier q.contained q.toBase
  have hpt : pointsMap B S hS (yoneda.obj (q.siteObject B S hS X)) (fieldMorphism B S hS X q)
      ((q.tautologicalPoint B S hS X).class B S hS (yoneda.obj (q.siteObject B S hS X))) = x :=
    (pointsMap_fieldMorphism_tautologicalPoint B S hS X q).trans hqx
  -- Every point of the fibre product lies above `x`.
  have hval : ∀ w : points B S hS (yoneda.obj P),
      pointsMap B S hS (yoneda.obj U) f (pointsMap B S hS (yoneda.obj P) i w) = x :=
    fun w ↦ by
      rw [← pointsMap_comp_apply, hpb.w, pointsMap_comp_apply,
        Subsingleton.elim (pointsMap B S hS (yoneda.obj P) (yoneda.map p) w)
          ((q.tautologicalPoint B S hS X).class B S hS (yoneda.obj (q.siteObject B S hS X)))]
      exact hpt
  -- and conversely every point of the fibre comes from one, by Stacks 03H4.
  have hsurj : Function.Surjective (fun w : points B S hS (yoneda.obj P) ↦
      (⟨pointsMap B S hS (yoneda.obj P) i w,
        Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (hval w))⟩ :
          (pointsMap B S hS (yoneda.obj U) f ⁻¹' {x} : Set _))) := by
    rintro ⟨y, hy⟩
    have hy' : pointsMap B S hS (yoneda.obj U) f y = x :=
      Set.mem_singleton_iff.mp (Set.mem_preimage.mp hy)
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hpb y
      ((q.tautologicalPoint B S hS X).class B S hS (yoneda.obj (q.siteObject B S hS X)))
      (hy'.trans hpt.symm)
    exact ⟨w, Subtype.ext hw⟩
  -- The fibre product is a scheme finite locally free of rank `r ≤ N` over a field, so it
  -- has at most `r` points.
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map p) r :=
    hrank
  calc Cardinal.mk (pointsMap B S hS (yoneda.obj U) f ⁻¹' {x})
      ≤ Cardinal.mk (points B S hS (yoneda.obj P)) := Cardinal.mk_le_of_surjective hsurj
    _ = Cardinal.lift.{u + 1, u}
          (Cardinal.mk ((BigFppfOver.toScheme B S hS).obj P)) := by
        rw [← Cardinal.mk_uLift]
        exact Cardinal.mk_congr ((pointsEquivScheme B S hS P).trans Equiv.ulift.symm)
    _ ≤ Cardinal.lift.{u + 1, u} (r : Cardinal.{u}) :=
        Cardinal.lift_le.2
          (cardinalMk_le_of_isFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map p) r hT)
    _ = (r : Cardinal.{u + 1}) := by simp
    _ ≤ (N.toNat : Cardinal.{u + 1}) := by exact_mod_cast (show r ≤ N.toNat by omega)

/-- If the fibres of a morphism `f : h_U ⟶ X` from a represented presheaf are universally
bounded, then the fibre of `|h_U| → |X|` above every point is finite. -/
theorem finite_pointFiber_of_hasUniversallyBoundedFibers
    (hf : HasUniversallyBoundedFibers B S hS U f) (x : points B S hS X) :
    (pointsMap B S hS (yoneda.obj U) f ⁻¹' {x}).Finite := by
  obtain ⟨n, hn⟩ := cardinalMk_pointFiber_le_of_hasUniversallyBoundedFibers B S hS U f hf
  exact Cardinal.lt_aleph0_iff_set_finite.mp ((hn x).trans_lt Cardinal.natCast_lt_aleph0)

end AlgebraicGeometry.Space

end
