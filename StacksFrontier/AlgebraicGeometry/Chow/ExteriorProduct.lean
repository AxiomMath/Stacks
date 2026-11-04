module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs

/-!
# The exterior product of algebraic cycles

Let `X` and `Y` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project. Writing `α = ∑ nᵢ [Vᵢ]` and `β = ∑ mⱼ [Wⱼ]` for cycles on `X` and on `Y`, the
exterior product is the cycle

  `α × β = ∑ nᵢ mⱼ [Vᵢ ×_S Wⱼ]`

on `X ×_S Y`, and it is `ℤ`-bilinear, so it is a homomorphism
`Z_r(X) ⟶ Z_s(Y) ⟶ Z_{r+s}(X ×_S Y)`.

Here the exterior product is defined over an arbitrary `Stacks.Chow.ChowSituation` by its
coefficients,

  `(α × β)(z) = α(pr_X z) · β(pr_Y z) · m_z`,

where `m_z` is the multiplicity of `z` in the delta-dimension `r + s` cycle of the product of the
reduced closures of its two projections. When `S` is the spectrum of a field this is the formula
above.

## Main definitions

* `Stacks.Chow.exteriorProductIdeal` — the ideal sheaf on `X ×_S Y` cutting out the product
  `closure {x} ×_S closure {y}` of the reduced closures of two points.
* `Stacks.Chow.exteriorProductWeight` — the multiplicity of a point of `X ×_S Y` in that
  product, in a given delta-dimension.
* `Stacks.Chow.exteriorProductCoeff` — the coefficient function of `α × β`.
* `Stacks.Chow.exteriorProduct` — the exterior product as a homomorphism
  `Z_n(X) ⟶ Z_m(Y) ⟶ Z_{n+m}(X ×_S Y)`.

## Main results

* `Stacks.Chow.exteriorProductCoeff_locallyFiniteSupport` — the coefficient function has
  locally finite support.
* `Stacks.Chow.exteriorProductCoeff_mem_cyclesOfDimension` — it is a cycle of delta-dimension
  `n + m`.
* `Stacks.Chow.exteriorProduct_apply` — the coefficient formula.

## References

* [Stacks Project, Tag 0B09](https://stacks.math.columbia.edu/tag/0B09)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### A local finiteness fact -/

/-- A finite family of locally finitely supported functions is jointly locally finite: around
every point there is a neighbourhood meeting the union of their supports in a finite set. -/
public theorem exists_nhds_finite_of_finset {T : Type u} [TopologicalSpace T] {ι : Type u}
    (s : Finset ι) (a : ι → T → ℤ) (ha : ∀ i ∈ s, LocallyFiniteSupport (a i)) (z : T) :
    ∃ N ∈ nhds z, (N ∩ {w | ∃ i ∈ s, a i w ≠ 0}).Finite := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Set.univ, Filter.univ_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨N, hN, hNfin⟩ := ih fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨M, hM, hMfin⟩ := ha i (Finset.mem_insert_self i s) z
    refine ⟨N ∩ M, Filter.inter_mem hN hM, (hMfin.union hNfin).subset ?_⟩
    rintro w ⟨⟨hwN, hwM⟩, j, hj, hwj⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact Or.inl ⟨hwM, hwj⟩
    · exact Or.inr ⟨hwN, ⟨j, hj, hwj⟩⟩

/-! ### The product of two reduced point closures -/

/-- The ideal sheaf on `X ×_S Y` cutting out the product `closure {x} ×_S closure {y}` of the
reduced closures of `x : X` and `y : Y`: the sum of the inverse images of their vanishing ideal
sheaves. -/
def exteriorProductIdeal {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) :
    (pullback f g : Scheme.{u}).IdealSheafData :=
  ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).comap
      (pullback.fst f g)) ⊔
    ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).comap
      (pullback.snd f g))

/-- The multiplicity with which a point `z` of `X ×_S Y` enters the delta-dimension `j` cycle of
the product `closure {x} ×_S closure {y}` of the reduced closures of `x` and `y`. -/
def exteriorProductWeight (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (j : ℤ) (x : X) (y : Y)
    (z : (pullback f g : Scheme.{u})) : ℤ :=
  closedSubschemeCycleCoeff C (pullback.fst f g ≫ f) (exteriorProductIdeal f g x y).subschemeι
    j z

/-- The multiplicity of a point in a product of reduced point closures is locally finitely
supported. -/
theorem exteriorProductWeight_locallyFiniteSupport (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (j : ℤ)
    (x : X) (y : Y) :
    LocallyFiniteSupport (exteriorProductWeight C f g j x y) :=
  closedSubschemeCycleCoeff_locallyFiniteSupport C (pullback.fst f g ≫ f)
    (exteriorProductIdeal f g x y).subschemeι j

/-! ### The exterior product of cycles -/

/-- The coefficient at `z` of the exterior product `α × β`: the product of the coefficients of
`α` and `β` at the two projections of `z`, times the multiplicity of `z` in the product of the
reduced closures of those projections. -/
def exteriorProductCoeff (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)
    (α : CycleGroup C f n) (β : CycleGroup C g m) (z : (pullback f g : Scheme.{u})) : ℤ :=
  α.1 ((pullback.fst f g).base z) * β.1 ((pullback.snd f g).base z) *
    exteriorProductWeight C f g (n + m) ((pullback.fst f g).base z)
      ((pullback.snd f g).base z) z

/-- The coefficient function of an exterior product has locally finite support. -/
theorem exteriorProductCoeff_locallyFiniteSupport (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)
    (α : CycleGroup C f n) (β : CycleGroup C g m) :
    LocallyFiniteSupport (exteriorProductCoeff C f g n m α β) := by
  classical
  intro z
  obtain ⟨V, hV, hVfin⟩ :=
    Function.locallyFinsupp.locallyFiniteSupport α.1 ((pullback.fst f g).base z)
  obtain ⟨W, hW, hWfin⟩ :=
    Function.locallyFinsupp.locallyFiniteSupport β.1 ((pullback.snd f g).base z)
  obtain ⟨N, hN, hNfin⟩ :=
    exists_nhds_finite_of_finset (hVfin.toFinset ×ˢ hWfin.toFinset)
      (fun p ↦ exteriorProductWeight C f g (n + m) p.1 p.2)
      (fun p _ ↦ exteriorProductWeight_locallyFiniteSupport C f g (n + m) p.1 p.2) z
  refine ⟨(pullback.fst f g).base ⁻¹' V ∩ (pullback.snd f g).base ⁻¹' W ∩ N,
    Filter.inter_mem (Filter.inter_mem ((pullback.fst f g).continuous.continuousAt hV)
      ((pullback.snd f g).continuous.continuousAt hW)) hN, hNfin.subset ?_⟩
  rintro w ⟨⟨⟨hwV, hwW⟩, hwN⟩, hwsupp⟩
  have hw : α.1 ((pullback.fst f g).base w) * β.1 ((pullback.snd f g).base w) *
      exteriorProductWeight C f g (n + m) ((pullback.fst f g).base w)
        ((pullback.snd f g).base w) w ≠ 0 := hwsupp
  obtain ⟨hprod, hweight⟩ := mul_ne_zero_iff.1 hw
  obtain ⟨hα, hβ⟩ := mul_ne_zero_iff.1 hprod
  refine ⟨hwN, ⟨((pullback.fst f g).base w, (pullback.snd f g).base w), ?_, hweight⟩⟩
  rw [Finset.mem_product]
  exact ⟨(Set.Finite.mem_toFinset hVfin).2 ⟨hwV, hα⟩,
    (Set.Finite.mem_toFinset hWfin).2 ⟨hwW, hβ⟩⟩

/-- The coefficient function of an exterior product is a cycle of delta-dimension `n + m`. -/
theorem exteriorProductCoeff_mem_cyclesOfDimension (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)
    (α : CycleGroup C f n) (β : CycleGroup C g m) :
    (⟨exteriorProductCoeff C f g n m α β, fun _ _ ↦ trivial, fun z _ ↦
      exteriorProductCoeff_locallyFiniteSupport C f g n m α β z⟩ :
        AlgebraicCycle (pullback f g : Scheme.{u}) ℤ) ∈
      cyclesOfDimension C (pullback.fst f g ≫ f) (n + m) := by
  rw [mem_cyclesOfDimension]
  intro Z hZ
  change exteriorProductCoeff C f g n m α β Z.isIrreducible.genericPoint ≠ 0 at hZ
  have hweight := (mul_ne_zero_iff.1 hZ).2
  have hdim : relativeDimension C.dimensionFunction (pullback.fst f g ≫ f)
      Z.isIrreducible.genericPoint = n + m := by
    unfold exteriorProductWeight closedSubschemeCycleCoeff at hweight
    split at hweight
    · rename_i h
      exact h.choose_spec.2
    · contradiction
  rw [deltaDimension_eq_of_isGenericPoint C (pullback.fst f g ≫ f) Z
    Z.isIrreducible.genericPoint
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)]
  exact hdim

/-- The exterior product of cycles, `Z_n(X) ⟶ Z_m(Y) ⟶ Z_{n+m}(X ×_S Y)`, sending `α` and `β`
to the cycle whose coefficient at `z` is `α(pr_X z) · β(pr_Y z)` times the multiplicity of `z`
in the product of the reduced closures of the two projections of `z`. -/
def exteriorProduct (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ) :
    CycleGroup C f n →+ CycleGroup C g m →+
      CycleGroup C (pullback.fst f g ≫ f) (n + m) where
  toFun α :=
    { toFun := fun β ↦ ⟨⟨exteriorProductCoeff C f g n m α β, fun _ _ ↦ trivial, fun z _ ↦
          exteriorProductCoeff_locallyFiniteSupport C f g n m α β z⟩,
        exteriorProductCoeff_mem_cyclesOfDimension C f g n m α β⟩
      map_zero' := by
        apply Subtype.ext
        ext z
        change exteriorProductCoeff C f g n m α 0 z = 0
        simp [exteriorProductCoeff]
      map_add' := by
        intro β γ
        apply Subtype.ext
        ext z
        change exteriorProductCoeff C f g n m α (β + γ) z =
          exteriorProductCoeff C f g n m α β z + exteriorProductCoeff C f g n m α γ z
        simp only [exteriorProductCoeff]
        change α.1 _ * (β.1 _ + γ.1 _) * _ = _
        ring }
  map_zero' := by
    ext β z
    change exteriorProductCoeff C f g n m 0 β z = 0
    simp [exteriorProductCoeff]
  map_add' α α' := by
    ext β z
    change exteriorProductCoeff C f g n m (α + α') β z =
      exteriorProductCoeff C f g n m α β z + exteriorProductCoeff C f g n m α' β z
    simp only [exteriorProductCoeff]
    change (α.1 _ + α'.1 _) * β.1 _ * _ = _
    ring

/-- The coefficient formula for the exterior product of two cycles. -/
@[simp]
theorem exteriorProduct_apply (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)
    (α : CycleGroup C f n) (β : CycleGroup C g m) (z : (pullback f g : Scheme.{u})) :
    (exteriorProduct C f g n m α β).1 z =
      α.1 ((pullback.fst f g).base z) * β.1 ((pullback.snd f g).base z) *
        exteriorProductWeight C f g (n + m) ((pullback.fst f g).base z)
          ((pullback.snd f g).base z) z :=
  rfl

/-- The coefficient of `α × β` at `z` is `α(pr_X z) · β(pr_Y z)` times the coefficient at `z` of
the cycle `[closure {pr_X z} ×_S closure {pr_Y z}]_{n+m}` of the product of the reduced closures
of the two projections of `z`. -/
theorem exteriorProduct_apply_eq_cycleAssociatedToClosedSubscheme (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (n m : ℤ) (α : CycleGroup C f n) (β : CycleGroup C g m)
    (z : (pullback f g : Scheme.{u})) :
    (exteriorProduct C f g n m α β).1 z =
      α.1 ((pullback.fst f g).base z) * β.1 ((pullback.snd f g).base z) *
        (cycleAssociatedToClosedSubscheme C (pullback.fst f g ≫ f)
          (exteriorProductIdeal f g ((pullback.fst f g).base z)
            ((pullback.snd f g).base z)).subschemeι (n + m)).1 z :=
  rfl

end Stacks.Chow

end
