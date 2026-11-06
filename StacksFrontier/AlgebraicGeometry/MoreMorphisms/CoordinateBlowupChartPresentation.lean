module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth
public import StacksFrontier.RingTheory.Kaehler.BlowupChartDifferentials

/-!
# The standard affine chart of the coordinate blowup, with its structure map

Fix a commutative ring `R` and integers `m, n ≥ 0`. Write affine `(m + n)`-space over `R` as
`Spec A` with `A = R[x₁, …, x_m, y₁, …, y_n]`, the polynomial ring on `Fin m ⊕ Fin n`, and let
`Z = 𝔸^m_R ⟶ 𝔸^{m+n}_R` be the closed immersion setting the last `n` coordinates to zero.

`Stacks.MoreMorphisms.coordinateChart_equiv_polynomial` identifies the `i`-th standard affine
chart of the blowup of `𝔸^{m+n}_R` along `Z` with a polynomial ring, on the variables
`x₁, …, x_m`, the pivot `y_i` and the ratios `t_j = y_j/y_i` for `j ≠ i`. Reindexing those
variables by `Fin m ⊕ Fin n` — the pivot becoming the `i`-th variable of the second block and the
ratio `t_j` the `j`-th — turns the four substitution formulas carried by that statement into the
single assertion that the chart's structure map over the ambient coordinate ring *is* the chart
morphism `Stacks.Kaehler.blowupChartHom`, namely the `R`-algebra endomorphism of `A` with
`x_k ↦ x_k`, `y_i ↦ y_i` and `y_j ↦ y_i y_j` for `j ≠ i`. That is what this file proves, in the
presentation of the chart that `AlgebraicGeometry.blowupChartι` uses, where the base of the affine
blowup algebra is the ring of global sections `Γ(Spec A, ⊤)` rather than `A` itself.

## Main definitions

* `Stacks.MoreMorphisms.coordinateChartReindex`: the reindexing
  `Fin m ⊕ (Unit ⊕ {j // j ≠ i}) ≃ Fin m ⊕ Fin n` of the chart's variables, carrying the pivot to
  `Sum.inr i` and the ratio `t_j` to `Sum.inr j`.
* `Stacks.MoreMorphisms.coordinateChartRename`: the induced isomorphism of polynomial rings.
* `Stacks.MoreMorphisms.coordinateBlowupChartRing`: the coordinate ring of the `i`-th standard
  affine chart of the coordinate blowup, in the presentation `AlgebraicGeometry.blowupChartι`
  uses.
* `Stacks.MoreMorphisms.coordinateBlowupChartStructureMap`: its structure map, read on the
  coordinate ring `A` of the ambient affine space.

## Main results

* `Stacks.MoreMorphisms.exists_coordinateBlowupChartPresentation`: the chart's coordinate ring is
  the polynomial ring `A` in such a way that its structure map becomes
  `Stacks.Kaehler.blowupChartHom`, and the exceptional ideal becomes `(y_i)`.
* `Stacks.MoreMorphisms.exists_coordinateChartEquiv_blowupChartHom`: the same statement for the
  presentation of the chart whose base is `A` itself.
* `Stacks.MoreMorphisms.map_coordinateRingIdeal_blowupChartHom`: the image of the ideal of the
  last `n` coordinates under `Stacks.Kaehler.blowupChartHom` generates `(y_i)`.

## Implementation notes

The chart isomorphism is produced as an existential statement, as
`Stacks.MoreMorphisms.coordinateChart_equiv_polynomial` is: the content is the two formulas it is
pinned by, and naming the map would commit to one of the two mutually inverse directions.

The structure map is pinned on all of `A`, not just on the variables. Both sides are ring maps out
of a polynomial ring, so the extension from the variables to all of `A` is a three-case induction;
it is done by hand rather than through `MvPolynomial.algHom_ext`, because the isomorphism coming
out of the existential statement is a `RingEquiv` and packaging it as an `AlgHom` would need the
very formula on constants that the induction's base case is.

The exceptional ideal is transported in the form `Ideal.map` of the structure map followed by
`Ideal.map` of the isomorphism, which is the image of the ideal sheaf on global sections in the
chart; `Ideal.map_map` turns the composite into `Stacks.Kaehler.blowupChartHom`, and the
computation is then the ring-theoretic statement that `blowupChartHom` carries `(y₁, …, y_n)`
onto `(y_i)`.

## References

* [Stacks Project, Tag 0H1H](https://stacks.math.columbia.edu/tag/0H1H)
* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial Stacks.Kaehler

universe u

namespace Stacks.MoreMorphisms

variable (R : Type u) [CommRing R] (m n : ℕ) (i : Fin n)

/-! ### Reindexing the variables of the chart -/

/-- The pivot and the ratios of the `i`-th chart, reindexed by the last `n` coordinates: the
pivot becomes the `i`-th coordinate and the ratio `t_j` becomes the `j`-th. -/
public def coordinateChartPivotEquiv : Unit ⊕ {j : Fin n // j ≠ i} ≃ Fin n where
  toFun := Sum.elim (fun _ ↦ i) fun j ↦ j.1
  invFun j := if h : j = i then Sum.inl () else Sum.inr ⟨j, h⟩
  left_inv v := by
    obtain _ | j := v
    · simp
    · simp [j.2]
  right_inv j := by by_cases h : j = i <;> simp [h]

/-- The reindexing of the variables of the `i`-th chart by the variables of the ambient affine
space: the first `m` coordinates are fixed, the pivot becomes the `i`-th of the last `n`
coordinates, and the ratio `t_j` becomes the `j`-th. -/
public def coordinateChartReindex : coordinateChartVariables m n i ≃ Fin m ⊕ Fin n :=
  Equiv.sumCongr (Equiv.refl (Fin m)) (coordinateChartPivotEquiv n i)

/-- The isomorphism of polynomial rings induced by
`Stacks.MoreMorphisms.coordinateChartReindex`. -/
public def coordinateChartRename :
    MvPolynomial (coordinateChartVariables m n i) R ≃+* MvPolynomial (Fin m ⊕ Fin n) R :=
  (renameEquiv R (coordinateChartReindex m n i)).toRingEquiv

/-- `Stacks.MoreMorphisms.coordinateChartRename` is renaming along the reindexing. -/
public theorem coordinateChartRename_apply
    (p : MvPolynomial (coordinateChartVariables m n i) R) :
    coordinateChartRename R m n i p = rename (coordinateChartReindex m n i) p := rfl

/-- The reindexing fixes the constants. -/
public theorem coordinateChartRename_C (r : R) :
    coordinateChartRename R m n i (C r) = C r := by
  rw [coordinateChartRename_apply, rename_C]

/-- The reindexing acts on a variable by the reindexing of the variables. -/
private theorem coordinateChartRename_X (v : coordinateChartVariables m n i) :
    coordinateChartRename R m n i (X v) = X (coordinateChartReindex m n i v) :=
  rename_X _ _

/-- The reindexing fixes the first `m` coordinates. -/
public theorem coordinateChartRename_X_inl (k : Fin m) :
    coordinateChartRename R m n i (X (Sum.inl k)) = X (Sum.inl k) :=
  coordinateChartRename_X ..

/-- The reindexing carries the pivot to the `i`-th of the last `n` coordinates. -/
public theorem coordinateChartRename_X_pivot :
    coordinateChartRename R m n i (X (Sum.inr (Sum.inl ()))) = X (Sum.inr i) :=
  coordinateChartRename_X ..

/-- The reindexing carries the ratio `t_j` to the `j`-th of the last `n` coordinates. -/
public theorem coordinateChartRename_X_ratio (j : {j : Fin n // j ≠ i}) :
    coordinateChartRename R m n i (X (Sum.inr (Sum.inr j))) = X (Sum.inr j.1) :=
  coordinateChartRename_X ..

/-! ### The chart morphism on the ideal of the last coordinates -/

/-- The chart morphism carries the ideal of the last `n` coordinates onto the principal ideal
generated by the `i`-th of them, the equation of the exceptional divisor. -/
public theorem map_coordinateRingIdeal_blowupChartHom :
    Ideal.map (blowupChartHom R (Fin m) (Fin n) i).toRingHom (coordinateRingIdeal R m n) =
      Ideal.span {X (Sum.inr i)} := by
  have hgen : ∀ j : Fin n,
      (blowupChartHom R (Fin m) (Fin n) i).toRingHom (X (Sum.inr j)) ∈
        Ideal.span {(X (Sum.inr i) : MvPolynomial (Fin m ⊕ Fin n) R)} := by
    intro j
    rw [Ideal.mem_span_singleton]
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hj]
  have hself : (X (Sum.inr i) : MvPolynomial (Fin m ⊕ Fin n) R) =
      (blowupChartHom R (Fin m) (Fin n) i).toRingHom (X (Sum.inr i)) := by simp
  refine le_antisymm ?_ ?_
  · rw [coordinateRingIdeal, Ideal.map_span, ← Set.range_comp, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hgen j
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hself]
    exact Ideal.mem_map_of_mem _ (X_inr_mem_coordinateRingIdeal R m n i)

/-! ### The chart over the ambient coordinate ring -/

/-- The structure map of the `i`-th chart carries a constant to the corresponding constant of the
chart. -/
private theorem algebraMap_coordinateChartAlgebra_C (r : R) :
    algebraMap (MvPolynomial (Fin m ⊕ Fin n) R) (coordinateChartAlgebra R m n i) (C r) =
      algebraMap R (coordinateChartAlgebra R m n i) r :=
  (IsScalarTower.algebraMap_apply R (MvPolynomial (Fin m ⊕ Fin n) R)
    (coordinateChartAlgebra R m n i) r).symm

/-- **The `i`-th standard affine blowup chart is affine space, with the chart morphism as its
structure map.** This is `Stacks.MoreMorphisms.coordinateChart_equiv_polynomial` with the chart's
variables reindexed by those of the ambient affine space: the four substitution formulas carried
by that statement become the single assertion that the structure map of the chart over the
ambient coordinate ring is `Stacks.Kaehler.blowupChartHom`. -/
public theorem exists_coordinateChartEquiv_blowupChartHom :
    ∃ e : coordinateChartAlgebra R m n i ≃+* MvPolynomial (Fin m ⊕ Fin n) R,
      ∀ p : MvPolynomial (Fin m ⊕ Fin n) R,
        e (algebraMap (MvPolynomial (Fin m ⊕ Fin n) R) (coordinateChartAlgebra R m n i) p) =
          blowupChartHom R (Fin m) (Fin n) i p := by
  obtain ⟨e, hC, hinl, hpivot, hratio⟩ := coordinateChart_equiv_polynomial R m n i
  have hX : ∀ v : Fin m ⊕ Fin n,
      coordinateChartRename R m n i (e (algebraMap (MvPolynomial (Fin m ⊕ Fin n) R)
          (coordinateChartAlgebra R m n i) (X v))) =
        blowupChartHom R (Fin m) (Fin n) i (X v) := by
    intro v
    obtain k | j := v
    · rw [hinl k, coordinateChartRename_X_inl, blowupChartHom_X_inl]
    · rcases eq_or_ne j i with rfl | hj
      · rw [hpivot, coordinateChartRename_X_pivot, blowupChartHom_X_inr_self]
      · rw [hratio j hj, map_mul, coordinateChartRename_X_pivot,
          coordinateChartRename_X_ratio, blowupChartHom_X_inr_of_ne _ _ _ _ hj]
  refine ⟨e.trans (coordinateChartRename R m n i), fun p ↦ ?_⟩
  rw [RingEquiv.trans_apply]
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [algebraMap_coordinateChartAlgebra_C, hC r, coordinateChartRename_C,
      MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    rw [(algebraMap _ _).map_add, e.map_add, (coordinateChartRename R m n i).map_add, hp, hq]
    exact (map_add (blowupChartHom R (Fin m) (Fin n) i) p q).symm
  | mul_X p v hp =>
    rw [(algebraMap _ _).map_mul, e.map_mul, (coordinateChartRename R m n i).map_mul, hp, hX v]
    exact (map_mul (blowupChartHom R (Fin m) (Fin n) i) p (X v)).symm

/-! ### The chart over the ring of global sections -/

/-- The coordinate ring of the `i`-th standard affine chart of the coordinate blowup, in the
presentation `AlgebraicGeometry.blowupChartι` uses: the affine blowup algebra of the ideal sheaf
of the centre on global sections, at the global section `y_i`. -/
public abbrev coordinateBlowupChartRing :=
  affineBlowupAlgebra ((coordinateIdeal R m n).ideal (topAffineOpen R m n))
    (coordinateSection R m n i) (Localization.Away (coordinateSection R m n i))

/-- The structure map of the `i`-th standard affine chart of the coordinate blowup, read on the
coordinate ring of the ambient affine space through `Stacks.MoreMorphisms.gammaEquiv`. -/
public def coordinateBlowupChartStructureMap :
    MvPolynomial (Fin m ⊕ Fin n) R →+* coordinateBlowupChartRing R m n i :=
  (algebraMap Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)
      (coordinateBlowupChartRing R m n i)).comp
    (gammaEquiv R m n : MvPolynomial (Fin m ⊕ Fin n) R →+*
      Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤))

/-- The structure map of the chart is the algebra map of the affine blowup algebra, precomposed
with the identification of the coordinate ring with the ring of global sections. -/
public theorem coordinateBlowupChartStructureMap_apply (p : MvPolynomial (Fin m ⊕ Fin n) R) :
    coordinateBlowupChartStructureMap R m n i p =
      algebraMap Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)
        (coordinateBlowupChartRing R m n i) (gammaEquiv R m n p) := rfl

/-- The structure morphism of the `i`-th standard chart of the coordinate blowup over the ambient
affine space, in the form of `AlgebraicGeometry.blowupChartι_comp_blowUpToBase`: it is `Spec` of
the algebra map of `Stacks.MoreMorphisms.coordinateBlowupChartRing`, followed by the inclusion of
the ambient affine space. -/
public theorem blowupChartι_comp_blowUpToBase_coordinateIdeal :
    blowupChartι (coordinateIdeal R m n) (topAffineOpen R m n)
          (coordinateIdealSection R m n i) ≫ blowUpToBase (coordinateIdeal R m n) =
      Spec.map (CommRingCat.ofHom
          (algebraMap Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)
            (coordinateBlowupChartRing R m n i))) ≫ (topAffineOpen R m n).2.fromSpec :=
  blowupChartι_comp_blowUpToBase _ _ _

/-- The exceptional ideal of the `i`-th chart, transported along any isomorphism of the chart
with affine space that identifies the structure map with the chart morphism, is generated by the
`i`-th of the last `n` coordinates. -/
public theorem map_coordinateIdeal_of_structureMap_eq
    (e : coordinateBlowupChartRing R m n i ≃+* MvPolynomial (Fin m ⊕ Fin n) R)
    (he : ∀ p : MvPolynomial (Fin m ⊕ Fin n) R,
      e (coordinateBlowupChartStructureMap R m n i p) = blowupChartHom R (Fin m) (Fin n) i p) :
    Ideal.map (e : coordinateBlowupChartRing R m n i →+* MvPolynomial (Fin m ⊕ Fin n) R)
        (Ideal.map (algebraMap Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)
            (coordinateBlowupChartRing R m n i))
          ((coordinateIdeal R m n).ideal (topAffineOpen R m n))) =
      Ideal.span {X (Sum.inr i)} := by
  have hcomp :
      ((e : coordinateBlowupChartRing R m n i →+* MvPolynomial (Fin m ⊕ Fin n) R).comp
            (algebraMap Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)
              (coordinateBlowupChartRing R m n i))).comp
          (gammaEquiv R m n : MvPolynomial (Fin m ⊕ Fin n) R →+*
            Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)) =
        (blowupChartHom R (Fin m) (Fin n) i).toRingHom :=
    RingHom.ext he
  rw [coordinateIdeal_ideal_top, Ideal.map_map, Ideal.map_map, hcomp,
    map_coordinateRingIdeal_blowupChartHom]

/-- The two presentations of the `i`-th standard affine chart agree: the affine blowup algebra
over the coordinate ring of the ambient affine space is the affine blowup algebra over its ring
of global sections, compatibly with the two structure maps. This is
`Stacks.Blowup.exists_ringEquiv_affineBlowupAlgebra'` applied to
`Stacks.MoreMorphisms.gammaEquiv`. -/
private theorem exists_coordinateBlowupChartTransport :
    ∃ E : coordinateChartAlgebra R m n i ≃+* coordinateBlowupChartRing R m n i,
      ∀ p : MvPolynomial (Fin m ⊕ Fin n) R,
        E (algebraMap (MvPolynomial (Fin m ⊕ Fin n) R) (coordinateChartAlgebra R m n i) p) =
          coordinateBlowupChartStructureMap R m n i p := by
  obtain ⟨E, hE⟩ := Stacks.Blowup.exists_ringEquiv_affineBlowupAlgebra'
    (gammaEquiv R m n) (chartLocalizationEquiv R m n i)
    (X (Sum.inr i) : MvPolynomial (Fin m ⊕ Fin n) R) (coordinateRingIdeal R m n)
    ((coordinateIdeal R m n).ideal (topAffineOpen R m n)) (coordinateSection R m n i)
    (fun x ↦ IsLocalization.ringEquivOfRingEquiv_eq _ x)
    (coordinateIdeal_ideal_top R m n) rfl
  refine ⟨E, fun p ↦ Subtype.ext ?_⟩
  rw [hE, coordinateBlowupChartStructureMap_apply, Subalgebra.coe_algebraMap,
    Subalgebra.coe_algebraMap]
  exact IsLocalization.ringEquivOfRingEquiv_eq _ p

/-- **The `i`-th standard affine chart of the coordinate blowup is affine space, with the chart
morphism as its structure map.** The chart's coordinate ring, in the presentation
`AlgebraicGeometry.blowupChartι` uses, is the polynomial ring on `Fin m ⊕ Fin n` over `R` in such
a way that the structure map over the ambient coordinate ring becomes
`Stacks.Kaehler.blowupChartHom`; and under that isomorphism the exceptional ideal — the image in
the chart of the ideal sheaf of the centre on global sections — is generated by the `i`-th of the
last `n` coordinates. -/
public theorem exists_coordinateBlowupChartPresentation :
    ∃ e : coordinateBlowupChartRing R m n i ≃+* MvPolynomial (Fin m ⊕ Fin n) R,
      (∀ p : MvPolynomial (Fin m ⊕ Fin n) R,
          e (coordinateBlowupChartStructureMap R m n i p) =
            blowupChartHom R (Fin m) (Fin n) i p) ∧
        Ideal.map (e : coordinateBlowupChartRing R m n i →+* MvPolynomial (Fin m ⊕ Fin n) R)
            (Ideal.map (algebraMap Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)
                (coordinateBlowupChartRing R m n i))
              ((coordinateIdeal R m n).ideal (topAffineOpen R m n))) =
          Ideal.span {X (Sum.inr i)} := by
  obtain ⟨E, hE⟩ := exists_coordinateBlowupChartTransport R m n i
  obtain ⟨e, he⟩ := exists_coordinateChartEquiv_blowupChartHom R m n i
  have hpin : ∀ p : MvPolynomial (Fin m ⊕ Fin n) R,
      (E.symm.trans e) (coordinateBlowupChartStructureMap R m n i p) =
        blowupChartHom R (Fin m) (Fin n) i p := fun p ↦ by
    rw [RingEquiv.trans_apply, (RingEquiv.symm_apply_eq E).mpr (hE p).symm, he p]
  exact ⟨E.symm.trans e, hpin,
    map_coordinateIdeal_of_structureMap_eq R m n i (E.symm.trans e) hpin⟩

end Stacks.MoreMorphisms

end
