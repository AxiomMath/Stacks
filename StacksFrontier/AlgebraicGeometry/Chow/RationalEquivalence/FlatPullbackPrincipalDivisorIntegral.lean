module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback of a principal divisor to an integral scheme

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
integral and locally of finite type over `S` with `n = dim_δ(Y)`, and let `f : X ⟶ Y` be flat of
constant relative dimension `r`. For a nonzero rational function `g` on `Y`, read on `X` through
the extension `R(Y) ⊆ R(X)` of function fields that `f` induces,

  `f^* div_Y(g) = div_X(g)`

in `Z_{n + r - 1}(X)`, as an equality of underlying cycles.

## Main results

* `Stacks.Chow.isDominant_of_flat`: a flat morphism of irreducible schemes is dominant.
* `Stacks.Chow.schemeDeltaDimension_eq_add_of_flat`: an irreducible scheme that is flat of
  relative dimension `r` over an integral scheme of delta-dimension `n` has delta-dimension
  `n + r`.
* `Stacks.Chow.flatPullback_principalDivisorCycle`: the identity above.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0EPH](https://stacks.math.columbia.edu/tag/0EPH)
* [Stacks Project, Tag 02RR](https://stacks.math.columbia.edu/tag/02RR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Dominance and delta-dimension of a flat morphism of irreducible schemes -/

/-- The whole space, as an irreducible component of an irreducible space. -/
private def univComponent (X : Scheme.{u}) [IrreducibleSpace X] : irreducibleComponents X :=
  ⟨Set.univ, by simp [irreducibleComponents_eq_singleton]⟩

/-- A flat morphism between irreducible schemes is dominant. -/
theorem isDominant_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IrreducibleSpace X]
    [IrreducibleSpace Y] : IsDominant f := by
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.image_univ]
  exact dense_image_irreducibleComponent f (univComponent X)

attribute [local instance] isDominant_of_flat

/-- An irreducible scheme that is flat of relative dimension `r` over an integral scheme of
delta-dimension `n` has delta-dimension `n + r`. -/
theorem schemeDeltaDimension_eq_add_of_flat (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IrreducibleSpace X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) {n : ℤ}
    (hY : schemeDeltaDimension C sY = (n : EInt)) :
    schemeDeltaDimension C sX = ((n + (r : ℤ) : ℤ) : EInt) := by
  have hgp : (univComponent X).2.1.genericPoint = genericPoint X :=
    ((univComponent X).2.1.isGenericPoint_genericPoint
      isClosed_univ).eq (genericPoint_spec X)
  have h := relativeDimension_genericPoint_irreducibleComponent C sX sY f hbase r hf hY
    (univComponent X)
  rw [hgp] at h
  rw [schemeDeltaDimension_eq_genericPoint C sX, h]

/-! ### Flat pullback of a principal divisor -/

/-- Let `C = (S, δ)` be the base situation of chapter 42, let `X` and `Y` be integral and
locally of finite type over `S` with `n = dim_δ(Y)`, and let `f : X ⟶ Y` be flat of relative
dimension `r`. For a nonzero rational function `g` on `Y`,

  `f^* div_Y(g) = div_X(g)`

in `Z_{n + r - 1}(X)`, where `g` is read on `X` through the extension `R(Y) ⊆ R(X)` of function
fields induced by `f`. -/
@[stacks 02RR]
theorem flatPullback_principalDivisorCycle (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) {n : ℤ}
    (hY : schemeDeltaDimension C sY = (n : EInt)) (g : Y.functionField) (hg : g ≠ 0) :
    (flatPullback C sX sY f hbase r hf (n - 1) (principalDivisorCycle C sY hY g)).1 =
      (principalDivisorCycle C sX
        (schemeDeltaDimension_eq_add_of_flat C sX sY f hbase r hf hY)
        (dominantFunctionFieldMap f g)).1 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hgen := relativeDimension_genericPoint_irreducibleComponent C sX sY f hbase r hf hY
  apply Function.locallyFinsuppWithin.ext
  intro x
  change (flatPullback C sX sY f hbase r hf (n - 1) (principalDivisorCycle C sY hY g)).1 x =
    (principalDivisorCycle C sX (schemeDeltaDimension_eq_add_of_flat C sX sY f hbase r hf hY)
      (dominantFunctionFieldMap f g)).1 x
  by_cases hx : relativeDimension C.dimensionFunction sX x = n + (r : ℤ) - 1
  · have hcoh : coheight x = 1 :=
      coheight_eq_one_of_relativeDimension_eq_sub_one C sX hgen (n := n + (r : ℤ)) (by omega)
    have hmax : ∀ z : X, z ⤳ x → z ≠ x → IsMax z := fun z hzx hne ↦
      isMax_of_specializes_of_relativeDimension_eq_sub_one C sX hgen (n := n + (r : ℤ))
        (by omega) hzx hne
    by_cases hy : f.base x = genericPoint Y
    · have hlhs : (flatPullback C sX sY f hbase r hf (n - 1)
          (principalDivisorCycle C sY hY g)).1 x = 0 := by
        rw [flatPullback_apply, principalDivisorCycle_apply, hy,
          Scheme.ord_eq_zero_of_coheight_neq_one
            (by simpa using (IsMax.coheight_eq_zero
              (fun w (_ : genericPoint Y ≤ w) ↦ genericPoint_specializes w)) ▸
                (by decide : ¬ (0 : ℕ∞) = 1)) g, zero_mul]
      have hrhs : (principalDivisorCycle C sX
          (schemeDeltaDimension_eq_add_of_flat C sX sY f hbase r hf hY)
          (dominantFunctionFieldMap f g)).1 x = 0 := by
        rw [principalDivisorCycle_apply]
        exact ord_dominantFunctionFieldMap_eq_zero_of_map_eq_genericPoint f hcoh hy hg
      rw [hlhs, hrhs]
    · have hycoh : coheight (f.base x) = 1 := coheight_map_eq_one_of_flat f hmax hy
      obtain ⟨a, b, ha, hb, hrep⟩ := exists_div_algebraMap_stalk_eq (f.base x) hg
      let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
        (f.stalkMap x).hom.toAlgebra
      have halg : algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) =
          (f.stalkMap x).hom := RingHom.algebraMap_toAlgebra _
      have : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) := by
        rw [halg]; infer_instance
      have : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := Flat.stalkMap f x
      have hydim : relativeDimension C.dimensionFunction sY (f.base x) = n - 1 := by
        rw [← deltaDimension_closure_singleton C sY (f.base x)]
        exact deltaDimension_closure_singleton_eq_sub_one C sY hY hycoh
      have hex := exists_genericPoints_comap_integralComponentAt C sX sY f hbase r hf x
        (by rw [hx, hydim]; ring)
      have hweight : flatPullbackWeight C sX f (n - 1 + (r : ℤ)) x =
          ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
            extendedMaximalIdeal (Y.presheaf.stalk (f.base x))
              (X.presheaf.stalk x))).toNat : ℤ) := by
        rw [flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sX f _ x hex
          (by omega), extendedMaximalIdeal, halg]
      have hlen : ∀ v : Y.presheaf.stalk (f.base x),
          ((Module.length (X.presheaf.stalk x)
              (X.presheaf.stalk x ⧸ Ideal.span {(f.stalkMap x).hom v})).toNat : ℤ) =
            ((Module.length (Y.presheaf.stalk (f.base x))
              (Y.presheaf.stalk (f.base x) ⧸ Ideal.span {v})).toNat : ℤ) *
              ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
                extendedMaximalIdeal (Y.presheaf.stalk (f.base x))
                  (X.presheaf.stalk x))).toNat : ℤ) := by
        intro v
        rw [← halg, length_quotient_span_algebraMap v, ENat.toNat_mul, Nat.cast_mul]
      rw [flatPullback_apply, principalDivisorCycle_apply, principalDivisorCycle_apply,
        hweight, ← hrep, ord_div_algebraMap_eq_length_sub hycoh ha hb,
        ord_dominantFunctionFieldMap_eq_length_sub f hcoh ha hb, hlen a, hlen b, sub_mul]
  · have hzero : ∀ (m : ℤ) (c : AlgebraicCycle X ℤ), c ∈ cyclesOfDimension C sX m →
        m = n + (r : ℤ) - 1 → c x = 0 := fun m c hc hm ↦ by
      by_contra hne
      exact hx (by have := (mem_cyclesOfDimension_iff_forall_point C sX m c).mp hc x hne; omega)
    rw [hzero _ _ (flatPullback C sX sY f hbase r hf (n - 1)
        (principalDivisorCycle C sY hY g)).2 (by ring),
      hzero _ _ (principalDivisorCycle C sX
        (schemeDeltaDimension_eq_add_of_flat C sX sY f hbase r hf hY)
        (dominantFunctionFieldMap f g)).2 rfl]

end Stacks.Chow

end
