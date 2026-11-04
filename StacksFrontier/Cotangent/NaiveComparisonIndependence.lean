module

public import StacksFrontier.Cotangent.NaiveComparisonMap

/-!
# The comparison map of Tag 08R9 does not depend on the chosen morphism

`Stacks.Cotangent.comparisonOfHom` is built from a chosen morphism of extensions
`U ⟶ (A[B] → B)` into the degree-zero term of the standard resolution. This file shows that the
map in `D(B)` it produces is the same for every choice, so that `Stacks.Cotangent.comparison` —
which takes the morphism attached to a presentation of `U` by variables, hence to a
`Classical.choice` — can be computed at any morphism one likes.

## Main results

* `Stacks.Cotangent.evalConeHomotopy`: the two evaluations at `U` attached to two morphisms are
  chain homotopic.
* `Stacks.Cotangent.comparisonOfHom_eq`: hence they give the same map in `D(B)`.
* `Stacks.Cotangent.comparison_eq_comparisonOfHom`: the tagged map `Stacks.Cotangent.comparison`
  is `Stacks.Cotangent.comparisonOfHom` at *any* morphism.

## Implementation notes

The homotopy is Mathlib's `Algebra.Extension.Hom.sub`: for two morphisms `s, t : P ⟶ P₀` of
extensions it is a map `Ω_{P/A} ⊗_P B ⟶ 𝒥₀/𝒥₀²`, and the two identities
`Algebra.Extension.Cotangent.map_sub_map` and `Algebra.Extension.CotangentSpace.map_sub_map` say
exactly that it is a chain homotopy between the two induced maps of two-term complexes.
Transported into the mapping cone by `CochainComplex.mappingCone.liftHomotopy` — with the
`𝒥/𝒥²` component of the homotopy given by `Algebra.Extension.Hom.sub` in cohomological degree
`0` and the `L_{B/A}` component zero — it becomes a homotopy between the two evaluations
`Stacks.Cotangent.evalCone`.

## References

* [Stacks Project, Tag 08R9](https://stacks.math.columbia.edu/tag/08R9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CochainComplex.HomComplex

universe u v

namespace Stacks.Cotangent

open CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
  (E : Algebra.Extension.{max u v} A ↥B)
  (s t : E.Hom (conormalExtension A B (op ⦋0⦌)))

/-! ### The homotopy identities of `Algebra.Extension.Hom.sub` -/

/-- The difference of the two maps `J/J² ⟶ 𝒥₀/𝒥₀²` is `Algebra.Extension.Hom.sub` precomposed
with the differential of the two-term complex at `U`. -/
theorem evalCotangent_eq_add :
    evalCotangent A B E s =
      ModuleCat.ofHom E.cotangentComplex ≫
          ModuleCat.ofHom (Y := conormalTerm A B (op ⦋0⦌)) (s.sub t) +
        evalCotangent A B E t := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (Algebra.Extension.Cotangent.map_sub_map s t) x
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at h
  show Algebra.Extension.Cotangent.map s x = (s.sub t) (E.cotangentComplex x) +
    Algebra.Extension.Cotangent.map t x
  exact eq_add_of_sub_eq h

/-- The difference of the two maps `Ω_{P/A} ⊗_P B ⟶ Ω_{P₀/A} ⊗_{P₀} B` is
`Algebra.Extension.Hom.sub` followed by the differential `d` of the standard resolution in
degree zero. -/
theorem evalCotangentSpace_eq_add :
    evalCotangentSpace A B E s =
      ModuleCat.ofHom (Y := conormalTerm A B (op ⦋0⦌)) (s.sub t) ≫
          conormalToCotangentApp A B (op ⦋0⦌) +
        evalCotangentSpace A B E t := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (Algebra.Extension.CotangentSpace.map_sub_map s t) x
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply] at h
  show Algebra.Extension.CotangentSpace.map s x =
    (conormalExtension A B (op ⦋0⦌)).cotangentComplex ((s.sub t) x) +
      Algebra.Extension.CotangentSpace.map t x
  exact eq_add_of_sub_eq h

/-! ### The homotopy -/

/-- The nonzero component of the chain homotopy, in cohomological degree `0`: the map
`Ω_{P/A} ⊗_P B ⟶ 𝒥₀/𝒥₀²` attached by `Algebra.Extension.Hom.sub` to two morphisms of `U` into
the degree-zero term of the standard resolution. -/
def evalHomotopyZero :
    (Algebra.Extension.naiveComplex E).X 0 ⟶ (conormalComplex A B).X 0 :=
  (Algebra.Extension.naiveComplexXZeroIso E).hom ≫
    ModuleCat.ofHom (Y := conormalTerm A B (op ⦋0⦌)) (s.sub t) ≫
    (conormalComplexXZeroIso A B).inv

/-- The chain homotopy, as a cochain of degree `0` from the two-term complex at `U` to the
conormal complex: `Stacks.Cotangent.evalHomotopyZero` in degree `0` and zero elsewhere. -/
def evalHomotopyCochain :
    Cochain (Algebra.Extension.naiveComplex E) (conormalComplex A B) 0 :=
  Cochain.mk fun p q hpq =>
    if h : p = 0 then
      eqToHom (by rw [h]) ≫ evalHomotopyZero A B E s t ≫
        eqToHom (by obtain rfl : q = 0 := by lia
                    rfl)
    else 0

/-- In degree `0`, the component of `Stacks.Cotangent.evalHomotopyCochain` is
`Stacks.Cotangent.evalHomotopyZero`. -/
theorem evalHomotopyCochain_v_zero :
    (evalHomotopyCochain A B E s t).v 0 0 (add_zero 0) = evalHomotopyZero A B E s t := by
  rw [evalHomotopyCochain, Cochain.mk_v, dif_pos rfl, eqToHom_refl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- In every degree `p ≠ 0`, the component of `Stacks.Cotangent.evalHomotopyCochain` is zero. -/
theorem evalHomotopyCochain_v_of_ne (p q : ℤ) (hpq : p + 0 = q) (hp : p ≠ 0) :
    (evalHomotopyCochain A B E s t).v p q hpq = 0 := by
  rw [evalHomotopyCochain, Cochain.mk_v, dif_neg hp]

/-- The first of the two conditions of `CochainComplex.mappingCone.liftHomotopy`: the `𝒥/𝒥²`
components of the two evaluations differ by `δ` of the homotopy. -/
theorem evalConeHomotopy_fst :
    (Cochain.ofHom (evalCone A B E s)).comp
        (CochainComplex.mappingCone.fst (conormalToCotangentComplex A B)).1 (zero_add 1) =
      -δ 0 1 (evalHomotopyCochain A B E s t) +
        (Cochain.ofHom (evalCone A B E t)).comp
          (CochainComplex.mappingCone.fst (conormalToCotangentComplex A B)).1 (zero_add 1) := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : p = -1
  · obtain rfl := hp
    obtain rfl : q = 0 := by lia
    rw [Cochain.add_v, Cochain.neg_v,
      Cochain.comp_v _ _ (zero_add 1) (-1) (-1) 0 (add_zero (-1)) (by lia),
      Cochain.comp_v _ _ (zero_add 1) (-1) (-1) 0 (add_zero (-1)) (by lia),
      Cochain.ofHom_v, Cochain.ofHom_v,
      δ_v 0 1 (zero_add 1) _ (-1) 0 (by lia) (-1) 0 (by lia) (by lia),
      evalHomotopyCochain_v_of_ne A B E s t (-1) (-1) (by lia) (by decide),
      evalHomotopyCochain_v_zero, evalCone_f, evalCone_f,
      evalConeComponent_negOne, evalConeComponent_negOne, evalConeNegOne, evalConeNegOne,
      evalHomotopyZero, Algebra.Extension.naiveComplex_d, evalCotangent_eq_add A B E s t]
    simp only [Limits.zero_comp, zero_add, Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg,
      Category.assoc, Iso.inv_hom_id_assoc,
      CochainComplex.mappingCone.inl_v_fst_v, Category.comp_id,
      Preadditive.add_comp, Preadditive.comp_add]
  · by_cases hp0 : p = 0
    · obtain rfl := hp0
      obtain rfl : q = 1 := by lia
      rw [Cochain.add_v, Cochain.neg_v,
        Cochain.comp_v _ _ (zero_add 1) 0 0 1 (add_zero 0) (by lia),
        Cochain.comp_v _ _ (zero_add 1) 0 0 1 (add_zero 0) (by lia),
        Cochain.ofHom_v, Cochain.ofHom_v,
        δ_v 0 1 (zero_add 1) _ 0 1 (by lia) 0 1 (by lia) (by lia),
        evalHomotopyCochain_v_zero,
        evalHomotopyCochain_v_of_ne A B E s t 1 1 (by lia) (by decide),
        evalCone_f, evalCone_f, evalConeComponent_zero, evalConeComponent_zero,
        evalConeZero, evalConeZero]
      simp only [Category.assoc, CochainComplex.mappingCone.inr_f_fst_v, Limits.comp_zero,
        conormalComplex_d_zero_one, smul_zero, add_zero, neg_zero]
    · rw [Cochain.add_v, Cochain.neg_v,
        Cochain.comp_v _ _ (zero_add 1) p p q (add_zero p) (by lia),
        Cochain.comp_v _ _ (zero_add 1) p p q (add_zero p) (by lia),
        Cochain.ofHom_v, Cochain.ofHom_v,
        δ_v 0 1 (zero_add 1) _ p q hpq p q (by lia) (by lia),
        evalCone_f, evalCone_f,
        evalConeComponent_eq_zero A B E s p hp hp0, evalConeComponent_eq_zero A B E t p hp hp0,
        evalHomotopyCochain_v_of_ne A B E s t p p (add_zero p) hp0]
      have hz : (Algebra.Extension.naiveComplex E).d p q = 0 :=
        (Algebra.Extension.isZero_naiveComplex_X E p hp hp0).eq_of_src _ _
      rw [hz]
      simp

/-- The second of the two conditions of `CochainComplex.mappingCone.liftHomotopy`: the `L_{B/A}`
components of the two evaluations differ by the homotopy composed with `d`. -/
theorem evalConeHomotopy_snd :
    (Cochain.ofHom (evalCone A B E s)).comp
        (CochainComplex.mappingCone.snd (conormalToCotangentComplex A B)) (zero_add 0) =
      δ (-1) 0 (0 : Cochain (Algebra.Extension.naiveComplex E) (cotangentComplex A B) (-1)) +
        (evalHomotopyCochain A B E s t).comp
          (Cochain.ofHom (conormalToCotangentComplex A B)) (zero_add 0) +
        (Cochain.ofHom (evalCone A B E t)).comp
          (CochainComplex.mappingCone.snd (conormalToCotangentComplex A B)) (zero_add 0) := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : p = 0
  · obtain rfl := hp
    obtain rfl : q = 0 := by lia
    rw [Cochain.add_v, Cochain.add_v,
      Cochain.comp_v _ _ (zero_add 0) 0 0 0 (add_zero 0) (add_zero 0),
      Cochain.comp_v _ _ (zero_add 0) 0 0 0 (add_zero 0) (add_zero 0),
      Cochain.comp_v _ _ (zero_add 0) 0 0 0 (add_zero 0) (add_zero 0),
      Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v,
      δ_zero, Cochain.zero_v, zero_add, evalCone_f, evalCone_f,
      evalConeComponent_zero, evalConeComponent_zero, evalConeZero, evalConeZero,
      evalHomotopyCochain_v_zero, evalHomotopyZero, conormalToCotangentComplex_f_zero,
      evalCotangentSpace_eq_add A B E s t]
    simp only [Category.assoc, CochainComplex.mappingCone.inr_f_snd_v, Category.comp_id,
      Iso.inv_hom_id_assoc, Preadditive.add_comp, Preadditive.comp_add]
  · by_cases hp1 : p = -1
    · obtain rfl := hp1
      obtain rfl : q = -1 := by lia
      rw [Cochain.add_v, Cochain.add_v,
        Cochain.comp_v _ _ (zero_add 0) (-1) (-1) (-1) (add_zero (-1)) (add_zero (-1)),
        Cochain.comp_v _ _ (zero_add 0) (-1) (-1) (-1) (add_zero (-1)) (add_zero (-1)),
        Cochain.comp_v _ _ (zero_add 0) (-1) (-1) (-1) (add_zero (-1)) (add_zero (-1)),
        Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v,
        δ_zero, Cochain.zero_v, zero_add, evalCone_f, evalCone_f,
        evalConeComponent_negOne, evalConeComponent_negOne, evalConeNegOne, evalConeNegOne,
        evalHomotopyCochain_v_of_ne A B E s t (-1) (-1) (by lia) (by decide)]
      simp only [Category.assoc, CochainComplex.mappingCone.inl_v_snd_v, Limits.comp_zero,
        Limits.zero_comp, add_zero]
    · rw [Cochain.add_v, Cochain.add_v,
        Cochain.comp_v _ _ (zero_add 0) p p q (add_zero p) hpq,
        Cochain.comp_v _ _ (zero_add 0) p p q (add_zero p) hpq,
        Cochain.comp_v _ _ (zero_add 0) p p q (add_zero p) hpq,
        Cochain.ofHom_v, Cochain.ofHom_v,
        δ_zero, Cochain.zero_v, zero_add, evalCone_f, evalCone_f,
        evalConeComponent_eq_zero A B E s p hp1 hp, evalConeComponent_eq_zero A B E t p hp1 hp,
        evalHomotopyCochain_v_of_ne A B E s t p p (add_zero p) hp]
      simp

/-- **The two evaluations at `U` attached to two morphisms into the degree-zero term of the
standard resolution are chain homotopic.** The homotopy is `Algebra.Extension.Hom.sub`. -/
def evalConeHomotopy : Homotopy (evalCone A B E s) (evalCone A B E t) :=
  CochainComplex.mappingCone.liftHomotopy (conormalToCotangentComplex A B)
    (evalCone A B E s) (evalCone A B E t) (evalHomotopyCochain A B E s t) 0
    (evalConeHomotopy_fst A B E s t) (evalConeHomotopy_snd A B E s t)

/-- **The comparison map of Tag 08R9 does not depend on the chosen morphism** of `U` into the
degree-zero term of the standard resolution. -/
theorem comparisonOfHom_eq : comparisonOfHom A B E s = comparisonOfHom A B E t := by
  rw [comparisonOfHom, comparisonOfHom,
    DerivedCategory.Q_map_eq_of_homotopy _ (evalConeHomotopy A B E s t)]

/-- The tagged comparison map `Stacks.Cotangent.comparison` is
`Stacks.Cotangent.comparisonOfHom` at *any* morphism of `U` into the degree-zero term of the
standard resolution, not only at the one `Stacks.Cotangent.toResolutionZero` extracts from a
presentation of `U` by variables. -/
theorem comparison_eq_comparisonOfHom (hP : Algebra.IsPolynomialAlgebra A E.Ring) :
    comparison A B E hP = comparisonOfHom A B E s :=
  comparisonOfHom_eq A B E _ s

end Stacks.Cotangent

end
