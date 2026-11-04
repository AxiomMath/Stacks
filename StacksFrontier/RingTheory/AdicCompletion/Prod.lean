module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Adic completion commutes with a binary product

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M`, `N` two `R`-modules.  The completion of
the product splits,

`(M × N)^∧ ≅ M^∧ × N^∧`,

linearly over the completed ring `R^∧`.  Mathlib has this for a family indexed by a `Fintype`
(`AdicCompletion.piEquivOfFintype`, `AdicCompletion.sumEquivOfFintype`) but not for a binary
product, whose two factors may moreover live in different universes.

Nothing about the levels is needed: the two maps are assembled out of
`AdicCompletion.map` applied to the four structure maps of the product, and the two round trips
are the two identities `fst ∘ inl = id`, `fst ∘ inr = 0`, ... and
`inl ∘ fst + inr ∘ snd = id` of the product itself, carried along by the functoriality and the
additivity of `AdicCompletion.map`.

## Main definitions

* `AdicCompletion.prodEquiv` — **the splitting `(M × N)^∧ ≅ M^∧ × N^∧`.**

## Main results

* `AdicCompletion.prodEquiv_apply`, `AdicCompletion.prodEquiv_symm_apply` — the two directions are
  the pair of the completed projections and the sum of the completed inclusions.
* `AdicCompletion.prodEquiv_of` — the splitting is compatible with the canonical maps from the
  uncompleted modules, which together with `R^∧`-linearity pins it down on a dense subgroup.
-/

@[expose] public noncomputable section

universe u v w

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]

/-- The pair of the completed projections, `(M × N)^∧ → M^∧ × N^∧`. -/
public def prodFst : AdicCompletion I (M × N) →ₗ[AdicCompletion I R]
    AdicCompletion I M × AdicCompletion I N :=
  (map I (LinearMap.fst R M N)).prod (map I (LinearMap.snd R M N))

/-- The sum of the completed inclusions, `M^∧ × N^∧ → (M × N)^∧`. -/
public def prodInl : AdicCompletion I M × AdicCompletion I N →ₗ[AdicCompletion I R]
    AdicCompletion I (M × N) :=
  (map I (LinearMap.inl R M N)).comp (LinearMap.fst _ _ _) +
    (map I (LinearMap.inr R M N)).comp (LinearMap.snd _ _ _)

/-- **Adic completion commutes with a binary product.**  The two factors may live in different
universes, which is why this is not an instance of `AdicCompletion.piEquivOfFintype`. -/
public def prodEquiv : AdicCompletion I (M × N) ≃ₗ[AdicCompletion I R]
    AdicCompletion I M × AdicCompletion I N :=
  LinearEquiv.ofLinearMap (prodFst I M N) (prodInl I M N)
    (by
      refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
      · change map I (LinearMap.fst R M N)
            (map I (LinearMap.inl R M N) x.1 + map I (LinearMap.inr R M N) x.2) = x.1
        rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, map_comp, map_comp,
          show (LinearMap.fst R M N).comp (LinearMap.inl R M N) = LinearMap.id from rfl,
          show (LinearMap.fst R M N).comp (LinearMap.inr R M N) = 0 from rfl, map_id, map_zero]
        simp
      · change map I (LinearMap.snd R M N)
            (map I (LinearMap.inl R M N) x.1 + map I (LinearMap.inr R M N) x.2) = x.2
        rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, map_comp, map_comp,
          show (LinearMap.snd R M N).comp (LinearMap.inl R M N) = 0 from rfl,
          show (LinearMap.snd R M N).comp (LinearMap.inr R M N) = LinearMap.id from rfl, map_id,
          map_zero]
        simp)
    (by
      refine LinearMap.ext fun x ↦ ?_
      change map I (LinearMap.inl R M N) (map I (LinearMap.fst R M N) x) +
        map I (LinearMap.inr R M N) (map I (LinearMap.snd R M N) x) = x
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, map_comp, map_comp,
        ← LinearMap.add_apply, ← map_add,
        show (LinearMap.inl R M N).comp (LinearMap.fst R M N) +
          (LinearMap.inr R M N).comp (LinearMap.snd R M N) = LinearMap.id from
          LinearMap.ext fun y ↦ Prod.ext (add_zero y.1) (zero_add y.2),
        map_id]
      rfl)

/-- The splitting `prodEquiv` applies `AdicCompletion.map` of the two projections. -/
@[simp] public theorem prodEquiv_apply (x : AdicCompletion I (M × N)) :
    prodEquiv I M N x =
      (map I (LinearMap.fst R M N) x, map I (LinearMap.snd R M N) x) := rfl

/-- The inverse of `prodEquiv` is the sum of `AdicCompletion.map` of the two inclusions. -/
@[simp] public theorem prodEquiv_symm_apply
    (x : AdicCompletion I M × AdicCompletion I N) :
    (prodEquiv I M N).symm x =
      map I (LinearMap.inl R M N) x.1 + map I (LinearMap.inr R M N) x.2 := rfl

/-- The splitting is compatible with the canonical maps from the uncompleted modules. -/
@[simp] public theorem prodEquiv_of (x : M × N) :
    prodEquiv I M N (of I (M × N) x) = (of I M x.1, of I N x.2) :=
  Prod.ext (map_of I _ x) (map_of I _ x)

end AdicCompletion

end
