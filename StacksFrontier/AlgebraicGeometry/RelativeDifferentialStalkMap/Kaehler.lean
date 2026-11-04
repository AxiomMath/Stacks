module

public import Mathlib.RingTheory.Kaehler.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kähler differentials do not see a surjective change of base ring

For a tower `R → S → B` of commutative rings in which `R → S` is **surjective**, the comparison
map `Ω[B⁄R] → Ω[B⁄S]` of `Mathlib.RingTheory.Kaehler.Basic` is an isomorphism: **the module of
Kähler differentials of `B` depends on the base ring only through its image in `B`.**

## Main results

* `Stacks.RelativeDifferentialStalkMap.kaehlerMap_bijective_of_surjective`: the comparison map
  `KaehlerDifferential.map R S B B` is bijective when `R → S` is surjective.
* `Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective`: that comparison read as a
  linear equivalence `Ω[B⁄R] ≃ₗ[B] Ω[B⁄S]`, with
  `Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective_D` and
  `Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective_symm_D` saying that it
  matches universal differentials on both sides.

## Implementation notes

Surjectivity of `R → S` is only used through `KaehlerDifferential.subsingleton_of_surjective`,
which says `Ω[S⁄R] = 0`.  Mathlib's exact sequence

```
B ⊗[S] Ω[S⁄R] ⟶ Ω[B⁄R] ⟶ Ω[B⁄S] ⟶ 0
```

— `KaehlerDifferential.exact_mapBaseChange_map` together with
`KaehlerDifferential.map_surjective` — then has a vanishing left-hand term, so its middle map is
injective as well as surjective.  Nothing else is needed; in particular neither
`KaehlerDifferential.kerTotal_map` nor `KaehlerDifferential.ker_map` is used, and the kernel is
never computed.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.RelativeDifferentialStalkMap

variable (R : Type u) (S : Type v) (B : Type w) [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- **The comparison map `Ω[B⁄R] → Ω[B⁄S]` is bijective when `R → S` is surjective.**

Surjectivity is `KaehlerDifferential.map_surjective`.  Injectivity holds because the kernel is
the image of `B ⊗[S] Ω[S⁄R]` by `KaehlerDifferential.exact_mapBaseChange_map`, and `Ω[S⁄R]`
vanishes for a surjective `R → S`. -/
@[ega "0 20.5.15", ega "0 22.4.5" "more general"]
public theorem kaehlerMap_bijective_of_surjective
    (h : Function.Surjective (algebraMap R S)) :
    Function.Bijective (KaehlerDifferential.map R S B B) := by
  refine ⟨?_, KaehlerDifferential.map_surjective R S B⟩
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S B
  have hsub : Subsingleton (KaehlerDifferential R S) :=
    KaehlerDifferential.subsingleton_of_surjective R S h
  rw [← LinearMap.ker_eq_bot, hex.linearMap_ker_eq, LinearMap.range_eq_bot]
  refine LinearMap.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => rw [Subsingleton.elim y 0]; simp
  | add a b ha hb => rw [map_add, ha, hb]; simp

/-- **Kähler differentials are invariant under a surjective change of base ring.**  For a tower
`R → S → B` with `R → S` surjective, `Ω[B⁄R] ≃ₗ[B] Ω[B⁄S]`, by the comparison map. -/
@[ega "0 20.5.15",
  ega "0 20.5.5" "special case",
  ega "0 22.4.5" "more general",
  ega "IV 16.5.10" "special case"]
public noncomputable def kaehlerMapEquivOfSurjective
    (h : Function.Surjective (algebraMap R S)) :
    KaehlerDifferential R B ≃ₗ[B] KaehlerDifferential S B :=
  LinearEquiv.ofBijective (KaehlerDifferential.map R S B B)
    (kaehlerMap_bijective_of_surjective R S B h)

/-- The equivalence carries the universal `R`-differential of an element of `B` to its universal
`S`-differential. -/
public theorem kaehlerMapEquivOfSurjective_D (h : Function.Surjective (algebraMap R S)) (b : B) :
    kaehlerMapEquivOfSurjective R S B h (KaehlerDifferential.D R B b) =
      KaehlerDifferential.D S B b := by
  show KaehlerDifferential.map R S B B (KaehlerDifferential.D R B b) = _
  rw [KaehlerDifferential.map_D]
  simp

/-- The inverse equivalence carries the universal `S`-differential of an element of `B` to its
universal `R`-differential. -/
public theorem kaehlerMapEquivOfSurjective_symm_D (h : Function.Surjective (algebraMap R S))
    (b : B) :
    (kaehlerMapEquivOfSurjective R S B h).symm (KaehlerDifferential.D S B b) =
      KaehlerDifferential.D R B b :=
  (LinearEquiv.symm_apply_eq _).2 (kaehlerMapEquivOfSurjective_D R S B h b).symm

end Stacks.RelativeDifferentialStalkMap

end
