module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.MinimalPrimeOrder

/-!
# The order of vanishing along the stalk map of an étale morphism of schemes

Let `f : X ⟶ Y` be an étale morphism of schemes and `x ∈ X`. The stalk map
`𝒪_{Y, f(x)} → 𝒪_{X, x}` is a flat local homomorphism, essentially of finite type and formally
unramified, so the maximal ideal of `𝒪_{Y, f(x)}` generates the maximal ideal of `𝒪_{X, x}`
(Stacks 00UW). By Stacks 02M1 it therefore leaves the order of vanishing `Ring.ord` unchanged.

This is what lets the order of vanishing along a prime divisor of an algebraic space be compared
on two étale charts through a common étale refinement: both legs of the refinement are étale
morphisms of schemes, and the comparison is made at the stalk of the refinement.

## Main results

* `AlgebraicGeometry.map_maximalIdeal_stalkMap_of_etale`: `𝔪_{f(x)} 𝒪_{X, x} = 𝔪_x`.
* `AlgebraicGeometry.ord_stalkMap_of_etale`: `ord_{𝒪_{X, x}}(f^♯ r) = ord_{𝒪_{Y, f(x)}}(r)`.
* `AlgebraicGeometry.stalkMap_mem_nonZeroDivisors_of_flat`: a flat stalk map carries
  nonzerodivisors to nonzerodivisors.

## References

* [Stacks Project, Tag 00UW](https://stacks.math.columbia.edu/tag/00UW)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The stalk map of an étale morphism extends the maximal ideal to the maximal ideal.** The
stalk map is a local homomorphism, essentially of finite type and formally unramified, so this is
Stacks 00UW (`Algebra.FormallyUnramified.map_maximalIdeal`). -/
theorem map_maximalIdeal_stalkMap_of_etale [Etale f] (x : X) :
    (maximalIdeal (Y.presheaf.stalk (f.base x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  exact Algebra.FormallyUnramified.map_maximalIdeal

/-- **The stalk map of an étale morphism leaves the order of vanishing unchanged.** It is flat,
local and extends the maximal ideal to the maximal ideal, so Stacks 02M1 applies with colength
one (`Ring.ord_map_of_flat_of_map_maximalIdeal`). -/
theorem ord_stalkMap_of_etale [Etale f] (x : X) (r : Y.presheaf.stalk (f.base x)) :
    Ring.ord (X.presheaf.stalk x) ((f.stalkMap x).hom r) =
      Ring.ord (Y.presheaf.stalk (f.base x)) r :=
  Ring.ord_map_of_flat_of_map_maximalIdeal (inferInstanceAs (IsLocalHom (f.stalkMap x).hom))
    (Flat.stalkMap f x) (map_maximalIdeal_stalkMap_of_etale f x) r

/-- A flat stalk map carries nonzerodivisors to nonzerodivisors. -/
theorem stalkMap_mem_nonZeroDivisors_of_flat [Flat f] (x : X)
    {r : Y.presheaf.stalk (f.base x)} (hr : r ∈ (Y.presheaf.stalk (f.base x))⁰) :
    (f.stalkMap x).hom r ∈ (X.presheaf.stalk x)⁰ :=
  Ring.map_mem_nonZeroDivisors_of_flatHom (Flat.stalkMap f x) hr

/-! ### Extension of the maximal ideal along composites -/

/-- The property that the stalk map of `f` at `x` extends the maximal ideal to the maximal
ideal, `𝔪_{f(x)} 𝒪_{X, x} = 𝔪_x`. -/
def MapsMaximalIdealOnto (x : X) : Prop :=
  (maximalIdeal (Y.presheaf.stalk (f.base x))).map (f.stalkMap x).hom =
    maximalIdeal (X.presheaf.stalk x)

variable {f} in
/-- The property is invariant under replacing the morphism by an equal one. -/
theorem MapsMaximalIdealOnto.congr {g : X ⟶ Y} (h : f = g) {x : X}
    (hf : MapsMaximalIdealOnto f x) : MapsMaximalIdealOnto g x := by
  subst h
  exact hf

/-- An étale morphism extends maximal ideals to maximal ideals. -/
theorem mapsMaximalIdealOnto_of_etale [Etale f] (x : X) : MapsMaximalIdealOnto f x :=
  map_maximalIdeal_stalkMap_of_etale f x

/-- A morphism surjective on stalks extends maximal ideals to maximal ideals. -/
theorem mapsMaximalIdealOnto_of_surjectiveOnStalks [SurjectiveOnStalks f] (x : X) :
    MapsMaximalIdealOnto f x :=
  IsLocalRing.map_maximalIdeal_of_surjective _ (f.stalkMap_surjective x)

/-- The extension of the maximal ideal along the stalk map of a composite is the iterated one. -/
private theorem map_stalkMap_comp_maximalIdeal {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    (a : A) :
    (maximalIdeal (C.presheaf.stalk (q.base (p.base a)))).map ((p ≫ q).stalkMap a).hom =
      ((maximalIdeal (C.presheaf.stalk (q.base (p.base a)))).map
        (q.stalkMap (p.base a)).hom).map (p.stalkMap a).hom := by
  rw [Ideal.map_map, Scheme.Hom.stalkMap_comp]
  rfl

variable {f} in
/-- The property is stable under composition. -/
theorem MapsMaximalIdealOnto.comp {Z : Scheme.{u}} {g : Y ⟶ Z} {x : X}
    (hf : MapsMaximalIdealOnto f x) (hg : MapsMaximalIdealOnto g (f.base x)) :
    MapsMaximalIdealOnto (f ≫ g) x := by
  unfold MapsMaximalIdealOnto at hf hg ⊢
  refine (map_stalkMap_comp_maximalIdeal f g x).trans ?_
  rw [hg, hf]

/-- **Cancellation of a second leg.** If `h ≫ a` extends the maximal ideal at `q` and `a` does
at `h(q)`, then so does `h`: the maximal ideal of `𝒪_{Q, q}` is generated by the image of that of
`𝒪_{P, h(q)}`, itself generated by the image of the maximal ideal downstairs. -/
theorem MapsMaximalIdealOnto.of_comp_left {Q P U : Scheme.{u}} {h : Q ⟶ P} {a : P ⟶ U} {q : Q}
    (hha : MapsMaximalIdealOnto (h ≫ a) q) (ha : MapsMaximalIdealOnto a (h.base q)) :
    MapsMaximalIdealOnto h q := by
  unfold MapsMaximalIdealOnto at hha ha ⊢
  have := (map_stalkMap_comp_maximalIdeal h a q).symm.trans hha
  rwa [ha] at this

/-- **A flat morphism extending the maximal ideal leaves the order of vanishing unchanged.** -/
theorem ord_stalkMap_of_flat_of_mapsMaximalIdealOnto [Flat f] {x : X}
    (hx : MapsMaximalIdealOnto f x) (r : Y.presheaf.stalk (f.base x)) :
    Ring.ord (X.presheaf.stalk x) ((f.stalkMap x).hom r) =
      Ring.ord (Y.presheaf.stalk (f.base x)) r :=
  Ring.ord_map_of_flat_of_map_maximalIdeal (inferInstanceAs (IsLocalHom (f.stalkMap x).hom))
    (Flat.stalkMap f x) hx r

end AlgebraicGeometry

end
