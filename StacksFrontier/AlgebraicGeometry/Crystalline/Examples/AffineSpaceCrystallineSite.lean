module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelSite
public import StacksFrontier.RingTheory.DividedPowers.PadicIntegersAtPrime

/-!
# The crystalline site of `𝐀^r_{𝐅_p}` over `Spec(𝐙_p)`

Keep the situation of
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRham`: the base `A = 𝐙_p` with
its divided power ideal `(p)` and its unique divided powers `γ`, and the presentation
`C = 𝐅_p[x_1, …, x_r] = P/J = P/pP` with `P = 𝐙_p[x_1, …, x_r]`.  This module builds the
global crystalline situation of the example of [Stacks, Tag 07LK] — `X = Spec(C)` over
`S = Spec(A, (p), γ)` — and proves that `X` and `S` are affine and that `p` is nilpotent on `X`.

## Main definitions

* `Crystalline.AffineSpaceCrystallineSetup.baseDividedPowerScheme` — `S = Spec(A, (p), γ)`.
* `Crystalline.AffineSpaceCrystallineSetup.residueToCoordinateRing` and `toClosedFibre` — the map
  `A/(p) = 𝐅_p → C` and the structure morphism `X ⟶ S₀`.
* `Crystalline.AffineSpaceCrystallineSetup.situation` — the global crystalline situation `X/S`.

## Main results

* `Crystalline.AffineSpaceCrystallineSetup.prime_eq_zero_coordinateRing` — `p = 0` in `C`.
* `Crystalline.AffineSpaceCrystallineSetup.isNilpotent_prime_sections` — `p` is nilpotent on
  `Γ(X, 𝒪_X)`.

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DividedPowers
open Crystalline.DividedPowerScheme

namespace Crystalline

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

attribute [local instance] DividedPowers.padicIntAlgebraAtPrime

/-- **The crystalline base `S = Spec(A, (p), γ)` of the example**, for `A = 𝐙_p` with its unique
divided powers on `(p)`. -/
abbrev baseDividedPowerScheme : DividedPowerScheme :=
  specBase T.baseIdeal T.baseDividedPowers

/-- The map `A/(p) = 𝐅_p → C` of the presentation: the composite `A → P → P/J` kills `(p)`,
because `J = pP`. -/
def residueToCoordinateRing : T.A ⧸ T.baseIdeal →+* T.C :=
  Ideal.Quotient.lift T.baseIdeal
    ((Ideal.Quotient.mk T.J).comp (algebraMap T.A T.P))
    (by
      have hp : algebraMap T.A T.P (T.p : T.A) ∈ T.J := by
        rw [map_natCast, T.J_eq_span]
        exact Ideal.subset_span (by simp)
      intro a ha
      rw [baseIdeal, Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [RingHom.comp_apply, map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right (algebraMap T.A T.P c) T.J hp)

/-- **The structure morphism `X ⟶ S₀`** of the example, `Spec` of the map `𝐅_p → C` read in the
closed fibre `S₀ = Spec(A/(p))` of `S` through
`Crystalline.DividedPowerScheme.specClosedFiberIso`. -/
def toClosedFibre : T.X ⟶ closedFiber T.baseDividedPowerScheme :=
  Spec.map (CommRingCat.ofHom T.residueToCoordinateRing) ≫
    (specClosedFiberIso (DividedPowerRing.of T.A T.baseIdeal T.baseDividedPowers)).inv

/-- `p = 0` in `C = P/pP`. -/
theorem prime_eq_zero_coordinateRing : (T.p : T.C) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk T.J) T.p, Ideal.Quotient.eq_zero_iff_mem, T.J_eq_span]
  exact Ideal.subset_span (by simp)

/-- `p = 0` in the global functions of `X = Spec(C)`. -/
theorem prime_eq_zero_sections : (T.p : Γ(T.X, ⊤)) = 0 := by
  refine (Scheme.ΓSpecIso (CommRingCat.of T.C)).commRingCatIsoToRingEquiv.injective ?_
  rw [map_natCast, map_zero]
  exact T.prime_eq_zero_coordinateRing

/-- `p` is nilpotent — indeed zero — in every local ring of `X = Spec(C)`. -/
theorem prime_locallyNilpotent (x : T.X) : IsNilpotent (T.p : T.X.presheaf.stalk x) := by
  have hx : x ∈ (⊤ : T.X.Opens) := trivial
  have h := map_natCast (T.X.presheaf.germ ⊤ x hx).hom T.p
  exact ⟨1, by rw [pow_one, ← h, T.prime_eq_zero_sections, map_zero]⟩

/-- **The global crystalline situation `X/S` of the example**, `X = Spec(𝐅_p[x_1, …, x_r])` over
`S = Spec(𝐙_p, (p), γ)`, which indexes the small crystalline site `Cris(X/S)`. -/
def situation : GlobalCrystallineSituation.{0} :=
  specSituation T.baseIdeal T.baseDividedPowers T.p T.X T.toClosedFibre T.prime_locallyNilpotent

/-- The prime of the crystalline situation `X/S` is the prime `p` of the example. -/
@[simp] theorem situation_p : T.situation.p = T.p := rfl

/-- The scheme of the crystalline situation `X/S` is the scheme `X = Spec(C)` of the example. -/
@[simp] theorem situation_X : T.situation.X = T.X := rfl

/-- The scheme `X = Spec(C)` of the example is affine. -/
instance isAffine_situation_X : IsAffine T.situation.X :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of T.C)))

/-- The base `S = Spec(𝐙_p)` of the example is affine. -/
instance isAffine_situation_S : IsAffine T.situation.S.scheme :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of T.A)))

/-- **`p` is nilpotent on `Γ(X, 𝒪_X)`** — indeed zero. -/
theorem isNilpotent_prime_sections : IsNilpotent (T.situation.p : Γ(T.situation.X, ⊤)) :=
  ⟨1, by rw [pow_one]; exact T.prime_eq_zero_sections⟩

end AffineSpaceCrystallineSetup

end Crystalline

end
