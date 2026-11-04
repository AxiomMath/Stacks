module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TopDifferentialFiniteType
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TopDifferentialSection
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalClaimsProof

/-!
# The top de Rham differential on `Rⁿ f_*` vanishes in the relative duality situation

In the situation of relative Poincaré duality ([Stacks, Tag 0G8G]) — `S` quasi-compact and
quasi-separated, `f : X ⟶ S` proper and smooth with all fibres nonempty and equidimensional of
dimension `n` — the map `d : Rⁿf_*Ω^{n-1}_{X/S} ⟶ Rⁿf_*Ωⁿ_{X/S}` induced by the de Rham
differential is zero ([Stacks, Tag 0G8J]). The map is a morphism of the underlying abelian
sheaves (the differential is only `f⁻¹𝒪_S`-linear), and `Rⁿf_*` is the higher direct image of
abelian sheaves.

The proof is the source's. The question is local on `S`, and by Noetherian approximation, the
Stein factorization and étale-local sections it reduces to a proper `Y ⟶ Spec B`, smooth of
relative dimension `n`, with `B` of finite type over `ℤ`, `B = Γ(Y, 𝒪_Y)` and a section
(`AlgebraicGeometry.RelativeDualitySituation.higherDirectImage_map_deRham_d_eq_zero_of_section`).
There the diagonal argument applies: `Stacks.WeilDeRham.topDifferentialVanishes_of_diagonalClaim`
with the diagonal claim `Stacks.WeilDeRham.diagonalClaim` and top-degree injectivity
`Stacks.WeilDeRham.topInjective`.

## Main results

* `Stacks.WeilDeRham.topDifferentialVanishes_of_section`: the case of a section over a base of
  finite type over `ℤ` with `Γ(Y, 𝒪_Y) = B`.
* `Stacks.WeilDeRham.higherDirectImage_map_deRham_d_top_eq_zero`: [Stacks, Tag 0G8J].

## References

* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
* [Stacks Project, Tag 0G8G](https://stacks.math.columbia.edu/tag/0G8G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.TopDegreeDifferential

universe u

namespace Stacks.WeilDeRham

/-- **The top de Rham differential vanishes on `Hⁿ` in the case of a section.** Let `B` be of
finite type over `ℤ` and `g : Y ⟶ Spec B` proper and smooth of relative dimension `n` with
`B ⟶ Γ(Y, 𝒪_Y)` bijective and a section `σ`. Then `d : Hⁿ(Y, Ω^{n-1}_{Y/B}) ⟶ Hⁿ(Y, Ωⁿ_{Y/B})`
is zero. -/
theorem topDifferentialVanishes_of_section (n : ℕ) (B : CommRingCat.{u})
    (hB : Algebra.FiniteType ℤ B) (Y : Scheme.{u}) (g : Y ⟶ Spec B) [IsProper g]
    [SmoothOfRelativeDimension n g] [IsIso g.appTop] (σ : Spec B ⟶ Y) (hσ : σ ≫ g = 𝟙 _) :
    TopDifferentialVanishes g n := by
  cases n with
  | zero => exact topDifferentialVanishes_zero g
  | succ e =>
    have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
    have : IsIso (σ ≫ g) := by rw [hσ]; infer_instance
    have : IsClosedImmersion σ := IsClosedImmersion.of_comp σ g
    have : Smooth (σ ≫ g) := by rw [hσ]; infer_instance
    have : FormallyUnramified (σ ≫ g) := by rw [hσ]; infer_instance
    have : LocallyOfFinitePresentation σ := locallyOfFinitePresentation_of_comp σ g
    exact topDifferentialVanishes_of_diagonalClaim (A := B) g e σ hσ
      (diagonalClaim (A := B) g e σ hσ) (topInjective (A := B) g e σ hσ)

/-- **Stacks Project, Tag 0G8J.** In the situation of relative Poincaré duality
([Stacks, Tag 0G8G]) — `S` quasi-compact and quasi-separated, `f : X ⟶ S` proper and smooth, all
fibres nonempty and equidimensional of dimension `n` — the map
`d : Rⁿf_*Ω^{n-1}_{X/S} ⟶ Rⁿf_*Ωⁿ_{X/S}` induced by the de Rham differential is zero. -/
@[stacks 0G8J]
theorem higherDirectImage_map_deRham_d_top_eq_zero (D : RelativeDualitySituation.{u}) :
    (Stacks.Cohomology.AbelianSheaf.higherDirectImage D.f.base D.n).map
      ((SheafOfModules.toSheaf _).map (D.f.deRhamComplex.d (D.n - 1) D.n)) = 0 :=
  D.higherDirectImage_map_deRham_d_eq_zero_of_section fun B hB Y g _ _ _ σ hσ =>
    topDifferentialVanishes_of_section D.n B hB Y g σ hσ

end Stacks.WeilDeRham

end
