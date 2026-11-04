module

public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpensRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens

/-!
# The normalizations relative to `ω_Y^•` on charts

Let `f : X ⟶ Y` be a morphism of schemes of finite type over `S`, and `ω_X^•`, `ω_Y^•` normalized
relative to `ω_S^•`. For opens `V ⊆ X` and `U ⊆ Y` separated over `S` with `f(V) ⊆ U`, the
normalizations give `ω_X^•|_V ≅ (V → Y)^! ω_Y^•` as in the proof of [Stacks, Tag 0AUB]. These
isomorphisms restrict to smaller opens of `X` and do not depend on `U`.

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.chartIso`.

## Main results

* `Stacks.Duality.NormalizedOnOpens.restrictLocalIso_chartIso`,
  `Stacks.Duality.NormalizedOnOpens.chartIso_eq_of_le`.

## References

* [Stacks Project, Tag 0AUB](https://stacks.math.columbia.edu/tag/0AUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v v'

namespace Stacks.Duality.NormalizedOnOpens

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)] {A : UpperShriek 𝒟}
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q} {ωS : 𝒟 S}
  (𝒦X : NormalizedOnOpens A hp ωS) (𝒦Y : NormalizedOnOpens A hq ωS)

/-- The normalization of `ω_X^•|_V` relative to `ω_Y^•` on a chart `V ⊆ f⁻¹U`, with `V` and `U`
separated over `S`: `α_V : ω_X^•|_V ≅ (V → S)^! ω_S^•` followed by the transport of
`β_U : ω_Y^•|_U ≅ (U → S)^! ω_S^•` along `V → U` ([Stacks, Tag 0AUB]). -/
def chartIso {V : X.Opens} (hV : IsShriekable (V.ι ≫ p)) {U : Y.Opens}
    (hU : IsShriekable (U.ι ≫ q)) (hVU : V ≤ f ⁻¹ᵁ U) :
    A.restrictTo hp V 𝒦X.complex ≅
      (A.shriek (V.ι ≫ f) (hp.isShriekable_ι_comp hq hpe hVU hV)).obj 𝒦Y.complex :=
  𝒦X.localIso V hV ≪≫
    A.transport (resLE_comp_structure hpe hVU) (Scheme.Hom.resLE_comp_ι f hVU)
      (hp.isShriekable_resLE hq hpe hVU hV) hU (hq.isShriekable_ι U) hV
      (hp.isShriekable_ι_comp hq hpe hVU hV) (𝒦Y.localIso U hU)

/-- **The chart normalizations restrict**: on `W ⊆ V` the restriction of the normalization on
`V` is the one on `W`. -/
theorem restrictLocalIso_chartIso {W V : X.Opens} (h : W ≤ V) (hV : IsShriekable (V.ι ≫ p))
    (hW : IsShriekable (W.ι ≫ p)) {U : Y.Opens} (hU : IsShriekable (U.ι ≫ q))
    (hVU : V ≤ f ⁻¹ᵁ U) (hWU : W ≤ f ⁻¹ᵁ U) :
    A.restrictLocalIso (hp.of_comp' hq hpe) 𝒦Y.complex 𝒦X.complex h
        (hp.isShriekable_ι_comp hq hpe hVU hV) (chartIso hpe 𝒦X 𝒦Y hV hU hVU) =
      chartIso hpe 𝒦X 𝒦Y hW hU hWU := by
  rw [chartIso, A.restrictLocalIso_trans hp (hp.of_comp' hq hpe), 𝒦X.compat h hV hW,
    A.restrictCompare_transport
      (hrg := show X.homOfLE h ≫ f.resLE U V hVU = f.resLE U W hWU by simp)
      (hg'c := resLE_comp_structure hpe hWU) (hg'b := Scheme.Hom.resLE_comp_ι f hWU)
      (hg' := hp.isShriekable_resLE hq hpe hWU hW)]
  rfl

/-- **The chart normalizations do not depend on the chart of `Y`**: shrinking `U` to `U' ⊇ f(V)`
does not change the normalization on `V`. -/
theorem chartIso_eq_of_le {V : X.Opens} (hV : IsShriekable (V.ι ≫ p)) {U' U : Y.Opens}
    (h : U' ≤ U) (hU : IsShriekable (U.ι ≫ q)) (hU' : IsShriekable (U'.ι ≫ q))
    (hVU' : V ≤ f ⁻¹ᵁ U') (hVU : V ≤ f ⁻¹ᵁ U) :
    chartIso hpe 𝒦X 𝒦Y hV hU' hVU' = chartIso hpe 𝒦X 𝒦Y hV hU hVU := by
  have hβ := 𝒦Y.compat h hU hU'
  rw [A.restrictLocalIso_eq_transport_symm hq] at hβ
  rw [chartIso, chartIso, ← hβ]
  congr 1
  exact (A.restrictCompare_comp
    (hr := show f.resLE U' V hVU' ≫ Y.homOfLE h = f.resLE U V hVU by simp)
    (h₁m := show Y.homOfLE h ≫ U.ι ≫ q = U'.ι ≫ q by rw [← Category.assoc, Y.homOfLE_ι])
    (h₁n := Y.homOfLE_ι h) (h₂m := resLE_comp_structure hpe hVU')
    (h₂n := Scheme.Hom.resLE_comp_ι f hVU') (hm₂ := resLE_comp_structure hpe hVU)
    (hn₂ := Scheme.Hom.resLE_comp_ι f hVU)
    (hp.isShriekable_resLE hq hpe hVU' hV) (hq.isShriekable_homOfLE h)
    (hp.isShriekable_resLE hq hpe hVU hV) hU (hq.isShriekable_ι U) hU' (hq.isShriekable_ι U')
    hV (hp.isShriekable_ι_comp hq hpe hVU hV) (𝒦Y.localIso U hU).symm)

end Stacks.Duality.NormalizedOnOpens
