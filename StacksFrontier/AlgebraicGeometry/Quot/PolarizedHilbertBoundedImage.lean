module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertBoundedNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.InfiniteFibreContractedPiece

/-!
# Stacks 0E96 without the algebraicity of `𝒫olarized`

**Stacks 0E96.** Let `n ≥ 1`, let `P` be a numerical polynomial and let `T ⊆ |𝒫olarized|` be a
set of points each of which is represented, over some field `k`, by a polarized proper scheme
`(X, ℒ)` such that (1) the Hilbert polynomial of `ℒ` on `X` is `P`, and (2) there is a closed
immersion `i : X → ℙⁿ_k` with `i^*𝒪(1) ≅ ℒ`. Then `T` is a Noetherian topological space.

The source's proof covers `T` by the image of `|H|` for the Hilbert space
`H = Hilb^{P, 𝒪(1)}_{ℙⁿ_ℤ/ℤ}` and then argues: `|𝒫olarized|` is locally Noetherian
(Stacks 0DQI, which needs `𝒫olarized` to be an *algebraic* stack, Quot Theorem 0D4X), the image
of `|H|` is quasi-compact, and a subset of a quasi-compact subset of a locally Noetherian space
is Noetherian (Stacks 0053 and 0052).

**The algebraicity of `𝒫olarized` is not needed for this.** `H` is proper over `Spec(ℤ)`
(Stacks 0DPH), so `|H|` is not merely quasi-compact but a *Noetherian* topological space; the
continuous image of a Noetherian space is Noetherian (`TopologicalSpace.NoetherianSpace.range`,
Stacks 0052 for a surjection) and so is any subset of it
(`TopologicalSpace.NoetherianSpace.of_subset`, Stacks 0052). Nothing about the ambient topology
of `|𝒫olarized|` enters, and `AlgebraicGeometry.Stack.pointTopology` is defined for an arbitrary
category fibred in groupoids. So no hypothesis standing for Quot Theorem 0D4X is taken below, and
quasi-compactness of `|H|` is strengthened to Noetherianity — which is what Stacks 0DPH gives in
any case.

## Main results

* `AlgebraicGeometry.subset_range_spacePointMap_of_isHilbertPolarizedPoint`: conditions (1) and
  (2) put every point of `T` in the image of `|H|`, which is the second half of the source's
  proof.
* `AlgebraicGeometry.noetherianSpace_of_isHilbertPolarizedPoint_of_noetherianSpace_points`:
  **Stacks 0E96 with no algebraicity hypothesis**, from a chart of `𝒫olarized` by an algebraic
  space with Noetherian space of points.

## Implementation notes

No tag attribute is placed: `Φ` and `hΦ` still stand for results the Stacks project
proves (Stacks 0D3W with Stacks 0E94), so a registration here would be conditional. Both `H` and
`Φ` are supplied in
`StacksFrontier/AlgebraicGeometry/Quot/PolarizedHilbertBoundedUniversal.lean`, which reduces the
whole statement to the universal family of `H`.

## References

* [Stacks Project, Tag 0E96](https://stacks.math.columbia.edu/tag/0E96)
* [Stacks Project, Tag 0052](https://stacks.math.columbia.edu/tag/0052)
* [Stacks Project, Tag 0DPH](https://stacks.math.columbia.edu/tag/0DPH)
* [Stacks Project, Tag 0D3W](https://stacks.math.columbia.edu/tag/0D3W)
* [Stacks Project, Tag 0E94](https://stacks.math.columbia.edu/tag/0E94)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- **Conditions (1) and (2) of Stacks 0E96 put `T` in the image of `|H|`.** Let `Φ` be a
1-morphism from the category of elements of a presheaf `H` to `𝒫olarized` with the moduli
interpretation `hΦ` over fields: a closed subscheme `Z ⊆ ℙⁿ_k`, flat and of finite presentation
over `k`, whose `𝒪(1)|_Z` has Hilbert polynomial `P`, is a `k`-point of `H` which `Φ` carries to
the polarized family `(Z, 𝒪(1)|_Z)` up to a morphism. Then every point of `T` is in the image of
the canonical map `|H| → |𝒫olarized|`.

This is the second half of the source's proof: conditions (1) and (2) make `(X, ℒ)` the target of
a morphism from `(X, i^*𝒪(1))` (`AlgebraicGeometry.hilbertPolarizedFamilyHom`), whose Hilbert
polynomial is that of `ℒ`, so `hΦ` applies and the composite is a common refinement. -/
theorem subset_range_spacePointMap_of_isHilbertPolarizedPoint
    (hT : IsTerminal (B.obj hS)) (n : ℕ) (P : Polynomial ℚ)
    (H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (Φ : (Stack.fibredCategory B S hS H).val ⥤ᵇ (polarizedStackUnconditional B hS hT).val)
    (hΦ : ∀ (U : B.Schemes) (k : Type u) [Field k] (e : B.inclusion.obj U ≅ Spec (.of k))
      {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n (B.inclusion.obj U)) [IsClosedImmersion i]
      (hfl : Flat (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U)))
      (hfp : FinitePresentation
        (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U))),
      (∀ d : ℤ, (polarizedHilbertFunction (hilbertPolarizedFamily n U i hfl hfp) k e d : ℚ) =
        P.eval (d : ℚ)) →
      ∃ q : Space.FieldValuedPoint B S hS H,
        Nonempty (Φ.obj (Stack.spaceFieldValuedPoint B S hS H q).obj ⟶
          hilbertPolarizedFamily n U i hfl hfp))
    (T : Set (Stack.points B S hS (polarizedStackUnconditional B hS hT).val
      (polarizedStackUnconditional B hS hT).property))
    (hTP : ∀ ξ ∈ T, ∃ p, Stack.pointClass B S hS _ _ p = ξ ∧
      IsHilbertPolarizedPoint B hS hT n P p) :
    T ⊆ Set.range
      (Stack.spacePointMap B S hS H (polarizedStackUnconditional B hS hT) Φ) := by
  intro ξ hξ
  obtain ⟨p, rfl, e, hP, i, hi, hcomm, ⟨φ⟩⟩ := hTP ξ hξ
  let x : PolarizedFamily B := p.obj
  let y := hilbertPolarizedFamily n x.base i (hcomm ▸ x.flat) (hcomm ▸ x.finitePresentation)
  have hPy (d : ℤ) : (polarizedHilbertFunction y p.carrier e d : ℚ) = P.eval (d : ℚ) := by
    rw [← hP d]
    congr 1
    exact eulerCharacteristic_tensorPowerModules_congr p.carrier (by rw [← hcomm]; rfl) _ _
      _ _ φ d _ _
  obtain ⟨q, ⟨a⟩⟩ := hΦ x.base p.carrier e i _ _ hPy
  refine ⟨q.class B S hS H, ?_⟩
  rw [Stack.spacePointMap_class]
  exact (Stack.class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2
    ⟨_, ⟨𝟙 _⟩, ⟨a ≫ hilbertPolarizedFamilyHom n x i hcomm φ⟩⟩

/-- **Stacks 0E96, with no algebraicity hypothesis on `𝒫olarized`.** Let `n ∈ ℕ`, let `P ∈ ℚ[t]`
and let `T ⊆ |𝒫olarized|` be a set of points each represented over a field by a polarized proper
scheme `(X, ℒ)` satisfying conditions (1) and (2) of Stacks 0E96
(`AlgebraicGeometry.IsHilbertPolarizedOver`). Then `T` is a Noetherian topological space.

The inputs are the Hilbert space `H = Hilb^{P, 𝒪(1)}_{ℙⁿ_ℤ/ℤ}` of the source's proof — an
algebraic space whose space of points is a *Noetherian* topological space, which is what its
properness over `Spec(ℤ)` (Stacks 0DPH) gives — together with the morphism `H → 𝒫olarized`
classifying its universal family (`Φ`, Stacks 0D3W and 0E94) and that morphism's moduli
interpretation over a field (`hΦ`).

The proof is the source's, with the topological half replaced: the canonical map
`|H| → |𝒫olarized|` is continuous (Stacks 04XL), so its image is a Noetherian subspace
(`TopologicalSpace.NoetherianSpace.range`), and `T` is contained in that image by
`AlgebraicGeometry.subset_range_spacePointMap_of_isHilbertPolarizedPoint`, hence Noetherian by
Stacks 0052. Local Noetherianity of `|𝒫olarized|`, and with it the algebraicity of `𝒫olarized`
(Quot, Theorem 0D4X), is not used. The source's `n ≥ 1` and the numericality of `P` are not
needed. -/
theorem noetherianSpace_of_isHilbertPolarizedPoint_of_noetherianSpace_points
    (hT : IsTerminal (B.obj hS)) (n : ℕ) (P : Polynomial ℚ)
    (H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hH : IsAlgebraicSpace B S hS H)
    (hnoeth : letI := Space.pointTopology B S hS H
      NoetherianSpace (Space.points B S hS H))
    (Φ : (Stack.fibredCategory B S hS H).val ⥤ᵇ (polarizedStackUnconditional B hS hT).val)
    (hΦ : ∀ (U : B.Schemes) (k : Type u) [Field k] (e : B.inclusion.obj U ≅ Spec (.of k))
      {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n (B.inclusion.obj U)) [IsClosedImmersion i]
      (hfl : Flat (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U)))
      (hfp : FinitePresentation
        (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U))),
      (∀ d : ℤ, (polarizedHilbertFunction (hilbertPolarizedFamily n U i hfl hfp) k e d : ℚ) =
        P.eval (d : ℚ)) →
      ∃ q : Space.FieldValuedPoint B S hS H,
        Nonempty (Φ.obj (Stack.spaceFieldValuedPoint B S hS H q).obj ⟶
          hilbertPolarizedFamily n U i hfl hfp))
    (T : Set (Stack.points B S hS (polarizedStackUnconditional B hS hT).val
      (polarizedStackUnconditional B hS hT).property))
    (hTP : ∀ ξ ∈ T, ∃ p, Stack.pointClass B S hS _ _ p = ξ ∧
      IsHilbertPolarizedPoint B hS hT n P p) :
    letI := Stack.pointTopology B S hS (polarizedStackUnconditional B hS hT)
    NoetherianSpace T := by
  let := Stack.pointTopology B S hS (polarizedStackUnconditional B hS hT)
  let := Space.pointTopology B S hS H
  let := hnoeth
  let : NoetherianSpace
      (Set.range (Stack.spacePointMap B S hS H (polarizedStackUnconditional B hS hT) Φ)) :=
    NoetherianSpace.range _
      (Stack.continuous_spacePointMap B S hS H hH (polarizedStackUnconditional B hS hT) Φ)
  exact NoetherianSpace.of_subset
    (subset_range_spacePointMap_of_isHilbertPolarizedPoint B hS hT n P H Φ hΦ T hTP)

end AlgebraicGeometry

end
