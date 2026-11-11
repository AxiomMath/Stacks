module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblySolution
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyFibreDimension
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodRingInjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes

/-!
# The ring of formal functions along the strict transform is torsion free over `k[t]`

In the construction of [Stacks, Tag 0D5E], `Z` is the blowup of the cubic surface `Y` at the
chosen point of the central fibre, `C ⊆ Z` the strict transform of the central fibre and
`A = lim Γ(Cₙ, 𝒪)` the ring of formal functions along `C`, a domain. This file shows that `A` is
torsion free over `k[t] = Γ(A¹_k, 𝒪)` via `Spec A ⟶ A¹_k`: the map `k[t] ⟶ A` is injective,
being the composite of `k[t] ⟶ Γ(Z, 𝒪)`, injective since `Z ⟶ A¹_k` is a dominant morphism of
integral schemes (`Stacks.Examples.CurveFamilyNotScheme.isDominant_cubicToLine`), and of
the restriction `Γ(Z, 𝒪) ⟶ A`, injective since `Z` is integral and locally Noetherian and `C`
is nonempty
(`AlgebraicGeometry.Scheme.IdealSheafData.injective_globalToFormalNeighborhood`).

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.injective_appTop_cubicToLine`: `k[t] ⟶ Γ(Z, 𝒪)` is
  injective.
* `Stacks.Examples.CurveFamilyNotScheme.isSMulRegular_cubicFormalRingToLine`: every nonzero
  `r ∈ k[t]` acts on `A` as a nonzerodivisor.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable (k : Type u) [Field k] [IsAlgClosed k] [Uncountable k] (h3 : ringChar k ≠ 3)

/-- **`k[t] ⟶ Γ(Z, 𝒪)` is injective**, `Z ⟶ A¹_k` being a dominant morphism of integral
schemes. -/
theorem injective_appTop_cubicToLine : Function.Injective (cubicToLine k h3).appTop := by
  have hdom := isDominant_cubicToLine k h3
  have hstalk := ((tfae_isDominant_of_isIntegral (cubicToLine k h3)).out 1 6).1 hdom
  set z := genericPoint (cubicBlowup k h3)
  intro r s hrs
  apply germ_injective_of_isIntegral (affineLine k) (U := ⊤) (cubicToLine k h3 z)
    (show cubicToLine k h3 z ∈ (⊤ : (affineLine k).Opens) from trivial)
  apply hstalk z
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
  exact congrArg _ hrs

/-- `C` is nonempty: it has a `k`-point. -/
theorem nonempty_support_strictTransformCentralFibre :
    ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3)).Nonempty := by
  obtain ⟨p, -⟩ := exists_point_conormal_iso k h3
  obtain ⟨x : Spec (.of k)⟩ := (inferInstance : Nonempty (Spec (.of k)))
  rw [← range_subschemeι]
  exact ⟨_, Set.mem_range_self (p x)⟩

/-- **`A` is torsion free over `k[t]`**: every nonzero `r ∈ k[t] = Γ(A¹_k, 𝒪)` acts on
`A = lim Γ(Cₙ, 𝒪)` (through `Spec A ⟶ A¹_k`) as a nonzerodivisor, since `A` is a domain and
`k[t] ⟶ A` is injective. -/
theorem isSMulRegular_cubicFormalRingToLine (r : Γ(affineLine k, ⊤)) (hr : r ≠ 0) :
    IsSMulRegular (cubicFormalRing k h3)
      (((cubicFormalRingToLine k h3).appTop ≫
        (Scheme.ΓSpecIso (.of (cubicFormalRing k h3))).hom) r) := by
  have hinj : Function.Injective (globalToFormalNeighborhood (strictTransformCentralFibre k h3)) :=
    injective_globalToFormalNeighborhood _ (nonempty_support_strictTransformCentralFibre k h3)
  have heq : ((cubicFormalRingToLine k h3).appTop ≫
      (Scheme.ΓSpecIso (.of (cubicFormalRing k h3))).hom) r =
      globalToFormalNeighborhood (strictTransformCentralFibre k h3)
        ((cubicToLine k h3).appTop r) := by
    rw [cubicFormalRingToLine, formalNeighborhoodToSpec, Scheme.ΓSpecIso_naturality]
    simp
  refine (IsRegular.of_ne_zero ?_).left.isSMulRegular
  rw [heq, ← map_zero (globalToFormalNeighborhood (strictTransformCentralFibre k h3)),
    hinj.ne_iff]
  exact fun h => hr (injective_appTop_cubicToLine k h3 (h.trans (map_zero _).symm))

end Stacks.Examples.CurveFamilyNotScheme

end
