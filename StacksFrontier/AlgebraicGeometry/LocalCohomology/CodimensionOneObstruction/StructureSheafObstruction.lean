module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointObstruction
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.PushforwardAffine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Non-coherence of the direct image of the structure sheaf at an associated point

Let `X` be a locally Noetherian scheme, `S` an open subscheme, `x` an associated point of `X`
lying in `S`, and `z` a point outside `S` in the closure of `{x}` at which the reduced closure of
`{x}` has dimension at most one. Then the direct image `(S → X)_* 𝒪_S` is not coherent.

## Main results

* `not_isCoherent_pushforward_structureSheaf_of_height_quotient_le_one`: the statement with the
  codimension hypothesis as a height bound in the coordinate ring of an affine chart containing
  `x` and `z`.
* `not_isCoherent_pushforward_structureSheaf_of_isAssociatedPoint`: the statement with the
  codimension hypothesis as the dimension of the local ring of the reduced closure of `{x}`.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

variable {X : Scheme.{u}}

/-- **The direct image of the structure sheaf of `S` is not coherent at an associated point**,
with the codimension hypothesis in its ring-theoretic form on an affine chart `V₀` containing
both `x` and `z`. Here `X` is locally Noetherian, `x` is an associated point of `X` lying in `S`,
`z` is a point outside `S` specializing from `x`, and the image of the prime of `z` in the quotient
of `Γ(X, V₀)` by the prime of `x` has height at most one. -/
@[ega "IV 7.8.3" "(ix), partial"]
theorem not_isCoherent_pushforward_structureSheaf_of_height_quotient_le_one
    [IsLocallyNoetherian X] {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) {x z : X} (hx : x ∈ V₀)
    (hz : z ∈ V₀) (hxz : x ⤳ z)
    (hdim : ((hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.map
        (Ideal.Quotient.mk (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal)).height ≤ 1)
    (hass : Stacks.Divisors.IsAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) x)
    {S : X.Opens} (hxS : x ∈ S) (hzS : z ∉ S) :
    ¬ ((Scheme.Modules.pushforward S.ι).obj (SheafOfModules.unit _)).IsCoherent := by
  intro hcoh
  have hqc : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  let := resAlgebra (inf_le_right : S ⊓ V₀ ≤ V₀)
  let := moduleOfLE (SheafOfModules.unit X.ringCatSheaf) (inf_le_right : S ⊓ V₀ ≤ V₀)
  have hfin : Module.Finite Γ(X, V₀)
      Γ((Scheme.Modules.pushforward S.ι).obj (SheafOfModules.unit _), V₀) :=
    AlgebraicGeometry.moduleFinite_sections _ ⟨V₀, hV₀⟩
  exact not_moduleFinite_sections_of_isAssociatedPoint hV₀
    (SheafOfModules.unit X.ringCatSheaf) hx hz hxz hdim hass
    (inf_le_right : S ⊓ V₀ ≤ V₀) ⟨hxS, hx⟩ (fun h => hzS h.1)
    (Module.Finite.of_surjective (pushforwardSectionsHom S V₀)
      (pushforwardSectionsHom_surjective S V₀))

/-- **The direct image of the structure sheaf of `S` is not coherent at an associated point.**
Let `X` be a locally Noetherian scheme, `S` an open subscheme, `x` an associated point of the
structure sheaf of `X` lying in `S`, let `X'` be the reduced closed subscheme of `X` supported on
the closure of `{x}`, and let `z'` be a point of `X'` whose image lies outside `S` and at which
`dim 𝒪_{X', z'} ≤ 1`. Then `(S → X)_* 𝒪_S` is not coherent. -/
@[ega "IV 5.10.10" "(ii), special case",
  ega "IV 5.11.1" "a) ⇒ c), special case",
  ega "IV 5.11.4" "special case",
  ega "IV 7.8.3" "(ix), partial"]
theorem not_isCoherent_pushforward_structureSheaf_of_isAssociatedPoint [IsLocallyNoetherian X]
    {x : X} (hass : Stacks.Divisors.IsAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) x)
    {S : X.Opens} (hxS : x ∈ S) {I : X.IdealSheafData}
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)))
    (z' : I.subscheme) (hzS : I.subschemeι z' ∉ S)
    (hdim : ringKrullDim (I.subscheme.presheaf.stalk z') ≤ 1) :
    ¬ ((Scheme.Modules.pushforward S.ι).obj (SheafOfModules.unit _)).IsCoherent := by
  have hsupp : (I.support : Set X) = (Closeds.closure ({x} : Set X) : Set X) := by
    rw [hI]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hmem : I.subschemeι z' ∈ (Closeds.closure ({x} : Set X) : Set X) := by
    have h1 : I.subschemeι z' ∈ Set.range I.subschemeι := ⟨z', rfl⟩
    rw [I.range_subschemeι] at h1
    exact hsupp ▸ h1
  have hxz : x ⤳ I.subschemeι z' := specializes_iff_mem_closure.mpr hmem
  obtain ⟨V₀, hV₀, hz, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (U := (⊤ : X.Opens)) (x := I.subschemeι z') trivial
  have hx : x ∈ V₀ := hxz.mem_open V₀.isOpen hz
  rw [ringKrullDim_stalk_vanishingIdeal_closure hV₀ hx hI z' hz] at hdim
  exact not_isCoherent_pushforward_structureSheaf_of_height_quotient_le_one hV₀ hx hz hxz
    (by exact_mod_cast hdim) hass hxS hzS

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
