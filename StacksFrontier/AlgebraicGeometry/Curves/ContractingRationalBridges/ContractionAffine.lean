module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.PushoutContraction
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections

/-!
# The restriction of a contraction of a rational bridge to the closure of the complement

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, let `C ⊆ X` be a rational bridge (Tag 0E3M), write `X'` for the
scheme-theoretic closure of `X \ C`, and let `c : X ⟶ Y` be a contraction of `C`. The source of
[Stacks, Tag 0E3M] uses throughout that the restriction `a = c|_{X'}` is affine. This file proves
it, for an arbitrary contraction.

## Main results

* `AlgebraicGeometry.isIntegralHom_of_isPushout` — the integrality assertion of
  [Stacks, Tag 0E25] for an arbitrary pushout square of a closed immersion along an integral
  morphism.
* `Stacks.Curves.fiber_preimage_subset_affine_bridge` — the affine-neighbourhood condition of
  [Stacks, Tag 0ECI] for the bridge square.
* `Stacks.Curves.isIntegralHom_complementaryCurveι_comp_contraction` — the restriction of a
  contraction to the closure of the complement is integral, hence affine.
* `Stacks.Curves.isAffineHom_intersection_subschemeι_comp_contraction` — so is its restriction to
  the intersection.

## Implementation notes

`AlgebraicGeometry.pushoutInl_isIntegralHom` records integrality for the pushout *constructed* in
`StacksFrontier/AlgebraicGeometry/Pushout/Gluing.lean`; `AlgebraicGeometry.isIntegralHom_of_isPushout`
transports it to an arbitrary pushout square on the same pair of morphisms, by the comparison
isomorphism `CategoryTheory.IsPushout.isoIsPushout`, exactly as
`AlgebraicGeometry.structureSheaf_isPullback_of_isPushout` transports the structure-sheaf
assertion. The affine-neighbourhood condition of the situation is not a property of the two
morphisms alone and is carried as a hypothesis in both.

For the bridge that hypothesis is available: `Spec k'` has a single point, so what is needed is
one affine open of `X'` containing every point of `C ∩ X'`, which is
`Stacks.Curves.exists_isAffineOpen_containing_intersection_bridge`.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The integrality assertion of [Stacks, Tag 0E25] for an arbitrary pushout square.** The
canonical map from `X` into any pushout of a closed immersion `i : Z ⟶ X` along an integral
morphism `j : Z ⟶ Y` is integral, provided the fibres of `j` map into affine opens of `X`. -/
theorem isIntegralHom_of_isPushout {X Y Z P : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}
    {a : X ⟶ P} {b : Y ⟶ P} [IsClosedImmersion i] [IsIntegralHom j] (h : IsPushout i j a b)
    (hAffine : ∀ y : Y, ∃ V : X.Opens, IsAffineOpen V ∧ ∀ z : Z, j z = y → i z ∈ V) :
    IsIntegralHom a := by
  let s : PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
    { S := P, X := X, Y := Y, Z := Z
      pX := a, pY := b, pZ := i ≫ a
      i := i, j := j
      i_over := rfl, j_over := h.w.symm
      fiber_preimage_subset_affine := hAffine }
  have ha : pushoutInl s ≫
      ((pushoutAlongClosedImmersionAndIntegral s).isPushout.isoIsPushout X Y h).hom = a :=
    IsPushout.inl_isoIsPushout_hom X Y (pushoutAlongClosedImmersionAndIntegral s).isPushout h
  rw [← ha]
  infer_instance

end AlgebraicGeometry

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **The affine-neighbourhood condition of [Stacks, Tag 0ECI] for the bridge square.** The
spectrum of the global functions on the bridge has a single point, so a single affine open of
the closure of the complement containing all of `C ∩ X'` does it, and that is
`Stacks.Curves.exists_isAffineOpen_containing_intersection_bridge`. -/
theorem fiber_preimage_subset_affine_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    ∀ y : Spec Γ(C.subscheme, ⊤), ∃ V : (complementaryCurve C).Opens, IsAffineOpen V ∧
      ∀ z : intersectionWithComplementaryCurve C,
        (Scheme.IdealSheafData.inclusion (I := C)
            (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫
          C.subscheme.toSpecΓ).base z = y →
        (Scheme.IdealSheafData.inclusion (I := complementaryCurveIdeal C)
          (J := intersectionWithComplementaryCurveIdeal C) le_sup_right).base z ∈ V := by
  obtain ⟨U, hUaff, hUmem⟩ := exists_isAffineOpen_containing_intersection_bridge hdim hnodal hC
  exact fun _ => ⟨U, hUaff, fun z _ => hUmem z⟩

/-- The leg of the bridge square into the spectrum of the global functions on the bridge is
integral: the intersection is finite over that spectrum
(`Stacks.Curves.isFinite_intersection_toSpec_bridgeSections`). -/
theorem isIntegralHom_intersection_toSpec_bridgeSections
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    IsIntegralHom (Scheme.IdealSheafData.inclusion (I := C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subscheme.toSpecΓ) :=
  have := isFinite_intersection_toSpec_bridgeSections hdim hnodal hC
  inferInstance

/-- **The restriction of a contraction of a rational bridge to the closure of the complement is
integral.** The contraction exhibits its target as a pushout of that closure along the
collapse of the bridge, and the canonical map from `X'` into such a pushout is integral
(`AlgebraicGeometry.isIntegralHom_of_isPushout`). -/
theorem isIntegralHom_complementaryCurveι_comp_contraction
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    IsIntegralHom (complementaryCurveι C ≫ c) := by
  obtain ⟨-, a, b, hpo, hac, -⟩ := hc
  have := isIntegralHom_intersection_toSpec_bridgeSections hdim hnodal hC
  rw [hac]
  exact isIntegralHom_of_isPushout hpo (fiber_preimage_subset_affine_bridge hdim hnodal hC)

/-- The restriction of a contraction of a rational bridge to the closure of the complement is
affine, an integral morphism being affine. -/
theorem isAffineHom_complementaryCurveι_comp_contraction
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    IsAffineHom (complementaryCurveι C ≫ c) :=
  have := isIntegralHom_complementaryCurveι_comp_contraction hdim hnodal hc
  inferInstance

/-- The restriction of a contraction of a rational bridge to the intersection of the bridge with
the closure of its complement is affine: it factors through the closure by a closed immersion. -/
theorem isAffineHom_intersection_subschemeι_comp_contraction
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    IsAffineHom ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ c) := by
  have := isAffineHom_complementaryCurveι_comp_contraction hdim hnodal hc
  rw [← Scheme.IdealSheafData.inclusion_subschemeι
    (le_sup_right : complementaryCurveIdeal C ≤ intersectionWithComplementaryCurveIdeal C),
    Category.assoc]
  infer_instance

end Stacks.Curves

end
