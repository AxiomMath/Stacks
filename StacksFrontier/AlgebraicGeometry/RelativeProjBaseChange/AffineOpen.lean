module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal

/-!
# `Proj` commutes with base change along a morphism of affine opens of schemes

Let `g : S' ⟶ S` be a morphism of schemes, `U` an affine open of `S`, `V` an affine open of
`S'` carried into `U` by `g`, and `𝒜` a graded `Γ(S, U)`-algebra. Then `Proj (Γ(S', V) ⊗ 𝒜)` is
the fibre product of `Proj 𝒜` with `V` over `U`, the bottom edge of the square being the
morphism `V ⟶ U` induced by `g`. This is the base change of `Proj` along affine spectra
(Tag 01N2), transported along the identifications of `U` and `V` with the spectra of their
rings of sections.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBaseChange.appLEAlgebra`: the `Γ(S, U)`-algebra structure
  on `Γ(S', V)` given by `g` on sections.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChange.Spec_map_algebraMap_isoSpec_inv`: the square
  identifying `Spec Γ(S', V) ⟶ Spec Γ(S, U)` with the induced morphism `V ⟶ U` of affine opens
  commutes.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChange.isPullback_map_resLE`: the base-change
  square over the affine opens is cartesian.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChange.isPullback_map_resLE_appLEAlgebra`: the same
  for the algebra structure `appLEAlgebra`.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChange

universe u

section Transport

variable {S S' : Scheme.{u}} {U : S.Opens} {V : S'.Opens} (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) (g : S' ⟶ S) (hVU : V ≤ g ⁻¹ᵁ U) [Algebra Γ(S, U) Γ(S', V)]
  (halg : algebraMap Γ(S, U) Γ(S', V) = (g.appLE U V hVU).hom)

include halg in
/-- **The affine spectra of the sections and the affine opens themselves form a commuting
square.** `Spec` of the structure map `Γ(S, U) ⟶ Γ(S', V)` followed by the identification of
`Spec Γ(S, U)` with `U` is the identification of `Spec Γ(S', V)` with `V` followed by the
morphism `V ⟶ U` induced by `g`. -/
public theorem Spec_map_algebraMap_isoSpec_inv :
    Spec.map (ofHom (algebraMap Γ(S, U) Γ(S', V))) ≫ hU.isoSpec.inv =
      hV.isoSpec.inv ≫ g.resLE U V hVU := by
  have happ : ofHom (algebraMap Γ(S, U) Γ(S', V)) = g.appLE U V hVU := hom_ext halg
  rw [happ, Iso.eq_inv_comp, IsAffineOpen.isoSpec_hom,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, hU.toSpecΓ_isoSpec_inv, Category.comp_id]

variable {B : Type u} [CommRing B] [Algebra Γ(S, U) B] (𝒜 : ℕ → Submodule Γ(S, U) B)
  [GradedAlgebra 𝒜]

include halg in
/-- **`Proj` commutes with base change along a morphism of affine opens of schemes.** For `U` an
affine open of `S`, `V` an affine open of `S'` carried into `U` by `g`, and `𝒜` a graded
`Γ(S, U)`-algebra, the square formed by `Proj (Γ(S', V) ⊗ 𝒜) ⟶ Proj 𝒜`, the two structure
morphisms to `V` and to `U`, and the morphism `V ⟶ U` induced by `g`, is cartesian. -/
public theorem isPullback_map_resLE :
    IsPullback (Stacks.ProjBaseChange.map 𝒜 Γ(S', V))
      (Proj.toSpecZero (Stacks.ProjBaseChange.grading 𝒜 Γ(S', V)) ≫
        Spec.map (ofHom (algebraMap Γ(S', V)
          ↥(Stacks.ProjBaseChange.grading 𝒜 Γ(S', V) 0))) ≫ hV.isoSpec.inv)
      (Proj.toSpecZero 𝒜 ≫ Spec.map (ofHom (algebraMap Γ(S, U) ↥(𝒜 0))) ≫ hU.isoSpec.inv)
      (g.resLE U V hVU) := by
  simpa only [Category.assoc] using
    (Stacks.ProjBaseChange.isPullback_map_Spec 𝒜 Γ(S', V)).paste_vert
      (IsPullback.of_vert_isIso ⟨Spec_map_algebraMap_isoSpec_inv hU hV g hVU halg⟩)

end Transport

/-! ### The canonical algebra structure -/

section Canonical

variable {S S' : Scheme.{u}} {U : S.Opens} {V : S'.Opens} (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) (g : S' ⟶ S) (hVU : V ≤ g ⁻¹ᵁ U)

/-- The `Γ(S, U)`-algebra structure on `Γ(S', V)` given by the morphism `g.appLE U V hVU` on
sections. -/
@[instance_reducible]
public def appLEAlgebra : Algebra Γ(S, U) Γ(S', V) := (g.appLE U V hVU).hom.toAlgebra

variable {B : Type u} [CommRing B] [Algebra Γ(S, U) B] (𝒜 : ℕ → Submodule Γ(S, U) B)
  [GradedAlgebra 𝒜]

/-- **`Proj` commutes with base change along a morphism of affine opens, for the canonical
algebra structure.** The square of `isPullback_map_resLE` is cartesian when `Γ(S', V)` carries
the `Γ(S, U)`-algebra structure `appLEAlgebra g hVU`. -/
public theorem isPullback_map_resLE_appLEAlgebra :
    letI := appLEAlgebra g hVU
    IsPullback (Stacks.ProjBaseChange.map 𝒜 Γ(S', V))
      (Proj.toSpecZero (Stacks.ProjBaseChange.grading 𝒜 Γ(S', V)) ≫
        Spec.map (ofHom (algebraMap Γ(S', V)
          ↥(Stacks.ProjBaseChange.grading 𝒜 Γ(S', V) 0))) ≫ hV.isoSpec.inv)
      (Proj.toSpecZero 𝒜 ≫ Spec.map (ofHom (algebraMap Γ(S, U) ↥(𝒜 0))) ≫ hU.isoSpec.inv)
      (g.resLE U V hVU) := by
  let := appLEAlgebra g hVU
  exact isPullback_map_resLE hU hV g hVU rfl 𝒜

end Canonical

end Stacks.AlgebraicGeometry.RelativeProjBaseChange

end
