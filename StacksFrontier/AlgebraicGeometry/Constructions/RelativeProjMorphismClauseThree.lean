module

public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjMorphismIsoTransport

/-!
# Clause (3) of Tag 01O9: the open of the triple, not only its morphism

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra and `rp` a relative homogeneous
spectrum for `𝒜`. Clause (3) of [Stacks, Tag 01O9] compares a *triple* over a nested pair
`Z ≤ V` of affine opens of the base: the open, the morphism `r_{ℒ, ψ}` on it, and the graded map
`θ`. `Stacks.AlgebraicGeometry.RelativeProjFromSections.resLE_relativeChart_of_iso` settles the
**morphism** component. This file settles the **open** component:

`U(χ ∘ res) = j^{-1}(U(ψ))`,

the open over `Z` on which the sections restricted from `V` generate is exactly the part of
`U(ψ)` lying over `Z`. Only `≤` was recorded before, as
`Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport.coveringOpen_comap_le_preimage_of_iso`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport.coveringOpen_comap_eq_preimage_of_iso`:
  **the open component of clause (3), for a datum whose invertible module is only isomorphic to
  the inverse image.** `U(χ ∘ φ)` is the preimage under `j` of `U(ψ)`.
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.coveringOpen_comap_eq_preimage`: the same
  read at the graded ring map `𝒜(V) → 𝒜(Z)` of a nested pair of opens of the base, which is the
  shape clause (3) is stated at.

## The route

The equality was already available for a datum attached to the *literal* inverse image:
`Stacks.AlgebraicGeometry.ProjChartGradedPullback.coveringOpen_eq`, which is Tag 0H78 — the
nonvanishing open of a pulled-back section is the preimage of the nonvanishing open — applied
degreewise and sup'd. Freeing the module to be any one isomorphic to the inverse image costs
nothing beyond `…ProjChartGradedIsoTransport.coveringOpen_comap_congrModule`, which says the
transport along an isomorphism of invertible modules leaves every nonvanishing open where it was.

Note that no hypothesis on `j` is needed: Tag 0H78 holds for an arbitrary morphism of schemes, so
the equality is not special to the inclusion of an open.

## Why the equality and not the containment

The containment is what `AlgebraicGeometry.Scheme.Hom.resLE` consumes, and so is what the
morphism component of clause (3) was stated with. The equality is what a *covering* argument
needs. To compare the two prescriptions of clause (3) over two affine opens `V₁`, `V₂` of the base
whose intersection is not affine, one covers `V₁ ∩ V₂` by affine opens `Z` and compares both
prescriptions with the one over `Z`; for the pieces so obtained to cover the overlap of the two
opens, each piece must be the *whole* part of `U(ψ)` lying over `Z`, which is this equality.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport

open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections (congrModule)
open Stacks.AlgebraicGeometry.ProjChartGradedPullback (coveringOpen_eq)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) {T T' : Scheme.{u}} (j : T' ⟶ T) {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {M : T'.Modules}
  [Stacks.Ample.IsInvertibleModule T' M] (β : M ≅ (Scheme.Modules.pullback j).obj L)
  (χ : GradedSections ℬ M)

/-- **Stacks Project, Tag 01O9, the open component of clause (3).** Let `ψ` be a Tag 01NK datum
for a graded ring `𝒜` on a scheme `T` with invertible module `L`, let `j : T' ⟶ T` be a morphism
of schemes, let `φ : 𝒜 →+*ᵍ ℬ` be a graded ring map and let `χ` be a Tag 01NK datum for `ℬ` on
`T'` with an invertible module `M` carrying an isomorphism `β : M ≅ j^*L`, under which the values
of `χ ∘ φ` are the values of `ψ` pulled back along `j`. Then

`U(χ ∘ φ) = j^{-1}(U(ψ))`.

That is, the open on which the datum restricted along `φ` generates is exactly the part of `U(ψ)`
lying over `T'`. Composed with the morphism component
`Stacks.AlgebraicGeometry.RelativeProjFromSections.resLE_relativeChart_of_iso`, this is the
agreement of the *pair* (open, morphism) that clause (3) asserts for a nested pair of opens of the
base; `θ` is not covered.

This strengthens `coveringOpen_comap_le_preimage_of_iso`, which records the containment only
because that is the form `AlgebraicGeometry.Scheme.Hom.resLE` consumes. No hypothesis is placed on
`j`: the degreewise input is [Stacks, Tag 0H78], which holds for an arbitrary morphism. -/
theorem coveringOpen_comap_eq_preimage_of_iso
    (hχ : ∀ (n : ℕ) (a : 𝒜 n),
      (Stacks.AmplePullbackPart1.natTensorPowCongr β n).hom.app ⊤ ((comap φ χ).toFun n a)
        = pullSection j L n (ψ.toFun n a)) :
    (comap φ χ).coveringOpen = j ⁻¹ᵁ ψ.coveringOpen :=
  (coveringOpen_comap_congrModule φ j β χ).symm.trans
    (coveringOpen_eq j L ψ (comap φ (congrModule β χ)) hχ)

end Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport

/-! ### The open component of clause (3), over a nested pair of opens of the base -/

namespace Stacks.AlgebraicGeometry.RelativeProjFromSections

open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport (coveringOpen_comap_eq_preimage_of_iso)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection)
open Stacks.AlgebraicGeometry.RelativeProjBridge

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} {Z V : S.Opens} (h : Z ≤ V)
  {T T' : Scheme.{u}} (j : T' ⟶ T) {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections (A.grading V) L) {M : T'.Modules}
  [Stacks.Ample.IsInvertibleModule T' M] (β : M ≅ (Scheme.Modules.pullback j).obj L)
  (χ : GradedSections (A.grading Z) M)

/-- **Stacks Project, Tag 01O9, the open component of clause (3), over a nested pair of opens of
the base.** For opens `Z ≤ V` of `S`, a Tag 01NK datum `ψ` for `𝒜(V)` on `T` and one `χ` for
`𝒜(Z)` on `T'` whose module is isomorphic to `j^*L` compatibly with the values of `ψ`, the open
on which the sections restricted from `V` generate is exactly the part of `U(ψ)` lying over `T'`.

This is
`Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport.coveringOpen_comap_eq_preimage_of_iso` at the
graded ring map `𝒜(V) → 𝒜(Z)`, which is the shape clause (3) is stated at; the morphism component
at the same shape is `resLE_relativeChart_of_iso`. The opens `Z`, `V` are not required to be
affine, that hypothesis being needed only by the charts the morphism component composes with. -/
theorem coveringOpen_comap_eq_preimage
    (hχ : ∀ (n : ℕ) (a : A.grading V n),
      (Stacks.AmplePullbackPart1.natTensorPowCongr β n).hom.app ⊤ ((comap (A.res h) χ).toFun n a)
        = pullSection j L n (ψ.toFun n a)) :
    (comap (A.res h) χ).coveringOpen = j ⁻¹ᵁ ψ.coveringOpen :=
  coveringOpen_comap_eq_preimage_of_iso (A.res h) j ψ β χ hχ

end Stacks.AlgebraicGeometry.RelativeProjFromSections

/-! ### The overlap of two affine opens of the base -/

namespace Stacks.AlgebraicGeometry.RelativeProjFromSections

open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport
  (coveringOpen_comap_eq_preimage_of_iso coveringOpen_comap_le_preimage_of_iso)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap coveringOpen_le)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

section Overlap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (rp : RelativeProjData A)
  {Z V₁ V₂ : S.Opens} (h₁ : Z ≤ V₁) (h₂ : Z ≤ V₂) (hZ : IsAffineOpen Z)
  (hV₁ : IsAffineOpen V₁) (hV₂ : IsAffineOpen V₂)
  {T₁ T₂ T' : Scheme.{u}} (j₁ : T' ⟶ T₁) (j₂ : T' ⟶ T₂)
  {L₁ : T₁.Modules} {L₂ : T₂.Modules}
  [Stacks.Ample.IsInvertibleModule T₁ L₁] [Stacks.Ample.IsInvertibleModule T₂ L₂]
  (ψ₁ : GradedSections (A.grading V₁) L₁) (ψ₂ : GradedSections (A.grading V₂) L₂)
  {M : T'.Modules} [Stacks.Ample.IsInvertibleModule T' M]
  (β₁ : M ≅ (Scheme.Modules.pullback j₁).obj L₁)
  (β₂ : M ≅ (Scheme.Modules.pullback j₂).obj L₂)
  (χ : GradedSections (A.grading Z) M)
  (hχ₁ : ∀ (n : ℕ) (a : A.grading V₁ n),
    (Stacks.AmplePullbackPart1.natTensorPowCongr β₁ n).hom.app ⊤
        ((comap (A.res h₁) χ).toFun n a)
      = pullSection j₁ L₁ n (ψ₁.toFun n a))
  (hχ₂ : ∀ (n : ℕ) (a : A.grading V₂ n),
    (Stacks.AmplePullbackPart1.natTensorPowCongr β₂ n).hom.app ⊤
        ((comap (A.res h₂) χ).toFun n a)
      = pullSection j₂ L₂ n (ψ₂.toFun n a))

include hχ₁ hχ₂

/-- **The common open of the overlap comparison is the part of `U(ψ₁)` and `U(ψ₂)` lying over
`T'`.** The source of `resLE_relativeChart_eq_of_refinement` is `U(χ ∘ res₁) ⊓ U(χ ∘ res₂)`, and
by the open component of clause (3) each factor is the preimage of the corresponding `U(ψ)`; so
the two prescriptions agree on exactly the part of `T'` lying over both, with nothing cut away by
the choice of the refinement `Z`. -/
theorem coveringOpen_comap_inf_eq :
    (comap (A.res h₁) χ).coveringOpen ⊓ (comap (A.res h₂) χ).coveringOpen
      = j₁ ⁻¹ᵁ ψ₁.coveringOpen ⊓ j₂ ⁻¹ᵁ ψ₂.coveringOpen := by
  rw [coveringOpen_comap_eq_preimage_of_iso (A.res h₁) j₁ ψ₁ β₁ χ hχ₁,
    coveringOpen_comap_eq_preimage_of_iso (A.res h₂) j₂ ψ₂ β₂ χ hχ₂]

section Refinement

include hZ

/-- **Stacks Project, Tag 01O9: the clause (3) prescriptions over two affine opens of the base
agree on their overlap.**

Let `V₁`, `V₂` be affine opens of `S` and let `Z` be an affine open contained in both. Let `ψ₁`,
`ψ₂` be Tag 01NK data for `𝒜(V₁)`, `𝒜(V₂)` on schemes `T₁`, `T₂` with invertible modules `L₁`,
`L₂`, and let `χ` be a Tag 01NK datum for `𝒜(Z)` on a scheme `T'` with an invertible module `M`
carrying isomorphisms `β₁ : M ≅ j₁^*L₁` and `β₂ : M ≅ j₂^*L₂` with morphisms `j₁ : T' ⟶ T₁`,
`j₂ : T' ⟶ T₂`, under which the values of `χ` on the images of `𝒜(V₁) → 𝒜(Z)` and
`𝒜(V₂) → 𝒜(Z)` are the values of `ψ₁`, `ψ₂` pulled back. Then the two morphisms
`r_{L₁, ψ₁}` and `r_{L₂, ψ₂}`, read into `Proj_S(𝒜)` through the charts of Tag 01NQ and restricted
to the part of `T'` lying over both, are equal.

This is the agreement of the clause (3) prescriptions on an **overlap**, which is the step the
source performs to glue them into the global `r_{ℒ, ψ}` and the one that
`resLE_relativeChart_of_iso` — a statement about a *nested* pair — does not give by itself. The
overlap `V₁ ∩ V₂` of two affine opens of a scheme need not be affine, so there is no chart over it;
the comparison is routed through a common affine refinement `Z`, against which both prescriptions
are consistent, and the two consistencies are composed. Both restrictions of `r_{L, χ}` to the
common open are the one inclusion `T'` followed by `r_{L, χ}`, because a composite of inclusions of
opens is the inclusion of the smaller in the larger.

Covers the morphism only; nothing about `θ` is asserted. -/
theorem resLE_relativeChart_eq_of_refinement :
    T'.homOfLE (inf_le_left :
          (comap (A.res h₁) χ).coveringOpen ⊓ (comap (A.res h₂) χ).coveringOpen
            ≤ (comap (A.res h₁) χ).coveringOpen)
        ≫ j₁.resLE ψ₁.coveringOpen (comap (A.res h₁) χ).coveringOpen
            (coveringOpen_comap_le_preimage_of_iso (A.res h₁) j₁ ψ₁ β₁ χ hχ₁)
          ≫ relativeChart rp V₁ hV₁ ψ₁
      = T'.homOfLE (inf_le_right :
            (comap (A.res h₁) χ).coveringOpen ⊓ (comap (A.res h₂) χ).coveringOpen
              ≤ (comap (A.res h₂) χ).coveringOpen)
          ≫ j₂.resLE ψ₂.coveringOpen (comap (A.res h₂) χ).coveringOpen
              (coveringOpen_comap_le_preimage_of_iso (A.res h₂) j₂ ψ₂ β₂ χ hχ₂)
            ≫ relativeChart rp V₂ hV₂ ψ₂ := by
  rw [← resLE_relativeChart_of_iso rp h₁ hZ hV₁ j₁ ψ₁ β₁ χ hχ₁,
    ← resLE_relativeChart_of_iso rp h₂ hZ hV₂ j₂ ψ₂ β₂ χ hχ₂,
    ← Category.assoc, ← Category.assoc, T'.homOfLE_homOfLE, T'.homOfLE_homOfLE]

end Refinement

end Overlap

end Stacks.AlgebraicGeometry.RelativeProjFromSections

end
