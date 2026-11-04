module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectivePushforwardStep
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistSectionsDegreeOne
public import StacksCore.Tactic.StacksAttribute

/-!
# The twisted ideal sheaf of the blowup in projective space, and the sections it lets through

Let `A` be a Noetherian ring, `I ⊆ A` an ideal with a chosen finite generating family
`x₀, …, x_m`, and `i : X ⟶ 𝐏 = Proj A[T₀, …, T_m]` the closed immersion of the blowup
`X = Proj(⨁ₙ Iⁿ)` of `Spec A` in `I` into projective space coming from the polynomial
presentation of the Rees algebra. This file supplies the **twisted ideal-sheaf short exact
sequence** at that immersion and reads off what it gives on global sections:

`Γ(𝐏, 𝒪_𝐏(q)) ⟶ Γ(𝐏, (i_*𝒪_X)(q))` is **surjective** for every large `q`,

and, composed with the comparison `(i_*𝒪_X)(q) ≅ i_*(𝒪_X(q))`, so is

`Γ(𝐏, 𝒪_𝐏(q)) ⟶ Γ(X, 𝒪_X(q))`.

## The argument, and what it is assembled from

Write `φ : 𝒪_𝐏 ⟶ i_*𝒪_X` for the canonical restriction. Three facts about it are used.

* `φ` is an **epimorphism** of `𝒪_𝐏`-modules, since `i` is a closed immersion:
  `Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion`.
  So `0 ⟶ ker φ ⟶ 𝒪_𝐏 ⟶ i_*𝒪_X ⟶ 0` is short exact, `ker φ` being the ideal sheaf of `X` in
  `𝐏`; this is the sequence [Stacks, Tag 0C6K] states for a closed subscheme, here at the
  immersion rather than at an `AlgebraicGeometry.Scheme.IdealSheafData`.
* `ker φ` is **coherent**: both `𝒪_𝐏` and `i_*𝒪_X` are — the first because `𝐏` is locally
  Noetherian, the second by [Stacks, Tag 087T] — and the kernel of a morphism of coherent
  modules is coherent ([Stacks, Tag 01BY] part (3)).
* Therefore `H¹(𝐏, (ker φ)(q))` **vanishes for all large `q`**, by Serre vanishing on projective
  space, [Stacks, Tag 01YS] clause (4).

The twisting of the sequence and the passage to sections is then the already-general
`Stacks.ProjectiveSpace.Cohomology.surjective_twistedSectionsAddHom_of_isZero_firstCohomology`:
`𝒪_𝐏(q)` is invertible, so twisting keeps the sequence short exact, and the long exact sequence
of sections has nothing left to obstruct a lift. Nothing of that machinery is rebuilt here; what
this file adds is the three facts above at this particular immersion, which is what was missing.

## Why this is the surjectivity half of Serre's section theorem on the blowup

[Stacks, Tag 0AG6] part (3) says the canonical `Iᑫ ⟶ Γ(X, 𝒪_X(q))` is bijective for large `q`.
Its injective half is
`Stacks.LocalCohomology.UniformityIII.exists_forall_injective_ambientSections`, and by
`Stacks.LocalCohomology.UniformityIII.exists_bijective_ambientSections_of_exists_surjective`
only surjectivity is left. The route to it is this file's conclusion followed by two known
identifications: `Γ(𝐏, 𝒪_𝐏(q)) = (A[T₀, …, T_m])_q` through the canonical section map
(`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_mvPolynomial`), and the action of the
degreewise comparison on a canonical section
(`Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso_degreeSection`).

**What that route still requires**, and what is not done here: the two
identifications are stated for *different* maps out of `Γ(𝐏, 𝒪_𝐏(q))`. This file's surjection is
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.twistedSectionsAddHom` at `φ` followed by
`Stacks.Blowup.twistedSectionsUnitMap`, i.e. the sections of `φ ⊗ 𝟙` followed by the projection
formula at `i`; `pullbackTwistIso_degreeSection` instead describes
`Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection` followed by the *pullback* form of
the comparison. Identifying those two composites is the adjunction bookkeeping between the unit
`Γ(𝐏, ℱ) ⟶ Γ(X, i^*ℱ)` and the projection formula, and it is not done here, so no statement
about `Stacks.LocalCohomology.UniformityIII.ambientSections` is made. **No attribute for
[Stacks, Tag 0AG6] or [Stacks, Tag 0GA7] is attached**: nothing below is a clause of either tag,
only an input to one.

## Main results

The elided prefix is `Stacks.Blowup`.

* `isCoherent_kernel_unitToPushforwardObjUnit_blowUpSpecToProjSpace`: the ideal sheaf of the
  blowup inside `𝐏` is coherent.
* `exists_forall_surjective_twistedSectionsAddHom_blowUpSpecToProjSpace`: **the twisted
  ideal-sheaf sequence read on global sections** — `Γ(𝐏, 𝒪_𝐏(q)) ⟶ Γ(𝐏, (i_*𝒪_X)(q))` is
  surjective for every large `q`.
* `exists_forall_surjective_twistedSectionsUnitMap_comp`: the same composed with the degreewise
  comparison, so that the target is `Γ(X, 𝒪_X(q))`.

## Implementation notes

The epimorphism is quoted at the
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` spelling of the comorphism, while the quoted
theorem is stated at `RingedSpaceModuleAdjunction.structureSheafHom`. The two name the same
morphism — both are the whiskering of `i^♯` along `forget₂ CommRingCat RingCat`, as
`Stacks.IdealSheafSequence.divisorQuotientMap_eq` records — so the quotation needs no transport.

The local transparency attributes are those of
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardStep.lean`: without them the sheaf of
rings of `𝐏` is not seen to be the one
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` takes its modules over, and the
coherence hypotheses cannot be handed to the projective-space statements.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistSheafOfModules)
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep (twistedSectionsAddHom)
open Stacks.ProjectiveCohomology (polyGrading)

universe u

namespace Stacks.Blowup

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {m : ℕ}
  (x : Fin (m + 1) → A) (hx : ∀ j, x j ∈ I) (hspan : I = Ideal.span (Set.range x))

/-- **The canonical restriction `𝒪_𝐏 ⟶ i_*𝒪_X`** along the closed immersion of the blowup into
projective space. Its kernel is the ideal sheaf of `X` in `𝐏`. -/
abbrev projSpaceQuotientMap :
    SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading A m)).ringCatSheaf ⟶
      (Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
        (SheafOfModules.unit (blowUpSpec I).ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit (blowUpSpecToProjSpace I x hx hspan).toRingCatSheafHom

/-- The immersion of the blowup into projective space is closed. -/
private instance isClosedImmersion_blowUpSpecToProjSpace' {B : Type u} [CommRing B] {J : Ideal B}
    {n : ℕ} (y : Fin (n + 1) → B) (hy : ∀ j, y j ∈ J) (hJ : J = Ideal.span (Set.range y)) :
    IsClosedImmersion (blowUpSpecToProjSpace J y hy hJ) :=
  isClosedImmersion_blowUpSpecToProjSpace J y hy hJ

omit [IsNoetherianRing A] in
/-- **`𝒪_𝐏 ⟶ i_*𝒪_X` is an epimorphism**, the immersion of the blowup into projective space
being closed. -/
theorem epi_projSpaceQuotientMap : Epi (projSpaceQuotientMap x hx hspan) :=
  Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion
    (blowUpSpecToProjSpace I x hx hspan)

/-- **The direct image of the structure sheaf of the blowup is coherent on `𝐏`**, by
[Stacks, Tag 087T]: `𝐏` is locally Noetherian and `i` is a closed immersion. -/
theorem isCoherent_pushforward_unit_blowUpSpecToProjSpace :
    _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
        (SheafOfModules.unit (blowUpSpec I).ringCatSheaf)) :=
  have : IsClosedImmersion (blowUpSpecToProjSpace I x hx hspan) :=
    isClosedImmersion_blowUpSpecToProjSpace I x hx hspan
  have : IsLocallyNoetherian (blowUpSpec I) :=
    isLocallyNoetherian_of_isClosedImmersion (blowUpSpecToProjSpace I x hx hspan)
  have : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit (blowUpSpec I).ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit (blowUpSpec I)
  isCoherent_pushforward_of_isClosedImmersion (blowUpSpecToProjSpace I x hx hspan)
    (SheafOfModules.unit (blowUpSpec I).ringCatSheaf)

/-- **The ideal sheaf of the blowup inside projective space is coherent.** It is the kernel of
`𝒪_𝐏 ⟶ i_*𝒪_X`, and both of those are coherent — the structure sheaf because `𝐏` is locally
Noetherian, its direct image by [Stacks, Tag 087T] — so [Stacks, Tag 01BY] part (3) applies. -/
theorem isCoherent_kernel_projSpaceQuotientMap :
    _root_.SheafOfModules.IsCoherent (kernel (projSpaceQuotientMap x hx hspan)) :=
  have : _root_.SheafOfModules.IsCoherent
      (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading A m)).ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit
      (AlgebraicGeometry.Proj (polyGrading A m))
  have := isCoherent_pushforward_unit_blowUpSpecToProjSpace x hx hspan
  AlgebraicGeometry.CoherentAbelian.isCoherent_kernel (projSpaceQuotientMap x hx hspan)

/-- **The twisted ideal-sheaf sequence of the blowup in projective space, read on global
sections.** For `q` large every global section of `(i_*𝒪_X)(q)` is the image of a global section
of `𝒪_𝐏(q)`.

The sequence `0 ⟶ ℐ ⟶ 𝒪_𝐏 ⟶ i_*𝒪_X ⟶ 0` is short exact because `i` is a closed immersion; `ℐ`
is coherent, so `H¹(𝐏, ℐ(q))` vanishes for large `q` by [Stacks, Tag 01YS] clause (4); and
twisting a short exact sequence by the invertible `𝒪_𝐏(q)` keeps it short exact, so the long
exact sequence of sections leaves nothing to obstruct the lift. -/
theorem exists_forall_surjective_twistedSectionsAddHom_blowUpSpecToProjSpace :
    ∃ q₀ : ℤ, ∀ q : ℤ, q₀ ≤ q →
      Function.Surjective
        (twistedSectionsAddHom (polyGrading A m) (projSpaceQuotientMap x hx hspan) q) := by
  obtain ⟨q₀, hq₀⟩ :=
    Stacks.ProjectiveSpace.SerreVanishing.exists_isZero_Hgroup_twist_of_isCoherent A m 1
      Nat.one_pos (kernel (projSpaceQuotientMap x hx hspan))
      (isCoherent_kernel_projSpaceQuotientMap x hx hspan)
  exact ⟨q₀, fun q hq =>
    @Stacks.ProjectiveSpace.Cohomology.surjective_twistedSectionsAddHom_of_isZero_firstCohomology
      A _ m _ _ (projSpaceQuotientMap x hx hspan) (epi_projSpaceQuotientMap x hx hspan) q
      (hq₀ q hq)⟩

/-- **Global sections of `𝒪_X(q)` on the blowup all come from `𝐏`, for `q` large.** The previous
theorem composed with `Stacks.Blowup.twistedSectionsUnitMap`, the degreewise comparison
`(i_*𝒪_X)(q) ≅ i_*(𝒪_X(q))` on global sections, which is surjective because it is an
isomorphism. -/
theorem exists_forall_surjective_twistedSectionsUnitMap_comp :
    letI : IsClosedImmersion (AlgebraicGeometry.Proj.map (reesPresentation I x hx)
        (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
          (surjective_reesPresentation I x hx hspan))) :=
      isClosedImmersion_blowUpSpecToProjSpace I x hx hspan
    ∃ q₀ : ℤ, ∀ q : ℤ, q₀ ≤ q →
      Function.Surjective (fun s =>
        twistedSectionsUnitMap (polyGrading A m) (reesGrading I) (reesPresentation I x hx)
          (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
            (surjective_reesPresentation I x hx hspan))
          (surjective_reesPresentation I x hx hspan)
          (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A m) q
          (twistedSectionsAddHom (polyGrading A m) (projSpaceQuotientMap x hx hspan) q s)) := by
  have : IsClosedImmersion (AlgebraicGeometry.Proj.map (reesPresentation I x hx)
      (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
        (surjective_reesPresentation I x hx hspan))) :=
    isClosedImmersion_blowUpSpecToProjSpace I x hx hspan
  obtain ⟨q₀, hq₀⟩ :=
    exists_forall_surjective_twistedSectionsAddHom_blowUpSpecToProjSpace x hx hspan
  exact ⟨q₀, fun q hq => Function.Surjective.comp
    (twistedSectionsUnitMap_surjective (polyGrading A m) (reesGrading I)
      (reesPresentation I x hx) _ (surjective_reesPresentation I x hx hspan)
      (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A m) q) (hq₀ q hq)⟩

end Stacks.Blowup

end
