module

public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison

/-!
# A generating family of sections gives a morphism to projective space with a pinned twist

Let `M` be an invertible `𝒪_X`-module and `s₀, …, sₙ` global sections of `M` whose germs generate
every stalk. This file assembles the two halves of [Stacks, Tag 01NE] that are proved separately
— the morphism `g : X ⟶ ℙⁿ_ℤ` of the ratio families and the comparison `g ^* 𝒪(1) ≅ M` pinned on
sections — into the single statement the construction of [Stacks, Tag 0CCP] invokes: a morphism
to projective space together with an isomorphism carrying the pulled-back homogeneous coordinate
`g ^* Tᵢ` to `sᵢ`.

The assembly needs no new mathematics: the pinning hypothesis of the comparison is verbatim the
conclusion of the morphism half, so the two compose. What the composite adds is that the morphism
and the pinned comparison exist *for the same* `g`, which is the form a consumer needs and which
neither half states.

## Main results

* `Stacks.TwistPullbackPinned.exists_hom_and_iso_pullback_twistingSheafAtUniverse`: for a
  generating family of global sections of an invertible module there are a morphism
  `g : X ⟶ ℙⁿ_ℤ` and an isomorphism `α : g ^* 𝒪(1) ⟶ M` with `α (g ^* Tᵢ) = sᵢ` for every `i`.
* `Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse`:
  the same over a base scheme, the morphism landing in `ℙⁿ_S` and lying over a given `f : X ⟶ S`.

## Implementation notes

The twist is pulled back along `g` for the absolute statement and along
`p ≫ projectiveSpaceOver.toIntegralAtUniverse n S` for the relative one, that composite being the
morphism to the integral model underlying `p : X ⟶ ℙⁿ_S`. Rewriting the relative statement as a
pullback along `p` of the twist of `ℙⁿ_S` would need the comparison of `(p ≫ q) ^*` with
`p ^* ∘ q ^*` on sheaves of modules, which is not used here.

No `@[stacks]` attribute is attached. Tag 01NE is a representability statement, whose inverse
construction and bijection are not in the repository, and Tag 0CCP additionally passes from a
linear series to the image of the map out of a free module, which is a separate input.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 0CCP](https://stacks.math.columbia.edu/tag/0CCP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections

universe u

namespace Stacks.TwistPullbackPinned

variable {X : Scheme.{u}} {n : ℕ} {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M]

/-- **A generating family of global sections of an invertible module gives a morphism to
projective space together with a pinned comparison of the twist.** For `s₀, …, sₙ` generating
every stalk of `M` there are `g : X ⟶ ℙⁿ_ℤ` and an isomorphism `α : g ^* 𝒪(1) ⟶ M` sending the
pullback of the `i`-th homogeneous coordinate to `sᵢ`. -/
public theorem exists_hom_and_iso_pullback_twistingSheafAtUniverse
    (s : Fin (n + 1) → Γ(M, ⊤)) (hs : GeneratesStalks s) :
    ∃ (g : X ⟶ projectiveSpaceAtUniverse.{u} n)
      (α : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n) ⟶ M),
      IsIso α ∧ ∀ i, α.app ⊤ (pullbackCoordSection.{u} g i) = s i := by
  obtain ⟨g, hpin⟩ := exists_hom_projectiveSpaceAtUniverse_of_generatesStalks
    Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality
    Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance s hs
  obtain ⟨α, hiso, hα⟩ := exists_iso_pullback_twistingSheafAtUniverse s g
    (isOpenCover_nvCover_of_generatesStalks s hs) hpin
  exact ⟨g, α, hiso, hα⟩

/-- **The same over a base scheme.** The morphism lands in `ℙⁿ_S` and lies over the given
`f : X ⟶ S`, and the twist is pulled back along the underlying morphism to the integral model. -/
public theorem exists_hom_over_and_iso_pullback_twistingSheafAtUniverse
    (s : Fin (n + 1) → Γ(M, ⊤)) (hs : GeneratesStalks s) {S : Scheme.{u}} (f : X ⟶ S) :
    ∃ p : X ⟶ projectiveSpaceOver n S,
      p ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
      ∃ α : (Scheme.Modules.pullback
          (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S)).obj
            (twistingSheafAtUniverse.{u} n) ⟶ M,
        IsIso α ∧ ∀ i, α.app ⊤ (pullbackCoordSection.{u}
          (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S) i) = s i := by
  obtain ⟨p, hf, hpin⟩ :=
    Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks s hs f
  obtain ⟨α, hiso, hα⟩ := exists_iso_pullback_twistingSheafAtUniverse s
    (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S)
    (isOpenCover_nvCover_of_generatesStalks s hs) hpin
  exact ⟨p, hf, α, hiso, hα⟩

end Stacks.TwistPullbackPinned

end
