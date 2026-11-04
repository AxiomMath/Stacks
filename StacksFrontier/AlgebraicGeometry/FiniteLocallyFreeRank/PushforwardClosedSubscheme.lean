module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite local freeness of a given rank on a closed subscheme, read on the ambient scheme

Let `I : X.IdealSheafData` cut out a closed subscheme `D = I.subscheme` of a scheme `X`, with
closed immersion `ι = I.subschemeι`, and let `G` be a sheaf of modules on `D`. Two statements
about `G` are available, and nothing so far connects them:

* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank G n`, finite local freeness of
  rank `n` **on `D`**;
* a description of the direct image `ι_* G` **on `X`**, which is the form in which a sheaf on a
  closed subscheme is met by a consumer working on the ambient scheme.

This file proves that the two are equivalent: `G` is finite locally free of rank `n` on `D`
exactly when, locally on `X`, the direct image `ι_* G` is isomorphic to `(𝒪_X ⧸ I)^{⊕ n}`.

The quotient `𝒪_X ⧸ I` is, in this library, the direct image `ι_* 𝒪_D`: the ideal sheaf of a
closed subscheme is *defined* as the kernel of `𝒪_X ⟶ ι_* 𝒪_D`
(`Stacks.IdealSheafSequence.divisorIdealMap`), and `ι_* 𝒪_D` is already named
`AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeStructureSheaf`. Accordingly
`(𝒪_X ⧸ I)^{⊕ n}` is the direct image of the free sheaf of rank `n` on `D`, which is
`closedSubschemeFreeSheaf` below. That object is the `n`-fold direct sum of `ι_* 𝒪_D`, the
direct image being additive and the free sheaf of rank `n` being by definition the `n`-fold
direct sum of `𝒪_D`; the comparison is not recorded as a declaration, because the direct image
of the free sheaf is the spelling a consumer states its local description in.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeFreeSheaf`: `(𝒪_X ⧸ I)^{⊕ n}`,
  namely `𝒪_D^{⊕ n}` pushed forward to the ambient scheme.

## Main results

* `Stacks.ClosedSubscheme.isFiniteLocallyFreeOfRank_iff_locally_pushforward_iso`: finite local
  freeness of rank `n` of `G` on the closed subscheme is equivalent to the direct image
  `ι_* G` being locally on `X` isomorphic to `(𝒪_X ⧸ I)^{⊕ n}`.

## Which direction a consumer uses

A consumer such as the graded-piece clause of [Stacks, Tag 0ESU] has a module `Q` on `X` — a
cokernel of a step of a filtration — together with an isomorphism `Q ≅ ι_* G`, and knows the
local shape of `Q` on `X` from local equations for the divisor. It owes
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank G n`, so the direction it needs is
`.mpr`: from the local description of the direct image on `X` to the rank on `D`.

The hypotheses taken are exactly `I : X.IdealSheafData` and `G : I.subscheme.Modules`; there is
no quasi-coherence, finiteness or effective-Cartier hypothesis on either, and no hypothesis
relating `G` to anything on `X`. An effective Cartier divisor is in particular given by an
ideal sheaf datum, so a consumer meets these hypotheses by construction.

## Implementation notes

Both directions pass through the pointwise form of the rank condition,
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank`, which is identified with the
single-datum form of Tag 01C6 by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_iff`. Both are then an application
of three facts, none of which is proved here:

* restriction to an open `U` of the target commutes with the direct image
  (`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`), which replaces
  `(ι_* M)|_U` by `(ι ∣_ U)_* (M|_{ι ⁻¹ᵁ U})`;
* the direct image along a closed immersion is fully faithful
  (`Stacks.ClosedImmersion.fullyFaithfulPushforward`, Tag 08KS), which descends an isomorphism
  of direct images over `U` to an isomorphism over `ι ⁻¹ᵁ U`;
* restriction carries a free sheaf to the free sheaf on the same index type
  (`Stacks.Modules.restrictFreeIso`).

The forward direction needs two further geometric inputs. Every open of `D` is the preimage of
an open of `X`, because the underlying map of a closed immersion is an embedding, hence
inducing; this is what lets a trivialising open of `D` be replaced by an open of `X`. And the
points of `X` off the support of `I` have to be covered too: there the open complement of the
support has empty preimage in `D`, so every sheaf of modules on that preimage is isomorphic to
every other (`AlgebraicGeometry.subsingleton_hom_of_isEmpty`), and the two direct images agree
over it for that reason rather than by any computation.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- `(𝒪_X ⧸ I)^{⊕ n}`: the free sheaf of rank `n` on the closed subscheme cut out by `I`,
pushed forward along its closed immersion and viewed as a sheaf of modules on the ambient
scheme. The free sheaf of rank `n` is the `n`-fold direct sum of `𝒪_D` and the direct image is
additive, so this is the `n`-fold direct sum of
`AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeStructureSheaf`, which is `𝒪_X ⧸ I`. -/
abbrev closedSubschemeFreeSheaf (I : X.IdealSheafData) (n : ℕ) : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj
    (_root_.SheafOfModules.free.{u} (ULift.{u, 0} (Fin n)))

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.ClosedSubscheme

variable {X : Scheme.{u}} (I : X.IdealSheafData) (G : I.subscheme.Modules) (n : ℕ)

/-- Restriction to an open `U` of the ambient scheme of the direct image along the closed
immersion of the subscheme, read as a direct image along the restricted closed immersion. This
is `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` at the closed immersion
of the subscheme, named so that both directions below can conjugate with it. -/
def restrictPushforwardSubschemeIso (U : X.Opens) (M : I.subscheme.Modules) :
    ((Scheme.Modules.pushforward I.subschemeι).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (I.subschemeι ∣_ U)).obj
        (M.restrict (I.subschemeι ⁻¹ᵁ U).ι) :=
  (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso I.subschemeι U).app M

/-- An isomorphism over `ι ⁻¹ᵁ U` between two sheaves on the closed subscheme gives one between
their direct images restricted to `U`. -/
private theorem restrict_pushforward_iso_of_restrict_iso (U : X.Opens) (F : I.subscheme.Modules)
    (h : Nonempty (G.restrict (I.subschemeι ⁻¹ᵁ U).ι ≅ F.restrict (I.subschemeι ⁻¹ᵁ U).ι)) :
    Nonempty (((Scheme.Modules.pushforward I.subschemeι).obj G).restrict U.ι ≅
      ((Scheme.Modules.pushforward I.subschemeι).obj F).restrict U.ι) :=
  h.map fun ε ↦ restrictPushforwardSubschemeIso I U G ≪≫
    (Scheme.Modules.pushforward (I.subschemeι ∣_ U)).mapIso ε ≪≫
    (restrictPushforwardSubschemeIso I U F).symm

/-- **Finite local freeness of rank `n` on a closed subscheme, read on the ambient scheme.**
A sheaf of modules `G` on the closed subscheme cut out by `I` is finite locally free of rank
`n` exactly when its direct image is, locally on the ambient scheme, isomorphic to
`(𝒪_X ⧸ I)^{⊕ n}`.

The `mpr` direction is the one a consumer with a description of the direct image uses. -/
@[ega "II 6.1.12" "special case"]
theorem isFiniteLocallyFreeOfRank_iff_locally_pushforward_iso :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G n ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        Nonempty (((Scheme.Modules.pushforward I.subschemeι).obj G).restrict U.ι ≅
          (I.closedSubschemeFreeSheaf n).restrict U.ι) := by
  constructor
  · intro h x
    by_cases hx : x ∈ (I.support : Set X)
    · rw [← I.range_subschemeι] at hx
      obtain ⟨y, rfl⟩ := hx
      obtain ⟨V, hyV, ⟨ε⟩⟩ := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff G n).mpr h y
      obtain ⟨t, ht, htV⟩ := I.subschemeι.isEmbedding.isInducing.isOpen_iff.mp V.2
      obtain rfl : V = I.subschemeι ⁻¹ᵁ (⟨t, ht⟩ : X.Opens) := TopologicalSpace.Opens.ext htV.symm
      exact ⟨⟨t, ht⟩, hyV, restrict_pushforward_iso_of_restrict_iso I G _ _
        ⟨ε ≪≫ (Stacks.Modules.restrictFreeIso
          (I.subschemeι ⁻¹ᵁ (⟨t, ht⟩ : X.Opens)).ι _).symm⟩⟩
    · refine ⟨⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩, hx, ?_⟩
      have : IsEmpty
          ((I.subschemeι ⁻¹ᵁ (⟨(I.support : Set X)ᶜ,
            I.support.isClosed.isOpen_compl⟩ : X.Opens)).toScheme) := by
        refine ⟨fun z ↦ ?_⟩
        have hmem : I.subschemeι z.1 ∈ Set.range I.subschemeι := Set.mem_range_self _
        rw [I.range_subschemeι] at hmem
        exact absurd hmem z.2
      exact restrict_pushforward_iso_of_restrict_iso I G _ _
        ⟨{ hom := 0, inv := 0, hom_inv_id := Subsingleton.elim _ _,
           inv_hom_id := Subsingleton.elim _ _ }⟩
  · intro h
    rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff]
    intro y
    obtain ⟨U, hxU, ⟨e⟩⟩ := h (I.subschemeι.base y)
    refine ⟨I.subschemeι ⁻¹ᵁ U, hxU, ⟨?_⟩⟩
    exact (Stacks.ClosedImmersion.fullyFaithfulPushforward
        (I.subschemeι ∣_ U)).preimageIso
        ((restrictPushforwardSubschemeIso I U G).symm ≪≫ e ≪≫
          restrictPushforwardSubschemeIso I U _) ≪≫
      Stacks.Modules.restrictFreeIso (I.subschemeι ⁻¹ᵁ U).ι _

end Stacks.ClosedSubscheme

end
