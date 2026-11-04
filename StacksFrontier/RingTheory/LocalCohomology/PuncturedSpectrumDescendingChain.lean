module

public import StacksFrontier.CategoryTheory.Abelian.InverseSystemProDominated
public import StacksFrontier.RingTheory.LocalCohomology.ArtinianOverLocalRing
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The descending chain condition on the punctured spectrum, and Mittag-Leffler

Let `(A, 𝔪)` be a Noetherian local ring and let `U = Spec A ∖ {𝔪}` be its punctured spectrum.
This file proves, for the coherent `𝒪_U`-modules of the form `M̃|_U` with `M` a finite
`A`-module and in the *ambient* spelling of `Hᵖ(U, -)` described below:

* the `A`-module `Hᵖ(U, M̃)` satisfies the descending chain condition, i.e. is Artinian, for
  every `p ≥ 1`, which is the content of [Stacks, Tag 0DX0] part (2) at such a module;
* for an inverse system `(Mₙ)` of finite `A`-modules the inverse system of `A`-modules
  `n ↦ Hᵖ(U, M̃ₙ)` satisfies the Mittag-Leffler condition for every `p ≥ 1`, which is the
  content of [Stacks, Tag 0DX1] part (2) at such a system.

The source derives part (2) of each lemma from part (1) through the comparison of
[Stacks, Tag 0BK0], and that is the derivation below: for `p ≥ 1` the `A`-module `Hᵖ(U, M̃)` is
the local cohomology `H^{p+1}_𝔪(M)`, which is Artinian for a finite module over a Noetherian
local ring by part (1); and an inverse system of modules whose terms are Artinian is
Mittag-Leffler, because the images of the transition maps into a fixed term form a descending
chain there.

## Main results

* `Stacks.LocalCohomology.isMittagLefflerCategorical_of_isArtinian` — an inverse system of
  Artinian modules satisfies the Mittag-Leffler condition of [Stacks, Tag 02N0].
* `Stacks.LocalCohomology.isArtinian_puncturedSpectrumTildeCohomology` — the descending chain
  condition for `Hᵖ(U, M̃)`, `p ≥ 1`.
* `Stacks.LocalCohomology.isMittagLefflerCategorical_puncturedSpectrumTildeCohomology` — the
  Mittag-Leffler condition for `n ↦ Hᵖ(U, M̃ₙ)`, `p ≥ 1`.

**No `@[stacks]` attribute is placed in this file.** Tags 0DX0 and 0DX1 are about an arbitrary
coherent `𝒪_U`-module, respectively an arbitrary inverse system of them, and about the genuine
derived sections of `U` read as a ringed space; both parts (2) are proved in that generality in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/PuncturedSpectrumCohomologyMittagLeffler.lean`,
which carries the attributes and which consumes the two results below. What is here is the
algebraic engine, in the spelling of `complementCohomologyBase`.

## Implementation notes

*The cohomology on `U`.* `Hᵖ(U, M̃)` is `Stacks.LocalCohomologySequence.complementCohomologyBase`
at the maximal ideal: the degree-`p` right derived functor, on sheaves of modules on `Spec A`, of
the sections over the open `Spec A ∖ V(𝔪)`, read as an `A`-module along the identification of `A`
with the global functions on `Spec A`. That is the spelling in which the library states the
comparison of [Stacks, Tag 0DWR] in positive degrees and clause (3) of [Stacks, Tag 0BK0], and in
which `Stacks.Algebraization.PuncturedNeighbourhood.finite_neighbourhoodCohomology` states
[Stacks, Tag 0DXQ].

*Coherent modules on `U` versus finite modules on `A`.* The source states both lemmas for an
arbitrary coherent `𝒪_U`-module, respectively an arbitrary inverse system of them. By
[Stacks, Tag 0BK0] part (1) — `AlgebraicGeometry.exists_finiteModule_tilde_restrict_zeroLocusCompl`
— every coherent `𝒪_U`-module is isomorphic to `M̃|_U` for some finite `A`-module `M`, so the
statements below are the source's for a single sheaf. They are weaker for a system, because that
lemma chooses the modules one sheaf at a time and does not produce an inverse system of modules
realizing a given inverse system of sheaves — which is why the tagged statement of
[Stacks, Tag 0DX1] part (2) is derived elsewhere from the *objectwise* Artinian conclusion, the
Mittag-Leffler condition needing nothing more.

*Which degrees.* The degree `p` ranges over `ℕ`, which is the indexing of
`complementCohomologyBase`, and `p ≥ 1` is the source's own restriction `i > 0`: in degree zero
the comparison of [Stacks, Tag 0DWR] is a four-term exact sequence rather than an isomorphism,
and `Γ(U, M̃)` is in general not Artinian — it contains the image of `M`.

*The Mittag-Leffler condition.* `IsMittagLefflerCategorical` is the condition of
[Stacks, Tag 02N0] read on subobjects; `isMittagLefflerCategorical_of_forall_exists_range_eq`
turns it into the elementary statement about the ranges of the transition maps, which is what the
descending chain condition is applied to.

## References

* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0DX0](https://stacks.math.columbia.edu/tag/0DX0)
* [Stacks Project, Tag 0DX1](https://stacks.math.columbia.edu/tag/0DX1)

## Tags

local cohomology, punctured spectrum, Mittag-Leffler, descending chain condition
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-! ### Inverse systems of Artinian modules -/

/-- **An inverse system of Artinian modules is Mittag-Leffler.** The images of the transition
maps `Fₖ ⟶ Fᵢ` into a fixed term form a descending chain of submodules of `Fᵢ` as `k` grows, and
a descending chain in an Artinian module stabilizes; so the ranges are eventually constant, which
is the Mittag-Leffler condition of [Stacks, Tag 02N0]. -/
@[ega "0 13.1.2" "special case"]
theorem isMittagLefflerCategorical_of_isArtinian {A : Type u} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (hF : ∀ n : ℕᵒᵖ, IsArtinian A (F.obj n)) :
    IsMittagLefflerCategorical F := by
  refine isMittagLefflerCategorical_of_forall_exists_range_eq F fun i => ?_
  have hart := hF (op i)
  have hmono : ∀ a b : ℕ, a ≤ b →
      LinearMap.range (F.map (homOfLE (show i ≤ i + b by omega)).op).hom ≤
        LinearMap.range (F.map (homOfLE (show i ≤ i + a by omega)).op).hom := by
    intro a b hab
    have hcomp := inverseSystem_transition_comp F (show i ≤ i + a by omega)
      (show i + a ≤ i + b by omega)
    rw [hcomp, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  let f : ℕ →o (Submodule A (F.obj (op i)))ᵒᵈ :=
    { toFun := fun n => LinearMap.range (F.map (homOfLE (show i ≤ i + n by omega)).op).hom
      monotone' := fun a b hab => hmono a b hab }
  obtain ⟨c, hc⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨i + c, by omega, fun k hck => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = i + d := ⟨k - i, by omega⟩
  exact (hc d (by omega)).symm

/-! ### Cohomology on the punctured spectrum -/

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- **`Hᵖ(U, M̃)` on the punctured spectrum `U = Spec A ∖ {𝔪}` of a local ring, as an
`A`-module.** This is `Stacks.LocalCohomologySequence.complementCohomologyBase` at the maximal
ideal: the degree-`p` cohomology on the complement of `V(𝔪)` of the sheaf attached to `M`. -/
abbrev puncturedSpectrumTildeCohomology (M : ModuleCat.{u} A) (p : ℕ) : ModuleCat.{u} A :=
  Stacks.LocalCohomologySequence.complementCohomologyBase (A := CommRingCat.of A)
    (IsLocalRing.maximalIdeal A) M p

/-- **`Hᵖ(U, -̃)` on the punctured spectrum, as a functor of the module.** Composing with an
inverse system of `A`-modules gives the inverse system of cohomology modules of the associated
sheaves, with the transition maps induced functorially. -/
abbrev puncturedSpectrumTildeCohomologyFunctor (p : ℕ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  Stacks.LocalCohomologyTilde.tildeSheafFunctor (CommRingCat.of A) ⋙
    Stacks.LocalCohomologySequence.complementCohomology (IsLocalRing.maximalIdeal A) p ⋙
      Stacks.LocalCohomologyTilde.globalToBase (CommRingCat.of A)

/-- The functor of the previous definition takes the value the previous one names. -/
theorem puncturedSpectrumTildeCohomologyFunctor_obj (M : ModuleCat.{u} A) (p : ℕ) :
    (puncturedSpectrumTildeCohomologyFunctor A p).obj M =
      puncturedSpectrumTildeCohomology A M p := rfl

/-- **The descending chain condition for `Hᵖ(U, M̃)` on the punctured spectrum**, which is the
content of [Stacks, Tag 0DX0] part (2) at the coherent module `M̃|_U`. Let `(A, 𝔪)` be a
Noetherian local ring, let
`U = Spec A ∖ {𝔪}` be its punctured spectrum and let `M` be a finite `A`-module.  Then the
`A`-module `Hᵖ(U, M̃)` satisfies the descending chain condition for every `p ≥ 1`.

The source deduces this from part (1) through Local Cohomology, Lemma [Stacks, Tag 0BK0], and so
does the proof: in positive degrees `Hᵖ(U, M̃)` is the local cohomology `H^{p+1}_𝔪(M)`, by the
comparison of [Stacks, Tag 0DWR] followed by the agreement of the two models of local cohomology
over a Noetherian ring of [Stacks, Tag 0955], and that module is Artinian by part (1). -/
theorem isArtinian_puncturedSpectrumTildeCohomology [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [Module.Finite A M] (p : ℕ) (hp : 1 ≤ p) :
    IsArtinian A (puncturedSpectrumTildeCohomology A M p) := by
  have hNoeth : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  obtain ⟨e⟩ :=
    Stacks.LocalCohomologySequence.nonempty_complementCohomologyBase_iso_localCohomology
      (A := CommRingCat.of A) (IsLocalRing.maximalIdeal A) M p hp
  have e₂ := localCohomologyWithSupportInIsoLocalCohomologyModule A
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M
    ((p + 1 : ℕ) : ℤ)
  have hart : IsArtinian A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M ((p + 1 : ℕ) : ℤ)) :=
    isArtinian_localCohomology_maximalIdeal A M ((p + 1 : ℕ) : ℤ)
  have := hart
  exact isArtinian_of_linearEquiv (e ≪≫ e₂).symm.toLinearEquiv

/-- **The Mittag-Leffler condition for `n ↦ Hᵖ(U, M̃ₙ)`**, which is the content of
[Stacks, Tag 0DX1] part (2) at a system of the form `M̃ₙ|_U`. Let `(A, 𝔪)` be a Noetherian local
ring and let
`U = Spec A ∖ {𝔪}` be its punctured spectrum.  Let `(Mₙ)` be an inverse system of finite
`A`-modules.  Then for every `p ≥ 1` the inverse system of `A`-modules `n ↦ Hᵖ(U, M̃ₙ)` satisfies
the Mittag-Leffler condition.

As in the source this follows immediately from [Stacks, Tag 0DX0]: each term of the system has
the descending chain condition, so the images of the transition maps into a fixed term are
eventually constant. -/
theorem isMittagLefflerCategorical_puncturedSpectrumTildeCohomology [IsNoetherianRing A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hM : ∀ n : ℕᵒᵖ, Module.Finite A (M.obj n))
    (p : ℕ) (hp : 1 ≤ p) :
    IsMittagLefflerCategorical (M ⋙ puncturedSpectrumTildeCohomologyFunctor A p) := by
  refine isMittagLefflerCategorical_of_isArtinian _ fun n => ?_
  have := hM n
  exact isArtinian_puncturedSpectrumTildeCohomology A (M.obj n) p hp

end Stacks.LocalCohomology

end
