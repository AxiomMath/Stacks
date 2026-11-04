module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZero
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSectionsAffineOpen
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothAffineLocally
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local projectivity of the differentials of a formally smooth morphism

[Stacks, Tag 0D0L] characterises formal smoothness of a morphism of schemes `f : X ⟶ Y` by two
conditions on its naive cotangent complex: `H⁻¹(NL_{X/Y}) = 0`, and
`H⁰(NL_{X/Y}) = Ω_{X/Y}` is locally projective. This file proves the **necessity of the second
condition**: for a formally smooth `f` the sheaf `Ω_{X/Y}` — equivalently, by the degree-zero
clause of [Stacks, Tag 0D0J], the degree-zero cohomology sheaf of `NL_{X/Y}` — is locally
projective in the sense of [Stacks, Tag 05JP], that is, its sections over every affine open are
a projective module over the functions on that open.

## Main results

* `Stacks.Smooth.projective_cotangentSheaf_sections`: if the ring map `Γ(Y, V) ⟶ Γ(X, U)` of a
  pair of affine opens `U ≤ f ⁻¹ᵁ V` is formally smooth, then `Γ(Ω_{X/Y}, U)` is a projective
  `Γ(X, U)`-module.
* `Stacks.Smooth.isLocallyProjective_cotangentSheaf_of_formallySmoothAffineLocally` and
  `Stacks.Smooth.isLocallyProjective_relativeDifferentials_of_formallySmoothAffineLocally`: an
  affine-locally formally smooth morphism has locally projective `Ω_{X/Y}`, for the two
  constructions of `Ω_{X/Y}` carried by the repository.  Affine-local formal smoothness is
  condition (3) of [Stacks, Tag 0D0F] and is the hypothesis that the étale charts of a formally
  smooth morphism of algebraic spaces supply.
* `Stacks.Smooth.isLocallyProjective_cotangentSheaf_of_formallySmooth` and
  `Stacks.Smooth.isLocallyProjective_relativeDifferentials_of_formallySmooth`: the same for a
  formally smooth morphism, for the two constructions of `Ω_{X/Y}` carried by the repository.
* `Stacks.Smooth.isLocallyProjective_homology_zero_naiveCotangentComplex_of_formallySmooth`:
  **the locally projective clause of [Stacks, Tag 0D0L]**, read on `H⁰(NL_{X/Y})` itself.

## Route

The proof is the source's, through [Stacks, Tag 0D0F]: formal smoothness of `f` is inherited by
every restriction `f.resLE V U` to a pair of affine opens, so the induced ring map
`Γ(Y, V) ⟶ Γ(X, U)` is formally smooth
(`Stacks.Smooth.formallySmoothAffineLocally_of_formallySmooth`, the implication (1) ⟹ (3) of
that tag). Projectivity of `Ω[Γ(X, U)⁄Γ(Y, V)]` is then part of Mathlib's *definition* of a
formally smooth algebra, which is [Stacks, Tag 031J] clause (6) — the clause the source's proof
of Tag 0D0L invokes. Transporting it along the identification
`Ω[Γ(X, U)⁄Γ(Y, V)] ≃ₗ Γ(Ω_{X/Y}, U)` of [Stacks, Tag 01UT]
(`Stacks.Smooth.cotangentSectionsEquiv`) gives projectivity of the sections of `Ω_{X/Y}`.

Affine opens of `X` mapping into an affine open of `Y` cover `X`, and for a quasi-coherent
sheaf local projectivity may be checked on a single affine open cover
(`AlgebraicGeometry.isLocallyProjective_iff_exists_affineOpen_cover`, [Stacks, Tag 05JQ]); this
is what turns the chartwise statement into the global one, and it is the only place
quasi-coherence of `Ω_{X/Y}` is used.

## Implementation notes

The two transported statements go through `AlgebraicGeometry.sectionsLinearEquivOfIso` — the
linear equivalence an isomorphism of `𝒪_X`-modules induces on sections over an open — rather
than through `AlgebraicGeometry.Scheme.Modules.isLocallyProjective_of_iso`, which says exactly
this for `IsLocallyProjective` but lives in
`StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.InternalHom`, a module whose whole
cohomological apparatus is irrelevant here. `IsLocallyProjective` is an abbreviation for a
statement about sections, so applying the equivalence on each affine open is the entire
transport.

## Scope

[Stacks, Tag 0D0L] is an equivalence with two clauses, and this file proves one clause in one
direction; the attribute says which. The rest of the tag is proved elsewhere, and the tag is
registered in full.

* The vanishing `H⁻¹(NL_{X/Y}) = 0` is proved, by the stalkwise route, in
  `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothVanishing`, as
  `Stacks.Smooth.isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth`, which carries
  the other clause-scoped [Stacks, Tag 0D0L] attribute. Together with the statement below that
  completes the forward implication of the tag.
* The converse implication is proved in
  `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothConverse`, as
  `Stacks.Smooth.formallySmooth_of_isZero_homology_negOne_of_isLocallyProjective_homology_zero`;
  the two together are the equivalence
  `Stacks.Smooth.formallySmooth_iff_isZero_homology_negOne_and_isLocallyProjective_homology_zero`,
  which is the declaration carrying [Stacks, Tag 0D0L] for the whole statement. That file reduces
  the converse to the affine charts by the implication (3) ⟹ (1) of [Stacks, Tag 0D0F] — proved
  in full and unconditionally as `Stacks.Smooth.formallySmooth_tfae` in
  `StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothTFAE` — and obtains the chartwise vanishing
  of `H¹(L_{Γ(X, U)/Γ(Y, V)})` from `H⁻¹(NL_{X/Y}) = 0` through the ring-level core of
  [Stacks, Tag 0D0I], which performs the change of base ring along the localization
  `Γ(Y, V) → 𝒪_{Y, f x}` that no flatness hypothesis is available for.

## References

* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L)
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F), formal smoothness read
  on affine opens, whose implication (1) ⟹ (3) is the first step.
* [Stacks Project, Tag 031J](https://stacks.math.columbia.edu/tag/031J), clause (6): a formally
  smooth algebra has projective differentials.
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT), the sections of
  `Ω_{X/Y}` over an affine open.
* [Stacks Project, Tag 05JP](https://stacks.math.columbia.edu/tag/05JP), locally projective
  sheaves of modules, and
  [Stacks Project, Tag 05JQ](https://stacks.math.columbia.edu/tag/05JQ), the affine open cover
  criterion.
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J), the degree-zero
  identification `H⁰(NL_{X/Y}) = Ω_{X/Y}`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Smooth

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The sections of `Ω_{X/Y}` on an affine chart of a formally smooth ring map are
projective.** Let `Spec Γ(X, U) = U ⊆ X` and `Spec Γ(Y, V) = V ⊆ Y` be affine opens with
`f(U) ⊆ V`. If the induced ring map `Γ(Y, V) ⟶ Γ(X, U)` is formally smooth, then
`Γ(Ω_{X/Y}, U)` is a projective `Γ(X, U)`-module.

Projectivity of `Ω[Γ(X, U)⁄Γ(Y, V)]` is one of the two defining conditions of a formally smooth
algebra, and `Stacks.Smooth.cotangentSectionsEquiv` ([Stacks, Tag 01UT]) identifies that module
with `Γ(Ω_{X/Y}, U)`. -/
theorem projective_cotangentSheaf_sections {V : Y.Opens} {U : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V)
    (h : RingHom.FormallySmooth (f.appLE V U hUV).hom) :
    Module.Projective Γ(X, U) Γ(cotangentSheaf f, U) := by
  let := algebraAppLE f hUV
  have : Algebra.FormallySmooth Γ(Y, V) Γ(X, U) := h.toAlgebra
  have : Module.Projective Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)] :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  exact Module.Projective.of_equiv' (cotangentSectionsEquiv f hU hV hUV)

/-- Local projectivity of a module on a scheme transports along an isomorphism. -/
private theorem isLocallyProjective_of_iso {M N : X.Modules} (e : N ≅ M)
    (h : Scheme.Modules.IsLocallyProjective N) : Scheme.Modules.IsLocallyProjective M :=
  fun U hU ↦ @Module.Projective.of_equiv' Γ(X, U) _ Γ(M, U) _ (M.val.obj (.op U)).isModule
    Γ(N, U) _ (N.val.obj (.op U)).isModule (h U hU) (sectionsLinearEquivOfIso e U)

/-- **Affine-locally formally smooth morphisms have locally projective differentials.** If every
ring map `Γ(Y, V) ⟶ Γ(X, U)` induced by `f` on a pair of affine opens with `f(U) ⊆ V` is formally
smooth, then `Ω_{X/Y}` is a locally projective sheaf of `𝒪_X`-modules.

The affine opens of `X` contained in the preimage of an affine open of `Y` cover `X`, and local
projectivity of a quasi-coherent sheaf may be read on one affine open cover by
[Stacks, Tag 05JQ]. -/
@[ega "IV 16.10.2" "Condition (i)", ega "IV 17.2.3"]
theorem isLocallyProjective_cotangentSheaf_of_formallySmoothAffineLocally
    (hf : FormallySmoothAffineLocally f) :
    Scheme.Modules.IsLocallyProjective (cotangentSheaf f) := by
  have := isQuasicoherent_cotangentSheaf f
  rw [AlgebraicGeometry.isLocallyProjective_iff_exists_affineOpen_cover]
  refine ⟨{p : Y.affineOpens × X.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1},
    fun i ↦ i.1.2.1, IsOpenCover.mk (top_le_iff.mp fun x _ ↦ ?_), fun i ↦ i.1.2.2, fun i ↦ ?_⟩
  · obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base x) (Opens.mem_top _)
    obtain ⟨U, hU, hxU, hUV⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V) hxV
    exact Opens.mem_iSup.mpr ⟨⟨(⟨V, hV⟩, ⟨U, hU⟩), hUV⟩, hxU⟩
  · exact projective_cotangentSheaf_sections f i.1.2.2 i.1.1.2 i.2
      ((formallySmoothAffineLocally_iff_appLE f).mp hf i.1.1 i.1.2 i.2)

/-- **A formally smooth morphism has locally projective differentials.** For a formally smooth
morphism of schemes `f : X ⟶ Y` the sheaf of relative differentials `Ω_{X/Y}` is locally
projective.

Formal smoothness restricts to every pair of opens ([Stacks, Tag 02H3]), hence induces a formally
smooth ring map on sections over a pair of affine opens — the implication (1) ⟹ (3) of
[Stacks, Tag 0D0F]. -/
@[ega "IV 16.10.2" "Condition (i)", ega "IV 17.2.3"]
theorem isLocallyProjective_cotangentSheaf_of_formallySmooth (hf : FormallySmoothScheme f) :
    Scheme.Modules.IsLocallyProjective (cotangentSheaf f) :=
  isLocallyProjective_cotangentSheaf_of_formallySmoothAffineLocally f
    (formallySmoothAffineLocally_of_formallySmooth (formallySmooth_of_formallySmoothScheme hf))

/-- **An affine-locally formally smooth morphism has locally projective differentials**, for the
corepresenting construction `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` of `Ω_{X/Y}`.

This is `Stacks.Smooth.isLocallyProjective_cotangentSheaf_of_formallySmoothAffineLocally`
transported along the canonical isomorphism between the repository's two constructions of
`Ω_{X/Y}`.  Affine-local formal smoothness is condition (3) of [Stacks, Tag 0D0F], and it is
what the étale charts of a formally smooth morphism of algebraic spaces supply, so this is the
form that a statement about algebraic spaces consumes. -/
@[ega "IV 16.10.2" "Condition (i)", ega "IV 17.2.3"]
theorem isLocallyProjective_relativeDifferentials_of_formallySmoothAffineLocally
    (hf : FormallySmoothAffineLocally f) :
    Scheme.Modules.IsLocallyProjective (Scheme.Hom.relativeDifferentials f) :=
  isLocallyProjective_of_iso (Scheme.Hom.cotangentSheafIso f).symm
    (isLocallyProjective_cotangentSheaf_of_formallySmoothAffineLocally f hf)

/-- **A formally smooth morphism has locally projective differentials**, for the corepresenting
construction `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` of `Ω_{X/Y}`.

This is
`Stacks.Smooth.isLocallyProjective_relativeDifferentials_of_formallySmoothAffineLocally` at the
affine-local formal smoothness which a formally smooth morphism has by the implication (1) ⟹ (3)
of [Stacks, Tag 0D0F]. -/
@[ega "IV 16.10.2" "Condition (i)", ega "IV 17.2.3"]
theorem isLocallyProjective_relativeDifferentials_of_formallySmooth
    (hf : FormallySmoothScheme f) :
    Scheme.Modules.IsLocallyProjective (Scheme.Hom.relativeDifferentials f) :=
  isLocallyProjective_relativeDifferentials_of_formallySmoothAffineLocally f
    (formallySmoothAffineLocally_of_formallySmooth (formallySmooth_of_formallySmoothScheme hf))

/-- **The locally projective clause of [Stacks, Tag 0D0L], in the direction that formal
smoothness is the hypothesis.** For a formally smooth morphism of schemes `f : X ⟶ Y` the
degree-zero cohomology sheaf `H⁰(NL_{X/Y})` of the naive cotangent complex is a locally
projective sheaf of `𝒪_X`-modules.

The tag states an equivalence between formal smoothness of `f` and the conjunction of
`H⁻¹(NL_{X/Y}) = 0` with local projectivity of `H⁰(NL_{X/Y}) = Ω_{X/Y}`. This statement is the
local projectivity of `H⁰`, in the direction that takes formal smoothness as the hypothesis; the
vanishing clause in that direction is
`Stacks.Smooth.isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth`, the converse is
`Stacks.Smooth.formallySmooth_of_isZero_homology_negOne_of_isLocallyProjective_homology_zero`, and
the equivalence itself is
`Stacks.Smooth.formallySmooth_iff_isZero_homology_negOne_and_isLocallyProjective_homology_zero`.
The identification of `H⁰(NL_{X/Y})` with `Ω_{X/Y}` along which the statement is read is the
degree-zero clause of [Stacks, Tag 0D0J],
`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`. -/
@[ega "IV 17.2.3"]
theorem isLocallyProjective_homology_zero_naiveCotangentComplex_of_formallySmooth
    (hf : FormallySmoothScheme f) :
    Scheme.Modules.IsLocallyProjective ((Scheme.naiveCotangentComplex f).homology 0) :=
  isLocallyProjective_of_iso (Scheme.naiveCotangentComplexHomologyZeroIso f).symm
    (isLocallyProjective_relativeDifferentials_of_formallySmooth f hf)

end Stacks.Smooth

end
