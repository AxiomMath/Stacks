module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterionMain
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence of an open direct image over an affine base, in degree zero

Let `A` be a Noetherian ring, `X = Spec A`, let `V ⊆ X` be an open and let `F` be a coherent
`𝒪_V`-module. The degree-zero clause of [Stacks, Tag 0BK0] says that the direct image `j_*F`
along `j : V ⟶ X` is coherent exactly when `H⁰(V, F)` is a finite `A`-module. This file proves
that equivalence.

Both directions were already available for the structure sheaf `F = 𝒪_V`:
`Stacks.LocalCohomology.module_finite_sections_of_isCoherent` and
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_module_finite_sections`. What is
added here is the same equivalence for an arbitrary coherent module on `V`, which is the shape
[Stacks, Tag 0BK0] states it in and the shape the induction of [Stacks, Tag 0BK1] consumes.

The sections of the direct image over the whole of `X` *are* the sections of `F` over the whole
of `V`, by the definition of the direct image of a presheaf along an open immersion; this is
`Stacks.LocalCohomology.sections_top_pushforward`, which holds by `rfl`. So the right-hand side
of the equivalence is literally `H⁰(V, F)` with its `A`-module structure coming from
`Γ(X, ⊤) ≅ A`, and no restriction of scalars along `A → Γ(X, V)` is needed.

## Main results

* `Stacks.LocalCohomology.sections_top_pushforward`: the global sections of the direct image
  along an open immersion are the global sections of the module itself.
* `Stacks.LocalCohomology.isCoherent_pushforward_iff_module_finite_sections`: **the degree-zero
  clause of [Stacks, Tag 0BK0]** — over an affine Noetherian base, the direct image of a coherent
  module on an open is coherent if and only if its global sections form a finite module over the
  base ring.
* `Stacks.LocalCohomology.isCoherent_higherDirectImage_zero_iff_module_finite_sections`: the same
  equivalence written with `R⁰j_*`, which is the indexing [Stacks, Tag 0BK0] states clause (3) in.

The open is an arbitrary open of `Spec A`, so the statement covers in particular the complement
`U = Spec A \ V(I)` of the zero locus of an ideal, which is the open [Stacks, Tag 0BK0] is stated
on; no finite generation of `I` is needed, `A` being Noetherian.

## Implementation notes

No `@[stacks 0BK0]` attribute is attached to anything here, and none may be: this is one clause of
a four-clause lemma. The other three clauses stand as follows.
* the extension of a coherent module on `V` to a *finite* `A`-module — part (1) of the tag. This
  is now proved, as
  `AlgebraicGeometry.exists_isCoherent_module_finite_sections_restrict_iso` in
  `StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeExtension`: the
  quasi-coherent extension of [Stacks, Tag 01PE] is upgraded to a finite type one by the
  finite-type extension lemma [Stacks, Tag 01PF],
  `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension`, and finite type plus
  quasi-coherent on a Noetherian affine scheme is finiteness of the global sections. It does not
  carry a `@[stacks 0BK0]` attribute either, for the same reason as the declarations here;
* the comparisons `H^p(V, F) ≅ H^{p+1}_Z(M)` for `p ≥ 1` — part (2) in higher degrees — of which
  nothing is in the library;
* the clauses of part (3) in degrees `p ≥ 1`, and part (4), both of which rest on part (2).

Part (2) in degrees `0` and `1` — the four-term sequence
`0 → H⁰_Z(M) → M → H⁰(V, F) → H¹_Z(M) → 0` — is available: it is
`Stacks.LocalCohomology.exists_lowDegreeLocalizationExactSequence`, which needs neither the
Noetherian hypothesis nor the coherence of `F`.

A faithful formalization of the tag must also fix a model of local cohomology and stay in it: this
library deliberately keeps the right-adjoint `RΓ_Z` of [Stacks, Tag 0A6Q] apart from the derived
`Z`-supported sections `RΓ_{V(I)}` of [Stacks, Tag 0EF4], because the comparison
`Stacks.LocalCohomology.compareSectionsWithSupportLocalCohomology` between them is only known to be
invertible by [Stacks, Tag 0955], which is not proved here. Nothing in the present file touches
local cohomology, so the question does not arise for these two declarations.

Quasi-coherence of the direct image is [Stacks, Tag 01LC] for a quasi-compact quasi-separated
morphism, available as
`Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs`; the inclusion of an
open of a scheme is quasi-compact here because `Spec A` is a Noetherian space, and quasi-separated
because it is a monomorphism, so both instances are found without hypotheses.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- The global sections of the direct image of a module along the inclusion of an open `V ⊆ X`
are the global sections of the module over `V` itself. -/
theorem sections_top_pushforward {X : Scheme.{u}} (V : X.Opens) (F : (V : Scheme).Modules) :
    Γ((Scheme.Modules.pushforward V.ι).obj F, (⊤ : X.Opens)) =
      Γ(F, (⊤ : (V : Scheme).Opens)) :=
  rfl

/-- **The degree-zero clause of [Stacks, Tag 0BK0].** Let `A` be a Noetherian ring, `V` an open of
`Spec A` and `F` a coherent `𝒪_V`-module. The direct image of `F` along `V ⟶ Spec A` is coherent
if and only if `H⁰(V, F)` is a finite `A`-module.

By `Stacks.LocalCohomology.sections_top_pushforward` the module on the right is `H⁰(V, F)`.

Both directions go through the characterisation of coherence on a locally Noetherian scheme as
quasi-coherence together with finite type ([Stacks, Tag 01XZ]), the direct image being
quasi-coherent by [Stacks, Tag 01LC]. Forwards, a coherent module is of finite type and a
quasi-coherent module of finite type on an affine scheme has finite global sections
(`AlgebraicGeometry.moduleFinite_of_isFiniteType_qc`). Backwards, finiteness of the global
sections makes the quasi-coherent direct image of finite type
(`Stacks.LocalCohomology.isFiniteType_of_moduleFinite_qc`), hence coherent.

This generalises `Stacks.LocalCohomology.module_finite_sections_of_isCoherent` and
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_module_finite_sections`, which
are the two directions for `F = 𝒪_V`, from the structure sheaf to an arbitrary coherent module. -/
@[ega "IV 7.2.4" "(e)"]
theorem isCoherent_pushforward_iff_module_finite_sections (R : CommRingCat.{u})
    [IsNoetherianRing R] (V : (Spec R).Opens) (F : (V : Scheme).Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward V.ι).obj F).IsCoherent ↔
      Module.Finite (ToType R)
        Γ((Scheme.Modules.pushforward V.ι).obj F, (⊤ : (Spec R).Opens)) := by
  have : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  have := Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs V.ι F
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h.isFiniteType
    exact AlgebraicGeometry.moduleFinite_of_isFiniteType_qc R _
  · have := isFiniteType_of_moduleFinite_qc R _ h
    exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **The degree-zero clause of [Stacks, Tag 0BK0], in the tag's own indexing.** Let `A` be a
Noetherian ring, `j : V ⟶ Spec A` the inclusion of an open and `F` a coherent `𝒪_V`-module. Then
`R⁰j_*F` is coherent if and only if `H⁰(V, F)` is a finite `A`-module.

The tag states clause (3) for the higher direct images `R^p j_*F`. In degree zero these agree with
the ordinary direct image, the pushforward of sheaves of modules being a right adjoint and hence
left exact (`AlgebraicGeometry.CoherentAbelian.isCoherent_higherDirectImage_zero_iff`), so this is
`isCoherent_pushforward_iff_module_finite_sections` read in the tag's indexing. The clauses in
degrees `p ≥ 1` are not proved; see the module docstring. -/
theorem isCoherent_higherDirectImage_zero_iff_module_finite_sections (R : CommRingCat.{u})
    [IsNoetherianRing R] (V : (Spec R).Opens) (F : (V : Scheme).Modules) [F.IsCoherent] :
    (((Scheme.Modules.pushforward V.ι).rightDerivedPlus 0).obj F).IsCoherent ↔
      Module.Finite (ToType R)
        Γ((Scheme.Modules.pushforward V.ι).obj F, (⊤ : (Spec R).Opens)) :=
  (AlgebraicGeometry.CoherentAbelian.isCoherent_higherDirectImage_zero_iff V.ι F).trans
    (isCoherent_pushforward_iff_module_finite_sections R V F)

end Stacks.LocalCohomology

end
