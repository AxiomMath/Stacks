module

public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmpleFamily

/-!
# Ample families from complements of effective Cartier divisors

Let `X` be a scheme, let `D 0, …, D (m-1)` be effective Cartier divisors on `X` and let
`L 0, …, L (m-1)` be invertible `𝒪_X`-modules such that

* the divisors have empty common intersection, equivalently the open complements
  `U i = X ∖ D i` cover `X`, and
* `L i` restricted to `U i` is ample for every `i`.

[Stacks, Tag 0GTS] concludes that `X` has an ample family of invertible modules in the sense of
[Stacks, Tag 0FXR] (`AlgebraicGeometry.Scheme.IsAmpleFamily`), namely that `X` is quasi-compact
and every point of `X` lies in an affine nonvanishing locus of a global section of a positive
tensor power of a member of some family of invertible modules.

This file holds the hypothesis of the tag and the two space-level consequences of it that the
proof needs: `X` is quasi-compact, which is clause (1) of the conclusion, and quasi-separated,
which is what the section-extension step of the source's proof asks of `X`. The tag itself is
`Stacks.AmpleFamilyCartier.exists_isAmpleFamily_of_isAmpleOnComplement_cover`, in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.AmpleFamilyCartier.AmpleFamily`.

## Main definitions

* `Stacks.AmpleFamilyCartier.IsAmpleOnComplement`: the hypothesis of Tag 0GTS at one index —
  the restriction of `L` to the open complement of the support of `D` is an invertible module and
  is ample there. The invertibility of the restriction is packaged into the predicate because
  `AlgebraicGeometry.Scheme.Modules.IsAmple` takes it as an instance argument, so the ampleness
  of the restriction cannot be stated without it.

## Main results

* `Stacks.AmpleFamilyCartier.compactSpace_of_isAmpleOnComplement_cover`: **clause (1) of the
  ample family of Tag 0FXR**, i.e. `CompactSpace X`, under the hypotheses of Tag 0GTS. Each
  `U i` is quasi-compact because ampleness of `L i|_{U i}` asserts it, and the `U i` cover `X`
  by the emptiness of the common intersection, so finitely many quasi-compact opens cover `X`.
  The effective Cartier hypothesis is not used.
* `Stacks.AmpleFamilyCartier.quasiSeparatedSpace_of_isAmpleOnComplement_cover`: `X` is a
  quasi-separated space under the same hypotheses. This clause is *not* part of the conclusion of
  Tag 0FXR; it is the hypothesis that [Stacks, Tag 01PW] — the section-extension lemma the
  source's proof invokes as Properties, Lemma 28.18.2 — asks of `X`, so it is recorded here
  beside the quasi-compactness.
* `Stacks.AmpleFamilyCartier.quasiSeparatedSpace_compl_of_isAmpleOnComplement` and
  `Stacks.AmpleFamilyCartier.compactSpace_compl_of_isAmpleOnComplement`: the two space-level
  consequences of ampleness on a single complement, unpacked from the packaged hypothesis.
* `Stacks.AmpleFamilyCartier.exists_isAmpleFamily_of_pointwise_affine_nonvanishing`: on a
  quasi-compact scheme, pointwise affine nonvanishing loci of global sections of invertible
  modules assemble into an ample family. This has nothing to do with divisors; it is the step
  that the proof of [Stacks, Tag 0GML] performs inline, factored out because it is also how the
  proof of Tag 0GTS ends.

## Implementation notes

The section-extension step of the source's proof (Properties, Lemma 28.18.2, [Stacks, Tag 01PW])
is run with twisting module `𝒪_X(D i)` and its canonical section, whose nonvanishing locus is
`X ∖ D i` (`Stacks.Divisors.nonvanishingLocus_canonicalSections`). That module has no section
which is nonvanishing at a point of `D i`, so the extension has to be glued over a cover of `X`
on which `𝒪_X(D i)` is merely trivialized, which is
`Stacks.TensorSectionPower.exists_tensorSection_of_compactSpace`.

## References

* [Stacks Project, Tag 0GTS](https://stacks.math.columbia.edu/tag/0GTS)
* [Stacks Project, Tag 0FXR](https://stacks.math.columbia.edu/tag/0FXR)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AmpleFamilyCartier

variable {X : Scheme.{u}}

/-- **The hypothesis of [Stacks, Tag 0GTS] at one index.** The restriction of the
`𝒪_X`-module `L` to the open complement `X ∖ D` of the support of the ideal sheaf `D` is an
invertible module there, and is ample.

The invertibility witness is existentially bound rather than taken as an instance because
`AlgebraicGeometry.Scheme.Modules.IsAmple` consumes it as an instance argument: without it the
tensor powers whose sections ampleness speaks of cannot be formed. The source states the
invertibility of `L` on all of `X`, which implies this; stating it on the complement only is the
weaker hypothesis, so nothing is lost by a consumer that has the stronger one. -/
def IsAmpleOnComplement (D : X.IdealSheafData) (L : X.Modules) : Prop :=
  ∃ h : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Scheme.Opens.toScheme D.support.compl).toRingedSpace.presheaf
      (structureSheafRing (Scheme.Opens.toScheme D.support.compl).toRingedSpace).property
      ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι D.support.compl)).obj L),
    @AlgebraicGeometry.Scheme.Modules.IsAmple (Scheme.Opens.toScheme D.support.compl)
      ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι D.support.compl)).obj L) h

/-- The open complement of the support of `D` is quasi-compact when `L` is ample there: this is
the first conjunct of ampleness ([Stacks, Tag 01PS]). -/
theorem compactSpace_compl_of_isAmpleOnComplement {D : X.IdealSheafData} {L : X.Modules}
    (h : IsAmpleOnComplement D L) :
    CompactSpace (Scheme.Opens.toScheme D.support.compl) :=
  h.2.1

/-- The open complement of the support of `D` is a quasi-separated space when `L` is ample there:
this is `AlgebraicGeometry.Scheme.Modules.quasiSeparatedSpace_of_isAmple`, the quasi-separated
half of the proof of [Stacks, Tag 01PY]. -/
theorem quasiSeparatedSpace_compl_of_isAmpleOnComplement {D : X.IdealSheafData} {L : X.Modules}
    (h : IsAmpleOnComplement D L) :
    QuasiSeparatedSpace (Scheme.Opens.toScheme D.support.compl) := by
  obtain ⟨hinv, hamp⟩ := h
  let _ := hinv
  exact AlgebraicGeometry.Scheme.Modules.quasiSeparatedSpace_of_isAmple _ _ hamp

/-- The intersection of two affine opens of `X` with the open complement of an effective Cartier
divisor `D` is quasi-compact when `L` is ample on that complement. -/
theorem isCompact_inter_inter_compl_of_isAmpleOnComplement {D : X.IdealSheafData}
    {L : X.Modules} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (h : IsAmpleOnComplement D L) (U V : X.affineOpens) :
    IsCompact ((U.1 : Set X) ∩ V.1 ∩ ((D.support.compl : X.Opens) : Set X)) := by
  let W : X.Opens := D.support.compl
  let j : Scheme.Opens.toScheme W ⟶ X := Scheme.Opens.ι W
  have : IsAffineHom j := Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor D hD
  have hEq : j '' ((↑(j ⁻¹ᵁ U.1) : Set (Scheme.Opens.toScheme W)) ∩ ↑(j ⁻¹ᵁ V.1)) =
      (U.1 : Set X) ∩ V.1 ∩ (W : Set X) := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
      exact ⟨⟨hyA, hyB⟩, y.2⟩
    · rintro ⟨⟨hxU, hxV⟩, hxW⟩
      exact ⟨⟨x, hxW⟩, ⟨hxU, hxV⟩, rfl⟩
  rw [← hEq]
  exact ((quasiSeparatedSpace_iff_forall_affineOpens.mp
    (quasiSeparatedSpace_compl_of_isAmpleOnComplement h))
    ⟨_, IsAffineHom.isAffine_preimage U.1 U.2⟩ ⟨_, IsAffineHom.isAffine_preimage V.1 V.2⟩).image
    j.continuous

variable {m : ℕ} {D : Fin m → X.IdealSheafData} {L : Fin m → X.Modules}

/-- **Clause (1) of the ample family of [Stacks, Tag 0FXR] under the hypotheses of
[Stacks, Tag 0GTS]:** a scheme covered by the complements of finitely many divisors, on each of
which some invertible module is ample, is quasi-compact.

The common intersection of the divisors being empty says exactly that the open complements cover
`X`; each complement is quasi-compact because ampleness asserts it; and a finite union of
quasi-compact sets is quasi-compact. Neither the effective Cartier hypothesis nor the
invertibility of `L i` on all of `X` is used. -/
theorem compactSpace_of_isAmpleOnComplement_cover
    (hcover : ∀ x : X, ∃ i : Fin m, x ∈ (D i).support.compl)
    (hample : ∀ i, IsAmpleOnComplement (D i) (L i)) : CompactSpace X := by
  have hU : ⋃ i, (((D i).support.compl : X.Opens) : Set X) = Set.univ :=
    Set.iUnion_eq_univ_iff.mpr hcover
  refine isCompact_univ_iff.mp ?_
  rw [← hU]
  exact isCompact_iUnion fun i =>
    isCompact_iff_compactSpace.mpr (compactSpace_compl_of_isAmpleOnComplement (hample i))

/-- **The scheme of [Stacks, Tag 0GTS] is a quasi-separated space.** This is not part of the
conclusion of [Stacks, Tag 0FXR]; it is the hypothesis that the section-extension lemma
[Stacks, Tag 01PW] of the source's proof asks of `X`.

Two affine opens `U`, `V` of `X` are given, and `U ∩ V` is cut into the finitely many pieces
`U ∩ V ∩ U i` with `U i = X ∖ D i`. The immersion `U i ⟶ X` is affine because the complement of
an effective Cartier divisor is affine over the ambient scheme ([Stacks, Tag 07ZU],
`Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor`), so the preimages of `U` and
`V` in `U i` are affine opens there; `U i` is quasi-separated by ampleness, so their intersection
is quasi-compact, and its homeomorphic image in `X` is the piece. -/
theorem quasiSeparatedSpace_of_isAmpleOnComplement_cover
    (hD : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (D i))
    (hcover : ∀ x : X, ∃ i : Fin m, x ∈ (D i).support.compl)
    (hample : ∀ i, IsAmpleOnComplement (D i) (L i)) : QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  have hU : ⋃ i, (((D i).support.compl : X.Opens) : Set X) = Set.univ :=
    Set.iUnion_eq_univ_iff.mpr hcover
  rw [← Set.inter_univ ((U.1 : Set X) ∩ V.1), ← hU, Set.inter_iUnion]
  exact isCompact_iUnion fun i =>
    isCompact_inter_inter_compl_of_isAmpleOnComplement (hD i) (hample i) U V

/-- **An ample family out of pointwise affine nonvanishing data.** On a quasi-compact scheme,
suppose every point `x` has an invertible module `M x` carrying a global section whose
nonvanishing locus is an affine open containing `x`. Then `X` has an ample family of invertible
modules.

This is [Stacks, Tag 0FXR] repackaged: the family is indexed by the points of `X` and the
exponent is `1`, for which `AlgebraicGeometry.Scheme.tensorPow` is the module itself, so no
comparison of tensor powers is needed. It is the step that the proof of [Stacks, Tag 0GML]
(`AlgebraicGeometry.exists_isAmpleFamily_of_isRegular`) performs inline, factored out here
because it is also how the proof of [Stacks, Tag 0GTS] ends: what that proof produces at each
point is a global section of `(L i)^{⊗ n} ⊗ 𝒪_X(N · D i)` with affine nonvanishing locus, which
is exactly this datum.

No `@[stacks]` attribute is attached: Tag 0FXR is the *definition*
`AlgebraicGeometry.Scheme.IsAmpleFamily`, which already carries it. -/
theorem exists_isAmpleFamily_of_pointwise_affine_nonvanishing (X : Scheme.{u}) [CompactSpace X]
    (hpt : ∀ x : X, ∃ (M : X.Modules)
      (_ : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
      (σ : M.sections) (V : X.Opens),
      (V : Set X) = X.nonvanishingSet M σ ∧ x ∈ V ∧ IsAffineOpen V) :
    ∃ (I : Type u) (M : I → X.Modules), X.IsAmpleFamily M := by
  choose M hMinv σ V hV hxV hVaff using hpt
  exact ⟨X, M, hMinv, inferInstance,
    fun x => ⟨x, 1, le_rfl, σ x, V x, hV x, hxV x, hVaff x⟩⟩

end Stacks.AmpleFamilyCartier

end
