module

public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Reduction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology

/-!
# Tag 09N8 from the vanishing of absolute cohomology over an affine

All names in this file live in the namespace
`Stacks.AlgebraicGeometry.OneDimensionalLocal`. `isZero_rightDerived_pushforward_of_isRetrocompact`
proves [Stacks, Tag 09N8] from three hypotheses, of which
`isZero_rightDerived_pushforward_of_flatBaseChangeVanishing` discharges two, leaving
`FlatBaseChangeVanishing` — the vanishing half of [Stacks, Tag 02KH] part (1) — alone. That
remaining hypothesis is *relative*: it quantifies over all cartesian squares with a flat base
change and a quasi-compact quasi-separated morphism, and so over an arbitrary base scheme.

This file replaces it by an *absolute* hypothesis about one class of schemes: the vanishing of
`Hⁿ(V, 𝒢)` in positive degrees for a quasi-coherent `𝒢` on a quasi-compact open subscheme `V`
of an affine scheme all of whose local rings are Noetherian of dimension at most one. No
cartesian square, no base change and no second scheme occur in it.

This is a change of *shape*, not of strength, and it is worth saying so plainly: the new
hypothesis also *follows* from the unconditional tag — by [Stacks, Tag 01XK] applied to the
quasi-compact open immersion, an implication not formalized here — so it is equivalent to the tag
rather than weaker than it. What it buys is that the residue no longer mentions a general base,
and so no longer needs
[Stacks, Tag 02KH] part (1) in positive degrees, which belongs to the chapter on cohomology of
schemes and is not available here.

The reduction is the source's own first move, "we may check the vanishing at stalks" followed by
"the statement is local on the base", carried out with the scheme-level form of
[Stacks, Tag 01E5] and with [Stacks, Tags 01XJ, 01XK]:

* a sheaf of modules vanishes as soon as all its stalks do, and the stalk at `y` vanishes as soon
  as the restriction to an open containing `y` does;
* over an affine open `W ∋ y`, formation of higher direct images commutes with restriction
  ([Stacks, Tag 01E5]), so `(R ᵖ U.ι_* ℱ)|_W` is `R ᵖ (U.ι ∣_ W)_*` of the restriction of `ℱ`;
* `U.ι ∣_ W` is a quasi-compact open immersion into the affine scheme `W`, so by
  [Stacks, Tags 01XK, 01XJ] — through `isZero_rightDerivedPlus_pushforward_of_isZero_cohomology`
  of `Stacks.AlgebraicGeometry.TopDegreeBaseChange` — its higher direct image vanishes as soon as
  `Hᵖ` of its source does.

What is *not* proved here is the hypothesis itself. The source proves it by passing to the local
ring, which is where flat base change enters; the argument that avoids flat base change is the
second paragraph of the proof of [Stacks, Tag 02KH]: a quasi-compact open of an affine scheme is
a finite union of principal opens whose finite intersections are again principal, hence affine,
so [Stacks, Tag 01XD] computes `Hᵖ` by the Čech complex of that covering, and the Čech complex of
the covering base-changed to a localization of the ring is the localization of the Čech complex —
degreewise by
`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange`, which is
[Stacks, Tag 02KH] part (2) in degree zero, the Čech terms being finite products of sections over
affine opens; and in cohomology because a localization is flat. Over the local ring the open
becomes affine by `AlgebraicGeometry.isAffineOpen_of_krullDimLE_one`, so its Čech cohomology
vanishes by [Stacks, Tag 01XB]. That is the remaining work, and it is work inside this chapter
rather than a statement about a general base.

## Main definitions

* `CohomologyVanishingQuasiCompactOpenInAffine`: the absolute hypothesis described above.

## Main results

* `isZero_rightDerived_pushforward_of_cohomologyVanishing`: [Stacks, Tag 09N8] from that
  hypothesis alone.

No `@[stacks 09N8]` attribute is attached: the tag asserts the conclusion unconditionally, and one
hypothesis remains.

## References

* [Stacks Project, Tag 09N8](https://stacks.math.columbia.edu/tag/09N8)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace Stacks.AlgebraicGeometry.OneDimensionalLocal

attribute [local instance] HasDerivedCategory.standard

/-! ### Local rings of an open subscheme -/

/-- **The local rings of an open subscheme are the local rings of the ambient scheme.** This is
`AlgebraicGeometry.Scheme.Opens.stalkIso`, read as a ring isomorphism and used to transport the
two hypotheses of [Stacks, Tag 09N8] on the local rings from `X` to an open subscheme. -/
theorem isNoetherianRing_stalk_opens {X : Scheme.{u}} (W : X.Opens)
    (h : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x)) (a : W.toScheme) :
    IsNoetherianRing (W.toScheme.presheaf.stalk a) :=
  have := h a.1
  isNoetherianRing_of_ringEquiv _ (W.stalkIso a).commRingCatIsoToRingEquiv.symm

/-- **The local rings of an open subscheme have the dimensions of the local rings of the ambient
scheme.** The companion of `isNoetherianRing_stalk_opens` for the dimension hypothesis. -/
theorem krullDimLE_stalk_opens {X : Scheme.{u}} (W : X.Opens)
    (h : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x)) (a : W.toScheme) :
    Ring.KrullDimLE 1 (W.toScheme.presheaf.stalk a) := by
  rw [Ring.krullDimLE_iff,
    ringKrullDim_eq_of_ringEquiv (W.stalkIso a).commRingCatIsoToRingEquiv]
  exact Ring.krullDimLE_iff.mp (h a.1)

/-! ### The absolute hypothesis -/

/-- **Positive cohomology of a quasi-coherent module on a quasi-compact open subscheme of an
affine scheme with Noetherian one-dimensional local rings vanishes.**

This is the affine-base, absolute-cohomology content of [Stacks, Tag 09N8]: the open immersion
`q : T ⟶ A` is quasi-compact, `A` is affine, and the local rings of `A` are Noetherian of
dimension at most one; the conclusion is the vanishing of `Hⁿ(T, 𝒢)` for `n > 0`, spelled with
the right derived functors of `Stacks.Cohomology.AffineBase.moduleGlobalSections` in which
[Stacks, Tag 01XK] is stated.

Nothing relative occurs: there is no cartesian square, no flat morphism and no higher direct
image. Contrast `FlatBaseChangeVanishing`, which quantifies over all cartesian squares with a
flat base change and a quasi-compact quasi-separated morphism. -/
def CohomologyVanishingQuasiCompactOpenInAffine : Prop :=
  ∀ {T A : Scheme.{u}} (q : T ⟶ A), IsOpenImmersion q → QuasiCompact q → IsAffine A →
    (∀ a : A, IsNoetherianRing (A.presheaf.stalk a)) →
    (∀ a : A, Ring.KrullDimLE 1 (A.presheaf.stalk a)) →
      ∀ (G : T.Modules), G.IsQuasicoherent → ∀ n : ℕ, 0 < n →
        IsZero (((moduleGlobalSections T).rightDerivedPlus (n : ℤ)).obj G)

/-! ### Tag 09N8 from the absolute hypothesis -/

/-- **The stalk of `R ᵖ U.ι_* ℱ` vanishes at a point lying in an affine open, granted the
absolute hypothesis.** Over an affine open `W` of `X`, formation of the higher direct image
commutes with restriction ([Stacks, Tag 01E5]), and `U.ι ∣_ W` is a quasi-compact open immersion
into the affine scheme `W`, so [Stacks, Tags 01XK, 01XJ] turn the vanishing of `Hᵖ` of its source
into the vanishing of its higher direct image. -/
theorem isZero_stalk_rightDerived_pushforward_of_cohomologyVanishing
    (hcoh : CohomologyVanishingQuasiCompactOpenInAffine.{u})
    (X : Scheme.{u}) (U : X.Opens) (hqc : QuasiCompact U.ι)
    (h_noetherian : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x))
    (h_dimension : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (F : U.toScheme.Modules) (hF : F.IsQuasicoherent) (p : ℕ) (hp : 0 < p)
    (W : X.Opens) (hW : IsAffineOpen W) (y : X) (hyW : y ∈ W) :
    IsZero ((((Scheme.Modules.pushforward U.ι).rightDerived p).obj F).presheaf.stalk y) := by
  have : IsAffine W.toScheme := hW
  have : QuasiCompact (U.ι ∣_ W) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict U.ι W).flip hqc
  have hFq : ((Scheme.Modules.restrictFunctor (U.ι ⁻¹ᵁ W).ι).obj F).IsQuasicoherent := by
    have := hF; infer_instance
  refine isZero_stalk_of_isZero_restrict W _ y hyW ?_
  refine IsZero.of_iso ?_ ((higherDirectImageRestrictIso U.ι W p).app F).symm
  refine (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
    (Scheme.Modules.pushforward (U.ι ∣_ W)) p _).2 ?_
  exact isZero_rightDerivedPlus_pushforward_of_isZero_cohomology (U.ι ∣_ W) (p : ℤ) _
    (hcoh (U.ι ∣_ W) inferInstance inferInstance inferInstance
      (isNoetherianRing_stalk_opens W h_noetherian) (krullDimLE_stalk_opens W h_dimension)
      _ hFq p hp)

/-- **[Stacks, Tag 09N8] from the vanishing of absolute cohomology over an affine.** Let `X` be a
scheme all of whose local rings are Noetherian of dimension at most one, let `U ⊆ X` be a
retrocompact open and let `ℱ` be a quasi-coherent `𝒪_U`-module. Then `R ᵖ U.ι_* ℱ = 0` for every
`p > 0`, provided `Hᵖ` vanishes on quasi-compact opens of affine schemes with Noetherian
one-dimensional local rings.

This is `isZero_rightDerived_pushforward_of_isRetrocompact` with all three of its hypotheses
replaced by the single absolute hypothesis
`CohomologyVanishingQuasiCompactOpenInAffine`: the vanishing is checked at stalks, and at each
point in an affine open `W` the question becomes the vanishing of `Hᵖ(U ∩ W, ℱ)`. -/
theorem isZero_rightDerived_pushforward_of_cohomologyVanishing
    (hcoh : CohomologyVanishingQuasiCompactOpenInAffine.{u})
    (X : Scheme.{u}) (U : X.Opens) (hU : IsRetrocompact (U : Set X))
    (h_noetherian : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x))
    (h_dimension : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (F : U.toScheme.Modules) (hF : F.IsQuasicoherent)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((Scheme.Modules.pushforward U.ι).rightDerived p).obj F) := by
  have hqc : QuasiCompact U.ι :=
    quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hU)
  refine isZero_of_forall_isZero_stalk _ fun y ↦ ?_
  exact isZero_stalk_rightDerived_pushforward_of_cohomologyVanishing hcoh X U hqc
    h_noetherian h_dimension F hF p hp
    (X.affineCover.f (X.affineCover.idx y)).opensRange (isAffineOpen_opensRange _) y
    (X.affineCover.covers y)

end Stacks.AlgebraicGeometry.OneDimensionalLocal

end
