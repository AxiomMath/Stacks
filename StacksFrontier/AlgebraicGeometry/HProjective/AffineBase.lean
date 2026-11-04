module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.VeryAmplePowersUniformDegree.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.AmpleRoute
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjective

/-!
# Stacks Tag 087S part (2) over an affine base, from Stacks Tag 01VS alone

`StacksFrontier/AlgebraicGeometry/HProjective/QuasiProjective.lean` proves part (2) of Stacks Tag
087S from the hypothesis `Stacks.HProjective.ProjectiveCompactification`. That hypothesis is
**equivalent to the conclusion it is used to prove**:
`Stacks.QuasiProjectiveCompactification.projectiveCompactification_iff` derives it back from part
(2) using half 2 of Tag 07RM's own proof. So that reduction advances nothing, and part (2) needs a
hypothesis that is genuinely upstream of it.

This file supplies one over an **affine** base. The single input is Stacks Tag 01VS, in the form
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`, whose own remaining obligation is
Stacks Tag 01NE — the morphism to projective space attached to a generating family of global
sections — which is absent from this repository and from Mathlib. Tag 01VS is not equivalent to
part (2): it is a statement about *absolutely* ample modules, and nothing in either direction
connects the two.

## The route, and where the ample sheaf on the base goes

Over an affine base the ample invertible sheaf on `S` carries no information — `𝒪_S` is
ample on an affine scheme — and it is **relative** ampleness that does the work. The point is
that over an affine base relative ampleness *is* absolute ampleness:
`Stacks.RelativeAmple.IsRelativelyAmple` asserts ampleness of `L` restricted to `f⁻¹(V)` for every
affine open `V ⊆ S`, and when `S` is affine `V = ⊤` is admissible and `f⁻¹(⊤) = ⊤` on the nose. So
the ampleness hypothesis of Tag 01VS is available for `f` itself, with no covering and no glueing
step — and glueing, Stacks Tag 01VR, is exactly what the general base costs. Tag 01VR cannot even
be stated here; see `StacksFrontier/AlgebraicGeometry/VeryAmplePowersUniformDegree/Basic.lean`.

What remains is to get from ampleness on the open subscheme `⊤` to ampleness on `X`, which is
`Stacks.HProjective.isAmple_of_isAmple_restrictTop` below.

## The ⊤-restriction transport

`StacksFrontier/AlgebraicGeometry/AmpleGlobalGeneration/Basic.lean` notes that transporting a
statement across `F.restrict (⊤ : X.Opens).ι ≅ F` is not done there. For ampleness it is done
here, and it needs no new mathematics — only the observation that `(⊤ : X.Opens).ι` is
`AlgebraicGeometry.Scheme.topIso`, an **isomorphism**, so that the transport runs in the direction
the repository's pullback theorem already goes:

* `Stacks.SectionExtension.isAmple_pullbackModule` carries ampleness *forward* along a
  quasi-compact immersion. Applied to `X.topIso.inv : X ⟶ ↑⊤` — an isomorphism, hence both — it
  carries ampleness on `↑⊤` back to `X`, at the module `X.topIso.inv^* (⊤.ι^* L)`.
* `Stacks.HProjective.topPullbackIso` identifies that module with `L`, by Mathlib's
  `AlgebraicGeometry.Scheme.Modules.pullbackComp` and `pullbackId` together with
  `X.topIso.inv ≫ ⊤.ι = 𝟙 X`.
* `Stacks.RelativeVeryAmple.isAmple_congr` moves ampleness across that isomorphism.

## Main definitions

* `Stacks.HProjective.topPullbackIso`: `X.topIso.inv^* (⊤.ι^* L) ≅ L`.

## Main results

* `Stacks.HProjective.isAmple_of_isAmple_restrictTop`: **the ⊤-restriction transport of
  ampleness.** If the restriction of `L` to the open subscheme `⊤` is ample, then `L` is ample.
* `Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine`: **over an affine base, relatively
  ample implies ample.** No hypothesis beyond affineness of the base.
* `Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffine`: **part (2) of Stacks
  Tag 087S over an affine base, from `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`
  alone.**
* `Stacks.HProjective.projectiveCompactification_of_isAffine_gap`: the same conclusion written as
  the conclusion of `Stacks.HProjective.ProjectiveCompactification` restricted to affine bases, so
  that what this file buys over `QuasiProjective.lean` is visible as a statement.

## Implementation notes

**No Stacks tag attribute is attached anywhere in this file, and in particular not Stacks Tag
087S.** The tag states part (2) for an arbitrary base carrying an ample invertible sheaf, and
`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffine` carries two hypotheses
the tag lacks: affineness of the base, and
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`.

**The two spellings of the module pullback are the same functor.** These files write the pullback
both as `AlgebraicGeometry.Scheme.Modules.pullback f` (in the ampleness-to-projective-space files)
and as `RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom` (in the relative-ampleness
files). In fact `Scheme.Modules.pullback f = modulePullback f.toLRSHom.toShHom`
holds by `rfl`, so Mathlib's functoriality isomorphisms for the first apply verbatim to the
second, and `Stacks.AmpleLocallyClosed.pullbackModule` — which is the second — needs no bridge.

**`f ⁻¹ᵁ ⊤ = ⊤` holds by `rfl`**, so no transport across an equality of open subschemes appears
in `Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine`; the term supplied by relative
ampleness at `V = ⊤` already has the type the transport consumes.

## References

* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.HProjective

/-! ### The ⊤-restriction transport of ampleness -/

/-- **`X.topIso.inv^* (⊤.ι^* L) ≅ L`.** The open immersion of `⊤ : X.Opens` is
`AlgebraicGeometry.Scheme.topIso`, an isomorphism, and `X.topIso.inv ≫ ⊤.ι = 𝟙 X`; so the
composite pullback is the pullback along the identity, which is the identity functor. The two
isomorphisms used are Mathlib's `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackId`. -/
def topPullbackIso (X : Scheme.{u}) (L : X.Modules) :
    Stacks.AmpleLocallyClosed.pullbackModule X.topIso.inv
      (Stacks.AmpleLocallyClosed.pullbackModule (⊤ : X.Opens).ι L) ≅ L := by
  refine (Scheme.Modules.pullbackComp X.topIso.inv (⊤ : X.Opens).ι).app L ≪≫ ?_
  refine eqToIso ?_ ≪≫ (Scheme.Modules.pullbackId X).app L
  rw [show X.topIso.inv ≫ (⊤ : X.Opens).ι = 𝟙 X from X.topIso.inv_hom_id]

/-- **The ⊤-restriction transport of ampleness.** If the restriction of `L` to the open subscheme
`⊤ : X.Opens` is ample, then `L` is ample on `X`.

`Stacks.SectionExtension.isAmple_pullbackModule` carries ampleness forward along a quasi-compact
immersion; `X.topIso.inv` is an isomorphism, so it is one, and the resulting module is identified
with `L` by `Stacks.HProjective.topPullbackIso`. -/
theorem isAmple_of_isAmple_restrictTop {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (h : Stacks.Ample.IsAmple (⊤ : X.Opens).toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule (⊤ : X.Opens).ι L)) :
    Stacks.Ample.IsAmple X L :=
  (Stacks.RelativeVeryAmple.isAmple_congr _ _ (topPullbackIso X L)).mp
    (Stacks.SectionExtension.isAmple_pullbackModule X.topIso.inv _ h
      (Or.inl ⟨inferInstance, inferInstance⟩))

/-! ### Over an affine base, relatively ample is ample -/

/-- **Over an affine base, a relatively ample invertible module is ample.** Stacks Tag 01VH asks
for ampleness of `L` restricted to `f⁻¹(V)` for every affine open `V` of `S`; when `S` is affine
`V = ⊤` is admissible, `f ⁻¹ᵁ ⊤ = ⊤` by `rfl`, and
`Stacks.HProjective.isAmple_of_isAmple_restrictTop` removes the restriction.

This is the step that makes the ampleness hypothesis of Stacks Tag 01VS available for `f` itself,
with no affine covering of the base and hence no appeal to the glueing step Stacks Tag 01VR. -/
theorem isAmple_of_isRelativelyAmple_of_isAffine {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) : Stacks.Ample.IsAmple X L :=
  isAmple_of_isAmple_restrictTop L (hL.2 (⊤ : S.Opens) (isAffineOpen_top S))

/-! ### Part (2) over an affine base -/

/-- **Part (2) of Stacks Tag 087S over an affine base, from Stacks Tag 01VS alone**: a
quasi-projective morphism to an affine scheme is H-quasi-projective.

Over an affine base the relatively ample module of quasi-projectivity is absolutely ample, by
`Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine`, so
`Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple` applies directly. The degree
bound it needs is Tag 01VS at the single situation `(X, S, f, L)`, which
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` supplies;
`Stacks.PowerFamilyBridge.immersionTwistGap_iff` moves it between the two tensor-power families.

**This is not Stacks Tag 087S part (2)** and carries no tag: the base is assumed affine, and
Tag 01VS is assumed. What it buys over
`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective` is that the hypothesis is upstream of
the conclusion rather than equivalent to it — see the module documentation. -/
theorem isHQuasiProjective_of_isQuasiProjective_of_isAffine
    (hgap : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u}) {X S : Scheme.{u}}
      [IsAffine S]
    (f : X ⟶ S) (hf : IsQuasiProjective f) : IsHQuasiProjective f := by
  obtain ⟨⟨hft, hqc⟩, L, hLinv, hLamp⟩ := hf
  have := hLinv
  have hamp : Stacks.Ample.IsAmple X L := isAmple_of_isRelativelyAmple_of_isAffine f L hLamp
  have := hft
  exact Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple f L hamp hqc
    ((Stacks.PowerFamilyBridge.immersionTwistGap_iff f L).mpr (hgap X S f L))

/-- **The conclusion of `Stacks.HProjective.ProjectiveCompactification` over an affine base**, from
Stacks Tag 01VS alone. Stated so that what this file buys over
`StacksFrontier/AlgebraicGeometry/HProjective/QuasiProjective.lean` is itself a statement: there the
factorisation is *assumed*, and the assumption is equivalent to part (2); here it is *derived*,
for an affine base, from a hypothesis about absolute ampleness.

The open immersion is produced by
`exists_isOpenImmersion_isHProjective_of_isHQuasiProjective`, half 2 of Tag 07RM's
own proof. -/
theorem projectiveCompactification_of_isAffine_gap
    (hgap : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u}) {X S : Scheme.{u}}
      [IsAffine S]
    (f : X ⟶ S) (hf : IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (j : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion j ∧ j ≫ p = f ∧ IsHProjective p := by
  obtain ⟨X', j, p, hj, hp, hjp⟩ :=
    QuasiProjectiveCompactification.exists_isOpenImmersion_isHProjective_of_isHQuasiProjective
      (isHQuasiProjective_of_isQuasiProjective_of_isAffine hgap f hf)
  exact ⟨X', j, p, hj, hjp, hp⟩

end Stacks.HProjective

end
