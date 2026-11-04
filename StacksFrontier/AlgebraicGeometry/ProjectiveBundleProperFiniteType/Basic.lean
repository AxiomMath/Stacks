module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Proper
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.VeryAmple
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
import StacksCore.Tactic.StacksAttribute

/-!
# The projective bundle of a quasi-coherent module of finite type is proper over its base

For a scheme `X` and a quasi-coherent `𝒪_X`-module `ℰ` **of finite type**, the projection

`π : 𝐏(ℰ) = Proj_X(Sym(ℰ)) ⟶ X`

is proper. `StacksFrontier/AlgebraicGeometry/ProjectiveBundle/Proper.lean` proves this for `ℰ`
finite locally *free*; the finite-type hypothesis of Tag 01W8 is weaker, and it is the one that
`AlgebraicGeometry.IsProjective` quantifies over, so that file's result does not apply to a
projective morphism. What is added here is exactly the one chartwise input that separates the two
hypotheses, and the three consequences for `AlgebraicGeometry.IsProjective` that the weaker
hypothesis unlocks.

## Main results

* `AlgebraicGeometry.SheafOfModules.exists_finset_span_of_isFiniteType`: the sections of a
  quasi-coherent module of finite type over an affine open are spanned by finitely many of them.
* `Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType`: **the projection of the
  projective bundle of a quasi-coherent module of finite type is proper.**
* `AlgebraicGeometry.isProper_schemeProjectiveBundleToBase`: the same for the other of the two
  presentations of `𝐏(ℰ)` that this repository carries, the one
  `AlgebraicGeometry.IsProjective` is stated at.
* `AlgebraicGeometry.IsProjective.isProper` and
  `AlgebraicGeometry.isProper_of_isLocallyProjective`: **Tag 01WC**, a locally projective morphism
  is proper.
* `AlgebraicGeometry.IsProjective.exists_isRelativelyVeryAmple`: the source of a projective
  morphism carries an `f`-very ample invertible module, by the definition of Tag 01VM.
* `AlgebraicGeometry.IsProjective.isQuasiProjective`: **Tag 07RL**, a projective morphism is
  quasi-projective, with no hypothesis on the base. This is also **clause (5) of
  [Stacks, Tag 0B43]**, which the source proves by citing Tag 07RL, and it carries that tag's
  attribute too.

## Where the finite-type hypothesis enters

`Stacks.RelativeProj.Situation.isProper_relativeProjToBase` reduces properness of the structure
morphism of a relative `Proj` to two conditions at every affine open `U` of the base: that the
degree-zero part of the graded ring of sections over `U` is `Γ(X, U)`, and that the ring of
sections over `U` is a finite type algebra over that degree-zero part. For `Sym(ℰ)` the first is
unconditional and the second splits into generation in degree one, which is also unconditional,
and the statement that the degree-one local sections over `U` — that is, `Γ(ℰ, U)` — are spanned
by finitely many of them. That last statement is the only place a finiteness hypothesis on `ℰ` is
used.

For `ℰ` finite locally free it holds only on a cover of the base, because the local free
presentations of `ℰ` live on a cover by arbitrary opens; that is why
`Stacks.RelativeProj.isProper_projectiveBundleToBase` has to go through the cover-indexed
`isProper_relativeProjToBase_of_cover`. For `ℰ` quasi-coherent of finite type it holds at
**every** affine open, by `AlgebraicGeometry.moduleFinite_sections_on_affine`: `Γ(ℰ, U)` is then a
finite `Γ(X, U)`-module outright, and a finite module is spanned by a finite subset. So the
all-affine-opens form of the properness criterion applies directly.

## Why two presentations appear

`AlgebraicGeometry.IsProjective` asks for a closed immersion into
`Stacks.SymGraded.schemeProjectiveBundle`, the relative `Proj` of `Sym(ℰ)` glued through
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData`, while the properness criterion above
lives on `Stacks.RelativeProj.Situation`, which glues the same charts through
`Stacks.RelativeProj.Data`. The two glueings are identified over the base by
`AlgebraicGeometry.projectiveBundlePresentationsAgree`, which is proved and unconditional, so
properness transports along an isomorphism over the base.

## The three consequences

`AlgebraicGeometry.IsProjective.isProper` is immediate: a closed immersion is proper and
properness is stable under composition.

`AlgebraicGeometry.IsProjective.exists_isRelativelyVeryAmple` needs no properness at all, only
the observation that `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` asks for an *immersion* into
`𝐏(ℰ)` over the base with `L ≅ i^* 𝒪_{𝐏(ℰ)}(1)`, and that a closed immersion is an immersion:
the module is `i^* 𝒪_{𝐏(ℰ)}(1)` itself and the isomorphism is the identity.

`AlgebraicGeometry.IsProjective.isQuasiProjective` combines the two. Properness gives finite
type; Tag 01VN turns the relatively very ample module into a relatively ample one, which is what
`AlgebraicGeometry.IsQuasiProjective` asks for. The source states Tag 07RL with no hypothesis on
the base and that is how it comes out here.

## Implementation notes

`Stacks.SymGraded.IsQuasicoherentPieces` is a `Prop`, so the projective bundle built from the
proof of it that `AlgebraicGeometry.IsProjective` carries is, by proof irrelevance, the same term
as the one built from `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`. That is what
makes `(Stacks.SymGraded.schemeProjectiveBundle E hqc).scheme` and
`(relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).scheme` the same scheme. They are
not *syntactically* the same, and instance synthesis does not unfold the definitions between
them, so the closed immersion is retyped by an explicit `let` before the invertibility of the
pullback of the twist and the immersion instance are asked for.

## References

* [Stacks Project, Tag 0800](https://stacks.math.columbia.edu/tag/0800)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
* [Stacks Project, Tag 0B43](https://stacks.math.columbia.edu/tag/0B43)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : Scheme.{u}}

/-- **The sections of a quasi-coherent module of finite type over an affine open are spanned by
finitely many of them.** This is `AlgebraicGeometry.moduleFinite_sections_on_affine` read as a
spanning statement: a finite module over a ring has a finite spanning subset.

It is the finite-type counterpart of
`AlgebraicGeometry.SheafOfModules.exists_affineOpen_finset_span`, which proves the same spanning
for a finite locally free module and only at *some* affine open around each point. -/
theorem exists_finset_span_of_isFiniteType (E : X.Modules) [E.IsQuasicoherent]
    [E.IsFiniteType] (V : X.Opens) (hV : IsAffineOpen V) :
    ∃ g : Finset (E.val.obj (op V)),
      Submodule.span (X.ringCatSheaf.obj.obj (op V)) (g : Set (E.val.obj (op V))) = ⊤ := by
  have := AlgebraicGeometry.moduleFinite_sections_on_affine E V hV
  obtain ⟨g, hg⟩ := Module.finite_def.mp this
  exact ⟨g, hg⟩

end AlgebraicGeometry.SheafOfModules

namespace Stacks.RelativeProj

variable (X : Scheme.{u}) (E : X.Modules)

/-- **The projection `π : 𝐏(ℰ) ⟶ X` of the projective bundle of a quasi-coherent module of
finite type is proper.**

This is the properness clause of Stacks 0800 for the graded algebra `Sym(ℰ)`, under the
finiteness hypothesis of Tag 01W8 rather than finite local freeness. Both chartwise conditions
of `Stacks.RelativeProj.Situation.isProper_relativeProjToBase` now hold at *every* affine open of
the base: the degree-zero one is unconditional, and the finite-type one follows from generation
in degree one together with
`AlgebraicGeometry.SheafOfModules.exists_finset_span_of_isFiniteType`. -/
@[stacks 0800 "proper, for the projective bundle of a quasi-coherent module of finite type",
  ega "II 3.4.1" "special case"]
theorem isProper_projectiveBundleToBase_of_isFiniteType [E.IsQuasicoherent] [E.IsFiniteType] :
    IsProper (projectiveBundleToBase X E) := by
  refine (symmetricSituationOfQuasicoherent X E).isProper_relativeProjToBase
    (fun V : X.affineOpens => isIso_sectionRingZeroMap_symmetricSituationOfQuasicoherent X E V.1)
    fun V : X.affineOpens => ?_
  obtain ⟨g, hg⟩ := exists_finset_span_sectionPieces_one X E V.1
    (AlgebraicGeometry.SheafOfModules.exists_finset_span_of_isFiniteType E V.1 V.2)
  exact (symmetricSituationOfQuasicoherent X E).finiteType_sectionRing_of_adjoin_eq_top V.1
    (adjoin_sectionRingGrading_one_eq_top_symmetricSituationOfQuasicoherent X E V.1 V.2) g hg

end Stacks.RelativeProj

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **The projection of the projective bundle of a quasi-coherent module of finite type is
proper**, at the `Stacks.SymGraded.schemeProjectiveBundle` presentation that
`AlgebraicGeometry.IsProjective` is stated at.

`AlgebraicGeometry.projectiveBundlePresentationsAgree` identifies that presentation with
`Stacks.RelativeProj.projectiveBundle` over the base, and properness is stable under composition
with an isomorphism. -/
theorem isProper_schemeProjectiveBundleToBase (E : S.Modules) [E.IsQuasicoherent]
    [E.IsFiniteType] (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) :
    IsProper (Stacks.SymGraded.schemeProjectiveBundle E hqc).toBase := by
  obtain ⟨b, hb⟩ := projectiveBundlePresentationsAgree E hqc
  rw [← hb]
  have := Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType S E
  infer_instance

/-- **The source of a projective morphism carries an `f`-very ample invertible module.** This is
the source's "follows directly from the definitions": relative very ampleness, [Stacks, Tag
01VM], asks for an *immersion* `i : X ⟶ 𝐏(ℰ)` over `S` with `L ≅ i^* 𝒪_{𝐏(ℰ)}(1)`, and the
closed immersion witnessing projectivity is one. The module is the pullback of the twist itself,
and the isomorphism is the identity. -/
theorem IsProjective.exists_isRelativelyVeryAmple {f : X ⟶ S} (hf : IsProjective f) :
    ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
      letI : Stacks.Ample.IsInvertibleModule X L := hL
      Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L := by
  obtain ⟨E, hq, hft, hqc, i, hi, hif⟩ := hf
  have := hq
  let i' : X ⟶ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
    (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).scheme := i
  have hi' : IsClosedImmersion i' := hi
  have : IsImmersion i' := inferInstance
  exact ⟨(Scheme.Modules.pullback i').obj (Stacks.Tag01VMVeryAmple.twistOne E), inferInstance,
    Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_immersion _ _ E i' inferInstance hif
      (Iso.refl _)⟩

/-- **Stacks Project, Tag 07RL. A projective morphism is quasi-projective.** Properness supplies
the finite-type half, and the `f`-very ample module of
`AlgebraicGeometry.IsProjective.exists_isRelativelyVeryAmple` is `f`-ample by [Stacks, Tag 01VN],
`f` being quasi-compact. No hypothesis on the base is used, which is how the source states the
tag.

It is also **clause (5) of [Stacks, Tag 0B43]**, which the source proves by citing Tag 07RL:
membership of `X` in the category `QP_S` of that tag is
`AlgebraicGeometry.IsQuasiProjective X.hom`, so "if `X ⟶ S` is projective then `X ∈ QP_S`" is
this statement. Tag 0B43's hypothesis that `S` carries an ample invertible sheaf is not needed
for it and is not assumed. -/
@[stacks 07RL,
  stacks 0B43 "part (5), a projective morphism is in `QP_S`; the source's hypothesis that `S` \
has an ample invertible sheaf is not needed, Tag 07RL needing no such hypothesis"]
theorem IsProjective.isQuasiProjective {f : X ⟶ S} (hf : IsProjective f) :
    IsQuasiProjective f := by
  have hp := hf.isProper
  obtain ⟨L, hL, hvamp⟩ := hf.exists_isRelativelyVeryAmple
  have : Stacks.Ample.IsInvertibleModule X L := hL
  exact ⟨⟨inferInstance, inferInstance⟩, L, hL,
    (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mp
      (Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple f L inferInstance hvamp)⟩

end AlgebraicGeometry

end
