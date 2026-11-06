module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Recompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffine
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineSupplement

/-!
# The completion of a formal algebraic space along a closed subset is a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` with reduction `i : X_red ⟶ X` and let `T ⊆ |X_red|` be a closed subset. **Stacks 0GVR**
says that the completion `X_{/T}` of `X` along `T` — the functor sending an object `U` of the
big fppf site of `S` to the morphisms `f : U ⟶ X` with `f(|U|) ⊆ T` — is a formal algebraic
space over `S`.

The completion is the datum `AlgebraicGeometry.FormalSpace.completionAlong` of Stacks
0GVS, the fppf sheafification of that subfunctor, so nothing is redefined here.

The argument is the one of the source. An atlas `{g_k : X_k ⟶ X}` of `X` as in Definition
0AIM is base changed along the inclusion `X_{/T} ⟶ X`. The completion square of Stacks 0GVT,
`AlgebraicGeometry.Space.isPullback_completionSheafMapULift`, identifies the base change
`X_k ×_X X_{/T}` with the completion `(X_k)_{/T_k}` of the chart along the inverse image
`T_k = |g_k|⁻¹ T`, which is closed because a morphism of fppf sheaves is continuous on points.
Each member of the base-changed family is therefore representable étale over `X_{/T}`, the
family is jointly surjective because `{g_k}` is, and each member is an affine formal algebraic
space by clause (1) of Stacks 0GVV. That is the atlas of Definition 0AIM for `X_{/T}`.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheafULift`: the completion
  of a formal algebraic space along a closed set of its own points is a formal algebraic space.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionAlong'`: **Stacks 0GVR**, the
  same statement for the completion along a closed subset of a reduction.

## What is assumed

One hypothesis is carried, `hset`, the set-theoretic condition of Stacks 0AIS for `X_{/T}`. It
is a hypothesis for the same reason as in
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover` (Stacks 0AJ1) and
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit` (Stacks 0GVM): the
condition is a clause of the definition of a formal algebraic space — Stacks 0AIM asks for a
family as in its (1), (2), (3) "*and `X` satisfies a set theoretic condition (see
Remark 0AIS)*", so it is the source's own clause and not a convention of this library — and it
does not follow from the corresponding conditions on the members of a covering family. The
source does not verify it here either: the proof of Stacks 0GVR exhibits a covering as in
Definition 0AIM and stops, which is the chapter's posture, explicit in the opening words of
Stacks 0AIR ("Modulo set theoretic issues …"). Carrying it as a named hypothesis is this
library making that gap visible, and it is the only residue here.

It cannot be discharged the way it is for an *affine* formal algebraic space: the argument of
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSheafULift` gets the
surjection onto the completion from the condition for `X` itself, but turns it into the full
condition through
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit_of_representable_epi`,
whose kernel-pair half needs the representability of the diagonal of a *directed colimit of
affines along thickenings* (Stacks 0AI8). A formal algebraic space is not such a colimit.

Nothing else is assumed.

* The affine case — clause (1) of Stacks 0GVV, which the source's proof invokes as Stacks
  0GVQ — is *not* a hypothesis: it is
  `AlgebraicGeometry.FormalSpace.completionOfAffineIsAffine` of
  `StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffine`, in the ambient spelling
  `AlgebraicGeometry.FormalSpace.CompletionOfAffineIsAffine` that the base-changed charts
  supply.
* Closedness of `T` is read in `|X_red|`, as the source states it. The proof uses it in `|X|`,
  for the image of `T` under the inclusion of the reduction, and that is no second hypothesis:
  the inclusion of a reduction is a homeomorphism on points,
  `AlgebraicGeometry.FormalSpace.IsReduction.isHomeomorph_pointsMapULift`, so it carries closed
  sets to closed sets,
  `AlgebraicGeometry.FormalSpace.IsReduction.isClosed_image_pointsMapULift`.

The reduction is supplied as data satisfying `AlgebraicGeometry.FormalSpace.IsReduction` rather
than constructed, since Stacks 0AIN — the existence of a reduction — is not available in this
library; this is also how Stacks 0GVQ and Stacks 0GVT are stated in the library.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
* [Stacks Project, Tag 0GVR](https://stacks.math.columbia.edu/tag/0GVR)
* [Stacks Project, Tag 0GVS](https://stacks.math.columbia.edu/tag/0GVS)
* [Stacks Project, Tag 0GVT](https://stacks.math.columbia.edu/tag/0GVT)
* [Stacks Project, Tag 0GVV](https://stacks.math.columbia.edu/tag/0GVV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Clause (1) of Stacks 0GVV**, in the ambient spelling: the completion of an affine formal
algebraic space `Y` over `S` along a closed set of points of `Y` is again an affine formal
algebraic space. Through the bijection `|Y_red| = |Y|` given by the inclusion of a reduction
this is the source's statement about a closed subset of `|Y_red|`. -/
abbrev CompletionOfAffineIsAffine : Prop :=
  ∀ Y : FppfSheaf B S hS, IsAffineFormalAlgebraicSpace B S hS Y →
    ∀ T : Set (Space.pointsULift.{u + 1} B S hS Y.obj),
      @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Y.obj) T →
      IsAffineFormalAlgebraicSpace B S hS (Space.completionSheafULift B S hS Y T)

/-- The completion of a formal algebraic space `X` over `S` along a closed set `T` of points of
`X` is a formal algebraic space: the completions of the charts of `X` along the inverse images
of `T` form an atlas as in Definition 0AIM.

The affine case `haff` and the set-theoretic condition `hset` of Stacks 0AIS are hypotheses;
see the section "What is assumed" of this file. -/
theorem isFormalAlgebraicSpace_completionSheafULift {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) T)
    (haff : CompletionOfAffineIsAffine B S hS)
    (hset : SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS X T)) :
    IsFormalAlgebraicSpace B S hS (Space.completionSheafULift B S hS X T) := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, I, Xi, g, hXiaff, hg, hcov⟩ := hX
  let Ti : ∀ k : I, Set (Space.pointsULift.{u + 1} B S hS (Xi k).obj) := fun k ↦
    Space.pointsMapULift.{u + 1} B S hS (Xi k).obj (g k).hom ⁻¹' T
  have hsub : ∀ k, Ti k ⊆ Space.pointsMapULift.{u + 1} B S hS (Xi k).obj (g k).hom ⁻¹' T :=
    fun _ _ hx ↦ hx
  have hsup : ∀ k, Space.pointsMapULift.{u + 1} B S hS (Xi k).obj (g k).hom ⁻¹' T ⊆ Ti k :=
    fun _ _ hx ↦ hx
  have hsq : ∀ k, IsPullback
      (Space.completionSheafULiftInclusion B S hS (Xi k) (Ti k))
      (Space.completionSheafMapULift B S hS (g k) (Ti k) T (hsub k))
      (g k)
      (Space.completionSheafULiftInclusion B S hS X T) := fun k ↦
    Space.isPullback_completionSheafMapULift B S hS (g k) (Ti k) T (hsub k) (hsup k)
  refine ⟨hset, I, fun k ↦ Space.completionSheafULift B S hS (Xi k) (Ti k),
    fun k ↦ Space.completionSheafMapULift B S hS (g k) (Ti k) T (hsub k), ?_, ?_, ?_⟩
  · intro k
    refine haff (Xi k) (hXiaff k) (Ti k) ?_
    let _instChart := Space.pointTopologyULift.{u + 1} B S hS (Xi k).obj
    let _instAmbient := Space.pointTopologyULift.{u + 1} B S hS X.obj
    exact hT.preimage (Space.continuous_pointsMapULift.{u + 1} B S hS (g k).hom)
  · exact fun k ↦ isRepresentableEtale_of_isPullback B S hS (hsq k) (hg k)
  · set φ := Space.completionSheafULiftInclusion B S hS X T with hφ
    let e : ∀ k, Space.completionSheafULift B S hS (Xi k) (Ti k) ≅ pullback (g k) φ :=
      fun k ↦ (hsq k).isoPullback
    let t : (∐ fun k ↦ Space.completionSheafULift B S hS (Xi k) (Ti k)) ⟶
        (∐ fun k ↦ pullback (g k) φ) :=
      Sigma.desc fun k ↦ (e k).hom ≫ Sigma.ι (fun j ↦ pullback (g j) φ) k
    have hts : IsSplitEpi t :=
      ⟨⟨Sigma.desc fun k ↦ (e k).inv ≫ Sigma.ι
          (fun j ↦ Space.completionSheafULift B S hS (Xi j) (Ti j)) k, by
        apply Sigma.hom_ext
        intro k
        simp [t]⟩⟩
    have hbase : Sheaf.IsLocallySurjective (Sigma.desc fun k ↦ pullback.snd (g k) φ) :=
      Sheaf.isLocallySurjective_sigmaDesc_pullback_snd φ g hcov
    have hfac : (Sigma.desc fun k ↦
          Space.completionSheafMapULift B S hS (g k) (Ti k) T (hsub k)) =
        t ≫ Sigma.desc fun k ↦ pullback.snd (g k) φ := by
      apply Sigma.hom_ext
      intro k
      simp only [t, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc]
      exact ((hsq k).isoPullback_hom_snd).symm
    rw [hfac, Sheaf.isLocallySurjective_iff_epi]
    let _ : Epi t := hts.epi
    let _ : Epi (Sigma.desc fun k ↦ pullback.snd (g k) φ) :=
      (Sheaf.isLocallySurjective_iff_epi _).mp hbase
    exact epi_comp _ _

/-- The completion of a formal algebraic space `X` over `S` along a closed set `T` of points of
`X` is a formal algebraic space: the completions of the charts of `X` along the inverse images
of `T` form an atlas as in Definition 0AIM.

The set-theoretic condition `hset` of Stacks 0AIS is the only hypothesis; the affine case is
`AlgebraicGeometry.FormalSpace.completionOfAffineIsAffine`, clause (1) of Stacks 0GVV. See the
section "What is assumed" of this file. -/
theorem isFormalAlgebraicSpace_completionSheafULift' {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) T)
    (hset : SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS X T)) :
    IsFormalAlgebraicSpace B S hS (Space.completionSheafULift B S hS X T) :=
  isFormalAlgebraicSpace_completionSheafULift B S hS hX T hT
    (completionOfAffineIsAffine B S hS) hset

/-- **Stacks 0GVR.** Let `S` be a scheme, let `X` be a formal algebraic space over `S` with
reduction `i : X_red ⟶ X` and let `T ⊆ |X_red|` be closed. The completion `X_{/T}` of `X`
along `T` — the fppf sheaf attached to the functor sending `U` to the morphisms `f : U ⟶ X`
with `f(|U|) ⊆ T` — is a formal algebraic space over `S`: the completions of the charts of `X`
along the inverse images of `T` form an atlas as in Definition 0AIM, each of them affine formal
by clause (1) of Stacks 0GVV, each representable étale over `X_{/T}` as a base change of a
chart of `X`, and jointly surjective because the charts of `X` are.

The closed subset `T` of `|X_red|` enters the completion through its image in `|X|`, which is
closed because the inclusion of a reduction is a homeomorphism on points:
`AlgebraicGeometry.FormalSpace.IsReduction.isClosed_image_pointsMapULift`. The set-theoretic
condition `hset` of Stacks 0AIS is the only hypothesis beyond the tag's own; see the section
"What is assumed" of this file. -/
@[stacks 0GVR "the whole statement for the tag's own hypotheses — `X` a formal algebraic space \
and `T` closed in `|X_red|` — from one carried hypothesis, `hset`, the set-theoretic condition \
of Stacks 0AIS for the completion, which this library carries by standing convention on the \
library's Stacks 0AJ1 (`isFormalAlgebraicSpace_of_etaleCover`, \
StacksFrontier/AlgebraicGeometry/FormalSpace/EtaleCover.lean) and Stacks 0GVM \
(`isAffineFormalAlgebraicSpace_colimit`, \
StacksFrontier/AlgebraicGeometry/FormalSpace/DirectedColimit.lean), the condition being part of \
the definition of a formal algebraic space used here and not following from the conditions on \
the members of a covering family. Nothing else: the affine case, clause (1) of Stacks 0GVV, is \
proved — `completionOfAffineIsAffine`; and closedness of \
`T` is the tag's own, in `|X_red|`, the inclusion of a reduction being a homeomorphism on \
points (`IsReduction.isHomeomorph_pointsMapULift`) and hence carrying `T` to a closed subset \
of `|X|`, which is where the proof uses it \
(`IsReduction.isClosed_image_pointsMapULift`). `hi` supplies the reduction as data because \
Stacks 0AIN is unavailable in this library, the convention of the library's Stacks 0GVQ and 0GVT"]
theorem isFormalAlgebraicSpace_completionAlong' {X Xred : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hset : SatisfiesSetTheoreticCondition B S hS (completionAlong i T)) :
    IsFormalAlgebraicSpace B S hS (completionAlong i T) :=
  isFormalAlgebraicSpace_completionSheafULift' B S hS hX _
    (hi.isClosed_image_pointsMapULift (T := T) hT) hset

/-- **Stacks 0GVR.** Let `S` be a scheme, let `X` be a formal algebraic space over `S` with
reduction `i : X_red ⟶ X` and let `T ⊆ |X_red|` be closed. The completion `X_{/T}` of `X`
along `T` — the fppf sheaf attached to the functor sending `U` to the morphisms `f : U ⟶ X`
with `f(|U|) ⊆ T` — is a formal algebraic space over `S`: the completions of the charts of `X`
along the inverse images of `T` form an atlas as in Definition 0AIM, each of them affine formal
by the affine case, each representable étale over `X_{/T}` as a base change of a chart of `X`,
and jointly surjective because the charts of `X` are.

`isFormalAlgebraicSpace_completionAlong'` draws the same conclusion from `T` closed in the
reduction rather than from its image being closed in `X`, and with `haff` discharged. -/
theorem isFormalAlgebraicSpace_completionAlong {X Xred : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {i : Xred ⟶ X}
    (_hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T))
    (haff : CompletionOfAffineIsAffine B S hS)
    (hset : SatisfiesSetTheoreticCondition B S hS (completionAlong i T)) :
    IsFormalAlgebraicSpace B S hS (completionAlong i T) :=
  isFormalAlgebraicSpace_completionSheafULift' B S hS hX _ hT hset

end AlgebraicGeometry.FormalSpace

end
