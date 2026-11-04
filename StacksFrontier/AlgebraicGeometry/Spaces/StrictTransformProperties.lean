module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform

/-!
# Properties of the strict transform of an algebraic space and of a module

This file collects the three lemmas of the section "Strict transform" of the chapter on
divisors on algebraic spaces that come after the definition itself, Stacks 0862: the behaviour
of the strict transform under flatness (Stacks 0865), under direct image along an affine
morphism (Stacks 0866), and under a composition of two blowups (Stacks 0868). Of Stacks 0868
only the constructions it is stated with are here; the tag is proved as
`AlgebraicGeometry.Space.exists_strictTransformSheaf_comp_iso_unconditional` and
`AlgebraicGeometry.Space.exists_strictTransformSpace_comp_iso_unconditional` in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformFlatCompositionUnassumed.lean`.

The strict transform used throughout is the one constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransform.lean`, for a morphism `b : A' ⟶ A` of
algebraic spaces together with a subspace `E ⊆ A'`; for `b` the blowup of `A` in a closed
subspace `Z` and `E = b^{-1}Z` its exceptional divisor this is the strict transform of
Stacks 0862.  "Being the blowup of `A` in `Z`" is `AlgebraicGeometry.Space.IsBlowupAlong`, the
universal property of Stacks 085U, since Stacks 085Q constructs no blowup of an algebraic
space in this library.

## Main results

* `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_top_of_isFlatAt` and
  `AlgebraicGeometry.Space.isIso_strictTransformSheafQuotient_of_isFlatOverAtGeometricPoint` are
  **Stacks 0865, parts (1) and (2)**, conditional on the hypothesis `hloc` described below.  The
  tag is proved as
  `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_top_of_isFlatAt_unconditional` and
  `Space.isIso_strictTransformSheafQuotient_of_isFlatOverAtGeometricPoint_unconditional` in
  `StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformFlatCompositionUnassumed.lean`.
* `AlgebraicGeometry.Space.exists_modulePushforward_strictTransformSheaf_iso` is **Stacks 0866**,
  conditional on the hypotheses `hloc` and `hpres` described below.  The tag is proved as
  `AlgebraicGeometry.Space.exists_modulePushforward_strictTransformSheaf_iso_unconditional` in
  `StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformAffinePushforward.lean`.

Unconditional auxiliary results, which are what the three lemmas are reduced to:

* `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_top_of_forall_definingIdealAt_eq_bot`:
  if the ideal of sections supported on `|pr_{A'}^{-1}E|` vanishes on every affine étale chart,
  then the strict transform of `X` is the whole base change `X ×_A A'`.  This is the passage
  that part (1) of Stacks 0865 and part (2) of Stacks 0868 need, and it is proved here from
  Stacks 03MB.
* `AlgebraicGeometry.Space.strictTransformSheafQuotient`: the canonical quotient map
  `pr_X^*F ⟶ F'` onto the strict transform of a module, which is what parts (2) of Stacks 0865
  and (1) of Stacks 0866 and 0868 compare.
* `AlgebraicGeometry.Space.strictTransformPullbackMap` and
  `AlgebraicGeometry.Space.strictTransformPullbackMap_toSource`,
  `AlgebraicGeometry.Space.strictTransformPullbackMap_toBlowUp`,
  `AlgebraicGeometry.Space.isPullback_strictTransformPullbackMap`: the base change
  `g' : X ×_A A' ⟶ Y ×_A A'` of a morphism `g : X ⟶ Y` over `A`, and the cartesian square it
  sits in, which is the `g'` of Stacks 0866.
* `AlgebraicGeometry.Space.iteratedStrictTransformPullbackIso`: the identification
  `(X ×_A A') ×_{A'} A'' ≅ X ×_A A''` of the two ambient base changes of Stacks 0868,
  compatibly with the projections to `X` and to `A''`.  This is proved here, by pasting
  cartesian squares.
* `AlgebraicGeometry.Space.iteratedStrictTransformSpaceMap`: the morphism
  `X' ×_{A'} A'' ⟶ X ×_A A''` of ambient base changes along which part (2) of Stacks 0868
  compares the two strict transforms of a space, `X'` being the first strict transform.  This
  too is proved here.

## A hypothesis Stacks 0865 and 0866 carry, and why

**Both Stacks 0865 and 0866 are stated below with the hypotheses of the source
*and one extra hypothesis*, named `hloc` in each case, which the source derives and this
library cannot.**  The statements are therefore conditional, and the names of the missing
inputs are recorded here so that discharging them is a well-defined task.

The Stacks Project proves all three by reducing to the case of schemes — Stacks 080F, 080G and
080I respectively, all three of which *are* available in this library, in
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/Flat.lean`,
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/AffinePushforward.lean` and
`StacksFrontier/AlgebraicGeometry/StrictTransform/CompositionBlowUp.lean` — by étale localization,
which is Stacks 0863.  Of Stacks 0863 only part (1) is available,
`AlgebraicGeometry.Space.isEtale_baseChange_blowup_of_isEtale`; parts (2) and (3), which are the
compatibility of the strict transform of a space and of a module with restriction to an étale
chart, are not.  They in turn rest on parts (2) and (3) of Stacks 0859, which are likewise not
available: `StacksFrontier/AlgebraicGeometry/Spaces/SupportedSectionsSubsheaf.lean` constructs the
supported-sections subsheaf and proves part (1) only, and records in its implementation notes
what the remaining parts need.

So each `hloc` below is the conclusion that Stacks 0863, parts (2) and (3), together with the
already-available scheme-level tag, would supply.  Each is stated as an *implication* whose
antecedent is the source's own geometric hypotheses, so that those hypotheses are genuinely
consumed and the statement is the source's statement relative to one named input, rather than a
statement about an unrelated situation.  Nothing below silently assumes its own conclusion: the
conclusions are statements about the strict transform — that a subfunctor is `⊤`, that a
quotient map is invertible, that two modules are isomorphic — and the work of getting there from
`hloc` is done in each proof.

## References

* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0865](https://stacks.math.columbia.edu/tag/0865)
* [Stacks Project, Tag 0866](https://stacks.math.columbia.edu/tag/0866)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The whole of an algebraic space as a closed subspace -/

/-- The whole of an algebraic space is a closed subspace of itself, being the intersection of
the empty family of closed subspaces. -/
private theorem isClosedSubspace_top_aux (W : AlgebraicSpaces B S hS) :
    IsClosedSubspace B S hS (⊤ : Subfunctor W.1) := by
  have h := isClosedSubspace_sInf B S hS W.2 (∅ : Set (Subfunctor W.1)) fun _ hZ => hZ.elim
  rwa [sInf_empty] at h

/-! ### Reductions used by the three lemmas -/

section Reductions

variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)

/-- **The strict transform of `X` is the whole base change as soon as the ideal of supported
sections vanishes on affine charts.**

The strict transform of `X` is the infimum of the closed subspaces whose defining ideal is
dominated, at every affine étale chart, by the ideal of sections supported on
`|pr_{A'}^{-1}E|`.  If that ideal is zero then every member of the family has zero defining
ideal at every affine chart, hence contains the whole space by the injectivity half of
Stacks 03MB, `AlgebraicGeometry.Space.le_of_forall_definingIdealAt_le`; so the infimum is
`⊤`. -/
theorem strictTransformSubfunctor_eq_top_of_forall_definingIdealAt_eq_bot (E : Subfunctor A'.1)
    (h : ∀ U : SmallEtale B S hS (strictTransformPullback B S hS f b).1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
      (strictTransformIdealSubmodule B S hS f b E).toSubmodule.obj (op U) = ⊥) :
    strictTransformSubfunctor B S hS f b E = ⊤ := by
  refine le_antisymm le_top (le_sInf ?_)
  rintro Z ⟨hZ, hZle⟩
  refine le_of_forall_definingIdealAt_le B S hS (strictTransformPullback B S hS f b)
    ⟨⊤, isClosedSubspace_top_aux B S hS _⟩ ⟨Z, hZ⟩ fun U hU => ?_
  exact ((hZle U hU).trans (le_of_eq (h U hU))).trans bot_le

/-- The submodule of `pr_X^*F` of those sections that are supported on `|pr_{A'}^{-1}E|`, whose
quotient is the strict transform of `F`. -/
abbrev strictTransformSupportedSections (E : Subfunctor A'.1)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F).Submodule :=
  supportedSectionsSubmodule B S hS (strictTransformPullback B S hS f b).1
    (strictTransformPullback B S hS f b).2 (exceptionalPreimageSet B S hS f b E)
    ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F)

/-- The canonical quotient map `pr_X^*F ⟶ F'` onto the strict transform of `F`: the cokernel
projection of the inclusion of the sections supported on `|pr_{A'}^{-1}E|`. -/
abbrev strictTransformSheafQuotient (E : Subfunctor A'.1) (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F ⟶
      strictTransformSheaf B S hS f b E F :=
  cokernel.π (strictTransformSupportedSections B S hS f b E F).ι

end Reductions

/-! ### Stacks 0865: strict transforms of flat spaces and modules -/

section Flat

variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)

/-- **Stacks 0865, part (1), conditional form.** Let `Z ⊆ A` be a closed subspace of an algebraic
space over `S`, let `b : A' ⟶ A` be the blowup of `A` in `Z` and let `f : X ⟶ A` be an algebraic
space over `A`.  If `X` is flat over `A` at every point lying over `Z`, then the strict transform
of `X` with respect to `b` is the whole base change `X ×_A A'`.

**This statement carries the extra hypothesis `hloc`, which the source derives and this library
cannot.**  `hloc` says that in this situation — `b` the blowup of `A` in `Z`, and `X` flat over
`A` above `Z` — the ideal of sections of `𝒪_{X ×_A A'}` supported on the exceptional preimage
vanishes on every affine étale chart.  That is what Stacks 0863, parts (2) and (3) together with
the scheme-level Stacks 080F, part (1)
(`AlgebraicGeometry.strictTransformIdeal_eq_bot_of_flat_at_exceptional`) supply, and parts (2)
and (3) of Stacks 0863 are absent from this library; see the module documentation.  The source's
own hypotheses are the antecedents of `hloc` and are consumed by this proof.

Given `hloc` the conclusion is
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_top_of_forall_definingIdealAt_eq_bot`,
that is Stacks 03MB.  The tag is proved without `hloc` as
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_top_of_isFlatAt_unconditional`. -/
theorem strictTransformSubfunctor_eq_top_of_isFlatAt (Z : ClosedSubspaces B S hS A.1)
    (hloc : IsBlowupAlong B S hS Z b →
      (∀ x : points B S hS X.1,
        pointsMap B S hS X.1 f.hom x ∈ Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) →
          IsFlatAt B S hS f.hom x) →
      ∀ U : SmallEtale B S hS (strictTransformPullback B S hS f b).1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
        (strictTransformIdealSubmodule B S hS f b
          (Z.1.preimage b.hom)).toSubmodule.obj (op U) = ⊥)
    (hb : IsBlowupAlong B S hS Z b)
    (hflat : ∀ x : points B S hS X.1,
      pointsMap B S hS X.1 f.hom x ∈ Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) →
        IsFlatAt B S hS f.hom x) :
    strictTransformSubfunctor B S hS f b (Z.1.preimage b.hom) = ⊤ :=
  strictTransformSubfunctor_eq_top_of_forall_definingIdealAt_eq_bot B S hS f b _ (hloc hb hflat)

/-- **Stacks 0865, part (2), conditional form.** In the situation of part (1), let `F` be a
quasi-coherent `𝒪_X`-module which is flat over `A` at every point lying over `Z`.  Then the
canonical quotient map `pr_X^*F ⟶ F'` onto the strict transform of `F` is an isomorphism, so the
strict transform of `F` is `pr_X^*F`.

Flatness of `F` over `A` at the points above `Z` is read at geometric points, condition (2) of
Stacks 05VU, `AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint`; a geometric point lies over
`Z` when its underlying point of `|X|` does.

**This statement carries the extra hypothesis `hloc`, which the source derives and this library
cannot**, exactly as in part (1): `hloc` says that in this situation the inclusion of the
submodule of sections of `pr_X^*F` supported on the exceptional preimage is the zero morphism,
that is, that there are no nonzero local sections of `pr_X^*F` supported there.  That is the
step the scheme-level proof of Stacks 080F, part (2) establishes before concluding
`AlgebraicGeometry.isIso_strictTransformSheaf_quotient_of_flat_at_exceptional`, and carrying it
across to algebraic spaces is Stacks 0863, parts (2) and (3).  See the module documentation.

No quasi-coherence hypothesis on `F` is carried: the strict transform is a cokernel and the
argument from `hloc` uses nothing of `F`, so the tag's quasi-coherence assumption would only
weaken the statement.  The tag is proved without `hloc` as
`isIso_strictTransformSheafQuotient_of_isFlatOverAtGeometricPoint_unconditional`. -/
theorem isIso_strictTransformSheafQuotient_of_isFlatOverAtGeometricPoint
    (Z : ClosedSubspaces B S hS A.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hloc : IsBlowupAlong B S hS Z b →
      (∀ xbar : GeometricPoint B S hS X.1,
        pointsMap B S hS X.1 f.hom xbar.image ∈
            Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) →
          IsFlatOverAtGeometricPoint B S hS f F xbar) →
      (strictTransformSupportedSections B S hS f b (Z.1.preimage b.hom) F).ι = 0)
    (hb : IsBlowupAlong B S hS Z b)
    (hflat : ∀ xbar : GeometricPoint B S hS X.1,
      pointsMap B S hS X.1 f.hom xbar.image ∈
          Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) →
        IsFlatOverAtGeometricPoint B S hS f F xbar) :
    IsIso (strictTransformSheafQuotient B S hS f b (Z.1.preimage b.hom) F) :=
  cokernel.π_of_zero (hloc hb hflat)

end Flat

/-! ### Stacks 0866: strict transforms and direct images along an affine morphism -/

section AffinePushforward

variable {A X Y A' : AlgebraicSpaces B S hS} (g : X ⟶ Y) (f : Y ⟶ A) (b : A' ⟶ A)

/-- The base change `g' : X ×_A A' ⟶ Y ×_A A'` of a morphism `g : X ⟶ Y` of algebraic spaces
over `A`. -/
def strictTransformPullbackMap :
    strictTransformPullback B S hS (g ≫ f) b ⟶ strictTransformPullback B S hS f b :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift
    (strictTransformPullbackToSource B S hS (g ≫ f) b ≫ g)
    (strictTransformPullbackToBlowUp B S hS (g ≫ f) b)
    (by
      rw [Category.assoc]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS (g ≫ f) b).w)

/-- Composing the base change of `g` with the projection to `Y` gives the projection to `X`
followed by `g`. -/
@[simp]
theorem strictTransformPullbackMap_toSource :
    strictTransformPullbackMap B S hS g f b ≫ strictTransformPullbackToSource B S hS f b =
      strictTransformPullbackToSource B S hS (g ≫ f) b ≫ g :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift_fst _ _ _

/-- The base change of `g` is a morphism over `A'`. -/
@[simp]
theorem strictTransformPullbackMap_toBlowUp :
    strictTransformPullbackMap B S hS g f b ≫ strictTransformPullbackToBlowUp B S hS f b =
      strictTransformPullbackToBlowUp B S hS (g ≫ f) b :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift_snd _ _ _

/-- **The square formed by `g`, its base change and the two projections to `X` and `Y` is
cartesian.**  It is the top square of the two pasted base-change squares whose composite is the
base change of `g ≫ f`, so this is cancellation of a cartesian square at the bottom. -/
theorem isPullback_strictTransformPullbackMap :
    IsPullback (strictTransformPullbackToSource B S hS (g ≫ f) b)
      (strictTransformPullbackMap B S hS g f b) g
      (strictTransformPullbackToSource B S hS f b) := by
  refine IsPullback.of_bot ?_ (strictTransformPullbackMap_toSource B S hS g f b).symm
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
  rw [strictTransformPullbackMap_toBlowUp]
  exact AlgebraicSpaces.isPullback_fiberProduct B S hS (g ≫ f) b

/-- **Stacks 0866, conditional form.** Let `Z ⊆ A` be a closed subspace of an algebraic space over
`S`, let `b : A' ⟶ A` be the blowup of `A` in `Z`, let `g : X ⟶ Y` be an affine morphism of
algebraic spaces over `A`, let `F` be an `𝒪_X`-module and let `g' : X ×_A A' ⟶ Y ×_A A'` be the
base change of `g`.  Then `g'_*` of the strict transform of `F` relative to `b` is the strict
transform of `g_* F`, compatibly with the two quotient maps and the base-change comparison.

**This statement carries two extra hypotheses that the source derives and this library
cannot.**

* `hloc` provides, in the source's situation, the base-change isomorphism `α` of Stacks 02KG,
  `g'_* pr_X^*F ≅ pr_Y^* g_*F`, together with the identification `β` of the direct image of the
  sections supported on the exceptional preimage with the sections of the direct image supported
  there, compatibly with `α`.  Of these two, `β` is available in essence — it is
  `AlgebraicGeometry.Space.pushforward_supportedSectionsSubmodule_range_eq` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SupportedSectionsPushforward.lean`, which identifies the
  two subsheaves of `g'_* pr_X^*F` chart by chart — while `α`, Stacks 02KG for an affine
  morphism of algebraic spaces, is not.
* `hpres` is right exactness of `g'_*` on the sequence at hand: that the direct image along the
  affine morphism `g'` preserves the cokernel defining the strict transform.  This is the use
  the Stacks Project makes of Stacks 01SB; for algebraic spaces the corresponding statement in
  this library, `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact_of_scheme_case`, is
  itself conditional and concerns integral morphisms and abelian sheaves rather than affine
  morphisms and modules.

What this proof does with them is the argument of the Stacks Project: the strict transform is a
cokernel, `hpres` carries it through the direct image, and `hloc` identifies the resulting
cokernel with the cokernel defining the strict transform of `g_* F`.  See the module
documentation.

No quasi-coherence hypothesis on `F` is carried, so the statement is more general than the
tag's: quasi-coherence of `F` enters the source's argument only through the two inputs above,
both of which are hypotheses here.  The tag is proved without `hloc` and `hpres` as
`AlgebraicGeometry.Space.exists_modulePushforward_strictTransformSheaf_iso_unconditional`. -/
theorem exists_modulePushforward_strictTransformSheaf_iso (Z : ClosedSubspaces B S hS A.1)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hloc : IsBlowupAlong B S hS Z b → IsAffineHom B S hS g.hom →
      ∃ (α : (modulePushforward B S hS (strictTransformPullbackMap B S hS g f b)).obj
                ((modulePullback B S hS
                  (strictTransformPullbackToSource B S hS (g ≫ f) b)).obj F) ≅
              (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
                ((modulePushforward B S hS g).obj F))
          (β : (modulePushforward B S hS (strictTransformPullbackMap B S hS g f b)).obj
                (strictTransformSupportedSections B S hS (g ≫ f) b
                  (Z.1.preimage b.hom) F).toSheafOfModules ≅
              (strictTransformSupportedSections B S hS f b (Z.1.preimage b.hom)
                ((modulePushforward B S hS g).obj F)).toSheafOfModules),
        (modulePushforward B S hS (strictTransformPullbackMap B S hS g f b)).map
              (strictTransformSupportedSections B S hS (g ≫ f) b (Z.1.preimage b.hom) F).ι ≫
            α.hom =
          β.hom ≫ (strictTransformSupportedSections B S hS f b (Z.1.preimage b.hom)
            ((modulePushforward B S hS g).obj F)).ι)
    (hpres : PreservesColimit
      (parallelPair
        (strictTransformSupportedSections B S hS (g ≫ f) b (Z.1.preimage b.hom) F).ι 0)
      (modulePushforward B S hS (strictTransformPullbackMap B S hS g f b)))
    (hb : IsBlowupAlong B S hS Z b) (hg : IsAffineHom B S hS g.hom) :
    ∃ (α : (modulePushforward B S hS (strictTransformPullbackMap B S hS g f b)).obj
              ((modulePullback B S hS
                (strictTransformPullbackToSource B S hS (g ≫ f) b)).obj F) ≅
            (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
              ((modulePushforward B S hS g).obj F))
        (e : (modulePushforward B S hS (strictTransformPullbackMap B S hS g f b)).obj
              (strictTransformSheaf B S hS (g ≫ f) b (Z.1.preimage b.hom) F) ≅
            strictTransformSheaf B S hS f b (Z.1.preimage b.hom)
              ((modulePushforward B S hS g).obj F)),
      (modulePushforward B S hS (strictTransformPullbackMap B S hS g f b)).map
            (strictTransformSheafQuotient B S hS (g ≫ f) b (Z.1.preimage b.hom) F) ≫ e.hom =
        α.hom ≫ strictTransformSheafQuotient B S hS f b (Z.1.preimage b.hom)
          ((modulePushforward B S hS g).obj F) := by
  obtain ⟨α, β, hβ⟩ := hloc hb hg
  have := hpres
  refine ⟨α, PreservesCokernel.iso _ _ ≪≫ cokernel.mapIso _ _ β α hβ, ?_⟩
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ (cokernel.mapIso _ _ β α hβ).hom)
    (PreservesCokernel.π_iso_hom _ _)) ?_
  exact cokernel.π_desc _ _ _

end AffinePushforward

/-! ### Stacks 0868: strict transforms and a composition of two blowups -/

section Composition

variable {A X A' A'' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A) (c : A'' ⟶ A')

/-- **The two ambient base changes of a composition of blowups agree**:
`(X ×_A A') ×_{A'} A'' ≅ X ×_A A''`, by pasting the two cartesian squares and comparing with
the cartesian square of the composite.  Unconditional. -/
def iteratedStrictTransformPullbackIso :
    strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c ≅
      strictTransformPullback B S hS f (c ≫ b) :=
  (IsPullback.paste_horiz
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (strictTransformPullbackToBlowUp B S hS f b) c)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f (c ≫ b))

/-- `AlgebraicGeometry.Space.iteratedStrictTransformPullbackIso` is compatible with the
projections to `X`. -/
@[simp]
theorem iteratedStrictTransformPullbackIso_hom_toSource :
    (iteratedStrictTransformPullbackIso B S hS f b c).hom ≫
        strictTransformPullbackToSource B S hS f (c ≫ b) =
      strictTransformPullbackToSource B S hS
          (strictTransformPullbackToBlowUp B S hS f b) c ≫
        strictTransformPullbackToSource B S hS f b :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- `AlgebraicGeometry.Space.iteratedStrictTransformPullbackIso` is compatible with the
projections to `A''`. -/
@[simp]
theorem iteratedStrictTransformPullbackIso_hom_toBlowUp :
    (iteratedStrictTransformPullbackIso B S hS f b c).hom ≫
        strictTransformPullbackToBlowUp B S hS f (c ≫ b) =
      strictTransformPullbackToBlowUp B S hS
        (strictTransformPullbackToBlowUp B S hS f b) c :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

variable (E : Subfunctor A'.1)

/-- The strict transform of `X` with respect to `(b, E)`, as an algebraic space over `S`. -/
abbrev strictTransformSpace : AlgebraicSpaces B S hS :=
  ⟨(strictTransform B S hS f b E).1.toFunctor, (strictTransform B S hS f b E).2.1⟩

/-- The closed immersion of the strict transform of `X` into the base change `X ×_A A'`. -/
abbrev strictTransformSpaceι :
    strictTransformSpace B S hS f b E ⟶ strictTransformPullback B S hS f b :=
  ObjectProperty.homMk (strictTransform B S hS f b E).1.ι

/-- The strict transform of `X` as an algebraic space over `A'`, which is what the second
blowup takes the strict transform of. -/
abbrev strictTransformSpaceToBlowUp : strictTransformSpace B S hS f b E ⟶ A' :=
  strictTransformSpaceι B S hS f b E ≫ strictTransformPullbackToBlowUp B S hS f b

/-- **The ambient base change of the second strict transform maps to the ambient base change of
the composite**: the morphism `X' ×_{A'} A'' ⟶ X ×_A A''` induced by the closed immersion
`X' ⟶ X ×_A A'` of the first strict transform.  Unconditional. -/
def iteratedStrictTransformSpaceMap :
    strictTransformPullback B S hS (strictTransformSpaceToBlowUp B S hS f b E) c ⟶
      strictTransformPullback B S hS f (c ≫ b) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f (c ≫ b)).lift
    (strictTransformPullbackToSource B S hS (strictTransformSpaceToBlowUp B S hS f b E) c ≫
      strictTransformSpaceι B S hS f b E ≫ strictTransformPullbackToSource B S hS f b)
    (strictTransformPullbackToBlowUp B S hS (strictTransformSpaceToBlowUp B S hS f b E) c)
    (by
      have h1 := (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).w
      have h2 := (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (strictTransformSpaceToBlowUp B S hS f b E) c).w
      simp only [Category.assoc] at h1 h2 ⊢
      rw [← Category.assoc] at h2
      rw [h1, ← Category.assoc, ← Category.assoc, h2, Category.assoc])

/-- `AlgebraicGeometry.Space.iteratedStrictTransformSpaceMap` is compatible with the projections
to `X`. -/
@[simp]
theorem iteratedStrictTransformSpaceMap_toSource :
    iteratedStrictTransformSpaceMap B S hS f b c E ≫
        strictTransformPullbackToSource B S hS f (c ≫ b) =
      strictTransformPullbackToSource B S hS (strictTransformSpaceToBlowUp B S hS f b E) c ≫
        strictTransformSpaceι B S hS f b E ≫ strictTransformPullbackToSource B S hS f b :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f (c ≫ b)).lift_fst _ _ _

/-- `AlgebraicGeometry.Space.iteratedStrictTransformSpaceMap` is compatible with the projections
to `A''`. -/
@[simp]
theorem iteratedStrictTransformSpaceMap_toBlowUp :
    iteratedStrictTransformSpaceMap B S hS f b c E ≫
        strictTransformPullbackToBlowUp B S hS f (c ≫ b) =
      strictTransformPullbackToBlowUp B S hS (strictTransformSpaceToBlowUp B S hS f b E) c :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f (c ≫ b)).lift_snd _ _ _

/-- The condition on the third centre of Stacks 0868: the points of `Y ⊆ A` are the points of
`Z` together with the image under `|b|` of the points of `Z' ⊆ A'`. -/
abbrev IsCompositeCentre (Z : ClosedSubspaces B S hS A.1) (Z' : ClosedSubspaces B S hS A'.1)
    (Y : ClosedSubspaces B S hS A.1) : Prop :=
  Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
    Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
      pointsMap B S hS A'.1 b.hom '' Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι)

end Composition

end AlgebraicGeometry.Space

end
