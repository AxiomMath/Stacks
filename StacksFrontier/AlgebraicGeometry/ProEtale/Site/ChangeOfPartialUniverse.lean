module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Enlargement
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.MorphismsOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology and abelian sheaves after a change of partial universe

Let `S` be a scheme and let `(Sch/S)_proétale` and `(Sch'/S)_proétale` be two big pro-étale
sites of `S` as in Definition 098K, the first contained in the second.  Then restriction of
abelian sheaves along the inclusion changes neither the cohomology over an object of the smaller
site, nor the category of abelian sheaves up to essential surjectivity: every abelian sheaf on
the smaller site is the restriction of one on the bigger site.

## Main definitions

* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.abelianRestrictionOver` and
  `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.abelianExtensionOver`: restriction
  of abelian sheaves to the smaller localized site, and the sheaf pullback extending them to the
  bigger one.

## Main results

* `AlgebraicGeometry.ProEtale.essentiallySmall_bigProetaleOver`: a big pro-étale site over a
  scheme is essentially small at the universe of its morphisms.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.cohomologyRestrictionIso`:
  Stacks 0F4T (1).
* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.exists_extension_abelianSheaf`:
  Stacks 0F4T (2).

## Implementation notes

The source deduces both statements from Stacks 0F4S, which says that the inclusion functor
satisfies the assumptions of Sites, Lemma 00XU.  That is
`AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn` and its properties in
`StacksFrontier.AlgebraicGeometry.ProEtale.Site.Enlargement`, which this file consumes: full
faithfulness, cocontinuity, continuity in the form of being a morphism of sites, and
preservation of finite limits, for the slices over `S`.  Cocontinuity there rests on Stacks 098J
(`AlgebraicGeometry.ProEtale.exists_covering_refining_proetaleCovering`), which is likewise
proved, so nothing is hypothetical and both statements below are unconditional.

What is added here is the passage from those site-level properties to abelian sheaves.
Statement (2) is Stacks 00XU, `CategoryTheory.Functor.full_and_faithful_sheafPullback`: the
sheaf pullback along the inclusion is fully faithful, so the unit of the adjunction exhibits
every abelian sheaf as the restriction of its pullback.  Statement (1) is Stacks 03YU,
`Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso`, whose remaining hypothesis is that
the two localized sites be essentially small at the universe of their morphisms; that is
`AlgebraicGeometry.ProEtale.essentiallySmall_bigProetaleOver`, from Stacks 000J.  Essential
smallness is also what supplies the Kan extensions along the inclusion with coefficients in
`Ab.{u}`, which the generic instances give only for coefficients in the universe of the objects.

Continuity is re-exposed as the instance
`AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.functorOver_isContinuous` so that the
restriction functor on sheaves is available to instance search; Stacks 0F4S proves it in the
bundled form `IsMorphismOfSites`, from which this is the projection.

Both statements are at coefficients `Ab.{u}`, the universe of the sites' morphisms, so that they
form a coherent pair over one category of abelian sheaves; statement (1) is held to that choice
by the `Ext`-based machinery of Stacks 03YU.  The sheafification and `Ext`-universe hypotheses
are instance binders on the statements rather than side conditions discharged here, exactly as
in the counterpart `AlgebraicGeometry.cohomologyRestrictionIso` for the other five topologies
(Stacks 03YY).

## References

* [Stacks Project, Tag 0F4T](https://stacks.math.columbia.edu/tag/0F4T)
* [Stacks Project, Tag 0F4S](https://stacks.math.columbia.edu/tag/0F4S)
* [Stacks Project, Tag 098K](https://stacks.math.columbia.edu/tag/098K)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.ProEtale

/-- **A big pro-étale site over a scheme is essentially small at the universe of its
morphisms.** It is a slice of the category of schemes below a cardinal, which is essentially
small by Stacks 000J. -/
theorem essentiallySmall_bigProetaleOver (B : BigProetaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : EssentiallySmall.{u} (BigProetaleOver B S hS) := by
  have : EssentiallySmall.{u} B.Scheme := AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  change EssentiallySmall.{u} (CostructuredArrow (𝟭 B.Scheme) (⟨S, hS⟩ : B.Scheme))
  infer_instance

namespace BigProetaleSite.IsContainedIn

variable {B B' : BigProetaleSite.{u}} (h : B.IsContainedIn B')
  (S : AlgebraicGeometry.Scheme.{u}) (hS : B.Contains S)

/-- The inclusion `(Sch/S)_proétale → (Sch'/S)_proétale` is continuous: the continuity half of
`AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.functorOver_isMorphismOfSites`
(Stacks 0F4S). -/
instance functorOver_isContinuous :
    (h.functorOver S hS).IsContinuous (BigProetaleOver.topology B S hS)
      (BigProetaleOver.topology B' S (h.contains hS)) :=
  (h.functorOver_isMorphismOfSites S hS).toIsContinuous

/-- Abelian presheaves on `(Sch/S)_proétale` have pointwise left Kan extensions along the
inclusion into `(Sch'/S)_proétale`, the smaller site being essentially small. -/
instance hasPointwiseLeftKanExtension_op_functorOver
    (P : (BigProetaleOver B S hS)ᵒᵖ ⥤ Ab.{u}) :
    (h.functorOver S hS).op.HasPointwiseLeftKanExtension P :=
  letI : EssentiallySmall.{u} (BigProetaleOver B S hS) := essentiallySmall_bigProetaleOver B S hS
  Stacks.Cohomology.BiggerSite.hasPointwiseLeftKanExtension_op (h.functorOver S hS) P

/-- Abelian presheaves on `(Sch/S)_proétale` have pointwise right Kan extensions along the
inclusion into `(Sch'/S)_proétale`. -/
instance hasPointwiseRightKanExtension_op_functorOver
    (P : (BigProetaleOver B S hS)ᵒᵖ ⥤ Ab.{u}) :
    (h.functorOver S hS).op.HasPointwiseRightKanExtension P :=
  letI : EssentiallySmall.{u} (BigProetaleOver B S hS) := essentiallySmall_bigProetaleOver B S hS
  Stacks.Cohomology.BiggerSite.hasPointwiseRightKanExtension_op (h.functorOver S hS) P

/-! ### Statement (1): cohomology over an object of the smaller site -/

/-- Let `S` be a scheme and let `(Sch/S)_proétale` and `(Sch'/S)_proétale` be two big pro-étale
sites of `S` as in Definition 098K, the first contained in the second.  For any object `U` of
`(Sch/S)_proétale` and any degree `p`,

`H^p(U, ℱ'|_{(Sch/S)_proétale}) = H^p(U, ℱ')`

naturally in the abelian sheaf `ℱ'` on `(Sch'/S)_proétale`, where cohomology over an object is
Mathlib's `Ext`-based `CategoryTheory.Sheaf.cohomologyPresheafFunctor`.

By Stacks 0F4S the localized inclusion is continuous, cocontinuous and preserves finite limits,
and both localized sites are essentially small, so this is Stacks 03YU,
`Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso`. -/
@[stacks 0F4T "part (1), the cohomology over an object of the smaller big pro-étale site of the
  restriction of an abelian sheaf agrees with its cohomology over the image of that object"]
noncomputable def cohomologyRestrictionIso
    [HasSheafify (BigProetaleOver.topology B S hS) Ab.{u}]
    [HasSheafify (BigProetaleOver.topology B' S (h.contains hS)) Ab.{u}]
    [HasExt.{w} (Sheaf (BigProetaleOver.topology B S hS) Ab.{u})]
    [HasExt.{w} (Sheaf (BigProetaleOver.topology B' S (h.contains hS)) Ab.{u})]
    (U : BigProetaleOver B S hS) (p : ℕ) :
    (h.functorOver S hS).sheafPushforwardContinuous Ab.{u}
          (BigProetaleOver.topology B S hS)
          (BigProetaleOver.topology B' S (h.contains hS)) ⋙
        Sheaf.cohomologyPresheafFunctor (BigProetaleOver.topology B S hS) p ⋙
          (evaluation (BigProetaleOver B S hS)ᵒᵖ Ab.{w}).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor (BigProetaleOver.topology B' S (h.contains hS)) p ⋙
        (evaluation (BigProetaleOver B' S (h.contains hS))ᵒᵖ Ab.{w}).obj
          (op ((h.functorOver S hS).obj U)) := by
  let : (h.functorOver S hS).IsCocontinuous (BigProetaleOver.topology B S hS)
      (BigProetaleOver.topology B' S (h.contains hS)) := h.functorOver_isCocontinuous S hS
  let : PreservesFiniteLimits (h.functorOver S hS) := h.functorOver_preservesFiniteLimits S hS
  let : HasFiniteLimits B.Scheme := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : HasFiniteLimits (BigProetaleOver B S hS) := inferInstance
  let : EssentiallySmall.{u} (BigProetaleOver B S hS) :=
    essentiallySmall_bigProetaleOver B S hS
  let : EssentiallySmall.{u} (BigProetaleOver B' S (h.contains hS)) :=
    essentiallySmall_bigProetaleOver B' S (h.contains hS)
  exact Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso
    (BigProetaleOver.topology B S hS) (BigProetaleOver.topology B' S (h.contains hS))
    (h.functorOver S hS) U p

/-! ### Statement (2): extension of an abelian sheaf to the bigger site -/

/-- Restriction of abelian sheaves from `(Sch'/S)_proétale` to `(Sch/S)_proétale`: the
pushforward along the continuous inclusion. -/
noncomputable abbrev abelianRestrictionOver :
    Sheaf (BigProetaleOver.topology B' S (h.contains hS)) Ab.{u} ⥤
      Sheaf (BigProetaleOver.topology B S hS) Ab.{u} :=
  (h.functorOver S hS).sheafPushforwardContinuous Ab.{u}
    (BigProetaleOver.topology B S hS) (BigProetaleOver.topology B' S (h.contains hS))

variable [HasSheafify (BigProetaleOver.topology B' S (h.contains hS)) Ab.{u}]

/-- Restriction of abelian sheaves to the smaller localized big pro-étale site has a left
adjoint, the sheaf pullback along the inclusion. -/
instance isRightAdjoint_abelianRestrictionOver :
    (h.abelianRestrictionOver S hS).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (h.functorOver S hS) Ab.{u}
    (BigProetaleOver.topology B S hS)
    (BigProetaleOver.topology B' S (h.contains hS))).isRightAdjoint

/-- The extension of an abelian sheaf on `(Sch/S)_proétale` to `(Sch'/S)_proétale`: the sheaf
pullback along the inclusion. -/
noncomputable def abelianExtensionOver
    (F : Sheaf (BigProetaleOver.topology B S hS) Ab.{u}) :
    Sheaf (BigProetaleOver.topology B' S (h.contains hS)) Ab.{u} :=
  ((h.functorOver S hS).sheafPullback Ab.{u}
    (BigProetaleOver.topology B S hS)
    (BigProetaleOver.topology B' S (h.contains hS))).obj F

/-- The restriction of
`AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.abelianExtensionOver F` to the smaller
site is `F` itself.  The isomorphism is the inverse of the unit of the adjunction between
pullback and restriction, which is invertible because the pullback is fully faithful
(Stacks 00XU). -/
noncomputable def abelianExtensionOverRestrictionIso
    (F : Sheaf (BigProetaleOver.topology B S hS) Ab.{u}) :
    (h.abelianRestrictionOver S hS).obj (h.abelianExtensionOver S hS F) ≅ F := by
  let G := h.functorOver S hS
  let J := BigProetaleOver.topology B S hS
  let K := BigProetaleOver.topology B' S (h.contains hS)
  let : G.IsCocontinuous J K := h.functorOver_isCocontinuous S hS
  let : G.Full := (h.fullyFaithfulFunctorOver S hS).full
  let : G.Faithful := (h.fullyFaithfulFunctorOver S hS).faithful
  let hff := Functor.full_and_faithful_sheafPullback G Ab.{u} J K
  let : (G.sheafPullback Ab.{u} J K).Full := hff.1
  let : (G.sheafPullback Ab.{u} J K).Faithful := hff.2
  exact (asIso ((G.sheafAdjunctionContinuous Ab.{u} J K).unit.app F)).symm

/-- Let `S` be a scheme and let `(Sch/S)_proétale` and `(Sch'/S)_proétale` be two big pro-étale
sites of `S` as in Definition 098K, the first contained in the second.  For any abelian sheaf
`ℱ` on `(Sch/S)_proétale` there is an abelian sheaf `ℱ'` on `(Sch'/S)_proétale` whose
restriction to `(Sch/S)_proétale` is isomorphic to `ℱ`.

The witness is the sheaf pullback along the inclusion, and the isomorphism is the inverse unit
of the adjunction, invertible by Stacks 00XU. -/
@[stacks 0F4T "part (2), every abelian sheaf on the smaller big pro-étale site is the
  restriction of an abelian sheaf on the bigger site"]
theorem exists_extension_abelianSheaf
    (F : Sheaf (BigProetaleOver.topology B S hS) Ab.{u}) :
    ∃ F' : Sheaf (BigProetaleOver.topology B' S (h.contains hS)) Ab.{u},
      Nonempty ((h.abelianRestrictionOver S hS).obj F' ≅ F) :=
  ⟨h.abelianExtensionOver S hS F, ⟨h.abelianExtensionOverRestrictionIso S hS F⟩⟩

end BigProetaleSite.IsContainedIn

end AlgebraicGeometry.ProEtale

end
