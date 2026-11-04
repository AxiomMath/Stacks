module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.CohomologyPresheafRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousDefs
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Over
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of a site localized at an object

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor between sites and `u^s` the induced direct image of
`𝒜`-valued sheaves. If `u^s` is exact and preserves injective objects — which it is as soon as it
has a right adjoint and an exact left adjoint — then it comes out of a right derived functor, and
the `p`-th cohomology presheaf of `𝒟` applied to `u^s F` is the `p`-th cohomology presheaf of `𝒞`
applied to `F`, restricted along `u`:

`u^s ⋙ R^p Γ_𝒟 ≅ (R^p Γ_𝒞) ⋙ (- ∘ u.op)`,  that is,  `H^p(V, u^s F) ≅ H^p(u V, F)`.

Both sides of the first display are *presheaves* on `𝒟`, so the isomorphism is natural in the
object `V` as well as in the sheaf `F`. That is what distinguishes it from
`Stacks.Cohomology.CompositeRightDerived.statement2_cohomology`, which is the same formula at a
fixed object, for two sites that are small categories in one universe and sheaves of abelian groups
in that universe.

Instantiating `u` at `CategoryTheory.Over.forget X` compares the cohomology of a site with the
cohomology of its localization at an object `X`: for `V` an object of `𝒞/X` and `F` a sheaf on
`𝒞`,

`H^p_{𝒞/X}(V, F|_X) ≅ H^p_𝒞(V.left, F)`.

For sheaves of abelian groups in any universe `w` dominating that of a site `𝒞 : Type u` with
`Category.{v} 𝒞` this needs no hypothesis beyond `UnivLE.{max u v, w}`, sheafification and
enough injectives: both properties of the restriction functor are available, right exactness
because `Over.forget X` is cocontinuous and preservation of injectives because extension by
zero is left exact.

## Main results

In the namespace `Stacks.Cohomology.SheafifiedHigherDirectImage`:

* `pushforwardRightDerivedSheafToPresheafIso`: the isomorphism of cohomology presheaves above.
* `pushforwardRightDerivedSectionsIso`: its objectwise form, `H^p(V, u^s F) ≅ H^p(u V, F)`.
* `preservesFiniteColimits_pushforwardOfContinuous`,
  `preservesInjectiveObjects_pushforwardOfContinuous`: the two hypotheses of those two
  isomorphisms, from the two adjoints of `u^s` and the left exactness of the left one.

In the namespace `Stacks.Cohomology.LocalizedSite`:

* `preservesFiniteColimits_overPullback`, `preservesFiniteColimits_overMapPullback`: restriction
  to a localization, and restriction along a morphism of localizations, are right exact on
  sheaves of abelian groups, with no adjoint of the restriction required.
* `preservesInjectiveObjects_overPullback`: restriction to a localization preserves injective
  abelian sheaves.
* `overPullbackRightDerivedSheafToPresheafIso`, `overPullbackRightDerivedSectionsIso`: the
  cohomology of a localized site, as presheaves and objectwise.

## Implementation notes

The engine is `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, which takes an
exact injective-preserving functor out of a right derived functor on the left, together with
`pushforwardCohomologyPresheafRestrictionIso`, which takes the exact functor `(- ∘ u.op)` out on
the right. The two fit together because
`CategoryTheory.Functor.sheafPushforwardContinuousCompSheafToPresheafIso` is the identity
isomorphism, so `u^s ⋙ sheafToPresheaf J A` is `pushforwardCohomologyPresheaf A u` on the nose.

The general isomorphisms take `PreservesFiniteColimits` and `PreservesInjectiveObjects` for `u^s`
as hypotheses rather than the adjunction data that
`preservesFiniteColimits_pushforwardOfContinuous` and
`preservesInjectiveObjects_pushforwardOfContinuous` derive them from, because the localized case
below establishes right exactness by a different route: almost cocontinuity
([Stacks, Tag 04BD]) rather than a right adjoint, which avoids asking for pointwise right Kan
extensions along `u.op` — an assumption that ties the universe of the sections to that of the
site and is not available for a localization.

`preservesInjectiveObjects_overPullback` must not be proved by instance search:
`extensionByZero_preservesMonos` is invoked by name and the adjunction is supplied explicitly,
for the reason recorded in the comment at that lemma, namely that the draft libraries expose an
unproved `PreservesMonomorphisms` instance for the left adjoint of the restriction which instance
search would select in preference to the genuine route through finite limits.

**The coefficient universe.** The localized statements are for `Ab.{w}` with the coefficient
universe `w` only required to dominate that of the site, `UnivLE.{max u v, w}`. That hypothesis
is where the left exactness of extension by zero lives: the pointwise value of the left Kan
extension along `(Over.forget X).op` is a coproduct indexed by `Hom(V, X)`, and Grothendieck's
AB4 has to be applied to `Ab.{w}` at that index size, so the index type is transported into
`Type w` along two equivalences of discrete categories before AB4 is invoked (see
`costructuredArrow_hasExactColimitsOfShape`). In particular a site whose objects form a
`Type (u + 1)` with morphisms in `Type u` and whose coefficients are
`AddCommGrpCat.{max (u + 1) v}` — a slice of the locally quasi-compact Zariski site, say — is
covered, since `UnivLE.{u + 1, max (u + 1) v}` holds unconditionally. Nothing else in the chain
below is universe-restricted.

## References

* [Stacks Project, Tag 01DR](https://stacks.math.columbia.edu/tag/01DR)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.SheafifiedHigherDirectImage

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (A : Type*) [Category* A] [Abelian A] [HasSheafify J A] [HasSheafify K A]
  (u : D ⥤ C) [u.IsContinuous J K]

omit [Abelian A] [HasSheafify J A] [HasSheafify K A] in
/-- **The direct image along a continuous and cocontinuous functor is right exact** once it has a
right adjoint, being then a left adjoint. Together with left exactness, which holds for every
continuous functor, this makes it exact. -/
theorem preservesFiniteColimits_pushforwardOfContinuous [u.IsCocontinuous J K]
    [∀ P : Dᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    PreservesFiniteColimits (u.sheafPushforwardContinuous A J K) :=
  have : PreservesColimitsOfSize.{0, 0} (u.sheafPushforwardContinuous A J K) :=
    (u.sheafAdjunctionCocontinuous A J K).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

omit [Abelian A] [HasSheafify J A] [HasSheafify K A] in
/-- **The direct image along a continuous functor preserves injective sheaves** once its left
adjoint `u_!` exists and preserves monomorphisms ([Stacks, Tag 015Z]). -/
theorem preservesInjectiveObjects_pushforwardOfContinuous
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u.sheafPullback A J K).PreservesMonomorphisms] :
    (u.sheafPushforwardContinuous A J K).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (u.sheafAdjunctionContinuous A J K)

variable [EnoughInjectives (Sheaf K A)] [EnoughInjectives (Sheaf J A)]
  [PreservesFiniteColimits (u.sheafPushforwardContinuous A J K)]
  [(u.sheafPushforwardContinuous A J K).PreservesInjectiveObjects]

/-- **The cohomology presheaf of a restricted sheaf is the restricted cohomology presheaf.** For a
continuous `u` whose direct image is exact and preserves injectives, the presheaf
`V ↦ H^p(V, u^s F)` on `𝒟` is the presheaf `U ↦ H^p(U, F)` on `𝒞` restricted along `u`, naturally
in `F`.

The exact direct image comes out of the right derived functor on the left
(`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`), leaving the right derived
functor of
`u^s ⋙ sheafToPresheaf J A`, which *is* `pushforwardCohomologyPresheaf A u`; the exact
precomposition with `u.op` then comes out on the right
(`pushforwardCohomologyPresheafRestrictionIso`). -/
@[sga "7 VI 3.1(c)" "more general"]
def pushforwardRightDerivedSheafToPresheafIso (p : ℕ) :
    u.sheafPushforwardContinuous A J K ⋙ (sheafToPresheaf J A).rightDerived p ≅
      (sheafToPresheaf K A).rightDerived p ⋙ (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj u.op :=
  (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
        (u.sheafPushforwardContinuous A J K) (sheafToPresheaf J A) p).symm ≪≫
    pushforwardCohomologyPresheafRestrictionIso A u p

/-- **[Stacks, Tag 03YU], statement 2, for arbitrary sites and arbitrary abelian coefficients.**
Cohomology over `V` of the restriction of `F` along `u` is the cohomology of `F` over `u V`,
naturally in `F`.

This is `pushforwardRightDerivedSheafToPresheafIso` evaluated at `V`, using that evaluation of
presheaves is exact (`sheafToPresheafRightDerivedEvaluationIso`) and that restricting a presheaf
along `u.op` and then evaluating at `V` is evaluating at `u V`. -/
@[sga "7 VI 3.1(c)" "more general"]
def pushforwardRightDerivedSectionsIso (p : ℕ) (V : D) :
    u.sheafPushforwardContinuous A J K ⋙
        (sheafToPresheaf J A ⋙ (evaluation Dᵒᵖ A).obj (op V)).rightDerived p ≅
      (sheafToPresheaf K A ⋙ (evaluation Cᵒᵖ A).obj (op (u.obj V))).rightDerived p :=
  Functor.isoWhiskerLeft (u.sheafPushforwardContinuous A J K)
      (sheafToPresheafRightDerivedEvaluationIso A p V) ≪≫
    Functor.isoWhiskerRight (pushforwardRightDerivedSheafToPresheafIso A u p)
        ((evaluation Dᵒᵖ A).obj (op V)) ≪≫
      (sheafToPresheafRightDerivedEvaluationIso A p (u.obj V)).symm

end Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Cohomology.LocalizedSite

universe v u w

open Stacks.Cohomology.SheafifiedHigherDirectImage

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Restriction to a localized site is right exact on sheaves of abelian groups.** The
forgetful functor `𝒞/X ⥤ 𝒞` is cocontinuous, hence almost cocontinuous, so the right exact half
of [Stacks, Tag 04BD] applies to its direct image, which is the restriction. Nothing beyond
sheafification on the two sites is needed; in particular no adjoint of the restriction has to be
produced. -/
theorem preservesFiniteColimits_overPullback (X : C)
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    PreservesFiniteColimits (J.overPullback AddCommGrpCat.{w} X) :=
  Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isAlmostCocontinuous
    (Over.forget X) (J.over X) J
    (isAlmostCocontinuous_of_isCocontinuous (Over.forget X) (J.over X) J)

/-- **Restriction along a morphism of localized sites is right exact on sheaves of abelian
groups**, by the argument of `preservesFiniteColimits_overPullback`: `Over.map f` is cocontinuous
for the localized topologies, hence almost cocontinuous. -/
theorem preservesFiniteColimits_overMapPullback {X Y : C} (f : X ⟶ Y)
    [HasSheafify (J.over X) AddCommGrpCat.{w}] [HasSheafify (J.over Y) AddCommGrpCat.{w}]
    [(J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{w} f) :=
  Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isAlmostCocontinuous
    (Over.map f) (J.over X) (J.over Y)
    (isAlmostCocontinuous_of_isCocontinuous (Over.map f) (J.over X) (J.over Y))

variable [UnivLE.{max u v, w}] [HasSheafify J Ab.{w}] [∀ U : C, HasSheafify (J.over U) Ab.{w}]

/-- **Restriction to a localized site preserves injective abelian sheaves.** Its left adjoint is
extension by zero, which is left exact ([Stacks, Tag 01DR]), so the right adjoint preserves
injectives. This is the functor-level form of `overPullback_preservesInjective`.

The adjunction and the mono-preservation are supplied by name rather than found by instance
search, for the reason recorded at `extensionByZero_preservesMonos`. -/
@[sga "4 V 2.2" "special case"]
theorem preservesInjectiveObjects_overPullback (X : C) :
    (J.overPullback Ab.{w} X).PreservesInjectiveObjects :=
  have : (J.overPullback Ab.{w} X).leftAdjoint.PreservesMonomorphisms :=
    extensionByZero_preservesMonos J X
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Adjunction.ofIsRightAdjoint (J.overPullback Ab.{w} X))

variable [EnoughInjectives (Sheaf J Ab.{w})]

/-- **The cohomology presheaf of a localized site.** The `p`-th cohomology presheaf of `𝒞/X`
applied to the restriction of a sheaf `F` on `𝒞` is the `p`-th cohomology presheaf of `𝒞` applied
to `F`, restricted along `Over.forget X`; equivalently, for an object `V` of `𝒞/X`,
`H^p_{𝒞/X}(V, F|_X) ≅ H^p_𝒞(V.left, F)`, naturally in `V` and in `F`.

This is the second item of the `TODO` of Mathlib's
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`, for right derived functors of sections
rather than for the `Ext`-theoretic `Sheaf.H`. -/
def overPullbackRightDerivedSheafToPresheafIso (X : C)
    [J.WEqualsLocallyBijective Ab.{w}]
    [EnoughInjectives (Sheaf (J.over X) Ab.{w})] (p : ℕ) :
    J.overPullback Ab.{w} X ⋙ (sheafToPresheaf (J.over X) Ab.{w}).rightDerived p ≅
      (sheafToPresheaf J Ab.{w}).rightDerived p ⋙
        (Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ Ab.{w}).obj (Over.forget X).op :=
  haveI := preservesFiniteColimits_overPullback.{v, u, w} J X
  haveI := preservesInjectiveObjects_overPullback J X
  pushforwardRightDerivedSheafToPresheafIso Ab.{w} (Over.forget X) p

/-- **Cohomology of a localized site, objectwise.** For an object `V` of `𝒞/X`, the cohomology
over `V` of the restriction of `F` to the localized site is the cohomology of `F` over `V.left`,
naturally in `F`. Taking `V` to be the terminal object `𝟙 X` of `𝒞/X` gives the global cohomology
of the localized site as the cohomology of `𝒞` over `X`. -/
def overPullbackRightDerivedSectionsIso (X : C)
    [J.WEqualsLocallyBijective Ab.{w}]
    [EnoughInjectives (Sheaf (J.over X) Ab.{w})] (p : ℕ) (V : Over X) :
    J.overPullback Ab.{w} X ⋙
        (sheafToPresheaf (J.over X) Ab.{w} ⋙
          (evaluation (Over X)ᵒᵖ Ab.{w}).obj (op V)).rightDerived p ≅
      (sheafToPresheaf J Ab.{w} ⋙
        (evaluation Cᵒᵖ Ab.{w}).obj (op V.left)).rightDerived p :=
  haveI := preservesFiniteColimits_overPullback.{v, u, w} J X
  haveI := preservesInjectiveObjects_overPullback J X
  pushforwardRightDerivedSectionsIso Ab.{w} (Over.forget X) p V

end Stacks.Cohomology.LocalizedSite

end
