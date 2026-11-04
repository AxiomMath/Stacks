module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.Morphism
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Morphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# The total ringed site and the degreewise ringed augmentations

Let `(C, O_C)` be a ringed site and let `K` be a simplicial semi-representable object of `C`.
Stacks 0D9W assembles the constructions of Stacks 0D8B and 0D9U into ringed data: the total
localization site carries the pulled-back structure sheaf `O = a⁻¹O_C`, and in each simplicial
degree the localization `C/K_n` is augmented over `C` by a morphism of ringed topoi
`a_n : (Sh(C/K_n), O_n) ⟶ (Sh(C), O_C)`.

This file supplies those two: the total ringed site, and the degreewise augmentation. The
underlying site, its topology and the pulled-back structure sheaf are already available, so the
first is the bundle of the three; the second is the augmentation of a localization at a single
semi-representable object, instantiated at the degree-`n` term of `K`.

## Main definitions

* `CategoryTheory.SemiRepresentable.Simplicial.totalRingedSite`: the total localization site
  with the pulled-back structure sheaf, as a ringed site.
* `AlgebraicGeometry.RingedSite.familyAugmentationMorphismOfTopoi`: the morphism of topoi
  underlying the augmentation of a semi-representable localization over the ambient site.
* `AlgebraicGeometry.RingedSite.familyAugmentationInverseImageCommRingIso`: the identification
  of the inverse image of `O_C` under that morphism with the localization structure sheaf.
* `AlgebraicGeometry.RingedSite.familyAugmentationCommRingFsharpAdjoint`: the structure map of
  the augmentation in direct-image form.
* `AlgebraicGeometry.RingedSite.familyRingedAugmentation`: the augmentation of a
  semi-representable localization, as a morphism of ringed topoi.
* `CategoryTheory.SemiRepresentable.Simplicial.degreewiseRingedAugmentation`: the augmentation
  in each simplicial degree.
* `AlgebraicGeometry.RingedSite.liftedRingedSite`: a ringed site with its structure sheaf
  presented in a larger universe of sections.
* `CategoryTheory.SemiRepresentable.Simplicial.totalAugmentationInverseImageCommRingIso` and
  `.totalAugmentationCommRingFsharpAdjoint`: the structure map of the total augmentation in
  its inverse-image and direct-image forms.
* `CategoryTheory.SemiRepresentable.Simplicial.totalRingedAugmentationAtLargeUniverse`: the
  total augmentation for a structure sheaf whose universe of sections already contains the
  total localization site.
* `CategoryTheory.SemiRepresentable.Simplicial.totalRingedAugmentation`: the augmentation
  `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` of the total ringed site.
* `CategoryTheory.SemiRepresentable.Simplicial.ringedTransitionMorphism`: the morphism of
  ringed topoi induced by a simplex map.

## Main results

* `CategoryTheory.SemiRepresentable.Simplicial.pulledBackRingSheaf_eq`: the sheaf of rings
  underlying the structure sheaf of the total ringed site is the one already recorded for the
  pulled-back structure sheaf.
* `AlgebraicGeometry.RingedSite.familyAugmentationInverseImageCommRingIso_forget`: the
  identification is the identity on underlying sheaves of sets.
* `AlgebraicGeometry.SheafOfModules.commRingCatULift_preservesLimitsOfSize`: the universe lift
  of commutative rings preserves limits, so composing a sheaf with it leaves a sheaf.
* `CategoryTheory.SemiRepresentable.Simplicial.ringedTransitionMorphism_isFlat`: every
  transition morphism of the simplicial ringed site is flat.
* `CategoryTheory.SemiRepresentable.Simplicial.ringedTransitionMorphism_eq`: the transition
  morphism is the Stacks 0D9U morphism of semi-representable objects at the simplex map.
* `AlgebraicGeometry.SheafOfModules.isFlatMapULift_of_isIso`: an isomorphism of sheaves of
  commutative rings is flat in the universe-lifted sense.
* `AlgebraicGeometry.RingedSite.familyRingedAugmentation_fSharpInverseImage` and
  `…Simplicial.totalRingedAugmentationAtLargeUniverse_fSharpInverseImage`: the structure maps of
  the two augmentations, read in inverse-image form, are the identifications of the inverse
  image of `O_C` with the localized structure sheaf.
* `AlgebraicGeometry.RingedSite.familyRingedAugmentation_isFlat`: the augmentation of a
  semi-representable localization is flat.
* `CategoryTheory.SemiRepresentable.Simplicial.degreewiseRingedAugmentation_isFlat`: every
  degreewise augmentation `a_n` is flat.
* `CategoryTheory.SemiRepresentable.Simplicial.totalRingedAugmentation_isFlat`: the total
  augmentation `a` is flat.

## Implementation notes

The augmentation of the localization at a semi-representable object `K` is the exact analogue,
one level up, of the augmentation of the localization at a single object recorded as
`AlgebraicGeometry.RingedSite.localizationRingedToposHom`: the functor `Over.forget U` is
replaced by `CategoryTheory.SemiRepresentable.LocalizationSites.localizationFunctor` of the
degenerate datum `⟨K, K, 𝟙 K⟩`, whose continuity and cocontinuity are Stacks 0D85, and the
identification of the inverse image of the structure sheaf with its restriction is the generic
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`. The structure map is the adjunct of that
identification, which is what `AlgebraicGeometry.RingedToposHom` takes as its data; by
construction of `AlgebraicGeometry.RingedSite.localizationStructureSheaf` the identification's
codomain is the structure sheaf of the localized ringed topos on the nose, so there is nothing
to compare.

Left exactness of the inverse image is the Stacks 04J4 instance
`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous`. It is applied
positionally rather than by instance search: the continuity hypothesis it carries is in scope
only as a local instance on `LocalizationSites.sourceTopology`, which is a plain `def`, so
synthesis does not see through it, while unification does once the lemma is applied.

The structure-sheaf universe is `max x u v w`, which is what the augmentation's topoi need: the
right adjoint to restriction along the localization functor forms products over the fibres of
the component index, whose universe is `x`. The site's object, morphism and component-index
universes stay independent.

The total augmentation `a` of item (2) is the same construction at the total localization
functor `j_total` rather than at a semi-representable localization functor: its morphism of
topoi is
`CategoryTheory.SemiRepresentable.Simplicial.localizationAugmentation` of Stacks 0D8B, and its
structure map is again the adjunct of `restrictionCommRingIso`, whose codomain is the
pulled-back structure sheaf of the total ringed site on the nose. The source states item (2)
with no universe hypothesis, so the tagged form takes an arbitrary ringed site and lifts its
structure sheaf internally; `totalRingedAugmentationAtLargeUniverse` is the same morphism for a
structure sheaf whose universe of sections is already large enough, and is the form the
degreewise and left-adjoint siblings of this tag consume.

Lifting the structure sheaf needs `sheafCompose` for the universe lift of commutative rings,
which needs that lift to preserve limits. The lift itself is
`AlgebraicGeometry.SheafOfModules.commRingCatULift`, so no second copy is introduced; what is
new here is its limit preservation, proved through `CategoryTheory.uliftFunctor` on underlying
types and the fact that `forget CommRingCat` creates limits.

The transition morphism of a simplex map is the Stacks 0D9U morphism of semi-representable
objects applied to `K.map φ.op`, exactly as the degreewise augmentation is the family-level
augmentation applied to `K.obj (op n)`, and its flatness is 0D9U's `f_flat` at the same
morphism. It is named `ringedTransitionMorphism` rather than `transitionMorphism` because
`CategoryTheory.SimplicialSiteSituation.transitionMorphism` is a different notion — a morphism
of topoi of a simplicial site situation, not a morphism of ringed topoi of a componentwise
localization.

Flatness of all three augmentations is one argument: the structure map in inverse-image form is
by construction the adjunct of `restrictionCommRingIso`, so the inverse-image form is that
identification itself, and an isomorphism of sheaves of commutative rings is flat. The last step
is `AlgebraicGeometry.SheafOfModules.isFlatMap_of_isIso`, reached through
`isFlatMapULift_of_isIso`, which takes the isomorphism as an explicit hypothesis: the morphisms
here carry `HasSheafCompose` arguments that instance search does not unfold, so an instance
argument is not synthesizable at the use sites although the term is available by name.

The six universe arguments of the flatness predicate have to be written out at every use. They
occur only inside its implicit ringed topoi and its four instance arguments, so they are not
determined by the explicit argument, and Lean defaults them to `0` rather than reporting a
universe constraint; with the lists dropped the statements still elaborate, at
`RingedSite.{0, 0, 0}`, and say nothing.

`familyRingedAugmentation_isFlat` is deliberately untagged: the augmentation it is about is
Stacks 0D9U's localization morphism `j`, and flatness of `j` is that remark's own key, asserted
there together with exactness of `j⁎`. It is recorded for the slot that lands 0D9U, as
`familyRingedAugmentation` itself already is.

Recorded rather than acted on: this file's `familyAugmentation*` triple, the total triple added
here, and `AlgebraicGeometry.RingedSite.localizationRingedToposHom` of Stacks 04IX are three
instances of one construction — the augmentation of a restriction along a continuous and
cocontinuous functor of sites, with the adjunct of `restrictionCommRingIso` as its structure
map. Factoring them through one generic declaration is a repository-level change that would
rewrite the bodies of declarations other tags already depend on, so it is left as a lead. A
second such lead: the flatness predicate used here,
`Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat`, has a permanent twin
`AlgebraicGeometry.RingedToposHom.IsFlat` carrying the Stacks 04JB key, with a
character-identical signature and equal to it as a function;
repointing this family at the twin would change the statement of the tagged
`AlgebraicGeometry.RingedSite.familyMorphism_isFlat` upstream, so it is also left as a lead.

## References

* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open CategoryTheory.SemiRepresentable

universe x u v w i j z

namespace CategoryTheory.SemiRepresentable.Simplicial

/-- **Stacks 0D9W, total ringed site.** The total localization of a simplicial
semi-representable object `K` of the underlying site of a ringed site `X`, equipped with the
pulled-back structure sheaf `a⁻¹O_C`. -/
@[stacks 0D9W "total_ringed_site", stacks 0D9X "ringed_total_site"]
def totalRingedSite (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) : AlgebraicGeometry.RingedSite where
  C := TotalLocalization K
  J := totalLocalizationTopology K X.J
  O := pulledBackStructureSheaf X K

/-- The sheaf of rings underlying the structure sheaf of the total ringed site is the sheaf of
rings already recorded for the pulled-back structure sheaf. -/
@[simp]
theorem pulledBackRingSheaf_eq (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    pulledBackRingSheaf X K = (Stacks.SheafOfModules.Tensor.ringSheaf (totalRingedSite X K).O) :=
  rfl

end CategoryTheory.SemiRepresentable.Simplicial

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max x u v w}) (K : FormalCoproduct.{x} X.C)

/-- The morphism of topoi underlying the augmentation of the localization at a
semi-representable object `K` over the ambient site: its inverse image is restriction along the
localization functor `C/K ⥤ C` and its direct image is the right Kan extension along it. -/
def familyAugmentationMorphismOfTopoi :
    MorphismOfTopoi (localizationRingedTopos X K).Topos (ringedTopos.{u, v, max x w} X).Topos :=
  letI S : LocalizationSites.{x} X.C X.J := ⟨K, K, 𝟙 K⟩
  letI := LocalizationSites.localizationFunctor_isContinuous S
  letI := LocalizationSites.localizationFunctor_isCocontinuous S
  { inverseImage := S.localizationFunctor.sheafPushforwardContinuous
      (Type (max x u v w)) S.sourceTopology X.J
    pushforward := S.localizationFunctor.sheafPushforwardCocontinuous
      (Type (max x u v w)) S.sourceTopology X.J
    adj := S.localizationFunctor.sheafAdjunctionCocontinuous
      (Type (max x u v w)) S.sourceTopology X.J
    preservesFiniteLimits :=
      CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous
        S.sourceTopology X.J S.localizationFunctor (Type (max x u v w)) }

/-- The inverse image of the structure sheaf `O_C` under the augmentation *is* the structure
sheaf `O_K` of the localization: both are restriction of `O_C` along the localization functor,
so the comparison is the canonical identity identification. -/
def familyAugmentationInverseImageCommRingIso :
    (inverseImageCommRingFunctor (familyAugmentationMorphismOfTopoi.{x, u, v, w} X K)).obj X.O ≅
      (localizationRingedTopos X K).O :=
  letI S : LocalizationSites.{x} X.C X.J := ⟨K, K, 𝟙 K⟩
  letI := LocalizationSites.localizationFunctor_isContinuous S
  restrictionCommRingIso S.sourceTopology X.J S.localizationFunctor X.O

/-- The identification of the inverse image of `O_C` with `O_K` is the identity on underlying
sheaves of sets. -/
@[simp]
theorem familyAugmentationInverseImageCommRingIso_forget :
    (localizationRingedTopos X K).forgetRing.map
        (familyAugmentationInverseImageCommRingIso.{x, u, v, w} X K).hom =
      𝟙 ((localizationRingedTopos X K).forgetRing.obj (localizationRingedTopos X K).O) :=
  rfl

/-- The structure map of the augmentation in direct-image form, `O_C ⟶ a_*O_K`: the adjunct of
`familyAugmentationInverseImageCommRingIso` under the adjunction `a⁻¹ ⊣ a_*` for sheaves of
commutative rings. This is what a morphism of ringed topoi takes as its data. -/
def familyAugmentationCommRingFsharpAdjoint :
    X.O ⟶ (pushforwardCommRingFunctor (familyAugmentationMorphismOfTopoi.{x, u, v, w} X K)).obj
      (localizationRingedTopos X K).O :=
  (commRingImageAdjunction (familyAugmentationMorphismOfTopoi.{x, u, v, w} X K)).homEquiv _ _
    (familyAugmentationInverseImageCommRingIso.{x, u, v, w} X K).hom

/-- The augmentation of the localization at a semi-representable object `K`, as a morphism of
ringed topoi `(Sh(C/K), O_K) ⟶ (Sh(C), O_C)`. -/
def familyRingedAugmentation :
    RingedToposHom (localizationRingedTopos X K) (ringedTopos.{u, v, max x w} X) where
  toToposHom := familyAugmentationMorphismOfTopoi.{x, u, v, w} X K
  fSharp := familyAugmentationCommRingFsharpAdjoint.{x, u, v, w} X K

/-- The augmentation and its underlying morphism of topoi agree. -/
@[simp]
theorem familyRingedAugmentation_toToposHom :
    (familyRingedAugmentation.{x, u, v, w} X K).toToposHom =
      familyAugmentationMorphismOfTopoi.{x, u, v, w} X K :=
  rfl

end AlgebraicGeometry.RingedSite

namespace CategoryTheory.SemiRepresentable.Simplicial

/-- **Stacks 0D9W, degreewise ringed augmentations.** For a simplicial semi-representable
object `K` of the underlying site of a ringed site `X`, each simplicial degree carries a
morphism of ringed topoi `a_n : (Sh(C/K_n), O_n) ⟶ (Sh(C), O_C)` from the localization at the
degree-`n` term to the ambient ringed topos. -/
@[stacks 0D9W "degreewise_ringed_augmentations"]
def degreewiseRingedAugmentation (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) (n : SimplexCategory) :
    AlgebraicGeometry.RingedToposHom
      (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op n)))
      (AlgebraicGeometry.RingedSite.ringedTopos.{u, v, max x w} X) :=
  AlgebraicGeometry.RingedSite.familyRingedAugmentation.{x, u, v, w} X (K.obj (op n))

/-- The degreewise augmentation is the augmentation of the localization at the degree-`n`
term. -/
@[simp]
theorem degreewiseRingedAugmentation_eq (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) (n : SimplexCategory) :
    degreewiseRingedAugmentation.{x, u, v, w} X K n =
      AlgebraicGeometry.RingedSite.familyRingedAugmentation.{x, u, v, w} X (K.obj (op n)) :=
  rfl

end CategoryTheory.SemiRepresentable.Simplicial

namespace AlgebraicGeometry.SheafOfModules

/-- The universe lift of commutative rings preserves any limit: it preserves the limit of the
underlying types, by `CategoryTheory.uliftFunctor`, and `forget CommRingCat` creates limits. -/
instance commRingCatULift_preservesLimit {I : Type i} [Category.{j} I]
    (K : I ⥤ CommRingCat.{w}) : PreservesLimit K (commRingCatULift.{w, z}) where
  preserves lc := by
    let h := isLimitOfPreserves CategoryTheory.uliftFunctor.{z}
      (isLimitOfPreserves (forget CommRingCat) lc)
    have hsmall : Small.{max w z}
        (((K ⋙ commRingCatULift.{w, z}) ⋙ forget CommRingCat).sections) :=
      (Types.hasLimit_iff_small_sections _).mp ⟨_, h⟩
    have : ReflectsLimit (K ⋙ commRingCatULift.{w, z}) (forget CommRingCat) :=
      createsLimitOfReflectsIsomorphismsOfPreserves.toReflectsLimit
    exact ⟨isLimitOfReflects (forget CommRingCat) h⟩

/-- The universe lift of commutative rings preserves limits of any shape. -/
instance commRingCatULift_preservesLimitsOfShape {I : Type i} [Category.{j} I] :
    PreservesLimitsOfShape I (commRingCatULift.{w, z}) where

/-- The universe lift of commutative rings preserves limits of any size; consequently
composing a sheaf of commutative rings with it leaves a sheaf. -/
instance commRingCatULift_preservesLimitsOfSize :
    PreservesLimitsOfSize.{j, i} (commRingCatULift.{w, z}) where

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.RingedSite

/-- A ringed site with its structure sheaf presented in a larger universe of sections: the
site and its topology are unchanged, and the structure sheaf is composed with the universe
lift of commutative rings. -/
abbrev liftedRingedSite (X : RingedSite.{u, v, w}) : RingedSite.{u, v, max x u v w} where
  C := X.C
  J := X.J
  O := (sheafCompose X.J (SheafOfModules.commRingCatULift.{w, max x u v})).obj X.O

end AlgebraicGeometry.RingedSite

namespace CategoryTheory.SemiRepresentable.Simplicial

/-- The inverse image of `O_C` under the total augmentation *is* the structure sheaf `O` of the
total ringed site: both are restriction of `O_C` along `j_total`, so the comparison is the
canonical identity identification. -/
def totalAugmentationInverseImageCommRingIso
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        (localizationAugmentation.{x, v, u, w} K X.J)).obj X.O ≅
      (totalRingedSite.{x, u, v, max x u v w} X K).O :=
  restrictionCommRingIso (totalLocalizationTopology K X.J) X.J
    (totalLocalizationFunctor K) X.O

/-- The structure map of the total augmentation in direct-image form, `O_C ⟶ a_*O`: the adjunct
of `totalAugmentationInverseImageCommRingIso` under `a⁻¹ ⊣ a_*` for sheaves of commutative
rings. -/
def totalAugmentationCommRingFsharpAdjoint
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    X.O ⟶ (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
      (localizationAugmentation.{x, v, u, w} K X.J)).obj
      (totalRingedSite.{x, u, v, max x u v w} X K).O :=
  (Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
      (localizationAugmentation.{x, v, u, w} K X.J)).homEquiv _ _
    (totalAugmentationInverseImageCommRingIso.{x, u, v, w} X K).hom

/-- The augmentation of the total ringed site, for a structure sheaf whose universe of sections
already contains the total localization site. -/
def totalRingedAugmentationAtLargeUniverse
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    AlgebraicGeometry.RingedToposHom
      (AlgebraicGeometry.RingedSite.ringedTopos.{max u v x, v, w}
        (totalRingedSite.{x, u, v, max x u v w} X K))
      (AlgebraicGeometry.RingedSite.ringedTopos.{u, v, max x w} X) where
  toToposHom := localizationAugmentation.{x, v, u, w} K X.J
  fSharp := totalAugmentationCommRingFsharpAdjoint.{x, u, v, w} X K

/-- **Stacks 0D9W, ringed augmentation.** For a simplicial semi-representable object `K` of the
underlying site of a ringed site `X`, the total ringed site is augmented over `X` by a morphism
of ringed topoi `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)`. -/
@[stacks 0D9W "ringed_augmentation"]
def totalRingedAugmentation (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    AlgebraicGeometry.RingedToposHom
      (AlgebraicGeometry.RingedSite.ringedTopos.{max u v x, v, w}
        (totalRingedSite (AlgebraicGeometry.RingedSite.liftedRingedSite.{x, u, v, w} X) K))
      (AlgebraicGeometry.RingedSite.ringedTopos.{u, v, max x w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x, u, v, w} X)) :=
  totalRingedAugmentationAtLargeUniverse.{x, u, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x, u, v, w} X) K

/-- The total augmentation and its underlying morphism of topoi agree. -/
@[simp]
theorem totalRingedAugmentationAtLargeUniverse_toToposHom
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    (totalRingedAugmentationAtLargeUniverse.{x, u, v, w} X K).toToposHom =
      localizationAugmentation.{x, v, u, w} K X.J :=
  rfl

/-- The morphism of ringed topoi `f_φ` attached to a simplex map `φ : [m] ⟶ [n]`, between the
componentwise localizations of `X` at `K_n` and at `K_m`. Its inverse image is restriction
along the componentwise relocalization functor and its structure map is the canonical identity
comparison, which is an isomorphism. -/
def ringedTransitionMorphism (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    let S : LocalizationSites.{x} X.C X.J :=
      ⟨K.obj (op n), K.obj (op m), K.map φ.op⟩
    { g : AlgebraicGeometry.RingedToposHom
        (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op n)))
        (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op m))) //
      (g.toToposHom.inverseImage ⋙
          sheafToPresheaf S.sourceTopology (Type (max x u v w)) =
        sheafToPresheaf S.targetTopology (Type (max x u v w)) ⋙
          (CategoryTheory.Functor.whiskeringLeft _ _ _).obj
            S.relocalizationFunctor.op) ∧
      (∃ h : (AlgebraicGeometry.RingedSite.localizationRingedTopos X
            (K.obj (op n))).forgetRing.obj
          ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor g.toToposHom).obj
            (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op m))).O) =
          (AlgebraicGeometry.RingedSite.localizationRingedTopos X
            (K.obj (op n))).forgetRing.obj
            (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op n))).O,
        (AlgebraicGeometry.RingedSite.localizationRingedTopos X
            (K.obj (op n))).forgetRing.map g.fSharpInverseImage = eqToHom h) ∧
      IsIso g.fSharpInverseImage } :=
  AlgebraicGeometry.RingedSite.familyMorphism.{x, v, u, w} X (K.map φ.op)

/-- The transition morphism is the Stacks 0D9U morphism of semi-representable objects attached
to the image of the simplex map. -/
@[simp]
theorem ringedTransitionMorphism_eq (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ringedTransitionMorphism.{x, u, v, w} X K φ =
      AlgebraicGeometry.RingedSite.familyMorphism.{x, v, u, w} X (K.map φ.op) :=
  rfl

/-- **Stacks 0D9W, flat transition morphisms.** For a simplicial semi-representable object `K`
of the underlying site of a ringed site `X`, the morphism of ringed topoi attached to a simplex
map `φ : [m] ⟶ [n]` is flat. -/
@[stacks 0D9W "flat_transition_morphisms"]
theorem ringedTransitionMorphism_isFlat
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{max u v x, max u v x,
        max x u v w, max u v x, max u v x, max x u v w}
      (ringedTransitionMorphism.{x, u, v, w} X K φ).val :=
  AlgebraicGeometry.RingedSite.familyMorphism_isFlat.{x, v, u, w} X (K.map φ.op)

end CategoryTheory.SemiRepresentable.Simplicial


namespace AlgebraicGeometry.SheafOfModules

/-- An isomorphism of sheaves of commutative rings is flat in the universe-lifted sense: the
lift is a functor, so it carries the isomorphism to an isomorphism, and an isomorphism is flat.

The isomorphism is taken as an explicit hypothesis rather than as an instance argument, because
at the use sites the morphism is the structure map of a morphism of ringed topoi, whose own
`HasSheafCompose` arguments instance search does not unfold. -/
theorem isFlatMapULift_of_isIso {C : Type i} [Category.{j} C]
    {J : GrothendieckTopology C} {O O' : Sheaf J CommRingCat.{z}} (f : O ⟶ O')
    (hf : IsIso f) : IsFlatMapULift.{z, i, j} f := by
  have := hf
  have : HasSheafify J AddCommGrpCat.{max z i j} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max z i j, j, i} J
  have : J.WEqualsLocallyBijective AddCommGrpCat.{max z i j} :=
    wEqualsLocallyBijective_addCommGrpCat.{max z i j, i, j} J
  exact isFlatMap_of_isIso ((sheafULift.{z, i, j} J).map f)

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max x u v w}) (K : FormalCoproduct.{x} X.C)

/-- The structure map of the augmentation of a semi-representable localization, read in
inverse-image form, is the identification `familyAugmentationInverseImageCommRingIso`: the
direct-image form is by definition that identification's adjunct. -/
theorem familyRingedAugmentation_fSharpInverseImage :
    (familyRingedAugmentation.{x, u, v, w} X K).fSharpInverseImage =
      (familyAugmentationInverseImageCommRingIso.{x, u, v, w} X K).hom :=
  Equiv.symm_apply_apply _ _

/-- The augmentation of a semi-representable localization over the ambient ringed site is flat:
its structure map in inverse-image form is the identification of the inverse image of `O_C`
with `O_K`, hence an isomorphism, and an isomorphism of sheaves of rings is flat. -/
theorem familyRingedAugmentation_isFlat :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{max u v x, max u v x,
        max x u v w, v, u, max x u v w}
      (familyRingedAugmentation.{x, u, v, w} X K) := by
  refine SheafOfModules.isFlatMapULift_of_isIso _ ?_
  rw [familyRingedAugmentation_fSharpInverseImage.{x, u, v, w} X K]
  exact (familyAugmentationInverseImageCommRingIso.{x, u, v, w} X K).isIso_hom

end AlgebraicGeometry.RingedSite

namespace CategoryTheory.SemiRepresentable.Simplicial

/-- **Stacks 0D9W, flat degreewise augmentations.** For a simplicial semi-representable object
`K` of the underlying site of a ringed site `X`, the morphism of ringed topoi
`a_n : (Sh(C/K_n), O_n) ⟶ (Sh(C), O_C)` is flat in every simplicial degree. -/
@[stacks 0D9W "flat_degreewise_augmentations"]
theorem degreewiseRingedAugmentation_isFlat
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) (n : SimplexCategory) :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{max u v x, max u v x,
        max x u v w, v, u, max x u v w}
      (degreewiseRingedAugmentation.{x, u, v, w} X K n) :=
  AlgebraicGeometry.RingedSite.familyRingedAugmentation_isFlat.{x, u, v, w} X (K.obj (op n))

/-- The structure map of the total augmentation, read in inverse-image form, is the
identification `totalAugmentationInverseImageCommRingIso`. -/
theorem totalRingedAugmentationAtLargeUniverse_fSharpInverseImage
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    (totalRingedAugmentationAtLargeUniverse.{x, u, v, w} X K).fSharpInverseImage =
      (totalAugmentationInverseImageCommRingIso.{x, u, v, w} X K).hom :=
  Equiv.symm_apply_apply _ _

/-- The total augmentation is flat for a structure sheaf whose universe of sections already
contains the total localization site. -/
theorem totalRingedAugmentationAtLargeUniverse_isFlat
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{v, max u v x,
        max x u v w, v, u, max x u v w}
      (totalRingedAugmentationAtLargeUniverse.{x, u, v, w} X K) := by
  refine AlgebraicGeometry.SheafOfModules.isFlatMapULift_of_isIso _ ?_
  rw [totalRingedAugmentationAtLargeUniverse_fSharpInverseImage.{x, u, v, w} X K]
  exact (totalAugmentationInverseImageCommRingIso.{x, u, v, w} X K).isIso_hom

/-- **Stacks 0D9W, flat augmentation.** For a simplicial semi-representable object `K` of the
underlying site of a ringed site `X`, the augmentation
`a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` of the total ringed site is flat. -/
@[stacks 0D9W "flat_augmentation"]
theorem totalRingedAugmentation_isFlat (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{v, max u v x,
        max x u v w, v, u, max x u v w}
      (totalRingedAugmentation.{x, u, v, w} X K) :=
  totalRingedAugmentationAtLargeUniverse_isFlat.{x, u, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x, u, v, w} X) K

end CategoryTheory.SemiRepresentable.Simplicial

end
