module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos

/-!
# The small pro-étale site of a weakly étale scheme is a localization

Let `B` be a chosen big pro-étale site, let `T` be an object of `B`, and let `j : Z ⟶ T` be
weakly étale, so that `j` is an object `Y` of the small pro-étale site of `T`. Composition with
`j` carries the small pro-étale site of `Z` to the small pro-étale site of `T`, and it factors as
an *equivalence* onto the localization of the small pro-étale site of `T` at `Y`, followed by the
slice forgetful functor. Consequently the small pro-étale topology of `Z` is the topology induced
from the localized topology, and composition with `j` is a continuous and cocontinuous functor of
sites which is left adjoint to base change along `j`.

This is the analogue, for the small pro-étale site `AlgebraicGeometry.ProEtale.SmallProetale`
cut out of a chosen big site by the size cutoff, of
`AlgebraicGeometry.ProEtale.localizationEquivalence`, which is available only for Mathlib's
unrestricted small pro-étale category `AlgebraicGeometry.Scheme.ProEt`. The two categories are
different, so this is not a transport of the existing statement; the mathematical input is the
same, namely that a morphism whose composite with a weakly étale morphism is weakly étale is
itself weakly étale (`AlgebraicGeometry.WeaklyEtale.of_comp`), applied at the level of the full
subcategory cut out of the slice by weak étaleness.

## Main definitions

* `AlgebraicGeometry.ProEtale.smallProetaleCompose`: composition with a weakly étale morphism,
  as a functor between small pro-étale sites.
* `AlgebraicGeometry.ProEtale.smallProetaleLocalizationEquivalence`: the equivalence between the
  small pro-étale site of the source of a small pro-étale object `Y` of `T` and the localization
  of the small pro-étale site of `T` at `Y`.
* `AlgebraicGeometry.ProEtale.smallProetaleCompose_adj`: composition is left adjoint to base
  change.

## Main results

* `AlgebraicGeometry.ProEtale.smallProetaleLocalizationEquivalence_forget`: the equivalence
  followed by the slice forgetful functor is composition.
* `AlgebraicGeometry.ProEtale.smallProetaleLocalizationEquivalence_inducedTopology`: the small
  pro-étale topology of the source is the topology induced along the equivalence from the
  localized small pro-étale topology of `T`.
* `AlgebraicGeometry.ProEtale.smallProetaleCompose_coverPreserving`,
  `AlgebraicGeometry.ProEtale.smallProetaleCompose_isContinuous` and
  `AlgebraicGeometry.ProEtale.smallProetaleCompose_isCocontinuous`: composition is a continuous
  and cocontinuous cover-preserving functor of sites.
* `AlgebraicGeometry.ProEtale.exists_iso_smallProetaleCompose_obj`: every object of the small
  pro-étale site of `T` equipped with a morphism to `Y` is isomorphic to the composition of an
  object of the small pro-étale site of the source of `Y`.

## Implementation notes

Cover preservation of composition is obtained from continuity of composition into the *big*
slice over `T`, which holds for an arbitrary morphism, together with cocontinuity of the
inclusion of the small site into the big slice; cocontinuity of composition is obtained from the
adjunction with base change. Neither uses the equivalence. The equivalence is used only for
continuity, which is the one property that cannot be obtained from a compatibility criterion
here: `CategoryTheory.compatiblePreservingOfDownwardsClosed` needs a fully faithful functor, and
composition with a weakly étale `j` is fully faithful only when `j` is a monomorphism.

The identification of the induced topology needs both halves of
`CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense`: cover preservation of
composition for one direction and cocontinuity of composition for the other. The latter uses
that a sieve is recovered from its pushforward along composition, which holds because
composition factors as a fully faithful functor followed by a slice forgetful functor, for each
of which the corresponding statement is available.

## References

* [Stacks Project, Tag 098K](https://stacks.math.columbia.edu/tag/098K)
* [Stacks Project, Tag 098T](https://stacks.math.columbia.edu/tag/098T)
* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u})

section Compose

variable {Z T : B.Scheme} (j : Z ⟶ T) (hj : WeaklyEtale (B.inclusion.map j))

/-- Composition with a weakly étale morphism `j : Z ⟶ T` of a chosen big pro-étale site, as a
functor from the small pro-étale site of `Z` to the small pro-étale site of `T`: a weakly étale
`Z`-scheme is weakly étale over `T`. -/
def smallProetaleCompose :
    SmallProetale B Z.obj Z.property ⥤ SmallProetale B T.obj T.property :=
  (IsWeaklyEtaleOver B T.obj T.property).lift
    (SmallProetale.inclusion B Z.obj Z.property ⋙ Over.map j)
    (fun X => by
      have h1 : WeaklyEtale (B.inclusion.map X.obj.hom) := X.property
      have h2 : WeaklyEtale (B.inclusion.map j) := hj
      change WeaklyEtale (B.inclusion.map X.obj.hom ≫ B.inclusion.map j)
      infer_instance)

/-- Composition with `j` followed by the inclusion of the small pro-étale site of `T` into the
big slice over `T` is the inclusion of the small pro-étale site of `Z` followed by composition
with `j` on big slices, including the action on morphisms. -/
theorem smallProetaleCompose_comp_inclusion :
    smallProetaleCompose B j hj ⋙ SmallProetale.inclusion B T.obj T.property =
      SmallProetale.inclusion B Z.obj Z.property ⋙ Over.map j := rfl

/-- Composition with `j` is left adjoint to base change along `j`. -/
def smallProetaleCompose_adj :
    smallProetaleCompose B j hj ⊣ smallProetaleBaseChange B Z T j :=
  (Over.mapPullbackAdj j).restrictFullyFaithful
    (.ofFullyFaithful (SmallProetale.inclusion B Z.obj Z.property))
    (.ofFullyFaithful (SmallProetale.inclusion B T.obj T.property))
    (eqToIso (smallProetaleCompose_comp_inclusion B j hj).symm)
    (eqToIso (smallProetaleBaseChange_comp_inclusion B Z T j).symm)

end Compose

/-- The inclusion of the small pro-étale site of `T` into the big pro-étale slice over `T` is
cocontinuous: it is composition with the identity of `T`. -/
theorem smallProetaleInclusion_isCocontinuous (T : B.Scheme) :
    (SmallProetale.inclusion B T.obj T.property).IsCocontinuous
      (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B T.obj T.property) := by
  have heq : smallProetaleToBigProetaleFunctor B T T (𝟙 T) =
      SmallProetale.inclusion B T.obj T.property := by
    dsimp [smallProetaleToBigProetaleFunctor]
    rw [Over.mapId_eq]
    rfl
  have : (smallProetaleToBigProetaleFunctor B T T (𝟙 T)).IsCocontinuous
      (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B T.obj T.property) :=
    smallProetaleToBigProetaleFunctor_isCocontinuous B T T (𝟙 T)
  exact Functor.IsCocontinuous.of_iso (eqToIso heq)

section ComposeSite

variable {Z T : B.Scheme} (j : Z ⟶ T) (hj : WeaklyEtale (B.inclusion.map j))

/-- Composition with a weakly étale morphism preserves covering sieves. -/
theorem smallProetaleCompose_coverPreserving :
    CoverPreserving (SmallProetale.topology B Z.obj Z.property)
      (SmallProetale.topology B T.obj T.property) (smallProetaleCompose B j hj) := by
  have : (SmallProetale.inclusion B T.obj T.property).IsCocontinuous
      (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B T.obj T.property) :=
    smallProetaleInclusion_isCocontinuous B T
  have hcomp : CoverPreserving (SmallProetale.topology B Z.obj Z.property)
      (BigProetaleOver.topology B T.obj T.property)
      (smallProetaleCompose B j hj ⋙ SmallProetale.inclusion B T.obj T.property) :=
    CoverPreserving.of_isContinuous (smallProetaleToBigProetaleFunctor B Z T j) _ _
  exact CoverPreserving.of_comp_of_isCocontinuous
    (SmallProetale.topology B Z.obj Z.property)
    (SmallProetale.topology B T.obj T.property)
    (SmallProetale.inclusion B T.obj T.property) hcomp

/-- Composition with a weakly étale morphism is cocontinuous, being left adjoint to the
cover-preserving base-change functor. -/
instance smallProetaleCompose_isCocontinuous :
    (smallProetaleCompose B j hj).IsCocontinuous
      (SmallProetale.topology B Z.obj Z.property)
      (SmallProetale.topology B T.obj T.property) := by
  have : (smallProetaleBaseChange B Z T j).IsContinuous
      (SmallProetale.topology B T.obj T.property)
      (SmallProetale.topology B Z.obj Z.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B Z T j).toIsContinuous
  exact ((smallProetaleCompose_adj B j hj).isCocontinuous_iff_coverPreserving _ _).2
    (CoverPreserving.of_isContinuous (smallProetaleBaseChange B Z T j) _ _)

end ComposeSite

variable (T : B.Scheme) (Y : SmallProetale B T.obj T.property)

/-- **The small pro-étale site of a weakly étale scheme is a localization.** For an object `Y` of
the small pro-étale site of `T`, with source `Y.obj.left` and structure morphism `Y.obj.hom`, the
small pro-étale site of `Y.obj.left` is equivalent to the localization of the small pro-étale
site of `T` at `Y`. The equivalence sends a weakly étale `Y.obj.left`-scheme to its composite
over `T`, viewed over `Y`; its inverse sends an object over `Y` to its structure morphism to
`Y.obj.left`, which is weakly étale by `AlgebraicGeometry.WeaklyEtale.of_comp`. -/
def smallProetaleLocalizationEquivalence :
    SmallProetale B Y.obj.left.obj Y.obj.left.property ≌ Over Y := by
  let C := SmallProetale B Y.obj.left.obj Y.obj.left.property
  let post := smallProetaleCompose B Y.obj.hom Y.property
  let F : C ⥤ Over Y := Over.lift post
    { app := fun V => ObjectProperty.homMk (Over.homMk V.obj.hom)
      naturality := by
        intro V W f
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        exact Over.w f.hom }
  let Gobj : Over Y → C := fun W => by
    have hw : W.hom.hom.left ≫ Y.obj.hom = W.left.obj.hom := Over.w W.hom.hom
    have hY : WeaklyEtale (B.inclusion.map Y.obj.hom) := Y.property
    have hcomp : WeaklyEtale (B.inclusion.map W.hom.hom.left ≫
        B.inclusion.map Y.obj.hom) := by
      rw [← Functor.map_comp, hw]
      exact W.left.property
    exact ⟨Over.mk W.hom.hom.left,
      WeaklyEtale.of_comp (B.inclusion.map W.hom.hom.left) (B.inclusion.map Y.obj.hom)⟩
  let G : Over Y ⥤ C :=
    { obj := Gobj
      map := fun {V W} f => ObjectProperty.homMk (Over.homMk f.left.hom.left (by
        change f.left.hom.left ≫ W.hom.hom.left = V.hom.hom.left
        exact congrArg (fun g => g.hom.left) (Over.w f)))
      map_id := by
        intro V
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        rfl
      map_comp := by
        intro V W Z f g
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        rfl }
  let hunit : ∀ V : C, V ≅ (F ⋙ G).obj V := fun V =>
    ObjectProperty.isoMk _ (Over.isoMk (Iso.refl V.obj.left))
  let hcounit : ∀ W : Over Y, (G ⋙ F).obj W ≅ W := fun W => by
    refine Over.isoMk
      (ObjectProperty.isoMk _ (Over.isoMk (Iso.refl W.left.obj.left) ?_)) ?_
    · exact (Category.id_comp _).trans (Over.w W.hom.hom).symm
    · apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact Category.id_comp _
  exact
    { functor := F
      inverse := G
      unitIso := NatIso.ofComponents hunit (by
        intro V W f
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        change f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.left
        simp)
      counitIso := NatIso.ofComponents hcounit (by
        intro V W f
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        change f.left.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.hom.left
        simp)
      functor_unitIso_comp := by
        intro V
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        change 𝟙 V.obj.left ≫ 𝟙 V.obj.left = 𝟙 V.obj.left
        simp }

/-- The localization equivalence followed by the slice forgetful functor is composition with the
structure morphism of `Y`. In particular, restriction to the localized site agrees, on
presheaves and sheaves, with restriction along composition. -/
theorem smallProetaleLocalizationEquivalence_forget :
    (smallProetaleLocalizationEquivalence B T Y).functor ⋙ Over.forget Y =
      smallProetaleCompose B Y.obj.hom Y.property := rfl

/-- The localization equivalence keeps the underlying object of the small pro-étale site of
`T`. -/
theorem smallProetaleLocalizationEquivalence_obj_left
    (V : SmallProetale B Y.obj.left.obj Y.obj.left.property) :
    ((smallProetaleLocalizationEquivalence B T Y).functor.obj V).left =
      (smallProetaleCompose B Y.obj.hom Y.property).obj V := rfl

/-- The sieve on `Y.obj.left` underlying the image of a sieve under the localization equivalence
is the pushforward of that sieve along composition. -/
theorem smallProetaleLocalizationEquivalence_overEquiv_functorPushforward
    {V : SmallProetale B Y.obj.left.obj Y.obj.left.property} (S : Sieve V) :
    Sieve.overEquiv ((smallProetaleLocalizationEquivalence B T Y).functor.obj V)
        (S.functorPushforward (smallProetaleLocalizationEquivalence B T Y).functor) =
      S.functorPushforward (smallProetaleCompose B Y.obj.hom Y.property) := by
  change (S.functorPushforward (smallProetaleLocalizationEquivalence B T Y).functor
    ).functorPushforward (Over.forget Y) = _
  rw [← Sieve.functorPushforward_comp]
  rfl

/-- A sieve is recovered from its pushforward along composition with the structure morphism of
`Y`: composition factors as the fully faithful localization equivalence followed by a slice
forgetful functor, and the statement holds for each factor. -/
theorem smallProetaleCompose_functorPullback_functorPushforward
    {V : SmallProetale B Y.obj.left.obj Y.obj.left.property} (S : Sieve V) :
    (S.functorPushforward (smallProetaleCompose B Y.obj.hom Y.property)).functorPullback
      (smallProetaleCompose B Y.obj.hom Y.property) = S := by
  change (S.functorPushforward ((smallProetaleLocalizationEquivalence B T Y).functor ⋙
      Over.forget Y)).functorPullback
      ((smallProetaleLocalizationEquivalence B T Y).functor ⋙ Over.forget Y) = S
  rw [Sieve.functorPushforward_comp, Sieve.functorPullback_comp,
    Sieve.functorPullback_functorPushforward_overForget,
    Sieve.functorPullback_functorPushforward_eq]

/-- The small pro-étale topology of the source of `Y` is the topology induced, along the
localization equivalence, from the localization at `Y` of the small pro-étale topology of `T`. -/
theorem smallProetaleLocalizationEquivalence_inducedTopology :
    SmallProetale.topology B Y.obj.left.obj Y.obj.left.property =
      (smallProetaleLocalizationEquivalence B T Y).functor.inducedTopology
        ((SmallProetale.topology B T.obj T.property).over Y) := by
  ext V S
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    GrothendieckTopology.mem_over_iff,
    smallProetaleLocalizationEquivalence_overEquiv_functorPushforward B T Y S]
  refine ⟨(smallProetaleCompose_coverPreserving B Y.obj.hom Y.property).cover_preserve,
    fun h => ?_⟩
  have h2 := (smallProetaleCompose B Y.obj.hom Y.property).cover_lift
    (SmallProetale.topology B Y.obj.left.obj Y.obj.left.property)
    (SmallProetale.topology B T.obj T.property) h
  rwa [smallProetaleCompose_functorPullback_functorPushforward B T Y S] at h2

/-- Composition with the structure morphism of `Y` is continuous: it is the localization
equivalence, which is continuous for the induced topology, followed by the slice forgetful
functor. -/
theorem smallProetaleCompose_isContinuous_obj :
    (smallProetaleCompose B Y.obj.hom Y.property).IsContinuous
      (SmallProetale.topology B Y.obj.left.obj Y.obj.left.property)
      (SmallProetale.topology B T.obj T.property) := by
  have hfun : (smallProetaleLocalizationEquivalence B T Y).functor.IsContinuous
      (SmallProetale.topology B Y.obj.left.obj Y.obj.left.property)
      ((SmallProetale.topology B T.obj T.property).over Y) := by
    rw [smallProetaleLocalizationEquivalence_inducedTopology B T Y]
    infer_instance
  have hcomp := Functor.isContinuous_comp
    (smallProetaleLocalizationEquivalence B T Y).functor (Over.forget Y)
    (SmallProetale.topology B Y.obj.left.obj Y.obj.left.property)
    ((SmallProetale.topology B T.obj T.property).over Y)
    (SmallProetale.topology B T.obj T.property)
  rwa [smallProetaleLocalizationEquivalence_forget] at hcomp

/-- Every object of the small pro-étale site of `T` which admits a morphism to `Y` is isomorphic
to the composite over `T` of an object of the small pro-étale site of the source of `Y`. -/
theorem exists_iso_smallProetaleCompose_obj
    {W : SmallProetale B T.obj T.property} (q : W ⟶ Y) :
    ∃ V : SmallProetale B Y.obj.left.obj Y.obj.left.property,
      Nonempty ((smallProetaleCompose B Y.obj.hom Y.property).obj V ≅ W) :=
  ⟨(smallProetaleLocalizationEquivalence B T Y).inverse.obj (Over.mk q),
    ⟨(Over.forget Y).mapIso
      ((smallProetaleLocalizationEquivalence B T Y).counitIso.app (Over.mk q))⟩⟩

section ComposeContinuous

variable {Z T : B.Scheme} (j : Z ⟶ T) (hj : WeaklyEtale (B.inclusion.map j))

/-- Composition with a weakly étale morphism is continuous. -/
instance smallProetaleCompose_isContinuous :
    (smallProetaleCompose B j hj).IsContinuous
      (SmallProetale.topology B Z.obj Z.property)
      (SmallProetale.topology B T.obj T.property) :=
  smallProetaleCompose_isContinuous_obj B T ⟨Over.mk j, hj⟩

end ComposeContinuous

end AlgebraicGeometry.ProEtale

end
