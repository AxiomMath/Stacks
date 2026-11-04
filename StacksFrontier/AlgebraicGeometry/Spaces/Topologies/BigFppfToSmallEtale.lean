module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleSquare
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites

/-!
# Comparing the big fppf and the étale topoi of an algebraic space

Let `S` be a scheme, let `T` be a big fppf site of algebraic spaces over `S` and let `E` be a big
étale site of algebraic spaces over `S` built on the same big fppf site of schemes, as recorded by
the hypothesis `h : T.schemeSite = E.fppfSite`. For a morphism `f : Y ⟶ X` of algebraic spaces of
`T` there are two commutative diagrams of topoi: the big one, relating `f_{big, fppf}` to
`f_{big, étale}` through the change-of-topology morphisms `ε`, and the small one, relating
`f_{big, fppf}` to `f_{small}` through `a = π ∘ ε`.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.canonicalSpaceEquivalence`: the identification of the two
  categories of algebraic spaces the two sites are built on.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtaleMorphism`: the change-of-topology morphism
  `ε_X` from the big fppf topos of `X` to its big étale topos.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleMorphism`: the morphism `a_X` to the small
  étale topos, as the composite `π_X ∘ ε_X`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtale_isContinuous`: the identity-on-spaces functor
  of slice categories is continuous from the big étale topology to the big fppf one.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtale_pushforwardIso`: the direct image of `ε_X`
  is restriction along that functor.
* `AlgebraicGeometry.BigFppfSpaceSite.pullbackChangeOfTopologyIso`: the change-of-topology functor
  commutes with base change along `f`.
* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfBigEtale_pushforwardCommIso`: the big fppf–big étale
  square commutes on direct images.
* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfSmallEtale_pushforwardCommIso`: the big fppf–small
  étale square commutes on direct images.

## References

* [Stacks Project, Tag 0DF3](https://stacks.math.columbia.edu/tag/0DF3)
* [Stacks Project, Tag 0DGI](https://stacks.math.columbia.edu/tag/0DGI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- The identification of the category of algebraic spaces a big fppf site of algebraic spaces is
built on with the one a big étale site of algebraic spaces over the same big fppf site of schemes
is built on, together with the facts that it is the identity on objects and on morphisms. -/
@[stacks 0DGI "identification of the underlying algebraic spaces"]
def canonicalSpaceEquivalence :
    { G : T.Spaces ≌ E.Spaces //
      (∀ X : T.Spaces, HEq X.1 (G.functor.obj X).1) ∧
      (∀ {X Y : T.Spaces} (f : X ⟶ Y), HEq f.hom (G.functor.map f).hom) } := by
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    exact ⟨CategoryTheory.Equivalence.refl, ⟨fun _ => HEq.rfl, fun _ => HEq.rfl⟩⟩

/-- An algebraic space of the big fppf site, read as one of the big étale site. -/
abbrev etaleSpace (X : T.Spaces) : E.Spaces :=
  (canonicalSpaceEquivalence T E h).1.functor.obj X

/-- A morphism of algebraic spaces of the big fppf site, read as one of the big étale site. -/
abbrev etaleMap {X Y : T.Spaces} (f : X ⟶ Y) : etaleSpace T E h X ⟶ etaleSpace T E h Y :=
  (canonicalSpaceEquivalence T E h).1.functor.map f

/-- The identity-on-spaces functor from the big étale slice at `X` to the big fppf slice at `X`
is continuous. -/
@[stacks 0DGI "continuity of the change-of-topology functor"]
instance fppfToBigEtale_isContinuous (X : T.Spaces) :
    ((Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse).IsContinuous
      (E.bigEtaleTopology (etaleSpace T E h X)) (BigFppfSpaceOver.topology T X) := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, tScheme, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      have htop : E'.topology ≤ T'.topology := by
        change E'.precoverage.toGrothendieck ≤ T'.precoverage.toGrothendieck
        intro U R hR
        rw [Precoverage.mem_toGrothendieck_iff] at hR ⊢
        induction hR with
        | of U R hR =>
            rw [BigEtaleSpaceSite.mem_precoverage_iff] at hR
            rcases hR with ⟨E₀, rfl, hE₀⟩
            have hEt : Space.IsEtaleCoveringFamily tScheme S eFppfMem ⟨U, E₀⟩ :=
              BigEtaleSpaceSite.IsCovering.etale hE₀
            have hFppf : Space.IsFppfCoveringFamily tScheme S eFppfMem ⟨U, E₀⟩ :=
              Space.isFppfCovering_of_isEtaleCovering tScheme S eFppfMem hEt
            obtain ⟨E₁, hE₁, hCE⟩ := tRepresentative ⟨U, E₀⟩ hFppf
            rcases hCE with ⟨hU, hCE'⟩
            change U = E₁.1 at hU
            subst hU
            have hpres := PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hCE'
            have hpre : E₁.2.presieve₀ ∈ T'.precoverage E₁.1 := by
              rw [BigFppfSpaceSite.mem_precoverage_iff]
              exact ⟨E₁.2, rfl, hE₁⟩
            rw [hpres]
            exact Precoverage.generate_mem_toGrothendieck hpre
        | top => exact T'.topology.top_mem _
        | pullback U R _ V f ih => exact T'.topology.pullback_stable _ ih
        | transitive U R R' _ _ ihR ihT =>
            exact T'.topology.transitive ihR _ fun V g hg => ihT hg
      change (𝟭 (Over X)).IsContinuous (E'.topology.over X) (T'.topology.over X)
      refine Functor.isContinuous_id_of_le _ _ fun Z R hR => ?_
      rw [GrothendieckTopology.mem_over_iff] at hR ⊢
      exact htop Z.left hR

/-- The change-of-topology morphism `ε_X` from the big fppf topos of `X` to its big étale topos,
induced by the identity-on-spaces functor of slice categories. -/
@[stacks 0DGI "the fppf-to-big-étale morphism"]
def fppfToBigEtaleMorphism (X : T.Spaces) :
    MorphismOfTopoi (Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1)))
      (Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) (Type (u + 1))) :=
  letI := fppfToBigEtale_isContinuous T E h X
  (Functor.isMorphismOfSites_of_representablyFlat
    ((Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse)
    (E.bigEtaleTopology (etaleSpace T E h X))
    (BigFppfSpaceOver.topology T X)).morphismOfTopoi

/-- The direct image of `ε_X` is restriction along the identity-on-spaces functor of slice
categories. -/
@[stacks 0DGI "direct image of the fppf-to-big-étale morphism"]
def fppfToBigEtale_pushforwardIso (X : T.Spaces) :
    (fppfToBigEtaleMorphism T E h X).pushforward ≅
      ((Over.postEquiv (canonicalSpaceEquivalence T E h).1
        (X := X)).inverse).sheafPushforwardContinuous (Type (u + 1))
        (E.bigEtaleTopology (etaleSpace T E h X)) (BigFppfSpaceOver.topology T X) :=
  Iso.refl _

/-- Base change along `f` commutes with the identity-on-spaces change-of-topology functor of
slice categories. -/
@[stacks 0DGI "canonical base-change comparison on the big sites"]
def pullbackChangeOfTopologyIso {X Y : T.Spaces} (f : Y ⟶ X) :
    Over.pullback (etaleMap T E h f) ⋙
        (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := Y)).inverse ≅
      (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse ⋙
        Over.pullback f := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      exact Iso.refl _

/-- The morphism `a_X` from the big fppf topos of `X` to its small étale topos: the composite of
`ε_X` with the big-to-small étale morphism `π_X` ([Stacks, Tag 0DF3]). -/
@[stacks 0DGI "the factorization through big étale"]
def fppfToSmallEtaleMorphism (X : T.Spaces) :
    MorphismOfTopoi (Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1)))
      (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
        (Type (u + 1))) :=
  (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).comp (fppfToBigEtaleMorphism T E h X)

/-- The big fppf–big étale square: for a morphism `f : Y ⟶ X` of algebraic spaces the direct
images of `ε_X ∘ f_{big, fppf}` and of `f_{big, étale} ∘ ε_Y` are canonically isomorphic. -/
@[stacks 0DGI "the big fppf–big étale square"]
def bigFppfBigEtale_pushforwardCommIso {X Y : T.Spaces} (f : Y ⟶ X) :
    ((E.bigEtaleMorphism (etaleMap T E h f)).comp (fppfToBigEtaleMorphism T E h Y)).pushforward ≅
      ((fppfToBigEtaleMorphism T E h X).comp (bigFppfMorphism T f)).pushforward := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, tScheme, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      let JeX := E'.topology.over X
      let JeY := E'.topology.over Y
      let JfX := T'.topology.over X
      let JfY := T'.topology.over Y
      let eX := (Over.postEquiv (canonicalSpaceEquivalence T' E' rfl).1 (X := X)).inverse
      let eY := (Over.postEquiv (canonicalSpaceEquivalence T' E' rfl).1 (X := Y)).inverse
      let be := Over.pullback (etaleMap T' E' rfl f)
      let bf := Over.pullback f
      haveI heX : eX.IsContinuous JeX JfX := fppfToBigEtale_isContinuous T' E' rfl X
      haveI heY : eY.IsContinuous JeY JfY := fppfToBigEtale_isContinuous T' E' rfl Y
      haveI hbpE : be.IsContinuous JeX JeY :=
        (StacksRelocalization.isMorphismOfSites_overPullback E'.topology
          (etaleMap T' E' rfl f)).isContinuous
      haveI hbpF : bf.IsContinuous JfX JfY :=
        (StacksRelocalization.isMorphismOfSites_overPullback T'.topology f).isContinuous
      haveI : (be ⋙ eY).IsContinuous JeX JfY := Functor.isContinuous_comp be eY JeX JeY JfY
      haveI : (eX ⋙ bf).IsContinuous JeX JfY := Functor.isContinuous_comp eX bf JeX JfX JfY
      let eXpush := eX.sheafPushforwardContinuous (Type (u + 1)) JeX JfX
      let eYpush := eY.sheafPushforwardContinuous (Type (u + 1)) JeY JfY
      let hEtale := StacksRelocalization.sheafPushforwardOverMapIso E'.topology f
      let hFppf := StacksRelocalization.sheafPushforwardOverMapIso T'.topology f
      let hEpsX := fppfToBigEtale_pushforwardIso T' E' rfl X
      let hEpsY := fppfToBigEtale_pushforwardIso T' E' rfl Y
      let hBigFppf := bigFppfMorphism_pushforwardIso T' f
      let hCompL := Functor.sheafPushforwardContinuousComp be eY (Type (u + 1)) JeX JeY JfY
      let hCompR := Functor.sheafPushforwardContinuousComp eX bf (Type (u + 1)) JeX JfX JfY
      have hsite : be ⋙ eY ≅ eX ⋙ bf := pullbackChangeOfTopologyIso T' E' rfl f
      let hSite := Functor.sheafPushforwardContinuousIso hsite (Type (u + 1)) JeX JfY
      change (fppfToBigEtaleMorphism T' E' rfl Y).pushforward ⋙
          (E'.bigEtaleMorphism (etaleMap T' E' rfl f)).pushforward ≅
        (bigFppfMorphism T' f).pushforward ⋙ (fppfToBigEtaleMorphism T' E' rfl X).pushforward
      exact
        Functor.isoWhiskerRight hEpsY
            (E'.bigEtaleMorphism (etaleMap T' E' rfl f)).pushforward ≪≫
          Functor.isoWhiskerLeft eYpush hEtale ≪≫ hCompL ≪≫ hSite ≪≫ hCompR.symm ≪≫
          (Functor.isoWhiskerRight hFppf eXpush).symm ≪≫
          (Functor.isoWhiskerRight hBigFppf eXpush).symm ≪≫
          Functor.isoWhiskerLeft (bigFppfMorphism T' f).pushforward hEpsX.symm

/-- The big fppf–small étale square: for a morphism `f : Y ⟶ X` of algebraic spaces the direct
images of `a_X ∘ f_{big, fppf}` and of `f_{small} ∘ a_Y` are canonically isomorphic. -/
@[stacks 0DGI "the big fppf–small étale square"]
def bigFppfSmallEtale_pushforwardCommIso {X Y : T.Spaces} (f : Y ⟶ X) :
    ((E.smallEtaleMorphism (etaleMap T E h f)).comp
        (fppfToSmallEtaleMorphism T E h Y)).pushforward ≅
      ((fppfToSmallEtaleMorphism T E h X).comp (bigFppfMorphism T f)).pushforward := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, tScheme, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      let epsX := fppfToBigEtaleMorphism T' E' rfl X
      let epsY := fppfToBigEtaleMorphism T' E' rfl Y
      let piX := E'.bigToSmallEtaleMorphism X
      let piY := E'.bigToSmallEtaleMorphism Y
      let sm := E'.smallEtaleMorphism f
      let bg := bigFppfMorphism T' f
      let hSmall := E'.bigSmallEtale_pushforwardCommIso f
      let hBig := bigFppfBigEtale_pushforwardCommIso T' E' rfl f
      change ((epsY.pushforward ⋙ piY.pushforward) ⋙ sm.pushforward) ≅
        (bg.pushforward ⋙ (epsX.pushforward ⋙ piX.pushforward))
      exact
        Functor.associator epsY.pushforward piY.pushforward sm.pushforward ≪≫
          Functor.isoWhiskerLeft epsY.pushforward hSmall ≪≫
          (Functor.associator epsY.pushforward (E'.bigEtaleMorphism f).pushforward
            piX.pushforward).symm ≪≫
          Functor.isoWhiskerRight hBig piX.pushforward ≪≫
          Functor.associator bg.pushforward epsX.pushforward piX.pushforward

end AlgebraicGeometry.BigFppfSpaceSite

end
