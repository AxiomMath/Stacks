module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites

/-!
# Comparing the big ph and the étale topoi of an algebraic space (Stacks 0DGW)

Let `S` be a scheme, let `P` be a big ph site of algebraic spaces over `S` and let `E` be a big
étale site of algebraic spaces over `S` built on the same big fppf site of schemes. For a
morphism `f : Y ⟶ X` of algebraic spaces of `P` there are two commutative diagrams of topoi: the
big one, relating `f_{big, ph}` to `f_{big, étale}` through the change-of-topology morphisms `ε`,
and the small one, relating `f_{big, ph}` to `f_{small}` through `a = π ∘ ε`.

## Main definitions

* `AlgebraicGeometry.BigPHSpaceSite.canonicalSpaceEquivalence`: the identification of the two
  categories of algebraic spaces the two sites are built on.
* `AlgebraicGeometry.BigPHSpaceSite.phToBigEtaleMorphism`: the change-of-topology morphism `ε_X`
  from the big ph topos of `X` to its big étale topos.
* `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtaleMorphism`: the morphism `a_X` to the small
  étale topos, as the composite `π_X ∘ ε_X`.
* `AlgebraicGeometry.BigPHSpaceSite.smallEtaleToPH`: the scheme charts of the small étale site of
  `X`, viewed in the big ph slice at `X`.

## Main results

* `AlgebraicGeometry.BigPHSpaceSite.phToBigEtale_isContinuous`: the identity-on-spaces functor of
  slice categories is continuous from the big étale topology to the big ph one.
* `AlgebraicGeometry.BigPHSpaceSite.phToBigEtale_pushforwardIso`: the direct image of `ε_X` is
  restriction along that functor.
* `AlgebraicGeometry.BigPHSpaceSite.pullbackChangeOfTopologyIso`: the change-of-topology functor
  commutes with base change along `f`.
* `AlgebraicGeometry.BigPHSpaceSite.bigPHBigEtale_pushforwardCommIso`: **Stacks 0DGW**, the big
  ph–big étale square.
* `AlgebraicGeometry.BigPHSpaceSite.bigPHSmallEtale_pushforwardCommIso`: **Stacks 0DGW**, the big
  ph–small étale square.
* `AlgebraicGeometry.BigPHSpaceSite.spacesEtale_inclusion_isContinuous`: the inclusion of the
  algebraic spaces étale over `X` into the big ph slice at `X` is continuous.
* `AlgebraicGeometry.BigPHSpaceSite.bigPHSmallEtaleCharts_pushforwardCommIso`: **Stacks 0DGW**,
  the big ph–small étale square for the presentation of the small étale topos by the site of
  scheme charts.

## Implementation notes

The two sites are chosen independently — `AlgebraicGeometry.BigPHSpaceSite` carries a big ph site
of schemes *and*, separately, the big fppf site of schemes whose algebraic spaces it topologizes,
and so does `AlgebraicGeometry.BigEtaleSpaceSite` with its big étale site of schemes. They
therefore describe the same category of algebraic spaces exactly when their two big fppf sites of
schemes agree, and that is the hypothesis `h` carried throughout. The membership proofs of `S` in
the two fppf sites are propositions, so once the sites agree the two categories of algebraic
spaces are the same; `canonicalSpaceEquivalence` records that as an equivalence together with the
two `HEq`s saying it is the identity on objects and on morphisms, which is what makes the
comparisons below canonical rather than merely abstract.

That the big étale topology is coarser than the big ph one is proved inside
`phToBigEtale_isContinuous` by induction on the generation of the ph topology from its
precoverage: a chosen étale covering family is a ph covering family by
`AlgebraicGeometry.Space.isPHCovering_of_isEtaleCovering` (**Stacks 0DFH**), and the chosen ph
representative supplied by the site generates the same sieve, by
`CategoryTheory.PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent`. Continuity of the
identity functor for a pair of comparable topologies is
`CategoryTheory.Functor.isContinuous_id_of_le`.

Commutativity is expressed by natural isomorphisms of direct-image functors rather than by
equalities of morphisms of topoi: the three morphisms involved are built from three different
site-theoretic constructions — base change along `f` for the ph side, composition with `f` for
the étale side, and the inclusion of the small étale site — and only their pushforwards are
canonically comparable. `AlgebraicGeometry.BigPHSpaceSite.bigPHMorphismPushforwardIso`
(**Stacks 0DFN**) and `StacksRelocalization.sheafPushforwardOverMapIso` (**Stacks 09W9**) are what
line the two descriptions up.

The second vertical morphism `a_X` is *defined* as `π_X ∘ ε_X`, so the factorization asserted by
Stacks 0DGW is definitional and the small square reduces to the big one composed with the
big–small étale square of **Stacks 0DF6**.

The small étale topos of `X` is presented above, as in Stacks 0DF3 and 0DF6, by the site of
algebraic spaces étale over `X`. The second square is therefore stated once more for the other
presentation of that topos, the site of *schemes* étale over `X` of Stacks 03G0: there the chart
functor `smallEtaleToPH` lands in the big ph slice directly, so the square needs no auxiliary big
étale site at all. Its two new ingredients are the continuity of the inclusion of the
spaces-étale site in the big ph slice — the ph analogue of Stacks 0DF3, proved from Stacks 0DFH
exactly as the coarsening above — and the identification of the small étale direct image with the
spaces-étale one, Stacks 03G2, part (3). That the inclusion of the charts commutes with base
change is, for the chosen base change of Stacks 03G2, part (1), the identity: the base change of a
chart is by construction the restriction of `CategoryTheory.Over.pullback f` to the charts.

This is the algebraic-space analogue of the scheme-level
`AlgebraicGeometry.bigPHSmallEtale_pushforwardCommIso` (**Stacks 0DDX**) in
`StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.PhToEtaleSquares`; there the étale site
is *constructed* from the ph one, which is why no compatibility hypothesis appears there. It is also
the ph analogue of `AlgebraicGeometry.BigFppfSpaceSite.bigFppfSmallEtale_pushforwardCommIso`
(**Stacks 0DGI**), whose proof it follows step for step, the only change being the covering
comparison that makes the change-of-topology functor continuous.

## References

* [Stacks Project, Tag 0DF3](https://stacks.math.columbia.edu/tag/0DF3)
* [Stacks Project, Tag 0DF5](https://stacks.math.columbia.edu/tag/0DF5)
* [Stacks Project, Tag 0DF6](https://stacks.math.columbia.edu/tag/0DF6)
* [Stacks Project, Tag 0DFH](https://stacks.math.columbia.edu/tag/0DFH)
* [Stacks Project, Tag 0DFN](https://stacks.math.columbia.edu/tag/0DFN)
* [Stacks Project, Tag 0DGW](https://stacks.math.columbia.edu/tag/0DGW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigPHSpaceSite

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite)

/-- The identification of the category of algebraic spaces a big ph site of algebraic spaces is
built on with the one a big étale site of algebraic spaces over the same big fppf site of schemes
is built on. It is the identity on objects and on morphisms, which the two `HEq` clauses
record. -/
def canonicalSpaceEquivalence :
    { G : P.Spaces ≌ E.Spaces //
      (∀ X : P.Spaces, HEq X.1 (G.functor.obj X).1) ∧
      (∀ {X Y : P.Spaces} (f : X ⟶ Y), HEq f.hom (G.functor.map f).hom) } := by
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change P.fppfSite = eFppfSite at h
    cases h
    exact ⟨CategoryTheory.Equivalence.refl, ⟨fun _ => HEq.rfl, fun _ => HEq.rfl⟩⟩

/-- An algebraic space of the big ph site, read as one of the big étale site. -/
abbrev etaleSpace (X : P.Spaces) : E.Spaces :=
  (canonicalSpaceEquivalence P E h).1.functor.obj X

/-- A morphism of algebraic spaces of the big ph site, read as one of the big étale site. -/
abbrev etaleMap {X Y : P.Spaces} (f : X ⟶ Y) : etaleSpace P E h X ⟶ etaleSpace P E h Y :=
  (canonicalSpaceEquivalence P E h).1.functor.map f

/-- The identity-on-spaces functor from the big étale slice at `X` to the big ph slice at `X` is
continuous: every big étale covering sieve is a big ph covering sieve, since a chosen étale
covering family is a ph covering family (**Stacks 0DFH**) and the chosen ph representative of it
generates the same sieve. -/
instance phToBigEtale_isContinuous (X : P.Spaces) :
    ((Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).inverse).IsContinuous
      (E.bigEtaleTopology (etaleSpace P E h X)) (BigPHSpaceOver.topology P X) := by
  cases P with
  | mk pSchemeSite pSchemeMem pFppfSite pFppfMem pCutoffEq pInitial pInitialSmall pInitialPH
      pBound pOrdinal pOrdinalLim pInitialBounded pIsSite pRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let P' : BigPHSpaceSite S :=
        ⟨pSchemeSite, pSchemeMem, pFppfSite, pFppfMem, pCutoffEq, pInitial, pInitialSmall,
          pInitialPH, pBound, pOrdinal, pOrdinalLim, pInitialBounded, pIsSite, pRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, pFppfSite, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      have htop : E'.topology ≤ P'.topology := by
        change E'.precoverage.toGrothendieck ≤ P'.precoverage.toGrothendieck
        intro U R hR
        rw [Precoverage.mem_toGrothendieck_iff] at hR ⊢
        induction hR with
        | of U R hR =>
            rw [BigEtaleSpaceSite.mem_precoverage_iff] at hR
            rcases hR with ⟨E₀, rfl, hE₀⟩
            obtain ⟨E₁, hE₁, hU, hCE'⟩ := pRepresentative ⟨U, E₀⟩
              (Space.isPHCovering_of_isEtaleCovering pFppfSite S eFppfMem
                (BigEtaleSpaceSite.IsCovering.etale hE₀))
            cases hU
            rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hCE']
            exact Precoverage.generate_mem_toGrothendieck ⟨E₁.2, rfl, hE₁⟩
        | top => exact P'.topology.top_mem _
        | pullback U R _ V f ih => exact P'.topology.pullback_stable _ ih
        | transitive U R R' _ _ ihR ihT =>
            exact P'.topology.transitive ihR _ fun _ _ hg ↦ ihT hg
      change (𝟭 (Over X)).IsContinuous (E'.topology.over X) (P'.topology.over X)
      refine Functor.isContinuous_id_of_le _ _ fun Z R hR => ?_
      rw [GrothendieckTopology.mem_over_iff] at hR ⊢
      exact htop Z.left hR

/-- **Stacks 0DGW.** The change-of-topology morphism `ε_X` from the big ph topos of `X` to its
big étale topos: the identity-on-spaces functor of slice categories is a morphism of sites,
because it is continuous and representably flat. -/
@[stacks 0DGW "the comparison morphism ε from the big ph to the big étale topos"]
def phToBigEtaleMorphism (X : P.Spaces) :
    MorphismOfTopoi (Sheaf (BigPHSpaceOver.topology P X) (Type (u + 1)))
      (Sheaf (E.bigEtaleTopology (etaleSpace P E h X)) (Type (u + 1))) :=
  letI := phToBigEtale_isContinuous P E h X
  (Functor.isMorphismOfSites_of_representablyFlat
    ((Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).inverse)
    (E.bigEtaleTopology (etaleSpace P E h X))
    (BigPHSpaceOver.topology P X)).morphismOfTopoi

/-- The direct image of `ε_X` is restriction along the identity-on-spaces functor of slice
categories, on the nose. -/
def phToBigEtale_pushforwardIso (X : P.Spaces) :
    (phToBigEtaleMorphism P E h X).pushforward ≅
      ((Over.postEquiv (canonicalSpaceEquivalence P E h).1
        (X := X)).inverse).sheafPushforwardContinuous (Type (u + 1))
        (E.bigEtaleTopology (etaleSpace P E h X)) (BigPHSpaceOver.topology P X) :=
  Iso.refl _

/-- Base change along `f` commutes with the identity-on-spaces change-of-topology functor of
slice categories. -/
def pullbackChangeOfTopologyIso {X Y : P.Spaces} (f : Y ⟶ X) :
    Over.pullback (etaleMap P E h f) ⋙
        (Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := Y)).inverse ≅
      (Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).inverse ⋙
        Over.pullback f := by
  cases P with
  | mk pSchemeSite pSchemeMem pFppfSite pFppfMem pCutoffEq pInitial pInitialSmall pInitialPH
      pBound pOrdinal pOrdinalLim pInitialBounded pIsSite pRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      exact Iso.refl _

/-- **Stacks 0DGW.** The morphism `a_X` from the big ph topos of `X` to its small étale topos,
defined as the composite of `ε_X` with the big-to-small étale morphism `π_X` of **Stacks 0DF3**.
The factorization `a_X = π_X ∘ ε_X` asserted by Stacks 0DGW is therefore definitional. -/
@[stacks 0DGW "the comparison morphism a to the small étale topos, as the composite π ∘ ε"]
def phToSmallEtaleMorphism (X : P.Spaces) :
    MorphismOfTopoi (Sheaf (BigPHSpaceOver.topology P X) (Type (u + 1)))
      (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
        (Type (u + 1))) :=
  (E.bigToSmallEtaleMorphism (etaleSpace P E h X)).comp (phToBigEtaleMorphism P E h X)

/-- **Stacks 0DGW**, the first diagram. For a morphism `f : Y ⟶ X` of algebraic spaces the direct
images of `ε_X ∘ f_{big, ph}` and of `f_{big, étale} ∘ ε_Y` are canonically isomorphic. -/
@[stacks 0DGW "the big ph–big étale square"]
def bigPHBigEtale_pushforwardCommIso {X Y : P.Spaces} (f : Y ⟶ X) :
    ((E.bigEtaleMorphism (etaleMap P E h f)).comp (phToBigEtaleMorphism P E h Y)).pushforward ≅
      ((phToBigEtaleMorphism P E h X).comp (bigPHMorphism P f)).pushforward := by
  cases P with
  | mk pSchemeSite pSchemeMem pFppfSite pFppfMem pCutoffEq pInitial pInitialSmall pInitialPH
      pBound pOrdinal pOrdinalLim pInitialBounded pIsSite pRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let P' : BigPHSpaceSite S :=
        ⟨pSchemeSite, pSchemeMem, pFppfSite, pFppfMem, pCutoffEq, pInitial, pInitialSmall,
          pInitialPH, pBound, pOrdinal, pOrdinalLim, pInitialBounded, pIsSite, pRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, pFppfSite, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      let JeX := E'.topology.over X
      let JeY := E'.topology.over Y
      let JpX := P'.topology.over X
      let JpY := P'.topology.over Y
      let eX := (Over.postEquiv (canonicalSpaceEquivalence P' E' rfl).1 (X := X)).inverse
      let eY := (Over.postEquiv (canonicalSpaceEquivalence P' E' rfl).1 (X := Y)).inverse
      let be := Over.pullback (etaleMap P' E' rfl f)
      let bp := Over.pullback f
      haveI heX : eX.IsContinuous JeX JpX := phToBigEtale_isContinuous P' E' rfl X
      haveI heY : eY.IsContinuous JeY JpY := phToBigEtale_isContinuous P' E' rfl Y
      haveI hbpE : be.IsContinuous JeX JeY :=
        (StacksRelocalization.isMorphismOfSites_overPullback E'.topology
          (etaleMap P' E' rfl f)).isContinuous
      haveI hbpP : bp.IsContinuous JpX JpY :=
        (StacksRelocalization.isMorphismOfSites_overPullback P'.topology f).isContinuous
      haveI : (be ⋙ eY).IsContinuous JeX JpY := Functor.isContinuous_comp be eY JeX JeY JpY
      haveI : (eX ⋙ bp).IsContinuous JeX JpY := Functor.isContinuous_comp eX bp JeX JpX JpY
      let eXpush := eX.sheafPushforwardContinuous (Type (u + 1)) JeX JpX
      let eYpush := eY.sheafPushforwardContinuous (Type (u + 1)) JeY JpY
      let hEtale := StacksRelocalization.sheafPushforwardOverMapIso E'.topology f
      let hPH := StacksRelocalization.sheafPushforwardOverMapIso P'.topology f
      let hEpsX := phToBigEtale_pushforwardIso P' E' rfl X
      let hEpsY := phToBigEtale_pushforwardIso P' E' rfl Y
      let hCompL := Functor.sheafPushforwardContinuousComp be eY (Type (u + 1)) JeX JeY JpY
      let hCompR := Functor.sheafPushforwardContinuousComp eX bp (Type (u + 1)) JeX JpX JpY
      have hsite : be ⋙ eY ≅ eX ⋙ bp := pullbackChangeOfTopologyIso P' E' rfl f
      let hSite := Functor.sheafPushforwardContinuousIso hsite (Type (u + 1)) JeX JpY
      change (phToBigEtaleMorphism P' E' rfl Y).pushforward ⋙
          (E'.bigEtaleMorphism (etaleMap P' E' rfl f)).pushforward ≅
        (bigPHMorphism P' f).pushforward ⋙ (phToBigEtaleMorphism P' E' rfl X).pushforward
      exact
        Functor.isoWhiskerRight hEpsY
            (E'.bigEtaleMorphism (etaleMap P' E' rfl f)).pushforward ≪≫
          Functor.isoWhiskerLeft eYpush hEtale ≪≫ hCompL ≪≫ hSite ≪≫ hCompR.symm ≪≫
          (Functor.isoWhiskerRight hPH eXpush).symm ≪≫
          Functor.isoWhiskerLeft (bigPHMorphism P' f).pushforward hEpsX.symm

/-- **Stacks 0DGW**, the second diagram. For a morphism `f : Y ⟶ X` of algebraic spaces the
direct images of `a_X ∘ f_{big, ph}` and of `f_{small} ∘ a_Y` are canonically isomorphic.

Since `a` is the composite of `ε` with `π`, this is the big square above pasted with the
big–small étale square of **Stacks 0DF6**. -/
@[stacks 0DGW "the big ph–small étale square"]
def bigPHSmallEtale_pushforwardCommIso {X Y : P.Spaces} (f : Y ⟶ X) :
    ((E.smallEtaleMorphism (etaleMap P E h f)).comp
        (phToSmallEtaleMorphism P E h Y)).pushforward ≅
      ((phToSmallEtaleMorphism P E h X).comp (bigPHMorphism P f)).pushforward := by
  cases P with
  | mk pSchemeSite pSchemeMem pFppfSite pFppfMem pCutoffEq pInitial pInitialSmall pInitialPH
      pBound pOrdinal pOrdinalLim pInitialBounded pIsSite pRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let P' : BigPHSpaceSite S :=
        ⟨pSchemeSite, pSchemeMem, pFppfSite, pFppfMem, pCutoffEq, pInitial, pInitialSmall,
          pInitialPH, pBound, pOrdinal, pOrdinalLim, pInitialBounded, pIsSite, pRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, pFppfSite, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      let epsX := phToBigEtaleMorphism P' E' rfl X
      let epsY := phToBigEtaleMorphism P' E' rfl Y
      let piX := E'.bigToSmallEtaleMorphism X
      let piY := E'.bigToSmallEtaleMorphism Y
      let sm := E'.smallEtaleMorphism f
      let bg := bigPHMorphism P' f
      let hSmall := E'.bigSmallEtale_pushforwardCommIso f
      let hBig := bigPHBigEtale_pushforwardCommIso P' E' rfl f
      change ((epsY.pushforward ⋙ piY.pushforward) ⋙ sm.pushforward) ≅
        (bg.pushforward ⋙ (epsX.pushforward ⋙ piX.pushforward))
      exact
        Functor.associator epsY.pushforward piY.pushforward sm.pushforward ≪≫
          Functor.isoWhiskerLeft epsY.pushforward hSmall ≪≫
          (Functor.associator epsY.pushforward (E'.bigEtaleMorphism f).pushforward
            piX.pushforward).symm ≪≫
          Functor.isoWhiskerRight hBig piX.pushforward ≪≫
          Functor.associator bg.pushforward epsX.pushforward piX.pushforward

/-! ### The small étale site of scheme charts

The small étale topos of an algebraic space `X` of the ph site is also presented by the site
`AlgebraicGeometry.Space.SmallEtale` of *schemes* étale over `X`, and for that presentation the
second square of Stacks 0DGW can be had from the ph site alone: the chart functor
`AlgebraicGeometry.BigPHSpaceSite.smallEtaleToPH` lands in the big ph slice directly, with no
auxiliary big étale site to mediate.
-/

/-- Every ph covering family of an algebraic space of the site generates a covering sieve, even
when the family itself does not satisfy the site's cardinal bound: the chosen representative of
it is combinatorially equivalent to it, hence generates the same sieve. -/
private theorem phCovering_generates_covering_sieve {X : P.Spaces}
    (F : PreZeroHypercover.{u + 2} X)
    (hF : Space.IsPHCovering P.fppfSite S P.fppf_mem (fun i ↦ (F.X i).1)
      (fun i ↦ (F.f i).hom)) :
    Sieve.generate F.presieve₀ ∈ P.topology X := by
  obtain ⟨F', hF', hX, hcomb⟩ := P.covering_representative ⟨X, F⟩ hF
  cases hX
  apply Precoverage.generate_mem_toGrothendieck
  rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb]
  exact ⟨F'.2, rfl, hF'⟩

/-- A jointly point-surjective family of algebraic spaces étale over `X` becomes a ph covering
sieve of the big ph slice at `X`: the family of underlying algebraic spaces is an étale covering
of `X`, hence a ph covering by **Stacks 0DFH**. -/
private theorem spacesEtale_precoverage_le_comap (X : P.Spaces) :
    Space.SpacesEtale.precoverage P.fppfSite S P.fppf_mem X ≤
      (P.topology.over X).toPrecoverage.comap
        (Space.SpacesEtale.inclusion P.fppfSite S P.fppf_mem X) := by
  let B := P.fppfSite
  let inc := Space.SpacesEtale.inclusion B S P.fppf_mem X
  rintro U _ ⟨F, rfl, hF⟩
  let e : ULift.{u + 2} F.I₀ ≃ F.I₀ := Equiv.ulift
  let F' : PreZeroHypercover.{u + 2} U := F.reindex e
  have hF' : Space.SpacesEtale.IsCovering B S P.fppf_mem X ⟨U, F'⟩ := by
    intro x
    obtain ⟨i, y, hy⟩ := hF x
    obtain ⟨j, rfl⟩ := e.surjective i
    refine ⟨j, y, ?_⟩
    dsimp [F', PreZeroHypercover.reindex, PreZeroHypercover.restrictIndex,
      Space.SpacesEtale.toSpaces, Space.SpacesEtale.inclusion]
    exact hy
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff,
    ← PreZeroHypercover.presieve₀_map]
  have hpre : (F.map inc).presieve₀ = (F'.map inc).presieve₀ := by
    simpa only [PreZeroHypercover.presieve₀_map] using
      congrArg (fun R ↦ R.map inc) (F.presieve₀_reindex e).symm
  rw [hpre]
  let G := F'.map (inc ⋙ Over.forget X)
  have hEt : Space.IsEtaleCovering B S P.fppf_mem (fun i ↦ (G.X i).1)
      (fun i ↦ (G.f i).hom) := by
    refine ⟨((inc ⋙ Over.forget X).obj U).property, fun i ↦ (G.X i).property,
      fun i ↦ Space.isEtale_of_isEtale_over B S P.fppf_mem
        (G.X i).property ((inc ⋙ Over.forget X).obj U).property X.property (G.f i).hom
        (F'.X i).1.hom.hom U.1.hom.hom (F'.X i).property U.property
        (congrArg (fun q ↦ q.hom) ((inc.map (F'.f i)).w)),
      Set.eq_univ_of_forall fun x ↦ ?_⟩
    obtain ⟨i, y, hy⟩ := hF' x
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨y, hy⟩⟩
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
    PreZeroHypercover.presieve₀_map]
  refine P.topology.superset_covering ((Sieve.generate_le_iff _ _).2 ?_)
    (phCovering_generates_covering_sieve P G
      (Space.isPHCovering_of_isEtaleCovering B S P.fppf_mem hEt))
  rw [Presieve.ofArrows_le_iff]
  intro i
  apply Sieve.le_generate
  exact ⟨_, (F'.map inc).f i, 𝟙 _, ⟨⟨i⟩⟩, rfl⟩

/-- The inclusion of the algebraic spaces étale over `X` into the big ph slice at `X` is
continuous: it preserves fibre products, and the image of a jointly point-surjective family
generates a ph covering sieve. -/
instance spacesEtale_inclusion_isContinuous (X : P.Spaces) :
    (Space.SpacesEtale.inclusion P.fppfSite S P.fppf_mem X).IsContinuous
      (Space.SpacesEtale.topology P.fppfSite S P.fppf_mem X) (BigPHSpaceOver.topology P X) :=
  Stacks.Sites.isContinuous_toGrothendieck_of_le_comap _ _ _
    (spacesEtale_precoverage_le_comap P X)

/-- The scheme charts of the small étale site of `X`, viewed in the big ph slice at `X`: a
scheme étale over `X` is an algebraic space étale over `X`. -/
abbrev smallEtaleToPH (X : P.Spaces) :
    Space.SmallEtale P.fppfSite S P.fppf_mem X.1 ⥤ Over X :=
  Space.comparisonFunctor P.fppfSite S P.fppf_mem X ⋙
    Space.SpacesEtale.inclusion P.fppfSite S P.fppf_mem X

/-- The chart functor of the small étale site into the big ph slice is continuous, being the
composite of the comparison functor of **Stacks 03G1** with the inclusion of the spaces-étale
site. -/
instance smallEtaleToPH_isContinuous (X : P.Spaces) :
    (smallEtaleToPH P X).IsContinuous
      (Space.SmallEtale.topology P.fppfSite S P.fppf_mem X.1) (BigPHSpaceOver.topology P X) :=
  Functor.isContinuous_comp (Space.comparisonFunctor P.fppfSite S P.fppf_mem X)
    (Space.SpacesEtale.inclusion P.fppfSite S P.fppf_mem X)
    (Space.SmallEtale.topology P.fppfSite S P.fppf_mem X.1)
    (Space.SpacesEtale.topology P.fppfSite S P.fppf_mem X) (BigPHSpaceOver.topology P X)

/-- **Stacks 0DGW**, the second diagram, for the presentation of the small étale topos by the
site of scheme charts. For a morphism `f : X ⟶ Y` of algebraic spaces of the ph site the direct
images of `f_{small} ∘ a_X` and of `a_Y ∘ f_{big, ph}` are canonically isomorphic, where `a` is
restriction along the chart functor `smallEtaleToPH`. No big étale site intervenes. -/
@[stacks 0DGW "the big ph–small étale square, for the small étale site of scheme charts"]
def bigPHSmallEtaleCharts_pushforwardCommIso {X Y : P.Spaces} (f : X ⟶ Y) :
    ((smallEtaleToPH P X).sheafPushforwardContinuous (Type (u + 1))
        (Space.SmallEtale.topology P.fppfSite S P.fppf_mem X.1)
        (BigPHSpaceOver.topology P X)) ⋙
      (Space.smallToposMorphism P.fppfSite S P.fppf_mem f).pushforward ≅
    (bigPHMorphism P f).pushforward ⋙
      (smallEtaleToPH P Y).sheafPushforwardContinuous (Type (u + 1))
        (Space.SmallEtale.topology P.fppfSite S P.fppf_mem Y.1)
        (BigPHSpaceOver.topology P Y) := by
  let B := P.fppfSite
  let Jex := Space.SmallEtale.topology B S P.fppf_mem X.1
  let Jey := Space.SmallEtale.topology B S P.fppf_mem Y.1
  let Jsx := Space.SpacesEtale.topology B S P.fppf_mem X
  let Jsy := Space.SpacesEtale.topology B S P.fppf_mem Y
  let Jpx := P.topology.over X
  let Jpy := P.topology.over Y
  let cx := Space.comparisonFunctor B S P.fppf_mem X
  let cy := Space.comparisonFunctor B S P.fppf_mem Y
  let ix := Space.SpacesEtale.inclusion B S P.fppf_mem X
  let iy := Space.SpacesEtale.inclusion B S P.fppf_mem Y
  let bx := (Space.spacesBaseChange B S P.fppf_mem f).functor
  let py := Over.pullback f
  letI : bx.IsContinuous Jsy Jsx :=
    (Space.spacesBaseChange_isMorphismOfSites B S P.fppf_mem f).isContinuous
  letI : py.IsContinuous Jpy Jpx :=
    (StacksRelocalization.isMorphismOfSites_overPullback P.topology f).isContinuous
  letI : (cx ⋙ ix).IsContinuous Jex Jpx := Functor.isContinuous_comp cx ix Jex Jsx Jpx
  letI : (cy ⋙ iy).IsContinuous Jey Jpy := Functor.isContinuous_comp cy iy Jey Jsy Jpy
  letI : (bx ⋙ ix).IsContinuous Jsy Jpx := Functor.isContinuous_comp bx ix Jsy Jsx Jpx
  letI : (iy ⋙ py).IsContinuous Jsy Jpx := Functor.isContinuous_comp iy py Jsy Jpy Jpx
  let A := Type (u + 1)
  let icx := ix.sheafPushforwardContinuous A Jsx Jpx
  let icy := iy.sheafPushforwardContinuous A Jsy Jpy
  let ccx := cx.sheafPushforwardContinuous A Jex Jsx
  let ccy := cy.sheafPushforwardContinuous A Jey Jsy
  let bxx := bx.sheafPushforwardContinuous A Jsy Jsx
  let pyy := py.sheafPushforwardContinuous A Jpy Jpx
  let ky := (cy ⋙ iy).sheafPushforwardContinuous A Jey Jpy
  let s := Space.smallToposMorphism B S P.fppf_mem f
  -- The chosen base change of a chart is, by its construction in Stacks 03G2, the restriction
  -- of `CategoryTheory.Over.pullback f` to the charts, so the square of site functors commutes
  -- on the nose.
  let bcIso : bx ⋙ ix ≅ iy ⋙ py :=
    ObjectProperty.liftCompιIso (Space.IsEtaleOver B S P.fppf_mem X) (iy ⋙ py)
      (fun V ↦ Space.isEtaleOver_overPullback B S P.fppf_mem f V.1 V.property)
  change ((cx ⋙ ix).sheafPushforwardContinuous A Jex Jpx ⋙ s.pushforward) ≅
    ((bigPHMorphism P f).pushforward ⋙ ky)
  exact
    Functor.isoWhiskerRight
        (Functor.sheafPushforwardContinuousComp cx ix A Jex Jsx Jpx).symm s.pushforward ≪≫
      Functor.associator icx ccx s.pushforward ≪≫
      Functor.isoWhiskerLeft icx
        (Space.smallToposMorphism_comparison B S P.fppf_mem f) ≪≫
      (Functor.associator icx bxx ccy).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.sheafPushforwardContinuousComp bx ix A Jsy Jsx Jpx) ccy ≪≫
      Functor.isoWhiskerRight
        (Functor.sheafPushforwardContinuousIso bcIso A Jsy Jpx) ccy ≪≫
      Functor.isoWhiskerRight
        (Functor.sheafPushforwardContinuousComp iy py A Jsy Jpy Jpx).symm ccy ≪≫
      Functor.associator pyy icy ccy ≪≫
      Functor.isoWhiskerLeft pyy
        (Functor.sheafPushforwardContinuousComp cy iy A Jey Jsy Jpy) ≪≫
      Functor.isoWhiskerRight (bigPHMorphismPushforwardIso P f).symm ky

end AlgebraicGeometry.BigPHSpaceSite

end
