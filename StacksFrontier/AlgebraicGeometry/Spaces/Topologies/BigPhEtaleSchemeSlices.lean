module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhToSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SchemeToSpaceSites
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MainstreamRepresentability
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.PhToEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableSmallEtaleBridge

/-!
# The big ph and étale slice sites of a scheme, inside those of algebraic spaces

Let `P` be a big ph site of algebraic spaces over `S`, `E` a big étale site of algebraic spaces
over `S` built on the same big fppf site, and `U` a scheme of the chosen big ph site of schemes
of `P`, over `S`. Write `B` for that big ph site of schemes. The slice of the big ph site of
schemes at `U` maps to the slice of the big ph site of algebraic spaces at the algebraic space
represented by `U`, by the inclusion of schemes into algebraic spaces; this file shows that the
induced restriction functor on sheaves is an equivalence, both for the ph topologies and for the
étale topologies (the étale topology of schemes being that of the big étale site
`AlgebraicGeometry.phAssociatedBigEtaleSite B` associated to `B`), and that the two are
compatible with the change of topology `ε`.

## Main definitions

* `AlgebraicGeometry.BigPHSpaceSite.schemeSliceToSpaceSlice`: the functor from the slice of
  the big ph site of schemes at `U` to the slice of the big ph site of algebraic spaces at `U`.
* `AlgebraicGeometry.BigPHSpaceSite.schemeSliceToEtaleSpaceSlice`: the same functor, landing in
  the slice of the big étale site of algebraic spaces.
* `AlgebraicGeometry.BigPHSpaceSite.schemeSliceToEtaleSpaceSliceCompIso`: followed by the
  identity-on-spaces functor of `ε`, the second functor is the first.

## Main results

* `AlgebraicGeometry.BigPHSpaceSite.schemeToEtaleSpace_isDenseSubsite`: **Stacks 0DFV**, étale
  case, for the inclusion of schemes into the algebraic spaces of `E`.
* The restriction functors along both slice functors are equivalences of sheaf categories, for
  any coefficient category with the relevant limits.
* `AlgebraicGeometry.BigPHSpaceSite.exists_smallEtaleSchemeChart`: the small étale site of a
  scheme `U` maps to the spaces-étale site of the algebraic space represented by `U` by a
  continuous and cocontinuous functor, restriction along which is an equivalence on sheaves of
  sets and on abelian sheaves.

## Implementation notes

The étale case of Stacks 0DFV on the base is stated for a big étale site of algebraic spaces
whose own chosen big étale site of schemes has the cutoff of its fppf site. The étale topology
of algebraic spaces does not depend on that chosen site of schemes, so it is applied to `E` with
its site of schemes replaced by `phAssociatedBigEtaleSite B`, whose cutoff is that of `B`, hence
that of the fppf site. Identifying the algebraic spaces of `E` with those of `P` requires the
compatibility `h : P.fppfSite = E.fppfSite`, which is eliminated by `cases`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigPHSpaceSite

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite)

/-- The identity-on-schemes functor between the two cutoff categories of a big ph site of
algebraic spaces is full. -/
instance schemesToFppf_full : (schemesToFppf P).Full where
  map_surjective f := ⟨ObjectProperty.homMk f.hom, rfl⟩

/-- The identity-on-schemes functor between the two cutoff categories of a big ph site of
algebraic spaces is faithful. -/
instance schemesToFppf_faithful : (schemesToFppf P).Faithful where
  map_injective {X Y} f g hfg := by
    ext
    exact congrArg (fun q ↦ q.hom) hfg

/-- The inclusion of the schemes of a big fppf site into its algebraic spaces is fully
faithful, by the Yoneda lemma. -/
def _root_.AlgebraicGeometry.schemeSpaceFunctorFullyFaithful (B : BigFppfSite.{u})
    (hS : B.Contains S) :
    (schemeSpaceFunctor B S hS).FullyFaithful where
  preimage f := yoneda.preimage f.hom
  map_preimage _ := ObjectProperty.hom_ext _ (yoneda.map_preimage _)
  preimage_map f := yoneda.preimage_map f

/-- The inclusion of schemes into algebraic spaces of a big ph site of algebraic spaces is fully
faithful. -/
def schemeToSpaceFullyFaithful : P.schemeToSpace.FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful
    (Over.post (X := P.schemeSite.obj S P.scheme_mem) (schemesToFppf P))).comp
    (schemeSpaceFunctorFullyFaithful P.fppfSite P.fppf_mem)

/-- The inclusion of schemes into algebraic spaces of a big ph site of algebraic spaces is
full. -/
instance schemeToSpace_full : P.schemeToSpace.Full :=
  (schemeToSpaceFullyFaithful P).full

/-- The inclusion of schemes into algebraic spaces of a big ph site of algebraic spaces is
faithful. -/
instance schemeToSpace_faithful : P.schemeToSpace.Faithful :=
  (schemeToSpaceFullyFaithful P).faithful

/-- **Stacks 0DFV**, ph case, localized: the inclusion of schemes into algebraic spaces,
localized at a scheme `U` over `S`, is a dense subsite inclusion. -/
instance overPost_schemeToSpace_isDenseSubsite (U : P.Schemes) :
    (Over.post (X := U) P.schemeToSpace).IsDenseSubsite
      ((BigPHOver.topology P.schemeSite S P.scheme_mem).over U)
      (P.topology.over (P.schemeToSpace.obj U)) := by
  have := (phSchemeToSpace_isSpecialCocontinuous P).2
  exact Functor.isDenseSubsite_overPost_of_fullyFaithful _ _ _ U

/-- The functor from the slice of the big ph site of schemes at a scheme `U` over `S` to the
slice of the big ph site of algebraic spaces at the algebraic space represented by `U`. -/
abbrev schemeSliceToSpaceSlice (U : P.Schemes) :
    Over U.left ⥤ Over (P.schemeToSpace.obj U) :=
  (Over.iteratedSliceEquiv U).inverse ⋙ Over.post P.schemeToSpace

/-- The slice functor is continuous for the ph topologies. -/
instance schemeSliceToSpaceSlice_isContinuous (U : P.Schemes) :
    (schemeSliceToSpaceSlice P U).IsContinuous (P.schemeSite.topology.over U.left)
      (BigPHSpaceOver.topology P (P.schemeToSpace.obj U)) :=
  Functor.isContinuous_comp _ _ _
    ((BigPHOver.topology P.schemeSite S P.scheme_mem).over U) _

/-- Restriction of sheaves along the slice functor is an equivalence, for the ph topologies. -/
instance schemeSliceToSpaceSlice_sheafPushforward_isEquivalence (U : P.Schemes)
    (A : Type*) [Category* A]
    [∀ X, HasLimitsOfShape (StructuredArrow X (Over.iteratedSliceEquiv U).inverse.op) A]
    [∀ X, HasLimitsOfShape (StructuredArrow X (Over.post (X := U) P.schemeToSpace).op) A] :
    ((schemeSliceToSpaceSlice P U).sheafPushforwardContinuous A
      (P.schemeSite.topology.over U.left)
      (BigPHSpaceOver.topology P (P.schemeToSpace.obj U))).IsEquivalence :=
  have : ((Over.iteratedSliceEquiv U).inverse.sheafPushforwardContinuous A
      (P.schemeSite.topology.over U.left)
      ((BigPHOver.topology P.schemeSite S P.scheme_mem).over U)).IsEquivalence := inferInstance
  have : ((Over.post (X := U) P.schemeToSpace).sheafPushforwardContinuous A
      ((BigPHOver.topology P.schemeSite S P.scheme_mem).over U)
      (BigPHSpaceOver.topology P (P.schemeToSpace.obj U))).IsEquivalence := inferInstance
  Functor.isEquivalence_of_iso (Functor.sheafPushforwardContinuousComp
    (Over.iteratedSliceEquiv U).inverse (Over.post P.schemeToSpace) A
    (P.schemeSite.topology.over U.left)
    ((BigPHOver.topology P.schemeSite S P.scheme_mem).over U)
    (BigPHSpaceOver.topology P (P.schemeToSpace.obj U)))

/-- The inclusion of schemes into the algebraic spaces of the big étale site `E`. -/
abbrev schemeToEtaleSpace : P.Schemes ⥤ E.Spaces :=
  P.schemeToSpace ⋙ (canonicalSpaceEquivalence P E h).1.functor

/-- The big étale site of algebraic spaces `E`, with its chosen big étale site of schemes
replaced by the one associated to the big ph site of schemes of `P`. Its algebraic spaces and
its topology are those of `E`. -/
abbrev etaleSpaceSiteOverPhSchemes : BigEtaleSpaceSite S :=
  { E with
    schemeSite := phAssociatedBigEtaleSite P.schemeSite
    scheme_mem := P.scheme_mem }

include h in
/-- The site `etaleSpaceSiteOverPhSchemes P E` satisfies the cutoff hypothesis of the étale case
of Stacks 0DFV: its chosen big étale site of schemes has the cutoff of its fppf site. -/
theorem etaleSpaceSiteOverPhSchemes_cutoff :
    (etaleSpaceSiteOverPhSchemes P E).schemeSite.cutoff =
      (etaleSpaceSiteOverPhSchemes P E).fppfSite.cutoff :=
  P.cutoff_eq.trans (congrArg BigFppfSite.cutoff h)

/-- **Stacks 0DFV**, étale case, for the algebraic spaces of `E`: the inclusion of the schemes of
the big ph site of schemes of `P` into the algebraic spaces of `E` is a dense subsite inclusion
for the étale topologies. -/
theorem schemeToEtaleSpace_isDenseSubsite :
    (schemeToEtaleSpace P E h).IsDenseSubsite
      ((phAssociatedBigEtaleSite P.schemeSite).topology.over
        ((phAssociatedBigEtaleSite P.schemeSite).obj S P.scheme_mem))
      E.topology := by
  have hd := (etaleSchemeToSpace_isSpecialCocontinuous (etaleSpaceSiteOverPhSchemes P E)
    (etaleSpaceSiteOverPhSchemes_cutoff P E h)).2
  rw [bigEtaleOver_topology_eq] at hd
  cases P
  cases E
  cases h
  exact hd

/-- The inclusion of schemes into the algebraic spaces of `E` is full. -/
instance schemeToEtaleSpace_full : (schemeToEtaleSpace P E h).Full :=
  inferInstanceAs (P.schemeToSpace ⋙ (canonicalSpaceEquivalence P E h).1.functor).Full

/-- The inclusion of schemes into the algebraic spaces of `E` is faithful. -/
instance schemeToEtaleSpace_faithful : (schemeToEtaleSpace P E h).Faithful :=
  inferInstanceAs (P.schemeToSpace ⋙ (canonicalSpaceEquivalence P E h).1.functor).Faithful

/-- Every algebraic space of `E` is covered, for the étale topology, by schemes of the big ph
site of schemes of `P`. -/
instance schemeToEtaleSpace_isCoverDense : (schemeToEtaleSpace P E h).IsCoverDense E.topology :=
  have := schemeToEtaleSpace_isDenseSubsite P E h
  Functor.IsDenseSubsite.isCoverDense
    ((phAssociatedBigEtaleSite P.schemeSite).topology.over
      ((phAssociatedBigEtaleSite P.schemeSite).obj S P.scheme_mem)) E.topology _

/-- **Stacks 0DFV**, étale case, localized at a scheme `U` over `S`. -/
instance overPost_schemeToEtaleSpace_isDenseSubsite (U : P.Schemes) :
    (Over.post (X := U) (schemeToEtaleSpace P E h)).IsDenseSubsite
      ((phAssociatedBigEtaleSite P.schemeSite).topology.over
        ((phAssociatedBigEtaleSite P.schemeSite).obj S P.scheme_mem) |>.over U)
      (E.bigEtaleTopology (etaleSpace P E h (P.schemeToSpace.obj U))) := by
  have := schemeToEtaleSpace_isDenseSubsite P E h
  exact Functor.isDenseSubsite_overPost_of_fullyFaithful
    ((phAssociatedBigEtaleSite P.schemeSite).topology.over
      ((phAssociatedBigEtaleSite P.schemeSite).obj S P.scheme_mem))
    E.topology (schemeToEtaleSpace P E h) U

/-- The functor from the slice of the big ph site of schemes at a scheme `U` over `S` to the
slice of the big étale site of algebraic spaces of `E` at the algebraic space represented by
`U`. -/
abbrev schemeSliceToEtaleSpaceSlice (U : P.Schemes) :
    Over U.left ⥤ Over (etaleSpace P E h (P.schemeToSpace.obj U)) :=
  (Over.iteratedSliceEquiv U).inverse ⋙ Over.post (schemeToEtaleSpace P E h)

/-- The étale slice functor is continuous for the étale topologies. -/
instance schemeSliceToEtaleSpaceSlice_isContinuous (U : P.Schemes) :
    (schemeSliceToEtaleSpaceSlice P E h U).IsContinuous
      ((phAssociatedBigEtaleSite P.schemeSite).topology.over U.left)
      (E.bigEtaleTopology (etaleSpace P E h (P.schemeToSpace.obj U))) :=
  Functor.isContinuous_comp _ _ _
    ((phAssociatedBigEtaleSite P.schemeSite).topology.over
        ((phAssociatedBigEtaleSite P.schemeSite).obj S P.scheme_mem) |>.over U) _

/-- Restriction of sheaves along the étale slice functor is an equivalence. -/
instance schemeSliceToEtaleSpaceSlice_sheafPushforward_isEquivalence (U : P.Schemes)
    (A : Type*) [Category* A]
    [∀ X, HasLimitsOfShape (StructuredArrow X (Over.iteratedSliceEquiv U).inverse.op) A]
    [∀ X, HasLimitsOfShape
      (StructuredArrow X (Over.post (X := U) (schemeToEtaleSpace P E h)).op) A] :
    ((schemeSliceToEtaleSpaceSlice P E h U).sheafPushforwardContinuous A
      ((phAssociatedBigEtaleSite P.schemeSite).topology.over U.left)
      (E.bigEtaleTopology (etaleSpace P E h (P.schemeToSpace.obj U)))).IsEquivalence :=
  have := overPost_schemeToEtaleSpace_isDenseSubsite P E h U
  have : ((Over.iteratedSliceEquiv U).inverse.sheafPushforwardContinuous A
      ((phAssociatedBigEtaleSite P.schemeSite).topology.over U.left)
      ((phAssociatedBigEtaleSite P.schemeSite).topology.over
        ((phAssociatedBigEtaleSite P.schemeSite).obj S P.scheme_mem) |>.over U)).IsEquivalence :=
    inferInstance
  have : ((Over.post (X := U) (schemeToEtaleSpace P E h)).sheafPushforwardContinuous A
      ((phAssociatedBigEtaleSite P.schemeSite).topology.over
        ((phAssociatedBigEtaleSite P.schemeSite).obj S P.scheme_mem) |>.over U)
      (E.bigEtaleTopology (etaleSpace P E h (P.schemeToSpace.obj U)))).IsEquivalence :=
    inferInstance
  Functor.isEquivalence_of_iso (Functor.sheafPushforwardContinuousComp
    (Over.iteratedSliceEquiv U).inverse (Over.post (schemeToEtaleSpace P E h)) A
    ((phAssociatedBigEtaleSite P.schemeSite).topology.over U.left)
    ((phAssociatedBigEtaleSite P.schemeSite).topology.over
        ((phAssociatedBigEtaleSite P.schemeSite).obj S P.scheme_mem) |>.over U)
    (E.bigEtaleTopology (etaleSpace P E h (P.schemeToSpace.obj U))))

/-- Followed by the identity-on-spaces functor of the change of topology `ε`, the étale slice
functor is the ph slice functor. -/
def schemeSliceToEtaleSpaceSliceCompIso (U : P.Schemes) :
    schemeSliceToEtaleSpaceSlice P E h U ⋙
        (Over.postEquiv (canonicalSpaceEquivalence P E h).1
          (X := P.schemeToSpace.obj U)).inverse ≅
      schemeSliceToSpaceSlice P U :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Over.iteratedSliceEquiv U).inverse
      (Functor.isoWhiskerRight
          (Over.postComp P.schemeToSpace (canonicalSpaceEquivalence P E h).1.functor) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (Over.post P.schemeToSpace)
          (Over.postEquiv (canonicalSpaceEquivalence P E h).1
            (X := P.schemeToSpace.obj U)).unitIso.symm ≪≫
        Functor.rightUnitor _)

/-- The small étale topology of a scheme of a big étale site is the étale precoverage of
schemes, restricted along the inclusions of the small étale site into the slice and of the slice
into all schemes. In particular it depends on the big étale site only through its cutoff. -/
theorem smallEtale_topology_eq_comap (E' : BigEtaleSite.{u}) (T : E'.Scheme) :
    SmallEtale.topology E' T.obj T.property =
      (((Scheme.etalePrecoverage.comap E'.inclusion).comap (Over.forget T)).comap
        (SmallEtale.inclusion E' T.obj T.property)).toGrothendieck := by
  rw [SmallEtale.topology, smallEtale_precoverage_eq_comap, bigEtaleOver_precoverage_eq_comap,
    bigEtalePrecoverage_eq_comap]

/-- Restriction along the chart functor of a representable algebraic space is an equivalence of
sheaf categories, for any coefficient category with the relevant limits. -/
private theorem representedChartFunctor_sheafPushforward_isEquivalence (F : BigFppfSite.{u})
    (hSF : F.Contains S) (T : BigFppfOver F S hSF) (A : Type*) [Category* A]
    [∀ X, HasLimitsOfShape
      (StructuredArrow X (Space.representedSmallEtaleEquivalence F S hSF T).inverse.op) A]
    [∀ X, HasLimitsOfShape
      (StructuredArrow X (Space.comparisonFunctor F S hSF (Space.yonedaSpace F S hSF T)).op) A] :
    ((Space.representedChartFunctor F S hSF T).sheafPushforwardContinuous A
      (Space.representedSchemeTopology F S hSF T)
      (Space.SpacesEtale.topology F S hSF (Space.yonedaSpace F S hSF T))).IsEquivalence :=
  have : (Space.comparisonFunctor F S hSF (Space.yonedaSpace F S hSF T)).IsDenseSubsite
      (Space.SmallEtale.topology F S hSF (yoneda.obj T))
      (Space.SpacesEtale.topology F S hSF (Space.yonedaSpace F S hSF T)) :=
    Space.comparisonFunctor_isDenseSubsite F S hSF (Space.yonedaSpace F S hSF T)
  have : ((Space.representedSmallEtaleEquivalence F S hSF T).inverse.sheafPushforwardContinuous
      A (Space.representedSchemeTopology F S hSF T)
      (Space.SmallEtale.topology F S hSF (yoneda.obj T))).IsEquivalence := inferInstance
  have : ((Space.comparisonFunctor F S hSF (Space.yonedaSpace F S hSF T)).sheafPushforwardContinuous
      A (Space.SmallEtale.topology F S hSF (yoneda.obj T))
      (Space.SpacesEtale.topology F S hSF (Space.yonedaSpace F S hSF T))).IsEquivalence :=
    inferInstance
  Functor.isEquivalence_of_iso
    (Functor.sheafPushforwardContinuousComp
      (Space.representedSmallEtaleEquivalence F S hSF T).inverse
      (Space.comparisonFunctor F S hSF (Space.yonedaSpace F S hSF T)) A
      (Space.representedSchemeTopology F S hSF T)
      (Space.SmallEtale.topology F S hSF (yoneda.obj T))
      (Space.SpacesEtale.topology F S hSF (Space.yonedaSpace F S hSF T)))

/-- **The small étale site of a scheme, inside the spaces-étale site of the algebraic space it
represents.** For a scheme `U` of the big ph site of schemes of `P`, over `S`, there is a
continuous and cocontinuous functor from the small étale site of `U` (in the big étale site
associated to the big ph site of schemes) to the spaces-étale site of the algebraic space of `E`
represented by `U`, restriction along which is an equivalence on sheaves of sets and on abelian
sheaves, and which is compatible with the inclusions of both sites into the big ph slice at
`U`. -/
theorem exists_smallEtaleSchemeChart (U : P.Schemes) :
    ∃ (σ : SmallEtale (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property ⥤
        Space.SpacesEtale E.fppfSite S E.fppf_mem (etaleSpace P E h (P.schemeToSpace.obj U)))
      (_ : σ.IsContinuous
        (SmallEtale.topology (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property)
        (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
          (etaleSpace P E h (P.schemeToSpace.obj U))))
      (_ : σ.IsCocontinuous
        (SmallEtale.topology (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property)
        (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
          (etaleSpace P E h (P.schemeToSpace.obj U)))),
      (σ.sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property)
        (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
          (etaleSpace P E h (P.schemeToSpace.obj U)))).IsEquivalence ∧
      (σ.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property)
        (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
          (etaleSpace P E h (P.schemeToSpace.obj U)))).IsEquivalence ∧
      Nonempty (σ ⋙ Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem
          (etaleSpace P E h (P.schemeToSpace.obj U)) ⋙
          (Over.postEquiv (canonicalSpaceEquivalence P E h).1
            (X := P.schemeToSpace.obj U)).inverse ≅
        SmallEtale.inclusion (phAssociatedBigEtaleSite P.schemeSite) U.left.obj U.left.property ⋙
          schemeSliceToSpaceSlice P U) := by
  revert U
  obtain ⟨⟨a₁, a₂, κ, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆⟩,
    hSB, F, hSF, hcut⟩ := P
  cases E
  cases h
  cases hcut
  intro U
  let B : BigPHSite.{u} :=
    ⟨a₁, a₂, F.cutoff, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆⟩
  let T : BigFppfOver F S hSF := Over.mk (ObjectProperty.homMk U.hom.hom :
    (⟨U.left.obj, U.left.property⟩ : F.Schemes) ⟶ F.obj hSF)
  have htop : SmallEtale.topology (phAssociatedBigEtaleSite B) U.left.obj U.left.property =
      Space.representedSchemeTopology F S hSF T :=
    (smallEtale_topology_eq_comap (phAssociatedBigEtaleSite B) U.left).trans
      (smallEtale_topology_eq_comap (associatedBigEtaleSite F) T.left).symm
  have hcd : (Space.comparisonFunctor F S hSF (Space.yonedaSpace F S hSF T)).IsDenseSubsite
      (Space.SmallEtale.topology F S hSF (yoneda.obj T))
      (Space.SpacesEtale.topology F S hSF (Space.yonedaSpace F S hSF T)) :=
    Space.comparisonFunctor_isDenseSubsite F S hSF (Space.yonedaSpace F S hSF T)
  have hcc : (Space.representedChartFunctor F S hSF T).IsCocontinuous
      (Space.representedSchemeTopology F S hSF T)
      (Space.SpacesEtale.topology F S hSF (Space.yonedaSpace F S hSF T)) :=
    isCocontinuous_comp (Space.representedSmallEtaleEquivalence F S hSF T).inverse
      (Space.comparisonFunctor F S hSF (Space.yonedaSpace F S hSF T))
      (Space.representedSchemeTopology F S hSF T)
      (Space.SmallEtale.topology F S hSF (yoneda.obj T))
  rw [htop]
  refine ⟨Space.representedChartFunctor F S hSF T,
    Space.representedChartFunctor_isContinuous F S hSF T, hcc,
    representedChartFunctor_sheafPushforward_isEquivalence F hSF T (Type (u + 1)),
    representedChartFunctor_sheafPushforward_isEquivalence F hSF T AddCommGrpCat.{u + 1}, ?_⟩
  exact ⟨NatIso.ofComponents (fun V ↦ Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ rfl))
    fun _ ↦ Over.OverMorphism.ext (ObjectProperty.hom_ext _ rfl)⟩

end AlgebraicGeometry.BigPHSpaceSite
