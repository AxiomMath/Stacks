module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Comparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion

/-!
# The small Zariski site inside a localized big `τ`-site

Let `B` be one of the five big sites of a topology `τ`, let `S` be a scheme below its cutoff
and let `ε : (Sch/S)_τ ⟶ S_Zar` be the inclusion of the small Zariski site of `S`.  This file
proves that the functor underlying `ε` is **continuous**, for all five `τ` at once.

The functor is `Stacks.Adequate.opensBelowToOver`, which sends an open `V` of `S` to the
size-bounded scheme `V` over `S` by its open immersion; at the cutoff of a big site its target
is the localized big site `Over (AlgebraicGeometry.base B S hS)`.  Continuity is Mathlib's
criterion for a representably flat functor — cover preserving plus representably flat — and
both halves are uniform in `τ`.

## Main definitions

* `AlgebraicGeometry.opensBelowHypercover`: the family of the localized big site cut out by a
  covering sieve of the small Zariski site, namely the open immersions of its members.

## Main results

* `AlgebraicGeometry.representablyFlat_opensBelowToOver`: the functor is representably flat.
* `AlgebraicGeometry.isTerminal_opensBelowToOver_top`: the whole of `S` goes to a final object.
* `AlgebraicGeometry.opensBelowToOver_preservesLimitsOfShape_walkingCospan` and
  `AlgebraicGeometry.opensBelowToOver_preservesLimitsOfShape_walkingParallelPair`: it preserves
  fibre products and equalizers, which is what makes restriction along it preserve injective
  abelian sheaves.
* `AlgebraicGeometry.coverPreserving_opensBelowToOver`: it is cover preserving into the
  localized `τ`-topology, for each of the five `τ`.
* `AlgebraicGeometry.isContinuous_opensBelowToOver`: **the instance this file exists for** —
  the functor is continuous, so restriction along it is the direct image of a morphism of sites
  `(Sch/S)_τ → S_Zar`.

## Implementation notes

The statements are indexed by `AlgebraicGeometry.CoveringTopology` and are about
`AlgebraicGeometry.overTopology`, which is the indexing of every other input of
[Stacks, Tag 03P2] on the big sites: the affine acyclicity
`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`, the eight covering-system slots of
`AlgebraicGeometry.overStandardCoverings`, and the continuity
`AlgebraicGeometry.isContinuous_overToSlice` of the functor into the slice of all schemes.

The library's other continuity statement for the small Zariski site inside a big site,
`AlgebraicGeometry.BigFppfOver.isContinuous_baseOpensToBig`, is **not** usable for that, even
though it covers five topologies too.  It is indexed by `AlgebraicGeometry.SiteKind` and is
about `AlgebraicGeometry.BigFppfOver.baseOverTopology`: five topologies on the *one* underlying
category of a chosen big **fppf** site, cut out by that site's own chosen fppf covering
families.  A `AlgebraicGeometry.BigSite` of a topology `τ` is instead its own structure, with
its own cutoff cardinal and its own chosen `τ`-covering families, so for `τ ≠ fppf` the two are
topologies on different categories and there is no map between the two indexings.  At `fppf`
alone they do agree — definitionally, by the `| fppf => rfl` branch of
`AlgebraicGeometry.overTopology_eq_siteTopology_over`.

Cover preservation is therefore proved from scratch against `overTopology`, and the route is the
uniform-in-`τ` one that
`AlgebraicGeometry.IsOverStandardCovering.sieve₀_mem_overTopology` also takes: the open
immersions of the members of a covering sieve are a `τ`-covering of schemes, every open
immersion being a covering morphism of each of the five topologies
(`AlgebraicGeometry.isOpenImmersion_le_coveringMorphismProperty`), so by
`AlgebraicGeometry.exists_isCovering_presieve₀_eq_aux` the family has the same presieve as one of
the site's chosen covering families, which generates a covering sieve.

Representable flatness repeats the argument of
`AlgebraicGeometry.BigFppfOver.representablyFlat_opensToBig` at an arbitrary cardinal cutoff
rather than at that of a chosen big fppf site: the opens of `S` through which an object factors
are closed under intersection and contain `⊤`, and the factorization through each is unique
because an open immersion is a monomorphism.  Neither statement mentions a topology, so this is
the whole difference between the two.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Adequate

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {κ : Cardinal.{u}} (hS : schemeSizeBelow κ S)

/-! ### Representable flatness at an arbitrary cutoff -/

/-- The structure morphism of a size-bounded scheme over `S` factors through the open immersion
of an open `U` of `S` whenever the object has a morphism to `U`. -/
public theorem opensBelow_hom_hom_eq {Z : Over (⟨S, hS⟩ : SchemeBelow κ)} {U : S.Opens}
    (f : Z ⟶ opensBelowObj hS U) : Z.hom.hom = f.left.hom ≫ U.ι :=
  congrArg (fun k : Z.left ⟶ (⟨S, hS⟩ : SchemeBelow κ) => k.hom) (Over.w f).symm

/-- The range of the structure morphism of a size-bounded scheme over `S` lies in an open `U` as
soon as the object has a morphism to `U`. -/
public theorem opensBelow_range_le_of_hom {Z : Over (⟨S, hS⟩ : SchemeBelow κ)} {U : S.Opens}
    (f : Z ⟶ opensBelowObj hS U) : Set.range ⇑Z.hom.hom ⊆ (U : Set S) := by
  rw [← Scheme.Opens.range_ι U]
  rintro x ⟨y, rfl⟩
  exact ⟨f.left.hom y, by rw [opensBelow_hom_hom_eq hS f]; simp⟩

/-- A size-bounded scheme over `S` whose structure morphism has range inside an open `U`
factors through `U`. -/
public noncomputable def opensBelowHomOfRangeLe {Z : Over (⟨S, hS⟩ : SchemeBelow κ)}
    (U : S.Opens) (h : Set.range ⇑Z.hom.hom ⊆ (U : Set S)) : Z ⟶ opensBelowObj hS U :=
  Over.homMk (ObjectProperty.homMk
      (IsOpenImmersion.lift U.ι Z.hom.hom (by rwa [Scheme.Opens.range_ι])))
    (ObjectProperty.hom_ext _ (IsOpenImmersion.lift_fac U.ι Z.hom.hom _))

/-- There is at most one morphism from a size-bounded scheme over `S` to an open of `S`, the
open immersion of that open being a monomorphism. -/
public theorem opensBelow_subsingleton_hom (Z : Over (⟨S, hS⟩ : SchemeBelow κ)) (U : S.Opens) :
    Subsingleton (Z ⟶ opensBelowObj hS U) := by
  refine ⟨fun f g => ?_⟩
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  rw [← cancel_mono U.ι, ← opensBelow_hom_hom_eq hS f, ← opensBelow_hom_hom_eq hS g]

/-- There is at most one morphism from a size-bounded scheme over `S` into the image of an open
of `S`. -/
public instance opensBelowToOver_subsingleton_hom (Z : Over (⟨S, hS⟩ : SchemeBelow κ))
    (U : S.Opens) : Subsingleton (Z ⟶ (opensBelowToOver hS).obj U) :=
  opensBelow_subsingleton_hom hS Z U

/-- **The small Zariski site of `S` is representably flat in the size-bounded schemes over
`S`.**  The opens through which an object factors are closed under intersection and contain `⊤`,
and the factorization through each is unique.  This is
`AlgebraicGeometry.BigFppfOver.representablyFlat_opensToBig` at an arbitrary cardinal cutoff. -/
public instance representablyFlat_opensBelowToOver :
    RepresentablyFlat (opensBelowToOver hS) := by
  refine ⟨fun Z => { cone_objs := ?_, cone_maps := ?_, nonempty := ?_ }⟩
  · intro A C
    have hA := opensBelow_range_le_of_hom hS A.hom
    have hC := opensBelow_range_le_of_hom hS C.hom
    exact ⟨StructuredArrow.mk (Y := A.right ⊓ C.right)
      (opensBelowHomOfRangeLe hS _ (Set.subset_inter hA hC)),
      StructuredArrow.homMk (homOfLE inf_le_left) (Subsingleton.elim _ _),
      StructuredArrow.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _), trivial⟩
  · intro A C f g
    refine ⟨A, 𝟙 _, ?_⟩
    simp only [Category.id_comp]
    exact StructuredArrow.hom_ext f g (Subsingleton.elim _ _)
  · exact ⟨StructuredArrow.mk (Y := ⊤) (opensBelowHomOfRangeLe hS ⊤ (by simp))⟩

/-- **The whole of `S`, read as an open, is a final object of the size-bounded schemes over
`S`**: every object maps to it by its own structure morphism, and in only one way.  This is what
makes cohomology over the image of `⊤` cohomology of `S` itself. -/
public noncomputable def isTerminal_opensBelowToOver_top :
    IsTerminal ((opensBelowToOver hS).obj (⊤ : S.Opens)) :=
  IsTerminal.ofUnique (h := fun Z =>
    ⟨⟨opensBelowHomOfRangeLe hS ⊤ (by simp)⟩, fun _ => Subsingleton.elim _ _⟩)

/-! ### Preservation of fibre products and equalizers -/

/-- The intersection of two opens of `S` is still their fibre product among the size-bounded
schemes over `S`: an object mapping to both has its image inside both opens, hence inside the
intersection, and there is at most one morphism to an open. -/
public noncomputable def isLimitMapOpensBelowInfPullbackCone {U V W : S.Opens} (f : U ⟶ W)
    (g : V ⟶ W) : IsLimit ((opensBelowToOver hS).mapCone (opensInfPullbackCone f g)) := by
  refine (PullbackCone.isLimitMapConeEquiv (opensInfPullbackCone f g)
    (opensBelowToOver hS)).2 ?_
  refine PullbackCone.IsLimit.mk _ (fun s => opensBelowHomOfRangeLe hS (U ⊓ V) ?_)
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)
  have hU := opensBelow_range_le_of_hom hS s.fst
  have hV := opensBelow_range_le_of_hom hS s.snd
  simpa only [Opens.coe_inf] using Set.subset_inter hU hV

/-- **The inclusion of the small Zariski site preserves fibre products**, the fibre product of
two opens being their intersection on both sides. -/
public instance opensBelowToOver_preservesLimitsOfShape_walkingCospan :
    PreservesLimitsOfShape WalkingCospan (opensBelowToOver hS) where
  preservesLimit {K} := by
    have : PreservesLimit
        (cospan (K.map WalkingCospan.Hom.inl) (K.map WalkingCospan.Hom.inr))
        (opensBelowToOver hS) :=
      preservesLimit_of_preserves_limit_cone (isLimitOpensInfPullbackCone _ _)
        (isLimitMapOpensBelowInfPullbackCone hS _ _)
    exact preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm

/-- An open of `S` is still the equalizer of any parallel pair out of it among the size-bounded
schemes over `S`: there is at most one morphism from the apex of a fork to an open. -/
public noncomputable def isLimitMapOpensBelowIdFork {U V : S.Opens} (f g : U ⟶ V) :
    IsLimit ((opensBelowToOver hS).mapCone (opensIdFork f g)) := by
  refine (isLimitMapConeForkEquiv (opensBelowToOver hS)
      (show (𝟙 U) ≫ f = (𝟙 U) ≫ g from Subsingleton.elim _ _)).symm
    (Fork.IsLimit.mk _ (fun s => s.ι) (fun s => ?_) (fun s m _ => ?_))
  all_goals exact @Subsingleton.elim _ (opensBelowToOver_subsingleton_hom hS _ U) _ _

/-- **The inclusion of the small Zariski site preserves equalizers**, the two morphisms of a
parallel pair of opens being equal. -/
public instance opensBelowToOver_preservesLimitsOfShape_walkingParallelPair :
    PreservesLimitsOfShape WalkingParallelPair (opensBelowToOver hS) where
  preservesLimit {K} := by
    have : PreservesLimit
        (parallelPair (K.map WalkingParallelPairHom.left) (K.map WalkingParallelPairHom.right))
        (opensBelowToOver hS) :=
      preservesLimit_of_preserves_limit_cone (isLimitOpensIdFork _ _)
        (isLimitMapOpensBelowIdFork hS _ _)
    exact preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

/-! ### Cover preservation and continuity into a localized big site -/

variable (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
  (hS : S.size < cutoff τ B)

/-- The family of the localized big site cut out by a covering sieve of the small Zariski site
of `S`: the open immersions of the members of the sieve. -/
public noncomputable def opensBelowHypercover {U : S.Opens} (R : Sieve U) :
    PreZeroHypercover.{u + 1} ((opensBelowObj (κ := cutoff τ B) hS U).left) where
  I₀ := ULift.{u + 1} (Σ V : S.Opens, { h : V ⟶ U // R.arrows h })
  X i := (opensBelowObj (κ := cutoff τ B) hS i.down.1).left
  f i := ((opensBelowToOver (κ := cutoff τ B) hS).map i.down.2.1).left

@[simp]
public theorem opensBelowHypercover_f_hom {U : S.Opens} (R : Sieve U)
    (i : (opensBelowHypercover τ B S hS R).I₀) :
    ((opensBelowHypercover τ B S hS R).f i).hom = S.homOfLE (leOfHom i.down.2.1) := rfl

/-- **A covering sieve of the small Zariski site of `S` cuts out a `τ`-covering family of
schemes**: its members are open immersions, hence covering morphisms of each of the five
topologies, and they are jointly surjective. -/
public theorem opensBelowHypercover_mem_precoverage {U : S.Opens} (R : Sieve U)
    (hR : R ∈ Opens.grothendieckTopology ↥S U) :
    ((opensBelowHypercover τ B S hS R).map (schemeBelowInclusion (cutoff τ B))).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ)
        ((schemeBelowInclusion (cutoff τ B)).obj
          (opensBelowObj (κ := cutoff τ B) hS U).left) := by
  rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
    Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun x => ?_, fun i => ?_⟩
  · obtain ⟨V, g, hg, hV⟩ := hR x.1 x.2
    refine ⟨⟨⟨V, g, hg⟩⟩, ⟨⟨x.1, hV⟩, ?_⟩⟩
    change (schemeBelowInclusion (cutoff τ B)).map
      (((opensBelowToOver (κ := cutoff τ B) hS).map g).left) _ = x
    rw [ObjectProperty.ι_map]
    change S.homOfLE (leOfHom g) _ = x
    exact (Scheme.homOfLE_apply' (leOfHom g) x.1 hV).trans (Subtype.ext rfl)
  · exact isOpenImmersion_le_coveringMorphismProperty τ _
      (inferInstanceAs (IsOpenImmersion (S.homOfLE (leOfHom i.down.2.1))))

/-- **The small Zariski site of `S` is cover preserving into a localized big `τ`-site**, for
each of the five `τ`.  An open covering of an open of `S` is a `τ`-covering family of schemes,
hence has the same presieve as one of the site's chosen covering families, which generates a
covering sieve. -/
public theorem coverPreserving_opensBelowToOver :
    CoverPreserving (Opens.grothendieckTopology ↥S) (overTopology τ B S hS)
      (opensBelowToOver (κ := cutoff τ B) hS) := by
  refine ⟨fun {U R} hR => ?_⟩
  rw [mem_overTopology_iff]
  obtain ⟨F, hF, hFeq⟩ := exists_isCovering_presieve₀_eq_aux τ B
    (opensBelowHypercover τ B S hS R) (opensBelowHypercover_mem_precoverage τ B S hS R hR)
  have hgen := generate_mem_siteTopology τ B F hF
  rw [← hFeq] at hgen
  refine (siteTopology τ B).superset_covering ?_ hgen
  refine (Sieve.generate_le_iff _ _).2 ?_
  rintro Y g ⟨i⟩
  refine (Sieve.overEquiv_iff _ _).2 ?_
  refine ⟨i.down.1, i.down.2.1, Over.homMk (𝟙 _) ?_, i.down.2.2, ?_⟩
  · exact (Category.id_comp _).trans
      (ObjectProperty.hom_ext _ (S.homOfLE_ι (leOfHom i.down.2.1)).symm)
  · exact Over.OverMorphism.ext (Category.id_comp _).symm

/-- **The small Zariski site of `S` is continuous in a localized big `τ`-site**, for each of the
five `τ`, so restriction along the inclusion is the direct image of a morphism of sites
`(Sch/S)_τ → S_Zar`.

This is the instance the big-site branch of [Stacks, Tag 03P2] needs, and it is stated against
`AlgebraicGeometry.overTopology` rather than
`AlgebraicGeometry.BigFppfOver.baseOverTopology`; see the implementation notes for why the
latter does not serve. -/
public instance isContinuous_opensBelowToOver :
    (opensBelowToOver (κ := cutoff τ B) hS).IsContinuous (Opens.grothendieckTopology ↥S)
      (overTopology τ B S hS) :=
  CategoryTheory.Functor.isContinuous_iff_coverPreserving.2
    (coverPreserving_opensBelowToOver τ B S hS)

end AlgebraicGeometry

end
