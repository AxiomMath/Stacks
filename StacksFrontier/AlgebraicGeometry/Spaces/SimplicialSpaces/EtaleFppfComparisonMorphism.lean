module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleFppfComparison

/-!
# The comparison morphism `h : Sh((Spaces/U)_{fppf,total}) → Sh(U_étale)` of Stacks 0DH5

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`. The upper
horizontal arrow of the diagram of Stacks 0DH5 is the morphism of topoi `h` given by the functor
`u : U_étale ⥤ (Spaces/U)_{fppf,total}`, `(n, V) ↦ V/U_n`, from the small étale site of Section
0DE7 to the fppf total site of Section 09X8. This file shows that `u` is continuous and defines a
morphism of sites, and that its square of component inclusions is Guitart exact, which is the
combinatorial content of Stacks 0D96 for `h`: the inverse image along `h` is computed in each
simplicial degree `n` by the comparison `a_{U_n}` of Section 0DGE.

## Main definitions

* `AlgebraicGeometry.Space.fppfTotalSituation`: the fppf total site of `U`.
* `AlgebraicGeometry.Space.etaleToFppfDegree`: the comparison functor `V ↦ V/U_n` in simplicial
  degree `n`.
* `AlgebraicGeometry.Space.etaleToFppfTotal`: the comparison functor `u`.
* `AlgebraicGeometry.Space.etaleToFppfSquare`: its square of component inclusions.
* `AlgebraicGeometry.Space.etaleFppfComparisonMorphism`: the morphism of topoi `h`.

## Main results

* `AlgebraicGeometry.Space.guitartExact_etaleToFppfSquare`: the square of component inclusions is
  Guitart exact.
* `AlgebraicGeometry.Space.etaleToFppfDegree_isMorphismOfSites`: in each degree the comparison is
  a morphism of sites.
* `AlgebraicGeometry.Space.etaleToFppfTotal_isContinuous` and
  `AlgebraicGeometry.Space.etaleToFppfTotal_isMorphismOfSites`: `u` is continuous and is a
  morphism of sites.
* `CategoryTheory.SimplicialSiteSituation.preservesFiniteLimits_of_restrict_inr`: a functor into
  sheaves of sets on a total site of case (B) is left exact when its restrictions to all
  simplicial degrees are.

## References

* [Stacks Project, Tag 0DH5](https://stacks.math.columbia.edu/tag/0DH5)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor (CoGrothendieck)
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- **The systems presentation of sheaves on a total site, case (B), in the form needed here.** A
functor into sheaves of sets on the total site of a cocontinuous simplicial site preserves
finite limits as soon as its composite with restriction to every simplicial degree does: limits
of sheaves are computed sectionwise, and every object of the total category lies in the component
of its simplicial degree. -/
theorem preservesFiniteLimits_of_restrict_inr {E : Type*} [Category* E]
    (D : CocontinuousSimplicialSite.{u})
    (L : E ⥤ Sheaf (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u))
    (hL : ∀ n, PreservesFiniteLimits
      (L ⋙ restrict (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}) n)) :
    PreservesFiniteLimits L := by
  have : PreservesFiniteLimits (L ⋙ sheafToPresheaf
      (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u)) := by
    apply preservesFiniteLimits_of_evaluation
    intro Z
    have := hL Z.unop.base.unop
    exact comp_preservesFiniteLimits (L ⋙ restrict _ Z.unop.base.unop)
      (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op Z.unop.fiber))
  exact preservesFiniteLimits_of_reflects_of_preserves L
    (sheafToPresheaf (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u))

end CategoryTheory.SimplicialSiteSituation

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

open EtaleComponent

/-! ### Passing to the total site of the simplicial semi-representable object -/

/-- The simplicial semi-representable object `n ↦ {U_n → X}` of the fppf site attached to an
augmented simplicial algebraic space. -/
abbrev fppfHypercover :=
  associatedSimplicialObject.{u + 1} A.left A.hom

/-- The fppf total site `(Spaces/U)_{fppf,total}` of Section 09X8: the simplicial-site situation
of the simplicial semi-representable object `n ↦ {U_n → X}` of the fppf site of `X`. -/
abbrev fppfTotalSituation : SimplicialSiteSituation.{u + 1} :=
  CategoryTheory.SimplicialSemiRepresentable.situation
    ((fppfPretopology B S hS).toGrothendieck.over A.right) (fppfHypercover A)

/-- The comparison functor in simplicial degree `n`: `V ↦ V/U_n`, read in the component
`(Spaces/X)/(U_n/X)` of the fppf total site. -/
abbrev etaleToFppfDegree (n : SimplexCategory) :
    (etaleSimplicialSite A).situation.component n ⥤ (fppfTotalSituation A).component n :=
  etaleToSlice A n ⋙ SimplicialOver.toComponentOver A.left A.hom (op n)

/-- **The comparison functor `u : U_étale ⥤ (Spaces/U)_{fppf,total}`**, `(n, V) ↦ V/U_n`, into the
fppf total site of Section 09X8. -/
abbrev etaleToFppfTotal :
    (etaleSimplicialSite A).situation.totalCategory ⥤ (fppfTotalSituation A).totalCategory :=
  etaleToSlicesTotal A ⋙ SimplicialOver.toAssociatedTotal A.left A.hom

/-- The comparison of the two presentations of the total site commutes with the inclusions of a
simplicial degree. -/
abbrev slicesToAssociatedSquare (n : SimplexCategory) :=
  TwoSquare.mk _ _ _ _ (Grothendieck.ιCompMap (SimplicialOver.toSlices A.left A.hom) (op n)).inv

/-- The square comparing the two presentations of the total site with the inclusions of simplicial
degree `n` is Guitart exact. -/
instance guitartExact_slicesToAssociatedSquare (n : SimplexCategory) :
    (slicesToAssociatedSquare A n).GuitartExact :=
  haveI : ((SimplicialOver.toSlices A.left A.hom).app (op n)).toFunctor.IsEquivalence :=
    inferInstanceAs
      (SimplicialOver.componentOverEquivalence A.left A.hom (op n)).inverse.IsEquivalence
  haveI : (Grothendieck.map (SimplicialOver.toSlices A.left A.hom)).IsEquivalence :=
    Functor.isEquivalence_of_iso (SimplicialOver.associatedTotalEquivalenceInverseIso A.left A.hom)
  haveI : IsIso (slicesToAssociatedSquare A n) :=
    inferInstanceAs
      (IsIso (Grothendieck.ιCompMap (SimplicialOver.toSlices A.left A.hom) (op n)).inv)
  TwoSquare.guitartExact_of_isEquivalence_of_isIso' _

/-- The square of component inclusions of the comparison functor `u`. -/
abbrev etaleToFppfSquare (n : SimplexCategory) :
    TwoSquare (etaleToFppfDegree A n)
      (SimplicialSiteSituation.componentFunctor (etaleSimplicialSite A).situation n)
      (SimplicialSiteSituation.componentFunctor (fppfTotalSituation A) n)
      (etaleToFppfTotal A) :=
  (etaleToSlicesSquare A n).hComp (slicesToAssociatedSquare A n)

/-- **Stacks 0D96 for the comparison functor, the combinatorial input**: the square of component
inclusions of `u` is Guitart exact. -/
instance guitartExact_etaleToFppfSquare (n : SimplexCategory) :
    (etaleToFppfSquare A n).GuitartExact :=
  @TwoSquare.GuitartExact.hComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (etaleToSlicesSquare A n) _ _ _
    (slicesToAssociatedSquare A n) (guitartExact_etaleToSlicesSquare A n)
    (guitartExact_slicesToAssociatedSquare A n)

/-- The natural transformation of the square of component inclusions of `u` is an isomorphism. -/
instance isIso_etaleToFppfSquare (n : SimplexCategory) :
    IsIso (etaleToFppfSquare A n) := by
  have h₁ : IsIso (slicesToAssociatedSquare A n) :=
    inferInstanceAs
      (IsIso (Grothendieck.ιCompMap (SimplicialOver.toSlices A.left A.hom) (op n)).inv)
  have key : ∀ x, IsIso (((etaleToSlicesSquare A n).hComp (slicesToAssociatedSquare A n)).app x) :=
    fun x ↦ by
      have e := TwoSquare.hComp_app (etaleToSlicesSquare A n) (slicesToAssociatedSquare A n) x
      have a₁ : IsIso ((slicesToAssociatedSquare A n).app ((etaleToSlice A n).obj x)) :=
        @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ h₁ _
      have a₂ : IsIso ((etaleToSlicesSquare A n).app x) :=
        NatIso.isIso_app_of_isIso _ _
      have a₃ : IsIso ((Grothendieck.map (SimplicialOver.toSlices A.left A.hom)).map
          ((etaleToSlicesSquare A n).app x)) := Functor.map_isIso _ _
      have : IsIso ((slicesToAssociatedSquare A n).app ((etaleToSlice A n).obj x) ≫
          (Grothendieck.map (SimplicialOver.toSlices A.left A.hom)).map
            ((etaleToSlicesSquare A n).app x)) := IsIso.comp_isIso
      exact (congrArg (fun f ↦ IsIso f) e).mpr this
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ key

/-! ### The comparison in one simplicial degree is a morphism of sites -/

/-- The functor `V ↦ V/U_n` from the component of degree `n` of `U_étale` to the fppf site of
`U_n` is a morphism of sites: it is the equivalence of the component with `U_{n, spaces, étale}`
followed by the morphism of sites `a_{U_n}` of Section 0DGE. -/
theorem etaleToSlice_isMorphismOfSites (n : SimplexCategory) :
    (etaleToSlice A n).IsMorphismOfSites (EtaleComponent.precoverage (A := A) n).toGrothendieck
      ((fppfPretopology B S hS).toGrothendieck.over (A.left.obj (op n))) := by
  have hR : (realizeFunctor (A := A) n).IsMorphismOfSites
      (EtaleComponent.precoverage (A := A) n).toGrothendieck
      (SpacesEtale.topology B S hS (A.left.obj (op n))) :=
    Functor.isMorphismOfSites_of_isTerminal _ _ _ (isTerminalFinal n)
      ((isTerminalFinal n).isTerminalObj (realizeFunctor n) _)
  have hI : (SpacesEtale.inclusion B S hS (A.left.obj (op n))).IsMorphismOfSites
      (SpacesEtale.topology B S hS (A.left.obj (op n)))
      ((fppfPretopology B S hS).toGrothendieck.over (A.left.obj (op n))) := by
    rw [fppfPretopology_toGrothendieck]
    exact spacesEtaleInclusion_isMorphismOfSites_fppf _
  exact hR.comp hI

/-- The identification of the fppf site of `U_n` with the component of degree `n` of the fppf
total site is a morphism of sites. -/
theorem toComponentOver_isMorphismOfSites (n : SimplexCategory) :
    (SimplicialOver.toComponentOver A.left A.hom (op n)).IsMorphismOfSites
      ((fppfPretopology B S hS).toGrothendieck.over (A.left.obj (op n)))
      (SemiRepresentable.componentwiseTopology
        ((fppfPretopology B S hS).toGrothendieck.over A.right)
        ((fppfHypercover A).obj (op n))) :=
  have : (SimplicialOver.toComponentOver A.left A.hom (op n)).IsEquivalence :=
    inferInstanceAs
      (SimplicialOver.componentOverEquivalence A.left A.hom (op n)).inverse.IsEquivalence
  have : (SimplicialOver.toComponentOver A.left A.hom (op n)).IsContinuous
      ((fppfPretopology B S hS).toGrothendieck.over (A.left.obj (op n)))
      (SemiRepresentable.componentwiseTopology
        ((fppfPretopology B S hS).toGrothendieck.over A.right)
        ((fppfHypercover A).obj (op n))) :=
    inferInstanceAs
      ((SimplicialOver.componentOverEquivalence A.left A.hom (op n)).inverse.IsContinuous _ _)
  Functor.isMorphismOfSites_of_isTerminal _ _ _ Over.mkIdTerminal
    (Over.mkIdTerminal.isTerminalObj _ _)

/-- **The comparison in simplicial degree `n` is a morphism of sites**: `V ↦ V/U_n` from the
component of degree `n` of `U_étale` to the component of degree `n` of the fppf total site. -/
theorem etaleToFppfDegree_isMorphismOfSites (n : SimplexCategory) :
    (etaleToFppfDegree A n).IsMorphismOfSites
      ((etaleSimplicialSite A).situation.componentTopology n)
      ((fppfTotalSituation A).componentTopology n) := by
  rw [SimplicialSemiRepresentable.componentTopology_eq]
  exact (etaleToSlice_isMorphismOfSites A n).comp (toComponentOver_isMorphismOfSites A n)

/-- The comparison functor `V ↦ V/U_n` in simplicial degree `n` is continuous. -/
instance etaleToFppfDegree_isContinuous (n : SimplexCategory) :
    (etaleToFppfDegree A n).IsContinuous ((etaleSimplicialSite A).situation.componentTopology n)
      ((fppfTotalSituation A).componentTopology n) :=
  (etaleToFppfDegree_isMorphismOfSites A n).isContinuous

/-! ### Continuity of the comparison functor -/

/-- The inclusion of the component of degree `n` into `(Spaces/U)_total` is continuous. -/
theorem slices_ι_isContinuous (n : SimplexCategory) :
    (Grothendieck.ι (SimplicialOver.slices A.left) (op n)).IsContinuous
      ((fppfPretopology B S hS).toGrothendieck.over (A.left.obj (op n)))
      (SimplicialOver.totalTopology (fppfPretopology B S hS).toGrothendieck A.left) := by
  have h := SimplicialSiteSituation.componentFunctor_isContinuous
    (SimplicialOver.situation (fppfPretopology B S hS).toGrothendieck A.left) n
  rw [SimplicialOver.componentTopology_eq] at h
  exact h

/-- **The functor `U_étale ⥤ (Spaces/U)_total` is continuous.** A covering family of `U_étale`
lies in one simplicial degree, where its pairwise fibre products are computed and preserved by
the inclusion of that degree; there the functor is `V ↦ V/U_n`, which is continuous. -/
instance etaleToSlicesTotal_isContinuous :
    (etaleToSlicesTotal A).IsContinuous (etaleSimplicialSite A).totalTopology
      (SimplicialOver.totalTopology (fppfPretopology B S hS).toGrothendieck A.left) where
  op_comp_isSheaf_of_types G := by
    have : (etaleSimplicialSite A).totalCoverage.HasPullbacks :=
      (etaleSimplicialSite A).totalCoverage_hasPullbacks
    have : (etaleSimplicialSite A).totalCoverage.IsStableUnderBaseChange :=
      (etaleSimplicialSite A).totalCoverage_isStableUnderBaseChange
    change Presieve.IsSheaf (etaleSimplicialSite A).totalCoverage.toGrothendieck _
    rw [← Precoverage.toGrothendieck_toCoverage, Presieve.isSheaf_coverage]
    rintro X R ⟨T, hT, rfl⟩
    obtain ⟨b, x⟩ := X
    have : ((etaleSimplicialSite A).coverage b.unop).HasPullbacks :=
      (etaleSimplicialSite A).coverage_hasPullbacks _
    have : T.HasPairwisePullbacks :=
      ((etaleSimplicialSite A).coverage b.unop).hasPairwisePullbacks_of_mem hT
    have : (CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor
        b).PreservesPairwisePullbacks T :=
      ((etaleSimplicialSite A).coverage_pullbacksPreservedBy_ι
        b.unop).preservesPairwisePullbacks_of_mem hT
    refine (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks _ _ T).mp ?_
    have hc := @Functor.isContinuous_comp _ _ _ _ _ _ (etaleToSlice A b.unop)
      (Grothendieck.ι (SimplicialOver.slices A.left) (op b.unop)) _ _ _
      (etaleToSlice_isMorphismOfSites A b.unop).isContinuous (slices_ι_isContinuous A b.unop)
    have hsh := hc.op_comp_isSheaf_of_types G
    have e : (CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b).op ⋙
        (etaleToSlicesTotal A).op ⋙ G.obj =
        (etaleToSlice A b.unop ⋙
          Grothendieck.ι (SimplicialOver.slices A.left) (op b.unop)).op ⋙ G.obj := by
      rw [etaleToSlice_comp_ι]
      rfl
    rw [e]
    exact hsh.isSheafFor _ (Precoverage.generate_mem_toGrothendieck hT)

/-- The comparison `(Spaces/U)_total ⥤ (Spaces/U)_{fppf,total}` of the two presentations of the
fppf total site is continuous. -/
instance toAssociatedTotal_isContinuous :
    (SimplicialOver.toAssociatedTotal A.left A.hom).IsContinuous
      (SimplicialOver.totalTopology (fppfPretopology B S hS).toGrothendieck A.left)
      (SimplicialOver.associatedTotalTopology A.left A.hom
        (fppfPretopology B S hS).toGrothendieck) :=
  haveI := SimplicialOver.associatedTotalEquivalence_inverse_isDenseSubsite A.left A.hom
    (fppfPretopology B S hS).toGrothendieck
  Functor.isContinuous_of_iso (SimplicialOver.associatedTotalEquivalenceInverseIso A.left A.hom) _ _

/-- **The comparison functor `u : U_étale ⥤ (Spaces/U)_{fppf,total}` is continuous.** -/
instance etaleToFppfTotal_isContinuous :
    (etaleToFppfTotal A).IsContinuous (etaleSimplicialSite A).situation.totalTopology
      (fppfTotalSituation A).totalTopology :=
  @Functor.isContinuous_comp _ _ _ _ _ _ (etaleToSlicesTotal A)
    (SimplicialOver.toAssociatedTotal A.left A.hom) _
    (SimplicialOver.totalTopology (fppfPretopology B S hS).toGrothendieck A.left) _
    (etaleToSlicesTotal_isContinuous A) (toAssociatedTotal_isContinuous A)

/-! ### The morphism of topoi `h` -/

/-- **Stacks 0D96 for `u`, on sheaves of sets**: restricting the inverse image along `u` to
simplicial degree `n` is the inverse image along the comparison of degree `n` of the restriction
to degree `n`. -/
def etaleToFppfBeckChevalleyIsoTypes (n : SimplexCategory) :=
  TwoSquare.sheafBeckChevalleyIso (etaleToFppfSquare A n)
    ((etaleToFppfTotal A).sheafAdjunctionContinuous (Type (u + 1))
      (etaleSimplicialSite A).situation.totalTopology (fppfTotalSituation A).totalTopology)
    ((etaleToFppfDegree A n).sheafAdjunctionContinuous (Type (u + 1))
      ((etaleSimplicialSite A).situation.componentTopology n)
      ((fppfTotalSituation A).componentTopology n))

/-- **The comparison functor `u` defines a morphism of sites** `(Spaces/U)_{fppf,total} → U_étale`:
the inverse image along `u` is left exact, because restricted to each simplicial degree it is the
inverse image along the morphism of sites `V ↦ V/U_n` (Stacks 0D96). -/
theorem etaleToFppfTotal_isMorphismOfSites :
    (etaleToFppfTotal A).IsMorphismOfSites (etaleSimplicialSite A).situation.totalTopology
      (fppfTotalSituation A).totalTopology := by
  rw [Functor.isMorphismOfSites_iff_preservesFiniteLimits]
  refine SimplicialSiteSituation.preservesFiniteLimits_of_restrict_inr
    (SimplicialSemiRepresentable.simplicialSite
      ((fppfPretopology B S hS).toGrothendieck.over A.right)
      (fppfHypercover A)) _ fun n ↦ ?_
  have h₁ := SimplicialSiteSituation.restrict_preservesFiniteLimits
    (etaleSimplicialSite A).situation n
  have h₂ := (etaleToFppfDegree_isMorphismOfSites A n).preservesFiniteLimits
  have h₃ := @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂
  exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _ (etaleToFppfBeckChevalleyIsoTypes A n) h₃

/-- **The comparison morphism `h : Sh((Spaces/U)_{fppf,total}) → Sh(U_étale)`** of Stacks 0DH5, the
morphism of topoi of the morphism of sites given by `u : (n, V) ↦ V/U_n`. -/
def etaleFppfComparisonMorphism :
    MorphismOfTopoi (Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1)))
      (Sheaf (etaleSimplicialSite A).situation.totalTopology (Type (u + 1))) :=
  (etaleToFppfTotal_isMorphismOfSites A).morphismOfTopoi

end AlgebraicGeometry.Space
