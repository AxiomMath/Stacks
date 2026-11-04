module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Sites.SumFormulaLegs
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormula

/-!
# The adjunction and the composition law of a simplicial transition on abelian sheaves

Let `φ` be a simplex map. The inverse image
`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAb` of abelian sheaves along the
simplicial transition attached to `φ` is left adjoint to a direct image: in case (A) the direct
image along a continuous functor, in case (B) the right Kan extension along a cocontinuous functor
(Stacks 00XL). Both are compatible with composition of simplex maps. In case (A) the summand
inclusions of the sum formula of Stacks 09WG are identified with conjugates of the comparison of
right adjoints.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.transitionDirectImageAb`: the right adjoint of
  `CategoryTheory.SimplicialSiteSituation.transitionInverseImageAb`.
* `CategoryTheory.SimplicialSiteSituation.transitionAdjunctionAb`: the adjunction between them.
* `CategoryTheory.SimplicialSiteSituation.transitionDirectImageAbComp` and
  `.transitionInverseImageAbComp`: the two composition laws.

## Main results

* `CategoryTheory.SimplicialSite.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv`:
  in case (A) the summand inclusions of the sum formula of Stacks 09WG are the conjugates, under
  the adjunctions above, of the comparison of right adjoints.
* `SimplicialSite.homEquiv_sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv`: the
  corresponding transposition formula.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pseudofunctor Opposite

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- Direct image of abelian sheaves along the simplicial transition attached to a simplex map
`φ : [n] ⟶ [m]`: the right adjoint of
`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAb`.

In case (A) the transition is a morphism of sites represented by a continuous functor
`u φ : C_n ⥤ C_m`, and this is the direct image along it. In case (B) the transition is a
cocontinuous functor `u φ : C_m ⥤ C_n` and this is the right Kan extension along it. -/
noncomputable def transitionDirectImageAb {n m : SimplexCategory} (φ : n ⟶ m) :
    Sheaf (S.componentTopology m) Ab.{u} ⥤ Sheaf (S.componentTopology n) Ab.{u} :=
  match S with
  | ⟨Sum.inl C⟩ =>
      haveI : ((C.underlying.map φ).toFunctor).IsContinuous
          (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck :=
        (C.isMorphismOfSites φ).isContinuous
      ((C.underlying.map φ).toFunctor).sheafPushforwardContinuous Ab.{u}
        (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck
  | ⟨Sum.inr C⟩ =>
      haveI : ((C.underlying.map φ.op).toFunctor).IsCocontinuous
          (topologyOfCoverings (C.coverage (op m))) (topologyOfCoverings (C.coverage (op n))) :=
        C.isCocontinuous φ.op
      ((C.underlying.map φ.op).toFunctor).sheafPushforwardCocontinuous Ab.{u}
        (topologyOfCoverings (C.coverage (op m))) (topologyOfCoverings (C.coverage (op n)))

/-- The inverse image of abelian sheaves along a simplicial transition is left adjoint to the
direct image along it.

In case (A) this is the adjunction between the sheaf pullback along a continuous functor and the
direct image along it; in case (B) it is the adjunction of Stacks 00XL between the sheafified
restriction along a cocontinuous functor and the right Kan extension along it. -/
noncomputable def transitionAdjunctionAb {n m : SimplexCategory} (φ : n ⟶ m) :
    transitionInverseImageAb S φ ⊣ transitionDirectImageAb S φ :=
  match S with
  | ⟨Sum.inl C⟩ =>
      haveI : ((C.underlying.map φ).toFunctor).IsContinuous
          (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck :=
        (C.isMorphismOfSites φ).isContinuous
      sheafPullbackConstruction.sheafAdjunctionContinuous
        ((C.underlying.map φ).toFunctor) Ab.{u}
        (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck
  | ⟨Sum.inr C⟩ =>
      haveI : ((C.underlying.map φ.op).toFunctor).IsCocontinuous
          (topologyOfCoverings (C.coverage (op m))) (topologyOfCoverings (C.coverage (op n))) :=
        C.isCocontinuous φ.op
      ((C.underlying.map φ.op).toFunctor).sheafAdjunctionPullbackCocontinuous Ab.{u}
        (topologyOfCoverings (C.coverage (op m))) (topologyOfCoverings (C.coverage (op n)))

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSite

open CategoryTheory.SimplicialSiteSituation in
/-- The composition law for direct images along the simplicial transitions, in case (A). -/
noncomputable def transitionDirectImageAbComp (C : SimplicialSite.{u})
    {n m k : SimplexCategory} (φ : n ⟶ m) (ψ : m ⟶ k) :
    transitionDirectImageAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) ψ ⋙
        transitionDirectImageAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ ≅
      transitionDirectImageAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) (φ ≫ ψ) := by
  haveI := (C.isMorphismOfSites φ).isContinuous
  haveI := (C.isMorphismOfSites ψ).isContinuous
  haveI := (C.isMorphismOfSites (φ ≫ ψ)).isContinuous
  exact Functor.sheafPushforwardContinuousComp'
    (eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_comp φ ψ)).symm)
    Ab.{u} (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck
    (C.coverage k).toGrothendieck

end CategoryTheory.SimplicialSite

namespace CategoryTheory.CocontinuousSimplicialSite

open CategoryTheory.SimplicialSiteSituation in
/-- The composition law for direct images along the simplicial transitions, in case (B). -/
noncomputable def transitionDirectImageAbComp (C : CocontinuousSimplicialSite.{u})
    {n m k : SimplexCategory} (φ : n ⟶ m) (ψ : m ⟶ k) :
    transitionDirectImageAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) ψ ⋙
        transitionDirectImageAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ ≅
      transitionDirectImageAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) (φ ≫ ψ) := by
  letI : ((C.underlying.map ψ.op).toFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage (op k))) (topologyOfCoverings (C.coverage (op m))) :=
    C.isCocontinuous ψ.op
  letI : ((C.underlying.map φ.op).toFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage (op m))) (topologyOfCoverings (C.coverage (op n))) :=
    C.isCocontinuous φ.op
  letI : ((C.underlying.map (φ ≫ ψ).op).toFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage (op k))) (topologyOfCoverings (C.coverage (op n))) :=
    C.isCocontinuous (φ ≫ ψ).op
  refine (Functor.fullyFaithfulCancelRight
    (sheafToPresheaf (topologyOfCoverings (C.coverage (op n))) Ab.{u})
    (Functor.isoWhiskerLeft (sheafToPresheaf (topologyOfCoverings (C.coverage (op k))) Ab.{u})
      ((((C.underlying.map (φ ≫ ψ).op).toFunctor).op.ranAdjunction Ab.{u}).rightAdjointUniq
        (((((C.underlying.map φ.op).toFunctor).op.ranAdjunction Ab.{u}).comp
            (((C.underlying.map ψ.op).toFunctor).op.ranAdjunction Ab.{u})).ofNatIsoLeft
          (eqToIso ?_))))).symm
  exact congrArg (fun F : (↑(C.underlying.obj (op k)))ᵒᵖ ⥤ (↑(C.underlying.obj (op n)))ᵒᵖ =>
      (Functor.whiskeringLeft _ _ Ab.{u}).obj F)
    (congrArg Functor.op
      (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ.op φ.op)).symm)

end CategoryTheory.CocontinuousSimplicialSite

namespace CategoryTheory.SimplicialSiteSituation

/-- The composition law for direct images along the simplicial transitions. -/
noncomputable def transitionDirectImageAbComp (S : SimplicialSiteSituation.{u})
    {n m k : SimplexCategory} (φ : n ⟶ m) (ψ : m ⟶ k) :
    transitionDirectImageAb S ψ ⋙ transitionDirectImageAb S φ ≅
      transitionDirectImageAb S (φ ≫ ψ) := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact SimplicialSite.transitionDirectImageAbComp C φ ψ
  | inr C => exact CocontinuousSimplicialSite.transitionDirectImageAbComp C φ ψ

/-- The composition law for inverse images along the simplicial transitions: the inverse image
along the transition at a composite of simplex maps is the composite of the inverse images.

It is the conjugate of `CategoryTheory.SimplicialSiteSituation.transitionDirectImageAbComp` under
the three transition adjunctions. -/
noncomputable def transitionInverseImageAbComp (S : SimplicialSiteSituation.{u})
    {n m k : SimplexCategory} (φ : n ⟶ m) (ψ : m ⟶ k) :
    transitionInverseImageAb S φ ⋙ transitionInverseImageAb S ψ ≅
      transitionInverseImageAb S (φ ≫ ψ) :=
  Adjunction.leftAdjointCompIso (S.transitionAdjunctionAb φ) (S.transitionAdjunctionAb ψ)
    (S.transitionAdjunctionAb (φ ≫ ψ)) (S.transitionDirectImageAbComp φ ψ)

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSite

/-- The inclusion of a component into the total category has right Kan extensions along its
opposite, for every functor to `Ab`. -/
private theorem hasRightKanExtension_op_ι_totalPseudofunctor (C : SimplicialSite.{u})
    (m : SimplexCategory) (G : (C.underlying.obj m)ᵒᵖ ⥤ Ab.{u}) :
    (CoGrothendieck.ι C.totalPseudofunctor (op m)).op.HasRightKanExtension G :=
  (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension _ G).hasRightKanExtension

open CategoryTheory.SimplicialSiteSituation in
/-- In case (A), the `φ`th summand inclusion into the sum formula of Stacks 09WG, followed by the
inverse of that formula, is the conjugate under the transition adjunctions of the comparison
`CategoryTheory.Functor.ranRestrictSheafComparison` of right adjoints. -/
theorem sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv (C : SimplicialSite.{u})
    (n m : SimplexCategory) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
          transitionInverseImageAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) ψ) φ ≫
        (componentLowerShriekRestrictionIsoCoproduct C n m).inv =
      Adjunction.conjugateInj
        ((sheafPullbackConstruction.sheafAdjunctionContinuous
            (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
            ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
            (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology).comp
          ((componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})
              m).sheafAdjunctionCocontinuous Ab.{u}
            ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
            (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology))
        (fun ψ : n ⟶ m =>
          transitionAdjunctionAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) ψ)
        (Functor.ranRestrictSheafComparison Ab.{u}
          ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
          ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
          (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
          (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m)
          (fun ψ : n ⟶ m => (C.underlying.map ψ).toFunctor)
          (fun ψ => continuousInclusionTransition C ψ)
          (ht := fun ψ => (C.isMorphismOfSites ψ).isContinuous)) φ := by
  have hranRaw := hasRightKanExtension_op_ι_totalPseudofunctor C m
  exact Functor.sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfRan_inv Ab.{u}
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
    (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
    (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m)
    (fun ψ : n ⟶ m => (C.underlying.map ψ).toFunctor)
    (fun ψ => continuousInclusionTransition C ψ)
    (ht := fun ψ => (C.isMorphismOfSites ψ).isContinuous)
    (fun P U => isLimitFanRanComponent C U P) φ

open CategoryTheory.SimplicialSiteSituation in
/-- In case (A), transposing along the adjunction of the `φ`th summand, after precomposing with
the `φ`th summand inclusion of the sum formula of Stacks 09WG, is transposing along the composite
adjunction and then postcomposing with the comparison
`CategoryTheory.Functor.ranRestrictSheafComparison` of right adjoints. -/
theorem homEquiv_sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv
    (C : SimplicialSite.{u}) (n m : SimplexCategory) (φ : n ⟶ m)
    (X : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
    (T : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) Ab.{u})
    (f : (sheafPullbackConstruction.sheafPullback
            (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
            ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
            (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology ⋙
          (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})
              m).sheafPushforwardContinuous Ab.{u}
            ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
            (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology).obj X ⟶ T) :
    (transitionAdjunctionAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).homEquiv X T
        ((Sigma.ι (fun ψ : n ⟶ m =>
            transitionInverseImageAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) ψ) φ ≫
          (componentLowerShriekRestrictionIsoCoproduct C n m).inv).app X ≫ f) =
      ((sheafPullbackConstruction.sheafAdjunctionContinuous
            (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
            ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
            (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology).comp
          ((componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})
              m).sheafAdjunctionCocontinuous Ab.{u}
            ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
            (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology)).homEquiv X T f ≫
        (Functor.ranRestrictSheafComparison Ab.{u}
          ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
          ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
          (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
          (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m)
          (fun ψ : n ⟶ m => (C.underlying.map ψ).toFunctor)
          (fun ψ => continuousInclusionTransition C ψ)
          (ht := fun ψ => (C.isMorphismOfSites ψ).isContinuous) φ).app T := by
  have hranRaw := hasRightKanExtension_op_ι_totalPseudofunctor C m
  exact Functor.homEquiv_sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfRan_inv Ab.{u}
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
    (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
    (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m)
    (fun ψ : n ⟶ m => (C.underlying.map ψ).toFunctor)
    (fun ψ => continuousInclusionTransition C ψ)
    (ht := fun ψ => (C.isMorphismOfSites ψ).isContinuous)
    (fun P U => isLimitFanRanComponent C U P) φ X T f

end CategoryTheory.SimplicialSite

end
