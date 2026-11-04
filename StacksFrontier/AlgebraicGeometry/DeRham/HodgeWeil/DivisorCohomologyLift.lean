module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorRestrictionKernel
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Pullback
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Blowup
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# Lifting a Hodge class restricting to zero on a closed subscheme

Let `f : X ⟶ S` be a morphism of schemes and `i : Y ⟶ X` the inclusion of the closed subscheme
cut out by `I`. If the Hodge pullback `i^* a ∈ H^q(Y, Ω^p_{Y/S})` of a class
`a ∈ H^q(X, Ω^p_{X/S})` vanishes, then `a` lifts to the cohomology `H^q(X, 𝒦^p)` of the sheaf
`𝒦^p` of forms vanishing on `Y`.

The Hodge pullback along `i` is `H^q` of the canonical map `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`, followed by
`H^q(X, i_* -) ⟶ H^q(X, Ri_* -)` and the Leray identification. Since `i` is a closed immersion,
`i_*` is exact, so the comparison `i_* ⟶ Ri_*` is invertible
(`Stacks.HodgeWeil.isIso_pushforwardComparisonQ_of_preservesFiniteColimits`), and the vanishing
of `i^* a` says that `a` dies in `H^q(X, i_*Ω^p_{Y/S})`. The long exact cohomology sequence of
`0 ⟶ 𝒦^p ⟶ Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S} ⟶ 0`
(`Stacks.HodgeWeil.kernelFormsShortComplex_shortExact`) then lifts `a`.

## Main results

* `Stacks.HodgeWeil.exists_cohomologyMap_single_eq_of_shortExact`: exactness in the middle of the
  long exact sequence of derived global sections, for a short exact sequence of sheaves of
  modules placed in degree `0`.
* `Stacks.HodgeWeil.exists_kernelForms_lift_of_hodgePullback_eq_zero`: **the lift**.

## References

* [Stacks Project, Section 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.GlobalKunneth (baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule cohomologyMap)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

section LongExact

variable {Z : RingedSpace.{u, u}}

/-- **Exactness in the middle of the long exact sequence of derived global sections**: for a
short exact sequence `0 ⟶ F ⟶ G ⟶ H ⟶ 0` of sheaves of modules, a class of `H^q(Z, G)` killed
by `H^q(Z, G ⟶ H)` comes from `H^q(Z, F)`. -/
theorem exists_cohomologyMap_single_eq_of_shortExact
    {T : ShortComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.SheafedSpace.sheaf Z)))}
    (hT : T.ShortExact) (q : ℤ)
    (x : cohomologyModule (S := Z)
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj T.X₂)) q)
    (hx : (cohomologyMap (S := Z) ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map T.g)
      q).hom x = 0) :
    ∃ y, (cohomologyMap (S := Z) ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map T.f)
      q).hom y = x := by
  have hT' := hT.map_of_exact (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
  have hd := DerivedCategory.triangleOfSES_distinguished hT'
  let := Functor.IsRightDerivedFunctor.commShift (baseSections Z)
    ((Stacks.Cohomology.DerivedSectionsLeray.homotopySectionsOverOpen Z ⊤).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
  have : (baseSections Z).IsTriangulated :=
    Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
      (fun K => Stacks.Injectives.exists_kInjective_resolution_of_grothendieck.{u} K)
      (Stacks.Cohomology.DerivedSectionsLeray.homotopySectionsOverOpen Z ⊤) (baseSections Z)
      ((Stacks.Cohomology.DerivedSectionsLeray.homotopySectionsOverOpen Z ⊤).totalRightDerivedUnit
        DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
  have hex := (DerivedCategory.homologyFunctor _ q).map_distinguished_exact _
    ((baseSections Z).map_distinguished _ hd)
  exact (ShortComplex.moduleCat_exact_iff _).1 hex x hx

end LongExact


section Lift

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso)

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

/-- The direct image of sheaves of modules along the closed immersion `i : Y ⟶ X` preserves
finite colimits. -/
instance preservesFiniteColimits_modulePushforward_subschemeι :
    PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.DeRhamBaseChange.inverseImageBaseMap I.subschemeι (I.subschemeι ≫ f) f (𝟙 S)
        (subschemeι_square f I))) :=
  Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward _
    I.subschemeι.isClosedEmbedding

/-- The degree-`0` comparison from the termwise direct image of `Ω^p_{Y/S}[0]` to
`(i_*Ω^p_{Y/S})[0]`, through which `formsSinglePushforward` factors `formsRestrictionBase` placed
in degree `0`. -/
def pushforwardSingleToSingle (p : ℕ) :
    (pushforwardComplex (Stacks.DeRhamBaseChange.inverseImageBaseMap I.subschemeι
        (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I))).obj
        (formsSingle (I.subschemeι ≫ f) p) ⟶
      (HomologicalComplex.single (_root_.SheafOfModules.{u}
          (structureSheafRing (Stacks.DeRhamDirectImage.inverseImageBase f)))
          (ComplexShape.up ℤ) 0).obj
        ((StacksDraft.KFlat.modulePushforward (Stacks.DeRhamBaseChange.inverseImageBaseMap
          I.subschemeι (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I))).obj
          ((Scheme.Hom.deRhamComplex (I.subschemeι ≫ f)).X p)) :=
  HomologicalComplex.mkHomToSingle
    ((StacksDraft.KFlat.modulePushforward (Stacks.DeRhamBaseChange.inverseImageBaseMap
      I.subschemeι (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I))).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((Scheme.Hom.deRhamComplex (I.subschemeι ≫ f)).X p)).hom)
    (fun k _ => by
      have hd : ((pushforwardComplex (Stacks.DeRhamBaseChange.inverseImageBaseMap I.subschemeι
          (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I))).obj
          (formsSingle (I.subschemeι ≫ f) p)).d k 0 = 0 :=
        (congrArg (StacksDraft.KFlat.modulePushforward (Stacks.DeRhamBaseChange.inverseImageBaseMap
          I.subschemeι (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I))).map
          (HomologicalComplex.single_obj_d _ _ _ _ _)).trans (Functor.map_zero _ _ _)
      rw [hd, Limits.zero_comp])

/-- `formsSinglePushforward` followed by `pushforwardSingleToSingle` is `formsRestriction`
placed in degree `0`. -/
theorem formsSinglePushforward_comp_pushforwardSingleToSingle (p : ℕ) :
    formsSinglePushforward I.subschemeι (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I) p ≫
        pushforwardSingleToSingle f I p =
      (HomologicalComplex.single (_root_.SheafOfModules.{u}
          (structureSheafRing (Stacks.DeRhamDirectImage.inverseImageBase f))) (ComplexShape.up ℤ)
          0).map (formsRestrictionBase f I p) := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f]
  refine Eq.trans ?_ (HomologicalComplex.single_map_f_self _ _ _).symm
  unfold formsSinglePushforward pushforwardSingleToSingle
  rw [HomologicalComplex.mkHomToSingle_f]
  refine Eq.trans (congrArg (· ≫ _) (HomologicalComplex.mkHomFromSingle_f _ _)) ?_
  ext U x
  rfl

/-- The underlying map of an isomorphism of modules is injective. -/
theorem injective_hom_of_iso {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (e : M ≅ N) :
    Function.Injective e.hom.hom := fun x y hxy =>
  (ConcreteCategory.congr_hom e.hom_inv_id x).symm.trans
    ((congrArg e.inv.hom hxy).trans (ConcreteCategory.congr_hom e.hom_inv_id y))

/-- **A pullback along a morphism of ringed spaces with exact direct image vanishes only if
the class dies in the cohomology of the direct image**: the comparison `h_* ⟶ Rh_*` and the
Leray identification are invertible. -/
theorem cohomologyMap_eq_zero_of_cohomologyPullback_eq_zero {Z Z' : RingedSpace.{u, u}}
    (h : Z' ⟶ Z) [PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePushforward h)]
    {K : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') (n : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) n)
    (hx : (cohomologyPullback h φ n).hom x = 0) :
    (cohomologyMap (S := Z) φ n).hom x = 0 := by
  have := isIso_pushforwardComparisonQ_of_preservesFiniteColimits h K'
  rw [cohomologyPullback_apply] at hx
  have hL := injective_hom_of_iso (lerayCohomologyIso h (DerivedCategory.Q.obj K') n)
  have h2 := hL (hx.trans (map_zero _).symm)
  rw [Functor.map_comp, Functor.map_comp, ModuleCat.comp_apply] at h2
  have hC := injective_hom_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
    ((baseSections Z).mapIso (asIso (pushforwardComparisonQ h K'))))
  exact hC (h2.trans (map_zero _).symm)

/-- **A Hodge class restricting to zero on `Y` lifts to the forms vanishing on `Y`**: if
`i^* a = 0` in `H^q(Y, Ω^p_{Y/S})`, then `a` is the image of a class of `H^q(X, 𝒦^p)`. -/
theorem exists_kernelForms_lift_of_hodgePullback_eq_zero (p : ℕ) (q : ℤ)
    (a : AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent
      (Scheme.Hom.deRhamAlgebras f) p q)
    (ha : hodgePullback I.subschemeι (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I) p q a = 0) :
    ∃ a' : cohomologyModule (S := Stacks.DeRhamDirectImage.inverseImageBase f)
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (kernelFormsSheaf f I p))) q,
      (cohomologyMap (S := Stacks.DeRhamDirectImage.inverseImageBase f)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (kernelFormsInclusion f I p))
          q).hom a' = a := by
  have h3 := cohomologyMap_eq_zero_of_cohomologyPullback_eq_zero
    (Stacks.DeRhamBaseChange.inverseImageBaseMap I.subschemeι (I.subschemeι ≫ f) f (𝟙 S)
      (subschemeι_square f I))
    (formsSinglePushforward I.subschemeι (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I) p)
    q a ha
  have h4 := (congrArg (fun ψ => (cohomologyMap (S := Stacks.DeRhamDirectImage.inverseImageBase f)
      ψ q).hom a) (formsSinglePushforward_comp_pushforwardSingleToSingle f I p)).symm.trans
    ((Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_comp_apply
      (S := Stacks.DeRhamDirectImage.inverseImageBase f) _ _ q a).symm.trans
      ((congrArg _ h3).trans (map_zero _)))
  exact exists_cohomologyMap_single_eq_of_shortExact (kernelFormsShortComplex_shortExact f I p) q
    a h4

end Lift

end Stacks.HodgeWeil

end
