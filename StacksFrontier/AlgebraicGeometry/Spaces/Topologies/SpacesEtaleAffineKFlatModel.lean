module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineGlobalPointDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesAffineDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSpaceSiteOfBigEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedAmplitudeOfDerivedLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedPushforwardCompExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceUniformBoundUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackAlongRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackCyclesInput
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.KFlatComplexesDefinition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescent
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# K-flat quasi-coherent models on the spaces-étale site of an affine algebraic space

Let `Y` be an algebraic space over a scheme `S` which is the algebraic space of an affine scheme,
and let `K` be an object of the derived category of `𝒪_Y`-modules on the spaces-étale site of
`Y`, at the universe `u + 1` of that site, all of whose cohomology sheaves are quasi-coherent.
Then `K` is represented by a K-flat complex of flat quasi-coherent `𝒪_Y`-modules. Here
`p : (Y_{spaces,étale}, 𝒪_Y) ⟶ (pt, Γ(Y, 𝒪_Y))` is the morphism to the ringed point of global
sections, `AlgebraicGeometry.BigFppfSpaceSite.affinePointHom`.

## Main results

* `AlgebraicGeometry.Space.isDerivedLimit_truncGETower_of_isQuasicoherentOnSite`: an object of
  `D(𝒪_Y)` on the spaces-étale site with quasi-coherent cohomology is the derived limit of its
  truncations from below.
* `AlgebraicGeometry.BigFppfSpaceSite.isLE_affinePointHom_derivedPushforward_obj`: `Rp_*` keeps
  `D^{≤ c}` on objects with quasi-coherent cohomology.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_affinePointDerivedAdjunction_counit_app`: the counit
  `Lp^* Rp_* K ⟶ K` is invertible for `K` with quasi-coherent cohomology.
* `AlgebraicGeometry.Space.exists_kFlat_isQuasicoherentOnSite_model_spacesEtale`: an object of
  `D(𝒪_Y)` with quasi-coherent cohomology is represented by a K-flat complex of flat
  quasi-coherent `𝒪_Y`-modules.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

attribute [local instance] HasDerivedCategory.standard


attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

attribute [local instance] AlgebraicGeometry.Space.enoughInjectives_spacesEtaleModules

/- The sheafification instance of `AddCommGrpCat.{u}`-valued presheaves on the spaces-étale site
is removed: every module category here is at the universe `u + 1` of the site, and instance
search would select that instance for `AddCommGrpCat.{u + 1}`, producing an ill-typed
term. -/
attribute [-instance] AlgebraicGeometry.Space.hasSheafify_spacesEtale_addCommGrp

/-! ### K-flat models out of an invertible counit -/

namespace Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe w

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X Y : AlgebraicGeometry.RingedTopos.{w, w, w}}
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)
  [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

include hmos in
/-- **A K-flat model out of an invertible counit.** Let `f` be a morphism of ringed topoi with
exact pullback, `Q` a property of `O_X`-modules satisfied by every pullback, and `K` an object of
`D(O_X)` at which the counit `Lf^* Rf_* K ⟶ K` is invertible. Then `K` is represented by a K-flat
complex of flat `O_X`-modules all of whose terms satisfy `Q`. -/
theorem exists_kFlat_model_of_isIso_counit
    (Q : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hQ : ∀ N, Q (f.pullbackTopos.obj N))
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app K)) :
    ∃ C : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      (∀ n, Q (C.X n)) ∧
      (letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{w, w, w, w, w} X.O;
        @CochainComplex.KFlatBifunctor.KFlat
          (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          (Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, w, w, w} X.O)
          (Stacks.SheafOfModules.Tensor.sheafTensor_additive.{w, w, w, w, w} X.O)
          (Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{w, w, w, w, w} X.O)
          inferInstance C) ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{w, w, w, w} (O := X.O) (C.X i)) ∧
      Nonempty (DerivedCategory.Q.obj C ≅ K) := by
  let M := (derivedPushforward f).obj K
  obtain ⟨P, hP, s, hs⟩ := hasResolutions_isKFlat (Y := Y) (DerivedCategory.Qh.objPreimage M)
  have hsiso : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) s hs
  refine ⟨(Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj P.as,
    fun n ↦ hQ _, ?_, fun i ↦ Stacks.Sheaves.DerivedPullback.KFlatPullback.isFlat_pullbackComplex_X
      f hmos (AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlat f) P.as hP.2 i, ⟨?_⟩⟩
  · exact (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).1
      (Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex f hmos
        (AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlat f)
        (AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesShortExact f)
        (Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat Y) P.as
        ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O _).2 hP.1) hP.2)
  · have := Stacks.Cohomology.CohomologicalDescent.isIso_derivedPullbackComparison f
    exact ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
      (asIso ((derivedPullbackComparison f).app P)).symm ≪≫
      (derivedPullback f).mapIso (asIso (DerivedCategory.Qh.map s) ≪≫
        DerivedCategory.Qh.objObjPreimageIso M) ≪≫
      asIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app K)

end Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)

/-! ### The images of the affine charts cover the spaces-étale site -/

/-- An object of the spaces-étale site represented by an affine scheme is the image of an affine
chart. -/
theorem SpacesEtale.mem_affineChartImages_of_isAffineScheme {U : SpacesEtale B S hS Y}
    (hU : SpacesEtale.IsAffineScheme B S hS Y U) :
    U ∈ SpacesEtale.affineChartImages B S hS Y := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hU
  have het : IsEtale B S hS (e.hom.hom ≫ U.obj.hom.hom) :=
    isEtale_comp B S hS (isEtale_of_isIso B S hS e.hom.hom) U.property
  let Wc : SmallEtale B S hS Y.1 :=
    ⟨CostructuredArrow.mk (e.hom.hom ≫ U.obj.hom.hom), isEtaleChart_of_isEtale B S hS _ het⟩
  refine ⟨Wc, hW, ⟨ObjectProperty.isoMk _ (Over.isoMk e.symm ?_)⟩⟩
  apply ObjectProperty.hom_ext
  change e.inv.hom ≫ e.hom.hom ≫ U.obj.hom.hom = U.obj.hom.hom
  rw [← Category.assoc]
  have h : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg (fun k ↦ k.hom) e.inv_hom_id
  rw [h, Category.id_comp]

/-- **Every object of the spaces-étale site is covered by images of affine charts.** -/
theorem SpacesEtale.exists_preZeroHypercover_affineChartImages (U : SpacesEtale B S hS Y) :
    ∃ 𝒰 : PreZeroHypercover.{u + 1} U, 𝒰.sieve₀ ∈ SpacesEtale.topology B S hS Y U ∧
      ∀ i, SpacesEtale.affineChartImages B S hS Y (𝒰.X i) := by
  refine ⟨⟨Σ V : SpacesEtale B S hS Y, {g : V ⟶ U // SpacesEtale.IsAffineScheme B S hS Y V},
    fun i ↦ i.1, fun i ↦ i.2.1⟩, ?_,
    fun i ↦ SpacesEtale.mem_affineChartImages_of_isAffineScheme B S hS Y i.2.2⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (SpacesEtale.generate_affineSchemePresieve_mem B S hS Y U)
  rw [Sieve.generate_le_iff]
  intro V g hg
  exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨V, ⟨g, hg⟩⟩, 𝟙 V, (Category.id_comp g).symm⟩

/-! ### Objects with quasi-coherent cohomology are derived limits of their truncations -/

attribute [local instance] Stacks.DerivedLimit.hasProduct_truncGETower

/-- **An object of `D(𝒪_Y)` on the spaces-étale site with quasi-coherent cohomology is the
derived limit of the tower `n ↦ τ_{≥ -n} K` of its truncations from below.** -/
theorem isDerivedLimit_truncGETower_of_isQuasicoherentOnSite
    (E : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj E).IsQuasicoherentOnSite) :
    IsDerivedLimit (Stacks.DerivedLimit.truncGETower _ E) E := by
  refine
    Stacks.DerivedCategory.AdjunctionUnitTruncations.isDerivedLimit_truncGETower_of_forall_isIso
      E (fun L c q hL hc ↦ ?_)
  exact Stacks.Cohomology.UniformBound.isIso_to_isDerivedLimit_truncGETower_of_vanishing_uniform.{
      u + 1, u + 1, u + 1, 0}
    (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O) E 0 le_rfl
    (SpacesEtale.affineChartImages B S hS Y)
    (SpacesEtale.exists_preZeroHypercover_affineChartImages B S hS Y)
    (fun V hV p hp q _ ↦ by
      unfold Stacks.Cohomology.moduleCohomology
      exact isZero_rightDerived_evaluation_spacesEtale_of_isQuasicoherentOnSite B S hS Y _ (hE q) V
        hV p (by exact_mod_cast hp))
    L c q hL hc

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigFppfSpaceSite

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) {X : T.Spaces} (V₀ : T.Schemes)
  (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
  (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ X)

/-! ### Global sections over the point, as abelian groups -/

omit T in
/-- The forgetful functor from modules to abelian groups preserves finite colimits, at the
universe `u + 1`. -/
theorem preservesFiniteColimits_forget₂_moduleCat (R : Type (u + 1)) [Ring R] :
    PreservesFiniteColimits (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
  have := ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0} R
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The modules on the ringed point of global sections of `X`. -/
abbrev AffinePointModules :=
  SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
    (RingedSite.globalPoint (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X)
      (affinePoint T V₀ hV₀ e)).O)

/-- **Global sections over the point, as abelian groups.** -/
abbrev affinePointSectionsAb : AffinePointModules T V₀ hV₀ e ⥤ AddCommGrpCat.{u + 1} :=
  RingedSite.globalPointEvaluation _ _ ⋙ forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}

/-- Evaluation at the point is an equivalence. -/
theorem isEquivalence_affinePoint_globalPointEvaluation :
    (RingedSite.globalPointEvaluation (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X)
      (affinePoint T V₀ hV₀ e)).IsEquivalence := by
  rw [← RingedSite.globalPointEvaluationEquivalence_functor (isTerminal_affinePoint T V₀ hV₀ e)
    (affineAssociatedAdjunction T V₀ hV₀ e) (affineAssociatedFullyFaithful T V₀ hV₀ e)]
  infer_instance

/-- Global sections over the point, as abelian groups, preserve finite limits. -/
theorem preservesFiniteLimits_affinePointSectionsAb :
    PreservesFiniteLimits (affinePointSectionsAb T V₀ hV₀ e) := by
  have := isEquivalence_affinePoint_globalPointEvaluation T V₀ hV₀ e
  exact comp_preservesFiniteLimits _ _

/-- Global sections over the point, as abelian groups, preserve finite colimits. -/
theorem preservesFiniteColimits_affinePointSectionsAb :
    PreservesFiniteColimits (affinePointSectionsAb T V₀ hV₀ e) := by
  have := isEquivalence_affinePoint_globalPointEvaluation T V₀ hV₀ e
  have := preservesFiniteColimits_forget₂_moduleCat
    ((spacesEtaleRing T X).obj.obj (op (affinePoint T V₀ hV₀ e)))
  exact comp_preservesFiniteColimits _ _

/-- Global sections over the point, as abelian groups, is additive. -/
theorem additive_affinePointSectionsAb : (affinePointSectionsAb T V₀ hV₀ e).Additive :=
  have := preservesFiniteLimits_affinePointSectionsAb T V₀ hV₀ e
  Functor.additive_of_preserves_binary_products _

/-- Sections over `X` of the direct image along `p`, as abelian groups, commute with countable
products. -/
theorem preservesLimitsOfShape_pushforward_comp_affinePointSectionsAb :
    PreservesLimitsOfShape (Discrete ℕ)
      ((affinePointHom T V₀ hV₀ e).pushforwardTopos ⋙ affinePointSectionsAb T V₀ hV₀ e) := by
  have := isEquivalence_affinePoint_globalPointEvaluation T V₀ hV₀ e
  have :=
    (affinePointHom T V₀ hV₀ e).pullbackPushforwardAdjunctionTopos.rightAdjoint_preservesLimits
  infer_instance

/-- Global sections over the point, as abelian groups, reflect zero objects. -/
theorem isZero_of_isZero_affinePointSectionsAb {Z : AffinePointModules T V₀ hV₀ e}
    (h : IsZero ((affinePointSectionsAb T V₀ hV₀ e).obj Z)) : IsZero Z := by
  have := isEquivalence_affinePoint_globalPointEvaluation T V₀ hV₀ e
  rw [IsZero.iff_id_eq_zero]
  refine (affinePointSectionsAb T V₀ hV₀ e).map_injective ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp h

/-! ### `Rp_*` keeps `D^{≤ c}` on objects with quasi-coherent cohomology -/

include hV₀ e in
/-- Quasi-coherence on the spaces-étale site of `X` contains a zero object. -/
theorem containsZero_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleRing T X)).ContainsZero :=
  have := (affineAssociatedAdjunction T V₀ hV₀ e).left_adjoint_additive
  ⟨⟨(affineAssociated T V₀ hV₀ e).obj (ModuleCat.of _ PUnit),
    (affineAssociated T V₀ hV₀ e).map_isZero
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of _ PUnit)),
    isQuasicoherentOnSite_affineAssociated_obj T V₀ hV₀ e _⟩⟩

/-- **`Rp_*` keeps `D^{≤ c}` on objects with quasi-coherent cohomology**, with no lower
bound. -/
theorem isLE_affinePointHom_derivedPushforward_obj
    (E : DerivedCategory (SheafOfModules.{u + 1} (spacesEtaleRing T X)))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj E).IsQuasicoherentOnSite)
    (c : ℤ) (hc : E.IsLE c) :
    ((derivedPushforward (affinePointHom T V₀ hV₀ e)).obj E).IsLE c := by
  have := containsZero_isQuasicoherentOnSite T V₀ hV₀ e
  have := additive_affinePointSectionsAb T V₀ hV₀ e
  have := preservesFiniteLimits_affinePointSectionsAb T V₀ hV₀ e
  have := preservesFiniteColimits_affinePointSectionsAb T V₀ hV₀ e
  have := preservesLimitsOfShape_pushforward_comp_affinePointSectionsAb T V₀ hV₀ e
  exact isLE_derivedPushforward_obj_of_isDerivedLimit (affinePointHom T V₀ hV₀ e)
    (affinePointSectionsAb T V₀ hV₀ e)
    (fun Z hZ ↦ isZero_of_isZero_affinePointSectionsAb T V₀ hV₀ e hZ)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1} (spacesEtaleRing T X))
    (fun M hM p hp ↦ isZero_homology_affinePointHom_derivedPushforward_single T V₀ hV₀ e M hM p hp)
    (fun E hE ↦ Space.isDerivedLimit_truncGETower_of_isQuasicoherentOnSite _ _ _ X E hE)
    E hE c hc

/-! ### The counit of `Lp^* ⊣ Rp_*` on `D_QCoh` -/

/-- **The counit `Lp^* Rp_* K ⟶ K` is invertible for every `K` with quasi-coherent
cohomology.** -/
theorem isIso_affinePointDerivedAdjunction_counit_app
    (K : DerivedCategory (SheafOfModules.{u + 1} (spacesEtaleRing T X)))
    (hK : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj K).IsQuasicoherentOnSite) :
    IsIso ((affinePointDerivedAdjunction T V₀ hV₀ e).counit.app K) :=
  isIso_derivedPullbackPushforwardAdjunctionOfExact_counit_app_of_homologyIn
    (affinePointHom T V₀ hV₀ e)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1} (spacesEtaleRing T X))
    (fun M hM n ↦ isIso_affinePointDerivedAdjunction_counit_app_singleFunctor T V₀ hV₀ e M hM n)
    (fun Y hY c hc ↦ isLE_affinePointHom_derivedPushforward_obj T V₀ hV₀ e Y
      (fun q ↦ (hY q).elim id (fun hz ↦ SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((containsZero_isQuasicoherentOnSite T V₀ hV₀ e).exists_zero.choose_spec.1.iso hz)
        (containsZero_isQuasicoherentOnSite T V₀ hV₀ e).exists_zero.choose_spec.2)) c hc)
    K (fun q ↦ Or.inl (hK q))

end AlgebraicGeometry.BigFppfSpaceSite


/-! ### The K-flat quasi-coherent model -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- There are a cardinal `κ` and a limit ordinal `α` such that the `κ`-bounded fppf covering
families of algebraic spaces over `S` form a site and every fppf covering family is combinatorially
equivalent to a `κ`-bounded one (Stacks 000X, with no initial coverings and index sets in the
universe used by big fppf sites of algebraic spaces). -/
theorem exists_covBounded_isSite_isFppfCoveringFamily_of_schemeSite :
    ∃ (κ : Cardinal.{u + 2}) (α : Ordinal.{u + 2}), Order.IsSuccLimit α ∧
      (∀ 𝒰 ∈ (∅ : Set (Covering.{_, _, u + 2} (AlgebraicSpaces B S hS))),
        CovBounded (IsFppfCoveringFamily B S hS) κ 𝒰) ∧
      IsSite (CovBounded (IsFppfCoveringFamily B S hS) κ) ∧
      (∀ 𝒰 : Covering (AlgebraicSpaces B S hS), IsFppfCoveringFamily B S hS 𝒰 →
          ∃ 𝒰', CovBounded (IsFppfCoveringFamily B S hS) κ 𝒰' ∧ Covering.CombEquiv 𝒰 𝒰') :=
  exists_covBounded_isSite_of_univ.{_, _, u + 2} (IsFppfCoveringFamily B S hS)
    (isSite_isFppfCoveringFamily B S hS) ∅ (by intro U hU; cases hU)

/-- **A big fppf site of algebraic spaces over the big fppf site of schemes `B`**, with no
initial coverings and the covering bound of Stacks 000X. -/
noncomputable def bigFppfSpaceSiteOfSchemeSite : BigFppfSpaceSite S :=
  let h := exists_covBounded_isSite_isFppfCoveringFamily_of_schemeSite B S hS
  { schemeSite := B
    scheme_mem := hS
    initialCoverings := ∅
    initialCoverings_small := inferInstance
    initialCoverings_fppf := by simp
    coveringBound := h.choose
    coveringOrdinal := h.choose_spec.choose
    coveringOrdinal_isSuccLimit := h.choose_spec.choose_spec.1
    initialCoverings_bounded := by simp
    coverings_isSite := h.choose_spec.choose_spec.2.2.1
    covering_representative := h.choose_spec.choose_spec.2.2.2 }

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction in
/-- **K-flat quasi-coherent models on the spaces-étale site of an affine algebraic space**, at
the universe `u + 1` of the spaces-étale site. Let `Y` be an algebraic space over `S` which is the
algebraic space of an affine scheme `W`, and let `K` be an object of the derived category of
`𝒪_Y`-modules on the spaces-étale site of `Y` all of whose cohomology sheaves are quasi-coherent.
Then `K` is represented by a K-flat complex of flat quasi-coherent `𝒪_Y`-modules. -/
theorem exists_kFlat_isQuasicoherentOnSite_model_spacesEtale (Y : AlgebraicSpaces B S hS)
    (hY : ∃ W : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      Nonempty ((schemeSpaceFunctor B S hS).obj W ≅ Y))
    (K : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.spacesEtaleRingedSite B S hS Y).O)))
    (hK : ∀ q, ((DerivedCategory.homologyFunctor _ q).obj K).IsQuasicoherentOnSite) :
    ∃ C : CochainComplex (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Space.spacesEtaleRingedSite B S hS Y).O)) ℤ,
      (∀ n, (C.X n).IsQuasicoherentOnSite) ∧
      (letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u + 1, u + 1, u + 1, u + 1,
          u + 1} (Space.spacesEtaleRingedSite B S hS Y).O;
        @CochainComplex.KFlatBifunctor.KFlat
          (_root_.SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (Space.spacesEtaleRingedSite B S hS Y).O))
          (_root_.SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (Space.spacesEtaleRingedSite B S hS Y).O))
          (_root_.SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (Space.spacesEtaleRingedSite B S hS Y).O))
          inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
            (Space.spacesEtaleRingedSite B S hS Y).O)
          (Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u + 1, u + 1, u + 1, u + 1, u + 1}
            (Space.spacesEtaleRingedSite B S hS Y).O)
          (Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u + 1, u + 1, u + 1, u + 1,
            u + 1} (Space.spacesEtaleRingedSite B S hS Y).O)
          inferInstance C) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
        (O := (Space.spacesEtaleRingedSite B S hS Y).O) (C.X i)) ∧
      Nonempty (DerivedCategory.Q.obj C ≅ K) := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hY
  let T := bigFppfSpaceSiteOfSchemeSite B S hS
  have := BigFppfSpaceSite.preservesFiniteLimits_affinePointHom_pullbackTopos T (X := Y) W hW e
  have := BigFppfSpaceSite.preservesFiniteColimits_affinePointHom_pullbackTopos T (X := Y) W hW e
  have := BigFppfSpaceSite.affinePointHom_hasLeftDerivedFunctor T (X := Y) W hW e
  have := BigFppfSpaceSite.isIso_affinePointDerivedAdjunction_counit_app T (X := Y) W hW e K hK
  exact exists_kFlat_model_of_isIso_counit (BigFppfSpaceSite.affinePointHom T (X := Y) W hW e)
    (RingedSite.Hom.isMorphismOfSites_toRingedToposSiteHom
      (RingedSite.toGlobalPoint (BigFppfSpaceSite.isTerminal_affinePoint T (X := Y) W hW e)))
    SheafOfModules.IsQuasicoherentOnSite
    (BigFppfSpaceSite.isQuasicoherentOnSite_affinePointHom_pullbackTopos_obj T (X := Y) W hW e)
    K inferInstance

end AlgebraicGeometry.Space

end
