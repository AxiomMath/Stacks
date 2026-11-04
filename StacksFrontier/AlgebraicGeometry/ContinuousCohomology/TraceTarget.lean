module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomSingle
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InjectiveUnderlying
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveRepresents
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Category.Grp.Injective

/-!
# The target of the Galois-equivariant trace

Let `Q` be a compact topological group and `W = ℚ/ℤ` with the trivial action, as a discrete
`Q`-module. A trace `H^d(P) → ℚ/ℤ` on a complex `P` of discrete `Q`-modules with no cohomology
above degree `d` is a morphism `P → W[-d]` in the derived category, uniquely, by the canonical
t-structure (`DerivedCategory.bijective_homologyToSingle_of_isLE`). It is a morphism of complexes
only after replacing `W[-d]` by an injective resolution `T`: the trivial module `ℚ/ℤ` is not
injective among discrete `Q`-modules. This file fixes that resolution, `traceTarget Q d`, with its
augmentation `ι : W[-d] → T`, and records two facts about it.

* The trace lifts to a morphism of complexes `P → T`, unique up to homotopy since `T` is
  K-injective (`Stacks.ContinuousCohomology.exists_traceLift`).
* `T` is also a bounded below complex of injective *abelian groups*
  (`Stacks.ContinuousCohomology.injective_forgetAb_of_injective`), so postcomposition with `ι` is
  a quasi-isomorphism of internal Hom complexes `Hom^•_ℤ(E, W[-d]) → Hom^•_ℤ(E, T)` for every
  complex `E` of discrete modules (`Stacks.ContinuousCohomology.quasiIso_postcomp_traceTargetι`).
  The first complex is the contragredient of `E`, shifted (`internalHomSingleIso`).

## Main definitions

* `Stacks.ContinuousCohomology.traceTarget`: the injective resolution of `ℚ/ℤ`, shifted to start
  in degree `d`.
* `Stacks.ContinuousCohomology.traceTargetι`: the augmentation `ℚ/ℤ[-d] → traceTarget Q d`.
* `Stacks.ContinuousCohomology.derivedTraceOfIsLE`: the morphism `P → ℚ/ℤ[-d]` in the derived
  category inducing a given map on `H^d`.

## Main results

* `Stacks.ContinuousCohomology.quasiIso_postcomp_traceTargetι`: postcomposition with the
  augmentation is a quasi-isomorphism of internal Hom complexes.
* `Stacks.ContinuousCohomology.exists_traceLift`: a morphism `P → ℚ/ℤ[-d]` in the derived category
  lifts to a morphism of complexes `P → traceTarget Q d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex Stacks.GroupHomology

universe u v w

namespace Stacks.ContinuousCohomology

variable (Q : Type v) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]

/-- The forgetful functor from discrete `Q`-modules over `R` to abelian groups preserves finite
limits. -/
instance forgetAb_preservesFiniteLimits (R : Type) [Ring R] :
    PreservesFiniteLimits (forgetAb.{0, v, w} R Q) := by
  have := Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{0, v, w} R Q
  exact comp_preservesFiniteLimits _ _

/-- The forgetful functor from discrete `Q`-modules over `R` to abelian groups preserves finite
colimits. -/
instance forgetAb_preservesFiniteColimits (R : Type) [Ring R] :
    PreservesFiniteColimits (forgetAb.{0, v, w} R Q) := by
  have := Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{0, v, w} R Q
  exact comp_preservesFiniteColimits _ _

/-- `ℚ/ℤ`, in the module universe. -/
abbrev ratCircle : Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q :=
  trivialRatCircleULift.{v, max v w} Q

/-- The chosen injective resolution of `ℚ/ℤ` among discrete `Q`-modules. -/
def ratCircleResolution : InjectiveResolution (ratCircle.{v, w} Q) :=
  injectiveResolution _

/-- **The target of the trace in degree `d`**: the injective resolution of `ℚ/ℤ`, shifted to start
in degree `d`. -/
def traceTarget (d : ℤ) :
    CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q) ℤ :=
  ((ratCircleResolution.{v, w} Q).cochainComplex)⟦-d⟧

/-- The augmentation `ℚ/ℤ[-d] → T`. -/
def traceTargetι (d : ℤ) : singleComplex (ratCircle.{v, w} Q) d ⟶ traceTarget.{v, w} Q d :=
  ((CochainComplex.singleFunctors _).shiftIso (-d) d 0 (by omega)).inv.app _ ≫
    ((ratCircleResolution.{v, w} Q).ι')⟦-d⟧'

/-- The augmentation `ℚ/ℤ[-d] → traceTarget Q d` is a quasi-isomorphism. -/
instance (d : ℤ) : QuasiIso (traceTargetι.{v, w} Q d) := by
  unfold traceTargetι
  have h0 : QuasiIso (ratCircleResolution.{v, w} Q).ι' := InjectiveResolution.instQuasiIsoIntι' _
  have h1 : QuasiIso (((ratCircleResolution.{v, w} Q).ι')⟦-d⟧') :=
    (CochainComplex.quasiIso_shift_iff (ratCircleResolution.{v, w} Q).ι' (-d)).2 h0
  have h2 : QuasiIso (((CochainComplex.singleFunctors _).shiftIso (-d) d 0 (by omega)).inv.app
      (ratCircle.{v, w} Q)) := quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h2) (hφ' := h1) _ _

/-- `traceTarget Q d` is strictly concentrated in degrees `≥ d`. -/
instance (d : ℤ) : (traceTarget.{v, w} Q d).IsStrictlyGE d := by
  unfold traceTarget
  exact CochainComplex.isStrictlyGE_shift _ 0 (-d) d (by omega)

/-- Every term of `traceTarget Q d` is an injective discrete `Q`-module. -/
instance (d n : ℤ) : Injective ((traceTarget.{v, w} Q d).X n) := by
  unfold traceTarget
  change Injective ((ratCircleResolution.{v, w} Q).cochainComplex.X (n + -d))
  infer_instance

/-- `traceTarget Q d` is K-injective. -/
instance (d : ℤ) : (traceTarget.{v, w} Q d).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ d

/-! ### The underlying complexes of abelian groups -/

/-- The underlying complex of abelian groups of `traceTarget Q d` is strictly concentrated in
degrees `≥ d`. -/
instance (d : ℤ) : (underlyingAb ℤ (traceTarget.{v, w} Q d)).IsStrictlyGE d :=
  (CochainComplex.isStrictlyGE_iff _ d).2 fun n hn => (forgetAb ℤ Q).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE (traceTarget.{v, w} Q d) d n hn)

/-- Every term of the underlying complex of abelian groups of `traceTarget Q d` is an injective
abelian group. -/
instance (d n : ℤ) : Injective ((underlyingAb ℤ (traceTarget.{v, w} Q d)).X n) :=
  injective_forgetAb_of_injective.{v, w} ((traceTarget.{v, w} Q d).X n)

/-- The underlying complex of abelian groups of `traceTarget Q d` is K-injective. -/
instance (d : ℤ) : (underlyingAb ℤ (traceTarget.{v, w} Q d)).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ d

/-- The underlying complex of abelian groups of `ℚ/ℤ[-d]` is strictly concentrated in degrees
`≥ d`. -/
instance (d : ℤ) : (underlyingAb ℤ (singleComplex (ratCircle.{v, w} Q) d)).IsStrictlyGE d :=
  (CochainComplex.isStrictlyGE_iff _ d).2 fun n hn => (forgetAb ℤ Q).map_isZero
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))

/-- Every term of the underlying complex of abelian groups of `ℚ/ℤ[-d]` is an injective abelian
group. -/
instance (d n : ℤ) : Injective ((underlyingAb ℤ (singleComplex (ratCircle.{v, w} Q) d)).X n) := by
  by_cases hn : n = d
  · subst hn
    exact Injective.of_iso ((forgetAb ℤ Q).mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (ratCircle.{v, w} Q))).symm
      (AddCommGrpCat.injective_of_divisible (ULift.{max v w} (AddCircle (1 : ℚ))))
  · exact (isZero_underlyingAb_singleComplex_X _ d n hn).injective

/-- The underlying complex of abelian groups of `ℚ/ℤ[-d]` is K-injective. -/
instance (d : ℤ) : (underlyingAb ℤ (singleComplex (ratCircle.{v, w} Q) d)).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ d

/-- **The augmentation is a homotopy equivalence on underlying abelian groups**: a
quasi-isomorphism between bounded below complexes of injective abelian groups. -/
theorem homotopyEquivalences_underlyingAb_traceTargetι (d : ℤ) :
    HomologicalComplex.homotopyEquivalences _ _
      (((forgetAb ℤ Q).mapHomologicalComplex _).map (traceTargetι.{v, w} Q d)) :=
  (CochainComplex.IsKInjective.quasiIso_iff _).1 inferInstance

/-- **Postcomposition with the augmentation is a quasi-isomorphism of internal Hom complexes**,
`Hom^•_ℤ(E, ℚ/ℤ[-d]) → Hom^•_ℤ(E, T)`, for every complex `E` of discrete modules. -/
theorem quasiIso_postcomp_traceTargetι (R : Type) [Ring R] [Finite R]
    (E : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ) (d : ℤ) :
    QuasiIso (internalHomComplexPostcomp R E (traceTargetι.{v, w} Q d)) := by
  obtain ⟨e, he⟩ := homotopyEquivalences_underlyingAb_traceTargetι.{v, w} Q d
  exact quasiIso_internalHomComplexPostcomp R E _ e he

/-! ### The trace and its lift -/

attribute [local instance] HasDerivedCategory.standard

/-- **The derived trace**: for `P` with no cohomology above degree `d`, the unique morphism
`P → ℚ/ℤ[-d]` in the derived category inducing `tr` on `H^d`. -/
def derivedTraceOfIsLE
    (P : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q) ℤ)
    (d : ℤ) [(DerivedCategory.Q.obj P).IsLE d]
    (tr : (DerivedCategory.homologyFunctor _ d).obj (DerivedCategory.Q.obj P) ⟶
      ratCircle.{v, w} Q) :
    DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (singleComplex (ratCircle.{v, w} Q) d) :=
  (AddEquiv.ofBijective _ (DerivedCategory.bijective_homologyToSingle_of_isLE
      (DerivedCategory.Q.obj P) (ratCircle.{v, w} Q) d)).symm tr ≫
    (DerivedCategory.singleFunctorIsoCompQ _ d).hom.app _

omit [CompactSpace Q] in
/-- The derived trace `derivedTraceOfIsLE Q P d tr` induces `tr` on `H^d`. -/
lemma homologyToSingle_derivedTraceOfIsLE
    (P : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q) ℤ)
    (d : ℤ) [(DerivedCategory.Q.obj P).IsLE d]
    (tr : (DerivedCategory.homologyFunctor _ d).obj (DerivedCategory.Q.obj P) ⟶
      ratCircle.{v, w} Q) :
    DerivedCategory.homologyToSingle _ _ d
      (derivedTraceOfIsLE.{v, w} Q P d tr ≫ (DerivedCategory.singleFunctorIsoCompQ _ d).inv.app _) =
      tr := by
  unfold derivedTraceOfIsLE
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  exact (AddEquiv.ofBijective _ (DerivedCategory.bijective_homologyToSingle_of_isLE
      (DerivedCategory.Q.obj P) (ratCircle.{v, w} Q) d)).apply_symm_apply tr

omit [CompactSpace Q] in
/-- **Every morphism `P → ℚ/ℤ[-d]` in the derived category lifts to a morphism of complexes into
the injective resolution `T`**, which is K-injective. -/
theorem exists_traceLift
    (P : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q) ℤ) (d : ℤ)
    (τ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (singleComplex (ratCircle.{v, w} Q) d)) :
    ∃ t : P ⟶ traceTarget.{v, w} Q d,
      DerivedCategory.Q.map t = τ ≫ DerivedCategory.Q.map (traceTargetι.{v, w} Q d) := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj P) (traceTarget.{v, w} Q d)).surjective
    ((DerivedCategory.quotientCompQhIso _).hom.app P ≫
      (τ ≫ DerivedCategory.Q.map (traceTargetι.{v, w} Q d)) ≫
      (DerivedCategory.quotientCompQhIso _).inv.app _)
  obtain ⟨t, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨t, ?_⟩
  have := congrArg (fun x => (DerivedCategory.quotientCompQhIso _).inv.app P ≫ x ≫
    (DerivedCategory.quotientCompQhIso _).hom.app _) hg
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Iso.inv_hom_id_app_assoc] at this
  rw [← this, ← Functor.comp_map, (DerivedCategory.quotientCompQhIso _).hom.naturality t,
    Iso.inv_hom_id_app_assoc]

end Stacks.ContinuousCohomology

end
