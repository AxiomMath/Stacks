module

public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantComplexLimit
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConnectedLocalInvariant
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstantComplexAdicTowerIso
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.LocallyConstantValues
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleReductions
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedReductionTower
public import StacksFrontier.AlgebraicGeometry.ProEtale.OverRestrictionReductionTower
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ConstantComplexGluing
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.AdicReductionSections
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ConstantTorAmplitude
public import StacksFrontier.Homology.TorAmplitude.ResolutionFlatRepresentative
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.FiniteProjectiveAdicModel
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Topology.Sheaves.Modules.StalkKFlat
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedCompletion
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces
public import StacksFrontier.Homology.DerivedComplete.FlatAdicCompletionExtension
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf

/-!
# Constructible complexes with locally constant reductions are adic lisse

Let `X` be a connected scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. A constructible
object `K` of `D(X_proét, Λ)` whose reduction `K ⊗_Λ^L \underline{Λ/I}` has locally constant
cohomology sheaves is adic lisse. We also show that such a first reduction is bounded with Tor
amplitude in one interval, and that every reduction `K ⊗_Λ^L \underline{Λ/Iⁿ⁺¹}` is pro-étale
locally the constant complex attached to one bounded complex of finite projective
`Λ^∧`-modules.

## Main results

* `AlgebraicGeometry.ProEtale.isAdicLisseDerivedSheaf_of_isLocallyConstant`: a constructible
  complex on a connected scheme whose reduction modulo `I` has locally constant cohomology sheaves
  is adic lisse.
* `isFiniteTypeLocallyConstantModuleSheaf_homology_derivedExtendScalars_iff`: a cohomology sheaf
  of `K ⊗_Λ^L \underline{Λ/𝔞}` is locally constant of finite type over `Λ/𝔞` exactly when the
  corresponding cohomology sheaf of the derived tensor product over `Λ` is so over `Λ`.
* `isFiniteTypeLocallyConstantModuleSheaf_homology_derivedExtendScalars_pow`: for `K` bounded
  above, local constancy of finite type of the cohomology of `K ⊗_Λ^L Λ/I` passes to every
  `K ⊗_Λ^L Λ/Iⁿ`.
* `AlgebraicGeometry.ProEtale.isFiniteTypeLocallyConstantModuleSheaf_homology_derivedReduction`:
  a constructible object whose first reduction has locally constant cohomology sheaves has
  locally constant cohomology sheaves of finite type.
* `AlgebraicGeometry.ProEtale.exists_isGE_isLE_derivedReduction_of_connectedSpace`: over a
  connected scheme the first reduction of such an object is bounded.
* `AlgebraicGeometry.ProEtale.exists_hasTorAmplitude_derivedReduction_of_connectedSpace`: over a
  connected scheme the first reduction of such an object has Tor amplitude in one interval.
* `AlgebraicGeometry.ProEtale.exists_cover_reduction_iso_constantSheaf_sheafFiber`: over a
  connected scheme every reduction `K ⊗_Λ^L Λ/Iⁿ⁺¹` is pro-étale locally the constant complex of
  `Λ/Iⁿ⁺¹ ⊗_Λ N`, for `N` the fibre at one point of a K-flat representative of `K`.
* `AlgebraicGeometry.ProEtale.exists_adicModel_cover_reduction_iso_of_connectedSpace`: over a
  connected scheme there is one bounded complex `M` of finite projective `Λ^∧`-modules such that
  every reduction `K ⊗_Λ^L Λ/Iⁿ⁺¹` is pro-étale locally the constant complex of
  `Λ/Iⁿ⁺¹ ⊗_{Λ^∧} M`.
* `AlgebraicGeometry.ProEtale.nonempty_overRestrictionDerived_iso_of_reductionTower_iso`: for a
  derived complete `K`, an isomorphism of towers `\underline{M^•/IⁿM^•}|_V ≅ Kₙ|_V` gives
  `K|_V ≅ \underline{M^•}^∧|_V`.

## References

* [Stacks Project, Tag 09C6](https://stacks.math.columbia.edu/tag/09C6)
* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits NoetherianAdicCompletion

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)

/-- The functor of the equivalence `constantCoefficientModuleEquiv X Λ` is additive. -/
instance constantCoefficientModuleEquiv_functor_additive :
    (constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of the equivalence `constantCoefficientModuleEquiv X Λ` is additive. -/
instance constantCoefficientModuleEquiv_inverse_additive :
    (constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor of the equivalence `derivedModuleEquiv X Λ` is the derived functor of the functor
of the exact equivalence `constantCoefficientModuleEquiv X Λ`. -/
theorem derivedModuleEquiv_functor :
    (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor =
      (constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.mapDerivedCategory :=
  rfl

/-- The derived functor of the functor of `constantCoefficientModuleEquiv X Λ` preserves limits
indexed by `Discrete ℕ`, that is, countable products. -/
instance preservesLimitsOfShape_constantCoefficientModuleEquiv_functor_mapDerivedCategory :
    PreservesLimitsOfShape (Discrete ℕ)
      (constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.mapDerivedCategory :=
  inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
    (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor)

/-- Derived restriction to an object `V` of `X_proét` is an additive functor. -/
instance overRestrictionDerived_additive (V : X.ProEt) :
    (overRestrictionDerived.{u, max (u + 1) w, w} X Λ V).Additive :=
  letI : PreservesFiniteLimits (SheafOfModules.overFunctor.{max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)) V) :=
    SheafOfModules.preservesFiniteLimits_pushforward _
  letI : PreservesFiniteColimits (SheafOfModules.overFunctor.{max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u,
      max (u + 1) w} V
  inferInstanceAs ((SheafOfModules.overFunctor.{max (u + 1) w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)) V).mapDerivedCategory.Additive)

/-- Derived restriction to an object `V` of `X_proét` commutes with the shift by `ℤ`. -/
instance overRestrictionDerived_commShift (V : X.ProEt) :
    (overRestrictionDerived.{u, max (u + 1) w, w} X Λ V).CommShift ℤ :=
  letI : PreservesFiniteLimits (SheafOfModules.overFunctor.{max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)) V) :=
    SheafOfModules.preservesFiniteLimits_pushforward _
  letI : PreservesFiniteColimits (SheafOfModules.overFunctor.{max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u,
      max (u + 1) w} V
  inferInstanceAs ((SheafOfModules.overFunctor.{max (u + 1) w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O))
        V).mapDerivedCategory.CommShift ℤ)

/-- Derived restriction to an object `V` of `X_proét` is a triangulated functor. -/
instance overRestrictionDerived_isTriangulated (V : X.ProEt) :
    (overRestrictionDerived.{u, max (u + 1) w, w} X Λ V).IsTriangulated :=
  letI : PreservesFiniteLimits (SheafOfModules.overFunctor.{max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)) V) :=
    SheafOfModules.preservesFiniteLimits_pushforward _
  letI : PreservesFiniteColimits (SheafOfModules.overFunctor.{max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u,
      max (u + 1) w} V
  inferInstanceAs ((SheafOfModules.overFunctor.{max (u + 1) w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O))
        V).mapDerivedCategory.IsTriangulated)

/-- **A compatible family of local models of the reductions gives a local model.** Let `K` be an
object of `D(X_proét, Λ)` that is derived complete with respect to the ideal sheaf
`I·\underline{Λ}`, `V` an object of
`X_proét` and `M^•` a complex of `Λ^∧`-modules. An isomorphism of towers
`\underline{M^•/IⁿM^•}|_V ≅ (K ⊗_Λ^L \underline{Λ/Iⁿ})|_V`, compatible with the transition maps,
gives an isomorphism `K|_V ≅ \underline{M^•}^∧|_V`. -/
theorem nonempty_overRestrictionDerived_iso_of_reductionTower_iso [IsNoetherianRing Λ]
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    (hK : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I) K)
    (V : X.ProEt) (M : CochainComplex (ModuleCat.{max (u + 1) w} (AdicCompletion I Λ)) ℤ)
    (φ : adicQuotientConstantComplexTower.{u, w} X Λ I
        (((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).mapHomologicalComplex
          _).obj M) ⋙ DerivedCategory.Q ⋙ overRestrictionDerived.{u, max (u + 1) w, w} X Λ V ≅
      derivedReductionTower.{u, w} X Λ I
          ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K) ⋙
        (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor ⋙
          overRestrictionDerived.{u, max (u + 1) w, w} X Λ V) :
    Nonempty ((overRestrictionDerived.{u, max (u + 1) w, w} X Λ V).obj K ≅
      (overRestrictionDerived.{u, max (u + 1) w, w} X Λ V).obj
        (DerivedCategory.Q.obj ((completedConstantCoefficientComplex.{u, max (u + 1) w, w}
          X Λ I).obj M))) := by
  let e := derivedModuleEquiv.{u, max (u + 1) w, w} X Λ
  let K' := e.inverse.obj K
  have := preservesLimitsOfShape_overRestrictionDerived.{u, max (u + 1) w, w} X Λ V
  have h₁ :=
    (Stacks.ModuleSheaf.isDerivedComplete_iff_isDerivedLimitWithProjections_derivedReductionTower
      (Scheme.ProEt.topology X) Λ I K').mp (isDerivedComplete_derivedModuleEquiv_inverse_obj X I hK)
  have h₂ := (h₁.map (constantCoefficientModuleEquiv.{u, max (u + 1) w, w}
    X Λ).functor.mapDerivedCategory).map (overRestrictionDerived.{u, max (u + 1) w, w} X Λ V)
  have h₃ := ((isDerivedLimitWithProjections_completedConstantCoefficientComplex.{u, w}
    X Λ I M).map (overRestrictionDerived.{u, max (u + 1) w, w} X Λ V)).comp_of_hasEventualInverses
      φ.hom (hasEventualInverses_of_isIso _)
  obtain ⟨f, -⟩ := h₂.exists_iso h₃
  exact ⟨(overRestrictionDerived.{u, max (u + 1) w, w} X Λ V).mapIso (e.counitIso.app K).symm ≪≫ f⟩

section Reductions

open MonoidalCategory

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
  Stacks.ModuleSheaf.derivedMonoidal Stacks.ModuleSheaf.derivedSymmetric

set_option linter.checkUnivs false in
/-- The quotient `Λ/𝔞`, as a module over itself read over `Λ` by restriction of scalars, is the
quotient module `Λ/𝔞` of `Λ`. -/
def restrictScalarsQuotientSelfIso (𝔞 : Ideal Λ) :
    (ModuleCat.restrictScalars.{max (u + 1) w} (Ideal.Quotient.mk 𝔞)).obj
        (ModuleCat.of (Λ ⧸ 𝔞) (Λ ⧸ 𝔞)) ≅ ModuleCat.of Λ (Λ ⧸ 𝔞) :=
  LinearEquiv.toModuleIso
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Local constancy of the cohomology of a derived reduction, read over `Λ`.** A cohomology
sheaf of `K ⊗_Λ^L \underline{Λ/𝔞}`, an object of `D(X_proét, Λ/𝔞)`, is locally constant of
finite type over `Λ/𝔞` exactly when the cohomology sheaf of the derived tensor product
`K ⊗_Λ^L \underline{Λ/𝔞}` in `D(X_proét, Λ)` is so over `Λ`. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedExtendScalars_iff (𝔞 : Ideal Λ)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) (i : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, w}
        (Scheme.ProEt.topology X) (Λ ⧸ 𝔞)
        ((DerivedCategory.homologyFunctor _ i).obj
          ((Stacks.ModuleSheaf.derivedExtendScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk 𝔞)).obj K)) ↔
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, w}
        (Scheme.ProEt.topology X) Λ
        ((DerivedCategory.homologyFunctor _ i).obj
          (Stacks.ConstantSheaf.derivedTensorConstant (Scheme.ProEt.topology X) Λ
            (curriedTensor _) K (ModuleCat.of Λ (Λ ⧸ 𝔞)))) := by
  let J := Scheme.ProEt.topology X
  let f := Ideal.Quotient.mk 𝔞
  let F := Stacks.ModuleSheaf.restrictScalars J f
  rw [← Stacks.ModuleSheaf.isFiniteTypeLocallyConstantModuleSheaf_restrictScalars_iff J
    (f := f) Ideal.Quotient.mk_surjective]
  obtain ⟨e⟩ := Stacks.ModuleSheaf.nonempty_restrictScalars_derivedExtendScalars_iso (J := J) f K
  let e' : F.obj ((DerivedCategory.homologyFunctor _ i).obj
      ((Stacks.ModuleSheaf.derivedExtendScalars J f).obj K)) ≅
      (DerivedCategory.homologyFunctor _ i).obj
        (Stacks.ConstantSheaf.derivedTensorConstant J Λ (curriedTensor _) K
          (ModuleCat.of Λ (Λ ⧸ 𝔞))) :=
    ((F.mapDerivedCategoryHomologyIso i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (e ≪≫
        ((DerivedCategory.singleFunctor _ 0).mapIso
          ((constantSheaf J (ModuleCat.{max (u + 1) w} Λ)).mapIso
            (restrictScalarsQuotientSelfIso.{u, w} Λ 𝔞)) ⊗ᵢ Iso.refl K) ≪≫ β_ _ _)
  exact ⟨ObjectProperty.prop_of_iso _ e', ObjectProperty.prop_of_iso _ e'.symm⟩

/-- Let `Λ` be Noetherian, `I ⊆ Λ` an ideal and `K` a bounded above object of `D(X_proét, Λ)`.
If the cohomology sheaves of `K ⊗_Λ^L Λ/I` are locally constant of finite type, so are those of
`K ⊗_Λ^L Λ/Iⁿ` for every `n ≥ 1`. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedExtendScalars_pow
    [IsNoetherianRing Λ]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (b : ℤ) [K.IsLE b]
    (hbase : ∀ i : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1,
        w} (Scheme.ProEt.topology X) (Λ ⧸ I)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((Stacks.ModuleSheaf.derivedExtendScalars (Scheme.ProEt.topology X)
          (Ideal.Quotient.mk I)).obj K)))
    (n : ℕ) (hn : 1 ≤ n) (i : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, w}
      (Scheme.ProEt.topology X) (Λ ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((Stacks.ModuleSheaf.derivedExtendScalars (Scheme.ProEt.topology X)
          (Ideal.Quotient.mk (I ^ n))).obj K)) := by
  let J := Scheme.ProEt.topology X
  let : ∀ L : DerivedCategory (Sheaf J (ModuleCat.{max (u + 1) w} Λ)),
      ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{max (u + 1) w} Λ)))).obj
        L).CommShift ℤ :=
    fun L => (Stacks.ModuleSheaf.exists_commShift_isTriangulated_tensorLeft J Λ L).choose
  have : ∀ L : DerivedCategory (Sheaf J (ModuleCat.{max (u + 1) w} Λ)),
      ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{max (u + 1) w} Λ)))).obj
        L).IsTriangulated :=
    fun L => (Stacks.ModuleSheaf.exists_commShift_isTriangulated_tensorLeft J Λ L).choose_spec
  refine (isFiniteTypeLocallyConstantModuleSheaf_homology_derivedExtendScalars_iff X Λ (I ^ n) K
    i).2 ?_
  open Stacks.ConstantSheaf in
  exact
    isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_isLE.{w, u, u + 1}
      J Λ I (curriedTensor _)
      (fun L M a b _ _ => Stacks.ModuleSheaf.isLE_tensor L M a b) b K
      (fun j => (isFiniteTypeLocallyConstantModuleSheaf_homology_derivedExtendScalars_iff X Λ I K
        j).1 (hbase j)) n hn i

end Reductions

section Connected

attribute [local instance] Sheaf.monoidalCategory

variable {X Λ I}

/-- A covering sieve generated by a presieve contains a member of the presieve whose source has a
point. -/
private theorem exists_mem_presieve_nonempty_left {U : X.ProEt} {R : Presieve U}
    (hR : Sieve.generate R ∈ Scheme.ProEt.topology X U) (y : U.left) :
    ∃ (V : X.ProEt) (f : V ⟶ U), R f ∧ Nonempty V.left := by
  obtain ⟨Z, g, hg, z, -⟩ := AlgebraicGeometry.Scheme.ProEt.exists_mem_range_of_mem_topology hR y
  obtain ⟨V, h, f, hf, -⟩ := hg
  exact ⟨V, f, hf, ⟨h.left z⟩⟩

/-- The constant sheaf functor to a slice of `X_proét` is additive on module categories. -/
private instance additive_constantSheaf_moduleCat (R : Type (max (u + 1) w)) [CommRing R]
    (V : X.ProEt) :
    (constantSheaf ((Scheme.ProEt.topology X).over V) (ModuleCat.{max (u + 1) w} R)).Additive :=
  have : PreservesFiniteColimits
      (constantSheaf ((Scheme.ProEt.topology X).over V) (ModuleCat.{max (u + 1) w} R)) := by
    unfold constantSheaf; infer_instance
  have := Stacks.ModuleSheaf.preservesFiniteLimits_constantSheaf
    ((Scheme.ProEt.topology X).over V) R
  Functor.additive_of_preserves_binary_products _

/-- The cohomology sheaves of the first reduction of a constructible object which are locally
constant are locally constant of finite type, for `Λ` Noetherian. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedReduction [IsNoetherianRing Λ]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hloc : ∀ i : ℤ, Stacks.ConstantSheaf.IsLocallyConstant (Scheme.ProEt.topology X)
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K)))
    (i : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, w}
      (Scheme.ProEt.topology X) (Λ ⧸ I)
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K)) :=
  isFiniteTypeLocallyConstantModuleSheaf_of_isLocallyConstant.{w, max (u + 1) w, u} (Λ ⧸ I) _
    (hl := hloc i) (hK.2.1 i)

/-- **Over a connected scheme the first reduction is bounded.** Let `X` be connected and `K` a
constructible object of `D(X_proét, Λ)` whose first reduction `K ⊗_Λ^L \underline{Λ/I}` has
locally constant cohomology sheaves of finite type. Then that reduction has cohomology in some
interval `[a, b]`. -/
theorem exists_isGE_isLE_derivedReduction_of_connectedSpace [ConnectedSpace X] [IsNoetherianRing Λ]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hlc : ∀ i : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, w}
      (Scheme.ProEt.topology X) (Λ ⧸ I)
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K))) :
    ∃ a b : ℤ, ((derivedReduction.{u, w} X Λ I).obj K).IsGE a ∧
      ((derivedReduction.{u, w} X Λ I).obj K).IsLE b := by
  let J := Scheme.ProEt.topology X
  let L := (derivedReduction.{u, w} X Λ I).obj K
  obtain ⟨S, hS, hS'⟩ := hK.2.2 (Scheme.ProEt.mk (𝟙 X))
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨V₀, f₀, hf₀, ⟨v₀⟩⟩ := exists_mem_presieve_nonempty_left hS x₀
  let := Stacks.ModuleSheaf.preservesFiniteLimits_overPullback J (Λ ⧸ I) V₀
  let := Stacks.ModuleSheaf.preservesFiniteColimits_overPullback J (Λ ⧸ I) V₀
  obtain ⟨a, b, hab⟩ := hS' f₀ hf₀
  obtain ⟨hGE, hLE⟩ := hab.isGE_isLE
  let G := J.overPullback (ModuleCat.{max (u + 1) w} (Λ ⧸ I)) V₀
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  have hzero : ∀ i : ℤ,
      IsZero ((DerivedCategory.homologyFunctor _ i).obj (G.mapDerivedCategory.obj L)) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj L) := fun i hi =>
    open Stacks.ConstantSheaf in
    isZero_of_isZero_overPullback_of_connectedSpace.{w, max (u + 1) w, u} (Λ ⧸ I) _
      ((isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf
        _ _ _).2 (hlc i)) v₀ (hi.of_iso ((G.mapDerivedCategoryHomologyIso i).app L).symm)
  exact ⟨a, b, (DerivedCategory.isGE_iff _ _).2 fun i hi => hzero i
    ((DerivedCategory.isGE_iff _ _).1 hGE i hi), (DerivedCategory.isLE_iff _ _).2 fun i hi =>
      hzero i ((DerivedCategory.isLE_iff _ _).1 hLE i hi)⟩

/-- **A local constant model of the first reduction has perfect coefficients.** Let `K` be a
constructible object of `D(X_proét, Λ)`, `Λ` Noetherian, and suppose that over a nonempty object
`W` the first reduction `K ⊗_Λ^L \underline{Λ/I}` is isomorphic to the constant complex
`\underline{P}` of a bounded complex `P` of finite `Λ/I`-modules. Then `P` is perfect. -/
theorem isPerfect_of_overPullback_iso_constantSheaf [IsNoetherianRing Λ]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    {T : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (Λ ⧸ I))) ℤ}
    (e : (derivedReduction.{u, w} X Λ I).obj K ≅ DerivedCategory.Q.obj T)
    (P : CochainComplex (ModuleCat.{max (u + 1) w} (Λ ⧸ I)) ℤ) (a b : ℤ)
    (hPv : ∀ n, n ∉ Set.Icc a b → IsZero (P.X n)) (hPfg : ∀ n, ModuleCat.isFG (Λ ⧸ I) (P.X n))
    {W : X.ProEt} (y : W.left)
    (eW : Nonempty (DerivedCategory.Q.obj
      ((((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) w} (Λ ⧸ I))
        W).mapHomologicalComplex (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj (((constantSheaf ((Scheme.ProEt.topology X).over W)
        (ModuleCat.{max (u + 1) w} (Λ ⧸ I))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P) := by
  classical
  let J := Scheme.ProEt.topology X
  let R := Λ ⧸ I
  let A := ModuleCat.{max (u + 1) w} R
  let L := (derivedReduction.{u, w} X Λ I).obj K
  obtain ⟨S, hS, hS'⟩ := hK.2.2 W
  obtain ⟨V, fV, hfV, ⟨v⟩⟩ := exists_mem_presieve_nonempty_left hS y
  let := Stacks.ModuleSheaf.preservesFiniteLimits_overPullback J R V
  let := Stacks.ModuleSheaf.preservesFiniteColimits_overPullback J R V
  obtain ⟨a', b', hab'⟩ := hS' fV hfV
  obtain ⟨eV⟩ := Scheme.ProEt.nonempty_constantComplexModel_of_hom R T fV eW
  let G := J.overPullback A V
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  let cV := constantSheaf (J.over V) A
  obtain ⟨P', hP'le, hP'f, ⟨eP'⟩⟩ :=
    Stacks.ModuleSheaf.exists_finiteFree_isStrictlyLE_iso P a b hPv hPfg
  have hampP' : Stacks.ModuleSheaf.HasTorAmplitude (J := J.over V)
      (DerivedCategory.Q.obj ((cV.mapHomologicalComplex (ComplexShape.up ℤ)).obj P'))
      (Set.Icc a' b') :=
    Stacks.ModuleSheaf.HasTorAmplitude.of_iso (K := G.mapDerivedCategory.obj L)
      (G.mapDerivedCategory.mapIso e ≪≫ G.mapDerivedCategoryFactors.app T ≪≫ eV ≪≫
      (cV.mapDerivedCategoryFactors.app P).symm ≪≫ cV.mapDerivedCategory.mapIso eP'.symm ≪≫
        cV.mapDerivedCategoryFactors.app P') hab'
  obtain ⟨p, ⟨x⟩⟩ := Scheme.ProEt.exists_point_nonempty_fiber_obj.{u, w} v
  have : ∀ n, Module.Flat R (P'.X n) := fun n => by
    have := (hP'f n).2
    infer_instance
  have hflat := StacksDraft.TorAmplitude.hasFlatRepresentative_of_isZero_homology_tensor P'
    (CochainComplex.KFlat.kFlat_of_flat P' b) a' b'
    (fun M F f hf _ hFle hFfree i hi =>
      have := hf
      have := hFle
      Stacks.ModuleSheaf.isZero_homology_tensor_of_hasTorAmplitude_constantSheaf (p.over x) P' b
        (fun n => (hP'f n).2) (fun N j hj => hampP' _ j hj) M F f hFfree hi)
  exact Stacks.ConstantSheaf.isPerfect_of_hasFlatRepresentative' P a b hPv hPfg a' b'
    (StacksDraft.TorAmplitude.hasFlatRepresentative_of_iso eP' hflat)

/-- **Over a connected scheme the first reduction has Tor amplitude in one interval.** Let `X` be
connected and `K` a constructible object of `D(X_proét, Λ)` whose first reduction
`K₁ = K ⊗_Λ^L \underline{Λ/I}` has locally constant cohomology sheaves of finite type. Then `K₁`
has Tor amplitude in some interval `[a, b]`. -/
theorem exists_hasTorAmplitude_derivedReduction_of_connectedSpace [ConnectedSpace X]
    [IsNoetherianRing Λ]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hlc : ∀ i : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, w}
      (Scheme.ProEt.topology X) (Λ ⧸ I)
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K))) :
    ∃ a b : ℤ, Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology X)
      ((derivedReduction.{u, w} X Λ I).obj K) (Set.Icc a b) := by
  classical
  let J := Scheme.ProEt.topology X
  let R := Λ ⧸ I
  let A := ModuleCat.{max (u + 1) w} R
  let L := (derivedReduction.{u, w} X Λ I).obj K
  obtain ⟨a₀, b₀, hGE, hLE⟩ := exists_isGE_isLE_derivedReduction_of_connectedSpace hK hlc
  let KB : DerivedCategory.Bounded (Sheaf J A) := ⟨L, ⟨⟨a₀, hGE⟩, ⟨b₀, hLE⟩⟩⟩
  obtain ⟨T, e, P, a, b, hPv, hPfg, hcov⟩ :=
    Scheme.ProEt.exists_uniform_constantComplex_representation_of_connectedSpace.{u, w} R KB hlc
  obtain ⟨ι, W, g, hW, hWm⟩ := hcov (Scheme.ProEt.mk (𝟙 X))
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨_, _, ⟨j₀⟩, ⟨w₀⟩⟩ := exists_mem_presieve_nonempty_left hW x₀
  have hperf := isPerfect_of_overPullback_iso_constantSheaf hK e P a b hPv hPfg w₀ (hWm j₀).2
  obtain ⟨E, aE, bE, hEGE, hELE, hEfin, hEproj, hEm⟩ :=
    Stacks.ConstantSheaf.exists_cover_constantFiniteProjectiveComplex_of_isPerfect' J R T P hperf W
      (fun j => (hWm j).2)
  refine ⟨aE, bE, Stacks.ModuleSheaf.hasTorAmplitude_of_coversTop (W := W) (V := W) ?_
    (fun j => 𝟙 _) L _ fun j => ?_⟩
  · rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ Scheme.ProEt.isTerminal_mk_id]
    refine J.superset_covering ?_ hW
    rintro Z f ⟨_, a, _, ⟨j⟩, -⟩
    exact ⟨j, ⟨a⟩⟩
  · let := Stacks.ModuleSheaf.preservesFiniteLimits_overPullback J R (W j)
    let := Stacks.ModuleSheaf.preservesFiniteColimits_overPullback J R (W j)
    let Gj := J.overPullback A (W j)
    have : Gj.Additive := Functor.additive_of_preserves_binary_products _
    have : ∀ n, Module.Flat R (E.X n) := fun n => by
      have := hEproj n
      infer_instance
    exact Stacks.ModuleSheaf.HasTorAmplitude.of_iso (K := DerivedCategory.Q.obj
        (((constantSheaf (J.over (W j)) A).mapHomologicalComplex (ComplexShape.up ℤ)).obj E))
      ((hEm j).some.symm ≪≫
        (Gj.mapDerivedCategoryFactors.app T).symm ≪≫ Gj.mapDerivedCategory.mapIso e.symm)
      (Stacks.ModuleSheaf.hasTorAmplitude_constantSheaf_of_flat (J := (J.over (W j))) E aE bE
        fun n => inferInstance)

/-- Restriction of sheaves of modules to a slice of `X_proét` is additive. -/
theorem additive_overPullback_moduleCat (R : Type (max (u + 1) w)) [CommRing R] (V : X.ProEt) :
    ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) w} R) V).Additive :=
  let := Stacks.ModuleSheaf.preservesFiniteLimits_overPullback (Scheme.ProEt.topology X) R V
  Functor.additive_of_preserves_binary_products _

/-- **The coefficients of a uniform constant model of a reduction are the reduction of a
fibre.** Let `P` be a K-flat complex representing `K`, `𝔞 ⊆ Λ` an ideal, and suppose that over
the members `W j` of a covering of the final object of `X_proét` the reduction
`K ⊗_Λ^L \underline{Λ/𝔞}`, represented by a complex `T`, is isomorphic to the constant complex
`\underline{E}` of one complex `E`. Then `E ≅ Λ/𝔞 ⊗_Λ N` in `D(Λ/𝔞)`, where `N` is the fibre of
`P` at any point `p` of `X_proét` with nonempty fibre at the final object. -/
theorem nonempty_iso_extendScalars_sheafFiber_of_cover (𝔞 : Ideal Λ)
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (eP : DerivedCategory.Q.obj P ≅ (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)
    (hP : CochainComplex.KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) P)
    (p : (Scheme.ProEt.topology X).Point.{max (u + 1) w})
    (hp : Nonempty (p.fiber.obj (Scheme.ProEt.mk (𝟙 X))))
    {T : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (Λ ⧸ 𝔞))) ℤ}
    (eT : (derivedReduction.{u, w} X Λ 𝔞).obj K ≅ DerivedCategory.Q.obj T)
    (E : CochainComplex (ModuleCat.{max (u + 1) w} (Λ ⧸ 𝔞)) ℤ)
    {ι : Type*} (W : ι → X.ProEt) (g : ∀ j, W j ⟶ Scheme.ProEt.mk (𝟙 X))
    (hW : Sieve.ofArrows W g ∈ Scheme.ProEt.topology X (Scheme.ProEt.mk (𝟙 X)))
    (hWm : ∀ j, Nonempty (DerivedCategory.Q.obj
      ((((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) w} (Λ ⧸ 𝔞))
        (W j)).mapHomologicalComplex (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj (((constantSheaf ((Scheme.ProEt.topology X).over (W j))
        (ModuleCat.{max (u + 1) w} (Λ ⧸ 𝔞))).mapHomologicalComplex (ComplexShape.up ℤ)).obj E))) :
    Nonempty (DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{max (u + 1) w, max (u + 1) w, max (u + 1) w}
        (Ideal.Quotient.mk 𝔞)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Stacks.ModuleSheaf.moduleSheafFiber Λ p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P))) := by
  let J := Scheme.ProEt.topology X
  let R := Λ ⧸ 𝔞
  let A := ModuleCat.{max (u + 1) w} R
  let f : Λ →+* R := Ideal.Quotient.mk 𝔞
  let PE := ((Stacks.ModuleSheaf.extendScalars J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let eTP : DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj PE :=
    eT.symm ≪≫ (Stacks.ModuleSheaf.derivedExtendScalars J f).mapIso eP.symm ≪≫
      Stacks.ModuleSheaf.derivedExtendScalarsObjIso J f hP
  have : (ModuleCat.extendScalars.{max (u + 1) w, max (u + 1) w, max (u + 1) w} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max (u + 1) w} f).left_adjoint_additive
  obtain ⟨x₀⟩ := hp
  obtain ⟨j, x, -⟩ := p.fiber_jointly_surjective_of_ofArrows g hW x₀
  obtain ⟨eW⟩ := hWm j
  let G := J.overPullback A (W j)
  have := additive_overPullback_moduleCat R (W j)
  let c := constantSheaf (J.over (W j)) A
  have : LocallySmall.{max (u + 1) w} (Over (W j)) :=
    CategoryTheory.locallySmall_max.{max (u + 1) w, u, u + 1}
  obtain ⟨e₁⟩ := Stacks.ModuleSheaf.nonempty_iso_sheafFiber_of_iso_constantSheaf (p.over x)
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj T) (DerivedCategory.Q.obj E)
    (eW ≪≫ (c.mapDerivedCategoryFactors.app E).symm)
  let St := Stacks.ModuleSheaf.moduleSheafFiber R p
  let St' := Stacks.ModuleSheaf.moduleSheafFiber R (p.over x)
  let eOver : G ⋙ St' ≅ St := p.sheafFiberOverIso x A
  exact ⟨e₁ ≪≫ DerivedCategory.Q.mapIso
    (((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ St')) (ComplexShape.up ℤ)).app T).symm ≪≫
      (NatIso.mapHomologicalComplex eOver (ComplexShape.up ℤ)).app T) ≪≫
    (St.mapDerivedCategoryFactors.app T).symm ≪≫ St.mapDerivedCategory.mapIso eTP ≪≫
    St.mapDerivedCategoryFactors.app PE ≪≫ DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app P ≪≫
        (NatIso.mapHomologicalComplex (Stacks.ModuleSheaf.sheafFiberExtendScalarsIso p f)
          (ComplexShape.up ℤ)).app P ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app P).symm)⟩

/-- **The first reduction of a fibre is perfect.** Let `X` be connected, `K` a constructible
object of `D(X_proét, Λ)` whose first reduction has locally constant cohomology sheaves, `P` a
K-flat complex representing `K` and `p` a point of `X_proét` with nonempty fibre at the final
object. Then `Λ/I ⊗_Λ N` is a perfect object of `D(Λ/I)`, for `N` the fibre of `P` at `p`. -/
theorem isPerfect_extendScalars_sheafFiber [ConnectedSpace X] [IsNoetherianRing Λ]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hloc : ∀ i : ℤ, Stacks.ConstantSheaf.IsLocallyConstant (Scheme.ProEt.topology X)
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K)))
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (eP : DerivedCategory.Q.obj P ≅ (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)
    (hP : CochainComplex.KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) P)
    (p : (Scheme.ProEt.topology X).Point.{max (u + 1) w})
    (hp : Nonempty (p.fiber.obj (Scheme.ProEt.mk (𝟙 X)))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{max (u + 1) w, max (u + 1) w, max (u + 1) w}
        (Ideal.Quotient.mk I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Stacks.ModuleSheaf.moduleSheafFiber Λ p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P))) := by
  let J := Scheme.ProEt.topology X
  let A := ModuleCat.{max (u + 1) w} (Λ ⧸ I)
  let L := (derivedReduction.{u, w} X Λ I).obj K
  have hlc := isFiniteTypeLocallyConstantModuleSheaf_homology_derivedReduction hK hloc
  obtain ⟨a₀, b₀, hGE, hLE⟩ := exists_isGE_isLE_derivedReduction_of_connectedSpace hK hlc
  let KB : DerivedCategory.Bounded (Sheaf J A) := ⟨L, ⟨⟨a₀, hGE⟩, ⟨b₀, hLE⟩⟩⟩
  obtain ⟨T, e, E, a, b, hEv, hEfg, hcov⟩ :=
    Scheme.ProEt.exists_uniform_constantComplex_representation_of_connectedSpace.{u, w} (Λ ⧸ I)
      KB hlc
  obtain ⟨ι, W, g, hW, hWm⟩ := hcov (Scheme.ProEt.mk (𝟙 X))
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨_, _, ⟨j₀⟩, ⟨w₀⟩⟩ := exists_mem_presieve_nonempty_left hW x₀
  obtain ⟨eN⟩ := nonempty_iso_extendScalars_sheafFiber_of_cover I eP hP p hp e E W g hW
    fun j => (hWm j).2
  exact StacksDraft.Perfect.isPerfect_of_iso eN.symm
    (isPerfect_of_overPullback_iso_constantSheaf hK e E a b hEv hEfg w₀ (hWm j₀).2)

/-- **One coefficient complex for every reduction over a connected scheme.** Let `X` be
connected, `K` a constructible object of `D(X_proét, Λ)` whose first reduction has locally
constant cohomology sheaves, `P` a K-flat complex representing `K` and `p` a point of `X_proét`
with nonempty fibre at the final object. Then every reduction `Λ/Iⁿ⁺¹ ⊗_Λ P` is, over the members
of a covering of any object, isomorphic to the constant complex of `Λ/Iⁿ⁺¹ ⊗_Λ N`, where `N` is
the fibre of `P` at `p`. -/
theorem exists_cover_reduction_iso_constantSheaf_sheafFiber [ConnectedSpace X] [IsNoetherianRing Λ]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hloc : ∀ i : ℤ, Stacks.ConstantSheaf.IsLocallyConstant (Scheme.ProEt.topology X)
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K)))
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (eP : DerivedCategory.Q.obj P ≅ (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)
    (hP : CochainComplex.KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) P)
    (p : (Scheme.ProEt.topology X).Point.{max (u + 1) w})
    (hp : Nonempty (p.fiber.obj (Scheme.ProEt.mk (𝟙 X)))) (n : ℕ) (U : X.ProEt) :
    ∃ (ι : Type (u + 1)) (W : ι → X.ProEt) (g : ∀ j, W j ⟶ U),
      Sieve.ofArrows W g ∈ Scheme.ProEt.topology X U ∧ ∀ j, Nonempty (DerivedCategory.Q.obj
        ((((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1)))
          (W j)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
              (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                P)) ≅
        DerivedCategory.Q.obj (((constantSheaf ((Scheme.ProEt.topology X).over (W j))
          (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1)))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars.{max (u + 1) w, max (u + 1) w, max (u + 1) w}
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((Stacks.ModuleSheaf.moduleSheafFiber Λ p).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)))) := by
  classical
  let J := Scheme.ProEt.topology X
  let Rn := Λ ⧸ I ^ (n + 1)
  let A := ModuleCat.{max (u + 1) w} Rn
  let f : Λ →+* Rn := Ideal.Quotient.mk (I ^ (n + 1))
  let E := derivedModuleEquiv.{u, max (u + 1) w, w} X Λ
  let K' := E.inverse.obj K
  have hlc := isFiniteTypeLocallyConstantModuleSheaf_homology_derivedReduction hK hloc
  obtain ⟨a, b, hab⟩ := exists_hasTorAmplitude_derivedReduction_of_connectedSpace hK hlc
  obtain ⟨⟨-, hzero⟩, hampl⟩ :=
    isDerivedLimit_derivedReductionTower_and_hasTorAmplitude_of_hasTorAmplitude X Λ I hK hab
  have hK'le : K'.IsLE b := by
    let Ec := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
    let : Ec.functor.Additive := Functor.additive_of_preserves_binary_products _
    rw [DerivedCategory.isLE_iff]
    intro i hi
    have h₁ : IsZero ((DerivedCategory.homologyFunctor _ i).obj (E.functor.obj K')) :=
      (hzero i fun h => hi.not_ge h.2).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso (E.counitIso.app K))
    have h₂ : IsZero (Ec.functor.obj ((DerivedCategory.homologyFunctor _ i).obj K')) :=
      h₁.of_iso ((Ec.functor.mapDerivedCategoryHomologyIso i).app K').symm
    exact (Ec.inverse.map_isZero h₂).of_iso (Ec.unitIso.app _)
  let Ln := (derivedReduction.{u, w} X Λ (I ^ (n + 1))).obj K
  have hlcn : ∀ i : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, w}
      J Rn ((DerivedCategory.homologyFunctor _ i).obj Ln) :=
    isFiniteTypeLocallyConstantModuleSheaf_homology_derivedExtendScalars_pow X Λ I K' b hlc
      (n + 1) (by omega)
  obtain ⟨hGE, hLE⟩ := (hampl (n + 1)).isGE_isLE
  let KB : DerivedCategory.Bounded (Sheaf J A) := ⟨Ln, ⟨⟨a, hGE⟩, ⟨b, hLE⟩⟩⟩
  obtain ⟨T, eT, Pn, -, -, -, -, hcov⟩ :=
    Scheme.ProEt.exists_uniform_constantComplex_representation_of_connectedSpace.{u, w} Rn KB hlcn
  let PE := ((Stacks.ModuleSheaf.extendScalars J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let eTP : DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj PE :=
    eT.symm ≪≫ (Stacks.ModuleSheaf.derivedExtendScalars J f).mapIso eP.symm ≪≫
      Stacks.ModuleSheaf.derivedExtendScalarsObjIso J f hP
  obtain ⟨ι₀, W₀, g₀, hW₀, hWm₀⟩ := hcov (Scheme.ProEt.mk (𝟙 X))
  obtain ⟨ePN⟩ := nonempty_iso_extendScalars_sheafFiber_of_cover (I ^ (n + 1)) eP hP p hp eT Pn
    W₀ g₀ hW₀ fun j => (hWm₀ j).2
  obtain ⟨ι, W, g, hW, hWm⟩ := hcov U
  refine ⟨ι, W, g, hW, fun j => ?_⟩
  obtain ⟨eW⟩ := (hWm j).2
  let G := J.overPullback A (W j)
  have := additive_overPullback_moduleCat Rn (W j)
  let c := constantSheaf (J.over (W j)) A
  exact ⟨(G.mapDerivedCategoryFactors.app PE).symm ≪≫ G.mapDerivedCategory.mapIso eTP.symm ≪≫
    G.mapDerivedCategoryFactors.app T ≪≫ eW ≪≫ (c.mapDerivedCategoryFactors.app Pn).symm ≪≫
    c.mapDerivedCategory.mapIso ePN ≪≫ c.mapDerivedCategoryFactors.app _⟩

variable (X Λ I) in
/-- **An adic model of the reductions over a connected scheme.** Let `X` be connected, `Λ`
Noetherian, `K` a constructible object of `D(X_proét, Λ)` whose first reduction has locally
constant cohomology sheaves, and `P` a K-flat complex representing `K`. There is a bounded complex
`M` of finite projective modules over the completion `Λ^∧` such that every reduction
`Λ/Iⁿ⁺¹ ⊗_Λ P` is, over the members of a covering of any object, isomorphic to the constant
complex of `Λ/Iⁿ⁺¹ ⊗_{Λ^∧} M`. The isomorphisms need not be compatible as `n` varies. -/
theorem exists_adicModel_cover_reduction_iso_of_connectedSpace [ConnectedSpace X]
    [IsNoetherianRing Λ]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hloc : ∀ i : ℤ, Stacks.ConstantSheaf.IsLocallyConstant (Scheme.ProEt.topology X)
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K)))
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (eP : DerivedCategory.Q.obj P ≅ (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)
    (hP : CochainComplex.KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) P) :
    ∃ (a b : ℤ) (M : CochainComplex (ModuleCat.{max (u + 1) w} (AdicCompletion I Λ)) ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
      (∀ k : ℤ, Module.Finite (AdicCompletion I Λ) (M.X k) ∧
        Module.Projective (AdicCompletion I Λ) (M.X k)) ∧
      ∀ (n : ℕ) (U : X.ProEt), ∃ (ι : Type (u + 1)) (W : ι → X.ProEt) (g : ∀ j, W j ⟶ U),
        Sieve.ofArrows W g ∈ Scheme.ProEt.topology X U ∧ ∀ j, Nonempty (DerivedCategory.Q.obj
          ((((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1)))
            (W j)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
                (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  P)) ≅
          DerivedCategory.Q.obj (((constantSheaf ((Scheme.ProEt.topology X).over (W j))
            (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1)))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{max (u + 1) w, max (u + 1) w, max (u + 1) w}
              (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M))) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨p, hp⟩ := Scheme.ProEt.exists_point_nonempty_fiber_obj.{u, w}
    (show (Scheme.ProEt.mk (𝟙 X)).left from x₀)
  let N := ((Stacks.ModuleSheaf.moduleSheafFiber Λ p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  have hN : ∀ n : ℕ, CochainComplex.KFlat.{max (u + 1) w, max (u + 1) w}
      (((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N) := fun n =>
    kFlat_baseChange _ _
      ((CochainComplex.kFlat_iff_kFlatBifunctor N).2 (Stacks.ModuleSheaf.kFlat_sheafFiber p hP))
  have hN₀ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (0 + 1)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)) := by
    rw [zero_add, pow_one]
    exact isPerfect_extendScalars_sheafFiber hK hloc eP hP p hp
  obtain ⟨M, a, b, hGE, hLE, hM, hMN⟩ :=
    StacksDraft.DerivedInverseLimit.exists_finiteProjective_adicCompletion_iso I N hN hN₀
  refine ⟨a, b, M, hGE, hLE, hM, fun n U => ?_⟩
  obtain ⟨ι, W, g, hW, hWm⟩ :=
    exists_cover_reduction_iso_constantSheaf_sheafFiber hK hloc eP hP p hp n U
  refine ⟨ι, W, g, hW, fun j => ?_⟩
  let c := constantSheaf ((Scheme.ProEt.topology X).over (W j))
    (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1)))
  exact ⟨(hWm j).some ≪≫ (c.mapDerivedCategoryFactors.app _).symm ≪≫
    c.mapDerivedCategory.mapIso (hMN n).some.symm ≪≫ c.mapDerivedCategoryFactors.app _⟩

/-- Let `X` be a connected scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. If `K` is in
`D_cons(X, Λ)` and `K ⊗_Λ^L \underline{Λ/I}` has locally constant cohomology sheaves, then `K` is
adic lisse. -/
@[stacks 09C6 "a constructible complex over a connected scheme whose reduction modulo I has \
locally constant cohomology sheaves is adic lisse"]
theorem isAdicLisseDerivedSheaf_of_isLocallyConstant [ConnectedSpace X] [IsNoetherianRing Λ]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hloc : ∀ i : ℤ, Stacks.ConstantSheaf.IsLocallyConstant (Scheme.ProEt.topology X)
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K))) :
    IsAdicLisseDerivedSheaf.{u, max (u + 1) w, w} X Λ I K := by
  classical
  let J := Scheme.ProEt.topology X
  let A := AdicCompletion I Λ
  let K' := (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K
  obtain ⟨P, p, hP, hp⟩ :=
    Stacks.ModuleSheaf.exists_kFlat_quasiIso (DerivedCategory.Q.objPreimage K')
  let eP : DerivedCategory.Q.obj P ≅ K' :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K'
  obtain ⟨a, b, M, hMa, hMb, hM, hcov⟩ :=
    exists_adicModel_cover_reduction_iso_of_connectedSpace X Λ I hK hloc eP hP
  refine ⟨a, b, M, hMa, hMb, hM, fun U => ?_⟩
  obtain ⟨ι, V, g, hV, hVc⟩ := Scheme.ProEt.hasEnoughObjects_isAffineWContractible U
  refine ⟨ULift.{u + 1} ι, fun j => V j.down, fun j => g j.down, ?_, fun j => ?_⟩
  · refine (Scheme.ProEt.topology X).superset_covering ?_ hV
    rintro Z f ⟨Y, h, k, hk, rfl⟩
    rcases hk with ⟨i⟩
    exact ⟨_, h, _, Presieve.ofArrows.mk (ULift.up i), rfl⟩
  · let W := V j.down
    have hW := hVc j.down
    have : IsAffine W.left := hW.1
    have : CochainComplex.IsStrictlyGE M a := hMa
    have : CochainComplex.IsStrictlyLE M b := hMb
    let PW := ((J.overPullback (ModuleCat.{max (u + 1) w} Λ) W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P
    have hα : ∀ n : ℕ, Nonempty (DerivedCategory.Q.obj
        (((Stacks.ModuleSheaf.extendScalars (J.over W)
          (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj PW) ≅
      DerivedCategory.Q.obj (((constantSheaf (J.over W)
          (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1)))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M))) := fun n => by
      let Rn := Λ ⧸ I ^ (n + 1)
      let f : Λ →+* Rn := Ideal.Quotient.mk (I ^ (n + 1))
      let g := (AdicCompletion.evalₐ I (n + 1)).toRingHom
      let N := ((ModuleCat.extendScalars.{max (u + 1) w, max (u + 1) w, max (u + 1) w}
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
      have : (ModuleCat.extendScalars.{max (u + 1) w, max (u + 1) w, max (u + 1) w} g).Additive :=
        (ModuleCat.extendRestrictScalarsAdj.{max (u + 1) w} g).left_adjoint_additive
      have : CochainComplex.IsStrictlyLE N b :=
        Stacks.ModuleSheaf.isStrictlyLE_mapHomologicalComplex _ M b
      have hN : ∀ k, Module.Projective Rn (N.X k) := fun k => by
        have : (ModuleCat.restrictScalars.{max (u + 1) w} g).PreservesEpimorphisms :=
          ⟨fun φ hφ => (ModuleCat.epi_iff_surjective _).2 ((ModuleCat.epi_iff_surjective φ).1 hφ)⟩
        exact (IsProjective.iff_projective _).2
          ((ModuleCat.extendRestrictScalarsAdj.{max (u + 1) w} g).map_projective _
            ((IsProjective.iff_projective _).1 (hM k).2))
      let PE :=
        ((Stacks.ModuleSheaf.extendScalars J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
      have hlocn : ∀ U : X.ProEt, ∃ (ι : Type (u + 1)) (W : ι → X.ProEt) (g : ∀ j, W j ⟶ U),
          Sieve.ofArrows W g ∈ J U ∧ ∀ j, Nonempty
            ((J.overPullback (ModuleCat.{max (u + 1) w} Rn) (W j)).mapDerivedCategory.obj
              (DerivedCategory.Q.obj PE) ≅
            DerivedCategory.Q.obj (((constantSheaf (J.over (W j))
              (ModuleCat.{max (u + 1) w} Rn)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj N)) := by
        intro U
        obtain ⟨ι, W', g', hW', he⟩ := hcov n U
        refine ⟨ι, W', g', hW', fun j => ?_⟩
        have := additive_overPullback_moduleCat Rn (W' j)
        exact ⟨((J.overPullback (ModuleCat.{max (u + 1) w} Rn)
          (W' j)).mapDerivedCategoryFactors.app PE) ≪≫ (he j).some⟩
      obtain ⟨eV⟩ := nonempty_overPullback_iso_constantSheaf_of_isAffineWContractible
        (DerivedCategory.Q.obj PE) N b hN hlocn W hW
      have := additive_overPullback_moduleCat Rn W
      let G := J.overPullback (ModuleCat.{max (u + 1) w} Rn) W
      let eC := ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app P) ≪≫
        (NatIso.mapHomologicalComplex (Stacks.ModuleSheaf.overPullbackCompExtendScalarsIso J f W)
          (ComplexShape.up ℤ)).app P ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app P).symm
      exact ⟨DerivedCategory.Q.mapIso eC ≪≫ (G.mapDerivedCategoryFactors.app PE).symm ≪≫ eV⟩
    obtain ⟨φ⟩ := Stacks.ModuleSheaf.nonempty_derivedReductionTower_iso_of_isWeaklyContractible I
      (T := Over.mk (𝟙 W)) Over.mkIdTerminal
      (fun φ hφ => Scheme.ProEt.surjective_app_over_of_isWContractible W hW.2 φ hφ)
      (Stacks.ModuleSheaf.kFlat_overPullback W hP) M a b hM hα
    obtain ⟨φ'⟩ := nonempty_reductionTower_iso_of_overPullback_iso X Λ I K eP hP W M φ
    exact nonempty_overRestrictionDerived_iso_of_reductionTower_iso X Λ I K hK.1 W M φ'

end Connected

end AlgebraicGeometry.ProEtale

end
