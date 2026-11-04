module

public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFibreBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyUniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent

/-!
# The fibre square of a morphism of `Coh_{X/B}` and the twisted Euler characteristic

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `L` an invertible
`𝒪_X`-module and `m : (T, 𝓕) ⟶ (T', 𝓕')` a morphism of `Coh_{X/B}` with underlying morphism
`h : T ⟶ T'`.  For a point `t ∈ T` the fibre `X_t` is the base change of `X_{h(t)}` along
`Spec κ(t) ⟶ Spec κ(h(t))`, and the twisted module `𝓕_t ⊗ L_t^{⊗ n}` is the pullback of
`𝓕'_{h(t)} ⊗ L_{h(t)}^{⊗ n}`.  Comparing the twisted Euler characteristics of `(T, 𝓕)` at `t`
and of `(T', 𝓕')` at `h(t)` is therefore flat base change of cohomology (Stacks 073K, part (2))
for this cartesian square.  This file verifies the hypotheses of that statement for the square:

* the lower horizontal morphism `Spec κ(t) ⟶ Spec κ(h(t))` is flat;
* the right vertical morphism `X_{h(t)} ⟶ Spec κ(h(t))` is quasi-compact and quasi-separated,
  being a base change of `f`;
* the twisted module `𝓕'_{h(t)} ⊗ L_{h(t)}^{⊗ n}` is quasi-coherent.

It also rewrites the twisted Euler characteristic through the cohomology of `𝒪`-modules whose
sections lie in the universe of the structure rings, the form in which flat base change of
cohomology is stated.

## Main results

* `ModuleCat.finrank_restrictScalars_uliftFunctor`: the universe lift of modules does not change
  dimensions.
* `AlgebraicGeometry.Space.eulerCharacteristicAlong_eq_finsum_rightDerived`: the Euler
  characteristic of a module computed with the cohomology of the module itself rather than of
  its universe lift.
* `AlgebraicGeometry.Space.CoherentSituation.isQuasiCompact_projection` and
  `AlgebraicGeometry.Space.CoherentSituation.isQuasiSeparated_projection`: the projection
  `X_T ⟶ T` is quasi-compact and quasi-separated.
* `AlgebraicGeometry.Space.CoherentHom.isFlat_pointSchemeMap`: the morphism
  `Spec κ(t) ⟶ Spec κ(h(t))` is flat.
* `AlgebraicGeometry.Space.CoherentObject.isQuasicoherentOnSite_fibreModule` and
  `AlgebraicGeometry.Space.CoherentObject.isQuasicoherentOnSite_fibreTwistedModule`: the fibre
  `𝓕_t` and the twisted module `𝓕_t ⊗ (L^{⊗ n})_t` are quasi-coherent.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Stacks.Cohomology.SiteModules

universe u

/-- Restricting scalars along `ψ : k ⟶ R` commutes with the universe lift of modules up to a
`k`-linear equivalence, so the lift does not change dimensions over `k`. -/
theorem ModuleCat.finrank_restrictScalars_uliftFunctor {R : Type*} [Ring R] {k : Type*} [Ring k]
    (ψ : k →+* R) (N : ModuleCat.{u + 1} R) :
    Module.finrank k ((ModuleCat.restrictScalars ψ).obj
        ((ModuleCat.uliftFunctor.{u + 1} R).obj N)) =
      Module.finrank k ((ModuleCat.restrictScalars ψ).obj N) :=
  LinearEquiv.finrank_eq
    { toFun := fun x => ULift.down (show ULift.{u + 1} N from x)
      invFun := fun x => (show ULift.{u + 1} N from ULift.up x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

section Cohomology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

attribute [local instance] hasInjectiveResolutions_modules

/-- The `i`-th cohomology of the universe lift of an `𝒪_F`-module is the universe lift of its
`i`-th cohomology, as modules over `Γ(F, 𝒪_F)`
(`Stacks.Cohomology.SiteModules.rightDerivedGlobalSectionsUliftIso` on the small étale ringed
site). -/
def globalModuleCohomologyUliftIso (M : Modules.{u, u} B S hS F hF) (i : ℕ) :
    (globalModuleCohomology.{u + 1, u, u, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) i).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} M) ≅
      (ModuleCat.uliftFunctor.{u + 1} _).obj (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).rightDerived
          i).obj M) := by
  have := hasSeparator_modules B S hS F hF
  have := site_hasSheafify_addCommGrp.{u + 1, u, u + 1}
    (J := (smallEtaleRingedSite B S hS F hF).J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, u + 1}
    (J := (smallEtaleRingedSite B S hS F hF).J)
  have := moduleSheavesEnoughInjectives.{u + 1, u, u, u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  exact ((rightDerivedGlobalSectionsUliftIso.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) i).app M).symm

/-- **The Euler characteristic through the cohomology of the module itself.**  The alternating
sum `∑ᵢ (-1)ⁱ dim_k Hⁱ(F, M)` of `AlgebraicGeometry.Space.eulerCharacteristicAlong`, which is
taken with the cohomology of the universe lift of `M`, is the same sum taken with the right
derived functors of global sections at `M`. -/
theorem eulerCharacteristicAlong_eq_finsum_rightDerived (k : Type u) [Field k]
    (ψ : k →+* GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (M : Modules.{u, u} B S hS F hF) :
    eulerCharacteristicAlong B S hS F hF k ψ M =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k
        ((ModuleCat.restrictScalars ψ).obj
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS F hF).O)).rightDerived i).obj M)) : ℤ) := by
  unfold eulerCharacteristicAlong
  congr 1
  funext i
  congr 2
  rw [LinearEquiv.finrank_eq
    ((ModuleCat.restrictScalars ψ).mapIso
      (globalModuleCohomologyUliftIso B S hS F hF M i)).toLinearEquiv]
  exact ModuleCat.finrank_restrictScalars_uliftFunctor ψ _

end Cohomology

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **The projection `X_T ⟶ T` is quasi-compact**, being a base change of the quasi-compact
morphism `f : X ⟶ Y` (Stacks 03HF). -/
theorem isQuasiCompact_projection (T : SchemesOver D.Y) :
    IsQuasiCompact B S hS (D.projection T).hom :=
  isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback D.f.hom T.hom.hom)
    D.finitePresentation.2.1

/-- **The projection `X_T ⟶ T` is quasi-separated**, being a base change of the
quasi-separated morphism `f : X ⟶ Y`. -/
theorem isQuasiSeparated_projection (T : SchemesOver D.Y) :
    IsQuasiSeparated B S hS (D.projection T).hom :=
  isQuasiSeparated_of_isPullback B S hS (IsPullback.of_hasPullback D.f.hom T.hom.hom)
    D.finitePresentation.2.2

end CoherentSituation

namespace CoherentHom

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {A A' : CoherentObject D}

/-- **The morphism `Spec κ(t) ⟶ Spec κ(h(t))` is flat**: it is the spectrum of a homomorphism of
fields, and every module over a field is flat. -/
theorem isFlat_pointSchemeMap (m : CoherentHom A A') (t : A.testScheme) :
    IsFlat B S hS ((schemeSpaceFunctor B S hS).map (m.pointSchemeMap t)).hom := by
  refine isFlat_yoneda_map B S hS (m.pointSchemeMap t) ?_
  change Flat (Spec.map (m.baseScheme.residueFieldMap t))
  rw [Flat.SpecMap_iff]
  algebraize [(m.baseScheme.residueFieldMap t).hom]
  exact (RingHom.flat_algebraMap_iff).2 inferInstance

end CoherentHom

namespace CoherentObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- **The fibre `𝓕_t` of an object of `Coh_{X/B}` is quasi-coherent**: it is the pullback of a
quasi-coherent module (Stacks 03GA). -/
theorem isQuasicoherentOnSite_fibreModule (A : CoherentObject D) (t : A.testScheme) :
    (A.fibreModule t).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ A.F A.quasicoherent

/-- **The twisted module `𝓕_t ⊗ M_t` is quasi-coherent** for every invertible `𝒪_X`-module `M`:
the pullback `M_t` is invertible, hence quasi-coherent, and a tensor product of quasi-coherent
modules is quasi-coherent (Stacks 03M1). -/
theorem isQuasicoherentOnSite_fibreTwistedModule (A : CoherentObject D) (t : A.testScheme)
    (M : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property M] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj
        (A.fibreModule t)).obj
      ((modulePullback B S hS
        (baseChangeProjection D.f (A.pointTest t))).obj M)).IsQuasicoherentOnSite := by
  have := A.isQuasicoherentOnSite_fibreModule t
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (baseChangeProjection D.f (A.pointTest t)) M
    (isQuasicoherentOnSite_of_isInvertible B S hS D.X M
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ ‹_›))
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (modulesTensorObjIso B S hS (A.fibreSpace t).1 (A.fibreSpace t).2 _ _)
    (isQuasicoherentOnSite_tensorObj B S hS (A.fibreSpace t).1 (A.fibreSpace t).2 _ _)

end CoherentObject

end AlgebraicGeometry.Space

end
