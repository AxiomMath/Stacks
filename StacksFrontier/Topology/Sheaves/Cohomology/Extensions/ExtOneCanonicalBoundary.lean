module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExact
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Extensions.FirstCohomologyAndExtensions
import StacksCore.Tactic.StacksAttribute

/-!
# First extensions of the structure sheaf and the boundary map of cohomology

Let `(X, O_X)` be a ringed space and `F` a sheaf of `O_X`-modules. This file constructs the
canonical bijection `Ext^1_{Mod(O_X)}(O_X, F) → H^1(X, F)` of [Stacks, Tag 0B3A] and proves that
it sends the class of an extension `0 → F → E → O_X → 0` to the image of `1 ∈ Γ(X, O_X)` under
the boundary map `H^0(X, O_X) → H^1(X, F)` of the long exact cohomology sequence of that
extension.

The boundary map is the canonical one: the cohomology `H^n(X, -)` of Tag 01E3 is the right
derived functor `(secF R ⊤).rightDerived n` of global sections, and its long exact sequence is
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (secF R ⊤)`, whose connecting
morphisms come from the distinguished triangle of a short exact sequence in the derived category.

## Main definitions

* `Stacks.Cohomology.SpaceModules.liftedCohomologyDeltaFunctor`: the canonical cohomological
  `δ`-functor `H^*(X, -)`, pushed one universe up so that it can be compared with `Ext`.
* `Stacks.Cohomology.SpaceModules.extLiftedCohomologyDeltaIso`: the isomorphism of
  `δ`-functors `Ext^*(O_X, -) ≅ H^*(X, -)` extending `Hom(O_X, -) = Γ(X, -)` in degree zero.
* `Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomologyCanonical`: its degree-one part,
  the additive equivalence `Ext^1(O_X, F) ≃+ H^1(X, F)`.

## Main results

* `Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomologyCanonical_extClass`: the class of an
  extension goes to the canonical boundary of `1`.
* `Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomologyCanonical_unique`: that formula
  determines the equivalence.
* `Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomologyCanonical_naturality`: the
  equivalence is natural in the coefficient module sheaf.

## Implementation notes

Both `n ↦ Ext^n(O_X, -)` (`Stacks.Cohomology.SiteModules.extDeltaFunctorForUnit`) and the
canonical cohomology `δ`-functor vanish on injectives in positive degrees, so they are universal
([Stacks, Tag 010T]) and the isomorphism `Ext^0(O_X, -) = Hom(O_X, -) = Γ(X, -) = H^0(X, -)`
extends uniquely to an isomorphism of `δ`-functors ([Stacks, Tag 010U]). Its compatibility with
the connecting maps, evaluated on `id_{O_X} ∈ Ext^0(O_X, O_X)`, is the boundary formula.

`Ext` groups of sheaves of modules in universe `u` live in universe `u + 1`, so the cohomology
`δ`-functor is composed with the exact functor `AddCommGrpCat.uliftFunctor`.

## References

* [Stacks Project, Tag 0B3A](https://stacks.math.columbia.edu/tag/0B3A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.SpaceModules

attribute [local instance] HasExt.standard

variable {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u} R)] [HasDerivedCategory AddCommGrpCat.{u}]

/-- The canonical cohomological `δ`-functor `n ↦ H^n(X, -)` of a ringed space, the right
derived functors of global sections with the connecting maps of their long exact sequence,
composed with `ULift` into abelian groups one universe up. -/
def liftedCohomologyDeltaFunctor :
    DeltaFunctor (SheafOfModules.{u} R) AddCommGrpCat.{u + 1} :=
  (DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (secF R ⊤)).mapExact
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- Higher cohomology vanishes on injectives, so the lifted cohomology `δ`-functor is
universal. -/
theorem liftedCohomologyDeltaFunctor_isUniversal :
    (liftedCohomologyDeltaFunctor R).IsUniversal := by
  apply DeltaFunctor.isUniversal_of_isZero_injective
  intro n I hI
  exact Functor.map_isZero AddCommGrpCat.uliftFunctor.{u + 1, u}
    (Functor.isZero_rightDerived_obj_injective_succ (secF R ⊤) n I)

/-- In degree zero both `δ`-functors are global sections:
`Ext^0(O_X, -) = Hom(O_X, -) = Γ(X, -) = H^0(X, -)`. -/
def extLiftedCohomologyZeroIso :
    (SiteModules.extDeltaFunctorForUnit R).functor 0 ≅
      (liftedCohomologyDeltaFunctor R).functor 0 := by
  have := SiteModules.globalSectionsFunctor_preservesFiniteLimits R
  have : PreservesFiniteLimits
      (SiteModules.globalSectionsFunctor R ⋙ forgetGlobalSectionsModule R) :=
    Limits.comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (secF R ⊤) :=
    preservesFiniteLimits_of_natIso (globalSectionsIsoSectionsTop R)
  exact SiteModules.extZeroIsoCoyoneda R ≪≫ SiteModules.unitCoyonedaSectionsIso R ≪≫
    Functor.isoWhiskerRight (globalSectionsIsoSectionsTop R)
      AddCommGrpCat.uliftFunctor.{u + 1, u} ≪≫
    Functor.isoWhiskerRight (asIso (secF R ⊤).toRightDerivedZero)
      AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The isomorphism of universal `δ`-functors `Ext^*(O_X, -) ≅ H^*(X, -)` extending the
identification in degree zero. -/
def extLiftedCohomologyDeltaIso :
    SiteModules.extDeltaFunctorForUnit R ≅ liftedCohomologyDeltaFunctor R := by
  have := SiteModules.extDeltaFunctorForUnit_isUniversal R
  have := liftedCohomologyDeltaFunctor_isUniversal R
  exact DeltaFunctor.IsUniversal.isoOfIso (extLiftedCohomologyZeroIso R)

/-- **Stacks 0B3A.** For a ringed space `(X, O_X)` and a sheaf of `O_X`-modules `F`, the
canonical bijection `Ext^1_{Mod(O_X)}(O_X, F) → H^1(X, F)`, an isomorphism of abelian groups. -/
@[stacks 0B3A "the canonical bijection, as an isomorphism of abelian groups"]
def extOneEquivFirstCohomologyCanonical (M : SheafOfModules.{u} R) :
    Abelian.Ext (SheafOfModules.unit R) M 1 ≃+ Hgroup R ⊤ 1 M :=
  (Iso.addCommGroupIsoToAddEquiv
    ((SiteModules.deltaFunctorEvalOne R M).mapIso (extLiftedCohomologyDeltaIso R))).trans
    AddEquiv.ulift.{u, u + 1}

/-- The equivalence is the degree-one component of the comparison of `δ`-functors. -/
theorem extOneEquivFirstCohomologyCanonical_apply (M : SheafOfModules.{u} R)
    (ξ : Abelian.Ext (SheafOfModules.unit R) M 1) :
    extOneEquivFirstCohomologyCanonical R M ξ =
      (((extLiftedCohomologyDeltaIso R).hom.app 1).app M ξ).down :=
  rfl

/-- The degree-zero comparison sends `id_{O_X} ∈ Ext^0(O_X, O_X)` to the class of
`1 ∈ Γ(X, O_X)` in `H^0(X, O_X)`. -/
theorem extLiftedCohomologyDeltaIso_hom_app_zero_mk₀_id :
    (((extLiftedCohomologyDeltaIso R).hom.app 0).app (SheafOfModules.unit R))
        (Ext.mk₀ (𝟙 (SheafOfModules.unit R))) =
      ULift.up (oneCohomologyClass R) := by
  have := SiteModules.extDeltaFunctorForUnit_isUniversal R
  have := liftedCohomologyDeltaFunctor_isUniversal R
  have h0 : (extLiftedCohomologyDeltaIso R).hom.app 0 = (extLiftedCohomologyZeroIso R).hom :=
    DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero _
  have hExt : Ext.addEquiv₀ (Ext.mk₀ (𝟙 (SheafOfModules.unit R))) =
      𝟙 (SheafOfModules.unit R) := by
    apply (Ext.mk₀_bijective _ _).injective
    simp
  rw [h0]
  change ULift.up ((secF R ⊤).toRightDerivedZero.app (SheafOfModules.unit R)
    ((globalSectionsIsoSectionsTop R).hom.app (SheafOfModules.unit R)
      (SheafOfModules.unitHomEquiv (SheafOfModules.unit R)
        (Ext.addEquiv₀ (Ext.mk₀ (𝟙 (SheafOfModules.unit R))))))) = _
  rw [hExt]
  rfl

/-- **Stacks 0B3A.** The canonical bijection sends the class of the extension
`0 → F → E → O_X → 0` to the image of `1 ∈ Γ(X, O_X)` under the boundary map
`H^0(X, O_X) → H^1(X, F)` of the long exact cohomology sequence of the extension. -/
@[stacks 0B3A "image of an extension: the boundary of `1` in the long exact cohomology sequence"]
theorem extOneEquivFirstCohomologyCanonical_extClass (M E : SheafOfModules.{u} R) (f : M ⟶ E)
    (g : E ⟶ SheafOfModules.unit R) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) :
    extOneEquivFirstCohomologyCanonical R M hS.extClass =
      (DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (secF R ⊤)).δ hS 0
        (oneCohomologyClass R) := by
  have h := congrArg (fun φ => φ (Ext.mk₀ (𝟙 (SheafOfModules.unit R))))
    ((extLiftedCohomologyDeltaIso R).hom.comm hS 0)
  change ((liftedCohomologyDeltaFunctor R).δ hS 0)
      ((((extLiftedCohomologyDeltaIso R).hom.app 0).app (SheafOfModules.unit R))
        (Ext.mk₀ (𝟙 (SheafOfModules.unit R)))) =
    (((extLiftedCohomologyDeltaIso R).hom.app 1).app M)
      ((SiteModules.extDeltaFunctorForUnit R).δ hS 0
        (Ext.mk₀ (𝟙 (SheafOfModules.unit R)))) at h
  have hclass : (SiteModules.extDeltaFunctorForUnit R).δ hS 0
      (Ext.mk₀ (𝟙 (SheafOfModules.unit R))) = hS.extClass := by
    change (Ext.mk₀ (𝟙 (SheafOfModules.unit R))).comp hS.extClass (zero_add 1) = hS.extClass
    exact Ext.mk₀_id_comp _
  rw [extLiftedCohomologyDeltaIso_hom_app_zero_mk₀_id, hclass] at h
  rw [extOneEquivFirstCohomologyCanonical_apply, ← h]
  rfl

/-- **Stacks 0B3A.** The boundary formula determines the canonical bijection uniquely. -/
@[stacks 0B3A "uniqueness: the boundary formula determines the bijection"]
theorem extOneEquivFirstCohomologyCanonical_unique (M : SheafOfModules.{u} R)
    (e : Abelian.Ext (SheafOfModules.unit R) M 1 ≃+ Hgroup R ⊤ 1 M)
    (he : ∀ (E : SheafOfModules.{u} R) (f : M ⟶ E)
      (g : E ⟶ SheafOfModules.unit R) (w : f ≫ g = 0)
      (hS : (ShortComplex.mk f g w).ShortExact),
      e hS.extClass =
        (DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (secF R ⊤)).δ hS 0
          (oneCohomologyClass R)) :
    e = extOneEquivFirstCohomologyCanonical R M := by
  ext ξ
  obtain ⟨E, f, g, w, hS, hξ⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (SheafOfModules.{u} R) (SheafOfModules.unit R) M).1 ξ
  rw [← hξ]
  exact (he E f g w hS).trans (extOneEquivFirstCohomologyCanonical_extClass R M E f g w hS).symm

/-- **Stacks 0B3A.** The canonical bijection is natural in the coefficient module sheaf. -/
@[stacks 0B3A "naturality in the coefficient module sheaf"]
theorem extOneEquivFirstCohomologyCanonical_naturality {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) (e : Abelian.Ext (SheafOfModules.unit R) M 1) :
    extOneEquivFirstCohomologyCanonical R N
        ((Abelian.Ext.mk₀ f).postcomp (SheafOfModules.unit R) (Nat.add_zero 1) e) =
      (Hfunctor R ⊤ 1).map f (extOneEquivFirstCohomologyCanonical R M e) := by
  have hnat := congrArg (fun φ => (φ e).down)
    (((extLiftedCohomologyDeltaIso R).hom.app 1).naturality f)
  exact hnat

end Stacks.Cohomology.SpaceModules

end
