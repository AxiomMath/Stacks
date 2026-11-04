module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageCompositionUnbounded
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
import StacksCore.Tactic.StacksAttribute

/-!
# The composition of derived lower shrieks on unbounded derived categories ([Stacks, Tag 0F7J])

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be separated morphisms of finite type of quasi-compact and
quasi-separated schemes and let `Λ` be a torsion ring, in any universe. Then
`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` as functors
`D(X_étale, Λ) ⥤ D(Z_étale, Λ)`. This is the second case of [Stacks, Tag 0F7J], the derived lower
shrieks of [Stacks, Tag 0F7H] being defined on the unbounded derived categories when `Λ` is
torsion; the case of `D⁺_tors` for an arbitrary ring is
`Stacks.EtaleCohomology.derivedLowerShriekCompIsoUniv`.

The proof is the source's. Choose a compactification `i : Y ⟶ Ȳ` of `Y` over `Z`, a
compactification `X ⟶ X̄` of `X` over `Ȳ`, and let `U = X̄ ×_Ȳ Y`, with `b : U ⟶ X̄`,
`f' : U ⟶ Y` and `f̄ : X̄ ⟶ Ȳ`. Then
`R(ḡ ∘ f̄)_* (b ∘ j)_! ≅ Rḡ_* Rf̄_* b_! j_! ≅ Rḡ_* i_! Rf'_* j_!`, and independence of the
compactifications ([Stacks, Tag 0F7I]) transports this to arbitrary compactifications of `f`, `g`
and `g ∘ f`.

The input is the open immersion case of [Stacks, Tag 0F7B] on unbounded derived categories,
`Rf̄_* ∘ b_! ≅ i_! ∘ Rf'_*`. Both sides are right derived functors of the same functor on sheaves:

* on sheaves `i_! ∘ f'_* ≅ f̄_* ∘ b_!`, the cohomology in degree zero of the open immersion case of
  [Stacks, Tag 0F7B] on `D⁺` (where every object has torsion cohomology sheaves, `Λ` being
  torsion);
* `Rf'_* ∘ i_!` is a right derived functor of `i_! ∘ f'_*`, `i_!` being exact;
* `b_! ∘ Rf̄_*` is a right derived functor of `f̄_* ∘ b_!`: at a complex `J` of injective sheaves
  each `b_! J^n` is `f̄_*`-acyclic, again by the case of `D⁺`, and complexes of `f̄_*`-acyclic
  sheaves compute the unbounded `Rf̄_*`, `f̄_*` having finite cohomological dimension
  ([Stacks, Tag 095U] and [Stacks, Tag 07K7]); every K-injective complex is homotopy equivalent to
  a K-injective complex of injective sheaves ([Stacks, Tag 079P]).

## Main results

* `Stacks.EtaleCohomology.etaleModuleDirectImageExtensionByZeroIso`: `i_! ∘ f'_* ≅ f̄_* ∘ b_!` on
  sheaves of `Λ`-modules, for a torsion ring `Λ`.
* `Stacks.EtaleCohomology.rightAcyclic_etaleModuleDirectImage_extensionByZero_of_injective`:
  `b_! J` is `f̄_*`-acyclic for an injective `J`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroDirectImageUnboundedIso`: the open immersion
  case of [Stacks, Tag 0F7B] on unbounded derived categories.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`: **[Stacks, Tag 0F7J]** on
  `D(X_étale, Λ)` for a torsion ring `Λ`.

## Implementation notes

The coefficient ring lives in an arbitrary universe `Type w`, as for the unbounded independence
of the compactification
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompactificationIsoUniv`) and the bounded below
case of the tag (`Stacks.EtaleCohomology.derivedLowerShriekCompIsoUniv`). Everything is stated in
the standard model `HasDerivedCategory.standard` of the
derived category, the model in which `Stacks.EtaleCohomology.derivedLowerShriekUnbounded` is
defined.

## References

* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance 2000] etaleModules_enoughInjectives

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

variable (Λ : Type w) [Ring Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-! ### The open immersion case of [Stacks, Tag 0F7B] on sheaves, over a torsion ring -/

section OpenBaseChange

variable {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
  (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i)

include hΛ in
/-- Over a torsion ring every object of `D⁺(P_étale, Λ)` has torsion cohomology sheaves. -/
theorem isTorsionPlus_of_torsion (K : DerivedCategory.Plus (EtaleModules.{u, w} Λ P)) :
    isTorsionPlus.{u, w} Λ P K := fun _ =>
  isTorsionEtaleModule_of_nsmul_eq_zero_univ Λ hΛ.choose hΛ.choose_spec.1 hΛ.choose_spec.2 _

/-- **`Rf̄_* ∘ Rb_! ≅ Ri_! ∘ Rf'_*` on the whole of `D⁺(P_étale, Λ)`** over a torsion ring, where
every object has torsion cohomology sheaves: the open immersion case of [Stacks, Tag 0F7B]
(`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProperUniv`). -/
def etaleModuleDerivedExtensionByZeroDirectImagePlusIso :
    etaleModuleDerivedExtensionByZero.{u, w} Λ b ⋙ etaleModuleDerivedDirectImage.{u, w} Λ fb ≅
      etaleModuleDerivedDirectImage.{u, w} Λ f' ⋙ etaleModuleDerivedExtensionByZero.{u, w} Λ i :=
  let L := ObjectProperty.lift (isTorsionPlus.{u, w} Λ P) (𝟭 _)
    (fun K => isTorsionPlus_of_torsion Λ hΛ K)
  let eL : L ⋙ (isTorsionPlus.{u, w} Λ P).ι ≅ 𝟭 _ := ObjectProperty.liftCompιIso _ _ _
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight eL.symm _ ≪≫
    Functor.isoWhiskerLeft L
      (etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProperUniv Λ fb i b f' sq) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eL _ ≪≫ Functor.leftUnitor _

include hΛ i f' sq in
/-- The sheaf `b_! J` is acyclic for `f̄_*` when `J` is injective, over a torsion ring: on
cohomology sheaves `R^q f̄_*(b_! J) = i_! R^q f'_* J`, by the open immersion case of
[Stacks, Tag 0F7B]. -/
theorem rightAcyclic_etaleModuleDirectImage_extensionByZero_of_injective
    (J : EtaleModules.{u, w} Λ P) [Injective J] :
    (etaleModuleDirectImage.{u, w} Λ fb).rightAcyclic
      ((etaleModuleExtensionByZero.{u, w} Λ b).obj J) := by
  rw [((etaleModuleDirectImage.{u, w} Λ fb).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    _).2 inferInstance]
  intro q hq
  have hJ := ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (etaleModuleDirectImage.{u, w} Λ f') J).2 inferInstance).1
    (Functor.rightAcyclic_of_injective _ J) q hq
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, w} Λ P) 0
  refine IsZero.of_iso ((etaleModuleExtensionByZero.{u, w} Λ i).map_isZero hJ) ?_
  exact (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((etaleModuleDerivedDirectImage.{u, w} Λ fb).mapIso
        ((etaleModuleExtensionByZero.{u, w} Λ b).rightDerivedFunctorPlusObjSingleIso J).symm ≪≫
      (etaleModuleDerivedExtensionByZeroDirectImagePlusIso Λ hΛ fb i b f' sq).app (S.obj J)) ≪≫
    etaleModuleDerivedExtensionByZeroHomologyIsoUniv Λ i _ q

/-- A left exact functor is its own `R⁰`, read through the bounded below derived functor:
`F ≅ H⁰ ∘ RF ∘ (-)[0]`. -/
def rightDerivedFunctorPlusZeroIso {A B : Type*} [Category* A] [Category* B] [Abelian A]
    [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] :
    F ≅ DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor B 0 :=
  F.rightDerivedZeroIsoSelf.symm ≪≫ Stacks.DerivedIndexing.rightDerivedIso F 0

/-- An exact functor commutes with the cohomology objects of `D⁺`, through its bounded below
derived functor: `H⁰ ∘ RE ≅ E ∘ H⁰`. -/
def rightDerivedFunctorPlusHomologyIso {A B : Type*} [Category* A] [Category* B] [Abelian A]
    [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (E : A ⥤ B)
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E] (q : ℤ) :
    E.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B q ≅
      DerivedCategory.Plus.homologyFunctor A q ⋙ E :=
  Functor.isoWhiskerRight E.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus _ ≪≫
    (Functor.isoWhiskerLeft DerivedCategory.Plus.ι (Stacks.Homology.derivedHomologyIso E q) :
      DerivedCategory.Plus.ι ⋙ E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q ≅ _)

/-- An exact functor commutes with the single functors of `D⁺`, through its bounded below derived
functor: `RE ∘ (-)[0] ≅ (-)[0] ∘ E`. -/
def singleFunctorCompRightDerivedFunctorPlusIso {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E] :
    DerivedCategory.Plus.singleFunctor A 0 ⋙ E.rightDerivedFunctorPlus ≅
      E ⋙ DerivedCategory.Plus.singleFunctor B 0 :=
  Functor.isoWhiskerLeft _ E.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus ≪≫
    ((Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight A).preimageIso
      (E.mapDerivedCategorySingleFunctor 0 :
        DerivedCategory.singleFunctor A 0 ⋙ E.mapDerivedCategory ≅ _)

include hΛ sq in
/-- **The underived open immersion case of [Stacks, Tag 0F7B]**, over a torsion ring:
`i_! ∘ f'_* ≅ f̄_* ∘ b_!` on sheaves of `Λ`-modules. It is the cohomology in degree zero of the
derived identification `etaleModuleDerivedExtensionByZeroDirectImagePlusIso` on objects placed in
degree zero. -/
def etaleModuleDirectImageExtensionByZeroIso :
    etaleModuleDirectImage.{u, w} Λ f' ⋙ etaleModuleExtensionByZero.{u, w} Λ i ≅
      etaleModuleExtensionByZero.{u, w} Λ b ⋙ etaleModuleDirectImage.{u, w} Λ fb :=
  Functor.isoWhiskerRight (rightDerivedFunctorPlusZeroIso (etaleModuleDirectImage.{u, w} Λ f')) _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        etaleModuleDerivedDirectImage.{u, w} Λ f')
      (rightDerivedFunctorPlusHomologyIso (etaleModuleExtensionByZero.{u, w} Λ i) 0).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.isoWhiskerRight
        (etaleModuleDerivedExtensionByZeroDirectImagePlusIso Λ hΛ fb i b f' sq).symm
        (DerivedCategory.Plus.homologyFunctor _ 0)) ≪≫
    (Functor.isoWhiskerRight
      (singleFunctorCompRightDerivedFunctorPlusIso (etaleModuleExtensionByZero.{u, w} Λ b))
      (etaleModuleDerivedDirectImage.{u, w} Λ fb ⋙ DerivedCategory.Plus.homologyFunctor _ 0) :
        (DerivedCategory.Plus.singleFunctor _ 0 ⋙ etaleModuleDerivedExtensionByZero.{u, w} Λ b) ⋙
          etaleModuleDerivedDirectImage.{u, w} Λ fb ⋙
            DerivedCategory.Plus.homologyFunctor _ 0 ≅ _) ≪≫
    Functor.isoWhiskerLeft (etaleModuleExtensionByZero.{u, w} Λ b)
      (rightDerivedFunctorPlusZeroIso (etaleModuleDirectImage.{u, w} Λ fb)).symm

end OpenBaseChange

/-! ### The open immersion case of [Stacks, Tag 0F7B] on unbounded derived categories -/

section Unbounded

open Stacks.Injectives.KInjectiveResolution (isRightDerivedFunctor_iff_isIso_app_of_isKInjective
  invertsQuasiIso_mapHomologicalComplex_comp_Q)

variable {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
  (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i)

/-- The comparison `(f̄_* ∘ b_!)(K) ⟶ Rf̄_*(b_! K)` exhibiting `b_! ⋙ Rf̄_*` as a candidate right
derived functor of `f̄_* ∘ b_!` on unbounded complexes. -/
def extensionByZeroDirectImageUnboundedUnit :
    (etaleModuleExtensionByZero.{u, w} Λ b ⋙
          etaleModuleDirectImage.{u, w} Λ fb).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ ((etaleModuleExtensionByZero.{u, w} Λ b).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, w} Λ fb) :=
  Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
      (Iso.refl (etaleModuleExtensionByZero.{u, w} Λ b ⋙ etaleModuleDirectImage.{u, w} Λ fb))
      (ComplexShape.up ℤ)).inv DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, w} Λ fb) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleModuleExtensionByZero.{u, w} Λ b).mapDerivedCategoryFactors.inv _ ≫
    (Functor.associator _ _ _).hom

include hΛ i f' sq in
/-- The comparison `(f̄_* ∘ b_!)(J) ⟶ Rf̄_*(b_! J)` is invertible at a complex `J` of injective
sheaves, over a torsion ring: each `b_! J^n` is `f̄_*`-acyclic
(`rightAcyclic_etaleModuleDirectImage_extensionByZero_of_injective`), and complexes of
`f̄_*`-acyclic sheaves compute the unbounded `Rf̄_*`, `f̄_*` having finite cohomological
dimension. -/
theorem isIso_extensionByZeroDirectImageUnboundedUnit_app_of_injective [CompactSpace Ub]
    (J : CochainComplex (EtaleModules.{u, w} Λ P) ℤ) (hJ : ∀ n, Injective (J.X n)) :
    IsIso ((extensionByZeroDirectImageUnboundedUnit Λ fb b).app J) := by
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_rightAcyclic_univ Λ fb
    hΛ.choose hΛ.choose_spec.1 hΛ.choose_spec.2
    (((etaleModuleExtensionByZero.{u, w} Λ b).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
    (fun n => haveI := hJ n
      rightAcyclic_etaleModuleDirectImage_extensionByZero_of_injective Λ hΛ fb i b f' sq (J.X n))
  simp only [extensionByZeroDirectImageUnboundedUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

include hΛ i f' sq in
/-- The comparison `(f̄_* ∘ b_!)(K) ⟶ Rf̄_*(b_! K)` is invertible at every K-injective complex,
over a torsion ring. A K-injective complex is quasi-isomorphic, hence homotopy equivalent, to a
K-injective complex of injective sheaves ([Stacks, Tag 079P]), at which the comparison is
invertible. -/
theorem isIso_extensionByZeroDirectImageUnboundedUnit_app_of_isKInjective [CompactSpace Ub]
    (I : CochainComplex (EtaleModules.{u, w} Λ P) ℤ) (hI : I.IsKInjective) :
    IsIso ((extensionByZeroDirectImageUnboundedUnit Λ fb b).app I) := by
  let R := (Stacks.Injectives.exists_functorial_quasiIso_isKInjective
    (EtaleModules.{u, w} Λ P)).some
  let s : I ⟶ R.functor.obj I := R.inclusion.app I
  have hs : QuasiIso s := R.quasiIso I
  have h₁ : IsIso ((((etaleModuleExtensionByZero.{u, w} Λ b ⋙
      etaleModuleDirectImage.{u, w} Λ fb).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Q).map s) :=
    invertsQuasiIso_mapHomologicalComplex_comp_Q _ s hI (R.isKInjective I) hs
  have h₂ : IsIso ((extensionByZeroDirectImageUnboundedUnit Λ fb b).app (R.functor.obj I)) :=
    isIso_extensionByZeroDirectImageUnboundedUnit_app_of_injective Λ hΛ fb i b f' sq _
      (R.injective I)
  have : IsIso (DerivedCategory.Q.map s) :=
    Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) s
      ((HomologicalComplex.mem_quasiIso_iff _).2 hs)
  have h₃ : IsIso ((DerivedCategory.Q ⋙
      ((etaleModuleExtensionByZero.{u, w} Λ b).mapDerivedCategory ⋙
      etaleModuleDerivedDirectImageUnbounded.{u, w} Λ fb)).map s) := by
    dsimp only [Functor.comp_map]
    infer_instance
  exact IsIso.of_isIso_fac_right
    ((extensionByZeroDirectImageUnboundedUnit Λ fb b).naturality s).symm

/-- The comparison `(i_! ∘ f'_*)(K) ⟶ i_!(Rf'_* K)` exhibiting `Rf'_* ⋙ i_!` as a candidate right
derived functor of `i_! ∘ f'_*` on unbounded complexes. -/
def directImageExtensionByZeroUnboundedUnit :
    (etaleModuleDirectImage.{u, w} Λ f' ⋙
          etaleModuleExtensionByZero.{u, w} Λ i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (etaleModuleDerivedDirectImageUnbounded.{u, w} Λ f' ⋙
        (etaleModuleExtensionByZero.{u, w} Λ i).mapDerivedCategory) :=
  Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
      (Iso.refl (etaleModuleDirectImage.{u, w} Λ f' ⋙ etaleModuleExtensionByZero.{u, w} Λ i))
      (ComplexShape.up ℤ)).inv DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (etaleModuleExtensionByZero.{u, w} Λ i).mapDerivedCategoryFactors.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, w} Λ f') _ ≫
    (Functor.associator _ _ _).hom

/-- `Rf'_* ⋙ i_!` is a right derived functor of `i_! ∘ f'_*`: `Rf'_*` is computed on K-injective
complexes and `i_!` is exact. -/
instance isRightDerivedFunctor_directImageExtensionByZeroUnboundedUnit :
    (etaleModuleDerivedDirectImageUnbounded.{u, w} Λ f' ⋙
        (etaleModuleExtensionByZero.{u, w} Λ i).mapDerivedCategory).IsRightDerivedFunctor
      (directImageExtensionByZeroUnboundedUnit Λ i f')
      (HomologicalComplex.quasiIso (EtaleModules.{u, w} Λ P) (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q _)]
  intro I hI
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, w} Λ f' I hI
  simp only [directImageExtensionByZeroUnboundedUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- The comparison `(i_! ∘ f'_*)(K) ⟶ Rf̄_*(b_! K)` through the underived identification
`i_! ∘ f'_* ≅ f̄_* ∘ b_!`. -/
def directImageExtensionByZeroUnboundedUnit' :
    (etaleModuleDirectImage.{u, w} Λ f' ⋙
          etaleModuleExtensionByZero.{u, w} Λ i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ ((etaleModuleExtensionByZero.{u, w} Λ b).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, w} Λ fb) :=
  Functor.whiskerRight (NatIso.mapHomologicalComplex
      (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq) (ComplexShape.up ℤ)).hom
      DerivedCategory.Q ≫
    extensionByZeroDirectImageUnboundedUnit Λ fb b

include hΛ in
/-- Over a torsion ring `b_! ⋙ Rf̄_*` is also a right derived functor of `i_! ∘ f'_*`. -/
theorem isRightDerivedFunctor_directImageExtensionByZeroUnboundedUnit' [CompactSpace Ub] :
    ((etaleModuleExtensionByZero.{u, w} Λ b).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, w} Λ fb).IsRightDerivedFunctor
      (directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq)
      (HomologicalComplex.quasiIso (EtaleModules.{u, w} Λ P) (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q _)]
  intro I hI
  have := isIso_extensionByZeroDirectImageUnboundedUnit_app_of_isKInjective Λ hΛ fb i b f' sq I hI
  simp only [directImageExtensionByZeroUnboundedUnit', NatTrans.comp_app,
    Functor.whiskerRight_app]
  infer_instance

/-- **The open immersion case of [Stacks, Tag 0F7B] on unbounded derived categories**, for a
torsion ring `Λ`: for a cartesian square `b ≫ f̄ = f' ≫ i` with `f̄` proper over a quasi-compact
base and `b`, `i` open immersions, `Rf̄_* ∘ b_! ≅ i_! ∘ Rf'_*` on `D(P_étale, Λ)`. Both are right
derived functors of `i_! ∘ f'_* ≅ f̄_* ∘ b_!`. -/
def etaleModuleExtensionByZeroDirectImageUnboundedIso [CompactSpace Ub] :
    (etaleModuleExtensionByZero.{u, w} Λ b).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, w} Λ fb ≅
      etaleModuleDerivedDirectImageUnbounded.{u, w} Λ f' ⋙
        (etaleModuleExtensionByZero.{u, w} Λ i).mapDerivedCategory :=
  haveI := isRightDerivedFunctor_directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq
  Functor.rightDerivedUnique _ _ (directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq)
    (directImageExtensionByZeroUnboundedUnit Λ i f')
    (HomologicalComplex.quasiIso (EtaleModules.{u, w} Λ P) (ComplexShape.up ℤ))

end Unbounded

/-! ### [Stacks, Tag 0F7J] on unbounded derived categories -/

section Composition

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` on `D(X_étale, Λ)` through the compactifications of the proof of
[Stacks, Tag 0F7J]**, for a torsion ring `Λ`: for a compactification `i : Y ⟶ Ȳ` of `g` with `Ȳ`
quasi-compact and a compactification `X ⟶ X̄` of `X` over `Ȳ`, with `Rf_!` computed through
`X ⟶ X̄ ×_Ȳ Y` and `R(g ∘ f)_!` through `X ⟶ X̄ ⟶ Ȳ ⟶ Z`. The chain is
`R(ḡ ∘ f̄)_* (j' ∘ j)_! ≅ Rḡ_* Rf̄_* j'_! j_! ≅ Rḡ_* i_! Rf'_* j_!`, the second isomorphism being
the open immersion case of [Stacks, Tag 0F7B]
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroDirectImageUnboundedIso`). -/
def derivedLowerShriekUnboundedCompOverIso (jg : CompactificationOf (Over.mk g))
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) [CompactSpace jg.space] :
    derivedLowerShriekUnbounded.{u, w} (f ≫ g) (CompactificationOf.compOver jg jX) Λ ≅
      derivedLowerShriekUnbounded.{u, w} f (CompactificationOf.restrictBase jg jX) Λ ⋙
        derivedLowerShriekUnbounded.{u, w} g jg Λ :=
  let a := (CompactificationOf.restrictBase jg jX).immersion
  let b := CompactificationOf.restrictBaseι jg jX
  let Ea := (etaleModuleExtensionByZero.{u, w} Λ a).mapDerivedCategory
  let Eb := (etaleModuleExtensionByZero.{u, w} Λ b).mapDerivedCategory
  let Ei := (etaleModuleExtensionByZero.{u, w} Λ jg.immersion).mapDerivedCategory
  let Rfb := etaleModuleDerivedDirectImageUnbounded.{u, w} Λ jX.toBase
  let Rgb := etaleModuleDerivedDirectImageUnbounded.{u, w} Λ jg.toBase
  let Rf' := etaleModuleDerivedDirectImageUnbounded.{u, w} Λ
    (CompactificationOf.restrictBase jg jX).toBase
  let e₁ : etaleModuleDerivedExtensionByZeroUnbounded.{u, w} Λ (a ≫ b) ≅ Ea ⋙ Eb :=
    etaleModuleDerivedExtensionByZeroUnboundedIso.{u, w} Λ (a ≫ b) ≪≫
      Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
        (etaleModuleExtensionByZeroCompIso.{u, w} Λ a b)
  let e₂ : etaleModuleDerivedDirectImageUnbounded.{u, w} Λ (jX.toBase ≫ jg.toBase) ≅
      Rfb ⋙ Rgb :=
    etaleModuleDerivedDirectImageUnboundedLerayIso.{u, w} Λ jX.toBase jg.toBase _ rfl
  let β : Eb ⋙ Rfb ≅ Rf' ⋙ Ei :=
    etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ jX.toBase jg.immersion b
      (CompactificationOf.restrictBase jg jX).toBase
      (IsPullback.of_hasPullback jX.toBase jg.immersion)
  let s₁ : derivedLowerShriekUnbounded.{u, w} (f ≫ g) (CompactificationOf.compOver jg jX) Λ ≅
      Ea ⋙ ((Eb ⋙ Rfb) ⋙ Rgb) :=
    Functor.isoWhiskerRight e₁ _ ≪≫ Functor.isoWhiskerLeft _ e₂
  let s₂ : Ea ⋙ ((Eb ⋙ Rfb) ⋙ Rgb) ≅ Ea ⋙ ((Rf' ⋙ Ei) ⋙ Rgb) :=
    Functor.isoWhiskerLeft Ea (Functor.isoWhiskerRight β Rgb)
  let s₃ : Ea ⋙ ((Rf' ⋙ Ei) ⋙ Rgb) ≅
      derivedLowerShriekUnbounded.{u, w} f (CompactificationOf.restrictBase jg jX) Λ ⋙
        derivedLowerShriekUnbounded.{u, w} g jg Λ :=
    Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, w} Λ a).symm
        ((Rf' ⋙ Ei) ⋙ Rgb) ≪≫
      Functor.isoWhiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, w} Λ a ⋙ Rf')
        (Functor.isoWhiskerRight
          (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, w} Λ jg.immersion).symm Rgb)
  s₁ ≪≫ s₂ ≪≫ s₃

/-- **Stacks Project, Tag 0F7J**, on unbounded derived categories. Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be separated morphisms of finite type of quasi-compact and quasi-separated schemes, and
let `Λ` be a torsion ring, in any universe. Then `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` as functors
`D(X_étale, Λ) ⥤ D(Z_étale, Λ)`, where `Rf_!`, `Rg_!` and `R(g ∘ f)_!` are computed through
arbitrary compactifications `jf`, `jg` and `j`.

The isomorphism is that of the source: through a compactification `X ⟶ X̄` of `X` over `Ȳ`
(Nagata's theorem, [Stacks, Tag 0F41]) it is
`R(ḡ ∘ f̄)_* (j' ∘ j)_! ≅ Rḡ_* Rf̄_* j'_! j_! ≅ Rḡ_* i_! Rf'_* j_!`
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompOverIso`, which uses
[Stacks, Tag 0F7B] for the open immersion `i`), and it is transported to the given
compactifications by [Stacks, Tag 0F7I]
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompactificationIsoUniv`). The case of
`D⁺_tors(X_étale, Λ)` for an arbitrary ring is
`Stacks.EtaleCohomology.derivedLowerShriekCompIsoUniv`. -/
@[stacks 0F7J "unbounded derived categories D(X_étale, Λ), Λ a torsion ring"]
def derivedLowerShriekUnboundedCompIso [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f]
    [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (jf : CompactificationOf (Over.mk f)) (jg : CompactificationOf (Over.mk g))
    (j : CompactificationOf (Over.mk (f ≫ g))) :
    derivedLowerShriekUnbounded.{u, w} (f ≫ g) j Λ ≅
      derivedLowerShriekUnbounded.{u, w} f jf Λ ⋙ derivedLowerShriekUnbounded.{u, w} g jg Λ :=
  haveI : QuasiCompact f := quasiCompact_of_compactSpace f
  haveI : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  haveI : UniversallyClosed jg.toBase := IsProper.toUniversallyClosed
  haveI : QuasiCompact jg.toBase := instQuasiCompactOfUniversallyClosed jg.toBase
  haveI : CompactSpace jg.space := QuasiCompact.compactSpace_of_compactSpace jg.toBase
  let jX := (nonempty_compactificationOf_comp_immersion f g jg).some
  derivedLowerShriekUnboundedCompactificationIsoUniv (f ≫ g) j
      (CompactificationOf.compOver jg jX) Λ hΛ ≪≫
    derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX ≪≫
    Functor.isoWhiskerRight
      (derivedLowerShriekUnboundedCompactificationIsoUniv f
        (CompactificationOf.restrictBase jg jX) jf Λ hΛ)
      (derivedLowerShriekUnbounded.{u, w} g jg Λ)

end Composition

end Stacks.EtaleCohomology

end
