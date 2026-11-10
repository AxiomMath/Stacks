module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtHypercohomologyDualTensorSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedDualPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale

/-!
# The dual tensor commutes with étale restriction, and `Ext` over an étale object

Let `g : U ⟶ X` be an étale morphism of algebraic spaces, let `E` be a perfect object of
`D(𝒪_X)` and let `K` be an arbitrary object of `D(𝒪_X)`.  This file proves the identification

`(E|_U)^∨ ⊗^𝐋_{𝒪_U} (K|_U) ≅ (E^∨ ⊗^𝐋_{𝒪_X} K)|_U`,

where `(-)|_U` is étale restriction of modules read on derived categories, and uses it to deduce
the `Ext`-clause of Stacks 0CRU **over an arbitrary quasi-compact absolutely quasi-separated
object `U` of the spaces-étale site of `X`** from the clause over `X`.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictDerivedDualTensorIso`:
  `(E|_U)^∨ ⊗^𝐋 (K|_U) ≅ (E^∨ ⊗^𝐋 K)|_U` for `E` perfect and `g : U ⟶ X` étale.

## Main results

* `AlgebraicGeometry.Space.countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor`:
  the `Ext`-clause of Stacks 0CRU over a quasi-compact absolutely quasi-separated étale `U ⟶ X`.

## References

* [Stacks Project, Tag 0CRU](https://stacks.math.columbia.edu/tag/0CRU)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AddCommGrpCat (HasCountableCohomology)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The dual tensor commutes with étale restriction.**  For an étale morphism `g : U ⟶ X` of
algebraic spaces, a perfect `E ∈ D(𝒪_X)` and an arbitrary `K ∈ D(𝒪_X)`,

`(E|_U)^∨ ⊗^𝐋_{𝒪_U} (K|_U) ≅ (E^∨ ⊗^𝐋_{𝒪_X} K)|_U`,

restriction being étale restriction of modules read on derived categories. -/
def etaleRestrictDerivedDualTensorIso {X U : AlgebraicSpaces B S hS} (g : U ⟶ X)
    (hg : IsEtale B S hS g.hom) (E K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    ((smallEtaleDerivedTensor B S hS U).obj
          (smallEtaleDerivedDual B S hS U
            ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E))).obj
        ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj K) ≅
      (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj K) :=
  let α := smallEtaleDerivedModulePullbackIsoEtale B S hS g hg
  let eDual : smallEtaleDerivedDual B S hS U
        ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E) ≅
      (smallEtaleDerivedModulePullback B S hS g).obj (smallEtaleDerivedDual B S hS X E) :=
    ((smallEtaleDerivedSheafHom B S hS U).mapIso (Iso.op (α.app E))).app
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS U))) ≪≫
      (smallEtaleDerivedModulePullbackDualIso g E hE).symm
  ((smallEtaleDerivedTensor B S hS U).mapIso eDual).app
      ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj K) ≪≫
    ((smallEtaleDerivedTensor B S hS U).obj
        ((smallEtaleDerivedModulePullback B S hS g).obj
          (smallEtaleDerivedDual B S hS X E))).mapIso (α.app K).symm ≪≫
      ((smallEtaleDerivedPullbackTensorIso g).app
          (smallEtaleDerivedDual B S hS X E, K)).symm ≪≫
        α.app (((smallEtaleDerivedTensor B S hS X).obj
          (smallEtaleDerivedDual B S hS X E)).obj K)

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The `Ext`-clause of Stacks 0CRU over a quasi-compact quasi-separated étale object.**  Let
`X` be a quasi-compact absolutely quasi-separated algebraic space over `S`, let `E` be a perfect
object of `D(𝒪_X)`, let `K` be an object of `D(𝒪_X)`, and suppose the cohomology sheaves of
`E^∨ ⊗^𝐋 K` are quasi-coherent with countable sets of sections over the affine étale charts of
`X`.  Then `Ext^i_{𝒪_U}(E|_U, K|_U)` is countable for every quasi-compact absolutely
quasi-separated object `U` of the spaces-étale site of `X`. -/
theorem countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor
    (X : AlgebraicSpaces B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hqcL : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      (((smallEtaleDerivedTensor B S hS X).obj
        (smallEtaleDerivedDual B S hS X E)).obj K)).IsQuasicoherentOnSite)
    (hcount : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
        (((smallEtaleDerivedTensor B S hS X).obj
          (smallEtaleDerivedDual B S hS X E)).obj K)).val.obj (op v)))
    (U : SpacesEtale B S hS X) (hUqc : IsQuasiCompactSpace B S hS U.1.left.1)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1.left.1) (i : ℤ) :
    Countable (DerivedCategory.Ext
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj E)
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj K) i) :=
  have hEU : RingedSite.IsPerfect (smallEtaleRingedSite B S hS U.1.left.1 U.1.left.2)
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj E) :=
    RingedSite.IsPerfect.of_iso _ (isPerfect_smallEtaleDerivedModulePullback U.1.hom E hE)
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS U.1.hom U.2).app E)
  have := (hasCountableCohomology_derivedGlobalSectionsAb_restrict B S hS hZ X
    (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj K)
    hqcL hcount U hUqc hUqs).of_iso
      ((derivedGlobalSectionsAb B S hS U.1.left).mapIso
        (etaleRestrictDerivedDualTensorIso B S hS U.1.hom U.2 E K hE).symm) i
  (smallEtaleExtDerivedGlobalSectionsAbEquiv B S hS U.1.left
    ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj E) hEU
    ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj K)
    i).injective.countable

end AlgebraicGeometry.Space

end
