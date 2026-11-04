module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionCohomologySingle

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesAPI
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedAdjunctionUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleTorsionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FiniteCohomology

/-!
# Base change for the higher direct images of a constant sheaf of `Λ`-modules

Let `Λ` be a ring killed by an integer `n > 0` and let
```
X' --g'--> X
|f'        |f
v          v
S' --g---> S
```
be a cartesian square of schemes along which cohomology commutes with base change for `f` (for `f`
proper this is the proper base change theorem, [Stacks, Tag 095T]). Then for every
`Λ`-module `M` and every `q`, the inverse image `g⁻¹ R^q f_* M̲` is `R^q f'_* M̲`. In particular
constructibility of `R^q f_* M̲` passes to `R^q f'_* M̲` ([Stacks, Tag 095G]). This is the use of
Tag 095T in the proof of [Stacks, Tag 0GKV].

## Main results

* `Stacks.EtaleCohomology.torsionCohomologyProperty_etaleModuleForgetDerived_of_natCast_eq_zero`:
  over a ring killed by `n > 0`, the underlying complex of abelian sheaves of every object of
  `D(X_étale, Λ)` has torsion cohomology sheaves.
* `Stacks.EtaleCohomology.etaleModuleInverseImageHomologyDerivedDirectImageIso`: the isomorphism
  `g⁻¹ R^q f_* ℱ ≅ R^q f'_* g'⁻¹ ℱ` for a torsion sheaf `ℱ`.
* `Stacks.EtaleCohomology.etaleModuleInverseImageHomologyDerivedDirectImageConstantIso`: the
  isomorphism `g⁻¹ R^q f_* M̲ ≅ R^q f'_* M̲`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isPullback`:
  constructibility of `R^q f_* M̲` passes to the base change.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 0GKV](https://stacks.math.columbia.edu/tag/0GKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat
attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

section Torsion

variable (Λ : Type r) [Ring Λ] {n : ℕ} (hn0 : 0 < n) (hn : (n : Λ) = 0) (X : Scheme.{u})

include hn0 hn in
/-- **Over a ring killed by `n > 0`, every complex of sheaves of modules has torsion cohomology.**
The cohomology sheaves of the underlying complex of abelian sheaves of an object `K` of
`D(X_étale, Λ)` are the underlying abelian sheaves of the cohomology sheaves of `K`, whose sections
are all killed by `n`. -/
theorem torsionCohomologyProperty_etaleModuleForgetDerived_of_natCast_eq_zero
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K) := fun q ↦
  Stacks.Torsion.torsionSheafProperty_of_iso X.smallEtaleTopology
    (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapDerivedCategoryHomologyIso
      q).app K).symm
    (fun U x ↦ ⟨⊤, (X.smallEtaleTopology).top_mem U, fun V v _ ↦
      ⟨n, hn0, nsmul_etaleModuleForget_eq_zero Λ hn X _ (Opposite.op V) _⟩⟩)

end Torsion

section BaseChange

variable (Λ : Type r) [CommRing Λ] {n : ℕ} (hn0 : 0 < n) (hn : (n : Λ) = 0)
  {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- The derived inverse image of the constant sheaf `M̲` placed in degree zero is the constant
sheaf `M̲` placed in degree zero: the inverse image is exact, so commutes with `single 0`, and
carries constant sheaves to constant sheaves
(`Stacks.EtaleCohomology.TorsionModules.etaleModuleInverseImageConstantIso`). -/
def etaleModuleDerivedInverseImageSingleConstantIso (g' : X' ⟶ X)
    (M : ModuleCat.{max (u + 1) r} Λ) :
    (etaleModuleDerivedInverseImageGeneral.{u, r} Λ g').obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) ≅
      (DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X') 0).obj
        ((constantSheaf X'.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M) :=
  ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X') 0).mapIso
      ((TorsionModules.etaleModuleInverseImageConstantIso Λ g').app M)

/-- **Base change for `R^q f_* ℱ`.** Suppose that cohomology commutes with base change for
`f : X ⟶ S` (for `f` proper this is [Stacks, Tag 095T]). For a cartesian square of `f` along
`g : S' ⟶ S`, every sheaf `ℱ` of `Λ`-modules on `X_étale` whose underlying abelian sheaf is
torsion, and every `q`, the inverse image `g⁻¹ R^q f_* ℱ` is `R^q f'_* g'⁻¹ ℱ`: inverse image is
exact, so commutes with cohomology sheaves, and the base change map
`g⁻¹ Rf_* ℱ ⟶ Rf'_* g'⁻¹ ℱ` is invertible. -/
def etaleModuleInverseImageHomologyDerivedDirectImageIso
    (hf : CohomologyCommutesWithBaseChange.{u, r} f) (sq : IsPullback g' f' f g)
    (F : EtaleModules.{u, r} Λ X)
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj F)) (q : ℤ) :
    (etaleModuleInverseImage.{u, r} Λ g).obj
        ((DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ S) q).obj
          ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj
            ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F))) ≅
      (DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ S') q).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X') 0).obj
            ((etaleModuleInverseImage.{u, r} Λ g').obj F))) :=
  have := isIso_etaleModuleDerivedBaseChange_of_cohomologyCommutesWithBaseChange.{u, r} Λ hf sq
    ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F) 0
    (fun q ↦ Stacks.Torsion.torsionSheafProperty_of_iso _
      ((DerivedCategory.homologyFunctor _ q).mapIso
        (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ
          X).mapDerivedCategorySingleFunctor 0).app F).symm)
      (Stacks.Torsion.torsionCohomologyProperty_singleFunctor _ _ hF q))
  (((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryHomologyIso q).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ S') q).mapIso
      (asIso ((etaleModuleDerivedBaseChangeGeneral.{u, r} Λ f g g' f' sq.w).app _) ≪≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').mapIso
          (((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategorySingleFunctor 0).app F))

include hn0 hn in
/-- **Base change for `R^q f_* M̲`.** Let `Λ` be a ring killed by an integer `n > 0`, and suppose
that cohomology commutes with base change for `f : X ⟶ S` (for `f` proper this is [Stacks,
Tag 095T]). For a cartesian square of `f` along `g : S' ⟶ S`, every `Λ`-module `M` and every
`q`, the inverse image `g⁻¹ R^q f_* M̲` is `R^q f'_* M̲`: inverse image is exact, so commutes with
cohomology sheaves, the base change map `g⁻¹ Rf_* M̲ ⟶ Rf'_* g'⁻¹ M̲` is invertible since `M̲` is
torsion, and `g'⁻¹ M̲ = M̲`. -/
def etaleModuleInverseImageHomologyDerivedDirectImageConstantIso
    (hf : CohomologyCommutesWithBaseChange.{u, r} f) (sq : IsPullback g' f' f g)
    (M : ModuleCat.{max (u + 1) r} Λ) (q : ℤ) :
    (etaleModuleInverseImage.{u, r} Λ g).obj
        ((DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ S) q).obj
          ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj
            ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)))) ≅
      (DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ S') q).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X') 0).obj
            ((constantSheaf X'.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M))) :=
  have := isIso_etaleModuleDerivedBaseChange_of_cohomologyCommutesWithBaseChange.{u, r} Λ hf sq
    ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) 0
    (torsionCohomologyProperty_etaleModuleForgetDerived_of_natCast_eq_zero Λ hn0 hn X _)
  (((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryHomologyIso q).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ S') q).mapIso
      (asIso ((etaleModuleDerivedBaseChangeGeneral.{u, r} Λ f g g' f' sq.w).app _) ≪≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').mapIso
          (etaleModuleDerivedInverseImageSingleConstantIso Λ g' M))

include hn0 hn in
/-- **Constructibility of `R^q f_* M̲` passes to base changes.** Under the hypotheses of
`Stacks.EtaleCohomology.etaleModuleInverseImageHomologyDerivedDirectImageConstantIso`, with `Λ`
Noetherian: if `R^q f_* M̲` is constructible, so is `R^q f'_* M̲`, which is its inverse image
([Stacks, Tag 095G]). -/
theorem isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isPullback
    [IsNoetherianRing Λ] (hf : CohomologyCommutesWithBaseChange.{u, r} f)
    (sq : IsPullback g' f' f g) (M : ModuleCat.{max (u + 1) r} Λ) (q : ℤ)
    (h : IsConstructibleEtaleModule Λ
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ S) q).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M))))) :
    IsConstructibleEtaleModule Λ
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ S') q).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X') 0).obj
            ((constantSheaf X'.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)))) :=
  (IsConstructibleEtaleModule Λ).prop_of_iso
    (etaleModuleInverseImageHomologyDerivedDirectImageConstantIso Λ hn0 hn hf sq M q)
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ g _ h)

end BaseChange

end Stacks.EtaleCohomology

end
