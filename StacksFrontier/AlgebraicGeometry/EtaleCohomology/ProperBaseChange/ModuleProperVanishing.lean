module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDirectImageForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Higher direct images of sheaves of modules forget to higher direct images of abelian sheaves

Let `f : X ⟶ Y` be a morphism of schemes and `Λ` a ring. Forgetting the `Λ`-module structure of a
sheaf on the small étale site is exact and carries injective sheaves of `Λ`-modules to abelian
sheaves acyclic for `f_*` (Stacks 03FD). Hence the underlying abelian sheaf of `R^q f_* G`,
computed for sheaves of `Λ`-modules, is `R^q f_*` of the underlying abelian sheaf of `G`.

As a consequence the vanishing theorem Stacks 095U holds for sheaves of `Λ`-modules: if `f` is
proper with fibres of dimension `≤ n` and the underlying abelian sheaf of `G` is torsion, then
`R^q f_* G = 0` for `q > 2n`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageForgetIso`:
  `Rf_* ⋙ U ≅ U ⋙ Rf_*` on bounded below derived categories.
* `Stacks.EtaleCohomology.etaleModuleForgetRightDerivedDirectImageIso`:
  `U(R^q f_* G) ≅ R^q f_*(U G)`.
* `Stacks.EtaleCohomology.isZero_rightDerived_etaleModuleDirectImage_of_isProper`: Stacks 095U
  for sheaves of `Λ`-modules, `R^q f_* G = 0` for `q > 2n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Sheaves of `Λ`-modules on a small étale site have enough injectives, at the coefficient
universe `u + 1`. -/
instance etaleModules_enoughInjectives_univZero (Z : Scheme.{u}) :
    EnoughInjectives (EtaleModules.{u, 0} Λ Z) :=
  etaleModules_enoughInjectives.{u, 0} Λ Z

/-- The direct image of sheaves of `Λ`-modules followed by forgetting the module structure is the
direct image of the underlying abelian sheaf. -/
def etaleModuleDirectImageForgetIso :
    etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleForgetAb.{u, 0} Λ Y ≅
      etaleModuleForgetAb.{u, 0} Λ X ⋙ etaleAbelianDirectImage.{u, 0} f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **`Rf_* ⋙ U ≅ U ⋙ Rf_*`**: the derived direct image of sheaves of `Λ`-modules commutes with
forgetting the module structure. -/
def etaleModuleDerivedDirectImageForgetIso :
    etaleModuleDerivedDirectImage.{u, 0} Λ f ⋙
        (etaleModuleForgetAb.{u, 0} Λ Y).mapDerivedCategoryPlus ≅
      (etaleModuleForgetAb.{u, 0} Λ X).mapDerivedCategoryPlus ⋙
        (etaleAbelianDirectImage.{u, 0} f).rightDerivedFunctorPlus :=
  letI := etaleModules_enoughInjectives.{u, 0} Λ X
  letI := etaleModules_enoughInjectives.{u, 0} Λ Y
  Functor.rightDerivedRestrictionIso _ _ _ _ (etaleModuleDirectImageForgetIso Λ f)
    (fun I _ => rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj Λ f I)

/-- Forgetting the module structure commutes with the cohomology objects of bounded below
complexes. -/
def etaleModuleForgetPlusHomologyIso (Z : Scheme.{u})
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Z)) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((etaleModuleForgetAb.{u, 0} Λ Z).mapDerivedCategoryPlus.obj K) ≅
      (etaleModuleForgetAb.{u, 0} Λ Z).obj
        ((DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ Z) q).obj K) :=
  (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (etaleModuleForgetAb.{u, 0} Λ Z) q).app (DerivedCategory.Plus.ι.obj K)

/-- Forgetting the module structure commutes with placing a sheaf in degree `n`, on bounded below
derived categories. -/
def etaleModuleForgetPlusSingleIso (Z : Scheme.{u}) (n : ℤ) (G : EtaleModules.{u, 0} Λ Z) :
    (etaleModuleForgetAb.{u, 0} Λ Z).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ Z) n).obj G) ≅
      (DerivedCategory.Plus.singleFunctor (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
        ((etaleModuleForgetAb.{u, 0} Λ Z).obj G) :=
  DerivedCategory.Plus.ι.preimageIso
    (((etaleModuleForgetAb.{u, 0} Λ Z).mapDerivedCategorySingleFunctor n).app G)

/-- **The underlying abelian sheaf of `R^q f_* G` is `R^q f_*` of the underlying abelian sheaf of
`G`**, for a sheaf `G` of `Λ`-modules on `X_étale`. -/
def etaleModuleForgetRightDerivedDirectImageIso (G : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    (etaleModuleForgetAb.{u, 0} Λ Y).obj
        (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj G) ≅
      ((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj
        ((etaleModuleForgetAb.{u, 0} Λ X).obj G) :=
  letI := etaleModules_enoughInjectives.{u, 0} Λ X
  (etaleModuleForgetAb.{u, 0} Λ Y).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, 0} Λ f) q).app G) ≪≫
    (etaleModuleForgetPlusHomologyIso Λ Y _ (q : ℤ)).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (q : ℤ)).mapIso
      ((etaleModuleDerivedDirectImageForgetIso Λ f).app
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj G)) ≪≫
    (DerivedCategory.Plus.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (q : ℤ)).mapIso
      ((etaleAbelianDirectImage.{u, 0} f).rightDerivedFunctorPlus.mapIso
        (etaleModuleForgetPlusSingleIso Λ X 0 G)) ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso (etaleAbelianDirectImage.{u, 0} f) q).app
      ((etaleModuleForgetAb.{u, 0} Λ X).obj G)).symm

/-- **Stacks 095U for sheaves of modules.** Let `f : X ⟶ Y` be proper with all fibres of
dimension `≤ n`, and let `G` be a sheaf of `Λ`-modules on `X_étale` whose underlying abelian sheaf
is torsion. Then `R^q f_* G = 0` for `q > 2n`. -/
theorem isZero_rightDerived_etaleModuleDirectImage_of_isProper [IsProper f] (n : ℕ)
    (hfib : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ n) (G : EtaleModules.{u, 0} Λ X)
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((etaleModuleForgetAb.{u, 0} Λ X).obj G)) (q : ℕ) (hq : 2 * n < q) :
    IsZero (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj G) := by
  have h := (isZero_rightDerived_etaleAbelianDirectImage_of_isProper f n hfib _ hG q hq).of_iso
    (etaleModuleForgetRightDerivedDirectImageIso Λ f G q)
  rw [IsZero.iff_id_eq_zero]
  exact (etaleModuleForgetAb.{u, 0} Λ Y).map_injective (by simpa using h.eq_of_src _ _)

end Stacks.EtaleCohomology

end
