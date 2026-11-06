module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDirectImageForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.RingedBaseChangeComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeTransportCompat
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeDerivedTransport
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base change map of sheaves of `Λ`-modules and of abelian sheaves, on `D⁺`

Let
```
X' <-h-- Y
|f'      |e
S  <-g-- T
```
be a commutative square of schemes, `h ≫ f' = e ≫ g`, and `Λ` a ring. On abelian sheaves on the
small étale sites the base change map `(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` on `D⁺` is
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`. This file builds the same map for sheaves
of `Λ`-modules, `Stacks.EtaleCohomology.EtaleModules Λ` (the coefficients of
[Stacks, Tag 0F14] in `StacksDraft.AlgebraicGeometry.EtaleCohomology.ProperKunneth`), and proves
that **forgetting the module structure carries the one to the other**: for `K ∈ D⁺(T_étale, Λ)`
the square

```
U((f')⁻¹Rg_*K) --U(bc)--> U(Rh_*e⁻¹K)
      ≅                        ≅
(f')⁻¹Rg_*U(K) ----bc---> Rh_*e⁻¹U(K)
```

commutes, the horizontal isomorphisms being the commutation isomorphisms of the right derived
functors with the forgetful functor `U`
(`etaleModuleForgetAb_map_etaleModuleDerivedBaseChangeMatePlus_app`). For any morphism
`c : X' ⟶ Z`, the map `Rc_*` of the abelian base change map is invertible at `U(K)` exactly when
the map `Rc_*` of the module base change map is invertible at `K`
(`isIso_rightDerivedFunctorPlus_map_smallEtaleDerivedBaseChangeAb_app_iff`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleForgetPullbackAbIso` — `U ⋙ g⁻¹ ≅ g⁻¹ ⋙ U`.
* `Stacks.EtaleCohomology.etaleModuleBaseChangeMate` — the underived base change map
  `(f')⁻¹ g_* ⟶ h_* e⁻¹` of sheaves of `Λ`-modules.
* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeMatePlus` — its descent to `D⁺`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetPullbackAbIso_unit` and
  `Stacks.EtaleCohomology.etaleModuleForgetPullbackAbIso_hom_app_comp_counit` — the comparison
  `U ⋙ g⁻¹ ≅ g⁻¹ ⋙ U` matches the units and counits of the two inverse image adjunctions.
* `Stacks.EtaleCohomology.natTransCompat_etaleModuleBaseChangeMate` — `U` carries the underived
  module base change map to `smallEtaleBaseChangeAb`.
* `Stacks.EtaleCohomology.etaleModuleForgetAb_map_etaleModuleDerivedBaseChangeMatePlus_app` — the
  square above.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_app_iff` — the two base change maps
  are invertible together.
* `Stacks.EtaleCohomology.isIso_rightDerivedFunctorPlus_map_smallEtaleDerivedBaseChangeAb_app_iff`
  — and so are their direct images along any `c : X' ⟶ Z`.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ]

/-- Postcomposition with the forgetful functor carries sheaves of modules to abelian sheaves. -/
local instance (Z : Scheme.{u}) : Z.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ Z.smallEtaleTopology

/-- Sheafification commutes with forgetting the module structure. -/
local instance (Z : Scheme.{u}) : Z.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ Z.smallEtaleTopology

attribute [local instance] forget₂_preservesLeftKanExtensions_smallEtaleBaseChange

/-! ### Forgetting the module structure and inverse image -/

section Pullback

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **Inverse image commutes with forgetting the module structure**, the inverse image of abelian
sheaves being `Stacks.EtaleCohomology.smallEtalePullbackAb`: the mate of the strict commutation
of direct image with forgetting the module structure. -/
def etaleModuleForgetPullbackAbIso :
    etaleModuleForgetAb.{u, 0} Λ X ⋙ smallEtalePullbackAb g ≅
      etaleModuleInverseImage.{u, 0} Λ g ⋙ etaleModuleForgetAb.{u, 0} Λ Y :=
  asIso (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g) X.smallEtaleTopology
    Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).natTrans

/-- **The comparison matches the units** of the inverse image adjunctions of sheaves of modules
and of abelian sheaves. -/
theorem etaleModuleForgetPullbackAbIso_unit (M : EtaleModules.{u, 0} Λ X) :
    (etaleModuleForgetAb.{u, 0} Λ X).map ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app M) =
      (smallEtaleAdjunctionAb g).unit.app ((etaleModuleForgetAb.{u, 0} Λ X).obj M) ≫
        (smallEtalePushforwardAb g).map ((etaleModuleForgetPullbackAbIso Λ g).hom.app M) :=
  coefficientSheafPullbackTwoSquare_unit (smallEtaleBaseChange g) X.smallEtaleTopology
    Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M

/-- **The comparison matches the counits** of the inverse image adjunctions of sheaves of modules
and of abelian sheaves. -/
theorem etaleModuleForgetPullbackAbIso_hom_app_comp_counit (N : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleForgetPullbackAbIso Λ g).hom.app ((etaleModuleDirectImage.{u, 0} Λ g).obj N) ≫
      (etaleModuleForgetAb.{u, 0} Λ Y).map ((etaleModuleInverseImageAdj.{u, 0} Λ g).counit.app N) =
    (smallEtaleAdjunctionAb g).counit.app ((etaleModuleForgetAb.{u, 0} Λ Y).obj N) := by
  apply ((smallEtaleAdjunctionAb g).homEquiv _ _).injective
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  refine Eq.trans ?_ ((smallEtaleAdjunctionAb g).right_triangle_components
    ((etaleModuleForgetAb.{u, 0} Λ Y).obj N)).symm
  refine ((congrArg (fun t ↦ (smallEtaleAdjunctionAb g).unit.app
      ((etaleModuleForgetAb.{u, 0} Λ X).obj ((etaleModuleDirectImage.{u, 0} Λ g).obj N)) ≫ t)
    (Functor.map_comp (smallEtalePushforwardAb g) _ _)).trans (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (· ≫ (smallEtalePushforwardAb g).map ((etaleModuleForgetAb.{u, 0} Λ Y).map
      ((etaleModuleInverseImageAdj.{u, 0} Λ g).counit.app N)))
    (etaleModuleForgetPullbackAbIso_unit Λ g
      ((etaleModuleDirectImage.{u, 0} Λ g).obj N)).symm).trans ?_
  refine (Functor.map_comp (etaleModuleForgetAb.{u, 0} Λ X)
    ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app ((etaleModuleDirectImage.{u, 0} Λ g).obj N))
    ((etaleModuleDirectImage.{u, 0} Λ g).map
      ((etaleModuleInverseImageAdj.{u, 0} Λ g).counit.app N))).symm.trans ?_
  refine (congrArg (etaleModuleForgetAb.{u, 0} Λ X).map
    ((etaleModuleInverseImageAdj.{u, 0} Λ g).right_triangle_components N)).trans ?_
  exact CategoryTheory.Functor.map_id _ _

end Pullback

/-! ### Forgetting the module structure and direct image -/

/-- **Direct image commutes with forgetting the module structure**, on the nose. -/
def etaleModuleDirectImageForgetAbIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleForgetAb.{u, 0} Λ Y ≅
      etaleModuleForgetAb.{u, 0} Λ X ⋙ smallEtalePushforwardAb f :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- Each component of `etaleModuleDirectImageForgetAbIso` is the identity. -/
@[simp]
theorem etaleModuleDirectImageForgetAbIso_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : EtaleModules.{u, 0} Λ X) :
    (etaleModuleDirectImageForgetAbIso Λ f).hom.app M = 𝟙 _ :=
  rfl

/-! ### The underived base change map -/

section Square

open Stacks.Cohomology.BaseChange in
/-- **Forgetting the module structure carries the composition isomorphism of direct images of
sheaves of modules to that of abelian sheaves.** -/
theorem compCompat_etaleModuleDirectImageCompIso {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    CompCompat (etaleModuleDirectImageForgetAbIso Λ a) (etaleModuleDirectImageForgetAbIso Λ b)
      (etaleModuleDirectImageForgetAbIso Λ (a ≫ b)) (etaleModuleDirectImageCompIso Λ a b).symm
      (smallEtalePushforwardAbCompIso a b) :=
  fun _ ↦ rfl

open Stacks.Cohomology.BaseChange in
/-- `compCompat_etaleModuleDirectImageCompIso` with the composite named. -/
theorem compCompat_etaleModuleDirectImageCompIso_ofEq {X Y Z : Scheme.{u}} (a : X ⟶ Y)
    (b : Y ⟶ Z) (c : X ⟶ Z) (hc : a ≫ b = c) :
    CompCompat (etaleModuleDirectImageForgetAbIso Λ a) (etaleModuleDirectImageForgetAbIso Λ b)
      (etaleModuleDirectImageForgetAbIso Λ c)
      ((etaleModuleDirectImageCompIso Λ a b).trans
        (eqToIso (congrArg (fun m => etaleModuleDirectImage.{u, 0} Λ m) hc))).symm
      ((smallEtalePushforwardAbCompIso a b).trans
        (eqToIso (congrArg smallEtalePushforwardAb hc))) := by
  subst hc
  exact fun _ ↦ rfl

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- The identification `e_* ⋙ g_* ≅ h_* ⋙ f'_*` of the two composite direct images of sheaves of
`Λ`-modules around a commutative square `h ≫ f' = e ≫ g`. -/
def etaleModuleDirectImageSquareIso :
    etaleModuleDirectImage.{u, 0} Λ e ⋙ etaleModuleDirectImage.{u, 0} Λ g ≅
      etaleModuleDirectImage.{u, 0} Λ h ⋙ etaleModuleDirectImage.{u, 0} Λ f' :=
  ((etaleModuleDirectImageCompIso Λ e g).trans
      (eqToIso (congrArg (fun m ↦ etaleModuleDirectImage.{u, 0} Λ m) w.symm))).symm.symm.trans
    (etaleModuleDirectImageCompIso Λ h f').symm

open Stacks.Cohomology.BaseChange in
/-- **The identification of the composite direct images is carried by forgetting the module
structure to the one of `smallEtaleBaseChangeAb`.** -/
theorem squareCompat_etaleModuleDirectImageSquareIso :
    SquareCompat (etaleModuleDirectImageForgetAbIso Λ e) (etaleModuleDirectImageForgetAbIso Λ g)
      (etaleModuleDirectImageForgetAbIso Λ h) (etaleModuleDirectImageForgetAbIso Λ f')
      (etaleModuleDirectImageSquareIso Λ f' g h e w)
      ((smallEtalePushforwardAbCompIso e g).trans
        ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
          (smallEtalePushforwardAbCompIso h f').symm)) :=
  SquareCompat.of_compCompat (compCompat_etaleModuleDirectImageCompIso_ofEq Λ e g (h ≫ f') w.symm)
    (compCompat_etaleModuleDirectImageCompIso Λ h f')

/-- **The base change map `(f')⁻¹ g_* ⟶ h_* e⁻¹` of sheaves of `Λ`-modules** of a commutative
square `h ≫ f' = e ≫ g`: the mate of the identification `e_* g_* ≅ h_* f'_*` of the two
composite direct images. -/
def etaleModuleBaseChangeMate :
    etaleModuleDirectImage.{u, 0} Λ g ⋙ etaleModuleInverseImage.{u, 0} Λ f' ⟶
      etaleModuleInverseImage.{u, 0} Λ e ⋙ etaleModuleDirectImage.{u, 0} Λ h :=
  Stacks.Cohomology.BaseChange.mate (etaleModuleInverseImageAdj.{u, 0} Λ f')
    (etaleModuleInverseImageAdj.{u, 0} Λ e) (etaleModuleDirectImage.{u, 0} Λ g)
    (etaleModuleDirectImage.{u, 0} Λ h) (etaleModuleDirectImageSquareIso Λ f' g h e w)

/-- **The module base change map is carried to the abelian one by forgetting the module
structure**, in the sense of `Stacks.Cohomology.BaseChange.NatTransCompat`. -/
theorem natTransCompat_etaleModuleBaseChangeMate :
    Stacks.Cohomology.BaseChange.NatTransCompat (etaleModuleDirectImageForgetAbIso Λ g)
      (etaleModuleDirectImageForgetAbIso Λ h) (etaleModuleForgetPullbackAbIso Λ f').symm
      (etaleModuleForgetPullbackAbIso Λ e).symm (etaleModuleBaseChangeMate Λ f' g h e w)
      (smallEtaleBaseChangeAb f' g h e w) := by
  refine Stacks.Cohomology.BaseChange.NatTransCompat.mate (etaleModuleInverseImageAdj.{u, 0} Λ f')
    (etaleModuleInverseImageAdj.{u, 0} Λ e) (smallEtaleAdjunctionAb f') (smallEtaleAdjunctionAb e)
    (ρe := etaleModuleDirectImageForgetAbIso Λ e) (ρf := etaleModuleDirectImageForgetAbIso Λ f')
    (fun x ↦ ?_) (fun t ↦ ?_) (squareCompat_etaleModuleDirectImageSquareIso Λ f' g h e w)
  · exact (Iso.inv_hom_id_app_assoc (etaleModuleForgetPullbackAbIso Λ f')
      ((etaleModuleDirectImage.{u, 0} Λ f').obj x) _).symm.trans
      (congrArg ((etaleModuleForgetPullbackAbIso Λ f').inv.app
        ((etaleModuleDirectImage.{u, 0} Λ f').obj x) ≫ ·)
        ((etaleModuleForgetPullbackAbIso_hom_app_comp_counit Λ f' x).trans
          ((Category.id_comp _).symm.trans (congrArg
            (· ≫ (smallEtaleAdjunctionAb f').counit.app ((etaleModuleForgetAb.{u, 0} Λ X').obj x))
            (CategoryTheory.Functor.map_id (smallEtalePullbackAb f')
              ((smallEtalePushforwardAb f').obj ((etaleModuleForgetAb.{u, 0} Λ X').obj x))).symm))))
  · refine (congrArg (· ≫ (etaleModuleDirectImageForgetAbIso Λ e).hom.app
        ((etaleModuleInverseImage.{u, 0} Λ e).obj t) ≫ (smallEtalePushforwardAb e).map
          ((etaleModuleForgetPullbackAbIso Λ e).symm.hom.app t))
      (etaleModuleForgetPullbackAbIso_unit Λ e t)).trans ?_
    refine (Category.assoc _ _ _).trans ((congrArg ((smallEtaleAdjunctionAb e).unit.app
      ((etaleModuleForgetAb.{u, 0} Λ T).obj t) ≫ ·) ?_).trans (Category.comp_id _))
    refine (congrArg ((smallEtalePushforwardAb e).map
      ((etaleModuleForgetPullbackAbIso Λ e).hom.app t) ≫ ·)
      (Category.id_comp ((smallEtalePushforwardAb e).map
        ((etaleModuleForgetPullbackAbIso Λ e).inv.app t)))).trans ?_
    refine (Functor.map_comp (smallEtalePushforwardAb e) _ _).symm.trans ?_
    refine (congrArg (smallEtalePushforwardAb e).map
      ((etaleModuleForgetPullbackAbIso Λ e).hom_inv_id_app t)).trans ?_
    exact CategoryTheory.Functor.map_id _ _

end Square

/-! ### The base change map on `D⁺` -/

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **The underlying complex of abelian sheaves reflects isomorphisms in `D⁺(X_étale, Λ)`.** -/
instance etaleModuleForgetAb_mapDerivedCategoryPlus_reflectsIsomorphisms (Z : Scheme.{u}) :
    (etaleModuleForgetAb.{u, 0} Λ Z).mapDerivedCategoryPlus.ReflectsIsomorphisms where
  reflects {A B} φ _ := by
    have h₁ : IsIso ((etaleModuleForgetAb.{u, 0} Λ Z).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map φ)) :=
      inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map
        ((etaleModuleForgetAb.{u, 0} Λ Z).mapDerivedCategoryPlus.map φ)))
    have h₂ : IsIso (DerivedCategory.Plus.ι.map φ) := by
      rw [DerivedCategory.isIso_iff] at h₁ ⊢
      intro n
      have : IsIso ((etaleModuleForgetAb.{u, 0} Λ Z).map
          ((DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Plus.ι.map φ))) := by
        rw [StacksDraft.DerivedCategoryHomology.map_homologyFunctor_map]
        have := h₁ n
        infer_instance
      exact isIso_of_reflects_iso _ (etaleModuleForgetAb.{u, 0} Λ Z)
    exact isIso_of_reflects_iso φ DerivedCategory.Plus.ι

/-- The underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic for the direct
image of abelian sheaves `Stacks.EtaleCohomology.smallEtalePushforwardAb` ([Stacks, Tag 03FD]). -/
@[sga "4 XVII 4.1.2" "special case"]
theorem rightAcyclic_smallEtalePushforwardAb_etaleModuleForgetAb_obj {X Y : Scheme.{u}}
    (f : X ⟶ Y) (I : EtaleModules.{u, 0} Λ X) (hI : Injective I) :
    (smallEtalePushforwardAb f).rightAcyclic ((etaleModuleForgetAb.{u, 0} Λ X).obj I) :=
  rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj Λ f I

/-- The underlying abelian sheaf of a sheaf of `Λ`-modules is acyclic for the inverse image of
abelian sheaves. -/
theorem rightAcyclic_smallEtalePullbackAb_etaleModuleForgetAb_obj {X Y : Scheme.{u}}
    (f : Y ⟶ X) (I : EtaleModules.{u, 0} Λ X) (_ : Injective I) :
    (smallEtalePullbackAb f).rightAcyclic ((etaleModuleForgetAb.{u, 0} Λ X).obj I) :=
  (smallEtalePullbackAb f).rightAcyclic_of_exact _

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The base change map `(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` on `D⁺` for sheaves of `Λ`-modules**: the
descent `Stacks.Cohomology.BaseChange.derived` of `etaleModuleBaseChangeMate`. -/
def etaleModuleDerivedBaseChangeMatePlus :
    (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus ⋙
        (etaleModuleInverseImage.{u, 0} Λ f').rightDerivedFunctorPlus ⟶
      (etaleModuleInverseImage.{u, 0} Λ e).rightDerivedFunctorPlus ⋙
        (etaleModuleDirectImage.{u, 0} Λ h).rightDerivedFunctorPlus :=
  letI : IsIso (etaleModuleInverseImage.{u, 0} Λ f').rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso (etaleModuleInverseImage.{u, 0} Λ f')
  Stacks.Cohomology.BaseChange.derived (etaleModuleDirectImage.{u, 0} Λ g)
    (etaleModuleDirectImage.{u, 0} Λ h) (etaleModuleInverseImage.{u, 0} Λ f')
    (etaleModuleInverseImage.{u, 0} Λ e) (etaleModuleBaseChangeMate Λ f' g h e w)
    (asIso (etaleModuleInverseImage.{u, 0} Λ f').rightDerivedFunctorPlusUnith)

/-- **Forgetting the module structure carries the module base change map on `D⁺` to the abelian
one**: for `K ∈ D⁺(T_étale, Λ)`, `U` of the module base change map at `K`, followed by the
commutation isomorphisms of `Rh_*` and `e⁻¹` with `U`, is the commutation isomorphisms of
`(f')⁻¹` and `Rg_*` with `U` followed by the abelian base change map at `U K`. -/
theorem etaleModuleForgetAb_map_etaleModuleDerivedBaseChangeMatePlus_app
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ T)) :
    (etaleModuleForgetAb.{u, 0} Λ X').mapDerivedCategoryPlus.map
        ((etaleModuleDerivedBaseChangeMatePlus Λ f' g h e w).app K) ≫
      (Functor.rightDerivedFunctorPlusExactSquareIso (etaleModuleDirectImageForgetAbIso Λ h)
          (rightAcyclic_smallEtalePushforwardAb_etaleModuleForgetAb_obj Λ h)).hom.app
        ((etaleModuleInverseImage.{u, 0} Λ e).rightDerivedFunctorPlus.obj K) ≫
      (smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusExactSquareIso (etaleModuleForgetPullbackAbIso Λ e).symm
          (rightAcyclic_smallEtalePullbackAb_etaleModuleForgetAb_obj Λ e)).hom.app K) =
    (Functor.rightDerivedFunctorPlusExactSquareIso (etaleModuleForgetPullbackAbIso Λ f').symm
        (rightAcyclic_smallEtalePullbackAb_etaleModuleForgetAb_obj Λ f')).hom.app
        ((etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.obj K) ≫
      (smallEtalePullbackAb f').rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusExactSquareIso (etaleModuleDirectImageForgetAbIso Λ g)
          (rightAcyclic_smallEtalePushforwardAb_etaleModuleForgetAb_obj Λ g)).hom.app K) ≫
      (smallEtaleDerivedBaseChangeAb f' g h e w).app
        ((etaleModuleForgetAb.{u, 0} Λ T).mapDerivedCategoryPlus.obj K) :=
  let : IsIso (etaleModuleInverseImage.{u, 0} Λ f').rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso (etaleModuleInverseImage.{u, 0} Λ f')
  Stacks.Cohomology.BaseChange.derived_exactTransport_app
    (rightAcyclic_smallEtalePushforwardAb_etaleModuleForgetAb_obj Λ g)
    (rightAcyclic_smallEtalePushforwardAb_etaleModuleForgetAb_obj Λ h)
    (rightAcyclic_smallEtalePullbackAb_etaleModuleForgetAb_obj Λ f')
    (rightAcyclic_smallEtalePullbackAb_etaleModuleForgetAb_obj Λ e)
    (natTransCompat_etaleModuleBaseChangeMate Λ f' g h e w) K

/-- In a square `x ≫ a = b ≫ y` with `a` and `b` invertible, `x` is invertible exactly when `y`
is. -/
private theorem isIso_iff_of_comp_eq {𝒞 : Type*} [Category* 𝒞] {A B A' B' : 𝒞} {x : A ⟶ B}
    {y : A' ⟶ B'} (a : B ⟶ B') (b : A ⟶ A') [IsIso a] [IsIso b] (hw : x ≫ a = b ≫ y) :
    IsIso x ↔ IsIso y := by
  rw [← isIso_comp_right_iff x a, hw, isIso_comp_left_iff]

/-- **The direct image of the abelian base change map is invertible exactly when the direct
image of the module base change map is.** For a morphism `c : X' ⟶ Z` and `K ∈ D⁺(T_étale, Λ)`,
`Rc_*` of the abelian base change map at the underlying complex of abelian sheaves of `K` is
invertible exactly when `Rc_*` of the module base change map at `K` is. -/
theorem isIso_rightDerivedFunctorPlus_map_smallEtaleDerivedBaseChangeAb_app_iff {Z : Scheme.{u}}
    (c : X' ⟶ Z) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ T)) :
    IsIso ((smallEtalePushforwardAb c).rightDerivedFunctorPlus.map
        ((smallEtaleDerivedBaseChangeAb f' g h e w).app
          ((etaleModuleForgetAb.{u, 0} Λ T).mapDerivedCategoryPlus.obj K))) ↔
      IsIso ((etaleModuleDirectImage.{u, 0} Λ c).rightDerivedFunctorPlus.map
        ((etaleModuleDerivedBaseChangeMatePlus Λ f' g h e w).app K)) := by
  have hsq := congrArg (smallEtalePushforwardAb c).rightDerivedFunctorPlus.map
    (etaleModuleForgetAb_map_etaleModuleDerivedBaseChangeMatePlus_app Λ f' g h e w K)
  simp only [Functor.map_comp] at hsq
  have hE := (Functor.rightDerivedFunctorPlusExactSquareIso (etaleModuleDirectImageForgetAbIso Λ c)
    (rightAcyclic_smallEtalePushforwardAb_etaleModuleForgetAb_obj Λ c)).hom.naturality
      ((etaleModuleDerivedBaseChangeMatePlus Λ f' g h e w).app K)
  simp only [Functor.comp_map] at hE
  exact ((isIso_iff_of_comp_eq _ _ (hsq.trans (Category.assoc _ _ _).symm)).symm.trans
    (isIso_iff_of_comp_eq _ _ hE).symm).trans
      (isIso_iff_of_reflects_iso _ (etaleModuleForgetAb.{u, 0} Λ Z).mapDerivedCategoryPlus)

/-- **The base change maps on `D⁺` are invertible together**: the abelian base change map is
invertible at the underlying complex of abelian sheaves of `K ∈ D⁺(T_étale, Λ)` exactly when the
module base change map is invertible at `K`. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_app_iff
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ T)) :
    IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app
        ((etaleModuleForgetAb.{u, 0} Λ T).mapDerivedCategoryPlus.obj K)) ↔
      IsIso ((etaleModuleDerivedBaseChangeMatePlus Λ f' g h e w).app K) :=
  ((isIso_iff_of_comp_eq _ _ ((etaleModuleForgetAb_map_etaleModuleDerivedBaseChangeMatePlus_app
    Λ f' g h e w K).trans (Category.assoc _ _ _).symm)).symm).trans
      (isIso_iff_of_reflects_iso _ (etaleModuleForgetAb.{u, 0} Λ X').mapDerivedCategoryPlus)

end Derived

end Stacks.EtaleCohomology

end
