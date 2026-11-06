module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyAPushforward
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageAbelian
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap

/-!
# The base change condition `BC(f, n, q₀)` for higher direct images

Let `f : X ⟶ S` be a morphism of schemes and let `n` be an integer. Stacks 0F02 introduces the
condition `BC(f, n, q₀)`: for every commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  T
```

with `X' = X ×_S S'` and `Y = X' ×_{S'} T` and `g` quasi-compact and quasi-separated, and every
abelian sheaf `F` on the small étale site of `T` annihilated by `n`, the base change map
`(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism for `q ≤ q₀`. This file defines that
condition, together with the base change map it is about.

The base change map on higher direct images is obtained from the canonical derived base change
comparison. The underived map `(f')⁻¹ g_* ⟶ h_* e⁻¹` is the mate of the identification
`e_* g_* ≅ h_* (f')_*` of the two composite direct images of the square, and the derived
comparison `R(f')⁻¹ Rg_* ⟶ Rh_* Re⁻¹` is its descent along the derived-functor unit of `Rg_*`,
which determines it. Taking degree-`q` cohomology recovers the map on higher direct images once
both sides have been identified with cohomology of the derived composites, and both
identifications are constructed rather than assumed: inverse image is exact, so its right
derived functor is itself applied degreewise, whence the comparisons
`H^q(R(f')⁻¹K) ≅ (f')⁻¹H^q(K)` and `Re⁻¹(F[0]) ≅ (e⁻¹F)[0]`; combined with the comparison of
the injective-resolution and bounded-below conventions for the right derived functor, they pin
the degree-`q` map down in every degree rather than only in degree zero.

## Main definitions

* `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso`,
  `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso`,
  `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle`,
  `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso` — the right derived functor of
  an exact functor is the functor applied degreewise, hence commutes with cohomology and with
  the degree-`n` embedding.
* `Stacks.EtaleCohomology.smallEtalePullbackAb` — inverse image of abelian sheaves on the small
  étale sites.
* `Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso` — the composition isomorphism for
  direct image of abelian sheaves.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb` — the underived base change map
  `(f')⁻¹ g_* ⟶ h_* e⁻¹`.
* `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` — the derived base change comparison
  `R(f')⁻¹ Rg_* ⟶ Rh_* Re⁻¹`.
* `Stacks.EtaleCohomology.baseChangeSourceIso`,
  `Stacks.EtaleCohomology.baseChangeTargetIso` — the identifications of `(f')⁻¹ R^q g_*` and of
  `R^q h_* e⁻¹` with cohomology of the derived composites.
* `Stacks.EtaleCohomology.higherBaseChangeMapAb` — **[Stacks, Tag 0F02]** the base change map
  `(f')⁻¹ R^q g_* ⟶ R^q h_* e⁻¹` on higher direct images.
* `Stacks.EtaleCohomology.BaseChangeHolds` — **[Stacks, Tag 0F02]** the condition
  `BC(f, n, q₀)`.

## Main results

* `Stacks.EtaleCohomology.baseChangeSourceIso_hom_app_comp` — the base change map on higher
  direct images is the degree-`q` cohomology of the derived base change comparison, read
  through the two identifications.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff` — the base change map on higher
  direct images is invertible exactly when the degree-`q` cohomology of the derived comparison
  is, the two identifications it is defined through being isomorphisms.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.DerivedFunctor

/-! ### An exact functor and right derivation on bounded below derived categories

An exact functor acts on bounded below derived categories degreewise, by
`CategoryTheory.Functor.mapDerivedCategoryPlus`; that action *is* its total right derived
functor, because the derived-functor unit of an exact functor is invertible. Transporting the
degreewise description of the action along that identification gives the two comparisons used
below: the right derived functor of an exact functor commutes with `H^n`, and it sends `X[0]` to
`F(X)[0]`. -/

section Exact

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The total right derived functor of an exact functor is the functor itself, applied
degreewise.** Both sides lift the degreewise action along the localization of the bounded below
homotopy category, the right derived functor because its unit is invertible for an exact
functor. -/
public def exactMapDerivedCategoryPlusIso :
    F.mapDerivedCategoryPlus ≅ F.rightDerivedFunctorPlus :=
  letI : IsIso F.rightDerivedFunctorPlusUnith :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  Localization.liftNatIso DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
    (DerivedCategory.Plus.Qh ⋙ F.mapDerivedCategoryPlus)
    (DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus)
    F.mapDerivedCategoryPlus F.rightDerivedFunctorPlus
    (F.mapDerivedCategoryPlusFactorsh ≪≫ asIso F.rightDerivedFunctorPlusUnith)

/-- **The right derived functor of an exact functor commutes with cohomology.** The comparison
`H^n(RF(K)) ≅ F(H^n(K))` on the bounded below derived category, obtained from the unbounded
comparison `Stacks.DerivedFunctor.derivedHomologyIso` by identifying `RF` with the degreewise
action. -/
public def exactRightDerivedPlusHomologyIso (n : ℤ) :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D n ≅
      DerivedCategory.Plus.homologyFunctor C n ⋙ F :=
  Functor.isoWhiskerRight (exactMapDerivedCategoryPlusIso F).symm
      (DerivedCategory.Plus.homologyFunctor D n) ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι (derivedHomologyIso F n)

/-- **An exact functor commutes with the degree-`n` embedding of the bounded below derived
category.** The restriction to bounded below derived categories of Mathlib's unbounded
comparison `Functor.mapDerivedCategorySingleFunctor`, which exists because the inclusion of the
bounded below subcategory is fully faithful. -/
public def exactMapDerivedCategoryPlusSingle (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ⋙ F.mapDerivedCategoryPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor D n :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
    (F.mapDerivedCategorySingleFunctor n)

/-- **The right derived functor of an exact functor commutes with the degree-`n` embedding.**
The comparison `F(X)[n] ≅ RF(X[n])`, obtained from `exactMapDerivedCategoryPlusSingle` by
identifying the degreewise action with `RF`. -/
public def exactSingleFunctorRightDerivedPlusIso (n : ℤ) :
    F ⋙ DerivedCategory.Plus.singleFunctor D n ≅
      DerivedCategory.Plus.singleFunctor C n ⋙ F.rightDerivedFunctorPlus :=
  (exactMapDerivedCategoryPlusSingle F n).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C n)
      (exactMapDerivedCategoryPlusIso F)

end Exact

end Stacks.DerivedFunctor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- Inverse image of abelian sheaves on the small étale sites along `f : X ⟶ Y`: the left
adjoint of `smallEtalePushforwardAb f`. -/
public abbrev smallEtalePullbackAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) Ab.{u + 1} ⥤ Sheaf (smallEtaleTopology X) Ab.{u + 1} :=
  (smallEtaleBaseChange f).sheafPullback Ab.{u + 1}
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- Abelian sheaves on a small étale site have enough injectives: the site is essentially
small, so the category is Grothendieck abelian. -/
public instance smallEtaleAbSheaf_enoughInjectives (X : Scheme.{u}) :
    EnoughInjectives (Sheaf (smallEtaleTopology X) Ab.{u + 1}) := by
  let : EssentiallySmall.{u + 1} X.Etale := inferInstance
  let : IsGrothendieckAbelian.{u + 1} (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} (smallEtaleTopology X) Ab.{u + 1}
  exact IsGrothendieckAbelian.enoughInjectives

/-- Direct image of abelian sheaves on the small étale sites is additive. -/
public instance smallEtalePushforwardAb_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtalePushforwardAb f).Additive where
  map_add := by intros; rfl

/-- Inverse image of abelian sheaves on the small étale sites is additive, being exact. -/
public instance smallEtalePullbackAb_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtalePullbackAb f).Additive :=
  exactFunctor_le_additiveFunctor _ _ _ (smallEtaleAbSheafPullback_exact f)

/-- Inverse image of abelian sheaves on the small étale sites preserves finite limits. -/
public instance smallEtalePullbackAb_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (smallEtalePullbackAb f) :=
  ((exactFunctor_iff _).mp (smallEtaleAbSheafPullback_exact f)).1

/-- Inverse image of abelian sheaves on the small étale sites preserves finite colimits. -/
public instance smallEtalePullbackAb_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (smallEtalePullbackAb f) :=
  ((exactFunctor_iff _).mp (smallEtaleAbSheafPullback_exact f)).2

/-- The canonical composition isomorphism `g_* ∘ f_* ≅ (f ≫ g)_*` for direct image of abelian
sheaves on the small étale sites, obtained from `smallEtaleBaseChangeComp` by transport through
`Functor.sheafPushforwardContinuousComp'`. -/
public def smallEtalePushforwardAbCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtalePushforwardAb f ⋙ smallEtalePushforwardAb g ≅
      smallEtalePushforwardAb (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp f g).symm _ _ _ _

section BaseChangeSquare

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- The underived base change map `(f')⁻¹ g_* ⟶ h_* e⁻¹` on abelian small étale sheaves of a
commutative square: the mate of the identification `e_* g_* ≅ h_* (f')_*` of the two composite
direct images under the two inverse-image/direct-image adjunctions. -/
public def smallEtaleBaseChangeAb :
    smallEtalePushforwardAb g ⋙ smallEtalePullbackAb f' ⟶
      smallEtalePullbackAb e ⋙ smallEtalePushforwardAb h :=
  Stacks.Cohomology.BaseChange.mate (smallEtaleAdjunctionAb f') (smallEtaleAdjunctionAb e)
    (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
    ((smallEtalePushforwardAbCompIso e g).trans
      ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
        (smallEtalePushforwardAbCompIso h f').symm))

/-- The canonical derived base change comparison `R(f')⁻¹ Rg_* ⟶ Rh_* R e⁻¹` on bounded below
derived categories of abelian small étale sheaves: the descent of `smallEtaleBaseChangeAb`
along the derived-functor unit of `Rg_*`, which determines it. -/
public def smallEtaleDerivedBaseChangeAb :
    (smallEtalePushforwardAb g).rightDerivedFunctorPlus ⋙
        (smallEtalePullbackAb f').rightDerivedFunctorPlus ⟶
      (smallEtalePullbackAb e).rightDerivedFunctorPlus ⋙
        (smallEtalePushforwardAb h).rightDerivedFunctorPlus :=
  letI : IsIso (smallEtalePullbackAb f').rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso (smallEtalePullbackAb f')
  Stacks.Cohomology.BaseChange.derived (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
    (smallEtalePullbackAb f') (smallEtalePullbackAb e) (smallEtaleBaseChangeAb f' g h e w)
    (asIso (smallEtalePullbackAb f').rightDerivedFunctorPlusUnith)

/-- The natural identification of `(f')⁻¹ R^q g_*` with the degree-`q` cohomology of the
bounded below derived source `R(f')⁻¹ Rg_*`: the comparison of the injective-resolution and
bounded-below conventions for the right derived functor of `g_*`, followed by the comparison of
the exact functor `(f')⁻¹` with cohomology. -/
public def baseChangeSourceIso (q : ℕ) :
    (smallEtalePushforwardAb g).rightDerived q ⋙ smallEtalePullbackAb f' ≅
      DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0 ⋙
        (smallEtalePushforwardAb g).rightDerivedFunctorPlus ⋙
        (smallEtalePullbackAb f').rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ) :=
  Functor.isoWhiskerRight
      (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q)
      (smallEtalePullbackAb f') ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0 ⋙
        (smallEtalePushforwardAb g).rightDerivedFunctorPlus)
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
        (smallEtalePullbackAb f') (q : ℤ)).symm

/-- The natural identification of `R^q h_* e⁻¹` with the degree-`q` cohomology of the bounded
below derived target `Rh_* Re⁻¹`: the comparison of the injective-resolution and bounded-below
conventions for the right derived functor of `h_*`, followed by the comparison of the exact
functor `e⁻¹` with the degree-zero embedding. -/
public def baseChangeTargetIso (q : ℕ) :
    smallEtalePullbackAb e ⋙ (smallEtalePushforwardAb h).rightDerived q ≅
      DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0 ⋙
        (smallEtalePullbackAb e).rightDerivedFunctorPlus ⋙
        (smallEtalePushforwardAb h).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ) :=
  Functor.isoWhiskerLeft (smallEtalePullbackAb e)
      (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) q) ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (smallEtalePullbackAb e) 0)
      ((smallEtalePushforwardAb h).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ))

/-- **The base change map on higher direct images**, `(f')⁻¹ R^q g_* ⟶ R^q h_* e⁻¹`, for abelian
sheaves on the small étale sites of a commutative square. It is the degree-`q` cohomology of the
canonical derived base change comparison `smallEtaleDerivedBaseChangeAb`, transported along the
canonical identifications `baseChangeSourceIso` and `baseChangeTargetIso` of the two sides with
cohomology of the bounded below derived composites. -/
@[stacks 0F02 "bc"]
public def higherBaseChangeMapAb (q : ℕ) :
    (smallEtalePushforwardAb g).rightDerived q ⋙ smallEtalePullbackAb f' ⟶
      smallEtalePullbackAb e ⋙ (smallEtalePushforwardAb h).rightDerived q :=
  (baseChangeSourceIso f' g q).hom ≫
    Functor.whiskerLeft
      (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0)
      (Functor.whiskerRight (smallEtaleDerivedBaseChangeAb f' g h e w)
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ))) ≫
    (baseChangeTargetIso h e q).inv

/-- The component of `higherBaseChangeMapAb` at `F`, unfolded to its three factors. -/
private theorem higherBaseChangeMapAb_app_eq (q : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (higherBaseChangeMapAb f' g h e w q).app F =
      (baseChangeSourceIso f' g q).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ)).map
          ((smallEtaleDerivedBaseChangeAb f' g h e w).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F)) ≫
        (baseChangeTargetIso h e q).inv.app F := rfl

/-- **The base change map on higher direct images is the degree-`q` cohomology of the derived
base change comparison.** This is how `higherBaseChangeMapAb` is constructed; recording it
pins the degreewise map to the derived one in *every* degree, not only in degree zero, and lets
clients rewrite between the two forms. -/
public theorem baseChangeSourceIso_hom_app_comp (q : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (baseChangeSourceIso f' g q).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ)).map
          ((smallEtaleDerivedBaseChangeAb f' g h e w).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F)) =
      (higherBaseChangeMapAb f' g h e w q).app F ≫ (baseChangeTargetIso h e q).hom.app F := by
  rw [higherBaseChangeMapAb_app_eq]
  simp

/-- **The base change map on higher direct images is invertible exactly when the derived
comparison is.** The two identifications `baseChangeSourceIso` and `baseChangeTargetIso` through
which `higherBaseChangeMapAb` is defined are isomorphisms, so the degreewise condition and the
degree-`q` cohomology of the derived base change comparison stand or fall together. In
particular the condition `BaseChangeHolds` below is not invertibility of something invertible by
construction. -/
public theorem isIso_higherBaseChangeMapAb_app_iff (q : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f' g h e w q).app F) ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor
        (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ)).map
        ((smallEtaleDerivedBaseChangeAb f' g h e w).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F))) := by
  rw [higherBaseChangeMapAb_app_eq, isIso_comp_left_iff, isIso_comp_right_iff]

end BaseChangeSquare

/-- **The condition `BC(f, n, q₀)` of Stacks 0F02.** For `f : X ⟶ S` a morphism of schemes and
`n` an integer, `BC(f, n, q₀)` holds if for every commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  T
```

in which `X' = X ×_S S'` and `Y = X' ×_{S'} T` and `g` is quasi-compact and quasi-separated,
and every abelian sheaf `F` on the small étale site of `T` annihilated by `n`, the base change
map `(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism for every `q ≤ q₀`.

The two cartesian squares are the hypotheses `IsPullback p f' f s` and `IsPullback h e f' g`;
the map whose invertibility is asserted is `higherBaseChangeMapAb`, the base change map on
higher direct images. Annihilation by `n` is imposed on every section of `F`, which is the same
as annihilation of `F` itself. -/
@[stacks 0F02]
public abbrev BaseChangeHolds {X S : Scheme.{u}} (f : X ⟶ S) (n q₀ : ℤ) : Prop :=
  ∀ {S' X' T Y : Scheme.{u}} (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_hp : IsPullback p f' f s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    (sq : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}),
    (∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0) →
      ∀ q : ℕ, (q : ℤ) ≤ q₀ → IsIso ((higherBaseChangeMapAb f' g h e sq.w q).app F)

end Stacks.EtaleCohomology

end
