module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardRightExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedOfExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunctionOfToposHom

/-!
# Ext groups into the direct image along a morphism of ringed topoi with exact direct image

Let `f : (Sh(C), 𝒪_X) ⟶ (Sh(D), 𝒪_Y)` be a morphism of ringed topoi whose direct image of
sheaves of modules `f_*` is exact, for instance because the direct image of sheaves of sets is an
equivalence, as for a thickening of algebraic spaces. Then no derivation happens: the total direct
image `Rf_*` is the functor `f_*` induces degreewise on derived categories, so it sends a sheaf
`G` placed in degree `m` to `f_*G` placed in degree `m`. Combined with the adjunction
`Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6] this identifies, for every `K ∈ D(𝒪_Y)`, every sheaf of
`𝒪_X`-modules `G` and every `n : ℤ`,
`Hom_{D(𝒪_Y)}(K, (f_*G)[n]) = Hom_{D(𝒪_X)}(Lf^*K, G[n])`,
additively.

## Main definitions

* `Stacks.Cohomology.DerivedPushforward.derivedPushforwardIsoMapDerivedCategoryOfExact`: for an
  exact `f_*`, `Rf_* ≅ f_*.mapDerivedCategory`.
* `Stacks.Cohomology.DerivedPushforward.derivedPushforwardSingleIsoOfExact`:
  `Rf_*(G[0]⟦n⟧) ≅ (f_*G)[0]⟦n⟧`.
* `Stacks.Cohomology.DerivedPushforward.homShiftSingleAddEquivOfExact`: the identification of
  the Ext groups, as an additive equivalence; `homShiftSingleEquivOfExact` is the underlying
  equivalence of types.
* `Stacks.Cohomology.DerivedPushforward.homShiftSingleAddEquivOfPreservesEpimorphisms`,
  `Stacks.Cohomology.DerivedPushforward.homShiftSingleAddEquivOfIsEquivalence`: the same when
  the direct image of sheaves of sets preserves epimorphisms, respectively is an equivalence.

## Implementation notes

Exactness is asked of `f_*` only as preservation of finite colimits: the direct image of
modules preserves finite limits for every morphism of ringed topoi
(`AlgebraicGeometry.RingedToposHom.pushforwardModules_preservesFiniteLimits`). The shift is
not commuted past `Rf_*`: `G[0]⟦n⟧` is rewritten as `G` placed in degree `-n`, where the
compatibility of `f_*.mapDerivedCategory` with the single functors applies directly.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedToposHom

universe u

namespace Stacks.Cohomology.DerivedPushforward

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] pushforwardModules_additive pushforwardModules_preservesFiniteLimits

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y)

section Exact

variable [PreservesFiniteColimits (pushforwardModules f)]

/-- **For an exact direct image of modules the total direct image is not derived**: `Rf_*` is
the functor `f_*` induces degreewise on the derived categories. -/
def derivedPushforwardIsoMapDerivedCategoryOfExact :
    derivedPushforward (X := X) (Y := Y) f ≅ (pushforwardModules f).mapDerivedCategory :=
  Stacks.Homology.rightDerivedIsoMapDerivedCategory (pushforwardModules f) _
    ((pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))

/-- For an exact direct image of modules, the total direct image of a sheaf of modules placed in
degree `m` is its direct image placed in degree `m`. -/
def derivedPushforwardSingleIsoOfExact'
    (G : SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O)) (m : ℤ) :
    (derivedPushforward f).obj ((DerivedCategory.singleFunctor _ m).obj G) ≅
      (DerivedCategory.singleFunctor _ m).obj ((pushforwardModules f).obj G) :=
  (derivedPushforwardIsoMapDerivedCategoryOfExact f).app _ ≪≫
    ((pushforwardModules f).mapDerivedCategorySingleFunctor m).app G

/-- For an exact direct image of modules, `Rf_*(G[0]⟦n⟧) ≅ (f_*G)[0]⟦n⟧`. -/
def derivedPushforwardSingleIsoOfExact
    (G : SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ) :
    (derivedPushforward f).obj (((DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj ((pushforwardModules f).obj G))⟦n⟧ :=
  (derivedPushforward f).mapIso
      (((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by omega)).app G) ≪≫
    derivedPushforwardSingleIsoOfExact' f G (-n) ≪≫
    (((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by omega)).app _).symm

/-- **Ext into the direct image along a morphism of ringed topoi with exact direct image.**
For every `K ∈ D(𝒪_Y)`, every sheaf of `𝒪_X`-modules `G` and every `n : ℤ`,
`Hom_{D(𝒪_Y)}(K, (f_*G)[0]⟦n⟧) ≃ Hom_{D(𝒪_X)}(Lf^*K, G[0]⟦n⟧)`, as abelian groups. It is the
adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6 composed with `Rf_*(G[0]⟦n⟧) ≅ (f_*G)[0]⟦n⟧`. -/
def homShiftSingleAddEquivOfExact
    (K : DerivedCategory (SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.O)))
    (G : SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ) :
    (K ⟶ ((DerivedCategory.singleFunctor _ 0).obj ((pushforwardModules f).obj G))⟦n⟧) ≃+
      ((DerivedPullbackOfToposHom.derivedPullback f).obj K ⟶
        ((DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) :=
  have := (derivedPullbackPushforwardAdjunctionOfToposHom f).rightAdjoint_preservesLimits
  have : PreservesBinaryBiproducts (derivedPushforward (X := X) (Y := Y) f) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : (derivedPushforward (X := X) (Y := Y) f).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have := (derivedPullbackPushforwardAdjunctionOfToposHom f).left_adjoint_additive
  (AddEquiv.mk ((Iso.refl K).homCongr (derivedPushforwardSingleIsoOfExact f G n).symm)
      (fun a b ↦ by simp [Iso.homCongr_apply, Preadditive.add_comp])).trans
    ((derivedPullbackPushforwardAdjunctionOfToposHom f).homAddEquiv _ _).symm

/-- **Ext into the direct image along a morphism of ringed topoi with exact direct image**, as
an equivalence of types: `Hom_{D(𝒪_Y)}(K, (f_*G)[0]⟦n⟧) ≃ Hom_{D(𝒪_X)}(Lf^*K, G[0]⟦n⟧)`. -/
def homShiftSingleEquivOfExact
    (K : DerivedCategory (SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.O)))
    (G : SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ) :
    (K ⟶ ((DerivedCategory.singleFunctor _ 0).obj ((pushforwardModules f).obj G))⟦n⟧) ≃
      ((DerivedPullbackOfToposHom.derivedPullback f).obj K ⟶
        ((DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) :=
  (homShiftSingleAddEquivOfExact f K G n).toEquiv

/-- `homShiftSingleEquivOfExact` is the adjunction `Lf^* ⊣ Rf_*` after
`Rf_*(G[0]⟦n⟧) ≅ (f_*G)[0]⟦n⟧`. -/
theorem homShiftSingleEquivOfExact_apply
    (K : DerivedCategory (SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.O)))
    (G : SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ)
    (a : K ⟶ ((DerivedCategory.singleFunctor _ 0).obj ((pushforwardModules f).obj G))⟦n⟧) :
    homShiftSingleEquivOfExact f K G n a =
      ((derivedPullbackPushforwardAdjunctionOfToposHom f).homEquiv _ _).symm
        (a ≫ (derivedPushforwardSingleIsoOfExact f G n).inv) := by
  simp [homShiftSingleEquivOfExact, homShiftSingleAddEquivOfExact, Iso.homCongr_apply]

end Exact

/-- `homShiftSingleAddEquivOfExact` when the direct image of sheaves of *sets* preserves
epimorphisms: the direct image of modules is then exact
(`AlgebraicGeometry.RingedToposHom.preservesFiniteColimits_pushforwardModules`). -/
def homShiftSingleAddEquivOfPreservesEpimorphisms
    [Functor.PreservesEpimorphisms f.toToposHom.pushforward]
    (K : DerivedCategory (SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.O)))
    (G : SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ) :
    (K ⟶ ((DerivedCategory.singleFunctor _ 0).obj ((pushforwardModules f).obj G))⟦n⟧) ≃+
      ((DerivedPullbackOfToposHom.derivedPullback f).obj K ⟶
        ((DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) :=
  have := preservesFiniteColimits_pushforwardModules f
  homShiftSingleAddEquivOfExact f K G n

/-- **Ext into the direct image along a morphism of ringed topoi whose direct image of sheaves of
sets is an equivalence** (for instance a thickening of algebraic spaces):
`Hom_{D(𝒪_Y)}(K, (f_*G)[0]⟦n⟧) ≃+ Hom_{D(𝒪_X)}(Lf^*K, G[0]⟦n⟧)`. An equivalence preserves
epimorphisms, so `homShiftSingleAddEquivOfPreservesEpimorphisms` applies. -/
def homShiftSingleAddEquivOfIsEquivalence [f.toToposHom.pushforward.IsEquivalence]
    (K : DerivedCategory (SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.O)))
    (G : SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ) :
    (K ⟶ ((DerivedCategory.singleFunctor _ 0).obj ((pushforwardModules f).obj G))⟦n⟧) ≃+
      ((DerivedPullbackOfToposHom.derivedPullback f).obj K ⟶
        ((DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) :=
  homShiftSingleAddEquivOfPreservesEpimorphisms f K G n

end Stacks.Cohomology.DerivedPushforward
