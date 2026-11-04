module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Punctured
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.UngradedSymmetricUniversal
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.FunctorBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability

/-!
# The functor of points of the total space of a line bundle

Let `D` be a line-bundle situation: a morphism of schemes `X ⟶ S` together with an invertible
`𝒪_X`-module `L`. The total space `p : Tot(L) ⟶ X` of `L` is the relative spectrum of
`Sym(L) = ⨁_{n ≥ 0} L^{⊗ n}`, and this file computes the morphisms into it: for every scheme `Y`

`(Y ⟶ Tot(L))  ≃  Σ g : Y ⟶ X, (L ⟶ g_* 𝒪_Y)`,

the first component of the pair attached to `f` being `f ≫ p`. The bijection is natural in `Y`,
and it sends the zero section to the zero module morphism.

## Main definitions

* `Stacks.LineBundle.Situation.algebraPairEquiv`: for a fixed `g : Y ⟶ X`, the algebra data of a
  relative-spectrum pair over `g` is the same thing as a morphism of `𝒪_X`-modules
  `L ⟶ g_* 𝒪_Y`.
* `Stacks.LineBundle.Situation.totalSpaceHomEquiv`: the functor of points of the total space.

## Main results

* `Stacks.LineBundle.Situation.totalSpaceHomEquiv_fst`: the morphism to the base attached to
  `f : Y ⟶ Tot(L)` is `f ≫ p`.
* `Stacks.LineBundle.Situation.totalSpaceHomEquiv_comp`: the bijection is natural in `Y`:
  precomposing with `a : Y' ⟶ Y` precomposes the morphism to the base with `a` and postcomposes
  the module morphism with the canonical map `g_* 𝒪_Y ⟶ (a ≫ g)_* 𝒪_{Y'}`.
* `Stacks.LineBundle.Situation.totalSpaceHomEquiv_zeroSection`: the zero section goes to the
  zero module morphism, over the identity of the base.
* `Stacks.LineBundle.Situation.algebraSheafAugmentation_algebraSheafIncl`: the augmentation of
  `Sym(L)` kills every homogeneous local section of nonzero degree.

## References

* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### The algebra datum of a pair as a module morphism -/

/-- **The algebra datum of a relative-spectrum pair over a fixed `g : Y ⟶ X` is a morphism of
`𝒪_X`-modules `L ⟶ g_* 𝒪_Y`.** -/
def Situation.algebraPairEquiv {Y : Scheme.{u}} (g : Y ⟶ D.X) :
    (Under.mk D.algebraSheaf.hom.hom ⟶ Under.mk g.c) ≃
      (D.L ⟶ (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
  (AlgebraSheaf.pairHomEquiv D.algebraSheaf g).symm.trans
    (ungradedAlgebraSheafModuleHomEquiv D.symmetricAlgebra D.symmetricAlgebra_mul_comm
      (pushforwardAlgebra g) D.symmetricAlgebraGen D.isSymmetricAlgebra_symmetricAlgebra)

/-- The module morphism attached to the algebra datum of a pair, on a local section of `L`: it is
the datum evaluated at the degree-one local section of `Sym(L)` determined by that section. -/
theorem Situation.algebraPairEquiv_val_app {Y : Scheme.{u}} (g : Y ⟶ D.X)
    (φ : Under.mk D.algebraSheaf.hom.hom ⟶ Under.mk g.c) (U : D.X.Opens)
    (s : D.L.val.obj (op U)) :
    ((D.algebraPairEquiv g φ).val.app (op U)) s =
      (φ.right.app (op U)).hom
        (D.algebraSheafIncl 1 U (D.symmetricAlgebraGen.val.app (op U) s)) := rfl

/-- The passage from the algebra datum of a pair to a module morphism is compatible with
pullback of pairs along a morphism of test schemes. -/
theorem Situation.algebraPairEquiv_comp {Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (g : Y ⟶ D.X)
    (φ : Under.mk D.algebraSheaf.hom.hom ⟶ Under.mk g.c) :
    D.algebraPairEquiv (a ≫ g)
        (φ ≫ Under.homMk ((TopCat.Presheaf.pushforward CommRingCat g.base).map a.c) (by rfl)) =
      D.algebraPairEquiv g φ ≫
        AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMapAux g a) :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-! ### The functor of points -/

/-- **The functor of points of the total space of a line bundle**: a morphism from a scheme `Y`
into `Tot(L)` is the same thing as a morphism `g : Y ⟶ X` together with a morphism of
`𝒪_X`-modules `L ⟶ g_* 𝒪_Y`. -/
def Situation.totalSpaceHomEquiv (Y : Scheme.{u}) :
    (Y ⟶ D.totalSpace) ≃
      Σ g : Y ⟶ D.X, (D.L ⟶ (Scheme.Modules.pushforward g).obj
        (SheafOfModules.unit Y.ringCatSheaf)) :=
  (relativeSpecRepresentableBy D.relativeSpecSituation).homEquiv.trans
    (Equiv.sigmaCongrRight fun g => D.algebraPairEquiv g)

/-- **The morphism to the base attached to a morphism into the total space is its composite with
the projection.** -/
theorem Situation.totalSpaceHomEquiv_fst {Y : Scheme.{u}} (f : Y ⟶ D.totalSpace) :
    (D.totalSpaceHomEquiv Y f).1 = f ≫ D.totalSpaceToBase := rfl

/-- **The functor of points of the total space is natural in the test scheme.** Precomposing a
morphism `f : Y ⟶ Tot(L)` with `a : Y' ⟶ Y` precomposes the morphism to the base with `a` and
postcomposes the module morphism with the canonical map `g_* 𝒪_Y ⟶ (a ≫ g)_* 𝒪_{Y'}`. -/
theorem Situation.totalSpaceHomEquiv_comp {Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    (f : Y ⟶ D.totalSpace) :
    D.totalSpaceHomEquiv Y' (a ≫ f) =
      ⟨a ≫ (D.totalSpaceHomEquiv Y f).1,
        (D.totalSpaceHomEquiv Y f).2 ≫ AlgebraSheaf.underlyingModuleMap
          (pushforwardAlgebraMapAux (D.totalSpaceHomEquiv Y f).1 a)⟩ :=
  (congrArg (Equiv.sigmaCongrRight fun g => D.algebraPairEquiv g)
    ((relativeSpecRepresentableBy D.relativeSpecSituation).homEquiv_comp a f)).trans
    (congrArg (Sigma.mk _) (D.algebraPairEquiv_comp a _ _))

/-! ### The zero section -/

/-- **The augmentation of the algebra sheaf of a line bundle kills a homogeneous local section
of nonzero degree.** -/
theorem Situation.algebraSheafAugmentation_algebraSheafIncl {n : ℤ} (hn : n ≠ 0)
    (U : D.X.Opens) (x : (D.symmetricAlgebra.piece n).val.obj (op U)) :
    (D.algebraSheafAugmentation.hom.app (op U)).hom (D.algebraSheafIncl n U x) = 0 := by
  have hunit := ((sheafificationAdjunction (Opens.grothendieckTopology (D.X : TopCat))
      CommRingCat.{u}).homEquiv (ungradedCommPresheaf D.X D.symmetricAlgebra
        D.symmetricAlgebra_mul_comm) D.X.sheaf).apply_symm_apply
    (ungradedCommAugmentation D.symmetricAlgebra D.symmetricAlgebra_mul_comm D.pieceZeroIso
      D.pieceZeroIso_hom_one D.isZero_symmetricAlgebra_piece)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app hunit (op U))
    (D.symmetricAlgebra.toPresheafGradedAlgebra.incl n x)
  refine h.trans ?_
  show pieceZeroAugmentation D.symmetricAlgebra D.pieceZeroIso (op U)
    (D.symmetricAlgebra.toPresheafGradedAlgebra.degreeZeroComponent (op U)
      (D.symmetricAlgebra.toPresheafGradedAlgebra.incl n x)) = 0
  rw [D.symmetricAlgebra.toPresheafGradedAlgebra.degreeZeroComponent_incl_of_ne hn, map_zero]

/-- **The functor of points of the total space sends the zero section to the zero module
morphism**, over the identity of the base. -/
theorem Situation.totalSpaceHomEquiv_zeroSection :
    D.totalSpaceHomEquiv D.X D.zeroSection = ⟨𝟙 D.X, 0⟩ := by
  have h0 : (relativeSpecRepresentableBy D.relativeSpecSituation).homEquiv D.zeroSection =
      retractionPair D.relativeSpecSituation D.algebraSheafAugmentation.hom
        D.hom_comp_algebraSheafAugmentation :=
    (relativeSpecRepresentableBy D.relativeSpecSituation).homEquiv.apply_symm_apply _
  refine Eq.trans (congrArg (Equiv.sigmaCongrRight fun g => D.algebraPairEquiv g) h0) ?_
  refine congrArg (Sigma.mk (𝟙 D.X)) ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  obtain ⟨U⟩ := W
  exact (D.algebraPairEquiv_val_app (𝟙 D.X) _ U s).trans
    (D.algebraSheafAugmentation_algebraSheafIncl one_ne_zero U _)

end Stacks.LineBundle

end
