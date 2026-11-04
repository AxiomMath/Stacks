module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnTheSlice
public import StacksFrontier.AlgebraicGeometry.Topologies.CoordinateAlgebraComparison

/-!
# The Čech powers of the associated module on an affine slice

Let `S` be a scheme, `F` a quasi-coherent `𝒪_S`-module, `U` an object of `Over S` with affine
total space, and write `R = Γ(U.left, 𝒪)` and `M = Fᵃ(U)`.  For an object `Y` of the slice at
`U` whose fibre powers `Y ×_U ⋯ ×_U Y` all have affine total space, the cosimplicial
`R`-module of sections of `Fᵃ` on those powers is the Amitsur coefficient cosimplicial module
`Γ(Y^{•}, 𝒪) ⊗_R M`.

This is the coefficient hypothesis `hpow` of
`AlgebraicGeometry.isZero_cechCohomology_singleton_succ_overAffine`, proved once and for all
rather than assumed, and for a general object `Y` of `Over U` rather than only for the objects
`AlgebraicGeometry.overAffineAlgSpec U |>.obj (op a)` that hypothesis is instantiated at.

Three things are composed.  `Stacks.Sites.tensorToSections` is the comparison
`Γ(Z, 𝒪) ⊗_R M ⟶ Fᵃ(Z)`, natural on all of `(Over U)ᵒᵖ` and an isomorphism at an object with
affine total space; whiskering it along the Čech nerve of `Y ⟶ U` and using the affineness
hypothesis at every simplex makes it an isomorphism of `AddCommGrpCat`-valued cosimplicial
objects.  That isomorphism is then lifted to `ModuleCat R` — the forgetful functor
`forget₂ (ModuleCat R) AddCommGrpCat` is faithful, so the only thing to check is that the
components commute with the action of `R`, which on the Amitsur side is the action on the first
tensor factor and on the sections side is `Stacks.Sites.sliceAssociatedPresheafModule`.
Finally `AlgebraicGeometry.powerSectionsAmitsurCoefficientsIso` replaces
`Stacks.Sites.gammaAlg` by the left adjoint `AlgebraicGeometry.overAffineAlgΓ`, which is the
coordinate-algebra functor the Čech-to-Amitsur comparison is stated against.

## Main definitions

* `Stacks.ModuleCatSites.natIsoOfForget₂`: a natural isomorphism of `ModuleCat R`-valued
  functors from one of the underlying `AddCommGrpCat`-valued functors together with the
  compatibility with the action of `R`.
* `AlgebraicGeometry.powerSectionsTensorToSections` and
  `AlgebraicGeometry.powerSectionsTensorToSectionsIso`: the coefficient comparison whiskered
  along the Čech nerve of `Y ⟶ U`, as a morphism and — under the affineness hypothesis — as an
  isomorphism of `AddCommGrpCat`-valued cosimplicial objects.
* `AlgebraicGeometry.powerSectionsSliceAssociatedModuleIso`: **the coefficient hypothesis of
  [Stacks, Tag 03FJ]**, for a general object of the slice with affine fibre powers.

## Main results

* `Stacks.Sites.gammaAlg_smul_smul` and `Stacks.Sites.tensorToSectionsApp_comp_smul`: **the
  comparison is `R`-linear**, first on the generators and then as an equation of morphisms of
  abelian groups.

## Implementation notes

The `R`-linearity is the whole content of the file, and it is one computation on a generator
`a ⊗ m`: the action of `r` on the Amitsur side goes through
`algebraMap R (ULift R)` and then `CategoryTheory.ModuleCat.restrictScalars`, so it multiplies
`a` by the image of `r` under the structure map of `Stacks.Sites.gammaAlg`, which by
`Stacks.Sites.gammaAlg_algebraMap` is `Γ` of the structure morphism of `Z`; the action of `r` on
the sections side is `Module.compHom` along the very same map, by
`Stacks.Sites.sliceAssociatedPresheafModule`.  So `Algebra.smul_def` and `mul_smul` are the only
steps that are not `rfl`.

`Stacks.Sites.tensorToSectionsApp_comp_smul` is phrased with `CategoryTheory.ModuleCat.smul`
rather than with `•`: the two actions of `R` it relates live on the objects of `ModuleCat R`
produced by `CategoryTheory.ModuleCat.restrictScalars` and by
`Stacks.Sites.sliceAssociatedModuleCatObj`, and are not findable by instance search at the
spellings of the carriers that appear in the goal.  `CategoryTheory.ModuleCat.smul` names them
without any search, and it is also the form `CategoryTheory.ModuleCat.isoMk` asks for.  The
generator computation `Stacks.Sites.gammaAlg_smul_smul`, by contrast, only ever uses the
coordinate-algebra action, which instance search does find, so it is stated with `•`.

`Stacks.Sites.instModuleCoeffSectionsId` re-registers `Stacks.Sites.instModuleCoeffSections` at
`toOver = 𝟭 (Over S)`.  That is not redundant: the general instance concludes a `Module`
structure over `Γ(((𝟭 (Over S)).obj X).left, 𝒪)`, and instance search will not unfold
`CategoryTheory.Functor.id` to match it against the `Γ(X.left, 𝒪)` that the statements here —
and `Stacks.Descent.amitsurCoefficients` — are phrased with.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped TensorProduct

universe v u u₁ v₁

namespace Stacks.ModuleCatSites

/-- **A natural isomorphism of `ModuleCat R`-valued functors from its underlying natural
isomorphism of abelian groups.**  The forgetful functor
`CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat` is faithful, so naturality is inherited and
the only thing to supply is that every component commutes with the action of `R`. -/
public def natIsoOfForget₂ {R : Type u} [Ring R] {J : Type u₁} [Category.{v₁} J]
    {X Y : J ⥤ ModuleCat.{v} R}
    (α : X ⋙ forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ≅
      Y ⋙ forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})
    (hα : ∀ (j : J) (r : R),
      α.hom.app j ≫ (Y.obj j).smul r = (X.obj j).smul r ≫ α.hom.app j) :
    X ≅ Y :=
  NatIso.ofComponents (fun j => ModuleCat.isoMk (α.app j) (hα j)) (by
    intro i j f
    apply (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).map_injective
    rw [Functor.map_comp, Functor.map_comp, ModuleCat.isoMk_hom, ModuleCat.isoMk_hom,
      ModuleCat.forget₂_map_homMk, ModuleCat.forget₂_map_homMk]
    exact α.hom.naturality f)

end Stacks.ModuleCatSites

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] (U : Over S)

/-- **The sections of `Fᵃ` over an object of `Over S` are a module over its coordinate ring**,
for the site presented by the identity functor.  This is
`Stacks.Sites.instModuleCoeffSections` at `toOver = 𝟭 (Over S)`; instance search does not find
that one here, because matching its conclusion against this one needs
`CategoryTheory.Functor.id` to unfold, which it does not do. -/
public instance instModuleCoeffSectionsId (X : Over S) :
    Module (Γ(X.left, ⊤) : Type u)
      ((associatedPresheaf S F (𝟭 (Over S))).obj (op X) : Type u) :=
  instModuleCoeffSections S F (𝟭 (Over S)) X

/-- **The action of the lifted base ring on the coordinate algebra of an object of the slice,
read through the sections of `Fᵃ`.**  Multiplying the coordinate-algebra factor by a scalar of
`ULift Γ(U.left, 𝒪)` and then acting on a section is acting by the image of that scalar under
the structure map of `Stacks.Sites.gammaAlg`.  Nothing but `Algebra.smul_def` and `mul_smul`;
the point is that the image of the structure map is computed by
`Stacks.Sites.gammaAlg_algebraMap` as `Γ` of the structure morphism of `Z`, which is how
`Stacks.Sites.sliceAssociatedPresheafModule` makes `Γ(U.left, 𝒪)` act. -/
public theorem gammaAlg_smul_smul (Z : (Over U)ᵒᵖ)
    (c : ULift.{u} (coeffBase S (𝟭 (Over S)) U))
    (a : (((gammaAlg S (𝟭 (Over S)) U).obj Z : CommAlgCat.{u} _) : Type u))
    (y : ((associatedPresheaf S F (𝟭 (Over S))).obj (op Z.unop.left) : Type u)) :
    (c • a) • y =
      algebraMap (ULift.{u} (coeffBase S (𝟭 (Over S)) U))
        (((gammaAlg S (𝟭 (Over S)) U).obj Z : CommAlgCat.{u} _) : Type u) c • (a • y) := by
  rw [Algebra.smul_def, mul_smul]

/-- **The coefficient comparison is `Γ(U.left, 𝒪)`-linear.**  The equation of morphisms of
abelian groups that `Stacks.ModuleCatSites.natIsoOfForget₂` consumes: two additive maps out of a
tensor product agreeing on the generators by
`Stacks.Sites.gammaAlg_smul_smul`. -/
public theorem tensorToSectionsApp_comp_smul (Z : (Over U)ᵒᵖ) (r : (Γ(U.left, ⊤) : Type u)) :
    tensorToSectionsApp S F (𝟭 (Over S)) U Z ≫ (sliceAssociatedModuleCatObj F U Z).smul r =
      ((Stacks.Descent.amitsurCoefficients.{u, u, u} (Γ(U.left, ⊤) : Type u)
          (coeffModule S F (𝟭 (Over S)) U)).obj
        ((gammaAlg S (𝟭 (Over S)) U).obj Z)).smul r ≫
        tensorToSectionsApp S F (𝟭 (Over S)) U Z := by
  apply AddCommGrpCat.hom_ext
  refine addHom_ext_tmul (Rr := ULift.{u} (coeffBase S (𝟭 (Over S)) U))
    (Mm := (((gammaAlg S (𝟭 (Over S)) U).obj Z : CommAlgCat.{u} _) : Type u))
    (Nn := coeffModule S F (𝟭 (Over S)) U)
    (Pp := ((associatedPresheaf S F (𝟭 (Over S))).obj (op Z.unop.left) : Type u))
    (fun a m => ?_)
  exact (gammaAlg_smul_smul S F U Z (@ULift.up.{u, u} (coeffBase S (𝟭 (Over S)) U) r) a
    (coeffRestrict S F (𝟭 (Over S)) U Z m)).symm

end Stacks.Sites

namespace AlgebraicGeometry

open Stacks.Sites

/-- **The coefficient comparison along the Čech nerve of an object of the slice.**
`Stacks.Sites.tensorToSections` whiskered along the Čech nerve of `Y ⟶ U`: a morphism of
`AddCommGrpCat`-valued cosimplicial objects from the Amitsur coefficients of the coordinate
algebras of the fibre powers of `Y` to the sections of `Fᵃ` on those powers. -/
public def powerSectionsTensorToSections (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (U : Over S) (Y : Over U) :
    (Stacks.CechSite.powerSections Y (gammaAlg S (𝟭 (Over S)) U) ⋙
          Stacks.Descent.amitsurCoefficients.{u, u, u} (Γ(U.left, ⊤) : Type u)
            (coeffModule S F (𝟭 (Over S)) U)) ⋙
        forget₂ (ModuleCat.{u} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{u} ⟶
      Stacks.CechSite.powerSections Y (sliceAssociatedModuleCat F U) ⋙
        forget₂ (ModuleCat.{u} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{u} :=
  Functor.whiskerLeft (cechNerveTerminalFrom Y).rightOp (tensorToSections S F (𝟭 (Over S)) U)

/-- **The coefficient comparison along the Čech nerve is an isomorphism when the fibre powers
are affine.**  Every component is `Stacks.Sites.isIso_tensorToSectionsApp` at one simplex. -/
public def powerSectionsTensorToSectionsIso (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] (U : Over S) [IsAffine U.left] (Y : Over U)
    (hY : ∀ n : SimplexCategory,
      IsAffine ((cechNerveTerminalFrom Y).obj (Opposite.op n)).left.left) :
    (Stacks.CechSite.powerSections Y (gammaAlg S (𝟭 (Over S)) U) ⋙
          Stacks.Descent.amitsurCoefficients.{u, u, u} (Γ(U.left, ⊤) : Type u)
            (coeffModule S F (𝟭 (Over S)) U)) ⋙
        forget₂ (ModuleCat.{u} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{u} ≅
      Stacks.CechSite.powerSections Y (sliceAssociatedModuleCat F U) ⋙
        forget₂ (ModuleCat.{u} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{u} := by
  have hU : IsAffine ((𝟭 (Over S)).obj U).left := inferInstanceAs (IsAffine U.left)
  have h : ∀ n : SimplexCategory,
      IsIso ((powerSectionsTensorToSections S F U Y).app n) := fun n => by
    have hn : IsAffine ((𝟭 (Over S)).obj
        ((cechNerveTerminalFrom Y).obj (Opposite.op n)).left).left :=
      inferInstanceAs (IsAffine ((cechNerveTerminalFrom Y).obj (Opposite.op n)).left.left)
    exact isIso_tensorToSectionsApp S F (𝟭 (Over S)) U
      (Opposite.op ((cechNerveTerminalFrom Y).obj (Opposite.op n)))
  have : IsIso (powerSectionsTensorToSections S F U Y) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (powerSectionsTensorToSections S F U Y)

/-- **The coefficient hypothesis of [Stacks, Tag 03FJ], proved.**  For `U` an object of `Over S`
with affine total space and `Y` an object of the slice at `U` all of whose fibre powers have
affine total space, the cosimplicial `Γ(U.left, 𝒪)`-module of sections of `Fᵃ` on the fibre
powers of `Y` is the Amitsur coefficient cosimplicial module
`Γ(Y^{•}, 𝒪) ⊗_{Γ(U.left, 𝒪)} Fᵃ(U)`.

This is the hypothesis `hpow` of
`AlgebraicGeometry.isZero_cechCohomology_singleton_succ_overAffine`, at
`H = Stacks.Sites.sliceAssociatedModuleCat F U` and
`M = Stacks.Sites.coeffModule S F (𝟭 (Over S)) U`, and for an arbitrary `Y` rather than only for
`AlgebraicGeometry.overAffineAlgSpec U |>.obj (op a)`. -/
public def powerSectionsSliceAssociatedModuleIso (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] (U : Over S) [IsAffine U.left] (Y : Over U)
    (hY : ∀ n : SimplexCategory,
      IsAffine ((CategoryTheory.cechNerveTerminalFrom Y).obj (Opposite.op n)).left.left) :
    Stacks.CechSite.powerSections Y (Stacks.Sites.sliceAssociatedModuleCat F U) ≅
      Stacks.CechSite.powerSections Y ((overAffineAlgΓ U).leftOp) ⋙
        Stacks.Descent.amitsurCoefficients.{u, u, u} (Γ(U.left, ⊤) : Type u)
          (Stacks.Sites.coeffModule S F (𝟭 (Over S)) U) :=
  (Stacks.ModuleCatSites.natIsoOfForget₂ (powerSectionsTensorToSectionsIso S F U Y hY)
        (fun n r => tensorToSectionsApp_comp_smul S F U
          (Opposite.op ((cechNerveTerminalFrom Y).obj (Opposite.op n))) r)).symm ≪≫
    powerSectionsAmitsurCoefficientsIso U Y (coeffModule S F (𝟭 (Over S)) U)

end AlgebraicGeometry

end
