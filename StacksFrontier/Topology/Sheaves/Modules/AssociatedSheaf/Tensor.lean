module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.PicardGroup
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Free
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
import StacksCore.Tactic.StacksAttribute

/-!
# Construction (3) is monoidal, and carries an invertible module to an invertible sheaf

Let `(X, 𝒪_X)` be a ringed space and `α : R → Γ(X, 𝒪_X)` a ring homomorphism, and write `ℱ_M`
for construction (3) of Stacks 01BH, the sheafification of `U ↦ 𝒪_X(U) ⊗_R M`. This file proves
that `ℱ_•` takes the tensor product of `R`-modules to the tensor product of sheaves of modules
and `R` itself to `𝒪_X`, and deduces that `ℱ_N` is an invertible sheaf of modules whenever `N`
is an invertible `R`-module.

## Main results

* `Stacks.AssociatedSheaf.associatedSheafTensorIso`: **`ℱ_{M ⊗_R N} ≅ ℱ_M ⊗_{𝒪_X} ℱ_N`** on an
  arbitrary ringed space.
* `Stacks.AssociatedSheaf.associatedSheafUnitIso`: **`ℱ_R ≅ 𝒪_X`**.
* `Stacks.AssociatedSheaf.isInvertible_associatedSheaf`: **`ℱ_N` is an invertible sheaf of
  modules for `N` an invertible `R`-module**, and
  `Stacks.AssociatedSheaf.isInvertible_associatedSheaf_algebraicGeometry` the same conclusion
  spelled as `AlgebraicGeometry.SheafOfModules.IsInvertible`.

## Implementation notes

*Where this comes from, and the one step that is not a generalisation.* The presheaf-level
comparison is the base-change distributivity of Mathlib's
`TensorProduct.AlgebraTensorModule.distribBaseChange` read over each open, and the passage to
sheaves is `Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso`, which says that
sheafifying the sectionwise tensor product of two presheaves of modules is the tensor product of
their sheafifications. The same chain is carried out, for `X = Spec R` and privately, in
`StacksFrontier/AlgebraicGeometry/Schemes/ZariskiAndSeparation/AffineTensor.lean`.

One link of it does **not** survive the generalisation, and the generalisation is not a
statement-only edit as it appears to be. The naturality of the presheaf comparison is discharged
there by `with_unfolding_all rfl`, and over a general ringed space that is false: on a pure
tensor, `distribBaseChange` sends `a ⊗ (m ⊗ n)` to `(a ⊗ m) ⊗ (1 ⊗ n)`, so the square commutes
only because the restriction map carries `1` to `1`, which on `Spec R` is a definitional
equality of pointwise units and in general is the *proof* `map_one`. So the generator case of
`associatedPresheafTensorIso` is proved here by transporting along `map_one` instead, which is
the only mathematical content this file adds to the affine computation.

*Invertibility is not read off the rank.*
`Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one` would also give the conclusion,
but its hypothesis is false here: an invertible `R`-module is projective of rank one, not free, and
the opens of `X` have nothing to do with the opens of `Spec R`, so `ℱ_N` need not be locally free
of rank one on `X`. That gap is not an artefact —
`Stacks.RingedSpace.exists_isInvertible_not_isFiniteLocallyFreeOfRank_one` exhibits an invertible
sheaf of modules on a ringed space which is not locally free of rank one. So the proof goes through
the tensor characterisation of Tag 0B8K instead, which asks only for a sheaf of modules tensoring
with `ℱ_N` to `𝒪_X`, and `ℱ_{N^∨}` is one.

*Two spellings of the structure sheaf.* Construction (3) is indexed by `structureSheafRing X`, the
tensor-sheafification development by
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf h𝒪`. The two are equal by
`rfl`, and the equality is absorbed by writing the sheaf condition as the projection
`(structureSheafRing X).property`, so that no statement below needs a transparency option.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace

namespace Stacks.AssociatedSheaf

universe u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

variable (X : RingedSpace.{u, u})

variable {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- **Base change distributes over the tensor product, over a fixed open.**
`𝒪_X(U) ⊗_R (M ⊗_R N) ≅ (𝒪_X(U) ⊗_R M) ⊗_{𝒪_X(U)} (𝒪_X(U) ⊗_R N)`. -/
def associatedPresheafTensorIsoAt (U : Opens X) (M N : ModuleCat.{u} R) :
    (associatedPresheaf X α (M ⊗ N)).obj (op U) ≅
      (PresheafOfModules.tensorObj (O := X.presheaf) (associatedPresheaf X α M)
        (associatedPresheaf X α N)).obj (op U) :=
  letI : Algebra R (X.presheaf.obj (op U)) :=
    ((globalSectionsMap X α).app (op U)).hom.toAlgebra
  (TensorProduct.AlgebraTensorModule.distribBaseChange R (X.presheaf.obj (op U))
    ((constantModulePresheaf X M).obj (op U))
    ((constantModulePresheaf X N).obj (op U))).toModuleIso

/-- **The presheaf-level comparison of construction (3) with the tensor product.** -/
def associatedPresheafTensorIso (M N : ModuleCat.{u} R) :
    associatedPresheaf X α (M ⊗ N) ≅
      PresheafOfModules.tensorObj (O := X.presheaf) (associatedPresheaf X α M)
        (associatedPresheaf X α N) := by
  refine PresheafOfModules.isoMk (fun U ↦ associatedPresheafTensorIsoAt X α U.unop M N)
    (fun {U V} i ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg (fun t ↦ t + _) hx).trans
      ((congrArg (fun t ↦ _ + t) hy).trans (map_add _ x y).symm))
  | tmul a z =>
    let := ((globalSectionsMap X α).app U).hom.toAlgebra
    let : Module ↑((constantRingPresheaf X R).obj U) (TensorProduct R M N) :=
      inferInstanceAs (Module ↑((constantRingPresheaf X R).obj U)
        ↑((constantModulePresheaf X (M ⊗ N)).obj U))
    induction z using TensorProduct.induction_on with
    | zero =>
      exact ((congrArg _ (TensorProduct.tmul_zero _ a)).trans (map_zero _)).trans
        (((congrArg _ (TensorProduct.tmul_zero _ a)).trans (map_zero _)).symm)
    | add z w hz hw =>
      exact ((congrArg _ (TensorProduct.tmul_add a z w)).trans ((map_add _ _ _).trans
        ((congrArg (fun t ↦ t + _) hz).trans ((congrArg (fun t ↦ _ + t) hw).trans
          (map_add _ _ _).symm)))).trans (congrArg _ (TensorProduct.tmul_add a z w)).symm
    | tmul m n =>
      let : Algebra R (X.presheaf.obj V) := ((globalSectionsMap X α).app V).hom.toAlgebra
      have h : (X.presheaf.map i).hom (1 : X.presheaf.obj U) = 1 := map_one _
      with_unfolding_all exact congrArg (fun b : X.presheaf.obj V =>
        TensorProduct.tmul (X.presheaf.obj V)
          (TensorProduct.tmul R ((X.presheaf.map i).hom a) m)
          (TensorProduct.tmul R b n)) h.symm

/-- **Construction (3) carries the tensor product of `R`-modules to the tensor product of
sheaves of modules:** `ℱ_{M ⊗_R N} ≅ ℱ_M ⊗_{𝒪_X} ℱ_N`, on an arbitrary ringed space.

This is the clause of Tag 01I8 that the determinant argument of Tag 0FJN needs on the
trivialising open of Tag 08BL rather than on an affine scheme. -/
@[stacks 01I8 "construction (3) commutes with the tensor product, on an arbitrary ringed space"]
def associatedSheafTensorIso (M N : ModuleCat.{u} R) :
    associatedSheaf X α (M ⊗ N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) (structureSheafRing X).property⟩).obj
        (associatedSheaf X α M)).obj (associatedSheaf X α N) :=
  (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf
      (structureSheafRing X).property).mapIso (associatedPresheafTensorIso X α M N) ≪≫
    Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso X.presheaf
      (structureSheafRing X).property (associatedPresheaf X α M) (associatedPresheaf X α N)

/-- **Construction (3) carries the base ring to the structure sheaf:** `ℱ_R ≅ 𝒪_X`.

Both legs are already in the repository: `Stacks.AssociatedSheaf.freeIsoAssociatedSheaf`
identifies `ℱ` of a free module with the free sheaf of modules on the same index type, and
`Stacks.SheafOfModules.Site.freePUnitIso` identifies the free sheaf of modules on a one-element
index type with the structure sheaf. What is interposed is only the `R`-module isomorphism
`(PUnit →₀ R) ≃ₗ[R] R`. -/
@[stacks 01BH "construction (3) at the base ring is the structure sheaf"]
def associatedSheafUnitIso :
    associatedSheaf X α (ModuleCat.of R R) ≅
      SheafOfModules.unit (structureSheafRing X) :=
  ((associatedSheafFunctor.{u, u} X α).mapIso
        (Finsupp.uniqueLinearEquiv R R (PUnit.unit : PUnit.{u + 1})).toModuleIso).symm ≪≫
      (freeIsoAssociatedSheaf X α PUnit.{u + 1}).symm ≪≫
    Stacks.SheafOfModules.Site.freePUnitIso

variable (N : ModuleCat.{u} R)

/-- The tensor inverse of an invertible module, read as an isomorphism in `ModuleCat R`:
`N ⊗_R N^∨ ≅ R`. This is Mathlib's `Module.Invertible.linearEquiv`, whose pairing is stated with
the dual on the left. -/
def tensorDualIso [Module.Invertible R N] :
    N ⊗ ModuleCat.of R (Module.Dual R N) ≅ ModuleCat.of R R :=
  ((TensorProduct.comm R N (Module.Dual R N)).trans
    (Module.Invertible.linearEquiv R N)).toModuleIso

/-- **Construction (3) carries an invertible module to an invertible sheaf of modules.**

This is the step with which the source of Stacks 0FJN concludes: on an open where a flat sheaf
of modules of finite presentation is `ℱ_M` for a finite projective `M`, its determinant is
`ℱ_{det M}`, and `det M` is an invertible `𝒪_X(U)`-module.

The proof is Tag 0B8K (2) ⟹ (1): the tensor inverse is `ℱ_{N^∨}`, because
`ℱ_N ⊗_{𝒪_X} ℱ_{N^∨} ≅ ℱ_{N ⊗_R N^∨} ≅ ℱ_R ≅ 𝒪_X`. No hypothesis on the stalks of `X` is
needed, and none may be assumed: `ℱ_N` is in general *not* locally free of rank one, as the
implementation notes explain. -/
theorem isInvertible_associatedSheaf [Module.Invertible R N] :
    Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property
      (associatedSheaf X α N) :=
  (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
      (associatedSheaf X α N)).mpr
    ⟨associatedSheaf X α (ModuleCat.of R (Module.Dual R N)),
      ⟨(associatedSheafTensorIso X α N (ModuleCat.of R (Module.Dual R N))).symm ≪≫
        (associatedSheafFunctor.{u, u} X α).mapIso (tensorDualIso N) ≪≫
          associatedSheafUnitIso X α⟩⟩

/-- `Stacks.AssociatedSheaf.isInvertible_associatedSheaf` with the conclusion spelled as
`AlgebraicGeometry.SheafOfModules.IsInvertible`, at the sheaf condition the determinant
development of Stacks 0FJN carries. -/
theorem isInvertible_associatedSheaf_algebraicGeometry [Module.Invertible R N] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
        (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf) (associatedSheaf X α N) :=
  isInvertible_associatedSheaf X α N

end Stacks.AssociatedSheaf

end
