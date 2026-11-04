module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafBocksteinSquare

import StacksCore.Tactic.StacksAttribute

/-!
# The reduction comparison in the derived category

Let `(X, O_X)` be a ringed space, `ι : I ⟶ O_X` an invertible ideal subsheaf, and `F` a cochain
complex of `I`-torsion-free `O_X`-modules. This file constructs the canonical arrow

`η_I F ⊗ O_X/I ⟶ H^•(F/I)`

in `D(O_X)` of Tag 0GT9, and the canonical isomorphism, as data, given that the canonical
morphism of complexes `Reduction.reductionComparisonChainMap` is a quasi-isomorphism.

## Main definitions

* `reductionComparisonQ`: the canonical arrow in `D(O_X)`, the image under `DerivedCategory.Q`
  of the canonical morphism of complexes.
* `reductionComparisonQIso`: the canonical isomorphism in `D(O_X)`, given that the canonical
  morphism of complexes is a quasi-isomorphism.
* `reductionComparisonQIsoOfSquare`: the same isomorphism, given instead the degreewise stalk
  comparison square `Reduction.HasStalkBocksteinSquare`.

## Main results

* `isIso_reductionComparisonQ_iff_quasiIso` and `isIso_reductionComparisonQ_iff_acyclic_kernel`:
  the canonical arrow of `D(O_X)` is invertible exactly when the canonical morphism of complexes
  is a quasi-isomorphism, equivalently exactly when `Reduction.reductionComparisonKernel` is
  acyclic.
* `reductionComparisonQIso_hom` and `reductionComparisonQIsoOfSquare_hom`: the forward map of
  each isomorphism is the canonical arrow.

## Implementation notes

The derived category is taken at the standard localization model: this file puts
`attribute [local instance 10000] HasDerivedCategory.standard` in scope.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 0GT4](https://stacks.math.columbia.edu/tag/0GT4)
* [Stacks Project, Tag 0F7T](https://stacks.math.columbia.edu/tag/0F7T)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.IdealTorsion.Reduction

open Stacks.IdealTorsion.Eta

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ

/-! ### The arrow of the tag, in the derived category -/

/-- The canonical arrow `η_I F ⊗ O_X/I ⟶ H^•(F/I)` in `D(O_X)`, for a termwise `I`-torsion-free
complex `F`: the image under `DerivedCategory.Q` of the canonical morphism of complexes
`Reduction.reductionComparisonChainMap` from the reduction of the décalage to the chain-level
Bockstein complex. -/
@[stacks 0GT9 "the canonical arrow in D(O_X)"]
public noncomputable def reductionComparisonQ
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    DerivedCategory.Q.obj (etaModIdealComplex X I ι F hF) ⟶
      DerivedCategory.Q.obj (bocksteinChainComplex X I ι F hF) :=
  DerivedCategory.Q.map (reductionComparisonChainMap X I ι F hF)

/-- The canonical arrow `reductionComparisonQ` is the image under `DerivedCategory.Q` of the
canonical morphism of complexes `reductionComparisonChainMap`. -/
@[simp] public theorem reductionComparisonQ_eq
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    reductionComparisonQ X I ι F hF =
      DerivedCategory.Q.map (reductionComparisonChainMap X I ι F hF) := rfl

/-! ### The derived-level statement of the tag is the chain-level one -/

/-- The canonical arrow `reductionComparisonQ` is invertible in `D(O_X)` if and only if the
canonical morphism of complexes `reductionComparisonChainMap` is a quasi-isomorphism. -/
public theorem isIso_reductionComparisonQ_iff_quasiIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    IsIso (reductionComparisonQ X I ι F hF) ↔
      QuasiIso (reductionComparisonChainMap X I ι F hF) :=
  DerivedCategory.isIso_Q_map_iff_quasiIso _ (reductionComparisonChainMap X I ι F hF)

/-- The canonical arrow `reductionComparisonQ` is invertible in `D(O_X)` if and only if the
kernel `Reduction.reductionComparisonKernel` of the canonical epimorphism of complexes is
acyclic. -/
public theorem isIso_reductionComparisonQ_iff_acyclic_kernel
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    IsIso (reductionComparisonQ X I ι F hF) ↔
      (reductionComparisonKernel X I ι F hF).Acyclic :=
  (isIso_reductionComparisonQ_iff_quasiIso X I ι F hF).trans
    (quasiIso_reductionComparisonChainMap_iff_acyclic_kernel X I ι F hF)

/-! ### The isomorphism itself, as data -/

/-- The canonical isomorphism `η_I F ⊗ O_X/I ≅ H^•(F/I)` in `D(O_X)`, given that the canonical
morphism of complexes is a quasi-isomorphism: the canonical arrow `reductionComparisonQ`, which is
then invertible. -/
public noncomputable def reductionComparisonQIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (hq : QuasiIso (reductionComparisonChainMap X I ι F hF)) :
    DerivedCategory.Q.obj (etaModIdealComplex X I ι F hF) ≅
      DerivedCategory.Q.obj (bocksteinChainComplex X I ι F hF) :=
  haveI : IsIso (reductionComparisonQ X I ι F hF) :=
    (isIso_reductionComparisonQ_iff_quasiIso X I ι F hF).2 hq
  asIso (reductionComparisonQ X I ι F hF)

/-- The forward map of `reductionComparisonQIso` is the canonical arrow `reductionComparisonQ`. -/
@[simp] public theorem reductionComparisonQIso_hom
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (hq : QuasiIso (reductionComparisonChainMap X I ι F hF)) :
    (reductionComparisonQIso X I ι F hF hq).hom = reductionComparisonQ X I ι F hF := rfl

/-- The canonical isomorphism `η_I F ⊗ O_X/I ≅ H^•(F/I)` in `D(O_X)`, given the degreewise
stalk comparison square `Reduction.HasStalkBocksteinSquare`, which makes the canonical morphism of
complexes a quasi-isomorphism. -/
public noncomputable def reductionComparisonQIsoOfSquare
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (h : HasStalkBocksteinSquare X I ι F hF) :
    DerivedCategory.Q.obj (etaModIdealComplex X I ι F hF) ≅
      DerivedCategory.Q.obj (bocksteinChainComplex X I ι F hF) :=
  reductionComparisonQIso X I ι F hF
    (quasiIso_reductionComparisonChainMap_of_hasStalkBocksteinSquare X I ι F hF h)

/-- The forward map of `reductionComparisonQIsoOfSquare` is the canonical arrow
`reductionComparisonQ`. -/
@[simp] public theorem reductionComparisonQIsoOfSquare_hom
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (h : HasStalkBocksteinSquare X I ι F hF) :
    (reductionComparisonQIsoOfSquare X I ι F hF h).hom = reductionComparisonQ X I ι F hF := rfl

end Stacks.IdealTorsion.Reduction

end
