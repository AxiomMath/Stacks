module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafBocksteinChain
public import StacksFrontier.Algebra.Homology.QuasiIsoOfAcyclicKernel
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-isomorphism of Tag 0GT9, reduced to the acyclicity of one complex

Let `(X, O_X)` be a ringed space, `ι : I ⟶ O_X` an invertible ideal subsheaf, and `F` a cochain
complex of `I`-torsion-free `O_X`-modules. The comparison of Tag 0GT9 is the morphism of complexes

`Reduction.reductionComparisonChainMap : η_I F ⊗ O_X/I ⟶ H^•(F/I)`,

an epimorphism by `Reduction.epi_reductionComparisonChainMap`. It is a quasi-isomorphism if and
only if its kernel complex is acyclic, and both conditions may be checked on stalks.

## Main definitions

* `reductionComparisonKernel`: the kernel complex of the comparison of Tag 0GT9.

## Main results

* `shortExact_reductionComparisonKernelSequence`: the comparison sits in a short exact sequence
  of complexes `0 ⟶ ker ⟶ η_I F ⊗ O_X/I ⟶ H^•(F/I) ⟶ 0`, because it is an epimorphism.
* `quasiIso_reductionComparisonChainMap_of_acyclic_kernel`: **if the kernel complex is acyclic
  then the comparison of Tag 0GT9 is a quasi-isomorphism.**
* `acyclic_reductionComparisonKernel_of_quasiIso`: the converse.
* `quasiIso_reductionComparisonChainMap_iff_acyclic_kernel`: the two are therefore equivalent.
* `quasiIso_reductionComparisonChainMap_of_forall_stalk_quasiIso` and
  `acyclic_reductionComparisonKernel_of_forall_stalk_acyclic`: the quasi-isomorphism and the
  acyclicity of the kernel complex may be checked on stalks.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.IdealTorsion.Reduction

open Stacks.IdealTorsion.Eta

variable (X : RingedSpace.{u, u})

local notation "Oₓ" =>
  (Stacks.SheafOfModules.Tensor.ringSheaf
    (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ

/-- The kernel complex of the comparison `reductionComparisonChainMap` of Tag 0GT9. -/
public noncomputable def reductionComparisonKernel
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    CochainComplex (SheafOfModules.{u} Oₓ) ℤ :=
  kernel (reductionComparisonChainMap X I ι F hF)

/-- **The comparison of Tag 0GT9 sits in a short exact sequence of complexes**
`0 ⟶ ker ⟶ η_I F ⊗ O_X/I ⟶ H^•(F/I) ⟶ 0`, because it is an epimorphism. -/
public theorem shortExact_reductionComparisonKernelSequence
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    (ShortComplex.kernelSequence (reductionComparisonChainMap X I ι F hF)).ShortExact :=
  have := epi_reductionComparisonChainMap X I ι F hF
  Stacks.Homology.kernelSequence_shortExact _

/-- **If the kernel complex is acyclic then the comparison of Tag 0GT9 is a
quasi-isomorphism.** -/
public theorem quasiIso_reductionComparisonChainMap_of_acyclic_kernel
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (hker : (reductionComparisonKernel X I ι F hF).Acyclic) :
    QuasiIso (reductionComparisonChainMap X I ι F hF) :=
  have := epi_reductionComparisonChainMap X I ι F hF
  Stacks.Homology.quasiIso_of_epi_of_acyclic_kernel _ hker

/-- The converse: if the comparison of Tag 0GT9 is a quasi-isomorphism then its kernel complex
is acyclic. -/
public theorem acyclic_reductionComparisonKernel_of_quasiIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (hq : QuasiIso (reductionComparisonChainMap X I ι F hF)) :
    (reductionComparisonKernel X I ι F hF).Acyclic :=
  have := epi_reductionComparisonChainMap X I ι F hF
  have := hq
  (Stacks.Homology.quasiIso_iff_acyclic_kernel _).1 hq

/-- The comparison of Tag 0GT9 is a quasi-isomorphism if and only if its kernel complex is
acyclic. -/
public theorem quasiIso_reductionComparisonChainMap_iff_acyclic_kernel
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    QuasiIso (reductionComparisonChainMap X I ι F hF) ↔
      (reductionComparisonKernel X I ι F hF).Acyclic :=
  ⟨acyclic_reductionComparisonKernel_of_quasiIso X I ι F hF,
    quasiIso_reductionComparisonChainMap_of_acyclic_kernel X I ι F hF⟩

/-! ### Checking on stalks -/

/-- **The quasi-isomorphism of Tag 0GT9 may be checked on stalks**: the comparison is a
quasi-isomorphism if for every point `x` the morphism of complexes of `O_{X,x}`-modules obtained by
taking stalks degreewise is a quasi-isomorphism. -/
public theorem quasiIso_reductionComparisonChainMap_of_forall_stalk_quasiIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (h : ∀ x : X, QuasiIso
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (reductionComparisonChainMap X I ι F hF))) :
    QuasiIso (reductionComparisonChainMap X I ι F hF) :=
  AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso Oₓ _ h

/-- **The acyclicity of the kernel complex may be checked on stalks**: the kernel complex of the
comparison of Tag 0GT9 is acyclic if each of its stalk complexes is acyclic. -/
public theorem acyclic_reductionComparisonKernel_of_forall_stalk_acyclic
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (h : ∀ x : X,
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (reductionComparisonKernel X I ι F hF)).Acyclic) :
    (reductionComparisonKernel X I ι F hF).Acyclic :=
  (AlgebraicGeometry.SheafOfModules.acyclic_iff_forall_stalk_acyclic Oₓ _).2 h

end Stacks.IdealTorsion.Reduction

end
