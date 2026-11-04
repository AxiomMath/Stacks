module

public import StacksFrontier.AlgebraicGeometry.Spaces.CommonLemmas

/-!
# Quasi-coherent modules on an algebraic space form a weak Serre class, as instances

The statements of `StacksFrontier/AlgebraicGeometry/Spaces/CommonLemmas.lean` (Stacks 03M1: the
quasi-coherent `𝒪_F`-modules on the small étale site of an algebraic space `F` are closed under
extensions and form a weak Serre class, at the universe of the schemes) registered as an instance
for an algebraic space given as a presheaf `F` together with a proof `hF` that it is one.

## Main results

* `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass_of_isAlgebraicSpace`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 03M1, as a weak Serre class**, as an instance: quasi-coherence of `𝒪_F`-modules on
the small étale site of an algebraic space contains `0` and is closed under isomorphisms,
kernels, cokernels and extensions. -/
instance quasicoherentSheaves_isWeakSerreClass_of_isAlgebraicSpace :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsWeakSerreClass :=
  isWeakSerreClass_quasicoherentSheaves B S hS ⟨F, hF⟩

end AlgebraicGeometry.Space

end
