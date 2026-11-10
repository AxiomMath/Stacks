module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineFlatBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfTensorAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomology

/-!
# `LQCoh^fbc(𝒪_𝒳)` is closed under tensor products (Stacks 0771, part (6))

**Stacks 0771** part (6) says that for `F` and `G` in `LQCoh^fbc(𝒪_𝒳)` on an algebraic stack the
tensor product `F ⊗_{𝒪_𝒳} G`, computed in `Mod(𝒪_𝒳)`, lies again in `LQCoh^fbc(𝒪_𝒳)`.

The proof goes through the cartesian condition along flat arrows between objects lying over affine
schemes, which characterizes both halves of membership:

* every member of `LQCoh^fbc(𝒪_𝒳)` is cartesian along such arrows
  (`AlgebraicGeometry.Stack.isIso_restrictionBaseChange_of_flat`, step R2 of Stacks 0779);
* the tensor product of two modules cartesian along such arrows is again cartesian along them
  (`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_sheafTensor`): its sections over an
  affine object are the tensor product of the sections, by the affine description of the fppf
  sheafification of a presheaf cartesian along flat affine arrows;
* a module cartesian along such arrows is locally quasi-coherent, étale morphisms being flat
  (`AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange`), and
  has the flat base change property of Stacks 0762
  (`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange`).

The source deduces the flat base change half from Stacks 0764 (5) and the local quasi-coherence
half from Stacks 06WM (4); the route above replaces both by the cartesian characterization.

## Main results

* `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_sheafTensor`: **Stacks 0771, part (6).**

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology

/-- **Stacks 0771, part (6).** For `F` and `G` in `LQCoh^fbc(𝒪_𝒳)` on an algebraic stack, the
tensor product `F ⊗_{𝒪_𝒳} G` computed in `Mod(𝒪_𝒳)` is again in `LQCoh^fbc(𝒪_𝒳)`.

Both factors are cartesian along the flat arrows between objects over affine schemes (step R2 of
Stacks 0779), hence so is their tensor product, whose sections over an affine object are the tensor
product of the sections; a module cartesian along those arrows is locally quasi-coherent and has
the flat base change property. -/
@[stacks 0771 "part (6): LQCoh^fbc is closed under the tensor product of Mod(𝒪_𝒳)"]
theorem lqcohSheafFbcFppfModules_sheafTensor (F G : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F)
    (hG : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 G) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (FlatFppf.fppfRingedTopos B S hS 𝒳).O).obj
        F).obj G) := by
  have hT : ∀ {z x : 𝒳.val.val.obj} (φ : z ⟶ x),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (FlatFppf.fppfRingedTopos B S hS 𝒳).O).obj
          F).obj G).val φ.op) := fun φ hz hx hφ =>
    FibredSite.isIso_restrictionBaseChange_sheafTensor B S hS _ _ F G
      (fun ψ hz' hx' hψ => isIso_restrictionBaseChange_of_flat B E h S hS _ _ F.val hF ψ hψ hz' hx')
      (fun ψ hz' hx' hψ => isIso_restrictionBaseChange_of_flat B E h S hS _ _ G.val hG ψ hψ hz' hx')
      φ hz hx hφ
  have hL : IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (FlatFppf.fppfRingedTopos B S hS 𝒳).O).obj F).obj G).val :=
    (isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange B E h S hS _ _
      ((fppfToEtaleModules B S hS 𝒳).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (FlatFppf.fppfRingedTopos B S hS 𝒳).O).obj F).obj G))).2
      fun _ _ φ hy hy' hφ => hT φ hy hy' (by
        have : Etale ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)) := hφ
        infer_instance)
  exact ⟨hL, hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange B E h S hS _ _ _
    fun φ hz hx hφ => hT φ hz hx hφ⟩

end AlgebraicGeometry.Stack
