module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# The chain of Tag 03EL along a composite of morphisms of ringed topoi

Let `φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi in the four-field sense of
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, and let `χ : (Sh(C), O_C) ⟶ (Sh(E), O_E)`
play the role of their composite, joined to it by a comparison `τ` of the geometric direct
images as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso`. The comparison of
Tag 03EL for `χ`,

`χ^*(F ⊗_{O_E} G) ≅ χ^*F ⊗_{O_C} χ^*G`,

ought to be the comparison for `ψ` pulled back along `φ`, followed by the comparison for `φ`
and the composition comparison
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` in each tensor factor. That
statement is what a consumer needs in order to move the comparison of Tag 03EL — and with it
the canonical map of Tag 0GMX — across a square of morphisms of ringed topoi, since each leg
of such a square is a composite.

The comparison of Tag 03EL is defined by the chain of six bijections
`Stacks.SheafOfModules.pullbackTensorStep1` … `Stacks.SheafOfModules.pullbackTensorStep6`, and
the identity above is the identity of the two chains. This file proves it for the first two
steps.

## Main results

* `Stacks.SheafOfModules.pullbackTensorStep1_comp`: **step 1 of the chain of Tag 03EL is
  compatible with composition.** Transposing a morphism out of `χ^*(F ⊗ G)` precomposed with
  the comparison of pullbacks is transposing it under the two adjunctions in turn, followed by
  the comparison of direct images. This is the mate correspondence of Stacks 03D8: the
  comparison of pullbacks is pinned down as the conjugate of the comparison of direct images,
  and `Stacks.CategoryTheory.homEquiv_conjugate` reads a conjugate on transposes.
* `Stacks.SheafOfModules.pullbackTensorStep2_comp`: **step 2 of the chain of Tag 03EL is
  compatible with composition.** Both readings of step 2 are the universal property of the
  tensor product sheaf over the *same* sheaf of rings `O_E` — only the sheaf of values differs,
  by the comparison of direct images — so this is the naturality of that universal property in
  the sheaf of values.

## What this file does not contain

The composition law for `Stacks.SheafOfModules.pullbackTensorIso` itself. Steps 1 and 2 take
place over the fixed site `E` and the fixed sheaf of rings `O_E`, which is what makes their
composition law well-posed step by step. The remaining four steps are not of that character:
step 3 transports bilinear pairings along the inverse image, step 4 is the universal property of
the tensor product sheaf over `χ⁻¹O_E`, and steps 5 and 6 are extension of scalars along the
structure map of `χ` and base change of a tensor product along it — and a composite route meets
none of those four, since its chains are over `ψ⁻¹O_E` on `D` and over `φ⁻¹O_D` on `C`. So there
is no statement "step 3 is compatible with composition" to prove, and the composition law cannot
be assembled one step at a time past step 2.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear` takes it from
here by *regrouping* the chain: those four steps compose to a single bijection on bilinear
pairings, with which the two routes do correspond, and the composition law becomes one equation
— `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_iff`. That one equation is still open, so
the composition law for the comparison of Tag 03EL is not yet available, and neither is the
composition law for the canonical map of Tag 0GMX that is read off it in
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomFlat`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

section ChainComp

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
  (χ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
  (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ : fSharpSetComp φ ψ ≫
    τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  (F G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **Step 1 of the chain of Tag 03EL is compatible with composition.** Let
`ρ : φ^*ψ^*(F ⊗_{O_E} G) ⟶ N`. Precomposing it with the comparison `χ^* ≅ ψ^* ⋙ φ^*` of
pullbacks and transposing under the adjunction of Stacks 03D7 for `χ` is the same as
transposing it under the adjunction for `φ` and then the one for `ψ`, and postcomposing with
the comparison `φ_* ⋙ ψ_* ≅ χ_*` of direct images.

This is the mate correspondence of Stacks 03D8. The comparison of pullbacks is defined by
uniqueness of left adjoints, so it has no formula; what pins it down is that its conjugate is
the comparison of direct images, which is
`Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom`, and
`Stacks.CategoryTheory.homEquiv_conjugate` is that statement read on transposes. -/
theorem pullbackTensorStep1_comp
    (ρ : (ψ.pullbackModules ⋙ φ.pullbackModules).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ⟶ N) :
    pullbackTensorStep1 χ F G N
        ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ≫ ρ) =
      ((pullbackAdjPushforwardModules ψ).comp
            (pullbackAdjPushforwardModules φ)).homEquiv _ N ρ ≫
        (pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N := by
  have hc := Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (pullbackAdjPushforwardModules χ) (pushforwardModulesCompIso φ ψ χ τ hτ).symm
    ((pullbackAdjPushforwardModules ψ).comp (pullbackAdjPushforwardModules φ))
  have h := Stacks.CategoryTheory.homEquiv_conjugate
    ((pullbackAdjPushforwardModules ψ).comp (pullbackAdjPushforwardModules φ))
    (pullbackAdjPushforwardModules χ) (pushforwardModulesCompIso φ ψ χ τ hτ).hom ρ
  rw [show ((conjugateEquiv ((pullbackAdjPushforwardModules ψ).comp
        (pullbackAdjPushforwardModules φ)) (pullbackAdjPushforwardModules χ)).symm
          (pushforwardModulesCompIso φ ψ χ τ hτ).hom) =
      (pullbackModulesCompIso φ ψ χ τ hτ).hom from
    (Equiv.symm_apply_eq _).2 hc.symm] at h
  exact h

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **Step 2 of the chain of Tag 03EL is compatible with composition.** Step 2 is the universal
property of the tensor product sheaf over the structure sheaf of the *target*, which the
composite and its two factors share; the two readings therefore differ only in the sheaf of
values, by the comparison `φ_* ⋙ ψ_* ≅ χ_*` of direct images. So this is the naturality of
that universal property in the sheaf of values, which is
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom_symm_naturality`. -/
theorem pullbackTensorStep2_comp
    (t : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G) ⟶
      (pushforwardModules ψ).obj ((pushforwardModules φ).obj N)) :
    pullbackTensorStep2 χ F G N (t ≫ (pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N) =
      ⟨(pullbackTensorStep2 ψ F G ((pushforwardModules φ).obj N) t).1 ≫
          (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
            ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N),
        (pullbackTensorStep2 ψ F G ((pushforwardModules φ).obj N) t).2.comp
          ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N)⟩ :=
  bilinearEquivTensorSheafHom_symm_naturality
    (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).property) t
    ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N)

end ChainComp

end Stacks.SheafOfModules

end
