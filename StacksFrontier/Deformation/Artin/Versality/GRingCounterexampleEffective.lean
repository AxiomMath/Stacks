module

public import StacksFrontier.Deformation.Artin.FormalObject.EffectiveOfBase
public import StacksFrontier.Deformation.Artin.Versality.GRingCounterexample

/-!
# Effectivity of the formal object of the Stacks 07XI counterexample

Let `Λ` be a Noetherian ring with maximal ideal `𝔪`, let `C` be a `Λ`-algebra of finite type
with a `Λ`-algebra map `ψ : C → R = Λ_𝔪^∧`, and let `𝒳 = 𝒮_F` and `ξ` be the category fibred
in sets and the formal object over `R` of
`StacksFrontier.Deformation.Artin.Versality.GRingCounterexample`.

This file proves the Example's assertion that `ξ` is **effective**, i.e. that it lies in the
essential image of the approximation functor of **Stacks 07X6**.

## Main definitions

* `Deformation.Artin.GRingCounterexample.homOfBase`: the morphism of `𝒮_F` over a prescribed
  morphism of the site.
* `Deformation.Artin.GRingCounterexample.completionObject`: `Spec R` as an object of `𝒮_F`.
* `Deformation.Artin.GRingCounterexample.completionCompleteLocalObject`: it as an object of
  `Deformation.Artin.CompleteLocalObjects`.

## Main results

* `Deformation.Artin.GRingCounterexample.isEffective_formalObject`: `ξ` is effective.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
-/

@[expose] public noncomputable section

namespace Deformation.Artin.GRingCounterexample

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

variable {Λ : Type u} [CommRing Λ] (m : Ideal Λ) [hm : m.IsMaximal]
variable (C : Type u) [CommRing C] (φ : Λ →+* C)
variable (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))

/-- **The morphism of `𝒳 = 𝒮_F` over a prescribed morphism of the site.** The fibres of
`𝒮_F` are discrete and `F` takes only subsingleton values, so the base component is the only
datum a morphism needs; `Deformation.Artin.GRingCounterexample.verticalHom` is the case of an
identification of the two objects of the site. -/
public def homOfBase {z w : (stack m C φ B hS).val.obj}
    (t : (stack m C φ B hS).val.p.obj z ⟶ (stack m C φ B hS).val.p.obj w) : z ⟶ w where
  base := t
  fiber := Discrete.eqToHom (Subsingleton.elim _ _)

/-- The base component of `Deformation.Artin.GRingCounterexample.homOfBase` is the given
morphism of the site. -/
public theorem homOfBase_base {z w : (stack m C φ B hS).val.obj}
    (t : (stack m C φ B hS).val.p.obj z ⟶ (stack m C φ B hS).val.p.obj w) :
    (homOfBase m C φ B hS t).base = t :=
  rfl

section Effective

variable [IsNoetherianRing Λ] (ψ : C →+* completion m)
  (hψ : ψ.comp φ = algebraMap Λ (completion m))
  (hR : B.Contains (Spec (.of (completion m))))

include ψ hψ

/-- **`Spec R` lies in `F`:** its structure morphism to `S` factors through `Spec(C)`, hence
through `g : S' ⟶ S`, by the Example's factorization `Λ → C → R`. -/
public theorem factors_baseOver :
    Factors m C φ B hS (Deformation.Artin.baseOver B (Spec (.of Λ)) hS
      (completionBase m) hR) := by
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ auxInr m C, ?_⟩
  show (Spec.map (CommRingCat.ofHom ψ) ≫ auxInr m C) ≫ auxMap m C φ =
    Spec.map (CommRingCat.ofHom (algebraMap Λ (completion m)))
  rw [Category.assoc, auxInr_auxMap, ← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext ?_)
  show ψ.comp φ = algebraMap Λ (completion m)
  exact hψ

/-- **`Spec R` as an object of `𝒳 = 𝒮_F`.** -/
public def completionObject : (stack m C φ B hS).val.obj :=
  ⟨Deformation.Artin.baseOver B (Spec (.of Λ)) hS (completionBase m) hR,
    Discrete.mk (ULift.up (PLift.up (factors_baseOver m C φ B hS ψ hψ hR)))⟩

/-- `Spec R` lies over the object of the site it was built from. -/
public theorem completionObject_base :
    (stack m C φ B hS).val.p.obj (completionObject m C φ B hS ψ hψ hR) =
      Deformation.Artin.baseOver B (Spec (.of Λ)) hS (completionBase m) hR :=
  rfl

/-- **`Spec R` as an object of `Deformation.Artin.CompleteLocalObjects`**, the source category
of the approximation functor of **Stacks 07X6**. -/
public def completionCompleteLocalObject :
    Deformation.Artin.CompleteLocalObjects B (Spec (.of Λ)) hS (stack m C φ B hS).val.p :=
  ⟨⟨completionObject m C φ B hS ψ hψ hR, completionBase m, hR,
    completionObject_base m C φ B hS ψ hψ hR⟩⟩

/-- **The formal object `ξ` over `R = Λ_𝔪^∧` is effective**, the first of the Example's two
assertions about `ξ`. -/
@[stacks 07XI "the Example's assertion that the formal object `ξ` over `R = Λ_𝔪^∧` is \
effective. The construction of `F`, `𝒳 = 𝒮_F` and `ξ` is in \
`StacksFrontier.Deformation.Artin.Versality.GRingCounterexample`, limit preservation on objects \
is `Deformation.Artin.GRingCounterexample.isLimitPreservingOnObjects_stack`, and versality \
is `Deformation.Artin.GRingCounterexample.isVersal_formalObject`. The Example whole -- these \
three assertions together with the Example's conditional conclusion, which assumes the \
conclusion of Stacks 07XH for these `𝒳` rather than any G-ring property -- is \
`Deformation.Artin.GRingCounterexample.exists_algHom_henselian`. NOT covered, and \
formalized nowhere: the Example's closing step from solvability in the henselization to \
`Λ_𝔪^h` and `Λ_𝔪` being G-rings, which the Stacks Project itself defers (\"insert future \
reference here\"), so there is no statement to formalize against."]
public theorem isEffective_formalObject :
    Deformation.Artin.FormalObject.IsEffective B (Spec (.of Λ)) hS (stack m C φ B hS).val.p
      ((stack m C φ B hS).isFiberedInGroupoids) (formalObject m C φ B hS ψ hψ hR) :=
  Deformation.Artin.isEffective_of_object_over_base B (Spec (.of Λ)) hS
    (stack m C φ B hS).val.p ((stack m C φ B hS).isFiberedInGroupoids)
    (fun t => ⟨homOfBase m C φ B hS t, homOfBase_base m C φ B hS t⟩)
    (fun s t h => stack_hom_ext m C φ B hS s t h)
    (formalObject m C φ B hS ψ hψ hR) hR
    (completionCompleteLocalObject m C φ B hS ψ hψ hR)
    (completionObject_base m C φ B hS ψ hψ hR)

end Effective

end Deformation.Artin.GRingCounterexample

end
