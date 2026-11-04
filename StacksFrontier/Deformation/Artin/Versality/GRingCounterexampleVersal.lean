module

public import StacksFrontier.Deformation.Artin.Predeformation.ThinVertical
public import StacksFrontier.Deformation.Artin.Versality.GRingCounterexample
public import StacksFrontier.Deformation.Smooth.Subsingleton

/-!
# Versality of the formal object of the Stacks 07XI counterexample

Let `Λ` be a Noetherian ring with maximal ideal `𝔪`, let `C` be a `Λ`-algebra of finite type
with a `Λ`-algebra map `ψ : C → R = Λ_𝔪^∧`, and let `𝒳 = 𝒮_F` and `ξ` be the category fibred
in sets and the formal object over `R` of
`StacksFrontier.Deformation.Artin.Versality.GRingCounterexample`.

This file proves the Example's assertion that `ξ` is **versal**.

## Main results

* `Deformation.Artin.GRingCounterexample.isVersal_formalObject`: `ξ` is versal.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 0CXJ](https://stacks.math.columbia.edu/tag/0CXJ)
* [Stacks Project, Tag 06HR](https://stacks.math.columbia.edu/tag/06HR)
-/

@[expose] public noncomputable section

namespace Deformation.Artin.GRingCounterexample

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

variable {Λ : Type u} [CommRing Λ] (m : Ideal Λ) [hm : m.IsMaximal]
variable (C : Type u) [CommRing C] (φ : Λ →+* C)
variable (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))

/-- **Any two objects of `𝒳 = 𝒮_F` over the same object of the site are joined by a morphism
over the identity**: a morphism whose image in the site is the identification of the two
objects. -/
public theorem exists_verticalHom {z w : (stack m C φ B hS).val.obj}
    (e : (stack m C φ B hS).val.p.obj z = (stack m C φ B hS).val.p.obj w) :
    ∃ s : z ⟶ w, (stack m C φ B hS).val.p.map s = eqToHom e :=
  ⟨verticalHom m C φ B hS e, verticalHom_base m C φ B hS e⟩

/-- **`𝒳 = 𝒮_F` is thin over the big fppf site:** a morphism is determined by its image in
schemes over `S`. -/
public theorem stack_map_injective {z w : (stack m C φ B hS).val.obj} (s t : z ⟶ w)
    (h : (stack m C φ B hS).val.p.map s = (stack m C φ B hS).val.p.map t) : s = t :=
  stack_hom_ext m C φ B hS s t h

section Versal

variable [IsNoetherianRing Λ] (ψ : C →+* completion m)
  (hψ : ψ.comp φ = algebraMap Λ (completion m))
  (hR : B.Contains (Spec (.of (completion m))))

/-- **The formal object `ξ` over `R = Λ_𝔪^∧` is versal**, the last of the Example's three
assertions about `𝒳 = 𝒮_F`. Versality is relative to `Λ_𝔪`, through which the structure morphism
of `R` factors by `Deformation.Artin.GRingCounterexample.base_toS_eq`. -/
@[stacks 07XI "the Example's assertion that the formal object `ξ` over `R = Λ_𝔪^∧` is \
versal, relative to `Λ_𝔪`, through which the structure morphism of `R` factors. The \
construction of `F`, `𝒳 = 𝒮_F` and `ξ` is in \
`StacksFrontier.Deformation.Artin.Versality.GRingCounterexample`, limit preservation on objects \
is `Deformation.Artin.GRingCounterexample.isLimitPreservingOnObjects_stack`, and \
effectivity is `Deformation.Artin.GRingCounterexample.isEffective_formalObject`. Versality \
relative to the local ring of `S` at `𝔪`, which is the form Stacks 07XH consumes, is \
`Deformation.Artin.GRingCounterexample.isVersal_formalObject_stalk`, and the Example whole \
is `Deformation.Artin.GRingCounterexample.exists_algHom_henselian`. NOT \
covered, and formalized nowhere: the Example's closing step from solvability in the \
henselization to `Λ_𝔪^h` and `Λ_𝔪` being G-rings, which the Stacks Project itself defers \
(\"insert future reference here\"), so there is no statement to formalize against."]
public theorem isVersal_formalObject :
    Deformation.Artin.FormalObject.IsVersal B (Spec (.of Λ)) hS (stack m C φ B hS).val.p
      ((stack m C φ B hS).isFiberedInGroupoids) (formalObject m C φ B hS ψ hψ hR)
      (Localization.AtPrime m) (localChart m) (base_toS_eq m C φ B hS ψ hψ hR) := by
  intro P
  exact Deformation.isSmooth_of_subsingleton_restrictedCoyoneda
    (nonempty_subsingleton_hom_predefBase m C φ B hS ψ hψ hR)
    (Deformation.Artin.exists_vertical_predeformationHom
      (fun s t h => stack_map_injective m C φ B hS s t h)
      (fun e => exists_verticalHom m C φ B hS e))
    (fun s t h => Deformation.Artin.predeformationCategory_hom_ext
      (fun s' t' h' => stack_map_injective m C φ B hS s' t' h') s t h) _

end Versal

end Deformation.Artin.GRingCounterexample

end
