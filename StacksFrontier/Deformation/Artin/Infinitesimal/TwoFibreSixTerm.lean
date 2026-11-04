module

public import StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreInfExact
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger

/-!
# The six-term exact sequence of a 2-fibre product, from (RS*)

This file states and proves **Stacks 0DNN** with exactly the source's hypotheses: `𝒳`, `𝒴`,
`𝒵` satisfy (RS\*), and nothing else is assumed. The `A`-linear functors `Inf_?` and `T_?`
appearing in the sequence are not inputs: for `x`, `z`, `y` they are the functors that
Stacks 07Y9 constructs from (RS\*) (`Deformation.Artin.infinitesimalAutomorphismFunctor`,
`Deformation.Artin.tangentFunctor`), and for `w` they are constructed in the same way from
(RS\*) for `𝒲 = 𝒳 ×_𝒴 𝒵`, which is Stacks 0CXQ
(`Deformation.Artin.twoFibreProductOver_satisfiesRSStar`), exactly as in the source's proof.

The exactness itself is `Deformation.Artin.twoFibre_sixTermExact`, which holds for *every*
choice of such linear structures.

## References

* [Stacks Project, Tag 0DNN](https://stacks.math.columbia.edu/tag/0DNN)
* [Stacks Project, Tag 0CXQ](https://stacks.math.columbia.edu/tag/0CXQ)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

section TwoFibreSixTerm
open Functor CategoryTheory.TwoFibreProductOver
universe u v₁ w₁ v₂ w₂ v₃ w₃

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒵 : Type v₂} [Category.{w₂} 𝒵]
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  {p𝒳 : 𝒳 ⥤ BigFppfOver B S hS} {p𝒵 : 𝒵 ⥤ BigFppfOver B S hS}
  {p𝒴 : 𝒴 ⥤ BigFppfOver B S hS} {P : 𝒳 ⥤ 𝒴} {Q : 𝒵 ⥤ 𝒴}
  (hP : P ⋙ p𝒴 = p𝒳) (hQ : Q ⋙ p𝒴 = p𝒵)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒵 : p𝒵.IsFiberedInGroupoids)
  (h𝒴 : p𝒴.IsFiberedInGroupoids)
  (w : TwoFibreProductOver p𝒳 p𝒵 p𝒴 P Q)
  (hw : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).obj w = algebraOver A B S hS toS hA)

/-- **Stacks 0DNN.** Let `P : 𝒳 ⟶ 𝒴` and `Q : 𝒵 ⟶ 𝒴` be `1`-morphisms of categories fibred in
groupoids over the big fppf site of `S`, and assume `𝒳`, `𝒴`, `𝒵` satisfy (RS\*). Let `w` be an
object of `𝒲 = 𝒳 ×_𝒴 𝒵` over `Spec A`, with components `x`, `z` and `y = P x`. For every
`A`-module `M` the six-term sequence

`0 ⟶ Inf_w(M) ⟶ Inf_x(M) ⊕ Inf_z(M) ⟶ Inf_y(M) --δ--> T_w(M) ⟶ T_x(M) ⊕ T_z(M) ⟶ T_y(M)`

of `A`-modules is exact. Here `Inf_?` and `T_?` are the `A`-linear functors that (RS\*)
produces (Stacks 07Y9), for `w` through (RS\*) for `𝒲` (Stacks 0CXQ); the horizontal maps
are those of Remark 07YA and `δ` is `Deformation.Artin.boundaryLinearMap`. Exactness is
stated as injectivity of the first map together with four `Function.Exact`s. -/
@[stacks 0DNN]
public theorem twoFibre_sixTermExact_of_satisfiesRSStar
    (hRS𝒳 : SatisfiesRSStar B S hS p𝒳 h𝒳) (hRS𝒵 : SatisfiesRSStar B S hS p𝒵 h𝒵)
    (hRS𝒴 : SatisfiesRSStar B S hS p𝒴 h𝒴) (M : SiteModule A B) :
    Function.Injective (LinearMap.prod (infLinearMapOfOneMorphism A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q)
      TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳
      h𝒵 h𝒴 hP hQ) h𝒳 (infinitesimalAutomorphismFunctor A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
      (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵))
      (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w
      hw) h𝒳 hRS𝒳) M) (infLinearMapOfOneMorphism A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q)
      TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳
      h𝒵 h𝒴 hP hQ) h𝒵 (infinitesimalAutomorphismFunctor A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
      (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵))
      (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w
      hw) h𝒵 hRS𝒵) M)) ∧ Function.Exact (LinearMap.prod (infLinearMapOfOneMorphism A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q)
      TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳
      h𝒵 h𝒴 hP hQ) h𝒳 (infinitesimalAutomorphismFunctor A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
      (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵))
      (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w
      hw) h𝒳 hRS𝒳) M) (infLinearMapOfOneMorphism A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q)
      TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳
      h𝒵 h𝒴 hP hQ) h𝒵 (infinitesimalAutomorphismFunctor A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
      (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵))
      (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w
      hw) h𝒵 hRS𝒵) M)) (LinearMap.coprod (infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 (infinitesimalAutomorphismFunctor A B S hS toS hA
      p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw) h𝒳 hRS𝒳) (infinitesimalAutomorphismFunctor A B S
      hS toS hA p𝒴 (P.obj w.x) (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 hRS𝒴) M)
      (-(twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw (infinitesimalAutomorphismFunctor A B S
      hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw) h𝒵 hRS𝒵)
      (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒴 (P.obj w.x) (twoFibreFstImageOver A B S
      hS toS hA hP w hw) h𝒴 hRS𝒴) M))) ∧ Function.Exact (LinearMap.coprod (infLinearMapOfOneMorphism
      A B S hS toS hA p𝒳 p𝒴 P hP w.x (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴
      (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w
      hw) h𝒳 hRS𝒳) (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 hRS𝒴) M) (-(twoFibreInfSideMap A B S hS toS
      hA hP hQ h𝒵 h𝒴 w hw (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒵 w.y (twoFibreSndOver
      A B S hS toS hA w hw) h𝒵 hRS𝒵) (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒴 (P.obj
      w.x) (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 hRS𝒴) M))) (boundaryLinearMap A B S hS
      toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 hRS𝒴) (tangentFunctor A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
      (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵)) M) ∧
      Function.Exact (boundaryLinearMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw
      (infinitesimalAutomorphismFunctor A B S hS toS hA p𝒴 (P.obj w.x) (twoFibreFstImageOver A B S
      hS toS hA hP w hw) h𝒴 hRS𝒴) (tangentFunctor A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
      (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵)) M)
      (LinearMap.prod (tangentLinearMapOfOneMorphism A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q)
      TwoFibreProductOver.fst_comp_eq w hw (tangentFunctor A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
      (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵))
      (tangentFunctor A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw) h𝒳 hRS𝒳) h𝒳 M)
      (tangentLinearMapOfOneMorphism A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴
      P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw
      (tangentFunctor A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
      (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵))
      (tangentFunctor A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw) h𝒵 hRS𝒵) h𝒵 M))
      ∧ Function.Exact (LinearMap.prod (tangentLinearMapOfOneMorphism A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q)
      TwoFibreProductOver.fst_comp_eq w hw (tangentFunctor A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
      (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵))
      (tangentFunctor A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw) h𝒳 hRS𝒳) h𝒳 M)
      (tangentLinearMapOfOneMorphism A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴
      P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw
      (tangentFunctor A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
      (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵))
      (tangentFunctor A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw) h𝒵 hRS𝒵) h𝒵 M))
      (LinearMap.coprod (tangentLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) (tangentFunctor A B S hS toS hA p𝒳 w.x (twoFibreFstOver
      A B S hS toS hA w hw) h𝒳 hRS𝒳) (tangentFunctor A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 hRS𝒴) h𝒴 M) (-(twoFibreTangentSideMap A B S
      hS toS hA hP hQ h𝒴 w hw (tangentFunctor A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS
      hA w hw) h𝒵 hRS𝒵) (tangentFunctor A B S hS toS hA p𝒴 (P.obj w.x) (twoFibreFstImageOver A B S
      hS toS hA hP w hw) h𝒴 hRS𝒴) M))) :=
  twoFibre_sixTermExact A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw
    (InfW := infinitesimalAutomorphismFunctor A B S hS toS hA (TwoFibreProductOver.structureFunctor
        p𝒳 p𝒵 p𝒴 P Q) w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
        (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵))
    (InfX := infinitesimalAutomorphismFunctor A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS
        hA w hw) h𝒳 hRS𝒳)
    (InfZ := infinitesimalAutomorphismFunctor A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS
        hA w hw) h𝒵 hRS𝒵)
    (InfY := infinitesimalAutomorphismFunctor A B S hS toS hA p𝒴 (P.obj w.x) (twoFibreFstImageOver A
        B S hS toS hA hP w hw) h𝒴 hRS𝒴)
    (hRS𝒴 := hRS𝒴)
    (TW := tangentFunctor A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ)
        (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 P Q h𝒳 h𝒴 h𝒵 hP hQ hRS𝒳 hRS𝒴 hRS𝒵))
    (TX := tangentFunctor A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw) h𝒳 hRS𝒳)
    (TZ := tangentFunctor A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw) h𝒵 hRS𝒵)
    (TY := tangentFunctor A B S hS toS hA p𝒴 (P.obj w.x) (twoFibreFstImageOver A B S hS toS hA hP w
        hw) h𝒴 hRS𝒴)
    (M := M)

end TwoFibreSixTerm

end Deformation.Artin

end
