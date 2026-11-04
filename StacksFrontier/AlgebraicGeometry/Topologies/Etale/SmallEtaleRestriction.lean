module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.RepresentableSheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image along an étale morphism is restriction

Let `f : T ⟶ S` be an étale morphism of schemes. On Mathlib's small étale sites there are two
readings of the inverse image `f⁻¹` of sheaves: the abstract inverse image
`(smallEtaleBaseChange f).sheafPullback`, the left adjoint of direct image along base change, and
restriction along composition with `f`, which is
`AlgebraicGeometry.Scheme.Etale.smallEtaleCompose f`. Composition with `f` is left adjoint to base
change along `f` (`AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeAdj`), so restriction
is also left adjoint to the direct image, and the two readings agree for every coefficient
category.

For sheaves of sets the restriction of a representable sheaf is again representable: the
restriction of the sheaf represented by `E` is the sheaf represented by the base change
`E ×_S T`, by the hom-set bijection of the same adjunction.

## Main results

* `AlgebraicGeometry.Scheme.Etale.sheafPullbackIsoRestrict`: the inverse image along an étale
  morphism is restriction, for an arbitrary coefficient category.
* `AlgebraicGeometry.Scheme.Etale.restrictUliftYonedaIso`: the restriction of the sheaf
  represented by `E` is the sheaf represented by the base change of `E`, naturally in `E`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w w' u

namespace AlgebraicGeometry.Scheme.Etale

open Stacks.EtaleCohomology

variable {T S : Scheme.{u}} (f : T ⟶ S) [Etale f]

/-- **Inverse image along an étale morphism is restriction.** For an étale `f : T ⟶ S` the
inverse image of sheaves along base change is isomorphic to restriction along composition with
`f`: both are left adjoint to the direct image along base change. -/
@[sga "4 VII 1.6" "more general"]
def sheafPullbackIsoRestrict (A : Type w) [Category.{w'} A]
    [((smallEtaleBaseChange f).sheafPushforwardContinuous A (smallEtaleTopology S)
      (smallEtaleTopology T)).IsRightAdjoint] :
    (smallEtaleBaseChange f).sheafPullback A (smallEtaleTopology S) (smallEtaleTopology T) ≅
      (smallEtaleCompose f).sheafPushforwardContinuous A (smallEtaleTopology T)
        (smallEtaleTopology S) :=
  ((smallEtaleBaseChange f).sheafAdjunctionContinuous A (smallEtaleTopology S)
      (smallEtaleTopology T)).leftAdjointUniq
    ((smallEtaleComposeBaseChangeAdj f).sheafPushforwardContinuous (smallEtaleTopology T)
      (smallEtaleTopology S))

/-- **The restriction of a representable sheaf is represented by the base change.** Restricting
the sheaf of sets represented by `E` along composition with an étale `f : T ⟶ S` gives the sheaf
represented by the base change of `E` along `f`, naturally in `E`: on sections over `V` both are
hom-sets matched by the adjunction between composition with `f` and base change. -/
def restrictUliftYonedaIso :
    (smallEtaleTopology S).uliftYoneda.{u + 1} ⋙
        (smallEtaleCompose f).sheafPushforwardContinuous (Type (u + 1)) (smallEtaleTopology T)
          (smallEtaleTopology S) ≅
      smallEtaleBaseChange f ⋙ (smallEtaleTopology T).uliftYoneda.{u + 1} :=
  NatIso.ofComponents
    (fun E ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents
        (fun V ↦ Equiv.toIso (Equiv.ulift.trans
          (((smallEtaleComposeBaseChangeAdj f).homEquiv V.unop E).trans Equiv.ulift.symm)))
        (fun {V V'} g ↦ by
          ext ⟨x⟩
          exact congrArg ULift.up
            ((smallEtaleComposeBaseChangeAdj f).homEquiv_naturality_left g.unop x))))
    (fun {E E'} g ↦ by
      ext V ⟨x⟩
      change ULift.up ((smallEtaleComposeBaseChangeAdj f).homEquiv V.unop E' (x ≫ g)) =
        ULift.up ((smallEtaleComposeBaseChangeAdj f).homEquiv V.unop E x ≫
          (smallEtaleBaseChange f).map g)
      exact congrArg ULift.up
        ((smallEtaleComposeBaseChangeAdj f).homEquiv_naturality_right x g))

/-- The isomorphism `restrictUliftYonedaIso` on sections: a morphism from the composite of `V`
with `f` to `E` goes to its adjoint morphism from `V` to the base change of `E`. -/
theorem restrictUliftYonedaIso_hom_app_hom_app (E : S.Etale) (V : T.Etaleᵒᵖ)
    (x : (smallEtaleCompose f).obj V.unop ⟶ E) :
    ((restrictUliftYonedaIso f).hom.app E).hom.app V (ULift.up x) =
      ULift.up ((smallEtaleComposeBaseChangeAdj f).homEquiv V.unop E x) :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end
