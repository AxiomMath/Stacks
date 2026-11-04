module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TrivializationTorsor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorOfPairs

/-!
# The class of the torsor of trivializations is additive in the pair

Let `C` be a site and `F : C ⥤ Scheme` a functor whose global functions form a sheaf of
commutative rings and whose units form a sheaf of abelian groups, so that the sheaf `μ_n` of
`n`-th roots of unity is defined. For two pairs `(L, α)` and `(M, β)` on the resulting ringed
site, tensoring trivializations is a morphism of sheaves of sets from the product of the two
torsors of trivializations to the torsor of trivializations of the tensor product pair, and it
adds the acting roots of unity: a root of unity acts by scaling, and the tensor product of two
scaled sections is scaled by the product of the two scalars. By the addition formula for torsor
classes this says that the first cohomology class of the torsor of trivializations of the tensor
product pair is the sum of the two classes.

This is part (3) of the proof of Tag 040Q — that the cohomology class of a tensor product of
pairs is the sum of the two classes — for the second construction of the tag.

## Main results

* `AlgebraicGeometry.rootAct_normalizedTensorPairing`: the pairing adds the acting roots of
  unity.
* `AlgebraicGeometry.trivializationTorsor_class_add`: **the class of the torsor of
  trivializations of a tensor product of pairs is the sum of the two classes.**

## Implementation notes

The addition formula is
`Stacks.Cohomology.Torsors.Generators.torsorClass_add_of_equivariant'`, which asks for an
equivariant morphism out of the product *presheaf* of the two underlying presheaves. The
underlying presheaf of `AlgebraicGeometry.trivializationTorsor` is the sheaf of normalized local
generators by `AlgebraicGeometry.trivializationTorsor_presheaf`, which is an equality of terms,
so `Stacks.Cohomology.Torsors.Generators.normalizedTensorPairing` already has the required type
and no transport appears.

Equivariance is checked on underlying sections: `AlgebraicGeometry.rootAct_val` turns the action
into multiplication by `AlgebraicGeometry.rootUnit`,
`Stacks.Cohomology.Torsors.Generators.tensorSection_smul_unit` multiplies the two scalars, and
`AlgebraicGeometry.rootUnit_add` identifies the product with the unit of the sum.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 040P](https://stacks.math.columbia.edu/tag/040P)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Torsors (AbelianTorsor torsorSetoid torsorIsoClassesEquivH1)
open Stacks.Cohomology.Torsors.Generators
open Stacks.SheafOfModules (IsInvertible)

universe t v u

namespace AlgebraicGeometry

section

variable {C : Type v} [Category.{u} C] (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (hO : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)
    [(schemeFunctionsRingedSite J F hO).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (schemeFunctionsRingedSite J F hO).J AddCommGrpCat.{u}]
    (hX : RingedSite.IsLocallyRinged (schemeFunctionsRingedSite J F hO))
    (hroot : LocalRoots (schemeFunctionsRingedSite J F hO) n)
    (L M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
    (hL : IsInvertible (schemeFunctionsRingedSite J F hO).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O).2 L)
    (hM : IsInvertible (schemeFunctionsRingedSite J F hO).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O).2 M)
    (al : tpow (schemeFunctionsRingedSite J F hO) L n ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
    (bl : tpow (schemeFunctionsRingedSite J F hO) M n ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))

/-- **The pairing adds the acting roots of unity.** Scaling the two trivializations by two roots
of unity scales their tensor product by the product of the two, which is the root of unity
attached to the sum of the two sections. -/
theorem rootAct_normalizedTensorPairing (U : Cᵒᵖ)
    (a b : (rootsOfUnitySheaf J F h n).obj.obj U)
    (s : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U)
    (t : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) M n bl).obj U) :
    normalizedTensor (schemeFunctionsRingedSite J F hO) L M n al bl U
        (rootAct J F hO h n L al U a s) (rootAct J F hO h n M bl U b t) =
      rootAct J F hO h n (tensorSheafOfModules (schemeFunctionsRingedSite J F hO) L M)
        (tensorTriv (schemeFunctionsRingedSite J F hO) L M n al bl) U (a + b)
        (normalizedTensor (schemeFunctionsRingedSite J F hO) L M n al bl U s t) := by
  apply Subtype.ext
  refine Eq.trans (congrArg₂
    (tensorSection (schemeFunctionsRingedSite J F hO) L M U.unop)
    (rootAct_val J F hO h n L al U a s) (rootAct_val J F hO h n M bl U b t)) ?_
  refine Eq.trans (tensorSection_smul_unit (schemeFunctionsRingedSite J F hO) L M U.unop
    (rootUnit J F hO h n U a) (rootUnit J F hO h n U b) s.val t.val) ?_
  refine Eq.trans (congrArg
    (fun z : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (schemeFunctionsRingedSite J F hO).O).obj.obj (op U.unop) : Type u)ˣ =>
      z.val • tensorSection (schemeFunctionsRingedSite J F hO) L M U.unop s.val t.val)
    (rootUnit_add J F hO h n U a b).symm) ?_
  exact (rootAct_val J F hO h n (tensorSheafOfModules (schemeFunctionsRingedSite J F hO) L M)
    (tensorTriv (schemeFunctionsRingedSite J F hO) L M n al bl) U (a + b)
    (normalizedTensor (schemeFunctionsRingedSite J F hO) L M n al bl U s t)).symm

variable [HasSheafify J AddCommGrpCat.{u}] [HasExt.{t} (Sheaf J AddCommGrpCat.{u})]

/-- **The class of the torsor of trivializations of a tensor product of pairs is the sum of the
two classes.** This is part (3) of the proof of Tag 040Q. -/
theorem trivializationTorsor_class_add :
    torsorIsoClassesEquivH1 (rootsOfUnitySheaf J F h n)
          (Quotient.mk _ (trivializationTorsor J F hO h n hX hroot L hL al)) +
        torsorIsoClassesEquivH1 (rootsOfUnitySheaf J F h n)
          (Quotient.mk _ (trivializationTorsor J F hO h n hX hroot M hM bl)) =
      torsorIsoClassesEquivH1 (rootsOfUnitySheaf J F h n)
        (Quotient.mk _ (trivializationTorsor J F hO h n hX hroot
          (tensorSheafOfModules (schemeFunctionsRingedSite J F hO) L M)
          (Stacks.SheafOfModules.isInvertible_tensorSheaf
            (schemeFunctionsRingedSite J F hO).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O).2 L M)
          (tensorTriv (schemeFunctionsRingedSite J F hO) L M n al bl))) := by
  refine torsorClass_add_of_equivariant' (rootsOfUnitySheaf J F h n) _ _ _
    (normalizedTensorPairing (schemeFunctionsRingedSite J F hO) L M n al bl) ?_
  intro U a b s t
  exact rootAct_normalizedTensorPairing J F hO h n L M hL hM al bl U a b s t

end

end AlgebraicGeometry

end
