module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeSectionsBijection
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionUnfold

/-!
# The transport that opens the chain of [Stacks, Tag 0EX3] (c), crossed

The first factor of `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
`.topDegreeFunctorObjIsoCohomologyUpstairs` is the transport along
`…TopDegreeBaseChange.topDegreeFunctor_obj_eq`, which identifies the value of the endofunctor
`Φ` of conclusion (b) of [Stacks, Tag 0EX3] with that value written out. The two sides are
definitionally equal, so the transport is the identity and crossing it is exactly the statement
that `Φ` applied to a morphism *is* the written-out morphism — which
`…TopDegreeBaseChange.HmulProjectionUnfold` supplies.

The crossing is proved here, in its own declaration and **at a bare module and a bare
morphism**, for the reason recorded in the implementation notes: the identification of the two
spellings of the object is a single definitional unfolding, and it only fits a heartbeat budget
it has to itself.

## Main results

* `…TopDegreeBaseChange.square_eqToIso_topDegreeFunctor_obj_eq`: **`Φ` applied to an
  endomorphism of a module crosses the transport that opens
  `…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs`**, becoming the written-out
  morphism.

## Implementation notes

*Why this is a declaration of its own, and why at bare variables.* Supplying
`…TopDegreeBaseChange.topDegreeFunctor_obj_eq` to `…TopDegreeBaseChange.square_eqToHom` asks the
elaborator to unify the transport's endpoints with the one definitional unfolding of `Φ` at an
object; done inside the long paste of conclusion (c) — where it shares its budget with the four
further crossings and with the specific module and multiplication operator the paste is taken
at — it exhausts the elaborator. Here the module and the morphism are variables, so nothing
inside them can unfold, and the check is the whole content of the declaration. The paste then
uses this as an equation, where no unfolding happens.

*Why the square goes through a helper rather than Mathlib's lemmas inline.* Rewriting
`CategoryTheory.eqToIso.hom` in the goal below leaves a target that is not type-correct at
`implicit` transparency, after which `CategoryTheory.eqToHom_refl` and
`CategoryTheory.comp_eqToHom_iff` both report that they cannot find their pattern. The helper is
those same Mathlib lemmas applied at variables of an abstract category, where the rewrites are at
default transparency.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  {V : S.Y'.Opens} [IsAffine (V : Scheme)]

/-- **`Φ` applied to an endomorphism crosses the transport that opens the chain.** The first
factor of `…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` is `eqToIso` of
`…TopDegreeBaseChange.topDegreeFunctor_obj_eq`; an endomorphism `ψ` of a `Γ(V, ⊤)`-module `N` is
carried across it by `Φ` to the degree-`d` cohomology of `F'|` tensored with the pullback of the
tilde module of `ψ`, read over the base ring.

Both sides of `topDegreeFunctor_obj_eq` are the same object, so the transport is the identity
and the square is the equality of the two morphisms, which is
`…TopDegreeBaseChange.topDegreeFunctor_map_eq_restrictBase` followed by
`…TopDegreeBaseChange.restrictScalars_rightDerived_tensorSheaf_map_eq`. -/
theorem square_eqToIso_topDegreeFunctor_obj_eq {N : ModuleCat.{u} Γ((V : Scheme), ⊤)}
    (ψ : N ⟶ N) :
    ((S.restrictBase V).topDegreeFunctor
            ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
              (inferInstance :
                ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                  F').IsQuasicoherent)⟩).map ψ ≫
          (eqToIso (topDegreeFunctor_obj_eq S F' N)).hom =
        (eqToIso (topDegreeFunctor_obj_eq S F' N)).hom ≫
          (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
              Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
            (((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).map
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                    (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
                ((𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
                  (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
                    ((AlgebraicGeometry.tilde.functor
                      (CommRingCat.of Γ((V : Scheme), ⊤))).map ψ) : _ ⟶ _)))) :=
  square_eqToHom (topDegreeFunctor_obj_eq S F' N)
    (heq_of_eq (Eq.trans (topDegreeFunctor_map_eq_restrictBase S F' ψ)
      (restrictScalars_rightDerived_tensorSheaf_map_eq S F' ψ)))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
