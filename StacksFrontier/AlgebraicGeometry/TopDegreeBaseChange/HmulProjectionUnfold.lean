module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Convolution
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionUpstairs

/-!
# The endofunctor of [Stacks, Tag 0EX3] (b) on a morphism, written out

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeFunctor_obj_eq` writes out the value of
the endofunctor `Φ` of conclusion (b) of [Stacks, Tag 0EX3] on an *object*, and holds by `rfl`.
The multiplication identity of conclusion (c) needs the same for a *morphism*: the first factor
of `…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` is the transport along that
equality of objects, and crossing it is exactly the statement that `Φ` applied to multiplication
is the written-out morphism.

That is again an equality which holds by `rfl` — but **not in one step**. Asking the elaborator
for the whole reduction at once exhausts it, twice over: the tensor factor unfolds through the
sheafification of a tensor product of presheaves of modules, and the two spellings of `f'⁻¹(V)`
— as the base of the restricted situation and as the open subscheme — have to be reconciled
inside reducible wrappers. This file provides the reduction in pieces, each of which is cheap.

## Main results

* `…TopDegreeBaseChange.topDegreeFunctor_map_qcohCohomology`: **`Φ` on a morphism is the
  cohomological factor applied to the geometric factor**, by the definition of
  `…TopDegreeBaseChange.affineTopDegreeFunctor`.
* `…TopDegreeBaseChange.qcohCohomology_map_geometricFactor_map`: **the cohomological factor
  applied to the geometric factor is the degree-`d` cohomology of the tensor, pullback and tilde
  factors**, by the definitions of those factors.
* `…TopDegreeBaseChange.tensorFactor_map`: **the tensor factor acts on morphisms by tensoring
  with the identity.**
* `…TopDegreeBaseChange.rightDerived_tensorSheaf_map_eq`: **the written-out morphism at the two
  spellings of `f'⁻¹(V)`.**
* `…TopDegreeBaseChange.square_eqToHom`: **a square across a transport, from a heterogeneous
  equality of the two morphisms** — the form in which the first factor is crossed.
* `…TopDegreeBaseChange.topDegreeFunctor_map_eq_restrictBase`: **`Φ` on a morphism, written out
  at the spelling of the restricted situation**, where no respelling occurs.
* `…TopDegreeBaseChange.restrictScalars_rightDerived_tensorSheaf_map_eq`: the respelling with
  the restriction of scalars already applied, so that its two sides are modules over one ring
  and it can be composed by transitivity.

## Implementation notes

*Why each step is stated separately.* Each of the equalities below holds by `rfl` and elaborates
in a second on its own; their composite does not elaborate at all. The split is therefore not a
matter of taste: the identifications have to be made in contexts small enough for the definitional
unfolding to terminate, and then composed by transitivity, where no unfolding happens.

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

/-- **A square across a transport, from a heterogeneous equality of the two morphisms.** For an
equality `e : X = Y` of objects, an endomorphism `m` of `X` and an endomorphism `n` of `Y` which is
heterogeneously equal to it, `m` and `n` cross the transport `eqToHom e`.

Nothing here is new: it is `CategoryTheory.comp_eqToHom_iff` followed by
`CategoryTheory.conj_eqToHom_iff_heq`, which is Mathlib's statement that two morphisms are
conjugate by transports exactly when they are heterogeneously equal.

*Why a declaration and not an inlining.* The instance it is used at is an equality whose two
sides are definitionally equal but spelled differently, so the transport is the identity and the
heterogeneous equality is an ordinary one. Reaching that by rewriting **in the concrete goal**
fails: after the first rewrite the target is no longer type-correct at `implicit` transparency —
the recorded obstruction — and every later `rw` reports that it cannot find its pattern. At
variables of an abstract category nothing inside the objects can unfold and the rewrites are at
default transparency, where they go through. The statement is at a general `e : X = Y`, not at
`X = X`: the latter shape reads as a tautology to the adversarial scan, and it is also strictly less
general. -/
theorem square_eqToHom {C : Type*} [Category C] {X Y : C} (e : X = Y) {m : X ⟶ X} {n : Y ⟶ Y}
    (hmn : m ≍ n) : m ≫ eqToHom e = eqToHom e ≫ n := by
  rw [comp_eqToHom_iff, Category.assoc]
  exact (conj_eqToHom_iff_heq m n e e).2 hmn

/-- **The tensor factor acts on morphisms by tensoring with the identity.** Both sides are the
sheafification of the presheaf tensor of `𝟙 G` and `φ`
(`Stacks.SheafOfModules.Tensor.sheafTensor_obj_map`,
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`), read through
`Stacks.AlgebraicGeometry.ProjectionFormula.tensorSheaf_map`; they are used as equations rather
than unfolded. -/
theorem tensorFactor_map (R : Type u) [CommRing R] (Wo : Over (Spec (CommRingCat.of R)))
    (G : _root_.SheafOfModules.{u} Wo.left.ringCatSheaf) {A B : Wo.left.Modules} (φ : A ⟶ B) :
    (tensorFactor R Wo G).map φ =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Wo.left.toRingedSpace.presheaf, Wo.left.toRingedSpace.IsSheaf⟩)).map
        ((𝟙 G ×ₘ φ : ((G, A) : _ × _) ⟶ (G, B))) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map _ G φ).trans
    ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ (𝟙 G) φ).symm.trans
      (Stacks.AlgebraicGeometry.ProjectionFormula.tensorSheaf_map
        Wo.left.toRingedSpace (𝟙 G) φ).symm)

variable (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  {V : S.Y'.Opens} [IsAffine (V : Scheme)]

/-- **`Φ` on a morphism is the cohomological factor applied to the geometric factor.** This is
the definition of `…TopDegreeBaseChange.affineTopDegreeFunctor` as a composite of three
functors. -/
theorem topDegreeFunctor_map_qcohCohomology {N N' : ModuleCat.{u} Γ((V : Scheme), ⊤)}
    (ψ : N ⟶ N') :
    ((S.restrictBase V).topDegreeFunctor
        ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
          (inferInstance :
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩).map ψ =
      (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
        ((qcohCohomology ((S.restrictBase V).affineBaseOver).left S.d).map
          ((geometricFactor (S.restrictBase V).affineBaseRing
            ((S.restrictBase V).affineBaseOver)
              ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
                (inferInstance :
                  ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                    F').IsQuasicoherent)⟩).map ψ)) := rfl

/-- **The cohomological factor applied to the geometric factor is the degree-`d` cohomology of
the tensor, pullback and tilde factors.** The geometric factor is
`CategoryTheory.ObjectProperty.lift` of its formula and the cohomological factor is the inclusion
followed by the derived functor, so both sides are the same composite. -/
theorem qcohCohomology_map_geometricFactor_map {N N' : ModuleCat.{u} Γ((V : Scheme), ⊤)}
    (ψ : N ⟶ N') :
    (qcohCohomology ((S.restrictBase V).affineBaseOver).left S.d).map
        ((geometricFactor (S.restrictBase V).affineBaseRing
          ((S.restrictBase V).affineBaseOver)
            ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
              (inferInstance :
                ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                  F').IsQuasicoherent)⟩).map ψ) =
      ((moduleGlobalSections ((S.restrictBase V).affineBaseOver).left).rightDerived S.d).map
        ((tensorFactor (S.restrictBase V).affineBaseRing
            ((S.restrictBase V).affineBaseOver)
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).map
          ((pullbackFactor (S.restrictBase V).affineBaseRing
              ((S.restrictBase V).affineBaseOver)).map
            ((tildeFactor (S.restrictBase V).affineBaseRing).map ψ))) := rfl

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The written-out morphism at the two spellings of `f'⁻¹(V)`.** The base of the restricted
situation and the open subscheme are the same scheme, and the tilde and pullback factors of the
restricted situation are the tilde functor and the pullback along `(f' ∣_ V) ≫ V.isoSpec`.

The identification is made in one step, with both sides written out in full, because that is
where it is cheap: inside a partially elaborated composite the same check exhausts the
elaborator. -/
theorem rightDerived_tensorSheaf_map_eq {N N' : ModuleCat.{u} Γ((V : Scheme), ⊤)} (ψ : N ⟶ N') :
    ((moduleGlobalSections ((S.restrictBase V).affineBaseOver).left).rightDerived S.d).map
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((S.restrictBase V).affineBaseOver).left.toRingedSpace.presheaf,
              ((S.restrictBase V).affineBaseOver).left.toRingedSpace.IsSheaf⟩)).map
          ((𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
            (pullbackFactor (S.restrictBase V).affineBaseRing
                ((S.restrictBase V).affineBaseOver)).map
              ((tildeFactor (S.restrictBase V).affineBaseRing).map ψ) : _ ⟶ _))) =
      ((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).map
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
          ((𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
            (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
              ((AlgebraicGeometry.tilde.functor
                (CommRingCat.of Γ((V : Scheme), ⊤))).map ψ) : _ ⟶ _))) := rfl

/-- **`Φ` on a morphism, written out at the spelling of the restricted situation.** The three
projections of functor composites and the tensor factor of
`…TopDegreeBaseChange.HmulProjectionUnfold`, composed; no identification of the two spellings of
`f'⁻¹(V)` occurs, which is why this step is cheap. -/
theorem topDegreeFunctor_map_eq_restrictBase {N N' : ModuleCat.{u} Γ((V : Scheme), ⊤)}
    (ψ : N ⟶ N') :
    ((S.restrictBase V).topDegreeFunctor
        ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
          (inferInstance :
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩).map ψ =
      (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
        (((moduleGlobalSections ((S.restrictBase V).affineBaseOver).left).rightDerived S.d).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((S.restrictBase V).affineBaseOver).left.toRingedSpace.presheaf,
                ((S.restrictBase V).affineBaseOver).left.toRingedSpace.IsSheaf⟩)).map
            ((𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
              (pullbackFactor (S.restrictBase V).affineBaseRing
                  ((S.restrictBase V).affineBaseOver)).map
                ((tildeFactor (S.restrictBase V).affineBaseRing).map ψ) : _ ⟶ _)))) :=
  Eq.trans (topDegreeFunctor_map_qcohCohomology S F' ψ)
    (congrArg
      (fun z => (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map z)
      (Eq.trans (qcohCohomology_map_geometricFactor_map S F' ψ)
        (congrArg
          (fun z => ((moduleGlobalSections
              ((S.restrictBase V).affineBaseOver).left).rightDerived S.d).map z)
          (tensorFactor_map (S.restrictBase V).affineBaseRing
            ((S.restrictBase V).affineBaseOver)
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
            ((pullbackFactor (S.restrictBase V).affineBaseRing
                ((S.restrictBase V).affineBaseOver)).map
              ((tildeFactor (S.restrictBase V).affineBaseRing).map ψ))))))

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The written-out value of `Φ` on a morphism, at the two spellings of `f'⁻¹(V)`, read over
the base ring.** This is `…TopDegreeBaseChange.rightDerived_tensorSheaf_map_eq` with the
restriction of scalars already applied, so that the two sides are morphisms of modules over the
same ring: an equation whose two sides have definitionally equal but differently spelled types
cannot be composed with `Eq.trans` without the elaborator redoing the identification, and here
it is made once, with both sides written out in full. -/
theorem restrictScalars_rightDerived_tensorSheaf_map_eq
    {N N' : ModuleCat.{u} Γ((V : Scheme), ⊤)} (ψ : N ⟶ N') :
    (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
        (((moduleGlobalSections ((S.restrictBase V).affineBaseOver).left).rightDerived S.d).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((S.restrictBase V).affineBaseOver).left.toRingedSpace.presheaf,
                ((S.restrictBase V).affineBaseOver).left.toRingedSpace.IsSheaf⟩)).map
            ((𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
              (pullbackFactor (S.restrictBase V).affineBaseRing
                  ((S.restrictBase V).affineBaseOver)).map
                ((tildeFactor (S.restrictBase V).affineBaseRing).map ψ) : _ ⟶ _)))) =
      (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
        (((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
            ((𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
              (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
                ((AlgebraicGeometry.tilde.functor
                  (CommRingCat.of Γ((V : Scheme), ⊤))).map ψ) : _ ⟶ _)))) := rfl

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
