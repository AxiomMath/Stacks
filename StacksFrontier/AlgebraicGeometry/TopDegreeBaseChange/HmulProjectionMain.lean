module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionTarget
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionTransport

/-!
# The multiplication identity of [Stacks, Tag 0EX3] (c), and the bijectivity it was the last
obstacle to

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.bijective_baseChangeSectionsMap` asks for one
identity — that the identification of the right-hand end of the comparison map of conclusion (c)
of [Stacks, Tag 0EX3] with the value of the endofunctor `Φ` of conclusion (b) at the functions on
`W` carries `Φ(multiplication by a)` to multiplication by `a`. This file proves it, and with it
the bijectivity of

`ψ : Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V) ⟶ Γ(R^d f''_* (h')^* F', W)`

over a compatible pair of affine opens, with no hypothesis beyond the situation, a cartesian
square and the affineness of the two opens.

The identity is assembled from the pieces proved in this directory. Two of the three factors of
the identification are scalar bookkeeping and were discharged by
`…TopDegreeBaseChange.hmul_of_mulUpstairs`; the first factor is the chain

`Φ(Γ(Y'', W)) ≅ H^d(f'⁻¹(V), F'| ⊗ (f' ∣_ V)^* Γ(Y'', W)~) ≅ H^d(f''⁻¹(W), ((h')^* F')|)`

whose geometric part is crossed by
`…TopDegreeBaseChange.sectionScalar_comp_cohomologyPullbackIsoTensorTildeAffineOpens` and whose
tilde part by `…TopDegreeBaseChange.mulLeftRestrictScalars_comp_pullbackTildeSectionsIso`.

## Main results

* `…TopDegreeBaseChange.mulUpstairs`: **multiplication by `a` crosses the identification of
  `Φ(Γ(Y'', W))` with the cohomology of `((h')^* F')|` over `f''⁻¹(W)`** — the hypothesis
  `hmul_of_mulUpstairs` asks for.
* `…TopDegreeBaseChange.hmul_topDegreeFunctorObjIsoTargetSections`: **the identity
  `bijective_baseChangeSectionsMap` asks for.**
* `…TopDegreeBaseChange.bijective_baseChangeSectionsMap_of_affineOpens`: **`ψ` is bijective**,
  with no hypothesis left.

## Implementation notes

*The transport that opens the chain is the identity.* The first factor of
`…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` is `eqToIso` of
`…TopDegreeBaseChange.topDegreeFunctor_obj_eq`, an equality of objects that holds by `rfl`; so
the transport is the identity and the square across it is the statement that `Φ` applied to
multiplication *is* the written-out morphism, again by `rfl`. Crossing it is
`…TopDegreeBaseChange.square_eqToIso_topDegreeFunctor_obj_eq`, which is a declaration of its own
and at a bare module and a bare morphism: the identification of the two spellings of the object
is one definitional unfolding, and asking for it inside the paste below — alongside the four
further crossings — exhausts the elaborator. Used as an equation, it costs nothing.

*The squares are pasted along the `Iso.trans` tree of the definition*, for the reason recorded
in `…TopDegreeBaseChange.HmulProjectionUpstairs`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.IntegralTransformQcoh
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

/-- **Multiplication by `a` crosses the identification of the value of `Φ` at the functions on
`W` with the cohomology upstairs.** This is the hypothesis
`…TopDegreeBaseChange.hmul_of_mulUpstairs` asks for: the endofunctor `Φ` of [Stacks, Tag 0EX3]
(b) applied to multiplication by `a : Γ(Y'', W)` is carried by
`…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` to multiplication by the pullback
`c` of `a` on the degree-`d` cohomology of `((h')^* F')|` over `f''⁻¹(W)`.

The identification has three factors. The first is a transport along an equality that holds by
`rfl`, so multiplication crosses it by
`…TopDegreeBaseChange.square_eqToIso_topDegreeFunctor_obj_eq`. The second rewrites the tilde
factor and is crossed by
`…TopDegreeBaseChange.mulLeftRestrictScalars_comp_pullbackTildeSectionsIso` tensored into the
second factor and taken in cohomology. The third is the computation of the
cohomology upstairs, crossed by
`…TopDegreeBaseChange.sectionScalar_comp_cohomologyPullbackIsoTensorTildeAffineOpens`, followed
by the comparison of the two spellings of that cohomology, crossed by
`…TopDegreeBaseChange.preimageScalar_comp_restrictPullbackRightDerivedPlusIso_inv`; the scalar
that comes out is read as a multiplication by
`…TopDegreeBaseChange.rightDerivedPlus_moduleGlobalSections_map_sectionScalar`. -/
theorem mulUpstairs (a : Γ(Y'', W)) (c : Γ((f'' ⁻¹ᵁ W : Scheme), ⊤))
    (hc : (f'' ∣_ W).appTop.hom ((Scheme.Opens.topIso W).inv.hom a) = c) :
    ((S.restrictBase V).topDegreeFunctor
          ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
            (inferInstance :
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                F').IsQuasicoherent)⟩).map
          (mulLeftRestrictScalars ((h.appLE V W hWV).hom.comp
            (Scheme.Opens.topIso V).hom.hom) a) ≫
        (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).hom =
      (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).hom ≫
        (ModuleCat.restrictScalars
            ((h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom.comp
              (algebraMap (S.restrictBase V).affineBaseRing
                Γ((((S.restrictBase V).affineBaseOver)).left, ⊤)))).map
          (c • 𝟙 (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus
            (S.d : ℤ)).obj
              ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
                ((Scheme.Modules.pullback h').obj F')))) :=
  comp_two_squares
    (square_eqToIso_topDegreeFunctor_obj_eq S F'
      (mulLeftRestrictScalars ((h.appLE V W hWV).hom.comp
        (Scheme.Opens.topIso V).hom.hom) a))
    (map_comp_square (ModuleCat.restrictScalars
        (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤)))
      (comp_two_squares
        (map_comp_square ((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d)
          (bifunctor_square_right
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩))
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
            (mulLeftRestrictScalars_comp_pullbackTildeSectionsIso S h hWV a)))
        (comp_two_squares
          (inv_square _
            (sectionScalar_comp_cohomologyPullbackIsoTensorTildeAffineOpens hsq hWV
              (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d
              ((Scheme.Opens.topIso W).symm.commRingCatIsoToRingEquiv a) c hc))
          (map_comp_square (ModuleCat.restrictScalars
              (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom)
            (sectionScalar_comp_restrictPullbackRightDerivedPlusIso_inv (h := h) (h' := h')
              (preimage_le_preimage_of_isPullback hsq hWV) F' S.d
              ((Scheme.Opens.topIso W).symm.commRingCatIsoToRingEquiv a) c hc)))))

/-- **The identity `…TopDegreeBaseChange.bijective_baseChangeSectionsMap` asks for.** The
identification `…TopDegreeBaseChange.topDegreeFunctorObjIsoTargetSections` of the right-hand end
`Γ(R^d f''_* (h')^* F', W)` with the value of the endofunctor `Φ` of [Stacks, Tag 0EX3] (b) at
the functions on `W` carries `Φ(multiplication by a)` to multiplication by `a`.

This is `…TopDegreeBaseChange.hmul_of_mulUpstairs` fed with `mulUpstairs`. -/
theorem hmul_topDegreeFunctorObjIsoTargetSections (a : Γ(Y'', W)) :
    ((S.restrictBase V).topDegreeFunctor
          ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
            (inferInstance :
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                F').IsQuasicoherent)⟩).map
          (mulLeftRestrictScalars ((h.appLE V W hWV).hom.comp
            (Scheme.Opens.topIso V).hom.hom) a) ≫
        (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom =
      (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom ≫
        (ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
            (Scheme.Opens.topIso V).hom.hom)).map
          (a • 𝟙 (ModuleCat.of Γ(Y'', W)
            Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
              ((Scheme.Modules.pullback h').obj F'), W))) :=
  hmul_of_mulUpstairs S F' h' f'' h hsq hWV a _ rfl
    (mulUpstairs S F' h' f'' h hsq hWV a _ rfl)

include hsq in
/-- **`ψ` is bijective**, with no hypothesis left. For a top-degree base-change situation `S`, a
quasi-coherent `F'` on `X'`, a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'` and an affine open `W` of `Y''` with `W ≤ h⁻¹(V)`, the
`Γ(Y'', W)`-linear map

`ψ : Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V) ⟶ Γ(R^d f''_* (h')^* F', W)`

of `…TopDegreeBaseChange.baseChangeSectionsMap` is bijective. Neither base carries a hypothesis
and neither morphism carries one beyond what the situation provides; only the two opens are
affine.

This is `…TopDegreeBaseChange.bijective_baseChangeSectionsMap` fed with
`hmul_topDegreeFunctorObjIsoTargetSections`. -/
theorem bijective_baseChangeSectionsMap_of_affineOpens :
    Function.Bijective (ModuleCat.Hom.hom
      (baseChangeSectionsMap S F' h' f'' h hsq hWV)) :=
  bijective_baseChangeSectionsMap S F' h' f'' h hsq hWV
    (hmul_topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
