module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineOpenTensorCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionBridge
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionFormula
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionLeray
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionTilde
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionUnit

/-!
# Multiplication crosses the computation of the cohomology upstairs

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.cohomologyPullbackIsoTensorTildeAffineOpens` is the
computation, over a compatible pair of affine opens, of the degree-`d` cohomology of `(h')^* F'`
upstairs as the degree-`d` cohomology downstairs of `F'` tensored with the pullback of the tilde
module of the functions on `W`. It is the geometric heart of conclusion (c) of
[Stacks, Tag 0EX3], and this file proves that multiplication by a function on `W` crosses it.

The computation is a composite of four factors, and the three with content have each been
crossed separately:

* the projection formula —
  `…TopDegreeBaseChange.sectionScalar_comp_pushforwardPullbackTensorIsoRight`;
* the Leray comparison along the affine `h' ∣` —
  `…TopDegreeBaseChange.cohomologyPullbackIsoPushforward_naturality`;
* the tilde comparison of the direct image of a structure sheaf —
  `…TopDegreeBaseChange.mulLeftRestrictScalars_comp_pushforwardUnitIsoAffineTilde`.

What remains here is to paste them, which needs two pieces of glue: a square in the second
argument of a bifunctor is obtained from a square in that argument, and a square across an
isomorphism crosses its inverse.

## Main results

* `…TopDegreeBaseChange.sectionScalar_comp_cohomologyPullbackIsoTensorTildeAffineOpens`:
  **multiplication by a function on `W` crosses the computation of the cohomology upstairs.**
* `…TopDegreeBaseChange.sectionScalar_eq_preimageScalar`: the two spellings of multiplication by
  the pullback of a function on an open of the target agree.
* `…TopDegreeBaseChange.sectionScalar_comp_restrictPullbackRightDerivedPlusIso_inv`:
  **multiplication crosses the comparison of the two spellings of the cohomology upstairs and
  comes out as a scalar multiple of an identity**, which is the shape the multiplication
  identity of (c) needs at that end.

## Implementation notes

*Why the squares are pasted along the `Iso.trans` tree of the definition.* `(α ≪≫ β).hom` is
`α.hom ≫ β.hom` and `(F.mapIso α).hom` is `F.map α.hom`, both definitionally, so a paste built by
following the shape of the definition has exactly the association the goal has, and the kernel
checks the identification. Building the paste in any other order needs
`CategoryTheory.Category.assoc` on goals where the rewriting tactics cannot find it.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.IntegralTransformQcoh
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **A square in the second argument of a bifunctor.** If `n` transports `m` across `g`, then
the image of `𝟙 ×ₘ n` transports the image of `𝟙 ×ₘ m` across the image of `𝟙 ×ₘ g`.

Stated for bare variables: its instance below is at a tensor product of module sheaves, where
the rewriting tactics cannot find `CategoryTheory.Functor.map_comp`. -/
theorem bifunctor_square_right {C D E : Type*} [Category C] [Category D] [Category E]
    (B : C × D ⥤ E) (A : C) {X Y : D} {m : X ⟶ X} {g : X ⟶ Y} {n : Y ⟶ Y}
    (h : m ≫ g = g ≫ n) :
    B.map ((𝟙 A ×ₘ m : ((A, X) : C × D) ⟶ (A, X))) ≫
        B.map ((𝟙 A ×ₘ g : ((A, X) : C × D) ⟶ (A, Y))) =
      B.map ((𝟙 A ×ₘ g : ((A, X) : C × D) ⟶ (A, Y))) ≫
        B.map ((𝟙 A ×ₘ n : ((A, Y) : C × D) ⟶ (A, Y))) := by
  rw [← B.map_comp, ← B.map_comp, prod_comp, prod_comp]
  simp only [Category.id_comp]
  rw [h]

/-- **The two spellings of multiplication by the pullback of a function on an open of the
target.** For `f : X ⟶ Y`, an open `U` of `Y` and a function `r` on `U`, multiplication by the
pullback `c = (f ∣_ U)^♯ r` on a module over `f⁻¹(U)` is
`…TopDegreeBaseChange.preimageScalar`.

Both are the action of `r` from the `Γ(U, ⊤)`-linear structure, compared through
`…TopDegreeBaseChange.sectionScalar_eq_baseScalar`; the image of `r` under the structure
morphism of `f⁻¹(U)` over `Spec Γ(U, ⊤)` is its pullback, by
`…TopDegreeBaseChange.baseRingToSections_comp_toSpecΓ_top`. -/
theorem sectionScalar_eq_preimageScalar {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (r : Γ((U : Scheme), ⊤)) (c : Γ((f ⁻¹ᵁ U : Scheme), ⊤))
    (hc : (f ∣_ U).appTop.hom r = c) (M : (f ⁻¹ᵁ U : Scheme).Modules) :
    sectionScalar (f ⁻¹ᵁ U : Scheme) c M = preimageScalar f U r M := by
  subst hc
  refine Eq.trans (congrArg (fun z => sectionScalar (f ⁻¹ᵁ U : Scheme) z M)
    (baseRingToSections_comp_toSpecΓ_top (f ∣_ U) r).symm) ?_
  exact sectionScalar_eq_baseScalar ↑Γ((U : Scheme), ⊤)
    (Over.mk ((f ∣_ U) ≫ (U : Scheme).toSpecΓ)) r M

variable {X' Y' X'' Y'' : Scheme.{u}} {f' : X' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}
  {h : Y'' ⟶ Y'}

/-- **Multiplication by a function on `W` crosses the computation of the cohomology
upstairs.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)`, a quasi-coherent `F'`,
a function `a` on `W` and its pullback `c` to `f''⁻¹(W)`, the computation
`…TopDegreeBaseChange.cohomologyPullbackIsoTensorTildeAffineOpens` carries multiplication by `c`
on the cohomology upstairs to multiplication by `a` in the tilde factor downstairs.

The three factors with content are crossed by the projection-formula, Leray and tilde statements
of this directory; the fourth is the rewriting of the tilde factor, which is the third of them
pushed through the pullback, the tensor product and the cohomology. -/
theorem sectionScalar_comp_cohomologyPullbackIsoTensorTildeAffineOpens
    (hsq : IsPullback h' f'' f' h) {V : Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens}
    [IsAffine (W : Scheme)] (hWV : W ≤ h ⁻¹ᵁ V)
    (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V)) (F' : X'.Modules) (hF' : F'.IsQuasicoherent)
    (n : ℕ) (a : Γ((W : Scheme), ⊤)) (c : Γ((f'' ⁻¹ᵁ W : Scheme), ⊤))
    (hc : (f'' ∣_ W).appTop.hom a = c) :
    (ModuleCat.restrictScalars
            (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle).appTop.hom).map
          (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerived n).map
            (sectionScalar (f'' ⁻¹ᵁ W : Scheme) c
              ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
                ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')))) ≫
        (cohomologyPullbackIsoTensorTildeAffineOpens hsq hWV hle F' hF' n).hom =
      (cohomologyPullbackIsoTensorTildeAffineOpens hsq hWV hle F' hF' n).hom ≫
        ((moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)).rightDerived n).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                (f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
            ((𝟙 ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F') ×ₘ
              (Scheme.Modules.pullback (f' ∣_ V)).map
                ((Stacks.Coherent.affineTilde (V : Scheme)).map
                  (mulLeftRestrictScalars (h.resLE V W hWV).appTop.hom a)) : _ ⟶ _))) := by
  have : IsAffineHom (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle) :=
    isAffineHom_resLE_of_isPullback hsq hWV hle
  refine comp_two_squares
    (comp_two_squares
      (cohomologyPullbackIsoPushforward_naturality
        (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)
        ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
        (Scheme.Modules.isQuasicoherent_restrictFunctor (f' ⁻¹ᵁ V).ι F') n _)
      (map_comp_square ((moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)).rightDerived n)
        (inv_square _
          (sectionScalar_comp_pushforwardPullbackTensorIsoRight (f' ∣_ V)
            (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle) (f'' ∣_ W) (h.resLE V W hWV)
            (isPullback_resLE_of_isPullback hsq hWV)
            ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
            (Scheme.Modules.isQuasicoherent_restrictFunctor (f' ⁻¹ᵁ V).ι F') a c hc))))
    (map_comp_square ((moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)).rightDerived n)
      (bifunctor_square_right (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
            (f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩))
        ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
        (map_comp_square (Scheme.Modules.pullback (f' ∣_ V))
          (inv_square _
            (mulLeftRestrictScalars_comp_pushforwardUnitIsoAffineTilde
              (h.resLE V W hWV) a)))))


/-- **Multiplication by a function on `W` crosses the comparison of the two spellings of the
cohomology upstairs, and comes out as a scalar.** For a function `a` on `W` with pullback `c` on
`f''⁻¹(W)`, multiplication by `c` on the `ℕ`-indexed cohomology of the pullback of `F'|` crosses
the inverse of `…TopDegreeBaseChange.restrictPullbackRightDerivedPlusIso` into multiplication by
`c` on the `ℤ`-indexed cohomology of the restriction of `(h')^* F'`.

This is `…TopDegreeBaseChange.preimageScalar_comp_restrictPullbackRightDerivedPlusIso_inv` read
through `sectionScalar_eq_preimageScalar`, with the resulting cohomology of a multiplication read
as a scalar by
`…TopDegreeBaseChange.rightDerivedPlus_moduleGlobalSections_map_sectionScalar`. It is the last
factor of the chain the multiplication identity of [Stacks, Tag 0EX3] (c) crosses, in the shape
that identity needs: a scalar multiple of an identity. -/
theorem sectionScalar_comp_restrictPullbackRightDerivedPlusIso_inv {V : Y'.Opens}
    {W : Y''.Opens} (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V)) (F' : X'.Modules) (d : ℕ)
    (a : Γ((W : Scheme), ⊤)) (c : Γ((f'' ⁻¹ᵁ W : Scheme), ⊤))
    (hc : (f'' ∣_ W).appTop.hom a = c) :
    ((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerived d).map
          (sectionScalar (f'' ⁻¹ᵁ W : Scheme) c
            ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
              ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))) ≫
        (restrictPullbackRightDerivedPlusIso h' hle F' d).inv =
      (restrictPullbackRightDerivedPlusIso h' hle F' d).inv ≫
        (c • 𝟙 (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus (d : ℤ)).obj
          ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
            ((Scheme.Modules.pullback h').obj F')))) := by
  have hbr : ∀ M : (f'' ⁻¹ᵁ W : Scheme).Modules,
      sectionScalar (f'' ⁻¹ᵁ W : Scheme) c M = preimageScalar f'' W a M :=
    fun M => sectionScalar_eq_preimageScalar f'' W a c hc M
  refine Eq.trans (congrArg
    (fun z => ((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerived d).map z ≫
      (restrictPullbackRightDerivedPlusIso h' hle F' d).inv) (hbr _)) ?_
  refine Eq.trans
    (preimageScalar_comp_restrictPullbackRightDerivedPlusIso_inv h' hle F' d a) ?_
  refine congrArg
    (fun z => (restrictPullbackRightDerivedPlusIso h' hle F' d).inv ≫ z) ?_
  refine Eq.trans (congrArg
    (fun z => ((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus (d : ℤ)).map z)
    (hbr _).symm) ?_
  exact rightDerivedPlus_moduleGlobalSections_map_sectionScalar
    (f'' ⁻¹ᵁ W : Scheme) d c _

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
