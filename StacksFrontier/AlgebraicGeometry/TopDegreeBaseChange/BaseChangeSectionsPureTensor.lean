module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeSectionsTail

/-!
# The pure-tensor agreement of [Stacks, Tag 0EX3] (c), granted the tail identification

`BaseChangeSectionsTail.lean` reads the `ψ` side of the pure-tensor agreement of conclusion (c) of
[Stacks, Tag 0EX3] as the sections over `V` of the ordinary unit followed by a tail in which no
unit occurs. This file assembles the agreement from the two sides' head-and-tail factorisations
and the identification of their tails, and states the head matching in the form that
factorisation asks for.

## Main results

* `…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul_eq_app_pullbackSection_of_tail`: the
  pure-tensor agreement of conclusion (c), from the two sides' head-and-tail factorisations and
  the identification of their tails.
* `…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE_of_id_obj`: the head matching with the
  identity functor dropped from the coefficient of its leading comparison.

## Implementation notes

What `htail` still owes, and why the reduction is not stated with the tails quantified, is
recorded in the implementation notes of `BaseChangeSectionsTail.lean`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TensorProduct
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

/-! ### The pure-tensor agreement, granted the tail identification -/

/-- **A map applied to an element, through a known factorisation.** At variables of a category of
modules. -/
private theorem apply_comp_of_eq {R : Type u} [Ring R] {M N P : ModuleCat.{u} R} {f : M ⟶ P}
    {g : M ⟶ N} {k : N ⟶ P} (hf : f = g ≫ k) (x : M) : f x = k (g x) := by
  rw [hf]
  rfl

/-- **A morphism of sheaves of modules read on sections, through a known factorisation.** At
variables. -/
private theorem sheaf_apply_comp_of_eq {Z : Scheme.{u}} {M N P : Z.Modules} {U : Z.Opens}
    {f : M ⟶ P} {g : M ⟶ N} {k : N ⟶ P} (hf : f = g ≫ k) (x : M.val.obj (op U)) :
    f.val.app (op U) x = k.val.app (op U) (g.val.app (op U) x) := by
  rw [hf]
  rfl

/-- **The pure-tensor agreement of [Stacks, Tag 0EX3] (c), granted the tail identification.** For
a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)` and a quasi-coherent
`F'`, the map `ψ` of `…TopDegreeBaseChange.baseChangeSectionsMap` agrees with `Γ(W, γ⁺)` on the
pure tensor `1 ⊗ a`, as soon as the two sides' **tails** agree.

The three hypotheses are the two sides' head-and-tail factorisations and the identification of
their tails.

* `hΘ` is discharged by
  `…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus_unit`, which
  fixes `ξ` as the degree-`d` higher direct image along `f'` of the ordinary unit of
  `(h')^* ⊣ (h')_*` and `Θ` as the `γ⁺` side's tail.
* `hT` is discharged by `psi_side_eq_sections_unit_comp_tail` fed with the head matching
  `…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE`, which fixes `T` as the `ψ` side's tail
  at that same `ξ` — its left-hand side is verbatim the `ψ` side of the agreement, as
  `…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul` computes it.
* `htail` is then **the one geometric identity conclusion (c) still owes**: the `ψ` side's tail
  `T` is the sections over `V` of the `γ⁺` side's tail `Θ`, restricted to `W`.

*Why the tails are carried as variables.* Written out, each is a composite of a dozen named
comparisons, and an application of either to an element exhausts the elaborator's recursion
budget — the wall `…TopDegreeBaseChange.fromExtendScalarsComp_one_tmul_of_eq` records. With `T`
and `Θ` variables fixed by `hT` and `hΘ` the reduction is checked on its own, and `htail` is read
off those two results.

Neither `Y'` nor `Y''` carries a hypothesis; only the two opens are affine. -/
theorem baseChangeSectionsMap_one_tmul_eq_app_pullbackSection_of_tail
    {Tgt : S.Y'.Modules}
    {ξ : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F' ⟶ Tgt}
    {Θ : Tgt ⟶ (Scheme.Modules.pushforward h).obj
      (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F'))}
    (hΘ : (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (topDirectImageBaseChangeMapPlus S F' h' f'' h
          (toShHom_comm_of_isPullback h' f'' h hsq)) = ξ ≫ Θ)
    {T : ModuleCat.of Γ(S.Y', V) Γ(Tgt, V) ⟶
      (ModuleCat.restrictScalars (h.appLE V W hWV).hom).obj
        (ModuleCat.of Γ(Y'', W)
          Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F'), W))}
    (hT : ((affineOpenCohomologyIsoSectionsOf S.f' S.quasiCompact_f' S.quasiSeparated_f'
              (‹IsAffine (V : Scheme)› : IsAffineOpen V) F' inferInstance S.d).inv ≫
            (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology S V F').hom) ≫
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
            ((ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
                  Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
                (affineOpenCohomologyPullbackMap hsq hWV
                    (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d ≫
                  (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
                    (restrictPullbackRightDerivedPlusIso h'
                      (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) ≫
              (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).inv ≫
                (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom) ≫
          (ModuleCat.restrictScalarsCongr (appLE_eq_comp_topIso S h hWV).symm).hom.app
            (ModuleCat.of Γ(Y'', W)
              Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
                ((Scheme.Modules.pullback h').obj F'), W)) = ξ.val.app (op V) ≫ T)
    (htail : ∀ b : Γ(Tgt, V),
      T b = (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F')).val.map (homOfLE hWV).op
          (Θ.val.app (op V) b))
    (a : Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', V)) :
    baseChangeSectionsMap S F' h' f'' h hsq hWV
        ((1 : Γ(Y'', W)) ⊗ₜ[Γ(S.Y', V), (h.appLE V W hWV).hom] a) =
      (topDirectImageBaseChangeMapPlus S F' h' f'' h
          (toShHom_comm_of_isPullback h' f'' h hsq)).val.app (op W)
        (Scheme.Modules.pullbackSection h
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
          V W hWV a) :=
  ((baseChangeSectionsMap_one_tmul S F' h' f'' h hsq hWV a).trans
      (((apply_comp_of_eq hT a).trans (htail _)).trans
        (congrArg (ConcreteCategory.hom
            ((((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
              ((Scheme.Modules.pullback h').obj F')).val.map (homOfLE hWV).op))
          (sheaf_apply_comp_of_eq hΘ a).symm))).trans
    (Scheme.Modules.pullbackSection_homEquiv h
      (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
      (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F'))
      (topDirectImageBaseChangeMapPlus S F' h' f'' h
        (toShHom_comm_of_isPullback h' f'' h hsq)) V W hWV a).symm

omit [F'.IsQuasicoherent] [IsAffine (V : Scheme)] [IsAffine (W : Scheme)] in
/-- **The head matching, with the identity functor dropped from the coefficient of its leading
comparison.** `…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE` states its leading factor at
`(𝟭 _).obj F'`; `psi_side_eq_sections_unit_comp_tail` asks for it at `F'`. The two comparisons are
one and the same, by `rightDerivedPlusRestrictObjIso_id_obj`, and the rest of the factorisation is
carried as the variable `r`, so that nothing of its shape enters here. -/
theorem rightDerivedPlus_map_unit_resLE_of_id_obj
    {r : (Scheme.Modules.restrictFunctor V.ι).obj
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F') ⟶
        ((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).obj
          ((Scheme.Modules.pushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV))).obj
            ((Scheme.Modules.pullback (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                  (preimage_le_preimage_of_isPullback hsq hWV))).obj
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')))}
    (hr : ((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
              (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV))).unit.app
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')) =
        (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d
            ((𝟭 (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace))).obj F')).hom ≫ r) :
    ((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
              (preimage_le_preimage_of_isPullback hsq hWV))).unit.app
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')) =
      (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F').hom ≫ r :=
  (rightDerivedPlusRestrictObjIso_id_obj S F' (V := V)) ▸ hr

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
