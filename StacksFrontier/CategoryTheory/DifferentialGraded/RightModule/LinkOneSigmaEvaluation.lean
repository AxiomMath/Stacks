module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.LinkApplyLemmas
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaCochainCommShift

/-!
# The first link on the Yoneda image of a morphism, computed on cocycles

`DGCategory.RightModule.homShiftEquivEvaluationGradedCohomology_mk` computes the first link of
[Stacks, Tag 09LK] on a morphism `h_K ⟶ M⟦n⟧` *already presented* as the homotopy class of a
degree-zero cocycle. The morphism the chain is applied to is not presented that way: it is

`h_f ≫ σ_n`, where `σ_n = (K(h).commShiftIso n).app Y`

is the canonical comparison `h_{Y⟦n⟧} ≅ (h_Y)⟦n⟧` of the differential graded Yoneda functor and
`f : K ⟶ Y⟦n⟧`. This file supplies the missing presentation and the resulting value.

## Main results

* `DGCategory.RightModule.symm_toShift_mem_gradedCocycles`: the inverse of the identification of
  axiom (B) carries a degree-zero cocycle `K ⟶ X⟦n⟧` to a cocycle of the shifted representable
  module.
* `CochainComplex.homShiftEquivEvaluationGradedCohomology_yonedaOnK_map_comp_commShiftIso`:
  **the first link takes `h_f ≫ σ_n` to the class of the degree-`n` cocycle `f` is the
  reindexing of.**

## The signs, audited

The value carries no Koszul sign, and the reason is not that one of the degrees in sight is zero.
There are exactly three places a sign could enter a composite built from
`DGCategory.yonedaShiftHom`, and each is accounted for:

* `DGCategory.RightModule.app_shiftMap` puts `(-1)^{np}` on the shift by `n` of a degree-`p`
  homogeneous morphism. No morphism is shifted here: the composite is `h_f` followed by the
  comparison followed by identities, so `DGCategory.RightModule.shiftMap` does not occur at all.
  (It does occur in `DGCategory.RightModule.homShiftEquivGradedCohomology_comp`, the naturality
  of this link in the module variable, which is a different statement.)
* `DGCategory.ShiftAxiomBIso.symm_toShift_comp_left` puts `(-1)^{nk}` on the inverse
  identification commuted past a degree-`k` left factor. It does not occur either, and this is
  the one that has to be checked rather than assumed: `DGCategory.RightModule.app_homComp`
  evaluates the inner factor first and hands its *value* to
  `DGCategory.app_yonedaShiftHom`, so the comparison is never commuted past anything. The place
  where that sign does appear is `DGCategory.homComp_yonedaShiftHom_yonedaPostcomp`, which is
  not used here.
* `DGCategory.ShiftAxiomBIso.symm_toShift_d` puts `(-1)^n` on the inverse identification against
  the differential. This one genuinely appears, in
  `DGCategory.RightModule.symm_toShift_mem_gradedCocycles`, and it is not cancelled: it is
  *matched*. The differential of the shifted module carries `(-1)^n` too, by
  `DGCategory.RightModule.shift_d`, so the closedness to be proved is literally the assertion
  that `(-1)^n` times a differential vanishes, and that is what
  `DGCategory.ShiftAxiomBIso.symm_toShift_d` delivers from the closedness of the given cocycle.
  The two occurrences of the sign are the same sign on the two sides of one equation. It is this
  agreement, and not a vanishing exponent, that keeps the sign out of the value.

What does survive of the degree `n` of `f` is a degree *index* and not a sign: the value lands in
degree `0 + n` of the complex `Hom^•(K, Y)`, and
`DGCategory.RightModule.gradedCocyclesShiftEquiv'` is retained in the conclusion to carry it to
degree `n`. `CochainComplex.dgToShift_zero_symm` — the degree-zero case of the inverse
identification — is not used, and would not suffice: `DGCategory.app_yonedaShiftHom` is applied
at the general `n`.

## Implementation notes

Presenting `h_f ≫ σ_n` as a homotopy class is the usual obstacle course.
`CategoryTheory.Functor.commShiftIso` of the registered
`CochainComplex.yonedaOnK_commShift` is the canonical `DGCategory.DGFunctor.CommShiftBIso.kIso`
by definition, but only after a structure field is unfolded, so it is first rewritten by an
equation proved by reflexivity; `DGCategory.DGFunctor.CommShiftBIso.kIso_hom_app` then exposes
the two `eqToHom`s comparing the translations with the differential graded shift functors, which
are identities only up to unfolding a semireducible definition and so cannot be rewritten away.
They are absorbed by `DGCategory.RightModule.mk_eq_comp_two`, applied by `exact`, which also
identifies the resulting two-factor composite of homotopy classes with a single one — the
cocycles being hypotheses, so that composition in the homotopy category is never unfolded in the
goal.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
-/

@[expose] public section

open CategoryTheory

namespace DGCategory.RightModule

universe v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-- **The inverse identification of axiom (B) carries a cocycle to a cocycle.** A closed
degree-zero morphism `K ⟶ X[n]` is a degree-`0 + n` element of the complex `C(K, X)`, and it is
closed there.

This is the one place in the computation of the first link on `h_f ≫ σ_n` where a Koszul sign
occurs, and the two sides carry the same one: the differential of `M[n]` is `(-1)^n` times that
of `M` (`DGCategory.RightModule.shift_d`), so what has to be shown is that `(-1)^n` times a
differential vanishes, and `DGCategory.ShiftAxiomBIso.symm_toShift_d` says that this signed
expression is the inverse identification applied to the differential of the given cocycle, which
is zero. The sign is therefore never divided out, and never reaches the value. -/
theorem symm_toShift_mem_gradedCocycles (S : ShiftAxiomBIso C) (n : ℤ) (K X : C.Obj)
    (fc : C.Cocycle K ((S.shiftFunctor n).obj X)) :
    (S.toShift n K X 0).symm fc.1 ∈
      gradedCocycles (shift (yonedaRightModule C X) n) K 0 := by
  have hd := S.symm_toShift_d n (show (0 : ℤ) + 1 = 0 + 1 from rfl) fc.1
  rw [show C.d' (show (0 : ℤ) + 1 = 0 + 1 from rfl) fc.1 = 0 from fc.2, map_zero] at hd
  rw [mem_gradedCocycles, shift_d, yonedaRightModule_d]
  exact hd.symm

/-- **The evaluation at the identity of the comparison composed with a Yoneda image.** For a
degree-zero cocycle `fc : K ⟶ X[n]`, the composite `h_{fc}` followed by the comparison
`h_{X[n]} ⟶ (h_X)[n]`, evaluated at `id_K`, is the inverse identification of `fc` — the
degree-`0 + n` cochain `K ⟶ X` that `fc` is the reindexing of.

No sign appears, and not because a degree is zero: `DGCategory.RightModule.app_homComp`
evaluates `DGCategory.yonedaPostcomp` first and hands its value to
`DGCategory.app_yonedaShiftHom`, so the Koszul sign `(-1)^{nk}` of
`DGCategory.ShiftAxiomBIso.symm_toShift_comp_left` — the sign of commuting the comparison past a
degree-`k` left factor — is never incurred. Every step but the unit law is reflexivity. -/
theorem yonedaEval_homComp_yonedaShiftHom (S : ShiftAxiomBIso C) (n : ℤ) (K X : C.Obj)
    (fc : C.Cocycle K ((S.shiftFunctor n).obj X)) :
    yonedaEval (shift (yonedaRightModule C X) n) K 0
        (RightModule.homComp (add_zero (0 : ℤ)) (yonedaShiftHom S n X)
          (yonedaPostcomp C fc.1)) =
      (S.toShift n K X 0).symm fc.1 :=
  congrArg (fun a => (S.toShift n K X 0).symm a) (C.comp_id fc.1)

/-- **A two-factor composite of homotopy classes, identified by cocycles.** The two morphisms and
the one they compose to are variables, each with its representing cocycle a hypothesis, and the
two `eqToHom`s that the comparison of a translation with a differential graded shift functor
produces are written as identities. Applied by `exact`, which identifies them at default
transparency, where `rw` and `simp` cannot act on them at all. -/
private theorem mk_eq_comp_two {X Y Z : C.K} (u : X ⟶ Y) (v : Y ⟶ Z) (L : X ⟶ Z)
    (cu : C.Cocycle (X : C.Obj) (Y : C.Obj)) (cv : C.Cocycle (Y : C.Obj) (Z : C.Obj))
    (cL : C.Cocycle (X : C.Obj) (Z : C.Obj))
    (hu : u = Quotient.mk _ cu) (hv : v = Quotient.mk _ cv) (hL : L = Quotient.mk _ cL)
    (hc : cL = C.compCocycle cv cu) :
    u ≫ 𝟙 Y ≫ v ≫ 𝟙 Z = L := by
  subst hu hv hL hc
  rw [Category.id_comp, Category.comp_id]
  exact (mk_comp_mk cu cv).symm

end DGCategory.RightModule

namespace CochainComplex

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A]

open DGCategory DGCategory.RightModule

attribute [local implicit_reducible] DGCategory.K

/-- The canonical comparison of the differential graded Yoneda functor of the differential graded
category of complexes, as the `CategoryTheory.Functor.CommShift` datum registered by
`CochainComplex.yonedaOnK_commShift` reports it. Both sides are the same term; the equation lets
`DGCategory.DGFunctor.CommShiftBIso.kIso_hom_app` be used on the registered instance. -/
theorem commShiftIso_yonedaOnK (n : ℤ) :
    (yonedaDGFunctor (dgCategory A)).onK.commShiftIso n =
      (commShiftBIso_yonedaDGFunctor (dgShiftAxiomBIso A)).kIso n :=
  rfl

/-- **The first link of [Stacks, Tag 09LK] on the differential graded Yoneda image of a
morphism.** Let `f : K ⟶ Y⟦n⟧` be the homotopy class of a degree-zero cocycle `fc`, and let `c`
be the degree-`0 + n` cocycle of the complex `Hom^•(K, Y)` that `fc` is the reindexing of, as
`hc` says. Then the first link takes

`h_f ≫ σ_n : h_K ⟶ (h_Y)⟦n⟧`

to the degree-`n` cohomology class of `c`.

The value is the cocycle `c` itself, with no Koszul sign; the degree `n` of `f` survives only as
the index the reindexing `DGCategory.RightModule.gradedCocyclesShiftEquiv'` moves. The signs are
audited in the header of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.LinkOneSigmaEvaluation`. -/
theorem homShiftEquivEvaluationGradedCohomology_yonedaOnK_map_comp_commShiftIso
    (n : ℤ) (K : CochainComplex A ℤ) (y : (dgCategory A).K)
    (e : (endDGCategory (dgCategory A) K).Obj)
    (fc : (dgCategory A).Cocycle K
      (((dgShiftAxiomBIso A).shiftFunctor n).obj (y : (dgCategory A).Obj)))
    (c : gradedCocycles
      (shift (yonedaRightModule (dgCategory A) (y : (dgCategory A).Obj)) n) K 0)
    (hc : (dgShiftAxiomBIso A).toShift n K (y : (dgCategory A).Obj) 0 c.1 = fc.1) :
    homShiftEquivEvaluationGradedCohomology
        ((yonedaDGFunctor (dgCategory A)).onK.obj y) K e n
        ((yonedaDGFunctor (dgCategory A)).onK.map (Quotient.mk _ fc) ≫
          ((yonedaDGFunctor (dgCategory A)).onK.commShiftIso n).hom.app y) =
      Submodule.Quotient.mk (gradedCocyclesShiftEquiv'
        ((yonedaDGFunctor (dgCategory A)).onK.obj y) n K (zero_add n) c) := by
  have hmk : (yonedaDGFunctor (dgCategory A)).onK.map (Quotient.mk _ fc) ≫
      ((yonedaDGFunctor (dgCategory A)).onK.commShiftIso n).hom.app y =
      Quotient.mk _ ((rightModuleCategory.{v} (dgCategory A)).compCocycle
        (yonedaShiftCocycle (dgShiftAxiomBIso A) n (y : (dgCategory A).Obj))
        ((yonedaDGFunctor (dgCategory A)).mapCocycle fc)) := by
    rw [commShiftIso_yonedaOnK, DGFunctor.CommShiftBIso.kIso_hom_app, eqToHom_map]
    exact mk_eq_comp_two _ _ _ _ _ _ rfl rfl rfl rfl
  refine Eq.trans (congrArg (fun g => homShiftEquivEvaluationGradedCohomology
    ((yonedaDGFunctor (dgCategory A)).onK.obj y) K e n g) hmk) ?_
  refine Eq.trans (homShiftEquivEvaluationGradedCohomology_mk
    ((yonedaDGFunctor (dgCategory A)).onK.obj y) K e n
    ((rightModuleCategory.{v} (dgCategory A)).compCocycle
      (yonedaShiftCocycle (dgShiftAxiomBIso A) n (y : (dgCategory A).Obj))
      ((yonedaDGFunctor (dgCategory A)).mapCocycle fc))) ?_
  refine congrArg Submodule.Quotient.mk (congrArg _ (Subtype.ext ?_))
  refine Eq.trans (yonedaEval_homComp_yonedaShiftHom (dgShiftAxiomBIso A) n K
    (y : (dgCategory A).Obj) fc) ?_
  exact ((dgShiftAxiomBIso A).toShift n K (y : (dgCategory A).Obj) 0).symm_apply_eq.mpr
    hc.symm

end CochainComplex

end
