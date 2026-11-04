module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.LiftedQuotientAdicSystem

/-!
# The columns of the double tower of reductions

Let `X` be a locally Noetherian scheme and let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves. The
proof of [Stacks, Tag 088A] works with the double family

`(n, e) ↦ F_n / 𝒦 ᵉ⁺¹ F_n`

attached to an object `(F_n)` of `Coh(X, ℐ)`, and reads it in both directions: along `n` it is
the tower of `𝒦`-power reductions of `(F_n)`, and along `e` it is, for each fixed `n`, the
`𝒦`-completion of the coherent module `F_n`.

This file carries the second reading. Both statements rest on the same elementary fact, that the
`n`-th term of the `ℐ`-completion of a coherent module `M` *is* the quotient `M / ℐ ⁿ⁺¹ M`
([Stacks, Tag 0880]), recorded here as a natural isomorphism of functors rather than as the
pointwise equality `Stacks.Algebraization.completionFunctor_obj`.

## Main definitions

* `Stacks.Coherent.completionTermQuotientIso` — **the `n`-th term of the `ℐ`-completion is the
  `ℐ ⁿ⁺¹`-reduction**, naturally in the coherent module.
* `Stacks.Coherent.idealPowerQuotientAdicColumnIso` — **the column at a term**: the tower
  `e ↦ F_n / 𝒦 ᵉ⁺¹ F_n` is the `𝒦`-completion of `F_n`.

## Main results

* `Stacks.Coherent.completionProjection_comp_completionTermQuotientIso` and
  `Stacks.Coherent.idealPowerQuotientAdicProjection_comp_columnIso` — both comparisons are
  normalized by the projections, which is what forces their naturality and what the rest of the
  proof of Tag 088A uses them through.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-! ### The terms of a completion, as a functor -/

/-- **The completion projection is the quotient projection**, after the identification of the
`n`-th term of the completion with the `ℐ ⁿ⁺¹`-quotient. -/
public theorem completionProjection_comp_eqToHom (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    completionProjection X I M n ≫ eqToHom (completionFunctor_obj X I M n) =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) M.obj).ι := by
  refine Eq.trans (Category.assoc (obj := X.Modules)
    (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) M.obj).ι)
    (eqToHom (completionFunctor_obj X I M n).symm)
    (eqToHom (completionFunctor_obj X I M n))) ?_
  exact (congrArg (fun z => cokernel.π (C := X.Modules)
    (idealPowerMultiple I (n + 1) M.obj).ι ≫ z) (eqToHom_trans _ _)).trans
    (Category.comp_id _)

/-- **The `n`-th term of the `ℐ`-completion of a coherent module is its `ℐ ⁿ⁺¹`-reduction**,
naturally in the module.

Each component is the equality `Stacks.Algebraization.completionFunctor_obj`; naturality is the
compatibility of the completion maps with the quotient projections, which are epimorphisms. -/
public def completionTermQuotientIso (I : X.IdealSheafData) (n : ℕ) :
    completionFunctor X I ⋙ ObjectProperty.ι (IsCoherentAdicSystem I) ⋙
        (evaluation ℕᵒᵖ X.Modules).obj (op n) ≅
      coherentIdealPowerQuotientFunctor I (n + 1) ⋙
        ObjectProperty.ι (fun P : _root_.SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent) :=
  NatIso.ofComponents (fun M => eqToIso (completionFunctor_obj X I M n)) (by
    intro M N f
    refine (Stacks.Algebraization.epi_completionProjection X I M n).left_cancellation
      _ _ ?_
    have hM := completionProjection_comp_eqToHom X I M n
    have hN := completionProjection_comp_eqToHom X I N n
    have hleft : completionProjection X I M n ≫
        (((completionFunctor X I).map f).hom.app (op n) ≫
          eqToHom (completionFunctor_obj X I N n)) =
        f.hom ≫ cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) N.obj).ι :=
      (Category.assoc (obj := X.Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ eqToHom (completionFunctor_obj X I N n))
            (completionFunctor_map_quotient X I f n)).trans
          ((Category.assoc (obj := X.Modules) _ _ _).trans
            (congrArg (fun z => f.hom ≫ z) hN)))
    have hright : completionProjection X I M n ≫
        (eqToHom (completionFunctor_obj X I M n) ≫
          idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl f.hom) =
        f.hom ≫ cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) N.obj).ι :=
      (Category.assoc (obj := X.Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl f.hom)
            hM).trans
          (idealPowerQuotientMap_π I I (n + 1) (n + 1) le_rfl f.hom))
    exact hleft.trans hright.symm)

/-- **The comparison is normalized by the completion projection.** -/
public theorem completionProjection_comp_completionTermQuotientIso (I : X.IdealSheafData)
    (n : ℕ) (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    completionProjection X I M n ≫ (completionTermQuotientIso I n).hom.app M =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) M.obj).ι :=
  completionProjection_comp_eqToHom X I M n

/-! ### The column of the double tower at a term -/

variable (I K : X.IdealSheafData)

/-- **The column of the tower of reductions at a term is a completion.** For a coherent adic
system `(F_m)` along `ℐ` and a fixed `n`, the tower `e ↦ F_n / 𝒦 ᵉ⁺¹ F_n` obtained by evaluating
the tower of `𝒦`-power reductions at `(F_m)` and then at the index `n` is the `𝒦`-completion of
the coherent module `F_n`.

Each term is `Stacks.Coherent.completionTermQuotientIso` read backwards; naturality is forced by
the normalization of both sides by the quotient projections. -/
public def idealPowerQuotientAdicColumnIso (F : CoherentAdicSystems I) (n : ℕ) :
    idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj F ⋙
        ObjectProperty.ι (IsCoherentAdicSystem I) ⋙
          (evaluation ℕᵒᵖ X.Modules).obj (op n) ≅
      ((completionFunctor X K).obj (((coherentAdicTerms I).obj F).obj (op n))).obj := by
  set A := idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj F ⋙
    ObjectProperty.ι (IsCoherentAdicSystem I) ⋙
      (evaluation ℕᵒᵖ X.Modules).obj (op n) with hA
  set Mn : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
    ((coherentAdicTerms I).obj F).obj (op n) with hMn
  set B := ((completionFunctor X K).obj Mn).obj with hB
  set r : ∀ e : ℕ, A.obj (op e) ⟶ B.obj (op e) := fun e =>
    ((completionTermQuotientIso K e).app Mn).inv with hr
  have hback : ∀ e : ℕ,
      cokernel.π (C := X.Modules) (idealPowerMultiple K (e + 1) Mn.obj).ι ≫ r e =
        completionProjection X K Mn e := by
    intro e
    refine Eq.trans (congrArg (fun z => z ≫ r e)
      (completionProjection_comp_completionTermQuotientIso K e Mn).symm) ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg (fun z => completionProjection X K Mn e ≫ z)
      ((completionTermQuotientIso K e).app Mn).hom_inv_id) ?_
    exact Category.comp_id _
  have hnat : ∀ e : ℕ, A.map (homOfLE (Nat.le_add_right e 1)).op ≫ r e =
      r (e + 1) ≫ B.map (homOfLE (Nat.le_add_right e 1)).op := by
    intro e
    refine (epi_cokernel_π_submodule_ι
      (idealPowerMultiple K (e + 1 + 1) Mn.obj)).left_cancellation _ _ ?_
    have hdrop : cokernel.π (C := X.Modules)
          (idealPowerMultiple K (e + 1 + 1) Mn.obj).ι ≫
        A.map (homOfLE (Nat.le_add_right e 1)).op =
        cokernel.π (C := X.Modules) (idealPowerMultiple K (e + 1) Mn.obj).ι := by
      have := F.property.isQuasicoherent n
      refine Eq.trans (congrArg (fun φ : idealPowerQuotientAdicFunctor I K (e + 1 + 1) ⟶
          idealPowerQuotientAdicFunctor I K (e + 1) =>
        cokernel.π (C := X.Modules) (idealPowerMultiple K (e + 1 + 1) Mn.obj).ι ≫
          (φ.app F).hom.app (op n)) (idealPowerQuotientAdicTower_map_succ I K e)) ?_
      exact idealPowerQuotientDrop'_π K (Nat.le_succ (e + 1)) (F.obj.obj (op n))
    have hleft : cokernel.π (C := X.Modules)
          (idealPowerMultiple K (e + 1 + 1) Mn.obj).ι ≫
        (A.map (homOfLE (Nat.le_add_right e 1)).op ≫ r e) =
        completionProjection X K Mn e :=
      (Category.assoc (obj := X.Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ r e) hdrop).trans (hback e))
    have hright : cokernel.π (C := X.Modules)
          (idealPowerMultiple K (e + 1 + 1) Mn.obj).ι ≫
        (r (e + 1) ≫ B.map (homOfLE (Nat.le_add_right e 1)).op) =
        completionProjection X K Mn e :=
      (Category.assoc (obj := X.Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ B.map (homOfLE (Nat.le_add_right e 1)).op)
            (hback (e + 1))).trans
          (completionProjection_transition X K Mn e))
    exact hleft.trans hright.symm
  exact NatIso.ofComponents (fun e => ((completionTermQuotientIso K e.unop).app Mn).symm)
    (fun g => (NatTrans.ofOpSequence (F := A) (G := B) r hnat).naturality g)

/-- The components of the column comparison are the termwise comparisons, read backwards. -/
public theorem idealPowerQuotientAdicColumnIso_hom_app (F : CoherentAdicSystems I) (n e : ℕ) :
    (idealPowerQuotientAdicColumnIso I K F n).hom.app (op e) =
      (completionTermQuotientIso K e).inv.app
        (((coherentAdicTerms I).obj F).obj (op n)) := rfl

/-- **The column comparisons at two consecutive indices are compatible with the transitions.**
On the left the transition of the coherent adic system, divided by `𝒦 ᵉ⁺¹`; on the right the
`𝒦`-completion of the same transition read on the terms. -/
public theorem idealPowerQuotientAdicColumnIso_hom_naturality (F : CoherentAdicSystems I)
    (n e : ℕ) :
    idealPowerQuotientMap K K (e + 1) (e + 1) le_rfl
        (F.obj.map (homOfLE (Nat.le_add_right n 1)).op) ≫
      (idealPowerQuotientAdicColumnIso I K F n).hom.app (op e) =
    (idealPowerQuotientAdicColumnIso I K F (n + 1)).hom.app (op e) ≫
      ((completionFunctor X K).map (((coherentAdicTerms I).obj F).map
        (homOfLE (Nat.le_add_right n 1)).op)).hom.app (op e) := by
  rw [idealPowerQuotientAdicColumnIso_hom_app, idealPowerQuotientAdicColumnIso_hom_app]
  exact (completionTermQuotientIso K e).inv.naturality
    (((coherentAdicTerms I).obj F).map (homOfLE (Nat.le_add_right n 1)).op)

/-- **The column comparison is normalized by the projection onto the reduction.** -/
public theorem idealPowerQuotientAdicProjection_comp_columnIso (F : CoherentAdicSystems I)
    (n e : ℕ) :
    ((idealPowerQuotientAdicProjection I K (e + 1)).app F).hom.app (op n) ≫
        (idealPowerQuotientAdicColumnIso I K F n).hom.app (op e) =
      completionProjection X K (((coherentAdicTerms I).obj F).obj (op n)) e := by
  rw [idealPowerQuotientAdicColumnIso_hom_app]
  refine Eq.trans (congrArg (· ≫ _) (completionProjection_comp_completionTermQuotientIso K e
    (((coherentAdicTerms I).obj F).obj (op n))).symm) ?_
  exact (Category.assoc (obj := X.Modules) _ _ _).trans
    ((congrArg (_ ≫ ·) ((completionTermQuotientIso K e).app _).hom_inv_id).trans
      (Category.comp_id _))

end Stacks.Coherent

end
