module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smoothing.BaseChangeOfPresentation
public import StacksFrontier.RingTheory.Smoothing.SpreadingOutResolutions
public import StacksFrontier.RingTheory.Smoothing.StandardSmoothPresentation
public import StacksFrontier.RingTheory.Smoothing.StandardSmoothRetract
public import StacksFrontier.RingTheory.Smoothing.DelocalizingSmoothFactorization.ClearingDenominators

/-!
# Delocalizing a smooth factorization over a localized base

Let `R → A → Λ` be ring maps with `A` of finite presentation over `R`, let `S ⊆ R` be a
multiplicative set, and suppose the localized map `S⁻¹A → S⁻¹Λ` factors through an algebra `B'`
that is smooth over `S⁻¹R`. Then the factorization can be pushed back down to `R`: there is a
factorization `A → B → Λ` in which some element of `S` becomes an elementary standard element
of `B` over `R` in the sense of Stacks 07C7.

The construction follows the source. Replacing `B'` by a standard smooth extension of it with a
retraction, one presents the extension as `S⁻¹R[x_1, …, x_{n + m}]/(f_1, …, f_c)` with the
images of the generators of `A` among the first `n` variables and the principal `c × c` Jacobian
minor invertible. Rescaling the remaining variables by elements of `S` makes each of them the
image of an element of `Λ`, and clearing denominators in the relation witnessing invertibility
of the Jacobian minor, in the relations of `A`, and in the vanishing of the `f_j` on `Λ`
produces polynomials over `R` and finitely many elements of `S`. The ring

`B = R[x_1, …, x_{n + m}]/(s'_1 f_1, …, s'_c f_c, g_1, …, g_t)`

then receives `A`, maps to `Λ`, and the product of all the collected elements of `S` is
elementary standard in `B` over `R`.

## Main results

* `Stacks.Smoothing.exists_factorization_isElementaryStandard`: the lemma above, Stacks 07F4.

## Implementation notes

The three localizations are the canonical models `Localization S`, `Localization (S.map
(algebraMap R A))` and `Localization (S.map (algebraMap R Λ))`; the algebra structures between
them that Mathlib does not already provide are taken as hypotheses, pinned down by the
accompanying scalar towers.

The first step of the source proof is Stacks 07CH, which replaces a smooth algebra by a standard
smooth extension of it admitting a retraction. It is supplied by
`Stacks.Smoothing.exists_smooth_isStandardSmooth_retraction`, specialised to the base
`Localization S`.

The explicit presentation interface used here is the one of
`standardSmooth_presentation_with_prescribed_generators` (Stacks 07EY), reached from Mathlib's
`Algebra.IsStandardSmooth` through
`Stacks.Smoothing.isStandardSmoothRingMap_of_isStandardSmooth`.

## References

* [Stacks Project, Tag 07F4](https://stacks.math.columbia.edu/tag/07F4)
* [Stacks Project, Tag 07C7](https://stacks.math.columbia.edu/tag/07C7)
* [Stacks Project, Tag 07CH](https://stacks.math.columbia.edu/tag/07CH)
* [Stacks Project, Tag 07EY](https://stacks.math.columbia.edu/tag/07EY)
-/

@[expose] public section

namespace Stacks.Smoothing

universe u v w u'

variable (R : Type u) (A : Type v) (Λ : Type w)
  [CommRing R] [CommRing A] [CommRing Λ]
  [Algebra R A] [Algebra A Λ] [Algebra R Λ] [IsScalarTower R A Λ]
  [Algebra.FinitePresentation R A]

/-- **Stacks 07F4.** Let `R → A → Λ` be ring maps with `A` of finite presentation over `R` and
let `S ⊆ R` be a multiplicative set. Given a factorization `S⁻¹A → B' → S⁻¹Λ` with `B'` smooth
over `S⁻¹R`, there is a factorization `A → B → Λ` of `A → Λ` by `R`-algebras in which some
`s ∈ S` maps to an elementary standard element of `B` over `R`.

Step 1 of the source proof, the reduction to a standard smooth `B'`, is Stacks 07CH; it is
supplied by `Stacks.Smoothing.exists_smooth_isStandardSmooth_retraction`. -/
@[stacks 07F4]
theorem exists_factorization_isElementaryStandard
    (S : Submonoid R)
    [Algebra (Localization S) (Localization (S.map (algebraMap R A)))]
    [IsScalarTower R (Localization S) (Localization (S.map (algebraMap R A)))]
    [Algebra (Localization S) (Localization (S.map (algebraMap R Λ)))]
    [Algebra (Localization (S.map (algebraMap R A)))
      (Localization (S.map (algebraMap R Λ)))]
    [Algebra A (Localization (S.map (algebraMap R Λ)))]
    [IsScalarTower A Λ (Localization (S.map (algebraMap R Λ)))]
    (h : ∃ (B' : Type u') (_ : CommRing B')
      (_ : Algebra (Localization (S.map (algebraMap R A))) B')
      (_ : Algebra (Localization S) B')
      (_ : Algebra B' (Localization (S.map (algebraMap R Λ))))
      (_ : Algebra A B')
      (_ : IsScalarTower A (Localization (S.map (algebraMap R A))) B')
      (_ : IsScalarTower (Localization S)
        (Localization (S.map (algebraMap R A))) B')
      (_ : IsScalarTower (Localization (S.map (algebraMap R A))) B'
        (Localization (S.map (algebraMap R Λ))))
      (_ : IsScalarTower A B' (Localization (S.map (algebraMap R Λ)))),
      Algebra.Smooth (Localization S) B') :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra B Λ)
      (_ : Algebra R B),
      IsScalarTower R A B ∧ IsScalarTower A B Λ ∧ IsScalarTower R B Λ ∧
        ∃ s : S, IsElementaryStandard (R := R) (algebraMap R B s) := by
  classical
  have hCH : ∀ (D : Type u') (_ : CommRing D) (_ : Algebra (Localization S) D),
      Algebra.Smooth (Localization S) D →
        ∃ (C : Type u') (_ : CommRing C) (_ : Algebra D C)
          (_ : Algebra (Localization S) C) (_ : IsScalarTower (Localization S) D C),
          Algebra.IsStandardSmooth (Localization S) C ∧
            ∃ r : C →+* D, r.comp (algebraMap D C) = RingHom.id D := by
    intro D _ _ _
    obtain ⟨C, hCcomm, hDC, hLocR_C, hTower, -, hStd, r, hr⟩ :=
      exists_smooth_isStandardSmooth_retraction (Localization S) D
    exact ⟨C, hCcomm, hDC, hLocR_C, hTower, hStd, r, hr⟩
  obtain ⟨B', hB'comm, hLocA_B', hLocR_B', hB'_LocΛ, hA_B',
      hTowerA, hTowerR, hTowerLocABLocΛ, hTowerABLocΛ, hSmooth⟩ := h
  let : CommRing B' := hB'comm
  let : Algebra (Localization (S.map (algebraMap R A))) B' := hLocA_B'
  let : Algebra (Localization S) B' := hLocR_B'
  let : Algebra B' (Localization (S.map (algebraMap R Λ))) := hB'_LocΛ
  let : Algebra A B' := hA_B'
  let : IsScalarTower A (Localization (S.map (algebraMap R A))) B' := hTowerA
  let : IsScalarTower (Localization S)
      (Localization (S.map (algebraMap R A))) B' := hTowerR
  let : IsScalarTower (Localization (S.map (algebraMap R A))) B'
      (Localization (S.map (algebraMap R Λ))) := hTowerLocABLocΛ
  let : IsScalarTower A B' (Localization (S.map (algebraMap R Λ))) := hTowerABLocΛ
  obtain ⟨C, hCcomm, hB'_C, hLocR_C, hTowerLocR_B'_C,
      hSmoothC, ⟨retract, hRetract⟩⟩ :=
    hCH B' hB'comm hLocR_B' hSmooth
  let : CommRing C := hCcomm
  let : Algebra B' C := hB'_C
  let : Algebra (Localization S) C := hLocR_C
  let : Algebra R C := Algebra.compHom C (algebraMap R (Localization S))
  let : IsScalarTower R (Localization S) C :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := Localization S) (A := C) (fun _ => rfl)
  let : IsScalarTower (Localization S) B' C := hTowerLocR_B'_C
  have hCstandard : IsStandardSmoothRingMap (Localization S) C :=
    isStandardSmoothRingMap_of_isStandardSmooth (Localization S) C hSmoothC
  let P := Algebra.Presentation.ofFinitePresentation R A
  let aToC : A →+* C := (algebraMap B' C).comp (algebraMap A B')
  let vC : Fin (Algebra.Presentation.ofFinitePresentationVars R A) → C :=
    fun i => aToC (P.toGenerators.val i)
  let E : Finset C := Finset.univ.image vC
  obtain ⟨m, c, hEc, hcnm, f, π, ⟨hπsurj, hπker⟩, hπdet, hEimages⟩ :=
    standardSmooth_presentation_with_prescribed_generators
      (Localization S) C hCstandard E E.card rfl
  -- Make a presentation in which every chosen generator of `A` has its own
  -- variable.  The extra equations are linear, so they extend the Jacobian
  -- block by an identity matrix even when several generators have the same
  -- image in `C`.
  let nA := Algebra.Presentation.ofFinitePresentationVars R A
  let nC := E.card + m
  let rC := nC - c
  have hcr : c + rC = nC := Nat.add_sub_of_le hcnm
  let eOld : Fin nC ≃ Fin c ⊕ Fin rC :=
    ((finSumFinEquiv : Fin c ⊕ Fin rC ≃ Fin (c + rC)).trans
      (finCongr hcr)).symm
  have heOld_inl (j : Fin c) : eOld (Fin.castLE hcnm j) = Sum.inl j := by
    change (finSumFinEquiv : Fin c ⊕ Fin rC ≃ Fin (c + rC)).symm
      ((finCongr hcr).symm (Fin.castLE hcnm j)) = Sum.inl j
    have hcast : (finCongr hcr).symm (Fin.castLE hcnm j) = Fin.castAdd rC j := Fin.ext rfl
    rw [hcast, finSumFinEquiv_symm_apply_castAdd]
  let gC : Algebra.Generators (Localization S) C (Fin nC) :=
    Algebra.Generators.ofAlgHom π hπsurj
  have hπaeval : MvPolynomial.aeval gC.val = π := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [gC, Algebra.Generators.ofAlgHom]
  let PC : Algebra.Presentation (Localization S) C (Fin nC) (Fin c) := {
    toGenerators := gC
    relation := f
    span_range_relation_eq_ker := by
      rw [Algebra.Generators.ker_eq_ker_aeval_val, hπaeval]
      exact hπker.symm }
  let gA : Algebra.Generators C C (Fin nA) := {
    val := vC
    σ' := fun x => MvPolynomial.C x
    aeval_val_σ' := by intro x; simp }
  let QA : Algebra.Presentation C C (Fin nA) (Fin nA) := {
    toGenerators := gA
    relation i := MvPolynomial.X i - MvPolynomial.C (vC i)
    span_range_relation_eq_ker := by
      rw [Algebra.Generators.ker_eq_ker_aeval_val]
      exact (kernel_aeval_constants vC).symm }
  have : IsScalarTower (Localization S) C C := inferInstance
  let Pcomp := QA.comp PC
  let ecomp : (Fin c ⊕ Fin nA) ⊕ Fin rC ≃ Fin nA ⊕ Fin nC :=
    (Equiv.sumCongr (Equiv.sumComm (Fin c) (Fin nA)) (Equiv.refl (Fin rC))).trans
      (Equiv.sumAssoc (Fin nA) (Fin c) (Fin rC)) |>.trans
      (Equiv.sumCongr (Equiv.refl (Fin nA)) eOld.symm)
  let Pext := Pcomp.reindex ecomp (Equiv.sumComm (Fin c) (Fin nA))
  let nB := c + nA + rC
  let eFin : (Fin c ⊕ Fin nA) ⊕ Fin rC ≃ Fin nB :=
    (Equiv.sumCongr (finSumFinEquiv : Fin c ⊕ Fin nA ≃ Fin (c + nA))
      (Equiv.refl (Fin rC))).trans
      (finSumFinEquiv : Fin (c + nA) ⊕ Fin rC ≃ Fin ((c + nA) + rC))
  let eRel : Fin c ⊕ Fin nA ≃ Fin (c + nA) := finSumFinEquiv
  let PextFin := Pext.reindex eFin.symm eRel.symm
  let QApre : Algebra.PreSubmersivePresentation C C (Fin nA) (Fin nA) := {
    toPresentation := QA
    map := id
    map_inj := fun _ _ h => h }
  let PCpre : Algebra.PreSubmersivePresentation (Localization S) C (Fin nC) (Fin c) := {
    toPresentation := PC
    map := Fin.castLE hcnm
    map_inj := Fin.castLE_injective hcnm }
  let PcompPre := QApre.comp PCpre
  let PextPre := (PcompPre.reindex ecomp (Equiv.sumComm (Fin c) (Fin nA))).reindex
    eFin.symm eRel.symm
  have hPextPre : PextPre.toPresentation = PextFin := rfl
  have hPextMap : PextPre.map = Fin.castLE (Nat.le_add_right (c + nA) rC) := by
    funext j
    by_cases hj : j.1 < c
    · have hj' : j = Fin.castAdd nA ⟨j.1, hj⟩ := by
        ext
        simp
      have hOldJ : eOld (⟨j.1, by omega⟩ : Fin nC) = Sum.inl ⟨j.1, hj⟩ := by
        simpa using heOld_inl (⟨j.1, hj⟩ : Fin c)
      have hsum : (finSumFinEquiv : Fin c ⊕ Fin nA ≃ Fin (c + nA)).symm j =
          Sum.inl ⟨j.1, hj⟩ := by
        apply (finSumFinEquiv : Fin c ⊕ Fin nA ≃ Fin (c + nA)).injective
        rw [Equiv.apply_symm_apply]
        simp
      simp [PextPre, PcompPre, QApre, PCpre, ecomp, eFin, eRel, hsum, hOldJ,
        Algebra.PreSubmersivePresentation.reindex,
        Algebra.PreSubmersivePresentation.comp, Equiv.sumComm_apply]
      simp [Fin.ext_iff, finSumFinEquiv]
    · have hjn : j.1 - c < nA := by omega
      have hj' : j = Fin.natAdd c ⟨j.1 - c, hjn⟩ := by
        ext
        simp
        omega
      have hsum : (finSumFinEquiv : Fin c ⊕ Fin nA ≃ Fin (c + nA)).symm j =
          Sum.inr ⟨j.1 - c, hjn⟩ := by
        apply (finSumFinEquiv : Fin c ⊕ Fin nA ≃ Fin (c + nA)).injective
        rw [Equiv.apply_symm_apply]
        simpa using hj'
      simp [PextPre, PcompPre, QApre, PCpre, ecomp, eFin, eRel, hsum,
        Algebra.PreSubmersivePresentation.reindex,
        Algebra.PreSubmersivePresentation.comp, Equiv.sumComm_apply]
      simp [Fin.ext_iff, finSumFinEquiv]
      omega
  have hqaMap : QApre.map = Fin.castLE (Nat.le_refl nA) := by
    funext i
    simp [QApre]
  have hQAjac : QApre.jacobian = 1 := by
    rw [preSub_jacobian_eq_aeval_jacobianDet (Nat.le_refl nA) QApre hqaMap]
    have hmat : (fun i j : Fin nA =>
        MvPolynomial.pderiv (Fin.castLE (Nat.le_refl nA) i) (QA.relation j)) =
          (1 : Matrix (Fin nA) (Fin nA) (MvPolynomial (Fin nA) C)) := by
      change (fun i j : Fin nA => MvPolynomial.pderiv i (QA.relation j)) =
        (1 : Matrix (Fin nA) (Fin nA) (MvPolynomial (Fin nA) C))
      apply funext
      intro i
      apply funext
      intro j
      by_cases hij : i = j
      · subst j
        simp [QA, MvPolynomial.pderiv_X]
      · have hji : j ≠ i := fun h => hij h.symm
        simp [QA, hij, hji, MvPolynomial.pderiv_X]
    rw [jacobianDet, hmat]
    simp
  have hPCjac : PCpre.jacobian = π (jacobianDet hcnm f) := by
    rw [preSub_jacobian_eq_aeval_jacobianDet hcnm PCpre rfl]
    simp [PCpre, PC, hπaeval]
  have hPcompJac : PcompPre.jacobian = PCpre.jacobian • QApre.jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
  have hPextJac : PextPre.jacobian = PcompPre.jacobian := by
    dsimp [PextPre]
    rw [Algebra.PreSubmersivePresentation.jacobian_reindex,
      Algebra.PreSubmersivePresentation.jacobian_reindex]
  have hPextJacUnit : IsUnit PextPre.jacobian := by
    rw [hPextJac, hPcompJac, hPCjac, hQAjac, Algebra.smul_def]
    simpa using hπdet
  let Λₛ := Localization (S.map (algebraMap R Λ))
  let L := Localization (S.map (algebraMap R A))
  have hTowerAΛ : IsScalarTower A Λ (Localization (S.map (algebraMap R Λ))) :=
    inferInstance
  have hTowerAB_map (a : A) :
      algebraMap B' (Localization (S.map (algebraMap R Λ))) (algebraMap A B' a) =
        algebraMap Λ (Localization (S.map (algebraMap R Λ))) (algebraMap A Λ a) := by
    have hAB := hTowerABLocΛ.smul_assoc a (1 : B')
      (1 : Localization (S.map (algebraMap R Λ)))
    have hAΛ := hTowerAΛ.smul_assoc a (1 : Λ)
      (1 : Localization (S.map (algebraMap R Λ)))
    have hAB' : algebraMap B' (Localization (S.map (algebraMap R Λ)))
        (algebraMap A B' a) = a • (1 : Localization (S.map (algebraMap R Λ))) := by
      simpa [Algebra.smul_def] using hAB
    have hAΛ' : algebraMap Λ (Localization (S.map (algebraMap R Λ)))
        (algebraMap A Λ a) = a • (1 : Localization (S.map (algebraMap R Λ))) := by
      simpa [Algebra.smul_def] using hAΛ
    exact hAB'.trans hAΛ'.symm
  let : IsScalarTower A B' Λₛ := hTowerABLocΛ
  let : Algebra (Localization S) Λₛ :=
    Algebra.compHom Λₛ (algebraMap (Localization S) L)
  let : IsScalarTower (Localization S) L Λₛ :=
    IsScalarTower.of_algebraMap_eq (R := Localization S) (S := L) (A := Λₛ) (fun _ => rfl)
  let : IsScalarTower (Localization S) B' Λₛ :=
    IsScalarTower.of_algebraMap_eq (R := Localization S) (S := B') (A := Λₛ) fun r => by
      calc
        algebraMap (Localization S) Λₛ r =
            algebraMap L Λₛ (algebraMap (Localization S) L r) :=
          IsScalarTower.algebraMap_apply (Localization S) L Λₛ r
        _ = algebraMap B' Λₛ
              (algebraMap L B' (algebraMap (Localization S) L r)) :=
          IsScalarTower.algebraMap_apply L B' Λₛ _
        _ = algebraMap B' Λₛ (algebraMap (Localization S) B' r) := by
          rw [IsScalarTower.algebraMap_apply (Localization S) L B' r]
  let : Algebra R B' := Algebra.compHom B' (algebraMap R A)
  let : IsScalarTower R A B' :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := A) (A := B') (fun _ => rfl)
  let : IsScalarTower R (Localization S) B' :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := Localization S) (A := B') fun r => by
      calc
        algebraMap R B' r = algebraMap A B' (algebraMap R A r) := rfl
        _ = algebraMap L B'
              (algebraMap A L (algebraMap R A r)) :=
          IsScalarTower.algebraMap_apply A L B' _
        _ = algebraMap L B' (algebraMap R L r) := by
          rw [IsScalarTower.algebraMap_apply R A L r]
        _ = algebraMap L B'
              (algebraMap (Localization S) L (algebraMap R (Localization S) r)) := by
          rw [IsScalarTower.algebraMap_apply R (Localization S) L r]
        _ = algebraMap (Localization S) B' (algebraMap R (Localization S) r) := by
          rw [← IsScalarTower.algebraMap_apply (Localization S) L B'
            (algebraMap R (Localization S) r)]
  let : IsScalarTower R (Localization S) Λₛ :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := Localization S) (A := Λₛ) fun r => by
      calc
        algebraMap R Λₛ r = algebraMap Λ Λₛ (algebraMap R Λ r) :=
          (IsScalarTower.algebraMap_apply R Λ Λₛ r).symm
        _ = algebraMap B' Λₛ (algebraMap A B' (algebraMap R A r)) := by
          rw [hTowerAB_map, IsScalarTower.algebraMap_apply R A Λ r]
        _ = algebraMap B' Λₛ
              (algebraMap (Localization S) B'
                (algebraMap R (Localization S) r)) := by
          congr 1
          calc
            algebraMap A B' (algebraMap R A r) = algebraMap R B' r := rfl
            _ = algebraMap (Localization S) B'
                  (algebraMap R (Localization S) r) :=
              IsScalarTower.algebraMap_apply R (Localization S) B' r
        _ = algebraMap (Localization S) Λₛ
              (algebraMap R (Localization S) r) :=
          (IsScalarTower.algebraMap_apply (Localization S) B' Λₛ
            (algebraMap R (Localization S) r)).symm
  let cToΛ : C →+* Λₛ := (algebraMap B' Λₛ).comp retract
  have hcToΛ_retract (y : B') : cToΛ (algebraMap B' C y) = algebraMap B' Λₛ y := by
    have hh := congrArg (fun f : B' →+* B' => f y) hRetract
    simpa [cToΛ] using congrArg (algebraMap B' Λₛ) hh
  have hcToΛ_base (r : Localization S) :
      cToΛ (algebraMap (Localization S) C r) = algebraMap (Localization S) Λₛ r := by
    rw [IsScalarTower.algebraMap_apply (Localization S) B' C r, hcToΛ_retract,
      ← IsScalarTower.algebraMap_apply (Localization S) B' Λₛ r]
  have hcToΛ_A (a : A) : cToΛ (aToC a) =
      algebraMap Λ Λₛ (algebraMap A Λ a) :=
    (hcToΛ_retract (algebraMap A B' a)).trans (hTowerAB_map a)
  choose denC liftC hliftC using fun i : Fin nC =>
    exists_localization_multiple_target (Λ := Λ) S (cToΛ (gC.val i))
  let oldVarB (i : Fin nC) : Fin nB :=
    match eOld i with
    | Sum.inl j => eFin (Sum.inl (Sum.inl j))
    | Sum.inr k => eFin (Sum.inr k)
  have hbaseExt (i : Fin nC) :
      PextFin.toGenerators.val (oldVarB i) = gC.val i := by
    rcases he : eOld i with j | k
    · have hi : i = eOld.symm (Sum.inl j) := by
        simpa using congrArg eOld.symm he
      have hidx : ecomp (Sum.inl (Sum.inl j)) = Sum.inr i := by
        simp [ecomp, eOld, hi]
      simp only [oldVarB, he]
      change Pcomp.toGenerators.val
        (ecomp (eFin.symm (eFin (Sum.inl (Sum.inl j))))) = gC.val i
      rw [eFin.symm_apply_apply, hidx]
      simp [Pcomp, Algebra.Presentation.comp, PC]
    · have hi : i = eOld.symm (Sum.inr k) := by
        simpa using congrArg eOld.symm he
      have hidx : ecomp (Sum.inr k) = Sum.inr i := by
        simp [ecomp, eOld, hi]
      simp only [oldVarB, he]
      change Pcomp.toGenerators.val
        (ecomp (eFin.symm (eFin (Sum.inr k)))) = gC.val i
      rw [eFin.symm_apply_apply, hidx]
      simp [Pcomp, Algebra.Presentation.comp, PC]
  have hsourceExt (i : Fin nA) :
    PextFin.toGenerators.val (Fin.castAdd rC (Fin.natAdd c i)) = vC i := by
    have hidx : ecomp (eFin.symm (Fin.castAdd rC (Fin.natAdd c i))) = Sum.inl i := by
      have hleft : eFin (Sum.inl (Sum.inr i)) = Fin.castAdd rC (Fin.natAdd c i) := by
        rfl
      have hright : ecomp (Sum.inl (Sum.inr i)) = Sum.inl i := by
        simp [ecomp]
      calc
        ecomp (eFin.symm (Fin.castAdd rC (Fin.natAdd c i))) =
            ecomp (Sum.inl (Sum.inr i)) := by rw [← hleft, eFin.symm_apply_apply]
        _ = Sum.inl i := hright
    change Pcomp.toGenerators.val
      (ecomp (eFin.symm (Fin.castAdd rC (Fin.natAdd c i)))) = vC i
    rw [hidx]
    simp [Pcomp, Algebra.Presentation.comp, QA, gA]
  let denB : Fin nB → S := fun i =>
    match eFin.symm i with
    | Sum.inl (Sum.inl j) => denC (eOld.symm (Sum.inl j))
    | Sum.inl (Sum.inr _) => 1
    | Sum.inr k => denC (eOld.symm (Sum.inr k))
  let liftB : Fin nB → Λ := fun i =>
    match eFin.symm i with
    | Sum.inl (Sum.inl j) => liftC (eOld.symm (Sum.inl j))
    | Sum.inl (Sum.inr j) => algebraMap A Λ (P.toGenerators.val j)
    | Sum.inr k => liftC (eOld.symm (Sum.inr k))
  have hliftB (i : Fin nB) :
      algebraMap Λ Λₛ (liftB i) =
        algebraMap R Λₛ (denB i : R) * cToΛ (PextFin.toGenerators.val i) := by
    have hi := eFin.apply_symm_apply i
    rcases hdec : eFin.symm i with (j | j) | k
    · have hi' : i = eFin (Sum.inl (Sum.inl j)) := by simpa [hdec] using hi.symm
      rw [hi']
      simp only [denB, liftB, eFin.symm_apply_apply]
      have hv := hbaseExt (eOld.symm (Sum.inl j))
      have hcoord : oldVarB (eOld.symm (Sum.inl j)) = eFin (Sum.inl (Sum.inl j)) := by
        simp [oldVarB]
      rw [← hcoord, hv, hliftC]
    · have hi' : i = eFin (Sum.inl (Sum.inr j)) := by simpa [hdec] using hi.symm
      rw [hi']
      simp only [denB, liftB, eFin.symm_apply_apply]
      have hcoord : eFin (Sum.inl (Sum.inr j)) =
          Fin.castAdd rC (Fin.natAdd c j) := rfl
      rw [hcoord, hsourceExt, hcToΛ_A]
      simp
    · have hi' : i = eFin (Sum.inr k) := by simpa [hdec] using hi.symm
      rw [hi']
      simp only [denB, liftB, eFin.symm_apply_apply]
      have hv := hbaseExt (eOld.symm (Sum.inr k))
      have hcoord : oldVarB (eOld.symm (Sum.inr k)) = eFin (Sum.inr k) := by
        simp [oldVarB]
      rw [← hcoord, hv, hliftC]
  let sourceVar : Fin nA → Fin nB := fun i =>
    Fin.castAdd rC (Fin.natAdd c i)
  have hPzero (j : Fin (Algebra.Presentation.ofFinitePresentationRels R A)) :
      MvPolynomial.aeval P.toGenerators.val (P.relation j) = 0 := by
    apply RingHom.mem_ker.mp
    rw [← P.toGenerators.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hsourceRel (j : Fin (Algebra.Presentation.ofFinitePresentationRels R A)) :
      MvPolynomial.aeval (PextFin.toGenerators.val ∘ sourceVar) (P.relation j) = 0 := by
    have hcomp : PextFin.toGenerators.val ∘ sourceVar = vC := funext hsourceExt
    rw [hcomp]
    change (MvPolynomial.aeval (aToC ∘ P.toGenerators.val) (P.relation j)) = 0
    have hcoeff (r : R) : aToC (algebraMap R A r) = algebraMap R C r := by
      change algebraMap B' C (algebraMap R B' r) = _
      rw [IsScalarTower.algebraMap_apply R (Localization S) B' r,
        ← IsScalarTower.algebraMap_apply (Localization S) B' C,
        ← IsScalarTower.algebraMap_apply R (Localization S) C]
    have hmap (q : MvPolynomial (Fin (Algebra.Presentation.ofFinitePresentationVars R A)) R) :
        aToC (MvPolynomial.aeval P.toGenerators.val q) =
          MvPolynomial.aeval (aToC ∘ P.toGenerators.val) q := by
      induction q using MvPolynomial.induction_on with
      | C r => simp [hcoeff]
      | add q q' hq hq' => simp [map_add, hq, hq']
      | mul_X q i hq => simp [map_mul, hq, Function.comp_def]
    rw [← hmap, hPzero j, map_zero]
  let fLoc : Fin (c + nA) → MvPolynomial (Fin nB) (Localization S) :=
    PextFin.relation
  let denUnit : Fin nB → (Localization S)ˣ := fun i =>
    (IsLocalization.map_units (Localization S) (denB i)).unit
  have hdenUnit (i : Fin nB) :
      (denUnit i : Localization S) = algebraMap R (Localization S) (denB i : R) :=
    (IsLocalization.map_units (Localization S) (denB i)).unit_spec
  let fScaled : Fin (c + nA) → MvPolynomial (Fin nB) (Localization S) :=
    fun j => (diagonalScaleEquiv denUnit).symm (fLoc j)
  choose denRel liftRel hLiftRel using fun j : Fin (c + nA) =>
    exists_localization_multiple_polynomial_lift S (fScaled j)
  let xLoc : Fin nB → Λₛ := fun i => cToΛ (PextFin.toGenerators.val i)
  let cToΛAlg : C →ₐ[Localization S] Λₛ := {
    toRingHom := cToΛ
    commutes' := hcToΛ_base }
  have hmemLoc (x : MvPolynomial (Fin nB) (Localization S)) :
      x ∈ Ideal.span (Set.range fLoc) ↔ MvPolynomial.aeval PextFin.toGenerators.val x = 0 := by
    rw [show Ideal.span (Set.range fLoc) = PextFin.toGenerators.ker from
      PextFin.span_range_relation_eq_ker, PextFin.toGenerators.ker_eq_ker_aeval_val,
      RingHom.mem_ker]
  have hrelEval (j : Fin (c + nA)) :
      MvPolynomial.aeval xLoc (fLoc j) = 0 := by
    have hzero : MvPolynomial.aeval PextFin.toGenerators.val (fLoc j) = 0 :=
      (hmemLoc _).mp (Ideal.subset_span ⟨j, rfl⟩)
    calc
      MvPolynomial.aeval xLoc (fLoc j) =
          cToΛ (MvPolynomial.aeval PextFin.toGenerators.val (fLoc j)) :=
        (MvPolynomial.comp_aeval_apply PextFin.toGenerators.val cToΛAlg (fLoc j)).symm
      _ = 0 := by rw [hzero, map_zero]
  have hscaledEval (j : Fin (c + nA)) :
      MvPolynomial.aeval
        (fun i => algebraMap (Localization S) Λₛ (denUnit i) * xLoc i)
        (fScaled j) = 0 := by
    simpa [fScaled, xLoc] using
      aeval_diagonalScale_symm denUnit xLoc (fLoc j) ▸ hrelEval j
  have hmapEval (p : MvPolynomial (Fin nB) R) :
      algebraMap Λ Λₛ (MvPolynomial.aeval liftB p) =
        MvPolynomial.aeval (fun i => algebraMap Λ Λₛ (liftB i))
          (MvPolynomial.map (algebraMap R Λₛ) p) := by
    induction p using MvPolynomial.induction_on with
    | C r => simp [IsScalarTower.algebraMap_eq R Λ Λₛ]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  have hcoords (i : Fin nB) :
      algebraMap Λ Λₛ (liftB i) =
        algebraMap (Localization S) Λₛ (denUnit i) * xLoc i := by
    rw [hliftB]
    calc
      algebraMap R Λₛ (denB i : R) * xLoc i =
          algebraMap (Localization S) Λₛ
            (algebraMap R (Localization S) (denB i : R)) * xLoc i :=
        congrArg (fun z : Λₛ => z * xLoc i)
          (IsScalarTower.algebraMap_apply R (Localization S) Λₛ (denB i : R))
      _ = algebraMap (Localization S) Λₛ (denUnit i) * xLoc i := by
        rw [← hdenUnit]
  have hmapScaledEval (p : MvPolynomial (Fin nB) (Localization S)) :
      MvPolynomial.aeval
          (fun i => algebraMap (Localization S) Λₛ (denUnit i) * xLoc i)
          (MvPolynomial.map (algebraMap (Localization S) Λₛ) p) =
        MvPolynomial.aeval
          (fun i => algebraMap (Localization S) Λₛ (denUnit i) * xLoc i) p := by
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have hcomp : (algebraMap Λₛ Λₛ).comp
        (algebraMap (Localization S) Λₛ) = algebraMap (Localization S) Λₛ := by
      ext x
      simp
    rw [hcomp]
  have hcoeffLift (j : Fin (c + nA)) :
      MvPolynomial.map (algebraMap R Λₛ) (liftRel j) =
        MvPolynomial.C (algebraMap R Λₛ (denRel j : R)) *
          MvPolynomial.map (algebraMap (Localization S) Λₛ) (fScaled j) := by
    have hh := congrArg (MvPolynomial.map (algebraMap (Localization S) Λₛ)) (hLiftRel j)
    rw [MvPolynomial.map_map] at hh
    have hcomp : (algebraMap (Localization S) Λₛ).comp (algebraMap R (Localization S)) =
        algebraMap R Λₛ := by
      ext r
      exact (IsScalarTower.algebraMap_apply R (Localization S) Λₛ r).symm
    rw [hcomp] at hh
    rw [map_mul, MvPolynomial.map_C] at hh
    have hden : algebraMap (Localization S) Λₛ
        (algebraMap R (Localization S) (denRel j : R)) =
          algebraMap R Λₛ (denRel j : R) :=
      (IsScalarTower.algebraMap_apply R (Localization S) Λₛ (denRel j : R)).symm
    rw [hden] at hh
    exact hh
  have hfirstEvalLoc (j : Fin (c + nA)) :
      algebraMap Λ Λₛ (MvPolynomial.aeval liftB (liftRel j)) = 0 := by
    rw [hmapEval, hcoeffLift]
    have hcoordFun : (fun i => algebraMap Λ Λₛ (liftB i)) =
        (fun i => algebraMap (Localization S) Λₛ (denUnit i) * xLoc i) := funext hcoords
    rw [hcoordFun, map_mul, MvPolynomial.aeval_C, hmapScaledEval, hscaledEval]
    simp
  choose denEval hEvalFirst using fun j : Fin (c + nA) =>
    exists_localization_multiple_eq_zero S (MvPolynomial.aeval liftB (liftRel j))
      (hfirstEvalLoc j)
  let firstRel : Fin (c + nA) → MvPolynomial (Fin nB) R := fun j =>
    MvPolynomial.C (denEval j : R) * liftRel j
  have hfirstRelEval (j : Fin (c + nA)) :
      MvPolynomial.aeval liftB (firstRel j) = 0 := by
    simp only [firstRel, map_mul, MvPolynomial.aeval_C]
    exact hEvalFirst j
  let sourceRelPoly : Fin (Algebra.Presentation.ofFinitePresentationRels R A) →
      MvPolynomial (Fin nB) R := fun j =>
        MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i)) (P.relation j)
  have hsourceLiftB (i : Fin nA) : liftB (sourceVar i) =
      algebraMap A Λ (P.toGenerators.val i) := by
    have hi : sourceVar i = eFin (Sum.inl (Sum.inr i)) := rfl
    rw [hi]
    simp [liftB]
  have hsourceRelEval (j : Fin (Algebra.Presentation.ofFinitePresentationRels R A)) :
      MvPolynomial.aeval liftB (sourceRelPoly j) = 0 := by
    change MvPolynomial.aeval liftB
      (MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i)) (P.relation j)) = 0
    rw [MvPolynomial.comp_aeval_apply
      (fun i => MvPolynomial.X (sourceVar i)) (MvPolynomial.aeval liftB)]
    rw [show (fun i => MvPolynomial.aeval liftB (MvPolynomial.X (sourceVar i))) =
        (algebraMap A Λ) ∘ P.toGenerators.val by
          funext i
          simp only [MvPolynomial.aeval_X]
          exact hsourceLiftB i]
    calc
      MvPolynomial.aeval ((algebraMap A Λ) ∘ P.toGenerators.val) (P.relation j) =
          algebraMap A Λ (MvPolynomial.aeval P.toGenerators.val (P.relation j)) := by
        symm
        exact MvPolynomial.comp_aeval_apply P.toGenerators.val
          (IsScalarTower.toAlgHom R A Λ) (P.relation j)
      _ = 0 := by rw [hPzero j, map_zero]
  have hmapEvalLoc (q : MvPolynomial (Fin nB) R) :
      MvPolynomial.aeval PextFin.toGenerators.val
          (MvPolynomial.map (algebraMap R (Localization S)) q) =
        MvPolynomial.aeval PextFin.toGenerators.val q := by
    induction q using MvPolynomial.induction_on with
    | C r => simp [IsScalarTower.algebraMap_eq R (Localization S) C]
    | add q q' hq hq' => simp [hq, hq']
    | mul_X q i hq => simp [hq]
  have hmapSourceRel (q : MvPolynomial (Fin nA) R) :
      MvPolynomial.map (algebraMap R (Localization S))
          (MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i)) q) =
        MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i))
          (MvPolynomial.map (algebraMap R (Localization S)) q) := by
    change MvPolynomial.map (algebraMap R (Localization S))
        (MvPolynomial.aeval (MvPolynomial.X ∘ sourceVar) q) =
      MvPolynomial.aeval (MvPolynomial.X ∘ sourceVar)
        (MvPolynomial.map (algebraMap R (Localization S)) q)
    rw [← MvPolynomial.rename_eq_aeval, MvPolynomial.map_rename,
      ← MvPolynomial.rename_eq_aeval]
  have hsourceRelMemLoc (j : Fin (Algebra.Presentation.ofFinitePresentationRels R A)) :
      MvPolynomial.map (algebraMap R (Localization S)) (sourceRelPoly j) ∈
        Ideal.span (Set.range fLoc) := by
    have hzero : MvPolynomial.aeval PextFin.toGenerators.val
        (MvPolynomial.map (algebraMap R (Localization S)) (sourceRelPoly j)) = 0 := by
      rw [hmapEvalLoc]
      change MvPolynomial.aeval PextFin.toGenerators.val
        (MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i)) (P.relation j)) = 0
      rw [MvPolynomial.comp_aeval_apply
        (fun i => MvPolynomial.X (sourceVar i))
        (MvPolynomial.aeval PextFin.toGenerators.val)]
      simpa only [MvPolynomial.aeval_X, Function.comp_def] using hsourceRel j
    exact (hmemLoc _).mpr hzero
  have hsourceUnit (i : Fin nA) : denUnit (sourceVar i) = 1 := by
    apply Units.ext
    rw [hdenUnit]
    have hden : denB (sourceVar i) = 1 := by
      have hi : sourceVar i = eFin (Sum.inl (Sum.inr i)) := rfl
      rw [hi]
      simp [denB]
    rw [hden]
    simp
  have hsourceX (i : Fin nA) :
      (diagonalScaleEquiv denUnit).symm (MvPolynomial.X (sourceVar i)) =
        MvPolynomial.X (sourceVar i) := by
    rw [diagonalScaleEquiv_symm_X]
    simp [hsourceUnit i]
  have hsourceScale (j : Fin (Algebra.Presentation.ofFinitePresentationRels R A)) :
      (diagonalScaleEquiv denUnit).symm
          (MvPolynomial.map (algebraMap R (Localization S)) (sourceRelPoly j)) =
        MvPolynomial.map (algebraMap R (Localization S)) (sourceRelPoly j) := by
    have hcomp := MvPolynomial.comp_aeval
      (fun i => MvPolynomial.X (sourceVar i))
      (diagonalScaleEquiv denUnit).symm.toAlgHom
    have happly := congrArg (fun φ : MvPolynomial (Fin nA) (Localization S) →ₐ[Localization S]
        MvPolynomial (Fin nB) (Localization S) => φ (MvPolynomial.map
          (algebraMap R (Localization S)) (P.relation j))) hcomp
    have happly' : (diagonalScaleEquiv denUnit).symm
        (MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i))
          (MvPolynomial.map (algebraMap R (Localization S)) (P.relation j))) =
        MvPolynomial.aeval (fun i => (diagonalScaleEquiv denUnit).symm
          (MvPolynomial.X (sourceVar i))) (MvPolynomial.map
            (algebraMap R (Localization S)) (P.relation j)) := by
      simpa only [AlgHom.coe_comp, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using happly
    calc
      (diagonalScaleEquiv denUnit).symm
          (MvPolynomial.map (algebraMap R (Localization S))
            (MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i)) (P.relation j))) =
          (diagonalScaleEquiv denUnit).symm
          (MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i))
              (MvPolynomial.map (algebraMap R (Localization S)) (P.relation j))) := by
                rw [hmapSourceRel (P.relation j)]
      _ = MvPolynomial.aeval (fun i => (diagonalScaleEquiv denUnit).symm
            (MvPolynomial.X (sourceVar i))) (MvPolynomial.map
              (algebraMap R (Localization S)) (P.relation j)) := happly'
      _ = MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i))
            (MvPolynomial.map (algebraMap R (Localization S)) (P.relation j)) := by
              have hfun : (fun i => (diagonalScaleEquiv denUnit).symm.toAlgHom
                  (MvPolynomial.X (sourceVar i))) =
                (fun i => MvPolynomial.X (sourceVar i)) := by
                funext i
                exact hsourceX i
              exact congrArg (fun f => MvPolynomial.aeval f
                (MvPolynomial.map (algebraMap R (Localization S)) (P.relation j))) hfun
      _ = MvPolynomial.map (algebraMap R (Localization S))
            (MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i)) (P.relation j)) := by
              rw [← hmapSourceRel (P.relation j)]
  have hsourceRelMemScaled (j : Fin (Algebra.Presentation.ofFinitePresentationRels R A)) :
      MvPolynomial.map (algebraMap R (Localization S)) (sourceRelPoly j) ∈
        Ideal.span (Set.range fScaled) := by
    rw [← hsourceScale j]
    exact diagonalScale_mem_span denUnit fLoc _ (hsourceRelMemLoc j)
  have hCunit (s : S) :
      IsUnit (MvPolynomial.C (algebraMap R (Localization S) (s : R)) :
        MvPolynomial (Fin nB) (Localization S)) := by
    exact (IsLocalization.map_units (Localization S) s).map MvPolynomial.C
  have hscaledInLiftRel (j : Fin (c + nA)) :
      fScaled j ∈ Ideal.span (Set.range (fun k =>
        MvPolynomial.map (algebraMap R (Localization S)) (liftRel k))) := by
    apply (Ideal.unit_mul_mem_iff_mem _ (hCunit (denRel j))).mp
    rw [← hLiftRel j]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hLiftRelInFirst (j : Fin (c + nA)) :
      MvPolynomial.map (algebraMap R (Localization S)) (liftRel j) ∈
        Ideal.span (Set.range (fun k =>
          MvPolynomial.map (algebraMap R (Localization S)) (firstRel k))) := by
    have hgen : MvPolynomial.C (algebraMap R (Localization S) (denEval j : R)) *
        MvPolynomial.map (algebraMap R (Localization S)) (liftRel j) ∈
          Ideal.span (Set.range (fun k =>
            MvPolynomial.map (algebraMap R (Localization S)) (firstRel k))) := by
      have hgen' : MvPolynomial.map (algebraMap R (Localization S)) (firstRel j) ∈
          Ideal.span (Set.range (fun k =>
            MvPolynomial.map (algebraMap R (Localization S)) (firstRel k))) :=
        Ideal.subset_span ⟨j, rfl⟩
      simpa [firstRel, map_mul, MvPolynomial.map_C] using hgen'
    exact (Ideal.unit_mul_mem_iff_mem _ (hCunit (denEval j))).mp hgen
  have hscaledInFirst (j : Fin (c + nA)) :
      fScaled j ∈ Ideal.span (Set.range (fun k =>
        MvPolynomial.map (algebraMap R (Localization S)) (firstRel k))) := by
    have hle : Ideal.span (Set.range (fun k =>
        MvPolynomial.map (algebraMap R (Localization S)) (liftRel k))) ≤
        Ideal.span (Set.range (fun k =>
        MvPolynomial.map (algebraMap R (Localization S)) (firstRel k))) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact hLiftRelInFirst k
    exact hle (hscaledInLiftRel j)
  have hscaledFirstLe : Ideal.span (Set.range fScaled) ≤
      Ideal.span (Set.range (fun j =>
        MvPolynomial.map (algebraMap R (Localization S)) (firstRel j))) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hscaledInFirst j
  have hsourceRelMemFirstLoc (j : Fin (Algebra.Presentation.ofFinitePresentationRels R A)) :
      MvPolynomial.map (algebraMap R (Localization S)) (sourceRelPoly j) ∈
        Ideal.span (Set.range (fun k =>
          MvPolynomial.map (algebraMap R (Localization S)) (firstRel k))) :=
    hscaledFirstLe (hsourceRelMemScaled j)
  obtain ⟨denTail, hdenTail⟩ := exists_localization_multiple_mem_span_family
    S firstRel sourceRelPoly hsourceRelMemFirstLoc
  let cFinal := c + nA
  let mSource := Algebra.Presentation.ofFinitePresentationRels R A
  let mFinal := cFinal + mSource
  let hcnFinal : cFinal ≤ nB := Nat.le_add_right _ _
  let hcmFinal : cFinal ≤ mFinal := Nat.le_add_right _ _
  let eAll : Fin cFinal ⊕ Fin mSource ≃ Fin mFinal := finSumFinEquiv
  let relB : Fin mFinal → MvPolynomial (Fin nB) R := fun j =>
    match eAll.symm j with
    | Sum.inl i => firstRel i
    | Sum.inr i => sourceRelPoly i
  let relIdealB : Ideal (MvPolynomial (Fin nB) R) := Ideal.span (Set.range relB)
  let B := MvPolynomial (Fin nB) R ⧸ relIdealB
  let qB : MvPolynomial (Fin nB) R →ₐ[R] B := Ideal.Quotient.mkₐ R relIdealB
  let evalB : MvPolynomial (Fin nB) R →ₐ[R] Λ := MvPolynomial.aeval liftB
  have hrelB_eval (j : Fin mFinal) : evalB (relB j) = 0 := by
    rcases hj : eAll.symm j with i | i
    · simpa [relB, hj, evalB] using hfirstRelEval i
    · simpa [relB, hj, evalB] using hsourceRelEval i
  have hrelB_kernel : relIdealB ≤ RingHom.ker evalB.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact RingHom.mem_ker.mpr (hrelB_eval j)
  let bToΛ : B →ₐ[R] Λ := Ideal.Quotient.liftₐ relIdealB evalB
    (fun p hp => RingHom.mem_ker.mp (hrelB_kernel hp))
  have hsourceRel_mem (j : Fin mSource) : sourceRelPoly j ∈ relIdealB := by
    apply Ideal.subset_span
    refine ⟨eAll (Sum.inr j), ?_⟩
    simp [relB, eAll]
  let sourcePoly : MvPolynomial (Fin nA) R →ₐ[R] MvPolynomial (Fin nB) R :=
    MvPolynomial.aeval (fun i => MvPolynomial.X (sourceVar i))
  let evalSource : MvPolynomial (Fin nA) R →ₐ[R] B := qB.comp sourcePoly
  have hsourceKer : P.toGenerators.ker ≤ RingHom.ker evalSource.toRingHom := by
    rw [← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change Ideal.Quotient.mk relIdealB (sourceRelPoly j) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hsourceRel_mem j
  let fromQuot : P.Quotient →ₐ[R] B :=
    Ideal.Quotient.liftₐ P.toGenerators.ker evalSource
      (fun p hp => RingHom.mem_ker.mp (hsourceKer hp))
  let eP : P.Quotient ≃ₐ[R] A := P.quotientEquiv.restrictScalars R
  let aToB : A →ₐ[R] B := fromQuot.comp eP.symm.toAlgHom
  have hsourceEvalB (i : Fin nA) : bToΛ (qB (MvPolynomial.X (sourceVar i))) =
      algebraMap A Λ (P.toGenerators.val i) := by
    change evalB (MvPolynomial.X (sourceVar i)) = _
    simp [evalB, hsourceLiftB]
  have hpolyComposite : bToΛ.comp evalSource =
      (IsScalarTower.toAlgHom R A Λ).comp (MvPolynomial.aeval P.toGenerators.val) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [evalSource, sourcePoly, hsourceEvalB]
  have hquotComposite (q : P.Quotient) :
      bToΛ (fromQuot q) = algebraMap A Λ (eP q) := by
    obtain ⟨p, hp⟩ := Ideal.Quotient.mkₐ_surjective R P.toGenerators.ker q
    rw [← hp]
    have hh := congrArg (fun φ : MvPolynomial (Fin nA) R →ₐ[R] Λ => φ p) hpolyComposite
    change bToΛ (fromQuot (Ideal.Quotient.mk P.toGenerators.ker p)) =
      algebraMap A Λ (eP (Ideal.Quotient.mk P.toGenerators.ker p))
    have hfrom : fromQuot (Ideal.Quotient.mk P.toGenerators.ker p) = evalSource p := by
      rfl
    rw [hfrom]
    simpa [evalSource, eP, P.quotientEquiv_mk] using hh
  have hTowerAB_map : bToΛ.comp aToB = IsScalarTower.toAlgHom R A Λ := by
    apply AlgHom.ext
    intro a
    change bToΛ (fromQuot (eP.symm a)) = algebraMap A Λ a
    rw [hquotComposite]
    simp
  let : Algebra A B := aToB.toRingHom.toAlgebra
  let : Algebra B Λ := bToΛ.toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r =>
    (aToB.commutes r).symm
  let : IsScalarTower A B Λ := IsScalarTower.of_algebraMap_eq fun a => by
    have h := congrArg (fun f : A →ₐ[R] Λ => f a) hTowerAB_map
    simpa [RingHom.algebraMap_toAlgebra] using h.symm
  let : IsScalarTower R B Λ := IsScalarTower.of_algebraMap_eq fun r =>
    (bToΛ.commutes r).symm
  let PF : Presentation R B := {
    n := nB
    m := mFinal
    f := relB
    iso := AlgEquiv.refl (R := R) }
  have hrelFirst (j : Fin cFinal) :
      relB (Fin.castLE hcmFinal j) = firstRel j := by
    have hidx : Fin.castLE hcmFinal j = eAll (Sum.inl j) := by
      apply Fin.ext
      rfl
    rw [hidx]
    simp [relB, eAll]
  have hfirstRelIdeal : PF.firstRelIdeal cFinal hcmFinal =
      Ideal.span (Set.range firstRel) := by
    rw [Presentation.firstRelIdeal]
    congr 1
    ext p
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, (hrelFirst j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, hrelFirst j⟩
  have hmSub : mFinal - cFinal = mSource := by
    simp [mFinal]
  have hrelTail (j : Fin mSource) :
      relB ⟨cFinal + j.1, by have := j.2; omega⟩ = sourceRelPoly j := by
    have hidx : (⟨cFinal + j.1, by have := j.2; omega⟩ : Fin mFinal) =
        eAll (Sum.inr j) := by
      apply Fin.ext
      rfl
    rw [hidx]
    simp [relB, eAll]
  let δ := PF.jacobianMinorPrincipal cFinal hcnFinal hcmFinal
  let p0 : MvPolynomial (Fin nB) R := MvPolynomial.C (denTail : R) * δ
  have hmulTail : ∀ j : Fin (mFinal - cFinal),
      p0 * PF.f (presentationTailIndex hcmFinal j) ∈
        PF.firstRelIdeal cFinal hcmFinal := by
    intro j
    let jSource : Fin mSource := Fin.cast hmSub j
    have hsourceBound : cFinal + jSource.1 < mFinal := by
      change cFinal + jSource.1 < cFinal + mSource
      exact Nat.add_lt_add_left jSource.2 cFinal
    have hidx : presentationTailIndex hcmFinal j =
        (⟨cFinal + jSource.1, hsourceBound⟩ : Fin mFinal) := by
      apply Fin.ext
      simp [presentationTailIndex, jSource]
    change p0 * relB (presentationTailIndex hcmFinal j) ∈ _
    rw [hfirstRelIdeal, hidx, hrelTail jSource]
    have heq : p0 * sourceRelPoly jSource =
        δ * (MvPolynomial.C (denTail : R) * sourceRelPoly jSource) := by
      change (MvPolynomial.C (denTail : R) * δ) * sourceRelPoly jSource = _
      ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ (hdenTail jSource)
  -- In the localization, the Jacobian of the first block is a unit.  Clearing
  -- an inverse for it lets us absorb the Jacobian factor into the denominator
  -- from `S`, leaving a scalar lift for the elementary-standard condition.
  have hSunitC (s : S) : IsUnit (algebraMap R C (s : R)) := by
    rw [IsScalarTower.algebraMap_apply R (Localization S) C]
    exact (IsLocalization.map_units (Localization S) s).map _
  let xScaledC : Fin nB → C := fun i =>
    algebraMap (Localization S) C (denUnit i : Localization S) *
      PextFin.toGenerators.val i
  let evalScaledC : MvPolynomial (Fin nB) (Localization S) →ₐ[Localization S] C :=
    MvPolynomial.aeval xScaledC
  let evalBaseC : MvPolynomial (Fin nB) (Localization S) →ₐ[Localization S] C :=
    MvPolynomial.aeval PextFin.toGenerators.val
  have hevalScaled (p : MvPolynomial (Fin nB) (Localization S)) :
      evalScaledC p = evalBaseC (diagonalScaleEquiv denUnit p) := by
    have h := aeval_diagonalScale_symm denUnit PextFin.toGenerators.val
      (diagonalScaleEquiv denUnit p)
    change evalScaledC ((diagonalScaleEquiv denUnit).symm
        (diagonalScaleEquiv denUnit p)) = evalBaseC (diagonalScaleEquiv denUnit p) at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  have hscaledEvalKernel (p : MvPolynomial (Fin nB) (Localization S))
      (hp : evalScaledC p = 0) : p ∈ Ideal.span (Set.range fScaled) := by
    have hzero : evalBaseC (diagonalScaleEquiv denUnit p) = 0 := by
      rw [← hevalScaled]
      exact hp
    have hm := diagonalScale_mem_span denUnit fLoc (diagonalScaleEquiv denUnit p)
      ((hmemLoc _).mpr hzero)
    simpa using hm
  let rowFactor : Fin cFinal → C := fun j =>
    algebraMap R C (denEval j : R) * algebraMap R C (denRel j : R)
  let colFactor : Fin cFinal → C := fun i =>
    algebraMap (Localization S) C
      (((denUnit (Fin.castLE hcnFinal i))⁻¹ : (Localization S)ˣ) : Localization S)
  let baseJacobianMatrix : Matrix (Fin cFinal) (Fin cFinal) C := fun i j =>
    evalBaseC (MvPolynomial.pderiv (Fin.castLE hcnFinal i) (fLoc j))
  have hbaseJacobianMatrix : baseJacobianMatrix =
      evalBaseC.mapMatrix PextPre.jacobiMatrix := by
    ext i j
    dsimp [baseJacobianMatrix]
    change evalBaseC (MvPolynomial.pderiv (Fin.castLE hcnFinal i) (fLoc j)) =
      evalBaseC (PextPre.jacobiMatrix i j)
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    rw [hPextMap]
    have hrel : PextPre.relation j = fLoc j := by
      change PextPre.toPresentation.relation j = PextFin.relation j
      rw [hPextPre]
    rw [hrel]
  have hbaseJacobianUnit : IsUnit (Matrix.det baseJacobianMatrix) := by
    rw [hbaseJacobianMatrix, ← evalBaseC.map_det]
    have hdet : evalBaseC PextPre.jacobiMatrix.det = PextPre.jacobian := by
      rw [PextPre.jacobian_eq_jacobiMatrix_det]
      have hval : PextPre.toPresentation.toGenerators.val = PextFin.toGenerators.val := by
        rw [hPextPre]
      change MvPolynomial.aeval PextFin.toGenerators.val _ = _
      rw [← hval]
      exact PextPre.toPresentation.toGenerators.algebraMap_apply _
    rw [hdet]
    exact hPextJacUnit
  have hscaledPderiv (j : Fin cFinal) (i : Fin cFinal) :
      evalScaledC (MvPolynomial.pderiv (Fin.castLE hcnFinal i) (fScaled j)) =
        colFactor i * baseJacobianMatrix i j := by
    let k := Fin.castLE hcnFinal i
    have hpoly : fScaled j = MvPolynomial.aeval
        (fun l => MvPolynomial.C ((((denUnit l)⁻¹ : (Localization S)ˣ) : Localization S)) *
          MvPolynomial.X l) (fLoc j) := by
      simp [fScaled, diagonalScaleEquiv]
    have hderiv := pderiv_aeval_diagonal
      (fun l => (((denUnit l)⁻¹ : (Localization S)ˣ) : Localization S))
      (fLoc j) k
    have hevalDeriv : evalScaledC
        (MvPolynomial.aeval
          (fun l => MvPolynomial.C ((((denUnit l)⁻¹ : (Localization S)ˣ) : Localization S)) *
            MvPolynomial.X l) (MvPolynomial.pderiv k (fLoc j))) =
        baseJacobianMatrix i j := by
      simpa [baseJacobianMatrix, evalScaledC, evalBaseC, xScaledC, k,
        diagonalScaleEquiv] using
        (aeval_diagonalScale_symm denUnit PextFin.toGenerators.val
          (MvPolynomial.pderiv k (fLoc j)))
    calc
      evalScaledC (MvPolynomial.pderiv k (fScaled j)) =
          evalScaledC (MvPolynomial.C ((((denUnit k)⁻¹ : (Localization S)ˣ) : Localization S)) *
            MvPolynomial.aeval
              (fun l => MvPolynomial.C ((((denUnit l)⁻¹ : (Localization S)ˣ) : Localization S)) *
                MvPolynomial.X l) (MvPolynomial.pderiv k (fLoc j))) := by
              rw [hpoly, hderiv]
      _ = colFactor i * baseJacobianMatrix i j := by
            rw [map_mul, MvPolynomial.aeval_C, hevalDeriv]
  have hfirstRelMap (j : Fin cFinal) :
      MvPolynomial.map (algebraMap R (Localization S)) (firstRel j) =
        MvPolynomial.C (algebraMap R (Localization S) (denEval j : R)) *
          (MvPolynomial.C (algebraMap R (Localization S) (denRel j : R)) * fScaled j) := by
    simp [firstRel, map_mul, MvPolynomial.map_C, hLiftRel]
  let scaledJacobianMatrix : Matrix (Fin cFinal) (Fin cFinal) C := fun j i =>
    evalScaledC (MvPolynomial.pderiv (Fin.castLE hcnFinal i)
      (MvPolynomial.map (algebraMap R (Localization S)) (firstRel j)))
  have hscaledJacobianMatrix : scaledJacobianMatrix =
      Matrix.diagonal rowFactor * baseJacobianMatrix.transpose * Matrix.diagonal colFactor := by
    ext j i
    have hmul :
        (Matrix.diagonal rowFactor * baseJacobianMatrix.transpose *
          Matrix.diagonal colFactor) j i =
          rowFactor j * baseJacobianMatrix i j * colFactor i := by
      simp [Matrix.mul_apply, Matrix.diagonal_apply]
    calc
      scaledJacobianMatrix j i = rowFactor j * baseJacobianMatrix i j * colFactor i := by
        dsimp [scaledJacobianMatrix]
        rw [hfirstRelMap,
          MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_C_mul]
        rw [map_mul, MvPolynomial.aeval_C, map_mul, MvPolynomial.aeval_C]
        rw [hscaledPderiv]
        rw [← IsScalarTower.algebraMap_apply R (Localization S) C (denEval j : R),
          ← IsScalarTower.algebraMap_apply R (Localization S) C (denRel j : R)]
        dsimp [rowFactor, colFactor]
        ring
      _ = (Matrix.diagonal rowFactor * baseJacobianMatrix.transpose *
          Matrix.diagonal colFactor) j i := hmul.symm
  let jacobianMatrixR : Matrix (Fin cFinal) (Fin cFinal) (MvPolynomial (Fin nB) R) :=
    fun j i => MvPolynomial.pderiv (Fin.castLE hcnFinal i)
      (PF.f (Fin.castLE hcmFinal j))
  have hδdef : δ = Matrix.det jacobianMatrixR := by
    unfold δ Presentation.jacobianMinorPrincipal
    apply congrArg Matrix.det
    ext j i
    rfl
  have hδeval : evalScaledC (MvPolynomial.map (algebraMap R (Localization S)) δ) =
      Matrix.det scaledJacobianMatrix := by
    rw [hδdef, RingHom.map_det, evalScaledC.map_det]
    congr 1
    ext j i
    simp only [AlgHom.mapMatrix_apply,
      Matrix.map_apply, jacobianMatrixR]
    change evalScaledC (MvPolynomial.map (algebraMap R (Localization S))
        (MvPolynomial.pderiv (Fin.castLE hcnFinal i)
          (PF.f (Fin.castLE hcmFinal j)))) =
      evalScaledC (MvPolynomial.pderiv (Fin.castLE hcnFinal i)
        (MvPolynomial.map (algebraMap R (Localization S)) (firstRel j)))
    rw [show PF.f (Fin.castLE hcmFinal j) = firstRel j from hrelFirst j,
      MvPolynomial.pderiv_map]
  have hrowFactorUnit (j : Fin cFinal) : IsUnit (rowFactor j) :=
    (hSunitC (denEval j)).mul (hSunitC (denRel j))
  have hcolFactorUnit (i : Fin cFinal) : IsUnit (colFactor i) := by
    apply IsUnit.map (algebraMap (Localization S) C)
    exact ((denUnit (Fin.castLE hcnFinal i))⁻¹).isUnit
  have hδevalUnit : IsUnit
      (evalScaledC (MvPolynomial.map (algebraMap R (Localization S)) δ)) := by
    rw [hδeval, hscaledJacobianMatrix, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, Matrix.det_transpose, Matrix.det_diagonal]
    simpa [mul_assoc] using (IsUnit.prod_univ_iff.mpr hrowFactorUnit).mul
      (hbaseJacobianUnit.mul (IsUnit.prod_univ_iff.mpr hcolFactorUnit))
  -- Lift an inverse of the localized Jacobian back to the polynomial ring.
  -- Its denominator can be absorbed into `denTail` and changes the displayed
  -- Jacobian multiple into the image of an element of `S`.
  let qC : C := ↑(hδevalUnit.unit⁻¹)
  let qBase : MvPolynomial (Fin nB) (Localization S) :=
    PextFin.toGenerators.σ' qC
  let qLoc : MvPolynomial (Fin nB) (Localization S) :=
    (diagonalScaleEquiv denUnit).symm qBase
  have hqLoc : evalScaledC qLoc = qC := by
    dsimp [qLoc, qBase, qC]
    calc
      evalScaledC ((diagonalScaleEquiv denUnit).symm
          (PextFin.toGenerators.σ' ↑(hδevalUnit.unit⁻¹))) =
          evalBaseC (PextFin.toGenerators.σ' ↑(hδevalUnit.unit⁻¹)) :=
        aeval_diagonalScale_symm denUnit PextFin.toGenerators.val _
      _ = ↑(hδevalUnit.unit⁻¹) := PextFin.toGenerators.aeval_val_σ' _
  have hδinverse : qC * evalScaledC
      (MvPolynomial.map (algebraMap R (Localization S)) δ) = 1 := by
    dsimp [qC]
    calc
      ↑(hδevalUnit.unit⁻¹) * evalScaledC
          (MvPolynomial.map (algebraMap R (Localization S)) δ) =
          ↑(hδevalUnit.unit⁻¹) * ↑hδevalUnit.unit := by
            congr 1
      _ = 1 := Units.inv_mul hδevalUnit.unit
  have hqRelLoc : evalScaledC
      (qLoc * MvPolynomial.map (algebraMap R (Localization S)) δ - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hqLoc, hδinverse]
    simp
  have hqRelScaled : qLoc * MvPolynomial.map (algebraMap R (Localization S)) δ - 1 ∈
      Ideal.span (Set.range fScaled) := hscaledEvalKernel _ hqRelLoc
  have hqRelFirst : qLoc * MvPolynomial.map (algebraMap R (Localization S)) δ - 1 ∈
      Ideal.span (Set.range (fun j =>
        MvPolynomial.map (algebraMap R (Localization S)) (firstRel j))) :=
    hscaledFirstLe hqRelScaled
  obtain ⟨u, q0, hq0⟩ := exists_localization_multiple_polynomial_lift S qLoc
  let qDiff : MvPolynomial (Fin nB) R :=
    q0 * δ - MvPolynomial.C (u : R)
  have hqDiffLoc : MvPolynomial.map (algebraMap R (Localization S)) qDiff =
      MvPolynomial.C (algebraMap R (Localization S) (u : R)) *
        (qLoc * MvPolynomial.map (algebraMap R (Localization S)) δ - 1) := by
    dsimp [qDiff]
    rw [map_sub, map_mul, hq0, MvPolynomial.map_C]
    ring
  have hqDiffMemLoc : MvPolynomial.map (algebraMap R (Localization S)) qDiff ∈
      Ideal.span (Set.range (fun j =>
        MvPolynomial.map (algebraMap R (Localization S)) (firstRel j))) := by
    rw [hqDiffLoc]
    exact Ideal.mul_mem_left _ _ hqRelFirst
  obtain ⟨t, ht⟩ := exists_localization_multiple_mem_span S firstRel qDiff hqDiffMemLoc
  let clearDen : S := u * t
  let qPoly : MvPolynomial (Fin nB) R := MvPolynomial.C (t : R) * q0
  have hqPolyRel : qPoly * δ - MvPolynomial.C (clearDen : R) ∈
      PF.firstRelIdeal cFinal hcmFinal := by
    rw [hfirstRelIdeal]
    have heq : qPoly * δ - MvPolynomial.C (clearDen : R) =
        MvPolynomial.C (t : R) * qDiff := by
      dsimp [qPoly, clearDen, qDiff]
      rw [map_mul]
      ring
    rw [heq]
    exact ht
  have hfirstLeRel : PF.firstRelIdeal cFinal hcmFinal ≤ PF.relIdeal := by
    rw [hfirstRelIdeal, Presentation.relIdeal]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [← hrelFirst j]
    exact Ideal.subset_span ⟨Fin.castLE hcmFinal j, rfl⟩
  have hqPolyRelB : qPoly * δ - MvPolynomial.C (clearDen : R) ∈ PF.relIdeal :=
    hfirstLeRel hqPolyRel
  let finalDen : S := denTail * clearDen
  let finalP0 : MvPolynomial (Fin nB) R := MvPolynomial.C (finalDen : R)
  let finalA : B := algebraMap R B (finalDen : R)
  have hfinalP0 : PF.IsLift finalA finalP0 := by
    change PF.lift finalP0 = finalA
    simp [PF, finalP0, finalA, Presentation.lift]
  have hmulTailFinal : ∀ j : Fin (mFinal - cFinal),
      finalP0 * PF.f (presentationTailIndex hcmFinal j) ∈
        PF.firstRelIdeal cFinal hcmFinal + PF.relIdeal ^ 2 := by
    intro j
    let tail := PF.f (presentationTailIndex hcmFinal j)
    have htail : tail ∈ PF.relIdeal :=
      Ideal.subset_span ⟨presentationTailIndex hcmFinal j, rfl⟩
    have hmain : qPoly * (p0 * tail) ∈ PF.firstRelIdeal cFinal hcmFinal :=
      Ideal.mul_mem_left _ _ (hmulTail j)
    have hsecondBase : (qPoly * δ - MvPolynomial.C (clearDen : R)) * tail ∈
        PF.relIdeal ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hfirstLeRel hqPolyRel) htail
    have hsecond : MvPolynomial.C (denTail : R) *
        ((qPoly * δ - MvPolynomial.C (clearDen : R)) * tail) ∈ PF.relIdeal ^ 2 :=
      Ideal.mul_mem_left _ _ hsecondBase
    have heq : finalP0 * tail = qPoly * (p0 * tail) -
        MvPolynomial.C (denTail : R) *
          ((qPoly * δ - MvPolynomial.C (clearDen : R)) * tail) := by
      dsimp [finalP0, finalDen, p0]
      rw [map_mul]
      ring
    rw [heq, sub_eq_add_neg, Ideal.add_eq_sup]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hmain)
      (Ideal.mem_sup_right ((PF.relIdeal ^ 2).neg_mem hsecond))
  have hfinalCond : PF.StandardCond2 finalA cFinal hcmFinal :=
    standardCond2_of_mul_mem PF finalA cFinal hcmFinal finalP0 hfinalP0 hmulTailFinal
  have hquotFactor : PF.lift (qPoly * δ) = algebraMap R B (clearDen : R) := by
    change Ideal.Quotient.mk relIdealB (qPoly * δ) =
      Ideal.Quotient.mk relIdealB (MvPolynomial.C (clearDen : R))
    exact (Ideal.Quotient.eq).2 hqPolyRelB
  have hfinalElementary : IsElementaryStandard (R := R) finalA := by
    refine ⟨PF, cFinal, hcnFinal, hcmFinal, ?_⟩
    constructor
    · refine ⟨algebraMap R B (denTail : R) * PF.lift qPoly, ?_⟩
      dsimp [finalA, finalDen]
      calc
        algebraMap R B ((denTail : R) * (clearDen : R)) =
            algebraMap R B (denTail : R) * algebraMap R B (clearDen : R) := map_mul _ _ _
        _ = algebraMap R B (denTail : R) * PF.lift (qPoly * δ) := by rw [← hquotFactor]
        _ = (algebraMap R B (denTail : R) * PF.lift qPoly) * PF.lift δ := by
            simp [Presentation.lift, PF, map_mul, mul_assoc]
    · exact hfinalCond
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨finalDen, hfinalElementary⟩

end Stacks.Smoothing
