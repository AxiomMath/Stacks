module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import StacksFrontier.Homology.HomComplex.TensorHom

/-!
# Shifts of Hom complexes

Let `R` be a commutative ring, let `M` and `K` be cochain complexes of `R`-modules and let `a`
and `b` be integers. Shifting the Hom complex `Hom^•(M, K)` by `a - b` canonically identifies it
with the Hom complex `Hom^•(M[b], K[a])` from the `b`-shift of the source to the `a`-shift of
the target. Transporting that identification into a morphism
`Hom^•(M, K) ⟶ Hom^•(M[b], K[a])[b - a]` multiplies a degree-`n` cochain by `(-1)^(n b)` before
reindexing.

## Main definitions

* `CochainComplex.HomComplex.homComplexShiftIso` ([stacks 0FNN]): the canonical shift
  identification `Hom^•(M, K)[a - b] ≅ Hom^•(M[b], K[a])`, bundled with the degreewise sign
  formula and the differential calculation that makes the reindexing a morphism of complexes.

## Main results

The specification carried by `homComplexShiftIso` is the content of the tag: its first conjunct
gives the degreewise sign `(-1)^(n b)` relating the isomorphism to the evident reindexing of
homogeneous components, and its second conjunct is the differential calculation, namely that the
differential in the shifted target is `(-1)^b` times the reindexed source differential.

## Implementation notes

The Hom complex is `CochainComplex.HomComplexR`. The unscaled reindexing appearing in the
specification is written out explicitly on homogeneous components, as the cochain whose
`(p, q)`-component is the component of the original cochain at `(p + b, q + a)`, conjugated by
the canonical identifications of the terms of a shifted complex. Because the degree-dependent
sign `(-1)^(n b)` is what turns that reindexing into a morphism of complexes, the two conjuncts
have to be stated separately: the second one is about the reindexing before the sign is
inserted.

The isomorphism is bundled with its specification as a subtype rather than being defined and
then characterized, because the specification is what the source asserts and the underlying
identification is only determined up to the stated formulas.

Universes are left fully general: the ring and the module universe are independent, since no
tensor product of complexes occurs.

## References

* [The Stacks Project, Tag 0FNN](https://stacks.math.columbia.edu/tag/0FNN)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.HomComplex

namespace CochainComplex.HomComplex

section ShiftHom

/-- Multiplication by the sign `(-1)^k`, as an `R`-linear automorphism of a module. -/
public noncomputable def negOnePowLinearEquiv (R V : Type*) [CommRing R]
    [AddCommGroup V] [Module R V] (k : ℤ) : V ≃ₗ[R] V where
  toFun x := k.negOnePow • x
  invFun x := k.negOnePow • x
  left_inv x := by
    change k.negOnePow • (k.negOnePow • x) = x
    rw [smul_smul, Int.units_mul_self, one_smul]
  right_inv x := by
    change k.negOnePow • (k.negOnePow • x) = x
    rw [smul_smul, Int.units_mul_self, one_smul]
  map_add' x y := by simp
  map_smul' r x := smul_comm k.negOnePow r x

/-- The reindexing of homogeneous components of a cochain along the shifts of source and target,
as an `R`-linear equivalence `Hom^n(M, K) ≃ Hom^{n + (b - a)}(M[b], K[a])`. -/
private noncomputable def reindexEquiv (R : Type*) [CommRing R]
    (M K : CochainComplex (ModuleCat R) ℤ) (a b n : ℤ) :
    Cochain M K n ≃ₗ[R] Cochain (M⟦b⟧) (K⟦a⟧) (n + (b - a)) :=
  ((Cochain.rightShiftLinearEquiv R M K n a (n - a) (by omega)).trans
    (Cochain.leftShiftLinearEquiv R M (K⟦a⟧) (n - a) b
      (n + (b - a)) (by omega))).trans
    (negOnePowLinearEquiv R _
      (b * (n + (b - a)) + b * (b - 1) / 2))

/-- The reindexing equivalence is the evident reindexing of homogeneous components. -/
private lemma reindexEquiv_apply (R : Type*) [CommRing R]
    (M K : CochainComplex (ModuleCat R) ℤ) (a b n : ℤ) (z : Cochain M K n) :
    reindexEquiv R M K a b n z = Cochain.mk fun p q _ ↦
      (M.shiftFunctorObjXIso b p (p + b) rfl).hom ≫
        z.v (p + b) (q + a) (by omega) ≫
        (K.shiftFunctorObjXIso a q (q + a) rfl).inv := by
  apply Cochain.ext
  intro p q hpq
  dsimp only [reindexEquiv, LinearEquiv.trans_apply, negOnePowLinearEquiv,
    Cochain.leftShiftLinearEquiv_apply, Cochain.rightShiftLinearEquiv_apply, Cochain.mk_v]
  change ((b * (n + (b - a)) + b * (b - 1) / 2).negOnePow •
    ((z.rightShift a (n - a) (by omega)).leftShift b (n + (b - a)) (by omega))).v
      p q hpq = _
  rw [Cochain.units_smul_v,
    Cochain.leftShift_v _ b (n + (b - a)) (by omega) p q hpq (p + b) (by omega),
    Cochain.rightShift_v _ a (n - a) (by omega) (p + b) q (by omega)
      (q + a) (by omega), smul_smul, Int.units_mul_self, one_smul]

/-- The reindexing equivalence carries the Hom-complex differential to `(-1)^a` times the
differential of the shifted Hom complex. -/
private lemma reindexEquiv_delta (R : Type*) [CommRing R]
    (M K : CochainComplex (ModuleCat R) ℤ) (a b n : ℤ) (z : Cochain M K n) :
    δ (n + (b - a)) (n + 1 + (b - a)) (reindexEquiv R M K a b n z) =
      a.negOnePow • reindexEquiv R M K a b (n + 1) (δ n (n + 1) z) := by
  simp only [reindexEquiv, LinearEquiv.trans_apply, negOnePowLinearEquiv,
    Cochain.leftShiftLinearEquiv_apply, Cochain.rightShiftLinearEquiv_apply,
    Int.negOnePow_add]
  change δ (n + (b - a)) (n + 1 + (b - a))
    (((b * (n + (b - a))).negOnePow * (b * (b - 1) / 2).negOnePow) •
      ((z.rightShift a (n - a) (by omega)).leftShift b (n + (b - a)) (by omega))) =
    a.negOnePow •
      (((b * (n + 1 + (b - a))).negOnePow * (b * (b - 1) / 2).negOnePow) •
        (((δ n (n + 1) z).rightShift a (n + 1 - a) (by omega)).leftShift b
          (n + 1 + (b - a)) (by omega)))
  rw [δ_units_smul,
    Cochain.δ_leftShift _ b (n + (b - a)) (n + 1 + (b - a)) (by omega)
      (n + 1 - a) (by omega),
    Cochain.δ_rightShift _ a (n - a) (n + 1 - a) (by omega) (n + 1) (by omega)]
  simp only [Cochain.leftShift_units_smul, smul_smul]
  simp only [← Int.negOnePow_add]
  congr 2
  ring

/-- The reindexing equivalence corrected by the sign `(-1)^(n b)`, which is the degree-`n`
component of the shift identification. -/
private noncomputable def signedReindexEquiv (R : Type*) [CommRing R]
    (M K : CochainComplex (ModuleCat R) ℤ) (a b n : ℤ) :
    Cochain M K n ≃ₗ[R] Cochain (M⟦b⟧) (K⟦a⟧) (n + (b - a)) :=
  (reindexEquiv R M K a b n).trans (negOnePowLinearEquiv R _ (n * b))

/-- The signed reindexing assembles into an isomorphism of complexes
`Hom^•(M, K) ≅ Hom^•(M[b], K[a])[b - a]`. -/
private noncomputable def shiftedIso (R : Type*) [CommRing R]
    (M K : CochainComplex (ModuleCat R) ℤ) (a b : ℤ) :
    CochainComplex.HomComplexR R M K ≅
      (CochainComplex.HomComplexR R (M⟦b⟧) (K⟦a⟧))⟦b - a⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦
    (signedReindexEquiv R M K a b n).toModuleIso ≪≫
      ((CochainComplex.HomComplexR R (M⟦b⟧) (K⟦a⟧)).shiftFunctorObjXIso
        (b - a) n (n + (b - a)) rfl).symm) (by
    intro i j hij
    obtain rfl : j = i + 1 := by simpa using hij.symm
    ext z
    change Cochain M K i at z
    let T := CochainComplex.HomComplexR R (M⟦b⟧) (K⟦a⟧)
    change ((T⟦b - a⟧).d i (i + 1)).hom
        ((T.shiftFunctorObjXIso (b - a) i (i + (b - a)) rfl).inv.hom
          ((i * b).negOnePow • reindexEquiv R M K a b i z)) =
      (T.shiftFunctorObjXIso (b - a) (i + 1) (i + 1 + (b - a)) rfl).inv.hom
        (((i + 1) * b).negOnePow •
          reindexEquiv R M K a b (i + 1) (δ i (i + 1) z))
    let eX := T.shiftFunctorObjXIso (b - a) (i + 1) (i + 1 + (b - a)) rfl
    have heX : Function.Injective eX.hom.hom := by
      intro x y h
      apply_fun eX.inv.hom at h
      simpa only [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply] using h
    apply_fun eX.hom.hom using heX
    simp only [← ModuleCat.comp_apply]
    change (b - a).negOnePow • δ (i + (b - a)) (i + 1 + (b - a))
        ((i * b).negOnePow • reindexEquiv R M K a b i z) =
      ((i + 1) * b).negOnePow • reindexEquiv R M K a b (i + 1) (δ i (i + 1) z)
    rw [δ_units_smul, reindexEquiv_delta]
    simp only [smul_smul, ← Int.negOnePow_add]
    congr 2
    ring)

/-- The signed reindexing commutes with the canonical identifications of terms in equal
degrees. -/
private lemma signedReindexEquiv_XIsoOfEq (R : Type*) [CommRing R]
    (M K : CochainComplex (ModuleCat R) ℤ) (a b n m : ℤ) (h : n = m)
    (h' : m + (b - a) = n + (b - a)) (z : Cochain M K n) :
    ((CochainComplex.HomComplexR R (M⟦b⟧) (K⟦a⟧)).XIsoOfEq h').hom.hom
      (signedReindexEquiv R M K a b m
        (((CochainComplex.HomComplexR R M K).XIsoOfEq h).hom.hom z)) =
      signedReindexEquiv R M K a b n z := by
  subst h; rfl

/-- **Stacks 0FNN.** The canonical identification
`Hom^•(M, K)[a - b] ≅ Hom^•(M[b], K[a])`.

After shifting the identification back to a map `Hom^•(M, K) ⟶ Hom^•(M[b], K[a])[b - a]`, its
degree-`n` component is the sign `(-1)^(n b)` times the evident reindexing. The final conjunct is
the homogeneous differential calculation: before inserting this degree-dependent sign, the
target differential is `(-1)^b` times the reindexed source differential. -/
@[stacks 0FNN, no_expose]
noncomputable def homComplexShiftIso (R : Type*) [CommRing R]
    (M K : CochainComplex (ModuleCat R) ℤ) (a b : ℤ) :
    { e : (CochainComplex.HomComplexR R M K)⟦a - b⟧ ≅
        CochainComplex.HomComplexR R (M⟦b⟧) (K⟦a⟧) //
      let H := CochainComplex.HomComplexR R M K
      let T := CochainComplex.HomComplexR R (M⟦b⟧) (K⟦a⟧)
      let reindex : ∀ n : ℤ, Cochain M K n → Cochain (M⟦b⟧) (K⟦a⟧) (n + (b - a)) :=
        fun n z ↦ Cochain.mk fun p q _ ↦
          (M.shiftFunctorObjXIso b p (p + b) rfl).hom ≫
            z.v (p + b) (q + a) (by omega) ≫
            (K.shiftFunctorObjXIso a q (q + a) rfl).inv
      let g : H ⟶ T⟦b - a⟧ :=
        (shiftFunctorCompIsoId _ (a - b) (b - a) (by omega)).inv.app H ≫ e.hom⟦b - a⟧'
      (∀ (n : ℤ) (z : Cochain M K n),
        (T.shiftFunctorObjXIso (b - a) n (n + (b - a)) rfl).hom.hom ((g.f n).hom z) =
          (n * b).negOnePow • reindex n z) ∧
      (∀ (n : ℤ) (z : Cochain M K n),
        (T.shiftFunctorObjXIso (b - a) (n + 1) (n + 1 + (b - a)) rfl).hom.hom
            (((T⟦b - a⟧).d n (n + 1)).hom
              ((T.shiftFunctorObjXIso (b - a) n (n + (b - a)) rfl).inv.hom
                (reindex n z))) =
          b.negOnePow • reindex (n + 1) (δ n (n + 1) z)) } := by
  let H := CochainComplex.HomComplexR R M K
  let T := CochainComplex.HomComplexR R (M⟦b⟧) (K⟦a⟧)
  let e : H⟦a - b⟧ ≅ T :=
    (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat R) ℤ) (a - b)).mapIso
      (shiftedIso R M K a b) ≪≫
        (shiftFunctorCompIsoId _ (b - a) (a - b) (by omega)).app T
  refine ⟨e, ?_, ?_⟩
  · intro n z
    have hs : (T.shiftFunctorObjXIso (b - a) n (n + (b - a)) rfl).hom.hom
        ((((shiftFunctorCompIsoId _ (a - b) (b - a) (by omega)).inv.app H ≫
          e.hom⟦b - a⟧').f n).hom z) = signedReindexEquiv R M K a b n z := by
      simp only [e, shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
        Iso.symm_inv, NatTrans.comp_app, Iso.app_hom,
        HomologicalComplex.comp_f, Functor.map_comp, CochainComplex.shiftFunctor_map_f',
        CochainComplex.shiftFunctorAdd'_inv_app_f', CochainComplex.shiftFunctorAdd'_hom_app_f',
        CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorZero_hom_app_f,
        CochainComplex.shiftFunctorObjXIso]
      simp only [HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom]
      exact signedReindexEquiv_XIsoOfEq R M K a b n _ (by omega) _ z
    refine hs.trans ?_
    change (n * b).negOnePow • reindexEquiv R M K a b n z = _
    rw [reindexEquiv_apply]
  · intro n z
    have hd : (b - a).negOnePow •
          δ (n + (b - a)) (n + 1 + (b - a)) (reindexEquiv R M K a b n z) =
        b.negOnePow • reindexEquiv R M K a b (n + 1) (δ n (n + 1) z) := by
      rw [reindexEquiv_delta, smul_smul, ← Int.negOnePow_add]
      congr 1
      · congr 1
        ring
    have hs : (T.shiftFunctorObjXIso (b - a) (n + 1)
          (n + 1 + (b - a)) rfl).hom.hom
        (((T⟦b - a⟧).d n (n + 1)).hom
          ((T.shiftFunctorObjXIso (b - a) n (n + (b - a)) rfl).inv.hom
            (reindexEquiv R M K a b n z))) =
        b.negOnePow • reindexEquiv R M K a b (n + 1) (δ n (n + 1) z) := by
      simp only [← ModuleCat.comp_apply]
      change (b - a).negOnePow •
          δ (n + (b - a)) (n + 1 + (b - a)) (reindexEquiv R M K a b n z) = _
      exact hd
    simpa only [reindexEquiv_apply] using hs

end ShiftHom

end CochainComplex.HomComplex

end
