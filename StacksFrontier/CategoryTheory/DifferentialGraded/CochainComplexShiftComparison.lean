module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.RepresentableFunctor
public import StacksFrontier.CategoryTheory.DifferentialGraded.RepresentableShift

/-!
# The shift of the differential graded category of complexes, and `Hom(K, X[n]) ≅ Hom(K, X)[n]`

Mathlib's shift on cochain complexes provides the differential graded category
`CochainComplex.dgCategory B` of Tag 09L9 with the data of axiom (B) that the representable
differential graded module needs: a degree `k + n` cochain `K ⟶ X` is a degree `k` cochain
`K ⟶ X[n]`, by `CochainComplex.HomComplex.Cochain.rightShift`; this identification multiplies
the Hom differential by `(-1)^n`, which is
`CochainComplex.HomComplex.Cochain.δ_rightShift`, and it leaves composition on the right
untouched, since it only reindexes the target.

Feeding that data to `DGCategory.representableShiftIso` gives the shift comparison
`Hom(K, X[n]) ≅ Hom(K, X)[n]` of differential graded modules over the endomorphism algebra
`End(K)`, for every cochain complex `K`.

## Main definitions

* `CochainComplex.dgShiftComparisonData`: the shift data of axiom (B) for
  `CochainComplex.dgCategory B`.
* `CochainComplex.homShiftIso`: the comparison `Hom(K, X[n]) ≅ Hom(K, X)[n]`.

## Main results

* `CochainComplex.dgCategory_d'_eq`: the transported Hom differential of the differential graded
  category of complexes is Mathlib's `δ` at the transported degree.
* `CochainComplex.rightShift_comp_eq`: shifting the target of a composite shifts only its left
  factor.
* `CochainComplex.homShiftIso_hom_toFun_of`: the comparison is
  `CochainComplex.HomComplex.Cochain.rightUnshift` on each graded piece.
* `CochainComplex.rightUnshift_comp_ofHom`, `CochainComplex.rightUnshift_zero_eq` and
  `CochainComplex.rightUnshift_add_eq`: the three coherence identities of `rightUnshift` —
  naturality against the shift of a chain map, and compatibility with the comparisons of
  `CategoryTheory.shiftFunctorZero` and `CategoryTheory.shiftFunctorAdd`.
* `CochainComplex.homShiftIso_hom_toFun_repPostcomp`,
  `CochainComplex.homShiftIso_hom_toFun_zero` and `CochainComplex.homShiftIso_hom_toFun_add`: the
  same three identities for the comparison itself.

## Implementation notes

Only `DGCategory.ShiftComparisonData` is constructed, not a full `DGCategory.ShiftAxiomB`. The
latter demands that the shift be *strictly* additive on objects, `X[0] = X` and
`X[n + m] = X[n][m]` as equalities of cochain complexes, which Mathlib's shift is not: it
reindexes by `p + n`, so those equalities would have to be proved by transporting the whole
`HomologicalComplex` structure along `p + 0 = p` and `p + (n + m) = p + n + m`. The shift
comparison for `Hom(K, -)` uses none of that.

The ground ring is `ℤ`, so the `ℤ`-linear identification of Hom modules is Mathlib's additive
equivalence `CochainComplex.HomComplex.Cochain.rightShiftAddEquiv` read through
`AddEquiv.toIntLinearEquiv`.

## References

* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the differential graded
  category of complexes; [Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (B); and
  [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE), the representable differential graded
  module.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex

open CochainComplex.HomComplex

variable (B : Type u) [Category.{v} B] [Preadditive B]

/-- The transported Hom differential of the differential graded category of complexes is
Mathlib's `δ` at the transported degree. -/
theorem dgCategory_d'_eq {X Y : CochainComplex B ℤ} {m n : ℤ} (e : m + 1 = n)
    (f : (dgCategory B).Hom X Y m) : (dgCategory B).d' e f = δ m n f := by
  subst e
  rfl

/-- Shifting the target of a composite of cochains shifts only its left factor. -/
theorem rightShift_comp_eq {X Y Z : CochainComplex B ℤ} {l m n : ℤ}
    (g : Cochain Y Z (m + n)) (f : Cochain X Y l)
    (h : l + (m + n) = (m + l) + n) (h' : l + m = m + l) :
    (f.comp g h).rightShift n (m + l) (by omega) =
      f.comp (g.rightShift n m (by omega)) h' := by
  ext p q hpq
  rw [(f.comp g h).rightShift_v n (m + l) (by lia) p q hpq (p + ((m + l) + n)) (by lia),
    Cochain.comp_v f g h p (p + l) (p + ((m + l) + n)) rfl (by lia),
    Cochain.comp_v f (g.rightShift n m (by lia)) h' p (p + l) q rfl (by lia),
    g.rightShift_v n m (by lia) (p + l) q (by lia) (p + ((m + l) + n)) (by lia),
    Category.assoc]

/-- Two applications of the sign `(-1)^n` cancel. -/
theorem negOnePow_smul_cancel {W : Type*} [AddCommGroup W] [Module ℤ W] (n : ℤ)
    (w : W) : ((-1 : ℤ) ^ n.natAbs) • (n.negOnePow • w) = w := by
  have hn : ((n.negOnePow : ℤˣ) : ℤ) = (-1 : ℤ) ^ n.natAbs := by
    simpa only [Int.cast_id] using Int.coe_negOnePow ℤ n
  rw [Units.smul_def, hn, smul_smul, ← pow_add,
    show ((-1 : ℤ)) ^ (n.natAbs + n.natAbs) = 1 from Even.neg_one_pow ⟨n.natAbs, rfl⟩, one_smul]

/-- **Mathlib's shift supplies axiom (B)'s identification of Hom modules for the differential
graded category of complexes.** A degree `k + n` cochain `X ⟶ Y` is a degree `k` cochain
`X ⟶ Y[n]`; the identification multiplies the Hom differential by `(-1)^n` and leaves
composition on the right alone. -/
@[stacks 09P6 "axiom (B)'s identification of Hom complexes, for complexes"]
noncomputable def dgShiftComparisonData :
    DGCategory.ShiftComparisonData (dgCategory B) where
  obj := fun n X => (X⟦n⟧ : CochainComplex B ℤ)
  toShift := fun n X Y k =>
    (Cochain.rightShiftAddEquiv (X : CochainComplex B ℤ) (Y : CochainComplex B ℤ)
      (k + n) n k rfl).toIntLinearEquiv
  toShift_d := by
    intro n X Y k f
    change ((dgCategory B).d' (show (k + n) + 1 = (k + 1) + n by lia) f).rightShift
        n (k + 1) rfl = ((-1 : ℤ) ^ n.natAbs) • δ k (k + 1) (f.rightShift n k rfl)
    rw [dgCategory_d'_eq B (show (k + n) + 1 = (k + 1) + n by lia) f,
      Cochain.δ_rightShift f n k (k + 1) rfl ((k + 1) + n) rfl]
    exact (negOnePow_smul_cancel n _).symm
  toShift_comp_right := by
    intro n X Y Z l m g f
    exact rightShift_comp_eq B g f (by lia) (by lia)

variable {B}

/-- **The shift comparison for `Hom(K, -)`.** For a cochain complex `K` in a preadditive
category, the identification of a degree `k + n` cochain `K ⟶ X` with a degree `k` cochain
`K ⟶ X[n]` is an isomorphism `Hom(K, X[n]) ≅ Hom(K, X)[n]` of differential graded modules over
the endomorphism algebra `End(K)`. -/
@[stacks 09LE "the shift comparison for the representable differential graded module"]
noncomputable def homShiftIso (K : CochainComplex B ℤ) (n : ℤ) (X : CochainComplex B ℤ) :
    DGCategory.representableModule (dgCategory B) K (X⟦n⟧ : CochainComplex B ℤ) ≅
      (DGCategory.representableModule (dgCategory B) K X).shift n :=
  DGCategory.representableShiftIso (dgCategory B) K (dgShiftComparisonData B) n X

/-- The shift comparison on a graded piece: it sends a degree-`k` cochain `K ⟶ X[n]` to the
corresponding degree-`k + n` cochain `K ⟶ X`, which is
`CochainComplex.HomComplex.Cochain.rightUnshift`. -/
theorem homShiftIso_hom_toFun_of (K : CochainComplex B ℤ) (n : ℤ) (X : CochainComplex B ℤ)
    (k : ℤ) (f : (dgCategory B).Hom K (X⟦n⟧ : CochainComplex B ℤ) k) :
    (homShiftIso K n X).hom.toFun
        (DirectSum.of (DGCategory.repFamily (dgCategory B) K (X⟦n⟧ : CochainComplex B ℤ)) k f) =
      DirectSum.of (DGCategory.repFamily (dgCategory B) K X) (k + n)
        (Cochain.rightUnshift f (k + n) rfl) :=
  DGCategory.repShiftLinearEquiv_of (dgCategory B) K (dgShiftComparisonData B) n X k f

/-- The shift comparison on a graded piece, with the target degree `k' = k + n` given
explicitly. -/
theorem homShiftIso_hom_toFun_of' (K : CochainComplex B ℤ) (n : ℤ) (X : CochainComplex B ℤ)
    (k k' : ℤ) (hk : k + n = k') (f : (dgCategory B).Hom K (X⟦n⟧ : CochainComplex B ℤ) k) :
    (homShiftIso K n X).hom.toFun
        (DirectSum.of (DGCategory.repFamily (dgCategory B) K (X⟦n⟧ : CochainComplex B ℤ)) k f) =
      DirectSum.of (DGCategory.repFamily (dgCategory B) K X) k'
        (Cochain.rightUnshift f k' hk) := by
  subst hk
  exact homShiftIso_hom_toFun_of K n X k f

/-! ### The three coherence identities of `CochainComplex.HomComplex.Cochain.rightUnshift`

The shift comparison is `CochainComplex.HomComplex.Cochain.rightUnshift` on each graded piece, so
its naturality in the target and its compatibility with `CategoryTheory.shiftFunctorZero` and
`CategoryTheory.shiftFunctorAdd` are three identities between cochains, proved on components.
Each is sign-free: the Koszul sign of the identification of axiom (B) against composition on the
left is `(-1)^{n·m}` in the degree `m` of the left factor, and all three left factors here are
the degree-zero cochains of chain maps.
-/

/-- **Unshifting the target is natural in the target.** When the left factor of a composite is
the shift `φ[n]` of a chain map `φ`, unshifting the target of the composite unshifts the right
factor and replaces `φ[n]` by `φ`. -/
theorem rightUnshift_comp_ofHom {K X Y : CochainComplex B ℤ} (n : ℤ) (φ : X ⟶ Y)
    {k d m m' : ℤ} (f : Cochain K (X⟦n⟧) k) (hd : k + 0 = d) (hm : d + n = m)
    (hm' : k + n = m') (hmm : m' + 0 = m) :
    (f.comp (Cochain.ofHom (φ⟦n⟧')) hd).rightUnshift m hm =
      (f.rightUnshift m' hm').comp (Cochain.ofHom φ) hmm := by
  ext p q hpq
  obtain rfl : q = p + k + n := by lia
  rw [Cochain.rightUnshift_v _ m hm p _ hpq (p + k) (by lia),
    Cochain.comp_v f _ hd p (p + k) (p + k) rfl (by lia),
    Cochain.comp_v _ _ hmm p (p + k + n) (p + k + n) (by lia) (by lia),
    Cochain.rightUnshift_v f m' hm' p (p + k + n) (by lia) (p + k) rfl,
    Cochain.ofHom_v, Cochain.ofHom_v]
  simp

/-- **Unshifting by `0` is composition with the comparison of `CategoryTheory.shiftFunctorZero`.**
-/
theorem rightUnshift_zero_eq {K X : CochainComplex B ℤ} {k m : ℤ}
    (f : Cochain K (X⟦(0 : ℤ)⟧) k) (hm : k + 0 = m) :
    f.rightUnshift m hm =
      f.comp (Cochain.ofHom
        ((CategoryTheory.shiftFunctorZero (CochainComplex B ℤ) ℤ).hom.app X)) hm := by
  ext p q hpq
  obtain rfl : q = p + k := by lia
  rw [Cochain.rightUnshift_v f m hm p _ hpq (p + k) rfl,
    Cochain.comp_v f _ hm p (p + k) (p + k) rfl (by lia), Cochain.ofHom_v,
    shiftFunctorZero_hom_app_f]
  simp

/-- **Unshifting by `a + b` is unshifting by `b` and then by `a`**, after composing with the
comparison of `CategoryTheory.shiftFunctorAdd`. -/
theorem rightUnshift_add_eq {K X : CochainComplex B ℤ} (a b : ℤ) {k d db dba : ℤ}
    (f : Cochain K (X⟦a + b⟧) k) (hd : k + 0 = d) (hdb : d + b = db) (hdba : db + a = dba)
    (h : k + (a + b) = dba) :
    f.rightUnshift dba h =
      ((f.comp (Cochain.ofHom
            ((CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) a b).hom.app X :
              (X⟦a + b⟧ : CochainComplex B ℤ) ⟶ ((X⟦a⟧ : CochainComplex B ℤ)⟦b⟧)))
            hd).rightUnshift db hdb).rightUnshift dba hdba := by
  ext p q hpq
  obtain rfl : q = p + k + b + a := by lia
  rw [Cochain.rightUnshift_v _ dba hdba p _ hpq (p + k + b) (by lia),
    Cochain.rightUnshift_v _ db hdb p _ (by lia) (p + k) (by lia),
    Cochain.comp_v f _ hd p (p + k) (p + k) rfl (by lia), Cochain.ofHom_v,
    shiftFunctorAdd_hom_app_f, Cochain.rightUnshift_v f dba h p _ hpq (p + k) rfl]
  simp

/-! ### The same three identities for `CochainComplex.homShiftIso` -/

/-- Two linear maps out of `Hom(K, Y)` that agree on every homogeneous element agree. -/
private theorem repTotal_apply_eq_of_of {K Y : CochainComplex B ℤ} {M : Type*} [AddCommGroup M]
    [Module ℤ M] (F G : DGCategory.repTotal (dgCategory B) K Y →ₗ[ℤ] M)
    (h : ∀ (k : ℤ) (f : (dgCategory B).Hom K Y k),
      F (DirectSum.of (DGCategory.repFamily (dgCategory B) K Y) k f) =
        G (DirectSum.of (DGCategory.repFamily (dgCategory B) K Y) k f))
    (z : DGCategory.repTotal (dgCategory B) K Y) : F z = G z :=
  LinearMap.congr_fun (DirectSum.linearMap_ext _ fun k => LinearMap.ext (h k)) z

/-- **The shift comparison is natural in the target.** Postcomposing with the shift `φ[n]` of a
chain map and then comparing is comparing and then postcomposing with `φ`. This is the naturality
square of `CochainComplex.homShiftIso`, read on underlying maps. -/
theorem homShiftIso_hom_toFun_repPostcomp (K : CochainComplex B ℤ) (n : ℤ)
    {X Y : CochainComplex B ℤ} (φ : X ⟶ Y)
    (z : DGCategory.repTotal (dgCategory B) K (X⟦n⟧ : CochainComplex B ℤ)) :
    (homShiftIso K n Y).hom.toFun
        (DGCategory.repPostcomp (dgCategory B) K (Cochain.ofHom (φ⟦n⟧')) z) =
      DGCategory.repPostcomp (dgCategory B) K (Cochain.ofHom φ)
        ((homShiftIso K n X).hom.toFun z) := by
  simp only [← LinearMap.comp_apply]
  refine repTotal_apply_eq_of_of _ _ (fun k f => ?_) z
  dsimp only [LinearMap.comp_apply]
  rw [DGCategory.repPostcomp_of,
    homShiftIso_hom_toFun_of' K n Y (0 + k) (0 + (k + n)) (by lia),
    homShiftIso_hom_toFun_of' K n X k (k + n) rfl, DGCategory.repPostcomp_of]
  exact congrArg _ (rightUnshift_comp_ofHom n φ f (by lia) (by lia) rfl (by lia))

/-- **The shift comparison for `0` is the one built from `CategoryTheory.shiftFunctorZero`.** The
comparison of the target category is the identity on underlying maps, so only the comparison
`X[0] ≅ X` of complexes appears. -/
theorem homShiftIso_hom_toFun_zero (K X : CochainComplex B ℤ)
    (z : DGCategory.repTotal (dgCategory B) K (X⟦(0 : ℤ)⟧ : CochainComplex B ℤ)) :
    (homShiftIso K 0 X).hom.toFun z =
      DGCategory.repPostcomp (dgCategory B) K
        (Cochain.ofHom
          ((CategoryTheory.shiftFunctorZero (CochainComplex B ℤ) ℤ).hom.app X)) z := by
  refine repTotal_apply_eq_of_of _ _ (fun k f => ?_) z
  rw [homShiftIso_hom_toFun_of' K 0 X k (0 + k) (by lia), DGCategory.repPostcomp_of]
  exact congrArg _ (rightUnshift_zero_eq f (by lia))

/-- **The shift comparison for `a + b` is the composite of those for `a` and for `b`.** The
comparison of the target category is the identity on underlying maps, so only the comparison
`X[a + b] ≅ (X[a])[b]` of complexes appears. -/
theorem homShiftIso_hom_toFun_add (K X : CochainComplex B ℤ) (a b : ℤ)
    (z : DGCategory.repTotal (dgCategory B) K (X⟦a + b⟧ : CochainComplex B ℤ)) :
    (homShiftIso K (a + b) X).hom.toFun z =
      (homShiftIso K a X).hom.toFun
        ((homShiftIso K b (X⟦a⟧ : CochainComplex B ℤ)).hom.toFun
          (DGCategory.repPostcomp (dgCategory B) K
            (Cochain.ofHom
              ((CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) a b).hom.app X :
                (X⟦a + b⟧ : CochainComplex B ℤ) ⟶ ((X⟦a⟧ : CochainComplex B ℤ)⟦b⟧))) z)) := by
  simp only [← LinearMap.comp_apply]
  refine repTotal_apply_eq_of_of _ _ (fun k f => ?_) z
  dsimp only [LinearMap.comp_apply]
  rw [DGCategory.repPostcomp_of]
  simp only [Functor.comp_obj]
  rw [homShiftIso_hom_toFun_of' K b (X⟦a⟧ : CochainComplex B ℤ) (0 + k) (0 + k + b) rfl,
    homShiftIso_hom_toFun_of' K a X (0 + k + b) (0 + k + b + a) rfl,
    homShiftIso_hom_toFun_of' K (a + b) X k (0 + k + b + a) (by lia)]
  exact congrArg _ (rightUnshift_add_eq a b f (by lia) rfl rfl (by lia))

end CochainComplex
