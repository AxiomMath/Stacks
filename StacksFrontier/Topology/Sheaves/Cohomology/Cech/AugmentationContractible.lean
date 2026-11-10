module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.Homotopy
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingAugmentation
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.OrderedComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Extended alternating and ordered Čech complexes are contractible

Let `F` be an abelian presheaf on a space `X`, let `U` be an open subset and let `V : I → Opens X`
be a family of open subsets all contained in `U`, one of which equals `U`. Augmenting the
alternating or the ordered Čech complex of `V` by the sections of `F` over `U` gives a complex
that is homotopy equivalent to zero.

## Main definitions

* `Stacks.Cech.orderedCechAugmentation`: the canonical augmentation of the ordered Čech
  complex.

## Main results

* `Stacks.Cech.alternatingCechComplex_augment_homotopyEquiv_zero_of_eq`: the extended
  alternating Čech complex is contractible.
* `Stacks.Cech.orderedCechComplex_augment_homotopyEquiv_zero_of_eq`: the same for the ordered
  Čech complex, for every linear order on the index type.

## Implementation notes

Mathlib's `CochainComplex.augment` shifts the grading up by one, putting the augmenting object
in degree zero; the augmenting object is taken in the universe of the cochain groups, which may
be larger than the universe of the values of `F`, hence the `ULift`. No covering hypothesis is
needed: containment of every member of the family in `U`, together with equality for one
member, is enough.

## References

* [Stacks Project, Tag 0G6T](https://stacks.math.columbia.edu/tag/0G6T)
* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FI](https://stacks.math.columbia.edu/tag/01FI)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
-/


@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Stacks.Cech

private lemma inter_cons_eq {X : TopCat.{u}} {I : Type v} {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (p : ℕ) (σ : Fin (p + 1) → I) :
    CechCochains.inter V (Fin.cons i σ) = CechCochains.inter V σ := by
  classical
  apply le_antisymm
  · simpa [CechCochains.inter] using
      (CechCochains.inter_le_omit V (Fin.cons i σ) (0 : Fin (p + 2)))
  · change (⨅ k : Fin (p + 1), V (σ k)) ≤
      ⨅ k : Fin (p + 2), V ((Fin.cons i σ : Fin (p + 2) → I) k)
    refine le_iInf fun k => ?_
    obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ
    · simpa only [Fin.cons_zero] using
        (iInf_le (fun j : Fin (p + 1) => V (σ j)) 0).trans
          ((hV (σ 0)).trans (le_of_eq hi.symm))
    · exact iInf_le (fun j : Fin (p + 1) => V (σ j)) k

private noncomputable def cechInsert (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U) (p : ℕ) :
    CechCochains.Cochain V F (p + 1) →+ CechCochains.Cochain V F p where
  toFun s σ := CechCochains.restr F (by
    exact le_of_eq (inter_cons_eq V hV i hi p σ).symm) (s (Fin.cons i σ))
  map_zero' := by funext σ; simp [CechCochains.Cochain.zero_apply]
  map_add' := by
    intro x y
    funext σ
    change CechCochains.restr F (le_of_eq (inter_cons_eq V hV i hi p σ).symm)
        ((x + y) (Fin.cons i σ)) =
      CechCochains.restr F (le_of_eq (inter_cons_eq V hV i hi p σ).symm)
          (x (Fin.cons i σ)) +
        CechCochains.restr F (le_of_eq (inter_cons_eq V hV i hi p σ).symm)
          (y (Fin.cons i σ))
    rw [CechCochains.Cochain.add_apply, map_add]

private lemma inter_singleton_eq {X : TopCat.{u}} {I : Type v}
    (V : I → Opens X) (i : I) :
    CechCochains.inter V (fun _ : Fin 1 => i) = V i := by
  simp [CechCochains.inter]

private noncomputable def cechZeroInsert (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X}
    (V : I → Opens X) (i : I) (hi : V i = U) :
    CechCochains.Cochain V F 0 →+ ULift.{v} (F.obj (op U) : Type w) where
  toFun s := ULift.up <| F.map
    (eqToHom (inter_singleton_eq V i |>.trans hi).symm).op (s (fun _ => i))
  map_zero' := by ext; simp
  map_add' := by intro x y; ext; simp [map_add]

private noncomputable def orderedInsert (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X} [LinearOrder I]
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U) (p : ℕ) :
    CechCochains.OrdCochain V F (p + 1) →+ CechCochains.OrdCochain V F p :=
  (CechCochains.pi V F p).comp <| (cechInsert X F V hV i hi p).comp (CechCochains.c V F (p + 1))


/-- Restricting the value of a cochain on equal index tuples is independent of the tuple. -/
private lemma restr_cochain_congr {X : TopCat.{u}} {F : TopCat.Presheaf Ab.{w} X} {I : Type v}
    {V : I → Opens X} {q : ℕ} (t : CechCochains.Cochain V F q) {W : Opens X}
    (f₁ f₂ : Fin (q + 1) → I) (hf : f₁ = f₂)
    (h₁ : W ≤ CechCochains.inter V f₁) (h₂ : W ≤ CechCochains.inter V f₂) :
    CechCochains.restr F h₁ (t f₁) = CechCochains.restr F h₂ (t f₂) := by
  subst hf
  rfl

/-- Restricting `s (Fin.cons i σ ∘ Fin.succ)` to the intersection for `σ` recovers `s σ`. -/
private lemma restr_cons_comp_succ {X : TopCat.{u}} {F : TopCat.Presheaf Ab.{w} X} {I : Type v}
    {V : I → Opens X} {p : ℕ} (s : CechCochains.Cochain V F p) (i : I) (σ : Fin (p + 1) → I)
    (h : CechCochains.inter V σ ≤ CechCochains.inter V (Fin.cons i σ ∘ Fin.succ)) :
    CechCochains.restr F h (s (Fin.cons i σ ∘ Fin.succ)) = s σ := by
  rw [restr_cochain_congr s _ σ (Fin.cons_comp_succ i σ) h le_rfl]
  unfold CechCochains.restr
  simp

private lemma cechInsert_d_succ (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (p : ℕ) (s : CechCochains.Cochain V F (p + 1)) :
    cechInsert X F V hV i hi (p + 1) (CechCochains.cechD V F (p + 1) s) +
        CechCochains.cechD V F p (cechInsert X F V hV i hi p s) = s := by
  classical
  funext σ
  change CechCochains.restr F
      (le_of_eq (inter_cons_eq V hV i hi (p + 1) σ).symm)
      (∑ j : Fin (p + 3), (-1 : ℤ) ^ (j : ℕ) •
        CechCochains.restr F (CechCochains.inter_le_omit V (Fin.cons i σ) j)
          (s ((Fin.cons i σ) ∘ j.succAbove))) +
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      CechCochains.restr F (CechCochains.inter_le_omit V σ j)
        (CechCochains.restr F (le_of_eq (inter_cons_eq V hV i hi p (σ ∘ j.succAbove)).symm)
          (s (Fin.cons i (σ ∘ j.succAbove)))) = s σ
  rw [map_sum]
  simp_rw [AddMonoidHom.map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero]
  simp_rw [CechCochains.restr_restr]
  have houter := le_of_eq (inter_cons_eq V hV i hi (p + 1) σ).symm
  have hinner : CechCochains.inter V (Fin.cons i σ) ≤
      CechCochains.inter V (Fin.cons i σ ∘ Fin.succ) := by
    simpa only [Fin.succAbove_zero] using
      CechCochains.inter_le_omit V (Fin.cons i σ) (0 : Fin (p + 3))
  have hval (x : Fin (p + 2)) :
      CechCochains.restr F
          (houter.trans (CechCochains.inter_le_omit V (Fin.cons i σ) x.succ))
          (s (Fin.cons i σ ∘ x.succ.succAbove)) =
        CechCochains.restr F
          ((CechCochains.inter_le_omit V σ x).trans
            (le_of_eq (inter_cons_eq V hV i hi p (σ ∘ x.succAbove)).symm))
          (s (Fin.cons i (σ ∘ x.succAbove))) := by
    apply restr_cochain_congr s _ _ ?_ _ _
    funext j
    obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
    · rfl
    · simp [Fin.succ_succAbove_succ]
  have hcancel :
      (∑ x : Fin (p + 2), (-1 : ℤ) ^ (x.succ : ℕ) •
          CechCochains.restr F
            (houter.trans (CechCochains.inter_le_omit V (Fin.cons i σ) x.succ))
            (s (Fin.cons i σ ∘ x.succ.succAbove))) +
        ∑ x : Fin (p + 2), (-1 : ℤ) ^ (x : ℕ) •
          CechCochains.restr F
            ((CechCochains.inter_le_omit V σ x).trans
              (le_of_eq (inter_cons_eq V hV i hi p (σ ∘ x.succAbove)).symm))
            (s (Fin.cons i (σ ∘ x.succAbove))) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hval x]
    have hsign : (-1 : ℤ) ^ (x.succ : ℕ) = -((-1 : ℤ) ^ (x : ℕ)) := by
      rw [Fin.val_succ, pow_succ]
      ring
    rw [hsign]
    simp [neg_smul]
  have hsplit : ∀ {M : Type w} [AddCommGroup M] (a b c t : M),
      a = t → b + c = 0 → a + b + c = t := by
    intro M _ a b c t ha hbc
    rw [ha, add_assoc, hbc, add_zero]
  exact hsplit _ _ _ _
    ((CechCochains.restr_restr _ _ _ _).trans (restr_cons_comp_succ s i σ _)) hcancel

private lemma cechZeroInsert_restrict (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (x : ULift.{v} (F.obj (op U) : Type w)) :
    cechZeroInsert X F V i hi (cechDegreeZeroRestriction X F V hV x) = x := by
  apply ULift.ext
  let e : CechCochains.inter V (fun _ : Fin 1 => i) = U :=
    (inter_singleton_eq V i).trans hi
  let hle : CechCochains.inter V (fun _ : Fin 1 => i) ≤ U := by
    simpa [CechCochains.inter] using hV i
  have hmap : eqToHom e.symm ≫ homOfLE hle = 𝟙 U :=
    Subsingleton.elim _ _
  change F.map (eqToHom e.symm).op
      ((cechDegreeZeroRestriction X F V hV x) (fun _ : Fin 1 => i)) = x.down
  have hsection : (cechDegreeZeroRestriction X F V hV x) (fun _ : Fin 1 => i) =
      F.map (homOfLE hle).op x.down := by
    dsimp [cechDegreeZeroRestriction, AddMonoidHom.pi, CechCochains.restr]
    have hproof :
        homOfLE (by simpa [CechCochains.inter] using hV i) = homOfLE hle :=
      Subsingleton.elim _ _
    rw [hproof]
    rfl
  rw [hsection]
  rw [← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp,
    hmap, op_id, F.map_id]
  rfl

private lemma cechInsert_degree_zero (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (s : CechCochains.Cochain V F 0) :
    cechInsert X F V hV i hi 0 (CechCochains.cechD V F 0 s) +
      cechDegreeZeroRestriction X F V hV
        (cechZeroInsert X F V i hi s) = s := by
  classical
  funext σ
  let τ : Fin 2 → I := Fin.cons i σ
  have htuple : τ ∘ Fin.succ = σ := by funext j; exact Fin.cons_comp_succ i σ ▸ rfl
  have htarget : CechCochains.inter V τ = CechCochains.inter V σ :=
    inter_cons_eq V hV i hi 0 σ
  let houter : CechCochains.inter V σ ≤ CechCochains.inter V τ := le_of_eq htarget.symm
  let hW : CechCochains.inter V σ ≤ U := by
    simpa [CechCochains.inter] using
      (iInf_le (fun j : Fin 1 => V (σ j)) 0).trans (hV (σ 0))
  have hface1 : τ ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 => i := by
    funext j
    fin_cases j; simp [τ]
  let e : CechCochains.inter V (fun _ : Fin 1 => i) = U :=
    (inter_singleton_eq V i).trans hi
  change CechCochains.restr F houter
      (∑ j : Fin 2, (-1 : ℤ) ^ (j : ℕ) •
        CechCochains.restr F (CechCochains.inter_le_omit V τ j)
          (s (τ ∘ j.succAbove))) +
    CechCochains.restr F hW
      (F.map (eqToHom e.symm).op (s (fun _ : Fin 1 => i))) = s σ
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    Fin.succAbove_zero, neg_one_smul]
  let f : Fin 1 → I := τ ∘ (1 : Fin 2).succAbove
  let g : Fin 1 → I := fun _ => i
  let hL : CechCochains.inter V σ ≤ CechCochains.inter V f :=
    houter.trans (CechCochains.inter_le_omit V τ 1)
  let hR : CechCochains.inter V σ ≤ CechCochains.inter V g :=
    hW.trans (le_of_eq e.symm)
  have hright : CechCochains.restr F hW
      (F.map (eqToHom e.symm).op (s g)) = CechCochains.restr F hR (s g) := by
    have heq : eqToHom e.symm = homOfLE (le_of_eq e.symm) := Subsingleton.elim _ _
    rw [heq]
    exact CechCochains.restr_restr (ℱ := F) (le_of_eq e.symm) hW (s g)
  have hface : CechCochains.restr F houter
      (CechCochains.restr F (CechCochains.inter_le_omit V τ 1) (s f)) =
      CechCochains.restr F hW
        (F.map (eqToHom e.symm).op (s g)) := by
    calc
      _ = CechCochains.restr F hL (s f) :=
        CechCochains.restr_restr (ℱ := F)
          (CechCochains.inter_le_omit V τ 1) houter (s f)
      _ = CechCochains.restr F hR (s g) := restr_cochain_congr s f g hface1 hL hR
      _ = _ := hright.symm
  have hface' : CechCochains.restr F houter
      (CechCochains.restr F (CechCochains.inter_le_omit V τ 1)
        (s (τ ∘ (1 : Fin 2).succAbove))) =
      CechCochains.restr F hW
        (F.map (eqToHom e.symm).op (s (fun _ : Fin 1 => i))) := by
    convert hface using 1
  have hzero' : CechCochains.restr F houter
      (CechCochains.restr F (by
        simpa only [Fin.succAbove_zero] using
          CechCochains.inter_le_omit V τ (0 : Fin 2))
        (s (τ ∘ Fin.succ))) = s σ := by
    exact (CechCochains.restr_restr (ℱ := F) _ houter _).trans (restr_cons_comp_succ s i σ _)
  calc
    _ = s σ + -(CechCochains.restr F houter
          (CechCochains.restr F (CechCochains.inter_le_omit V τ 1)
            (s (τ ∘ (1 : Fin 2).succAbove)))) +
          CechCochains.restr F hW
            (F.map (eqToHom e.symm).op (s (fun _ : Fin 1 => i))) := by
      simp only [map_add, map_neg]
      exact congrArg₂ (· + ·) (congrArg₂ (· + ·) hzero' rfl) rfl
    _ = s σ + -(CechCochains.restr F hW
          (F.map (eqToHom e.symm).op (s (fun _ : Fin 1 => i)))) +
          CechCochains.restr F hW
            (F.map (eqToHom e.symm).op (s (fun _ : Fin 1 => i))) := by rw [hface']
    _ = s σ := by abel

private noncomputable def orderedZeroInsert (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X} [LinearOrder I]
    (V : I → Opens X) (i : I) (hi : V i = U) :
    CechCochains.OrdCochain V F 0 →+ ULift.{v} (F.obj (op U) : Type w) := by
  classical
  let j : CechCochains.OrdIndex (I := I) 0 :=
    ⟨fun _ => i, by intro a b hab; fin_cases a; fin_cases b; simp at hab⟩
  exact {
    toFun := fun s => ULift.up <| F.map
      (eqToHom ((inter_singleton_eq V i).trans hi).symm).op (s j)
    map_zero' := by ext; simp
    map_add' := by intro x y; ext; simp [map_add] }

private lemma orderedZeroInsert_eq_cechZeroInsert (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X} [LinearOrder I]
    (V : I → Opens X) (i : I) (hi : V i = U)
    (s : CechCochains.OrdCochain V F 0) :
    orderedZeroInsert X F V i hi s = cechZeroInsert X F V i hi (CechCochains.c V F 0 s) := by
  apply ULift.ext
  classical
  let j : CechCochains.OrdIndex (I := I) 0 :=
    ⟨fun _ => i, by intro a b hab; fin_cases a; fin_cases b; simp at hab⟩
  change F.map (eqToHom ((inter_singleton_eq V i).trans hi).symm).op (s j) =
    F.map (eqToHom ((inter_singleton_eq V i).trans hi).symm).op
      ((CechCochains.c V F 0 s) (fun _ => i))
  rw [CechCochains.c_on_ord V F s j]

private lemma ordD_eq_pi_cechD_c (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I]
    (V : I → Opens X) (p : ℕ) (s : CechCochains.OrdCochain V F p) :
    CechCochains.ordD V F p s = CechCochains.pi V F (p + 1)
      (CechCochains.cechD V F p (CechCochains.c V F p s)) := by
  have h := congrArg (CechCochains.pi V F (p + 1)) (CechCochains.c_chainMap V F p s)
  simpa only [CechCochains.pi_c] using h

private lemma pi_cechD_c_pi (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I]
    (V : I → Opens X) (p : ℕ) (s : CechCochains.Cochain V F p) :
    CechCochains.pi V F (p + 1)
      (CechCochains.cechD V F p (CechCochains.c V F p (CechCochains.pi V F p s))) =
    CechCochains.pi V F (p + 1) (CechCochains.cechD V F p s) := by
  classical
  funext j
  change (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
      CechCochains.restr F (CechCochains.inter_le_omit V j.1 k)
        ((CechCochains.c V F p (CechCochains.pi V F p s)) (j.1 ∘ k.succAbove))) =
    ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
      CechCochains.restr F (CechCochains.inter_le_omit V j.1 k)
        (s (j.1 ∘ k.succAbove))
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [CechCochains.c_on_ord V F (CechCochains.pi V F p s)
    ⟨j.1 ∘ k.succAbove, CechCochains.strictMono_omit j.2 k⟩]
  change (-1 : ℤ) ^ (k : ℕ) • CechCochains.restr F
      (CechCochains.inter_le_omit V j.1 k) (s (j.1 ∘ k.succAbove)) =
    (-1 : ℤ) ^ (k : ℕ) • CechCochains.restr F
      (CechCochains.inter_le_omit V j.1 k) (s (j.1 ∘ k.succAbove))
  rfl

private lemma orderedInsert_d_succ (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X} [LinearOrder I]
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (p : ℕ) (s : CechCochains.OrdCochain V F (p + 1)) :
    orderedInsert X F V hV i hi (p + 1) (CechCochains.ordD V F (p + 1) s) +
      CechCochains.ordD V F p (orderedInsert X F V hV i hi p s) = s := by
  classical
  have htop := cechInsert_d_succ X F V hV i hi p (CechCochains.c V F (p + 1) s)
  change CechCochains.pi V F (p + 1)
      (cechInsert X F V hV i hi (p + 1)
        (CechCochains.c V F (p + 2) (CechCochains.ordD V F (p + 1) s))) +
      CechCochains.ordD V F p (orderedInsert X F V hV i hi p s) = s
  rw [CechCochains.c_chainMap]
  rw [ordD_eq_pi_cechD_c]
  simp only [orderedInsert, AddMonoidHom.comp_apply]
  rw [pi_cechD_c_pi]
  rw [← map_add, htop, CechCochains.pi_c]

private lemma orderedInsert_degree_zero (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X} [LinearOrder I]
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (s : CechCochains.OrdCochain V F 0) :
    orderedInsert X F V hV i hi 0 (CechCochains.ordD V F 0 s) +
      (CechCochains.pi V F 0).comp (cechDegreeZeroRestriction X F V hV)
        (orderedZeroInsert X F V i hi s) = s := by
  classical
  have htop := cechInsert_degree_zero X F V hV i hi (CechCochains.c V F 0 s)
  change CechCochains.pi V F 0
      (cechInsert X F V hV i hi 0
        (CechCochains.c V F 1 (CechCochains.ordD V F 0 s))) +
      CechCochains.pi V F 0
        (cechDegreeZeroRestriction X F V hV (orderedZeroInsert X F V i hi s)) = s
  rw [CechCochains.c_chainMap, orderedZeroInsert_eq_cechZeroInsert]
  rw [← map_add, htop, CechCochains.pi_c]

/-- The canonical augmentation from sections on `U` to ordered degree-zero Čech cochains. -/
noncomputable def orderedCechAugmentation (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ i, V i ≤ U) :
    AddCommGrpCat.of (ULift.{v} (F.obj (op U) : Type w)) ⟶
      (orderedCechComplex V F).X 0 :=
  AddCommGrpCat.ofHom <| (CechCochains.pi V F 0).comp (cechDegreeZeroRestriction X F V hV)

private lemma orderedAugmentation_d (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) :
    orderedCechAugmentation X F V hV ≫ (orderedCechComplex V F).d 0 1 = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change CechCochains.ordD V F 0
      (CechCochains.pi V F 0 (cechDegreeZeroRestriction X F V hV x)) = 0
  rw [ordD_eq_pi_cechD_c]
  rw [CechCochains.c_pi_of_isAlternating V F 0 _
    (cechDegreeZeroRestriction_isAlternating X F V hV x)]
  rw [cechDegreeZeroRestriction_d]
  simp

private lemma orderedZeroInsert_restrict (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (x : ULift.{v} (F.obj (op U) : Type w)) :
    orderedZeroInsert X F V i hi (orderedCechAugmentation X F V hV x) = x := by
  change orderedZeroInsert X F V i hi
      (CechCochains.pi V F 0 (cechDegreeZeroRestriction X F V hV x)) = x
  rw [orderedZeroInsert_eq_cechZeroInsert]
  rw [CechCochains.c_pi_of_isAlternating V F 0 _
    (cechDegreeZeroRestriction_isAlternating X F V hV x)]
  exact cechZeroInsert_restrict X F V hV i hi x

private noncomputable def orderedAltDegreeIso (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I]
    (V : I → Opens X) (p : ℕ) :
    AddCommGrpCat.of (CechCochains.OrdCochain V F p) ≅
      AddCommGrpCat.of (CechCochains.alternatingSubgroup V F p) where
  hom := AddCommGrpCat.ofHom (CechCochains.cAddEquiv V F p).toAddMonoidHom
  inv := AddCommGrpCat.ofHom (CechCochains.cAddEquiv V F p).symm.toAddMonoidHom
  hom_inv_id := by ext x; simp
  inv_hom_id := by ext x; simp

private lemma orderedAugmentation_c (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) :
    orderedCechAugmentation X F V hV ≫ (orderedAltDegreeIso X F V 0).hom =
      alternatingCechAugmentation X F V hV :=
  AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x => Subtype.ext <|
    CechCochains.c_pi_of_isAlternating V F 0 _ (cechDegreeZeroRestriction_isAlternating X F V hV x)

private noncomputable def orderedAltAugIso (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U)
    (wO : orderedCechAugmentation X F V hV ≫
      (orderedCechComplex V F).d 0 1 = 0)
    (wA : alternatingCechAugmentation X F V hV ≫
      (alternatingCechComplex V F).d 0 1 = 0) :
    ((orderedCechComplex V F).augment
      (orderedCechAugmentation X F V hV) wO) ≅
    ((alternatingCechComplex V F).augment
      (alternatingCechAugmentation X F V hV) wA) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => match n with
      | 0 => eqToIso (by simp only [CochainComplex.augment_X_zero])
      | n + 1 => orderedAltDegreeIso X F V n)
    (by
      intro a b hab
      simp only [ComplexShape.up_Rel] at hab
      cases a with
      | zero =>
          cases b with
          | zero => simp at hab
          | succ b =>
              cases b with
              | zero =>
                  simpa [orderedAltDegreeIso] using
                    (orderedAugmentation_c X F V hV).symm
              | succ b => omega
      | succ a =>
          cases b with
          | zero => omega
          | succ b =>
              have hb : b = a + 1 := by omega
              subst b
              rw [CochainComplex.augment_d_succ_succ,
                CochainComplex.augment_d_succ_succ,
                orderedCechComplex_d,
                alternatingCechComplex_d]
              dsimp [orderedAltDegreeIso]
              apply AddCommGrpCat.hom_ext
              apply AddMonoidHom.ext
              intro s
              apply Subtype.ext
              change CechCochains.cechD V F a (CechCochains.c V F a s) =
                CechCochains.c V F (a + 1) (CechCochains.ordD V F a s)
              exact (CechCochains.c_chainMap V F a s).symm)



private noncomputable def orderedHom (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (w : orderedCechAugmentation X F V hV ≫
      (orderedCechComplex V F).d 0 1 = 0) (a b : ℕ) :
    (((orderedCechComplex V F).augment
      (orderedCechAugmentation X F V hV) w).X a ⟶
      ((orderedCechComplex V F).augment
        (orderedCechAugmentation X F V hV) w).X b) := by
  by_cases h : b + 1 = a
  · subst a
    cases b with
    | zero => exact AddCommGrpCat.ofHom (orderedZeroInsert X F V i hi)
    | succ n => exact AddCommGrpCat.ofHom (orderedInsert X F V hV i hi n)
  · exact 0

@[simp] private lemma orderedHom_zero_zero (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (w : orderedCechAugmentation X F V hV ≫
      (orderedCechComplex V F).d 0 1 = 0) :
    orderedHom X F V hV i hi w 0 0 = 0 := by
  simp [orderedHom]; rfl

@[simp] private lemma orderedHom_one_zero (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (w : orderedCechAugmentation X F V hV ≫
      (orderedCechComplex V F).d 0 1 = 0) :
    orderedHom X F V hV i hi w 1 0 =
      AddCommGrpCat.ofHom (orderedZeroInsert X F V i hi) := by
  simp [orderedHom]; rfl

@[simp] private lemma orderedHom_succ_succ (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (w : orderedCechAugmentation X F V hV ≫
      (orderedCechComplex V F).d 0 1 = 0) (n : ℕ) :
    orderedHom X F V hV i hi w (n + 2) (n + 1) =
      AddCommGrpCat.ofHom (orderedInsert X F V hV i hi n) := by
  unfold orderedHom
  rw [dite_eq_left (show n + 1 + 1 = n + 2 by omega)]

@[simp] private lemma orderedHom_zero_succ_zero (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (w : orderedCechAugmentation X F V hV ≫
      (orderedCechComplex V F).d 0 1 = 0) :
    orderedHom X F V hV i hi w (0 + 1) 0 =
      AddCommGrpCat.ofHom (orderedZeroInsert X F V i hi) := by
  simp

private noncomputable def orderedContraction (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} [LinearOrder I] {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) (i : I) (hi : V i = U)
    (w : orderedCechAugmentation X F V hV ≫
      (orderedCechComplex V F).d 0 1 = 0) :
    Homotopy (𝟙 ((orderedCechComplex V F).augment
        (orderedCechAugmentation X F V hV) w)) 0 where
  hom := orderedHom X F V hV i hi w
  zero a b h := by
    simp only [ComplexShape.up_Rel] at h
    unfold orderedHom
    split
    · rename_i he
      exact (h he).elim
    · rfl
  comm := by
    intro n
    cases n with
    | zero =>
        rw [Homotopy.dNext_cochainComplex,
          Homotopy.prevD_zero_cochainComplex]
        have hd : ((orderedCechComplex V F).augment
            (orderedCechAugmentation X F V hV) w).d 0 1 =
            orderedCechAugmentation X F V hV := rfl
        rw [hd, orderedHom_zero_succ_zero]
        simp only [add_zero]
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        change ULift.{v} (F.obj (op U) : Type w) at x
        change x = ((AddCommGrpCat.ofHom
          ((CechCochains.pi V F 0).comp (cechDegreeZeroRestriction X F V hV)) ≫
          AddCommGrpCat.ofHom (orderedZeroInsert X F V i hi) + 0).hom) x
        rw [AddCommGrpCat.hom_add]
        change x = ((orderedZeroInsert X F V i hi).comp
          ((CechCochains.pi V F 0).comp (cechDegreeZeroRestriction X F V hV)) + 0) x
        simp only [AddMonoidHom.comp_apply, add_zero]
        exact (orderedZeroInsert_restrict X F V hV i hi x).symm
    | succ n =>
        cases n with
        | zero =>
            rw [Homotopy.dNext_cochainComplex,
              Homotopy.prevD_succ_cochainComplex]
            rw [CochainComplex.augment_d_succ_succ,
              orderedHom_succ_succ, orderedHom_zero_succ_zero]
            have hd : ((orderedCechComplex V F).augment
                (orderedCechAugmentation X F V hV) w).d 0 1 =
                orderedCechAugmentation X F V hV := rfl
            rw [hd]
            simp only [HomologicalComplex.zero_f_apply, add_zero]
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro s
            change s = ((AddCommGrpCat.ofHom (CechCochains.ordD V F 0) ≫
                AddCommGrpCat.ofHom (orderedInsert X F V hV i hi 0)) +
              (AddCommGrpCat.ofHom (orderedZeroInsert X F V i hi) ≫
                AddCommGrpCat.ofHom
                  ((CechCochains.pi V F 0).comp
                    (cechDegreeZeroRestriction X F V hV)))).hom s
            rw [AddCommGrpCat.hom_add]
            change s = ((orderedInsert X F V hV i hi 0).comp
                (CechCochains.ordD V F 0) +
              ((CechCochains.pi V F 0).comp (cechDegreeZeroRestriction X F V hV)).comp
                (orderedZeroInsert X F V i hi)) s
            exact (orderedInsert_degree_zero X F V hV i hi s).symm
        | succ n =>
            rw [Homotopy.dNext_cochainComplex,
              Homotopy.prevD_succ_cochainComplex]
            have hH : orderedHom X F V hV i hi w (n + 1 + 1) (n + 1) =
                AddCommGrpCat.ofHom (orderedInsert X F V hV i hi n) := by
              convert orderedHom_succ_succ X F V hV i hi w n using 1
            have hH' : orderedHom X F V hV i hi w (n + 1 + 1 + 1) (n + 1 + 1) =
                AddCommGrpCat.ofHom (orderedInsert X F V hV i hi (n + 1)) := by
              convert orderedHom_succ_succ X F V hV i hi w (n + 1) using 1
            rw [hH, hH']
            have hd : ((orderedCechComplex V F).augment
                (orderedCechAugmentation X F V hV) w).d (n + 1) (n + 1 + 1) =
                (orderedCechComplex V F).d n (n + 1) := rfl
            have hdtop : ((orderedCechComplex V F).augment
                (orderedCechAugmentation X F V hV) w).d (n + 1 + 1) (n + 1 + 1 + 1) =
                (orderedCechComplex V F).d (n + 1) (n + 2) := rfl
            rw [hdtop, hd, orderedCechComplex_d]
            simp only [orderedCechComplex_d,
              HomologicalComplex.zero_f_apply, add_zero]
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro s
            change CechCochains.OrdCochain V F (n + 1) at s
            change s = ((orderedInsert X F V hV i hi (n + 1)).comp
                (CechCochains.ordD V F (n + 1)) +
              (CechCochains.ordD V F n).comp
                (orderedInsert X F V hV i hi n)) s
            exact (orderedInsert_d_succ X F V hV i hi n s).symm

/-- A complex whose identity is null-homotopic is homotopy equivalent to zero. -/
private lemma nonempty_homotopyEquiv_zero_of_homotopy {C : CochainComplex Ab.{w} ℕ}
    (h : Homotopy (𝟙 C) 0) :
    Nonempty (HomotopyEquiv C (HomologicalComplex.zero : CochainComplex Ab.{w} ℕ)) :=
  ⟨{ hom := 0
     inv := 0
     homotopyHomInvId := by simpa using h.symm
     homotopyInvHomId := Homotopy.ofEq (HomologicalComplex.isZero_zero.eq_of_src _ _) }⟩

/-- If a family of opens contained in `U` contains `U`, its extended alternating Čech complex is
homotopy equivalent to zero. -/
@[stacks 0G6T "alternating complex"]
lemma alternatingCechComplex_augment_homotopyEquiv_zero_of_eq
    (X : TopCat.{u}) (F : TopCat.Presheaf Ab.{w} X)
    {I : Type v} {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U)
    (i : I) (hi : V i = U) :
    ∃ (w : alternatingCechAugmentation X F V hV ≫
        (alternatingCechComplex V F).d 0 1 = 0),
      Nonempty (HomotopyEquiv
        ((alternatingCechComplex V F).augment
          (alternatingCechAugmentation X F V hV) w)
        (HomologicalComplex.zero : CochainComplex Ab.{max v w} ℕ)) :=
  by
    classical
    obtain ⟨order, _⟩ := exists_wellFoundedLT I
    let : LinearOrder I := order
    let wA := alternatingCechAugmentation_d X F V hV
    let wO := orderedAugmentation_d X F V hV
    let OA := orderedAltAugIso X F V hV wO wA
    let O := (orderedCechComplex V F).augment
      (orderedCechAugmentation X F V hV) wO
    let A := (alternatingCechComplex V F).augment
      (alternatingCechAugmentation X F V hV) wA
    obtain ⟨hO⟩ := nonempty_homotopyEquiv_zero_of_homotopy
      (orderedContraction X F V hV i hi wO)
    refine ⟨wA, ⟨?_⟩⟩
    simpa [A, O] using (HomotopyEquiv.ofIso OA.symm).trans hO

/-- For any ordering, if a family of opens contained in `U` contains `U`, its extended ordered
Čech complex is homotopy equivalent to zero. -/
@[stacks 0G6T "ordered complex"]
lemma orderedCechComplex_augment_homotopyEquiv_zero_of_eq
    (X : TopCat.{u}) (F : TopCat.Presheaf Ab.{w} X)
    {I : Type v} [LinearOrder I] {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U)
    (i : I) (hi : V i = U) :
    ∃ (w : orderedCechAugmentation X F V hV ≫
        (orderedCechComplex V F).d 0 1 = 0),
      Nonempty (HomotopyEquiv
        ((orderedCechComplex V F).augment
          (orderedCechAugmentation X F V hV) w)
        (HomologicalComplex.zero : CochainComplex Ab.{max v w} ℕ)) :=
  by
    let w := orderedAugmentation_d X F V hV
    refine ⟨w, ⟨?_⟩⟩
    exact (nonempty_homotopyEquiv_zero_of_homotopy (orderedContraction X F V hV i hi w)).some

end Stacks.Cech
