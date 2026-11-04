module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.Data.Fin.Parity
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.GroupTheory.Perm.Fin
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingProjection
import StacksCore.Tactic.StacksAttribute

/-!
# The alternating and ordered Čech complexes of a family in a category

[Stacks, Tag 01FG] through [Stacks, Tag 01FK] build, from an abelian presheaf `ℱ` on a
topological space `X` and a family `U : I → Opens X` indexed by a totally ordered set, the
*alternating* and *ordered* Čech cochain groups and compare them with the full Čech cochain
groups.  This file carries that comparison over to a family `U : ι → C` of objects of an
arbitrary category with finite products and a presheaf `P : Cᵒᵖ ⥤ AddCommGrpCat` — the
setting of `StacksFrontier/CategoryTheory/Sites/CechComplex.lean`, in which the `p`-fold
intersection is the product `inter U t = ∏ a, U (t a)` and the restriction along a
reindexing is `interMap`.  Applied in a slice category `Over V` this is the alternating
Čech theory of a covering family `{U_i ⟶ V}` of an object of a site, the `p`-fold
intersection being the fibre product `U_{i_0} ×_V ⋯ ×_V U_{i_p}`.

## Main definitions

Everything lives in the namespace `Stacks.CategoryTheory.CechComplex.Alternating`.

* `tres` — restriction along a reindexing `φ : Fin m → Fin n` of a tuple, that is, the map
  `P(inter U (t ∘ φ)) ⟶ P(inter U t)` induced by `interMap`.
* `CechCochain`, `CechCochainOrd`, `CechCochainAlt` — the full, the ordered and the
  alternating Čech cochain groups of [Stacks, Tag 01FG], [Stacks, Tag 01FH] and
  [Stacks, Tag 01FI].
* `cechDiff`, `cechDiffOrd`, `cechDiffAlt` — their differentials.
* `cechComp` and `cechProj` — the comparison map `c` and the projection `π` of
  [Stacks, Tag 01FJ] and [Stacks, Tag 01FK].

## Main results

* `tres_id`, `tres_tres`, `tres_congr` — functoriality of the reindexing restrictions, and
  the fact that two reindexings equal as *functions* restrict the same way.
* `isSubterminal_inter` and `tres_congr_of_isSubterminal` — **if every member of the family
  is subterminal then two reindexings which agree only after composing with the tuple still
  restrict the same way.**
* `cechDiff_comp_cechDiff`, `cechDiffOrd_comp_cechDiffOrd` — the full and the ordered Čech
  cochains are complexes.  No subterminality is needed.
* `isAlt_cechComp`, `cechProj_comp_cechComp`, `cechComp_cechProj_of_isAlt` and
  `cechProjAltEquiv` — **[Stacks, Tag 01FJ] and [Stacks, Tag 01FK] (2), (3) for a family in
  an arbitrary category**: `c` lands in the alternating cochains, `π ∘ c = id`, `c ∘ π = id`
  on the alternating cochains, and hence `π : C^p_alt ≃+ C^p_ord` in each degree.  Again no
  subterminality is needed.
* `cechProj_comp_cechDiff` — [Stacks, Tag 01FK] (1), `π` commutes with the differentials.
* `cechDiff_mem_alt`, `cechDiffAlt` and `cechProjAlt_comp_cechDiffAlt` — **the differential
  preserves the alternating cochains, and `π` is an isomorphism of complexes onto the
  ordered complex.**  These, and only these, need the members of the family to be
  subterminal.

The homotopy equivalence of [Stacks, Tag 01FM] is not part of this file.

## References

* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FI](https://stacks.math.columbia.edu/tag/01FI)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01FK](https://stacks.math.columbia.edu/tag/01FK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v u

namespace Stacks.CategoryTheory.CechComplex.Alternating

noncomputable section

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} [LinearOrder ι]

/-! ### Restriction along a reindexing of a tuple -/

omit [LinearOrder ι] in
/-- **Restriction along a reindexing** `φ : Fin m → Fin n`: the map from the sections of `P`
over the intersection of the coarser tuple `t ∘ φ` to the sections over the intersection of
`t`, induced by the reindexing morphism `interMap U t φ`. -/
def tres (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) {m n : ℕ} (φ : Fin m → Fin n)
    (t : Fin n → ι) :
    (P.obj (op (inter U (t ∘ φ))) : Type w') →+ (P.obj (op (inter U t)) : Type w') :=
  (P.map (interMap U t φ).op).hom

omit [LinearOrder ι] in
/-- Restriction along the identity reindexing is the identity. -/
theorem tres_id (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) {n : ℕ} (t : Fin n → ι) :
    tres P U (id : Fin n → Fin n) t = AddMonoidHom.id (P.obj (op (inter U t))) := by
  show (P.map (interMap U t (id : Fin n → Fin n)).op).hom = AddMonoidHom.id _
  rw [interMap_id]
  exact congrArg AddCommGrpCat.Hom.hom (P.map_id _)

omit [LinearOrder ι] in
/-- Composing two reindexing restrictions is the restriction along the composite
reindexing, applied pointwise. -/
theorem tres_tres (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) {l m n : ℕ}
    (φ : Fin m → Fin n) (ψ : Fin l → Fin m) (t : Fin n → ι)
    (x : (P.obj (op (inter U (t ∘ φ ∘ ψ))) : Type w')) :
    tres P U φ t (tres P U ψ (t ∘ φ) x) = tres P U (φ ∘ ψ) t x := by
  simp only [tres, interMap_comp, op_comp, Functor.map_comp]
  rfl

omit [LinearOrder ι] in
/-- Two reindexings that are equal as functions restrict the same way, after transporting
the source section along the equality. -/
theorem tres_congr (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) {m n : ℕ}
    (φ ψ : Fin m → Fin n) (t : Fin n → ι) (h : φ = ψ)
    (x : (P.obj (op (inter U (t ∘ φ))) : Type w'))
    (y : (P.obj (op (inter U (t ∘ ψ))) : Type w')) (hxy : HEq x y) :
    tres P U φ t x = tres P U ψ t y := by
  subst h
  obtain rfl : x = y := eq_of_heq hxy
  rfl

omit [LinearOrder ι] in
/-- **An intersection of subterminal objects is subterminal.** -/
theorem isSubterminal_inter (U : ι → C) (hU : ∀ i, IsSubterminal (U i)) {n : ℕ}
    (t : Fin n → ι) : IsSubterminal (inter U t) :=
  fun _ _ _ => inter_hom_ext U fun a => hU (t a) _ _

omit [LinearOrder ι] in
/-- **If every member of the family is subterminal then two reindexings which agree only
after composing with the tuple restrict the same way.** -/
theorem tres_congr_of_isSubterminal (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C)
    (hU : ∀ i, IsSubterminal (U i)) {m n : ℕ} (φ ψ : Fin m → Fin n) (t : Fin n → ι)
    (h : t ∘ φ = t ∘ ψ)
    (x : (P.obj (op (inter U (t ∘ φ))) : Type w'))
    (y : (P.obj (op (inter U (t ∘ ψ))) : Type w')) (hxy : HEq x y) :
    tres P U φ t x = tres P U ψ t y := by
  have key : ∀ (r : Fin m → ι), t ∘ φ = r → ∀ (g : inter U t ⟶ inter U r)
      (z : (P.obj (op (inter U r)) : Type w')), HEq x z →
      tres P U φ t x = (P.map g.op).hom z := by
    intro r hr
    subst hr
    intro g z hz
    obtain rfl : x = z := eq_of_heq hz
    obtain rfl : g = interMap U t φ :=
      isSubterminal_inter U hU (t ∘ φ) g (interMap U t φ)
    rfl
  exact key (t ∘ ψ) h (interMap U t ψ) y hxy

/-- The Čech `p`-cochains:
`C^p(U, P) = prod_{(i_0,...,i_p)} P(U_{i_0...i_p})`. -/
@[ega "0 11.8.7" "more general"]
abbrev CechCochain (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) : Type _ :=
  ∀ t : Fin (p+1) → ι, (P.obj (op (inter U t)) : Type w')

/-- The Čech `p`-cochains form an abelian group, componentwise. -/
instance (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    AddCommGroup (Alternating.CechCochain P U p) := by
  unfold Alternating.CechCochain; infer_instance

/-- The ordered Čech `p`-cochains:
`C^p_ord(U, P) = prod_{i_0<...<i_p} P(U_{i_0...i_p})`. -/
@[ega "III 6.6.4"]
abbrev CechCochainOrd (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) : Type _ :=
  ∀ t : OrdTuple ι p, (P.obj (op (inter U t.1)) : Type w')

/-- The ordered Čech `p`-cochains form an abelian group, componentwise. -/
instance (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    AddCommGroup (Alternating.CechCochainOrd P U p) := by
  unfold Alternating.CechCochainOrd; infer_instance

/-- The Čech differential `d : C^p → C^{p+1}`,
`d(s)_t = sum_j (-1)^j s_{t∘δ_j}|_t`, where `δ_j = Fin.succAbove j` omits the `j`-th
index. -/
noncomputable def cechDiff (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    Alternating.CechCochain P U p →+ Alternating.CechCochain P U (p+1) where
  toFun s := fun t => ∑ j : Fin (p+2),
    (-1 : ℤ) ^ (j : ℕ) • tres P U (Fin.succAbove j) t (s (t ∘ Fin.succAbove j))
  map_zero' := by funext t; simp
  map_add' s₁ s₂ := by funext t; simp [Finset.sum_add_distrib]

/-- The ordered Čech differential `d : C^p_ord → C^{p+1}_ord`, given by the formula of
`cechDiff` (the faces of a strictly increasing tuple are strictly increasing). -/
noncomputable def cechDiffOrd (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    Alternating.CechCochainOrd P U p →+ Alternating.CechCochainOrd P U (p+1) where
  toFun s := fun t => ∑ j : Fin (p+2),
    (-1 : ℤ) ^ (j : ℕ) • tres P U (Fin.succAbove j) t.1 (s (t.face j))
  map_zero' := by funext t; simp
  map_add' s₁ s₂ := by funext t; simp [Finset.sum_add_distrib]

/-- The projection `π : C^• → C^•_ord`: forget all components except
those indexed by strictly increasing tuples. -/
def cechProj (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    Alternating.CechCochain P U p →+ Alternating.CechCochainOrd P U p where
  toFun s := fun t => s t.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The comparison map `c : C^•_ord → C^•`.  On a tuple `t`: `0` if `t`
repeats an index; otherwise `sgn(σ) • s_{sorted}`, where `σ = Tuple.sort t` sorts the
indices into strictly increasing order, the value of `s` at the sorted tuple `t ∘ σ`
being transported to `(P.obj (op (inter U t)) : Type w')` along the restriction `tres P U σ`. -/
noncomputable def cechComp (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    Alternating.CechCochainOrd P U p →+ Alternating.CechCochain P U p where
  toFun s := fun t =>
    if h : Function.Injective t then
      (Equiv.Perm.sign (Tuple.sort t) : ℤ) •
        tres P U (Tuple.sort t) t (s ⟨t ∘ Tuple.sort t, strictMono_comp_sort t h⟩)
    else 0
  map_zero' := by funext t; by_cases h : Function.Injective t <;> simp [h]
  map_add' s₁ s₂ := by
    funext t
    by_cases h : Function.Injective t
    · simp only [Pi.add_apply, dite_eq_left h, map_add, smul_add]
    · simp only [Pi.add_apply, dite_eq_right h, add_zero]

/-- The alternating Čech cochains, as an additive subgroup of all
cochains: those `s` that vanish on tuples with a repeated index and that are antisymmetric,
i.e. for every permutation `σ` of the `p+1` indices, transporting the `(t∘σ)`-component
along the restriction `tres P U σ` yields `sgn(σ)` times the `t`-component.  (Equivalently:
zero on tuples with a repeat, and transposing two entries negates the component.) -/
@[ega "0 11.8.7" "more general", ega "0 12.1.2" "partial"]
def CechCochainAlt (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    AddSubgroup (Alternating.CechCochain P U p) where
  carrier := {s | (∀ t : Fin (p+1) → ι, ¬ Function.Injective t → s t = 0) ∧
    (∀ (t : Fin (p+1) → ι) (σ : Equiv.Perm (Fin (p+1))),
      tres P U σ t (s (t ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • s t)}
  zero_mem' := ⟨fun t _ => rfl, fun t σ => by simp⟩
  add_mem' {a b} ha hb := by
    refine ⟨fun t ht => by rw [Pi.add_apply, ha.1 t ht, hb.1 t ht, add_zero], fun t σ => ?_⟩
    change tres P U σ t ((a + b) (t ∘ σ)) = _
    rw [Pi.add_apply, map_add, ha.2 t σ, hb.2 t σ, ← smul_add, ← Pi.add_apply]
  neg_mem' {a} ha := by
    refine ⟨fun t ht => by rw [Pi.neg_apply, ha.1 t ht, neg_zero], fun t σ => ?_⟩
    change tres P U σ t ((-a) (t ∘ σ)) = _
    rw [Pi.neg_apply, map_neg, ha.2 t σ, ← smul_neg, ← Pi.neg_apply]

/-- The alternating Čech `p`-cochains form an abelian group. -/
instance (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    AddCommGroup (Alternating.CechCochainAlt P U p) := by infer_instance

/-- Evaluation of the comparison map at an injective tuple. -/
private theorem cechComp_apply_of_injective (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) {p : ℕ}
    (s : Alternating.CechCochainOrd P U p) (t : Fin (p + 1) → ι) (h : Function.Injective t) :
    Alternating.cechComp P U p s t = (Equiv.Perm.sign (Tuple.sort t) : ℤ) •
      tres P U (Tuple.sort t) t (s ⟨t ∘ Tuple.sort t, strictMono_comp_sort t h⟩) :=
  by simp [Alternating.cechComp, h]

/-- The comparison map vanishes at a non-injective tuple. -/
private theorem cechComp_apply_of_not_injective (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C)
    {p : ℕ} (s : Alternating.CechCochainOrd P U p) (t : Fin (p + 1) → ι)
    (h : ¬ Function.Injective t) : Alternating.cechComp P U p s t = 0 :=
  by simp [Alternating.cechComp, h]


/-- The comparison map lands in the alternating cochains: `c(s)` is an alternating cochain for
every ordered cochain `s`. -/
theorem isAlt_cechComp (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ)
    (s : Alternating.CechCochainOrd P U p) :
    Alternating.cechComp P U p s ∈ Alternating.CechCochainAlt P U p := by
  refine ⟨fun t ht => cechComp_apply_of_not_injective P U s t ht, fun t τ => ?_⟩
  by_cases hinj : Function.Injective t
  · have hinj' : Function.Injective (t ∘ τ) := hinj.comp τ.injective
    rw [cechComp_apply_of_injective P U s _ hinj', cechComp_apply_of_injective P U s _ hinj,
      map_zsmul, sign_sort_comp_perm t τ hinj, mul_smul, tres_tres P U]
    have hfun : (⇑τ ∘ ⇑(Tuple.sort (t ∘ ⇑τ))) = ⇑(Tuple.sort t) := by
      rw [sort_comp_perm t τ hinj]
      funext i
      simp only [Function.comp_apply, Equiv.Perm.coe_mul, Equiv.Perm.coe_inv,
        Equiv.apply_symm_apply]
    congr 2
    exact tres_congr P U _ _ t hfun _ _ (congr_arg_heq s (Subtype.ext
      ((Function.comp_assoc _ _ _).trans (congrArg (t ∘ ·) hfun))))
  · have hinj' : ¬ Function.Injective (t ∘ τ) := fun hc => hinj (by
      simpa [Function.comp_assoc] using hc.comp τ⁻¹.injective)
    rw [cechComp_apply_of_not_injective P U s _ hinj', cechComp_apply_of_not_injective P U s _ hinj,
      map_zero, smul_zero]

/-- The comparison map regarded as a map into the alternating subgroup. -/
noncomputable def cechCompAlt (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    Alternating.CechCochainOrd P U p →+ Alternating.CechCochainAlt P U p :=
  (Alternating.cechComp P U p).codRestrict (Alternating.CechCochainAlt P U p)
    (Alternating.isAlt_cechComp P U p)

/-- The projection restricted to the alternating cochains, `π : C^•_alt → C^•_ord`. -/
def cechProjAlt (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    Alternating.CechCochainAlt P U p →+ Alternating.CechCochainOrd P U p :=
  (Alternating.cechProj P U p).comp (Alternating.CechCochainAlt P U p).subtype


/-- Composing the face maps in the two possible orders gives the same reindexing. -/
private theorem succAbove_comp_predAbove {n : ℕ} (k : Fin (n + 3)) (j : Fin (n + 2)) :
    Fin.succAbove (k.succAbove j) ∘ Fin.succAbove (j.predAbove k)
      = Fin.succAbove k ∘ Fin.succAbove j :=
  funext fun i => Fin.succAbove_succAbove_succAbove_predAbove k j i

/-- The double face sum of a family invariant under the face involution
`(k, j) ↦ (k.succAbove j, j.predAbove k)` vanishes. -/
private theorem sum_neg_one_pow_mul_smul_succAbove_eq_zero {M : Type*} [AddCommGroup M] {n : ℕ}
    (f : Fin (n + 3) → Fin (n + 2) → M)
    (hf : ∀ k j, f k j = f (k.succAbove j) (j.predAbove k)) :
    ∑ k : Fin (n + 3), ∑ j : Fin (n + 2),
      ((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (j : ℕ)) • f k j = 0 := by
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_involution
    (g := fun (x : Fin (n + 3) × Fin (n + 2)) _ => (x.1.succAbove x.2, x.2.predAbove x.1))
  · rintro ⟨k, j⟩ _
    simp only
    rw [hf k j, show ((-1 : ℤ) ^ (↑(k.succAbove j) : ℕ) * (-1 : ℤ) ^ (↑(j.predAbove k) : ℕ))
          = - ((-1 : ℤ) ^ (↑k : ℕ) * (-1 : ℤ) ^ (↑j : ℕ)) by
        rw [← pow_add, ← pow_add, Fin.neg_one_pow_succAbove_add_predAbove], neg_smul,
      add_neg_cancel]
  · rintro ⟨k, j⟩ _ _
    simp [Fin.succAbove_ne]
  · exact fun _ _ => Finset.mem_univ _
  · rintro ⟨k, j⟩ _
    simp only
    rw [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

omit [LinearOrder ι] in
/-- `d ∘ d = 0` for the full Cech complex, so `C^•(U, P)` is a complex. -/
theorem cechDiff_comp_cechDiff (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    (Alternating.cechDiff P U (p+1)).comp (Alternating.cechDiff P U p) = 0 := by
  ext s t
  show (Alternating.cechDiff P U (p+1)) ((Alternating.cechDiff P U p) s) t = 0
  show (∑ k : Fin (p+3), (-1 : ℤ) ^ (k : ℕ) •
      tres P U (Fin.succAbove k) t (((Alternating.cechDiff P U p) s) (t ∘ Fin.succAbove k))) = 0
  have hinner : ∀ k : Fin (p+3),
      (-1 : ℤ) ^ (k : ℕ) •
        tres P U (Fin.succAbove k) t (((Alternating.cechDiff P U p) s) (t ∘ Fin.succAbove k))
      = ∑ j : Fin (p+2),
        ((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (j : ℕ)) •
          tres P U (Fin.succAbove k ∘ Fin.succAbove j) t
            (s ((t ∘ Fin.succAbove k) ∘ Fin.succAbove j)) := by
    intro k
    show (-1 : ℤ) ^ (k : ℕ) •
        tres P U (Fin.succAbove k) t
          (∑ j : Fin (p+2), (-1 : ℤ) ^ (j : ℕ) •
            tres P U (Fin.succAbove j) (t ∘ Fin.succAbove k)
              ((t ∘ Fin.succAbove k) ∘ Fin.succAbove j |> s)) = _
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul, smul_smul, tres_tres P U]
  rw [Finset.sum_congr rfl (fun k _ => hinner k)]
  refine sum_neg_one_pow_mul_smul_succAbove_eq_zero
    (fun k j => tres P U (Fin.succAbove k ∘ Fin.succAbove j) t
      (s ((t ∘ Fin.succAbove k) ∘ Fin.succAbove j))) fun k j => ?_
  refine tres_congr P U _ _ t (succAbove_comp_predAbove k j).symm _ _ (congr_arg_heq s ?_)
  exact (congrArg (t ∘ ·) (succAbove_comp_predAbove k j)).symm

/-- `d ∘ d = 0` for the ordered Cech complex, so `C^•_ord(U, P)` is a complex. -/
theorem cechDiffOrd_comp_cechDiffOrd (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    (Alternating.cechDiffOrd P U (p+1)).comp (Alternating.cechDiffOrd P U p) = 0 := by
  ext s t
  show (Alternating.cechDiffOrd P U (p+1)) ((Alternating.cechDiffOrd P U p) s) t = 0
  show (∑ k : Fin (p+3), (-1:ℤ)^(k:ℕ) •
      tres P U (Fin.succAbove k) t.1 (((Alternating.cechDiffOrd P U p) s) (t.face k))) = 0
  have hinner : ∀ k : Fin (p+3),
      (-1:ℤ)^(k:ℕ) • tres P U (Fin.succAbove k) t.1 (((Alternating.cechDiffOrd P U p) s) (t.face k))
      = ∑ j : Fin (p+2), ((-1:ℤ)^(k:ℕ) * (-1:ℤ)^(j:ℕ)) •
          tres P U (Fin.succAbove k ∘ Fin.succAbove j) t.1 (s ((t.face k).face j)) := by
    intro k
    show (-1:ℤ)^(k:ℕ) • tres P U (Fin.succAbove k) t.1
        (∑ j : Fin (p+2), (-1:ℤ)^(j:ℕ) •
          tres P U (Fin.succAbove j) (t.face k).1 (s ((t.face k).face j))) = _
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul, smul_smul, tres_tres P U]
  rw [Finset.sum_congr rfl (fun k _ => hinner k)]
  refine sum_neg_one_pow_mul_smul_succAbove_eq_zero
    (fun k j => tres P U (Fin.succAbove k ∘ Fin.succAbove j) t.1 (s ((t.face k).face j)))
    fun k j => ?_
  refine tres_congr P U _ _ t.1 (succAbove_comp_predAbove k j).symm _ _ (congr_arg_heq s ?_)
  exact Subtype.ext (congrArg (t.1 ∘ ·) (succAbove_comp_predAbove k j)).symm

omit [LinearOrder ι] in
/-- If every member of the family is subterminal and `s` is an alternating cochain, then
`(d s)_t = 0` for every tuple `t` which is not injective. -/
theorem cechDiff_apply_eq_zero_of_not_injective (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C)
    (hU : ∀ i, IsSubterminal (U i)) (p : ℕ) (s : Alternating.CechCochain P U p)
    (hzero : ∀ t : Fin (p+1) → ι, ¬ Function.Injective t → s t = 0)
    (halt : ∀ (t : Fin (p+1) → ι) (σ : Equiv.Perm (Fin (p+1))),
      tres P U σ t (s (t ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • s t)
    (t : Fin (p+2) → ι) (ht : ¬ Function.Injective t) :
    Alternating.cechDiff P U p s t = 0 := by
  show (∑ j : Fin (p+2),
      (-1 : ℤ) ^ (j : ℕ) • tres P U (Fin.succAbove j) t (s (t ∘ Fin.succAbove j))) = 0
  set f : Fin (p+2) → (P.obj (op (inter U t)) : Type w') :=
    fun j => (-1 : ℤ) ^ (j : ℕ) • tres P U (Fin.succAbove j) t (s (t ∘ Fin.succAbove j))
    with hf
  have core : ∀ (a b : Fin (p+2)), a < b → t a = t b → (∑ j, f j) = 0 := by
    intro a b hlt hval
    have hab : a ≠ b := ne_of_lt hlt
    have hvanish : ∀ j ∈ (Finset.univ : Finset (Fin (p+2))), j ∉ ({a, b} : Finset (Fin (p+2))) →
        f j = 0 := by
      intro j _ hj
      have hja : a ≠ j := by
        rintro rfl; exact hj (Finset.mem_insert_self _ _)
      have hjb : b ≠ j := by
        rintro rfl; exact hj (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      obtain ⟨ka, hka⟩ := Fin.exists_succAbove_eq hja
      obtain ⟨kb, hkb⟩ := Fin.exists_succAbove_eq hjb
      have hkab : ka ≠ kb := by
        intro h; apply hab; rw [← hka, ← hkb, h]
      have hni : ¬ Function.Injective (t ∘ Fin.succAbove j) := by
        rw [Function.not_injective_iff]
        refine ⟨ka, kb, ?_, hkab⟩
        simp only [Function.comp_apply, hka, hkb]; exact hval
      have hz : s (t ∘ Fin.succAbove j) = 0 := hzero _ hni
      rw [hf]; simp only; rw [hz, map_zero, smul_zero]
    have hsum : (∑ j, f j) = f a + f b := by
      rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset (Fin (p+2)))) hvanish]
      rw [Finset.sum_pair hab]
    rw [hsum]
    set Φ : Equiv.Perm (Fin (p+2)) := a.cycleRange * Equiv.swap a b * (b.cycleRange)⁻¹ with hΦ
    have hΦ0 : Φ 0 = 0 := by
      rw [hΦ]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      have h1 : (b.cycleRange)⁻¹ 0 = b := by
        rw [← Fin.cycleRange_self b]; simp
      rw [h1, Equiv.swap_apply_right, Fin.cycleRange_self]
    have hΦne (y : Fin (p+2)) : Φ y ≠ 0 ↔ y ≠ 0 := Φ.injective.ne_iff' hΦ0
    set ρ : Equiv.Perm (Fin (p+1)) :=
      (⟨ fun x => ⟨x.succ, Fin.succ_ne_zero x⟩, fun y => y.1.pred y.2,
        fun x => by simp, fun y => by ext; simp ⟩ :
          Fin (p+1) ≃ {y : Fin (p+2) // y ≠ 0}).permCongr.symm (Φ.subtypePerm hΦne) with hρ
    have hsignρ : (Equiv.Perm.sign ρ : ℤ) = -((-1)^(a:ℕ) * (-1)^(b:ℕ)) := by
      have e12 : Equiv.Perm.sign ρ = Equiv.Perm.sign Φ := by
        rw [hρ, Equiv.permCongr_symm, Equiv.Perm.sign_permCongr]
        apply Equiv.Perm.sign_subtypePerm
        intro x hx h0
        subst h0
        exact hx hΦ0
      have e3 : Equiv.Perm.sign Φ
          = Equiv.Perm.sign a.cycleRange * Equiv.Perm.sign (Equiv.swap a b)
            * Equiv.Perm.sign (b.cycleRange)⁻¹ := by
        rw [hΦ, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul]
      rw [e12, e3, Fin.sign_cycleRange, Equiv.Perm.sign_swap hab,
        Equiv.Perm.sign_inv, Fin.sign_cycleRange]
      push_cast
      ring
    have hρsucc : ∀ x : Fin (p+1), (ρ x).succ = Φ (x.succ) := by
      intro x
      rw [hρ]
      simp only [Equiv.permCongr_symm, Equiv.permCongr_apply, Equiv.symm_symm,
        Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Equiv.Perm.subtypePerm_apply]
      rw [Fin.succ_pred]
    have htswap : ∀ y : Fin (p+2), t (Equiv.swap a b y) = t y := by
      intro y
      rcases eq_or_ne y a with rfl | hya
      · rw [Equiv.swap_apply_left]; exact hval.symm
      · rcases eq_or_ne y b with rfl | hyb
        · rw [Equiv.swap_apply_right]; exact hval
        · rw [Equiv.swap_apply_of_ne_of_ne hya hyb]
    have hfun : (t ∘ Fin.succAbove a) ∘ ρ = t ∘ Fin.succAbove b := by
      funext x
      simp only [Function.comp_apply]
      have hsa : Fin.succAbove a (ρ x) = a.cycleRange.symm (ρ x).succ := by
        rw [← Fin.cycleRange_succAbove a (ρ x)]; simp
      have hsb : Fin.succAbove b x = b.cycleRange.symm x.succ := by
        rw [← Fin.cycleRange_succAbove b x]; simp
      rw [hsa, hρsucc x, hΦ]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rw [Equiv.symm_apply_apply, hsb]
      show t (Equiv.swap a b ((b.cycleRange)⁻¹ x.succ)) = t ((b.cycleRange).symm x.succ)
      rw [htswap]
      rfl
    rw [hf]
    simp only
    set Xa := tres P U (Fin.succAbove a) t (s (t ∘ Fin.succAbove a)) with hXa
    have hH := halt (t ∘ Fin.succAbove a) ρ
    have hH2 : tres P U (Fin.succAbove a) t
          (tres P U (⇑ρ) (t ∘ Fin.succAbove a) (s ((t ∘ Fin.succAbove a) ∘ ⇑ρ)))
        = tres P U (Fin.succAbove a) t ((Equiv.Perm.sign ρ : ℤ) • s (t ∘ Fin.succAbove a)) := by
      rw [hH]
    rw [tres_tres P U, map_zsmul, ← hXa] at hH2
    have hYb : tres P U (Fin.succAbove b) t (s (t ∘ Fin.succAbove b))
        = (Equiv.Perm.sign ρ : ℤ) • Xa := by
      rw [← hH2]
      refine (tres_congr_of_isSubterminal P U hU (Fin.succAbove a ∘ ⇑ρ)
        (Fin.succAbove b) t ?_ _ _ ?_).symm
      · show t ∘ (Fin.succAbove a ∘ ⇑ρ) = t ∘ Fin.succAbove b
        rw [← Function.comp_assoc]; exact hfun
      · exact congr_arg_heq s hfun
    rw [hYb, smul_smul, hsignρ]
    have hbb : (-1 : ℤ) ^ (b : ℕ) * (-1 : ℤ) ^ (b : ℕ) = 1 := by
      rw [← mul_pow]; norm_num
    rw [show ((-1 : ℤ) ^ (b : ℕ) * -((-1)^(a:ℕ) * (-1)^(b:ℕ))) = -((-1)^(a:ℕ)) by
      have : (-1 : ℤ) ^ (b : ℕ) * -((-1)^(a:ℕ) * (-1)^(b:ℕ))
          = -((-1)^(a:ℕ) * ((-1)^(b:ℕ) * (-1)^(b:ℕ))) := by ring
      rw [this, hbb, mul_one]]
    rw [neg_smul, add_neg_cancel]
  obtain ⟨a, b, hval, hne⟩ := Function.not_injective_iff.mp ht
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact core a b hlt hval
  · exact core b a hgt hval.symm

omit [LinearOrder ι] in
/-- If the cochain `s` is antisymmetric then so is `d s`: for any tuple `t` and permutation `σ`,
`tres P U σ t ((d s)_{t∘σ}) = sgn σ • (d s)_t`. -/
theorem cechDiff_apply_perm (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ)
    (s : Alternating.CechCochain P U p)
    (halt : ∀ (t : Fin (p + 1) → ι) (σ : Equiv.Perm (Fin (p + 1))),
      tres P U σ t (s (t ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • s t)
    (t : Fin (p + 2) → ι) (σ : Equiv.Perm (Fin (p + 2))) :
    tres P U σ t ((Alternating.cechDiff P U p s) (t ∘ σ))
      = (Equiv.Perm.sign σ : ℤ) • (Alternating.cechDiff P U p s) t := by
  show tres P U σ t (∑ j : Fin (p+2),
      (-1 : ℤ) ^ (j : ℕ) • tres P U (Fin.succAbove j) (t ∘ σ) (s ((t ∘ σ) ∘ Fin.succAbove j)))
    = (Equiv.Perm.sign σ : ℤ) • ∑ j : Fin (p+2),
      (-1 : ℤ) ^ (j : ℕ) • tres P U (Fin.succAbove j) t (s (t ∘ Fin.succAbove j))
  rw [map_sum]
  set g : Fin (p+2) → (P.obj (op (inter U t)) : Type w') :=
    fun k => (-1 : ℤ) ^ (k : ℕ) • tres P U (Fin.succAbove k) t (s (t ∘ Fin.succAbove k)) with hg
  have hsummand : ∀ j : Fin (p+2),
      tres P U σ t ((-1 : ℤ) ^ (j : ℕ) •
          tres P U (Fin.succAbove j) (t ∘ σ) (s ((t ∘ σ) ∘ Fin.succAbove j)))
      = (Equiv.Perm.sign σ : ℤ) • g (σ j) := by
    intro j
    obtain ⟨σj, hfun, hsign⟩ := succAbove_perm_aux σ j
    have hcomp : (Fin.succAbove (σ j) ∘ σj) = (σ ∘ Fin.succAbove j) := by
      funext x; simp only [Function.comp_apply]; exact hfun x
    rw [map_zsmul, tres_tres P U]
    have harg : (t ∘ σ) ∘ Fin.succAbove j = (t ∘ Fin.succAbove (σ j)) ∘ σj := by
      rw [Function.comp_assoc, ← hcomp]; rfl
    have hbody : tres P U (σ ∘ Fin.succAbove j) t (s ((t ∘ σ) ∘ Fin.succAbove j))
        = (Equiv.Perm.sign σj : ℤ) •
            tres P U (Fin.succAbove (σ j)) t (s (t ∘ Fin.succAbove (σ j))) := by
      have step1 : tres P U (σ ∘ Fin.succAbove j) t (s ((t ∘ σ) ∘ Fin.succAbove j))
          = tres P U (Fin.succAbove (σ j) ∘ σj) t (s ((t ∘ Fin.succAbove (σ j)) ∘ σj)) := by
        refine tres_congr P U (σ ∘ Fin.succAbove j) (Fin.succAbove (σ j) ∘ σj) t ?_ _ _ ?_
        · exact hcomp.symm
        · have hsub : ((t ∘ σ) ∘ Fin.succAbove j) = ((t ∘ Fin.succAbove (σ j)) ∘ σj) := harg
          exact congr_arg_heq s hsub
      rw [step1, ← tres_tres P U, halt (t ∘ Fin.succAbove (σ j)) σj, map_zsmul]
    rw [hbody, smul_smul, hsign, hg]
    simp only
    rw [smul_smul]
    congr 1
    have hjj : (-1 : ℤ) ^ (j : ℕ) * (-1 : ℤ) ^ (j : ℕ) = 1 := by rw [← mul_pow]; norm_num
    have : (-1 : ℤ) ^ (j : ℕ) * ((-1) ^ ((σ j : Fin (p+2)) : ℕ) * (Equiv.Perm.sign σ : ℤ) *
        (-1) ^ (j : ℕ)) = ((-1 : ℤ) ^ (j : ℕ) * (-1) ^ (j : ℕ)) *
          ((-1) ^ ((σ j : Fin (p+2)) : ℕ) * (Equiv.Perm.sign σ : ℤ)) := by
      ring
    rw [this, hjj, one_mul]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hsummand j)]
  rw [← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp σ g

omit [LinearOrder ι] in
/-- The differential preserves the alternating subcomplex: `d` maps alternating cochains
to alternating cochains, so `C^•_alt(U, P)` is a subcomplex of `C^•(U, P)`. -/
theorem cechDiff_mem_alt (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C)
    (hU : ∀ i, IsSubterminal (U i)) (p : ℕ)
    (s : Alternating.CechCochain P U p) (hs : s ∈ Alternating.CechCochainAlt P U p) :
    Alternating.cechDiff P U p s ∈ Alternating.CechCochainAlt P U (p+1) := by
  obtain ⟨hzero, halt⟩ := hs
  refine ⟨?_, ?_⟩
  · intro t ht
    exact Alternating.cechDiff_apply_eq_zero_of_not_injective P U hU p s hzero halt t ht
  · intro t σ
    exact Alternating.cechDiff_apply_perm P U p s halt t σ

/-- The differential on the alternating subcomplex `d : C^p_alt → C^{p+1}_alt`. -/
noncomputable def cechDiffAlt (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C)
    (hU : ∀ i, IsSubterminal (U i)) (p : ℕ) :
    Alternating.CechCochainAlt P U p →+ Alternating.CechCochainAlt P U (p+1) :=
  ((Alternating.cechDiff P U p).comp (Alternating.CechCochainAlt P U p).subtype).codRestrict
    (Alternating.CechCochainAlt P U (p+1)) (fun s => Alternating.cechDiff_mem_alt P U hU p s.1 s.2)


/-- The projection `π : C^• → C^•_ord` is a morphism of complexes: it commutes with the
differentials, `π ∘ d = d ∘ π`. -/
@[stacks 01FK "(1)"]
theorem cechProj_comp_cechDiff (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    (Alternating.cechProj P U (p+1)).comp (Alternating.cechDiff P U p)
      = (Alternating.cechDiffOrd P U p).comp (Alternating.cechProj P U p) := by
  ext s t
  rfl

/-- `π` is a left inverse to the comparison map `c`: `π ∘ c = id` on the ordered cochains. -/
@[stacks 01FK "(3)"]
theorem cechProj_comp_cechComp (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    (Alternating.cechProj P U p).comp (Alternating.cechComp P U p) =
      AddMonoidHom.id (Alternating.CechCochainOrd P U p) := by
  ext s t
  show Alternating.cechComp P U p s t.1 = s t
  have hinj : Function.Injective t.1 := t.2.injective
  have hsort : Tuple.sort t.1 = Equiv.refl _ := Tuple.sort_eq_refl_iff_monotone.2 t.2.monotone
  rw [cechComp_apply_of_injective P U s _ hinj]
  have key : ∀ (σ : Equiv.Perm (Fin (p+1))), σ = Equiv.refl _ →
      ∀ (h : StrictMono (t.1 ∘ σ)),
      (Equiv.Perm.sign σ : ℤ) • tres P U (⇑σ) t.1 (s ⟨t.1 ∘ σ, h⟩) = s t := by
    intro σ hσ h
    subst hσ
    rw [Equiv.Perm.sign_refl, Units.val_one, one_smul]
    have e1 : tres P U (⇑(Equiv.refl (Fin (p+1))) : Fin (p+1) → Fin (p+1)) t.1
        = AddMonoidHom.id _ := tres_id P U t.1
    rw [e1]
    rfl
  exact key (Tuple.sort t.1) hsort (strictMono_comp_sort t.1 hinj)

/-- On the alternating cochains `c ∘ π = id`: an alternating cochain is determined by its
strictly increasing components. -/
theorem cechComp_cechProj_of_isAlt (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) {p : ℕ}
    (s : Alternating.CechCochain P U p) (hs : s ∈ Alternating.CechCochainAlt P U p) :
    Alternating.cechComp P U p (Alternating.cechProj P U p s) = s := by
  obtain ⟨hzero, halt⟩ := hs
  funext t
  show Alternating.cechComp P U p (Alternating.cechProj P U p s) t = s t
  by_cases hinj : Function.Injective t
  · rw [cechComp_apply_of_injective P U _ _ hinj]
    show (Equiv.Perm.sign (Tuple.sort t) : ℤ) •
        tres P U (Tuple.sort t) t (s (t ∘ Tuple.sort t)) = s t
    rw [halt t (Tuple.sort t), smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
      one_smul]
  · rw [cechComp_apply_of_not_injective P U _ _ hinj, (hzero t hinj).symm]

/-- The restriction of the projection to the alternating cochains, `π : C^•_alt → C^•_ord`,
is an *isomorphism* of abelian groups in each degree, with inverse the comparison map `c`. -/
@[stacks 01FK "(2)"]
noncomputable def cechProjAltEquiv (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C) (p : ℕ) :
    Alternating.CechCochainAlt P U p ≃+ Alternating.CechCochainOrd P U p where
  toFun := Alternating.cechProjAlt P U p
  invFun := Alternating.cechCompAlt P U p
  left_inv s := Subtype.ext (Alternating.cechComp_cechProj_of_isAlt P U s.1 s.2)
  right_inv s := DFunLike.congr_fun (Alternating.cechProj_comp_cechComp P U p) s
  map_add' a b := by rw [map_add]

/-- The isomorphism `π : C^•_alt → C^•_ord`
commutes with the differentials, hence is an isomorphism of complexes.  Equivalently, the
comparison map `c : C^•_ord → C^•_alt` is a morphism of complexes (`c ∘ d_ord = d_alt ∘ c`),
exhibiting `c` as the inverse morphism of complexes. -/
@[stacks 01FK "(2)"]
theorem cechProjAlt_comp_cechDiffAlt (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C)
    (hU : ∀ i, IsSubterminal (U i)) (p : ℕ) :
    (Alternating.cechProjAlt P U (p+1)).comp (Alternating.cechDiffAlt P U hU p)
      = (Alternating.cechDiffOrd P U p).comp (Alternating.cechProjAlt P U p) := by
  ext s t
  rfl

/-! ### The subterminality hypothesis in the lattice case -/

/-- **Every object of a thin category is subterminal.**  In particular every open subset of
a topological space is subterminal, as in the setting of [Stacks, Tag 01FK]. -/
theorem isSubterminal_of_isThin {L : Type*} [Category L] [Quiver.IsThin L] (A : L) :
    IsSubterminal A := fun _ _ _ => Subsingleton.elim _ _

end

end Stacks.CategoryTheory.CechComplex.Alternating

end
