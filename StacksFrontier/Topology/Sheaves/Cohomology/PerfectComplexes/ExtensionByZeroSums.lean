module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ExtensionByZeroGenerator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductLocalFiniteSumLarge
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TotalComplexLocalSections

/-!
# Local sections of a sum of extensions by zero of the structure sheaf

For a family of opens `U_α` of a space `T` with a sheaf of rings `O`, a section of a sum
`⊕_α j_{U_α!} O_{U_α}` is, near each point `y`, a finite `O`-linear combination of the generators
of the summands whose opens contain `y`; the same holds for finitely many sections at once.

## Main results

* `Stacks.Cohomology.LeftDualPerfect.exists_nhd_eq_sum_elemSec`
* `Stacks.Cohomology.LeftDualPerfect.exists_nhd_inSpan_finset`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite ExtensionByZeroModules

universe u

namespace Stacks.Cohomology.LeftDualPerfect

variable {T : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u})
  {I : Type u} (U : I → Opens T) (c : Cofan fun α => extUnit O (U α))

/-- The section of a sum `⊕_α j_{U_α!} O_{U_α}` given by the generator of the summand `α`,
over an open inside `U_α`. -/
abbrev elemSec (α : I) {Z : Opens T} (hZ : Z ≤ imTop (U α)) : c.pt.val.obj (op Z) :=
  (c.inj α).val.app (op Z) (resS (extUnit O (U α)) hZ (extGen O (U α)))

theorem resS_sum {S' : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (M : SheafOfModules.{u} S') {V' V : Opens T} (h : V' ≤ V) {ι : Type*} (s : Finset ι)
    (f : ι → M.val.obj (op V)) : resS M h (∑ i ∈ s, f i) = ∑ i ∈ s, resS M h (f i) :=
  map_sum _ _ _

theorem resS_app {S' : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    {M N : SheafOfModules.{u} S'} (φ : M ⟶ N) {V' V : Opens T} (h : V' ≤ V)
    (x : M.val.obj (op V)) : resS N h (φ.val.app (op V) x) = φ.val.app (op V') (resS M h x) :=
  (PresheafOfModules.naturality_apply φ.val (homOfLE h).op x).symm

theorem resS_elemSec (α : I) {Z' Z : Opens T} (h : Z' ≤ Z) (hZ : Z ≤ imTop (U α)) :
    resS c.pt h (elemSec O U c α hZ) = elemSec O U c α (h.trans hZ) := by
  rw [elemSec, resS, ← PresheafOfModules.naturality_apply, ← resS, resS_resS]

/-- **A section of a sum of extensions by zero of structure sheaves is, near each point, a
finite combination of the generators of the summands whose opens contain the point.** -/
theorem exists_nhd_eq_sum_elemSec (hc : IsColimit c) {V : Opens T} (s : c.pt.val.obj (op V))
    (y : T) (hy : y ∈ V) :
    ∃ (Z : Opens T) (hZ : Z ≤ V), y ∈ Z ∧ ∃ (S : Finset I) (hS : ∀ α ∈ S, Z ≤ imTop (U α))
      (coef : I → O.obj.obj (op Z)),
        resS c.pt hZ s = ∑ α ∈ S.attach, coef α • elemSec O U c α (hS α.1 α.2) := by
  classical
  obtain ⟨Sv, hSv, hsum⟩ :=
    Stacks.SheafOfModules.CoproductSheafificationLarge.exists_sieve_sum_inj_of_isColimit O
      (fun α => extUnit O (U α)) hc s
  obtain ⟨Z₁, g, hg, hyZ₁⟩ := hSv y hy
  obtain ⟨S₀, yv₀, hyv⟩ := hsum g hg
  let yv : ∀ α, (extUnit O (U α)).val.obj (op Z₁) := yv₀
  have hyv' : resS c.pt (leOfHom g) s = ∑ α ∈ S₀, (c.inj α).val.app (op Z₁) (yv α) := hyv
  have key : ∀ α, ∃ (Zα : Opens T) (h : Zα ≤ Z₁), y ∈ Zα ∧ (y ∈ U α → Zα ≤ imTop (U α)) ∧
      (y ∉ U α → resS _ h (yv α) = 0) := by
    intro α
    by_cases hα : y ∈ U α
    · exact ⟨Z₁ ⊓ U α, inf_le_left, ⟨hyZ₁, hα⟩, fun _ => inf_le_right.trans (imTop_eq _).ge,
        fun h => absurd hα h⟩
    · obtain ⟨Z', h, hy', h0⟩ := exists_resS_eq_zero_of_not_mem O (U α) (yv α) y hyZ₁ hα
      exact ⟨Z', h, hy', fun h' => absurd h' hα, fun _ => h0⟩
  choose Zα hZα₁ hyα hin hout using key
  let Z : Opens T := Z₁ ⊓ S₀.inf Zα
  have hZ₁ : Z ≤ Z₁ := inf_le_left
  have hZα : ∀ α ∈ S₀, Z ≤ Zα α := fun α hα => inf_le_right.trans (Finset.inf_le hα)
  have hyZ : y ∈ Z := ⟨hyZ₁, mem_finset_inf_opens _ _ _ fun α _ => hyα α⟩
  let S := S₀.filter fun α => y ∈ U α
  have hS : ∀ α ∈ S, Z ≤ imTop (U α) := fun α hα =>
    (hZα α (Finset.mem_filter.1 hα).1).trans (hin α (Finset.mem_filter.1 hα).2)
  have hcoef : ∀ α, ∃ e : O.obj.obj (op Z), ∀ hα : α ∈ S,
      resS _ hZ₁ (yv α) = e • resS (extUnit O (U α)) (hS α hα) (extGen O (U α)) := by
    intro α
    by_cases hα : α ∈ S
    · obtain ⟨e, he⟩ := exists_eq_smul_res_extGen O (U α) (hS α hα) (resS _ hZ₁ (yv α))
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hα⟩
  choose coef hcoef using hcoef
  refine ⟨Z, hZ₁.trans (leOfHom g), hyZ, S, hS, coef, ?_⟩
  rw [← resS_resS _ hZ₁ (leOfHom g), hyv', resS_sum,
    ← Finset.sum_filter_add_sum_filter_not S₀ (fun α => y ∈ U α)]
  have h0 : ∑ α ∈ S₀.filter (fun α => ¬ y ∈ U α),
      resS c.pt hZ₁ ((c.inj α).val.app (op Z₁) (yv α)) = 0 := by
    refine Finset.sum_eq_zero fun α hα => ?_
    obtain ⟨hα₀, hαU⟩ := Finset.mem_filter.1 hα
    rw [resS_app, ← resS_resS _ (hZα α hα₀) (hZα₁ α), hout α hαU, resS_zero, map_zero]
  rw [h0, add_zero, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [resS_app, hcoef α.1 α.2, map_smul]

open Classical in
/-- The generator of the summand `α` over `Z`, and zero when `Z` is not inside `U_α`. -/
def elemSecD (α : I) (Z : Opens T) : c.pt.val.obj (op Z) :=
  if h : Z ≤ imTop (U α) then elemSec O U c α h else 0

theorem elemSecD_of_le (α : I) {Z : Opens T} (h : Z ≤ imTop (U α)) :
    elemSecD O U c α Z = elemSec O U c α h := dite_eq_left h

theorem resS_elemSecD (α : I) {Z' Z : Opens T} (h : Z' ≤ Z) (hZ : Z ≤ imTop (U α)) :
    resS c.pt h (elemSecD O U c α Z) = elemSecD O U c α Z' := by
  rw [elemSecD_of_le O U c α hZ, elemSecD_of_le O U c α (h.trans hZ), resS_elemSec]

/-- A section over `Z` is an `O(Z)`-combination of the generators of the summands in `S`, all
of whose opens contain `Z`. -/
def InSpan (Z : Opens T) (S : Finset I) (x : c.pt.val.obj (op Z)) : Prop :=
  (∀ α ∈ S, Z ≤ imTop (U α)) ∧
    ∃ coef : I → O.obj.obj (op Z), x = ∑ α ∈ S, coef α • elemSecD O U c α Z

theorem InSpan.mono {Z : Opens T} {S S' : Finset I} {x : c.pt.val.obj (op Z)}
    (hx : InSpan O U c Z S x) (hSS : S ⊆ S') (hS' : ∀ α ∈ S', Z ≤ imTop (U α)) :
    InSpan O U c Z S' x := by
  classical
  obtain ⟨-, coef, hcoef⟩ := hx
  refine ⟨hS', fun α => if α ∈ S then coef α else 0, ?_⟩
  rw [hcoef, ← Finset.sum_subset hSS (fun α _ hα => by simp [hα])]
  exact Finset.sum_congr rfl fun α hα => by simp [hα]

theorem InSpan.res {Z' Z : Opens T} (h : Z' ≤ Z) {S : Finset I} {x : c.pt.val.obj (op Z)}
    (hx : InSpan O U c Z S x) : InSpan O U c Z' S (resS c.pt h x) := by
  obtain ⟨hS, coef, hcoef⟩ := hx
  refine ⟨fun α hα => h.trans (hS α hα), fun α => O.obj.map (homOfLE h).op (coef α), ?_⟩
  rw [hcoef, resS_sum]
  exact Finset.sum_congr rfl fun α hα => by rw [resS_smul, resS_elemSecD O U c α h (hS α hα)]

theorem inSpan_zero {Z : Opens T} {S : Finset I} (hS : ∀ α ∈ S, Z ≤ imTop (U α)) :
    InSpan O U c Z S 0 :=
  ⟨hS, fun _ => 0, by simp⟩

theorem exists_nhd_inSpan (hc : IsColimit c) {V : Opens T} (s : c.pt.val.obj (op V)) (y : T)
    (hy : y ∈ V) :
    ∃ (Z : Opens T) (hZ : Z ≤ V), y ∈ Z ∧ ∃ S : Finset I, InSpan O U c Z S (resS c.pt hZ s) := by
  obtain ⟨Z, hZ, hyZ, S, hS, coef, h⟩ := exists_nhd_eq_sum_elemSec O U c hc s y hy
  refine ⟨Z, hZ, hyZ, S, hS, coef, h.trans ?_⟩
  rw [← Finset.sum_attach S (fun α => coef α • elemSecD O U c α Z)]
  exact Finset.sum_congr rfl fun α _ => by rw [elemSecD_of_le O U c α (hS α.1 α.2)]

/-- **Finitely many sections of a sum of extensions by zero lie, near each point, in the span of
finitely many generators.** -/
theorem exists_nhd_inSpan_finset (hc : IsColimit c) {V : Opens T} {ι : Type*} (A : Finset ι)
    (s : ι → c.pt.val.obj (op V)) (y : T) (hy : y ∈ V) :
    ∃ (Z : Opens T) (hZ : Z ≤ V), y ∈ Z ∧ ∃ S : Finset I, (∀ α ∈ S, Z ≤ imTop (U α)) ∧
      ∀ i ∈ A, InSpan O U c Z S (resS c.pt hZ (s i)) := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨V, le_rfl, hy, ∅, by simp, by simp⟩
  | insert i A hi ih =>
    obtain ⟨Z, hZ, hyZ, S, hS, hA⟩ := ih
    obtain ⟨Z', hZ', hyZ', S', hS'⟩ := exists_nhd_inSpan O U c hc (resS c.pt hZ (s i)) y hyZ
    have hall : ∀ α ∈ S ∪ S', Z' ≤ imTop (U α) := by
      intro α hα
      rcases Finset.mem_union.1 hα with h | h
      · exact hZ'.trans (hS α h)
      · exact hS'.1 α h
    refine ⟨Z', hZ'.trans hZ, hyZ', S ∪ S', hall, fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · rw [← resS_resS]
      exact hS'.mono O U c Finset.subset_union_right hall
    · rw [← resS_resS]
      exact ((hA j hj).res O U c hZ').mono O U c Finset.subset_union_left hall

end Stacks.Cohomology.LeftDualPerfect
