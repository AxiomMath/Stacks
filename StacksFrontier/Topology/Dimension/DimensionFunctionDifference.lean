module

public import Mathlib.Topology.LocallyConstant.Basic
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# Two dimension functions differ by a locally constant function (Stacks 02IB)

Let `X` be a locally Noetherian sober topological space and let `δ, δ' : X → ℤ` be dimension
functions on `X`, in the sense of `TopologicalSpace.DimensionFunction`: both drop strictly along
non-trivial specializations and drop by exactly one along immediate specializations. This file
proves that `δ - δ'` is locally constant.

The argument has two halves. The first is purely order-theoretic: `δ - δ'` is *constant along
specializations*. Along an immediate specialization both functions drop by exactly one, so the
difference is unchanged; a general specialization `x ⤳ y` is bridged by finitely many immediate
ones, and induction on the gap `δ x - δ y` (a natural number, since `δ` drops strictly) reduces
to that case. The second half is topological: around any point `x₀` of a Noetherian sober open
set `U` there is an open `V ∋ x₀` such that every `y ∈ V` has a *common generalization* with
`x₀`, namely the generic point of an irreducible component of `U` containing both. It is
obtained by deleting from `U` the finitely many irreducible components that miss `x₀`. Combining
the two halves, `δ y - δ' y = δ η - δ' η = δ x₀ - δ' x₀` for every `y ∈ V`.

Sobriety is Mathlib's `QuasiSober` together with `T0Space`, and `IsLocallyNoetherianSpace` is
the topological local Noetherian condition. Both, along with `DimensionFunction` and
`IsImmediateSpecialization`, are taken from
`StacksFrontier.Topology.Dimension.DimensionFunctionCatenary` (tag 02IC) rather
than restated here, so that the two tags speak about literally the same notions.
-/

@[expose] public section

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- The difference of two dimension functions is unchanged along an immediate specialization,
because each of them drops by exactly one. -/
lemma DimensionFunction.sub_eq_of_isImmediateSpecialization (δ δ' : DimensionFunction X) {x y : X}
    (h : IsImmediateSpecialization x y) : δ x - δ' x = δ y - δ' y := by
  have h1 := δ.step_immediate h
  have h2 := δ'.step_immediate h
  omega

/-- Every non-trivial specialization `x ⤳ y` begins with an immediate one: there is a point `z`
such that `x ⤳ z` is an immediate specialization and `z ⤳ y`.

The proof is by induction on the gap `δ x - δ y`, which a dimension function makes a natural
number. Either `x ⤳ y` is already immediate, or some `z` with `x ⤳ z ⤳ y` differs from both
endpoints, and then the gap between `x` and `z` is strictly smaller. -/
lemma DimensionFunction.exists_isImmediateSpecialization (δ : DimensionFunction X) {x y : X}
    (hspec : x ⤳ y) (hne : x ≠ y) : ∃ z : X, IsImmediateSpecialization x z ∧ z ⤳ y := by
  suffices h :
    ∀ (n : ℕ) (y' : X),
      x ⤳ y' → x ≠ y' → (δ x - δ y').toNat ≤ n → ∃ z : X, IsImmediateSpecialization x z ∧ z ⤳ y'
    from h _ y hspec hne le_rfl
  intro n
  induction n with
  | zero =>
    intro y' hspec' hne' hle
    have := δ.strictAnti_specializes hspec' hne'
    omega
  | succ k ih =>
    intro y' hspec' hne' hle
    by_cases himm : ∀ z : X, x ⤳ z → z ⤳ y' → z = x ∨ z = y'
    · exact ⟨y', ⟨hspec', hne', himm⟩, specializes_refl y'⟩
    · push Not at himm
      obtain ⟨v, hxv, hvy, hvx, hvy'⟩ := himm
      have hv_gap : (δ x - δ v).toNat ≤ k := by
        have h1 : δ v < δ x := δ.strictAnti_specializes hxv (Ne.symm hvx)
        have h2 : δ y' < δ v := δ.strictAnti_specializes hvy hvy'
        omega
      obtain ⟨z, hz_imm, hz_v⟩ := ih v hxv (Ne.symm hvx) hv_gap
      exact ⟨z, hz_imm, hz_v.trans hvy⟩

/-- Induction on the gap `δ a - δ b` for the statement that `δ - δ'` is constant along
specializations. -/
private lemma DimensionFunction.sub_eq_of_specializes_aux (δ δ' : DimensionFunction X) (n : ℕ) :
    ∀ a b : X, a ⤳ b → a ≠ b → (δ a - δ b).toNat ≤ n → δ a - δ' a = δ b - δ' b := by
  induction n with
  | zero =>
    intro a b hab hne hle
    have := δ.strictAnti_specializes hab hne
    omega
  | succ k ih =>
    intro a b hab hne hle
    obtain ⟨z, himm, hzb⟩ := δ.exists_isImmediateSpecialization hab hne
    have hdiff : δ a - δ' a = δ z - δ' z := δ.sub_eq_of_isImmediateSpecialization δ' himm
    by_cases hze : z = b
    · subst hze; linarith
    · have hstep : δ a = δ z + 1 := δ.step_immediate himm
      have := δ.strictAnti_specializes hzb hze
      have hrec := ih z b hzb hze (by omega)
      linarith

/-- The difference of two dimension functions is constant along specializations: if `x ⤳ y`
then `δ x - δ' x = δ y - δ' y`. -/
lemma DimensionFunction.sub_eq_of_specializes (δ δ' : DimensionFunction X) {x y : X}
    (hspec : x ⤳ y) : δ x - δ' x = δ y - δ' y := by
  by_cases heq : x = y
  · subst heq; rfl
  · exact DimensionFunction.sub_eq_of_specializes_aux δ δ' _ x y hspec heq le_rfl

/-- In a Noetherian sober open subspace `U` of `X`, every point `x₀ ∈ U` has an open
neighbourhood `V ⊆ U` all of whose points admit a *common generalization* with `x₀`: for each
`y ∈ V` there is an `η ∈ U` with `η ⤳ x₀` and `η ⤳ y`.

Being Noetherian, `U` has finitely many irreducible components, each with a unique generic point
by sobriety (which open subspaces inherit). Deleting from `U` the components that miss `x₀` — a
finite union of closed subsets of `U` — leaves such a `V`: any `y ∈ V` lies in a component that
also contains `x₀`, and the generic point of that component specializes to both. -/
lemma noetherian_sober_common_specialization [QuasiSober X] [T0Space X] (U : Set X) (hU : IsOpen U)
    (hNS : NoetherianSpace U) (x₀ : X) (hx₀ : x₀ ∈ U) :
    ∃ V : Set X,
      IsOpen V ∧
        x₀ ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, ∃ η : X, η ∈ U ∧ Specializes η x₀ ∧ Specializes η y := by
  have hQS_U : QuasiSober U := (hU.isOpenEmbedding_subtypeVal).quasiSober
  have hfin : (irreducibleComponents U).Finite := NoetherianSpace.finite_irreducibleComponents
  set x₀U : U := ⟨x₀, hx₀⟩
  set bad := {C ∈ irreducibleComponents U | x₀U ∉ C}
  have hbad_fin : bad.Finite := hfin.subset (fun C hC => hC.1)
  have hbad_closed : IsClosed (⋃₀ bad : Set U) := by
    rw [Set.sUnion_eq_biUnion]
    exact hbad_fin.isClosed_biUnion (fun C hC => isClosed_of_mem_irreducibleComponents C hC.1)
  set goodU := (⋃₀ bad)ᶜ
  have hgoodU_open : IsOpen goodU := hbad_closed.isOpen_compl
  set V := Subtype.val '' goodU
  have hV_open : IsOpen V := (hU.isOpenEmbedding_subtypeVal).isOpenMap _ hgoodU_open
  have hV_sub_U : V ⊆ U := fun x ⟨⟨_, hm⟩, _, rfl⟩ => hm
  have hx₀_good : x₀U ∈ goodU := by
    intro h
    obtain ⟨C, hC, hx₀C⟩ := h
    exact hC.2 hx₀C
  have hx₀V : x₀ ∈ V := ⟨x₀U, hx₀_good, rfl⟩
  refine ⟨V, hV_open, hx₀V, hV_sub_U, ?_⟩
  intro y hy
  obtain ⟨yU, hyU_good, hyU_val⟩ := hy
  have hyU_mem : yU ∈ (⋃₀ irreducibleComponents U : Set U) := by
    rw [sUnion_irreducibleComponents]; exact Set.mem_univ _
  obtain ⟨C, hC_irr, hyU_in_C⟩ := hyU_mem
  have hC_not_bad : C ∉ bad := by
    intro hbad_mem
    exact hyU_good ⟨C, hbad_mem, hyU_in_C⟩
  have hx₀_in_C : x₀U ∈ C := by
    by_contra h
    exact hC_not_bad ⟨hC_irr, h⟩
  have hC_irred : IsIrreducible C := hC_irr.1
  have hC_closed : IsClosed C := isClosed_of_mem_irreducibleComponents C hC_irr
  obtain ⟨ηU, hηU_generic⟩ := QuasiSober.sober hC_irred hC_closed
  have hη_spec_x₀ : ηU ⤳ x₀U := hηU_generic.specializes hx₀_in_C
  have hη_spec_y : ηU ⤳ yU := hηU_generic.specializes hyU_in_C
  refine ⟨ηU.val, ηU.property, ?_, ?_⟩
  · exact (subtype_specializes_iff ηU x₀U).mp hη_spec_x₀
  · rw [← hyU_val]
    exact (subtype_specializes_iff ηU yU).mp hη_spec_y

/-- **Stacks 02IB.** On a locally Noetherian sober topological space `X`, the difference of two
dimension functions `δ, δ' : X → ℤ` is locally constant. -/
@[stacks 02IB]
theorem DimensionFunction.isLocallyConstant_sub [QuasiSober X] [T0Space X]
    (hX : IsLocallyNoetherianSpace X) (δ δ' : DimensionFunction X) :
    IsLocallyConstant (fun x : X => δ x - δ' x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x₀
  obtain ⟨U, hUopen, hx₀U, hNS⟩ := hX x₀
  obtain ⟨V, hVopen, hx₀V, _, hcommon⟩ :=
    noetherian_sober_common_specialization U hUopen hNS x₀ hx₀U
  refine ⟨V, hVopen, hx₀V, ?_⟩
  intro y hy
  obtain ⟨η, _, hηx₀, hηy⟩ := hcommon y hy
  have h1 := δ.sub_eq_of_specializes δ' hηx₀
  have h2 := δ.sub_eq_of_specializes δ' hηy
  linarith

end TopologicalSpace
