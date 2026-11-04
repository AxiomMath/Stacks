module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.SetNotation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves on a basis and cofinal systems of coverings (Stacks 009L)

Let `B` be a family of subsets of `X` that is closed under intersection in the weak sense that
`U' ∩ U'' ∈ B` whenever `U', U'' ∈ B` are both contained in a common `U ∈ B`
(`Stacks.SheafOnBasis.ClosedUnderInter`). A *covering* of `U ∈ B` is an indexed family of
members of `B` contained in `U` whose union is exactly `U` (`Stacks.SheafOnBasis.Covering`), and a
choice `C U` of coverings for each `U ∈ B` is *cofinal* if every covering of `U` is refined by a
member of `C U` (`Stacks.SheafOnBasis.IsCofinalSystem`).

For a presheaf of sets `F` on `B` (`Stacks.SheafOnBasis.Presheaf`) there are then two sheaf
conditions. `Presheaf.IsSheaf` is the sheaf condition on a basis as the Stacks Project states it
(Tag 009H): gluing is demanded for *every* covering, and compatibility of a family `sᵢ` is tested
on every `W ∈ B` with `W ⊆ Uᵢ ∩ Uⱼ`, because `Uᵢ ∩ Uⱼ` itself need not belong to `B`.
`Presheaf.IsSheafOnCofinal` is the simplified condition of 009L: gluing is demanded only for the
coverings in `C U`, and compatibility is the single equation `sᵢ|_{Uᵢ ∩ Uⱼ} = sⱼ|_{Uᵢ ∩ Uⱼ}`,
which is well posed precisely because of the closure-under-intersection hypothesis.
`sheaf_iff_cofinal_sheaf` identifies the two conditions.

## Relation to the source statement

The Stacks Project states 009L for a *basis* `B` of the topology of a topological space `X`.
Neither fact is used in the proof, so `B` is here an arbitrary family `B : Set (Set X)` and `X`
carries no topology at all. The statement below is therefore strictly more general than the
source's, and specialises to it by taking `B` to be a basis; the two hypotheses the argument does
use — closure under intersection and cofinality — are carried explicitly.

## Implementation notes

The index type of a covering lives in a universe `v` independent of the universe `u` of `X` and
of the universe `w` in which the presheaf takes its values. The explicit universe annotations
`Covering.{u, v}` and `Presheaf.IsSheaf.{u, v, w}` below are what ties the covering universe
appearing in `IsSheaf` to the one used by `IsCofinalSystem`: without them Lean binds a fresh
universe for each occurrence and the cofinality hypothesis becomes inapplicable.

The two directions of the equivalence are proved separately, as
`Presheaf.IsSheaf.isSheafOnCofinal` and `Presheaf.IsSheafOnCofinal.isSheaf`; only the latter
needs cofinality.
-/

@[expose] public section

namespace Stacks.SheafOnBasis

universe u v w

variable {X : Type u}

/-- A covering of `U` by members of the family `B`: an indexed family `Uᵢ` of members of `B`,
each contained in `U`, whose union is exactly `U`. -/
structure Covering (B : Set (Set X)) (U : Set X) where
  /-- Index set of the covering. -/
  ι : Type v
  /-- The family of members of `B` indexed by `ι`. -/
  fam : ι → Set X
  /-- Each member of the family belongs to `B`. -/
  mem : ∀ i, fam i ∈ B
  /-- Each member of the family is contained in `U`. -/
  subset : ∀ i, fam i ⊆ U
  /-- The union of the family is exactly `U`. -/
  cover : U = ⋃ i, fam i

/-- A covering `V` refines a covering `W` if every member of `V` is contained in some member
of `W`. -/
def Covering.Refines {B : Set (Set X)} {U : Set X} (V W : Covering.{u, v} B U) : Prop :=
  ∀ j, ∃ i, V.fam j ⊆ W.fam i

/-- A choice `C U` of coverings for each `U ∈ B` is *cofinal* if every covering of `U` admits a
refinement belonging to `C U`. -/
def IsCofinalSystem (B : Set (Set X)) (C : ∀ U ∈ B, Set (Covering.{u, v} B U)) : Prop :=
  ∀ (U : Set X) (hU : U ∈ B) (𝓤 : Covering.{u, v} B U),
    ∃ 𝓥 ∈ C U hU, Covering.Refines 𝓥 𝓤

/-- A presheaf of sets on the family `B`: a set `F U` of sections for each `U ∈ B` together with
restriction maps `F U → F V` for each inclusion `V ⊆ U` of members of `B`, subject to the
identity and composition laws. -/
structure Presheaf (B : Set (Set X)) where
  /-- The set of sections over each member of `B`. -/
  obj : ∀ U ∈ B, Type w
  /-- The restriction map along an inclusion `V ⊆ U` of members of `B`. -/
  res : ∀ {U V : Set X} (hU : U ∈ B) (hV : V ∈ B), V ⊆ U → obj U hU → obj V hV
  /-- Restriction along the identity inclusion is the identity. -/
  res_id : ∀ {U : Set X} (hU : U ∈ B) (s : obj U hU), res hU hU (subset_refl U) s = s
  /-- Restriction is functorial for composition of inclusions. -/
  res_comp : ∀ {U V W : Set X} (hU : U ∈ B) (hV : V ∈ B) (hW : W ∈ B)
      (hVU : V ⊆ U) (hWV : W ⊆ V) (s : obj U hU),
    res hV hW hWV (res hU hV hVU s) = res hU hW (hWV.trans hVU) s

/-- The closure-under-intersection hypothesis on `B`: whenever `U', U'' ∈ B` are both contained
in a common `U ∈ B`, the intersection `U' ∩ U''` again belongs to `B`. -/
def ClosedUnderInter (B : Set (Set X)) : Prop :=
  ∀ ⦃U U' U'' : Set X⦄, U ∈ B → U' ∈ B → U'' ∈ B → U' ⊆ U → U'' ⊆ U → U' ∩ U'' ∈ B

/-- Intersecting a covering of `U` with a member `V ⊆ U` of `B` gives a covering of `V`. -/
def Covering.inter {B : Set (Set X)} (hB_inter : ClosedUnderInter B) {U V : Set X}
    (hU : U ∈ B) (hV : V ∈ B) (hVU : V ⊆ U) (𝓥 : Covering.{u, v} B U) :
    Covering.{u, v} B V where
  ι := 𝓥.ι
  fam k := 𝓥.fam k ∩ V
  mem k := hB_inter hU (𝓥.mem k) hV (𝓥.subset k) hVU
  subset _ := Set.inter_subset_right
  cover := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    refine ⟨fun hx => ?_, fun ⟨_, _, hx⟩ => hx⟩
    have hxU := hVU hx
    rw [𝓥.cover, Set.mem_iUnion] at hxU
    obtain ⟨k, hxk⟩ := hxU
    exact ⟨k, hxk, hx⟩

/-- The sheaf condition on a basis in the form the Stacks Project uses (Tag 009H): for every
`U ∈ B`, every covering of `U` by members of `B`, and every family of sections agreeing on every
`W ∈ B` with `W ⊆ Uᵢ ∩ Uⱼ`, there is a unique section over `U` restricting to each `sᵢ`.

Compatibility is tested on the members of `B` below `Uᵢ ∩ Uⱼ` rather than on `Uᵢ ∩ Uⱼ` itself,
which need not belong to `B`. -/
@[ega "0 3.2.2"]
def Presheaf.IsSheaf {B : Set (Set X)} (F : Presheaf.{u, w} B) : Prop :=
  ∀ (U : Set X) (hU : U ∈ B) (𝓤 : Covering.{u, v} B U) (s : ∀ i, F.obj (𝓤.fam i) (𝓤.mem i)),
    (∀ (i j : 𝓤.ι) (W : Set X) (hW : W ∈ B) (hWi : W ⊆ 𝓤.fam i) (hWj : W ⊆ 𝓤.fam j),
      F.res (𝓤.mem i) hW hWi (s i) = F.res (𝓤.mem j) hW hWj (s j)) →
    ∃! t : F.obj U hU, ∀ i, F.res hU (𝓤.mem i) (𝓤.subset i) t = s i

/-- The simplified sheaf condition of Stacks 009L(2): for every `U ∈ B`, every covering
`𝓤 ∈ C U` and every family of sections satisfying the single equation
`sᵢ|_{Uᵢ ∩ Uⱼ} = sⱼ|_{Uᵢ ∩ Uⱼ}`, there is a unique section over `U` restricting to each `sᵢ`.

The restrictions to `Uᵢ ∩ Uⱼ` make sense because `hB_inter` puts that intersection in `B`. -/
def Presheaf.IsSheafOnCofinal {B : Set (Set X)} (F : Presheaf.{u, w} B)
    (hB_inter : ClosedUnderInter B) (C : ∀ U ∈ B, Set (Covering.{u, v} B U)) : Prop :=
  ∀ (U : Set X) (hU : U ∈ B) (𝓤 : Covering.{u, v} B U) (_ : 𝓤 ∈ C U hU)
    (s : ∀ i, F.obj (𝓤.fam i) (𝓤.mem i)),
    (∀ i j : 𝓤.ι,
      F.res (𝓤.mem i) (hB_inter hU (𝓤.mem i) (𝓤.mem j) (𝓤.subset i) (𝓤.subset j))
            Set.inter_subset_left (s i) =
      F.res (𝓤.mem j) (hB_inter hU (𝓤.mem i) (𝓤.mem j) (𝓤.subset i) (𝓤.subset j))
            Set.inter_subset_right (s j)) →
    ∃! t : F.obj U hU, ∀ i, F.res hU (𝓤.mem i) (𝓤.subset i) t = s i

/-- A sheaf on `B` satisfies the simplified sheaf condition on any family of coverings.

The simplified compatibility of `s` on a covering `𝓤` implies the full compatibility demanded by
`Presheaf.IsSheaf`, because for `W ⊆ Uᵢ ∩ Uⱼ` in `B` restriction to `W` factors through
`Uᵢ ∩ Uⱼ`:
`sᵢ|_W = (sᵢ|_{Uᵢ ∩ Uⱼ})|_W = (sⱼ|_{Uᵢ ∩ Uⱼ})|_W = sⱼ|_W`.
Neither cofinality of `C` nor membership of `𝓤` in `C U` is needed. -/
theorem Presheaf.IsSheaf.isSheafOnCofinal {B : Set (Set X)} {F : Presheaf.{u, w} B}
    (hF : Presheaf.IsSheaf.{u, v, w} F) (hB_inter : ClosedUnderInter B)
    (C : ∀ U ∈ B, Set (Covering.{u, v} B U)) :
    F.IsSheafOnCofinal hB_inter C := by
  intro U hU 𝓤 _ s hcompat
  refine hF U hU 𝓤 s fun i j W hW hWi hWj => ?_
  have hinter := hB_inter hU (𝓤.mem i) (𝓤.mem j) (𝓤.subset i) (𝓤.subset j)
  have hW_sub_inter : W ⊆ 𝓤.fam i ∩ 𝓤.fam j := Set.subset_inter hWi hWj
  rw [← F.res_comp (𝓤.mem i) hinter hW Set.inter_subset_left hW_sub_inter (s i),
    ← F.res_comp (𝓤.mem j) hinter hW Set.inter_subset_right hW_sub_inter (s j), hcompat i j]

/-- Under the simplified sheaf condition, two sections over `V` that agree on every member of a
covering of `V` belonging to `C V` are equal. -/
theorem Presheaf.IsSheafOnCofinal.eq_of_res_eq {B : Set (Set X)} {F : Presheaf.{u, w} B}
    {hB_inter : ClosedUnderInter B} {C : ∀ U ∈ B, Set (Covering.{u, v} B U)}
    (hF : F.IsSheafOnCofinal hB_inter C) {V : Set X} (hV : V ∈ B)
    {𝓦 : Covering.{u, v} B V} (h𝓦 : 𝓦 ∈ C V hV) {a b : F.obj V hV}
    (h : ∀ l, F.res hV (𝓦.mem l) (𝓦.subset l) a = F.res hV (𝓦.mem l) (𝓦.subset l) b) :
    a = b := by
  obtain ⟨τ, _, hτ⟩ := hF V hV 𝓦 h𝓦 (fun l => F.res hV (𝓦.mem l) (𝓦.subset l) a)
    fun l m => by simp only [F.res_comp]
  exact (hτ a fun _ => rfl).trans (hτ b fun l => (h l).symm).symm

/-- A presheaf satisfying the simplified sheaf condition on a *cofinal* system of coverings is a
sheaf on `B`.

Given an arbitrary covering `𝓤` of `U ∈ B` and a compatible family `s`, cofinality provides
`𝓥 ∈ C U` refining `𝓤` along some `φ : 𝓥.ι → 𝓤.ι`. Restricting `s` along `φ` gives a family on
`𝓥` which is compatible for the simplified condition, hence glues to a section `σ` over `U`.
That `σ` restricts to `sᵢ` on each `Uᵢ` is checked by gluing on `Uᵢ` itself: the sets
`Vₖ ∩ Uᵢ` cover `Uᵢ`, so a covering of `Uᵢ` from `C (Uᵢ)` refining them separates sections, and
both `σ|_{Uᵢ}` and `sᵢ` restrict to the same family on it. Uniqueness of the gluing on `𝓥`
transfers back to `𝓤` the same way. -/
theorem Presheaf.IsSheafOnCofinal.isSheaf {B : Set (Set X)} {F : Presheaf.{u, w} B}
    {hB_inter : ClosedUnderInter B} {C : ∀ U ∈ B, Set (Covering.{u, v} B U)}
    (hF : F.IsSheafOnCofinal hB_inter C) (hC : IsCofinalSystem B C) :
    Presheaf.IsSheaf.{u, v, w} F := by
  intro U hU 𝓤 s hcompat
  obtain ⟨𝓥, h𝓥mem, h𝓥ref⟩ := hC U hU 𝓤
  choose φ hφsub using h𝓥ref
  let t : ∀ k : 𝓥.ι, F.obj (𝓥.fam k) (𝓥.mem k) :=
    fun k => F.res (𝓤.mem (φ k)) (𝓥.mem k) (hφsub k) (s (φ k))
  have hcompat_t : ∀ k l : 𝓥.ι,
      F.res (𝓥.mem k) (hB_inter hU (𝓥.mem k) (𝓥.mem l) (𝓥.subset k) (𝓥.subset l))
            Set.inter_subset_left (t k) =
      F.res (𝓥.mem l) (hB_inter hU (𝓥.mem k) (𝓥.mem l) (𝓥.subset k) (𝓥.subset l))
            Set.inter_subset_right (t l) := by
    intro k l
    simp only [t, F.res_comp]
    exact hcompat (φ k) (φ l) (𝓥.fam k ∩ 𝓥.fam l) (hB_inter hU (𝓥.mem k) (𝓥.mem l) (𝓥.subset k)
        (𝓥.subset l)) (Set.inter_subset_left.trans (hφsub k)) (Set.inter_subset_right.trans
        (hφsub l))
  obtain ⟨σ, hσ_res, hσ_uniq⟩ := hF U hU 𝓥 h𝓥mem t hcompat_t
  have hσ_correct : ∀ i, F.res hU (𝓤.mem i) (𝓤.subset i) σ = s i := by
    intro i
    obtain ⟨𝓦', h𝓦'mem, h𝓦'ref⟩ :=
      hC (𝓤.fam i) (𝓤.mem i) (𝓥.inter hB_inter hU (𝓤.mem i) (𝓤.subset i))
    choose ψ hψsub using h𝓦'ref
    refine hF.eq_of_res_eq (𝓤.mem i) h𝓦'mem fun l => ?_
    have hW'l_sub_V : 𝓦'.fam l ⊆ 𝓥.fam (ψ l) := (hψsub l).trans Set.inter_subset_left
    rw [F.res_comp hU (𝓤.mem i) (𝓦'.mem l) (𝓤.subset i) (𝓦'.subset l) σ,
      ← F.res_comp hU (𝓥.mem (ψ l)) (𝓦'.mem l) (𝓥.subset (ψ l)) hW'l_sub_V σ, hσ_res (ψ l),
      F.res_comp (𝓤.mem (φ (ψ l))) (𝓥.mem (ψ l)) (𝓦'.mem l) (hφsub (ψ l)) hW'l_sub_V
        (s (φ (ψ l)))]
    exact hcompat (φ (ψ l)) i (𝓦'.fam l) (𝓦'.mem l) (hW'l_sub_V.trans (hφsub (ψ l)))
      (𝓦'.subset l)
  refine ⟨σ, hσ_correct, fun σ' hσ' => hσ_uniq _ fun k => ?_⟩
  rw [← F.res_comp hU (𝓤.mem (φ k)) (𝓥.mem k) (𝓤.subset (φ k)) (hφsub k) σ', hσ' (φ k)]

/-- **Stacks 009L.** Let `B` be a family of subsets closed under intersection of pairs of its
members lying in a common member, and for each `U ∈ B` let `C U` be a cofinal system of coverings
of `U` by members of `B`. Then a presheaf of sets on `B` is a sheaf on `B` if and only if gluing
holds for the coverings in `C U` with compatibility tested on the intersections `Uᵢ ∩ Uⱼ`. -/
@[stacks 009L]
theorem sheaf_iff_cofinal_sheaf {B : Set (Set X)} (hB_inter : ClosedUnderInter B)
    (C : ∀ U ∈ B, Set (Covering.{u, v} B U)) (hC : IsCofinalSystem B C) (F : Presheaf.{u, w} B) :
    Presheaf.IsSheaf.{u, v, w} F ↔ F.IsSheafOnCofinal hB_inter C :=
  ⟨fun hF => hF.isSheafOnCofinal hB_inter C, fun hF => hF.isSheaf hC⟩

end Stacks.SheafOnBasis
