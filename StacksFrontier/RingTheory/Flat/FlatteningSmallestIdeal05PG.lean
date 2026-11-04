module

public import StacksFrontier.RingTheory.Flat.Artinian
public import StacksFrontier.RingTheory.Flat.FlatteningBridge
public import StacksFrontier.RingTheory.Flat.FlatteningEquivalence
public import StacksFrontier.RingTheory.Flat.FlatteningFGApprox
public import StacksFrontier.RingTheory.Flat.FlatteningFlatDescent
public import StacksFrontier.RingTheory.Flat.QuotientInf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The flattening ideals of the local flattening problem form a filter

In the situation of Stacks Tag 05MK — a local homomorphism `A → B` of local rings together with
a `B`-module `M` — say that an ideal `J ⊆ A` *flattens* the situation if the flatness condition
of Stacks Tag 05ML holds over `A ⧸ J`; this is
`Module.FlatAtPointSituation.Flattens`. Stacks Tag 05PG asserts that for `A` henselian, `A → B`
essentially of finite type and `M` finite over `B` the flattening ideals are exactly the ideals
containing one fixed ideal `I`.

`StacksFrontier.RingTheory.Flat.HenselianFlattening` reduces that assertion to
`Module.FlatAtPointSituation.FlattensSInf` (the flattening ideals are closed under arbitrary
nonempty intersections), `Module.FlatAtPointSituation.FlattensKer` (the kernel of a local
`A`-algebra satisfying the condition flattens) and
`Module.FlatAtPointSituation.FlattensFGApprox` (a flattening ideal contains a finitely generated
one). The third is proved in `StacksFrontier.RingTheory.Flat.FlatteningFGApprox`; the first two are
*together* equivalent to Stacks Tag 05PG itself, by
`Module.FlatAtPointSituation.flattensSInf_and_flattensKer_iff_exists_ideal`.

This file proves, unconditionally, the part of those two statements that needs no dévissage.

The *binary* intersection of two flattening ideals flattens: by
`Module.FlatAtPointSituation.flattens_iff_flat_quotient` flattening is flatness of `M ⧸ J M`
over `A ⧸ J`, and that property is stable under binary intersections by `Module.Flat.quotient_inf`
(Stacks Tag 0522). Together with `Module.FlatAtPointSituation.Flattens.mono` this makes the
flattening ideals a filter in the lattice of ideals of `A`, and it cuts `FlattensSInf` down to
*codirected* families: the finite intersections of a family form a codirected family of
flattening ideals with the same infimum. Under the hypotheses of the finite-generation half of
Stacks Tag 05PG the codirected family may moreover be taken to consist of finitely generated
ideals.

On the `FlattensKer` side the flat case is unconditional: if `R` is flat over `A ⧸ J` for an
ideal `J` killed in `R`, then the condition over `R` descends to `A ⧸ J` by Stacks Tag 05MN
part (1), so `J` flattens. What remains of `FlattensKer` is therefore exactly the non-flat case.

## Main results

* `Module.FlatAtPointSituation.Flattens.inf` and
  `Module.FlatAtPointSituation.Flattens.finsetInf`: the flattening ideals are closed under
  binary, hence finite nonempty, intersections.
* `Module.FlatAtPointSituation.flattensSInf_iff_codirected`:
  `Module.FlatAtPointSituation.FlattensSInf` holds as soon as it holds for codirected families.
* `Module.FlatAtPointSituation.exists_codirected_fg_sInf_eq_flatteningIdeal`: the smallest
  flattening ideal is the infimum of a codirected family of finitely generated flattening
  ideals.
* `Module.FlatAtPointSituation.flattensSInf_of_isArtinianRing`:
  `Module.FlatAtPointSituation.FlattensSInf` holds outright when `A` is Artinian.
* `Module.FlatAtPointSituation.Flattens.of_conditionOn_of_flat`: the flat case of
  `Module.FlatAtPointSituation.FlattensKer`.

## Implementation notes

Codirectedness is `DirectedOn (· ≥ ·)`: every two members of the family dominate a common
member.

`Module.FlatAtPointSituation.Flattens.of_conditionOn_of_flat` takes the `A ⧸ J`-algebra structure
on `R` as an instance argument rather than building it from `J ≤ RingHom.ker (algebraMap A R)`,
because the flatness hypothesis has to be stated for whichever structure is used. Locality of
`A ⧸ J → R` is not assumed: it follows from locality of `A → R` and surjectivity of
`A → A ⧸ J`.

Nothing here proves Stacks Tag 05PG, so nothing here carries its tag; the tag is proved, by the
dévissage argument of the source, in `StacksFrontier.RingTheory.Flat.HenselianFlatteningTheorem`.

`StacksFrontier.RingTheory.Flat.FlatteningDevissageBridge` reduces the second link to base-change
*injectivity* of that map, which is the shape Stacks Tag 05I3 delivers rather than the shape
Stacks Tag 05PE consumes. What is still missing there is the application of Stacks Tag 05I3 over
a general local `A`-algebra `A'`: the condition of Stacks Tag 05ML is stated for the *local*
algebra `B`, while a dévissage stage algebra `B₁` is not local and `B` is its localization at the
stage prime, so the primes of `B ⊗_A A'` tested by the condition have first to be matched with
the primes of `B₁ ⊗_A A'` lying over `𝔪_{A'}` and over the stage prime.

## References

* [Stacks Project, Tag 0522](https://stacks.math.columbia.edu/tag/0522)
* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05MN](https://stacks.math.columbia.edu/tag/05MN)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing

universe u v w x

/-- The infima of the finite nonempty subsets of a nonempty family in a complete lattice form a
codirected family with the same infimum. -/
theorem Set.Nonempty.exists_codirected_sInf_eq {α : Type u} [CompleteLattice α] {𝒥 : Set α}
    (h𝒥 : 𝒥.Nonempty) :
    ∃ 𝒟 : Set α, 𝒟.Nonempty ∧ DirectedOn (· ≥ ·) 𝒟 ∧
      (∀ K ∈ 𝒟, ∃ T : Finset α, (T : Set α) ⊆ 𝒥 ∧ T.Nonempty ∧ K = T.inf id) ∧
      sInf 𝒟 = sInf 𝒥 := by
  classical
  refine ⟨{K | ∃ T : Finset α, (T : Set α) ⊆ 𝒥 ∧ T.Nonempty ∧ K = T.inf id}, ?_,
    ?_, fun _ h ↦ h, ?_⟩
  · obtain ⟨J, hJ⟩ := h𝒥
    exact ⟨J, {J}, by simpa using hJ, Finset.singleton_nonempty J, by simp⟩
  · rintro K₁ ⟨T₁, hT₁, hT₁ne, rfl⟩ K₂ ⟨T₂, hT₂, hT₂ne, rfl⟩
    refine ⟨(T₁ ∪ T₂).inf id, ⟨T₁ ∪ T₂, ?_, hT₁ne.mono Finset.subset_union_left, rfl⟩, ?_, ?_⟩
    · intro J hJ
      rcases Finset.mem_union.mp hJ with h | h
      · exact hT₁ h
      · exact hT₂ h
    · exact Finset.inf_mono Finset.subset_union_left
    · exact Finset.inf_mono Finset.subset_union_right
  · refine le_antisymm (le_sInf fun J hJ ↦ sInf_le ⟨{J}, by simpa using hJ, ?_, by simp⟩)
      (le_sInf ?_)
    · exact Finset.singleton_nonempty J
    · rintro K ⟨T, hT, -, rfl⟩
      exact Finset.le_inf fun J hJ ↦ sInf_le (hT hJ)

namespace Module.FlatAtPointSituation

/-- The intersection of two flattening ideals flattens the situation.

By `Module.FlatAtPointSituation.flattens_iff_flat_quotient` an ideal `J` flattens exactly when
`M ⧸ J M` is flat over `A ⧸ J`, and `Module.Flat.quotient_inf` (Stacks Tag 0522) is that property
for `J₁ ⊓ J₂`. No hypothesis on the situation is needed. -/
theorem Flattens.inf {S : FlatAtPointSituation.{u, v, w}} {J K : Ideal S.A}
    (hJ : S.Flattens J) (hK : S.Flattens K) : S.Flattens (J ⊓ K) := by
  rw [S.flattens_iff_flat_quotient] at hJ hK ⊢
  exact Module.Flat.quotient_inf J K hJ hK

/-- The intersection of a finite nonempty family of flattening ideals flattens the situation. -/
theorem Flattens.finsetInf {S : FlatAtPointSituation.{u, v, w}} {T : Finset (Ideal S.A)}
    (hT : T.Nonempty) (h : ∀ J ∈ T, S.Flattens J) : S.Flattens (T.inf id) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton J => simpa using h J (by simp)
  | cons J T hJ _ ih =>
      rw [Finset.inf_cons]
      exact (h J (by simp)).inf (ih fun K hK ↦ h K (by simp [hK]))

/-- **`FlattensSInf` is a statement about codirected families.** The flattening ideals are
closed under arbitrary nonempty intersections as soon as they are closed under the intersections
of codirected families.

The finite intersections of a family of flattening ideals flatten, by
`Module.FlatAtPointSituation.Flattens.finsetInf`, and form a codirected family with the same
infimum. This is an equivalence, so it does not prove `FlattensSInf`; it narrows the remaining
obligation of Stacks Tag 05PG from arbitrary families to codirected ones. -/
theorem flattensSInf_iff_codirected (S : FlatAtPointSituation.{u, v, w}) :
    S.FlattensSInf ↔ ∀ 𝒟 : Set (Ideal S.A), 𝒟.Nonempty → DirectedOn (· ≥ ·) 𝒟 →
      (∀ J ∈ 𝒟, S.Flattens J) → S.Flattens (sInf 𝒟) := by
  refine ⟨fun h 𝒟 h𝒟 _ h' ↦ h 𝒟 h𝒟 h', fun h 𝒥 h𝒥 h' ↦ ?_⟩
  obtain ⟨𝒟, h𝒟ne, h𝒟dir, h𝒟fin, h𝒟inf⟩ := h𝒥.exists_codirected_sInf_eq
  refine h𝒟inf ▸ h 𝒟 h𝒟ne h𝒟dir fun K hK ↦ ?_
  obtain ⟨T, hT, hTne, rfl⟩ := h𝒟fin K hK
  exact Flattens.finsetInf hTne fun J hJ ↦ h' J (hT hJ)

/-- **The smallest flattening ideal is the infimum of a codirected family of finitely generated
flattening ideals**, under the hypotheses of the finite-generation half of Stacks Tag 05PG.

The finitely generated flattening ideals are codirected: the intersection of two of them
flattens by `Module.FlatAtPointSituation.Flattens.inf`, and
`Module.FlatAtPointSituation.flattensFGApprox` — the limit preservation of Stacks Tag 05MN
part (2) — puts a finitely generated flattening ideal below it. They are cofinal downwards for
the same reason, so their infimum is `Module.FlatAtPointSituation.flatteningIdeal`. -/
theorem exists_codirected_fg_sInf_eq_flatteningIdeal (S : FlatAtPointSituation.{u, v, w})
    (hS : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M] :
    ∃ 𝒟 : Set (Ideal S.A), 𝒟.Nonempty ∧ DirectedOn (· ≥ ·) 𝒟 ∧
      (∀ J ∈ 𝒟, J.FG ∧ S.Flattens J) ∧ sInf 𝒟 = S.flatteningIdeal := by
  have happrox := S.flattensFGApprox hS
  refine ⟨{J | J.FG ∧ S.Flattens J}, ?_, ?_, fun _ h ↦ h, ?_⟩
  · obtain ⟨J, -, hJfg, hJ⟩ := happrox _ S.flattens_maximalIdeal
    exact ⟨J, hJfg, hJ⟩
  · rintro J₁ ⟨-, hJ₁⟩ J₂ ⟨-, hJ₂⟩
    obtain ⟨K, hKle, hKfg, hK⟩ := happrox _ (hJ₁.inf hJ₂)
    exact ⟨K, ⟨hKfg, hK⟩, le_trans hKle inf_le_left, le_trans hKle inf_le_right⟩
  · refine le_antisymm (le_sInf fun J hJ ↦ ?_) (le_sInf fun J hJ ↦ sInf_le hJ.2)
    obtain ⟨K, hKle, hKfg, hK⟩ := happrox _ hJ
    exact le_trans (sInf_le ⟨hKfg, hK⟩) hKle

/-- **`FlattensSInf` for an Artinian base.** If `A` is Artinian then the flattening ideals are
closed under arbitrary nonempty intersections.

An Artinian ring has a *least* ideal `I` with `M ⧸ I M` flat over `A ⧸ I`
(`exists_least_flat_quotient_ideal`, Stacks Tag 0524), which by
`Module.FlatAtPointSituation.flattens_iff_flat_quotient` is a least flattening ideal; it lies
below the infimum of any family of flattening ideals, and the flattening ideals are closed
upwards.

This discharges the first of the two outstanding conditions of Stacks Tag 05PG over an Artinian
base. It does not give Stacks Tag 05PG there, because
`Module.FlatAtPointSituation.FlattensKer` — the condition over a local `A`-algebra `R` being
detected by the kernel of `A → R` — is a separate statement which no least flattening ideal
supplies. -/
@[ega "IV 11.4.4" "partial"]
theorem flattensSInf_of_isArtinianRing (S : FlatAtPointSituation.{u, v, w})
    [IsArtinianRing S.A] : S.FlattensSInf := by
  obtain ⟨I, hI, hmin⟩ := _root_.exists_least_flat_quotient_ideal (R := S.A) (M := S.M)
  intro 𝒥 _ h
  exact ((S.flattens_iff_flat_quotient I).mpr hI).mono
    (le_sInf fun J hJ ↦ hmin J ((S.flattens_iff_flat_quotient J).mp (h J hJ)))

/-- **The flat case of `FlattensKer`.** If an ideal `J` of `A` dies in a local `A`-algebra `R`
which is flat over `A ⧸ J`, and the flatness condition of Stacks Tag 05ML holds over `R`, then
`J` flattens the situation.

This is Stacks Tag 05MN part (1) — `Module.FlatAtPointSituation.ConditionOn.of_flat` — applied to
the local homomorphism `A ⧸ J → R`, whose locality is automatic. The improper ideal flattens for
want of a prime to test. What remains of `Module.FlatAtPointSituation.FlattensKer` is the case
of an `R` which is not flat over the quotient by the kernel of `A → R`. -/
theorem Flattens.of_conditionOn_of_flat {S : FlatAtPointSituation.{u, v, w}} (J : Ideal S.A)
    (R : Type x) [CommRing R] [IsLocalRing R] [Algebra S.A R] [IsLocalHom (algebraMap S.A R)]
    [Algebra (S.A ⧸ J) R] [IsScalarTower S.A (S.A ⧸ J) R] [Module.Flat (S.A ⧸ J) R]
    (h : S.ConditionOn R) : S.Flattens J := by
  rcases eq_or_ne J ⊤ with rfl | hJ
  · exact S.flattens_top
  have _ : Nontrivial (S.A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have _ : IsLocalRing (S.A ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have _ : IsLocalHom (algebraMap (S.A ⧸ J) R) := by
    refine ⟨fun a ha ↦ ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hb : IsUnit (algebraMap S.A R b) := by
      rw [IsScalarTower.algebraMap_apply S.A (S.A ⧸ J) R b, Ideal.Quotient.algebraMap_eq]
      exact ha
    exact (IsLocalHom.map_nonunit (f := algebraMap S.A R) b hb).map (Ideal.Quotient.mk J)
  have hquot : S.ConditionOn (S.A ⧸ J) := ConditionOn.of_flat (S := S) (S.A ⧸ J) R h
  unfold Flattens
  rw [maximalIdeal_quotient hJ]
  exact hquot

end Module.FlatAtPointSituation

end
