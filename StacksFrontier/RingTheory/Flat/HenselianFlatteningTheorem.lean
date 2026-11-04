module

public import StacksFrontier.RingTheory.Flat.FlatteningBridge
public import StacksFrontier.RingTheory.Flat.FlatteningDevissageInduction
public import StacksFrontier.RingTheory.Flat.FlatteningEquivalence
public import StacksFrontier.RingTheory.Flat.FlatteningFGApprox
public import StacksFrontier.RingTheory.Flat.FlatteningHenselianReduction

/-!
# The local flattening theorem over a henselian base

Let `A → B` be a local homomorphism of local rings with `A` henselian and `B` essentially of
finite type over `A`, and let `M` be a finite `B`-module. Stacks Tag 05PG asserts that there is an
ideal `I ⊆ A` such that, for every local homomorphism of local rings `A → A'`, the base change
`M' = M ⊗_A A'` is flat over `A'` at every prime of `B' = B ⊗_A A'` above the closed points of
`A'` and of `B` exactly when `I` dies in `A'`; that is, `A ⧸ I` corepresents the functor `F_lf` of
Stacks Tag 05MK. If moreover `B` is essentially of finite presentation over `A` and `M` is of
finite presentation over `B`, then `I` is finitely generated.

The proof follows the source. By Stacks Tag 05P5 and Stacks Tag 05I1, and because `A` is
henselian, `(B, M)` may be replaced by the localization at a prime `q` of a finite type
`A`-algebra `C` and of a finite `C`-module `N` admitting a complete dévissage at `q` over `A`
(`Module.FlatAtPointSituation.exists_devissage_isFlatAtPrimesAbove`). Along the dévissage the
functor is corepresented stage by stage, from the last stage down
(`Module.CompleteDevissage.exists_ideal_isFlatAtPrimesAbove_iff`): Stacks Tags 05I3, 05P4 and the
argument of Stacks Tag 05PF for the image of the stage map. The finite generation follows from
the limit preservation of Stacks Tag 05MN, as in the source.

## Main results

* `Module.FlatAtPointSituation.exists_ideal_conditionOn_iff_map_eq_bot_of_henselian`: the
  corepresenting ideal, tested against local `A`-algebras in any universe containing that of `A`.
* `Module.FlatAtPointSituation.exists_ideal_condition_iff_map_eq_bot_of_henselian`:
  **Stacks Tag 05PG**.
* `Module.FlatAtPointSituation.exists_ideal_flat_quotient_iff_le_of_henselian`: the same ideal
  read as the smallest ideal `I` with `M ⧸ IM` flat over `A ⧸ I`.

## Implementation notes

The test algebras of the corepresentability statement range over the objects of
`LocalAlgCat.{u, x} S.A` for an arbitrary universe `x`; the proof tests the universe lift
`ULift.{u} R` of each of them, since the stage algebras of the dévissage live in the universe of
`A`. The finite generation half is stated as an implication inside the existential, so that the
one ideal produced satisfies both halves of the tag.

## References

* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05MN](https://stacks.math.columbia.edu/tag/05MN)
-/

@[expose] public section

open IsLocalRing

universe u v w x

namespace Module.FlatAtPointSituation

/-- **The local flattening ideal over a henselian base**, tested against the local `A`-algebras
with local structure map in the universe `max u x`. -/
theorem exists_ideal_conditionOn_iff_map_eq_bot_of_henselian
    (S : FlatAtPointSituation.{u, v, w}) [HenselianLocalRing S.A]
    [Algebra.EssFiniteType S.A S.B] [Module.Finite S.B S.M] :
    ∃ I : Ideal S.A, ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)],
      S.ConditionOn R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  obtain ⟨C, _, _, _, N, _, _, _, q, _, hq, hdev, hcond⟩ :=
    exists_devissage_isFlatAtPrimesAbove.{u, v, w, max u x} S
  obtain ⟨I, hI⟩ : ∃ I : Ideal S.A, ∀ (R : Type max u x) [CommRing R] [IsLocalRing R]
      [Algebra S.A R] [IsLocalHom (algebraMap S.A R)],
      IsFlatAtPrimesAbove S.A C q N R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
    rcases hdev with hN | ⟨D, ⟨pts⟩⟩
    · exact ⟨⊥, fun R _ _ _ _ ↦ by
        simpa only [Ideal.map_bot, iff_true] using isFlatAtPrimesAbove_of_subsingleton q N R⟩
    · exact D.exists_ideal_isFlatAtPrimesAbove_iff pts
  exact ⟨I, fun R _ _ _ _ ↦ (hcond R).trans (hI R)⟩

/-- **Stacks Project, Tag 05PG.** Let `A → B` be a local homomorphism of local rings with `A`
henselian and `B` essentially of finite type over `A`, and let `M` be a finite `B`-module. There
is an ideal `I ⊆ A` such that `A ⧸ I` corepresents the functor `F_lf` of Stacks Tag 05MK: for
every local `A`-algebra `A'` with local structure map, the base change of `M` is flat over `A'`
at every prime of `B ⊗_A A'` containing the extensions of the maximal ideals of `A'` and of `B`
exactly when `I` dies in `A'`. If `B` is essentially of finite presentation over `A` and `M` is
of finite presentation over `B`, then `I` is finitely generated. -/
@[stacks 05PG]
theorem exists_ideal_condition_iff_map_eq_bot_of_henselian
    (S : FlatAtPointSituation.{u, v, w}) [HenselianLocalRing S.A]
    [Algebra.EssFiniteType S.A S.B] [Module.Finite S.B S.M] :
    ∃ I : Ideal S.A,
      (∀ R : LocalAlgCat.{u, x} S.A, S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥) ∧
      ((algebraMap S.A S.B).EssentiallyOfFinitePresentation →
        Module.FinitePresentation S.B S.M → I.FG) := by
  obtain ⟨I, hI⟩ := exists_ideal_conditionOn_iff_map_eq_bot_of_henselian.{u, v, w, x} S
  refine ⟨I, fun R ↦ ?_, fun hB hM ↦ ?_⟩
  · show S.ConditionOn R ↔ _
    rw [← S.conditionOn_ulift_iff.{u, v, w, x, u} R, hI (ULift.{u} R),
      Ideal.map_eq_bot_iff_le_ker, Ideal.map_eq_bot_iff_le_ker, ULift.ker_algebraMap]
  · have := hM
    have hI' : ∀ R : LocalAlgCat.{u, max u x} S.A,
        S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := fun R ↦ hI R
    obtain ⟨J, hJI, hJfg, hJ⟩ := S.flattensFGApprox hB I
      ((flattens_iff_le_of_condition_iff hI' I).mpr le_rfl)
    have hIJ : I ≤ J := (flattens_iff_le_of_condition_iff hI' J).mp hJ
    exact le_antisymm hIJ hJI ▸ hJfg

/-- **Stacks Tag 05PG as a smallest flattening ideal.** Let `A → B` be a local homomorphism of
local rings with `A` henselian and `B` essentially of finite type over `A`, and let `M` be a
finite `B`-module. There is an ideal `I ⊆ A` such that, for an ideal `K ⊆ A`, the reduction
`M ⧸ KM` is flat over `A ⧸ K` exactly when `I ⊆ K`. If `B` is essentially of finite presentation
over `A` and `M` is of finite presentation over `B`, then `I` is finitely generated.

This is `Module.FlatAtPointSituation.exists_ideal_condition_iff_map_eq_bot_of_henselian` read
through the two dictionaries of `StacksDraft.RingTheory.Flat`: the corepresenting ideal detects
exactly the flattening ideals by
`Module.FlatAtPointSituation.flattens_iff_le_of_condition_iff`, and flattening the situation is
flatness of the reduction by `Module.FlatAtPointSituation.flattens_iff_flat_quotient`. It is the
shape the proof of Stacks 05U9 consumes, through
`Stacks.flat_of_least_flattening_of_flat_away` and
`Stacks.exists_fg_isNilpotent_flat_quotient_of_least`. -/
theorem exists_ideal_flat_quotient_iff_le_of_henselian
    (S : FlatAtPointSituation.{u, v, w}) [HenselianLocalRing S.A]
    [Algebra.EssFiniteType S.A S.B] [Module.Finite S.B S.M] :
    ∃ I : Ideal S.A,
      (∀ K : Ideal S.A,
        Module.Flat (S.A ⧸ K) (S.M ⧸ (K • (⊤ : Submodule S.A S.M))) ↔ I ≤ K) ∧
      ((algebraMap S.A S.B).EssentiallyOfFinitePresentation →
        Module.FinitePresentation S.B S.M → I.FG) := by
  obtain ⟨I, hI, hfg⟩ := exists_ideal_condition_iff_map_eq_bot_of_henselian.{u, v, w, u} S
  refine ⟨I, fun K ↦ ?_, hfg⟩
  rw [← S.flattens_iff_flat_quotient K]
  exact flattens_iff_le_of_condition_iff hI K

/-- **Stacks Tag 05PG as a smallest flattening ideal, on unbundled data.** Let `R → T` be a local
homomorphism of local rings with `R` henselian and `T` essentially of finite type over `R`, and
let `X` be a finite `T`-module which is also an `R`-module through `R → T`. There is an ideal
`I ⊆ R` such that, for an ideal `K ⊆ R`, the reduction `X ⧸ KX` is flat over `R ⧸ K` exactly when
`I ⊆ K`; it is finitely generated once `R → T` is essentially of finite presentation and `X` is of
finite presentation over `T`.

This is `Module.FlatAtPointSituation.exists_ideal_flat_quotient_iff_le_of_henselian` with the
situation unbundled, and it is the form a caller holding an ambient `Module R X` can use. The
bundled statement is about `Module.FlatAtPointSituation.moduleAM`, which is
`Module.compHom _ (algebraMap R T)`: equal to the ambient structure by
`Module.compHom_algebraMap_eq` but not definitionally so, and `K • ⊤` depends on which one is
used, so the two readings are bridged here once by `Module.flat_quotient_smul_top_congr` rather
than at each call site. -/
theorem exists_ideal_flat_quotient_iff_le_of_henselian_of_isScalarTower (R : Type u) [CommRing R]
    [IsLocalRing R] [HenselianLocalRing R] (T : Type v) [CommRing T] [IsLocalRing T] [Algebra R T]
    [IsLocalHom (algebraMap R T)] [Algebra.EssFiniteType R T] (X : Type w) [AddCommGroup X]
    [Module T X] [Module R X] [IsScalarTower R T X] [Module.Finite T X] :
    ∃ I : Ideal R,
      (∀ K : Ideal R, Module.Flat (R ⧸ K) (X ⧸ (K • (⊤ : Submodule R X))) ↔ I ≤ K) ∧
      ((algebraMap R T).EssentiallyOfFinitePresentation →
        Module.FinitePresentation T X → I.FG) := by
  obtain ⟨I, hI, hfg⟩ := exists_ideal_flat_quotient_iff_le_of_henselian
    ({ A := R, B := T, M := X } : FlatAtPointSituation.{u, v, w})
  have hmod : moduleAM ({ A := R, B := T, M := X } : FlatAtPointSituation.{u, v, w}) =
      (inferInstance : Module R X) :=
    Module.ext' _ _ fun a x ↦ (IsScalarTower.algebraMap_smul T a x : _)
  exact ⟨I, fun K ↦ (Module.flat_quotient_smul_top_congr _ _ hmod K).symm.trans (hI K), hfg⟩

end Module.FlatAtPointSituation

end
