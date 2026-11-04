module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import StacksFrontier.RingTheory.Dualizing.PowerBasisSelfDual

/-!
# A finite ring map factors through `R[x_1, …, x_n]/(f_1, …, f_n)` by a surjection

Let `φ : R → A` be a finite ring map.  Choose generators `a_1, …, a_n` of `A` as an `R`-module;
each is integral over `R`, say `f_i(a_i) = 0` with `f_i ∈ R[x]` monic.  Then

`C = R[x_1, …, x_n]/(f_1(x_1), …, f_n(x_n))`

is a finite free `R`-algebra, the map `C → A` sending `x_i ↦ a_i` is a surjection, and `φ` is its
composite with `R → C`.  Moreover `C` is its own `R`-linear dual.

This is the reduction of the finite case of [Stacks, Tag 0C0G] to the surjective case: the only
part of the tag's proof that is not about a surjection is the bottom map `R → C`, and there
[Stacks, Tag 0BZE] applies because `C` is finite projective and self-dual —
`Dualizing.nonempty_derivedHom_iso_derivedTensorProductOver_of_selfDual_algebra`.

The proof of Tag 0C0G in the finite case,
`Dualizing.upperShriekFunctor_iso_derivedHom_of_finite`, uses
`Dualizing.exists_monicIdeal_quotient_surjection` rather than the factorization built here: it is
the same factorization, but with `C` presented as a quotient of a polynomial ring in `n`
variables, which is what computing `ω_{C/R}` needs.  This bundle records finiteness, freeness and
self-duality of `C` built as an iterated `AdjoinRoot`, and no presentation.

## Main definitions

* `Dualizing.MonicTowerFactorization` — the factorization as a bundle: the intermediate algebra,
  its finiteness, freeness and self-duality, the surjection and the commutation.

## Main results

* `Dualizing.nonempty_monicTowerFactorization` — **every finite ring map admits one.**

## Implementation notes

`C` is built as the *tower* of monic root extensions
`R → R[x_1]/(f_1) → ⋯ → R[x_1, …, x_n]/(f_1, …, f_n)`, one `Mathlib.RingTheory.AdjoinRoot` at a
time, rather than as a quotient of a polynomial ring in `n` variables.  Each step is monogenic, so
finiteness and freeness are `Polynomial.Monic.finite_adjoinRoot` and
`Polynomial.Monic.free_adjoinRoot`, and self-duality is `Dualizing.isSelfDualAlgebra_adjoinRoot`,
the source's generator `δ_{d-1}`; the three then compose along the tower by
`Module.Finite.trans`, `Module.Free.trans` and `Dualizing.IsSelfDualAlgebra.trans`.  The
induction is on the number of generators with the *base ring varying*: after adjoining a root for
`a_1` the remaining `a_2, …, a_n` generate `A` over the new base, and are still integral over it.

The generators are taken as an arbitrary family `a : Fin n → A` generating `A` as an *algebra*,
which is weaker than generating it as a module and is all the induction uses; finiteness of `φ`
enters only to produce such a family whose members are integral.

## References

* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
* [Stacks Project, Tag 00P9](https://stacks.math.columbia.edu/tag/00P9)
-/

@[expose] public section

open Polynomial

universe u

namespace Dualizing

/-- **A factorization of a ring map through a finite free self-dual algebra by a surjection.**
For `φ : R → A` this bundles an `R`-algebra `C`, finite and free as an `R`-module and isomorphic
to its own `R`-linear dual, together with a surjection `C → A` whose composite with `R → C` is
`φ`.

`Dualizing.nonempty_monicTowerFactorization` produces one for every finite `φ`, with
`C = R[x_1, …, x_n]/(f_1, …, f_n)` for monic `f_i`, whence the name. -/
structure MonicTowerFactorization {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) where
  /-- The intermediate algebra `C = R[x_1, …, x_n]/(f_1, …, f_n)`. -/
  middle : Type u
  /-- `C` is a commutative ring. -/
  [commRingMiddle : CommRing middle]
  /-- `C` is an `R`-algebra. -/
  [algebraMiddle : Algebra R middle]
  /-- `C` is a finite `R`-module, each `R[x_i]/(f_i)` being finite over the previous stage. -/
  finiteMiddle : Module.Finite R middle
  /-- `C` is a free `R`-module, each `R[x_i]/(f_i)` being free over the previous stage. -/
  freeMiddle : Module.Free R middle
  /-- `C` is its own `R`-linear dual: self-duality holds at each monogenic stage and composes. -/
  selfDualMiddle : IsSelfDualAlgebra R middle
  /-- The surjection `C → A`, sending `x_i` to the `i`-th generator. -/
  toTarget : middle →+* A
  /-- The map to the target is surjective. -/
  surjective_toTarget : Function.Surjective toTarget
  /-- The factorization recovers `φ`. -/
  comp_eq : toTarget.comp (algebraMap R middle) = φ

namespace MonicTowerFactorization

attribute [instance] commRingMiddle algebraMiddle

variable {R A : Type u} [CommRing R] [CommRing A]

/-- The factorization of the structure map of an `R`-algebra read as a factorization of the
algebra map, with the intermediate algebra's instances in scope. -/
theorem algebraMap_eq {φ : R →+* A} (F : MonicTowerFactorization φ) (r : R) :
    F.toTarget (algebraMap R F.middle r) = φ r :=
  congrArg (fun ψ => ψ r) F.comp_eq

end MonicTowerFactorization

/-- **A ring map generated by finitely many integral elements factors through a finite free
self-dual algebra by a surjection.**  If `a : Fin n → A` generates `A` as an `R`-algebra and each
`a i` is integral over `R`, then `algebraMap R A` has a `Dualizing.MonicTowerFactorization`.

The induction is on `n`, with the base ring varying.  For `n = 0` the algebra map is itself
surjective and `C = R` works, `R` being self-dual over itself.  For `n + 1` adjoin a root of a
monic polynomial killing `a 0`, giving `B = R[x]/(f_0)`: it is finite free and self-dual over `R`,
the remaining `a 1, …, a n` are integral over `B` and generate `A` over it, and the factorization
obtained for `B → A` is pushed down to `R` by transitivity of finiteness, freeness and
self-duality. -/
theorem nonempty_monicTowerFactorization_of_adjoin_eq_top (n : ℕ) :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (a : Fin n → A),
      (∀ i, IsIntegral R (a i)) → Algebra.adjoin R (Set.range a) = ⊤ →
      Nonempty (MonicTowerFactorization (algebraMap R A)) := by
  induction n with
  | zero =>
    intro R A _ _ _ a _ htop
    have hbot : (⊥ : Subalgebra R A) = ⊤ := by
      rw [← Algebra.adjoin_empty R A, ← Set.range_eq_empty a, htop]
    have hsurj : Function.Surjective (algebraMap R A) := fun x =>
      Algebra.mem_bot.mp (hbot ▸ Algebra.mem_top)
    exact ⟨{ middle := R
             finiteMiddle := inferInstance
             freeMiddle := inferInstance
             selfDualMiddle := isSelfDualAlgebra_self R
             toTarget := algebraMap R A
             surjective_toTarget := hsurj
             comp_eq := by ext r; simp }⟩
  | succ n ih =>
    intro R A _ _ _ a hint htop
    obtain ⟨p, hpm, hpe⟩ := hint 0
    have hp0 : aeval (a 0) p = 0 := by rwa [aeval_def]
    let B := AdjoinRoot p
    let h : B →ₐ[R] A := AdjoinRoot.liftAlgHom p (Algebra.ofId R A) (a 0) hp0
    let : Algebra B A := h.toRingHom.toAlgebra
    have : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq fun r => (h.commutes r).symm
    have : Module.Finite R B := hpm.finite_adjoinRoot
    have : Module.Free R B := hpm.free_adjoinRoot
    have hroot : algebraMap B A (AdjoinRoot.root p) = a 0 :=
      AdjoinRoot.liftAlgHom_root p (Algebra.ofId R A) (a 0) hp0
    have htopB : Algebra.adjoin B (Set.range fun i : Fin n => a i.succ) = ⊤ := by
      refine eq_top_iff.mpr ?_
      have hle : Algebra.adjoin R (Set.range a) ≤
          (Algebra.adjoin B (Set.range fun i : Fin n => a i.succ)).restrictScalars R := by
        refine Algebra.adjoin_le ?_
        rintro x ⟨i, rfl⟩
        rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · rw [← hroot]
          exact Subalgebra.algebraMap_mem _ (AdjoinRoot.root p)
        · exact Algebra.subset_adjoin ⟨j, rfl⟩
      intro x _
      exact hle (by simp [htop])
    obtain ⟨F⟩ := ih (R := B) (A := A) (fun i : Fin n => a i.succ)
      (fun i => (hint i.succ).tower_top) htopB
    let : Algebra R F.middle := ((algebraMap B F.middle).comp (algebraMap R B)).toAlgebra
    have : IsScalarTower R B F.middle := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have := F.finiteMiddle
    have := F.freeMiddle
    refine ⟨{ middle := F.middle
              finiteMiddle := Module.Finite.trans B F.middle
              freeMiddle := Module.Free.trans (R := R) (S := B) (M := F.middle)
              selfDualMiddle :=
                (isSelfDualAlgebra_adjoinRoot p hpm).trans F.selfDualMiddle
              toTarget := F.toTarget
              surjective_toTarget := F.surjective_toTarget
              comp_eq := ?_ }⟩
    ext r
    show F.toTarget (algebraMap B F.middle (algebraMap R B r)) = algebraMap R A r
    rw [F.algebraMap_eq]
    exact (IsScalarTower.algebraMap_apply R B A r).symm

/-- **Every finite ring map factors through a finite free self-dual algebra by a surjection.**
Let `φ : R → A` be finite.  Then there is an `R`-algebra `C`, finite and free as an `R`-module and
isomorphic to its own `R`-linear dual, with a surjection `C → A` whose composite with `R → C` is
`φ`; concretely `C = R[x_1, …, x_n]/(f_1, …, f_n)` for monic `f_i`.

`A` is a finite `R`-module, so it is generated as an `R`-algebra by a finite family, and every
element of it is integral over `R`;
`Dualizing.nonempty_monicTowerFactorization_of_adjoin_eq_top` applies to that family. -/
theorem nonempty_monicTowerFactorization {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    (hφ : φ.Finite) : Nonempty (MonicTowerFactorization φ) := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Finite R A := hφ
  have : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  obtain ⟨s, hs⟩ : ∃ s : Finset A, Submodule.span R (s : Set A) = ⊤ :=
    Module.Finite.iff_fg.mp inferInstance
  let a : Fin s.card → A := fun i => ((s.equivFin.symm i : {x // x ∈ s}) : A)
  have hrange : Set.range a = (s : Set A) := by
    ext x
    refine ⟨?_, fun hx => ⟨s.equivFin ⟨x, hx⟩, by simp [a]⟩⟩
    rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  have htop : Algebra.adjoin R (Set.range a) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hsub : Submodule.span R (Set.range a) ≤
        Subalgebra.toSubmodule (Algebra.adjoin R (Set.range a)) :=
      Submodule.span_le.mpr Algebra.subset_adjoin
    exact hsub (by rw [hrange, hs]; exact Submodule.mem_top)
  exact nonempty_monicTowerFactorization_of_adjoin_eq_top s.card a
    (fun i => Algebra.IsIntegral.isIntegral (a i)) htop

end Dualizing

end
