module

public import StacksFrontier.RingTheory.Koszul.PowKoszulDerivedLimit
public import StacksFrontier.RingTheory.Koszul.PowModuleSystems
public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemSemilinearBimodule

/-!
# A Koszul system of differential graded bimodules, and Tag 0GZJ for it

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_m` be the Koszul differential
graded algebra with `d ξᵢ = fᵢ ^ m` and fix `t ≥ 1`. The algebra `K_t` is a differential graded
`(K_{t+n}, K_t)`-bimodule, through the transition homomorphism `τ_{t+n,t} : K_{t+n} → K_t` on the
left and its own multiplication on the right, and the identity of `K_t` is a semilinear
homomorphism between any two of these readings, because the transition homomorphisms compose.

So `({}_{t+n}K_t)` is a strict inverse system of differential graded bimodules in the sense of
`DifferentialGraded.StrictBimoduleSystem`, and
`DifferentialGraded.StrictBimoduleSystem.toBimoduleSystem` turns it into an inverse system of
bimodules in the sense of `DifferentialGraded.BimoduleSystem` whose comparison maps are *by
definition* the derived comparisons of the plain comparisons attached to the identity of `K_t`.
That is the hypothesis `hcmp` of `Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance`,
so Tag 0GZJ holds for this system with no coherence hypothesis left to supply; that is
`Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalanceRegular`.

The point of this file is that the hypotheses of Tag 0GZJ are satisfiable: the statement is not
vacuous. It is the bimodule counterpart of `Koszul.powRestrictedStrictModuleSystem`, which records
the same `({}_{t+n}K_t)` as a system of *modules*.

## Main definitions

* `Koszul.powRegularBimoduleSystem`: the system `({}_{t+n}K_t)` of differential graded
  `(K_{t+n}, K_t)`-bimodules, with the identity of `K_t` for every transition.
* `Koszul.powRegularBimoduleTrans`: its one-step semilinear transition homomorphisms, in the shape
  Tag 0GZJ asks for.

## Main results

* `Koszul.powRegularBimoduleSystem_cmp`: the comparison maps of the system are the derived
  comparisons of the plain ones — the hypothesis `hcmp` of Tag 0GZJ, here by `rfl`.
* `Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalanceRegular`: **Tag 0GZJ for this
  system**, with no coherence hypothesis.

## Implementation notes

*Left modules are right modules over the opposite algebra.* As everywhere in this development the
`n`-th algebra of `Koszul.powStrictAlgebraSystem` is the graded opposite of `K_{t+n}`, so the
source's `M_n` — a right differential graded `K_{t+n}`-module with a commuting action of `B` — is
a differential graded `(K_{t+n}^{opp}, B)`-bimodule. Here `B` is `K_t^{opp}` and `M_n` is `K_t`
itself.

*The order of the imports matters.* `CategoryTheory.Pretriangulated.IsDerivedLimit` asks for
`∀ n, (shiftFunctor (derivedCategory' B) n).Additive`, and at the concrete algebra `K_t^{opp}`
that instance is found only if the Koszul modules are imported before
`StacksFrontier/Algebra/DifferentialGraded/Module/InverseSystemSemilinearBimodule.lean` — instance
search tries candidates in reverse declaration order, and the order of the imports decides it.
The same happens with the pre-existing
`StacksFrontier/Algebra/DifferentialGraded/Module/InverseSystemStrictModule.lean`, so this is not a
feature of the new module; the imports below are therefore not in alphabetical order.

*Nothing is evaluated on an element.* The construction is an application of
`DifferentialGraded.StrictBimoduleSystem.ofRegularId`, whose only hypothesis is the equality
`τ_{t+n,t} ∘ τ_{t+m,t+n} = τ_{t+m,t}` of homomorphisms of algebras — which is
`Koszul.oppPowTransition_comp`. This is the discipline of `Koszul.powModuleSystems`: the
underlying module of a graded opposite algebra is produced by a choice, so a homomorphism of
graded opposite Koszul algebras must never be applied to an element.

## References

* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ)
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX) is the regular bimodule
  structure a homomorphism of differential graded algebras provides.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite DifferentialGraded.Bimodule

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t)

/-- **The system `({}_{t+n}K_t)` of differential graded bimodules over the Koszul algebras**: the
algebra `K_t`, with `K_{t+n}` acting on the left through the transition homomorphism `τ_{t+n,t}`
and `K_t` acting on the right by multiplication, and with the identity of `K_t` for every
transition homomorphism. The transitions compose because the transition homomorphisms of the
Koszul algebras do (`Koszul.oppPowTransition_comp`). -/
def powRegularBimoduleSystem :
    StrictBimoduleSystem (powStrictAlgebraSystem f ht) (oppAlgebra (powAlgebra f t)) :=
  StrictBimoduleSystem.ofRegularId (powStrictAlgebraSystem f ht) (oppAlgebra (powAlgebra f t))
    (fun n => oppPowTransition f ht (Nat.le_add_right t n))
    fun h => oppPowTransition_comp f ht (Nat.le_add_right t _) (Nat.add_le_add_left h t)

/-- The one-step semilinear transition homomorphisms of the system `({}_{t+n}K_t)` of bimodules,
in the shape Tag 0GZJ asks for: the identity of `K_t`, read as a homomorphism of differential
graded `(K_{t+n+1}, K_t)`-bimodules into the restriction along `τ_{t+n+1,t+n}`. -/
def powRegularBimoduleTrans (n : ℕ) :
    (powRegularBimoduleSystem f ht).toBimoduleSystem.obj (n + 1) ⟶
      Bimodule.restrictLeft ((powStrictAlgebraSystem f ht).trans (Nat.le_succ n))
        ((powRegularBimoduleSystem f ht).toBimoduleSystem.obj n) :=
  (powRegularBimoduleSystem f ht).trans (Nat.le_succ n)

/-- **The comparison maps of the system `({}_{t+n}K_t)` of bimodules are the derived comparisons
of the plain ones.** This is the hypothesis `hcmp` of
`Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance`, and for a system built by
`DifferentialGraded.StrictBimoduleSystem.toBimoduleSystem` it holds by `rfl`. -/
theorem powRegularBimoduleSystem_cmp (n : ℕ) :
    (powRegularBimoduleSystem f ht).toBimoduleSystem.cmp (Nat.le_succ n) =
      Bimodule.derivedTensorRestrictTrans ((powStrictAlgebraSystem f ht).trans (Nat.le_succ n))
        ((powRegularBimoduleSystem f ht).toBimoduleSystem.obj (n + 1))
        ((powRegularBimoduleSystem f ht).toBimoduleSystem.obj n)
        (Bimodule.tensorCompNatTransOfSemilinear
          ((powStrictAlgebraSystem f ht).trans (Nat.le_succ n))
          ((powRegularBimoduleSystem f ht).toBimoduleSystem.obj (n + 1))
          ((powRegularBimoduleSystem f ht).toBimoduleSystem.obj n)
          (powRegularBimoduleTrans f ht n)) :=
  (powRegularBimoduleSystem f ht).toBimoduleSystem_cmp (Nat.le_succ n)

/-- The tower `n ↦ {}_{t+n}K_t ⊗_{K_{t+n}}^𝐋 {}_{t+n}K_t` of `D(K_t^{opp}, d)`: the tensored
tower of Tag 0GZI for the system `Koszul.powRegularBimoduleSystem` of bimodules and the system
`Koszul.powRestrictedModuleSystem` of modules. It is the left-hand side of Tag 0GZJ for this
system. -/
abbrev powRegularTower : ℕᵒᵖ ⥤ derivedCategory' (oppAlgebra (powAlgebra f t)) :=
  (powRegularBimoduleSystem f ht).toBimoduleSystem.tower (powRestrictedModuleSystem f ht)

/-- The tower `n ↦ {}_{t+n}K_t ⊗_R^𝐋 K_t` of `D(K_t^{opp}, d)` for the system
`Koszul.powRegularBimoduleSystem` of bimodules: the right-hand side of Tag 0GZJ for this
system. -/
abbrev powRegularBaseTower : ℕᵒᵖ ⥤ derivedCategory' (oppAlgebra (powAlgebra f t)) :=
  (powBaseDegreeZeroDerivedTensorTower f t ht
    (powRegularBimoduleSystem f ht).toBimoduleSystem.obj (powRegularBimoduleTrans f ht)).tower

/-- **Tag 0GZJ for the system `({}_{t+n}K_t)` of bimodules.** With `M_n = K_t`, read as a
differential graded `(K_{t+n}, K_t)`-bimodule through the transition homomorphism, the derived
limits of `n ↦ M_n ⊗_R^𝐋 K_t` and of `n ↦ M_n ⊗_{K_{t+n}}^𝐋 K_t` are isomorphic.

This is `Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance` with every hypothesis on
the system discharged: it exhibits a system of bimodules whose comparison maps really are the
derived comparisons of its semilinear transition homomorphisms, so that statement is not
vacuous. -/
theorem nonempty_iso_of_isDerivedLimit_powKoszulTensorBalanceRegular
    [HasProduct fun n : ℕ => (powRegularTower f ht).obj (op n)]
    [HasProduct fun n : ℕ => (powRegularBaseTower f ht).obj (op n)]
    (K K' : derivedCategory' (oppAlgebra (powAlgebra f t)))
    (hK : Pretriangulated.IsDerivedLimit (powRegularTower f ht) K)
    (hK' : Pretriangulated.IsDerivedLimit (powRegularBaseTower f ht) K') :
    Nonempty (K ≅ K') :=
  nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance f ht
    (powRegularBimoduleSystem f ht).toBimoduleSystem (powRegularBimoduleTrans f ht)
    (powRegularBimoduleSystem_cmp f ht) K K' hK hK'

end Koszul

end
