module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRestrictLeft
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorPlainTower
public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemStrictModule

/-!
# A derived tensor tower from semilinear transitions of bimodules

A `DifferentialGraded.Bimodule.DerivedTensorTower` asks, among its data, for a comparison
`P_{n+1} ⊗_{A_{n+1}} Y|_{A_{n+1}} ⟶ P_n ⊗_{A_n} Y` of the plain tensor functors over two
different algebras. This file supplies that comparison from the datum one actually has in
practice: a homomorphism `P_{n+1} ⟶ P_n|_{τ_n}` of differential graded `(A_{n+1}, B)`-bimodules,
that is a semilinear homomorphism `P_{n+1} ⟶ P_n` over the transition homomorphism
`τ_n : A_{n+1} ⟶ A_n`. The comparison is
`DifferentialGraded.Bimodule.tensorCompNatTransOfSemilinear`, so a tower of derived tensor
products over a varying algebra needs no data in the derived category at all: algebras, modules
and bimodules with their transition homomorphisms, and the left orthogonality of the modules.

The tower so obtained agrees, one step at a time, with the tensored tower
`DifferentialGraded.BimoduleSystem.tower` of an inverse system of bimodules: if the comparisons of
a `DifferentialGraded.BimoduleSystem` are the derived
comparisons `DifferentialGraded.Bimodule.derivedTensorRestrictTrans` of these plain ones, and the
system of modules is the one underlying a `DifferentialGraded.StrictModuleSystem`, then the
one-step transition map of its tensored tower is the transition map of the derived tensor tower.

## Main definitions

* `DifferentialGraded.Bimodule.DerivedTensorTower.ofSemilinear`: the derived tensor tower built
  from semilinear transition homomorphisms of the bimodules.

## Main results

* `DifferentialGraded.BimoduleSystem.towerMap_ofSemilinear_towerMap`: the one-step transition map
  of the tensored tower of an inverse system of bimodules is the transition map of the derived
  tensor tower, as soon as the comparison of the system is the derived comparison of the plain
  one.

## Implementation notes

*Why the agreement is an identity of terms.* `DifferentialGraded.BimoduleSystem.towerMap` is the
derived tensor product of the transition map of the system of modules followed by the comparison
of the system of bimodules, and
`DifferentialGraded.Bimodule.DerivedTensorTower.towerMap` is the derived tensor product of
`DifferentialGradedModule.derivedTrans` of the transition homomorphism followed by
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans` of the plain comparison. The transition
map of the system of modules underlying a strict one *is* `DifferentialGradedModule.derivedTrans`
of the transition homomorphism, by
`DifferentialGraded.StrictModuleSystem.toModuleSystem`; so once the comparison of the system is
rewritten into the derived comparison the two sides are the same term, and no coherence in the
derived category is used.

*The two indexings.* An inverse system indexes its transitions by all pairs `n ≤ m`, a derived
tensor tower only by the one-step maps; the agreement below is therefore stated for
`Nat.le_succ`, which is the only index at which both sides are defined.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the plain tensor
  functor, [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) the derived one and
  [Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) where such a tower is used.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded

open DifferentialGradedModule

variable {R : Type u} [CommRing R]

namespace Bimodule.DerivedTensorTower

variable {B : DifferentialGradedAlgebra.{u, u} R}

/-- **A derived tensor tower from semilinear transition homomorphisms of the bimodules.** The
comparison of the plain tensor functors is
`DifferentialGraded.Bimodule.tensorCompNatTransOfSemilinear` of the homomorphism
`P_{n+1} ⟶ P_n|_{τ_n}`; everything else is the data handed in. -/
def ofSemilinear (alg : ℕ → DifferentialGradedAlgebra.{u, u} R)
    (algTrans : ∀ n : ℕ, (alg (n + 1)).Hom (alg n))
    (bimod : ∀ n : ℕ, Bimodule (alg n) B)
    (bimodTrans : ∀ n : ℕ, bimod (n + 1) ⟶ Bimodule.restrictLeft (algTrans n) (bimod n))
    (mod : ∀ n : ℕ, DifferentialGradedModule.{u, u, u} (alg n))
    (modTrans : ∀ n : ℕ, mod (n + 1) ⟶ restrictScalars (algTrans n) (mod n))
    (orth : ∀ n : ℕ,
      (acyclic' (alg n)).leftOrthogonal ((toHomotopyCategory (alg n)).obj (mod n))) :
    DerivedTensorTower B where
  alg := alg
  trans := algTrans
  bimod := bimod
  mod := mod
  modTrans := modTrans
  plainCmp := fun n =>
    tensorCompNatTransOfSemilinear (algTrans n) (bimod (n + 1)) (bimod n) (bimodTrans n)
  leftOrthogonal := orth

/-- The algebras of `DifferentialGraded.Bimodule.DerivedTensorTower.ofSemilinear` are the ones
handed in. -/
@[simp] theorem ofSemilinear_alg (alg : ℕ → DifferentialGradedAlgebra.{u, u} R)
    (algTrans : ∀ n : ℕ, (alg (n + 1)).Hom (alg n)) (bimod : ∀ n : ℕ, Bimodule (alg n) B)
    (bimodTrans : ∀ n : ℕ, bimod (n + 1) ⟶ Bimodule.restrictLeft (algTrans n) (bimod n))
    (mod : ∀ n : ℕ, DifferentialGradedModule.{u, u, u} (alg n))
    (modTrans : ∀ n : ℕ, mod (n + 1) ⟶ restrictScalars (algTrans n) (mod n))
    (orth : ∀ n : ℕ,
      (acyclic' (alg n)).leftOrthogonal ((toHomotopyCategory (alg n)).obj (mod n))) :
    (ofSemilinear alg algTrans bimod bimodTrans mod modTrans orth).alg = alg := rfl

/-- The bimodules of `DifferentialGraded.Bimodule.DerivedTensorTower.ofSemilinear` are the ones
handed in. -/
@[simp] theorem ofSemilinear_bimod (alg : ℕ → DifferentialGradedAlgebra.{u, u} R)
    (algTrans : ∀ n : ℕ, (alg (n + 1)).Hom (alg n)) (bimod : ∀ n : ℕ, Bimodule (alg n) B)
    (bimodTrans : ∀ n : ℕ, bimod (n + 1) ⟶ Bimodule.restrictLeft (algTrans n) (bimod n))
    (mod : ∀ n : ℕ, DifferentialGradedModule.{u, u, u} (alg n))
    (modTrans : ∀ n : ℕ, mod (n + 1) ⟶ restrictScalars (algTrans n) (mod n))
    (orth : ∀ n : ℕ,
      (acyclic' (alg n)).leftOrthogonal ((toHomotopyCategory (alg n)).obj (mod n))) :
    (ofSemilinear alg algTrans bimod bimodTrans mod modTrans orth).bimod = bimod := rfl

/-- The comparison of the plain tensor functors of
`DifferentialGraded.Bimodule.DerivedTensorTower.ofSemilinear` is
`DifferentialGraded.Bimodule.tensorCompNatTransOfSemilinear` of the semilinear transition
homomorphism. -/
@[simp] theorem ofSemilinear_plainCmp (alg : ℕ → DifferentialGradedAlgebra.{u, u} R)
    (algTrans : ∀ n : ℕ, (alg (n + 1)).Hom (alg n)) (bimod : ∀ n : ℕ, Bimodule (alg n) B)
    (bimodTrans : ∀ n : ℕ, bimod (n + 1) ⟶ Bimodule.restrictLeft (algTrans n) (bimod n))
    (mod : ∀ n : ℕ, DifferentialGradedModule.{u, u, u} (alg n))
    (modTrans : ∀ n : ℕ, mod (n + 1) ⟶ restrictScalars (algTrans n) (mod n))
    (orth : ∀ n : ℕ,
      (acyclic' (alg n)).leftOrthogonal ((toHomotopyCategory (alg n)).obj (mod n)))
    (n : ℕ) :
    (ofSemilinear alg algTrans bimod bimodTrans mod modTrans orth).plainCmp n =
      tensorCompNatTransOfSemilinear (algTrans n) (bimod (n + 1)) (bimod n) (bimodTrans n) :=
  rfl

end Bimodule.DerivedTensorTower

/-! ### Agreement with the tensored tower of an inverse system -/

/-- **The two transition maps agree.** Let `(A_n)` be a strict inverse system of differential
graded algebras, `(M_n)` an inverse system of differential graded bimodules over it and `(N_n)` a
strict inverse system of differential graded modules whose terms are orthogonal on the left to
the acyclic modules. If the one-step comparison of `(M_n)` is the derived comparison
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans` of the plain comparison attached to
semilinear transition homomorphisms `M_{n+1} ⟶ M_n|_{τ_n}`, then the one-step transition map of
the tensored tower of `(M_n)` is the transition map of the derived tensor tower built from those
transition homomorphisms. -/
theorem BimoduleSystem.towerMap_ofSemilinear_towerMap {B : DifferentialGradedAlgebra.{u, u} R}
    (T : StrictAlgebraSystem R) (M : BimoduleSystem T.toAlgebraSystem B)
    (N : StrictModuleSystem T)
    (bimodTrans : ∀ n : ℕ,
      M.obj (n + 1) ⟶ Bimodule.restrictLeft (T.trans (Nat.le_succ n)) (M.obj n))
    (hcmp : ∀ n : ℕ, M.cmp (Nat.le_succ n) =
      Bimodule.derivedTensorRestrictTrans (T.trans (Nat.le_succ n)) (M.obj (n + 1)) (M.obj n)
        (Bimodule.tensorCompNatTransOfSemilinear (T.trans (Nat.le_succ n)) (M.obj (n + 1))
          (M.obj n) (bimodTrans n)))
    (orth : ∀ n : ℕ,
      (acyclic' (T.alg n)).leftOrthogonal ((toHomotopyCategory (T.alg n)).obj (N.mod n)))
    (n : ℕ) :
    M.towerMap N.toModuleSystem (Nat.le_succ n) =
      (Bimodule.DerivedTensorTower.ofSemilinear T.alg (fun k => T.trans (Nat.le_succ k)) M.obj
        bimodTrans N.mod (fun k => N.trans (Nat.le_succ k)) orth).towerMap n := by
  rw [BimoduleSystem.towerMap, hcmp n]
  rfl

end DifferentialGraded

end
