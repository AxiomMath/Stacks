module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestrictionComposite
public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemProIsomorphism

/-!
# Strict inverse systems of differential graded algebras

An inverse system of differential graded algebras in the sense of
`DifferentialGraded.AlgebraSystem` carries the identification of a two-step restriction of
scalars with a one-step one as data. When the transition homomorphisms compose on the nose that
identification is `DifferentialGradedModule.derivedRestrictionComp` and need not be assumed; this
file records such a *strict* system and the inverse system it gives.

It also records the map in the derived category that a homomorphism `M ⟶ N|_A` of differential
graded modules produces, which is what the transition maps of an inverse system of modules over
such a system are built from.

## Main definitions

* `DifferentialGradedModule.derivedTrans`: a homomorphism `M ⟶ N|_A` of differential graded
  modules, read as a map `M ⟶ N|_A` in the derived category of `A`.
* `DifferentialGraded.StrictAlgebraSystem` and
  `DifferentialGraded.StrictAlgebraSystem.toAlgebraSystem`: a strict inverse system of
  differential graded algebras and the inverse system it gives.

## Implementation notes

*What is here and what is not.* Only the passage from a strict system of algebras to a
`DifferentialGraded.AlgebraSystem` is proved. The corresponding passage one level up — from
differential graded modules `N_n` with homomorphisms `N_m ⟶ N_n|_{A_m}` whose underlying linear
maps compose, to a `DifferentialGraded.ModuleSystem` — is not: its one compatibility is an
identity between components of `DifferentialGradedModule.derivedRestrictionFactorization` and of
`DifferentialGradedModule.derivedRestrictionComp`, and the rewrites it needs are blocked because
the two sides of a composition in a localized category are presented at different instance paths
for `Quiver.Hom`. `DifferentialGradedModule.derivedTrans` is the map that construction would use.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- A homomorphism `M ⟶ N|_A` of differential graded modules, read in the derived category of
`A`: push it into the derived category and compose with the defining factorization of derived
restriction of scalars. -/
def derivedTrans (φ : A.Hom B) {M : DifferentialGradedModule.{u, u, u} A}
    {N : DifferentialGradedModule.{u, u, u} B} (u : M ⟶ restrictScalars φ N) :
    (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj M) ⟶
      (derivedRestriction φ).obj
        ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N)) :=
  (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map u) ≫
    (derivedRestrictionFactorization φ).inv.app ((toHomotopyCategory B).obj N)

end DifferentialGradedModule

namespace DifferentialGraded

open DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- **A strict inverse system of differential graded algebras:** an algebra `A_n` for every `n`
and a transition homomorphism `A_m → A_n` for every `n ≤ m`, composing on the nose. -/
structure StrictAlgebraSystem (R : Type u) [CommRing R] where
  /-- The `n`-th differential graded algebra of the system. -/
  alg : ℕ → DifferentialGradedAlgebra.{u, u} R
  /-- The transition homomorphism `A_m → A_n` of the system, for `n ≤ m`. -/
  trans : ∀ {n m : ℕ}, n ≤ m → (alg m).Hom (alg n)
  /-- The transition homomorphisms compose. -/
  trans_comp : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k),
    (trans h).comp (trans h') = trans (h.trans h')

namespace StrictAlgebraSystem

/-- The inverse system of differential graded algebras underlying a strict one: the
identification of a two-step restriction of scalars with a one-step one is the one that
restriction along a composite provides, so it is not assumed. -/
def toAlgebraSystem (T : StrictAlgebraSystem R) : AlgebraSystem R where
  alg := T.alg
  trans := T.trans
  restrComp h h' :=
    derivedRestrictionComp (T.trans h') (T.trans h) ≪≫
      eqToIso (congrArg (fun α => derivedRestriction α) (T.trans_comp h h'))

/-- The `n`-th algebra of `T.toAlgebraSystem` is the `n`-th algebra of `T`. -/
@[simp] theorem toAlgebraSystem_alg (T : StrictAlgebraSystem R) (n : ℕ) :
    T.toAlgebraSystem.alg n = T.alg n := rfl

/-- The transition homomorphism `A_m → A_n` of `T.toAlgebraSystem` is that of `T`. -/
@[simp] theorem toAlgebraSystem_trans (T : StrictAlgebraSystem R) {n m : ℕ} (h : n ≤ m) :
    T.toAlgebraSystem.trans h = T.trans h := rfl

end StrictAlgebraSystem

end DifferentialGraded

end
