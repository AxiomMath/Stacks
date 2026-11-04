module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ChainEnvelopeTower07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.ChainDeRham07Q9

/-!
# The base change map along a tower of completed `p`-th root extensions

Let `D_0 ⟶ D_1 ⟶ ⋯ ⟶ D_n` be a tower of completed extensions of [Stacks, Lemma 60.25.3, Tag 07N1],
`D_{k+1} = (D_k[z]⟨ξ⟩/(ξ - (z^p - λ_k)))^∧` (`Crystalline.PrimeTower07Q9`), each `D_k` carrying
the `p`-adically completed divided power forms of `D_k` itself.  If along every single extension
the cones of the base change maps of completed de Rham complexes of integrable modules are killed
by `p`, then along the whole tower they are killed by `p ^ n`.

## Main definitions

* `Crystalline.PrimeTower07Q9.algebraA07Q9` — the `A`-algebra structure of the top of a tower.
* `Crystalline.PrimeTower07Q9.algebraTop07Q9` — the top as an algebra over the base.
* `Crystalline.PrimeTower07Q9.formsMap07Q9` — the comparison of forms along the tower.

## Main results

* `Crystalline.PrimeTower07Q9.baseChangeConeKilled07Q9_tower` — killed by `p ^ n` along a tower
  of length `n`, given killed by `p` along each extension.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public noncomputable section

open DividedPowers CategoryTheory

universe u

namespace Crystalline

open CompletedDeRham

/-! ### One extension -/

section Step

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (hp : p ≠ 0) (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
  (lam : (B : Type u))

/-- The structure map of a completed extension is a divided power morphism, read for the
`A`-algebra map of the scalar tower. -/
theorem isDPMorphism_completedPrimeStep07Q9 :
    DividedPowers.IsDPMorphism B.dividedPowers (completedPrimeStep07Q9 B p hp hB lam).dividedPowers
      (IsScalarTower.toAlgHom A (B : Type u)
        (completedPrimeStep07Q9 B p hp hB lam : Type u)).toRingHom :=
  (completedPrimeStepι07Q9 B p hp hB lam).isDPMorphism

/-- **The comparison of forms along one completed extension** `D → D'`. -/
def completedPrimeStepForms07Q9 (i : ℕ) :
    completedDividedPowerForms p A B.dividedPowers i →ₛₗ[algebraMap (B : Type u)
        (completedPrimeStep07Q9 B p hp hB lam : Type u)]
      completedDividedPowerForms p A (completedPrimeStep07Q9 B p hp hB lam).dividedPowers i :=
  completedMapDifferentialForms p A B.dividedPowers
    (completedPrimeStep07Q9 B p hp hB lam).dividedPowers
    (IsScalarTower.toAlgHom A (B : Type u) (completedPrimeStep07Q9 B p hp hB lam : Type u))
    (isDPMorphism_completedPrimeStep07Q9 A B p hp hB lam) i

end Step

namespace PrimeTower07Q9

variable (A : Type u) [CommRing A] {p : ℕ}

/-- **The top of a tower as an algebra over its base**, through the composite of the structure
maps. -/
abbrev algebraTop07Q9 {B : DividedPowerRing.{u}} {n : ℕ} (T : PrimeTower07Q9 p B n) :
    Algebra (B : Type u) (T.top : Type u) :=
  T.toTop.toRingHom.toAlgebra

variable {A}

/-- **The composite of the structure maps of a tower, as a map of `A`-algebras**, for any
`A`-algebra structure on the top compatible with the structure maps. -/
def toTopAlgHom07Q9 {B : DividedPowerRing.{u}} {n : ℕ} (T : PrimeTower07Q9 p B n)
    [Algebra A (B : Type u)] [Algebra A (T.top : Type u)]
    (hc : ∀ a : A, T.toTop (algebraMap A (B : Type u) a) = algebraMap A (T.top : Type u) a) :
    (B : Type u) →ₐ[A] (T.top : Type u) :=
  { T.toTop.toRingHom with commutes' := hc }

/-- **The comparison of forms along a tower**, the comparison of completed forms along the
composite of its structure maps. -/
abbrev formsMap07Q9 {B : DividedPowerRing.{u}} {n : ℕ} (T : PrimeTower07Q9 p B n)
    [Algebra A (B : Type u)] [Algebra A (T.top : Type u)]
    (hc : ∀ a : A, T.toTop (algebraMap A (B : Type u) a) = algebraMap A (T.top : Type u) a)
    (i : ℕ) :
    letI := algebraTop07Q9 T
    completedDividedPowerForms p A B.dividedPowers i →ₛₗ[algebraMap (B : Type u) (T.top : Type u)]
      completedDividedPowerForms p A T.top.dividedPowers i :=
  completedMapDifferentialForms p A B.dividedPowers T.top.dividedPowers (toTopAlgHom07Q9 T hc)
    T.toTop.isDPMorphism i

/-- The compatibility of the `A`-algebra structures passes from a tower to the rest of it. -/
theorem toTop_algebraMap_rest07Q9 {B : DividedPowerRing.{u}} [Algebra A (B : Type u)] {n : ℕ}
    (hp : p ≠ 0) (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
    (lam : (B : Type u)) (rest : PrimeTower07Q9 p (completedPrimeStep07Q9 B p hp hB lam) n)
    [Algebra A (rest.top : Type u)]
    (hc : ∀ a : A, (cons hp hB lam rest).toTop (algebraMap A (B : Type u) a) =
      algebraMap A (rest.top : Type u) a) (a : A) :
    rest.toTop (algebraMap A (completedPrimeStep07Q9 B p hp hB lam : Type u) a) =
      algebraMap A (rest.top : Type u) a := by
  refine Eq.trans ?_ (hc a)
  show _ = rest.toTop (completedPrimeStepι07Q9 B p hp hB lam (algebraMap A (B : Type u) a))
  congr 1

variable (A) in
/-- **Along a tower of length `n`, the cones are killed by `p ^ n`**, for the genuine completed
forms, as soon as along every single completed extension of [Stacks, Tag 07N1] they are killed by
`p`.  The proof is by induction on the tower, through the transitivity
`Crystalline.CompletedDeRham.genuineBaseChangeConeKilled07Q9_trans`. -/
theorem genuineBaseChangeConeKilled07Q9_tower
    (hstep : ∀ (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (hp : p ≠ 0)
      (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
      (lam : (B : Type u)),
      GenuineBaseChangeConeKilled07Q9 p A (B : Type u) B.dividedPowers
        (completedPrimeStep07Q9 B p hp hB lam : Type u)
        (completedPrimeStep07Q9 B p hp hB lam).dividedPowers
        (IsScalarTower.toAlgHom A (B : Type u) (completedPrimeStep07Q9 B p hp hB lam : Type u))
        (isDPMorphism_completedPrimeStep07Q9 A B p hp hB lam) (fun _ ↦ rfl) (p : ℤ))
    {B : DividedPowerRing.{u}} {n : ℕ} (T : PrimeTower07Q9 p B n) :
    ∀ [Algebra A (B : Type u)] [Algebra A (T.top : Type u)]
      (hc : ∀ a : A, T.toTop (algebraMap A (B : Type u) a) = algebraMap A (T.top : Type u) a),
      letI := algebraTop07Q9 T
      GenuineBaseChangeConeKilled07Q9 p A (B : Type u) B.dividedPowers (T.top : Type u)
        T.top.dividedPowers (toTopAlgHom07Q9 T hc) T.toTop.isDPMorphism (fun _ ↦ rfl)
        ((p : ℤ) ^ n) := by
  induction T with
  | nil B =>
    intro instB instTop hc
    have h : instB = instTop := Algebra.algebra_ext _ _ hc
    subst h
    rw [pow_zero]
    exact genuineBaseChangeConeKilled07Q9_self p A (B : Type u) B.dividedPowers _ _ (fun _ ↦ rfl)
  | @cons B n hp hB lam rest ih =>
    intro _ instTop hc
    let : Algebra A (rest.top : Type u) := instTop
    let := algebraTop07Q9 rest
    let : Algebra (B : Type u) (rest.top : Type u) := algebraTop07Q9 (cons hp hB lam rest)
    have : IsScalarTower (B : Type u) (completedPrimeStep07Q9 B p hp hB lam : Type u)
        (rest.top : Type u) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hr := toTop_algebraMap_rest07Q9 hp hB lam rest hc
    rw [pow_succ']
    exact genuineBaseChangeConeKilled07Q9_trans p A (B : Type u) B.dividedPowers
      (completedPrimeStep07Q9 B p hp hB lam : Type u)
      (completedPrimeStep07Q9 B p hp hB lam).dividedPowers (rest.top : Type u)
      rest.top.dividedPowers _ _ (fun _ ↦ rfl) (toTopAlgHom07Q9 rest hr)
      rest.toTop.isDPMorphism (fun _ ↦ rfl)
      (toTopAlgHom07Q9 (cons hp hB lam rest) hc) (cons hp hB lam rest).toTop.isDPMorphism
      (fun _ ↦ rfl) (hstep B hp hB lam) (ih hr)

end PrimeTower07Q9

end Crystalline

end
