module

public import StacksFrontier.Algebra.Homology.RightDerivedBiprod
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.EmptySupportVanishing
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Polynomial
public import StacksFrontier.Topology.Dimension.Krull
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The empty-support case of Tag 0BEM

[Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM) asserts that the Euler
characteristics of the twists of a coherent sheaf `ℱ` on a proper scheme over a field are the
values of a rational polynomial `P` which is **zero or** of total degree at most
`dim Supp ℱ`. The zero disjunct is not decoration: when `Supp ℱ = ∅` the dimension of the
support is `⊥`, and *no* natural number is `≤ ⊥`, so the degree bound cannot be met by any
polynomial whatever — only `P = 0` can discharge that case.

That is exactly the case the induction of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_dimension_descent`
(`StacksFrontier/AlgebraicGeometry/TwistedSheaf/Polynomial.lean`) does not reach: its
hypothesis `hdim` bounds a natural number by `topologicalKrullDim (Supp ℱ)` and is therefore
unsatisfiable on empty support. This file closes it, **unconditionally** — it needs neither of
that theorem's two geometric inputs and no Tag beyond what is already in the library — by the
only route available: a sheaf with empty support is a zero object, every twist of a zero object
is a zero object, and the Euler characteristic of a zero object is `0`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_eq_zero_of_isZero`: `χ(X, 0) = 0`. This is the
  arithmetic fact the degenerate disjunct needs.
* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_supp_eq_empty`: the empty-support
  case of Tag 0BEM, with the conclusion in the shape the tagged statement gives it.
* `SheafOfModules.isZero_of_supp_eq_empty` of
  `StacksFrontier.AlgebraicGeometry.DevissageNoetherian.EmptySupportVanishing`, imported here and
  stated for an arbitrary sheaf of rings on a topological space: a sheaf of modules with empty support
  is a zero object.
* `AlgebraicGeometry.isZero_twistedSheaf_of_isZero`: every twist of a zero object is a zero
  object.
* `CategoryTheory.Equivalence.isZero_functor_obj` and
  `CategoryTheory.Functor.isZero_rightDerived_obj_of_isZero`: the two general facts the above
  rest on, neither of which is in Mathlib. The second is
  `CategoryTheory.Functor.isZero_rightDerived_obj` of
  `StacksFrontier.Algebra.Homology.RightDerivedBiprod`, restated here.
* `AlgebraicGeometry.topologicalKrullDim_supp_eq_bot_iff`: the dimension of the support is `⊥`
  exactly on empty support, which is what makes this case and the dimension-descent case
  exhaustive.

## Implementation notes

**Why `χ` of a zero object is not immediate.** `AlgebraicGeometry.cohomologyOverField` is a
right derived functor followed by restriction of scalars, and Mathlib carries no `Additive`
instance for `CategoryTheory.Functor.rightDerived`, so `CategoryTheory.Functor.map_isZero` does
not apply to it. `CategoryTheory.Functor.isZero_rightDerived_obj_of_isZero` supplies the fact
instead, by the argument of Mathlib's `Functor.isZero_rightDerived_obj_injective_succ` run at
degree `0` as well: a zero object is injective, so it is its own injective resolution, and that
resolution is the zero complex in *every* degree rather than only in positive ones.

**Why tensoring needs the invertibility.** `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`
  is a sheafified presheaf
tensor product, and neither it nor `Stacks.SheafOfModules.TensorSheafification.sheafify` is known
  additive here, so "tensoring
with a zero object gives a zero object" is not available by functoriality. It is available from
the invertibility that the twist already assumes: tensoring by an invertible sheaf is an
*equivalence* (`Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence`), and an
equivalence preserves zero objects — which is `CategoryTheory.Equivalence.isZero_functor_obj`,
proved from the adjunction's hom-equivalences rather than from additivity, since an equivalence
of preadditive categories is not known additive either.

**The tag is not placed.** Tag 0BEM sits on the Euler-characteristic theorem, which
still depends on Tags 02OL, 02OM, 02OZ, 02P2, 089W and 0AYT (4)+(5); this file closes one
case of it, not the theorem.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

universe v u

namespace CategoryTheory

/-- **An equivalence of categories preserves zero objects.** The hom-sets out of and into
`E.functor.obj Z` are in bijection, by the two adjunctions of the equivalence, with hom-sets out
of and into `Z`, each of which is a singleton. No additivity is used, and none is available: an
equivalence of preadditive categories carries no `CategoryTheory.Functor.Additive` instance, so
`CategoryTheory.Functor.map_isZero` does not apply. -/
theorem Equivalence.isZero_functor_obj {C : Type*} {D : Type*} [Category C] [Category D]
    (E : C ≌ D) {Z : C} (h : IsZero Z) : IsZero (E.functor.obj Z) where
  unique_to Y := by
    obtain ⟨u⟩ := h.unique_to (E.inverse.obj Y)
    have := u
    exact ⟨Equiv.unique (E.toAdjunction.homEquiv Z Y)⟩
  unique_from Y := by
    obtain ⟨u⟩ := h.unique_from (E.symm.functor.obj Y)
    have := u
    exact ⟨Equiv.unique (E.symm.toAdjunction.homEquiv Y Z).symm⟩

/-- **The right derived functors of an additive functor vanish on a zero object**, in every
degree including degree zero.

Mathlib's `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ` gives this for an
injective object in positive degrees, where the chosen resolution `InjectiveResolution.self` is
the zero object. A zero object is injective and its own resolution is zero in degree `0` too, so
the same argument reaches degree `0`. This is what `CategoryTheory.Functor.map_isZero` cannot
supply: `CategoryTheory.Functor.rightDerived` has no `Additive` instance in Mathlib. -/
@[ega "0 13.7.7.4" "partial"]
theorem Functor.isZero_rightDerived_obj_of_isZero {C : Type*} {D : Type*} [Category C]
    [Category D] [Abelian C] [Abelian D] [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    (n : ℕ) {Z : C} (hZ : IsZero Z) : IsZero ((F.rightDerived n).obj Z) :=
  F.isZero_rightDerived_obj n hZ

end CategoryTheory

namespace Stacks.SheafOfModules

/-- **The sheaf tensor product of a zero object with an invertible sheaf of modules is a zero
object.** The braiding puts the zero object in the second variable, where tensoring by the
invertible factor is an equivalence, and an equivalence preserves zero objects.

The invertibility hypothesis is stated with `AlgebraicGeometry.SheafOfModules.IsInvertible`,
which is the class the twists of
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/Basic.lean` assume; the equivalence criterion
is stated with `Stacks.SheafOfModules.IsInvertible`, so the witness is carried across once by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` and nothing is restated. -/
theorem isZero_tensorSheaf_of_isZero {X : AlgebraicGeometry.Scheme.{u}} (M A : X.Modules)
    [hA : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hM : IsZero M) :
    IsZero ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj (M)).obj (A)))
      :=
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
      (X.ringCatSheaf.2)⟩).obj A
  have : T.IsEquivalence :=
    (isInvertible_iff_tensorLeftFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 A).mp
      ((isInvertible_iff_algebraicGeometry X.presheaf X.ringCatSheaf.2 A).mpr hA)
  IsZero.of_iso (T.asEquivalence.isZero_functor_obj hM)
    (tensorSheafBraiding X.presheaf X.ringCatSheaf.2 M A)

end Stacks.SheafOfModules

namespace AlgebraicGeometry

/-! ### Vanishing of the Euler characteristic on a zero object -/

section EulerCharacteristic

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The cohomology of a zero object vanishes in every degree.** -/
theorem isZero_cohomologyOverField_of_isZero {G : X.Modules} (hG : IsZero G) (n : ℕ) :
    IsZero (cohomologyOverField k f G n) := by
  unfold cohomologyOverField
  exact Functor.map_isZero _ (Functor.isZero_rightDerived_obj_of_isZero
    (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))) n hG)

/-- **The Euler characteristic of a zero object is zero**: `χ(X, 0) = 0`. Every cohomology group
vanishes, so every term of the alternating sum does. -/
theorem eulerCharacteristic_eq_zero_of_isZero [IsProper f] (G : X.Modules)
    (hG : SheafOfModules.IsCoherent G) (h : IsZero G) :
    @eulerCharacteristic k _ X f _ G hG = 0 := by
  rw [eulerCharacteristic_eq_finsum]
  have hz : ∀ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f G n) : ℤ) = 0 := by
    intro n
    have := ModuleCat.subsingleton_of_isZero (isZero_cohomologyOverField_of_isZero k f h n)
    rw [Module.finrank_zero_of_subsingleton]
    simp
  simp [hz]

end EulerCharacteristic

/-! ### A sheaf with empty support is a zero object -/

/-- **The dimension of the support is `⊥` exactly on empty support.** This is what makes the
empty-support case below and the hypothesis `hdim` of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_dimension_descent` exhaustive: on
nonempty support the Krull dimension is at least `0`, so `hdim` is satisfiable, and on empty
support it is `⊥` and no natural number meets it. -/
theorem topologicalKrullDim_supp_eq_bot_iff {X : Scheme.{u}} (F : X.Modules) :
    topologicalKrullDim (SheafOfModules.supp F) = ⊥ ↔ SheafOfModules.supp F = ∅ := by
  rw [topologicalKrullDim_eq_bot_iff_isEmpty, isEmpty_subtype,
    Set.eq_empty_iff_forall_notMem]

/-! ### The twists of a zero object -/

section Twists

variable {X : Scheme.{u}} {r : ℕ} (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- **Every fold of tensor products with invertible sheaves fixes a zero object.** -/
theorem isZero_twistList_of_isZero (e : Fin r → ℤ) :
    ∀ (l : List (Fin r)) (M : X.Modules), IsZero M → IsZero (twistList L e l M) := by
  intro l
  induction l with
  | nil => exact fun _ hM => hM
  | cons i t ih =>
    refine fun M hM => ih _ ?_
    have := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
      X.ringCatSheaf.2 (L i) (e i)
    exact Stacks.SheafOfModules.isZero_tensorSheaf_of_isZero M _ hM

/-- **Every twist of a zero object is a zero object.** -/
theorem isZero_twistedSheaf_of_isZero {F : X.Modules} (hF : IsZero F) (n : Fin r → ℤ) :
    IsZero (twistedSheaf F L n) :=
  isZero_twistList_of_isZero L n (List.finRange r) F hF

end Twists

/-! ### The empty-support case of Tag 0BEM -/

/-- **The empty-support case of [Stacks, Tag 0BEM].** If the support of the coherent sheaf `ℱ`
is empty then the zero polynomial computes the Euler characteristics of all of its twists, which
is the degenerate disjunct of the tag's conclusion.

This case is **not** covered by
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_dimension_descent`, whose hypothesis
`hdim` bounds a natural number by `topologicalKrullDim (Supp ℱ) = ⊥`; and it needs neither of
that theorem's geometric inputs. A sheaf with empty support is a zero object, so is every twist
of it, and the Euler characteristic of a zero object is `0`. -/
theorem exists_eulerPolynomial_twistedSheaf_of_supp_eq_empty (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)] (F : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hsupp : SheafOfModules.supp F = ∅) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) := by
  refine ⟨0, Or.inl rfl, fun n => ?_⟩
  rw [map_zero]
  rw [eulerCharacteristic_eq_zero_of_isZero k f _ (@twistedSheaf_isCoherent X r F L _ hF n)
    (isZero_twistedSheaf_of_isZero L (SheafOfModules.isZero_of_supp_eq_empty F hsupp) n)]
  simp

end AlgebraicGeometry

end
