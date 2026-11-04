module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Finite.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Coherent sheaves with fixed Hilbert polynomial (Stacks 0DNF), and the reindexings 0DP7, 0DP8

Let `f : X ⟶ B` be a separated morphism of algebraic spaces of finite presentation, let `L` be an
invertible `𝒪_X`-module and let `P : ℤ → ℤ` be a numerical polynomial.  Stacks 0DNF forms the
substack `Coh^P_{X/B} = Coh^{P,L}_{X/B} ⊆ Coh_{X/B}` whose objects `(T ⟶ B, 𝓕)` are those
satisfying

`P(n) = χ(X_t, 𝓕_t ⊗_{𝒪_{X_t}} L_t^{⊗ n})`  for every `n ∈ ℤ` and every `t ∈ T`,

and it does so by *specialising* Situation 0DNC — the standing data of a set `I`, a perfect object
`E i` of `D(𝒪_X)` for each `i ∈ I` and prescribed invariants `P : I → ℤ` — to `I = ℤ` and the
family `n ↦ L^{⊗ n}`.  That specialisation is what this file constructs, together with the
membership condition itself and the two reindexings of it which are Stacks 0DP7 and 0DP8.

## Main definitions

* `AlgebraicGeometry.Space.invertibleTensorPower`: the integer tensor power `L^{⊗ n}` of an
  invertible module on the small étale ringed site of an algebraic space.  This is the tensor
  power of Stacks 01CU at the site spelling that `AlgebraicGeometry.Space.twistStep` already uses.
* `AlgebraicGeometry.Space.invertibleTwistObject`: the object `L^{⊗ n}` of `D(𝒪_X)`, that is, the
  image of `L^{⊗ n}` under the embedding of modules in degree zero.
* `AlgebraicGeometry.Space.NumericalSituation.ofInvertibleTwists`: **Stacks 0DNF**, the standing
  data of Situation 0DNC specialised to `I = ℤ` and `n ↦ L^{⊗ n}` with the given `P`.
* `AlgebraicGeometry.Space.IsPrescribedTwistedEuler`: **Stacks 0DNF**, the membership condition
  `P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` of the source, stated for a given family of fibrewise twisted
  Euler characteristics.

## Main results

* `AlgebraicGeometry.Space.isPrescribedTwistedEuler_iff_shift`: **Stacks 0DP7**, the final
  statement of the source at the level of membership conditions — the condition for `P` and `𝓕`
  is the condition for `P'(t) = P(t + 1)` and `𝓕 ⊗ L`, whose twisted Euler characteristics are
  those of `𝓕` shifted by one.
* `AlgebraicGeometry.Space.isPrescribedTwistedEuler_iff_reindexMul`: **Stacks 0DP8**, the
  equality `Quot^{P,L} = Quot^{P',L^{⊗ n}}` with `P'(t) = P(n t)` at the level of membership
  conditions, for `n ≠ 0`.

## Implementation notes

**What `Coh^P_{X/B}` is here, and what it is not.**  Situation 0DNC is formalized in
`StacksFrontier/AlgebraicGeometry/Quot/NumericalInvariants.lean` as the standing data only; the
implementation notes there record that the derived pullback `E_{i,T}`, the derived tensor product
`E_{i,T} ⊗^𝐋 𝓕`, the Euler-characteristic function `χ_i : |T| → ℤ` and the substack cut out by
`χ_i = P i` are each blocked on a different absent input.  Nothing here removes any of those
obstructions.  Consequently:

* the *specialisation* of 0DNC which 0DNF asks for is constructed, and that is a complete
  statement: it is the datum `I = ℤ`, `E n = L^{⊗ n}`, `P`, over the separated morphism;
* the *membership condition* of 0DNF is stated as
  `AlgebraicGeometry.Space.IsPrescribedTwistedEuler`, a predicate on a family `χ : ι → ℤ → ℤ`
  which is *given*, `ι` standing for the points of the test scheme and `χ t n` for
  `χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})`.  This is the pattern that
  `AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreChi` already uses for the same obstruction;
* the assertion that `Coh^P_{X/B}` is an **open and closed** algebraic substack is *not*
  established.  The source attributes it to Lemma 0DNE, which in turn reduces to Lemma 0DND, and
  neither is present in this development.  No attribute for 0DNE or 0DND is attached anywhere
  here, and the substack is deliberately *not* defined in a way that would make openness and
  closedness true by fiat.
* the disjoint union decomposition `Coh_{X/B} = ⨿_P Coh^P_{X/B}` over all numerical polynomials
  `P` is not established either; it rests on Stacks 0DN4, which is absent.

**Perfectness of the twists is a named hypothesis.**  Stacks 0DNF takes for granted that an
invertible module is a perfect object of `D(𝒪_X)`.  In this development the only route to
`AlgebraicGeometry.RingedSite.IsPerfect` for a module built from an invertible one is
`AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfect_of_hasInvertibleModuleDecomposition`,
which asks for a locally finite direct product decomposition of the structure sheaf, and no such
decomposition is available for the small étale ringed site of an algebraic space.  Perfectness of
the family `n ↦ L^{⊗ n}` is therefore carried as the hypothesis `perfect` of
`AlgebraicGeometry.Space.NumericalSituation.ofInvertibleTwists`.

**The numerical polynomial is encoded by a representing rational polynomial.**  Stacks 0DP8 is
false for a general function `P : ℤ → ℤ`: knowing `P(n m) = χ(n m)` for every `m` says nothing
about the remaining values.  What makes the two conditions agree is that both sides are numerical
polynomials in the sense of Stacks 027X, so that agreeing at the infinitely many multiples of
`n ≠ 0` forces agreement everywhere.  The hypotheses of
`AlgebraicGeometry.Space.isPrescribedTwistedEuler_iff_reindexMul` are therefore a rational
polynomial representing `P` and, for each point, one representing the twisted Euler
characteristics; each such hypothesis in particular exhibits `Polynomial.IsNumerical` for the
polynomial in question.  Stacks 0DP7 needs no such hypothesis, the reindexing there being a
bijection of the index set `ℤ`.

**The module universe is `u`.**  The tensor power of Stacks 01CU is available on the small étale
ringed site of an algebraic space only at `AlgebraicGeometry.Space.Modules.{u, u}`, the
sheafification instances of that site being available for `AddCommGrpCat.{u}`; this is the same
restriction under which `AlgebraicGeometry.Space.twistStep` is stated.  The index set of the
specialised situation is `ℤ`, so the situation produced lives at
`AlgebraicGeometry.Space.NumericalSituation.{u, 0, u}`.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DP7](https://stacks.math.columbia.edu/tag/0DP7)
* [Stacks Project, Tag 0DP8](https://stacks.math.columbia.edu/tag/0DP8)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 027X](https://stacks.math.columbia.edu/tag/027X)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

/-! ### Integer tensor powers of an invertible module on an algebraic space -/

section TensorPower

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The integer tensor power `L^{⊗ n}` of an invertible module on the small étale ringed site of
the algebraic space `F`.

This is `Stacks.SheafOfModules.Invertible.tensorPower`, the power of Stacks 01CU, applied with
the underlying category and the topology spelled as the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`; that is the spelling at which the sheafification
instances of the site are stated, and it is the one
`AlgebraicGeometry.Space.twistStep` uses for the same power. -/
def invertibleTensorPower (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (n : ℤ) : Modules.{u, u} B S hS F hF :=
  @Stacks.SheafOfModules.Invertible.tensorPower.{u, u + 1, u}
    (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
    (structurePresheaf B S hS F)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property _ _ L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) n

/-- The tensor power `L^{⊗ n}` read as an object of `D(𝒪_F)`, by the embedding of modules as
complexes concentrated in degree zero.

This is the family `I = ℤ → D(𝒪_X)`, `n ↦ L^{⊗ n}`, to which Stacks 0DNF specialises Situation
0DNC. -/
def invertibleTwistObject (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (n : ℤ) : DerivedCategory (Modules.{u, u} B S hS F hF) :=
  (DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj
    (invertibleTensorPower B S hS F hF L n)

end TensorPower

/-! ### Stacks 0DNF: the one-parameter specialisation of Situation 0DNC -/

section Specialisation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : CoherentSituation B S hS)
    [∀ U : (smallEtaleRingedSite B S hS D.X.1 D.X.2).C,
      HasSheafify ((smallEtaleRingedSite B S hS D.X.1 D.X.2).J.over U) AddCommGrpCat.{u}]
    [∀ U : (smallEtaleRingedSite B S hS D.X.1 D.X.2).C,
      ((smallEtaleRingedSite B S hS D.X.1 D.X.2).J.over U).WEqualsLocallyBijective
        AddCommGrpCat.{u}]

/-- **Stacks 0DNF, the specialisation of Situation 0DNC.**  Over a separated morphism
`f : X ⟶ B` of algebraic spaces of finite presentation, an invertible `𝒪_X`-module `L` and a
map `P : ℤ → ℤ`, the standing data of Stacks 0DNC with index set `I = ℤ` and with the family
`n ↦ L^{⊗ n}` of perfect objects of `D(𝒪_X)`.  This is the datum relative to which the source's
`Coh^P_{X/B} = Coh^{P,L}_{X/B}` is formed.

Perfectness of the twists `L^{⊗ n}` is the hypothesis `perfect`: the source takes it for granted
for an invertible module, and this development has no route to it on the small étale ringed site
of an algebraic space.  Nothing here asserts that the resulting substack is open and closed —
that is Lemma 0DNE, which is absent — nor that `P` is a numerical polynomial, which the source
assumes but which no clause of the specialisation uses. -/
@[stacks 0DNF "the substack as the specialisation of Situation 0DNC to the index set `ℤ` and the
family `n ↦ L^{⊗ n}`; perfectness of those twists is a hypothesis, and openness and closedness
(Lemma 0DNE) and the disjoint union decomposition are not established"]
def NumericalSituation.ofInvertibleTwists (separated : IsSeparated B S hS D.f.hom)
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (perfect : ∀ n : ℤ, (smallEtaleRingedSite B S hS D.X.1 D.X.2).IsPerfect
      (invertibleTwistObject B S hS D.X.1 D.X.2 L n))
    (P : ℤ → ℤ) : NumericalSituation.{u, 0, u} B S hS D where
  separated := separated
  I := ℤ
  E n := invertibleTwistObject B S hS D.X.1 D.X.2 L n
  perfect := perfect
  P := P

variable (separated : IsSeparated B S hS D.f.hom) (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (perfect : ∀ n : ℤ, (smallEtaleRingedSite B S hS D.X.1 D.X.2).IsPerfect
      (invertibleTwistObject B S hS D.X.1 D.X.2 L n))
    (P : ℤ → ℤ)

/-- The index set of the specialised situation is `ℤ`, as the source's `I = ℤ` asks. -/
theorem NumericalSituation.ofInvertibleTwists_I :
    (NumericalSituation.ofInvertibleTwists B S hS D separated L perfect P).I = ℤ :=
  rfl

/-- The family of perfect objects of the specialised situation is `n ↦ L^{⊗ n}`. -/
@[simp]
theorem NumericalSituation.ofInvertibleTwists_E (n : ℤ) :
    (NumericalSituation.ofInvertibleTwists B S hS D separated L perfect P).E n =
      invertibleTwistObject B S hS D.X.1 D.X.2 L n :=
  rfl

/-- The prescribed invariants of the specialised situation are `P` itself. -/
@[simp]
theorem NumericalSituation.ofInvertibleTwists_P (n : ℤ) :
    (NumericalSituation.ofInvertibleTwists B S hS D separated L perfect P).P n = P n :=
  rfl

end Specialisation

/-! ### Stacks 0DNF: the membership condition -/

/-- **Stacks 0DNF, the membership condition.**  An object `(T ⟶ B, 𝓕)` of `Coh_{X/B}` lies in
`Coh^P_{X/B} = Coh^{P,L}_{X/B}` exactly when

`P(n) = χ(X_t, 𝓕_t ⊗_{𝒪_{X_t}} L_t^{⊗ n})`

holds for every `n ∈ ℤ` and every `t ∈ T`.  Here `ι` is the type of points of the test scheme and
`χ t n` is the Euler characteristic above.  That family is *given*: the Euler characteristic of a
perfect object on an algebraic space cannot be constructed in this development, for the reason
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/NumericalInvariants.lean`, and the same device is used by
`AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreChi`. -/
@[stacks 0DNF "the membership condition `P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})`, stated for a given
family of fibrewise twisted Euler characteristics, which this development cannot construct"]
def IsPrescribedTwistedEuler {ι : Type v} (P : ℤ → ℤ) (χ : ι → ℤ → ℤ) : Prop :=
  ∀ t : ι, ∀ n : ℤ, P n = χ t n

/-! ### The two reindexings: Stacks 0DP7 and Stacks 0DP8 -/

/-- Two functions `ℤ → ℤ` agree everywhere as soon as they agree after a translation of the
argument.  This is the reindexing underlying Stacks 0DP7. -/
private theorem forall_eq_iff_forall_add {P c : ℤ → ℤ} (k : ℤ) :
    (∀ m : ℤ, P m = c m) ↔ ∀ m : ℤ, P (m + k) = c (m + k) := by
  refine ⟨fun h m => h _, fun h m => ?_⟩
  simpa using h (m - k)

/-- Two functions `ℤ → ℤ` represented by rational polynomials agree everywhere as soon as they
agree at every multiple of a nonzero integer `n`: the two polynomials then agree on the infinite
set of those multiples, hence are equal.  This is the arithmetic content of Stacks 0DP8, and it
is where the hypothesis that the invariants are *numerical polynomials* is used. -/
private theorem forall_eq_iff_forall_mul_eq {P c : ℤ → ℤ} {p q : Polynomial ℚ}
    (hp : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) (hq : ∀ m : ℤ, q.eval (m : ℚ) = (c m : ℚ))
    {n : ℤ} (hn : n ≠ 0) :
    (∀ m : ℤ, P m = c m) ↔ ∀ m : ℤ, P (n * m) = c (n * m) := by
  refine ⟨fun h m => h _, fun h => ?_⟩
  have hpq : p = q := by
    refine Polynomial.eq_of_infinite_eval_eq p q ?_
    refine Set.infinite_of_injective_forall_mem
      (f := fun m : ℤ => ((n * m : ℤ) : ℚ)) ?_ ?_
    · intro a b hab
      simpa [hn] using hab
    · intro m
      simp only [Set.mem_ofPred_eq, hp, hq, h m]
  intro m
  have hm := hp m
  rw [hpq, hq m] at hm
  exact_mod_cast hm.symm

/-- **Stacks 0DP7, the final statement, at the level of membership conditions.**  Tensoring with
an invertible module `L` replaces the twisted Euler characteristics `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})`
of `𝓕` by their shift `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ (n + 1)})`, which is the hypothesis `twist`.  The
condition cutting out `Quot^P_{𝓕/X/B}` is then the condition cutting out
`Quot^{P'}_{𝓕 ⊗ L/X/B}` for `P'(t) = P(t + 1)`.

The isomorphism `Quot_{𝓕/X/B} ⟶ Quot_{𝓕 ⊗ L/X/B}` of the first statement of the source is not
constructed here, and neither are the two open and closed substacks it is claimed to restrict
to. -/
@[stacks 0DP7 "the final statement at the level of membership conditions: the condition for `P`
and `𝓕` is the condition for `P'(t) = P(t + 1)` and `𝓕 ⊗ L`.  The isomorphism
`Quot_{𝓕/X/B} ⟶ Quot_{𝓕 ⊗ L/X/B}` itself is not constructed"]
theorem isPrescribedTwistedEuler_iff_shift {ι : Type v} {P : ℤ → ℤ} {χ χ' : ι → ℤ → ℤ}
    (twist : ∀ (t : ι) (m : ℤ), χ' t m = χ t (m + 1)) :
    IsPrescribedTwistedEuler P χ ↔ IsPrescribedTwistedEuler (fun m => P (m + 1)) χ' := by
  simp only [IsPrescribedTwistedEuler, twist]
  exact forall_congr' fun t => forall_eq_iff_forall_add 1

/-- **Stacks 0DP8, at the level of membership conditions.**  Replacing `L` by `L^{⊗ n}` replaces
the twisted Euler characteristics `m ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ m})` by `m ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n m})`,
which is the hypothesis `twist`.  For `n ≠ 0` the condition cutting out `Quot^{P,L}_{𝓕/X/B}` is
then the condition cutting out `Quot^{P',L^{⊗ n}}_{𝓕/X/B}` for `P'(t) = P(n t)`: this is the
source's equality of the two substacks, read on their defining conditions.

The hypotheses `hP` and `hχ` say that `P` and each `χ t` are numerical polynomials, represented by
the rational polynomials `p` and `q t`.  They are not removable: for a general `P` the right-hand
condition constrains only the values of `P` at the multiples of `n`. -/
@[stacks 0DP8 "the equality `Quot^{P,L} = Quot^{P',L^{⊗ n}}` with `P'(t) = P(n t)`, read on the
two membership conditions, for `n ≠ 0` and numerical-polynomial invariants; the substacks
themselves are not constructed in this development"]
theorem isPrescribedTwistedEuler_iff_reindexMul {ι : Type v} {P : ℤ → ℤ} {χ χ' : ι → ℤ → ℤ}
    {p : Polynomial ℚ} {q : ι → Polynomial ℚ}
    (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ))
    (hχ : ∀ (t : ι) (m : ℤ), (q t).eval (m : ℚ) = (χ t m : ℚ))
    {n : ℤ} (hn : n ≠ 0) (twist : ∀ (t : ι) (m : ℤ), χ' t m = χ t (n * m)) :
    IsPrescribedTwistedEuler P χ ↔ IsPrescribedTwistedEuler (fun m => P (n * m)) χ' := by
  simp only [IsPrescribedTwistedEuler, twist]
  exact forall_congr' fun t => forall_eq_iff_forall_mul_eq hP (hχ t) hn

end AlgebraicGeometry.Space

end
