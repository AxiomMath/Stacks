module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple

/-!
# Equivalence of quadruples of different degrees

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN). Section 01NS attaches to
each integer `d` the quadruples `(d, f : T → S, L, ψ)` over a test scheme `T` and the set
`F_d(T)` of their strict equivalence classes. To compare quadruples whose integers `d` and `d'`
differ one restricts both maps `ψ` to a common multiple `m = a d = a' d'` of the two degrees and
asks for an isomorphism `β : L^{⊗ a} ⟶ (L')^{⊗ a'}` carrying one restriction to the other. Tag
01NW is the assertion that this does not depend on the common multiple chosen: comparability at
the least common multiple, comparability at `d d'` — which is what *equivalence* of quadruples
means — and comparability at some positive common multiple all say the same thing.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.IsScaledPair`: the pairs of degrees
  `(p, q) = (n a, n a')` at which a comparison of two quadruples at `(a, a')` is defined.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.CompatibleAt`: **the comparison of
  two quadruples at a common multiple `m = a d = a' d'` of their degrees**, the isomorphism
  `β : L^{⊗ a} ⟶ (L')^{⊗ a'}` carrying `ψ|_{f^*𝒜^{(m)}}` to `ψ'|_{f^*𝒜^{(m)}}`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.Equivalent`: **equivalence of two
  quadruples of possibly different degrees**, the comparison at the common multiple `d d'`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.IsComparisonAt`: the three
  conditions on the family `γ` that `CompatibleAt` asserts the existence of, named so that the
  family itself can be spoken about; `Quadruple.compatibleAt_iff_exists_isComparisonAt` records
  that this is the same predicate.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.CompatibleAt.mul_left`: **a
  comparison at `(a, a')` restricts to a comparison at `(k a, k a')`**, that is, to any more
  divisible common multiple of the two degrees.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.epi_tensorHom`: **a tensor product of two
  surjections of sheaves of modules on a ringed space is surjective**, at the spelling of the
  monoidal structure of Tag 01CA that the multiplicativity of `ψ` is stated with.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.epi_app_of_pos`: **the components of
  `ψ` in positive degrees are surjective**, given that the degree-one component is. This is the
  step the source takes when it says that `ψ` and `ψ'`, being surjective in degrees `d` and
  `d'`, remain surjective in degree `m₀`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.IsComparisonAt.eq`: **a comparison
  of two quadruples at a fixed pair `(a, a')` with `a` positive is unique**, in every component.
  This is the uniqueness of `β₀` that the source's descent argument consumes.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.equivalent_of_lcm_compatible`:
  **Tag 01NW, (1) implies (2)**: two quadruples comparable at the least common multiple of their
  degrees are equivalent. The restriction is along the factor `gcd(d, d')`, which carries the
  least common multiple to `d d'`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.exists_compatible_of_equivalent`:
  **Tag 01NW, (2) implies (3)**: equivalent quadruples are comparable at a positive common
  multiple of their degrees, namely at `d d'`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.kernel_ι_comp_eq_zero`: **two morphisms out of
  one sheaf of modules have the same kernel as soon as their tensor products with a pair of
  morphisms onto invertible modules have a common factorisation**, the second of the two
  morphisms being surjective. With
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.exists_iso_of_kernel_comp_eq_zero` this is the
  engine of the descent below.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.exists_isCompAt_of_add`: **a
  comparison of the components of `ψ` and `ψ'` in the degrees `(p + p', q + q')` descends to the
  degrees `(p, q)`**, when all four degrees are positive. This is the step the source of Tag 01NW
  calls "not a complete triviality", for one component.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.hasCompAt_lcm_of_compatibleAt`:
  **Tag 01NW, the descent to the least common multiple in every positive degree**: two quadruples
  comparable at some positive common multiple of their degrees admit, for every `n ≥ 1`, an
  isomorphism `L^{⊗ n a₀} ≅ (L')^{⊗ n a₀'}` carrying `ψ_{n a₀}` to `ψ'_{n a₀'}`, where
  `m₀ = a₀ d = a₀' d'` is the least common multiple. For `n = 1` this is the isomorphism `β` of
  condition (1).

## Implementation notes

The clause `f = f'` occurs in each of the three conditions of Tag 01NW, so the content of the
tag is the equivalence of the three comparison conditions for two quadruples over one and the
same morphism `f : T ⟶ S`; that is how the statements here are phrased, as is `StrictlyEquivalent`
of Section 01NS.

A comparison records, as Section 01NS does for strict equivalence, not the single isomorphism
`β : L^{⊗ a} ≅ (L')^{⊗ a'}` but the isomorphism of graded algebras

`⨁_{n ∈ ℤ} L^{⊗ n a} ⟶ ⨁_{n ∈ ℤ} (L')^{⊗ n a'}`

that `β` induces, which is the `β ∘ -` the source writes; `β` itself is its component in degree
`n = 1`. The two formulations carry the same information, because multiplication by the
degree-one piece generates the graded algebra, and the second is the one that does not need the
functoriality of the tensor powers in `L`.

That isomorphism of graded algebras is recorded as a family of isomorphisms
`L^{⊗ p} ≅ (L')^{⊗ q}` indexed by the pairs `(p, q)` lying on the line through `(a, a')`, rather
than by the integer `n` with `(p, q) = (n a, n a')`. Indexing by the pair makes the degrees of
the source and the target of each component free variables, so the multiplicativity condition
and the compatibility with `ψ` are stated with no transport of a tensor power along an equality
of exponents; and since the condition `IsScaledPair a a' p q` singling out the pairs is a
proposition, hence proof-irrelevant, a comparison at `(a, a')` *is* a comparison at `(k a, k a')`
on the nose, which is what makes `CompatibleAt.mul_left` hold with no bookkeeping at all. The
one transport that remains is on the algebra: the degree-`p` component of `ψ` has source
`f^*𝒜_{p d}` and the degree-`q` component of `ψ'` has source `f^*𝒜_{q d'}`, and `p d = q d'`
only propositionally.

**Why the statements about `SheafOfModules.GradedAlgebra.mulSheaf` are proved by explicit terms.**
Its source is `((Stacks.SheafOfModules.Tensor.sheafTensor 𝒪_T).obj _).obj _`, and the sheaf of
commutative rings there arrives as `T.toRingedSpace.sheaf`, whose type `TopCat.Sheaf CommRingCat T`
agrees with the expected `Sheaf (Opens.grothendieckTopology T) CommRingCat` only after
`TopCat.Sheaf` is unfolded. That does not happen at the `implicit` transparency level, so a goal
naming a `mulSheaf` is not type-correct there: `rw` refuses to build a motive over it and
instance search does not solve `Epi` or `Mono` of it even with the invertibility in the local
context. Elaboration of a term runs at default transparency and is unaffected, so
`epi_mulSheaf_laurent`, `mono_mulSheaf_laurent` and `mulSheaf_eqToHom_comp` pass the morphism
and its invertibility as arguments instead of calling `inferInstance` or `rw`.

## Not done here

The implication (3) implies (1) of Tag 01NW — the upgrade of a comparison at some common multiple
to a comparison at the least common multiple — is not proved here, but only because it needs the
*shape* of a comparison and not a further descent;
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.EquivalenceDescent` supplies that and closes
the cycle.

What this file contributes to it is the descent itself. No amount of restriction along
`CompatibleAt.mul_left` reaches a less divisible pair: for `d = d' = 1` and `a = a' = 2` the pair
`(1, 1)` is not of the form `(2k, 2k)`. The descent that does reach it is
`exists_isCompAt_of_add`, and `hasCompAt_lcm_of_compatibleAt` runs it in every positive degree:
from a comparison at `(a, a')` with `a` positive one obtains, for every `n ≥ 1`, an isomorphism
`L^{⊗ n a₀} ≅ (L')^{⊗ n a₀'}` carrying `ψ_{n a₀}` to `ψ'_{n a₀'}`. That argument is formal — it
uses the surjectivity of `ψ` and `ψ'` in the positive degrees (`Twisting.epi_app_of_pos`), the
invertibility of the tensor powers, and the abelian structure, and it needs neither a local
trivialisation of `L` nor an open cover of the test scheme, so neither Tag 01NB nor the
correspondence between triples and quadruples of Tag 01NU is involved.

What remains between that and `CompatibleAt P Q a₀ a₀'`, and is done in the module named above,
is the components in the degrees `(n a₀, n a₀')` for `n ≤ 0`, where `ψ_{n a₀}` is no longer
surjective, together with the multiplicativity of the resulting family in an arbitrary pair of
degrees. So of the three conditions, this file carries (1) implies (2) and (2) implies (3), and
the implications producing a comparison at the least common multiple carry the tag there.

## References

* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

/-! ### Surjectivity of `ψ` in the positive degrees -/

/-- **A tensor product of two surjections of sheaves of modules on a ringed space is
surjective**, at the spelling of the monoidal structure of Tag 01CA that the multiplicativity of
a `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting` is stated with.

The mathematics is `Stacks.SheafOfModules.TensorPresentations.tensorSheafMapOnSite_epi`, the
exactness at the last term of the tensor product of two presentations; what this adds is the
identification of the tensor product of two morphisms in the monoidal structure with the
sheafified objectwise one, which is
`Stacks.SheafOfModules.Strict.tensorHom_eq_sheafifyMap`. The two epimorphism hypotheses are
supplied by hand across the two definitionally equal spellings of the sheaf of rings, as
instance search does not transport them. -/
theorem epi_tensorHom (Z : RingedSpace.{u, u})
    {M M' N N' : SheafOfModules.{u} (structureRingSheaf Z)}
    (φ : M ⟶ M') (χ : N ⟶ N') [Epi φ] [Epi χ] :
    Epi (φ ⊗ₘ χ) := by
  have comparison : (φ ⊗ₘ χ) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).map φ).app N ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj M').map χ :=
    (Stacks.SheafOfModules.Strict.tensorHom_eq_sheafifyMap Z.presheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property φ χ).trans
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Z.sheaf φ χ).symm
  rw [comparison]
  exact Stacks.SheafOfModules.TensorPresentations.tensorSheafMapOnSite_epi Z.presheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property φ χ
    (leftEpi := ‹Epi φ›) (rightEpi := ‹Epi χ›)

/-- The second factor of an epimorphic composite is an epimorphism, with the composite supplied
as an argument rather than as an instance. -/
private theorem epi_of_epi_comp {C : Type*} [Category C] {X Y Z : C} {u : X ⟶ Y} {v : Y ⟶ Z}
    (h : Epi (u ≫ v)) : Epi v := by
  have := h
  exact epi_of_epi u v

section Epi

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The homogeneous multiplication of the Laurent algebra is invertible**: it is the coherent
multiplication `L^{⊗ i} ⊗ L^{⊗ j} ≅ L^{⊗ (i + j)}` of Tag 01CU, which is an isomorphism. -/
theorem isIso_mulSheaf_laurent (i j : ℤ) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf (laurent L) i j) := by
  rw [mulSheaf_laurent]
  exact (mulIso L i j).isIso_hom

/-- The homogeneous multiplication of the Laurent algebra is surjective, being invertible.

The invertibility is supplied to `CategoryTheory.IsIso.epi_of_iso` as an argument rather than
left to instance search; see the implementation notes for why search does not reach it. -/
theorem epi_mulSheaf_laurent (i j : ℤ) :
    Epi (SheafOfModules.GradedAlgebra.mulSheaf (laurent L) i j) :=
  @IsIso.epi_of_iso _ _ _ _ _ (isIso_mulSheaf_laurent i j)

/-- The homogeneous multiplication of the Laurent algebra is injective, being invertible. The
invertibility is supplied as an argument, as in `epi_mulSheaf_laurent`. -/
theorem mono_mulSheaf_laurent (i j : ℤ) :
    Mono (SheafOfModules.GradedAlgebra.mulSheaf (laurent L) i j) :=
  @IsIso.mono_of_iso _ _ _ _ _ (isIso_mulSheaf_laurent i j)

/-- **The surjective degrees of `ψ` are closed under addition.** The multiplicativity of `ψ` in
bidegree `(i, j)` factors `ψ_i ⊗ ψ_j` followed by the multiplication of the Laurent algebra
through `ψ_{i + j}`; the left-hand side is surjective because a tensor product of surjections
is, and because the multiplication of the Laurent algebra is invertible, and the two factors
preceding `ψ_{i + j}` on the right-hand side may therefore be discarded. -/
theorem Twisting.epi_app_add (ψ : Twisting f A d L) {i j : ℤ}
    (hi : Epi (ψ.app i)) (hj : Epi (ψ.app j)) : Epi (ψ.app (i + j)) := by
  have htens : Epi (MonoidalCategoryStruct.tensorHom (ψ.app i) (ψ.app j)) := by
    have := hi
    have := hj
    exact epi_tensorHom T.toRingedSpace _ _
  have hlhs : Epi (MonoidalCategoryStruct.tensorHom (ψ.app i) (ψ.app j) ≫
      (laurent L).mulSheaf i j) := epi_comp' htens (epi_mulSheaf_laurent i j)
  rw [ψ.app_mul i j] at hlhs
  exact epi_of_epi_comp (epi_of_epi_comp hlhs)

/-- **The components of `ψ` in the positive degrees are surjective** as soon as the degree-one
component is: every positive integer is a sum of ones, and the surjective degrees are closed
under addition.

This is the step the source of Tag 01NW takes when it says that `ψ` and `ψ'`, being surjective
in degrees `d` and `d'`, remain surjective in degree `m₀`. -/
theorem Twisting.epi_app_of_pos (ψ : Twisting f A d L) (h1 : Epi (ψ.app 1)) {n : ℤ}
    (hn : 0 < n) : Epi (ψ.app n) := by
  have key : ∀ k : ℕ, Epi (ψ.app ((k : ℤ) + 1)) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
        have hc : ((k + 1 : ℕ) : ℤ) + 1 = ((k : ℤ) + 1) + 1 := by push_cast; ring
        rw [hc]
        exact ψ.epi_app_add ih h1
  have hk : n = ((n - 1).toNat : ℤ) + 1 := by omega
  rw [hk]
  exact key _

/-- **The components of the map `ψ` of a quadruple in the positive degrees are surjective.**
Section 01NS requires the degree-one component to be, and `Twisting.epi_app_of_pos` propagates
that upwards. -/
theorem Quadruple.epi_app_of_pos (P : Quadruple f A d) {n : ℤ} (hn : 0 < n) :
    Epi (P.twisting.app n) :=
  P.twisting.epi_app_of_pos P.epi_app_one hn

end Epi

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d d' : ℤ}

/-- The pair of degrees `(p, q)` is a common multiple of the pair `(a, a')`: there is one
integer `n` with `p = n a` and `q = n a'`. These are the pairs of degrees at which a comparison
of two quadruples at `(a, a')` has a component, namely `L^{⊗ n a} ≅ (L')^{⊗ n a'}`. -/
def IsScaledPair (a a' p q : ℤ) : Prop := ∃ n : ℤ, p = n * a ∧ q = n * a'

namespace IsScaledPair

/-- The pair `(0, 0)` is a common multiple of every pair, with factor `n = 0`. -/
theorem zero (a a' : ℤ) : IsScaledPair a a' 0 0 := ⟨0, (zero_mul a).symm, (zero_mul a').symm⟩

/-- Common multiples of a pair are closed under addition. -/
theorem add {a a' p q p' q' : ℤ} (h : IsScaledPair a a' p q) (h' : IsScaledPair a a' p' q') :
    IsScaledPair a a' (p + p') (q + q') := by
  obtain ⟨n, hp, hq⟩ := h
  obtain ⟨n', hp', hq'⟩ := h'
  exact ⟨n + n', by rw [hp, hp']; ring, by rw [hq, hq']; ring⟩

/-- A common multiple of `(k a, k a')` is a common multiple of `(a, a')`. -/
theorem of_mul_left {a a' p q : ℤ} (k : ℤ) (h : IsScaledPair (k * a) (k * a') p q) :
    IsScaledPair a a' p q := by
  obtain ⟨n, hp, hq⟩ := h
  exact ⟨n * k, by rw [hp]; ring, by rw [hq]; ring⟩

/-- On a common multiple `(p, q)` of a pair `(a, a')` satisfying `a d = a' d'`, the degrees
`p d` and `q d'` of the algebra agree: both are `n` times the common multiple `a d` of `d` and
`d'`. -/
theorem degree_eq {a a' p q : ℤ} (h : IsScaledPair a a' p q) {d d' : ℤ}
    (hm : a * d = a' * d') : p * d = q * d' := by
  obtain ⟨n, hp, hq⟩ := h
  subst hp
  subst hq
  calc n * a * d = n * (a * d) := by ring
    _ = n * (a' * d') := by rw [hm]
    _ = n * a' * d' := by ring

end IsScaledPair

/-- **Stacks Project, Tag 01NW, the comparison of two quadruples at a common multiple of their
degrees.** Let `(d, f, L, ψ)` and `(d', f, L', ψ')` be quadruples over a test scheme `T` and let
`m = a d = a' d'` be a common multiple of their degrees. The two quadruples are *compatible at*
`(a, a')` when there is an isomorphism `β : L^{⊗ a} ⟶ (L')^{⊗ a'}` such that
`β ∘ ψ|_{f^*𝒜^{(m)}}` and `ψ'|_{f^*𝒜^{(m)}}` agree as homomorphisms of graded algebras
`f^*𝒜^{(m)} ⟶ ⨁_{n ∈ ℤ} (L')^{⊗ n a'}`.

The isomorphism is recorded through the map `β ∘ -` it induces on all the tensor powers
`L^{⊗ n a} ⟶ (L')^{⊗ n a'}`: a multiplicative, unit-preserving family, whose component in
degree `(a, a')` is `β` itself. -/
def CompatibleAt (P : Quadruple f A d) (Q : Quadruple f A d') (a a' : ℤ) : Prop :=
  ∃ hm : a * d = a' * d',
    ∃ γ : ∀ p q : ℤ, IsScaledPair a a' p q → ((laurent P.L).piece p ≅ (laurent Q.L).piece q),
      (∀ (p q p' q' : ℤ) (h : IsScaledPair a a' p q) (h' : IsScaledPair a a' p' q'),
          MonoidalCategoryStruct.tensorHom (γ p q h).hom (γ p' q' h').hom ≫
              (laurent Q.L).mulSheaf q q' =
            (laurent P.L).mulSheaf p p' ≫ (γ (p + p') (q + q') (h.add h')).hom) ∧
        SheafOfModules.GradedAlgebra.oneHom (laurent P.L) ≫
            (γ 0 0 (IsScaledPair.zero a a')).hom =
          SheafOfModules.GradedAlgebra.oneHom (laurent Q.L) ∧
          ∀ (p q : ℤ) (h : IsScaledPair a a' p q),
            P.twisting.app p ≫ (γ p q h).hom =
              (pullbackFunctor (ringedSpaceHom f)).map
                  (eqToHom (congrArg A.piece (h.degree_eq hm))) ≫
                Q.twisting.app q

/-- **Stacks Project, Section 01NS, equivalence of two quadruples of possibly different
degrees.** The quadruples `(d, f, L, ψ)` and `(d', f, L', ψ')` over a test scheme `T` are
*equivalent* when there is an isomorphism `β : L^{⊗ d'} ⟶ (L')^{⊗ d}` with
`β ∘ ψ|_{f^*𝒜^{(d d')}} = ψ'|_{f^*𝒜^{(d d')}}`, that is, when they are compatible at the
common multiple `d d'` of their degrees. -/
def Equivalent (P : Quadruple f A d) (Q : Quadruple f A d') : Prop :=
  CompatibleAt P Q d' d

variable {P : Quadruple f A d} {Q : Quadruple f A d'}

/-- **A comparison of two quadruples restricts to any more divisible common multiple of their
degrees**: a comparison at `(a, a')` is a comparison at `(k a, k a')`.

The components of the restricted comparison are the components of the given one: the degrees
`(p, q)` at which the restriction has a component are those of the form `(n k a, n k a')`, and
those are among the degrees `(n a, n a')`. -/
theorem CompatibleAt.mul_left {a a' : ℤ} (h : CompatibleAt P Q a a') (k : ℤ) :
    CompatibleAt P Q (k * a) (k * a') := by
  obtain ⟨hm, γ, hmul, hone, hψ⟩ := h
  refine ⟨?_, fun p q hpq => γ p q (hpq.of_mul_left k), fun p q p' q' h h' => hmul p q p' q' _ _,
    hone, fun p q h => hψ p q _⟩
  calc k * a * d = k * (a * d) := by ring
    _ = k * (a' * d') := by rw [hm]
    _ = k * a' * d' := by ring

/-- The least common multiple of two positive integers, written as `a d` and as `a' d'`, has
cofactors `a = d' / gcd(d, d')` and `a' = d / gcd(d, d')`: multiplying either cofactor by
`gcd(d, d')` gives the other degree. -/
private theorem gcd_mul_eq_of_lcm_eq {a a' : ℤ} (hd : 0 < d) (hd' : 0 < d')
    (ha : (Int.lcm d d' : ℤ) = a * d) (ha' : (Int.lcm d d' : ℤ) = a' * d') :
    (Int.gcd d d' : ℤ) * a = d' ∧ (Int.gcd d d' : ℤ) * a' = d := by
  have key : (Int.gcd d d' : ℤ) * (Int.lcm d d' : ℤ) = d * d' := by
    have h : ((Int.gcd d d' : ℕ) : ℤ) * ((Int.lcm d d' : ℕ) : ℤ) =
        ((d.natAbs : ℕ) : ℤ) * ((d'.natAbs : ℕ) : ℤ) := by
      exact_mod_cast Int.gcd_mul_lcm d d'
    rw [h, Int.natAbs_of_nonneg hd.le, Int.natAbs_of_nonneg hd'.le]
  refine ⟨mul_right_cancel₀ hd.ne' ?_, mul_right_cancel₀ hd'.ne' ?_⟩
  · calc (Int.gcd d d' : ℤ) * a * d = (Int.gcd d d' : ℤ) * (a * d) := by ring
      _ = (Int.gcd d d' : ℤ) * (Int.lcm d d' : ℤ) := by rw [ha]
      _ = d * d' := key
      _ = d' * d := by ring
  · calc (Int.gcd d d' : ℤ) * a' * d' = (Int.gcd d d' : ℤ) * (a' * d') := by ring
      _ = (Int.gcd d d' : ℤ) * (Int.lcm d d' : ℤ) := by rw [ha']
      _ = d * d' := key

/-- **Stacks Project, Tag 01NW, (1) implies (2).** Two quadruples with positive degrees `d` and
`d'` which are compatible at the least common multiple `m = a d = a' d'` of their degrees are
equivalent.

The least common multiple times `gcd(d, d')` is `d d'`, so restricting the comparison along the
factor `gcd(d, d')` turns it into a comparison at `(d', d)`, which is equivalence. -/
theorem equivalent_of_lcm_compatible {a a' : ℤ} (hd : 0 < d) (hd' : 0 < d')
    (ha : (Int.lcm d d' : ℤ) = a * d) (ha' : (Int.lcm d d' : ℤ) = a' * d')
    (h : CompatibleAt P Q a a') : Equivalent P Q := by
  obtain ⟨hk, hk'⟩ := gcd_mul_eq_of_lcm_eq hd hd' ha ha'
  have hrestrict := h.mul_left (Int.gcd d d' : ℤ)
  rw [hk, hk'] at hrestrict
  exact hrestrict

/-- **Stacks Project, Tag 01NW, (2) implies (3).** Two equivalent quadruples with positive
degrees `d` and `d'` are compatible at a positive common multiple of their degrees, namely at
`m = d' d = d d'`. -/
theorem exists_compatible_of_equivalent (hd : 0 < d) (hd' : 0 < d') (h : Equivalent P Q) :
    ∃ m a a' : ℤ, 0 < m ∧ m = a * d ∧ m = a' * d' ∧ CompatibleAt P Q a a' :=
  ⟨d' * d, d', d, mul_pos hd' hd, rfl, mul_comm d' d, h⟩

/-! ### The comparison at a fixed pair of degrees is unique -/

/-- **The three conditions on the family `γ` of a comparison of `P` with `Q` at `(a, a')`**:
multiplicativity, preservation of the unit, and compatibility with `ψ`. These are exactly the
conditions `CompatibleAt` asserts the existence of a family satisfying; naming them is what lets
the family be spoken about, and in particular lets it be asserted to be unique. -/
def IsComparisonAt (P : Quadruple f A d) (Q : Quadruple f A d') {a a' : ℤ}
    (hm : a * d = a' * d')
    (γ : ∀ p q : ℤ, IsScaledPair a a' p q → ((laurent P.L).piece p ≅ (laurent Q.L).piece q)) :
    Prop :=
  (∀ (p q p' q' : ℤ) (h : IsScaledPair a a' p q) (h' : IsScaledPair a a' p' q'),
      MonoidalCategoryStruct.tensorHom (γ p q h).hom (γ p' q' h').hom ≫
          (laurent Q.L).mulSheaf q q' =
        (laurent P.L).mulSheaf p p' ≫ (γ (p + p') (q + q') (h.add h')).hom) ∧
    SheafOfModules.GradedAlgebra.oneHom (laurent P.L) ≫
          (γ 0 0 (IsScaledPair.zero a a')).hom =
        SheafOfModules.GradedAlgebra.oneHom (laurent Q.L) ∧
      ∀ (p q : ℤ) (h : IsScaledPair a a' p q),
        P.twisting.app p ≫ (γ p q h).hom =
          (pullbackFunctor (ringedSpaceHom f)).map
              (eqToHom (congrArg A.piece (h.degree_eq hm))) ≫
            Q.twisting.app q

/-- A comparison of two quadruples at `(a, a')` is a family satisfying `IsComparisonAt`: the two
predicates are the same, so a statement about the families is a statement about `CompatibleAt`. -/
theorem compatibleAt_iff_exists_isComparisonAt (P : Quadruple f A d) (Q : Quadruple f A d')
    (a a' : ℤ) :
    CompatibleAt P Q a a' ↔
      ∃ (hm : a * d = a' * d')
        (γ : ∀ p q : ℤ, IsScaledPair a a' p q → ((laurent P.L).piece p ≅ (laurent Q.L).piece q)),
        IsComparisonAt P Q hm γ :=
  Iff.rfl

variable {a a' : ℤ} {hm : a * d = a' * d'}
  {γ γ' : ∀ p q : ℤ, IsScaledPair a a' p q → ((laurent P.L).piece p ≅ (laurent Q.L).piece q)}

/-- **A comparison is determined in every degree at which `ψ` is surjective.** The compatibility
with `ψ` says that the component of the comparison in degrees `(p, q)` composes with `ψ_p` to
the transport of `ψ'_q`, and `ψ_p` is an epimorphism for `p` positive. -/
theorem IsComparisonAt.hom_eq_of_pos (hγ : IsComparisonAt P Q hm γ)
    (hγ' : IsComparisonAt P Q hm γ') {p q : ℤ} (h : IsScaledPair a a' p q) (hp : 0 < p) :
    (γ p q h).hom = (γ' p q h).hom := by
  have := P.epi_app_of_pos hp
  exact (cancel_epi (P.twisting.app p)).mp ((hγ.2.2 p q h).trans (hγ'.2.2 p q h).symm)

/-- Whiskering on the right by an invertible module is faithful and zero-reflecting. -/
private theorem whiskerRight_injective_and_eq_zero_iff
    {M N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (Z : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) Z]
    (w w' : M ⟶ N) :
    (MonoidalCategoryStruct.whiskerRight w Z = MonoidalCategoryStruct.whiskerRight w' Z →
      w = w') ∧ (MonoidalCategoryStruct.whiskerRight w Z = 0 ↔ w = 0) := by
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
      (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj Z
  have : F.IsEquivalence :=
    Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible _ _ _
  have hb := bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T) w Z
  have hb' := bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T) w' Z
  exact ⟨fun h => F.map_injective (hb.trans (h.trans hb'.symm)),
    ⟨fun h => (Functor.map_eq_zero_iff F).mp (hb.trans h),
      fun h => hb.symm.trans ((Functor.map_eq_zero_iff F).mpr h)⟩⟩

private theorem IsComparisonAt.hom_eq_of_shift
    (hγ : IsComparisonAt P Q hm γ) (hγ' : IsComparisonAt P Q hm γ')
    {leftDegree rightDegree shiftLeftDegree shiftRightDegree : ℤ}
    (base : IsScaledPair a a' leftDegree rightDegree)
    (shift : IsScaledPair a a' shiftLeftDegree shiftRightDegree)
    (shift_eq : (γ shiftLeftDegree shiftRightDegree shift).hom =
      (γ' shiftLeftDegree shiftRightDegree shift).hom)
    (sum_eq : (γ (leftDegree + shiftLeftDegree) (rightDegree + shiftRightDegree)
      (base.add shift)).hom =
      (γ' (leftDegree + shiftLeftDegree) (rightDegree + shiftRightDegree)
        (base.add shift)).hom) :
    (γ leftDegree rightDegree base).hom = (γ' leftDegree rightDegree base).hom := by
  let : Mono ((laurent Q.L).mulSheaf rightDegree shiftRightDegree) :=
    mono_mulSheaf_laurent (T := T) (L := Q.L) rightDegree shiftRightDegree
  have tensorEquality :
      MonoidalCategoryStruct.tensorHom (γ leftDegree rightDegree base).hom
          (γ shiftLeftDegree shiftRightDegree shift).hom =
        MonoidalCategoryStruct.tensorHom (γ' leftDegree rightDegree base).hom
          (γ shiftLeftDegree shiftRightDegree shift).hom := by
    refine (cancel_mono ((laurent Q.L).mulSheaf rightDegree shiftRightDegree)).mp ?_
    refine (hγ.1 leftDegree rightDegree shiftLeftDegree shiftRightDegree base shift).trans ?_
    refine (congrArg (fun morphism =>
      (laurent P.L).mulSheaf leftDegree shiftLeftDegree ≫ morphism) sum_eq).trans ?_
    refine (hγ'.1 leftDegree rightDegree shiftLeftDegree shiftRightDegree base shift).symm.trans ?_
    exact congrArg (fun morphism => MonoidalCategoryStruct.tensorHom
      (γ' leftDegree rightDegree base).hom morphism ≫
        (laurent Q.L).mulSheaf rightDegree shiftRightDegree) shift_eq.symm
  have whiskeredEquality :
      ((γ leftDegree rightDegree base).hom ▷ (laurent P.L).piece shiftLeftDegree) ≫
          ((laurent Q.L).piece rightDegree ◁ (γ shiftLeftDegree shiftRightDegree shift).hom) =
        ((γ' leftDegree rightDegree base).hom ▷ (laurent P.L).piece shiftLeftDegree) ≫
          ((laurent Q.L).piece rightDegree ◁ (γ shiftLeftDegree shiftRightDegree shift).hom) :=
    (tensorHom_def (γ leftDegree rightDegree base).hom
      (γ shiftLeftDegree shiftRightDegree shift).hom).symm.trans
        (tensorEquality.trans (tensorHom_def (γ' leftDegree rightDegree base).hom
          (γ shiftLeftDegree shiftRightDegree shift).hom))
  let : IsIso (MonoidalCategoryStruct.whiskerLeft ((laurent Q.L).piece rightDegree)
      (γ shiftLeftDegree shiftRightDegree shift).hom) :=
    (MonoidalCategory.whiskerLeftIso ((laurent Q.L).piece rightDegree)
      (γ shiftLeftDegree shiftRightDegree shift)).isIso_hom
  have cancelled := (cancel_mono
    ((laurent Q.L).piece rightDegree ◁ (γ shiftLeftDegree shiftRightDegree shift).hom)).mp
      whiskeredEquality
  let : AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
      (isSheafStruct T) ((laurent P.L).piece shiftLeftDegree) :=
    isInvertible_tensorPower T.toRingedSpace.presheaf (isSheafStruct T) P.L shiftLeftDegree
  exact (whiskerRight_injective_and_eq_zero_iff ((laurent P.L).piece shiftLeftDegree) _ _).1
    cancelled

/-- **A comparison at a pair `(a, a')` with `a` positive is determined in every degree, not only
in the positive ones.**

The degrees at which a comparison has a component are the `(n a, n a')`, and for `n` positive the
previous statement applies. For `n` non-positive, choose `m` positive with `n + m = 1`:
multiplicativity in the bidegree `((n a, n a'), (m a, m a'))` expresses the tensor product of the
component at `n` with the component at `m` through the component at `n + m = 1`, both of which are
already determined, and the multiplications of the two Laurent algebras are invertible. Cancelling
the invertible component at `m` and the invertible multiplications leaves the component at `n`
whiskered by `L^{⊗ m a}`, and whiskering by a tensor power of an invertible module is an
equivalence, hence faithful. -/
theorem IsComparisonAt.hom_eq (hγ : IsComparisonAt P Q hm γ) (hγ' : IsComparisonAt P Q hm γ')
    (ha : 0 < a) (p q : ℤ) (h : IsScaledPair a a' p q) :
    (γ p q h).hom = (γ' p q h).hom := by
  obtain ⟨n, hp, hq⟩ := id h
  subst hp
  subst hq
  rcases lt_or_ge 0 n with hn | hn
  · exact hγ.hom_eq_of_pos hγ' h (mul_pos hn ha)
  obtain ⟨m, hm0, hsum⟩ : ∃ m : ℤ, 0 < m ∧ n + m = 1 := ⟨1 - n, by omega, by omega⟩
  have hn' : IsScaledPair a a' (n * a) (n * a') := ⟨n, rfl, rfl⟩
  have hmS : IsScaledPair a a' (m * a) (m * a') := ⟨m, rfl, rfl⟩
  have hsa : n * a + m * a = a := by
    calc n * a + m * a = (n + m) * a := by ring
      _ = 1 * a := by rw [hsum]
      _ = a := one_mul a
  have hpossum : 0 < n * a + m * a := by rw [hsa]; exact ha
  have e1 := hγ.hom_eq_of_pos hγ' hmS (mul_pos hm0 ha)
  have e2 := hγ.hom_eq_of_pos hγ' (hn'.add hmS) hpossum
  exact hγ.hom_eq_of_shift hγ' hn' hmS e1 e2

/-- **The comparison of two quadruples at a fixed pair `(a, a')` with `a` positive is unique.**
Two families satisfying the three conditions of a comparison are equal.

Uniqueness is what the descent step of Tag 01NW consumes: a comparison constructed on the
members of an open cover of the test scheme agrees with any other on the overlaps for free, so
it glues. -/
theorem IsComparisonAt.eq (hγ : IsComparisonAt P Q hm γ) (hγ' : IsComparisonAt P Q hm γ')
    (ha : 0 < a) : γ = γ' := by
  funext p q h
  exact Iso.ext (hγ.hom_eq hγ' ha p q h)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

/-! ### Descending a comparison to a less divisible pair of degrees

The source of Tag 01NW calls the implication (3) implies (1) "not a complete triviality": a
comparison at a common multiple `(a, a')` of the two degrees has to be replaced by one at the pair
of cofactors of the least common multiple, and the components of the first are defined only in the
degrees `(n a, n a')`.

What follows descends one component. Its input is that `ψ_p` and `ψ'_q` are surjective, so that
`L^{⊗ p}` and `(L')^{⊗ q}` are two quotients of one and the same `f^*𝒜_{p d} = f^*𝒜_{q d'}`, and
its content is that the two quotients coincide. The argument is formal: no local trivialisation of
`L` and no open cover of the test scheme appears.
-/

section Descent

open CategoryTheory.Limits

attribute [local instance] modulesAbelian

variable {X Y : RingedSpace.{u, u}}

/-- **Naturality of the comparison `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` of Tag 01CD in both variables at
once**, obtained by composing the two whiskered naturality statements
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_naturality_left` and
`..._naturality_right`. -/
theorem tensorComparison_naturality (f : X ⟶ Y)
    {A A' B B' : SheafOfModules.{u} (structureRingSheaf Y)} (a : A ⟶ A') (b : B ⟶ B') :
    (pullbackFunctor f).map (MonoidalCategoryStruct.tensorHom a b) ≫
        pullbackTensorComparison f A' B' =
      pullbackTensorComparison f A B ≫
        MonoidalCategoryStruct.tensorHom ((pullbackFunctor f).map a)
          ((pullbackFunctor f).map b) := by
  rw [MonoidalCategory.tensorHom_def, CategoryTheory.Functor.map_comp, Category.assoc,
    pullbackTensorComparison_naturality_right f b, ← Category.assoc,
    pullbackTensorComparison_naturality_left f a, Category.assoc,
    MonoidalCategory.tensorHom_def]

/-- **Naturality of the inverse of the comparison of Tag 01CD in both variables at once.** The
comparison is an isomorphism, so transposing `tensorComparison_naturality` moves a tensor product
of two pulled-back morphisms across it. -/
theorem tensorComparison_inv_naturality (f : X ⟶ Y)
    {A A' B B' : SheafOfModules.{u} (structureRingSheaf Y)} (a : A ⟶ A') (b : B ⟶ B') :
    MonoidalCategoryStruct.tensorHom ((pullbackFunctor f).map a) ((pullbackFunctor f).map b) ≫
        inv (pullbackTensorComparison f A' B') =
      inv (pullbackTensorComparison f A B) ≫
        (pullbackFunctor f).map (MonoidalCategoryStruct.tensorHom a b) := by
  rw [IsIso.comp_inv_eq, Category.assoc, tensorComparison_naturality f a b, IsIso.inv_hom_id_assoc]


/-- **A morphism of sheaves of modules vanishes as soon as it does after tensoring on the right by
an invertible module.** Tensoring by an invertible module is an equivalence, hence full, faithful,
and therefore zero-preserving. -/
theorem whiskerRight_eq_zero_iff {T : Scheme.{u}}
    {M N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (Z : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) Z]
    (w : M ⟶ N) : MonoidalCategoryStruct.whiskerRight w Z = 0 ↔ w = 0 := by
  exact (Quadruple.whiskerRight_injective_and_eq_zero_iff Z w 0).2

/-- **Two morphisms out of one sheaf of modules have the same kernel as soon as their tensor
products with a pair of morphisms onto invertible modules have a common factorisation.**

Precisely: if `(u ⊗ u₂) ≫ Θ = (v ⊗ v₂) ≫ Ξ` with `Ξ` a monomorphism, if `v₂` is an epimorphism and
if the targets `Z` and `Z'` of `u₂` and `v₂` are invertible, then `v` annihilates the kernel of
`u`.

The kernel of `u`, whiskered into the first factor, is killed by `u ⊗ u₂`, hence by `v ⊗ v₂` after
`Ξ`; the interchange law rewrites that composite as `K ◁ v₂` followed by `(ker u ≫ v) ▷ Z'`, and
`K ◁ v₂` is an epimorphism because a tensor product of epimorphisms is one. Whiskering by the
invertible `Z'` is faithful, so `ker u ≫ v` vanishes. -/
theorem kernel_ι_comp_eq_zero {T : Scheme.{u}}
    {N N' M M' Z Z' W : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) Z]
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) Z']
    (u : N ⟶ M) (u₂ : N' ⟶ Z) (v : N ⟶ M') (v₂ : N' ⟶ Z') [Epi v₂]
    (Θ : M ⊗ Z ⟶ W) (Ξ : M' ⊗ Z' ⟶ W) (hΞ : Mono Ξ)
    (hcomm : MonoidalCategoryStruct.tensorHom u u₂ ≫ Θ =
      MonoidalCategoryStruct.tensorHom v v₂ ≫ Ξ) :
    kernel.ι u ≫ v = 0 := by
  have hepi : Epi (MonoidalCategoryStruct.whiskerLeft (kernel u) v₂) := by
    have := epi_tensorHom T.toRingedSpace (CategoryStruct.id (kernel u)) v₂
    rwa [MonoidalCategory.id_tensorHom] at this
  have exch : ∀ {R R' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
      (r : N ⟶ R) (r₂ : N' ⟶ R'), MonoidalCategoryStruct.whiskerLeft (kernel u) r₂ ≫
        MonoidalCategoryStruct.whiskerRight (kernel.ι u ≫ r) R' =
      MonoidalCategoryStruct.whiskerRight (kernel.ι u) N' ≫
        MonoidalCategoryStruct.tensorHom r r₂ := fun r r₂ => by
    rw [MonoidalCategory.comp_whiskerRight, ← Category.assoc,
      MonoidalCategory.whisker_exchange, Category.assoc, MonoidalCategory.tensorHom_def']
  have h0 : MonoidalCategoryStruct.whiskerRight (kernel.ι u) N' ≫
      MonoidalCategoryStruct.tensorHom u u₂ = 0 := by
    rw [← exch, kernel.condition, (whiskerRight_eq_zero_iff Z (0 : kernel u ⟶ M)).mpr rfl,
      comp_zero]
  have h1 := exch v v₂
  have key : MonoidalCategoryStruct.whiskerLeft (kernel u) v₂ ≫
      MonoidalCategoryStruct.whiskerRight (kernel.ι u ≫ v) Z' = 0 := by
    refine hΞ.right_cancellation _ _ ?_
    rw [h1, Category.assoc, ← hcomm, ← Category.assoc, h0, zero_comp, zero_comp]
  have hz := (cancel_epi (MonoidalCategoryStruct.whiskerLeft (kernel u) v₂)).mp
    (key.trans (comp_zero (f := MonoidalCategoryStruct.whiskerLeft (kernel u) v₂)).symm)
  exact (whiskerRight_eq_zero_iff Z' _).mp hz

/-- **Two epimorphisms out of one object which annihilate each other's kernels have isomorphic
targets, compatibly with the two epimorphisms.** Each factors through the other, an epimorphism in
an abelian category being the cokernel of its kernel, and the two factorisations are mutually
inverse because the epimorphisms can be cancelled. -/
theorem exists_iso_of_kernel_comp_eq_zero {T : Scheme.{u}}
    {N M M' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (u : N ⟶ M) (v : N ⟶ M') [Epi u] [Epi v]
    (h1 : kernel.ι u ≫ v = 0) (h2 : kernel.ι v ≫ u = 0) :
    ∃ g : M ≅ M', u ≫ g.hom = v := by
  refine ⟨⟨Abelian.epiDesc u v h1, Abelian.epiDesc v u h2, ?_, ?_⟩, Abelian.comp_epiDesc u v h1⟩
  · refine (cancel_epi u).mp ?_
    rw [← Category.assoc, Abelian.comp_epiDesc, Abelian.comp_epiDesc, Category.comp_id]
  · refine (cancel_epi v).mp ?_
    rw [← Category.assoc, Abelian.comp_epiDesc, Abelian.comp_epiDesc, Category.comp_id]

/-- **The multiplication of a sheaf of graded algebras commutes with the transport of its two
arguments along equalities of degrees.** Both sides are the multiplication in the bidegree
`(i, j)` followed by the transport of the total degree to `k`. -/
theorem mulSheaf_eqToHom_comp {S : Scheme.{u}}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    {i j i' j' m k : ℤ} (hi : i = i') (hj : j = j')
    (h1 : i + j = m) (h2 : m = k) (h3 : i' + j' = k) :
    (A.mulSheaf i j ≫ eqToHom (congrArg A.piece h1)) ≫ eqToHom (congrArg A.piece h2) =
      MonoidalCategoryStruct.tensorHom (eqToHom (congrArg A.piece hi))
          (eqToHom (congrArg A.piece hj)) ≫
        (A.mulSheaf i' j' ≫ eqToHom (congrArg A.piece h3)) := by
  subst hi
  subst hj
  subst h2
  refine Eq.trans (Category.comp_id _) (Eq.trans (Category.id_comp _).symm ?_)
  exact congrArg (fun z => z ≫ A.mulSheaf i j ≫ eqToHom (congrArg A.piece h3))
    ((MonoidalCategory.tensorHom_id (CategoryStruct.id (A.piece i)) (A.piece j)).trans
      (MonoidalCategory.id_whiskerRight (A.piece i) (A.piece j))).symm

namespace Quadruple

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d d' : ℤ}

/-- **The compatibility of a single component of a comparison with `ψ`**: the morphism `g` carries
the degree-`p` component of `ψ` to the degree-`q` component of `ψ'`, across the identification of
`f^*𝒜_{p d}` with `f^*𝒜_{q d'}` supplied by `p d = q d'`.

This is the third clause of `Quadruple.CompatibleAt` at one pair of degrees, with neither the
multiplicativity nor the unit clause. -/
def IsCompAt (P : Quadruple f A d) (Q : Quadruple f A d') {p q : ℤ} (h : p * d = q * d')
    (g : (laurent P.L).piece p ⟶ (laurent Q.L).piece q) : Prop :=
  P.twisting.app p ≫ g =
    (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece h)) ≫ Q.twisting.app q

/-- The right-hand side of `isCompAt_tensor`, pushed through the comparison of the pullback with
the tensor product of Tag 01CD and through the multiplication of `𝒜`. -/
theorem isCompAt_tensor_rhs {Q : Quadruple f A d'} {p q p' q' : ℤ}
    (hp : p * d = q * d') (hp' : p' * d = q' * d') :
    MonoidalCategoryStruct.tensorHom
        ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ≫
          Q.twisting.app q)
        ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
          Q.twisting.app q') ≫ (laurent Q.L).mulSheaf q q' =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
            (MonoidalCategoryStruct.tensorHom (eqToHom (congrArg A.piece hp))
                (eqToHom (congrArg A.piece hp')) ≫
              (A.mulSheaf (q * d') (q' * d') ≫
                eqToHom (congrArg A.piece (by ring : q * d' + q' * d' = (q + q') * d')))) ≫
          Q.twisting.app (q + q') :=
calc MonoidalCategoryStruct.tensorHom
        ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ≫
          Q.twisting.app q)
        ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
          Q.twisting.app q') ≫ (laurent Q.L).mulSheaf q q'
      = (MonoidalCategoryStruct.tensorHom
            ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)))
            ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp'))) ≫
          MonoidalCategoryStruct.tensorHom (Q.twisting.app q) (Q.twisting.app q')) ≫
        (laurent Q.L).mulSheaf q q' :=
      congrArg (fun z => z ≫ (laurent Q.L).mulSheaf q q')
        (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm
    _ = MonoidalCategoryStruct.tensorHom
          ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)))
          ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp'))) ≫
        MonoidalCategoryStruct.tensorHom (Q.twisting.app q) (Q.twisting.app q') ≫
          (laurent Q.L).mulSheaf q q' := Category.assoc _ _ _
    _ = MonoidalCategoryStruct.tensorHom
          ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)))
          ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp'))) ≫
        (inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (q * d'))
              (A.piece (q' * d'))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map
              (A.mulSheaf (q * d') (q' * d') ≫
                eqToHom (congrArg A.piece
                  (by ring : q * d' + q' * d' = (q + q') * d'))) ≫
            Q.twisting.app (q + q')) :=
      congrArg (fun z => MonoidalCategoryStruct.tensorHom
          ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)))
          ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp'))) ≫ z)
        (Q.twisting.app_mul q q')
    _ = (MonoidalCategoryStruct.tensorHom
            ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)))
            ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp'))) ≫
          inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (q * d'))
            (A.piece (q' * d')))) ≫
        ((pullbackFunctor (ringedSpaceHom f)).map
            (A.mulSheaf (q * d') (q' * d') ≫
              eqToHom (congrArg A.piece
                (by ring : q * d' + q' * d' = (q + q') * d'))) ≫
          Q.twisting.app (q + q')) := (Category.assoc _ _ _).symm
    _ = (inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map
            (MonoidalCategoryStruct.tensorHom (eqToHom (congrArg A.piece hp))
              (eqToHom (congrArg A.piece hp')))) ≫
        ((pullbackFunctor (ringedSpaceHom f)).map
            (A.mulSheaf (q * d') (q' * d') ≫
              eqToHom (congrArg A.piece
                (by ring : q * d' + q' * d' = (q + q') * d'))) ≫
          Q.twisting.app (q + q')) :=
      congrArg (fun z => z ≫ ((pullbackFunctor (ringedSpaceHom f)).map
          (A.mulSheaf (q * d') (q' * d') ≫
            eqToHom (congrArg A.piece
              (by ring : q * d' + q' * d' = (q + q') * d'))) ≫
        Q.twisting.app (q + q')))
        (tensorComparison_inv_naturality (ringedSpaceHom f) (eqToHom (congrArg A.piece hp))
          (eqToHom (congrArg A.piece hp')))
    _ = inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
            (MonoidalCategoryStruct.tensorHom (eqToHom (congrArg A.piece hp))
              (eqToHom (congrArg A.piece hp'))) ≫
          ((pullbackFunctor (ringedSpaceHom f)).map
              (A.mulSheaf (q * d') (q' * d') ≫
                eqToHom (congrArg A.piece
                  (by ring : q * d' + q' * d' = (q + q') * d'))) ≫
            Q.twisting.app (q + q')) := Category.assoc _ _ _
    _ = inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
            (MonoidalCategoryStruct.tensorHom (eqToHom (congrArg A.piece hp))
                (eqToHom (congrArg A.piece hp')) ≫
              (A.mulSheaf (q * d') (q' * d') ≫
                eqToHom (congrArg A.piece
                  (by ring : q * d' + q' * d' = (q + q') * d')))) ≫
          Q.twisting.app (q + q') :=
      congrArg (fun z => inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
          (A.piece (p' * d))) ≫ z)
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ Q.twisting.app (q + q'))
            (CategoryTheory.Functor.map_comp (pullbackFunctor (ringedSpaceHom f))
              _ _).symm))

/-- **A comparison in the degrees `(p + p', q + q')` compares the tensor products of the
components in the degrees `(p, q)` and `(p', q')`.** The multiplicativity of `ψ` and of `ψ'` turns
the compatibility in the total degree into one of `ψ_p ⊗ ψ_{p'}` with `ψ'_q ⊗ ψ'_{q'}`, mediated by
the multiplications of the two Laurent algebras; the transport on the algebra side is
`mulSheaf_eqToHom_comp`. -/
theorem isCompAt_tensor {P : Quadruple f A d} {Q : Quadruple f A d'} {p q p' q' : ℤ}
    (hp : p * d = q * d') (hp' : p' * d = q' * d')
    (hsum : (p + p') * d = (q + q') * d')
    (δ : (laurent P.L).piece (p + p') ⟶ (laurent Q.L).piece (q + q'))
    (hδ : IsCompAt P Q hsum δ) :
    MonoidalCategoryStruct.tensorHom (P.twisting.app p) (P.twisting.app p') ≫
        (laurent P.L).mulSheaf p p' ≫ δ =
      MonoidalCategoryStruct.tensorHom
        ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ≫
          Q.twisting.app q)
        ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
          Q.twisting.app q') ≫ (laurent Q.L).mulSheaf q q' :=
  calc MonoidalCategoryStruct.tensorHom (P.twisting.app p) (P.twisting.app p') ≫
        (laurent P.L).mulSheaf p p' ≫ δ
      = (MonoidalCategoryStruct.tensorHom (P.twisting.app p) (P.twisting.app p') ≫
          (laurent P.L).mulSheaf p p') ≫ δ := (Category.assoc _ _ _).symm
    _ = (inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
              (A.piece (p' * d))) ≫
            (pullbackFunctor (ringedSpaceHom f)).map
                (A.mulSheaf (p * d) (p' * d) ≫
                  eqToHom (congrArg A.piece (by ring : p * d + p' * d = (p + p') * d))) ≫
              P.twisting.app (p + p')) ≫ δ :=
        congrArg (fun z => z ≫ δ) (P.twisting.app_mul p p')
    _ = inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
          ((pullbackFunctor (ringedSpaceHom f)).map
              (A.mulSheaf (p * d) (p' * d) ≫
                eqToHom (congrArg A.piece (by ring : p * d + p' * d = (p + p') * d))) ≫
            P.twisting.app (p + p')) ≫ δ := Category.assoc _ _ _
    _ = inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map
              (A.mulSheaf (p * d) (p' * d) ≫
                eqToHom (congrArg A.piece (by ring : p * d + p' * d = (p + p') * d))) ≫
            (P.twisting.app (p + p') ≫ δ) :=
        congrArg (fun z => inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
          (A.piece (p' * d))) ≫ z) (Category.assoc _ _ _)
    _ = inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map
              (A.mulSheaf (p * d) (p' * d) ≫
                eqToHom (congrArg A.piece (by ring : p * d + p' * d = (p + p') * d))) ≫
            ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hsum)) ≫
              Q.twisting.app (q + q')) :=
        congrArg (fun z => inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map
              (A.mulSheaf (p * d) (p' * d) ≫
                eqToHom (congrArg A.piece (by ring : p * d + p' * d = (p + p') * d))) ≫ z) hδ
    _ = inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map
              ((A.mulSheaf (p * d) (p' * d) ≫
                  eqToHom (congrArg A.piece (by ring : p * d + p' * d = (p + p') * d))) ≫
                eqToHom (congrArg A.piece hsum)) ≫
            Q.twisting.app (q + q') :=
        congrArg (fun z => inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫ z)
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun z => z ≫ Q.twisting.app (q + q'))
              (CategoryTheory.Functor.map_comp (pullbackFunctor (ringedSpaceHom f)) _ _).symm))
    _ = inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map
              (MonoidalCategoryStruct.tensorHom (eqToHom (congrArg A.piece hp))
                  (eqToHom (congrArg A.piece hp')) ≫
                (A.mulSheaf (q * d') (q' * d') ≫
                  eqToHom (congrArg A.piece
                    (by ring : q * d' + q' * d' = (q + q') * d')))) ≫
            Q.twisting.app (q + q') :=
        congrArg (fun z => inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (p * d))
            (A.piece (p' * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map z ≫ Q.twisting.app (q + q'))
          (mulSheaf_eqToHom_comp A hp hp' (by ring) hsum (by ring))
    _ = MonoidalCategoryStruct.tensorHom
          ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ≫
            Q.twisting.app q)
          ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
            Q.twisting.app q') ≫ (laurent Q.L).mulSheaf q q' :=
        (isCompAt_tensor_rhs hp hp').symm

/-- **The descent of a comparison to a less divisible pair of degrees.** If an isomorphism
carries the degree-`(p + p')` component of `ψ` to the degree-`(q + q')` component of `ψ'`, and all
four degrees are positive, then some isomorphism carries the degree-`p` component of `ψ` to the
degree-`q` component of `ψ'`.

Both `ψ_p` and `ψ'_q` are surjective, so `L^{⊗ p}` and `(L')^{⊗ q}` are two quotients of one and
the same sheaf `f^*𝒜_{p d} = f^*𝒜_{q d'}`, and what has to be shown is that the two have the same
kernel. The given isomorphism in degree `p + p'` says, through the multiplicativity of `ψ` and
`ψ'`, that the two kernels agree after tensoring with the degree-`p'` part; the surjectivity of
`ψ'_{q'}` cancels the second factor, and tensoring by the invertible module `(L')^{⊗ q'}` is
faithful. No local trivialisation of `L` is used. -/
theorem exists_isCompAt_of_add {P : Quadruple f A d} {Q : Quadruple f A d'} {p q p' q' : ℤ}
    (hp : p * d = q * d') (hp' : p' * d = q' * d') (hsum : (p + p') * d = (q + q') * d')
    (hp0 : 0 < p) (hq0 : 0 < q) (hp'0 : 0 < p') (hq'0 : 0 < q')
    (δ : (laurent P.L).piece (p + p') ≅ (laurent Q.L).piece (q + q'))
    (hδ : IsCompAt P Q hsum δ.hom) :
    ∃ g : (laurent P.L).piece p ≅ (laurent Q.L).piece q, IsCompAt P Q hp g.hom := by
  have hmQ : Mono ((laurent Q.L).mulSheaf q q') := mono_mulSheaf_laurent q q'
  have hmP : Mono ((laurent P.L).mulSheaf p p') := mono_mulSheaf_laurent p p'
  have hZ : AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
      (isSheafStruct T) ((laurent P.L).piece p') :=
    isInvertible_tensorPower T.toRingedSpace.presheaf (isSheafStruct T) P.L p'
  have hZ' : AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
      (isSheafStruct T) ((laurent Q.L).piece q') :=
    isInvertible_tensorPower T.toRingedSpace.presheaf (isSheafStruct T) Q.L q'
  have hep : Epi (P.twisting.app p) := P.epi_app_of_pos hp0
  have hep' : Epi (P.twisting.app p') := P.epi_app_of_pos hp'0
  have heq0 : Epi (Q.twisting.app q) := Q.epi_app_of_pos hq0
  have heq' : Epi (Q.twisting.app q') := Q.epi_app_of_pos hq'0
  have hev : Epi ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ≫
      Q.twisting.app q) := epi_comp _ _
  have hev' : Epi ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
      Q.twisting.app q') := epi_comp _ _
  have hcomm := isCompAt_tensor hp hp' hsum δ.hom hδ
  have hcomm' : MonoidalCategoryStruct.tensorHom
        ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ≫
          Q.twisting.app q)
        ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
          Q.twisting.app q') ≫ (laurent Q.L).mulSheaf q q' ≫ δ.inv =
      MonoidalCategoryStruct.tensorHom (P.twisting.app p) (P.twisting.app p') ≫
        (laurent P.L).mulSheaf p p' :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ δ.inv) hcomm.symm).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z => MonoidalCategoryStruct.tensorHom (P.twisting.app p)
              (P.twisting.app p') ≫ z)
            ((Category.assoc _ _ _).trans
              ((congrArg (fun z => (laurent P.L).mulSheaf p p' ≫ z) δ.hom_inv_id).trans
                (Category.comp_id _))))))
  exact exists_iso_of_kernel_comp_eq_zero _ _
    (kernel_ι_comp_eq_zero (P.twisting.app p) (P.twisting.app p')
      ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ≫
        Q.twisting.app q)
      ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
        Q.twisting.app q')
      ((laurent P.L).mulSheaf p p' ≫ δ.hom) ((laurent Q.L).mulSheaf q q') hmQ hcomm)
    (kernel_ι_comp_eq_zero
      ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ≫
        Q.twisting.app q)
      ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
        Q.twisting.app q')
      (P.twisting.app p) (P.twisting.app p')
      ((laurent Q.L).mulSheaf q q' ≫ δ.inv) ((laurent P.L).mulSheaf p p') hmP hcomm')

/-- **There is a comparison of `P` with `Q` in the degrees `(p, q)`**: the degrees satisfy
`p d = q d'`, and some isomorphism `L^{⊗ p} ≅ (L')^{⊗ q}` carries `ψ_p` to `ψ'_q`.

This is the existential form of `IsCompAt`, in which the degrees are the only data, so that it can
be transported along an equality of degrees. -/
def HasCompAt (P : Quadruple f A d) (Q : Quadruple f A d') (p q : ℤ) : Prop :=
  ∃ (h : p * d = q * d') (g : (laurent P.L).piece p ≅ (laurent Q.L).piece q),
    IsCompAt P Q h g.hom

/-- A comparison in a pair of degrees is a comparison in any equal pair of degrees. -/
theorem HasCompAt.congr {P : Quadruple f A d} {Q : Quadruple f A d'} {p q p' q' : ℤ}
    (hp : p = p') (hq : q = q') (h : HasCompAt P Q p q) : HasCompAt P Q p' q' := by
  subst hp
  subst hq
  exact h

/-- `exists_isCompAt_of_add`, read through `HasCompAt`. -/
theorem HasCompAt.of_add {P : Quadruple f A d} {Q : Quadruple f A d'} {p q p' q' : ℤ}
    (hp : p * d = q * d') (hp' : p' * d = q' * d')
    (hp0 : 0 < p) (hq0 : 0 < q) (hp'0 : 0 < p') (hq'0 : 0 < q')
    (h : HasCompAt P Q (p + p') (q + q')) : HasCompAt P Q p q := by
  obtain ⟨hsum, δ, hδ⟩ := h
  obtain ⟨g, hg⟩ := exists_isCompAt_of_add hp hp' hsum hp0 hq0 hp'0 hq'0 δ hδ
  exact ⟨hp, g, hg⟩

/-- **Stacks Project, Tag 01NW: the descent of a comparison to a less divisible pair of degrees,
in every positive degree.** Two quadruples compatible at `(k a₀, k a₀')`, with `k`, `a₀` and `a₀'`
positive, admit for every positive `n` an isomorphism `L^{⊗ n a₀} ≅ (L')^{⊗ n a₀'}` carrying
`ψ_{n a₀}` to `ψ'_{n a₀'}`.

For `k = 1` this is the given comparison. For `k > 1` the given comparison is a compatibility in
the degrees `(n k a₀, n k a₀') = (n a₀ + (k - 1) n a₀, n a₀' + (k - 1) n a₀')`, which
`exists_isCompAt_of_add` descends to `(n a₀, n a₀')`. -/
theorem hasCompAt_of_compatibleAt_mul {P : Quadruple f A d} {Q : Quadruple f A d'}
    {a₀ a₀' k : ℤ} (hk : 0 < k) (ha₀ : 0 < a₀) (ha₀' : 0 < a₀')
    (h : CompatibleAt P Q (k * a₀) (k * a₀')) {n : ℤ} (hn : 0 < n) :
    HasCompAt P Q (n * a₀) (n * a₀') := by
  obtain ⟨hm, γ, _, _, hψ⟩ := h
  have hsp : IsScaledPair (k * a₀) (k * a₀') (n * (k * a₀)) (n * (k * a₀')) := ⟨n, rfl, rfl⟩
  have hbase : HasCompAt P Q (n * (k * a₀)) (n * (k * a₀')) :=
    ⟨hsp.degree_eq hm, γ _ _ hsp, hψ _ _ hsp⟩
  have hm₀ : a₀ * d = a₀' * d' := mul_left_cancel₀ hk.ne' (by linear_combination hm)
  rcases eq_or_lt_of_le (show (1 : ℤ) ≤ k from hk) with hk1 | hk1
  · exact hbase.congr (by rw [← hk1]; ring) (by rw [← hk1]; ring)
  · refine HasCompAt.of_add (p' := (k - 1) * (n * a₀)) (q' := (k - 1) * (n * a₀'))
      (by linear_combination n * hm₀) (by linear_combination (k - 1) * n * hm₀)
      (mul_pos hn ha₀) (mul_pos hn ha₀') (mul_pos (by omega) (mul_pos hn ha₀))
      (mul_pos (by omega) (mul_pos hn ha₀')) (hbase.congr (by ring) (by ring))

/-- **Stacks Project, Tag 01NW: the descent to the least common multiple, in every positive
degree.** If two quadruples of positive degrees `d` and `d'` are compatible at some `(a, a')` with
`a` positive — condition (3) of the tag — then for every positive `n` there is an isomorphism
`L^{⊗ n a₀} ≅ (L')^{⊗ n a₀'}` carrying `ψ_{n a₀}` to `ψ'_{n a₀'}`, where `m₀ = a₀ d = a₀' d'` is
the least common multiple of the two degrees. In the degree `n = 1` this is the isomorphism `β` of
condition (1).

The common multiple `m = a d` is positive, hence divisible by `m₀`, so `a = k a₀` and `a' = k a₀'`
for a single positive `k`, and `hasCompAt_of_compatibleAt_mul` applies. -/
theorem hasCompAt_lcm_of_compatibleAt {P : Quadruple f A d} {Q : Quadruple f A d'}
    (hd : 0 < d) (hd' : 0 < d') {a a' a₀ a₀' : ℤ} (ha : 0 < a)
    (ha₀ : (Int.lcm d d' : ℤ) = a₀ * d) (ha₀' : (Int.lcm d d' : ℤ) = a₀' * d')
    (h : CompatibleAt P Q a a') {n : ℤ} (hn : 0 < n) :
    HasCompAt P Q (n * a₀) (n * a₀') := by
  obtain ⟨hm, -⟩ := id h
  have hlcm : 0 < (Int.lcm d d' : ℤ) := by
    have h1 : 0 < Int.lcm d d' :=
      Nat.lcm_pos (Int.natAbs_pos.mpr hd.ne') (Int.natAbs_pos.mpr hd'.ne')
    exact_mod_cast h1
  have hA₀ : 0 < a₀ := by nlinarith
  have hA₀' : 0 < a₀' := by nlinarith
  have hd1 : d ∣ a * d := dvd_mul_left d a
  have hd2 : d' ∣ a * d := by rw [hm]; exact dvd_mul_left d' a'
  have hdvd : (Int.lcm d d' : ℤ) ∣ a * d := Int.coe_lcm_dvd_iff.mpr ⟨hd1, hd2⟩
  obtain ⟨k, hkeq⟩ := hdvd
  have hk : 0 < k := by nlinarith
  have hak : a = k * a₀ := mul_right_cancel₀ hd.ne' (by linear_combination hkeq + k * ha₀)
  have hak' : a' = k * a₀' := mul_right_cancel₀ hd'.ne' (by
    linear_combination hkeq - hm + k * ha₀')
  subst hak
  subst hak'
  exact hasCompAt_of_compatibleAt_mul hk hA₀ hA₀' h hn

end Quadruple

end Descent

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
