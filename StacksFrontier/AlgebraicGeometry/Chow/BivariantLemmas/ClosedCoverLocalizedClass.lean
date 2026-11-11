module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# The localized class of a set-theoretic cover by two closed subschemes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, and let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions
with `X = X₁ ∪ X₂` set theoretically. **Stacks 0F9H** attaches to a perfect object
`E₂ ∈ D(𝒪_{X₂})` whose Chern classes are defined and which restricts on `X₁ ∩ X₂` to zero,
respectively to a finite locally free module of rank `< p` in cohomological degree `0`, bivariant
classes `P'_p(E₂)`, `c'_p(E₂) ∈ A^p(X₂ ⟶ X)`, and characterizes them by

  `c'_p(E₂) ∩ i₂,*α₂ = c_p(E₂) ∩ α₂`  and  `c'_p(E₂) ∩ i₁,*α₁ = 0`

for `αᵢ ∈ CH_k(Xᵢ)`, and similarly after any base change `X' ⟶ X`.

`Stacks.Chow.IsClosedCoverLocalizedClass` is that characterizing property, and
`Stacks.Chow.eq_of_isClosedCoverLocalizedClass` says that the class it characterizes does not
depend on the choice of `X₁`. Applied to the classes `P'_p(E₂)` and `c'_p(E₂)` constructed in
`StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernClass` it gives
**Stacks 0FAH**, `Stacks.Chow.localizedPowerSumOfClosedCover_eq` and
`Stacks.Chow.localizedChernClassOfClosedCover_eq` in
`StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.IndependentLocalizedClass`.

## Main definitions

* `Stacks.Chow.closedCoverPushforward` — pushforward of Chow classes from the base change of a
  closed subscheme of `X` along a test morphism `g : T ⟶ X` to `T` itself. The structure-morphism
  bookkeeping is `Stacks.Chow.pullbackSnd_comp_structureMorphism_eq`, already in the library.
* `Stacks.Chow.IsClosedCoverLocalizedClass` — the characterizing property of Stacks 0F9H for a
  bivariant class in `A^p(X₂ ⟶ X)`, relative to the cover `X = X₁ ∪ X₂` and to a class
  `κ ∈ A^p(X₂)`.

## Main results

* `Stacks.Chow.eq_of_isClosedCoverLocalizedClass` — the key step of Stacks 0FAH: two bivariant
  classes in
  `A^p(X₂ ⟶ X)` with the characterizing property of Stacks 0F9H for the two covers
  `X = X₁ ∪ X₂` and `X = X₁' ∪ X₂` and for the same class `κ ∈ A^p(X₂)` are equal.
* `Stacks.Chow.isBirational_of_isIso_of_isIntegral` — an isomorphism onto an integral scheme is
  birational.
* `Stacks.Chow.isIso_pullbackSnd_of_range_eq_univ` — a closed subscheme of a reduced scheme whose
  support is the whole scheme is the scheme itself, read on the base change of a closed immersion
  along a test morphism.
* `Stacks.Chow.closedCoverPushforward_fundamentalChowClass` — that base change carries the
  fundamental class to the fundamental class when it is surjective and the test scheme is
  integral.

## Implementation notes

### Why the class on `X₂` is a parameter

The statement here is about an arbitrary class `κ ∈ A^p(X₂)` and arbitrary elements of
`A^p(X₂ ⟶ X)` satisfying `Stacks.Chow.IsClosedCoverLocalizedClass`. The source's hypotheses on
`E₂` — perfect, Chern classes defined, and `E₂|_{X₁ ∩ X₂}` zero respectively finite locally free
of rank `< p` in degree `0` — are used in Stacks 0F9H only to produce a class with that property.
Taking `κ` to be `P_p(E₂)` respectively `c_p(E₂)` and the two classes to be the constructions of
Stacks 0F9H (`Stacks.Chow.localizedPowerSumOfClosedCover`,
`Stacks.Chow.localizedChernClassOfClosedCover`) gives Stacks 0FAH itself, which is stated for
those classes in `StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.IndependentLocalizedClass`.

### The route through Stacks 02UC rather than Stacks 0F94

The source argues from `X = (X₁ ∩ X₁') ∪ X₂` that every class in `CH_k(X)` is a sum of a class
pushed forward from `X₁ ∩ X₁'` and one pushed forward from `X₂`, which is the surjectivity half
of Stacks 0F94 — and needs it on every base change of `X`, which this repository does not have.

The proof below instead tests the difference of the two classes against the fundamental class of
an integral scheme, which suffices by the criterion of Stacks 02UC. On an *integral* test
scheme the decomposition is trivial: the test scheme is irreducible and is covered by the
supports of the two base-changed closed subschemes, so one of them is the whole of it; and a
closed subscheme of a reduced scheme whose support is everything is the scheme itself, by
`AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective`. The fundamental class is therefore
pushed forward from one of the two pieces, and the two classes agree on it by the same clause of
their characterizations.

### The base-changed pieces

A test morphism `g : T ⟶ X` is tested against the base changes `pullback i₁ g` and
`pullback i₂ g`, with `pullback.snd` the closed immersion into `T`; this is the same fibre product
the cap operation of a bivariant class for `i₂` lands on, so clause (2) below needs no transport.
The scheme-theoretic preimage of a closed subscheme as an ideal sheaf,
`AlgebraicGeometry.Scheme.IdealSheafData.comap`, would present the pieces on the other side of
the fibre product and is not used.

## References

* [Stacks Project, Tag 0FAH](https://stacks.math.columbia.edu/tag/0FAH)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### An isomorphism onto an integral scheme is birational -/

/-- An isomorphism onto an integral scheme is birational: its source is integral too, and a
surjective morphism of irreducible schemes which is an isomorphism on the local ring at the
generic point is birational. -/
theorem isBirational_of_isIso_of_isIntegral {Z T : Scheme.{u}} [IsIntegral T] (m : Z ⟶ T)
    [IsIso m] : AlgebraicGeometry.IsBirational m := by
  have : IsIntegral Z := IsIntegral.of_isIso (CategoryTheory.inv m)
  exact isBirational_of_isIso_stalkMap_genericPoint m

/-! ### The base change of a closed immersion along a test morphism -/

/-- **A closed subscheme of a reduced scheme whose support is everything is the scheme itself**,
read on the base change of a closed immersion `i : Z ⟶ X` along a test morphism `g : T ⟶ X`: if
the base change is surjective then it is an isomorphism. -/
theorem isIso_pullbackSnd_of_range_eq_univ {X Z T : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (g : T ⟶ X) [IsReduced T]
    (hrange : Set.range (pullback.snd i g).base = Set.univ) : IsIso (pullback.snd i g) := by
  have : Surjective (pullback.snd i g) := ⟨Set.range_eq_univ.mp hrange⟩
  exact isIso_of_isClosedImmersion_of_surjective (pullback.snd i g)

section BaseChange

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (i : Z ⟶ X) [IsClosedImmersion i]

/-- Pushforward of Chow classes along the base change `T ×_X Z ⟶ T` of a closed subscheme
`i : Z ⟶ X` of `X` along a test morphism `g : T ⟶ X`. The base change of a closed immersion is a
closed immersion, so this needs no descent hypothesis: it is
`Stacks.Chow.chowPushforwardOfIsClosedImmersion`. -/
def closedCoverPushforward (hi : i ≫ sX = sZ) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (pullback.fst i g ≫ sZ) k →+ chowGroup C (g ≫ sX) k :=
  chowPushforwardOfIsClosedImmersion C (pullback.fst i g ≫ sZ) (g ≫ sX) (pullback.snd i g)
    (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi g) k

/-- **The surjective base change of a closed subscheme carries the fundamental class of an
integral test scheme to its fundamental class.** Being a surjective closed immersion into a
reduced scheme it is an isomorphism, hence birational, and proper pushforward along a proper
birational morphism onto an integral scheme preserves fundamental cycles. -/
theorem closedCoverPushforward_fundamentalChowClass (hi : i ≫ sX = sZ) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] [IsIntegral T]
    (hrange : Set.range (pullback.snd i g).base = Set.univ) (k : ℤ) :
    closedCoverPushforward C sX sZ i hi g k
        (fundamentalChowClass C (pullback.fst i g ≫ sZ) k) =
      fundamentalChowClass C (g ≫ sX) k := by
  have hiso : IsIso (pullback.snd i g) := isIso_pullbackSnd_of_range_eq_univ i g hrange
  have hbir : AlgebraicGeometry.IsBirational (pullback.snd i g) :=
    isBirational_of_isIso_of_isIntegral (pullback.snd i g)
  unfold closedCoverPushforward fundamentalChowClass
  rw [chowPushforwardOfIsClosedImmersion_mk,
    properPushforward_fundamentalCycle_of_isBirational C (pullback.fst i g ≫ sZ) (g ≫ sX)
      (pullback.snd i g) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi g) hbir k]

end BaseChange

/-! ### The characterizing property of Stacks 0F9H -/

section Characterization

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sX₁ : X₁ ⟶ C.S) [LocallyOfFiniteType sX₁] (sX₂ : X₂ ⟶ C.S)
  [LocallyOfFiniteType sX₂] (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (hi₁ : i₁ ≫ sX = sX₁)
  (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ sX = sX₂) (p : ℤ)

/-- **The characterizing property of Stacks 0F9H.** For closed immersions `i₁ : X₁ ⟶ X` and
`i₂ : X₂ ⟶ X` and a class `κ ∈ A^p(X₂)`, a bivariant class `c ∈ A^p(X₂ ⟶ X)` is *the localized
class of `κ` along the cover `X = X₁ ∪ X₂`* if, on every test scheme `g : T ⟶ X` locally of
finite type, `c` kills every Chow class pushed forward from `T ×_X X₁` and acts on a class pushed
forward from `T ×_X X₂` as `κ` does:

  `c ∩ i₁,*α₁ = 0`  and  `c ∩ i₂,*α₂ = κ ∩ α₂`.

Quantifying over all test schemes is the source's "and similarly after any base change". -/
def IsClosedCoverLocalizedClass (κ : chowCohomologyComponent C G sX₂ p)
    (c : BivariantClass C G sX₂ sX i₂ hi₂ p) : Prop :=
  (∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (pullback.fst i₁ g ≫ sX₁) k),
      c.cap g k (closedCoverPushforward C sX sX₁ i₁ hi₁ g k α) = 0) ∧
    ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (pullback.fst i₂ g ≫ sX₂) k),
      c.cap g k (closedCoverPushforward C sX sX₂ i₂ hi₂ g k α) =
        BivariantClass.toIdentityCapRule C G sX₂ p κ (pullback.fst i₂ g) k α

end Characterization

/-! ### Independence of the choice of `X₁` -/

section Independence

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X₁ X₁' X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sX₁ : X₁ ⟶ C.S) [LocallyOfFiniteType sX₁] (sX₁' : X₁' ⟶ C.S)
  [LocallyOfFiniteType sX₁'] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (i₁ : X₁ ⟶ X)
  [IsClosedImmersion i₁] (hi₁ : i₁ ≫ sX = sX₁) (i₁' : X₁' ⟶ X) [IsClosedImmersion i₁']
  (hi₁' : i₁' ≫ sX = sX₁') (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ sX = sX₂) (p : ℤ)

omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] in
/-- On a test scheme `g : T ⟶ X` the supports of the base changes of a set-theoretic cover of `X`
by two closed subschemes cover `T`: the range of the base change of a closed immersion is the
inverse image of its range. -/
theorem union_range_pullbackSnd_eq_univ {T : Scheme.{u}} (g : T ⟶ X)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    Set.range (pullback.snd i₁ g).base ∪ Set.range (pullback.snd i₂ g).base = Set.univ := by
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_union, hcover,
    Set.preimage_univ]

/-- A closed subset of an irreducible space containing its generic point is the whole space. -/
theorem eq_univ_of_isClosed_of_genericPoint_mem {T : Scheme.{u}} [IrreducibleSpace T]
    {A : Set T} (hA : IsClosed A) (hmem : genericPoint T ∈ A) : A = Set.univ := by
  have hclosure : closure {genericPoint T} = (Set.univ : Set T) := by
    simpa only [Set.top_eq_univ] using (genericPoint_spec T).def
  refine Set.univ_subset_iff.mp ?_
  rw [← hclosure]
  exact hA.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)

/-- On an *integral* test scheme one of the two base-changed pieces of a set-theoretic cover of
`X` by two closed subschemes is already the whole test scheme: the test scheme is irreducible and
its generic point lies in one of the two ranges, each of which is closed. -/
theorem range_pullbackSnd_eq_univ_or {T : Scheme.{u}} (g : T ⟶ X) [IsIntegral T]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    Set.range (pullback.snd i₁ g).base = Set.univ ∨
      Set.range (pullback.snd i₂ g).base = Set.univ := by
  have hmem : genericPoint T ∈
      Set.range (pullback.snd i₁ g).base ∪ Set.range (pullback.snd i₂ g).base := by
    rw [union_range_pullbackSnd_eq_univ i₁ i₂ g hcover]
    exact Set.mem_univ _
  rcases hmem with h | h
  · exact Or.inl (eq_univ_of_isClosed_of_genericPoint_mem
      (pullback.snd i₁ g).isClosedEmbedding.isClosed_range h)
  · exact Or.inr (eq_univ_of_isClosed_of_genericPoint_mem
      (pullback.snd i₂ g).isClosedEmbedding.isClosed_range h)

/-- If a bivariant class `c` for `i₂` acts in a fixed way on the classes pushed forward from the
base change of a closed subscheme `j` that fills an integral test scheme, it acts so on `[T]`. -/
private theorem cap_fundamentalChowClass_eq_of_range_eq_univ {X X₂ Y : Scheme.{u}}
    (C : ChowSituation.{u}) (G : GysinSystem C) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂]
    (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ sX = sX₂) {p : ℤ}
    (c : BivariantClass C G sX₂ sX i₂ hi₂ p) (j : Y ⟶ X) [IsClosedImmersion j]
    (hj : j ≫ sX = sY) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] [IsIntegral T]
    (hrange : Set.range (pullback.snd j g).base = Set.univ) (k : ℤ)
    (v : chowGroup C (pullback.fst j g ≫ sY) k → chowGroup C (pullback.fst i₂ g ≫ sX₂) (k - p))
    (h : ∀ α, c.cap g k (closedCoverPushforward C sX sY j hj g k α) = v α) :
    c.cap g k (fundamentalChowClass C (g ≫ sX) k) =
      v (fundamentalChowClass C (pullback.fst j g ≫ sY) k) := by
  rw [← h, closedCoverPushforward_fundamentalChowClass C sX sY j hj g hrange k]

/-- **Independence of the choice of `X₁`**, the key step of Stacks 0FAH. The localized class of
Stacks 0F9H does not depend on the choice of `X₁`: if
`c` has the characterizing property for the cover `X = X₁ ∪ X₂` and `c'` has it for the cover
`X = X₁' ∪ X₂`, both with the same class `κ ∈ A^p(X₂)`, then `c = c'`.

By Stacks 02UC it is enough that `c - c'` kill the fundamental class of every integral scheme
`T` locally of finite type over `X`. Such a `T` is irreducible and covered by the base changes of
the two closed subschemes of whichever cover, so for each cover one of the two pieces is the whole
of `T`; being a surjective closed immersion into a reduced scheme that piece is an isomorphism,
and `[T]` is the pushforward of the fundamental class of the piece. If the `X₂`-piece fills `T`
then both classes cap `[T]` to `κ ∩ [T]`; otherwise the `X₁`-piece and the `X₁'`-piece both fill
`T`, and both classes cap `[T]` to zero. -/
theorem eq_of_isClosedCoverLocalizedClass
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (hcover' : Set.range i₁'.base ∪ Set.range i₂.base = Set.univ)
    {κ : chowCohomologyComponent C G sX₂ p} {c c' : BivariantClass C G sX₂ sX i₂ hi₂ p}
    (hc : IsClosedCoverLocalizedClass C G sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ p κ c)
    (hc' : IsClosedCoverLocalizedClass C G sX sX₁' sX₂ i₁' hi₁' i₂ hi₂ p κ c') :
    c = c' := by
  have hzero : c - c' = 0 := by
    rw [BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero]
    intro T g _ _ k
    rw [BivariantClass.sub_cap, sub_eq_zero]
    by_cases h₂ : Set.range (pullback.snd i₂ g).base = Set.univ
    · rw [cap_fundamentalChowClass_eq_of_range_eq_univ C G sX sX₂ sX₂ i₂ hi₂ c i₂ hi₂ g h₂ k _
        (hc.2 g k), cap_fundamentalChowClass_eq_of_range_eq_univ C G sX sX₂ sX₂ i₂ hi₂ c' i₂ hi₂ g
        h₂ k _ (hc'.2 g k)]
    · rw [cap_fundamentalChowClass_eq_of_range_eq_univ C G sX sX₁ sX₂ i₂ hi₂ c i₁ hi₁ g
        ((range_pullbackSnd_eq_univ_or i₁ i₂ g hcover).resolve_right h₂) k _ (hc.1 g k),
        cap_fundamentalChowClass_eq_of_range_eq_univ C G sX sX₁' sX₂ i₂ hi₂ c' i₁' hi₁' g
        ((range_pullbackSnd_eq_univ_or i₁' i₂ g hcover').resolve_right h₂) k _ (hc'.1 g k)]
  exact sub_eq_zero.mp hzero

end Independence

end Stacks.Chow

end
