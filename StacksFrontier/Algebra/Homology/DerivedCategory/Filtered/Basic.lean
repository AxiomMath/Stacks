module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Localization.HomEquiv
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded functors on the filtered derived category, and bounded replacements

Let `𝒜` be an abelian category. A filtered cochain complex of `𝒜` is a cochain complex `K^•`
together with a decreasing `ℤ`-indexed filtration `F^p K^•` by subcomplexes; its `p`-th graded
piece is the quotient complex `gr^p K^• = F^p K^•/F^{p + 1} K^•`
(`CategoryTheory.FilteredObject.gr`), a morphism `α : K^• ⟶ L^•` is a *filtered
quasi-isomorphism* when every `gr^p(α)` is a quasi-isomorphism
(`CochainComplex.filteredQuasiIso`), and the filtered derived category
`DF(𝒜) = FQis(𝒜)^{-1}K(Fil^f(𝒜))` (`CochainComplex.FilteredDerivedCategory`) is the localisation
of the complexes of finitely filtered objects at those morphisms. Two theorems about these
notions are proved here.

*The functors `gr^p` and `(forget F)` followed by `Q` invert the filtered
quasi-isomorphisms*, which is the input to the universal property of localisation in
[Stacks, Tag 05S3]: a functor factors through a localisation exactly when it inverts the class
of morphisms localised at (`CategoryTheory.Localization.lift` and
`CategoryTheory.Localization.fac`, which is [Stacks, Tag 05R7]); the exact functors on `DF(𝒜)`
so obtained are constructed in `StacksFrontier.Homology.FilteredDerivedCategory.ExactFunctors`.
For `gr^p` that is the definition of a filtered
quasi-isomorphism together with the inversion of quasi-isomorphisms by `Q`, and it holds for an
arbitrary filtration. For `(forget F)` it is a theorem, and it needs finiteness: for the constant
filtration `F^p K^• = K^•` every graded piece vanishes, so `0 ⟶ K^•` is a filtered
quasi-isomorphism whose underlying morphism of complexes is not a quasi-isomorphism unless `K^•`
is acyclic. The proof forms the mapping cone `C(α)`, filters it by the cones `C(α_p)` of the
morphisms `α_p : F^p K^• ⟶ F^p L^•`, whose graded pieces are the acyclic cones `C(gr^p α)`, and
runs the descending induction of [Stacks, Tag 05QH] in a fixed degree `n`: homology in degree `n`
sees only the degrees `n - 1, n, n + 1`, hence only finitely many of the bounds at a time.

*A filtered complex may be replaced by one whose terms vanish where the homology of its
associated graded does.* If `H^n(gr(K^•)) = 0` for `n < a` there is a filtered quasi-isomorphism
`K^• ⟶ L^•` with `L^n = 0` for `n < a`; if `H^n(gr(K^•)) = 0` for `n > b` there is a filtered
quasi-isomorphism `M^• ⟶ K^•` with `M^n = 0` for `n > b`; and when both hold the two replacements
fit in a commutative square

```
M^• ⟶ K^•
 ↓       ↓
N^• ⟶ L^•
```

of filtered quasi-isomorphisms with `L^•` bounded below, `M^•` bounded above and `N^•` bounded.
The witnesses are the truncations `L^• = τ_{≥ a} K^•`, `M^• = τ_{≤ b} K^•` and
`N^• = τ_{≥ a} τ_{≤ b} K^•`, filtered by the truncations of the steps of the filtration of `K^•`;
the two points of the proof are that every step `F^p K^•` inherits the bounds on the homology of
the graded pieces, again by the descending induction of [Stacks, Tag 05QH], so that the canonical
map to, resp. from, its truncation is a quasi-isomorphism; and that the truncations of the steps
are subcomplexes of the truncation, which for `τ_{≥ a}` is the strictness of the differentials
asserted by [Stacks, Tag 05QH] and is proved here from a four lemma.

## Main results

* `CochainComplex.kernel_eq_filteredAcyclic_and_filteredQuasiIso_eq_inverseImage_isomorphisms`:
  the filtered acyclic complexes are strictly full and closed under retracts; every localisation
  `L` of the filtered complexes at the filtered quasi-isomorphisms has kernel the filtered acyclic
  complexes and inverts precisely the filtered quasi-isomorphisms; and each `H^n ∘ gr^p` inverts
  the filtered quasi-isomorphisms, hence factors through `L`.
* `CochainComplex.isIso_Q_map_gradedPiece_and_forget_of_filteredQuasiIso`: a filtered
  quasi-isomorphism is inverted by `gr^p` followed by the localisation functor to `D(𝒜)`, for
  every `p`, and — when the two filtrations are finite in each degree — also by `(forget F)`
  followed by that functor.
* `CochainComplex.exists_filteredQuasiIso_bounded_of_isGE_of_isLE_gradedPiece`: the bounded below
  replacement `K^• ⟶ L^•`, the bounded above replacement `M^• ⟶ K^•`, and the commutative square
  the two fit in, as the three clauses of one statement about a filtered complex with finite
  filtration in each degree.
* `CategoryTheory.FilteredObject.isSplitMono_of_isFilteredInjective`: a strict monomorphism
  out of a filtered injective object of `Fil^f(𝒜)` is a split monomorphism.
* `CochainComplex.exists_filteredQuasiIso_isStrictlyGE_injective_gradedPiece`: over an abelian
  category with enough injectives, a filtered complex concentrated in degree `0` with finite
  filtration admits a filtered quasi-isomorphism into a complex of filtered injective objects
  vanishing in negative degrees.
* `CategoryTheory.FilteredObject.factors_of_isFilteredInjective`: a morphism into a filtered
  injective object of `Fil^f(𝒜)` extends along any strict morphism of filtered objects.
* `CochainComplex.exists_homotopy_zero_of_filteredAcyclic_of_injective_gradedPiece`: a morphism
  from a filtered acyclic complex into a bounded below complex of filtered injective objects is
  homotopic to zero by a filtered homotopy, i.e. `Hom_{K(Fil^f(𝒜))}(K^•, I^•) = 0`.
* `CochainComplex.exists_termwiseSplit_shortExact_of_filteredQuasiIso_of_injective_gr`: a short
  exact sequence of `Fil^f(𝒜)` lifts, along filtered quasi-isomorphisms of its outer terms into
  complexes of filtered injective objects, to a short exact sequence of filtered complexes that is
  termwise split.
* `CochainComplex.bijective_precomp_full_and_map_eq_iff_filteredHomotopy_of_injective_gradedPiece`:
  for a bounded below complex `I^•` of filtered injective objects, precomposition with a filtered
  quasi-isomorphism is bijective on filtered homotopy classes of morphisms into `I^•`, and
  `Hom_{K(Fil^f(𝒜))}(-, I^•)` already computes `Hom_{DF(𝒜)}(-, I^•)`.
* `CochainComplex.exists_hom_comp_eq_of_filteredQuasiIso_of_injective_gradedPiece`:
  a morphism of filtered objects, placed in degree `0`, lifts along a filtered quasi-isomorphism of
  its source into a filtered complex and any morphism of its target into a bounded below complex of
  filtered injective objects, to a morphism of the two complexes making the square commute on the
  nose.
* `CategoryTheory.FilteredObject.singleFil`: the functor placing a filtered object of `𝒜` in a
  single degree, together with its commutation with `gr^p`
  (`CategoryTheory.FilteredObject.gradedPieceSingleFilIso`) and the transfer of short exactness of
  the graded pieces (`CategoryTheory.FilteredObject.shortExact_gradedPiece_singleFil_map`) and of
  finiteness of the filtration (`CategoryTheory.FilteredObject.isDegreewiseFinite_singleFil`) to
  the object so placed.
* `CochainComplex.isStrictlyGE_isDegreewiseFinite_injective_gr_filteredQuasiIso_of_termwiseSplit`:
  the middle term of a termwise split short exact sequence of filtered complexes with bounded below
  outer terms vanishes in negative degrees, has degreewise finite filtration and filtered injective
  graded pieces, and the comparison map into it is a filtered quasi-isomorphism.

## Implementation notes

*Complexes rather than the homotopy category.* Filtered quasi-isomorphism and the vanishing
conditions on the graded pieces are invariant under filtered homotopy — `gr^p` is additive, so it
carries a filtered homotopy between `α` and `β` to a homotopy between `gr^p(α)` and `gr^p(β)`,
and quasi-isomorphism is homotopy invariant — so the hypotheses read on a representing morphism
of complexes are the source's hypotheses on `K(Fil^f(𝒜))`, and the morphisms produced in the
second theorem are morphisms of complexes, as in the source's own diagram. The square produced
in its third clause commutes on the nose, which is stronger than commuting in `K(Fil^f(𝒜))`.

*`DF(𝒜)` is not mentioned in the first theorem.* It is stated on filtered complexes, as the
hypothesis of the universal property (`CategoryTheory.MorphismProperty.IsInvertedBy` unfolded at
a single morphism); the induced exact functors on `DF(𝒜)`, which need the triangulated structure
of `K(Fil^f(𝒜))` and of `DF(𝒜)`, are built from it in
`StacksFrontier.Homology.FilteredDerivedCategory.ExactFunctors`.

*`gr` is the family `(gr^p)_p`, and the bounds are uniform in `p`.* The source phrases the
hypotheses with the single functor `gr = ⨁_p gr^p` into complexes of graded objects; the pieces
are the available reading — `GradedObject ℤ 𝒜` carries no `Preadditive` instance, so `K(Gr(𝒜))`
cannot be formed — and the correct one for a filtration that is not finite, homology commuting
with an infinite direct sum only when coproducts are exact. Homology of a complex of graded
objects is computed componentwise, so `H^n(gr(K^•)) = 0` says `H^n(gr^p K^•) = 0` for every `p`
with `n` independent of `p`: that is why the bound `a`, resp. `b`, of the second theorem is
quantified outside `p`. The per-`p` condition is strictly weaker, and with it that theorem is
false: for `K^•` the complex `ℤ` in degree `-1` and `ℤ` in degree `0` over `𝒜 = ModuleCat ℤ`,
with zero differential and `F^p K^• = K^•` for `p ≤ -1`, `F^0 K^• = ℤ` in degree `-1` and
`F^p K^• = 0` for `p ≥ 1`, each `gr^p K^•` is concentrated in one degree, while a filtered
quasi-isomorphism `K^• ⟶ L^•` with `L^n = 0` for `n < 0` would give
`ℤ = H^{-1}(gr^0 K^•) ≅ H^{-1}(gr^0 L^•) = 0`.

*Finiteness of the filtration is degreewise.* As in the source, `K^• ∈ K(Fil^f(𝒜))` asks the
filtration of each term `K^n` to be finite, the bounds depending on `n`: spelled
`∀ n, ∃ p q, IsIso ((K.filtration.ι.app (op p)).f n) ∧ IsZero ((K.filtration.obj (op q)).X n)`,
the degreewise form of `CategoryTheory.Filtration.IsFinite` applied to the filtration of `K^n`.
That is strictly weaker than finiteness of the filtration of the complex `K^•`, one `p` and one
`q` serving all degrees at once (the uniformly bounded objects are Illusie's smaller filtered
derived category), and it is all the proofs use. Neither half of it can be dropped: with the
constant filtration `F^p K^• = K^•` (no vanishing) or the zero filtration `F^p K^• = 0` (no
exhaustion) every graded piece is zero, so every morphism is a filtered quasi-isomorphism and the
underlying morphism of complexes is arbitrary; and for `K^•` the module `⨁_{p ≥ 0} ℤ` in degree
`0` filtered by `F^p K^• = ⨁_{q ≥ p} ℤ` for `p ≥ 0`, which exhausts but never vanishes, every
graded piece is `ℤ` in degree `0`, while a complex finitely filtered in degree `0` has
`gr^p = 0` in degree `0` for all large `p`, so no replacement of `K^•` inside `K(Fil^f(𝒜))`
exists at all. The same clause is part of the conclusion of the second theorem, for each complex
produced: the source's replacements are again objects of `K(Fil^f(𝒜))`.

*The bounds of the third clause of the second theorem are pinned to `a` and `b`.* The source
asserts only that `L^•` is bounded below, `M^•` bounded above and `N^•` bounded, having replaced
`|n| ≫ 0` by unnamed bounds; the truncations vanish below `a` and above `b` exactly as in the
first two clauses, so that sharper conclusion is recorded, and it implies the source's by taking
for `a`, `b` the bounds provided by `H^n(gr(K^•)) = 0` for `|n| ≫ 0`. The third clause is not the
conjunction of the first two: it asserts in addition that the two replacements fit in a square.

## References

* [Stacks, Tag 05S1](https://stacks.math.columbia.edu/tag/05S1)
* [Stacks, Tag 05S3](https://stacks.math.columbia.edu/tag/05S3)
* [Stacks, Tag 05S5](https://stacks.math.columbia.edu/tag/05S5)
* [Stacks, Tag 05TQ](https://stacks.math.columbia.edu/tag/05TQ)
* [Stacks, Tag 05TT](https://stacks.math.columbia.edu/tag/05TT)
* [Stacks, Tag 05TR](https://stacks.math.columbia.edu/tag/05TR)
* [Stacks, Tag 05TU](https://stacks.math.columbia.edu/tag/05TU)
* [Stacks, Tag 05TV](https://stacks.math.columbia.edu/tag/05TV)
* [Stacks, Tag 05TX](https://stacks.math.columbia.edu/tag/05TX)
* [Stacks, Tag 05TY](https://stacks.math.columbia.edu/tag/05TY)
* [Stacks, Tag 015P](https://stacks.math.columbia.edu/tag/015P)
* [Stacks, Tag 05RY](https://stacks.math.columbia.edu/tag/05RY)
* [Stacks, Tag 05R7](https://stacks.math.columbia.edu/tag/05R7)
* [Stacks, Tag 05QH](https://stacks.math.columbia.edu/tag/05QH)
* [Stacks, Tag 0127](https://stacks.math.columbia.edu/tag/0127)
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section Filtration

/-- The `p`-th step of the filtration of a filtered cochain complex. -/
abbrev fil (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p : ℤ) : CochainComplex 𝒜 ℤ :=
  X.filtration.obj (op p)

/-- The inclusion `F^{p + 1} X^• ⟶ F^p X^•`, whose cokernel is `gr^p X^•`. -/
private abbrev filIncl (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p : ℤ) :
    fil X (p + 1) ⟶ fil X p :=
  X.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op

/-- If the filtration of `X^•` vanishes in degree `n` at some step, it vanishes in degree `n` at
every later step. -/
lemma isZero_fil_X_of_le (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) {p q n : ℤ}
    (hpq : p ≤ q) (hp : IsZero ((fil X p).X n)) : IsZero ((fil X q).X n) :=
  IsZero.of_mono ((X.filtration.diagram.map (homOfLE hpq : p ⟶ q).op).f n) hp

/-- If the filtration of `X^•` exhausts `X^n` at some step, it exhausts `X^n` at every earlier
step. -/
lemma isIso_ι_f_of_le (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) {p q n : ℤ}
    (hpq : p ≤ q) (hq : IsIso ((X.filtration.ι.app (op q)).f n)) :
    IsIso ((X.filtration.ι.app (op p)).f n) := by
  have hfac : X.filtration.diagram.map (homOfLE hpq : p ⟶ q).op ≫ X.filtration.ι.app (op p) =
      X.filtration.ι.app (op q) := X.filtration.diagram_map_comp_ι_app _
  have : Mono ((X.filtration.ι.app (op p)).f n) := inferInstance
  have : Epi ((X.filtration.ι.app (op p)).f n) :=
    epi_of_epi_fac (f := (X.filtration.diagram.map (homOfLE hpq : p ⟶ q).op).f n)
      (by rw [← HomologicalComplex.comp_f, hfac])
  exact isIso_of_mono_of_epi _

/-- The short exact sequence `0 ⟶ F^{p + 1} X^• ⟶ F^p X^• ⟶ gr^p X^• ⟶ 0`. -/
private lemma shortExact_filIncl (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p : ℤ) :
    (ShortComplex.mk (filIncl X p) (cokernel.π (filIncl X p)) (cokernel.condition _)).ShortExact
    where
  mono_f := inferInstance
  epi_g := inferInstance
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/-- The filtration steps of a filtered complex with degreewise finite filtration vanish in each
degree at a late enough step. -/
private lemma exists_isZero_fil_X (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hX : X.filtration.IsDegreewiseFinite) (n : ℤ) : ∃ q : ℤ, IsZero ((fil X q).X n) := by
  obtain ⟨-, q, -, hq⟩ := hX n
  exact ⟨q, hq⟩

end Filtration

section Degreewise

variable {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex 𝒜 c} (φ : K ⟶ L) (i : ι)

/-- A morphism of complexes which is invertible in the degrees `c.prev i`, `i` and `c.next i`
induces an isomorphism of the short complexes computing the homology in degree `i`. -/
private lemma isIso_shortComplexFunctor_map (h₀ : IsIso (φ.f (c.prev i))) (h₁ : IsIso (φ.f i))
    (h₂ : IsIso (φ.f (c.next i))) : IsIso ((shortComplexFunctor 𝒜 c i).map φ) := by
  have : IsIso ((shortComplexFunctor 𝒜 c i).map φ).τ₁ := h₀
  have : IsIso ((shortComplexFunctor 𝒜 c i).map φ).τ₂ := h₁
  have : IsIso ((shortComplexFunctor 𝒜 c i).map φ).τ₃ := h₂
  exact ShortComplex.isIso_of_isIso _

/-- A morphism of complexes which is invertible in the degrees `c.prev i`, `i` and `c.next i`
induces an isomorphism on the opcycles in degree `i`. -/
private lemma isIso_opcyclesMap (h₀ : IsIso (φ.f (c.prev i))) (h₁ : IsIso (φ.f i))
    (h₂ : IsIso (φ.f (c.next i))) : IsIso (opcyclesMap φ i) :=
  have := isIso_shortComplexFunctor_map φ i h₀ h₁ h₂
  inferInstanceAs (IsIso (ShortComplex.opcyclesMap ((shortComplexFunctor 𝒜 c i).map φ)))

/-- **The four lemma for opcycles.** If `φ` is injective on the homology in degree `i` and on
the terms in the next degree, then it is injective on the opcycles in degree `i`. This is the
step which turns the vanishing of the homology of the graded pieces into the strictness of the
differentials of Homology, Lemma 05QH(4): applied to the inclusion of a step of a filtration it
says that `Coim(d^{i - 1}) = Im(d^{i - 1})` there. -/
private lemma mono_opcyclesMap_of_mono_homologyMap {j : ι} (hij : c.next i = j)
    (h₁ : Mono (homologyMap φ i)) (h₂ : Mono (φ.f j)) : Mono (opcyclesMap φ i) := by
  let S₁ : ShortComplex 𝒜 :=
    ShortComplex.mk (K.homologyι i) (K.fromOpcycles i j) (K.homologyι_comp_fromOpcycles i j)
  let S₂ : ShortComplex 𝒜 :=
    ShortComplex.mk (L.homologyι i) (L.fromOpcycles i j) (L.homologyι_comp_fromOpcycles i j)
  let ψ : S₁ ⟶ S₂ :=
    { τ₁ := homologyMap φ i
      τ₂ := opcyclesMap φ i
      τ₃ := φ.f j
      comm₁₂ := homologyι_naturality φ i
      comm₂₃ := by simp [S₁, S₂, ← cancel_epi (K.pOpcycles i)] }
  have hex : S₁.Exact := ShortComplex.exact_of_f_is_kernel _ (K.homologyIsKernel i j hij)
  have : Mono S₁.f := inferInstanceAs (Mono (K.homologyι i))
  have : Mono S₂.f := inferInstanceAs (Mono (L.homologyι i))
  have : Mono ψ.τ₁ := h₁
  have : Mono ψ.τ₃ := h₂
  exact ShortComplex.mono_τ₂_of_exact_of_mono ψ hex

end Degreewise

/-- A morphism of cochain complexes which is invertible in the degrees `n - 1`, `n` and `n + 1`
induces an isomorphism on the homology in degree `n`. -/
private lemma isIso_homologyMap_of_isIso_f {K L : CochainComplex 𝒜 ℤ} (φ : K ⟶ L) (n : ℤ)
    (h₀ : IsIso (φ.f (n - 1))) (h₁ : IsIso (φ.f n)) (h₂ : IsIso (φ.f (n + 1))) :
    IsIso (homologyMap φ n) :=
  have := isIso_shortComplexFunctor_map φ n
    (by rwa [show (ComplexShape.up ℤ).prev n = n - 1 by simp]) h₁
    (by rwa [show (ComplexShape.up ℤ).next n = n + 1 by simp])
  inferInstanceAs (IsIso (ShortComplex.homologyMap ((shortComplexFunctor 𝒜 (.up ℤ) n).map φ)))

section MappingCone

open CochainComplex

/-- **The biproduct of two short exact sequences is short exact.** The identity of the biproduct
splits as the sum of the two idempotents cutting out the summands, and homology is an additive
functor, so the identity of the homology of the biproduct is a sum of two morphisms factoring
through objects that vanish. -/
private lemma shortExact_biprod {S T : ShortComplex 𝒜} (hS : S.ShortExact) (hT : T.ShortExact)
    (w : biprod.map S.f T.f ≫ biprod.map S.g T.g = 0) :
    (ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g) w).ShortExact := by
  have := hS.mono_f; have := hT.mono_f; have := hS.epi_g; have := hT.epi_g
  refine { mono_f := biprod.map_mono _ _, epi_g := biprod.map_epi _ _, exact := ?_ }
  let U : ShortComplex 𝒜 := ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g) w
  let pS : U ⟶ S := ShortComplex.Hom.mk biprod.fst biprod.fst biprod.fst (by simp [U]) (by simp [U])
  let iS : S ⟶ U := ShortComplex.Hom.mk biprod.inl biprod.inl biprod.inl (by simp [U]) (by simp [U])
  let pT : U ⟶ T := ShortComplex.Hom.mk biprod.snd biprod.snd biprod.snd (by simp [U]) (by simp [U])
  let iT : T ⟶ U := ShortComplex.Hom.mk biprod.inr biprod.inr biprod.inr (by simp [U]) (by simp [U])
  have hid : 𝟙 U = pS ≫ iS + pT ≫ iT := by
    refine ShortComplex.hom_ext _ _ ?_ ?_ ?_ <;> exact biprod.total.symm
  have hSz : IsZero S.homology := (S.exact_iff_isZero_homology).1 hS.exact
  have hTz : IsZero T.homology := (T.exact_iff_isZero_homology).1 hT.exact
  change U.Exact
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero,
    ← ShortComplex.homologyMap_id, hid, ShortComplex.homologyMap_add,
    ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp,
    hSz.eq_zero_of_tgt (ShortComplex.homologyMap pS),
    hTz.eq_zero_of_tgt (ShortComplex.homologyMap pT)]
  simp

/-- The degreewise biproduct decomposition `C(φ)^i ≅ K^{i + 1} ⊞ L^i` of the mapping cone of
`φ : K^• ⟶ L^•`: `Mathlib`'s `HomologicalComplex.homotopyCofiber.XIsoBiprod`, of which
`CochainComplex.mappingCone` is a special case, with its source read as `(mappingCone φ).X i`. -/
private noncomputable abbrev mappingConeXIsoBiprod {F G : CochainComplex 𝒜 ℤ} (φ : F ⟶ G)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) : (mappingCone φ).X i ≅ F.X j ⊞ G.X i :=
  homotopyCofiber.XIsoBiprod φ i j hij

/-- The left inclusion of the mapping cone is the first inclusion of the biproduct. -/
@[reassoc (attr := simp)]
private lemma inl_v_comp_mappingConeXIsoBiprod_hom {F G : CochainComplex 𝒜 ℤ} (φ : F ⟶ G)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (h : j + (-1) = i) :
    (mappingCone.inl φ).v j i h ≫ (mappingConeXIsoBiprod φ i j hij).hom = biprod.inl :=
  homotopyCofiber.inlX_XIsoBiprod_hom φ j i hij

/-- The right inclusion of the mapping cone is the second inclusion of the biproduct. -/
@[reassoc (attr := simp)]
private lemma inr_f_comp_mappingConeXIsoBiprod_hom {F G : CochainComplex 𝒜 ℤ} (φ : F ⟶ G)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (mappingCone.inr φ).f i ≫ (mappingConeXIsoBiprod φ i j hij).hom = biprod.inr :=
  homotopyCofiber.inrX_XIsoBiprod_hom φ j i hij

/-- In degree `i`, the morphism of mapping cones induced by a commutative square is the
biproduct of the two morphisms of the square, in the degrees `i + 1` and `i`, read through the
canonical isomorphism `C(φ)^i ≅ K^{i + 1} ⊞ L^i` of `HomologicalComplex.homotopyCofiber`. -/
private lemma mappingCone_map_f_comp_XIsoBiprod_hom {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ}
    {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (comm : φ₁ ≫ b = a ≫ φ₂)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (mappingCone.map φ₁ φ₂ a b comm).f i ≫ (mappingConeXIsoBiprod φ₂ i j hij).hom
      = (mappingConeXIsoBiprod φ₁ i j hij).hom ≫ biprod.map (a.f j) (b.f i) := by
  rw [mappingCone.ext_from_iff φ₁ j i hij]
  constructor <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp [mappingCone.map]

/-- The morphism of mapping cones induced by a commutative square whose two horizontal sides
vanish is zero. The vanishing is a hypothesis rather than built into the statement because the
argument `comm` of `mappingCone.map` depends on those two sides. -/
private lemma mappingCone_map_eq_zero {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ} {φ₁ : K₁ ⟶ L₁}
    {φ₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (comm : φ₁ ≫ b = a ≫ φ₂)
    (ha : a = 0) (hb : b = 0) : mappingCone.map φ₁ φ₂ a b comm = 0 := by
  subst ha hb
  ext n
  simp [mappingCone.ext_from_iff _ (n + 1) n rfl, mappingCone.map]

/-- **Mapping cones of a short exact sequence of arrows.** If `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` and
`0 ⟶ L₁ ⟶ L₂ ⟶ L₃ ⟶ 0` are short exact sequences of cochain complexes and the squares
`comm`, `comm'` commute, then the induced sequence of mapping cones is short exact: in each
degree it is the biproduct of the two given sequences shifted by one, and a biproduct of short
exact sequences is short exact. -/
@[sga "4 XVII 5.5.25.2" "more general"]
private lemma shortExact_mappingCone_map {K₁ K₂ K₃ L₁ L₂ L₃ : CochainComplex 𝒜 ℤ}
    {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} {φ₃ : K₃ ⟶ L₃} {a : K₁ ⟶ K₂} {a' : K₂ ⟶ K₃}
    {b : L₁ ⟶ L₂} {b' : L₂ ⟶ L₃} {ha : a ≫ a' = 0} {hb : b ≫ b' = 0}
    (comm : φ₁ ≫ b = a ≫ φ₂) (comm' : φ₂ ≫ b' = a' ≫ φ₃)
    (hK : (ShortComplex.mk a a' ha).ShortExact) (hL : (ShortComplex.mk b b' hb).ShortExact)
    (hz : mappingCone.map φ₁ φ₂ a b comm ≫ mappingCone.map φ₂ φ₃ a' b' comm' = 0) :
    (ShortComplex.mk (mappingCone.map φ₁ φ₂ a b comm)
      (mappingCone.map φ₂ φ₃ a' b' comm') hz).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have hKi := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hK (i + 1)
  have hLi := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hL i
  have hai : ∀ m : ℤ, a.f m ≫ a'.f m = 0 := fun m => by
    rw [← HomologicalComplex.comp_f, ha]; simp
  have hbi : ∀ m : ℤ, b.f m ≫ b'.f m = 0 := fun m => by
    rw [← HomologicalComplex.comp_f, hb]; simp
  have hB := shortExact_biprod hKi hLi (by
    simp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map]
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp only [biprod.inl_map_assoc, biprod.inl_map]
      rw [← Category.assoc, hai, zero_comp, comp_zero]
    · simp only [biprod.inr_map_assoc, biprod.inr_map]
      rw [← Category.assoc, hbi, zero_comp, comp_zero])
  exact (ShortComplex.shortExact_iff_of_iso (ShortComplex.isoMk
    (mappingConeXIsoBiprod φ₁ i (i + 1) rfl) (mappingConeXIsoBiprod φ₂ i (i + 1) rfl)
    (mappingConeXIsoBiprod φ₃ i (i + 1) rfl)
    (mappingCone_map_f_comp_XIsoBiprod_hom comm i (i + 1) rfl).symm
    (mappingCone_map_f_comp_XIsoBiprod_hom comm' i (i + 1) rfl).symm)).2 hB

/-- A morphism of mapping cones is an isomorphism in degree `i` as soon as the two morphisms it
comes from are isomorphisms in the degrees `i + 1` and `i`. -/
private lemma isIso_mappingCone_map_f {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ} {φ₁ : K₁ ⟶ L₁}
    {φ₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (comm : φ₁ ≫ b = a ≫ φ₂) (i : ℤ)
    (ha : IsIso (a.f (i + 1))) (hb : IsIso (b.f i)) :
    IsIso ((mappingCone.map φ₁ φ₂ a b comm).f i) := by
  have h : (mappingCone.map φ₁ φ₂ a b comm).f i =
      ((mappingConeXIsoBiprod φ₁ i (i + 1) rfl).hom ≫ biprod.map (a.f (i + 1)) (b.f i)) ≫
        (mappingConeXIsoBiprod φ₂ i (i + 1) rfl).inv :=
    (Iso.eq_comp_inv _).2 (mappingCone_map_f_comp_XIsoBiprod_hom comm i (i + 1) rfl)
  rw [h]
  have : IsIso (biprod.map (a.f (i + 1)) (b.f i)) :=
    (biprod.mapIso (asIso (a.f (i + 1))) (asIso (b.f i))).isIso_hom
  infer_instance

/-- A morphism of cochain complexes is a quasi-isomorphism precisely when its mapping cone is
acyclic. The cone sits in a distinguished triangle of `K(𝒜)` whose first morphism it is, and the
quasi-isomorphisms of `K(𝒜)` are the class attached to the acyclic complexes. -/
@[sga "6 I 1.4.2" "All-degree case"]
private lemma quasiIso_iff_exactAt_mappingCone {X Y : CochainComplex 𝒜 ℤ} (f : X ⟶ Y) :
    QuasiIso f ↔ ∀ n : ℤ, (mappingCone f).ExactAt n := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt _)

/-- The mapping cone of a quasi-isomorphism is acyclic. -/
private lemma isZero_homology_mappingCone_of_quasiIso {X Y : CochainComplex 𝒜 ℤ} (f : X ⟶ Y)
    (hf : QuasiIso f) (n : ℤ) : IsZero ((mappingCone f).homology n) :=
  ((mappingCone f).exactAt_iff_isZero_homology n).1 ((quasiIso_iff_exactAt_mappingCone f).1 hf n)

/-- A morphism of cochain complexes whose mapping cone has vanishing homology is a
quasi-isomorphism. -/
private lemma quasiIso_of_isZero_homology_mappingCone {X Y : CochainComplex 𝒜 ℤ} (f : X ⟶ Y)
    (h : ∀ n : ℤ, IsZero ((mappingCone f).homology n)) : QuasiIso f :=
  (quasiIso_iff_exactAt_mappingCone f).2 fun n =>
    ((mappingCone f).exactAt_iff_isZero_homology n).2 (h n)

/-- **Homology, Lemma 05QH, descending induction.** Let `M` be a tower of cochain complexes with
short exact sequences `0 ⟶ M_{p + 1} ⟶ M_p ⟶ N_p ⟶ 0`, and let `n` be a degree in which every
`N_p` has vanishing homology. If `H^n(M_q) = 0` then `H^n(M_p) = 0` for every `p ≤ q`. -/
private lemma isZero_homology_of_tower {M N : ℤ → CochainComplex 𝒜 ℤ}
    {u : ∀ p : ℤ, M (p + 1) ⟶ M p} {v : ∀ p : ℤ, M p ⟶ N p} {w : ∀ p : ℤ, u p ≫ v p = 0}
    (hSE : ∀ p : ℤ, (ShortComplex.mk (u p) (v p) (w p)).ShortExact)
    {n : ℤ} (hN : ∀ p : ℤ, IsZero ((N p).homology n)) {q : ℤ}
    (hq : IsZero ((M q).homology n)) :
    ∀ p ≤ q, IsZero ((M p).homology n) := by
  refine Int.leInductionDown hq fun r _ hr => ?_
  exact ((hSE (r - 1)).homology_exact₂ n).isZero_of_both_isZero (by simpa using hr) (hN _)

/-- **The tower of mapping cones.** Let `α : K^• ⟶ L^•` be a filtered quasi-isomorphism whose two
filtrations vanish in each degree at a late enough step. Then the mapping cone of every step
`F^p α : F^p K^• ⟶ F^p L^•` is acyclic. The cones `C(F^p α)` form a tower whose graded pieces are
the cones `C(gr^p α)`, acyclic because `α` is a filtered quasi-isomorphism; at a step `q ≥ p` with
`F^q L^n = 0` and `F^q K^{n + 1} = 0` the cone `C(F^q α)` vanishes in degree `n`, and the
descending induction of [Stacks, Tag 05QH] carries the vanishing of `H^n` from `q` down to `p`. -/
private lemma isZero_homology_mappingCone_natTrans_app
    {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (hα : CochainComplex.filteredQuasiIso 𝒜 α)
    (hK : ∀ n : ℤ, ∃ q : ℤ, IsZero ((fil K q).X n))
    (hL : ∀ n : ℤ, ∃ q : ℤ, IsZero ((fil L q).X n))
    (p n : ℤ) : IsZero ((mappingCone (α.natTrans.app (op p))).homology n) := by
  -- the tower `C(α_r)` of mapping cones and its graded pieces `C(gr^r α)`
  let M : ℤ → CochainComplex 𝒜 ℤ := fun r => mappingCone (α.natTrans.app (op r))
  let N : ℤ → CochainComplex 𝒜 ℤ :=
    fun r => mappingCone ((FilteredObject.gr r).map α)
  have commIncl : ∀ r : ℤ, α.natTrans.app (op (r + 1)) ≫ filIncl L r =
      filIncl K r ≫ α.natTrans.app (op r) := fun r =>
    (α.natTrans.naturality (homOfLE (Int.le_add_one le_rfl) : (r : ℤ) ⟶ r + 1).op).symm
  have commπ : ∀ r : ℤ, α.natTrans.app (op r) ≫ cokernel.π (filIncl L r) =
      cokernel.π (filIncl K r) ≫
        (FilteredObject.gr r).map α := fun r =>
    (cokernel.π_desc _ _ _).symm
  let u : ∀ r : ℤ, M (r + 1) ⟶ M r := fun r =>
    mappingCone.map _ _ (filIncl K r) (filIncl L r) (commIncl r)
  let v : ∀ r : ℤ, M r ⟶ N r := fun r =>
    mappingCone.map _ _ (cokernel.π (filIncl K r)) (cokernel.π (filIncl L r)) (commπ r)
  have w : ∀ r : ℤ, u r ≫ v r = 0 := by
    intro r
    have h := mappingCone.map_comp (α.natTrans.app (op (r + 1))) (α.natTrans.app (op r))
      ((FilteredObject.gr r).map α) (filIncl K r) (filIncl L r)
      (commIncl r) (cokernel.π (filIncl K r)) (cokernel.π (filIncl L r)) (commπ r)
    rw [← h]
    exact mappingCone_map_eq_zero _ (cokernel.condition _) (cokernel.condition _)
  have hSE : ∀ r : ℤ, (ShortComplex.mk (u r) (v r) (w r)).ShortExact := fun r =>
    shortExact_mappingCone_map _ _ (shortExact_filIncl K r) (shortExact_filIncl L r) (w r)
  -- the base of the induction: `C(α_q)` vanishes in degree `n` at a step `q ≥ p` where the
  -- filtration of `L^•` vanishes in degree `n` and that of `K^•` in degree `n + 1`
  obtain ⟨qK, hqK⟩ := hK (n + 1)
  obtain ⟨qL, hqL⟩ := hL n
  set q : ℤ := max (max qK qL) p with hqdef
  have hbase : IsZero ((M q).homology n) := by
    have hX : IsZero ((M q).X n) := by
      refine HomologicalComplex.homotopyCofiber.isZero_X (α.natTrans.app (op q)) n ?_ ?_
      · exact isZero_fil_X_of_le L (by omega) hqL
      · intro j hj
        obtain rfl : j = n + 1 := hj.symm
        exact isZero_fil_X_of_le K (by omega) hqK
    exact ((M q).exactAt_iff_isZero_homology n).1 (ExactAt.of_isZero hX)
  exact isZero_homology_of_tower hSE
    (fun r => isZero_homology_mappingCone_of_quasiIso _ (hα r) n) hbase p (by omega)

/-- The mapping cone of a filtered quasi-isomorphism between complexes of finitely filtered
objects is acyclic. This is the content of [Stacks, Tag 05S3] for `(forget F)`. -/
private lemma isZero_homology_mappingCone
    {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (hα : CochainComplex.filteredQuasiIso 𝒜 α)
    (hK : K.filtration.IsDegreewiseFinite)
    (hL : L.filtration.IsDegreewiseFinite)
    (n : ℤ) : IsZero ((mappingCone α.hom).homology n) := by
  -- the degrees `n - 1, n, n + 1, n + 2` are the only ones homology in degree `n` sees, so
  -- finitely many bounds suffice: `p₀` is a step where both filtrations exhaust in all four
  obtain ⟨pK₀, -, hpK₀, -⟩ := hK n
  obtain ⟨pK₁, -, hpK₁, -⟩ := hK (n + 1)
  obtain ⟨pK₂, -, hpK₂, -⟩ := hK (n + 2)
  obtain ⟨pKm, -, hpKm, -⟩ := hK (n - 1)
  obtain ⟨pL₀, -, hpL₀, -⟩ := hL n
  obtain ⟨pL₁, -, hpL₁, -⟩ := hL (n + 1)
  obtain ⟨pLm, -, hpLm, -⟩ := hL (n - 1)
  set p₀ : ℤ := min (min (min pK₀ pK₁) (min pK₂ pKm)) (min (min pL₀ pL₁) pLm) with hp₀def
  -- the shift of degree is performed here rather than inside `isIso_ι_f_of_le` below, where the
  -- step of the filtration is still an unassigned metavariable
  have hpK₀' : IsIso ((K.filtration.ι.app (op pK₀)).f (n - 1 + 1)) := by
    rw [show n - 1 + 1 = n from by omega]; exact hpK₀
  have hpK₂' : IsIso ((K.filtration.ι.app (op pK₂)).f (n + 1 + 1)) := by
    rw [show n + 1 + 1 = n + 2 from by omega]; exact hpK₂
  -- the tower at `p₀`, and the comparison of `C(α_{p₀})` with `C(α)`
  have hp₀ : IsZero ((mappingCone (α.natTrans.app (op p₀))).homology n) :=
    isZero_homology_mappingCone_natTrans_app α hα (exists_isZero_fil_X K hK)
      (exists_isZero_fil_X L hL) p₀ n
  set w₀ := mappingCone.map (α.natTrans.app (op p₀)) α.hom (K.filtration.ι.app (op p₀))
    (L.filtration.ι.app (op p₀)) (α.comm (op p₀))
  have : IsIso (HomologicalComplex.homologyMap w₀ n) :=
    isIso_homologyMap_of_isIso_f _ n
      (isIso_mappingCone_map_f _ _
        (isIso_ι_f_of_le K (by omega) hpK₀') (isIso_ι_f_of_le L (by omega) hpLm))
      (isIso_mappingCone_map_f _ _
        (isIso_ι_f_of_le K (by omega) hpK₁) (isIso_ι_f_of_le L (by omega) hpL₀))
      (isIso_mappingCone_map_f _ _
        (isIso_ι_f_of_le K (by omega) hpK₂') (isIso_ι_f_of_le L (by omega) hpL₁))
  exact IsZero.of_iso hp₀ (asIso (HomologicalComplex.homologyMap w₀ n)).symm

namespace CochainComplex

/-- **The functors `gr^p` and `(forget F)`, followed by `Q`, invert filtered
quasi-isomorphisms.** Let `𝒜` be an abelian category and let `α : K^• ⟶ L^•` be a filtered
quasi-isomorphism of filtered cochain complexes of `𝒜`. Then, for every `p`, the localisation
functor `Q : CochainComplex 𝒜 ℤ ⥤ D(𝒜)` inverts `gr^p(α)`; and if moreover the filtrations of
`K^•` and of `L^•` are finite in each degree — `F^p K^n = K^n` for some `p` and `F^q K^n = 0` for
some `q`, for each `n`, i.e. `K^•` and `L^•` are complexes of finitely filtered objects — then
`Q` inverts the underlying morphism of complexes `(forget F)(α)` as well. This is the input to the
universal property of localisation in the proof of [Stacks, Tag 05S3]; the exact functors
`gr^p, (forget F) : DF(𝒜) ⥤ D(𝒜)` and `gr : DF(𝒜) ⥤ D(Gr(𝒜))` it produces, and their
commutation with the localisation functors, are
`CochainComplex.FilteredDerivedCategory.isTriangulated_grDF_forgetDF_grGradedDF`. -/
@[sga "4 Vbis 2.5.2" "more general"]
public theorem isIso_Q_map_gradedPiece_and_forget_of_filteredQuasiIso {A : Type u}
    [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {K L : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (hα : CochainComplex.filteredQuasiIso A α) :
    (∀ p : ℤ, IsIso (DerivedCategory.Q.map
        ((FilteredObject.gr p).map α))) ∧
      ((∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
          IsZero ((K.filtration.obj (op q)).X n)) →
        (∀ n : ℤ, ∃ p q : ℤ, IsIso ((L.filtration.ι.app (op p)).f n) ∧
          IsZero ((L.filtration.obj (op q)).X n)) →
        IsIso (DerivedCategory.Q.map (FilteredObject.forget.map α))) := by
  refine ⟨fun p => (DerivedCategory.isIso_Q_map_iff_quasiIso _
      ((FilteredObject.gr p).map α)).2 (hα p), fun hK hL => ?_⟩
  refine (DerivedCategory.isIso_Q_map_iff_quasiIso _ (FilteredObject.forget.map α)).2 ?_
  exact quasiIso_of_isZero_homology_mappingCone α.hom (isZero_homology_mappingCone α hα hK hL)

/-- **A morphism of filtered complexes which is a quasi-isomorphism on every graded piece is a
quasi-isomorphism**, provided both filtrations are finite in each degree. This is the step of the
proof of [Stacks, Tag 05S3] showing that `(forget F)` descends to `DF(𝒜)`, read as a statement
about the morphism of complexes rather than about its image in the derived category, which is the
form the proofs of [Stacks, Tag 07LD] and
[Stacks, Tag 0FKH] use when they conclude from the graded pieces. Unlike
`CochainComplex.isIso_Q_map_gradedPiece_and_forget_of_filteredQuasiIso` it asks for no
`HasDerivedCategory` instance: the mapping cone of `α.hom` is acyclic outright.

Finiteness cannot be dropped: for the constant filtration `F^p K^• = K^•` every graded piece
vanishes, so `0 ⟶ K^•` is a filtered quasi-isomorphism whose underlying morphism is not a
quasi-isomorphism unless `K^•` is acyclic. -/
@[sga "4 Vbis 2.5.2" "more general"]
public theorem quasiIso_hom_of_filteredQuasiIso
    {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (hα : CochainComplex.filteredQuasiIso 𝒜 α)
    (hK : K.filtration.IsDegreewiseFinite) (hL : L.filtration.IsDegreewiseFinite) :
    QuasiIso α.hom :=
  quasiIso_of_isZero_homology_mappingCone α.hom (isZero_homology_mappingCone α hα hK hL)

/-- Every step `F^p α : F^p K^• ⟶ F^p L^•` of a filtered quasi-isomorphism `α : K^• ⟶ L^•` of
filtered cochain complexes with degreewise finite filtrations is a quasi-isomorphism; of the
finiteness only the vanishing of `F^q K^n` and of `F^q L^n` for `q ≫ 0` is used. The cones
`C(F^p α)` form a tower whose graded pieces `C(gr^p α)` are acyclic and which vanishes in a fixed
degree at a late enough step, so the descending induction of [Stacks, Tag 05QH] reaches every `p`;
the second clause of [Stacks, Tag 05S3], about `(forget F)(α)`, compares this with a step
exhausting in the degrees the homology sees. Support for [Stacks, Tag 05TW] and
[Stacks, Tag 05S6], where the total complex of a resolution system, resp. a bounded above
truncation, is shown to be a filtered quasi-isomorphism step by step. -/
public theorem quasiIso_natTrans_app_of_filteredQuasiIso
    {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (hα : CochainComplex.filteredQuasiIso 𝒜 α)
    (hK : K.filtration.IsDegreewiseFinite) (hL : L.filtration.IsDegreewiseFinite)
    (p : ℤᵒᵖ) : QuasiIso (α.natTrans.app p) :=
  quasiIso_of_isZero_homology_mappingCone _
    (isZero_homology_mappingCone_natTrans_app α hα (exists_isZero_fil_X K hK)
      (exists_isZero_fil_X L hL) p.unop)

end CochainComplex

end MappingCone

section Tower

/-- Being cohomologically `≥ a` is invariant under quasi-isomorphism. -/
private lemma isGE_of_quasiIso {Z W : CochainComplex 𝒜 ℤ} (φ : Z ⟶ W) [QuasiIso φ] (a : ℤ)
    [W.IsGE a] : Z.IsGE a :=
  (HomologicalComplex.isSupported_iff_of_quasiIso φ _).2 ‹W.IsGE a›

/-- **The tower.** If all the graded pieces of a filtered complex with degreewise finite
filtration are exact in degree `n`, then so is every step of its filtration. This is the form
taken here by the descending induction of Homology, Lemma 05QH. -/
private lemma exactAt_fil (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hX : ∀ n : ℤ, ∃ q : ℤ, IsZero ((fil X q).X n)) (n : ℤ)
    (h : ∀ p : ℤ, ((FilteredObject.gr p).obj X).ExactAt n)
    (p : ℤ) : (fil X p).ExactAt n := by
  obtain ⟨q, hq⟩ := hX n
  by_cases hpq : q ≤ p
  · exact ExactAt.of_isZero (isZero_fil_X_of_le X hpq hq)
  · have key : ∀ r ≤ q, (fil X r).ExactAt n := by
      refine Int.leInductionDown (ExactAt.of_isZero hq) ?_
      intro r _ hr
      refine (shortExact_filIncl X (r - 1)).exactAt_X₂ n ?_ (h (r - 1))
      simpa using hr
    exact key p (by omega)

/-- If all the graded pieces of a filtered complex with degreewise finite filtration are
cohomologically `≥ a`, then so is every step of its filtration. -/
private lemma isGE_fil (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hX : ∀ n : ℤ, ∃ q : ℤ, IsZero ((fil X q).X n)) (a : ℤ)
    (h : ∀ p : ℤ, ((FilteredObject.gr p).obj X).IsGE a)
    (p : ℤ) : (fil X p).IsGE a := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  refine exactAt_fil X hX i (fun r => ?_) p
  have := h r
  exact CochainComplex.exactAt_of_isGE _ a i hi

/-- If all the graded pieces of a filtered complex with degreewise finite filtration are
cohomologically `≤ b`, then so is every step of its filtration. -/
private lemma isLE_fil (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hX : ∀ n : ℤ, ∃ q : ℤ, IsZero ((fil X q).X n)) (b : ℤ)
    (h : ∀ p : ℤ, ((FilteredObject.gr p).obj X).IsLE b)
    (p : ℤ) : (fil X p).IsLE b := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  refine exactAt_fil X hX i (fun r => ?_) p
  have := h r
  exact CochainComplex.exactAt_of_isLE _ b i hi

end Tower

section Graded

/-- A morphism of filtered complexes each of whose components `F^p X^• ⟶ F^p Y^•` is a
quasi-isomorphism is a filtered quasi-isomorphism: `gr^p` of it is the third map of the morphism
of short exact sequences `0 ⟶ F^{p + 1} ⟶ F^p ⟶ gr^p ⟶ 0` it induces, whose first two maps are
quasi-isomorphisms. -/
public lemma filteredQuasiIso_of_natTrans {X Y : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (α : X ⟶ Y) (h : ∀ p : ℤ, QuasiIso (α.natTrans.app (op p))) :
    CochainComplex.filteredQuasiIso 𝒜 α := fun p =>
  HomologySequence.quasiIso_τ₃ (FilteredObject.stepShortComplexMap _ α)
    (FilteredObject.stepShortComplex_shortExact _ X)
    (FilteredObject.stepShortComplex_shortExact _ Y)
    (h (p + 1)) (h p)

end Graded

section Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {K L : HomologicalComplex 𝒜 c'} (φ : K ⟶ L) (e : c.Embedding c')

/-- The degreewise description of `truncGEMap` away from the boundary: the unprimed companion
of `HomologicalComplex.truncGE'Map_f_eq`. -/
private lemma truncGEMap_f_eq [e.IsTruncGE] {i : ι} (hi : ¬ e.BoundaryGE i) {i' : ι'}
    (h : e.f i = i') :
    (truncGEMap φ e).f i' =
      (K.truncGEXIso e h hi).hom ≫ φ.f i' ≫ (L.truncGEXIso e h hi).inv := by
  simp only [truncGEMap, truncGE, truncGEXIso, ComplexShape.Embedding.extendFunctor_map,
    extendMap_f _ _ h, truncGE'Map_f_eq _ _ hi h, Iso.trans_hom, Iso.trans_inv, Category.assoc]

/-- The degreewise description of `truncGEMap` at the boundary: the unprimed companion of
`HomologicalComplex.truncGE'Map_f_eq_opcyclesMap`. -/
private lemma truncGEMap_f_eq_opcyclesMap [e.IsTruncGE] {i : ι} (hi : e.BoundaryGE i) {i' : ι'}
    (h : e.f i = i') :
    (truncGEMap φ e).f i' =
      (K.truncGEXIsoOpcycles e h hi).hom ≫ opcyclesMap φ i' ≫
        (L.truncGEXIsoOpcycles e h hi).inv := by
  simp only [truncGEMap, truncGE, truncGEXIsoOpcycles, ComplexShape.Embedding.extendFunctor_map,
    extendMap_f _ _ h, truncGE'Map_f_eq_opcyclesMap _ _ hi h, Iso.trans_hom, Iso.trans_inv,
    Category.assoc]

/-- `τ_{≥ e}` preserves monomorphisms degreewise, given injectivity on the opcycles at the
boundary. -/
private lemma mono_truncGEMap_f [e.IsTruncGE] (i' : ι') (h₁ : Mono (φ.f i'))
    (h₂ : ∀ i, e.f i = i' → e.BoundaryGE i → Mono (opcyclesMap φ i')) :
    Mono ((truncGEMap φ e).f i') := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, h⟩ := hi'
    by_cases hb : e.BoundaryGE i
    · have := h₂ i h hb
      rw [truncGEMap_f_eq_opcyclesMap φ e hb h]
      infer_instance
    · rw [truncGEMap_f_eq φ e hb h]
      infer_instance
  · have hz := (K.truncGE e).isZero_X_of_isStrictlySupported e i' (by simpa using hi')
    exact ⟨fun g₁ g₂ _ => hz.eq_of_tgt g₁ g₂⟩

/-- `τ_{≥ e}` preserves degreewise isomorphisms, given invertibility on the opcycles at the
boundary. -/
private lemma isIso_truncGEMap_f [e.IsTruncGE] (i' : ι') (h₁ : IsIso (φ.f i'))
    (h₂ : IsIso (opcyclesMap φ i')) : IsIso ((truncGEMap φ e).f i') := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, h⟩ := hi'
    by_cases hb : e.BoundaryGE i
    · rw [truncGEMap_f_eq_opcyclesMap φ e hb h]
      infer_instance
    · rw [truncGEMap_f_eq φ e hb h]
      infer_instance
  · have hz := (K.truncGE e).isZero_X_of_isStrictlySupported e i' (by simpa using hi')
    have hz' := (L.truncGE e).isZero_X_of_isStrictlySupported e i' (by simpa using hi')
    exact ⟨0, hz.eq_of_src _ _, hz'.eq_of_src _ _⟩

/-- `τ_{≤ e}` turns a morphism which is invertible in the degrees `c'.prev i'`, `i'` and
`c'.next i'` into a morphism which is invertible in degree `i'`. Dual to
`isIso_truncGEMap_f`, deduced from it through `op` as Mathlib itself deduces the
`truncLE` API from the `truncGE` one. -/
private lemma isIso_truncLEMap_f_of_isIso [e.IsTruncLE] (i' : ι')
    (h₀ : IsIso (φ.f (c'.prev i'))) (h₁ : IsIso (φ.f i')) (h₂ : IsIso (φ.f (c'.next i'))) :
    IsIso ((truncLEMap φ e).f i') := by
  have e₁ : IsIso (((opFunctor 𝒜 c').map φ.op).f i') := inferInstanceAs (IsIso (φ.f i').op)
  have e₂ : IsIso (opcyclesMap ((opFunctor 𝒜 c').map φ.op) i') :=
    isIso_opcyclesMap _ i' (inferInstanceAs (IsIso (φ.f (c'.next i')).op))
      (inferInstanceAs (IsIso (φ.f i').op)) (inferInstanceAs (IsIso (φ.f (c'.prev i')).op))
  have := isIso_truncGEMap_f ((opFunctor 𝒜 c').map φ.op) e.op i' e₁ e₂
  exact inferInstanceAs (IsIso ((truncGEMap ((opFunctor 𝒜 c').map φ.op) e.op).f i').unop)

end Embedding

section Truncation

variable {X Y : CochainComplex 𝒜 ℤ}

/-- The inclusion `τ_{≤ b} Z^• ⟶ Z^•` is a degreewise monomorphism. -/
private lemma mono_ιTruncLE_f (Z : CochainComplex 𝒜 ℤ) (b n : ℤ) : Mono ((Z.ιTruncLE b).f n) := by
  dsimp [CochainComplex.ιTruncLE]; infer_instance

/-- The projection `Z^• ⟶ τ_{≥ a} Z^•` is a degreewise epimorphism. -/
private lemma epi_πTruncGE_f (Z : CochainComplex 𝒜 ℤ) (a n : ℤ) : Epi ((Z.πTruncGE a).f n) := by
  dsimp [CochainComplex.πTruncGE]; infer_instance

/-- `τ_{≤ b}` preserves monomorphisms. -/
private lemma mono_truncLEMap (φ : X ⟶ Y) [Mono φ] (b : ℤ) :
    Mono (CochainComplex.truncLEMap φ b) := by
  have : Mono (X.ιTruncLE b) := by dsimp [CochainComplex.ιTruncLE]; infer_instance
  have : Mono (X.ιTruncLE b ≫ φ) := mono_comp _ _
  exact mono_of_mono_fac (CochainComplex.ιTruncLE_naturality φ b)

/-- `τ_{≥ a}` preserves degreewise epimorphisms. -/
private lemma epi_truncGEMap_f (φ : X ⟶ Y) (a n : ℤ) (hφ : Epi (φ.f n)) :
    Epi ((CochainComplex.truncGEMap φ a).f n) := by
  have hfac : (X.πTruncGE a).f n ≫ (CochainComplex.truncGEMap φ a).f n =
      φ.f n ≫ (Y.πTruncGE a).f n := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
      CochainComplex.πTruncGE_naturality]
  have := epi_πTruncGE_f Y a n
  have : Epi (φ.f n ≫ (Y.πTruncGE a).f n) := epi_comp _ _
  exact epi_of_epi_fac hfac

/-- A degree in which `Z^•` vanishes is a degree in which `τ_{≥ a} Z^•` vanishes. -/
private lemma isZero_truncGE_X (Z : CochainComplex 𝒜 ℤ) (a n : ℤ) (h : IsZero (Z.X n)) :
    IsZero ((Z.truncGE a).X n) :=
  have := epi_πTruncGE_f Z a n
  IsZero.of_epi ((Z.πTruncGE a).f n) h

/-- A degree in which `Z^•` vanishes is a degree in which `τ_{≤ b} Z^•` vanishes. -/
public lemma isZero_truncLE_X (Z : CochainComplex 𝒜 ℤ) (b n : ℤ) (h : IsZero (Z.X n)) :
    IsZero ((Z.truncLE b).X n) :=
  have := mono_ιTruncLE_f Z b n
  IsZero.of_mono ((Z.ιTruncLE b).f n) h

/-- `τ_{≤ b}` turns a morphism which is invertible in the degrees `n - 1`, `n` and `n + 1` into
a morphism which is invertible in degree `n`. In the degrees `n < b` this is the identification
of `(τ_{≤ b} X^•)^n` with `X^n`, in the degree `n = b` the invertibility of
`Z^b(φ) : Z^b(X^•) ⟶ Z^b(Y^•)`, and in the degrees `n > b` it is a map of zero objects. -/
private lemma isIso_truncLEMap_f (φ : X ⟶ Y) (b n : ℤ) (h₀ : IsIso (φ.f (n - 1)))
    (h₁ : IsIso (φ.f n)) (h₂ : IsIso (φ.f (n + 1))) :
    IsIso ((CochainComplex.truncLEMap φ b).f n) := by
  refine isIso_truncLEMap_f_of_isIso φ (ComplexShape.embeddingUpIntLE b) n ?_ h₁ ?_
  · rw [show (ComplexShape.up ℤ).prev n = n - 1 by simp]
    exact h₀
  · rw [show (ComplexShape.up ℤ).next n = n + 1 by simp]
    exact h₂

/-- `τ_{≥ a}` preserves monomorphisms, given injectivity on the opcycles in degree `a`. -/
private lemma mono_truncGEMap (φ : X ⟶ Y) [Mono φ] (a : ℤ) (h : Mono (opcyclesMap φ a)) :
    Mono (CochainComplex.truncGEMap φ a) := by
  refine mono_of_mono_f _ fun n => mono_truncGEMap_f φ _ n inferInstance ?_
  intro i hfi hb
  rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff] at hb
  subst hb
  obtain rfl : n = a := by simpa using hfi.symm
  exact h

/-- `τ_{≥ a}` of a complex whose terms vanish in the degrees `> b` again has vanishing terms in
the degrees `> b`, since `Z^• ⟶ τ_{≥ a} Z^•` is a degreewise epimorphism. -/
private lemma isStrictlyLE_truncGE (Z : CochainComplex 𝒜 ℤ) (a b : ℤ) [Z.IsStrictlyLE b] :
    (Z.truncGE a).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact isZero_truncGE_X Z a i (Z.isZero_of_isStrictlyLE b i hi)

end Truncation

section TruncGE

variable (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (a : ℤ)

/-- The diagram `p ↦ τ_{≥ a} F^p X^•`. -/
public noncomputable def truncGEDiagram : ℤᵒᵖ ⥤ CochainComplex 𝒜 ℤ where
  obj p := (X.filtration.obj p).truncGE a
  map f := CochainComplex.truncGEMap (X.filtration.diagram.map f) a
  map_id p := by simp [CochainComplex.truncGEMap]
  map_comp f g := by simp [CochainComplex.truncGEMap, ← HomologicalComplex.truncGEMap_comp]

/-- The transformation `τ_{≥ a} F^p X^• ⟶ τ_{≥ a} X^•`. -/
public noncomputable def truncGEι :
    truncGEDiagram X a ⟶ (Functor.const ℤᵒᵖ).obj (X.X.truncGE a) where
  app p := CochainComplex.truncGEMap (X.filtration.ι.app p) a
  naturality p q f := by
    dsimp [truncGEDiagram, CochainComplex.truncGEMap]
    rw [← HomologicalComplex.truncGEMap_comp]
    simp

/-- `τ_{≥ a} X^•`, filtered by the truncations `τ_{≥ a} F^p X^•` of the steps of the filtration
of `X^•`. This is the complex `L^•` of part (1). -/
public noncomputable def filteredTruncGE
    (hm : ∀ p : ℤᵒᵖ, Mono (CochainComplex.truncGEMap (X.filtration.ι.app p) a)) :
    FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ where
  X := X.X.truncGE a
  filtration :=
    haveI : ∀ p : ℤᵒᵖ, Mono ((truncGEι X a).app p) := hm
    Filtration.ofDiagram (truncGEDiagram X a) (truncGEι X a)

/-- The canonical morphism `X^• ⟶ τ_{≥ a} X^•` of filtered complexes. -/
public noncomputable def πFilteredTruncGE
    (hm : ∀ p : ℤᵒᵖ, Mono (CochainComplex.truncGEMap (X.filtration.ι.app p) a)) :
    X ⟶ filteredTruncGE X a hm :=
  FilteredObject.homMk (X.X.πTruncGE a) (fun p => (X.filtration.obj p).πTruncGE a)
    (fun p => CochainComplex.πTruncGE_naturality (X.filtration.ι.app p) a)

end TruncGE

/-- `τ_{≥ a}` of a morphism of filtered complexes: the morphism `τ_{≥ a} X^• ⟶ τ_{≥ a} Y^•`
whose step at `p` is `τ_{≥ a}` of the step at `p` of the given morphism. -/
public noncomputable def truncGEFilteredMap {X Y : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (α : X ⟶ Y) (a : ℤ)
    (hmX : ∀ p : ℤᵒᵖ, Mono (CochainComplex.truncGEMap (X.filtration.ι.app p) a))
    (hmY : ∀ p : ℤᵒᵖ, Mono (CochainComplex.truncGEMap (Y.filtration.ι.app p) a)) :
    filteredTruncGE X a hmX ⟶ filteredTruncGE Y a hmY :=
  FilteredObject.homMk (CochainComplex.truncGEMap α.hom a)
    (fun p => CochainComplex.truncGEMap (α.natTrans.app p) a)
    (fun p => by
      change CochainComplex.truncGEMap (α.natTrans.app p) a ≫
            CochainComplex.truncGEMap (Y.filtration.ι.app p) a =
          CochainComplex.truncGEMap (X.filtration.ι.app p) a ≫ CochainComplex.truncGEMap α.hom a
      rw [← HomologicalComplex.truncGEMap_comp, ← HomologicalComplex.truncGEMap_comp, α.comm p])

section TruncLE

variable (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (b : ℤ)

/-- The diagram `p ↦ τ_{≤ b} F^p X^•`. -/
public noncomputable def truncLEDiagram : ℤᵒᵖ ⥤ CochainComplex 𝒜 ℤ where
  obj p := (X.filtration.obj p).truncLE b
  map f := CochainComplex.truncLEMap (X.filtration.diagram.map f) b
  map_id p := by simp [CochainComplex.truncLEMap]
  map_comp f g := by simp [CochainComplex.truncLEMap, ← HomologicalComplex.truncLEMap_comp]

/-- The transformation `τ_{≤ b} F^p X^• ⟶ τ_{≤ b} X^•`. -/
public noncomputable def truncLEι :
    truncLEDiagram X b ⟶ (Functor.const ℤᵒᵖ).obj (X.X.truncLE b) where
  app p := CochainComplex.truncLEMap (X.filtration.ι.app p) b
  naturality p q f := by
    dsimp [truncLEDiagram, CochainComplex.truncLEMap]
    rw [← HomologicalComplex.truncLEMap_comp]
    simp

/-- The transformation `τ_{≤ b} F^p X^• ⟶ τ_{≤ b} X^•` is a monomorphism, `τ_{≤ b}` being left
exact. -/
public lemma mono_truncLEι_app (p : ℤᵒᵖ) : Mono ((truncLEι X b).app p) :=
  mono_truncLEMap _ _

/-- `τ_{≤ b} X^•`, filtered by the truncations `τ_{≤ b} F^p X^•` of the steps of the filtration
of `X^•`. This is the complex `M^•` of part (2). -/
public noncomputable def filteredTruncLE : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ where
  X := X.X.truncLE b
  filtration :=
    haveI : ∀ p : ℤᵒᵖ, Mono ((truncLEι X b).app p) := mono_truncLEι_app X b
    Filtration.ofDiagram (truncLEDiagram X b) (truncLEι X b)

/-- The canonical morphism `τ_{≤ b} X^• ⟶ X^•` of filtered complexes. -/
public noncomputable def ιFilteredTruncLE : filteredTruncLE X b ⟶ X :=
  FilteredObject.homMk (X.X.ιTruncLE b) (fun p => (X.filtration.obj p).ιTruncLE b)
    (fun p => (CochainComplex.ιTruncLE_naturality (X.filtration.ι.app p) b).symm)

end TruncLE

section Bounded

/-- The vanishing `H^{a - 1}(gr^p X^•) = 0` forces the inclusion `F^{p + 1}X^• ⟶ F^p X^•` to be
injective on the homology in degree `a`: that map is the second one of the exact sequence
`H^{a - 1}(gr^p X^•) ⟶ H^a(F^{p + 1}X^•) ⟶ H^a(F^p X^•)` of the short exact sequence
`0 ⟶ F^{p + 1}X^• ⟶ F^p X^• ⟶ gr^p X^• ⟶ 0`. -/
private lemma mono_homologyMap_filIncl (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (a p : ℤ)
    (h : ((FilteredObject.gr p).obj X).IsGE a) :
    Mono (homologyMap (filIncl X p) a) := by
  have hz : IsZero
      (((FilteredObject.gr p).obj X).homology (a - 1)) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (CochainComplex.exactAt_of_isGE _ a (a - 1) (by omega))
  exact ((shortExact_filIncl X p).homology_exact₁ (a - 1) a (by simp)).mono_g
    (hz.eq_of_src _ _)

/-- Every transition map `F^q X^• ⟶ F^p X^•` of the filtration is injective on the homology in
degree `a`, by induction along the filtration from `mono_homologyMap_filIncl`. -/
private lemma mono_homologyMap_diagram_map (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (a : ℤ)
    (h : ∀ p : ℤ, ((FilteredObject.gr p).obj X).IsGE a) (p q : ℤ)
    (f : (op q : ℤᵒᵖ) ⟶ op p) : Mono (homologyMap (X.filtration.diagram.map f) a) := by
  suffices H : ∀ r, p ≤ r → ∀ g : (op r : ℤᵒᵖ) ⟶ op p,
      Mono (homologyMap (X.filtration.diagram.map g) a) from H q (leOfHom f.unop) f
  refine Int.leInduction (fun g => ?_) fun r hr ih g => ?_
  · obtain rfl : g = 𝟙 _ := Subsingleton.elim _ _
    rw [CategoryTheory.Functor.map_id, homologyMap_id]
    infer_instance
  · obtain rfl : g = (homOfLE (Int.le_add_one le_rfl) : (r : ℤ) ⟶ r + 1).op ≫ (homOfLE hr).op :=
      Subsingleton.elim _ _
    rw [CategoryTheory.Functor.map_comp, homologyMap_comp]
    have := mono_homologyMap_filIncl X a r (h r)
    have := ih (homOfLE hr).op
    exact mono_comp _ _

/-- Every step of the filtration is injective on the homology in degree `a`: it propagates along
the filtration from `H^{a - 1}(gr^p X^•) = 0` by `mono_homologyMap_diagram_map`, the
base case being a step `p₀` at which `F^{p₀} X^•` already agrees with `X^•` in the degrees
`a - 1, a, a + 1`, where the map is an isomorphism (`isIso_homologyMap`). -/
private lemma mono_homologyMap_filtration_ι (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hX : X.filtration.IsDegreewiseFinite) (a : ℤ)
    (h : ∀ p : ℤ, ((FilteredObject.gr p).obj X).IsGE a)
    (p : ℤ) : Mono (homologyMap (X.filtration.ι.app (op p)) a) := by
  obtain ⟨p₁, -, hp₁, -⟩ := hX (a - 1)
  obtain ⟨p₂, -, hp₂, -⟩ := hX a
  obtain ⟨p₃, -, hp₃, -⟩ := hX (a + 1)
  obtain ⟨p₀, hle₁, hle₂, hle₃, hle⟩ : ∃ p₀ : ℤ, p₀ ≤ p₁ ∧ p₀ ≤ p₂ ∧ p₀ ≤ p₃ ∧ p₀ ≤ p :=
    ⟨min (min p₁ p₂) (min p₃ p), by omega, by omega, by omega, by omega⟩
  have hiso : IsIso (homologyMap (X.filtration.ι.app (op p₀)) a) :=
    isIso_homologyMap_of_isIso_f _ a (isIso_ι_f_of_le X hle₁ hp₁)
      (isIso_ι_f_of_le X hle₂ hp₂) (isIso_ι_f_of_le X hle₃ hp₃)
  have hfac : X.filtration.diagram.map (homOfLE hle : p₀ ⟶ p).op ≫
      X.filtration.ι.app (op p₀) = X.filtration.ι.app (op p) :=
    X.filtration.diagram_map_comp_ι_app _
  rw [← hfac, homologyMap_comp]
  have h₂ := mono_homologyMap_diagram_map X a h p₀ p (homOfLE hle).op
  exact mono_comp _ _

/-- Homology, Lemma 05QH(4). If the graded pieces of `X^•` are cohomologically `≥ a` then the
differentials of `X^•` are strict at `a`, so that `Coim(d^{a - 1}) = Im(d^{a - 1})` in
`Fil^f(𝒜)`; equivalently the canonical maps `τ_{≥ a} F^p X^• ⟶ τ_{≥ a} X^•` are monomorphisms.
In the degrees `> a` this is the monomorphism `F^p X^n ⟶ X^n`, and in the degree `a` it is the
injectivity of `F^p X^a / Im(d^{a - 1}) ⟶ X^a / Im(d^{a - 1})`, which the four lemma
`mono_opcyclesMap_of_mono_homologyMap` reduces to the injectivity of
`H^a(F^p X^•) ⟶ H^a(X^•)`. -/
private lemma mono_truncGEMap_filtration_ι (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hX : X.filtration.IsDegreewiseFinite) (a : ℤ)
    (h : ∀ p : ℤ, ((FilteredObject.gr p).obj X).IsGE a)
    (p : ℤᵒᵖ) : Mono (CochainComplex.truncGEMap (X.filtration.ι.app p) a) := by
  obtain ⟨p⟩ := p
  have hm : Mono (X.filtration.ι.app (op p)) := inferInstance
  refine mono_truncGEMap _ a ?_
  exact mono_opcyclesMap_of_mono_homologyMap _ a (j := a + 1) (by simp)
    (mono_homologyMap_filtration_ι X hX a h p) inferInstance

/-- The canonical morphism `X^• ⟶ τ_{≥ a} X^•` of filtered complexes is a filtered
quasi-isomorphism as soon as the graded pieces of `X^•` are cohomologically `≥ a`: each step
`F^p X^• ⟶ τ_{≥ a} F^p X^•` of it is a quasi-isomorphism, since `F^p X^•` is cohomologically
`≥ a` by `isGE_fil`. -/
private lemma filteredQuasiIso_πFilteredTruncGE (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hX : ∀ n : ℤ, ∃ q : ℤ, IsZero ((fil X q).X n)) (a : ℤ)
    (ha : ∀ p : ℤ, ((FilteredObject.gr p).obj X).IsGE a)
    (hm : ∀ p : ℤᵒᵖ, Mono (CochainComplex.truncGEMap (X.filtration.ι.app p) a)) :
    CochainComplex.filteredQuasiIso 𝒜 (πFilteredTruncGE X a hm) := by
  refine filteredQuasiIso_of_natTrans _ fun p => ?_
  change QuasiIso ((fil X p).πTruncGE a)
  rw [CochainComplex.quasiIso_πTruncGE_iff]
  exact isGE_fil X hX a ha p

/-- The filtration of `τ_{≥ a} X^•` is again finite in each degree: at a step where the
filtration of `X^n` is already all of `X^n` the map of truncations is both a monomorphism and an
epimorphism in degree `n`, and a step where `X^n` vanishes is a step where `(τ_{≥ a} X)^n`
vanishes. -/
private lemma finite_filteredTruncGE (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hX : X.filtration.IsDegreewiseFinite) (a : ℤ)
    (hm : ∀ p : ℤᵒᵖ, Mono (CochainComplex.truncGEMap (X.filtration.ι.app p) a)) :
    (filteredTruncGE X a hm).filtration.IsDegreewiseFinite := by
  intro n
  obtain ⟨p, q, hp, hq⟩ := hX n
  refine ⟨p, q, ?_, isZero_truncGE_X _ a n hq⟩
  have := hm (op p)
  have : Mono ((CochainComplex.truncGEMap (X.filtration.ι.app (op p)) a).f n) := inferInstance
  have : Epi ((CochainComplex.truncGEMap (X.filtration.ι.app (op p)) a).f n) :=
    epi_truncGEMap_f _ a n (have := hp; inferInstance)
  change IsIso ((CochainComplex.truncGEMap (X.filtration.ι.app (op p)) a).f n)
  exact isIso_of_mono_of_epi _

/-- The canonical morphism `τ_{≤ b} X^• ⟶ X^•` of filtered complexes is a filtered
quasi-isomorphism as soon as the graded pieces of `X^•` are cohomologically `≤ b`: each step
`τ_{≤ b} F^p X^• ⟶ F^p X^•` of it is a quasi-isomorphism, since `F^p X^•` is cohomologically
`≤ b` by `isLE_fil`. -/
public lemma filteredQuasiIso_ιFilteredTruncLE (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hX : ∀ n : ℤ, ∃ q : ℤ, IsZero ((fil X q).X n)) (b : ℤ)
    (hb : ∀ p : ℤ, ((FilteredObject.gr p).obj X).IsLE b) :
    CochainComplex.filteredQuasiIso 𝒜 (ιFilteredTruncLE X b) := by
  refine filteredQuasiIso_of_natTrans _ fun p => ?_
  change QuasiIso ((fil X p).ιTruncLE b)
  rw [CochainComplex.quasiIso_ιTruncLE_iff]
  exact isLE_fil X hX b hb p

/-- The filtration of `τ_{≤ b} X^•` is again finite in each degree: `τ_{≤ b}` sees only the
degrees `n - 1, n, n + 1` around `n`, where the filtration of `X^•` is already all of `X^•` at a
common step, and a step where `X^n` vanishes is a step where `(τ_{≤ b} X)^n` vanishes. -/
public lemma finite_filteredTruncLE (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hX : X.filtration.IsDegreewiseFinite) (b : ℤ) :
    (filteredTruncLE X b).filtration.IsDegreewiseFinite := by
  intro n
  obtain ⟨p, q, hp, hq⟩ := hX n
  obtain ⟨p', -, hp', -⟩ := hX (n + 1)
  obtain ⟨p'', -, hp'', -⟩ := hX (n - 1)
  refine ⟨min (min p p') p'', q, ?_, isZero_truncLE_X _ b n hq⟩
  exact isIso_truncLEMap_f _ b n
    (isIso_ι_f_of_le X (min_le_right (min p p') p'') hp'')
    (isIso_ι_f_of_le X ((min_le_left (min p p') p'').trans (min_le_left p p')) hp)
    (isIso_ι_f_of_le X ((min_le_left (min p p') p'').trans (min_le_right p p')) hp')

/-- Clause (1) of [Stacks, Tag 05S5]: the bounded below replacement of `K^•` is its truncation
`τ_{≥ a} K^•`, filtered by the truncations of the steps of the filtration of `K^•`. -/
private lemma exists_filteredQuasiIso_isStrictlyGE_of_isGE_gradedPiece
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hK : K.filtration.IsDegreewiseFinite) (a : ℤ)
    (ha : ∀ p : ℤ, ((FilteredObject.gr p).obj K).IsGE a) :
    ∃ (L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (α : K ⟶ L)
      (_ : CochainComplex.filteredQuasiIso 𝒜 α)
      (_ : L.X.IsStrictlyGE a), L.filtration.IsDegreewiseFinite := by
  have hm := mono_truncGEMap_filtration_ι K hK a ha
  exact ⟨filteredTruncGE K a hm, πFilteredTruncGE K a hm,
    filteredQuasiIso_πFilteredTruncGE K (exists_isZero_fil_X K hK) a ha hm,
    (by change (K.X.truncGE a).IsStrictlyGE a; infer_instance),
    finite_filteredTruncGE K hK a hm⟩

/-- Clause (2) of [Stacks, Tag 05S5]: the bounded above replacement of `K^•` is its truncation
`τ_{≤ b} K^•`, filtered by the truncations of the steps of the filtration of `K^•`. -/
private lemma exists_filteredQuasiIso_isStrictlyLE_of_isLE_gradedPiece
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hK : K.filtration.IsDegreewiseFinite) (b : ℤ)
    (hb : ∀ p : ℤ, ((FilteredObject.gr p).obj K).IsLE b) :
    ∃ (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (α : M ⟶ K)
      (_ : CochainComplex.filteredQuasiIso 𝒜 α)
      (_ : M.X.IsStrictlyLE b), M.filtration.IsDegreewiseFinite :=
  ⟨filteredTruncLE K b, ιFilteredTruncLE K b,
    filteredQuasiIso_ιFilteredTruncLE K (exists_isZero_fil_X K hK) b hb,
    (by change (K.X.truncLE b).IsStrictlyLE b; infer_instance),
    finite_filteredTruncLE K hK b⟩

/-- Clause (3) of [Stacks, Tag 05S5]: the commutative square of filtered quasi-isomorphisms with
`L^• = τ_{≥ a} K^•`,
`M^• = τ_{≤ b} K^•` and `N^• = τ_{≥ a} τ_{≤ b} K^•`. The graded pieces of `M^•` are again
cohomologically `≥ a`, since `gr^p(M^•) ⟶ gr^p(K^•)` is a quasi-isomorphism, so part (1) applies
to `M^•` and produces `N^•`; the fourth arrow is `τ_{≥ a}` of the second
(`truncGEFilteredMap`), the square commutes because `X^• ⟶ τ_{≥ a} X^•` is natural,
and the fourth arrow is a filtered quasi-isomorphism because the other three are and `gr^p` is a
functor. -/
private lemma exists_commSq_filteredQuasiIso_of_isGE_of_isLE_gradedPiece
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hK : K.filtration.IsDegreewiseFinite) (a b : ℤ)
    (ha : ∀ p : ℤ, ((FilteredObject.gr p).obj K).IsGE a)
    (hb : ∀ p : ℤ, ((FilteredObject.gr p).obj K).IsLE b) :
    ∃ (L M N : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (f : M ⟶ K) (g : M ⟶ N) (h : K ⟶ L)
      (i : N ⟶ L) (_ : CommSq f g h i) (_ : CochainComplex.filteredQuasiIso 𝒜 f)
      (_ : CochainComplex.filteredQuasiIso 𝒜 g) (_ : CochainComplex.filteredQuasiIso 𝒜 h)
      (_ : CochainComplex.filteredQuasiIso 𝒜 i) (_ : L.X.IsStrictlyGE a)
      (_ : M.X.IsStrictlyLE b) (_ : N.X.IsStrictlyGE a) (_ : N.X.IsStrictlyLE b),
      (L.filtration.IsDegreewiseFinite) ∧
        (M.filtration.IsDegreewiseFinite) ∧
        (N.filtration.IsDegreewiseFinite) := by
  have hfM : CochainComplex.filteredQuasiIso 𝒜 (ιFilteredTruncLE K b) :=
    filteredQuasiIso_ιFilteredTruncLE K (exists_isZero_fil_X K hK) b hb
  have hKM := finite_filteredTruncLE K hK b
  have haM : ∀ p : ℤ, ((FilteredObject.gr p).obj
      (filteredTruncLE K b)).IsGE a := by
    intro p
    have := hfM p
    have := ha p
    exact isGE_of_quasiIso
      ((FilteredObject.gr p).map (ιFilteredTruncLE K b)) a
  have hmK := mono_truncGEMap_filtration_ι K hK a ha
  have hmM := mono_truncGEMap_filtration_ι (filteredTruncLE K b) hKM a haM
  have hhK : CochainComplex.filteredQuasiIso 𝒜 (πFilteredTruncGE K a hmK) :=
    filteredQuasiIso_πFilteredTruncGE K (exists_isZero_fil_X K hK) a ha hmK
  have hgM : CochainComplex.filteredQuasiIso 𝒜
      (πFilteredTruncGE (filteredTruncLE K b) a hmM) :=
    filteredQuasiIso_πFilteredTruncGE (filteredTruncLE K b)
      (exists_isZero_fil_X (filteredTruncLE K b) hKM) a haM hmM
  have hsq : ιFilteredTruncLE K b ≫ πFilteredTruncGE K a hmK =
      πFilteredTruncGE (filteredTruncLE K b) a hmM ≫
        truncGEFilteredMap (ιFilteredTruncLE K b) a hmM hmK := by
    refine FilteredObject.hom_ext ?_
    dsimp [πFilteredTruncGE, ιFilteredTruncLE, truncGEFilteredMap]
    exact (CochainComplex.πTruncGE_naturality (K.X.ιTruncLE b) a).symm
  have hfi : CochainComplex.filteredQuasiIso 𝒜
      (truncGEFilteredMap (ιFilteredTruncLE K b) a hmM hmK) := by
    intro p
    have := hgM p
    have : QuasiIso ((FilteredObject.gr p).map
        (πFilteredTruncGE (filteredTruncLE K b) a hmM) ≫
          (FilteredObject.gr p).map
            (truncGEFilteredMap (ιFilteredTruncLE K b) a hmM hmK)) := by
      rw [← CategoryTheory.Functor.map_comp, ← hsq, CategoryTheory.Functor.map_comp]
      have := hfM p
      have := hhK p
      infer_instance
    exact quasiIso_of_comp_left ((FilteredObject.gr p).map
      (πFilteredTruncGE (filteredTruncLE K b) a hmM)) _
  exact ⟨filteredTruncGE K a hmK, filteredTruncLE K b,
    filteredTruncGE (filteredTruncLE K b) a hmM, ιFilteredTruncLE K b,
    πFilteredTruncGE (filteredTruncLE K b) a hmM, πFilteredTruncGE K a hmK,
    truncGEFilteredMap (ιFilteredTruncLE K b) a hmM hmK, ⟨hsq⟩, hfM, hgM, hhK, hfi,
    (by change (K.X.truncGE a).IsStrictlyGE a; infer_instance),
    (by change (K.X.truncLE b).IsStrictlyLE b; infer_instance),
    (by change ((K.X.truncLE b).truncGE a).IsStrictlyGE a; infer_instance),
    (by
      change ((K.X.truncLE b).truncGE a).IsStrictlyLE b
      have : (K.X.truncLE b).IsStrictlyLE b := inferInstance
      exact isStrictlyLE_truncGE (K.X.truncLE b) a b),
    finite_filteredTruncGE K hK a hmK, finite_filteredTruncLE K hK b,
    finite_filteredTruncGE (filteredTruncLE K b) hKM a hmM⟩

namespace CochainComplex

/-- **Stacks 05S5.** Let `𝒜` be an abelian category and let `K^•` be a filtered cochain complex
of `𝒜` whose filtration is finite in each degree, i.e. an object of `K(Fil^f(𝒜))`. Then, writing
`gr^p` for the graded pieces of the filtration:

1. if `H^n(gr(K^•)) = 0` for all `n < a`, i.e. every `gr^p(K^•)` is cohomologically `≥ a`, there
   is a filtered quasi-isomorphism `K^• ⟶ L^•` with `L^n = 0` for all `n < a`;
2. if `H^n(gr(K^•)) = 0` for all `n > b`, i.e. every `gr^p(K^•)` is cohomologically `≤ b`, there
   is a filtered quasi-isomorphism `M^• ⟶ K^•` with `M^n = 0` for all `n > b`;
3. if `H^n(gr(K^•)) = 0` for all `n < a` and for all `n > b`, i.e. `H^n(gr(K^•)) = 0` for
   `|n| ≫ 0`, there is a commutative square

   ```
   M^• ⟶ K^•
    ↓       ↓
   N^• ⟶ L^•
   ```

   of morphisms of filtered complexes all four of which are filtered quasi-isomorphisms, with
   `L^•` bounded below (`L^n = 0` for `n < a`), `M^•` bounded above (`M^n = 0` for `n > b`) and
   `N^•` bounded (`N^n = 0` for `n < a` and for `n > b`);

and in each case the complexes produced again have finite filtration in each degree, i.e. lie in
`K(Fil^f(𝒜))`. -/
@[stacks 05S5]
public theorem exists_filteredQuasiIso_bounded_of_isGE_of_isLE_gradedPiece
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hK : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n)) :
    (∀ a : ℤ, (∀ p : ℤ, ((FilteredObject.gr p).obj K).IsGE a) →
        ∃ (L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (α : K ⟶ L)
          (_ : CochainComplex.filteredQuasiIso 𝒜 α) (_ : L.X.IsStrictlyGE a),
          ∀ n : ℤ, ∃ p q : ℤ, IsIso ((L.filtration.ι.app (op p)).f n) ∧
            IsZero ((L.filtration.obj (op q)).X n)) ∧
      (∀ b : ℤ, (∀ p : ℤ, ((FilteredObject.gr p).obj K).IsLE b) →
        ∃ (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (α : M ⟶ K)
          (_ : CochainComplex.filteredQuasiIso 𝒜 α) (_ : M.X.IsStrictlyLE b),
          ∀ n : ℤ, ∃ p q : ℤ, IsIso ((M.filtration.ι.app (op p)).f n) ∧
            IsZero ((M.filtration.obj (op q)).X n)) ∧
      (∀ a b : ℤ, (∀ p : ℤ, ((FilteredObject.gr p).obj K).IsGE a) →
        (∀ p : ℤ, ((FilteredObject.gr p).obj K).IsLE b) →
        ∃ (L M N : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (f : M ⟶ K) (g : M ⟶ N) (h : K ⟶ L)
          (i : N ⟶ L) (_ : CommSq f g h i) (_ : CochainComplex.filteredQuasiIso 𝒜 f)
          (_ : CochainComplex.filteredQuasiIso 𝒜 g) (_ : CochainComplex.filteredQuasiIso 𝒜 h)
          (_ : CochainComplex.filteredQuasiIso 𝒜 i) (_ : L.X.IsStrictlyGE a)
          (_ : M.X.IsStrictlyLE b) (_ : N.X.IsStrictlyGE a) (_ : N.X.IsStrictlyLE b),
          (∀ n : ℤ, ∃ p q : ℤ, IsIso ((L.filtration.ι.app (op p)).f n) ∧
              IsZero ((L.filtration.obj (op q)).X n)) ∧
            (∀ n : ℤ, ∃ p q : ℤ, IsIso ((M.filtration.ι.app (op p)).f n) ∧
              IsZero ((M.filtration.obj (op q)).X n)) ∧
            (∀ n : ℤ, ∃ p q : ℤ, IsIso ((N.filtration.ι.app (op p)).f n) ∧
              IsZero ((N.filtration.obj (op q)).X n))) :=
  ⟨exists_filteredQuasiIso_isStrictlyGE_of_isGE_gradedPiece K hK,
    exists_filteredQuasiIso_isStrictlyLE_of_isLE_gradedPiece K hK,
    exists_commSq_filteredQuasiIso_of_isGE_of_isLE_gradedPiece K hK⟩

end CochainComplex

end Bounded

end
