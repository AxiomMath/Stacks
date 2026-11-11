module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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

@[expose] public section

universe w w' v v' u u'

/-!
# The graded pieces of a filtered right derived functor

Let `T : 𝒜 ⥤ ℬ` be an additive functor of abelian categories with `𝒜` having enough injectives.
This file proves the isomorphism `gr^p ∘ RT ≅ RT ∘ gr^p` of Tag 015U read at one filtered
injective resolution: for a filtered quasi-isomorphism `α : K^• ⟶ I^•`
into a filtered injective complex and a filtered complex `M^•` of `ℬ` with
`gr^p M^• ≅ T(gr^p I^•)` in `K^+(ℬ)` — the datum of `M^• = T_ext(I^•)` — there is an isomorphism
`gr^p M^• ≅ RT(gr^p K^•)` in `D^+(ℬ)`. The natural isomorphism of functors `DF^+(𝒜) ⥤ D^+(ℬ)`
of Tag 015U is `CategoryTheory.FilteredDerived.filteredRightDerivedFunctorGrPIso`.

## Main results

* `Stacks.FilteredDerived.GradedPieceIso.solution`: the isomorphism of Tag 015U at one filtered
  injective resolution.

## Implementation notes

The isomorphism is forced. Two of the three maps in the required commuting square are
isomorphisms, and the produced `Φ` is the composite of one with the inverse of the other:

* `gr^p α` is a quasi-isomorphism, because `α` is a filtered quasi-isomorphism; hence its image
  in `D^+(𝒜)` is an isomorphism, `DerivedCategory.Plus.Qh` being a localisation at the
  quasi-isomorphisms of `K^+(𝒜)`, and so is its image under `RT`;
* the unit `ε : Q ∘ T ⟶ RT ∘ Q` of the right derived functor is an isomorphism at
  `gr^p I^•`, a bounded below complex of injective objects.

So `Φ := (Q(e p) ≫ ε(gr^p I^•)) ≫ (RT(Q(gr^p α)))⁻¹`, and the pinning equation holds by
cancelling the inverse.

## References

* [Stacks Project, Tag 015U](https://stacks.math.columbia.edu/tag/015U)
-/

@[expose] public section



open CategoryTheory Limits Opposite FilteredObject

namespace Stacks.FilteredDerived.GradedPieceIso

/-- The isomorphism `gr^p ∘ RT ≅ RT ∘ gr^p` of [Stacks, Tag 015U] at one filtered injective
resolution `α : K^• ⟶ I^•`, with `M^•` presenting `T_ext(I^•)`: an isomorphism
`gr^p M^• ≅ RT(gr^p K^•)` in `D⁺(ℬ)` compatible with `RT(gr^p α)` and the unit of `RT`. -/
public theorem solution
    {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (T : A ⥤ B) [T.Additive]
    {K I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} (α : K ⟶ I)
    (hα : CochainComplex.filteredQuasiIso A α)
    (hinj : ∀ p n : ℤ, Injective (((gr p).obj I).X n))
    (M : FilteredObject (CochainComplex B ℤ) ℤᵒᵖ)
    (hK : ∀ p : ℤ, CochainComplex.plus A ((gr p).obj K))
    (hI : ∀ p : ℤ, CochainComplex.plus A ((gr p).obj I))
    (hM : ∀ p : ℤ, CochainComplex.plus B ((gr p).obj M))
    (e : ∀ p : ℤ, (HomotopyCategory.Plus.quotient B).obj ⟨_, hM p⟩ ≅
      T.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient A).obj ⟨_, hI p⟩)) (p : ℤ) :
    ∃ Φ : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient B).obj ⟨_, hM p⟩) ≅
        T.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
          ((HomotopyCategory.Plus.quotient A).obj ⟨_, hK p⟩)),
      Φ.hom ≫ T.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient A).map (ObjectProperty.homMk
            (X := ⟨_, hK p⟩) (Y := ⟨_, hI p⟩)
            ((gr p).map α)))) =
        DerivedCategory.Plus.Qh.map (e p).hom ≫
          T.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient A).obj ⟨_, hI p⟩) := by
  set f := (HomotopyCategory.Plus.quotient A).map (ObjectProperty.homMk
    (X := (⟨_, hK p⟩ : CochainComplex.Plus A)) (Y := ⟨_, hI p⟩) ((gr p).map α))
  -- `gr^p α` is a quasi-isomorphism, hence an isomorphism in `D^+(𝒜)`.
  have hf : HomotopyCategory.Plus.quasiIso A f := by
    rw [HomotopyCategory.Plus.quasiIso_iff]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff ((gr p).map α)).2 (hα p)
  have : IsIso (DerivedCategory.Plus.Qh.map f) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _ hf
  -- The unit of the right derived functor is an isomorphism at the complex of injectives.
  have : ∀ n : ℤ, Injective (((HomotopyCategory.Plus.quotient A).obj
      (⟨_, hI p⟩ : CochainComplex.Plus A)).obj.as.X n) := fun n => hinj p n
  refine ⟨(DerivedCategory.Plus.Qh.mapIso (e p)).trans
    ((asIso (T.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient A).obj ⟨_, hI p⟩))).trans
      (asIso (T.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map f))).symm), ?_⟩
  simp

end Stacks.FilteredDerived.GradedPieceIso

end

/-!
# The graded pieces of a filtered right derived functor

Let `T : 𝒜 ⥤ ℬ` be a functor of abelian categories with `𝒜` having enough injectives, so that the
right derived functor `RT : D⁺(𝒜) ⥤ D⁺(ℬ)` exists. On the filtered side, the filtered right
derived functor `RT : DF⁺(𝒜) ⥤ DF⁺(ℬ)` of [Stacks, Tag 015S] is defined as `T_ext ∘ j'`
([Stacks, Tag 05U2]), where `j'` is a quasi-inverse of the equivalence `K⁺(I^f) ⥤ DF⁺(𝒜)` of
[Stacks, Tag 015Q] and `T_ext` is the functor of [Stacks, Tag 05U0] on filtered injective objects,
built from the splitting `I ≅ ⨁_p I_p` of [Stacks, Tag 015T] so that its defining property is
`gr^p(T_ext I) = T(gr^p I)`. [Stacks, Tag 015U] is the isomorphism
```
gr^p ∘ RT ≅ RT ∘ gr^p
```
of functors `DF⁺(𝒜) ⥤ D⁺(ℬ)`, which is
`CategoryTheory.FilteredDerived.filteredRightDerivedFunctorGrPIso`. This file proves it read at
one filtered injective resolution: for a filtered injective resolution `α : K^• ⟶ I^•` of a filtered
complex, `gr^p(RT(K^•)) = gr^p(T_ext(I^•)) = T(gr^p I^•)` by the construction of `RT`, while
`gr^p α : gr^p K^• ⟶ gr^p I^•` is an injective resolution, so that `T(gr^p I^•)` computes
`RT(gr^p K^•)`; the isomorphism is the composite of the two.

## Main results

* `CochainComplex.exists_iso_gradedPiece_rightDerivedFunctorPlus_of_filteredQuasiIso`: let
  `α : K^• ⟶ I^•` be a filtered quasi-isomorphism of filtered cochain complexes of `𝒜` with each
  `gr^p I^n` injective and all graded pieces bounded below, and let `M^•` be a filtered cochain
  complex of `ℬ` whose graded pieces are bounded below and isomorphic in `K⁺(ℬ)` to
  `T(gr^p I^•)` — the datum of `M^• = T_ext(I^•)` used to construct the filtered `RT`. Then for
  every `p` there is an isomorphism `gr^p M^• ≅ RT(gr^p K^•)` in `D⁺(ℬ)`, compatible with
  `RT(gr^p α)` and with the canonical map `Q(T(gr^p I^•)) ⟶ RT(Q(gr^p I^•))`; that compatibility
  determines it uniquely.

## Implementation notes

*Stated on resolutions rather than on `DF⁺(𝒜)`.* This file does not use the functors on
`DF⁺(𝒜)`: `RT(K^•)` is presented by the data that define it, a filtered quasi-isomorphism
`α : K^• ⟶ I^•` into a filtered injective complex — every object of `DF⁺(𝒜)` is of this form, by
[Stacks, Tag 015Q] — together with `M^• = T_ext(I^•)`, and the conclusion is the isomorphism of the
source's formula for that presentation, pinned by an equation whose other two maps are
isomorphisms. The natural isomorphism of functors `DF⁺(𝒜) ⥤ D⁺(ℬ)` itself, built on the
triangulated `DF⁺(𝒜)` and the equivalence `K⁺(I^f) ≌ DF⁺(𝒜)` of [Stacks, Tag 015Q], is
`CategoryTheory.FilteredDerived.filteredRightDerivedFunctorGrPIso`, which carries the tag.

*`T_ext` is presented by its defining property.* The functor `T_ext` of [Stacks, Tag 05U0] depends
on a choice of splitting; on filtered injective objects it is `T` applied with the filtration
`F^p T(I) = T(F^p I)`, which is how `CategoryTheory.FilteredDerived.filteredRightDerivedFunctor`
builds it. Here what its construction contributes here is exactly
the identification `gr^p(T_ext I^•) = T(gr^p I^•)`, so `T_ext(I^•)` is quantified over as any
filtered complex `M^•` of `ℬ` with isomorphisms `e p : gr^p M^• ≅ T(gr^p I^•)`. Two consequences,
both strengthening the statement: it holds for every such `M^•`, in particular for `T_ext(I^•)`
once that functor is constructed; and `e p` is asked for only in the homotopy category `K⁺(ℬ)`,
i.e. as a homotopy equivalence, where the source has an equality of complexes.

*Filtered complexes rather than complexes of filtered objects.* As in [Stacks, Tag 05RZ],
[Stacks, Tag 05S3] and [Stacks, Tag 015W], a complex of filtered objects is the same datum as a
complex filtered by subcomplexes, so `Comp(Fil(𝒜))` is `FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ`
with `ℤᵒᵖ` recording that the filtration decreases, `gr^p` is
`FilteredObject.gr p`, and a filtered quasi-isomorphism is
`CochainComplex.filteredQuasiIso`. The localisation `D⁺` is spelled as `DerivedCategory.Plus.Qh`
on the bounded below homotopy category, rather than through `DerivedCategory.Plus.Q`, because that
is where Mathlib's unit `Functor.rightDerivedFunctorPlusUnith` of the right derived functor lives.

*Minimal hypotheses.* Only what the conclusion uses is assumed: `T` is additive, where the source
assumes it left exact (as in [Stacks, Tag 015J] and [Stacks, Tag 015W]; `RT` exists for an additive
functor out of a category with enough injectives, [Stacks, Tag 015A]); the filtrations are not
assumed finite in any degree, since finiteness enters the source's discussion only through the
equivalence of [Stacks, Tag 015Q], which is bypassed by quantifying over the resolution; and
`K^•`, `I^•`, `M^•` are not assumed bounded below, only their graded pieces, which is what names
them as objects of `D⁺` and is the source's membership of `Comp⁺(Fil^f)` — it holds for each of
the three as soon as the complex itself is bounded below.

Faithfulness. (1) No hypothesis is idle: `EnoughInjectives 𝒜` and `T.Additive` are what make `RT`
exist, `hα` is used through `RT(gr^p α)` in the pinning equation, the injectivity of the terms of
`gr^p I^•` is what makes `Q(T(gr^p I^•)) ⟶ RT(Q(gr^p I^•))` an isomorphism, `M^•` with the
isomorphisms `e` is the source of the isomorphism produced, and the three boundedness hypotheses
name the objects it is between. (2) The data are the source's: two abelian categories, one functor
`T : 𝒜 ⥤ ℬ`, cochain complexes with cohomological indexing, decreasing `ℤ`-indexed filtrations,
and the isomorphism in `D⁺(ℬ)` itself, not in a localisation of it. (3) The isomorphism is pinned,
not merely asserted to exist: it satisfies `Φ ≫ RT(Q(gr^p α)) = Q(e p) ≫ ε(gr^p I^•)` for
Mathlib's canonical unit `ε : Q ∘ T ⟶ RT ∘ Q` of the right derived functor, and since
`RT(Q(gr^p α))` is an isomorphism this determines `Φ`; the content of the statement is that
`Q(e p) ≫ ε(gr^p I^•)` is an isomorphism. (4) The instantiation is not degenerate: with
`𝒜 = ℬ = ModuleCat ℤ`, `T = Hom(ℤ/2, -)`, `K^• = ℤ[0]` and `I^•` an injective resolution of `ℤ`,
both filtered by `F^0 = ⬝` and `F^1 = 0`, and `M^• = T(I^•)` filtered the same way, the statement
gives `Q(T(I^•)) ≅ RT(Q(ℤ[0]))`, whose degree `1` cohomology is `Ext^1(ℤ/2, ℤ) = ℤ/2 ≠ 0`.

## References

* [Stacks Project, Tag 015U](https://stacks.math.columbia.edu/tag/015U)
* [Stacks Project, Tag 015S](https://stacks.math.columbia.edu/tag/015S)
* [Stacks Project, Tag 015T](https://stacks.math.columbia.edu/tag/015T)
* [Stacks Project, Tag 05U0](https://stacks.math.columbia.edu/tag/05U0)
* [Stacks Project, Tag 05U2](https://stacks.math.columbia.edu/tag/05U2)
* [Stacks Project, Tag 015Q](https://stacks.math.columbia.edu/tag/015Q)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 05RZ](https://stacks.math.columbia.edu/tag/05RZ)
* [Stacks Project, Tag 05S3](https://stacks.math.columbia.edu/tag/05S3)
* [Stacks Project, Tag 015W](https://stacks.math.columbia.edu/tag/015W)
-/

@[expose] public section



open CategoryTheory Limits Opposite FilteredObject

namespace CochainComplex

/-- Let `T : 𝒜 ⥤ ℬ` be an additive functor of abelian categories with `𝒜` having
enough injectives, and let `RT : D⁺(𝒜) ⥤ D⁺(ℬ)` be its right derived functor. Let `α : K^• ⟶ I^•`
be a filtered quasi-isomorphism of filtered cochain complexes of `𝒜` with `I^•` filtered
injective, i.e. every `gr^p I^n` injective — a filtered injective resolution of `K^•` — and let
`M^•` be a filtered cochain complex of `ℬ` together with isomorphisms
`e p : gr^p M^• ≅ T(gr^p I^•)` in the homotopy category, the datum of `M^• = T_ext(I^•)` out of
which the filtered right derived functor is built, so that `M^•` presents `RT(K^•)` in `DF⁺(ℬ)`;
assume the graded pieces of `K^•`, `I^•` and `M^•` are bounded below. Then, for every `p`, there
is an isomorphism `gr^p(RT(K^•)) = gr^p M^• ≅ RT(gr^p K^•)` in `D⁺(ℬ)` compatible with
`RT(gr^p α)` and with the canonical map `Q(T(gr^p I^•)) ⟶ RT(Q(gr^p I^•))` of the right derived
functor; since the former is an isomorphism, the compatibility determines it uniquely. This is the
isomorphism `gr^p ∘ RT ≅ RT ∘ gr^p` of [Stacks, Tag 015U] read at one filtered injective
resolution; the isomorphism of functors on `DF⁺(𝒜)` is
`CategoryTheory.FilteredDerived.filteredRightDerivedFunctorGrPIso`. -/
public theorem exists_iso_gradedPiece_rightDerivedFunctorPlus_of_filteredQuasiIso
    {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (T : A ⥤ B) [T.Additive]
    {K I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} (α : K ⟶ I)
    (hα : filteredQuasiIso A α)
    (hinj : ∀ p n : ℤ, Injective (((gr p).obj I).X n))
    (M : FilteredObject (CochainComplex B ℤ) ℤᵒᵖ)
    (hK : ∀ p : ℤ, CochainComplex.plus A ((gr p).obj K))
    (hI : ∀ p : ℤ, CochainComplex.plus A ((gr p).obj I))
    (hM : ∀ p : ℤ, CochainComplex.plus B ((gr p).obj M))
    (e : ∀ p : ℤ, (HomotopyCategory.Plus.quotient B).obj ⟨_, hM p⟩ ≅
      T.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient A).obj ⟨_, hI p⟩)) (p : ℤ) :
    ∃ Φ : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient B).obj ⟨_, hM p⟩) ≅
        T.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
          ((HomotopyCategory.Plus.quotient A).obj ⟨_, hK p⟩)),
      Φ.hom ≫ T.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient A).map (ObjectProperty.homMk
            (X := ⟨_, hK p⟩) (Y := ⟨_, hI p⟩)
            ((gr p).map α)))) =
        DerivedCategory.Plus.Qh.map (e p).hom ≫
          T.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient A).obj ⟨_, hI p⟩) :=
  Stacks.FilteredDerived.GradedPieceIso.solution (I := I) (K := K) T α hα hinj M hK hI hM e p

end CochainComplex

end

/-!
# Forgetting the filtration commutes with the filtered right derived functor

Let `T : 𝒜 ⥤ ℬ` be an additive functor of abelian categories with `𝒜` having enough injectives,
and let `I` be a bounded below filtered cochain complex of `𝒜` with degreewise finite filtration
all of whose graded pieces `gr^p I` are complexes of injective objects. This file proves that the
component at `(forget F) I` of the unit `Q ∘ T ⟶ RT ∘ Q` of the right derived functor
`RT : D⁺(𝒜) ⥤ D⁺(ℬ)` is an isomorphism. This is the pointwise input to the isomorphism of
functors `(forget F) ∘ RT ≅ RT ∘ (forget F)` of [Stacks, Tag 015V], which is
`CategoryTheory.FilteredDerived.filteredRightDerivedFunctorForgetIso`.

## Main results

* `Stacks.FilteredDerived.ForgetCommutes.solution`: the unit of `RT` is invertible at the
  underlying complex of a bounded below complex of filtered injective objects.

## Implementation notes

*The mathematical content is that `(forget F) I` is a complex of injectives.* The unit of a right
derived functor is invertible on a bounded below complex with injective terms — this is the
injective derivability structure of `Mathlib.Algebra.Homology.DerivedCategory.
DerivabilityStructureInjectives`, which supplies the instance
`IsIso (α.app K)` for `K : HomotopyCategory.Plus 𝒜` all of whose terms are injective. So the whole
of the proof is the identification of the underlying complex of a complex of filtered injective
objects as a complex of injective objects, which is [Stacks, Tag 05TP] in the form used by
[Stacks, Tag 015Q](4): a degree at a time, descending induction along the finite filtration, the
inductive step being that `F^p` is injective as soon as `F^{p + 1}` and
`gr^p = F^p / F^{p + 1}` are, because `0 → F^{p + 1} → F^p → gr^p → 0` splits when `F^{p + 1}` is
injective. Cokernels of cochain complexes being computed degreewise, `gr^p I` in degree `n` is the
cokernel of the `n`-th term of `F^{p + 1} I ⟶ F^p I`, which is what lets the induction run inside a
fixed degree.

## References

* [Stacks Project, Tag 015V](https://stacks.math.columbia.edu/tag/015V)
* [Stacks Project, Tag 015Q](https://stacks.math.columbia.edu/tag/015Q)
* [Stacks Project, Tag 05TP](https://stacks.math.columbia.edu/tag/05TP)
-/

@[expose] public section

open CategoryTheory Limits Opposite



namespace Stacks.FilteredDerived.ForgetCommutes

section Injective

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- If `A ⟶ B` is a monomorphism with `A` and `B/A` injective, then `B` is injective: the
sequence `0 → A → B → B/A → 0` splits, so `B ≅ A ⊞ B/A`. -/
lemma injective_of_injective_cokernel {A B : 𝒜} (i : A ⟶ B) [Mono i]
    (hA : Injective A) (hQ : Injective (cokernel i)) : Injective B := by
  have := hA
  have := hQ
  let S : ShortComplex 𝒜 := ShortComplex.mk i (cokernel.π i) (by simp)
  have sp : S.Splitting :=
    ShortComplex.Splitting.ofExactOfRetraction S (ShortComplex.exact_cokernel i)
      (Injective.factorThru (𝟙 A) i) (Injective.comp_factorThru _ _) inferInstance
  exact Injective.of_iso sp.isoBinaryBiproduct.symm Injective.instBiprod

/-- The `n`-th term of the `p`-th graded piece of a filtered cochain complex is the cokernel of
the `n`-th term of the inclusion `F^{p + 1} ⟶ F^p`: cokernels of cochain complexes are computed
degreewise. -/
private noncomputable def gradedPieceXIso (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (p n : ℤ) :
    ((FilteredObject.gr p).obj K).X n ≅
      cokernel ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n).map
        (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)) :=
  PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n) _

/-- If `F^{p + 1} K` and `gr^p K` are injective in degree `n`, then so is `F^p K`: the short exact
sequence `0 → F^{p + 1} K^n → F^p K^n → gr^p K^n → 0` splits. -/
private lemma injective_filtration_obj_X (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p n : ℤ)
    (hsucc : Injective ((K.filtration.obj (op (p + 1))).X n))
    (hgr : Injective (((FilteredObject.gr p).obj K).X n)) :
    Injective ((K.filtration.obj (op p)).X n) :=
  injective_of_injective_cokernel
    ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n).map
      (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op))
    hsucc (Injective.of_iso (gradedPieceXIso K p n) hgr)

/-- Descending induction along the filtration: if every graded piece is injective in degree `n`
and `F^q K` vanishes in degree `n`, then every step `F^p K` with `p ≤ q` is injective in degree
`n`. -/
lemma injective_filtration_obj_X_of_isZero (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (n q : ℤ) (hq : IsZero ((K.filtration.obj (op q)).X n))
    (hgr : ∀ p : ℤ, Injective (((FilteredObject.gr p).obj K).X n)) :
    ∀ (k : ℕ) (p : ℤ), p + k = q → Injective ((K.filtration.obj (op p)).X n) := by
  intro k
  induction k with
  | zero =>
    intro p hp
    obtain rfl : p = q := by simpa using hp
    exact hq.injective
  | succ k ih =>
    intro p hp
    exact injective_filtration_obj_X K p n (ih (p + 1) (by push_cast at hp ⊢; omega)) (hgr p)

/-- The underlying complex of a complex of filtered injective objects with degreewise finite
filtration has injective terms ([Stacks, Tag 05TP], in the form of [Stacks, Tag 015Q](4)). -/
lemma injective_X_of_injective_gradedPiece
    (I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hIfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
      IsZero ((I.filtration.obj (op q)).X n))
    (hI : ∀ p n : ℤ, Injective (((FilteredObject.gr p).obj I).X n))
    (n : ℤ) : Injective (I.X.X n) := by
  obtain ⟨p₀, q₀, hiso, hzero⟩ := hIfin n
  obtain ⟨k, p₁, hle, hsum⟩ : ∃ (k : ℕ) (p₁ : ℤ), p₁ ≤ p₀ ∧ p₁ + k = q₀ :=
    ⟨(q₀ - p₀).toNat, q₀ - (q₀ - p₀).toNat, by omega, by omega⟩
  have hnat : I.filtration.diagram.map (homOfLE hle : p₁ ⟶ p₀).op ≫
      I.filtration.ι.app (op p₁) = I.filtration.ι.app (op p₀) :=
    I.filtration.diagram_map_comp_ι_app (homOfLE hle : p₁ ⟶ p₀).op
  have hnatf := HomologicalComplex.congr_hom hnat n
  rw [HomologicalComplex.comp_f] at hnatf
  have hepi : Epi ((I.filtration.ι.app (op p₁)).f n) := by
    have : Epi ((I.filtration.diagram.map (homOfLE hle : p₁ ⟶ p₀).op).f n ≫
        (I.filtration.ι.app (op p₁)).f n) := by
      rw [hnatf]
      infer_instance
    exact epi_of_epi ((I.filtration.diagram.map (homOfLE hle : p₁ ⟶ p₀).op).f n) _
  have : IsIso ((I.filtration.ι.app (op p₁)).f n) := isIso_of_mono_of_epi _
  exact Injective.of_iso (asIso ((I.filtration.ι.app (op p₁)).f n))
    (injective_filtration_obj_X_of_isZero I n q₀ hzero (fun p => hI p n) k p₁ hsum)

end Injective

/-- The unit `Q ∘ T ⟶ RT ∘ Q` of the right derived functor is invertible at the underlying
complex of a bounded below filtered complex with degreewise finite filtration and injective
graded pieces. This is the pointwise input to [Stacks, Tag 015V]; the isomorphism of functors
itself is `CategoryTheory.FilteredDerived.filteredRightDerivedFunctorForgetIso`. -/
public theorem solution
    {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (T : A ⥤ B) [T.Additive]
    (I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (a : ℤ) [I.X.IsStrictlyGE a]
    (hI : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
      IsZero ((I.filtration.obj (op q)).X n))
    (hinj : ∀ p n : ℤ,
      Injective (((FilteredObject.gr p).obj I).X n)) :
    IsIso (T.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj
      ⟨FilteredObject.forget.obj I,
        (CochainComplex.plus_iff A _).2 ⟨a, ‹I.X.IsStrictlyGE a›⟩⟩)) := by
  -- The underlying complex of `I` is a bounded below complex of injective objects.
  have : ∀ n : ℤ, Injective ((FilteredObject.forget.obj I).X n) := fun n =>
    injective_X_of_injective_gradedPiece I hI hinj n
  -- The unit of a right derived functor is invertible there, by the injective derivability
  -- structure.
  infer_instance

end Stacks.FilteredDerived.ForgetCommutes

end

/-!
# Forgetting the filtration commutes with the filtered right derived functor

Let `𝒜`, `ℬ` be abelian categories, let `T : 𝒜 ⥤ ℬ` be an additive functor and assume `𝒜` has
enough injectives. The *filtered right derived functor* `RT : DF⁺(𝒜) ⥤ DF⁺(ℬ)`
([Stacks, Tag 015S]) is constructed by choosing a quasi-inverse `j'` of the equivalence
`K⁺(I^f) ⥤ DF⁺(𝒜)` of [Stacks, Tag 015Q] and applying, to a bounded below complex `I` of filtered
injective objects, the functor `T_ext` of [Stacks, Tag 05U0]: writing `I ≅ ⨁_p I_p` with
`F^p I = ⨁_{q ≥ p} I_q` ([Stacks, Tag 015T]), one sets `T_ext(I) = ⨁_p T(I_p)` with
`F^p T_ext(I) = ⨁_{q ≥ p} T(I_q)`, and `RT = T_ext ∘ j'` ([Stacks, Tag 05U2]). Because
`RT : D⁺(𝒜) ⥤ D⁺(ℬ)` is computed by injective resolutions as well, the square

```
DF⁺(𝒜) --RT--> DF⁺(ℬ)
  |                |
forget F        forget F
  v                v
 D⁺(𝒜) --RT-->  D⁺(ℬ)
```

commutes: `(forget F) ∘ RT ≅ RT ∘ (forget F)` as functors `DF⁺(𝒜) ⥤ D⁺(ℬ)`. Concretely, the
underlying complex of a bounded below complex `I` of filtered injective objects is a bounded below
complex of injective objects ([Stacks, Tag 05TP], [Stacks, Tag 015Q]), hence an injective
resolution of the underlying complex of any filtered complex mapping to `I` by a filtered
quasi-isomorphism ([Stacks, Tag 05S3]); and the underlying complex of `T_ext(I)` is `⨁_p T(I_p)`,
which is `T` of the underlying complex of `I` because `T` is additive and the filtration is finite
(`CategoryTheory.Functor.mapBiproduct`). So both composites are computed by `T` applied termwise
to the underlying complex of `I`, and the comparison map between them is the canonical one, the
unit `Q ∘ T ⟶ RT ∘ Q` of the right derived functor.

## Main results

* `CochainComplex.isIso_rightDerivedFunctorPlusUnit_app_forget_of_injective_gradedPiece`: for `I` a
  bounded below filtered cochain complex of `𝒜` with degreewise finite filtration all of whose
  graded pieces have injective terms, the canonical map `Q(T((forget F) I)) ⟶ RT(Q((forget F) I))`
  in `D⁺(ℬ)` is an isomorphism.

## Implementation notes

*What is stated.* This is a pointwise statement, not the isomorphism of functors of
[Stacks, Tag 015V]: it says that the component at `(forget F) I` of
`CategoryTheory.Functor.rightDerivedFunctorPlusUnith`, the canonical natural transformation
`Q ∘ T ⟶ RT ∘ Q` on `K⁺(𝒜)`, is invertible when `I` is a bounded below complex of filtered
injective objects. That is the input from which the isomorphism of functors
`RT ⋙ forget F ≅ forget F ⋙ RT` on `DF⁺(𝒜)`, with `RT : DF⁺(𝒜) ⥤ DF⁺(ℬ)` the filtered right
derived functor, is built: that statement is
`CategoryTheory.FilteredDerived.filteredRightDerivedFunctorForgetIso`.

*Filtered complexes rather than complexes of filtered objects.* As in [Stacks, Tag 05RZ] and
[Stacks, Tag 015Q], a complex of filtered objects `(I^n, F)` is the same datum as a complex `I^•`
filtered by subcomplexes, so the source's `K(Fil^f(𝒜))` is modelled by
`FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ` with `ℤᵒᵖ` recording that the filtration decreases;
`(forget F) I` is `CategoryTheory.FilteredObject.forget.obj I` and finiteness of the filtration in
each degree is spelled exactly as in [Stacks, Tag 05S3] and [Stacks, Tag 015Q] by
`∃ p, IsIso ((I.filtration.ι.app (op p)).f n)` and `∃ q, IsZero ((I.filtration.obj (op q)).X n)`.
Filtered injectivity is spelled as in [Stacks, Tag 015P] and [Stacks, Tag 015Q]: every `gr^p I` is
a complex of injective objects of `𝒜`, `gr^p` being
`CategoryTheory.FilteredObject.gr p` of [Stacks, Tag 05RZ].

*`T` is additive, where the source assumes it left exact.* Left exactness is what makes the induced
functor `Fil^f(𝒜) ⥤ Fil^f(ℬ)` of [Stacks, Tag 05TZ] exist, and it is not used here: `RT`, its unit
and `T_ext` exist for `T` merely additive, which is the source's own observation before
[Stacks, Tag 015T]. The same departure is made in [Stacks, Tag 015J] and [Stacks, Tag 015W].

*Bounded below in the strict sense.* Membership of `L(I)` in `DF⁺(𝒜)` is the cohomological
condition `filteredPlus 𝒜` of [Stacks, Tag 05S4], while the complexes of filtered injectives
produced by [Stacks, Tag 05TW] and named in [Stacks, Tag 015Q](1) are bounded below strictly,
`I^n = 0` for `n < a`; the strict form is assumed here, as in those two statements, and it is what
places `(forget F) I` in `CochainComplex.Plus 𝒜` and so lets the two sides be formed at all.

Faithfulness. (1) No hypothesis is idle. `EnoughInjectives 𝒜` and `T.Additive` are what make `RT`
and its unit exist; the lower bound `a` is what names the object of `D⁺(ℬ)`; degreewise finiteness
of the filtration and injectivity of the terms of every `gr^p I` are jointly what make the
underlying complex of `I` a complex of injectives ([Stacks, Tag 05TP]), and neither can be
dropped: with the constant filtration `F^p I = I` for all `p` every `gr^p I` vanishes, hence has
injective terms, while for `𝒜 = ℬ = ModuleCat ℤ`, `I = ℤ[0]` and `T = Hom(ℤ/2, -)` the map in
question is `0 ⟶ RT(ℤ)`, and `H^1(RT(ℤ)) = Ext^1(ℤ/2, ℤ) = ℤ/2 ≠ 0`; the same pair `I`, `T` with
the one-step filtration `F^p I = I` for `p ≤ 0`, `F^p I = 0` for `p ≥ 1` — which is degreewise
finite, with `gr^0 I = I` not injective — shows injectivity of the graded pieces cannot be
dropped either. (2) The base is the source's: two abelian categories `𝒜`, `ℬ`, one additive
functor `T : 𝒜 ⥤ ℬ` between them, filtrations indexed by `ℤ` with the source's decreasing
convention, cochain complexes with cohomological indexing, and the comparison taken in `D⁺(ℬ)`
itself. (3) The canonical map is pinned: it is the component of
`CategoryTheory.Functor.rightDerivedFunctorPlusUnith`, not an unnamed isomorphism, so the statement
is the characterising property of `RT` at this object rather than a bare equivalence of objects.
(4) The instantiation is not degenerate: for `𝒜 = ℬ = ModuleCat ℤ`, `E^• = (ℚ ⟶ ℚ/ℤ)` in degrees
`0, 1` and `I^• = E^• ⊕ E^•` filtered by `F^p I = I` for `p ≤ 0`, `F^1 I = 0 ⊕ E^•` and
`F^p I = 0` for `p ≥ 2`, the filtration is degreewise finite and non-trivial with
`gr^0 I = gr^1 I = E^•` a complex of injectives, `(forget F) I` is an injective resolution of
`ℤ ⊕ ℤ`, and for `T = Hom(ℤ/2, -)` both sides of the isomorphism have
`H^1 = Ext^1(ℤ/2, ℤ ⊕ ℤ) = ℤ/2 ⊕ ℤ/2`, so the isomorphism is not one between zero objects.

## References

* [Stacks Project, Tag 015V](https://stacks.math.columbia.edu/tag/015V)
* [Stacks Project, Tag 015Q](https://stacks.math.columbia.edu/tag/015Q)
* [Stacks Project, Tag 015S](https://stacks.math.columbia.edu/tag/015S)
* [Stacks Project, Tag 015T](https://stacks.math.columbia.edu/tag/015T)
* [Stacks Project, Tag 05U0](https://stacks.math.columbia.edu/tag/05U0)
* [Stacks Project, Tag 05U2](https://stacks.math.columbia.edu/tag/05U2)
* [Stacks Project, Tag 05TP](https://stacks.math.columbia.edu/tag/05TP)
* [Stacks Project, Tag 05TW](https://stacks.math.columbia.edu/tag/05TW)
* [Stacks Project, Tag 05TZ](https://stacks.math.columbia.edu/tag/05TZ)
* [Stacks Project, Tag 05S1](https://stacks.math.columbia.edu/tag/05S1)
* [Stacks Project, Tag 05S3](https://stacks.math.columbia.edu/tag/05S3)
* [Stacks Project, Tag 05S4](https://stacks.math.columbia.edu/tag/05S4)
* [Stacks Project, Tag 05RZ](https://stacks.math.columbia.edu/tag/05RZ)
* [Stacks Project, Tag 015P](https://stacks.math.columbia.edu/tag/015P)
-/

@[expose] public section



open CategoryTheory Limits Opposite

namespace CochainComplex

/-- Let `T : 𝒜 ⥤ ℬ` be an additive functor of abelian categories with `𝒜` having
enough injectives, and let `I` be a bounded below complex of filtered injective objects: a bounded
below filtered cochain complex of `𝒜` every term `(I^n, F^• I^n)` of which is a filtered injective
object of `Fil^f(𝒜)`. Then the canonical map
```
Q(T((forget F) I)) ⟶ RT(Q((forget F) I))
```
in `D⁺(ℬ)` — the component at `(forget F) I` of the unit of the right derived functor
`RT : D⁺(𝒜) ⥤ D⁺(ℬ)` — is an isomorphism. This is a pointwise statement: the isomorphism of
functors `(forget F) ∘ RT ≅ RT ∘ (forget F)` on `DF⁺(𝒜)` of [Stacks, Tag 015V] is
`CategoryTheory.FilteredDerived.filteredRightDerivedFunctorForgetIso`. -/
public theorem isIso_rightDerivedFunctorPlusUnit_app_forget_of_injective_gradedPiece
    {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (T : A ⥤ B) [T.Additive]
    (I : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (a : ℤ) [I.X.IsStrictlyGE a]
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective) :
    IsIso (T.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj
      ⟨FilteredObject.forget.obj I,
        (CochainComplex.plus_iff A _).2 ⟨a, ‹I.X.IsStrictlyGE a›⟩⟩)) :=
  Stacks.FilteredDerived.ForgetCommutes.solution (B := B) T I a
    (fun n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).1)
    (fun p n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).2 p)

end CochainComplex

end
