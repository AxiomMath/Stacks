module

public import StacksFrontier.AlgebraicGeometry.Chow.SmoothChowCohomologyDedekind

/-!
# Stacks 0FCB in one statement

Let `(S, δ)` be a base as in Stacks section 42.63: `S` is locally Noetherian with an open covering
by spectra of Dedekind domains, `δ = 0` at the closed points and `δ = 1` elsewhere. A field is a
Dedekind domain (in the Stacks Project, Algebra, Lemma 034X, as in Mathlib), so a component of `S`
may be a point; this is the hypothesis of the source, not a generalization of it. Let `X` be smooth
over `S` and equidimensional of dimension `d`: every irreducible component of `X` has
δ-dimension `d`.

This file assembles Stacks 0FCB into one theorem,
`IsDedekindChowBase.chowCohomologyCapFundamentalClass_bijective_and_mulId`:

1. the map `Θ : A^p(X) ⟶ CH_{d-p}(X)`, `c ↦ c ∩ [X]_d`, is an isomorphism for every `p`;
2. for `d = e + 1`, `Θ(a · b) = Θ(a) · Θ(b)` on the part `X₁` of `X` over the one-dimensional part
   of `S` (all of `X` when `S` has no zero-dimensional component), with the intersection product
   `α · β = Δ^!(α × β)` of section 42.64; for `d = 0` the part `X₁` is empty;
3. the second clause is false as stated over a field component of `S`: for `S = X = Spec k`,
   `Θ(1 · 1) = [X]₀ ≠ 0`, while every intersection product of two `0`-cycles lands in
   `CH_{-1}(X) = 0`, the exterior product of section 42.63 lowering the degree by one.

## Main results

* `IsDedekindChowBase.chowCohomologyCapFundamentalClass_bijective_and_mulId` — **Stacks 0FCB**.

## References

* [Stacks Project, Tag 0FCB](https://stacks.math.columbia.edu/tag/0FCB)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Section 42.64 (Tag 0FC9)](https://stacks.math.columbia.edu/tag/0FC9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.IsDedekindChowBase

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] [Smooth sX]

include hS in
/-- **Stacks 0FCB.** Let `(S, δ)` be a base as in section 42.63 of the Stacks Project (locally the
spectrum of a Dedekind domain, a field being one; `δ = 0` at closed points and `1` elsewhere), and
let `X` be smooth over `S`, equidimensional of dimension `d`: every irreducible component of `X`
has δ-dimension `d`. Write `Θ : c ↦ c ∩ [X]_d`. Then

1. `Θ : A^p(X) ⟶ CH_{d-p}(X)` is bijective for every `p ∈ ℤ`;
2. if `d = e + 1`, then `Θ(a · b)|_{X₁} = Θ(a)|_{X₁} · Θ(b)|_{X₁}` on the open and closed part
   `X₁` of `X` over the one-dimensional part of `S`, the intersection product of section 42.64
   being formed with the Gysin class `Δ^!` of the diagonal of `X₁` (Stacks 0FBR); `X₁ = X` when
   `S` has no zero-dimensional component;
3. the second clause as printed fails over a field `k`: for `S = X = Spec k`, `d = 0`, one has
   `Θ(1 · 1) ≠ 0`, whereas the intersection product of section 42.64 vanishes on
   `CH_0(X) ⊗ CH_0(X)` for every class of the diagonal. -/
@[stacks 0FCB "the whole tag: Θ is bijective in every degree, for S as in section 42.63 (a field \
is a Dedekind domain, so field components are part of the source's hypothesis) and X smooth and \
equidimensional of dimension d (δ-dimension of every irreducible component); the second clause in \
corrected form, Θ(a · b) = Θ(a) · Θ(b) on the part X₁ of X over the one-dimensional part of S (all \
of X when S has no zero-dimensional component), with the product Δ^!(α × β) of section 42.64; and \
the formal counterexample to the second clause as printed, S = X = Spec k, where the exterior \
product of section 42.63 vanishes, also stated as \
`Stacks.Chow.not_chowCohomologyCapFundamentalClass_mulId_fieldChowSituation`"]
theorem chowCohomologyCapFundamentalClass_bijective_and_mulId (d : ℕ)
    (hd : ∀ V : irreducibleComponents X,
      deltaDimension C sX ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = d) :
    (∀ p : ℤ, Function.Bijective
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX d p)) ∧
    (∀ (e : ℕ) (hde : d = e + 1) (p q : ℤ)
      (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
      (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q),
      chowGroupRestrict C sX ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
          (hS.oneDimensionalPartPreimage sX).ι rfl ((e : ℤ) + 1 - (p + q))
          (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) (p + q)
            (a.mulId C sX b)) =
        chowGroupDegreeEquiv C ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
          (by ring : ((e : ℤ) + 1 - p) + ((e : ℤ) + 1 - q) - 1 - e = (e + 1) - (p + q))
          (chowGroupSelfProductUnitCollapse C ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
            (((e : ℤ) + 1 - p) + ((e : ℤ) + 1 - q) - 1 - e)
            (hS.intersectionProduct (gysinSystemOfInvertible C)
              ((hS.oneDimensionalPartPreimage sX).ι ≫ sX) (𝟙 _) (𝟙 _) e
              (bivariantClassCongrBase C (gysinSystemOfInvertible C)
                (pullback.diagonal ((hS.oneDimensionalPartPreimage sX).ι ≫ sX))
                (diagonal_comp_selfProductStructure C ((hS.oneDimensionalPartPreimage sX).ι ≫ sX))
                rfl e (diagonalGysinClass C ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
                  ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
                  (hS.relativeDimension_oneDimensionalPartPreimage sX e
                    (fun V ↦ (hd V).trans (by exact_mod_cast hde)))))
              ((e : ℤ) + 1 - p) ((e : ℤ) + 1 - q)
              (chowGroupCongr C (Category.id_comp _).symm ((e : ℤ) + 1 - p)
                (chowGroupRestrict C sX ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
                  (hS.oneDimensionalPartPreimage sX).ι rfl ((e : ℤ) + 1 - p)
                  (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) p a))
                ⊗ₜ[ℤ] chowGroupCongr C (Category.id_comp _).symm ((e : ℤ) + 1 - q)
                  (chowGroupRestrict C sX ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
                    (hS.oneDimensionalPartPreimage sX).ι rfl ((e : ℤ) + 1 - q)
                    (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) q
                      b)))))) ∧
    (∀ (k : Type u) [Field k],
      chowCohomologyCapFundamentalClass (fieldChowSituation k)
          (gysinSystemOfInvertible (fieldChowSituation k)) (𝟙 (fieldChowSituation k).S) 0 (0 + 0)
          ((bivariantIdentityClassOfInvertible (fieldChowSituation k)
            (𝟙 (fieldChowSituation k).S)).mulId (fieldChowSituation k)
            (𝟙 (fieldChowSituation k).S)
            (bivariantIdentityClassOfInvertible (fieldChowSituation k)
              (𝟙 (fieldChowSituation k).S))) ≠ 0 ∧
        ∀ (c : BivariantClass (fieldChowSituation k)
            (gysinSystemOfInvertible (fieldChowSituation k)) (𝟙 (fieldChowSituation k).S)
            (selfProductStructure (fieldChowSituation k) (𝟙 (fieldChowSituation k).S))
            (pullback.diagonal (𝟙 (fieldChowSituation k).S))
            (diagonal_comp_selfProductStructure (fieldChowSituation k)
              (𝟙 (fieldChowSituation k).S)) 0)
          (t : TensorProduct ℤ
            (chowGroup (fieldChowSituation k)
              (𝟙 (fieldChowSituation k).S ≫ 𝟙 (fieldChowSituation k).S) 0)
            (chowGroup (fieldChowSituation k)
              (𝟙 (fieldChowSituation k).S ≫ 𝟙 (fieldChowSituation k).S) 0)),
          (isDedekindChowBase_fieldChowSituation k).intersectionProduct
            (gysinSystemOfInvertible (fieldChowSituation k)) (𝟙 (fieldChowSituation k).S)
            (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) 0 c 0 0 t = 0) := by
  refine ⟨hS.chowCohomologyCapFundamentalClass_bijective_of_smooth_of_equidimensional sX d hd,
    fun e hde p q a b ↦ ?_,
    fun k _ ↦ not_chowCohomologyCapFundamentalClass_mulId_fieldChowSituation k⟩
  exact hS.chowGroupRestrict_chowCohomologyCapFundamentalClass_mulId sX e
    (fun V ↦ (hd V).trans (by exact_mod_cast hde)) p q a b

end Stacks.Chow.IsDedekindChowBase

end
