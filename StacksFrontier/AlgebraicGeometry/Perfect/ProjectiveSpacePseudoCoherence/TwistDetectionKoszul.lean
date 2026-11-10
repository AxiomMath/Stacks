module

public import StacksFrontier.AlgebraicGeometry.ProjKoszulOverBase.ComplexOverBase
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Trace
public import StacksFrontier.Homology.CyclesShortComplex
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Vanishing against the twists `𝒪, 𝒪(1), …, 𝒪(n)` propagates to every nonnegative twist

Let `S` be a scheme and `ℙⁿ_S` projective space over it. For every integer `a` the Koszul
complex of the coordinates

`0 ⟶ 𝒪(a) ⟶ 𝒪(a+1)^{⊕ binom(n+1,1)} ⟶ ⋯ ⟶ 𝒪(a+n+1) ⟶ 0`

is exact ([Stacks, Tag 0BQS]). Splicing it into the short exact sequences of its cycles shows
that any property of modules on `ℙⁿ_S` which is invariant under isomorphism, holds for finite
direct sums of modules having it, and passes from the first two terms of a short exact sequence to
the third, holds for `𝒪(a + n + 1)` as soon as it holds for `𝒪(a), …, 𝒪(a + n)`. By induction it
then holds for every `𝒪(d)`, `d ≥ 0`, once it holds for `𝒪, 𝒪(1), …, 𝒪(n)`.

The property of interest is the vanishing, in all degrees at least `m`, of the cohomology of the
image of a module under an exact functor out of `D(𝒪_{ℙⁿ_S})` — in the application,
`M ↦ RΓ(ℙⁿ_S, K ⊗^𝐋 M)` for a fixed object `K`. Such a property passes along a short exact
sequence because the sequence gives a distinguished triangle in the derived category, and an
exact functor followed by cohomology turns it into a long exact sequence.

## Main results

* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.twist_of_koszul`: one step of the
  propagation along the Koszul complex.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.twist_of_window`: the propagation from
  `𝒪, …, 𝒪(n)` to every `𝒪(d)`, `d ≥ 0`.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.isZero_homology_obj_twist_of_window`: the
  same for the vanishing of cohomology in degrees at least `m` after an exact functor.

## References

* [Stacks Project, Tag 0BQS](https://stacks.math.columbia.edu/tag/0BQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe w u v

namespace AlgebraicGeometry.ProjectiveSpacePseudoCoherence

open Stacks.AlgebraicGeometry.ProjKoszulComplex (koszulFamily koszulIndex)
open Stacks.AlgebraicGeometry.ProjKoszulOverBase (koszulOver toProj)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (S : Scheme.{u})

section Abstract

variable {n S} (V : (projectiveSpaceOver n S).Modules → Prop)
  (hiso : ∀ {M N : (projectiveSpaceOver n S).Modules}, (M ≅ N) → V M → V N)
  (hzero : ∀ M : (projectiveSpaceOver n S).Modules, IsZero M → V M)
  (hsum : ∀ (a j : ℤ),
    V (twistOver n S (a + j)) → V ((koszulOver n S a).X j))
  (hses : ∀ T : ShortComplex (projectiveSpaceOver n S).Modules, T.ShortExact →
    V T.X₁ → V T.X₂ → V T.X₃)

include hiso hzero hsum hses in
/-- **One step of the propagation along the Koszul complex.** If a property `V` of modules on
`ℙⁿ_S` is invariant under isomorphism, holds for zero modules, holds for every term of the
Koszul complex whose summands `𝒪(a + j)` have it, and passes from the first two terms of a short
exact sequence to the third, then `V` holds for `𝒪(a + n + 1)` as soon as it holds for
`𝒪(a), …, 𝒪(a + n)`.

The cycles `Z^j` of the Koszul complex `K^•` with `K^0 = 𝒪(a)` sit in short exact sequences
`0 ⟶ Z^j ⟶ K^j ⟶ Z^{j+1} ⟶ 0`, the complex being exact. `Z^0 = 0`, so induction on `j` gives `V`
for `Z^{n+1}`, which is the whole of the top term `K^{n+1} = 𝒪(a + n + 1)`, the differential out
of that term being zero. -/
theorem twist_of_koszul (a : ℤ) (h : ∀ e : ℤ, a ≤ e → e ≤ a + n → V (twistOver n S e)) :
    V (twistOver n S (a + n + 1)) := by
  set Kz := koszulOver n S a
  -- the cycles in degree `j` have `V`, for `0 ≤ j ≤ n + 1`
  have hcyc : ∀ j : ℕ, j ≤ n + 1 → V (Kz.cycles (j : ℤ)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine hzero _ ?_
      have hS := Kz.cyclesShortComplex_shortExact
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
        (Stacks.AlgebraicGeometry.ProjKoszulOverBase.acyclic_koszulOver n S a 0)
      have : Epi (Kz.toCycles (-1) 0) := hS.epi_g
      exact IsZero.of_epi (Kz.toCycles (-1) 0)
        (Stacks.AlgebraicGeometry.ProjKoszulOverBase.isZero_koszulOver_X n S a (-1)
          (Or.inl (by norm_num)))
    | succ j ih =>
      intro hj
      have hS := Kz.cyclesShortComplex_shortExact
        (show (ComplexShape.up ℤ).Rel (j : ℤ) ((j + 1 : ℕ) : ℤ) by simp)
        (Stacks.AlgebraicGeometry.ProjKoszulOverBase.acyclic_koszulOver n S a _)
      exact hses _ hS (ih (by omega)) (hsum a j (h _ (by omega) (by omega)))
  -- the top cycles are the top term
  have htop : Kz.cycles ((n + 1 : ℕ) : ℤ) ≅ Kz.X ((n + 1 : ℕ) : ℤ) :=
    Kz.iCyclesIso ((n + 1 : ℕ) : ℤ) ((n + 1 : ℕ) + 1 : ℤ)
      ((ComplexShape.up ℤ).next_eq' rfl)
      ((Stacks.AlgebraicGeometry.ProjKoszulOverBase.isZero_koszulOver_X n S a _
        (Or.inr (by push_cast; omega))).eq_of_tgt _ _)
  -- the top term is a direct sum over a single index, so `V` for it is `V` for the twist
  have e : Kz.X ((n + 1 : ℕ) : ℤ) ≅ twistOver n S (a + n + 1) :=
    (Scheme.Modules.pullback (toProj n S)).mapIso
      (biproductUniqueIso (koszulFamily (ULift.{u} ℤ) n a ((n : ℤ) + 1))) ≪≫
      eqToIso (congrArg (twistOver n S) (by ring))
  exact hiso e (hiso htop (hcyc (n + 1) le_rfl))

include hiso hzero hsum hses in
/-- **The propagation from `𝒪, 𝒪(1), …, 𝒪(n)` to every nonnegative twist.** Under the hypotheses
of `twist_of_koszul`, a property holding for the twists `𝒪(d)` with `0 ≤ d ≤ n` holds for every
`𝒪(d)` with `d ≥ 0`: by strong induction, `𝒪(d)` for `d > n` is reached from the window
`𝒪(d - n - 1), …, 𝒪(d - 1)` by one step along the Koszul complex. -/
theorem twist_of_window (h : ∀ d : ℕ, d ≤ n → V (twistOver n S d)) :
    ∀ d : ℕ, V (twistOver n S d) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    by_cases hd : d ≤ n
    · exact h d hd
    · exact hiso (eqToIso (congrArg (twistOver n S) (by ring)))
        (twist_of_koszul V hiso hzero hsum hses ((d : ℤ) - n - 1) fun e he₁ he₂ => by
          lift e to ℕ using (by omega)
          exact ih e (by omega))

end Abstract

section Exact

variable {n S} {B : Type v} [Category.{w} B] [Abelian B] [HasDerivedCategory B]
  [HasDerivedCategory (projectiveSpaceOver n S).Modules]
  (F : DerivedCategory (projectiveSpaceOver n S).Modules ⥤ DerivedCategory B)
  [F.CommShift ℤ] [F.IsTriangulated]

/-- **Vanishing of cohomology in degrees at least `m` after an exact functor propagates from
`𝒪, 𝒪(1), …, 𝒪(n)` to every nonnegative twist.** For an exact functor
`F : D(𝒪_{ℙⁿ_S}) ⥤ D(B)` into the derived category of an abelian category, if the cohomology of
`F(𝒪(d)[0])` vanishes in every degree at least `m` for `0 ≤ d ≤ n`, then it does so for every
`d ≥ 0`. -/
theorem isZero_homology_obj_twist_of_window (m : ℤ)
    (h : ∀ d : ℕ, d ≤ n → ∀ i : ℤ, m ≤ i → IsZero ((DerivedCategory.homologyFunctor B i).obj
      (F.obj ((DerivedCategory.singleFunctor _ 0).obj (twistOver n S d))))) :
    ∀ d : ℕ, ∀ i : ℤ, m ≤ i → IsZero ((DerivedCategory.homologyFunctor B i).obj
      (F.obj ((DerivedCategory.singleFunctor _ 0).obj (twistOver n S d)))) := by
  let V : (projectiveSpaceOver n S).Modules → Prop := fun M => ∀ i : ℤ, m ≤ i →
    IsZero ((DerivedCategory.homologyFunctor B i).obj
      (F.obj ((DerivedCategory.singleFunctor _ 0).obj M)))
  refine twist_of_window V ?_ ?_ ?_ ?_ h
  · intro M N e hM i hi
    exact (hM i hi).of_iso ((DerivedCategory.homologyFunctor B i).mapIso
      (F.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e))).symm
  · intro M hM i _
    exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ hM))
  · intro a j hV i hi
    let G : (projectiveSpaceOver n S).Modules ⥤ B :=
      DerivedCategory.singleFunctor _ 0 ⋙ F ⋙ DerivedCategory.homologyFunctor B i
    have : G.Additive := by
      dsimp only [G]
      infer_instance
    have : HasFiniteBiproducts B := HasFiniteBiproducts.of_hasFiniteProducts
    change IsZero (G.obj _)
    exact Functor.isZero_obj_biproduct
      (Scheme.Modules.pullback (toProj n S) ⋙ G)
      (koszulFamily (ULift.{u} ℤ) n a j) fun _ => hV i hi
  · intro T hT hV₁ hV₂ i hi
    exact (DerivedCategory.HomologySequence.exact₃ _
        (F.map_distinguished _ hT.singleTriangle_distinguished) i (i + 1)).isZero_of_both_zeros
      ((hV₂ i hi).eq_of_src _ _) ((hV₁ (i + 1) (by omega)).eq_of_tgt _ _)

end Exact

end AlgebraicGeometry.ProjectiveSpacePseudoCoherence

end
