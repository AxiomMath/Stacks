module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.ExtSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementDistinct

/-!
# Higher vanishing for quasi-coherent sheaves on a quasi-compact separated algebraic space

Let `X` be a quasi-compact and separated algebraic space over a scheme `S`, let `f : U → X` be a
surjective, étale and separated morphism with `U` affine, and let `d` bound the degrees of the
fibres of `f`.  [Stacks, Tag 072B] asserts that `H^n(X, ℱ) = 0` for `n ≥ d` and every
quasi-coherent `𝒪_X`-module `ℱ`.  The alternating Čech spectral sequence of [Stacks, Tag 0728]
has first page `E₁^{p,q} = H^q(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))`, for `U_p = W_p/S_{p+1}` the quotient
of the complement `W_p` of the diagonals in the `(p+1)`-fold self-product of `U` over `X`, and
converges to `H^{p+q}(X, ℱ)`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isZero_obj_diagonalComplement_of_isEmpty_points`: an
  abelian sheaf has no nonzero sections over `W_p` when `W_p` has no points.
* `AlgebraicGeometry.Space.SpacesEtale.exists_forall_isZero_sheafH_of_isEmpty_diagonalComplement`:
  the vanishing above the fibre bound of the chart, read uniformly in `ℱ`, the degree depending
  only on the chart.
* `AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH_of_isEmpty_diagonalComplement`:
  **[Stacks, Tag 072B]**, the vanishing `H^n(X, ℱ) = 0` above the fibre bound of the chart.

## Implementation notes

**The one input the library does not have.**  The first page of [Stacks, Tag 0728] is available
only in the row `q = 0`, as the group of `S_{p+1}`-anti-invariant sections of `ℱ` over `W_p`
(`AlgebraicGeometry.Space.SpacesEtale.exists_alternatingCechSignTwistedSpectralSequence`); the
higher rows are its `Ext` groups `Ext^q(K^p, ℱ)`, the identification with the cohomology of the
quotient `U_p` needing that quotient, which rests on [Stacks, Tag 071S] for a free action of a
finite group on an algebraic space.  Their vanishing for `q > 0` — the conjunction of the
affineness of `U_p`, of [Stacks, Tag 072A] and of [Stacks, Tag 01XB] — is the binder
`hUpVanishing`, in the `Ext` spelling the library's first page has.

**The form of the fibre bound.**  The source states the bound `d` as an upper bound for the size
of the fibres of `|U| → |X|`, but what its proof uses is the emptiness of `W_p` for `p ≥ d`, and
that follows from the *degree* bound of [Stacks, Tag 03JL] and not from a bound on the
cardinality of the topological fibres: over `X = Spec k` with `U = Spec k'` for a separable
quadratic extension `k'/k` the map `|U| → |X|` is a bijection while `W_1 = U ×_X U ∖ Δ` is
nonempty.  The fibre bound is therefore taken in the degree form, as
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers` on an étale chart `c : W ⟶ X`, and the
emptiness of `W_p` above it is proved from that by
`AlgebraicGeometry.Space.SpacesEtale.exists_forall_isEmpty_points_diagonalComplement`; the
degree is existentially quantified because that predicate hides its own bound.

## References

* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 072A](https://stacks.math.columbia.edu/tag/072A)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

/-- **A sheaf has a zero group of sections over an object covered by the empty sieve.** -/
theorem isZero_obj_of_bot_mem {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {A : Type*} [Category A] [Preadditive A] (F : Sheaf J A) {V : C}
    (hV : (⊥ : Sieve V) ∈ J V) : IsZero (F.obj.obj (op V)) := by
  rw [IsZero.iff_id_eq_zero]
  obtain ⟨_, -, hu⟩ := F.property (F.obj.obj (op V)) (⊥ : Sieve V) hV
    (fun _ _ hf => hf.elim) (fun _ _ _ _ _ _ _ h₁ => h₁.elim)
  exact (hu _ fun _ _ hf => hf.elim).trans (hu _ fun _ _ hf => hf.elim).symm

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The sections of an abelian sheaf on the spaces-étale site of `X` over the complement `W` of
the diagonals in `U^n` form the zero group when `W` has no points. -/
theorem isZero_obj_diagonalComplement_of_isEmpty_points (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (hW : IsEmpty (points B S hS
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1)) :
    IsZero (F.obj.obj (op (diagonalComplement B S hS X U n hsep))) :=
  Sheaf.isZero_obj_of_bot_mem F
    (bot_mem_topology_of_isEmpty_points B S hS X (diagonalComplement B S hS X U n hsep) hW)

/-- The vanishing of [Stacks, Tag 072B] read uniformly in the coefficient sheaf: the degree
beyond which the cohomology vanishes depends only on the chart, not on the sheaf. -/
theorem exists_forall_isZero_sheafH_of_isEmpty_diagonalComplement (W : BigFppfOver B S hS)
    (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsurj : IsSurjective B S hS c) (hsep : IsSeparated B S hS c)
    (hbound : HasUniversallyBoundedFibers B S hS W c) :
    ∃ N : ℕ, ∀ F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1},
      (∀ (p : ℕ) (q : ℤ), 0 < q →
        IsZero (AddCommGrpCat.of (Abelian.zExt
          ((koszulComplex B S hS X (chartObj B S hS X W c hc)).X p) F q))) →
      ∀ n : ℕ, N ≤ n → IsZero (AddCommGrpCat.of (Sheaf.H F n)) := by
  obtain ⟨d, hd⟩ := exists_forall_isEmpty_points_diagonalComplement B S hS X W c hc hsep hbound
  refine ⟨d, fun F hUpVanishing n hn ↦ ?_⟩
  obtain ⟨E, hE, hrow, hvanish, hAbuts, hH⟩ :=
    exists_alternatingCechSignTwistedSpectralSequence B S hS X
      (chartObj B S hS X W c hc) hsurj hsep F
  refine IsZero.of_iso (hAbuts.isZero_of_isZero_page (r := 1) le_rfl (n : ℤ) ?_) (hH n).some
  intro p q hpq
  rcases lt_or_ge p 0 with hp | hp
  · exact hvanish p q (Or.inl hp)
  rcases lt_or_ge q 0 with hq | hq
  · exact hvanish p q (Or.inr hq)
  lift p to ℕ using hp with p
  rcases hq.lt_or_eq with hq0 | hq0
  · exact IsZero.of_iso (hUpVanishing p q hq0) (hE p q).some
  · have hpn : p = n := by omega
    subst hq0
    have hsub : Subsingleton (ToType (F.obj.obj
        (op (diagonalComplement B S hS X (chartObj B S hS X W c hc) (p + 1) hsep)))) :=
      AddCommGrpCat.subsingleton_of_isZero (isZero_obj_diagonalComplement_of_isEmpty_points
        B S hS X (chartObj B S hS X W c hc) (p + 1) hsep F (hd (p + 1) (by omega)))
    have : Subsingleton (ToType ((E.page 1).X ((p : ℤ), 0))) :=
      ((hrow p).some.toEquiv).subsingleton
    exact AddCommGrpCat.isZero_of_subsingleton _

/-- Let `S` be a scheme, let `X` be an algebraic space over `S` and let `c : W ⟶ X` be a
surjective, étale and separated morphism from a scheme whose fibres are universally bounded in the
sense of [Stacks, Tag 03JL].  If the rows `q > 0` of the first page of the alternating Čech
spectral sequence of [Stacks, Tag 0728] vanish, then `H^n(X, ℱ) = 0` above the fibre bound of
`c`. -/
@[stacks 072B "the vanishing H^n(X, F) = 0 above the fibre bound of the chart. The bound used \
is the degree bound of Stacks 03JL on the fibres of the chart, which is what empties W_p and \
so what the source's proof uses, rather than the source's stated bound on the cardinality of \
the topological fibres of the chart; the degree is existentially quantified because the \
predicate of Stacks 03JL hides its own bound, and the emptiness of W_p above it is proved \
here. What the source draws from the quasi-compactness and separatedness of X and the \
affineness of the chart is the vanishing of the rows q > 0 of the E_1-page of Stacks 0728; \
that rests on the affineness of the quotients U_p = W_p/S_{p+1}, hence on Stacks 071S for a \
free action of a finite group on an arbitrary algebraic space, which this subtree does not \
state in any shape, and it is the binder hUpVanishing"]
theorem isZero_sheafH_of_isEmpty_diagonalComplement (W : BigFppfOver B S hS)
    (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsurj : IsSurjective B S hS c) (hsep : IsSeparated B S hS c)
    (hbound : HasUniversallyBoundedFibers B S hS W c)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (hUpVanishing : ∀ (p : ℕ) (q : ℤ), 0 < q →
      IsZero (AddCommGrpCat.of (Abelian.zExt
        ((koszulComplex B S hS X (chartObj B S hS X W c hc)).X p) F q))) :
    ∃ d : ℕ, ∀ n : ℕ, d ≤ n → IsZero (AddCommGrpCat.of (Sheaf.H F n)) := by
  obtain ⟨N, hN⟩ := exists_forall_isZero_sheafH_of_isEmpty_diagonalComplement B S hS X W c hc
    hsurj hsep hbound
  exact ⟨N, fun n hn ↦ hN F hUpVanishing n hn⟩

end AlgebraicGeometry.Space.SpacesEtale

end
