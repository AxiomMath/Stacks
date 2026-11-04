module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.HigherVanishing

/-!
# The convergence step of Stacks 072C

Let `f : U ⟶ X` be a surjective, étale and separated morphism of algebraic spaces over a scheme
`S` whose fibres are universally bounded, and let `ℱ` be an abelian sheaf on the spaces-étale
site of `X`.  The alternating Čech spectral sequence of [Stacks, Tag 0728] has first page
`E₁^{p,q} = Ext^q(K^p, ℱ)` and converges to `H^{p+q}(X, ℱ)`, and the fibre bound empties the
complement `W_{p+1}` of the diagonals in the `(p+1)`-fold self-product of `U` over `X` for `p`
above a degree `d`.

[Stacks, Tag 072B] kills the first page by making every row `q > 0` vanish, which needs the
quotients `U_p = W_{p+1}/S_{p+1}` affine and so needs `X` separated.  [Stacks, Tag 072C] instead
allows each *column* `p` its own degree `d_p` above which the row entries vanish — in the source
`d_p` comes from applying [Stacks, Tag 072B] to `U_p`, which is quasi-compact and separated even
when `X` is only quasi-separated — and concludes the vanishing of `H^n(X, ℱ)` for
`n ≥ max (d_p + p)`.  This file is that passage: the shape of the hypothesis is the one the
source's proof produces, and the conclusion is the source's bound.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isZero_koszulComplex_X_of_isEmpty_points`: the term `K^p`
  of the Koszul complex is a zero object when `W_{p+1}` has no points.
* `AlgebraicGeometry.Space.SpacesEtale.isZero_zExt_koszulComplex_X_of_isEmpty_points`: hence the
  whole column `p` of the first page vanishes there, in every degree `q`.
* `AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH_of_zExt_column_bounds`: **the convergence
  step of [Stacks, Tag 072C]** — column bounds `d_p` on the first page give the vanishing of
  `H^n(X, ℱ)` for `n ≥ max (d_p + p)`.
* `AlgebraicGeometry.Space.SpacesEtale.exists_forall_isZero_sheafH_of_exists_zExt_column_bounds`:
  the same read uniformly in `ℱ` over a class of coefficient sheaves, which is the form
  [Stacks, Tag 072C] states — a single degree for every quasi-coherent module at once.

## Implementation notes

**What the column bound replaces.**  The hypothesis `hUpVanishing` of
`AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH_of_isEmpty_diagonalComplement` asks the rows
`q > 0` of the first page to vanish *everywhere*; that is the separated case, and it is why that
declaration concludes at the fibre bound `d` of the chart.  Here the hypothesis is asked only in
the columns `p` below the fibre bound, and only above a degree `d_p` depending on `p`; the
columns at or above the fibre bound are discharged outright, because there `K^p` is a zero
object.

**Why the column above the bound vanishes entirely.**  The emptiness of `W_{p+1}` gives the
vanishing of the *sections* of any abelian sheaf over it, which is only the row `q = 0`.  What
makes the whole column vanish is that `K^p` is then a zero object: by [Stacks, Tag 0726] —
`AlgebraicGeometry.Space.SpacesEtale.koszulHomSignSectionsEquiv` — the group `Hom(K^p, 𝒢)` is a
subgroup of the sections of `𝒢` over `W_{p+1}`, so taking `𝒢 = K^p` makes the identity of `K^p`
zero.  `Ext` out of a zero object vanishes in every degree, including the negative ones.

**The uniform form.**  The source's conclusion is a single degree `N` serving every
quasi-coherent `ℱ`, so the column bounds must be chosen before the sheaf.  That is the shape of
`exists_forall_isZero_sheafH_of_exists_zExt_column_bounds`, whose predicate `P` on coefficient
sheaves is quasi-coherence in the intended application; `N` is the supremum of `d_p + p` over
the finitely many columns `p` below the fibre bound, which is where the finiteness of the bound
is used a second time.

## References

* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Abelian

/-- **`Ext` out of a zero object vanishes in every degree.**  The degree-`i` extension group is a
group of morphisms out of the image of the source under the degree-zero inclusion of the abelian
category into its derived category, and that functor is additive. -/
theorem subsingleton_zExt_of_isZero {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory C] {A : C} (hA : IsZero A) (Y : C) (i : ℤ) :
    Subsingleton (Abelian.zExt A Y i) :=
  ⟨fun f g => ((DerivedCategory.singleFunctor C 0).map_isZero hA).eq_of_src f g⟩

end CategoryTheory.Abelian

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The term `K^p` of the Koszul complex is a zero object when `W_{p+1}` has no points.**  By
[Stacks, Tag 0726] the group `Hom(K^p, 𝒢)` is the group of `S_{p+1}`-anti-invariant sections of
`𝒢` over `W_{p+1}`, a subgroup of the sections of `𝒢` over `W_{p+1}`; those sections are zero
when `W_{p+1}` has no points, and taking `𝒢 = K^p` makes the identity of `K^p` zero. -/
theorem isZero_koszulComplex_X_of_isEmpty_points (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.obj.hom.hom)
    (hW : IsEmpty (points B S hS
      (underlying B S hS X (diagonalComplement B S hS X U (p + 1) hsep)).1)) :
    IsZero ((koszulComplex B S hS X U).X p) := by
  have hsub : Subsingleton (ToType (((koszulComplex B S hS X U).X p).obj.obj
      (op (diagonalComplement B S hS X U (p + 1) hsep)))) :=
    AddCommGrpCat.subsingleton_of_isZero (isZero_obj_diagonalComplement_of_isEmpty_points
      B S hS X U (p + 1) hsep _ hW)
  rw [IsZero.iff_id_eq_zero]
  refine (koszulHomSignSectionsEquiv B S hS X U p hsep
    ((koszulComplex B S hS X U).X p)).injective ?_
  exact Subtype.val_injective.subsingleton.elim _ _

/-- **The column `p` of the first page of [Stacks, Tag 0728] vanishes in every degree when
`W_{p+1}` has no points.**  The term `K^p` is then a zero object, and `Ext` out of a zero object
vanishes. -/
theorem isZero_zExt_koszulComplex_X_of_isEmpty_points (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.obj.hom.hom)
    (hW : IsEmpty (points B S hS
      (underlying B S hS X (diagonalComplement B S hS X U (p + 1) hsep)).1))
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (q : ℤ) :
    IsZero (AddCommGrpCat.of (Abelian.zExt ((koszulComplex B S hS X U).X p) F q)) :=
  have := Abelian.subsingleton_zExt_of_isZero
    (isZero_koszulComplex_X_of_isEmpty_points B S hS X U p hsep hW) F q
  AddCommGrpCat.isZero_of_subsingleton _

/-- **The convergence step of [Stacks, Tag 072C].**  Let `c : W ⟶ X` be a surjective, étale and
separated chart, let `d` be a degree above which the complements `W_m` of the diagonals have no
points, and suppose that for each column `p < d` the entries of the first page of the alternating
Čech spectral sequence of [Stacks, Tag 0728] vanish in the degrees `q ≥ d_p`.  Then
`H^n(X, ℱ) = 0` for every `n` dominating all the sums `d_p + p`.

This is the source's argument for Tag 072C.  The columns `p ≥ d` are discharged outright: there
`K^p` is a zero object.  The columns `p < d` are where the source applies [Stacks, Tag 072B] to
the quotient `U_p = W_p/S_{p+1}`, which is quasi-compact and separated even when `X` is only
quasi-separated; that application is what the hypothesis `hcol` stands for. -/
theorem isZero_sheafH_of_zExt_column_bounds (W : BigFppfOver B S hS)
    (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsurj : IsSurjective B S hS c) (hsep : IsSeparated B S hS c) (d : ℕ)
    (hd : ∀ m : ℕ, d < m → IsEmpty (points B S hS (underlying B S hS X
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) m hsep)).1))
    (e : ℕ → ℕ) (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (hcol : ∀ (p : ℕ) (q : ℤ), p < d → (e p : ℤ) ≤ q →
      IsZero (AddCommGrpCat.of (Abelian.zExt
        ((koszulComplex B S hS X (chartObj B S hS X W c hc)).X p) F q)))
    (n : ℕ) (hn : ∀ p : ℕ, p < d → e p + p ≤ n) :
    IsZero (AddCommGrpCat.of (Sheaf.H F n)) := by
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
  rcases lt_or_ge p d with hpd | hpd
  · refine IsZero.of_iso (hcol p q hpd ?_) (hE p q).some
    have := hn p hpd
    omega
  · exact IsZero.of_iso (isZero_zExt_koszulComplex_X_of_isEmpty_points B S hS X
      (chartObj B S hS X W c hc) p hsep (hd (p + 1) (by omega)) F q) (hE p q).some

/-- **[Stacks, Tag 072C] from column bounds on the first page, uniformly in the coefficients.**
If every column `p` of the first page of the alternating Čech spectral sequence of
[Stacks, Tag 0728] has a degree `d_p` above which it vanishes for every coefficient sheaf in a
class `P`, then there is a single degree `N` beyond which `H^n(X, ℱ) = 0` for every `ℱ` in `P`.

This is the shape in which [Stacks, Tag 072C] states its conclusion, with `P` quasi-coherence;
`N` is the supremum of `d_p + p` over the finitely many columns below the fibre bound of the
chart, which is the source's `max (d_p + p)`. -/
theorem exists_forall_isZero_sheafH_of_exists_zExt_column_bounds (W : BigFppfOver B S hS)
    (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsurj : IsSurjective B S hS c) (hsep : IsSeparated B S hS c)
    (hbound : HasUniversallyBoundedFibers B S hS W c)
    (P : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1} → Prop)
    (hcol : ∀ p : ℕ, ∃ ep : ℕ, ∀ F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1},
      P F → ∀ q : ℤ, (ep : ℤ) ≤ q →
        IsZero (AddCommGrpCat.of (Abelian.zExt
          ((koszulComplex B S hS X (chartObj B S hS X W c hc)).X p) F q))) :
    ∃ N : ℕ, ∀ F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1},
      P F → ∀ n : ℕ, N ≤ n → IsZero (AddCommGrpCat.of (Sheaf.H F n)) := by
  obtain ⟨d, hd⟩ := exists_forall_isEmpty_points_diagonalComplement B S hS X W c hc hsep hbound
  choose e he using hcol
  refine ⟨(Finset.range d).sup fun p => e p + p, fun F hF n hn => ?_⟩
  refine isZero_sheafH_of_zExt_column_bounds B S hS X W c hc hsurj hsep d hd e F
    (fun p q hpd hq => he p F hF q hq) n fun p hpd => le_trans ?_ hn
  exact Finset.le_sup (f := fun p => e p + p) (Finset.mem_range.2 hpd)

end AlgebraicGeometry.Space.SpacesEtale

end
