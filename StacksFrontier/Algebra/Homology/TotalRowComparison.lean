module

public import StacksFrontier.Algebra.Homology.TotalDegeneration

/-!
# Degeneration of a first-quadrant double complex by a rowwise *comparison*

`StacksFrontier/Algebra/Homology/TotalDegeneration.lean` degenerates a first-quadrant double
complex `Z^{•,•}` in the row direction from the hypothesis that the rows off `0` are **acyclic**.
That hypothesis is too strong for the use the proof of [Stacks, Proposition 60.21.3, Tag 07LG]
makes of it: there the clause of [Stacks, Lemma 60.21.2, Tag 07LD] makes each row only
*quasi-isomorphic* to the row `0`, and the rows off `0` are genuinely not acyclic — see
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialDeRhamRowObstruction.lean`,
which proves that assuming their acyclicity forces `p` to be invertible.

This module runs the degeneration from a *comparison* instead.  The input is a morphism of double
complexes `φ : Z ⟶ Z'` which is a quasi-isomorphism on every row, together with the information
that `Z'` is **constant in the row direction** in the homological sense: each of its columns is a
resolution of its own degree-`0` term, i.e. exact off `0` with vanishing differential out of `0`.
The conclusion is that the row `0` of `Z` and the column `0` of `Z` have the same cohomology,
which is what the two spectral sequences of the source are used for.

## How it is proved

Three steps, none of them a spectral sequence.

* `rowZero_quasiIso_total`: when every column of `Z'` is exact off `0` and its differential out of
  degree `0` vanishes, each column is a resolution of its degree-`0` term, so [Stacks, Tag 0133]
  in the form `quasiIso_total_of_resolution` — applied to the identity of `rowZero Z'` — makes the
  canonical map `Z'^{•,0} ⟶ Tot(Z'^{•,•})` a quasi-isomorphism.  The kernel clause of
  `Hypotheses` is satisfied because a vanishing differential has the whole object as its kernel.
* `quasiIso_total_map_flip` and `totalHomologyIsoOfRows`: [Stacks, Tag 0133] is stated columnwise,
  so the rowwise hypothesis is fed to it through `HomologicalComplex₂.flip`, and the resulting
  quasi-isomorphism of the total complexes of the flips is transported back along
  `HomologicalComplex₂.totalFlipIso`, on cohomology.
* `StacksDraft.TotalDegeneration.totalHomologyIsoColumnZero` is the column degeneration, already
  available.

## Main results

* `StacksDraft.TotalRowComparison.quasiIso_total_map_flip` — **[Stacks, Tag 0133] rowwise**: a
  morphism of first-quadrant double complexes which is a quasi-isomorphism on every row is a
  quasi-isomorphism on the total complexes of the flips.
* `StacksDraft.TotalRowComparison.totalHomologyIsoOfRows` — hence an isomorphism on the cohomology
  of the total complexes themselves.
* `StacksDraft.TotalRowComparison.rowZeroHomologyIsoTotal` — **a first-quadrant double complex
  whose columns resolve their degree-`0` terms has the cohomology of its row `0`.**
* `StacksDraft.TotalRowComparison.rowZeroHomologyIsoColumnZero_of_rowComparison` — **the
  replacement for the second spectral sequence**: with the columns of `Z` off `0` acyclic and a
  rowwise quasi-isomorphism from `Z` to such a `Z'`, the cohomology of the row `0` of `Z` is the
  cohomology of its column `0`.

No tag attribute is placed: this is a degeneration of [Stacks, Tag 0130] and is not itself the
content of a tag.

## References

* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.TotalRowComparison

open StacksDraft.TotalComplexQuasiIso StacksDraft.TotalDegeneration

variable {A : Type u} [Category.{v} A] [Abelian A]

/-! ### The row `0` as the flip in degree `0` -/

/-- The row `0` of a double complex, in the two spellings the two files use for it: `rowZero Z`,
the complex `p ↦ Z^{p,0}` with the first differential, is `Z.flip.X 0`. -/
public theorem rowZero_eq_flip_X_zero
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    rowZero Z = Z.flip.X 0 := rfl

/-- **A first-quadrant double complex has finite diagonals.**  On the antidiagonal of `n` only the
indices `p` with `a ≤ p ≤ n` can carry a nonzero term: below `a` the whole column vanishes, and
above `n` the second index `n - p` is negative. -/
public theorem diagonalFinite_of_bounded
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ)
    (hq : ∀ p q : ℤ, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p : ℤ, p < a → IsZero (Z.X p)) :
    DiagonalFinite Z := by
  intro n
  refine (Set.finite_Icc a n).subset (fun p hp' => ⟨?_, ?_⟩)
  · by_contra hlt
    exact hp' (Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) (n - p))
      (hp p (by omega)))
  · by_contra hgt
    exact hp' (hq p (n - p) (by omega))

/-- A differential that vanishes in an isomorphic complex vanishes: the two are conjugate by the
isomorphism, which is invertible in each degree. -/
public theorem d_eq_zero_of_iso {K L : CochainComplex A ℤ} (e : K ≅ L) (i j : ℤ)
    (h : L.d i j = 0) : K.d i j = 0 := by
  have hj : IsIso (e.hom.f j) :=
    ((HomologicalComplex.eval A (ComplexShape.up ℤ) j).mapIso e).isIso_hom
  have hcomm := e.hom.comm i j
  rw [h, comp_zero] at hcomm
  exact (cancel_mono (e.hom.f j)).1 (hcomm.symm.trans zero_comp.symm)

/-! ### The flip of a morphism of double complexes -/

/-- **The flip of a morphism of double complexes**, `Mathlib`'s
`HomologicalComplex₂.flipFunctor` read with its source and target spelled as
`HomologicalComplex₂.flip` rather than as the functor applied to them, which is what the
`HasTotal` instance of the flip is stated about. -/
public abbrev flipMap {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (φ : Z ⟶ Z') : Z.flip ⟶ Z'.flip :=
  (HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map φ

/-- The flip of a morphism in the row `q` is the morphism read in that row. -/
@[simp] public theorem flipMap_f_f
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (φ : Z ⟶ Z')
    (q p : ℤ) : ((flipMap φ).f q).f p = (φ.f p).f q := rfl

/-! ### The rowwise form of [Stacks, Tag 0133] -/

/-- **[Stacks, Tag 0133] rowwise**, at the flips: a morphism of first-quadrant double complexes
which is a quasi-isomorphism on every *row* is a quasi-isomorphism on the total complexes of the
flips.

`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map` is stated columnwise — its first index is
the one the columns are indexed by — so the rowwise hypothesis is fed to it at the flips, where
the rows of `Z` are the columns. -/
public theorem quasiIso_total_map_flip
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (φ : Z ⟶ Z')
    [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)]
    (hq : ∀ p q : ℤ, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p : ℤ, p < 0 → IsZero (Z.X p))
    (hq' : ∀ p q : ℤ, q < 0 → IsZero ((Z'.X p).X q)) (hp' : ∀ p : ℤ, p < 0 → IsZero (Z'.X p))
    (hrow : ∀ q : ℤ, QuasiIso ((flipMap φ).f q)) :
    QuasiIso (HomologicalComplex₂.total.map (flipMap φ) (ComplexShape.up ℤ)) :=
  quasiIso_total_map _ 0 (isZero_flip_X_X_of_neg Z hp) (isZero_flip_X_of_neg Z hq)
    (isZero_flip_X_X_of_neg Z' hp') (isZero_flip_X_of_neg Z' hq') hrow

/-- **A morphism of first-quadrant double complexes which is a quasi-isomorphism on every row
induces an isomorphism on the cohomology of the total complexes.**

The comparison is made at the flips, where the rows are the columns and
`StacksDraft.TotalRowComparison.quasiIso_total_map_flip` applies, and
`HomologicalComplex₂.totalFlipIso` identifies the total complex of each flip with the total
complex itself.

The conclusion is an isomorphism of cohomology rather than a quasi-isomorphism
`Tot(Z) ⟶ Tot(Z')`, because the latter would be the statement that
`HomologicalComplex₂.totalFlipIso` is *natural* in the double complex, which Mathlib states only
for the total complex of a bifunctor (`HomologicalComplex.mapBifunctorFlipIso_hom_naturality`).
For a bicomplex the two sides of that square are typed by `(Z.flip.X q).X p` on one side and by
`(Z.X p).X q` on the other, so even writing it down needs the relaxed transparency that Mathlib's
own `HomologicalComplex₂.ιTotal_totalFlipIso_f_hom` carries.  Nothing downstream needs more than
the isomorphism. -/
public def totalHomologyIsoOfRows
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (φ : Z ⟶ Z')
    [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)]
    (hq : ∀ p q : ℤ, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p : ℤ, p < 0 → IsZero (Z.X p))
    (hq' : ∀ p q : ℤ, q < 0 → IsZero ((Z'.X p).X q)) (hp' : ∀ p : ℤ, p < 0 → IsZero (Z'.X p))
    (hrow : ∀ q : ℤ, QuasiIso ((flipMap φ).f q)) (n : ℤ) :
    (Z.total (ComplexShape.up ℤ)).homology n ≅ (Z'.total (ComplexShape.up ℤ)).homology n :=
  have hflip : QuasiIso (HomologicalComplex₂.total.map (flipMap φ) (ComplexShape.up ℤ)) :=
    quasiIso_total_map_flip φ hq hp hq' hp' hrow
  have : IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (flipMap φ) (ComplexShape.up ℤ)) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 (hflip.quasiIsoAt n)
  ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).mapIso
        (Z.totalFlipIso (ComplexShape.up ℤ))).symm.trans
    ((asIso (HomologicalComplex.homologyMap
          (HomologicalComplex₂.total.map (flipMap φ) (ComplexShape.up ℤ)) n)).trans
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).mapIso
        (Z'.totalFlipIso (ComplexShape.up ℤ))))

/-! ### A double complex whose columns resolve their degree-zero terms -/

section Resolution

variable (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  (hfin : DiagonalFinite Z) (hq : ∀ p q : ℤ, q < 0 → IsZero ((Z.X p).X q))
  (hex : ∀ p q : ℤ, q ≠ 0 → (Z.X p).ExactAt q) (hd : ∀ p : ℤ, (Z.X p).d 0 1 = 0)

include hfin hq hex hd

/-- **Each column of such a double complex is a resolution of its own degree-`0` term**, with the
identity of the row `0` as the augmentation: the differential out of degree `0` vanishes, so the
degree-`0` cocycles are the whole of `Z^{p,0}`. -/
public theorem hypotheses_rowZero_id : Hypotheses (rowZero Z) Z (𝟙 (rowZero Z)) where
  diagonalFinite := hfin
  zero_of_neg := hq
  exactAt_of_ne_zero := hex
  inducesIsoKernel p := by
    have hz : HomologicalComplex.Hom.f (𝟙 (rowZero Z)) p ≫ (Z.X p).d 0 1 = 0 := by
      rw [hd p, comp_zero]
    have : IsIso (kernel.ι ((Z.X p).d 0 1)) := kernel.ι_of_zero (hd p)
    exact ⟨hz, IsIso.of_isIso_fac_right (h := 𝟙 _) (kernel.lift_ι _ _ hz)⟩

/-- **The row `0` of such a double complex maps quasi-isomorphically to the total complex**, by the
inclusion of the summand indexed by `(n, 0)` in each total degree `n`.  This is
[Stacks, Tag 0133] in the form `quasiIso_total_of_resolution`, applied to the resolution
`StacksDraft.TotalRowComparison.hypotheses_rowZero_id`. -/
public theorem exists_quasiIso_rowZero_total [Z.HasTotal (ComplexShape.up ℤ)] :
    ∃ f : rowZero Z ⟶ Z.total (ComplexShape.up ℤ),
      (∀ n : ℤ, f.f n = Z.ιTotal (ComplexShape.up ℤ) n 0 n (by simp)) ∧ QuasiIso f := by
  obtain ⟨f, hf, hqi⟩ := exists_comparisonMap_p (rowZero Z) Z (𝟙 (rowZero Z))
    (hypotheses_rowZero_id Z hfin hq hex hd) inferInstance
  refine ⟨f, fun n => ?_, hqi⟩
  rw [hf n]
  exact Category.id_comp _

/-- **The canonical morphism from the row `0` to the total complex** of a first-quadrant double
complex whose columns resolve their degree-`0` terms, as data: in degree `n` it is the inclusion
of the summand indexed by `(n, 0)`, by
`StacksDraft.TotalRowComparison.rowZeroTotalMap_f`. -/
public def rowZeroTotalMap [Z.HasTotal (ComplexShape.up ℤ)] :
    Z.flip.X 0 ⟶ Z.total (ComplexShape.up ℤ) :=
  (exists_quasiIso_rowZero_total Z hfin hq hex hd).choose

/-- In total degree `n`, `StacksDraft.TotalRowComparison.rowZeroTotalMap` is the inclusion of the
summand indexed by `(n, 0)`. -/
public theorem rowZeroTotalMap_f [Z.HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    (rowZeroTotalMap Z hfin hq hex hd).f n = Z.ιTotal (ComplexShape.up ℤ) n 0 n (by simp) :=
  (exists_quasiIso_rowZero_total Z hfin hq hex hd).choose_spec.1 n

/-- `StacksDraft.TotalRowComparison.rowZeroTotalMap` is a quasi-isomorphism. -/
public theorem quasiIso_rowZeroTotalMap [Z.HasTotal (ComplexShape.up ℤ)] :
    QuasiIso (rowZeroTotalMap Z hfin hq hex hd) :=
  (exists_quasiIso_rowZero_total Z hfin hq hex hd).choose_spec.2

/-- **A first-quadrant double complex whose columns resolve their degree-`0` terms has the
cohomology of its row `0`**, in every degree.  The isomorphism is the one induced by the canonical
morphism `StacksDraft.TotalRowComparison.rowZeroTotalMap`. -/
public def rowZeroHomologyIsoTotal [Z.HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    (Z.flip.X 0).homology n ≅ (Z.total (ComplexShape.up ℤ)).homology n :=
  have hqi : QuasiIso (rowZeroTotalMap Z hfin hq hex hd) :=
    quasiIso_rowZeroTotalMap Z hfin hq hex hd
  have : IsIso (HomologicalComplex.homologyMap (rowZeroTotalMap Z hfin hq hex hd) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 (hqi.quasiIsoAt n)
  asIso (HomologicalComplex.homologyMap (rowZeroTotalMap Z hfin hq hex hd) n)

end Resolution

/-! ### The replacement for the second spectral sequence -/

/-- **The row degeneration from a rowwise comparison rather than a rowwise vanishing.**

Let `Z^{•,•}` be a first-quadrant double complex whose columns off `0` are acyclic — the first
spectral sequence of [Stacks, Proposition 60.21.3, Tag 07LG], which is what
[Stacks, Lemma 60.19.1, Tag 07LA] supplies — and let `φ : Z ⟶ Z'` be a morphism to a
first-quadrant double complex each of whose columns is a resolution of its degree-`0` term, which
is a quasi-isomorphism on every row.  Then the cohomology of the row `0` of `Z` is the cohomology
of its column `0`.

This replaces the composite of the two acyclic degenerations: the rows of `Z` off `0` are *not*
assumed acyclic, only compared.  For the crystalline double complex `Z'` is the constant
cosimplicial object on `M ⊗^∧_D Ω^*_D` and `φ` is induced by the codiagonal `ε_b : D(b) → D`; the
rowwise hypothesis is the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD]. -/
public def rowZeroHomologyIsoColumnZero_of_rowComparison
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (φ : Z ⟶ Z')
    [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)]
    (hq : ∀ p q : ℤ, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p : ℤ, p < 0 → IsZero (Z.X p))
    (hq' : ∀ p q : ℤ, q < 0 → IsZero ((Z'.X p).X q)) (hp' : ∀ p : ℤ, p < 0 → IsZero (Z'.X p))
    (hfin' : DiagonalFinite Z') (hex' : ∀ p q : ℤ, q ≠ 0 → (Z'.X p).ExactAt q)
    (hd' : ∀ p : ℤ, (Z'.X p).d 0 1 = 0)
    (hrow : ∀ q : ℤ, QuasiIso ((flipMap φ).f q))
    (hcol : ∀ p : ℤ, p ≠ 0 → (Z.X p).Acyclic) (n : ℤ) :
    (Z.flip.X 0).homology n ≅ (Z.X 0).homology n :=
  have : IsIso (HomologicalComplex.homologyMap ((flipMap φ).f 0) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 ((hrow 0).quasiIsoAt n)
  (asIso (HomologicalComplex.homologyMap ((flipMap φ).f 0) n)).trans
    ((rowZeroHomologyIsoTotal Z' hfin' hq' hex' hd' n).trans
      ((totalHomologyIsoOfRows φ hq hp hq' hp' hrow n).symm.trans
        (totalHomologyIsoColumnZero Z hq hp hcol n)))

end StacksDraft.TotalRowComparison

end
