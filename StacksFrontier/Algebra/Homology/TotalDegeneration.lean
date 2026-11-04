module

public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso

/-!
# The two degenerations of a first-quadrant double complex

Let `Z^{•,•}` be a double complex of an abelian category, indexed by `ℤ` in both directions with
cochain conventions, and concentrated in the first quadrant.  If every column `Z^{p,•}` with
`p ≠ 0` is acyclic, then the total complex has the cohomology of the remaining column `Z^{0,•}`;
if every row `Z^{•,q}` with `q ≠ 0` is acyclic, it has the cohomology of the remaining row.

These are the two degenerations the proof of [Stacks, Proposition 60.21.3, Tag 07LG] runs on, for
the double complex `K^{a,b} = M ⊗̂_D Ω^a_{D(b)}` whose first column is `M(•)` and whose first row
is `M ⊗^∧_D Ω^*_D`.  `StacksFrontier/Algebra/Homology/SpectralSequence/TotalAcyclic.lean` has the
case in which *all* the columns, resp. rows, are acyclic, where the conclusion is that the total
complex is acyclic; that is not enough to compare two complexes with each other, which is what
the source does with its two spectral sequences.

## How they are proved

Not through the spectral sequence.  Deleting the bottom column of a double complex concentrated
in first degrees `≥ 0` is the morphism `StacksDraft.TotalComplexQuasiIso.bottomProj`, from `Z` to
the double complex concentrated in the column `0` whose column there is `Z^{0,•}`.  In the column
`0` that morphism is the canonical identification, and in every other column it is a morphism
from an acyclic complex to a zero complex; so it is a quasi-isomorphism in every column, and
[Stacks, Tag 0133] — `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map`, proved there by an
induction along the deletions of bottom columns rather than by a spectral sequence — says the
induced morphism of total complexes is a quasi-isomorphism.  The total complex of a double
complex concentrated in the column `0` is that column, by
`StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit`.

The isomorphism is therefore canonical rather than a choice: it is the one induced on cohomology
by an actual morphism of complexes out of `Tot(Z^{•,•})`.  The row statement is the column
statement read at `HomologicalComplex₂.flip`, transported along
`HomologicalComplex₂.totalFlipIso`.

## Main results

* `StacksDraft.TotalDegeneration.quasiIso_total_bottomProj_zero` — the projection onto the column
  `0` of a first-quadrant double complex with acyclic columns off `0` is a quasi-isomorphism on
  total complexes.
* `StacksDraft.TotalDegeneration.totalHomologyIsoColumnZero` — **the first degeneration**:
  `H^n(Tot(Z^{•,•})) ≅ H^n(Z^{0,•})`.
* `StacksDraft.TotalDegeneration.totalHomologyIsoRowZero` — **the second degeneration**:
  `H^n(Tot(Z^{•,•})) ≅ H^n(Z^{•,0})`, the row being `Z.flip.X 0`.

No tag attribute is placed: both statements are degenerations of [Stacks, Tag 0130] and are not
themselves the content of a tag.

## References

* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.TotalDegeneration

open StacksDraft.TotalComplexQuasiIso

attribute [local instance] StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A morphism from an acyclic complex to a zero complex is a quasi-isomorphism: in each degree
both cohomology objects vanish. -/
public theorem quasiIso_of_acyclic_of_isZero {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (hK : K.Acyclic) (hL : IsZero L) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_of_isZero _ ((K.exactAt_iff_isZero_homology n).1 (hK n))
    (Functor.map_isZero (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n) hL)

variable (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The column `-1` of a double complex concentrated in nonnegative first degrees vanishes, which
is what makes the projection onto the column `0` exist. -/
public theorem isZero_X_neg_one (hp : ∀ p : ℤ, p < 0 → IsZero (Z.X p)) :
    IsZero (Z.X ((0 : ℤ) - 1)) :=
  hp ((0 : ℤ) - 1) (by omega)

section Column

/-- Off the column `0` the double complex concentrated in the column `0` vanishes. -/
public theorem isZero_singleColumn_X_of_neg (p : ℤ) (hp' : p < 0) :
    IsZero ((singleColumn (Z.X 0) 0).X p) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (Z.X 0) p (by omega)

/-- The double complex concentrated in the column `0` lies in the first quadrant too: in the
column `0` it is `Z^{0,•}` and elsewhere it vanishes. -/
public theorem isZero_singleColumn_X_X_of_neg (hq : ∀ p q : ℤ, q < 0 → IsZero ((Z.X p).X q))
    (p q : ℤ) (hq' : q < 0) : IsZero (((singleColumn (Z.X 0) 0).X p).X q) := by
  by_cases h : p = 0
  · subst h
    exact IsZero.of_iso (hq 0 q hq')
      ((HomologicalComplex.eval A (ComplexShape.up ℤ) q).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Z.X 0)))
  · exact isZero_singleColumn_X_X (Z.X 0) 0 p h q

/-- **The projection onto the column `0` is a quasi-isomorphism in every column** as soon as every
column off `0` is acyclic: in the column `0` it is an isomorphism, and elsewhere its target
vanishes. -/
public theorem quasiIso_bottomProj_zero_f (hp : ∀ p : ℤ, p < 0 → IsZero (Z.X p))
    (hcol : ∀ p : ℤ, p ≠ 0 → (Z.X p).Acyclic) (p : ℤ) :
    QuasiIso ((bottomProj Z 0 (isZero_X_neg_one Z hp)).f p) := by
  by_cases h : p = 0
  · subst h
    have hiso : IsIso ((bottomProj Z 0 (isZero_X_neg_one Z hp)).f 0) := by
      rw [bottomProj_f_self]
      infer_instance
    infer_instance
  · exact quasiIso_of_acyclic_of_isZero _ (hcol p h)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (Z.X 0) p h)

/-- **The projection onto the column `0` is a quasi-isomorphism on total complexes.**  This is
[Stacks, Tag 0133] for `StacksDraft.TotalComplexQuasiIso.bottomProj`, whose columnwise hypothesis
is discharged by `StacksDraft.TotalDegeneration.quasiIso_bottomProj_zero_f`. -/
public theorem quasiIso_total_bottomProj_zero [Z.HasTotal (ComplexShape.up ℤ)]
    (hq : ∀ p q : ℤ, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p : ℤ, p < 0 → IsZero (Z.X p))
    (hcol : ∀ p : ℤ, p ≠ 0 → (Z.X p).Acyclic) :
    QuasiIso (HomologicalComplex₂.total.map (bottomProj Z 0 (isZero_X_neg_one Z hp))
      (ComplexShape.up ℤ)) :=
  quasiIso_total_map (bottomProj Z 0 (isZero_X_neg_one Z hp)) 0 hq hp
    (isZero_singleColumn_X_X_of_neg Z hq) (isZero_singleColumn_X_of_neg Z)
    (quasiIso_bottomProj_zero_f Z hp hcol)

/-- **The first degeneration: a first-quadrant double complex whose columns off `0` are acyclic
has the cohomology of its column `0`.**

The isomorphism is the one induced by the projection onto the column `0`, followed by the
identification of the total complex of a double complex concentrated in the column `0` with that
column; it is canonical, and in particular it is induced by a morphism of complexes. -/
public def totalHomologyIsoColumnZero [Z.HasTotal (ComplexShape.up ℤ)]
    (hq : ∀ p q : ℤ, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p : ℤ, p < 0 → IsZero (Z.X p))
    (hcol : ∀ p : ℤ, p ≠ 0 → (Z.X p).Acyclic) (n : ℤ) :
    (Z.total (ComplexShape.up ℤ)).homology n ≅ (Z.X 0).homology n :=
  have hqi : QuasiIso (HomologicalComplex₂.total.map (bottomProj Z 0 (isZero_X_neg_one Z hp))
      (ComplexShape.up ℤ)) := quasiIso_total_bottomProj_zero Z hq hp hcol
  have _h₁ : IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (bottomProj Z 0 (isZero_X_neg_one Z hp))
        (ComplexShape.up ℤ)) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 (hqi.quasiIsoAt n)
  have _h₂ : IsIso (totalSingleColumnUnit (Z.X 0) 0) := isIso_totalSingleColumnUnit (Z.X 0) 0
  (asIso (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (bottomProj Z 0 (isZero_X_neg_one Z hp))
        (ComplexShape.up ℤ)) n)).trans
    (((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).mapIso
        (asIso (totalSingleColumnUnit (Z.X 0) 0))).symm.trans
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).mapIso
        ((CategoryTheory.shiftFunctorZero (CochainComplex A ℤ) ℤ).app (Z.X 0))))

end Column

section Row

/-- A cochain complex all of whose terms vanish is a zero object. -/
public theorem isZero_of_isZero_X {K : CochainComplex A ℤ} (h : ∀ n : ℤ, IsZero (K.X n)) :
    IsZero K :=
  (IsZero.iff_id_eq_zero K).2 (by ext n; exact (h n).eq_of_src _ _)

/-- The flip of a first-quadrant double complex vanishes in negative second degrees. -/
public theorem isZero_flip_X_X_of_neg (hp : ∀ p : ℤ, p < 0 → IsZero (Z.X p)) (p q : ℤ)
    (hq' : q < 0) : IsZero ((Z.flip.X p).X q) :=
  Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) p) (hp q hq')

/-- The flip of a first-quadrant double complex vanishes in negative first degrees. -/
public theorem isZero_flip_X_of_neg (hq : ∀ p q : ℤ, q < 0 → IsZero ((Z.X p).X q)) (p : ℤ)
    (hp' : p < 0) : IsZero (Z.flip.X p) :=
  isZero_of_isZero_X fun q => hq q p hp'

/-- **The second degeneration: a first-quadrant double complex whose rows off `0` are acyclic has
the cohomology of its row `0`.**

The row `q` is `Z.flip.X q`, the complex `p ↦ Z^{p,q}` with the first differential of `Z`.  This
is `StacksDraft.TotalDegeneration.totalHomologyIsoColumnZero` read at `Z.flip`, transported along
`HomologicalComplex₂.totalFlipIso`. -/
public def totalHomologyIsoRowZero [Z.HasTotal (ComplexShape.up ℤ)]
    (hq : ∀ p q : ℤ, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p : ℤ, p < 0 → IsZero (Z.X p))
    (hrow : ∀ q : ℤ, q ≠ 0 → (Z.flip.X q).Acyclic) (n : ℤ) :
    (Z.total (ComplexShape.up ℤ)).homology n ≅ (Z.flip.X 0).homology n :=
  ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).mapIso
      (HomologicalComplex₂.totalFlipIso Z (ComplexShape.up ℤ))).symm.trans
    (totalHomologyIsoColumnZero Z.flip (isZero_flip_X_X_of_neg Z hp)
      (isZero_flip_X_of_neg Z hq) hrow n)

end Row

end StacksDraft.TotalDegeneration

end
