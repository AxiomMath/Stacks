module

public import StacksFrontier.Algebra.Homology.TotalDegeneration
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplex

/-!
# The two spectral sequences of [Stacks, Tag 07LG], for the cosimplicial double complex

`Crystalline.cosimplicialDoubleComplexFunctor` turns a cochain complex of cosimplicial abelian
groups into the first-quadrant double complex `K^{a,b}` whose column `a` is the Moore complex of
[Stacks, Tag 019I] of the `a`-th cosimplicial group.  This module runs the two degenerations of
`StacksFrontier/Algebra/Homology/TotalDegeneration.lean` on it and composes them, which is the
comparison of the two complexes the proof of [Stacks, Proposition 60.21.3, Tag 07LG] carries out
with its two spectral sequences:

* the first spectral sequence, whose `E_1` page is the cohomology of the columns, degenerates
  because [Stacks, Lemma 60.19.1, Tag 07LA] makes every column with `a > 0` acyclic, leaving the
  column `a = 0`, which is `M(•)`;
* the second, whose `E_1` page is the cohomology of the rows, is run here from the hypothesis
  that every row with `b > 0` is acyclic, leaving the row `b = 0`, which is `M ⊗^∧_D Ω^*_D`.

**That second hypothesis is not what [Stacks, Lemma 60.21.2, Tag 07LD] supplies, and for the
crystalline double complex it fails whenever `p` is not invertible in `D̂(b)`.**  The clause of
that lemma makes each row *quasi-isomorphic to the row `b = 0`*, not acyclic, and the source's
`E_1` page is `E_1^{a,b} = H^a(M ⊗^∧_D Ω^*_D)` for every `b` with differentials
`0, 1, 0, 1, …`.  See
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialDeRhamRowObstruction.lean`
for the proof that the acyclicity cannot hold.  So `hrow` below is satisfiable only for a `K`
whose rows off `0` really do vanish, and the crystalline application needs a different
degeneration: a rowwise quasi-isomorphism `K ⟶ Const(M ⊗^∧_D Ω^*_D)` fed to
`StacksDraft.quasiIso_total_map` ([Stacks, Tag 0133]).

So `H^j(M ⊗^∧_D Ω^*_D) ≅ H^j(M(•))`, which is the whole remaining content of
[Stacks, Tag 07LG] once [Stacks, Proposition 60.20.1, Tag 07JN] is in hand; see
`StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGFrom07JN.lean`.

Nothing here is about the crystalline site, and nothing here *proves* either acyclicity: both are
hypotheses, named so that what each of the two tags has to supply is visible.

## Main results

* `Crystalline.acyclic_cosimplicialDoubleComplex_X_of_ne_zero` — the columns off `0` are acyclic
  as soon as the Moore complexes of the cosimplicial groups in positive degree are, which is the
  shape [Stacks, Tag 07LA] delivers.
* `Crystalline.cosimplicialDoubleComplexColumnZeroHomologyIso` — the cohomology of the column `0`
  of the double complex is that of the Moore complex of the `0`-th cosimplicial group.
* `Crystalline.cosimplicialDoubleComplexRowZeroHomologyIso` — **the two spectral sequences of
  [Stacks, Tag 07LG], composed**: with the columns off `0` and the rows off `0` acyclic, the
  cohomology of the row `0` is the cohomology of the Moore complex of the `0`-th cosimplicial
  group.

No tag attribute is placed: this is the homological-algebra step inside the proof of
[Stacks, Tag 07LG], not the statement of a tag.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace Crystalline

variable (K : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ)

/-- **The columns of the double complex off the column `0` are acyclic** as soon as the Moore
complex of every cosimplicial group in positive degree is.  The hypothesis is the shape
[Stacks, Lemma 60.19.1, Tag 07LA] delivers, the degree `0` being excluded because that is where
the lemma says nothing. -/
public theorem acyclic_cosimplicialDoubleComplex_X_of_ne_zero
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X n)).homology j))
    (a : ℤ) (ha : a ≠ 0) : ((cosimplicialDoubleComplexFunctor.obj K).X a).Acyclic :=
  acyclic_cosimplicialDoubleComplex_X K fun n hn j => hcol n (by omega) j

/-- **The cohomology of the column `0` of the double complex is the cohomology of the Moore
complex of the `0`-th cosimplicial group.**  The column is that Moore complex extended from `ℕ`
to `ℤ`, and the extension does not change the cohomology in a degree in the image of the
embedding. -/
public def cosimplicialDoubleComplexColumnZeroHomologyIso (j : ℕ) :
    ((cosimplicialDoubleComplexFunctor.obj K).X (0 : ℤ)).homology (j : ℤ) ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X 0)).homology j :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (j : ℤ)).mapIso
      (cosimplicialDoubleComplexColumnIso K 0)).trans
    (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X 0)).extendHomologyIso
      ComplexShape.embeddingUpNat (j := j) (j' := (j : ℤ)) rfl)

/-- **The two spectral sequences of [Stacks, Proposition 60.21.3, Tag 07LG], composed.**

With every column off `0` acyclic — which is what [Stacks, Lemma 60.19.1, Tag 07LA] gives — and
every row off `0` acyclic, the cohomology of the row `0` and the cohomology of the column `0`
are both the cohomology of the total complex, hence each other's.

The second hypothesis is **not** the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD]: that
clause gives a quasi-isomorphism of each row with the row `0`, which is a weaker conclusion about
each row and a usable one about the double complex.  For the crystalline `K` the rows off `0`
are not acyclic; see the module documentation.

For the crystalline double complex `K^{a,b} = M ⊗̂_D Ω^a_{D(b)}` the row `0` is
`M ⊗^∧_D Ω^*_D` and the column `0` is `M(•)`, so this is exactly the comparison of the two
complexes that remains of that proposition once [Stacks, Tag 07JN] is in hand. -/
public def cosimplicialDoubleComplexRowZeroHomologyIso
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X n)).homology j))
    (hrow : ∀ b : ℤ, b ≠ 0 → ((cosimplicialDoubleComplexFunctor.obj K).flip.X b).Acyclic)
    (j : ℕ) :
    ((cosimplicialDoubleComplexFunctor.obj K).flip.X 0).homology (j : ℤ) ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X 0)).homology j :=
  (StacksDraft.TotalDegeneration.totalHomologyIsoRowZero (cosimplicialDoubleComplexFunctor.obj K)
        (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg K p hq)
        (fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg K hp) hrow (j : ℤ)).symm.trans
    ((StacksDraft.TotalDegeneration.totalHomologyIsoColumnZero
        (cosimplicialDoubleComplexFunctor.obj K)
        (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg K p hq)
        (fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg K hp)
        (acyclic_cosimplicialDoubleComplex_X_of_ne_zero K hcol) (j : ℤ)).trans
      (cosimplicialDoubleComplexColumnZeroHomologyIso K j))

end Crystalline

end
