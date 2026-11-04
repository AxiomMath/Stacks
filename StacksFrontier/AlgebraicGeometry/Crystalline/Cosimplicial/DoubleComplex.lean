module

public import StacksFrontier.Algebra.Homology.SpectralSequence.TotalAcyclic
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Acyclicity
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.CechIsTheDerivedFunctor

/-!
# The double complex of a cochain complex of cosimplicial abelian groups

The proof of [Stacks, Proposition 60.21.3, Tag 07LG] runs over the double complex

`K^{a,b} = M ⊗̂_D Ω^a_{D(b)}`,

whose `b` direction is the cosimplicial direction of the cosimplicial envelope `D(*)` and whose
`a` direction is the de Rham direction of the completed divided power forms.  Both directions
are indexed by `ℕ`, and the first of the two spectral sequences the source invokes is
`HomologicalComplex₂.acyclic_total_of_acyclic_column` of
`StacksFrontier/Algebra/Homology/SpectralSequence/TotalAcyclic.lean`, which is stated for a
`HomologicalComplex₂` over `ComplexShape.up ℤ` in both directions.

This module performs the assembly and the two ℕ-to-ℤ extensions once, in the form the crystalline
input arrives in.  The `b` direction of `K` is *cosimplicial*, not already a complex: what
[Stacks, Tag 07LA] delivers is a null homotopy of a cosimplicial module, which
`Crystalline.isZero_homology_alternatingCofaceMapComplex_of_homotopic_id_zero` turns into the
acyclicity of the Moore complex of [Stacks, Tag 019I].  So the input taken here is a cochain
complex of *cosimplicial* abelian groups — the `a` direction already assembled, the `b` direction
not yet — and `Crystalline.cosimplicialDoubleComplexFunctor` applies the Moore complex degreewise
and then extends both indices to `ℤ`.

The orientation is the one `HomologicalComplex₂.acyclic_total_of_acyclic_column` needs: the first
index is the outer one, so `K.X a` is the *column* `K^{a,•}`, the Moore complex of the `a`-th
cosimplicial group, and that is the complex [Stacks, Tag 07LA] says is acyclic for `a > 0`.

## Main definitions

* `Crystalline.cosimplicialDoubleComplexFunctor` — **the double complex of a cochain complex of
  cosimplicial abelian groups**, as a functor into
  `HomologicalComplex₂ AddCommGrpCat (ComplexShape.up ℤ) (ComplexShape.up ℤ)`.
* `Crystalline.cosimplicialDoubleComplexColumnIso` — its column in degree `a : ℕ` is the
  ℤ-extension of the Moore complex of the `a`-th cosimplicial group.

## Main results

* `Crystalline.isZero_cosimplicialDoubleComplex_X_of_neg` and
  `Crystalline.isZero_cosimplicialDoubleComplex_X_X_of_neg` — the double complex is concentrated
  in the first quadrant.
* `Crystalline.finite_not_isZero_cosimplicialDoubleComplex` and the `HasTotal` instance — hence
  each antidiagonal carries only finitely many nonzero terms and the total complex exists.
* `Crystalline.acyclic_cosimplicialDoubleComplex_X` — a column whose cosimplicial group has
  acyclic Moore complex is acyclic, including in the degrees the extension adds.
* `Crystalline.acyclic_total_cosimplicialDoubleComplex` — **the first spectral sequence of
  [Stacks, Tag 07LG] in its acyclic form**: if the Moore complex of every one of the cosimplicial
  groups is acyclic then the total complex of the double complex is acyclic.
  To feed it the input in the shape [Stacks, Tag 07LA] delivers it — a null homotopy of the
  identity of each cosimplicial module — compose it with
  `Crystalline.isZero_homology_alternatingCofaceMapComplex_of_homotopic_id_zero` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/Acyclicity.lean`, which is where
  `Crystalline.Homotopic`, the relation that lemma is stated with, lives.

What the proof of [Stacks, Tag 07LG] uses is not the acyclicity of the total complex but the
*comparison of two complexes* the two degenerations give; that is
`Crystalline.cosimplicialDoubleComplexRowZeroHomologyIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/DoubleComplexDegeneration.lean`.

## What this does and does not supply

It supplies the double complex *given its two differentials*.  The de Rham differential in the
`a` direction for the cosimplicial forms is built elsewhere, as
`Crystalline.CosimplicialCompletedPair.columnDifferential` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialDeRhamDoubleComplex.lean`,
and the cochain complex of cosimplicial groups fed to
`Crystalline.cosimplicialDoubleComplexFunctor` in the crystalline case is
`Crystalline.CosimplicialCompletedPair.doubleComplex`, which exists for the coefficient sheaf
`𝒪_{X/S}` as `Crystalline.envelopeStructureDoubleComplex`.  Nothing here is about the
crystalline site, and no tag attribute is placed: the assembly is bookkeeping around
[Stacks, Tag 0130] and is not itself the content of a tag.

The *columns* of the double complex are described below; its *rows* are described in
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/DoubleComplexRow.lean`, which is where
the flip is moved past the two `ℕ`-to-`ℤ` extensions performed here.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite

universe u

namespace Crystalline

/-- **The double complex of a cochain complex of cosimplicial abelian groups.**

The Moore complex of [Stacks, Tag 019I] is applied in each degree of the `a` direction, turning
the cosimplicial `b` direction into a cochain complex indexed by `ℕ`; the inner and then the outer
index are extended to `ℤ` along `ComplexShape.embeddingUpNat`, which is what
`HomologicalComplex₂.acyclic_total_of_acyclic_column` is stated over.

The first index is the outer one, so the column `(cosimplicialDoubleComplexFunctor.obj K).X a` is
the Moore complex of `K.X a`; see `Crystalline.cosimplicialDoubleComplexColumnIso`. -/
public def cosimplicialDoubleComplexFunctor :
    CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ ⥤
      HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (alternatingCofaceMapComplex AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (CochainComplex AddCommGrpCat.{u} ℤ)

variable (K : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ)

/-- **The column of the double complex in degree `a : ℕ` is the Moore complex of the `a`-th
cosimplicial group**, extended from `ℕ` to `ℤ`. -/
public def cosimplicialDoubleComplexColumnIso (a : ℕ) :
    (cosimplicialDoubleComplexFunctor.obj K).X (a : ℤ) ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X a)).extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendXIso
    (((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (((alternatingCofaceMapComplex AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K))
    ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f a = (a : ℤ) from rfl)

/-- The `ℕ`-to-`ℤ` extension of a complex vanishes in the degrees outside the image of `ℕ`. -/
private theorem isZero_extend_X_embeddingUpNat {V : Type*} [Category V] [HasZeroMorphisms V]
    [HasZeroObject V] (C : CochainComplex V ℕ) {a : ℤ} (ha : ∀ n : ℕ, (n : ℤ) ≠ a) :
    IsZero ((C.extend ComplexShape.embeddingUpNat).X a) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat a fun i hi => ha i hi

/-- **The double complex vanishes in negative first degrees.** -/
public theorem isZero_cosimplicialDoubleComplex_X_of_neg {a : ℤ} (ha : a < 0) :
    IsZero ((cosimplicialDoubleComplexFunctor.obj K).X a) :=
  isZero_extend_X_embeddingUpNat _ fun n hn => by omega

/-- **The double complex vanishes in negative second degrees.** -/
public theorem isZero_cosimplicialDoubleComplex_X_X_of_neg (a : ℤ) {b : ℤ} (hb : b < 0) :
    IsZero (((cosimplicialDoubleComplexFunctor.obj K).X a).X b) := by
  by_cases ha : ∃ n : ℕ, (n : ℤ) = a
  · obtain ⟨n, rfl⟩ := ha
    refine IsZero.of_iso ?_
      ((HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) b).mapIso
        (cosimplicialDoubleComplexColumnIso K n))
    exact isZero_extend_X_embeddingUpNat _ fun n hn => by omega
  · exact Functor.map_isZero (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) b)
      (isZero_extend_X_embeddingUpNat _ fun n hn => ha ⟨n, hn⟩)

/-- **Each antidiagonal of the double complex carries only finitely many nonzero terms**: it is
concentrated in the first quadrant. -/
public theorem finite_not_isZero_cosimplicialDoubleComplex (n : ℤ) :
    {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero (((cosimplicialDoubleComplexFunctor.obj K).X pq.1).X pq.2)}.Finite :=
  StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded _ 0
    (fun a _ hb => isZero_cosimplicialDoubleComplex_X_X_of_neg K a hb)
    (fun _ ha => isZero_cosimplicialDoubleComplex_X_of_neg K ha) n

/-- **The total complex of the double complex exists**: the coproducts defining it are finite. -/
public instance hasTotal_cosimplicialDoubleComplex :
    (cosimplicialDoubleComplexFunctor.obj K).HasTotal (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded _ 0
    (fun a _ hb => isZero_cosimplicialDoubleComplex_X_X_of_neg K a hb)
    (fun _ ha => isZero_cosimplicialDoubleComplex_X_of_neg K ha)

/-- **A column of the double complex is acyclic as soon as the Moore complex of the corresponding
cosimplicial group is.**

The extension from `ℕ` to `ℤ` adds no cohomology: in a degree in the image of the embedding the
cohomology is that of the Moore complex, and in a negative degree the term itself vanishes. -/
public theorem acyclic_cosimplicialDoubleComplex_X {a : ℤ}
    (h : ∀ n : ℕ, (a : ℤ) = (n : ℤ) → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X n)).homology j)) :
    ((cosimplicialDoubleComplexFunctor.obj K).X a).Acyclic := by
  intro m
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  by_cases ha : ∃ n : ℕ, (n : ℤ) = a
  · obtain ⟨n, rfl⟩ := ha
    refine IsZero.of_iso ?_
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) m).mapIso
        (cosimplicialDoubleComplexColumnIso K n))
    by_cases hm : 0 ≤ m
    · lift m to ℕ using hm
      exact IsZero.of_iso (h n rfl m)
        (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X n)).extendHomologyIso
          ComplexShape.embeddingUpNat (j := m) (j' := (m : ℤ)) rfl)
    · exact ShortComplex.isZero_homology_of_isZero_X₂ (_ : ShortComplex AddCommGrpCat.{u})
        (isZero_extend_X_embeddingUpNat _ fun n hn => by omega)
  · exact Functor.map_isZero
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) m)
      (isZero_extend_X_embeddingUpNat _ fun n hn => ha ⟨n, hn⟩)

/-- **The first spectral sequence of [Stacks, Tag 07LG] in its acyclic form**: if the Moore
complex of every one of the cosimplicial groups is acyclic then the total complex of the double
complex is acyclic.

This is the acyclic assembly lemma `HomologicalComplex₂.acyclic_total_of_acyclic_column`, whose
two hypotheses are `Crystalline.finite_not_isZero_cosimplicialDoubleComplex` and
`Crystalline.acyclic_cosimplicialDoubleComplex_X`.  For the comparison of two complexes rather
than the vanishing of one, which is what the proof of [Stacks, Tag 07LG] actually performs, see
`Crystalline.cosimplicialDoubleComplexRowZeroHomologyIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/DoubleComplexDegeneration.lean`. -/
public theorem acyclic_total_cosimplicialDoubleComplex
    (h : ∀ n j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X n)).homology j)) :
    ((cosimplicialDoubleComplexFunctor.obj K).total (ComplexShape.up ℤ)).Acyclic :=
  HomologicalComplex₂.acyclic_total_of_acyclic_column _
    (finite_not_isZero_cosimplicialDoubleComplex K)
    fun _ => acyclic_cosimplicialDoubleComplex_X K fun n _ j => h n j

end Crystalline

end
