module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FirstQuadrantDoubleComplex
public import StacksFrontier.Algebra.Homology.TricomplexHomology
public import StacksFrontier.CategoryTheory.Sites.CechComplexExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.Tricomplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.SequenceAndSecondPage

/-!
# The Čech double complex of a Cartan-Eilenberg resolution, and its first page

Let `U : I → C` be a family of objects of a site and let `L^{•,•}` be a double complex of
abelian presheaves on `C` -- in the intended application the double complex of presheaves
underlying a Cartan-Eilenberg resolution of a bounded below complex of sheaves, with the
**degree of the resolved complex outer and the resolution degree inner**, as in
`CochainComplex.CartanEilenbergResolution`.

The proof of the spectral sequence of [Stacks, Tag 08BN] runs as follows.  Apply the Čech
complex of `U` to every term of `L`, producing the triple complex
`Č^p(U, L^{q,m})` of `Stacks.Cech.cechTricomplexFunctor`; integrate the Čech degree `p` against
the degree `q` of the resolved complex, producing the double complex

```
A^{n,m} = ⨁_{p + q = n} Č^p(U, L^{q,m})
```

of [Stacks, Tag 08BI]; and take the **first** spectral sequence of `A^{•,•}`, that of the
filtration by `n`.  Its first page is `E_1^{n,m} = H^m(A^{n,•})`, which this file identifies
with the degree-`n` term of `Tot(Č^•(U, H^m(L^{•,•})))`, so that its second page is
`E_2^{p,q} = H^p(Tot(Č^•(U, H^q(L^{•,•}))))`.

The one piece of bookkeeping that makes this fit the library is `cechCartanEilenbergBicomplex`
below: the spectral sequence wanted is the *first* one of `A^{•,•}`, and the functorial `E₂`
engine of
`StacksFrontier/Algebra/Homology/SpectralSequence/FirstQuadrantDoubleComplex.lean` is written for
the *second* one, that of the filtration by the inner coordinate.  So the double complex is
recorded flipped, `B^{m,n} = A^{n,m}`, with the resolution degree outer; the second spectral
sequence of `B^{•,•}` is the first spectral sequence of `A^{•,•}`, since
`''E_2^{p,q}(B) = H^p_{II}(H^q_I(B)) = H^p_n(H^q_m(A)) = 'E_2^{p,q}(A)`.  This is the same
orientation decision, and for the same reason, as the one explained in the module
documentation of
`StacksFrontier/Topology/Sheaves/Cohomology/CechSpectralSequence/SequenceAndSecondPage.lean`.

**Neither clause of [Stacks, Tag 08BN] is proved here, and nothing in this file carries that
tag**; the second clause is assembled out of this file in the module
`BoundedBelowComplexSpectralSequence` of
`StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence`,
and the implementation notes say which further results that needs.

## Main definitions

* `HomologicalComplex₂.flipHomologyIso`: homology of the flip of a double complex in its outer
  direction is the complex of homologies of the columns of the original, i.e.
  `H^q_I(K^{•,•}.flip) ≅ H^q_{II}(K^{•,•})`.
* `Stacks.Cech.cechCartanEilenbergBicomplex`: the double complex `B^{m,n} = A^{n,m}` above.

## Main results

* `Stacks.Cech.cechCartanEilenbergBicomplexHomologyIso`: **the first page.**
  `H^q_I(B^{•,•}) ≅ Tot(Č^•(U, H^q(L^{•,•})))`, an isomorphism of complexes in the remaining
  degree `n`, which is [Stacks, Tag 08BN]'s identification of `'E_1^{•,q}(A)`.
* `Stacks.Cech.cechCartanEilenbergBicomplexPageTwoIso`: **the second page.**
  `''E_2^{p,q}(B) ≅ H^p(Tot(Č^•(U, H^q(L^{•,•}))))`.
* `Stacks.Cech.preservesHomology_cechComplexFunctorInt_comp_eval`: each term of the Čech
  complex of abelian presheaves, extended by zero to the integers, preserves homology.  This
  is the hypothesis `HomologicalComplex₃.int₁₂HomologyIsoOfComplexValuedFunctor` carries, and
  it is [Stacks, Tag 01EJ] together with the exactness of extension by zero.

## Implementation notes

The finiteness hypothesis `hL` of the two main results is the one of
`Stacks.Cech.int₂₃IsoCechBicomplex`: on each antidiagonal of the integrated pair of degrees
only finitely many terms of the triple complex are nonzero.  It holds in the intended
application because the Čech degree is `≥ 0` and a Cartan-Eilenberg resolution of a bounded
below complex is bounded below in the degree of the resolved complex; it is carried as a
hypothesis rather than derived, exactly as in `Stacks.Cech.int₂₃IsoCechBicomplex`, because the
two bounds are properties of the application and not of the construction.

The second clause of [Stacks, Tag 08BN] is proved out of this file, in the module
`BoundedBelowComplexSpectralSequence` of
`StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence`
(`Stacks.Cech.exists_cechSpectralSequence`), which is where that clause's tag sits.  The three
pieces it adds to the construction and the second page recorded here are:

* the identification of `H^q(L^{•,•})` with the complex `n ↦ R^q i(F^n)` of cohomology
  presheaves of [Stacks, Tag 01ER]:
  `CochainComplex.CartanEilenbergResolution.nonempty_rowHomologyIso_rightDerivedPlus`, an
  isomorphism of complexes, which assembles the isomorphism family and the naturality square of
  the first conjunct of
  `CochainComplex.CartanEilenbergResolution.exists_homologyIso_rightDerivedPlus`.  The
  `(F.rightDerivedPlus q).Additive` that assembling needs is not an instance but it is a
  theorem, part (1) of [Stacks, Tag 05TE]
  (`Stacks.Cohomology.CechDelta.rightDerivedPlus_deltaAxioms`), at the standard derived
  category -- which is the one this development works at;
* the abutment, i.e. `H^n(Tot(B^{•,•})) ≅ H^n(X, F^•)`:
  `Stacks.Cech.cechCartanEilenbergTotalIso`, which by `HomologicalComplex₂.totalFlipIso`, the
  associator `HomologicalComplex₃.totalAssociator` of [Stacks, Tag 08BI] and
  `Stacks.Cech.total₂₃IsoCechTotalComplex` identifies the total complex of `B` with
  `Tot(Č^•(U, Tot(L)))`, together with the Čech comparison at the complex of injectives
  `Tot(I^{•,•})`, which is `Stacks.Cech.cechDerivedIsoDerivedGlobalSections`;
* convergence: `Stacks.Cohomology.CechSpectral.abutsTo_totalSpectralSequence₂Functor`, the
  abutment reading of [Stacks, Tag 0132] for the canonical functorial second spectral sequence,
  whose diagonal-finiteness hypothesis is supplied by
  `Stacks.Cech.finite_diagonal_cechCartanEilenbergBicomplex` -- note that the spectral sequence
  of a merely bounded below complex is *not* first quadrant, so the first-quadrant abutment
  plumbing of [Stacks, Tag 01ES] does not apply, `E₂CohomologicalSpectralSequenceNat` is not
  the right target, and convergence is stated as
  `CategoryTheory.SpectralSequence.AbutsTo`.

Functoriality of that spectral sequence in `F^•` is not asserted by [Stacks, Tag 08BN] and is
not proved.  It would need Cartan-Eilenberg resolutions to be functorial up to homotopy -- the
analogue for `CochainComplex.CartanEilenbergResolution` of
`CategoryTheory.InjectiveResolution.desc`, `descIdHomotopy` and `descCompHomotopy`.  Nothing
of that exists yet.  Once it does, the homotopies have components of degree `(-1, 0)` on
`B^{•,•}`, which preserve the filtration by the inner coordinate on the nose, so
`HomologicalComplex₂.filteredHomotopy₂_of_homotopy` and
`HomologicalComplex₂.e₂FunctorOfHomotopyClasses` apply verbatim.

## References

* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 08BI](https://stacks.math.columbia.edu/tag/08BI)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape

namespace HomologicalComplex₂

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {I₁ I₂ : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K : HomologicalComplex₂ C c₁ c₂) (q : I₂)

/-- The comparison in degree `n`: the degree-`n` term of `H^q_I(K^{•,•}.flip)` is the homology
at `q` of the column `K^{n,•}`.  Homology in the category of complexes is computed degreewise,
which is to say that `HomologicalComplex.eval C c₁ n` preserves homology. -/
def flipHomologyIsoX (n : I₁) : (K.X n).homology q ≅ (K.flip.homology q).X n :=
  (K.flip.sc q).mapHomologyIso (HomologicalComplex.eval C c₁ n)

/-- **Homology of the flip of a double complex in its outer direction is the complex of
homologies of the columns of the original**, `H^q_I(K^{•,•}.flip) ≅ H^q_{II}(K^{•,•})`, as
complexes in the remaining degree.  The commutation square is naturality of
`ShortComplex.mapHomologyIso` in the *functor*, applied to
`HomologicalComplex.dNatTrans`; this is the same square as the one in the first direction of
`HomologicalComplex₃.homologyIsoOfComplexValuedFunctor`. -/
def flipHomologyIso :
    ((HomologicalComplex.homologyFunctor C c₂ q).mapHomologicalComplex c₁).obj K ≅
      K.flip.homology q :=
  HomologicalComplex.Hom.isoOfComponents (K.flipHomologyIsoX q)
    (fun n n' _ => (HomologicalComplex.mapHomologyIso_hom_naturality_natTrans
      (HomologicalComplex.dNatTrans C c₁ n n') K.flip q).symm)

end HomologicalComplex₂

namespace Stacks.Cech

universe w v u

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {I : Type w} (U : I → C)
  [(CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) U).Additive]

/-- **Each term of the integer-indexed Čech complex of abelian presheaves preserves
homology.**  The Čech complex functor is exact ([Stacks, Tag 01EJ]), extension by zero is
exact, and evaluation in a fixed degree is exact.  This is the hypothesis
`HomologicalComplex₃.int₁₂HomologyIsoOfComplexValuedFunctor` carries about its functor. -/
instance preservesHomology_cechComplexFunctorInt_comp_eval (p : ℤ) :
    (cechComplexFunctorInt U ⋙
      HomologicalComplex.eval AddCommGrpCat.{w} (up ℤ) p).PreservesHomology := by
  have h₁ : PreservesFiniteLimits (cechComplexFunctorInt U ⋙
      HomologicalComplex.eval AddCommGrpCat.{w} (up ℤ) p) := by
    dsimp only [cechComplexFunctorInt]
    infer_instance
  have h₂ : PreservesFiniteColimits (cechComplexFunctorInt U ⋙
      HomologicalComplex.eval AddCommGrpCat.{w} (up ℤ) p) := by
    dsimp only [cechComplexFunctorInt]
    infer_instance
  infer_instance

variable (L : HomologicalComplex₂ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ) (up ℤ))
  [∀ K : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ), K.HasTotal (up ℤ)]

/-- **The Čech double complex of a Cartan-Eilenberg resolution**, recorded with the resolution
degree outer:

```
B^{m,n} = A^{n,m} = ⨁_{p + q = n} Č^p(U, L^{q,m}).
```

This is the double complex of the proof of [Stacks, Tag 08BN], flipped.  The flip is what makes
the spectral sequence wanted -- the one filtered by the integrated degree `n` -- be the
*second* spectral sequence of the double complex recorded here, which is the one the library's
functorial `E₂` machinery is written for. -/
def cechCartanEilenbergBicomplex : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ) :=
  (((cechTricomplexFunctor U).obj L).int₁₂ (up ℤ)).flip

/-- The index convention of `cechCartanEilenbergBicomplex`: its column at the resolution degree
`m` is the total complex, over the Čech degree and the degree of the resolved complex, of the
Čech complexes of the slice of `L` at `m`. -/
lemma cechCartanEilenbergBicomplex_X (m : ℤ) :
    (cechCartanEilenbergBicomplex U L).X m =
      (((cechTricomplexFunctor U).obj L).X' m).total (up ℤ) :=
  rfl

/-- **The first page of the spectral sequence of [Stacks, Tag 08BN].**  Taking homology of the
double complex `B^{•,•}` in the resolution direction at `q` gives the total Čech complex of the
complex `H^q(L^{•,•})` of homologies of the columns of `L`:

```
'E_1^{n,q}(A) = H^q(A^{n,•}) = Tot(Č^•(U, H^q(L^{•,•})))^n,
```

an isomorphism of complexes in `n`, so that the differential `'d_1` is the one induced by the
differential of `H^q(L^{•,•})` and of the Čech complex.  The content is that the Čech complex
functor is exact, hence commutes with homology
(`HomologicalComplex₃.int₁₂HomologyIsoOfComplexValuedFunctor`), together with the fact that
homology in the category of complexes is degreewise
(`HomologicalComplex₂.flipHomologyIso`). -/
def cechCartanEilenbergBicomplexHomologyIso (q : ℤ)
    (hL : ∀ n : ℤ, {pq : ℤ × ℤ | ComplexShape.π (up ℤ) (up ℤ) (up ℤ) pq = n ∧
      ¬ IsZero ((((cechTricomplexFunctor U).obj L).X pq.1).X pq.2)}.Finite) :
    (cechCartanEilenbergBicomplex U L).homology q ≅
      (cechTotalComplexFunctor U).obj (HomologicalComplex₃.rowHomology L q) :=
  (HomologicalComplex₂.flipHomologyIso
      (((cechTricomplexFunctor U).obj L).int₁₂ (up ℤ)) q).symm ≪≫
    HomologicalComplex₃.int₁₂HomologyIsoOfComplexValuedFunctor
      (cechComplexFunctorInt U) L q (up ℤ) hL

/-- **The second page of the spectral sequence of [Stacks, Tag 08BN].**  The second page of the
second spectral sequence of `B^{•,•}` -- which is the first spectral sequence of `A^{•,•}` --
is

```
E_2^{p,q} = H^p(Tot(Č^•(U, H^q(L^{•,•})))).
```

This is [Stacks, Tag 0130] (6) for `B^{•,•}`, in the natural form
`HomologicalComplex₂.pageTwoNatIso`, followed by `H^p` of the first-page identification. -/
def cechCartanEilenbergBicomplexPageTwoIso (p q : ℤ)
    (hL : ∀ n : ℤ, {pq : ℤ × ℤ | ComplexShape.π (up ℤ) (up ℤ) (up ℤ) pq = n ∧
      ¬ IsZero ((((cechTricomplexFunctor U).obj L).X pq.1).X pq.2)}.Finite) :
    (HomologicalComplex₂.e₂SpectralSequence₂Functor AddCommGrpCat.{w} ⋙
          CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{w} _ 2 2 ⋙
            HomologicalComplex.eval AddCommGrpCat.{w} _ (p, q)).obj
        (cechCartanEilenbergBicomplex U L) ≅
      ((cechTotalComplexFunctor U).obj
        (HomologicalComplex₃.rowHomology L q)).homology p :=
  (HomologicalComplex₂.pageTwoNatIso AddCommGrpCat.{w} p q).app
      (cechCartanEilenbergBicomplex U L) ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (up ℤ) p).mapIso
      (cechCartanEilenbergBicomplexHomologyIso U L q hL)

/-! ### The finiteness hypothesis, for a resolution bounded below -/

omit [∀ K : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ), K.HasTotal (up ℤ)] in
/-- A homological complex all of whose terms are zero is zero. -/
lemma isZero_of_forall_isZero_X {D : Type*} [Category* D] [Preadditive D] {ι : Type*}
    {c : ComplexShape ι} (M : HomologicalComplex D c) (h : ∀ i, IsZero (M.X i)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext i
  exact (h i).eq_of_src _ _

omit [∀ K : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ), K.HasTotal (up ℤ)] in
/-- The Čech triple complex vanishes in negative Čech degrees, the Čech complex being extended
by zero from the nonnegative degrees. -/
lemma isZero_cechTricomplexFunctor_X_X_of_neg (p : ℤ) (hp : p < 0) (q : ℤ) :
    IsZero ((((cechTricomplexFunctor U).obj L).X p).X q) :=
  isZero_of_forall_isZero_X _ fun _ =>
    HomologicalComplex.isZero_extend_X _ embeddingUpNat p fun i => by
      change ((i : ℕ) : ℤ) ≠ p; omega

omit [∀ K : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ), K.HasTotal (up ℤ)] in
/-- The Čech triple complex vanishes below the bound of the resolved complex. -/
lemma isZero_cechTricomplexFunctor_X_X_of_lt (n₀ : ℤ) [CochainComplex.IsStrictlyGE L n₀]
    (p q : ℤ) (hq : q < n₀) :
    IsZero ((((cechTricomplexFunctor U).obj L).X p).X q) :=
  Functor.map_isZero
    (((cechComplexFunctorInt U ⋙
      HomologicalComplex.eval AddCommGrpCat.{w} (up ℤ) p).mapHomologicalComplex (up ℤ)))
    (CochainComplex.isZero_of_isStrictlyGE L n₀ q hq)

omit [∀ K : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ), K.HasTotal (up ℤ)] in
/-- **The finiteness hypothesis of the two results above holds for a Cartan-Eilenberg
resolution of a bounded below complex.**  On the antidiagonal `p + q = n` of the integrated
pair of degrees, the Čech degree `p` is bounded below by `0` and the degree `q` of the resolved
complex by its bound `n₀`, so only the finitely many pairs with `p ∈ [0, n - n₀]` contribute. -/
lemma finite_support_cechTricomplexFunctor (n₀ : ℤ) [CochainComplex.IsStrictlyGE L n₀] (n : ℤ) :
    {pq : ℤ × ℤ | ComplexShape.π (up ℤ) (up ℤ) (up ℤ) pq = n ∧
      ¬ IsZero ((((cechTricomplexFunctor U).obj L).X pq.1).X pq.2)}.Finite := by
  refine Set.Finite.subset
    ((Set.finite_Icc (0 : ℤ) (n - n₀)).prod (Set.finite_Icc n₀ n)) ?_
  intro pq hpq
  obtain ⟨hsum, hne⟩ := hpq
  have hsum' : pq.1 + pq.2 = n := hsum
  have hp : 0 ≤ pq.1 := by
    by_contra h
    exact hne (isZero_cechTricomplexFunctor_X_X_of_neg U L pq.1 (by omega) pq.2)
  have hq : n₀ ≤ pq.2 := by
    by_contra h
    exact hne (isZero_cechTricomplexFunctor_X_X_of_lt U L n₀ pq.1 pq.2 (by omega))
  exact Set.mem_prod.2 ⟨⟨hp, by omega⟩, ⟨hq, by omega⟩⟩

end Stacks.Cech

end
