module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamRow
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexRowQuasiIso

/-!
# The rowwise hypothesis of [Stacks, Tag 07LG] from [Stacks, Tag 07LD] in each cosimplicial degree

`Crystalline.quasiIso_flipMap_of_rowDegreewiseHomotopyEquiv` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/DoubleComplexRowQuasiIso.lean` reduces
the rowwise hypothesis `hrows` of `...SmallSite.computes07LG_of_doubleComplex` to a homotopy
equivalence of each row of `K` with the comparison complex `R`.  For a `K` built from a
`Crystalline.CosimplicialCompletedPair` the rows are known: by
`Crystalline.CosimplicialCompletedPair.rowDeRhamIso` the row `b` *is* the completed de Rham
complex

`M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}`

of the cosimplicial degree `b`.  This module composes the two, so that `hrows` becomes a
hypothesis stated purely about completed de Rham complexes — which is the form the completed
clause of [Stacks, Lemma 60.21.2, Tag 07LD] is proved in, as
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` and its instantiation at the genuine
divided power forms,
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_pushedConnection`.

This replaces `Crystalline.CosimplicialCompletedPair.acyclic_flip_X_of_ne_zero`, whose antecedent
is the acyclicity of those complexes and which
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialDeRhamRowObstruction.lean`
proves unsatisfiable: that antecedent forces `p` to be invertible in `D̂(b)`.  What the source uses
is a comparison, not a vanishing, and that is what is assumed here.

## The shape of the hypothesis

`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` produces its homotopy equivalence as
*additive maps in each exterior degree* together with the identities relating them to
`Crystalline.CompletedDeRham.differential`; it says so in its own docstring.  The two steps from
there to `hrows` are both performed here:

* `Crystalline.cochainComplexHomOfDegreewise` turns a degreewise family commuting with the
  differentials out of each degree into a morphism of cochain complexes.  For a complex built by
  `Crystalline.CompletedDeRham.complex` the differential out of `i` is the de Rham differential, by
  `Crystalline.CompletedDeRham.complex_d`, so a family of additive maps satisfying the
  perturbation lemma's third and fourth conjuncts is exactly such a family.
* `Crystalline.CosimplicialCompletedPair.quasiIso_flipMap_of_deRhamHomotopyEquiv` then feeds the
  resulting chain maps, the degreewise homotopy and the retraction property of the codiagonal to
  `Crystalline.quasiIso_flipMap_of_rowDegreewiseHomotopyEquiv`.

## Main results

* `Crystalline.cochainComplexHomOfDegreewise` — **a morphism of `ℕ`-indexed cochain complexes from
  a degreewise family**, the commutation being asked for only out of each degree.
* `Crystalline.CosimplicialCompletedPair.rowDeRhamComparison` — the comparison of the completed de
  Rham complex of the cosimplicial degree `b` with `R`, read off a morphism
  `K ⟶ Const(R)` through `Crystalline.CosimplicialCompletedPair.rowDeRhamIso`.
* `Crystalline.CosimplicialCompletedPair.quasiIso_flipMap_of_deRhamHomotopyEquiv` — **the rowwise
  hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG] for a `K` built from a pair, from a
  degreewise homotopy equivalence of `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` with `R` in each cosimplicial
  degree.**
* `Crystalline.CosimplicialCompletedPair.quasiIso_flipMap_of_deRhamDegreewiseHomotopyEquiv` — the
  same with every morphism of complexes replaced by the degreewise family it is assembled from,
  whose seven hypotheses are in bijection with the conjuncts of the perturbation lemma's
  conclusion.
* `Crystalline.deRhamComparisonTarget` — the comparison complex `R` built from the perturbation
  lemma's own output, a family of abelian groups with a square-zero family of additive maps.
* `Crystalline.CosimplicialCompletedPair.quasiIso_flipMap_of_deRhamAddHomHomotopyEquiv` — the same
  again with every morphism of `AddCommGrpCat` replaced by an additive map and every identity read
  on elements.  **This is the interface the completed clause of [Stacks, Tag 07LD] plugs into**:
  its data and hypotheses are the conclusion of
  `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` with nothing translated.

## What is still owed

The homotopy equivalence itself, for the crystalline pair.  Two identifications separate it from
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_pushedConnection`: `D(b)` has to be
recognised as the `p`-adic completion of a divided power polynomial algebra over `D`, and the row
`M(b) ⊗̂_{D(b)} Ω^*_{D(b)}` has to be recognised as `M ⊗̂_D Ω̂^*_{D(b)}`, which is the crystal
property.  Neither is done here or anywhere else in the library, and no tag attribute is placed.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial

universe u v w uN

namespace Crystalline

/-! ### A morphism of cochain complexes from a degreewise family -/

/-- **A morphism of `ℕ`-indexed cochain complexes from a degreewise family of maps.**

In the shape `ComplexShape.up ℕ` the only related pairs are `(i, i + 1)`, so a degreewise family
commuting with the differentials out of each degree is a morphism of complexes.  This is the shape
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` produces its comparison maps in: a
family of additive maps, one in each exterior degree, together with the identity relating them to
`Crystalline.CompletedDeRham.differential`. -/
public def cochainComplexHomOfDegreewise {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {X Y : CochainComplex C ℕ} (phi : ∀ i, X.X i ⟶ Y.X i)
    (hphi : ∀ i : ℕ, phi i ≫ Y.d i (i + 1) = X.d i (i + 1) ≫ phi (i + 1)) : X ⟶ Y where
  f := phi
  comm' i j h := by
    obtain rfl : i + 1 = j := h
    exact hphi i

/-- The components of `Crystalline.cochainComplexHomOfDegreewise` are the given family. -/
public theorem cochainComplexHomOfDegreewise_f {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {X Y : CochainComplex C ℕ} (phi : ∀ i, X.X i ⟶ Y.X i)
    (hphi : ∀ i : ℕ, phi i ≫ Y.d i (i + 1) = X.d i (i + 1) ≫ phi (i + 1)) (i : ℕ) :
    (cochainComplexHomOfDegreewise phi hphi).f i = phi i := rfl

/-! ### The rows of the crystalline double complex -/

namespace CosimplicialCompletedPair

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedPair.{u, v, w} E p) {R : CochainComplex AddCommGrpCat.{max v w} ℕ}

/-- **The comparison of the completed de Rham complex of the cosimplicial degree `b` with `R`**
induced by a morphism `K ⟶ Const(R)`: the row `b` of that morphism, read through
`Crystalline.CosimplicialCompletedPair.rowDeRhamIso`.

For the crystalline double complex the morphism `K ⟶ Const(R)` is the one the codiagonal
`ε_b : D(b) → D` supplies, by `Crystalline.CosimplicialDoubleComplex.constHom`. -/
public def rowDeRhamComparison
    (rho : W.doubleComplex ⟶ constantCosimplicialCochainComplex.obj R) (b : ℕ) :
    W.degreeDeRhamComplex b ⟶ R :=
  (W.rowDeRhamIso b).inv ≫ cosimplicialRowMap rho b

/-- The row `b` of `rho` is `Crystalline.CosimplicialCompletedPair.rowDeRhamComparison` read back
through `Crystalline.CosimplicialCompletedPair.rowDeRhamIso`. -/
public theorem cosimplicialRowMap_eq_rowDeRhamComparison
    (rho : W.doubleComplex ⟶ constantCosimplicialCochainComplex.obj R) (b : ℕ) :
    cosimplicialRowMap rho b = (W.rowDeRhamIso b).hom ≫ W.rowDeRhamComparison rho b :=
  (Iso.hom_inv_id_assoc (W.rowDeRhamIso b) (cosimplicialRowMap rho b)).symm

/-- **The rowwise hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG] for a `K` built from a
pair, from a degreewise homotopy equivalence in each cosimplicial degree.**

For each `b` the hypothesis is the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] at the
cosimplicial degree `b`: a map `iotaRow b : R ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}`, a retraction
`piRow b` with `iotaRow b ≫ piRow b = 𝟙`, a degree-lowering family `hh b` contracting
`piRow b ≫ iotaRow b` to the identity, and `hsec`, the statement that the comparison induced by
`rho` retracts `iotaRow b` — which for the crystalline `K` is the identity
`ε_b ∘ coproj = id` of `Crystalline.completedEnvelopeCodiagonal_coprojection`.

The conclusion is the hypothesis `hrows` of `...SmallSite.computes07LG_of_doubleComplex` verbatim.
The rows indexed by a negative integer need no hypothesis, both sides vanishing there. -/
public theorem quasiIso_flipMap_of_deRhamHomotopyEquiv
    (rho : W.doubleComplex ⟶ constantCosimplicialCochainComplex.obj R)
    (iotaRow : ∀ b : ℕ, R ⟶ W.degreeDeRhamComplex b)
    (piRow : ∀ b : ℕ, W.degreeDeRhamComplex b ⟶ R)
    (hh : ∀ b i : ℕ, (W.degreeDeRhamComplex b).X (i + 1) ⟶ (W.degreeDeRhamComplex b).X i)
    (hretract : ∀ b : ℕ, iotaRow b ≫ piRow b = 𝟙 R)
    (h0 : ∀ b : ℕ, (W.degreeDeRhamComplex b).d 0 (0 + 1) ≫ hh b 0 +
      (piRow b).f 0 ≫ (iotaRow b).f 0 = 𝟙 ((W.degreeDeRhamComplex b).X 0))
    (hsucc : ∀ b i : ℕ, (W.degreeDeRhamComplex b).d (i + 1) (i + 1 + 1) ≫ hh b (i + 1) +
        hh b i ≫ (W.degreeDeRhamComplex b).d i (i + 1) +
        (piRow b).f (i + 1) ≫ (iotaRow b).f (i + 1) =
      𝟙 ((W.degreeDeRhamComplex b).X (i + 1)))
    (hsec : ∀ b : ℕ, iotaRow b ≫ W.rowDeRhamComparison rho b = 𝟙 R) (b : ℤ) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f b) := by
  refine quasiIso_flipMap_of_quasiIso_row rho (fun c => ?_) b
  have : QuasiIso (iotaRow c) :=
    CompletedDeRham.quasiIso_of_degreewiseHomotopyRetract (iotaRow c) (piRow c) (hh c)
      (hretract c) (h0 c) (hsucc c)
  have : QuasiIso (iotaRow c ≫ (W.rowDeRhamIso c).inv) := inferInstance
  refine CompletedDeRham.quasiIso_of_section (iotaRow c ≫ (W.rowDeRhamIso c).inv)
    (cosimplicialRowMap rho c) ?_
  exact (Category.assoc _ _ _).trans (hsec c)

/-- **The rowwise hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG] for a `K` built from a
pair, from the output of the perturbation lemma degree by degree.**

This is `Crystalline.CosimplicialCompletedPair.quasiIso_flipMap_of_deRhamHomotopyEquiv` with every
morphism of complexes replaced by the degreewise family it is assembled from, which is the
language `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` and its instantiation
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_pushedConnection` produce their
output in: maps in each exterior degree, with the commutation with the de Rham differential stated
separately.

The seven hypotheses are in bijection with that output.  `hiota` and `hpi` are its third and
fourth conjuncts, that `ι'` and `π'` are maps of complexes; `hretract` is its second, `π' ι' = 1`;
`h0` and `hsucc` are its fifth and sixth, the two contraction identities of the homotopy `H`; and
`hsec` says that the comparison `rho` induces retracts `ι'`, which for the crystalline `K` is the
identity `ε_b ∘ coproj = id` of
`Crystalline.completedEnvelopeCodiagonal_coprojection`.  Nothing is assumed of `hDeg` beyond the
two contraction identities.

The conclusion is the hypothesis `hrows` of `...SmallSite.computes07LG_of_doubleComplex`
verbatim. -/
public theorem quasiIso_flipMap_of_deRhamDegreewiseHomotopyEquiv
    (rho : W.doubleComplex ⟶ constantCosimplicialCochainComplex.obj R)
    (iotaDeg : ∀ b i : ℕ, R.X i ⟶ (W.degreeDeRhamComplex b).X i)
    (piDeg : ∀ b i : ℕ, (W.degreeDeRhamComplex b).X i ⟶ R.X i)
    (hDeg : ∀ b i : ℕ, (W.degreeDeRhamComplex b).X (i + 1) ⟶ (W.degreeDeRhamComplex b).X i)
    (hiota : ∀ b i : ℕ, iotaDeg b i ≫ (W.degreeDeRhamComplex b).d i (i + 1) =
      R.d i (i + 1) ≫ iotaDeg b (i + 1))
    (hpi : ∀ b i : ℕ, piDeg b i ≫ R.d i (i + 1) =
      (W.degreeDeRhamComplex b).d i (i + 1) ≫ piDeg b (i + 1))
    (hretract : ∀ b i : ℕ, iotaDeg b i ≫ piDeg b i = 𝟙 (R.X i))
    (h0 : ∀ b : ℕ, (W.degreeDeRhamComplex b).d 0 (0 + 1) ≫ hDeg b 0 +
      piDeg b 0 ≫ iotaDeg b 0 = 𝟙 ((W.degreeDeRhamComplex b).X 0))
    (hsucc : ∀ b i : ℕ, (W.degreeDeRhamComplex b).d (i + 1) (i + 1 + 1) ≫ hDeg b (i + 1) +
        hDeg b i ≫ (W.degreeDeRhamComplex b).d i (i + 1) +
        piDeg b (i + 1) ≫ iotaDeg b (i + 1) =
      𝟙 ((W.degreeDeRhamComplex b).X (i + 1)))
    (hsec : ∀ b i : ℕ, iotaDeg b i ≫ (W.rowDeRhamComparison rho b).f i = 𝟙 (R.X i)) (b : ℤ) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f b) :=
  W.quasiIso_flipMap_of_deRhamHomotopyEquiv rho
    (fun c => cochainComplexHomOfDegreewise (iotaDeg c) (hiota c))
    (fun c => cochainComplexHomOfDegreewise (piDeg c) (hpi c)) hDeg
    (fun c => HomologicalComplex.hom_ext _ _ (fun i => hretract c i)) h0 hsucc
    (fun c => HomologicalComplex.hom_ext _ _ (fun i => hsec c i)) b

end CosimplicialCompletedPair

/-! ### The interface the perturbation lemma plugs into -/

/-- **The comparison complex `R`, built from a family of abelian groups and a square-zero
differential.**

`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` produces the differential of its left
complex as a family of additive maps `dL` with `dL (i + 1) ∘ dL i = 0`, not as a cochain complex;
this is that family read as one. -/
public def deRhamComparisonTarget (N : ℕ → Type uN) [∀ i, AddCommGroup (N i)]
    (dL : ∀ i, N i →+ N (i + 1)) (hdL : ∀ (i : ℕ) (x : N i), dL (i + 1) (dL i x) = 0) :
    CochainComplex AddCommGrpCat.{uN} ℕ :=
  CochainComplex.of (fun i => AddCommGrpCat.of (N i)) (fun i => AddCommGrpCat.ofHom (dL i))
    (fun i => AddCommGrpCat.ext fun x => hdL i x)

/-- The differential of `Crystalline.deRhamComparisonTarget` is the given family. -/
public theorem deRhamComparisonTarget_d (N : ℕ → Type uN) [∀ i, AddCommGroup (N i)]
    (dL : ∀ i, N i →+ N (i + 1)) (hdL : ∀ (i : ℕ) (x : N i), dL (i + 1) (dL i x) = 0) (i : ℕ) :
    (deRhamComparisonTarget N dL hdL).d i (i + 1) = AddCommGrpCat.ofHom (dL i) :=
  CochainComplex.of_d (fun i => AddCommGrpCat.of (N i)) (fun i => AddCommGrpCat.ofHom (dL i)) i

namespace CosimplicialCompletedPair

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedPair.{u, v, w} E p)

/-- **The rowwise hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG] for a `K` built from a
pair, from the conclusion of the perturbation lemma element by element.**

This is the interface the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] plugs into.  Its
data and its seven hypotheses are the conclusion of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` — and of its instantiation at the
genuine completed divided power forms,
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_pushedConnection` — read in each
cosimplicial degree `b`, with nothing translated: `dL` is its perturbed differential, `iotaDeg`
its `ι'`, `piDeg` its `π'` and `hDeg` its `H`; `hdL` is its first conjunct, `hretract` its second,
`hiota` its third, `hpi` its fourth, and `h0` and `hsucc` its fifth and sixth.  Only `hsec` is
extra, and it is the retraction property of the codiagonal
(`Crystalline.completedEnvelopeCodiagonal_coprojection`), which is what makes the comparison
`rho` — running `K^{*,b} ⟶ R`, the direction the degeneration needs — a quasi-isomorphism from a
section running the other way.

The conclusion is the hypothesis `hrows` of `...SmallSite.computes07LG_of_doubleComplex`, and of
`...SmallSite.computes07LG_of_doubleComplex_rowwise` after
`Crystalline.quasiIso_row_of_quasiIso_flipMap`. -/
public theorem quasiIso_flipMap_of_deRhamAddHomHomotopyEquiv
    (N : ℕ → Type (max v w)) [∀ i, AddCommGroup (N i)] (dL : ∀ i, N i →+ N (i + 1))
    (hdL : ∀ (i : ℕ) (x : N i), dL (i + 1) (dL i x) = 0)
    (rho : W.doubleComplex ⟶
      constantCosimplicialCochainComplex.obj (deRhamComparisonTarget N dL hdL))
    (iotaDeg : ∀ (b i : ℕ), N i →+ W.toCosimplicialCompletedModule.obj i b)
    (piDeg : ∀ (b i : ℕ), W.toCosimplicialCompletedModule.obj i b →+ N i)
    (hDeg : ∀ (b i : ℕ), W.toCosimplicialCompletedModule.obj (i + 1) b →+
      W.toCosimplicialCompletedModule.obj i b)
    (hiota : ∀ (b i : ℕ) (x : N i),
      W.degreeDifferential b i (iotaDeg b i x) = iotaDeg b (i + 1) (dL i x))
    (hpi : ∀ (b i : ℕ) (y : W.toCosimplicialCompletedModule.obj i b),
      dL i (piDeg b i y) = piDeg b (i + 1) (W.degreeDifferential b i y))
    (hretract : ∀ (b i : ℕ) (x : N i), piDeg b i (iotaDeg b i x) = x)
    (h0 : ∀ (b : ℕ) (x : W.toCosimplicialCompletedModule.obj 0 b),
      hDeg b 0 (W.degreeDifferential b 0 x) + iotaDeg b 0 (piDeg b 0 x) = x)
    (hsucc : ∀ (b i : ℕ) (x : W.toCosimplicialCompletedModule.obj (i + 1) b),
      W.degreeDifferential b i (hDeg b i x) +
          hDeg b (i + 1) (W.degreeDifferential b (i + 1) x) +
          iotaDeg b (i + 1) (piDeg b (i + 1) x) = x)
    (hsec : ∀ (b i : ℕ) (x : N i),
      (W.rowDeRhamComparison rho b).f i (iotaDeg b i x) = x) (b : ℤ) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f b) := by
  refine W.quasiIso_flipMap_of_deRhamDegreewiseHomotopyEquiv rho
    (fun c i => AddCommGrpCat.ofHom (iotaDeg c i))
    (fun c i => AddCommGrpCat.ofHom (piDeg c i))
    (fun c i => AddCommGrpCat.ofHom (hDeg c i)) (fun c i => ?_) (fun c i => ?_)
    (fun c i => AddCommGrpCat.ext fun x => hretract c i x) (fun c => ?_) (fun c i => ?_)
    (fun c i => AddCommGrpCat.ext fun x => hsec c i x) b
  all_goals simp only [W.degreeDeRhamComplex_d, deRhamComparisonTarget_d]
  all_goals refine AddCommGrpCat.ext fun x => ?_
  · exact hiota c i x
  · exact hpi c i x
  · exact h0 c x
  · change hDeg c (i + 1) (W.degreeDifferential c (i + 1) x) +
        W.degreeDifferential c i (hDeg c i x) +
        iotaDeg c (i + 1) (piDeg c (i + 1) x) = x
    refine Eq.trans ?_ (hsucc c i x)
    abel

end CosimplicialCompletedPair

end Crystalline

end
