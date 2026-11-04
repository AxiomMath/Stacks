module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialStructurePair
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexRow

/-!
# The rows of `K` are the completed de Rham complexes of the cosimplicial degrees

Let `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` be the double complex
`Crystalline.CosimplicialCompletedPair.doubleComplex` of a pair, with the de Rham differential
`Crystalline.CosimplicialCompletedPair.columnDifferential` in the `a` direction. For each
cosimplicial degree `b` the `a` direction of `K` is, on the nose, the completed de Rham complex

`M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}`

of that degree — `Crystalline.CompletedDeRham.complex` at the ring `D̂(b)`, the forms
`Ω^*_{D(b)}`, the module `M(b)` and the connection `∇_b` the pair carries. Composed with
`Crystalline.cosimplicialDoubleComplexRowIso` this identifies the rows of the double complex of
[Stacks, Proposition 60.21.3, Tag 07LG] with completed de Rham complexes.

## Main definitions

* `Crystalline.CosimplicialCompletedPair.rowDeRhamIso` — **the row `b` of `K` is the completed de
  Rham complex of the cosimplicial degree `b`.**
* `Crystalline.CosimplicialCompletedPair.flipRowDeRhamIso` and
  `Crystalline.CosimplicialCompletedPair.rowHomologyIso` — the same after the two `ℕ`-to-`ℤ`
  extensions, and the resulting identification of cohomology.
* `Crystalline.CosimplicialDPAlgebra.structureRowDeRhamIso` and
  `Crystalline.envelopeStructureRowDeRhamIso` — the same at the pair of the coefficient sheaf
  `𝒪_{X/S}`, where the de Rham complex of the degree `b` is the one of the universal connection
  `∇ x = 1 ⊗ d x` on `D̂(b)`.

## Main results

* `Crystalline.CosimplicialCompletedPair.acyclic_flip_X_of_acyclic_deRham` — a row of the double
  complex is acyclic as soon as the completed de Rham complex of its cosimplicial degree is.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Equation 60.17.3, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial
open DividedPowers

universe u v w uC

namespace Crystalline

namespace CosimplicialCompletedPair

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedPair.{u, v, w} E p)

/-- **The completed de Rham complex `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` of one cosimplicial degree**:
`Crystalline.CompletedDeRham.complex` at the completed ring `D̂(b)`, the forms `Ω^*_{D(b)}`, the
module `M(b)` and the connection `∇_b` of the pair.  Its square-zero hypothesis is the field
`isSquareZero` the pair carries. -/
def degreeDeRhamComplex (b : ℕ) : CochainComplex AddCommGrpCat.{max v w} ℕ :=
  CompletedDeRham.complex p (E.completedRing p b) (fun a => E.forms p a b) (E.wedge p b)
    (E.deRham p b) (W.carrier b) (W.nabla b) (E.isGradedLeibniz p b) (W.isSquareZero b)

/-- The exterior degree `a` of the completed de Rham complex of the cosimplicial degree `b` is
the term `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of the double complex. -/
theorem degreeDeRhamComplex_X (b a : ℕ) :
    (W.degreeDeRhamComplex b).X a =
      AddCommGrpCat.of (W.toCosimplicialCompletedModule.obj a b) := rfl

/-- The differential of the completed de Rham complex of the cosimplicial degree `b` is the de
Rham differential `Crystalline.CosimplicialCompletedPair.degreeDifferential` of that degree. -/
theorem degreeDeRhamComplex_d (b a : ℕ) :
    (W.degreeDeRhamComplex b).d a (a + 1) = AddCommGrpCat.ofHom (W.degreeDifferential b a) :=
  CompletedDeRham.complex_d p (E.completedRing p b) (fun a => E.forms p a b) (E.wedge p b)
    (E.deRham p b) (W.carrier b) (W.nabla b) (E.isGradedLeibniz p b) (W.isSquareZero b) a

/-- **The row `b` of the double complex `K` is the completed de Rham complex of the cosimplicial
degree `b`.** The comparison is the identity in every degree. -/
def rowDeRhamIso (b : ℕ) :
    cosimplicialRowComplex W.doubleComplex b ≅ W.degreeDeRhamComplex b := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro a a' h
  change a + 1 = a' at h
  subst h
  have hd : (cosimplicialRowComplex W.doubleComplex b).d a (a + 1) =
      (W.degreeDeRhamComplex b).d a (a + 1) := by
    rw [cosimplicialRowComplex_d, W.doubleComplex_d a, W.degreeDeRhamComplex_d b a]
    rfl
  simp only [Iso.refl_hom, hd]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- **The row `b` of the double complex of `K`, after the two `ℕ`-to-`ℤ` extensions, is the
extension of the completed de Rham complex of the cosimplicial degree `b`.**  This is
`Crystalline.cosimplicialDoubleComplexRowIso` composed with
`Crystalline.CosimplicialCompletedPair.rowDeRhamIso`. -/
def flipRowDeRhamIso (b : ℕ) :
    (cosimplicialDoubleComplexFunctor.obj W.doubleComplex).flip.X (b : ℤ) ≅
      (W.degreeDeRhamComplex b).extend ComplexShape.embeddingUpNat :=
  cosimplicialDoubleComplexRowIso W.doubleComplex b ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max v w}).mapIso (W.rowDeRhamIso b)

/-- **The cohomology of the row `b` of the double complex is the cohomology of the completed de
Rham complex `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}`**, in each degree. -/
def rowHomologyIso (b j : ℕ) :
    ((cosimplicialDoubleComplexFunctor.obj W.doubleComplex).flip.X (b : ℤ)).homology (j : ℤ) ≅
      (W.degreeDeRhamComplex b).homology j :=
  cosimplicialDoubleComplexRowHomologyIso W.doubleComplex b j ≪≫
    HomologicalComplex.homologyMapIso (W.rowDeRhamIso b) j

/-- **The cohomology of the row `b = 0` of the double complex is the cohomology of
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}`**, in each degree. -/
def rowZeroHomologyIso (j : ℕ) :
    ((cosimplicialDoubleComplexFunctor.obj W.doubleComplex).flip.X 0).homology (j : ℤ) ≅
      (W.degreeDeRhamComplex 0).homology j :=
  W.rowHomologyIso 0 j

/-- **A row of the double complex is acyclic as soon as the completed de Rham complex of its
cosimplicial degree is.** -/
theorem acyclic_flip_X_of_acyclic_deRham (b : ℕ)
    (h : ∀ j : ℕ, IsZero ((W.degreeDeRhamComplex b).homology j)) :
    ((cosimplicialDoubleComplexFunctor.obj W.doubleComplex).flip.X (b : ℤ)).Acyclic :=
  acyclic_cosimplicialDoubleComplex_flip_X W.doubleComplex b
    fun j => IsZero.of_iso (h j) (HomologicalComplex.homologyMapIso (W.rowDeRhamIso b) j)

/-- **The rows of the double complex of a pair at the nonzero integers are acyclic as soon as the
completed de Rham complex of each positive cosimplicial degree is.** -/
theorem acyclic_flip_X_of_ne_zero
    (h : ∀ b : ℕ, 0 < b → ∀ j : ℕ, IsZero ((W.degreeDeRhamComplex b).homology j))
    (b : ℤ) (hb : b ≠ 0) :
    ((cosimplicialDoubleComplexFunctor.obj W.doubleComplex).flip.X b).Acyclic := by
  rcases lt_or_ge b 0 with hneg | hpos
  · exact acyclic_cosimplicialDoubleComplex_flip_X_of_neg W.doubleComplex hneg
  · lift b to ℕ using hpos
    exact W.acyclic_flip_X_of_acyclic_deRham b
      (h b (by exact_mod_cast hb.lt_of_le' (Int.natCast_nonneg b)))

end CosimplicialCompletedPair

/-! ### The rows for the coefficient sheaf `𝒪_{X/S}` -/

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A] (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)

/-- **The row `b` of the structure sheaf's double complex `K` is the completed de Rham complex of
`D̂(b)` for the universal connection `∇ x = 1 ⊗ d x`.**  This is
`Crystalline.CosimplicialCompletedPair.rowDeRhamIso` at
`Crystalline.CosimplicialDPAlgebra.structurePair`. -/
def structureRowDeRhamIso (b : ℕ) :
    cosimplicialRowComplex (E.structureDoubleComplex p) b ≅
      (E.structurePair p).degreeDeRhamComplex b :=
  (E.structurePair p).rowDeRhamIso b

/-- **The cohomology of the row `b` of the structure sheaf's `K` is the cohomology of the
completed de Rham complex of `D̂(b)`.** -/
def structureRowHomologyIso (b j : ℕ) :
    ((cosimplicialDoubleComplexFunctor.obj
        (E.structureDoubleComplex p)).flip.X (b : ℤ)).homology (j : ℤ) ≅
      ((E.structurePair p).degreeDeRhamComplex b).homology j :=
  (E.structurePair p).rowHomologyIso b j

end CosimplicialDPAlgebra

/-! ### The rows at the actual cosimplicial envelope `D(*)` -/

section Envelope

variable (s : AffineCrystallineSituation.{u, uC}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- **The row `b` of the double complex `K` of the actual cosimplicial envelope `D(*)` and the
structure sheaf is the completed de Rham complex of `D̂(b)`**, at the rings `D(b)` of
[Stacks, Equation 60.17.3, Tag 07JF]. -/
def envelopeStructureRowDeRhamIso (b : ℕ) :
    cosimplicialRowComplex (envelopeStructureDoubleComplex s f) b ≅
      (envelopeStructurePair s f).degreeDeRhamComplex b :=
  (envelopeStructurePair s f).rowDeRhamIso b

/-- **The cohomology of the row `b` of the actual envelope's `K` is the cohomology of the
completed de Rham complex of `D̂(b)`.** -/
def envelopeStructureRowHomologyIso (b j : ℕ) :
    ((cosimplicialDoubleComplexFunctor.obj
        (envelopeStructureDoubleComplex s f)).flip.X (b : ℤ)).homology (j : ℤ) ≅
      ((envelopeStructurePair s f).degreeDeRhamComplex b).homology j :=
  (envelopeStructurePair s f).rowHomologyIso b j

end Envelope

end Crystalline

end
