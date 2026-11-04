module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.Exactness
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Polynomial
import StacksCore.Tactic.StacksAttribute

/-!
# The terms of the Koszul complex on projective space are vector bundles

Let `A` be a ring and `X = P^n_A = Proj A[X₀, …, Xₙ]`. The `j`-th term of the Koszul complex of
the coordinates is a direct sum of copies of `𝒪_X(a+j)` indexed by the `j`-element subsets of
the coordinates, and each twisting sheaf is trivial on the standard open of a degree-one
element. Since `A[X₀, …, Xₙ]` is generated in degree one over its degree-zero part those
standard opens cover `X`, so the `j`-th term is free on each member of a covering, on an index
set of cardinality `binom(n+1, j)`: it is a vector bundle of that rank.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulTermOverIso`: the `j`-th term, restricted to
  the standard open of a degree-one element, is free on the `j`-element subsets.

## Main results

* `Stacks.AlgebraicGeometry.ProjKoszulComplex.adjoin_degree_one_polyGrading`: the polynomial ring
  is generated in degree one over its degree-zero part.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.exists_coversTop_nonempty_iso_free_koszulTerm`:
  **every term of the Koszul complex is a vector bundle**, free on the subsets of the coordinates
  of the corresponding cardinality over each member of a covering.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.acyclic_koszulComplex_and_locallyFree_koszulTerm`:
  **Stacks 0BQS**, the exactness of the complex together with the rank and local freeness of its
  terms.

## Implementation notes

The restriction functor to a slice of the site is additive, and an additive functor between
preadditive categories with finite biproducts preserves finite biproducts, so
`CategoryTheory.Functor.mapBiproduct` carries the restriction of the direct sum to the direct sum
of the restrictions. The remaining two steps are the trivialization of each twisting sheaf, which
is Tag 01MS at degree one, and the identification of a finite direct sum of copies of the unit
object with the free sheaf of modules, which is `CategoryTheory.Limits.biproduct.isoCoproduct`
together with the definition of `SheafOfModules.free` as a coproduct.

Local freeness is stated as the existence of a covering over whose members the term is
isomorphic to a free sheaf of modules, rather than as the class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`: packaging the same data as an instance of
that class exhausts the elaborator, because its instance arguments quantify over every object of
the site and have to be resynthesized inside the structure instance.

The index set of the free presentation is `ULift` of the set of subsets of the coordinates of the
given cardinality, since `SheafOfModules.free` takes its index in the universe of the sheaf of
modules while the index set of the direct sum has to lie in `Type 0` for
`CategoryTheory.Limits.biproduct.matrix` to apply.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 0BQS](https://stacks.math.columbia.edu/tag/0BQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjKoszulComplex

universe u

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The category of sheaves of modules over the restriction of the structure sheaf of
`Proj (A[X₀, …, Xₙ])` to an open `U` has finite biproducts. -/
local instance hasFiniteBiproducts_over
    (U : Opens (ProjectiveSpectrum.top (polyGrading A n))) :
    HasFiniteBiproducts (SheafOfModules.{u} ((projRingSheaf (polyGrading A n)).over U)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **The polynomial ring is generated in degree one over its degree-zero part.** This is the
hypothesis under which the standard opens of the degree-one elements cover `Proj`. -/
theorem adjoin_degree_one_polyGrading :
    Algebra.adjoin (polyGrading A n 0)
      ((polyGrading A n 1 : Set (MvPolynomial (Fin (n + 1)) A))) = ⊤ := by
  have h := Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule
    (Fin (n + 1)) A
  have hset : (Set.range fun f : polyGrading A n 1 => (f : MvPolynomial (Fin (n + 1)) A)) =
      (polyGrading A n 1 : Set (MvPolynomial (Fin (n + 1)) A)) := by
    ext p; simp
  rwa [hset] at h

variable (a : ℤ)

/-- **The `j`-th term of the Koszul complex is free on the `j`-element subsets of the coordinates
over the standard open of a degree-one element.** The restriction functor carries the direct sum
to the direct sum of the restrictions, each twisting sheaf is trivial there, and a finite direct
sum of copies of the structure sheaf is the free sheaf of modules. -/
def koszulTermOverIso (j : ℤ) {f : MvPolynomial (Fin (n + 1)) A} (hf : f ∈ polyGrading A n 1) :
    SheafOfModules.free.{u} (ULift.{u} (koszulIndex (n + 1) j)) ≅
      (koszulTerm A n a j).over (ProjectiveSpectrum.basicOpen (polyGrading A n) f) :=
  ((Sigma.whiskerEquiv (Equiv.ulift (α := koszulIndex (n + 1) j)) fun _ =>
      Iso.refl (SheafOfModules.unit ((projRingSheaf (polyGrading A n)).over
        (ProjectiveSpectrum.basicOpen (polyGrading A n) f)))).trans
    ((biproduct.isoCoproduct fun _ : koszulIndex (n + 1) j =>
        SheafOfModules.unit ((projRingSheaf (polyGrading A n)).over
          (ProjectiveSpectrum.basicOpen (polyGrading A n) f))).symm.trans
      ((biproduct.mapIso fun _ : koszulIndex (n + 1) j =>
          (ProjDegreeOne.twistingSheafOverBasicOpenDegreeOneIsoUnit (polyGrading A n) f hf
            (a + j)).symm).trans
        (Functor.mapBiproduct (SheafOfModules.overFunctor (projRingSheaf (polyGrading A n))
          (ProjectiveSpectrum.basicOpen (polyGrading A n) f))
          (koszulFamily A n a j)).symm)))

/-- **Every term of the Koszul complex of the coordinates on `P^n_A` is a vector bundle**: the
standard opens of the degree-one elements cover `P^n_A`, and over each of them the `j`-th term is
free on the `j`-element subsets of the coordinates, of which there are `binom(n+1, j)` by
`Stacks.AlgebraicGeometry.ProjKoszulComplex.card_koszulIndexFin`. -/
theorem exists_coversTop_nonempty_iso_free_koszulTerm (j : ℤ) :
    ∃ (I : Type u) (U : I → Opens (ProjectiveSpectrum.top (polyGrading A n))),
      (Opens.grothendieckTopology (ProjectiveSpectrum.top (polyGrading A n))).CoversTop U ∧
        ∀ f : I, Nonempty (SheafOfModules.free.{u} (ULift.{u} (koszulIndex (n + 1) j)) ≅
          (koszulTerm A n a j).over (U f)) :=
  ⟨↥(polyGrading A n 1),
    fun f => ProjectiveSpectrum.basicOpen (polyGrading A n) (f : MvPolynomial (Fin (n + 1)) A),
    ProjDegreeOne.coversTop_basicOpen_degreeOne (polyGrading A n)
      (adjoin_degree_one_polyGrading A n),
    fun f => ⟨koszulTermOverIso A n a j f.2⟩⟩

/-! ### The statement of the tag -/

/-- **Stacks 0BQS.** Let `A` be a ring and `X = P^n_A = Proj A[X₀, …, Xₙ]`. For every integer `a`
there is an exact complex of vector bundles

`0 ⟶ 𝒪_X(a) ⟶ … ⟶ 𝒪_X(a+j)^{⊕ binom(n+1, j)} ⟶ … ⟶ 𝒪_X(a+n+1) ⟶ 0`

on `X`, namely the Koszul complex `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulComplex` of
the coordinates `X₀, …, Xₙ`, graded so that the generators of the `j`-th exterior power sit in
degree `j` and twisted by `a`. Its `j`-th term is the direct sum of copies of `𝒪_X(a+j)` indexed
by the `j`-element subsets of the coordinates, of which there are `binom(n+1, j)`, and each term
is free on that index set over every standard open of a degree-one element, those opens covering
`X`; the complex is acyclic, so it is exact in every degree, and it is concentrated in degrees
`0, …, n+1` because outside that range the index set is empty. -/
@[stacks 0BQS]
theorem acyclic_koszulComplex_and_locallyFree_koszulTerm (j : ℕ) :
    (koszulComplex A n a).Acyclic ∧
      (koszulComplex A n a).X (j : ℤ) =
        (⨁ fun _ : koszulIndex (n + 1) (j : ℤ) =>
          twistingSheaf (polyGrading A n) (a + (j : ℤ))) ∧
      Fintype.card (koszulIndex (n + 1) (j : ℤ)) = (n + 1).choose j ∧
      ∃ (I : Type u) (U : I → Opens (ProjectiveSpectrum.top (polyGrading A n))),
        (Opens.grothendieckTopology (ProjectiveSpectrum.top (polyGrading A n))).CoversTop U ∧
          ∀ f : I, Nonempty (SheafOfModules.free.{u} (ULift.{u} (koszulIndex (n + 1) (j : ℤ))) ≅
            (koszulTerm A n a (j : ℤ)).over (U f)) :=
  ⟨acyclic_koszulComplex A n a, rfl, card_koszulIndexFin n j,
    exists_coversTop_nonempty_iso_free_koszulTerm A n a (j : ℤ)⟩

end Stacks.AlgebraicGeometry.ProjKoszulComplex

end
