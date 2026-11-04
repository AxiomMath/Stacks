module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# The Hom complex transported along an adjunction

Let `F ⊣ G` be an adjunction between preadditive categories with `F` additive. For a cochain
complex `X` in the source of `F` and a cochain complex `I` in its target, the degreewise
adjunction bijections assemble into an isomorphism of Hom complexes

`Hom(F X, I) ≅ Hom(X, G I)`.

This is the two-complex form of
`CategoryTheory.SimplicialSiteSituation.Augmentation.coyonedaComplexAdjIso`, which does the same
for a single object in the first variable; here both variables are complexes, so the
compatibility with the differential uses the naturality of `Adjunction.homEquiv` in *both*
variables rather than in the second alone.

## Main definitions

* `CochainComplex.cochainAdjAddEquiv`: the transport of cochains of a fixed degree, as an
  additive equivalence.
* `CochainComplex.homComplexAdjIso`: **the isomorphism `Hom(F X, I) ≅ Hom(X, G I)`**.

## Implementation notes

A cochain of degree `n` is a family of morphisms indexed by the triplets `⟨p, q, p + n = q⟩`, so
the transport is the adjunction bijection applied at each triplet, and additivity is
`CategoryTheory.Adjunction.homAddEquiv`. The differential of Mathlib's Hom complex is
`CochainComplex.HomComplex.δ`, whose expansion `CochainComplex.HomComplex.δ_v` has two terms: the
first is handled by `Adjunction.homEquiv_naturality_right` and the second, up to the sign
`Int.negOnePow`, by `Adjunction.homEquiv_naturality_left`.

The sign is a unit of `ℤ` acting on a hom-group, and an additive equivalence is not by itself
known to commute with that action; it does, by the two cases of
`Int.units_eq_one_or`, and that is the `key` step of the proof.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u₁ u₂

namespace CochainComplex

variable {A : Type u₁} [Category.{v} A] [Preadditive A]
  {B : Type u₂} [Category.{v} B] [Preadditive B]
  {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) [F.Additive] [G.Additive]

/-- The transport of cochains of degree `n` along an adjunction `F ⊣ G`: at each triplet
`⟨p, q, p + n = q⟩`, the adjunction bijection `Hom(F X_p, I_q) ≃ Hom(X_p, G I_q)`. -/
def cochainAdjAddEquiv (X : CochainComplex A ℤ) (I : CochainComplex B ℤ) (n : ℤ) :
    HomComplex.Cochain ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) I n ≃+
      HomComplex.Cochain X ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) n where
  toFun z := HomComplex.Cochain.mk fun p q hpq => adj.homAddEquiv (X.X p) (I.X q) (z.v p q hpq)
  invFun z := HomComplex.Cochain.mk fun p q hpq =>
    (adj.homAddEquiv (X.X p) (I.X q)).symm (z.v p q hpq)
  left_inv z := by ext p q hpq; simp
  right_inv z := by ext p q hpq; simp
  map_add' z₁ z₂ := by ext p q hpq; simp

/-- **An adjunction identifies the Hom complexes**: for `F ⊣ G` with `F` additive, the Hom
complex out of `F X` into `I` is the Hom complex out of `X` into `G I`. -/
def homComplexAdjIso (X : CochainComplex A ℤ) (I : CochainComplex B ℤ) :
    HomComplex ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) I ≅
      HomComplex X ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => AddEquiv.toAddCommGrpIso (cochainAdjAddEquiv adj X I n))
    (by
      intro i j hij
      ext (z : HomComplex.Cochain _ _ i)
      have hij' : i + 1 = j := hij
      change HomComplex.δ i j (cochainAdjAddEquiv adj X I i z) =
        cochainAdjAddEquiv adj X I j (HomComplex.δ i j z)
      ext p q hpq
      have key : ∀ (u : ℤˣ) (y : F.obj (X.X p) ⟶ I.X q),
          adj.homAddEquiv (X.X p) (I.X q) (u • y) =
            u • adj.homAddEquiv (X.X p) (I.X q) y := by
        intro u y
        rcases Int.units_eq_one_or u with rfl | rfl <;> simp
      rw [HomComplex.δ_v i j hij' (cochainAdjAddEquiv adj X I i z) p q hpq
        (q - 1) (p + 1) rfl rfl]
      change _ = adj.homAddEquiv (X.X p) (I.X q) ((HomComplex.δ i j z).v p q hpq)
      rw [HomComplex.δ_v i j hij' z p q hpq (q - 1) (p + 1) rfl rfl, map_add, key]
      simp only [Functor.mapHomologicalComplex_obj_d]
      congr 1
      · exact (adj.homEquiv_naturality_right _ _).symm
      · congr 1
        exact (adj.homEquiv_naturality_left _ _).symm)

end CochainComplex

end
