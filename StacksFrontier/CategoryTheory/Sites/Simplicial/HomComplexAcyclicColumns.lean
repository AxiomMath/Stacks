module

public import StacksFrontier.Algebra.Homology.ProductTotalAcyclic
public import StacksFrontier.CategoryTheory.Abelian.ExactOnHom
public import StacksFrontier.CategoryTheory.Sites.Simplicial.VanishingCohomology

/-!
# The Hom complex out of a resolution, when every column is acyclic

Let `P` be a chain complex indexed by `ℕ` in an abelian category and let `W` be a cochain
complex. Placing `P` in non-positive degrees, the Hom complex `Hom(P, W)` is the product total
complex of the double complex `Hom(P_p, W^q)`, whose `p`-th column is `Hom(P_p, W^•)`. So if
every one of those columns is acyclic, `Hom(P, W)` is acyclic.

This is the form in which the product-total-complex argument is used: the complex `W` need not be
K-injective, and the Hom complex out of an arbitrary complex into it need not compute anything —
only the columns, the Hom complexes out of the *terms* of `P`, are asked to be acyclic.

## Main results

* `CochainComplex.acyclic_homComplex_extend_of_acyclic_coyonedaComplex`: the statement above.
* `CochainComplex.acyclic_of_acyclic_coyonedaComplex`: a complex in an abelian category is acyclic
  as soon as the Hom complex out of every object is acyclic.
* `CochainComplex.acyclic_coyonedaComplex_of_isKInjective_of_acyclic`: the Hom complex into an
  acyclic K-injective complex is acyclic.
* `CochainComplex.acyclic_homComplex_extend_of_isKInjective_of_acyclic`: the instance when the
  columns are acyclic for the reason that occurs in practice, namely that each `Hom(P_p, W^•)` is
  the Hom complex into a K-injective acyclic complex.

## Implementation notes

The identification of the Hom complex with the product total complex is
`CochainComplex.homProductTotalIso`, and the acyclicity of a product total complex with acyclic
columns is `HomologicalComplex₂.acyclic_productTotal`; the `p`-th column of the double complex is
`CochainComplex.coyonedaComplex (P.X p) W` on the nose, by
`CochainComplex.homProductDoubleComplex_X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

/-- A shift of a zero object is a zero object, the shift being additive. -/
private lemma isZero_shift {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]
    [HasShift A ℤ] (i : ℤ) [(shiftFunctor A i).Additive] {Z : A} (hZ : IsZero Z) :
    IsZero (Z⟦i⟧) := by
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id (shiftFunctor A i),
    (IsZero.iff_id_eq_zero _).mp hZ, CategoryTheory.Functor.map_zero]

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The Hom complex out of a chain complex placed in non-positive degrees is acyclic as soon as
the Hom complex out of each of its terms is.** -/
theorem acyclic_homComplex_extend_of_acyclic_coyonedaComplex (P : ChainComplex C ℕ)
    (W : CochainComplex C ℤ) (h : ∀ p : ℕ, (coyonedaComplex (P.X p) W).Acyclic) :
    (CochainComplex.HomComplex (P.extend ComplexShape.embeddingDownNat) W).Acyclic := fun i =>
  (HomologicalComplex₂.exactAt_productTotal (K := homProductDoubleComplex P W) h i).of_iso
    (homProductTotalIso P W).symm

/-- **Acyclicity of a complex is detected by the Hom complexes out of objects**: a complex in an
abelian category is acyclic as soon as `Hom(T, -)` of it is acyclic for every object `T`.

Left exactness of `Hom(T, -)` is no obstruction, because `T` is allowed to be the kernel of the
differential; this is `Stacks.CategoryTheory.ExactOnHom.exact_of_forall_function_exact`. -/
theorem acyclic_of_acyclic_coyonedaComplex (Y : CochainComplex C ℤ)
    (h : ∀ T : C, (coyonedaComplex T Y).Acyclic) : Y.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff' Y (n - 1) n (n + 1) (by simp) (by simp)]
  refine Stacks.CategoryTheory.ExactOnHom.exact_of_forall_function_exact
    (Y.d (n - 1) n) (Y.d n (n + 1)) (Y.d_comp_d _ _ _) fun T => ?_
  have hT := h T n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)] at hT
  intro k
  refine ⟨fun hk => ?_, ?_⟩
  · exact (ShortComplex.ab_exact_iff _).mp hT k hk
  · rintro ⟨k', rfl⟩
    show (k' ≫ Y.d (n - 1) n) ≫ Y.d n (n + 1) = 0
    rw [Category.assoc, Y.d_comp_d, Limits.comp_zero]

/-- **The Hom complex into an acyclic K-injective complex is acyclic.** -/
theorem acyclic_coyonedaComplex_of_isKInjective_of_acyclic [HasDerivedCategory.{w} C] (X : C)
    (W : CochainComplex C ℤ) [W.IsKInjective] (hW : W.Acyclic) :
    (coyonedaComplex X W).Acyclic := by
  have hQ : IsZero (DerivedCategory.Q.obj W) := by
    have hq : QuasiIso (0 : W ⟶ W) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt (0 : W ⟶ W) i (hW i)).mpr (hW i)
    have h : IsIso (0 : DerivedCategory.Q.obj W ⟶ DerivedCategory.Q.obj W) := by
      simpa using (inferInstance : IsIso (DerivedCategory.Q.map (0 : W ⟶ W)))
    exact (IsZero.iff_id_eq_zero _).mpr (isIsoZeroSelfEquiv _ h)
  intro i
  refine exactAt_coyonedaComplex X W i ?_
  exact ⟨fun f g => (isZero_shift i hQ).eq_of_tgt f g⟩

/-- **The Hom complex out of a chain complex placed in non-positive degrees, into an acyclic
K-injective complex, is acyclic.** -/
theorem acyclic_homComplex_extend_of_isKInjective_of_acyclic [HasDerivedCategory.{w} C]
    (P : ChainComplex C ℕ) (W : CochainComplex C ℤ) [W.IsKInjective] (hW : W.Acyclic) :
    (CochainComplex.HomComplex (P.extend ComplexShape.embeddingDownNat) W).Acyclic :=
  acyclic_homComplex_extend_of_acyclic_coyonedaComplex P W fun p =>
    acyclic_coyonedaComplex_of_isKInjective_of_acyclic (P.X p) W hW

end CochainComplex

end
