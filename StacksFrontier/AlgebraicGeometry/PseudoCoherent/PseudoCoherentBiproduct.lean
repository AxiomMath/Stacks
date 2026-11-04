module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `m`-pseudo-coherence is closed under finite direct sums

A finite direct sum of `m`-pseudo-coherent objects of the derived category of `𝒪_X`-modules is
`m`-pseudo-coherent. The binary case is Stacks 08CD part (2) applied to the split triangle
`A ⟶ A ⊞ B ⟶ B ⟶ A⟦1⟧`, and the general case follows by induction on the number of summands.

Stacks 09VA needs this: its hypothesis is that `i_*𝒪_Z` is pseudo-coherent as an `𝒪_X`-module,
while the triangle steps of its induction involve `i_*(𝒪_Z^{⊕n}[-p]) = (i_*𝒪_Z)^{⊕n}[-p]`.

## Main definitions

* `CategoryTheory.Limits.biproductFinSuccIso` splits off the first summand of a biproduct indexed
  by `Fin (n + 1)`.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_biprod`: the binary case.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_biproduct`: a biproduct of finitely many
  `m`-pseudo-coherent objects is `m`-pseudo-coherent.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_biproduct_const`: the case of a constant
  family, which is the form Stacks 09VA uses.

## Implementation notes

`CategoryTheory.Limits.biproductFinSuccIso` is stated here rather than reused from
`StacksFrontier/CategoryTheory/Triangulated/OperationsOnFullSubcategories.lean`, which has a
`CategoryTheory.Limits.biproductSumIso` from which it could be assembled: that file is outside the
import chain of the pseudo-coherence development, assembling the `Fin (n + 1)` form from it needs
a reindexing along `finSumFinEquiv` and a `⨁_{Fin 1} A ≅ A` as well, and the direct statement is
shorter than either. Both directions are built from `CategoryTheory.Limits.biproduct.ι` and
`CategoryTheory.Limits.biprod.inl`/`inr`, so the two identities are checked by `simp` on the
components after `CategoryTheory.Limits.biproduct.hom_ext'`.

The zero case of the induction is the empty biproduct, which is a zero object because
`CategoryTheory.Limits.biproduct.hom_ext'` has nothing to check.

## References

* [Stacks Project, Lemma 20.46.10 (Tag 08CD)](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated StrictlyPerfect

universe d u

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C]

/-- **Splitting off the first summand of a biproduct indexed by `Fin (n + 1)`**,
`⨁ f ≅ f 0 ⊞ ⨁ (f ∘ Fin.succ)`.

Both morphisms are assembled from the inclusions of the summands, so the two identities are
checked on the inclusions of `⨁ f`, resp. on the two inclusions of the binary biproduct. -/
public def biproductFinSuccIso (n : ℕ) (f : Fin (n + 1) → C) :
    (⨁ f) ≅ (f 0) ⊞ (⨁ (fun i : Fin n => f i.succ)) where
  hom := biproduct.desc (fun j => Fin.cases (motive := fun j => f j ⟶ _) biprod.inl
    (fun i => biproduct.ι (fun i : Fin n => f i.succ) i ≫ biprod.inr) j)
  inv := biprod.desc (biproduct.ι f 0) (biproduct.desc (fun i => biproduct.ι f i.succ))
  hom_inv_id := by
    refine biproduct.hom_ext' _ _ fun j => ?_
    induction j using Fin.cases <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp
    · apply biproduct.hom_ext'
      intro i
      simp

omit [HasBinaryBiproducts C] in
/-- A biproduct indexed by an empty type is a zero object: its identity morphism is zero, because
there is no inclusion of a summand on which to check anything. -/
public theorem isZero_biproduct_of_isEmpty {J : Type*} [Finite J] [IsEmpty J] (f : J → C) :
    IsZero (⨁ f) := by
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext' _ _ fun j => isEmptyElim j

end CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **A binary direct sum of `m`-pseudo-coherent objects is `m`-pseudo-coherent.**

The split triangle `A ⟶ A ⊞ B ⟶ B ⟶ A⟦1⟧` is distinguished, and its first and third terms are
`m`-pseudo-coherent, so Stacks 08CD part (2) applies to its second term. -/
@[sga "6 I 2.12" "Sufficiency"]
public theorem isPseudoCoherentFrom_biprod (m : ℤ) {A B : DerivedCategory (OXMod.{u, u} X)}
    (hA : IsPseudoCoherentFrom A m) (hB : IsPseudoCoherentFrom B m) :
    IsPseudoCoherentFrom (A ⊞ B) m :=
  isPseudoCoherentFrom_obj₂_of_distinguished m (binaryBiproductTriangle A B)
    (binaryBiproductTriangle_distinguished A B) hA hB

/-- **A finite direct sum of `m`-pseudo-coherent objects is `m`-pseudo-coherent.**

Induction on the number of summands. The empty direct sum is a zero object, hence
`m`-pseudo-coherent; the inductive step splits off the first summand with
`CategoryTheory.Limits.biproductFinSuccIso` and applies the binary case
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_biprod`. -/
@[sga "6 I 2.12" "partial"]
public theorem isPseudoCoherentFrom_biproduct (m : ℤ) :
    ∀ (n : ℕ) (f : Fin n → DerivedCategory (OXMod.{u, u} X)),
      (∀ i : Fin n, IsPseudoCoherentFrom (f i) m) → IsPseudoCoherentFrom (⨁ f) m := by
  intro n
  induction n with
  | zero =>
    exact fun f _ =>
      (isPseudoCoherent_of_isZero (isZero_biproduct_of_isEmpty f)).isPseudoCoherentFrom m
  | succ n ih =>
    intro f hf
    exact (isPseudoCoherentFrom_biprod m (hf 0) (ih _ fun i => hf i.succ)).ofIso
      (biproductFinSuccIso n f).symm

/-- **The `n`-fold direct sum of an `m`-pseudo-coherent object is `m`-pseudo-coherent.**

This is the form Stacks 09VA uses: its hypothesis gives pseudo-coherence of the single object
`i_*𝒪_Z`, and the triangle steps of its induction need it for `(i_*𝒪_Z)^{⊕n}`. -/
public theorem isPseudoCoherentFrom_biproduct_const (m : ℤ)
    {A : DerivedCategory (OXMod.{u, u} X)} (hA : IsPseudoCoherentFrom A m) (n : ℕ) :
    IsPseudoCoherentFrom (⨁ (fun _ : Fin n => A)) m :=
  isPseudoCoherentFrom_biproduct m n _ fun _ => hA

end AlgebraicGeometry.RingedSpace

end
