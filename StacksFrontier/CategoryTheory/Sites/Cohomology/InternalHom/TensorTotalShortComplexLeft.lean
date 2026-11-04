module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeStrictlyPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexFlip

/-!
# The row of total tensor complexes in the first tensor variable

Let `X` be a ringed site, let `T` be a short complex of cochain complexes of `O`-modules which is
split in every degree, and let `B` be a cochain complex of `O`-modules. Then

`Tot(T₁ ⊗_O B) ⟶ Tot(T₂ ⊗_O B) ⟶ Tot(T₃ ⊗_O B)`

is short exact. This is the first of the two rows of the dévissage of Stacks 0ATN part (2), whose
induction runs over the tensor factor.

The companion statement for a short complex varying in the **second** tensor factor is
`tensorTotalShortComplex_shortExact`, and it is already proved: it is what part (1)'s dévissage
needs, the source of the internal Hom entering the total tensor complex as its second factor.
Everything here is that statement transported along the Koszul symmetry
`tensorTotalFlipIso`, whose naturality makes the two rows isomorphic as short complexes. In
particular the degreewise family maps of the first tensor variable, and their four compatibility
lemmas, are not written a second time.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Section 20.48 (Tag 06YM)](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u} X.O) (ComplexShape.up ℤ)]

/-- **The total tensor-product morphism of a zero morphism and an identity vanishes.** This is
the left-hand companion of `tensorTotalMap_zero_right`, obtained from it by the symmetry of the
total tensor complex rather than by a second computation on local pure tensors. -/
lemma tensorTotalMap_zero_left
    {A A' B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} :
    tensorTotalMap X (0 : A ⟶ A') (𝟙 B) = 0 := by
  refine (cancel_mono (tensorTotalFlipIso X A' B).hom).1 ?_
  rw [tensorTotalFlipIso_hom_naturality, tensorTotalMap_zero_right, comp_zero, zero_comp]

/-- **The row obtained by tensoring a short complex of complexes with `B` in the second variable
and taking total complexes.** This is the companion of `tensorTotalShortComplex`, where the short
complex varies in the second tensor factor; here it varies in the first, which is the variable the
dévissage of Stacks 0ATN part (2) runs over. -/
def tensorTotalShortComplexLeft
    (T : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  ShortComplex.mk (tensorTotalMap X T.f (𝟙 B)) (tensorTotalMap X T.g (𝟙 B)) (by
    rw [tensorTotalMap_comp, Category.comp_id, T.zero, tensorTotalMap_zero_left])

/-- **The two rows agree under the symmetry of the total tensor complex.** Componentwise this is
`tensorTotalFlipIso`, and the two squares are its naturality. -/
def tensorTotalShortComplexLeftIso
    (T : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotalShortComplexLeft X T B ≅ tensorTotalShortComplex X B T :=
  ShortComplex.isoMk (tensorTotalFlipIso X T.X₁ B) (tensorTotalFlipIso X T.X₂ B)
    (tensorTotalFlipIso X T.X₃ B)
    (tensorTotalFlipIso_hom_naturality X T.f (𝟙 B)).symm
    (tensorTotalFlipIso_hom_naturality X T.g (𝟙 B)).symm

/-- **A degreewise split short complex of complexes stays short exact after `Tot(− ⊗_O B)`.**
This is `tensorTotalShortComplex_shortExact` transported along the symmetry; in particular no
second copy of the degreewise family maps in the first tensor variable is needed. -/
lemma tensorTotalShortComplexLeft_shortExact
    (T : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σ : ∀ q : ℤ, (T.map (HomologicalComplex.eval _ _ q)).Splitting)
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (tensorTotalShortComplexLeft X T B).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso (tensorTotalShortComplexLeftIso X T B)).2
    (tensorTotalShortComplex_shortExact X B T σ)

/-- **The symmetry of `tensorTotal` is natural, in the form that composes with the inverse.**
This is `tensorTotalFlipIso_hom_naturality` conjugated; it is the form in which the symmetry
gives an isomorphism *to* the row in the first variable from the one in the second. -/
theorem tensorTotalFlipIso_inv_naturality
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ A') (g : B ⟶ B') :
    (tensorTotalFlipIso X A B).inv ≫ tensorTotalMap X f g =
      tensorTotalMap X g f ≫ (tensorTotalFlipIso X A' B').inv :=
  (Iso.inv_comp_eq _).2
    (((Iso.eq_comp_inv _).2 (tensorTotalFlipIso_hom_naturality X f g)).trans
      (Category.assoc _ _ _))

/-- **The row in the first variable is split in every degree**, the splitting being the one of
the row in the second variable carried across by the symmetry. This is what the second row of the
dévissage of Stacks 0ATN part (2) consumes: `internalHomTermwiseSplittingTarget` needs the
splitting itself, not merely the short exactness. -/
def tensorTotalShortComplexLeftSplitting
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σ : ∀ q : ℤ, (S.map (HomologicalComplex.eval _ _ q)).Splitting)
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    ((tensorTotalShortComplexLeft X S B).map (HomologicalComplex.eval _ _ n)).Splitting :=
  ShortComplex.Splitting.ofIso (tensorTotalTermwiseSplitting X B S σ n)
    (ShortComplex.isoMk
      ((HomologicalComplex.eval _ _ n).mapIso (tensorTotalFlipIso X S.X₁ B).symm)
      ((HomologicalComplex.eval _ _ n).mapIso (tensorTotalFlipIso X S.X₂ B).symm)
      ((HomologicalComplex.eval _ _ n).mapIso (tensorTotalFlipIso X S.X₃ B).symm)
      (congrArg (fun φ => HomologicalComplex.Hom.f φ n)
        (tensorTotalFlipIso_inv_naturality X S.f (𝟙 B)))
      (congrArg (fun φ => HomologicalComplex.Hom.f φ n)
        (tensorTotalFlipIso_inv_naturality X S.g (𝟙 B))))

end AlgebraicGeometry.RingedSite

end
