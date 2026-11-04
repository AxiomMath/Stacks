module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison

/-!
# The Koszul symmetry of the total tensor complex, and its naturality

Let `X` be a ringed site. The total tensor complex of Stacks 06YM is symmetric up to the Koszul
signs, and on the `tensorComplex` construction that symmetry is
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso`. This file records two things that symmetry
needs in order to be used as a transport: that it is **natural** in both complexes, and that it
transports along `tensorTotalIsoTensorComplex` to the `tensorTotal` construction, where it is
again natural.

The point of it is the dévissage of Stacks 0ATN part (2). That dévissage runs over the **tensor
factor** of the interchange morphism of Stacks 0BYR, whereas the dévissage of part (1) runs over
the source of the internal Hom, which enters the total tensor complex as its second factor. The
machinery for a degreewise split short complex of second factors — the degreewise family maps and
the short exactness of the resulting row — is therefore already present, and the symmetry carries
it to the first factor instead of a second copy being written.

## References

* [Stacks Project, Section 20.48 (Tag 06YM)](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u v w

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(sheafTensor.{u, v, w} R).Additive]
  [∀ M, ((sheafTensor.{u, v, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{w} (ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor R) (ComplexShape.up ℤ)]

/-- **The Koszul symmetry of the total tensor complex is natural in both complexes.** The
symmetry `tensorComplexFlipIso` of Stacks 06YM is the isomorphism of bifunctors given by the
braiding followed by the comparison of a bifunctor with its flip; this is the composite of the
naturality of those two, `HomologicalComplex.mapBifunctorNatIso_hom_naturality` and Mathlib's
`HomologicalComplex.mapBifunctorFlipIso_hom_naturality`.

It is stated here rather than beside `tensorComplexFlipIso` because that declaration's file has
nine importers, one of them expensive, and nothing else in this development needs it. -/
@[reassoc (attr := simp)]
theorem tensorComplexFlipIso_hom_naturality
    {K K' L L' : CochainComplex (SheafOfModules.{w} (ringSheaf.{u, v, w} R)) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    HomologicalComplex.mapBifunctorMap f g (sheafTensor R) (ComplexShape.up ℤ) ≫
        (tensorComplexFlipIso R K' L').hom =
      (tensorComplexFlipIso R K L).hom ≫
        HomologicalComplex.mapBifunctorMap g f (sheafTensor R) (ComplexShape.up ℤ) := by
  dsimp only [tensorComplexFlipIso]
  have hnat := HomologicalComplex.mapBifunctorNatIso_hom_naturality K L (ComplexShape.up ℤ)
    (sheafTensorBraiding R) f g
  have hflip := HomologicalComplex.mapBifunctorFlipIso_hom_naturality
    (F := sheafTensor R) (c := ComplexShape.up ℤ) (φ₁ := g) (φ₂ := f)
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (HomologicalComplex.mapBifunctorFlipIso L' K' (sheafTensor R)
        (ComplexShape.up ℤ)).hom) hnat).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => (HomologicalComplex.mapBifunctorNatIso K L (ComplexShape.up ℤ)
            (sheafTensorBraiding R)).hom ≫ z) hflip).trans
          (Category.assoc _ _ _).symm))))

end Stacks.SheafOfModules.Tensor

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.Tensor

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u} X.O) (ComplexShape.up ℤ)]

/-- **The Koszul symmetry of the total tensor complex, for the sheafify-then-totalise
construction.** `AlgebraicGeometry.RingedSite.tensorTotal` and
`Stacks.SheafOfModules.Tensor.tensorComplex` are the two total tensor complexes on a ringed site
and agree by `tensorTotalIsoTensorComplex`; this transports the symmetry of the second to the
first. -/
def tensorTotalFlipIso
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotal X A B ≅ tensorTotal X B A :=
  tensorTotalIsoTensorComplex X A B ≪≫ tensorComplexFlipIso X.O A B ≪≫
    (tensorTotalIsoTensorComplex X B A).symm

/-- **The comparison of the two total tensor complexes is natural, in the form that composes
with the forward map.** `tensorTotalIsoTensorComplex_naturality` states the square with the
inverse; this is the same square read with the isomorphism the other way round, which is the
form a transport along it needs. -/
@[reassoc (attr := simp)]
theorem tensorTotalIsoTensorComplex_hom_naturality
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ A') (g : B ⟶ B') :
    tensorTotalMap X f g ≫ (tensorTotalIsoTensorComplex X A' B').hom =
      (tensorTotalIsoTensorComplex X A B).hom ≫
        HomologicalComplex.mapBifunctorMap f g (sheafTensor X.O) (ComplexShape.up ℤ) := by
  have h2 := (Iso.inv_comp_eq (tensorTotalIsoTensorComplex X A B)).1
    (tensorTotalIsoTensorComplex_naturality X f g)
  exact (congrArg (fun z => z ≫ (tensorTotalIsoTensorComplex X A' B').hom) h2).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun z => (tensorTotalIsoTensorComplex X A B).hom ≫ z)
        (((Category.assoc _ _ _).trans
          (congrArg (fun z => HomologicalComplex.mapBifunctorMap f g (sheafTensor X.O)
            (ComplexShape.up ℤ) ≫ z)
            (tensorTotalIsoTensorComplex X A' B').inv_hom_id)).trans
          (Category.comp_id _))))

/-- **The symmetry of `tensorTotal` is natural in both complexes.** This is what makes the
symmetry usable for transporting a statement about a short complex of complexes from one tensor
variable to the other: a square for the morphisms `tensorTotalMap X f g` and
`tensorTotalMap X g f`. -/
theorem tensorTotalFlipIso_hom_naturality
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ A') (g : B ⟶ B') :
    tensorTotalMap X f g ≫ (tensorTotalFlipIso X A' B').hom =
      (tensorTotalFlipIso X A B).hom ≫ tensorTotalMap X g f := by
  simp only [tensorTotalFlipIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    tensorTotalIsoTensorComplex_hom_naturality_assoc]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => (tensorTotalIsoTensorComplex X A B).hom ≫ z)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (tensorTotalIsoTensorComplex X B' A').inv)
          (tensorComplexFlipIso_hom_naturality X.O f g)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun z => (tensorComplexFlipIso X.O A B).hom ≫ z)
              (tensorTotalIsoTensorComplex_naturality X g f).symm)))))

end AlgebraicGeometry.RingedSite

end
