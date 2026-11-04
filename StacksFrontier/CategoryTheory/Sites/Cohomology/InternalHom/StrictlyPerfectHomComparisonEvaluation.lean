module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingHomEquiv
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorsorsAndColimits.KFlatResolution

/-! # The evaluation square of Tag 0GM7, released to a K-flat source

Let `(C, O)` be a ringed site and let `B`, `C` be complexes of `O`-modules with `B` K-flat.  The
evaluation square the dévissage of Tag 0GM7 asks for compares two evaluation morphisms

`Q(SheafHom(B, C)) ⊗^𝐋_O QB ⟶ QC`:

the derived one, the value of the bijection of Stacks 08DI at an identity, precomposed with the
comparison of Stacks 08DM, and the class of the cochain-level evaluation morphism
`Tot(SheafHom(B, C) ⊗_O B) ⟶ C` of Tag 0A90, precomposed with the one-sided K-flat comparison of
Stacks 06YU.

This file does not prove that square.  What it does is **reduce it to the same statement at a
K-flat source**, which is what removes the last hypothesis on `C` from the route:

* each side of the square has a version at a morphism of complexes `f : A ⟶ SheafHom(B, C)` in
  place of the identity, and both versions are the square itself pushed along `f`
  (`comparisonRight_comp_curryHomEquiv` on the cochain side, Stacks 08J8 in the source variable
  on the derived side);
* so the square at the identity and the square at `f` are equivalent as soon as `Q f` is
  invertible, and `f` may be taken to be a K-flat resolution (Stacks 06YS).

The point of the reduction is that the Stacks 08JA preimage of the comparison of Stacks 08DM,
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparisonClass`, is available at a K-flat
source with **no hypothesis on the target**, whereas at the source `SheafHom(B, C)` of the square
itself its K-flatness hypothesis is Stacks 0GM5 and needs `C` K-flat.  After the reduction below
that hypothesis is gone: `AlgebraicGeometry.RingedSite.kFlatResolution_kFlat` supplies the
K-flatness of the source for an arbitrary `C`.

## Main results

* `AlgebraicGeometry.RingedSite.comparisonRight_comp_curryHomEquiv`: the cochain side of the
  square is natural in the source — the K-flat comparison of Stacks 06YU followed by the class of
  the transpose of `f` is `f ⊗ 1` followed by the K-flat comparison and the class of the
  cochain-level evaluation.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_Q_map_comp`: the derived side of the square
  is natural in the source, by Stacks 08J8 in the source variable — for an arbitrary morphism
  `σ : Q(SheafHom(B, C)) ⟶ RSheafHom(QB, QC)` of `D(O)` in place of the comparison of
  Stacks 08DM, which is all the argument uses.
* `AlgebraicGeometry.RingedSite.curryingSquare_of_evaluationSquare` and
  `AlgebraicGeometry.RingedSite.evaluationSquare_of_curryingSquare`: the two squares imply each
  other, the second one as soon as `Q f` is invertible.
* `AlgebraicGeometry.RingedSite.evaluationSquare_of_curryingSquare_kFlatResolution`: **the
  reduction**, at the chosen K-flat resolution of `SheafHom(B, C)`.

## Nothing here is tagged

The square itself is a step of the *proof* of Tag 0GM7 — the published statement of Tag 0GM7 is
the invertibility of the base-change map of Tag 08I3 — and the statements below are two
naturality properties of its two sides together with the equivalence they produce.  Stacks 08J8
is carried by `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` and by
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, and Stacks 06YS by the
chosen resolution in `Stacks.Cohomology`.  No declaration here carries a tag.

## What is still owed

The hypothesis of `evaluationSquare_of_curryingSquare_kFlatResolution` at
`σ = strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C`, written out at the
chosen resolution `P = Stacks.Cohomology.kFlatResolution X SheafHom(B, C)` with augmentation
`p = Stacks.Cohomology.kFlatResolutionHom X SheafHom(B, C)`:

```
derivedCurryHomEquiv X (Q.obj P) (Q.obj B) (Q.obj C)
    (Q.map p ≫ strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C) =
  ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight P B hB).hom ≫
    DerivedCategory.Q.map (curryHomEquiv X P B C p)
```

There `P` is K-flat with **no hypothesis on `C`**, so
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparisonClass` applies — its two K-flatness
hypotheses are `hB` and the K-flatness of `P` — and what remains is the computation of the
degree-zero global hypercohomology of the currying isomorphism of Stacks 08DJ on that class.

## Implementation notes

*The comparison is a variable.*  Nothing in the two naturality statements, nor in the
equivalence they produce, uses what the morphism
`σ : Q(SheafHom(B, C)) ⟶ RSheafHom(QB, QC)` is: the derived side is Stacks 08J8 in the source
variable, which holds for an arbitrary morphism of `D(O)`.  So `σ` is a variable here, and a
consumer supplies the comparison of Stacks 08DM at whatever spelling it has.  That is not only a
strengthening; it is what makes the statements usable at a ringed space.  With the comparison
written into the statements as
`strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C`, a ringed-space consumer
must identify that datum with `Stacks.SheafOfModules.derivedInternalHom Rc`, and although the two
are equal by `rfl`, the `exact` that decides it **exhausts `maxRecDepth`**.  With `σ`
a variable there is no identification to make.

*The site-level statement does elaborate.*  The implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCurryingComparisonArbitraryTarget`
record that a site-level statement joining `strictlyPerfectHomComparison` to the derived currying
isomorphism "would not typecheck", because
`AlgebraicGeometry.RingedSite.canonicalDerivedInternalHom` is a `Classical.choice` and is not the
bifunctor `derivedSheafHomBifunctor X` that `derivedCurryIso` is built from.  That is true of
`canonicalDerivedInternalHom` and false of
`AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor`, whose `hom` field is that bifunctor
by `rfl` (`AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor_hom`): the joined statement
elaborates at the site with that datum, which is why the statements here are site-level and not
space-level.

*One further crossing.*  At a ringed space the conclusion must be written with
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite Rc)` and
not with the abbreviation `Stacks.SheafOfModules.derivedSheafHom Rc` in the object argument of
`derivedCurryHomEquiv`: the two are the same by delta, but matching them there exhausts
`maxRecDepth`, while `Stacks.SheafOfModules.derivedTensor Rc` in the same statement costs
nothing.

`comparisonRight_comp_curryHomEquiv` is finished by `paste_right`, a two-square pasting over an
abstract category with every object and morphism a variable, rather than by rewriting with the
naturality hypothesis in place: the rewrite is rejected — `did not find an occurrence` of a
pattern the goal prints verbatim — because `rw` re-checks the goal at a transparency at which
these derived-category composites do not match, while `exact` settles the same step with one
definitional-equality check.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0GM5](https://stacks.math.columbia.edu/tag/0GM5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable
  (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (σ : DerivedCategory.Q.obj (sheafHomComplex X B C).obj ⟶
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
      (DerivedCategory.Q.obj C))

/-- Two commuting squares in a row paste.  Stated over an abstract category with every object and
morphism a variable, which is what makes the step below one definitional-equality check instead
of a keyed rewrite inside the derived category of a category of module sheaves. -/
private lemma paste_right {D : Type*} [Category D] {a b c d e : D}
    (u : a ⟶ b) (p : b ⟶ c) (q : a ⟶ d) (r : d ⟶ c) (z : c ⟶ e)
    (h : u ≫ p = q ≫ r) : q ≫ r ≫ z = u ≫ p ≫ z := by
  rw [← Category.assoc, ← h, Category.assoc]

/-! ### The cochain side of the square is natural in the source -/

/-- **The cochain-level side of the evaluation square is the square at the identity, pushed along
`f`.**  For complexes `A`, `B`, `C` of `O`-modules with `B` K-flat and a morphism of complexes
`f : A ⟶ SheafHom(B, C)`, the one-sided K-flat comparison of Stacks 06YU followed by the class of
the transpose of `f` is `f ⊗ 1` followed by the K-flat comparison at `SheafHom(B, C)` and the
class of the cochain-level evaluation morphism of Tag 0A90.

The two ingredients are that the transpose of `f` is `f ⊗ 1` followed by the evaluation
(`AlgebraicGeometry.RingedSite.curryHomEquiv_eq_tensor_evaluation`) and the naturality of the
K-flat comparison in its left variable, at the identity of `B`. -/
theorem comparisonRight_comp_curryHomEquiv (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom ≫
        DerivedCategory.Q.map (curryHomEquiv X A B C f) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight
            (sheafHomComplex X B C).obj B hB).hom ≫
          DerivedCategory.Q.map (cochainEvaluation X B C) := by
  -- The map of total tensor complexes induced by `f` and the identity of `B` is the value at `B`
  -- of the image of `f` under the total tensor complex functor; that holds by `rfl`.
  have hmb : HomologicalComplex.mapBifunctorMapReg f (𝟙 B)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app B := rfl
  have hnat := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight_naturality
    f (𝟙 B) hB hB
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, Category.id_comp, hmb] at hnat
  have hc : DerivedCategory.Q.map (curryHomEquiv X A B C f) =
      DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app B) ≫
        DerivedCategory.Q.map (cochainEvaluation X B C) := by
    rw [curryHomEquiv_eq_tensor_evaluation X A B C f, CategoryTheory.Functor.map_comp]
  rw [hc]
  exact paste_right _ _ _ _ _ hnat

/-! ### The derived side of the square is natural in the source -/

/-- **The derived side of the evaluation square is the square at the identity, pushed along
`f`.**  The value of the bijection of Stacks 08DI at `Q f ≫ σ` is `f ⊗ 1` followed by `σ`
tensored with the identity and the derived evaluation.

`σ` is an arbitrary morphism `Q(SheafHom(B, C)) ⟶ RSheafHom(QB, QC)` of `D(O)` — in the
application the comparison of Stacks 08DM, of which the argument uses nothing.

This is Stacks 08J8 in the source variable
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`) followed by the
reduction of the bijection to its value at an identity
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation`). -/
theorem derivedCurryHomEquiv_Q_map_comp
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    derivedCurryHomEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C)
        (DerivedCategory.Q.map f ≫ σ) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map σ).app
            (DerivedCategory.Q.obj B) ≫
          derivedCurryHomEquiv X
            (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
              (DerivedCategory.Q.obj C))
            (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) := by
  have h1 := derivedCurryHomEquiv_naturality_source X (DerivedCategory.Q.map f) σ
  have h2 := derivedCurryHomEquiv_eq_tensor_evaluation X
    (DerivedCategory.Q.obj (sheafHomComplex X B C).obj) (DerivedCategory.Q.obj B)
    (DerivedCategory.Q.obj C)
    σ
  simp only [h1, h2]

/-! ### The two squares imply each other -/

/-- **The evaluation square implies the currying square at every source.**  If the derived
evaluation of Stacks 08DI, precomposed with `σ` tensored with the identity, is the K-flat
comparison of Stacks 06YU followed by the class of the cochain-level evaluation, then the
bijection of Stacks 08DI carries `Q f ≫ σ` to the K-flat comparison followed by the class
of the transpose of `f`, for every morphism of complexes `f : A ⟶ SheafHom(B, C)`. -/
theorem curryingSquare_of_evaluationSquare (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hev : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map σ).app
          (DerivedCategory.Q.obj B) ≫
        derivedCurryHomEquiv X
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
            (DerivedCategory.Q.obj C))
          (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight
          (sheafHomComplex X B C).obj B hB).hom ≫
        DerivedCategory.Q.map (cochainEvaluation X B C))
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    derivedCurryHomEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C)
        (DerivedCategory.Q.map f ≫ σ) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom ≫
        DerivedCategory.Q.map (curryHomEquiv X A B C f) :=
  ((derivedCurryHomEquiv_Q_map_comp X A B C σ f).trans
    (congrArg (fun t => ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B) ≫ t) hev)).trans
    (comparisonRight_comp_curryHomEquiv X A B C hB f).symm

/-- **The currying square at one source with `Q f` invertible implies the evaluation square.**
Both sides of the currying square are the corresponding side of the evaluation square
precomposed with `f ⊗ 1`, so when `Q f` is invertible — and therefore so is `Q f ⊗ 1`, the
derived tensor product being a functor in each variable — that factor cancels.

This is the step that releases the target: the currying square may be read at a source of one's
choosing, and a K-flat one exists for an arbitrary `C`. -/
theorem evaluationSquare_of_curryingSquare (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (f : A ⟶ (sheafHomComplex X B C).obj) (hf : IsIso (DerivedCategory.Q.map f))
    (hcurry : derivedCurryHomEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C)
        (DerivedCategory.Q.map f ≫ σ) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom ≫
        DerivedCategory.Q.map (curryHomEquiv X A B C f)) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map σ).app
        (DerivedCategory.Q.obj B) ≫
      derivedCurryHomEquiv X
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
          (DerivedCategory.Q.obj C))
        (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) =
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight
        (sheafHomComplex X B C).obj B hB).hom ≫
      DerivedCategory.Q.map (cochainEvaluation X B C) := by
  have := hf
  have : IsIso (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B)) := inferInstance
  exact (cancel_epi (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B))).1
    ((derivedCurryHomEquiv_Q_map_comp X A B C σ f).symm.trans
      (hcurry.trans (comparisonRight_comp_curryHomEquiv X A B C hB f)))

/-- **The reduction of the evaluation square to a K-flat source.**  The square follows from the
currying square at the chosen K-flat resolution of `SheafHom(B, C)` (Stacks 06YS), whose
augmentation is a quasi-isomorphism and therefore invertible in `D(O)`.

No hypothesis on `C` is carried, and that is the point: at the source `SheafHom(B, C)` of the
square itself the Stacks 08JA preimage of the comparison of Stacks 08DM needs that complex to be
K-flat, which is Stacks 0GM5 and asks for `C` K-flat, whereas
`Stacks.Cohomology.kFlatResolution_kFlat` gives a K-flat source for an arbitrary `C`. -/
theorem evaluationSquare_of_curryingSquare_kFlatResolution
    (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hcurry : derivedCurryHomEquiv X
        (DerivedCategory.Q.obj (Stacks.Cohomology.kFlatResolution X (sheafHomComplex X B C).obj))
        (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C)
        (DerivedCategory.Q.map
            (Stacks.Cohomology.kFlatResolutionHom X (sheafHomComplex X B C).obj) ≫
          σ) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight
          (Stacks.Cohomology.kFlatResolution X (sheafHomComplex X B C).obj) B hB).hom ≫
        DerivedCategory.Q.map (curryHomEquiv X
          (Stacks.Cohomology.kFlatResolution X (sheafHomComplex X B C).obj) B C
          (Stacks.Cohomology.kFlatResolutionHom X (sheafHomComplex X B C).obj))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map σ).app
        (DerivedCategory.Q.obj B) ≫
      derivedCurryHomEquiv X
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
          (DerivedCategory.Q.obj C))
        (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) =
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight
        (sheafHomComplex X B C).obj B hB).hom ≫
      DerivedCategory.Q.map (cochainEvaluation X B C) :=
  evaluationSquare_of_curryingSquare X _ B C σ hB _
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (Stacks.Cohomology.kFlatResolutionHom_quasiIso X (sheafHomComplex X B C).obj))
    hcurry

end AlgebraicGeometry.RingedSite

end
