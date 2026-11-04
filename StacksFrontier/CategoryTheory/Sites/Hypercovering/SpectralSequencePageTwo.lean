module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# The second page of the hypercovering spectral sequence

Let `C` be a site, `X` an object of `C` and `K` a simplicial object of
`FormalCoproduct (Over X)` -- a simplicial semi-representable object over `X`, `SR(C, X)` in the
source. Evaluating a presheaf of abelian groups on the levels of `K` and taking alternating
cofaces gives the Čech complex `s(P(K))` of [Stacks, Tag 01GX], whose cohomology is the Čech
cohomology of `K`. [Stacks, Tag 01GY] asserts that there is a spectral sequence with
`E₂^{p,q} = ČHᵖ(K, Hᵠ(F))` abutting to `H^{p+q}(X, F)`, functorially in the hypercovering and in
the coefficient sheaf. This file supplies the second-page functor of that assertion, together
with the exactness of the Čech complex functor which the identification of the second page needs.

**Neither [Stacks, Tag 01GY] nor any part of it is proved here and nothing in this file carries
the tag.** What is here is the functor `(K, F) ↦ ČHᵖ(K, Hᵠ(F))` of the two variables, with its
values and both of its actions on morphisms pinned down -- `pageTwoBifunctor`,
`pageTwoBifunctor_obj`, `pageTwoBifunctor_map_hypercovering` and
`pageTwoBifunctor_map_sheaf` -- and the exactness which
turns the homology of the hypercover double complex of an injective resolution into that functor.
The spectral sequence itself, its second-page isomorphism and its filtered abutment are not here;
see the implementation notes.

## Main results

* `CategoryTheory.Limits.FormalCoproduct.preservesFiniteLimits_cochainComplexFunctor` and
  `CategoryTheory.Limits.FormalCoproduct.preservesFiniteColimits_cochainComplexFunctor`: **the
  cochain complex functor of a simplicial semi-representable object is exact.** This is
  [Stacks, Tag 01EJ] / [Stacks, Tag 03AQ] for an arbitrary simplicial semi-representable object
  rather than for the Čech nerve of a family of morphisms, which is the form
  `Stacks.CechSite.cechComplexPlusFunctor_exact` has.
* `Stacks.CategoryTheory.Hypercovering.preservesHomology_cechComplexOverBifunctor_obj`: the Čech
  complex functor of `K` preserves homology, so it commutes with the homology of a complex of
  presheaves.
* `Stacks.CategoryTheory.Hypercovering.pageTwoBifunctor_obj`,
  `Stacks.CategoryTheory.Hypercovering.pageTwoBifunctor_map_hypercovering` and
  `Stacks.CategoryTheory.Hypercovering.pageTwoBifunctor_map_sheaf`: the value of the second-page
  functor is `ČHᵖ(K, Hᵠ(F))`, its action on a morphism of hypercoverings is the canonical pullback
  map on Čech cohomology, and its action on a morphism of sheaves is Čech cohomology of the
  induced morphism of cohomology presheaves.

## Main definitions

* `CategoryTheory.Limits.FormalCoproduct.rightOpFunctor`: `K ↦ K.rightOp`, contravariantly in the
  simplicial object.
* `CategoryTheory.Limits.FormalCoproduct.cochainComplexBifunctor`: Mathlib's
  `FormalCoproduct.cochainComplexFunctor` as a functor of the simplicial semi-representable
  object as well, contravariantly.
* `Stacks.CategoryTheory.Hypercovering.cechComplexOverBifunctor` and
  `Stacks.CategoryTheory.Hypercovering.cechCohomologyOverBifunctor`: the Čech complex `s(P(K))`
  of a presheaf on `C` and a simplicial semi-representable object over `X`, and its cohomology,
  each as a functor of both arguments.
* `Stacks.CategoryTheory.Hypercovering.pageTwoBifunctor`: the second-page functor
  `(K, F) ↦ ČHᵖ(K, Hᵠ(F))`.

## Implementation notes

Exactness is proved factor by factor, as in
`StacksFrontier/CategoryTheory/Sites/CechComplexExactness.lean`: evaluation at a formal coproduct is a
product of evaluations, so it is exact as soon as `w`-indexed products are, which is
`AB4StarOfSize` and holds for abelian groups in any universe containing `w`; precomposition with a
functor and the alternating coface complex are computed termwise, so they are exact
unconditionally. Nothing in the proof uses the shape of the Čech nerve, which is why the statement
generalises to an arbitrary simplicial semi-representable object.

Both functors of the two variables are assembled out of whiskerings, so their functoriality needs
no proof, and the second-page functor is `CategoryTheory.Functor.uncurry` of the result. The two
`eqToHom` transports that [Stacks, Tag 01GY] carries in its second-page equations are not needed
here: `uncurry` is applied to a functor whose value at `K` is *syntactically* the Čech cohomology
functor of `K`, so `pageTwoBifunctor_obj` holds by `rfl` and the two naturality equations are
equalities of morphisms between the same objects.

**What the rest of [Stacks, Tag 01GY] needs, and where it stops.** The spectral sequence itself
is the second spectral sequence of the double complex `A^{q,p} = s(I^q(K))^p` of an injective
resolution `I^•` of `F`, with the resolution degree outer;
`HomologicalComplex₂.e₂FunctorOfHomotopyClasses` of
`StacksFrontier/Algebra/Homology/SpectralSequence/FirstQuadrantDoubleComplex.lean` makes that
functorial out of a resolution functorial only up to homotopy, exactly as
`Stacks.Cohomology.CechSpectral.cechE₂Functor` does for a covering. The coefficient sheaves of
[Stacks, Tag 01GY] live in `AddCommGrpCat.{v}` while the Čech complex of a `w`-indexed
semi-representable object needs coefficients in `AddCommGrpCat.{max u v w}`, so that double
complex is formed from the resolution composed with a universe lift. The *second page* survives
that lift, because the lift is exact and the identification `H^q(I^•(U)) ≅ Ext^q(**Z**_U^♯, F)`
is taken inside the coefficient universe; the *abutment* needs more, because the vanishing of
positive-degree Čech cohomology on a hypercovering ([Stacks, Tag 01GW],
`Stacks.CategoryTheory.Hypercovering.cechCohomologyOver_isZero_of_injective`) is available only
for an injective object of `Sheaf J AddCommGrpCat.{max u v w}`.

The universe lift does carry injective abelian sheaves to injective abelian sheaves --
`Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor` of
`StacksFrontier/CategoryTheory/Sites/UniverseLiftInjective.lean`, proved by Baer's criterion rather
than by the usual adjunction argument, which is unavailable here since the lift has no left
adjoint. **But lifting the resolution does not reach the abutment, and the route that looked
like it would is circular.** With `[HasSheafify J AddCommGrpCat.{v}]` and
`[HasExt.{max u v w} (Sheaf J AddCommGrpCat.{v})]` as sole hypotheses,
`Sheaf J AddCommGrpCat.{v}` is not known to be a Grothendieck abelian category at any universe
`z`, and the two conditions pull in opposite directions: `LocallySmall.{z}` wants `z` at least
`max u v`, since a morphism of sheaves is a family of components indexed by the objects of the
site, while `AB5OfSize.{z, z}` wants the coefficients to have `z`-sized colimits, hence `z` at
most `v`. So there is no injective resolution of the coefficient sheaf in its own
universe, the resolution has to be taken in `Sheaf J AddCommGrpCat.{max u v w}`, and the
abutment then computes `Ext` in the *larger* sheaf category -- whereas
`Sheaf.cohomologyPresheafFunctor`, and hence the statement of [Stacks, Tag 01GY], uses the `Ext`
of the smaller one. Identifying the two is not an extra lemma one can go and prove: the only
comparisons of `Ext` along a fully faithful exact functor are
`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects` and its projective
counterpart, and each of them requires enough injectives (resp. projectives) *in the source
category*, which here is `Sheaf J AddCommGrpCat.{v}` -- the very thing that is missing. Lifting
the resolution and identifying the `Ext` therefore assumes what it is meant to supply.

**The hypothesis that closes it is in the source, and was dropped.** The obstruction above is an
artefact of asserting [Stacks, Tag 01GY] for a site `C : Type u` with `Category.{v} C` and no
relation between `u` and `v`. The source asserts no such thing: in the Stacks Project a site is a
*small* category. Conventions, Section 2.2 (tag `0005`): "A category `𝒞` consists of a **set** of
objects and, for each pair of objects, a **set** of morphisms between them. In other words, it is
what is called a 'small' category in other texts. We will use 'big' categories ... only those that
are listed in Categories, Remark 4.2.2." Sites, Remark 7.6.3 (tag `00VI`): "In order to avoid
thinking about things like 'classes of classes' and so on, we will **not allow sites to be 'big'
categories**, in contrast to what we do for categories and 2-categories." So adding smallness back
is a *correction*, not a weakening, and the corrected statement is the faithful one.

Smallness closes the gap twice over, and the sharper form is the one to use. The weak form,
`UnivLE.{u, v}`, gives `EnoughInjectives (Sheaf J AddCommGrpCat.{v})` -- it makes the site
`EssentiallySmall.{v}`, which is the hypothesis of
`Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite` -- so the resolution
can be taken in the coefficient universe itself and no `Ext` comparison is needed; but the Čech
complex still lives in `AddCommGrpCat.{max u v w}` and the universe lift of the resolution is still
needed, `UnivLE` being a smallness class and not a universe equation. The strong form is literal
smallness, which is what the source says: a site `C : Type v` with `Category.{v} C` whose
semi-representable objects are indexed in `Type v`. Then `max u v w` *is* `v`, the Čech complex
and the coefficient sheaves live in one and the same category, there is no lift and no `Ext`
comparison at all, and all of `HasSheafify`, `EnoughInjectives` and `HasExt.{v}` become free --
see `StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequenceHypothesis.lean`, whose
`Stacks.CategoryTheory.Hypercovering.pageTwoSmallSite` is the second-page functor below at the
source's hypotheses and carries no instance hypotheses whatever.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
* [Stacks Project, Tag 03AQ](https://stacks.math.columbia.edu/tag/03AQ)
* [Stacks Project, Tag 0005](https://stacks.math.columbia.edu/tag/0005)
* [Stacks Project, Tag 00VI](https://stacks.math.columbia.edu/tag/00VI)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u uA vA

namespace CategoryTheory.Limits.FormalCoproduct

section Exactness

variable {D : Type u} [Category.{v} D] {A : Type uA} [Category.{vA} A] [HasProducts.{w} A]

/-- Evaluating a presheaf at a formal coproduct is the product of its evaluations at the
summands. -/
private def evalOpEvaluationIso (T : FormalCoproduct.{w} D) :
    evalOp.{w} D A ⋙ (evaluation _ _).obj (op T) ≅
      (Functor.whiskeringLeft _ _ A).obj
        (Discrete.functor (fun i : T.I ↦ op (T.obj i))) ⋙ lim :=
  NatIso.ofComponents
    (fun F ↦ Pi.isoLimit ((Discrete.functor (fun i : T.I ↦ op (T.obj i))) ⋙ F))
    (by
      intro F G f
      apply limit.hom_ext
      intro ⟨i⟩
      simp [evalOp])

variable (D A)

/-- Evaluation of presheaves at formal coproducts preserves finite limits. -/
instance preservesFiniteLimits_evalOp [HasFiniteLimits A] :
    PreservesFiniteLimits (evalOp.{w} D A) :=
  preservesFiniteLimits_of_evaluation _ fun T ↦
    preservesFiniteLimits_of_natIso (evalOpEvaluationIso T.unop).symm

/-- Evaluation of presheaves at formal coproducts preserves finite colimits when `w`-indexed
products in `A` are exact. -/
instance preservesFiniteColimits_evalOp [Abelian A] [AB4StarOfSize.{w} A] :
    PreservesFiniteColimits (evalOp.{w} D A) :=
  preservesFiniteColimits_of_evaluation _ fun T ↦
    preservesFiniteColimits_of_natIso (evalOpEvaluationIso T.unop).symm

/-- The alternating coface map complex of cosimplicial objects preserves finite limits. -/
instance preservesFiniteLimits_alternatingCofaceMapComplex [Preadditive A] [HasFiniteLimits A] :
    PreservesFiniteLimits (AlgebraicTopology.alternatingCofaceMapComplex A) :=
  ⟨fun J _ _ ↦ by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    change PreservesLimitsOfShape J ((evaluation SimplexCategory A).obj (SimplexCategory.mk n))
    infer_instance⟩

/-- The alternating coface map complex of cosimplicial objects preserves finite colimits. -/
instance preservesFiniteColimits_alternatingCofaceMapComplex
    [Preadditive A] [HasFiniteColimits A] :
    PreservesFiniteColimits (AlgebraicTopology.alternatingCofaceMapComplex A) :=
  ⟨fun J _ _ ↦ by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape J ((evaluation SimplexCategory A).obj (SimplexCategory.mk n))
    infer_instance⟩

variable {D A}

/-- **The cochain complex of a simplicial semi-representable object preserves finite limits.** -/
instance preservesFiniteLimits_cosimplicialObjectFunctor [HasFiniteLimits A]
    (K : SimplicialObject (FormalCoproduct.{w} D)) :
    PreservesFiniteLimits (cosimplicialObjectFunctor.{w} (A := A) K) := by
  unfold cosimplicialObjectFunctor
  infer_instance

/-- The cosimplicial object functor of a simplicial semi-representable object preserves finite
colimits when `w`-indexed products in `A` are exact. -/
instance preservesFiniteColimits_cosimplicialObjectFunctor [Abelian A] [AB4StarOfSize.{w} A]
    (K : SimplicialObject (FormalCoproduct.{w} D)) :
    PreservesFiniteColimits (cosimplicialObjectFunctor.{w} (A := A) K) := by
  unfold cosimplicialObjectFunctor
  infer_instance

/-- **The cochain complex functor of a simplicial semi-representable object preserves finite
limits.** -/
instance preservesFiniteLimits_cochainComplexFunctor [Preadditive A] [HasFiniteLimits A]
    (K : SimplicialObject (FormalCoproduct.{w} D)) :
    PreservesFiniteLimits (cochainComplexFunctor.{w} (A := A) K) := by
  unfold cochainComplexFunctor
  infer_instance

/-- **The cochain complex functor of a simplicial semi-representable object preserves finite
colimits.** -/
instance preservesFiniteColimits_cochainComplexFunctor [Abelian A] [AB4StarOfSize.{w} A]
    (K : SimplicialObject (FormalCoproduct.{w} D)) :
    PreservesFiniteColimits (cochainComplexFunctor.{w} (A := A) K) := by
  unfold cochainComplexFunctor
  infer_instance

end Exactness

section Bifunctor

variable (D : Type u) [Category.{v} D] (A : Type uA) [Category.{vA} A]

/-- `K ↦ K.rightOp`, contravariantly in the simplicial object. -/
def rightOpFunctor : (SimplicialObject D)ᵒᵖ ⥤ SimplexCategory ⥤ Dᵒᵖ where
  obj K := K.unop.rightOp
  map f := NatTrans.rightOp f.unop
  map_id _ := rfl
  map_comp _ _ := rfl

variable [HasProducts.{w} A] [Preadditive A]

/-- **The cochain complex functor of a simplicial semi-representable object, as a functor of that
object too.** It is contravariant: a morphism `K ⟶ L` pulls sections on `L` back to sections
on `K`. -/
def cochainComplexBifunctor :
    (SimplicialObject (FormalCoproduct.{w} D))ᵒᵖ ⥤ (Dᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  rightOpFunctor (FormalCoproduct.{w} D) ⋙
    Functor.whiskeringLeft SimplexCategory (FormalCoproduct.{w} D)ᵒᵖ A ⋙
      ((Functor.whiskeringLeft (Dᵒᵖ ⥤ A) ((FormalCoproduct.{w} D)ᵒᵖ ⥤ A)
            (CosimplicialObject A)).obj (evalOp.{w} D A) ⋙
        (Functor.whiskeringRight (Dᵒᵖ ⥤ A) (CosimplicialObject A)
            (CochainComplex A ℕ)).obj (AlgebraicTopology.alternatingCofaceMapComplex A))

/-- `cochainComplexBifunctor` at a simplicial semi-representable object is
`cochainComplexFunctor`. -/
lemma cochainComplexBifunctor_obj (K : SimplicialObject (FormalCoproduct.{w} D)) :
    (cochainComplexBifunctor.{w} D A).obj (op K) = cochainComplexFunctor.{w} (A := A) K :=
  rfl

end Bifunctor

end CategoryTheory.Limits.FormalCoproduct

open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] (X : C)

/-- The complex `s(P(K))` of a presheaf of abelian groups on `C` and a simplicial
semi-representable object over `X`, as a functor of both, contravariantly in `K`. -/
def cechComplexOverBifunctor :
    (SimplicialObject (FormalCoproduct.{w} (Over X)))ᵒᵖ ⥤
      (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤ CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  FormalCoproduct.cochainComplexBifunctor.{w} (Over X) AddCommGrpCat.{max u v w} ⋙
    (Functor.whiskeringLeft (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w})
        ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
        (CochainComplex AddCommGrpCat.{max u v w} ℕ)).obj
      ((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
        (Over.forget X).op)

/-- **The Čech complex functor of a simplicial semi-representable object over `X` is exact.**
Abelian groups in the universe `max u v w` have exact `w`-indexed products, which is the only
size hypothesis the exactness of the alternating coface complex needs. -/
instance preservesFiniteLimits_cechComplexOverBifunctor_obj
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    PreservesFiniteLimits ((cechComplexOverBifunctor.{w} X).obj (op K)) := by
  change PreservesFiniteLimits
    ((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj (Over.forget X).op ⋙
      FormalCoproduct.cochainComplexFunctor.{w} K)
  infer_instance

/-- The Čech complex functor of a simplicial semi-representable object over `X` preserves finite
colimits. -/
instance preservesFiniteColimits_cechComplexOverBifunctor_obj
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    PreservesFiniteColimits ((cechComplexOverBifunctor.{w} X).obj (op K)) := by
  have : AB4StarOfSize.{w} AddCommGrpCat.{max u v w} := ⟨fun I ↦
    HasExactLimitsOfShape.of_domain_equivalence AddCommGrpCat.{max u v w}
      (Discrete.equivalence (Equiv.ulift.{max u v} : ULift.{max u v} I ≃ I))⟩
  change PreservesFiniteColimits
    ((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj (Over.forget X).op ⋙
      FormalCoproduct.cochainComplexFunctor.{w} K)
  infer_instance

/-- The Čech complex functor of a simplicial semi-representable object preserves homology; this
is what makes it commute with the homology of a complex of presheaves, which is the coefficient
half of the second-page identification of [Stacks, Tag 01GY]. -/
instance preservesHomology_cechComplexOverBifunctor_obj
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    ((cechComplexOverBifunctor.{w} X).obj (op K)).PreservesHomology :=
  inferInstance

/-- **Čech cohomology of a hypercovering with presheaf coefficients, functorial in both
arguments.** At a simplicial semi-representable object `K` over `X` and a presheaf `P` it is the
degree-`p` cohomology of the alternating coface complex of `P` evaluated on `K`. -/
def cechCohomologyOverBifunctor (p : ℕ) :
    (SimplicialObject (FormalCoproduct.{w} (Over X)))ᵒᵖ ⥤
      (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤ AddCommGrpCat.{max u v w} :=
  cechComplexOverBifunctor.{w} X ⋙
    (Functor.whiskeringRight (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w})
        (CochainComplex AddCommGrpCat.{max u v w} ℕ) AddCommGrpCat.{max u v w}).obj
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w} (ComplexShape.up ℕ) p)

/-- The value of `cechCohomologyOverBifunctor` at a fixed `K` is the Čech cohomology functor of
`K`, spelled as the composite of restriction along `Over.forget X`, the alternating coface
complex and homology. -/
lemma cechCohomologyOverBifunctor_obj (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (p : ℕ) :
    (cechCohomologyOverBifunctor.{w} X p).obj (op K) =
      (Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
          (Over.forget X).op ⋙
        FormalCoproduct.cochainComplexFunctor K ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w} (ComplexShape.up ℕ) p :=
  rfl

/-- The action of `cechCohomologyOverBifunctor` on a morphism of simplicial semi-representable
objects is the canonical pullback map on Čech cohomology. -/
lemma cechCohomologyOverBifunctor_map_app
    {K L : SimplicialObject (FormalCoproduct.{w} (Over X))} (f : K ⟶ L)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    ((cechCohomologyOverBifunctor.{w} X p).map f.op).app P =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
          (ComplexShape.up ℕ) p).map
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).map
          (Functor.whiskerRight (NatTrans.rightOp f)
            ((FormalCoproduct.evalOp.{w} (Over X) AddCommGrpCat.{max u v w}).obj
              ((Over.forget X).op ⋙ P)))) :=
  rfl

section PageTwo

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{v})]

/-- **The second-page functor of the hypercovering spectral sequence of [Stacks, Tag 01GY]**:
`(K, F) ↦ ČHᵖ(K, Hᵠ(F))`, contravariantly in the simplicial semi-representable object `K` over
`X` and covariantly in the coefficient sheaf `F`. Its action on a morphism of `K`'s is the
canonical pullback map on Čech cohomology and its action on a morphism of sheaves is Čech
cohomology of the induced morphism of cohomology presheaves; those are
`pageTwoBifunctor_map_hypercovering` and `pageTwoBifunctor_map_sheaf`. -/
def pageTwoBifunctor (p q : ℕ) :
    (SimplicialObject (FormalCoproduct.{w} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v} ⥤
      AddCommGrpCat.{max u v w} :=
  Functor.uncurry.obj (cechCohomologyOverBifunctor.{w} X p ⋙
    (Functor.whiskeringLeft (Sheaf J AddCommGrpCat.{v}) (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w})
      AddCommGrpCat.{max u v w}).obj (Sheaf.cohomologyPresheafFunctor J q))

/-- **The value of the second-page functor is `ČHᵖ(K, Hᵠ(F))`**, on the nose. -/
lemma pageTwoBifunctor_obj (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{v}) (p q : ℕ) :
    (pageTwoBifunctor.{w} X J p q).obj (op K, F) =
      ((cechCohomologyOverBifunctor.{w} X p).obj (op K)).obj
        ((Sheaf.cohomologyPresheafFunctor J q).obj F) :=
  rfl

/-- **On a morphism of simplicial semi-representable objects the second-page map is the canonical
pullback map on Čech cohomology**, with the coefficient sheaf fixed. -/
lemma pageTwoBifunctor_map_hypercovering
    {K L : SimplicialObject (FormalCoproduct.{w} (Over X))} (f : K ⟶ L)
    (F : Sheaf J AddCommGrpCat.{v}) (p q : ℕ) :
    (pageTwoBifunctor.{w} X J p q).map (f.op ×ₘ 𝟙 F) =
      ((cechCohomologyOverBifunctor.{w} X p).map f.op).app
        ((Sheaf.cohomologyPresheafFunctor J q).obj F) := by
  dsimp [pageTwoBifunctor, Functor.uncurry]
  simp

/-- **On a morphism of coefficient sheaves the second-page map is Čech cohomology of the induced
morphism of cohomology presheaves**, with the hypercovering fixed. -/
lemma pageTwoBifunctor_map_sheaf (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    {F G : Sheaf J AddCommGrpCat.{v}} (g : F ⟶ G) (p q : ℕ) :
    (pageTwoBifunctor.{w} X J p q).map (𝟙 (op K) ×ₘ g) =
      ((cechCohomologyOverBifunctor.{w} X p).obj (op K)).map
        ((Sheaf.cohomologyPresheafFunctor J q).map g) := by
  dsimp [pageTwoBifunctor, Functor.uncurry]
  simp

end PageTwo

end Stacks.CategoryTheory.Hypercovering

end
