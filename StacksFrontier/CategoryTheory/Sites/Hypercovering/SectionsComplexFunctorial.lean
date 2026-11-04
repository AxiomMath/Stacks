module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Limits.FormalCoproductAdditive
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.DerivedComparison
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.HomComplexAugmentation
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectCohomology

/-!
# The sections of a hypercovering of an object, functorially in the coefficient sheaf

Let `C` be a site with fibre products, let `X` be an object of `C` and let `K` be a simplicial
formal coproduct over `X`.  Two identifications made in the library at a *fixed* abelian sheaf
`F` are upgraded here to natural isomorphisms of functors of `F`:

* the complex of sections `s(F(K))` is the complex `Hom(s(**Z**_{F(K)}^♯), F)` of morphisms out
  of the associated complex of free abelian sheaves — [Stacks, Tag 01GX];
* the sections `F(X)` are the morphisms `Hom(**Z**_X^♯, F)` out of the free abelian sheaf on the
  presheaf represented by `X` — the Yoneda lemma together with the two adjunctions defining
  `**Z**_X^♯`.

Together they say that the pair `(Γ(X, -), s(-(K)))` of functors of the coefficient sheaf is
isomorphic to the pair `(Hom(**Z**_X^♯, -), Hom(s(**Z**_{F(K)}^♯), -))`, which is the pair that
`CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafEpsNatTrans` equips with an
augmentation.  That is what lets the comparison map of [Stacks, Tag 01GY] be assembled from the
abstract construction of `StacksDraft.DerivedSectionsComparison`.

## Main definitions

* `SectionsOver.sectionsComplexFunctor`: the complex of sections `s(-(K))`, as a functor of the
  coefficient sheaf.
* `SectionsOver.sectionsComplexFunctorIsoHomFreeAbelianSheafComplexFunctor`: [Stacks, Tag 01GX],
  natural in the coefficient sheaf.
* `homFreeAbelianSheafComplexFunctorIsoHypercoverCochain`: the same isomorphism with its target
  spelled `hypercoverCochainNatFunctor`, which is the spelling the comparison map of
  [Stacks, Tag 01GY] is built against.
* `evaluationIsoFreeAbelianSheafSections`: `Γ(X, -) ≅ Hom(**Z**_X^♯, -)`.

## Main results

* `SectionsOver.sectionsEquiv_comp`: the identification of the sections of a formal coproduct
  with a product of groups of sections is compatible with postcomposition in the coefficient
  sheaf.
* `freeEvaluationHomAddEquiv_comp`: the same for the Yoneda identification of the sections on
  `X` with the morphisms out of the free abelian sheaf on the presheaf of `X`.
* `SectionsOver.sectionsComplexFunctor_additive`, `hypercoverCochainNatFunctor_additive` and
  `hypercoverCochainIntFunctor_additive`: the complex of sections is additive in the coefficient
  sheaf, in each of its three spellings.

## Implementation notes

The two isomorphisms are stated in the spellings in which the material downstream consumes
them.  The target of the first is literally
`CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafHomCx` at the augmented simplicial
presheaf of `K`, which is definitionally
`Stacks.CategoryTheory.Hypercovering.SectionsOver.homFreeAbelianSheafComplex`; the target of the
second is literally `CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafSections` at that
same augmented simplicial presheaf.  Stating them at the other spelling and transporting
afterwards would mean carrying an `eqToHom` through every naturality square downstream.

Both naturality proofs come down to one computation, carried out once in `sectionsEquiv_comp`
and once in `freeEvaluationHomAddEquiv_comp`: postcomposition with a morphism of sheaves passes
through the sheafification adjunction, through the free-abelian-presheaf adjunction and through
the Yoneda identification, each by the naturality of a `homEquiv` in its right variable.  The
components of the isomorphisms are not `simp`-normal — each is an `Equiv.trans` of three
bijections — so the proofs work on elements, projected to the factors of the product by
`Concrete.productEquiv`.

Those elementwise computations are stated as the auxiliary equation `key` inside the naturality
proof rather than rewritten into the goal.  The goal mentions the two functors, whose values are
reached only by unfolding `getLimitCone`, which is not exposed; a rewrite inside the goal
therefore produces a motive that fails to typecheck at `instances` transparency.  Proving the
equation in its own words and closing the goal with it defers the unfolding to a single
definitional check.

## References

* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject.Augmented

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]

/-- The Yoneda identification of a map out of a free abelian presheaf, transported along the
free-forgetful adjunction, is natural in the target presheaf. -/
private lemma uliftYonedaEquiv_comp_homEquiv {X : C} {A : Cᵒᵖ ⥤ Type (max u v w)}
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}} (m : P ⟶ Q) (j : uliftYoneda.{max u w}.obj X ⟶ A)
    (k : A ⋙ AddCommGrpCat.free.{max u v w} ⟶ P) :
    uliftYonedaEquiv.{max u w} (j ≫ (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ (k ≫ m)) =
      m.app (op X) (uliftYonedaEquiv.{max u w}
        (j ≫ (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ k)) := by
  rw [(AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_right, ← Category.assoc,
    uliftYonedaEquiv_comp]
  rfl

namespace SectionsOver

/-- **Postcomposition in the coefficient sheaf, read through the identification of the sections
of a formal coproduct with a product of groups of sections.**  Each of the three bijections
composing `sectionsEquiv` is natural in its right variable, so the identification is too. -/
lemma sectionsEquiv_comp (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {X : C} (T : FormalCoproduct.{w} (Over X))
    {F G : Sheaf J AddCommGrpCat.{max u v w}} (g : F ⟶ G)
    (f : freeAbelianSheaf J T ⟶ F) (i : T.I) :
    ConcreteCategory.hom (Pi.π (fun i ↦ G.obj.obj (op ((T.obj i).left))) i)
        ((sectionsEquiv J T G).toFun (f ≫ g)) =
      g.hom.app (op (T.obj i).left)
        (ConcreteCategory.hom (Pi.π (fun i ↦ F.obj.obj (op ((T.obj i).left))) i)
          ((sectionsEquiv J T F).toFun f)) := by
  rw [sectionsEquiv_π J T G (f ≫ g) i, sectionsEquiv_π J T F f i,
    (sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv_naturality_right,
    uliftYonedaEquiv_comp_homEquiv]
  rfl

/-- **The complex of sections `s(-(K))` of a simplicial formal coproduct over `X`, as a functor
of the coefficient sheaf.**  A sheaf is restricted to the objects over `X`, evaluated on the
levels of `K` and turned into a cochain complex by the alternating sum of the cofaces. -/
noncomputable def sectionsComplexFunctor (J : GrothendieckTopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    Sheaf J AddCommGrpCat.{max u v w} ⥤ CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  sheafToPresheaf J AddCommGrpCat.{max u v w} ⋙
    (Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj (Over.forget X).op ⋙
      FormalCoproduct.cochainComplexFunctor K

/-- The value of `sectionsComplexFunctor` at a sheaf is the complex of sections `sectionsComplex`
formed at that sheaf. -/
lemma sectionsComplexFunctor_obj (J : GrothendieckTopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) :
    (sectionsComplexFunctor J K).obj F = sectionsComplex J K F := rfl

/-- The complex of sections of `K` is an additive functor of the coefficient sheaf: each of the
three functors composing it is. -/
instance sectionsComplexFunctor_additive (J : GrothendieckTopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    (sectionsComplexFunctor J K).Additive := by
  dsimp only [sectionsComplexFunctor]
  infer_instance

/-- **[Stacks, Tag 01GX], natural in the coefficient sheaf.**  The functor of morphisms out of
the complex of free abelian sheaves of `K` is the functor of sections of `K`.  The fixed-sheaf
isomorphism is `sectionsComplexIsoHomFreeAbelianSheafComplex`; what is proved here is that it is
natural. -/
noncomputable def homFreeAbelianSheafComplexFunctorIsoSectionsComplexFunctor
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    freeAbelianSheafHomCx J (associatedAugmentedSimplicialPresheafOver.{w} K) ≅
      sectionsComplexFunctor J K := by
  refine NatIso.ofComponents
    (fun F ↦ (sectionsComplexIsoHomFreeAbelianSheafComplex J K F).symm) ?_
  intro F G g
  apply HomologicalComplex.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply (Concrete.productEquiv
    (fun i ↦ G.obj.obj (op ((K.obj (op ⦋n⦌)).obj i).left))).injective
  funext i
  have key :
      (Concrete.productEquiv (fun i ↦ G.obj.obj (op ((K.obj (op ⦋n⦌)).obj i).left)))
          (sectionsEquiv J (K.obj (op ⦋n⦌)) G (z ≫ g)) i =
        (Concrete.productEquiv (fun i ↦ G.obj.obj (op ((K.obj (op ⦋n⦌)).obj i).left)))
          ((ConcreteCategory.hom (CategoryTheory.Limits.Pi.map
              (fun i ↦ g.hom.app (op ((K.obj (op ⦋n⦌)).obj i).left))))
            (sectionsEquiv J (K.obj (op ⦋n⦌)) F z)) i := by
    rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply,
      ← ConcreteCategory.comp_apply, Pi.map_π, ConcreteCategory.comp_apply]
    exact sectionsEquiv_comp J (K.obj (op ⦋n⦌)) g z i
  exact key

/-- **[Stacks, Tag 01GX], natural in the coefficient sheaf**, in the direction in which the
comparison map of [Stacks, Tag 01GY] consumes it. -/
noncomputable abbrev sectionsComplexFunctorIsoHomFreeAbelianSheafComplexFunctor
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    sectionsComplexFunctor J K ≅
      freeAbelianSheafHomCx J (associatedAugmentedSimplicialPresheafOver.{w} K) :=
  (homFreeAbelianSheafComplexFunctorIsoSectionsComplexFunctor J K).symm

end SectionsOver

section Pretopology

variable [HasPullbacks C] (J : Pretopology C) (X : C)
  (K : SimplicialObject (FormalCoproduct.{w} (Over X)))

/-- The complex of sections of `K` is the hypercovering cochain complex of [Stacks, Tag 01GY],
on the nose. -/
lemma hypercoverCochainNatFunctor_eq_sectionsComplexFunctor :
    hypercoverCochainNatFunctor.{w} J X K =
      SectionsOver.sectionsComplexFunctor J.toGrothendieck K := rfl

/-- The hypercovering cochain complex of [Stacks, Tag 01GY] is an additive functor of the
coefficient sheaf. -/
instance hypercoverCochainNatFunctor_additive :
    (hypercoverCochainNatFunctor.{w} J X K).Additive :=
  inferInstanceAs (SectionsOver.sectionsComplexFunctor J.toGrothendieck K).Additive

/-- The hypercovering cochain complex of [Stacks, Tag 01GY], extended by zero to integer
degrees, is an additive functor of the coefficient sheaf. -/
instance hypercoverCochainIntFunctor_additive :
    (hypercoverCochainIntFunctor.{w} J X K).Additive := by
  dsimp only [hypercoverCochainIntFunctor]
  infer_instance

/-- **[Stacks, Tag 01GX], natural in the coefficient sheaf**, with its target spelled as the
hypercovering cochain complex functor of [Stacks, Tag 01GY]. -/
noncomputable def homFreeAbelianSheafComplexFunctorIsoHypercoverCochain
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}] :
    freeAbelianSheafHomCx J.toGrothendieck
        (associatedAugmentedSimplicialPresheafOver.{w} K) ≅
      hypercoverCochainNatFunctor.{w} J X K :=
  SectionsOver.homFreeAbelianSheafComplexFunctorIsoSectionsComplexFunctor J.toGrothendieck K

/-- **[Stacks, Tag 01GX], natural in the coefficient sheaf**, from the hypercovering cochain
complex functor of [Stacks, Tag 01GY] to the Hom complex out of the free abelian sheaves. -/
noncomputable abbrev hypercoverCochainIsoHomFreeAbelianSheafComplexFunctor
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}] :
    hypercoverCochainNatFunctor.{w} J X K ≅
      freeAbelianSheafHomCx J.toGrothendieck
        (associatedAugmentedSimplicialPresheafOver.{w} K) :=
  (homFreeAbelianSheafComplexFunctorIsoHypercoverCochain J X K).symm

end Pretopology

/-- **Postcomposition read through the Yoneda identification of the sections on `X` with the
morphisms out of the free abelian presheaf on the presheaf of `X`.** -/
lemma freeEvaluationHomAddEquiv_comp {X : C}
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}} (m : P ⟶ Q)
    (k : uliftYoneda.{max u w}.obj X ⋙ AddCommGrpCat.free.{max u v w} ⟶ P) :
    freeEvaluationHomAddEquiv (X := X) Q (k ≫ m) =
      m.app (op X) (freeEvaluationHomAddEquiv (X := X) P k) := by
  exact uliftYonedaEquiv_comp_homEquiv m (𝟙 _) k

/-- **Postcomposition read through the identification of the sections of an abelian sheaf on `X`
with the morphisms out of the free abelian *sheaf* on the presheaf of `X`.**  Both the
sheafification adjunction and the Yoneda identification are natural in the right variable. -/
lemma freeAbelianSheafEvaluationHomAddEquiv_comp (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] (X : C)
    {F G : Sheaf J AddCommGrpCat.{max u v w}} (g : F ⟶ G)
    (z : (presheafToSheaf J AddCommGrpCat.{max u v w}).obj
      (uliftYoneda.{max u w}.obj X ⋙ AddCommGrpCat.free.{max u v w}) ⟶ F) :
    freeEvaluationHomAddEquiv G.obj
        ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ (z ≫ g)) =
      g.hom.app (op X) (freeEvaluationHomAddEquiv F.obj
        ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ z)) := by
  rw [(sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv_naturality_right,
    freeEvaluationHomAddEquiv_comp]
  rfl

/-- **The sections of an abelian sheaf on `X` are the morphisms out of the free abelian sheaf on
the presheaf represented by `X`**, naturally in the sheaf.  This is the Yoneda lemma followed by
the two adjunctions defining `**Z**_X^♯`; the fixed-sheaf statement is the composite used in the
proof of [Stacks, Tag 01GV], and what is proved here is that it is natural. -/
@[sga "4 XVIII 1.4.24" "(a), special case"]
noncomputable def evaluationIsoFreeAbelianSheafSections (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    sheafToPresheaf J AddCommGrpCat.{max u v w} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v w}).obj (op X) ≅
      freeAbelianSheafSections J (associatedAugmentedSimplicialPresheafOver.{w} K) := by
  refine (NatIso.ofComponents (fun F ↦ (((sheafificationAdjunction J
      AddCommGrpCat.{max u v w}).homAddEquiv
        (uliftYoneda.{max u w}.obj X ⋙ AddCommGrpCat.free.{max u v w}) F).trans
      (freeEvaluationHomAddEquiv F.obj)).toAddCommGrpIso) ?_).symm
  intro F G g
  ext z
  exact freeAbelianSheafEvaluationHomAddEquiv_comp J X g z

end Stacks.CategoryTheory.Hypercovering

end
