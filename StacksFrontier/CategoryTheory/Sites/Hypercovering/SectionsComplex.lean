module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Presheaf

/-!
# The complex of sections on a simplicial semi-representable object

Let `C` be a category with a Grothendieck topology `J`, let `K` be a simplicial object of the
category `SR(C) = FormalCoproduct.{w} C` of semi-representable objects, and let `F` be a sheaf
of abelian groups on `C`. Evaluating `F` on `K` degreewise gives a cochain complex of abelian
groups, `sectionsComplex`, whose degree-`n` term is `∏ i, F(K_n(i))`. On the other hand `K`
has an associated simplicial presheaf of sets `F(K)` (Tag 09VU), hence a chain complex
`s(**Z**_{F(K)}^♯)` of free abelian sheaves (Tag 01GB), and applying `Hom(-, F)` to it gives a
second cochain complex, `homFreeAbelianSheafComplex`. This file identifies the two.

## Main definitions

* `sectionsComplex`: the alternating coface complex obtained by evaluating a sheaf of abelian
  groups on a simplicial semi-representable object.
* `homFreeAbelianSheafComplex`: the complex of morphisms from the complex of free abelian
  sheaves of the associated simplicial presheaf into a fixed sheaf.
* `presheafULift`: the universe lift on presheaves of sets carrying the values of
  `uliftYoneda.{w}` into the common universe of the statement.
* `underlyingPresheaf`: the underlying presheaf of sets of a sheaf of abelian groups.
* `evalCoproductIso`, `evalι`: the presheaf represented by a semi-representable object is the
  coproduct of the representables of its members, together with the inclusion of a member.
* `nestedYonedaIso`, `yonedaEquiv`: Yoneda's lemma for the lifted representable presheaves.
* `evaluationEquiv`, `sectionsEquiv`, `sectionsAddEquiv`: a morphism out of the presheaf
  (resp. out of the free abelian sheaf) of a semi-representable object is a family of sections,
  the last of these as an isomorphism of abelian groups.
* `freeAbelianSheaf`, `freeAbelianSheafMap`: the free abelian sheaf of a semi-representable
  object, and its functoriality.
* `evalOpProductIso`, `sectionsDegreeIso`: the degreewise comparison of the two complexes.

## Main results

* `sectionsComplexIsoHomFreeAbelianSheafComplex`: **Tag 01GX** for an arbitrary simplicial
  semi-representable object — the two cochain complexes above are canonically isomorphic.
* `sectionsComplex_d` and `homFreeAbelianSheafComplex_d`: the differentials of the two
  complexes, each as the alternating sum of the (co)face maps.
* `sectionsDegreeIso_comm_face`: the degreewise comparison commutes with the `j`-th face map,
  which is the content of the tag one summand of the alternating sum at a time.
* `evaluationEquiv_π`, `sectionsEquiv_π`, `sectionValue_add`, `evalι_naturality`,
  `yonedaEquiv_naturality`, `sectionsEquiv_naturality`,
  `sectionsEquiv_sectionsDegreeIso`: the component and naturality calculations the comparison
  rests on.

## Implementation notes

The source states Tag 01GX as an equality; it is given here as an isomorphism of cochain
complexes, because the two sides are built from independently chosen products and
sheafifications. The right-hand side is obtained by applying the additive Yoneda functor
`Hom(-, F)` to the chain complex of free abelian sheaves and then passing from the resulting
opposite chain complex to a cochain complex.

Four universes occur and none of them is specialised. `C : Type u` with `Category.{v} C`, the
index types of the semi-representable objects live in `Type w`, and `q` is a further free
universe: the sheaf of abelian groups takes values in
`AddCommGrpCat.{max (max u v) (max q w)}`, so that the statement covers sheaves valued in any
universe at least `max u v w`. This is forced rather than chosen: the presheaf represented by a
semi-representable object has values in `Type (max w v)`, so a comparison with a sheaf of
abelian groups requires both to be lifted into one universe, and `q` is what makes that
universe arbitrary. The `max` expressions are therefore load-bearing throughout, and the
degreewise comparison would not typecheck with any of them collapsed.

The associated simplicial presheaf is Tag 09VU's
`Stacks.CategoryTheory.Hypercovering.associatedSimplicialPresheaf`, and the complex of free
abelian sheaves is Tag 01GB's
`CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor`; both are used rather than
redefined. In particular the functor `F` of the source is
`Stacks.CategoryTheory.Hypercovering.associatedPresheafFunctor` at the universe
`max (max u v) (max q w)`, which is why that constant appears in place of a local abbreviation.

Two choices about naming are forced by the `checkUnivs` linter, which rejects a declaration in
whose type two universe parameters never occur apart. First, the representable summand
`uliftYoneda.{w}.obj X` composed with the universe lift is not given a name of its own: a
declaration of type `C ⥤ Cᵒᵖ ⥤ Type (max (max u v) (max q w))` has no subterm in which `q` or
`w` occurs on its own. Only the lifting functor `presheafULift` is named — its type does
mention `Type (max w v)`, which separates `w` — and the summand is written out as
`(presheafULift ..).obj (uliftYoneda.{w}.obj X)`. Second, `underlyingPresheaf` and
`preadditiveYonedaRightOpMapApply` are stated for an arbitrary value universe `t` rather than
for `max (max u v) (max q w)`; this is both more general and, for the same reason, accepted.

The comparison is checked degreewise and then face map by face map, and three devices are used
to keep every step typed at the shape `ComplexShape.up ℕ` in which the statement is phrased.
They are all made necessary by the same mismatch: `homFreeAbelianSheafComplex` is built with
`HomologicalComplex.unop`, so natively it is indexed by `(ComplexShape.down ℕ).symm`, which is
definitionally but not syntactically `ComplexShape.up ℕ`.

* `sectionsComplex_d` and `homFreeAbelianSheafComplex_d` state the two differentials with the
  complexes left folded, so that the alternating sums they produce are sums of morphisms whose
  type is spelled at shape `up`. Each is proved by a `change` into the unfolded spelling,
  which is accepted at default transparency; without them `CochainComplex.of_d` cannot be
  rewritten, since the successor `n + 1` in the goal and in that lemma reach `Nat.add` through
  different instances.
* The alternating sum is split with `Preadditive.comp_sum` and `Preadditive.sum_comp` supplied
  as terms to `Eq.trans`, not as rewrite rules: as rewrite rules neither fires, because
  matching the sum against the pattern has to reconcile the two spellings of the shape, while
  `Eq.trans` only ever asks for a definitional equality.
* Likewise the last step applies `Pi.lift_π_apply` with its family given explicitly rather
  than by matching.

Transport along `sectionsEquiv` in `sectionsDegreeIso_comm_face` is done by introducing the two
morphisms of sheaves being compared as local variables `g` and `h` pinned by hypotheses `hT'`
and `hU'`, rather than by rewriting in place: the spelled-out terms only have the expected
types after unfolding `sectionsDegreeIso`, so a `rw` whose motive abstracts them is rejected by
the type-correctness check. The same device is used for the degree-zero augmentation in
`StacksFrontier/CategoryTheory/Sites/CechNerveHomology.lean`.

## References

* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
* [Stacks Project, Tag 01GB](https://stacks.math.columbia.edu/tag/01GB)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
-/

@[expose] public section

universe q w v u t

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryTheory.Hypercovering.SemiRepresentable

variable {C : Type u} [Category.{v} C]

/-- The cochain complex obtained by evaluating a sheaf of abelian groups on an arbitrary
simplicial semi-representable object. -/
noncomputable abbrev sectionsComplex
    (J : GrothendieckTopology C) (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) :
    CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℕ :=
  (FormalCoproduct.cochainComplexFunctor K).obj F.obj

/-- The complex of morphisms from the complex of free abelian sheaves of a simplicial
semi-representable object into a fixed sheaf of abelian groups. -/
noncomputable abbrev homFreeAbelianSheafComplex
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) :
    CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℕ :=
  ((((preadditiveYoneda.obj F).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    ((_root_.CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (associatedSimplicialPresheaf.{max (max u v) (max q w)} K))).unop)

/-- The universe lift on presheaves of sets taking the values of `uliftYoneda.{w}` into the
common universe `max (max u v) (max q w)` of the comparison. -/
noncomputable abbrev presheafULift :
    (Cᵒᵖ ⥤ Type (max w v)) ⥤ (Cᵒᵖ ⥤ Type (max (max u v) (max q w))) :=
  (Functor.whiskeringRight Cᵒᵖ (Type (max w v))
    (Type (max (max u v) (max q w)))).obj uliftFunctor.{max (max u v) (max q w)}

/-- The underlying presheaf of sets of a sheaf of abelian groups. -/
noncomputable abbrev underlyingPresheaf (J : GrothendieckTopology C)
    (F : Sheaf J AddCommGrpCat.{t}) :
    Cᵒᵖ ⥤ Type t :=
  (sheafToPresheaf J AddCommGrpCat.{t}).obj F ⋙ forget AddCommGrpCat.{t}

/-- The presheaf represented by a semi-representable object is the coproduct of the
representable presheaves of its members. -/
noncomputable def evalCoproductIso (T : FormalCoproduct.{w} C) :
    associatedPresheafFunctor.{max (max u v) (max q w)} (C := C).obj T ≅
      ∐ fun i : T.I => (presheafULift.{q, w, v, u} (C := C)).obj
        (uliftYoneda.{w}.obj (T.obj i)) := by
  let G := presheafULift.{q, w, v, u} (C := C)
  let D := Discrete.functor (fun i : T.I => uliftYoneda.{w}.obj (T.obj i))
  let h : ((FormalCoproduct.eval C (Cᵒᵖ ⥤ Type (max w v))).obj
      uliftYoneda).obj T = colimit D :=
    FormalCoproduct.eval_obj_obj C (Cᵒᵖ ⥤ Type (max w v)) uliftYoneda T
  haveI : PreservesColimit D G := inferInstance
  let hDiag : Discrete.functor (fun i : T.I => G.obj (uliftYoneda.{w}.obj (T.obj i))) ≅
      Discrete.functor
        (fun i : T.I => (presheafULift.{q, w, v, u} (C := C)).obj
          (uliftYoneda.{w}.obj (T.obj i))) :=
    Discrete.natIso (fun i => Iso.refl _)
  exact G.mapIso (eqToIso h) ≪≫ preservesColimitIso G D ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete
      (fun i : T.I => uliftYoneda.{w}.obj (T.obj i)) G) ≪≫
    HasColimit.isoOfNatIso hDiag

/-- The inclusion of the representable presheaf of a member of a semi-representable object into
the presheaf the latter represents. -/
noncomputable def evalι (T : FormalCoproduct.{w} C) (i : T.I) :
    (presheafULift.{q, w, v, u} (C := C)).obj (uliftYoneda.{w}.obj (T.obj i)) ⟶
      associatedPresheafFunctor.{max (max u v) (max q w)} (C := C).obj T :=
  Sigma.ι (fun j : T.I => (presheafULift.{q, w, v, u} (C := C)).obj
      (uliftYoneda.{w}.obj (T.obj j))) i ≫
    (evalCoproductIso.{q, w, v, u} (C := C) T).inv

/-- Lifting the values of `uliftYoneda.{w}` into the common universe gives the representable
presheaf of that universe. -/
noncomputable def nestedYonedaIso (X : C) :
    (uliftYoneda.{w}.obj X ⋙
      uliftFunctor.{max (max u v) (max q w)}) ≅
    uliftYoneda.{max (max u v) (max q w)}.obj X := by
  refine NatIso.ofComponents (fun Y => Equiv.toIso {
    toFun := fun x => ULift.up x.down.down
    invFun := fun x => ULift.up (ULift.up x.down)
    left_inv := by intro x; cases x; rfl
    right_inv := by intro x; cases x; rfl }) ?_
  intro Y Z f
  ext x
  cases x
  rfl

/-- Yoneda's lemma for the lifted representable presheaves: a morphism out of the lifted
representable presheaf of `X` is a section over `X`. -/
noncomputable def yonedaEquiv (X : C)
    (F : Cᵒᵖ ⥤ Type (max (max u v) (max q w))) :
    ((presheafULift.{q, w, v, u} (C := C)).obj (uliftYoneda.{w}.obj X) ⟶ F) ≃
      F.obj (op X) where
  toFun f := uliftYonedaEquiv.{max (max u v) (max q w)}
    ((nestedYonedaIso.{q, w, v, u} (C := C) X).inv ≫ f)
  invFun x := (nestedYonedaIso.{q, w, v, u} (C := C) X).hom ≫
    uliftYonedaEquiv.{max (max u v) (max q w)}.symm x
  left_inv f := by simp
  right_inv x := by simp

/-- A morphism from the presheaf represented by a semi-representable object into the underlying
presheaf of a sheaf of abelian groups is a family of sections over its members. -/
noncomputable def evaluationEquiv (J : GrothendieckTopology C)
    (T : FormalCoproduct.{w} C) (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) :
    (associatedPresheafFunctor.{max (max u v) (max q w)} (C := C).obj T ⟶
      underlyingPresheaf J F) ≃
      (∏ᶜ fun i => F.obj.obj (op (T.obj i)) : AddCommGrpCat.{max (max u v) (max q w)}) where
  toFun f := (Concrete.productEquiv (fun i => F.obj.obj (op (T.obj i)))).symm
    (fun i => yonedaEquiv.{q, w, v, u} (C := C) (T.obj i)
      (underlyingPresheaf J F)
      (evalι.{q, w, v, u} (C := C) T i ≫ f))
  invFun a := (evalCoproductIso.{q, w, v, u} (C := C) T).hom ≫ Sigma.desc (fun i =>
    (yonedaEquiv.{q, w, v, u} (C := C) (T.obj i)
      (underlyingPresheaf J F)).symm
      (Concrete.productEquiv (fun i => F.obj.obj (op (T.obj i))) a i))
  left_inv f := by
    apply (cancel_epi (evalCoproductIso.{q, w, v, u} (C := C) T).inv).1
    apply Sigma.hom_ext
    intro i
    apply (yonedaEquiv.{q, w, v, u} (C := C) (T.obj i)
      (underlyingPresheaf J F)).injective
    simp [evalι, Category.assoc]
  right_inv a := by
    apply (Concrete.productEquiv
      (fun i => F.obj.obj (op (T.obj i)))).injective
    ext i
    simp only [Concrete.productEquiv_apply_apply, Concrete.productEquiv_symm_apply_π,
      Sigma.ι_desc, evalι, Category.assoc, Iso.inv_hom_id_assoc]
    exact Equiv.apply_symm_apply _ _

/-- The components of `evaluationEquiv` are the restrictions along the inclusions of the
members. -/
lemma evaluationEquiv_π (J : GrothendieckTopology C)
    (T : FormalCoproduct.{w} C) (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)})
    (f : associatedPresheafFunctor.{max (max u v) (max q w)} (C := C).obj T ⟶
      underlyingPresheaf J F) (i : T.I) :
    ConcreteCategory.hom (Pi.π (fun i => F.obj.obj (op (T.obj i))) i)
      ((evaluationEquiv.{q, w, v, u} (C := C) J T F).toFun f) =
    yonedaEquiv.{q, w, v, u} (C := C) (T.obj i)
      (underlyingPresheaf J F)
      (evalι.{q, w, v, u} (C := C) T i ≫ f) := by
  simp [evaluationEquiv]

/-- The free abelian sheaf on the presheaf represented by a semi-representable object. -/
@[sga "4 XVIII 1.4.24" "more general"]
noncomputable abbrev freeAbelianSheaf (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (T : FormalCoproduct.{w} C) : Sheaf J AddCommGrpCat.{max (max u v) (max q w)} :=
  (presheafToSheaf J AddCommGrpCat.{max (max u v) (max q w)}).obj
    (((Functor.whiskeringRight Cᵒᵖ
      (Type (max (max u v) (max q w)))
      AddCommGrpCat.{max (max u v) (max q w)}).obj AddCommGrpCat.free).obj
      (associatedPresheafFunctor.{max (max u v) (max q w)} (C := C).obj T))

/-- The functoriality of `freeAbelianSheaf` in the semi-representable object. -/
noncomputable def freeAbelianSheafMap (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    {U T : FormalCoproduct.{w} C} (f : U ⟶ T) :
    freeAbelianSheaf.{q, w, v, u} (C := C) J U ⟶
      freeAbelianSheaf.{q, w, v, u} (C := C) J T :=
  (presheafToSheaf J AddCommGrpCat.{max (max u v) (max q w)}).map
    (((Functor.whiskeringRight Cᵒᵖ
      (Type (max (max u v) (max q w)))
      AddCommGrpCat.{max (max u v) (max q w)}).obj AddCommGrpCat.free).map
      ((associatedPresheafFunctor.{max (max u v) (max q w)} (C := C)).map f))

/-- A morphism from the free abelian sheaf of a semi-representable object into a sheaf of
abelian groups is a family of sections over its members. -/
noncomputable def sectionsEquiv (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (T : FormalCoproduct.{w} C) (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) :
    (freeAbelianSheaf.{q, w, v, u} (C := C) J T ⟶ F) ≃
      (∏ᶜ fun i => F.obj.obj (op (T.obj i)) : AddCommGrpCat.{max (max u v) (max q w)}) :=
  ((sheafificationAdjunction J AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans
      (evaluationEquiv.{q, w, v, u} (C := C) J T F))

/-- The components of `sectionsEquiv` are the restrictions along the inclusions of the
members. -/
lemma sectionsEquiv_π (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (T : FormalCoproduct.{w} C) (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)})
    (f : freeAbelianSheaf.{q, w, v, u} (C := C) J T ⟶ F) (i : T.I) :
    ConcreteCategory.hom (Pi.π (fun i => F.obj.obj (op (T.obj i))) i)
      ((sectionsEquiv.{q, w, v, u} (C := C) J T F).toFun f) =
    yonedaEquiv.{q, w, v, u} (C := C) (T.obj i)
      (underlyingPresheaf J F)
      (evalι.{q, w, v, u} (C := C) T i ≫
        (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
          ((sheafificationAdjunction J
            AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _ f)) := by
  simp only [sectionsEquiv]
  exact evaluationEquiv_π.{q, w, v, u} (C := C) J T F _ i

/-- Taking the section over a member of a semi-representable object is additive. -/
lemma sectionValue_add (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (T : FormalCoproduct.{w} C) (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)})
    (f g : freeAbelianSheaf.{q, w, v, u} (C := C) J T ⟶ F) (i : T.I) :
    yonedaEquiv.{q, w, v, u} (C := C) (T.obj i)
      (underlyingPresheaf J F)
        (evalι.{q, w, v, u} (C := C) T i ≫
          (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
            ((sheafificationAdjunction J
              AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _ (f + g))) =
      yonedaEquiv.{q, w, v, u} (C := C) (T.obj i)
        (underlyingPresheaf J F)
          (evalι.{q, w, v, u} (C := C) T i ≫
            (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
              ((sheafificationAdjunction J
                AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _ f)) +
      yonedaEquiv.{q, w, v, u} (C := C) (T.obj i)
        (underlyingPresheaf J F)
          (evalι.{q, w, v, u} (C := C) T i ≫
            (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
              ((sheafificationAdjunction J
                AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _ g)) := by
  let qfun :
      (((Functor.whiskeringRight Cᵒᵖ
        (Type (max (max u v) (max q w)))
        AddCommGrpCat.{max (max u v) (max q w)}).obj AddCommGrpCat.free).obj
        (associatedPresheafFunctor.{max (max u v) (max q w)} (C := C).obj T) ⟶
          (sheafToPresheaf J AddCommGrpCat.{max (max u v) (max q w)}).obj F) →
        F.obj.obj (op (T.obj i)) := fun k =>
    yonedaEquiv.{q, w, v, u} (C := C) (T.obj i)
      (underlyingPresheaf J F)
      (evalι.{q, w, v, u} (C := C) T i ≫
        (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ k)
  calc
    _ = qfun ((sheafificationAdjunction J
          AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _ (f + g)) := rfl
    _ = qfun (((sheafificationAdjunction J
          AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _ f) +
        ((sheafificationAdjunction J
          AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _ g)) :=
      congrArg qfun ((sheafificationAdjunction J
        AddCommGrpCat.{max (max u v) (max q w)}).homAddEquiv_add _ _ f g)
    _ = _ := rfl

/-- `sectionsEquiv` as an isomorphism of abelian groups. -/
noncomputable def sectionsAddEquiv (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (T : FormalCoproduct.{w} C) (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) :
    (freeAbelianSheaf.{q, w, v, u} (C := C) J T ⟶ F) ≃+
      (∏ᶜ fun i => F.obj.obj (op (T.obj i)) : AddCommGrpCat.{max (max u v) (max q w)}) where
  toEquiv := sectionsEquiv.{q, w, v, u} (C := C) J T F
  map_add' f g := by
    apply (Concrete.productEquiv (fun i => F.obj.obj (op (T.obj i)))).injective
    funext i
    rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply]
    simp only [map_add]
    rw [sectionsEquiv_π.{q, w, v, u} J T F (f + g) i,
      sectionsEquiv_π.{q, w, v, u} J T F f i,
      sectionsEquiv_π.{q, w, v, u} J T F g i]
    exact sectionValue_add.{q, w, v, u} J T F f g i

/-- The inclusions of the members are natural in the semi-representable object. -/
lemma evalι_naturality {U T : FormalCoproduct.{w} C}
    (f : U ⟶ T) (i : U.I) :
    evalι.{q, w, v, u} (C := C) U i ≫
        (associatedPresheafFunctor.{max (max u v) (max q w)} (C := C)).map f =
    (presheafULift.{q, w, v, u} (C := C)).map (uliftYoneda.{w}.map (f.φ i)) ≫
        evalι.{q, w, v, u} (C := C) T (f.f i) := by
  let G := presheafULift.{q, w, v, u} (C := C)
  cases FormalCoproduct.eval_obj_obj.{w} (C := C)
    (A := Cᵒᵖ ⥤ Type (max (max u v) (max q w)))
    (F := uliftYoneda.{w} ⋙ presheafULift.{q, w, v, u} (C := C)) (X := U)
  cases FormalCoproduct.eval_obj_obj.{w} (C := C)
    (A := Cᵒᵖ ⥤ Type (max (max u v) (max q w)))
    (F := uliftYoneda.{w} ⋙ presheafULift.{q, w, v, u} (C := C)) (X := T)
  simp only [presheafULift, Functor.whiskeringRight_obj_obj, associatedPresheafFunctor,
    Functor.comp_obj, evalι, evalCoproductIso, Discrete.functor_obj_eq_as, Iso.trans_inv,
    Category.assoc, Functor.mapIso_inv, eqToIso.inv, Functor.whiskeringRight_obj_map,
    HasColimit.isoOfNatIso_ι_inv_assoc, Function.comp_apply, Discrete.natIso_inv_app,
    Iso.refl_inv, Discrete.compNatIsoDiscrete_inv_app, ι_preservesColimitIso_inv_assoc,
    Category.id_comp, Functor.comp_map, FormalCoproduct.eval_obj_map]
  show G.map (colimit.ι
        (Discrete.functor (fun j : U.I => uliftYoneda.{w}.obj (U.obj j))) ⟨i⟩) ≫
      G.map (Sigma.desc (fun j => uliftYoneda.{w}.map (f.φ j) ≫
        Sigma.ι (fun j : T.I => uliftYoneda.{w}.obj (T.obj j)) (f.f j))) =
    G.map (uliftYoneda.{w}.map (f.φ i)) ≫
      G.map (colimit.ι
        (Discrete.functor (fun j : T.I => uliftYoneda.{w}.obj (T.obj j))) ⟨f.f i⟩)
  rw [← G.map_comp, ← G.map_comp]
  simp

/-- `yonedaEquiv` is natural in the object of `C`. -/
lemma yonedaEquiv_naturality {X Y : C} (f : X ⟶ Y)
    (F : Cᵒᵖ ⥤ Type (max (max u v) (max q w)))
    (g : (presheafULift.{q, w, v, u} (C := C)).obj (uliftYoneda.{w}.obj Y) ⟶ F) :
    F.map f.op (yonedaEquiv.{q, w, v, u} (C := C) Y F g) =
      yonedaEquiv.{q, w, v, u} (C := C) X F
        ((presheafULift.{q, w, v, u} (C := C)).map (uliftYoneda.{w}.map f) ≫ g) := by
  show F.map f.op
      (uliftYonedaEquiv.{max (max u v) (max q w)}
        ((nestedYonedaIso.{q, w, v, u} (C := C) Y).inv ≫ g)) =
    uliftYonedaEquiv.{max (max u v) (max q w)}
      ((nestedYonedaIso.{q, w, v, u} (C := C) X).inv ≫
      ((presheafULift.{q, w, v, u} (C := C)).map (uliftYoneda.{w}.map f) ≫ g))
  rw [uliftYonedaEquiv_naturality]
  congr 1

/-- `sectionsEquiv` is natural in the semi-representable object: restricting a morphism along
`freeAbelianSheafMap` restricts the corresponding family of sections. -/
lemma sectionsEquiv_naturality (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    {U T : FormalCoproduct.{w} C} (f : U ⟶ T)
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)})
    (g : freeAbelianSheaf.{q, w, v, u} (C := C) J T ⟶ F) (i : U.I) :
    ConcreteCategory.hom (Pi.π (fun i => F.obj.obj (op (U.obj i))) i)
      ((sectionsEquiv.{q, w, v, u} (C := C) J U F).toFun
        (freeAbelianSheafMap.{q, w, v, u} (C := C) J f ≫ g)) =
    F.obj.map (f.φ i).op
      (ConcreteCategory.hom (Pi.π (fun i => F.obj.obj (op (T.obj i))) (f.f i))
        ((sectionsEquiv.{q, w, v, u} (C := C) J T F).toFun g)) := by
  rw [sectionsEquiv_π J U F _ i, sectionsEquiv_π J T F _ (f.f i)]
  let k := evalι.{q, w, v, u} (C := C) T (f.f i) ≫
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
      ((sheafificationAdjunction J AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _ g)
  have hmap :
      evalι.{q, w, v, u} (C := C) U i ≫
        (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
          ((sheafificationAdjunction J AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _
            (freeAbelianSheafMap.{q, w, v, u} (C := C) J f ≫ g)) =
      (presheafULift.{q, w, v, u} (C := C)).map (uliftYoneda.{w}.map (f.φ i)) ≫ k := by
    show evalι.{q, w, v, u} (C := C) U i ≫
        (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
          ((sheafificationAdjunction J AddCommGrpCat.{max (max u v) (max q w)}).homEquiv _ _
            ((presheafToSheaf J AddCommGrpCat.{max (max u v) (max q w)}).map
              (((Functor.whiskeringRight Cᵒᵖ
                (Type (max (max u v) (max q w)))
                AddCommGrpCat.{max (max u v) (max q w)}).obj AddCommGrpCat.free).map
                  ((associatedPresheafFunctor.{max (max u v) (max q w)}
                    (C := C)).map f)) ≫ g)) = _
    rw [(sheafificationAdjunction J
      AddCommGrpCat.{max (max u v) (max q w)}).homEquiv_naturality_left
      (((Functor.whiskeringRight Cᵒᵖ (Type (max (max u v) (max q w)))
        AddCommGrpCat.{max (max u v) (max q w)}).obj AddCommGrpCat.free).map
        ((associatedPresheafFunctor.{max (max u v) (max q w)} (C := C)).map f)) g]
    rw [(AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left
      ((associatedPresheafFunctor.{max (max u v) (max q w)} (C := C)).map f)]
    rw [← Category.assoc, evalι_naturality]
    simp [k, Category.assoc]
  conv_lhs => rw [hmap]
  exact (yonedaEquiv_naturality (f := f.φ i) _ _).symm

/-- Evaluating the underlying presheaf of a sheaf of abelian groups on a semi-representable
object is the product of its values on the members. -/
noncomputable def evalOpProductIso (J : GrothendieckTopology C)
    (T : FormalCoproduct.{w} C) (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) :
    ((FormalCoproduct.evalOp C AddCommGrpCat.{max (max u v) (max q w)}).obj
      ((sheafToPresheaf J AddCommGrpCat.{max (max u v) (max q w)}).obj F)).obj (op T) ≅
      (∏ᶜ fun i => F.obj.obj (op (T.obj i)) : AddCommGrpCat.{max (max u v) (max q w)}) :=
  eqToIso (FormalCoproduct.evalOp_obj_obj C AddCommGrpCat.{max (max u v) (max q w)}
    ((sheafToPresheaf J AddCommGrpCat.{max (max u v) (max q w)}).obj F) (op T))

/-- The degreewise comparison of the complex of sections with the Hom complex. -/
noncomputable def sectionsDegreeIso (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) (n : ℕ) :
    (sectionsComplex.{q, w, v, u} J K F).X n ≅
      (homFreeAbelianSheafComplex.{q, w, v, u} J K F).X n := by
  exact ((Iso.addCommGroupIsoToAddEquiv
      (evalOpProductIso.{q, w, v, u} (C := C) J
        (K.obj (op (SimplexCategory.mk n))) F)).trans
    (sectionsAddEquiv.{q, w, v, u} (C := C) J
      (K.obj (op (SimplexCategory.mk n))) F).symm).toAddCommGrpIso

/-- The degreewise comparison, read through `sectionsEquiv`, is the product comparison. -/
lemma sectionsEquiv_sectionsDegreeIso (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) (n : ℕ)
    (z : (sectionsComplex.{q, w, v, u} J K F).X n) :
    (sectionsEquiv.{q, w, v, u} (C := C) J
      (K.obj (op (SimplexCategory.mk n))) F).toFun
      (ConcreteCategory.hom (sectionsDegreeIso.{q, w, v, u} (C := C) J K F n).hom z) =
    ConcreteCategory.hom
      (evalOpProductIso.{q, w, v, u} (C := C) J
        (K.obj (op (SimplexCategory.mk n))) F).hom z := by
  show sectionsEquiv.{q, w, v, u} (C := C) J
      (K.obj (op (SimplexCategory.mk n))) F
      ((sectionsEquiv.{q, w, v, u} (C := C) J
        (K.obj (op (SimplexCategory.mk n))) F).symm
        ((evalOpProductIso.{q, w, v, u} (C := C) J
          (K.obj (op (SimplexCategory.mk n))) F).hom z)) = _
  exact Equiv.apply_symm_apply _ _

/-- The additive Yoneda functor acts on a morphism of sheaves by precomposition. -/
lemma preadditiveYonedaRightOpMapApply {J : GrothendieckTopology C}
    (F A B : Sheaf J AddCommGrpCat.{t}) (f : A ⟶ B) (g : B ⟶ F) :
    ConcreteCategory.hom ((preadditiveYoneda.obj F).rightOp.map f).unop g = f ≫ g := rfl

/-- The differential of the complex of sections is the alternating sum of the coface maps. -/
lemma sectionsComplex_d (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) (n : ℕ) :
    (sectionsComplex.{q, w, v, u} J K F).d n (n + 1) =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ) •
        ((FormalCoproduct.cosimplicialObjectFunctor K).obj F.obj).δ j :
          (sectionsComplex.{q, w, v, u} J K F).X n ⟶
            (sectionsComplex.{q, w, v, u} J K F).X (n + 1)) := by
  show CochainComplex.of.d
      (fun m => ((FormalCoproduct.cosimplicialObjectFunctor K).obj F.obj).obj
        (SimplexCategory.mk m))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor K).obj F.obj)) n (n + 1) = _
  exact CochainComplex.of_d _ _ _

/-- The differential of the Hom complex is the alternating sum of the images under
`Hom(-, F)` of the face maps. -/
lemma homFreeAbelianSheafComplex_d (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) (n : ℕ) :
    (homFreeAbelianSheafComplex.{q, w, v, u} J K F).d n (n + 1) =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ) •
        ((preadditiveYoneda.obj F).rightOp.map
          ((((SimplicialObject.whiskering _
                (Sheaf J AddCommGrpCat.{max (max u v) (max q w)})).obj
              (_root_.CategoryTheory.Presheaf.freeAbelianSheaf J)).obj
            (associatedSimplicialPresheaf.{max (max u v) (max q w)} K)).δ j)).unop :
          (homFreeAbelianSheafComplex.{q, w, v, u} J K F).X n ⟶
            (homFreeAbelianSheafComplex.{q, w, v, u} J K F).X (n + 1)) := by
  show (((preadditiveYoneda.obj F).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((_root_.CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (associatedSimplicialPresheaf.{max (max u v) (max q w)} K))).unop.d n (n + 1) = _
  rw [HomologicalComplex.unop_d, Functor.mapHomologicalComplex_obj_d]
  dsimp only [_root_.CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor,
    Functor.comp_obj]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD, Functor.map_sum,
    Functor.map_zsmul, unop_sum, unop_zsmul]
  rfl

/-- The degreewise comparison is compatible with the `j`-th face map: this is the Tag 01GX
commutation, one summand of the alternating sum at a time. -/
lemma sectionsDegreeIso_comm_face (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) (i : ℕ) (j : Fin (i + 2)) :
    (sectionsDegreeIso.{q, w, v, u} (C := C) J K F i).hom ≫
        ((preadditiveYoneda.obj F).rightOp.map
          ((((SimplicialObject.whiskering _
                (Sheaf J AddCommGrpCat.{max (max u v) (max q w)})).obj
              (_root_.CategoryTheory.Presheaf.freeAbelianSheaf J)).obj
            (associatedSimplicialPresheaf.{max (max u v) (max q w)} K)).δ j)).unop =
      ((FormalCoproduct.cosimplicialObjectFunctor K).obj F.obj).δ j ≫
        (sectionsDegreeIso.{q, w, v, u} (C := C) J K F (i + 1)).hom := by
  apply ConcreteCategory.hom_ext
  intro z
  apply (sectionsEquiv.{q, w, v, u} (C := C) J
    (K.obj (op (SimplexCategory.mk (i + 1)))) F).injective
  apply (Concrete.productEquiv (fun k =>
    F.obj.obj (op ((K.obj (op (SimplexCategory.mk (i + 1)))).obj k)))).injective
  funext k
  simp only [Concrete.productEquiv_apply_apply]
  let T := K.obj (op (SimplexCategory.mk i))
  let U := K.obj (op (SimplexCategory.mk (i + 1)))
  have hT := sectionsEquiv_sectionsDegreeIso.{q, w, v, u} (C := C) J K F i z
  have hU := sectionsEquiv_sectionsDegreeIso.{q, w, v, u} (C := C) J K F (i + 1)
    ((ConcreteCategory.hom
      (((FormalCoproduct.cosimplicialObjectFunctor K).obj F.obj).δ j)) z)
  set g : freeAbelianSheaf.{q, w, v, u} (C := C) J T ⟶ F :=
    ConcreteCategory.hom (sectionsDegreeIso.{q, w, v, u} (C := C) J K F i).hom z
  set h : freeAbelianSheaf.{q, w, v, u} (C := C) J U ⟶ F :=
    ConcreteCategory.hom (sectionsDegreeIso.{q, w, v, u} (C := C) J K F (i + 1)).hom
      (ConcreteCategory.hom (((FormalCoproduct.cosimplicialObjectFunctor K).obj F.obj).δ j) z)
  have hn := sectionsEquiv_naturality.{q, w, v, u} (C := C) J
    (K.δ j) F g k
  let face := (((SimplicialObject.whiskering
      (Cᵒᵖ ⥤ Type (max (max (max u v) (max q w)) w v))
      (Sheaf J AddCommGrpCat.{max (max u v) (max q w)})).obj
      ((Functor.whiskeringRight Cᵒᵖ
        (Type (max (max (max u v) (max q w)) w v))
        AddCommGrpCat.{max (max u v) (max q w)}).obj AddCommGrpCat.free ⋙
        presheafToSheaf J AddCommGrpCat.{max (max u v) (max q w)})).obj
      (associatedSimplicialPresheaf.{max (max u v) (max q w)} K)).δ j
  have hface : face = freeAbelianSheafMap.{q, w, v, u} (C := C) J (K.δ j) := by
    rfl
  have hmap :
      ConcreteCategory.hom ((preadditiveYoneda.obj F).rightOp.map face).unop
        (ConcreteCategory.hom
          (sectionsDegreeIso.{q, w, v, u} (C := C) J K F i).hom z) =
      freeAbelianSheafMap.{q, w, v, u} (C := C) J (K.δ j) ≫ g := by
    rw [hface]
    show ConcreteCategory.hom
        ((preadditiveYoneda.obj F).rightOp.map
          (freeAbelianSheafMap.{q, w, v, u} (C := C) J (K.δ j))).unop
        (ConcreteCategory.hom
          (sectionsDegreeIso.{q, w, v, u} (C := C) J K F i).hom z) =
      freeAbelianSheafMap.{q, w, v, u} (C := C) J (K.δ j) ≫ g
    exact preadditiveYonedaRightOpMapApply (C := C) (F := F)
      (A := freeAbelianSheaf.{q, w, v, u} (C := C) J U)
      (B := freeAbelianSheaf.{q, w, v, u} (C := C) J T)
      (f := freeAbelianSheafMap.{q, w, v, u} (C := C) J (K.δ j))
      (g := ConcreteCategory.hom
        (sectionsDegreeIso.{q, w, v, u} (C := C) J K F i).hom z)
  dsimp only [face] at hmap
  calc
    _ = (ConcreteCategory.hom (F.obj.map ((K.δ j).φ k).op))
        (ConcreteCategory.hom
          (Pi.π (fun l => F.obj.obj (op ((K.obj (op (SimplexCategory.mk i))).obj l)))
            ((K.δ j).f k))
          ((sectionsEquiv.{q, w, v, u} (C := C) J T F).toFun g)) := by
      show ConcreteCategory.hom
          (Pi.π (fun l => F.obj.obj
            (op ((K.obj (op (SimplexCategory.mk (i + 1)))).obj l))) k)
          ((sectionsEquiv.{q, w, v, u} (C := C) J U F).toFun
            (ConcreteCategory.hom
              ((preadditiveYoneda.obj F).rightOp.map face).unop
              (ConcreteCategory.hom
                (sectionsDegreeIso.{q, w, v, u} (C := C) J K F i).hom z))) = _
      rw [hmap]
      simpa [T] using hn
    _ = _ := by
      show _ = ConcreteCategory.hom
        (Pi.π (fun k => F.obj.obj
          (op ((K.obj (op (SimplexCategory.mk (i + 1)))).obj k))) k)
        ((sectionsEquiv.{q, w, v, u} (C := C) J U F).toFun h)
      rw [hT, hU]
      show ConcreteCategory.hom (F.obj.map ((K.δ j).φ k).op)
          (ConcreteCategory.hom
            (Pi.π (fun l => F.obj.obj (op ((K.obj (op (SimplexCategory.mk i))).obj l)))
              ((K.δ j).f k)) z) =
        ConcreteCategory.hom
          (Pi.π (fun l => F.obj.obj
            (op ((K.obj (op (SimplexCategory.mk (i + 1)))).obj l))) k)
          (ConcreteCategory.hom
            (((FormalCoproduct.cosimplicialObjectFunctor K).obj F.obj).δ j) z)
      refine Eq.trans ?_ (Pi.lift_π_apply
        (fun l => Pi.π (fun m => F.obj.obj (op ((K.obj (op (SimplexCategory.mk i))).obj m)))
            ((K.δ j).f l) ≫ F.obj.map ((K.δ j).φ l).op) k z).symm
      rfl


/-- **Stacks Project, Tag 01GX.** The cochain complex of sections on any simplicial
semi-representable presheaf is canonically the Hom complex from its complex of free abelian
sheaves. -/
@[stacks 01GX "arbitrary semi-representable simplicial object"]
noncomputable def sectionsComplexIsoHomFreeAbelianSheafComplex
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) :
    sectionsComplex.{q, w, v, u} J K F ≅
      homFreeAbelianSheafComplex.{q, w, v, u} J K F := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => sectionsDegreeIso.{q, w, v, u} (C := C) J K F n) ?_
  intro i j hij
  have hrel : i + 1 = j := by simpa [ComplexShape.up] using hij
  subst j
  rw [sectionsComplex_d.{q, w, v, u}, homFreeAbelianSheafComplex_d.{q, w, v, u}]
  refine Eq.trans (Preadditive.comp_sum _ _ _)
    (Eq.trans (Finset.sum_congr rfl ?_) (Preadditive.sum_comp _ _ _).symm)
  intro j _
  exact Eq.trans (Preadditive.comp_zsmul _ _ _)
    (Eq.trans (congrArg (fun x => (-1 : ℤ) ^ (j : ℕ) • x)
      (sectionsDegreeIso_comm_face.{q, w, v, u} (C := C) J K F i j))
      (Preadditive.zsmul_comp _ _ _).symm)

end Stacks.CategoryTheory.Hypercovering.SemiRepresentable

end
