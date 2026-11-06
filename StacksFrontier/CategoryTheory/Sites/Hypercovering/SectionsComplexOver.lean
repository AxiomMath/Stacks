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

/-!
# The complex of sections of a simplicial semi-representable object over an object

Let `C` be a category with a Grothendieck topology `J`, let `X : C`, let
`K` be a simplicial object of `FormalCoproduct (Over X)` — a simplicial semi-representable
object over `X`, `SR(C, X)` in the source — and let `F` be a sheaf of abelian groups on `C`.
Evaluating `F` degreewise on `K` gives a cochain complex `s(F(K))`, and this file develops the
identification of its degree-`n` term with the group of morphisms from the degree-`n` term of
the complex of free abelian sheaves `s(**Z**_{F(K)}^♯)` into `F`.

## Main definitions

* `associatedSimplicialPresheaf`: the simplicial presheaf represented by `K`, after forgetting
  the structure maps to `X`.
* `sectionsComplex`: the cochain complex `s(F(K))` obtained by evaluating `F` on `K`, i.e.
  Mathlib's `FormalCoproduct.cochainComplexFunctor` applied to the restriction of `F` along
  `Over.forget X`.
* `homFreeAbelianSheafComplex`: the cochain complex `Hom(s(**Z**_{F(K)}^♯), F)`.
* `formalEvalCoproductIso`, `formalEvalι`: the presheaf represented by a formal coproduct is
  the coproduct of the presheaves represented by its components, with its injections.
* `evaluationEquiv`, `sectionsEquiv`, `sectionsAddEquiv`: the sections of `F` over a formal
  coproduct, as a bijection, resp. an additive bijection, onto the product of the sections over
  the components; equivalently onto the morphisms from the free abelian sheaf.
* `evalOpProductIso`: the degreewise comparison with the chosen product.
* `sectionsDegreeIso`: the resulting degreewise isomorphism between the two complexes.

## Main results

* `sectionsEquiv_naturality`: `sectionsEquiv` is natural in the formal coproduct.
* `sectionsComplex_d` and `homFreeAbelianSheafComplex_d`: the differentials of the two
  complexes, each as the alternating sum of the (co)face maps.
* `sectionsDegreeIso_comm_face`: the degreewise comparison commutes with the `j`-th face map.
* `sectionsComplexIsoHomFreeAbelianSheafComplex`: **Stacks Project, Tag 01GX** for a simplicial
  semi-representable object over `X` — the two cochain complexes are isomorphic.

## Implementation notes

The universes `u`, `v` of `C` and the index universe `w` of the formal coproducts are
independent; the coefficient sheaf is `AddCommGrpCat.{max u v w}`-valued, which is forced: the
presheaf represented by a `w`-indexed family of objects over `X` takes values in
`Type (max u v w)`.

The comparison of the two complexes is arranged around three definitional mismatches. First,
`sectionsComplex` is a `CochainComplex`, indexed by `ComplexShape.up ℕ`, while
`homFreeAbelianSheafComplex` is built by `HomologicalComplex.unop` and is natively indexed by
`(ComplexShape.down ℕ).symm`; the two shapes are definitionally but not syntactically equal, so a
goal mentioning both is not type-correct at `implicit` transparency and `rw`/`simp` are rejected on
it. `homFreeAbelianSheafComplex` is therefore a `def` rather than an `abbrev`, so that keyed
matching cannot unfold it into the ill-typed form, and `homFreeAbelianSheafComplex_d` confines the
one unfolding that is needed to a goal with no composition in it.

Second, for the same reason `Preadditive.comp_sum` and `Preadditive.sum_comp` cannot be used as
rewrites in the commutation goal: matching happens at reducible transparency, where the two
spellings do not meet. They are instead applied as *terms* through `Eq.trans`, which only ever
asks for a definitional equality. The whole assembly of
`sectionsComplexIsoHomFreeAbelianSheafComplex` from `sectionsDegreeIso_comm_face` is that one
`Eq.trans` chain.

Third, in the last step of `sectionsDegreeIso_comm_face` the comparison isomorphisms of
`evalOpProductIso` carry `eqToHom` of definitional equalities, which block `Pi.lift_π_apply`; a
`change` discharges them by proof irrelevance, after which the lemma has to be supplied with its
family of morphisms explicit.

## References

* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe q w v u

namespace Stacks.CategoryTheory.Hypercovering.SectionsOver

variable {C : Type u} [Category.{v} C]

/-- The simplicial presheaf represented by a simplicial formal coproduct of objects over `X`,
after forgetting the structure maps to `X`. -/
noncomputable abbrev associatedSimplicialPresheaf {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    SimplicialObject (Cᵒᵖ ⥤ Type (max u v w)) :=
  ((SimplicialObject.whiskering _ _).obj
    ((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
      (Over.forget X ⋙ uliftYoneda.{max u w}))).obj K

/-- The presheaf represented by a formal coproduct `T` of objects over `X` is the coproduct of
the presheaves represented by the components of `T`. -/
noncomputable def formalEvalCoproductIso {X : C}
    (T : FormalCoproduct.{w} (Over X)) :
    (((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
      (Over.forget X ⋙ uliftYoneda.{max u w})).obj T) ≅
      (∐ fun i ↦ uliftYoneda.{max u w}.obj ((T.obj i).left)) :=
  (eqToIso (FormalCoproduct.eval_obj_obj (C := Over X)
    (A := Cᵒᵖ ⥤ Type (max u v w))
    (F := Over.forget X ⋙ uliftYoneda.{max u w}) (X := T)))

/-- The injection of the presheaf represented by the `i`-th component of `T` into the presheaf
represented by `T`. -/
noncomputable def formalEvalι {X : C} (T : FormalCoproduct.{w} (Over X))
    (i : T.I) : uliftYoneda.{max u w}.obj ((T.obj i).left) ⟶
      (((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
        (Over.forget X ⋙ uliftYoneda.{max u w})).obj T) :=
  Sigma.ι (fun i ↦ uliftYoneda.{max u w}.obj ((T.obj i).left)) i ≫
    (formalEvalCoproductIso (X := X) T).inv

/-- The injections `formalEvalι` are natural with respect to morphisms of formal coproducts. -/
lemma formalEvalι_naturality {X : C} {U T : FormalCoproduct.{w} (Over X)}
    (f : U ⟶ T) (i : U.I) :
    formalEvalι U i ≫
        ((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
          (Over.forget X ⋙ uliftYoneda.{max u w})).map f =
      uliftYoneda.{max u w}.map ((Over.forget X).map (f.φ i)) ≫
        formalEvalι T (f.f i) := by
  cases FormalCoproduct.eval_obj_obj (C := Over X)
    (A := Cᵒᵖ ⥤ Type (max u v w))
    (F := Over.forget X ⋙ uliftYoneda.{max u w}) (X := U)
  cases FormalCoproduct.eval_obj_obj (C := Over X)
    (A := Cᵒᵖ ⥤ Type (max u v w))
    (F := Over.forget X ⋙ uliftYoneda.{max u w}) (X := T)
  simp only [formalEvalι, formalEvalCoproductIso, eqToIso.inv, FormalCoproduct.eval_obj_map,
    Functor.comp_obj, Over.forget_obj, Functor.comp_map, Over.forget_map]
  show Sigma.ι (fun j ↦ uliftYoneda.{max u w}.obj ((U.obj j).left)) i ≫
      Sigma.desc (fun j ↦ uliftYoneda.{max u w}.map ((Over.forget X).map (f.φ j)) ≫
        Sigma.ι (fun j ↦ uliftYoneda.{max u w}.obj ((T.obj j).left)) (f.f j)) =
    uliftYoneda.{max u w}.map ((Over.forget X).map (f.φ i)) ≫
      Sigma.ι (fun j ↦ uliftYoneda.{max u w}.obj ((T.obj j).left)) (f.f i)
  simp

/-- Morphisms from the presheaf represented by `T` to the underlying presheaf of sets of `F`
correspond to elements of the product of the sections of `F` over the components of `T`. -/
noncomputable def evaluationEquiv {X : C} (J : GrothendieckTopology C)
    (T : FormalCoproduct.{w} (Over X)) (F : Sheaf J AddCommGrpCat.{max u v w}) :
    ((((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
      (Over.forget X ⋙ uliftYoneda.{max u w})).obj T) ⟶
        ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F ⋙ forget AddCommGrpCat)) ≃
      (∏ᶜ fun i ↦ F.obj.obj (op ((T.obj i).left)) : AddCommGrpCat.{max u v w}) where
  toFun f := (Concrete.productEquiv (fun i ↦ F.obj.obj (op ((T.obj i).left)))).symm
    (fun i ↦ uliftYonedaEquiv.{max u w}
      (formalEvalι T i ≫ f))
  invFun a := (formalEvalCoproductIso (X := X) T).hom ≫
    Sigma.desc fun i ↦ uliftYonedaEquiv.{max u w}.symm
      (Concrete.productEquiv (fun i ↦ F.obj.obj (op ((T.obj i).left))) a i)
  left_inv f := by
    apply (cancel_epi (formalEvalCoproductIso (X := X) T).inv).1
    apply Sigma.hom_ext
    intro i
    apply uliftYonedaEquiv.{max u w}.injective
    simp [formalEvalι, Category.assoc]
  right_inv a := by
    apply (Concrete.productEquiv (fun i ↦ F.obj.obj (op ((T.obj i).left)))).injective
    ext i
    simp only [Equiv.apply_symm_apply]
    apply (uliftYonedaEquiv.{max u w} (C := C)).symm.injective
    simp [formalEvalι]

/-- The `i`-th component of `evaluationEquiv J T F f` is the section of `F` corresponding by
Yoneda to the restriction of `f` to the `i`-th component of `T`. -/
lemma evaluationEquiv_π {X : C} (J : GrothendieckTopology C)
    (T : FormalCoproduct.{w} (Over X)) (F : Sheaf J AddCommGrpCat.{max u v w})
    (f : (((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
      (Over.forget X ⋙ uliftYoneda.{max u w})).obj T ⟶
      ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F ⋙ forget AddCommGrpCat)))
    (i : T.I) :
      ConcreteCategory.hom (Pi.π (fun i ↦ F.obj.obj (op ((T.obj i).left))) i)
      ((evaluationEquiv J T F).toFun f) =
      uliftYonedaEquiv.{max u w} (formalEvalι T i ≫ f) := by
  simp [evaluationEquiv, Concrete.productEquiv_symm_apply_π]

/-- The section of `F` over the `i`-th component of `T` attached to a morphism from the free
abelian sheaf on `T` is additive in that morphism. -/
lemma sectionValue_add {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (T : FormalCoproduct.{w} (Over X)) (F : Sheaf J AddCommGrpCat.{max u v w})
    (f g : (presheafToSheaf J AddCommGrpCat.{max u v w}).obj
      ((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
        AddCommGrpCat.free |>.obj
        (((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
          (Over.forget X ⋙ uliftYoneda.{max u w})).obj T)) ⟶ F)
    (i : T.I) :
    (uliftYonedaEquiv.{max u w}
        (Sigma.ι (fun i ↦ uliftYoneda.obj ((T.obj i).left)) i ≫
          (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
            ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ (f + g))) :
        F.obj.obj (op ((T.obj i).left))) =
      @HAdd.hAdd (F.obj.obj (op ((T.obj i).left)))
        (F.obj.obj (op ((T.obj i).left))) (F.obj.obj (op ((T.obj i).left))) inferInstance
        (uliftYonedaEquiv.{max u w}
          (Sigma.ι (fun i ↦ uliftYoneda.obj ((T.obj i).left)) i ≫
            (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
              ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ f)) :
          F.obj.obj (op ((T.obj i).left)))
        (uliftYonedaEquiv.{max u w}
          (Sigma.ι (fun i ↦ uliftYoneda.obj ((T.obj i).left)) i ≫
            (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
              ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ g)) :
          F.obj.obj (op ((T.obj i).left))) := by
  let q : (((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
      AddCommGrpCat.free |>.obj
      (((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
        (Over.forget X ⋙ uliftYoneda.{max u w})).obj T)) ⟶
      (sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F) →
      F.obj.obj (op ((T.obj i).left)) := fun k ↦
    uliftYonedaEquiv.{max u w}
      (Sigma.ι (fun i ↦ uliftYoneda.obj ((T.obj i).left)) i ≫
        (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ k)
  calc
    _ = q ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ (f + g)) := rfl
    _ = q (((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ f) +
        ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ g)) :=
      congrArg q ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homAddEquiv_add _ _ f g)
    _ = _ := rfl

/-- Morphisms from the free abelian sheaf on the presheaf represented by `T` to `F` correspond to
elements of the product of the sections of `F` over the components of `T`. -/
noncomputable def sectionsEquiv {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (T : FormalCoproduct.{w} (Over X)) (F : Sheaf J AddCommGrpCat.{max u v w}) :
    ((presheafToSheaf J AddCommGrpCat.{max u v w}).obj
        ((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
          AddCommGrpCat.free |>.obj
          (((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
            (Over.forget X ⋙ uliftYoneda.{max u w})).obj T)) ⟶ F) ≃
      (∏ᶜ fun i ↦ F.obj.obj (op ((T.obj i).left)) : AddCommGrpCat.{max u v w}) :=
  ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans (evaluationEquiv J T F))

/-- The `i`-th component of `sectionsEquiv J T F f` is the section of `F` over the `i`-th
component of `T` corresponding to `f`. -/
lemma sectionsEquiv_π {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (T : FormalCoproduct.{w} (Over X)) (F : Sheaf J AddCommGrpCat.{max u v w})
    (f : (presheafToSheaf J AddCommGrpCat.{max u v w}).obj
      ((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
        AddCommGrpCat.free |>.obj
        (((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
          (Over.forget X ⋙ uliftYoneda.{max u w})).obj T)) ⟶ F)
    (i : T.I) :
    ConcreteCategory.hom (Pi.π (fun i ↦ F.obj.obj (op ((T.obj i).left))) i)
      ((sectionsEquiv J T F).toFun f) =
      uliftYonedaEquiv.{max u w}
        (formalEvalι T i ≫
          (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
            ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ f)) := by
  simp only [sectionsEquiv]
  exact evaluationEquiv_π J T F _ i

/-- The bijection `sectionsEquiv` as an isomorphism of abelian groups. -/
noncomputable def sectionsAddEquiv {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (T : FormalCoproduct.{w} (Over X)) (F : Sheaf J AddCommGrpCat.{max u v w}) :
    ((presheafToSheaf J AddCommGrpCat.{max u v w}).obj
        ((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
          AddCommGrpCat.free |>.obj
          (((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
            (Over.forget X ⋙ uliftYoneda.{max u w})).obj T)) ⟶ F) ≃+
      (∏ᶜ fun i ↦ F.obj.obj (op ((T.obj i).left)) : AddCommGrpCat.{max u v w}) where
  toEquiv := sectionsEquiv J T F
  map_add' f g := by
    apply (Concrete.productEquiv (fun i ↦ F.obj.obj (op ((T.obj i).left)))).injective
    funext i
    simp only [Concrete.productEquiv_apply_apply, map_add]
    rw [sectionsEquiv_π J T F (f + g) i, sectionsEquiv_π J T F f i,
      sectionsEquiv_π J T F g i]
    exact sectionValue_add J T F f g i

/-- The free abelian sheaf `**Z**_T^♯` on the presheaf represented by a formal coproduct `T` of
objects over `X`. -/
noncomputable abbrev freeAbelianSheaf {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] (T : FormalCoproduct.{w} (Over X)) :
    Sheaf J AddCommGrpCat.{max u v w} :=
  (presheafToSheaf J AddCommGrpCat.{max u v w}).obj
    ((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
      AddCommGrpCat.free |>.obj
      (((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
        (Over.forget X ⋙ uliftYoneda.{max u w})).obj T))

/-- The morphism of free abelian sheaves induced by a morphism of formal coproducts. -/
noncomputable def freeAbelianSheafMap {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {U T : FormalCoproduct.{w} (Over X)}
    (f : U ⟶ T) : freeAbelianSheaf J U ⟶ freeAbelianSheaf J T :=
  (presheafToSheaf J AddCommGrpCat.{max u v w}).map
    (((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
      AddCommGrpCat.free).map
      (((FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
        (Over.forget X ⋙ uliftYoneda.{max u w})).map f))

/-- `sectionsEquiv` is natural in the formal coproduct: precomposing with `freeAbelianSheafMap J f`
corresponds to restricting sections along the components of `f`. -/
lemma sectionsEquiv_naturality {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    {U T : FormalCoproduct.{w} (Over X)} (f : U ⟶ T)
    (F : Sheaf J AddCommGrpCat.{max u v w})
    (g : freeAbelianSheaf J T ⟶ F) (i : U.I) :
    ConcreteCategory.hom (Pi.π (fun i ↦ F.obj.obj (op ((U.obj i).left))) i)
      ((sectionsEquiv J U F).toFun (freeAbelianSheafMap J f ≫ g)) =
    F.obj.map ((Over.forget X).map (f.φ i)).op
      (ConcreteCategory.hom (Pi.π (fun i ↦ F.obj.obj (op ((T.obj i).left))) (f.f i))
        ((sectionsEquiv J T F).toFun g)) := by
  rw [sectionsEquiv_π J U F _ i, sectionsEquiv_π J T F _ (f.f i)]
  let k := formalEvalι T (f.f i) ≫
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
      ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ g)
  conv_rhs =>
    change ConcreteCategory.hom
      (((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F ⋙ forget AddCommGrpCat).map
        ((Over.forget X).map (f.φ i)).op)
      (uliftYonedaEquiv k)
    rw [uliftYonedaEquiv_naturality
      (F := (sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F ⋙ forget AddCommGrpCat)
      (f := k) (g := ((Over.forget X).map (f.φ i)).op)]
  let e := uliftYonedaEquiv.{max u w} (C := C) (X := (U.obj i).left)
    (F := (sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F ⋙ forget AddCommGrpCat)
  show e _ = e _
  rw [e.apply_eq_iff_eq]
  dsimp only [freeAbelianSheafMap]
  rw [(sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv_naturality_left,
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left, ← Category.assoc,
    formalEvalι_naturality (X := X) (U := U) (T := T) f i]
  simp [k, Category.assoc]

/-- The cochain complex `s(F(K))` obtained by evaluating an abelian sheaf `F` on a simplicial
formal coproduct `K`. -/
noncomputable abbrev sectionsComplex {X : C} (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  ((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
      (Over.forget X).op ⋙ FormalCoproduct.cochainComplexFunctor K).obj
    ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F)

/-- The differential of the complex of sections is the alternating sum of the coface maps. -/
lemma sectionsComplex_d {X : C} (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) (n : ℕ) :
    (sectionsComplex J K F).d n (n + 1) =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ) •
        ((FormalCoproduct.cosimplicialObjectFunctor K).obj
        (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
          (Over.forget X).op).obj ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F))).δ j :
          (sectionsComplex J K F).X n ⟶ (sectionsComplex J K F).X (n + 1)) := by
  show CochainComplex.of.d
      (fun m ↦ ((FormalCoproduct.cosimplicialObjectFunctor K).obj
        (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
          (Over.forget X).op).obj ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F))).obj
        (SimplexCategory.mk m))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor K).obj
        (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
          (Over.forget X).op).obj
            ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F)))) n (n + 1) = _
  exact CochainComplex.of_d _ _ _

/-- The cochain complex `Hom(s(ℤ_{F(K)}^♯), F)`. -/
noncomputable def homFreeAbelianSheafComplex {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  ((((preadditiveYoneda.obj F).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    ((CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (associatedSimplicialPresheaf K))).unop)

/-- The evaluation of `F` on a formal coproduct `T` is the product of the sections of `F` over
the components of `T`. -/
noncomputable def evalOpProductIso {X : C} (J : GrothendieckTopology C)
    (T : FormalCoproduct.{w} (Over X)) (F : Sheaf J AddCommGrpCat.{max u v w}) :
    ((FormalCoproduct.evalOp (Over X) AddCommGrpCat.{max u v w}).obj
      ((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
        (Over.forget X).op |>.obj ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F))).obj
      (op T) ≅ (∏ᶜ fun i ↦ F.obj.obj (op ((T.obj i).left)) : AddCommGrpCat.{max u v w}) :=
  eqToIso (FormalCoproduct.evalOp_obj_obj (C := Over X)
    (A := AddCommGrpCat.{max u v w})
    (F := ((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
      (Over.forget X).op).obj ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F))
    (X := op T))

/-- The isomorphism between the degree-`n` terms of `sectionsComplex J K F` and
`homFreeAbelianSheafComplex J K F`. -/
noncomputable def sectionsDegreeIso {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) (n : ℕ) :
    (sectionsComplex J K F).X n ≅ (homFreeAbelianSheafComplex J K F).X n :=
  ((Iso.addCommGroupIsoToAddEquiv
      (evalOpProductIso J (K.obj (op (SimplexCategory.mk n))) F)).trans
    (sectionsAddEquiv J (K.obj (op (SimplexCategory.mk n))) F).symm).toAddCommGrpIso

/-- `sectionsEquiv` sends the image of `z` under `sectionsDegreeIso` to the image of `z` under
`evalOpProductIso`. -/
lemma sectionsEquiv_sectionsDegreeIso {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) (n : ℕ)
    (z : (sectionsComplex J K F).X n) :
    sectionsEquiv J (K.obj (op (SimplexCategory.mk n))) F
      ((sectionsDegreeIso J K F n).hom z) =
    (evalOpProductIso J (K.obj (op (SimplexCategory.mk n))) F).hom z := by
  show sectionsEquiv J (K.obj (op (SimplexCategory.mk n))) F
      ((sectionsEquiv J (K.obj (op (SimplexCategory.mk n))) F).symm
        ((evalOpProductIso J (K.obj (op (SimplexCategory.mk n))) F).hom z)) = _
  exact Equiv.apply_symm_apply _ _

/-- The map induced by `f : A ⟶ B` on `Hom(-, F)` sends `g : B ⟶ F` to `f ≫ g`. -/
lemma preadditiveYoneda_rightOp_map_apply {J : GrothendieckTopology C}
    (F A B : Sheaf J AddCommGrpCat.{max u v w}) (f : A ⟶ B) (g : B ⟶ F) :
    ConcreteCategory.hom ((preadditiveYoneda.obj F).rightOp.map f).unop g = f ≫ g := rfl

/-- The differential of `homFreeAbelianSheafComplex` is the alternating sum of the images
under `Hom(-, F)` of the face maps of the simplicial object of free abelian sheaves. -/
lemma homFreeAbelianSheafComplex_d {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) (n : ℕ) :
    (homFreeAbelianSheafComplex J K F).d n (n + 1) =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ) •
        ((preadditiveYoneda.obj F).rightOp.map
          ((((SimplicialObject.whiskering _
              (Sheaf J AddCommGrpCat.{max u v w})).obj
            (Presheaf.freeAbelianSheaf J)).obj
          (associatedSimplicialPresheaf K)).δ j)).unop :
          (homFreeAbelianSheafComplex J K F).X n ⟶
            (homFreeAbelianSheafComplex J K F).X (n + 1)) := by
  show (((preadditiveYoneda.obj F).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (associatedSimplicialPresheaf K))).unop.d n (n + 1) = _
  rw [HomologicalComplex.unop_d, Functor.mapHomologicalComplex_obj_d]
  dsimp only [CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor, Functor.comp_obj]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD, Functor.map_sum,
    Functor.map_zsmul, unop_sum, unop_zsmul]

/-- The degreewise comparison `sectionsDegreeIso` is compatible with the `j`-th face maps. -/
lemma sectionsDegreeIso_comm_face {X : C} (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) (i : ℕ) (j : Fin (i + 2)) :
    (sectionsDegreeIso J K F i).hom ≫
        ((preadditiveYoneda.obj F).rightOp.map
          ((((SimplicialObject.whiskering _
              (Sheaf J AddCommGrpCat.{max u v w})).obj
            (Presheaf.freeAbelianSheaf J)).obj
          (associatedSimplicialPresheaf K)).δ j)).unop =
      ((FormalCoproduct.cosimplicialObjectFunctor K).obj
          (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
            (Over.forget X).op).obj
            ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F))).δ j ≫
        (sectionsDegreeIso J K F (i + 1)).hom := by
  apply ConcreteCategory.hom_ext
  intro z
  apply (sectionsEquiv J (K.obj (op (SimplexCategory.mk (i + 1)))) F).injective
  apply (Concrete.productEquiv (fun k ↦
    F.obj.obj (op ((K.obj (op (SimplexCategory.mk (i + 1)))).obj k).left))).injective
  funext k
  simp only [Concrete.productEquiv_apply_apply]
  let T := K.obj (op (SimplexCategory.mk i))
  let U := K.obj (op (SimplexCategory.mk (i + 1)))
  let g : freeAbelianSheaf J T ⟶ F :=
    ConcreteCategory.hom (sectionsDegreeIso J K F i).hom z
  have key : ∀ (n : ℕ) (z : (sectionsComplex J K F).X n),
      (sectionsEquiv J (K.obj (op (SimplexCategory.mk n))) F).toFun
        (ConcreteCategory.hom (sectionsDegreeIso J K F n).hom z) =
      ConcreteCategory.hom (evalOpProductIso J (K.obj (op (SimplexCategory.mk n))) F).hom z :=
    sectionsEquiv_sectionsDegreeIso J K F
  have hn := sectionsEquiv_naturality (J := J) (f := K.δ j) F g k
  have hT' : (sectionsEquiv J T F).toFun g =
      (ConcreteCategory.hom (evalOpProductIso J T F).hom) z := key i z
  let h : freeAbelianSheaf J U ⟶ F := ConcreteCategory.hom
    (sectionsDegreeIso J K F (i + 1)).hom
    (ConcreteCategory.hom
      (((FormalCoproduct.cosimplicialObjectFunctor K).obj
        (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat).obj
          (Over.forget X).op).obj ((sheafToPresheaf J AddCommGrpCat).obj F))).δ j) z)
  have hU' : (sectionsEquiv J U F).toFun h =
      (ConcreteCategory.hom (evalOpProductIso J U F).hom)
        ((ConcreteCategory.hom
          (((FormalCoproduct.cosimplicialObjectFunctor K).obj
            (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat).obj
              (Over.forget X).op).obj ((sheafToPresheaf J AddCommGrpCat).obj F))).δ j)) z) :=
    key (i + 1) _
  let face :=
    (((SimplicialObject.whiskering (Cᵒᵖ ⥤ Type (max (max u v) w))
      (Sheaf J AddCommGrpCat.{max u v w})).obj
      (Presheaf.freeAbelianSheaf J)).obj (associatedSimplicialPresheaf K)).δ j
  have hmap :
      ConcreteCategory.hom ((preadditiveYoneda.obj F).rightOp.map face).unop
        ((ConcreteCategory.hom (sectionsDegreeIso J K F i).hom) z) =
      freeAbelianSheafMap J (K.δ j) ≫ g :=
    preadditiveYoneda_rightOp_map_apply F _ _ (freeAbelianSheafMap J (K.δ j)) g
  dsimp only [face] at hmap
  calc
    _ = (ConcreteCategory.hom (F.obj.map ((Over.forget X).map ((K.δ j).φ k)).op))
        (ConcreteCategory.hom
          (Pi.π (fun l ↦ F.obj.obj (op ((K.obj (op (SimplexCategory.mk i))).obj l).left))
            ((K.δ j).f k))
          ((sectionsEquiv J T F).toFun g)) := by
      show ConcreteCategory.hom
          (Pi.π (fun l ↦ F.obj.obj
            (op ((K.obj (op (SimplexCategory.mk (i + 1)))).obj l).left)) k)
          ((sectionsEquiv J (K.obj (op (SimplexCategory.mk (i + 1)))) F).toFun
            (ConcreteCategory.hom
              ((preadditiveYoneda.obj F).rightOp.map face).unop
              (ConcreteCategory.hom (sectionsDegreeIso J K F i).hom z))) = _
      rw [hmap]
      simpa [T] using hn
    _ = _ := by
      show _ = ConcreteCategory.hom
        (Pi.π (fun k ↦ F.obj.obj
          (op ((K.obj (op (SimplexCategory.mk (i + 1)))).obj k).left)) k)
        ((sectionsEquiv J U F).toFun h)
      rw [hT', hU']
      show ConcreteCategory.hom
          (F.obj.map ((Over.forget X).map ((K.δ j).φ k)).op)
          (ConcreteCategory.hom
            (Pi.π (fun l ↦ F.obj.obj
              (op ((K.obj (op (SimplexCategory.mk i))).obj l).left))
              ((K.δ j).f k)) z) =
        ConcreteCategory.hom
          (Pi.π (fun l ↦ F.obj.obj
            (op ((K.obj (op (SimplexCategory.mk (i + 1)))).obj l).left)) k)
          (ConcreteCategory.hom
            (((FormalCoproduct.cosimplicialObjectFunctor K).obj
              (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
                (Over.forget X).op).obj
                ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F))).δ j) z)
      refine Eq.trans ?_ (Pi.lift_π_apply
        (fun l ↦ Pi.π (fun m ↦ F.obj.obj
            (op ((K.obj (op (SimplexCategory.mk i))).obj m).left))
            ((K.δ j).f l) ≫
          F.obj.map ((Over.forget X).map ((K.δ j).φ l)).op) k z).symm
      rfl

/-- The complex obtained by evaluating an abelian sheaf `F` on a simplicial semi-representable
object `K` is isomorphic to the complex of morphisms from the associated complex of free abelian
sheaves into `F`. -/
@[stacks 01GX "formal coproducts over an object"]
noncomputable def sectionsComplexIsoHomFreeAbelianSheafComplex {X : C}
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v w}]
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) :
    sectionsComplex J K F ≅ homFreeAbelianSheafComplex J K F := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n ↦ sectionsDegreeIso J K F n) ?_
  intro i j hij
  obtain rfl : i + 1 = j := by simpa [ComplexShape.up] using hij
  rw [sectionsComplex_d, homFreeAbelianSheafComplex_d]
  refine Eq.trans (Preadditive.comp_sum _ _ _)
    (Eq.trans (Finset.sum_congr rfl ?_) (Preadditive.sum_comp _ _ _).symm)
  intro j _
  exact Eq.trans (Preadditive.comp_zsmul _ _ _)
    (Eq.trans (congrArg (fun x ↦ (-1 : ℤ) ^ (j : ℕ) • x)
      (sectionsDegreeIso_comm_face J K F i j))
      (Preadditive.zsmul_comp _ _ _).symm)

end Stacks.CategoryTheory.Hypercovering.SectionsOver

end
