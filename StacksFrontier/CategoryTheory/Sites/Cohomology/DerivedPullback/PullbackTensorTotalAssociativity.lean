module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictBifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex

/-!
# The associativity coherence of Tag 03EL at the tensor bifunctor of Tag 06YM

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The associativity
coherence of the comparison `f^*(F ⊗ G) ≅ f^*F ⊗ f^*G` of Tag 03EL is proved for the strict
monoidal structure of Tag 01CA (`Stacks.SheafOfModules.RingedToposPullback.associativity`). This
file reads it for the monoidal structures re-seated on the tensor bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, the one total tensor complexes are built from, and
records the comparison of total tensor complexes on the summands of its target.

## Main results

* `Stacks.SheafOfModules.associator_sheafTensor_eq_strict`: the two structures have the same
  associator.
* `Stacks.SheafOfModules.pullbackTensorIso_hom_associativity` and
  `Stacks.SheafOfModules.pullbackTensorIso_inv_associativity`: the associativity coherence.
* `Stacks.SheafOfModules.pullbackTensorIso_inv_naturality_fst`, `_snd`.
* `Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_inv`.

## Implementation notes

The objects of the two structures agree by `rfl`, but a comparison of nested tensor products
across the two spellings is expensive, and the cost adds up within a declaration. The
comparison is therefore split, by `Stacks.SheafOfModules.comp₃_heq`, into comparisons of the
factors, each in a declaration of its own.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.SheafOfModules

section Associator

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

/-- The associator of the monoidal structure of `Mod(O)` re-seated on `⊗_O` is the associator
of the strict monoidal structure of Tag 01CA. -/
theorem associator_sheafTensor_eq_strict
    (A B D : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (@MonoidalCategoryStruct.associator _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor O).toMonoidalCategoryStruct A B
        D).hom =
      (@MonoidalCategoryStruct.associator _ _
        (Strict.monoidalUnderlyingRingSheaf O).toMonoidalCategoryStruct A B D).hom := by
  have reseatedFormula := @CategoryTheory.MonoidalCategory.reseat_associator _ _
    (_root_.SheafOfModules.monoidalCategory O) _ _
    (_root_.SheafOfModules.sheafTensorNatIso O) (_root_.SheafOfModules.unitIso O) A B D
  have strictFormula := congrArg Iso.hom
    (Stacks.SheafOfModules.Strict.associator_eq O.obj
      (TensorEncodings.isSheaf_structureRingPresheaf O) A B D)
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc] at strictFormula
  refine reseatedFormula.trans ?_
  refine Eq.trans ?_ strictFormula.symm
  simp only [Category.assoc]
  rfl

end Associator

section Pullback

/-- Two threefold composites are heterogeneously equal as soon as their factors are, the objects
being equal. This splits a comparison of composites across two spellings of the same objects
into comparisons of the factors. -/
lemma comp₃_heq {𝒞 : Type*} [Category 𝒞] {A B D E A' B' D' E' : 𝒞} (hA : A = A')
    (hB : B = B') (hD : D = D') (hE : E = E') {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E}
    {a' : A' ⟶ B'} {b' : B' ⟶ D'} {c' : D' ⟶ E'} (ha : HEq a a') (hb : HEq b b')
    (hc : HEq c c') : HEq (a ≫ b ≫ c) (a' ≫ b' ≫ c') := by
  subst hA hB hD hE
  subst ha hb hc
  rfl

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

attribute [local instance] Strict.monoidalUnderlyingRingSheaf in
private theorem whiskerLeft_pullbackTensorComparison
    (F G H : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
        ((RingedToposHom.pullbackModules f).obj F)).map
        ((pullbackTensorIso f).hom.app (G, H)) =
      (RingedToposHom.pullbackModules f).obj F ◁
        RingedToposPullback.pullbackTensorComparison f G H :=
  (tensorSheafBifunctor_map_id_fst X.O _ _).symm.trans
    (Strict.whiskerLeft_eq_tensorSheafBifunctor_map X.O _ _).symm

attribute [local instance] Strict.monoidalUnderlyingRingSheaf in
private theorem whiskerRight_pullbackTensorComparison
    (F G H : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    RingedToposPullback.pullbackTensorComparison f F G ▷ (RingedToposHom.pullbackModules f).obj H =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
        ((pullbackTensorIso f).hom.app (F, G))).app ((RingedToposHom.pullbackModules f).obj H) :=
  (Strict.whiskerRight_eq_tensorSheafBifunctor_map X.O _ _).trans
    (tensorSheafBifunctor_map_id_snd X.O _ _)

attribute [local instance] Strict.monoidalUnderlyingRingSheaf in
private theorem associativity_left_eq
    (F G H : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (RingedToposHom.pullbackModules f).map (@MonoidalCategoryStruct.associator _ _
          (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O).toMonoidalCategoryStruct
          F G H).hom ≫
        (pullbackTensorIso f).hom.app
          (F, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj G).obj H) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              ((RingedToposHom.pullbackModules f).obj F)).map
            ((pullbackTensorIso f).hom.app (G, H)) =
      (RingedToposHom.pullbackModules f).map (α_ F G H).hom ≫
        RingedToposPullback.pullbackTensorComparison f F (G ⊗ H) ≫
          ((RingedToposHom.pullbackModules f).obj F ◁
             RingedToposPullback.pullbackTensorComparison f G H) :=
  eq_of_heq (comp₃_heq rfl rfl rfl rfl
    (heq_of_eq (congrArg (RingedToposHom.pullbackModules f).map
      (associator_sheafTensor_eq_strict Y.O F G H))) HEq.rfl
    (heq_of_eq (whiskerLeft_pullbackTensorComparison f F G H)))

attribute [local instance] Strict.monoidalUnderlyingRingSheaf in
private theorem associativity_right_eq
    (F G H : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    RingedToposPullback.pullbackTensorComparison f (F ⊗ G) H ≫
        (RingedToposPullback.pullbackTensorComparison f F G ▷
            (RingedToposHom.pullbackModules f).obj H) ≫
          (α_ ((RingedToposHom.pullbackModules f).obj F) ((RingedToposHom.pullbackModules f).obj G)
            ((RingedToposHom.pullbackModules f).obj H)).hom =
      (pullbackTensorIso f).hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj G, H) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            ((pullbackTensorIso f).hom.app (F, G))).app ((RingedToposHom.pullbackModules f).obj H) ≫
          (@MonoidalCategoryStruct.associator _ _
            (_root_.SheafOfModules.monoidalCategorySheafTensor X.O).toMonoidalCategoryStruct
            ((RingedToposHom.pullbackModules f).obj F) ((RingedToposHom.pullbackModules f).obj G)
            ((RingedToposHom.pullbackModules f).obj H)).hom :=
  eq_of_heq (comp₃_heq rfl rfl rfl rfl HEq.rfl
    (heq_of_eq (whiskerRight_pullbackTensorComparison f F G H))
    (heq_of_eq (associator_sheafTensor_eq_strict X.O _ _ _).symm))

/-- **The associativity coherence of Tag 03EL at the tensor bifunctor of Tag 06YM**: the
comparison `f^*(F ⊗ G) ≅ f^*F ⊗ f^*G` is compatible with the associators of the monoidal
structures of `Mod(O_D)` and `Mod(O_C)` re-seated on `⊗`. -/
theorem pullbackTensorIso_hom_associativity
    (F G H : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (RingedToposHom.pullbackModules f).map (@MonoidalCategoryStruct.associator _ _
          (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O).toMonoidalCategoryStruct
          F G H).hom ≫
        (pullbackTensorIso f).hom.app
          (F, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj G).obj H) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              ((RingedToposHom.pullbackModules f).obj F)).map
            ((pullbackTensorIso f).hom.app (G, H)) =
      (pullbackTensorIso f).hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj G, H) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            ((pullbackTensorIso f).hom.app (F, G))).app ((RingedToposHom.pullbackModules f).obj H) ≫
          (@MonoidalCategoryStruct.associator _ _
            (_root_.SheafOfModules.monoidalCategorySheafTensor X.O).toMonoidalCategoryStruct
            ((RingedToposHom.pullbackModules f).obj F) ((RingedToposHom.pullbackModules f).obj G)
            ((RingedToposHom.pullbackModules f).obj H)).hom :=
  (associativity_left_eq f F G H).trans ((RingedToposPullback.associativity f F G H).trans
    (associativity_right_eq f F G H))

/-- Inverting the two sides of an equation between composites of three isomorphisms. -/
private lemma inv_assoc_of_hom {𝒞 : Type*} [Category 𝒞] {A B C D E G : 𝒞} (a : A ≅ B)
    (b : B ≅ C) (c : C ≅ D) (d : A ≅ E) (e : E ≅ G) (g : G ≅ D)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ g.hom) :
    e.inv ≫ d.inv ≫ a.hom = g.hom ≫ c.inv ≫ b.inv := by
  rw [← cancel_epi e.hom, ← cancel_epi d.hom, ← cancel_mono b.hom, ← cancel_mono c.hom]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- **The associativity coherence of Tag 03EL at the tensor bifunctor of Tag 06YM**, for the
inverse comparison `f^*F ⊗ f^*G ⟶ f^*(F ⊗ G)`: the form in which it is the associativity of a
tensorator. -/
theorem pullbackTensorIso_inv_associativity
    (F G H : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
        ((pullbackTensorIso f).inv.app (F, G))).app ((RingedToposHom.pullbackModules f).obj H) ≫
        (pullbackTensorIso f).inv.app
            (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj G, H) ≫
          (RingedToposHom.pullbackModules f).map (@MonoidalCategoryStruct.associator _ _
          (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O).toMonoidalCategoryStruct
          F G H).hom =
      (@MonoidalCategoryStruct.associator _ _
          (_root_.SheafOfModules.monoidalCategorySheafTensor X.O).toMonoidalCategoryStruct
          ((RingedToposHom.pullbackModules f).obj F) ((RingedToposHom.pullbackModules f).obj G)
          ((RingedToposHom.pullbackModules f).obj H)).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
            ((RingedToposHom.pullbackModules f).obj F)).map
            ((pullbackTensorIso f).inv.app (G, H)) ≫
          (pullbackTensorIso f).inv.app
            (F, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj G).obj H) :=
  inv_assoc_of_hom
    ((RingedToposHom.pullbackModules f).mapIso (@MonoidalCategoryStruct.associator _ _
          (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O).toMonoidalCategoryStruct F G H))
    ((pullbackTensorIso f).app (F, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj G).obj H))
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
        ((RingedToposHom.pullbackModules f).obj F)).mapIso
      ((pullbackTensorIso f).app (G, H)))
    ((pullbackTensorIso f).app (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj G, H))
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).mapIso
      ((pullbackTensorIso f).app (F, G))).app ((RingedToposHom.pullbackModules f).obj H))
    (@MonoidalCategoryStruct.associator _ _
          (_root_.SheafOfModules.monoidalCategorySheafTensor X.O).toMonoidalCategoryStruct
          ((RingedToposHom.pullbackModules f).obj F) ((RingedToposHom.pullbackModules f).obj G)
          ((RingedToposHom.pullbackModules f).obj H))
    (pullbackTensorIso_hom_associativity f F G H)

/-- Reading a naturality square of isomorphisms on the inverses. -/
private lemma inv_comp_of_comp_hom {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞} (x : A ⟶ C)
    (i : A ≅ B) (i' : C ≅ D) (y : B ⟶ D) (h : x ≫ i'.hom = i.hom ≫ y) :
    y ≫ i'.inv = i.inv ≫ x := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- The inverse comparison of Tag 03EL is natural in the first module. -/
theorem pullbackTensorIso_inv_naturality_fst
    {A A' : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} (a : A ⟶ A')
    (B : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
        ((RingedToposHom.pullbackModules f).map a)).app
        ((RingedToposHom.pullbackModules f).obj B) ≫ (pullbackTensorIso f).inv.app (A', B) =
      (pullbackTensorIso f).inv.app (A, B) ≫
        (RingedToposHom.pullbackModules f).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map a).app B) :=
  inv_comp_of_comp_hom _ ((pullbackTensorIso f).app (A, B)) ((pullbackTensorIso f).app (A', B)) _
    (pullbackTensorIso_hom_naturality_fst f a B)

/-- The inverse comparison of Tag 03EL is natural in the second module. -/
theorem pullbackTensorIso_inv_naturality_snd
    (A : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    {B B' : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (b : B ⟶ B') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
        ((RingedToposHom.pullbackModules f).obj A)).map
        ((RingedToposHom.pullbackModules f).map b) ≫ (pullbackTensorIso f).inv.app (A, B') =
      (pullbackTensorIso f).inv.app (A, B) ≫
        (RingedToposHom.pullbackModules f).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj A).map b) :=
  inv_comp_of_comp_hom _ ((pullbackTensorIso f).app (A, B)) ((pullbackTensorIso f).app (A, B')) _
    (pullbackTensorIso_hom_naturality_snd f A b)

end Pullback

end Stacks.SheafOfModules

namespace Stacks.Sheaves.DerivedPullback

open Stacks.SheafOfModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w', w'} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The inverse comparison of total tensor complexes on the summands**: on the summand of
bidegree `(p, q)` of `Tot(f^*K ⊗ f^*L)` it is the inverse comparison of Tag 03EL followed by
`f^*` of the summand inclusion. -/
lemma ι_pullbackTensorTotalIso_inv
    (K L : CochainComplex (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor ((pullbackComplexFunctor f).obj K)
          ((pullbackComplexFunctor f).obj L) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) p q n hpq ≫ (pullbackTensorTotalIso f K L).inv.f n =
      (pullbackTensorIso f).inv.app (K.X p, L.X q) ≫
        (RingedToposHom.pullbackModules f).map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p q n hpq) :=
  Stacks.SheafOfModules.inv_comp_of_comp_hom _ ((pullbackTensorIso f).app (K.X p, L.X q))
    ((HomologicalComplex.eval _ _ n).mapIso (pullbackTensorTotalIso f K L)) _
    (ι_pullbackTensorTotalIso_hom f K L p q n hpq)

end Stacks.Sheaves.DerivedPullback

end
