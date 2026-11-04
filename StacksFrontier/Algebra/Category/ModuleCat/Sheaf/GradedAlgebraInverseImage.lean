module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact

/-!
# Inverse image of a sheaf of graded algebras along a morphism of topoi

A morphism of topoi `f` carries a sheaf of graded `O`-algebras to a sheaf of graded
`f⁻¹O`-algebras, degree by degree: the homogeneous pieces of the result are the inverse images
of the homogeneous pieces, and the multiplication and unit are the inverse images of the
original ones.

## Main definitions

* `mulSheafHom` and `oneSheafHom` read the multiplication and unit of a sheaf of graded algebras
  as morphisms of the underlying sheaves of sets, out of a binary product and out of the
  terminal sheaf respectively.
* `transportGradedAlgebra` transports a sheaf of graded algebras along a finite-product-
  preserving functor of sheaves of sets, and `transportGradedAlgebraFunctor` is the functor it
  defines.
* `inverseImageGradedAlgebra` and `inverseImageGradedAlgebraFunctor` are the inverse image of a
  sheaf of graded algebras along a morphism of topoi, and the functor it defines.

## Main results

* `inverseImageGradedAlgebra_piece`: the homogeneous pieces are the inverse images of the
  original homogeneous pieces, on the nose.

## Implementation notes

Sections of an inverse image are not computable from sections of the original sheaf, so none of
the laws of a graded algebra can be checked on sections of the pieces of `f⁻¹A`. What replaces
that is the functor `Ψ X = Φ ⋙ (sections over X)` from sheaves of sets on the target site to
types, for `Φ` the functor on sheaves of sets underlying the transport: it preserves finite
products, so a pair of sections of the transports of two sheaves is the same thing as a section
of the transport of their product. Every operation is then the image under `Ψ X` of a morphism
of sheaves of sets on the target site, and every law is the image of an equation between such
morphisms. Those equations are proved on sections over the target site, where the graded
algebra's own laws are available.

The addition and scalar multiplication of sections of a transported sheaf of modules are
themselves of this form, by `Stacks.Sheaves.ToposPullback.moduleAddHom_pullback_apply` and
`moduleSMulHom_pullback_apply`, which is what makes the biadditivity and bilinearity of the
transported multiplication provable this way.

The two sides of a heterogeneous law land in homogeneous pieces whose degrees agree only
propositionally. The equation behind such a law is therefore a heterogeneous equality of
morphisms of sheaves of sets, obtained from the pointwise heterogeneous law by
`heq_sheafHom_of_sections`, and `heq_map_of_heq_hom` carries it through `Ψ X`.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.GradedAlgebraInverseImage

universe t w w' v u v' u'

/-! ### Heterogeneous equalities of morphisms of sheaves of sets -/

section Heq

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}

/-- Two morphisms of sheaves of sets with propositionally equal targets are heterogeneously
equal as soon as they agree on sections heterogeneously. -/
public lemma heq_sheafHom_of_sections {Z L R : Sheaf K (Type w')} (hLR : L = R)
    (left : Z ⟶ L) (right : Z ⟶ R)
    (h : ∀ (V : Dᵒᵖ) (s : (sectionsFunctor K V).obj Z),
      HEq ((sectionsFunctor K V).map left s) ((sectionsFunctor K V).map right s)) :
    HEq left right := by
  subst hLR
  refine heq_of_eq (hom_ext_sections fun V s => ?_)
  exact eq_of_heq (h V s)

/-- Equal morphisms of sheaves of sets act equally on sections, read through any functor to
types. -/
public lemma sheafHom_map_apply_congr {Z W : Sheaf K (Type w')} {left right : Z ⟶ W}
    (h : left = right) (P : Sheaf K (Type w') ⥤ Type t) (s : P.obj Z) :
    P.map left s = P.map right s := by
  rw [h]

/-- A heterogeneous equality of morphisms of sheaves of sets is carried to sections by any
functor to types. -/
public lemma heq_map_of_heq_hom {Z L R : Sheaf K (Type w')} (hLR : L = R)
    {left : Z ⟶ L} {right : Z ⟶ R} (h : HEq left right)
    (P : Sheaf K (Type w') ⥤ Type t) (s : P.obj Z) :
    HEq (P.map left s) (P.map right s) := by
  subst hLR
  rw [eq_of_heq h]

/-- Two sections which are images under `P` of heterogeneously equal morphisms are
heterogeneously equal. -/
private theorem heq_of_map_eq_of_heq_hom {Z L R : Sheaf K (Type w')} (hLR : L = R)
    {left : Z ⟶ L} {right : Z ⟶ R} (h : HEq left right)
    (P : Sheaf K (Type w') ⥤ Type t) (s : P.obj Z) {a : P.obj L} {b : P.obj R}
    (hL : P.map left s = a) (hR : P.map right s = b) : HEq a b := by
  subst hL hR
  exact heq_map_of_heq_hom hLR h P s

end Heq

/-! ### The multiplication and the unit as morphisms of sheaves of sets -/

section Operations

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{w'})] [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  {O : Sheaf K RingCat.{w'}}

/-- The underlying sheaf of sets of a homogeneous piece. -/
public noncomputable abbrev pieceSheaf (A : SheafOfModules.GradedAlgebra.{w', w'} O) (n : ℤ) :
    Sheaf K (Type w') :=
  moduleSheaf O (A.piece n)

variable (A : SheafOfModules.GradedAlgebra.{w', w'} O)

/-- Multiplication of homogeneous sections, as a morphism out of the product of the underlying
sheaves of sets. -/
public noncomputable def mulSheafHom (i j : ℤ) :
    pieceSheaf A i ⨯ pieceSheaf A j ⟶ pieceSheaf A (i + j) :=
  binaryOpHom (fun X x y => (A.mul i j).app X x y)
    (fun g x y => (A.mul i j).naturality g x y)

/-- The unit of a sheaf of graded algebras, as a morphism out of the terminal sheaf of sets. -/
public noncomputable def oneSheafHom :
    (⊤_ (Sheaf K (Type w'))) ⟶ pieceSheaf A 0 :=
  constHom (fun X => A.one.eval X) (fun g => PresheafOfModules.sections_property A.one g)

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- On sections, `mulSheafHom` is the multiplication of homogeneous sections. -/
public lemma sections_mulSheafHom (i j : ℤ) (X : Dᵒᵖ)
    (x : (sectionsFunctor K X).obj (pieceSheaf A i))
    (y : (sectionsFunctor K X).obj (pieceSheaf A j)) :
    (sectionsFunctor K X).map (mulSheafHom A i j) (Functor.prodObjMk x y) =
      (A.mul i j).app X x y :=
  sectionsFunctor_map_binaryOpHom _ _ X x y

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- On sections, `oneSheafHom` is the unit section of the graded algebra. -/
public lemma sections_oneSheafHom (X : Dᵒᵖ)
    (p : (sectionsFunctor K X).obj (⊤_ (Sheaf K (Type w')))) :
    (sectionsFunctor K X).map (oneSheafHom A) p = A.one.eval X :=
  sectionsFunctor_map_constHom _ _ X p

/-! ### The five laws, as equations of morphisms of sheaves of sets -/

variable {Z : Sheaf K (Type w')}

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- Additivity of the multiplication in the first variable. -/
public lemma mulSheafHom_add_left (i j : ℤ) (x y : Z ⟶ pieceSheaf A i)
    (z : Z ⟶ pieceSheaf A j) :
    prod.lift (prod.lift x y ≫ moduleAddHom O (A.piece i)) z ≫ mulSheafHom A i j =
      prod.lift (prod.lift x z ≫ mulSheafHom A i j) (prod.lift y z ≫ mulSheafHom A i j) ≫
        moduleAddHom O (A.piece (i + j)) := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleAddHom]
  rw [sections_mulSheafHom, sections_mulSheafHom, sections_mulSheafHom]
  exact (congrArg (fun φ : (A.piece j).val.obj V →+ (A.piece (i + j)).val.obj V =>
      φ ((sectionsFunctor K V).map z s))
    (map_add ((A.mul i j).app V) ((sectionsFunctor K V).map x s)
      ((sectionsFunctor K V).map y s))).trans (AddMonoidHom.add_apply _ _ _)

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- Additivity of the multiplication in the second variable. -/
public lemma mulSheafHom_add_right (i j : ℤ) (x : Z ⟶ pieceSheaf A i)
    (y z : Z ⟶ pieceSheaf A j) :
    prod.lift x (prod.lift y z ≫ moduleAddHom O (A.piece j)) ≫ mulSheafHom A i j =
      prod.lift (prod.lift x y ≫ mulSheafHom A i j) (prod.lift x z ≫ mulSheafHom A i j) ≫
        moduleAddHom O (A.piece (i + j)) := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleAddHom]
  rw [sections_mulSheafHom, sections_mulSheafHom, sections_mulSheafHom]
  exact map_add ((A.mul i j).app V ((sectionsFunctor K V).map x s))
    ((sectionsFunctor K V).map y s) ((sectionsFunctor K V).map z s)

/-- Linearity of the multiplication in the first variable. -/
public lemma mulSheafHom_smul_left (i j : ℤ) (r : Z ⟶ Sheaf.ringSheaf O)
    (x : Z ⟶ pieceSheaf A i) (y : Z ⟶ pieceSheaf A j) :
    prod.lift (prod.lift r x ≫ moduleSMulHom O (A.piece i)) y ≫ mulSheafHom A i j =
      prod.lift r (prod.lift x y ≫ mulSheafHom A i j) ≫
        moduleSMulHom O (A.piece (i + j)) := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleSMulHom]
  rw [sections_mulSheafHom, sections_mulSheafHom]
  exact (A.mul i j).map_smul_left V ((sectionsFunctor K V).map r s)
    ((sectionsFunctor K V).map x s) ((sectionsFunctor K V).map y s)

/-- Linearity of the multiplication in the second variable. -/
public lemma mulSheafHom_smul_right (i j : ℤ) (r : Z ⟶ Sheaf.ringSheaf O)
    (x : Z ⟶ pieceSheaf A i) (y : Z ⟶ pieceSheaf A j) :
    prod.lift x (prod.lift r y ≫ moduleSMulHom O (A.piece j)) ≫ mulSheafHom A i j =
      prod.lift r (prod.lift x y ≫ mulSheafHom A i j) ≫
        moduleSMulHom O (A.piece (i + j)) := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleSMulHom]
  rw [sections_mulSheafHom, sections_mulSheafHom]
  exact (A.mul i j).map_smul_right V ((sectionsFunctor K V).map r s)
    ((sectionsFunctor K V).map x s) ((sectionsFunctor K V).map y s)

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- Associativity of the multiplication. -/
public lemma mulSheafHom_assoc (i j k : ℤ) (x : Z ⟶ pieceSheaf A i) (y : Z ⟶ pieceSheaf A j)
    (z : Z ⟶ pieceSheaf A k) :
    HEq (prod.lift (prod.lift x y ≫ mulSheafHom A i j) z ≫ mulSheafHom A (i + j) k)
      (prod.lift x (prod.lift y z ≫ mulSheafHom A j k) ≫ mulSheafHom A i (j + k)) := by
  refine heq_sheafHom_of_sections (congrArg (pieceSheaf A) (add_assoc i j k)) _ _
    fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply]
  rw [sections_mulSheafHom, sections_mulSheafHom, sections_mulSheafHom, sections_mulSheafHom]
  exact A.mul_assoc i j k V _ _ _

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- The unit is a left identity for the multiplication. -/
public lemma mulSheafHom_one_mul (i : ℤ) (x : Z ⟶ pieceSheaf A i) :
    HEq (prod.lift (terminal.from Z ≫ oneSheafHom A) x ≫ mulSheafHom A 0 i) x := by
  refine heq_sheafHom_of_sections (congrArg (pieceSheaf A) (zero_add i)) _ _ fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply]
  rw [sections_mulSheafHom, sections_oneSheafHom]
  exact A.one_mul i V _

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- The unit is a right identity for the multiplication. -/
public lemma mulSheafHom_mul_one (i : ℤ) (x : Z ⟶ pieceSheaf A i) :
    HEq (prod.lift x (terminal.from Z ≫ oneSheafHom A) ≫ mulSheafHom A i 0) x := by
  refine heq_sheafHom_of_sections (congrArg (pieceSheaf A) (add_zero i)) _ _ fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply]
  rw [sections_mulSheafHom, sections_oneSheafHom]
  exact A.mul_one i V _

/-! ### Homomorphisms, read on the underlying sheaves of sets -/

section OperationsMap

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})] {O : Sheaf K RingCat.{w'}}
  {A B : SheafOfModules.GradedAlgebra.{w', w'} O} (g : A ⟶ B) {Z : Sheaf K (Type w')}

/-- A homomorphism of sheaves of graded algebras commutes with the multiplication read on the
underlying sheaves of sets. -/
public lemma mulSheafHom_map (i j : ℤ) (x : Z ⟶ pieceSheaf A i) (y : Z ⟶ pieceSheaf A j) :
    (prod.lift x y ≫ mulSheafHom A i j) ≫
        (Sheaf.moduleSheafFunctor O).map (g.app (i + j)) =
      prod.lift (x ≫ (Sheaf.moduleSheafFunctor O).map (g.app i))
          (y ≫ (Sheaf.moduleSheafFunctor O).map (g.app j)) ≫ mulSheafHom B i j := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply]
  rw [sections_mulSheafHom, sections_mulSheafHom]
  exact g.map_mul i j V _ _

end OperationsMap

end Operations

/-! ### Transport along a finite-product-preserving functor of sheaves of sets -/

section Transport

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {O : Sheaf K RingCat.{w'}}

/-- Sections over an object of the source site of the transport of a sheaf of sets. A pair of
such sections for two sheaves is the same thing as one for their product, which is what lets
the operations of a graded algebra be transported. -/
public noncomputable def transportSections (X : Cᵒᵖ) : Sheaf K (Type w') ⥤ Type w :=
  Φ ⋙ sectionsFunctor J X

/-- The sections functor of a transport preserves finite products, being the composite of two
functors that do. -/
public noncomputable instance transportSections_preservesFiniteProducts (X : Cᵒᵖ) :
    PreservesFiniteProducts (transportSections J Φ X) := by
  delta transportSections
  infer_instance

/-- Restriction of sections of a transport, as a natural transformation. -/
public noncomputable def transportRestrict {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    transportSections J Φ X ⟶ transportSections J Φ Y :=
  Functor.whiskerLeft Φ (sectionsRestrict g)

variable (A : SheafOfModules.GradedAlgebra.{w', w'} O)

/-- A transported homogeneous piece, as a sheaf of modules over the transported sheaf of
rings. -/
public noncomputable abbrev transportPiece (n : ℤ) :
    SheafOfModules.{w} (pullbackRingSheaf J Φ O) :=
  pullbackModuleObj J Φ O (A.piece n)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The addition of sections of a transported sheaf of modules is the transport of the addition
of the original sheaf of modules. -/
public lemma transportSections_add (n : ℤ) (X : Cᵒᵖ)
    (x y : (transportPiece J Φ A n).val.obj X) :
    (transportSections J Φ X).map (moduleAddHom O (A.piece n)) (Functor.prodObjMk x y) =
      x + y :=
  ((moduleAddHom_pullback_apply J Φ O (A.piece n) X x y).symm).trans
    (sectionsFunctor_map_moduleAddHom (pullbackRingSheaf J Φ O)
      (pullbackModuleObj J Φ O (A.piece n)) X x y)

/-- The scalar multiplication of sections of a transported sheaf of modules is the transport of
the scalar multiplication of the original sheaf of modules. -/
public lemma transportSections_smul (n : ℤ) (X : Cᵒᵖ)
    (r : (pullbackRingSheaf J Φ O).obj.obj X)
    (x : (transportPiece J Φ A n).val.obj X) :
    (transportSections J Φ X).map (moduleSMulHom O (A.piece n)) (Functor.prodObjMk r x) =
      r • x :=
  ((moduleSMulHom_pullback_apply J Φ O (A.piece n) X r x).symm).trans
    (sectionsFunctor_map_moduleSMulHom (pullbackRingSheaf J Φ O)
      (pullbackModuleObj J Φ O (A.piece n)) X r x)

/-- Multiplication of sections of the transported homogeneous pieces. -/
public noncomputable def transportMulApp (i j : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (pieceSheaf A i))
    (y : (transportSections J Φ X).obj (pieceSheaf A j)) :
    (transportSections J Φ X).obj (pieceSheaf A (i + j)) :=
  (transportSections J Φ X).map (mulSheafHom A i j) (Functor.prodObjMk x y)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication is additive in the first variable. -/
public lemma transportMulApp_add_left (i j : ℤ) (X : Cᵒᵖ)
    (x y : (transportSections J Φ X).obj (pieceSheaf A i))
    (z : (transportSections J Φ X).obj (pieceSheaf A j)) :
    transportMulApp J Φ A i j X
        ((transportSections J Φ X).map (moduleAddHom O (A.piece i))
          (Functor.prodObjMk x y)) z =
      (transportSections J Φ X).map (moduleAddHom O (A.piece (i + j)))
        (Functor.prodObjMk (transportMulApp J Φ A i j X x z)
          (transportMulApp J Φ A i j X y z)) := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (mulSheafHom_add_left A i j (Z := (pieceSheaf A i ⨯ pieceSheaf A i) ⨯ pieceSheaf A j)
        (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) prod.snd)
      (Functor.prodObjMk (Functor.prodObjMk x y) z)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication is additive in the second variable. -/
public lemma transportMulApp_add_right (i j : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (pieceSheaf A i))
    (y z : (transportSections J Φ X).obj (pieceSheaf A j)) :
    transportMulApp J Φ A i j X x
        ((transportSections J Φ X).map (moduleAddHom O (A.piece j))
          (Functor.prodObjMk y z)) =
      (transportSections J Φ X).map (moduleAddHom O (A.piece (i + j)))
        (Functor.prodObjMk (transportMulApp J Φ A i j X x y)
          (transportMulApp J Φ A i j X x z)) := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (mulSheafHom_add_right A i j (Z := pieceSheaf A i ⨯ (pieceSheaf A j ⨯ pieceSheaf A j))
        prod.fst (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd))
      (Functor.prodObjMk x (Functor.prodObjMk y z))

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication is linear in the first variable. -/
public lemma transportMulApp_smul_left (i j : ℤ) (X : Cᵒᵖ)
    (r : (transportSections J Φ X).obj (Sheaf.ringSheaf O))
    (x : (transportSections J Φ X).obj (pieceSheaf A i))
    (y : (transportSections J Φ X).obj (pieceSheaf A j)) :
    transportMulApp J Φ A i j X
        ((transportSections J Φ X).map (moduleSMulHom O (A.piece i))
          (Functor.prodObjMk r x)) y =
      (transportSections J Φ X).map (moduleSMulHom O (A.piece (i + j)))
        (Functor.prodObjMk r (transportMulApp J Φ A i j X x y)) := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (mulSheafHom_smul_left A i j (Z := (Sheaf.ringSheaf O ⨯ pieceSheaf A i) ⨯ pieceSheaf A j)
        (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) prod.snd)
      (Functor.prodObjMk (Functor.prodObjMk r x) y)

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication is linear in the second variable. -/
public lemma transportMulApp_smul_right (i j : ℤ) (X : Cᵒᵖ)
    (r : (transportSections J Φ X).obj (Sheaf.ringSheaf O))
    (x : (transportSections J Φ X).obj (pieceSheaf A i))
    (y : (transportSections J Φ X).obj (pieceSheaf A j)) :
    transportMulApp J Φ A i j X x
        ((transportSections J Φ X).map (moduleSMulHom O (A.piece j))
          (Functor.prodObjMk r y)) =
      (transportSections J Φ X).map (moduleSMulHom O (A.piece (i + j)))
        (Functor.prodObjMk r (transportMulApp J Φ A i j X x y)) := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (mulSheafHom_smul_right A i j (Z := pieceSheaf A i ⨯ (Sheaf.ringSheaf O ⨯ pieceSheaf A j))
        (prod.snd ≫ prod.fst) prod.fst (prod.snd ≫ prod.snd))
      (Functor.prodObjMk x (Functor.prodObjMk r y))

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication commutes with restriction of sections. -/
public lemma transportMulApp_naturality (i j : ℤ) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (x : (transportSections J Φ X).obj (pieceSheaf A i))
    (y : (transportSections J Φ X).obj (pieceSheaf A j)) :
    (transportRestrict J Φ g).app (pieceSheaf A (i + j))
        (transportMulApp J Φ A i j X x y) =
      transportMulApp J Φ A i j Y ((transportRestrict J Φ g).app (pieceSheaf A i) x)
        ((transportRestrict J Φ g).app (pieceSheaf A j) y) := by
  rw [transportMulApp, transportMulApp,
    Functor.natTrans_app_map_apply (transportRestrict J Φ g) (mulSheafHom A i j),
    Functor.prodObjMk_naturality]

/-- The unit of the transported graded algebra, on sections over an object of the source
site. -/
public noncomputable def transportOneApp (X : Cᵒᵖ) :
    (transportSections J Φ X).obj (pieceSheaf A 0) :=
  (transportSections J Φ X).map (oneSheafHom A) default

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported unit commutes with restriction of sections. -/
public lemma transportOneApp_naturality {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    (transportRestrict J Φ g).app (pieceSheaf A 0) (transportOneApp J Φ A X) =
      transportOneApp J Φ A Y := by
  rw [transportOneApp, transportOneApp,
    Functor.natTrans_app_map_apply (transportRestrict J Φ g) (oneSheafHom A)]
  exact congrArg ((transportSections J Φ Y).map (oneSheafHom A)) (Subsingleton.elim _ _)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication is associative. -/
public lemma transportMulApp_assoc (i j k : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (pieceSheaf A i))
    (y : (transportSections J Φ X).obj (pieceSheaf A j))
    (z : (transportSections J Φ X).obj (pieceSheaf A k)) :
    HEq (transportMulApp J Φ A (i + j) k X (transportMulApp J Φ A i j X x y) z)
      (transportMulApp J Φ A i (j + k) X x (transportMulApp J Φ A j k X y z)) := by
  refine heq_of_map_eq_of_heq_hom (congrArg (pieceSheaf A) (add_assoc i j k))
    (mulSheafHom_assoc A i j k (Z := (pieceSheaf A i ⨯ pieceSheaf A j) ⨯ pieceSheaf A k)
      (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) prod.snd)
    (transportSections J Φ X) (Functor.prodObjMk (Functor.prodObjMk x y) z) ?_ ?_ <;>
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportMulApp]

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported unit is a left identity for the transported multiplication. -/
public lemma transportMulApp_one_mul (i : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (pieceSheaf A i)) :
    HEq (transportMulApp J Φ A 0 i X (transportOneApp J Φ A X) x) x := by
  refine heq_of_map_eq_of_heq_hom (congrArg (pieceSheaf A) (zero_add i))
    (mulSheafHom_one_mul A i (Z := pieceSheaf A i) (𝟙 (pieceSheaf A i)))
    (transportSections J Φ X) x ?_ ((transportSections J Φ X).map_id_apply _ x)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_terminalFrom_apply,
    Functor.map_id_apply, transportMulApp, transportOneApp]

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported unit is a right identity for the transported multiplication. -/
public lemma transportMulApp_mul_one (i : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (pieceSheaf A i)) :
    HEq (transportMulApp J Φ A i 0 X x (transportOneApp J Φ A X)) x := by
  refine heq_of_map_eq_of_heq_hom (congrArg (pieceSheaf A) (add_zero i))
    (mulSheafHom_mul_one A i (Z := pieceSheaf A i) (𝟙 (pieceSheaf A i)))
    (transportSections J Φ X) x ?_ ((transportSections J Φ X).map_id_apply _ x)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_terminalFrom_apply,
    Functor.map_id_apply, transportMulApp, transportOneApp]

/-! ### The transported graded algebra -/

/-- The transported multiplication in two fixed degrees, as a bilinear map of the transported
homogeneous pieces. -/
public noncomputable def transportMul (i j : ℤ) :
    SheafOfModules.BilinearMap (transportPiece J Φ A i) (transportPiece J Φ A j)
      (transportPiece J Φ A (i + j)) where
  app X := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => transportMulApp J Φ A i j X x y)
      (fun y z => ((congrArg (fun u => transportMulApp J Φ A i j X x u)
            (transportSections_add J Φ A j X y z).symm).trans
          (transportMulApp_add_right J Φ A i j X x y z)).trans
        (transportSections_add J Φ A (i + j) X _ _)))
    (fun x y => AddMonoidHom.ext fun z =>
      ((congrArg (fun u => transportMulApp J Φ A i j X u z)
            (transportSections_add J Φ A i X x y).symm).trans
          (transportMulApp_add_left J Φ A i j X x y z)).trans
        (transportSections_add J Φ A (i + j) X _ _))
  map_smul_left X r x y :=
    ((congrArg (fun u => transportMulApp J Φ A i j X u y)
          (transportSections_smul J Φ A i X r x).symm).trans
        (transportMulApp_smul_left J Φ A i j X r x y)).trans
      (transportSections_smul J Φ A (i + j) X r _)
  map_smul_right X r x y :=
    ((congrArg (fun u => transportMulApp J Φ A i j X x u)
          (transportSections_smul J Φ A j X r y).symm).trans
        (transportMulApp_smul_right J Φ A i j X r x y)).trans
      (transportSections_smul J Φ A (i + j) X r _)
  naturality g x y := transportMulApp_naturality J Φ A i j g x y

/-- The unit of the transported graded algebra. -/
public noncomputable def transportOne : (transportPiece J Φ A 0).sections :=
  PresheafOfModules.sectionsMk (fun X => transportOneApp J Φ A X)
    (fun {_ _} g => transportOneApp_naturality J Φ A g)

/-- **Transport of a sheaf of graded algebras.** The homogeneous pieces are the transports of
the original homogeneous pieces, and the multiplication and unit are the transports of the
original ones. -/
public noncomputable def transportGradedAlgebra :
    SheafOfModules.GradedAlgebra.{w, w} (pullbackRingSheaf J Φ O) where
  piece n := transportPiece J Φ A n
  mul i j := transportMul J Φ A i j
  one := transportOne J Φ A
  mul_assoc i j k X x y z := transportMulApp_assoc J Φ A i j k X x y z
  one_mul i X x := transportMulApp_one_mul J Φ A i X x
  mul_one i X x := transportMulApp_mul_one J Φ A i X x

/-- The homogeneous pieces of the transported graded algebra are the transports of the original
homogeneous pieces. -/
public theorem transportGradedAlgebra_piece (n : ℤ) :
    (transportGradedAlgebra J Φ A).piece n = pullbackModuleObj J Φ O (A.piece n) := rfl

end Transport

/-! ### The transport as a functor of sheaves of graded algebras -/

section TransportFunctor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {O : Sheaf K RingCat.{w'}} {A B : SheafOfModules.GradedAlgebra.{w', w'} O} (g : A ⟶ B)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported degreewise morphisms preserve the transported multiplication. -/
public lemma transportMulApp_map (i j : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (pieceSheaf A i))
    (y : (transportSections J Φ X).obj (pieceSheaf A j)) :
    (transportSections J Φ X).map ((Sheaf.moduleSheafFunctor O).map (g.app (i + j)))
        (transportMulApp J Φ A i j X x y) =
      transportMulApp J Φ B i j X
        ((transportSections J Φ X).map ((Sheaf.moduleSheafFunctor O).map (g.app i)) x)
        ((transportSections J Φ X).map ((Sheaf.moduleSheafFunctor O).map (g.app j)) y) := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (mulSheafHom_map g i j (Z := pieceSheaf A i ⨯ pieceSheaf A j) prod.fst prod.snd)
      (Functor.prodObjMk x y)

/-- The transport of a homomorphism of sheaves of graded algebras. -/
public noncomputable def transportHom :
    transportGradedAlgebra J Φ A ⟶ transportGradedAlgebra J Φ B where
  app n := (pullbackModuleFunctor J Φ O).map (g.app n)
  map_mul i j X x y := transportMulApp_map J Φ g i j X x y

/-- **Transport of sheaves of graded algebras, as a functor.** -/
public noncomputable def transportGradedAlgebraFunctor :
    SheafOfModules.GradedAlgebra.{w', w'} O ⥤
      SheafOfModules.GradedAlgebra.{w, w} (pullbackRingSheaf J Φ O) where
  obj A := transportGradedAlgebra J Φ A
  map g := transportHom J Φ g
  map_id A := by
    refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    exact (pullbackModuleFunctor J Φ O).map_id (A.piece n)
  map_comp g h := by
    refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    exact (pullbackModuleFunctor J Φ O).map_comp (g.app n) (h.app n)

/-- The functor's value on an object is the transported graded algebra. -/
public theorem transportGradedAlgebraFunctor_obj
    (A : SheafOfModules.GradedAlgebra.{w', w'} O) :
    (transportGradedAlgebraFunctor J Φ (O := O)).obj A = transportGradedAlgebra J Φ A := rfl

/-- The functor's degreewise components are the transports of the degreewise components. -/
public theorem transportGradedAlgebraFunctor_map_app (n : ℤ) :
    ((transportGradedAlgebraFunctor J Φ (O := O)).map g).app n =
      (pullbackModuleFunctor J Φ O).map (g.app n) := rfl

end TransportFunctor

/-! ### The inverse image along a morphism of topoi -/

section InverseImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'}) (A : SheafOfModules.GradedAlgebra.{w', w'} O)

/-- **The inverse image of a sheaf of graded algebras** along a morphism of topoi, a sheaf of
graded `f⁻¹O`-algebras. Its homogeneous pieces are the inverse images of the homogeneous pieces
of the original graded algebra, and its multiplication and unit are the inverse images of the
original ones. This is part (2) of Stacks 0FQX at the level of the underlying topoi, before
extension of scalars along the structure map of a morphism of ringed topoi. -/
public noncomputable def inverseImageGradedAlgebra :
    SheafOfModules.GradedAlgebra.{w, w} (inverseImageRingSheaf f O) :=
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  transportGradedAlgebra J f.inverseImage A

/-- The homogeneous pieces of the inverse image of a sheaf of graded algebras are the inverse
images of the original homogeneous pieces. -/
public theorem inverseImageGradedAlgebra_piece (n : ℤ) :
    (inverseImageGradedAlgebra f O A).piece n = (inverseImageModules f O).obj (A.piece n) :=
  rfl

/-- **The inverse image of sheaves of graded algebras, as a functor.** Its degreewise components
are the inverse images of the degreewise components. -/
public noncomputable def inverseImageGradedAlgebraFunctor :
    SheafOfModules.GradedAlgebra.{w', w'} O ⥤
      SheafOfModules.GradedAlgebra.{w, w} (inverseImageRingSheaf f O) :=
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  transportGradedAlgebraFunctor J f.inverseImage

/-- The inverse-image functor of sheaves of graded algebras acts on objects by
`inverseImageGradedAlgebra`. -/
public theorem inverseImageGradedAlgebraFunctor_obj :
    (inverseImageGradedAlgebraFunctor f O).obj A = inverseImageGradedAlgebra f O A := rfl

end InverseImage

end Stacks.Sheaves.GradedAlgebraInverseImage
