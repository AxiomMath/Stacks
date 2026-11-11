module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Inverse image of a sheaf of graded modules along a morphism of topoi

Let `f` be a morphism of topoi, `O` a sheaf of rings on its target, `B` a sheaf of graded
`O`-algebras and `N` a right graded `B`-module. The inverse image `f⁻¹N` is the right graded
`f⁻¹B`-module whose degree-`n` piece is the inverse image `f⁻¹N^n`, with multiplication

`f⁻¹ν_{n,m} : f⁻¹N^n × f⁻¹B^m ⟶ f⁻¹N^{n+m}`,

the inverse image of the multiplication `ν_{n,m} : N^n × B^m ⟶ N^{n+m}` of `N`, which makes
sense because `f⁻¹` commutes with products. The construction is functorial in `N`, both on
homomorphisms of right graded modules and on homomorphisms homogeneous of degree `n`.

## Main definitions

* `smulSheafHom` reads the multiplication of a right graded module as a morphism of the
  underlying sheaves of sets, out of a binary product.
* `transportGradedModule` transports a right graded `B`-module along a finite-product-preserving
  functor of sheaves of sets to a right graded module over the transport of `B`;
  `transportGradedModuleMap`, `transportGradedModuleFunctor` and
  `transportGradedHomOfDegree` are its action on homomorphisms, the functor it defines, and its
  action on homomorphisms homogeneous of degree `n`.
* `inverseImageGradedModule`, `inverseImageGradedModuleFunctor` and
  `inverseImageGradedHomOfDegree` are the inverse image of a right graded module along a
  morphism of topoi, the functor `f⁻¹ : Mod(B) ⥤ Mod(f⁻¹B)` and its action on homomorphisms
  homogeneous of degree `n`.

## Main results

* `inverseImageGradedModule_piece`: the homogeneous pieces of `f⁻¹N` are the inverse images of
  the homogeneous pieces of `N`, on the nose.

## Implementation notes

This is the module counterpart of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedAlgebraInverseImage.lean`, and it is proved
the same way: sections of an inverse image cannot be computed from sections of the original
sheaf, so every operation of `f⁻¹N` is the image under `Φ ⋙ (sections over X)` of a morphism of
sheaves of sets on the target site, and every law is the image of an equation between such
morphisms, proved on sections of the target site where the laws of `N` are available.

## References

* [Stacks Project, Tag 0FR7](https://stacks.math.columbia.edu/tag/0FR7)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.GradedAlgebraInverseImage

namespace Stacks.Sheaves.GradedModuleInverseImage

universe w w' v u v' u'

/-! ### The multiplication of a graded module as a morphism of sheaves of sets -/

section Operations

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{w'})] [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  {O : Sheaf K RingCat.{w'}} {B : SheafOfModules.GradedAlgebra.{w', w'} O}

/-- The underlying sheaf of sets of a homogeneous piece of a right graded module. -/
public noncomputable abbrev modulePieceSheaf (N : SheafOfModules.GradedModule.{w', w', w'} B)
    (n : ℤ) : Sheaf K (Type w') :=
  moduleSheaf O (N.piece n)

variable (N : SheafOfModules.GradedModule.{w', w', w'} B)

/-- The multiplication of a right graded module, as a morphism out of the product of the
underlying sheaves of sets. -/
public noncomputable def smulSheafHom (n i : ℤ) :
    modulePieceSheaf N n ⨯ pieceSheaf B i ⟶ modulePieceSheaf N (n + i) :=
  binaryOpHom (fun X x y => N.smul n i X x y) (fun g x y => N.smul_naturality n i g x y)

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- On sections, `smulSheafHom` is the multiplication of the graded module. -/
public lemma sections_smulSheafHom (n i : ℤ) (X : Dᵒᵖ)
    (x : (sectionsFunctor K X).obj (modulePieceSheaf N n))
    (y : (sectionsFunctor K X).obj (pieceSheaf B i)) :
    (sectionsFunctor K X).map (smulSheafHom N n i) (Functor.prodObjMk x y) =
      N.smul n i X x y :=
  sectionsFunctor_map_binaryOpHom _ _ X x y

variable {Z : Sheaf K (Type w')}

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- Additivity of the multiplication in the module variable. -/
public lemma smulSheafHom_add_left (n i : ℤ) (x y : Z ⟶ modulePieceSheaf N n)
    (z : Z ⟶ pieceSheaf B i) :
    prod.lift (prod.lift x y ≫ moduleAddHom O (N.piece n)) z ≫ smulSheafHom N n i =
      prod.lift (prod.lift x z ≫ smulSheafHom N n i) (prod.lift y z ≫ smulSheafHom N n i) ≫
        moduleAddHom O (N.piece (n + i)) := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleAddHom]
  rw [sections_smulSheafHom, sections_smulSheafHom, sections_smulSheafHom]
  exact (congrArg (fun φ : (B.piece i).val.obj V →+ (N.piece (n + i)).val.obj V =>
      φ ((sectionsFunctor K V).map z s))
    (map_add (N.smul n i V) ((sectionsFunctor K V).map x s)
      ((sectionsFunctor K V).map y s))).trans (AddMonoidHom.add_apply _ _ _)

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- Additivity of the multiplication in the algebra variable. -/
public lemma smulSheafHom_add_right (n i : ℤ) (x : Z ⟶ modulePieceSheaf N n)
    (y z : Z ⟶ pieceSheaf B i) :
    prod.lift x (prod.lift y z ≫ moduleAddHom O (B.piece i)) ≫ smulSheafHom N n i =
      prod.lift (prod.lift x y ≫ smulSheafHom N n i) (prod.lift x z ≫ smulSheafHom N n i) ≫
        moduleAddHom O (N.piece (n + i)) := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleAddHom]
  rw [sections_smulSheafHom, sections_smulSheafHom, sections_smulSheafHom]
  exact map_add (N.smul n i V ((sectionsFunctor K V).map x s))
    ((sectionsFunctor K V).map y s) ((sectionsFunctor K V).map z s)

/-- Linearity of the multiplication in the module variable. -/
public lemma smulSheafHom_smul_left (n i : ℤ) (r : Z ⟶ Sheaf.ringSheaf O)
    (x : Z ⟶ modulePieceSheaf N n) (y : Z ⟶ pieceSheaf B i) :
    prod.lift (prod.lift r x ≫ moduleSMulHom O (N.piece n)) y ≫ smulSheafHom N n i =
      prod.lift r (prod.lift x y ≫ smulSheafHom N n i) ≫
        moduleSMulHom O (N.piece (n + i)) := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleSMulHom]
  rw [sections_smulSheafHom, sections_smulSheafHom]
  exact N.smul_smul_left n i V ((sectionsFunctor K V).map r s)
    ((sectionsFunctor K V).map x s) ((sectionsFunctor K V).map y s)

/-- Linearity of the multiplication in the algebra variable. -/
public lemma smulSheafHom_smul_right (n i : ℤ) (r : Z ⟶ Sheaf.ringSheaf O)
    (x : Z ⟶ modulePieceSheaf N n) (y : Z ⟶ pieceSheaf B i) :
    prod.lift x (prod.lift r y ≫ moduleSMulHom O (B.piece i)) ≫ smulSheafHom N n i =
      prod.lift r (prod.lift x y ≫ smulSheafHom N n i) ≫
        moduleSMulHom O (N.piece (n + i)) := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleSMulHom]
  rw [sections_smulSheafHom, sections_smulSheafHom]
  exact N.smul_smul_right n i V ((sectionsFunctor K V).map r s)
    ((sectionsFunctor K V).map x s) ((sectionsFunctor K V).map y s)

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- Associativity of the multiplication with the multiplication of the algebra. -/
public lemma smulSheafHom_assoc (n i j : ℤ) (x : Z ⟶ modulePieceSheaf N n)
    (y : Z ⟶ pieceSheaf B i) (z : Z ⟶ pieceSheaf B j) :
    HEq (prod.lift (prod.lift x y ≫ smulSheafHom N n i) z ≫ smulSheafHom N (n + i) j)
      (prod.lift x (prod.lift y z ≫ mulSheafHom B i j) ≫ smulSheafHom N n (i + j)) := by
  refine heq_sheafHom_of_sections (congrArg (modulePieceSheaf N) (add_assoc n i j)) _ _
    fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply]
  rw [sections_mulSheafHom]
  exact (heq_of_eq (sections_smulSheafHom N (n + i) j V _ _)).trans
    (((heq_of_eq (congrArg (fun t => N.smul (n + i) j V t _)
      (sections_smulSheafHom N n i V _ _))).trans (N.smul_mul n i j V _ _ _)).trans
      (heq_of_eq (sections_smulSheafHom N n (i + j) V _ _).symm))

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- The unit of the algebra acts as the identity. -/
public lemma smulSheafHom_one (n : ℤ) (x : Z ⟶ modulePieceSheaf N n) :
    HEq (prod.lift x (terminal.from Z ≫ oneSheafHom B) ≫ smulSheafHom N n 0) x := by
  refine heq_sheafHom_of_sections (congrArg (modulePieceSheaf N) (add_zero n)) _ _
    fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply]
  rw [sections_smulSheafHom, sections_oneSheafHom]
  exact N.smul_one n V _

end Operations

/-! ### Homomorphisms, read on the underlying sheaves of sets -/

section OperationsMap

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})] {O : Sheaf K RingCat.{w'}}
  {B : SheafOfModules.GradedAlgebra.{w', w'} O} {Z : Sheaf K (Type w')}

/-- A homomorphism of right graded modules commutes with the multiplication read on the
underlying sheaves of sets. -/
public lemma smulSheafHom_map {N N' : SheafOfModules.GradedModule.{w', w', w'} B} (g : N ⟶ N')
    (n i : ℤ) (x : Z ⟶ modulePieceSheaf N n) (y : Z ⟶ pieceSheaf B i) :
    (prod.lift x y ≫ smulSheafHom N n i) ≫ (Sheaf.moduleSheafFunctor O).map (g.app (n + i)) =
      prod.lift (x ≫ (Sheaf.moduleSheafFunctor O).map (g.app n)) y ≫ smulSheafHom N' n i := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply]
  rw [sections_smulSheafHom, sections_smulSheafHom]
  exact g.map_smul n i V _ _

/-- A homomorphism of right graded modules homogeneous of degree `d` commutes with the
multiplication read on the underlying sheaves of sets. -/
public lemma smulSheafHom_mapOfDegree {N N' : SheafOfModules.GradedModule.{w', w', w'} B}
    {d : ℤ} (g : SheafOfModules.GradedHomOfDegree N N' d) (i j : ℤ) (hij : i + d = j) (p : ℤ)
    (x : Z ⟶ modulePieceSheaf N i) (y : Z ⟶ pieceSheaf B p) :
    (prod.lift x y ≫ smulSheafHom N i p) ≫
        (Sheaf.moduleSheafFunctor O).map (g.app (i + p) (j + p) (by omega)) =
      prod.lift (x ≫ (Sheaf.moduleSheafFunctor O).map (g.app i j hij)) y ≫
        smulSheafHom N' j p := by
  refine hom_ext_sections fun V s => ?_
  simp only [Functor.map_comp_apply, Functor.map_lift_apply]
  rw [sections_smulSheafHom, sections_smulSheafHom]
  exact g.map_mul i j hij p V _ _

end OperationsMap

/-! ### Transport along a finite-product-preserving functor of sheaves of sets -/

section Transport

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {O : Sheaf K RingCat.{w'}} {B : SheafOfModules.GradedAlgebra.{w', w'} O}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The addition of sections of a transported sheaf of modules is the transport of the addition
of the original sheaf of modules. -/
public lemma transportModuleSections_add (G : SheafOfModules.{w'} O) (X : Cᵒᵖ)
    (x y : (pullbackModuleObj J Φ O G).val.obj X) :
    (transportSections J Φ X).map (moduleAddHom O G) (Functor.prodObjMk x y) = x + y :=
  ((moduleAddHom_pullback_apply J Φ O G X x y).symm).trans
    (sectionsFunctor_map_moduleAddHom (pullbackRingSheaf J Φ O)
      (pullbackModuleObj J Φ O G) X x y)

/-- The scalar multiplication of sections of a transported sheaf of modules is the transport of
the scalar multiplication of the original sheaf of modules. -/
public lemma transportModuleSections_smul (G : SheafOfModules.{w'} O) (X : Cᵒᵖ)
    (r : (pullbackRingSheaf J Φ O).obj.obj X) (x : (pullbackModuleObj J Φ O G).val.obj X) :
    (transportSections J Φ X).map (moduleSMulHom O G) (Functor.prodObjMk r x) = r • x :=
  ((moduleSMulHom_pullback_apply J Φ O G X r x).symm).trans
    (sectionsFunctor_map_moduleSMulHom (pullbackRingSheaf J Φ O)
      (pullbackModuleObj J Φ O G) X r x)

variable (N : SheafOfModules.GradedModule.{w', w', w'} B)

/-- Multiplication of a section of a transported homogeneous piece of the module by a section of
a transported homogeneous piece of the algebra. -/
public noncomputable def transportSMulApp (n i : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (modulePieceSheaf N n))
    (y : (transportSections J Φ X).obj (pieceSheaf B i)) :
    (transportSections J Φ X).obj (modulePieceSheaf N (n + i)) :=
  (transportSections J Φ X).map (smulSheafHom N n i) (Functor.prodObjMk x y)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication is additive in the module variable. -/
public lemma transportSMulApp_add_left (n i : ℤ) (X : Cᵒᵖ)
    (x y : (transportSections J Φ X).obj (modulePieceSheaf N n))
    (z : (transportSections J Φ X).obj (pieceSheaf B i)) :
    transportSMulApp J Φ N n i X
        ((transportSections J Φ X).map (moduleAddHom O (N.piece n))
          (Functor.prodObjMk x y)) z =
      (transportSections J Φ X).map (moduleAddHom O (N.piece (n + i)))
        (Functor.prodObjMk (transportSMulApp J Φ N n i X x z)
          (transportSMulApp J Φ N n i X y z)) := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportSMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (smulSheafHom_add_left N n i
        (Z := (modulePieceSheaf N n ⨯ modulePieceSheaf N n) ⨯ pieceSheaf B i)
        (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) prod.snd)
      (Functor.prodObjMk (Functor.prodObjMk x y) z)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication is additive in the algebra variable. -/
public lemma transportSMulApp_add_right (n i : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (modulePieceSheaf N n))
    (y z : (transportSections J Φ X).obj (pieceSheaf B i)) :
    transportSMulApp J Φ N n i X x
        ((transportSections J Φ X).map (moduleAddHom O (B.piece i))
          (Functor.prodObjMk y z)) =
      (transportSections J Φ X).map (moduleAddHom O (N.piece (n + i)))
        (Functor.prodObjMk (transportSMulApp J Φ N n i X x y)
          (transportSMulApp J Φ N n i X x z)) := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportSMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (smulSheafHom_add_right N n i
        (Z := modulePieceSheaf N n ⨯ (pieceSheaf B i ⨯ pieceSheaf B i))
        prod.fst (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd))
      (Functor.prodObjMk x (Functor.prodObjMk y z))

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication is linear in the module variable. -/
public lemma transportSMulApp_smul_left (n i : ℤ) (X : Cᵒᵖ)
    (r : (transportSections J Φ X).obj (Sheaf.ringSheaf O))
    (x : (transportSections J Φ X).obj (modulePieceSheaf N n))
    (y : (transportSections J Φ X).obj (pieceSheaf B i)) :
    transportSMulApp J Φ N n i X
        ((transportSections J Φ X).map (moduleSMulHom O (N.piece n))
          (Functor.prodObjMk r x)) y =
      (transportSections J Φ X).map (moduleSMulHom O (N.piece (n + i)))
        (Functor.prodObjMk r (transportSMulApp J Φ N n i X x y)) := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportSMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (smulSheafHom_smul_left N n i
        (Z := (Sheaf.ringSheaf O ⨯ modulePieceSheaf N n) ⨯ pieceSheaf B i)
        (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) prod.snd)
      (Functor.prodObjMk (Functor.prodObjMk r x) y)

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication is linear in the algebra variable. -/
public lemma transportSMulApp_smul_right (n i : ℤ) (X : Cᵒᵖ)
    (r : (transportSections J Φ X).obj (Sheaf.ringSheaf O))
    (x : (transportSections J Φ X).obj (modulePieceSheaf N n))
    (y : (transportSections J Φ X).obj (pieceSheaf B i)) :
    transportSMulApp J Φ N n i X x
        ((transportSections J Φ X).map (moduleSMulHom O (B.piece i))
          (Functor.prodObjMk r y)) =
      (transportSections J Φ X).map (moduleSMulHom O (N.piece (n + i)))
        (Functor.prodObjMk r (transportSMulApp J Φ N n i X x y)) := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportSMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (smulSheafHom_smul_right N n i
        (Z := modulePieceSheaf N n ⨯ (Sheaf.ringSheaf O ⨯ pieceSheaf B i))
        (prod.snd ≫ prod.fst) prod.fst (prod.snd ≫ prod.snd))
      (Functor.prodObjMk x (Functor.prodObjMk r y))

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication commutes with restriction of sections. -/
public lemma transportSMulApp_naturality (n i : ℤ) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (x : (transportSections J Φ X).obj (modulePieceSheaf N n))
    (y : (transportSections J Φ X).obj (pieceSheaf B i)) :
    (transportRestrict J Φ g).app (modulePieceSheaf N (n + i))
        (transportSMulApp J Φ N n i X x y) =
      transportSMulApp J Φ N n i Y ((transportRestrict J Φ g).app (modulePieceSheaf N n) x)
        ((transportRestrict J Φ g).app (pieceSheaf B i) y) := by
  rw [transportSMulApp, transportSMulApp,
    Functor.natTrans_app_map_apply (transportRestrict J Φ g) (smulSheafHom N n i),
    Functor.prodObjMk_naturality]

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported multiplication is associative with the transported multiplication of the
algebra. -/
public lemma transportSMulApp_assoc (n i j : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (modulePieceSheaf N n))
    (y : (transportSections J Φ X).obj (pieceSheaf B i))
    (z : (transportSections J Φ X).obj (pieceSheaf B j)) :
    HEq (transportSMulApp J Φ N (n + i) j X (transportSMulApp J Φ N n i X x y) z)
      (transportSMulApp J Φ N n (i + j) X x (transportMulApp J Φ B i j X y z)) := by
  have h := heq_map_of_heq_hom (congrArg (modulePieceSheaf N) (add_assoc n i j))
    (smulSheafHom_assoc N n i j
      (Z := (modulePieceSheaf N n ⨯ pieceSheaf B i) ⨯ pieceSheaf B j)
      (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) prod.snd)
    (transportSections J Φ X) (Functor.prodObjMk (Functor.prodObjMk x y) z)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk] at h
  exact h

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported unit of the algebra acts as the identity. -/
public lemma transportSMulApp_one (n : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (modulePieceSheaf N n)) :
    HEq (transportSMulApp J Φ N n 0 X x (transportOneApp J Φ B X)) x := by
  have h := heq_map_of_heq_hom (congrArg (modulePieceSheaf N) (add_zero n))
    (smulSheafHom_one N n (Z := modulePieceSheaf N n) (𝟙 (modulePieceSheaf N n)))
    (transportSections J Φ X) x
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_terminalFrom_apply,
    Functor.map_id_apply] at h
  exact h

/-- **Transport of a right graded module.** The homogeneous pieces are the transports of the
original homogeneous pieces, and the multiplication is the transport of the original one; the
result is a right graded module over the transported graded algebra. -/
public noncomputable def transportGradedModule :
    SheafOfModules.GradedModule.{w, w, w} (transportGradedAlgebra J Φ B) where
  piece n := pullbackModuleObj J Φ O (N.piece n)
  smul n i X := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => transportSMulApp J Φ N n i X x y)
      (fun y z => ((congrArg (fun t => transportSMulApp J Φ N n i X x t)
            (transportModuleSections_add J Φ (B.piece i) X y z).symm).trans
          (transportSMulApp_add_right J Φ N n i X x y z)).trans
        (transportModuleSections_add J Φ (N.piece (n + i)) X _ _)))
    (fun x y => AddMonoidHom.ext fun z =>
      ((congrArg (fun t => transportSMulApp J Φ N n i X t z)
            (transportModuleSections_add J Φ (N.piece n) X x y).symm).trans
          (transportSMulApp_add_left J Φ N n i X x y z)).trans
        (transportModuleSections_add J Φ (N.piece (n + i)) X _ _))
  smul_smul_left n i X r x y :=
    ((congrArg (fun t => transportSMulApp J Φ N n i X t y)
          (transportModuleSections_smul J Φ (N.piece n) X r x).symm).trans
        (transportSMulApp_smul_left J Φ N n i X r x y)).trans
      (transportModuleSections_smul J Φ (N.piece (n + i)) X r _)
  smul_smul_right n i X r x y :=
    ((congrArg (fun t => transportSMulApp J Φ N n i X x t)
          (transportModuleSections_smul J Φ (B.piece i) X r y).symm).trans
        (transportSMulApp_smul_right J Φ N n i X r x y)).trans
      (transportModuleSections_smul J Φ (N.piece (n + i)) X r _)
  smul_naturality n i _ _ g x y := transportSMulApp_naturality J Φ N n i g x y
  smul_mul n i j X x y z := transportSMulApp_assoc J Φ N n i j X x y z
  smul_one n X x := transportSMulApp_one J Φ N n X x

/-- The homogeneous pieces of the transported graded module are the transports of the original
homogeneous pieces. -/
public theorem transportGradedModule_piece (n : ℤ) :
    (transportGradedModule J Φ N).piece n = pullbackModuleObj J Φ O (N.piece n) := rfl

/-- The multiplication of the transported graded module is the transport of the original
multiplication. -/
public theorem transportGradedModule_smul (n i : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (modulePieceSheaf N n))
    (y : (transportSections J Φ X).obj (pieceSheaf B i)) :
    (transportGradedModule J Φ N).smul n i X x y =
      (transportSections J Φ X).map (smulSheafHom N n i) (Functor.prodObjMk x y) := rfl

end Transport

/-! ### The transport on homomorphisms -/

section TransportFunctor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {O : Sheaf K RingCat.{w'}} {B : SheafOfModules.GradedAlgebra.{w', w'} O}
  {N N' : SheafOfModules.GradedModule.{w', w', w'} B}

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported degreewise morphisms preserve the transported multiplication. -/
public lemma transportSMulApp_map (g : N ⟶ N') (n i : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (modulePieceSheaf N n))
    (y : (transportSections J Φ X).obj (pieceSheaf B i)) :
    (transportSections J Φ X).map ((Sheaf.moduleSheafFunctor O).map (g.app (n + i)))
        (transportSMulApp J Φ N n i X x y) =
      transportSMulApp J Φ N' n i X
        ((transportSections J Φ X).map ((Sheaf.moduleSheafFunctor O).map (g.app n)) x) y := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportSMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (smulSheafHom_map g n i (Z := modulePieceSheaf N n ⨯ pieceSheaf B i) prod.fst prod.snd)
      (Functor.prodObjMk x y)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transported components of a homogeneous homomorphism preserve the transported
multiplication. -/
public lemma transportSMulApp_mapOfDegree {d : ℤ} (g : SheafOfModules.GradedHomOfDegree N N' d)
    (i j : ℤ) (hij : i + d = j) (p : ℤ) (X : Cᵒᵖ)
    (x : (transportSections J Φ X).obj (modulePieceSheaf N i))
    (y : (transportSections J Φ X).obj (pieceSheaf B p)) :
    (transportSections J Φ X).map
        ((Sheaf.moduleSheafFunctor O).map (g.app (i + p) (j + p) (by omega)))
        (transportSMulApp J Φ N i p X x y) =
      transportSMulApp J Φ N' j p X
        ((transportSections J Φ X).map ((Sheaf.moduleSheafFunctor O).map (g.app i j hij)) x)
        y := by
  simpa only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk, transportSMulApp] using
    sheafHom_map_apply_congr (P := transportSections J Φ X)
      (smulSheafHom_mapOfDegree g i j hij p (Z := modulePieceSheaf N i ⨯ pieceSheaf B p)
        prod.fst prod.snd)
      (Functor.prodObjMk x y)

/-- The transport of a homomorphism of right graded modules: its degreewise components are the
transports of the original degreewise components. -/
public noncomputable def transportGradedModuleMap (g : N ⟶ N') :
    transportGradedModule J Φ N ⟶ transportGradedModule J Φ N' where
  app n := (pullbackModuleFunctor J Φ O).map (g.app n)
  map_smul n i X x y := transportSMulApp_map J Φ g n i X x y

/-- The degreewise components of the transport of a homomorphism are the transports of its
degreewise components. -/
public theorem transportGradedModuleMap_app (g : N ⟶ N') (n : ℤ) :
    (transportGradedModuleMap J Φ g).app n = (pullbackModuleFunctor J Φ O).map (g.app n) := rfl

/-- **Transport of right graded modules, as a functor.** -/
public noncomputable def transportGradedModuleFunctor :
    SheafOfModules.GradedModule.{w', w', w'} B ⥤
      SheafOfModules.GradedModule.{w, w, w} (transportGradedAlgebra J Φ B) where
  obj N := transportGradedModule J Φ N
  map g := transportGradedModuleMap J Φ g
  map_id N := SheafOfModules.GradedModule.Hom.ext fun n =>
    (pullbackModuleFunctor J Φ O).map_id (N.piece n)
  map_comp g h := SheafOfModules.GradedModule.Hom.ext fun n =>
    (pullbackModuleFunctor J Φ O).map_comp (g.app n) (h.app n)

/-- The transport of a homomorphism of right graded modules homogeneous of degree `d`: its
components are the transports of the original components, and it is again homogeneous of
degree `d`. -/
public noncomputable def transportGradedHomOfDegree {d : ℤ}
    (g : SheafOfModules.GradedHomOfDegree N N' d) :
    SheafOfModules.GradedHomOfDegree (transportGradedModule J Φ N)
      (transportGradedModule J Φ N') d where
  app i j hij := (pullbackModuleFunctor J Φ O).map (g.app i j hij)
  map_mul i j hij p X x b := transportSMulApp_mapOfDegree J Φ g i j hij p X x b

/-- The components of the transport of a homogeneous homomorphism are the transports of its
components. -/
public theorem transportGradedHomOfDegree_app {d : ℤ}
    (g : SheafOfModules.GradedHomOfDegree N N' d) (i j : ℤ) (hij : i + d = j) :
    (transportGradedHomOfDegree J Φ g).app i j hij =
      (pullbackModuleFunctor J Φ O).map (g.app i j hij) := rfl

end TransportFunctor

/-! ### The inverse image along a morphism of topoi -/

section InverseImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'}) {B : SheafOfModules.GradedAlgebra.{w', w'} O}

/-- **The inverse image `f⁻¹N` of a right graded `B`-module** along a morphism of topoi, a right
graded `f⁻¹B`-module. Its degree-`n` piece is the inverse image `f⁻¹N^n` of the degree-`n` piece
of `N`, and its multiplication `f⁻¹N^n × f⁻¹B^m ⟶ f⁻¹N^{n+m}` is the inverse image `f⁻¹ν_{n,m}`
of the multiplication `ν_{n,m}` of `N`, which uses that `f⁻¹` commutes with products. -/
@[stacks 0FR7 "the graded f⁻¹B-module f⁻¹N, with degree-n piece f⁻¹N^n and multiplication \
f⁻¹ν_{n,m}"]
public noncomputable def inverseImageGradedModule
    (N : SheafOfModules.GradedModule.{w', w', w'} B) :
    SheafOfModules.GradedModule.{w, w, w} (inverseImageGradedAlgebra f O B) :=
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  transportGradedModule J f.inverseImage N

/-- The homogeneous pieces of the inverse image of a right graded module are the inverse images
of the original homogeneous pieces. -/
public theorem inverseImageGradedModule_piece
    (N : SheafOfModules.GradedModule.{w', w', w'} B) (n : ℤ) :
    (inverseImageGradedModule f O N).piece n = (inverseImageModules f O).obj (N.piece n) :=
  rfl

/-- **The inverse image functor `f⁻¹ : Mod(B) ⥤ Mod(f⁻¹B)`** on right graded modules. Its
degreewise components are the inverse images of the degreewise components. -/
@[stacks 0FR7 "the functor f⁻¹ : Mod(B) ⥤ Mod(f⁻¹B)"]
public noncomputable def inverseImageGradedModuleFunctor :
    SheafOfModules.GradedModule.{w', w', w'} B ⥤
      SheafOfModules.GradedModule.{w, w, w} (inverseImageGradedAlgebra f O B) :=
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  transportGradedModuleFunctor J f.inverseImage

/-- The inverse-image functor acts on objects by `inverseImageGradedModule`. -/
public theorem inverseImageGradedModuleFunctor_obj
    (N : SheafOfModules.GradedModule.{w', w', w'} B) :
    (inverseImageGradedModuleFunctor f O).obj N = inverseImageGradedModule f O N := rfl

/-- **The inverse image of a homomorphism homogeneous of degree `d`**, again homogeneous of
degree `d`: the action on morphisms of `f⁻¹ : Mod^gr(B) ⥤ Mod^gr(f⁻¹B)`. -/
@[stacks 0FR7 "f⁻¹ on homogeneous morphisms of degree n"]
public noncomputable def inverseImageGradedHomOfDegree
    {N N' : SheafOfModules.GradedModule.{w', w', w'} B} {d : ℤ}
    (g : SheafOfModules.GradedHomOfDegree N N' d) :
    SheafOfModules.GradedHomOfDegree (inverseImageGradedModule f O N)
      (inverseImageGradedModule f O N') d :=
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  transportGradedHomOfDegree J f.inverseImage g

end InverseImage

end Stacks.Sheaves.GradedModuleInverseImage
