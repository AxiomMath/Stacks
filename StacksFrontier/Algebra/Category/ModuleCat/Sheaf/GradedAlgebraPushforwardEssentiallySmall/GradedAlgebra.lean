module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardEssentiallySmall.SectionMultiplication

/-!
# Pushforward of a graded algebra at unrelated universes: the graded algebra

## Main definitions

* `pushforwardGradedAlgebra`: the direct image of a sheaf of graded algebras.

## Main results

* `pushforwardGradedAlgebra_piece`, `pushforwardGradedAlgebra_mul_app` and
  `isPushforwardGradedAlgebra_pushforwardGradedAlgebra`: the direct-image graded algebra has the
  direct images of the source pieces as its homogeneous pieces, and satisfies the specification.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

open Stacks.Sheaves.GradedAlgebraPushforward

universe u u' u₂ v v' v₂ w w' x x' u₁ u₁'

variable {X : RingedTopos.{v, u₁, w}} {Y : RingedTopos.{v', u₁', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [EssentiallySmall.{w} X.C] [EssentiallySmall.{w'} Y.C]

private noncomputable def transportedMultiplicationMap
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Y).O))
    (h : ∀ n, B.piece n =
      f.pushforwardModules.obj
        (A.piece n)) (i j : ℤ) :
    underlyingPiece B i ⨯ underlyingPiece B j ⟶ underlyingPiece B (i + j) :=
  Limits.prod.map (pieceComparison f A B h i).hom (pieceComparison f A B h j).hom ≫
    pushforwardMultiplicationMap f A i j ≫
    (pieceComparison f A B h (i + j)).inv

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] [EssentiallySmall.{w'} Y.C] in
private lemma transportedMultiplicationMap_comp_pieceComparison
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Y).O))
    (h : ∀ n, B.piece n =
      f.pushforwardModules.obj
        (A.piece n)) (i j : ℤ) :
    transportedMultiplicationMap f A B h i j ≫
        (pieceComparison f A B h (i + j)).hom =
      Limits.prod.lift
          (Limits.prod.fst ≫ (pieceComparison f A B h i).hom)
          (Limits.prod.snd ≫ (pieceComparison f A B h j).hom) ≫
        (pushforwardProductIso f (underlyingPiece A i) (underlyingPiece A j)).inv ≫
        f.toToposHom.pushforward.map (multiplicationSheafMap A i j) := by
  rw [transportedMultiplicationMap, pushforwardMultiplicationMap]
  simp [Category.assoc, Limits.prod.map]

attribute [local irreducible] transposedMultiplicationAt

/-- Local sections of direct images in equal degrees are heterogeneously equal when their
transposed morphisms agree on every section. -/
private lemma heq_of_pushedSectionEquiv_hom_app_heq
    {X : RingedTopos.{v, u₁, w}} {Y : RingedTopos.{v', u₁', w'}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] [EssentiallySmall.{w'} Y.C]
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (U : Y.Cᵒᵖ) {first second : ℤ} (index_eq : first = second)
    {left : (f.pushforwardModules.obj (A.piece first)).val.obj U}
    {right : (f.pushforwardModules.obj (A.piece second)).val.obj U}
    (value_eq : ∀ (V : X.Cᵒᵖ) (element : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop))).obj.obj V),
      HEq ((pushedSectionEquiv f (A.piece first) U left).hom.app V element)
        ((pushedSectionEquiv f (A.piece second) U right).hom.app V element)) :
    HEq left right := by
  apply heq_of_equiv_heq
    (Source := fun degree =>
      (f.pushforwardModules.obj
        (A.piece degree)).val.obj U)
    (Target := fun degree => f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop)) ⟶
        underlyingPiece A degree)
    (fun degree => pushedSectionEquiv f (A.piece degree) U) index_eq
  exact sheaf_hom_heq_of_pointwise (C := X.C) (J := X.J)
    (congrArg (underlyingPiece A) index_eq) _ _ value_eq

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- The multiplication of the direct image of a graded algebra is associative. -/
public lemma transposedMultiplicationAt_assoc
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j k : ℤ) (U : Y.Cᵒᵖ)
    (left : (f.pushforwardModules.obj
      (A.piece i)).val.obj U)
    (middle : (f.pushforwardModules.obj
      (A.piece j)).val.obj U)
    (right : (f.pushforwardModules.obj
      (A.piece k)).val.obj U) :
    HEq (transposedMultiplicationAt f A (i + j) k U
      (transposedMultiplicationAt f A i j U left middle) right)
      (transposedMultiplicationAt f A i (j + k) U left
        (transposedMultiplicationAt f A j k U middle right)) := by
  refine heq_of_pushedSectionEquiv_hom_app_heq f A U (add_assoc i j k) fun V element => ?_
  rw [transposedMultiplicationAt_apply f A (i + j) k U _ _ V element,
    transposedMultiplicationAt_apply f A i (j + k) U _ _ V element,
    transposedMultiplicationAt_apply f A i j U left middle V element,
    transposedMultiplicationAt_apply f A j k U middle right V element]
  exact A.mul_assoc i j k V _ _ _

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [EssentiallySmall.{w} X.C] in
private lemma pushedUnitSection_apply
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (U : Y.Cᵒᵖ) (V : X.Cᵒᵖ)
    (element : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop))).obj.obj V) :
    (pushedSectionEquiv f (A.piece 0) U
      ((pushforwardUnitSection f A).eval U)).hom.app V element = A.one.eval V := by
  let terminalElement : (⊤_ (Sheaf Y.J (Type w'))).obj.obj U :=
    (terminalPUnitIso (X := Y)).hom.hom.app U PUnit.unit
  rw [pushforwardUnitSection_eval f A U terminalElement]
  change (transposedSectionEquiv f U _
    ((pushedPieceUnderlyingIso f (A.piece 0)).hom.hom.app U
      ((pushforwardUnitMap f A ≫
        (pushedPieceUnderlyingIso f (A.piece 0)).inv).hom.app U terminalElement))).hom.app
          V element = _
  rw [← sheaf_comp_apply]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (transposedSectionEquiv f U _
    ((f.toToposHom.pushforward.map (unitSheafMap A)).hom.app U
      ((pushforwardTerminalIso f).inv.hom.app U terminalElement))).hom.app V element = _
  rw [transposedSectionEquiv_comp, sheaf_comp_apply]
  rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [EssentiallySmall.{w} X.C] in
/-- The unit of the direct image of a graded algebra is a left identity. -/
public lemma transposedMultiplicationAt_one_mul
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i : ℤ) (U : Y.Cᵒᵖ)
    (value : (f.pushforwardModules.obj
      (A.piece i)).val.obj U) :
    HEq (transposedMultiplicationAt f A 0 i U
      ((pushforwardUnitSection f A).eval U) value) value := by
  refine heq_of_pushedSectionEquiv_hom_app_heq f A U (zero_add i) fun V element => ?_
  rw [transposedMultiplicationAt_apply f A 0 i U _ value V element,
    pushedUnitSection_apply f A U V element]
  exact A.one_mul i V _

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [EssentiallySmall.{w} X.C] in
/-- The unit of the direct image of a graded algebra is a right identity. -/
public lemma transposedMultiplicationAt_mul_one
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i : ℤ) (U : Y.Cᵒᵖ)
    (value : (f.pushforwardModules.obj
      (A.piece i)).val.obj U) :
    HEq (transposedMultiplicationAt f A i 0 U value
      ((pushforwardUnitSection f A).eval U)) value := by
  refine heq_of_pushedSectionEquiv_hom_app_heq f A U (add_zero i) fun V element => ?_
  rw [transposedMultiplicationAt_apply f A i 0 U value _ V element,
    pushedUnitSection_apply f A U V element]
  exact A.mul_one i V _

/-- **The direct image of a graded algebra under a morphism of ringed topoi.** Its homogeneous
pieces are the direct images of the homogeneous pieces of the source, on the nose, and its
multiplication and unit are the induced ones. -/
public noncomputable def pushforwardGradedAlgebra
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) :
    SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Y).O) where
  piece degree := f.pushforwardModules.obj (A.piece degree)
  mul := pushforwardBilinearMap f A
  one := pushforwardUnitSection f A
  mul_assoc := transposedMultiplicationAt_assoc f A
  one_mul := transposedMultiplicationAt_one_mul f A
  mul_one := transposedMultiplicationAt_mul_one f A

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- The homogeneous pieces of the direct image of a graded algebra are the direct images of the
homogeneous pieces of the source. -/
public theorem pushforwardGradedAlgebra_piece
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (n : ℤ) :
    (pushforwardGradedAlgebra f A).piece n = f.pushforwardModules.obj (A.piece n) :=
  rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- The multiplication of the direct image of a graded algebra, on local sections, is
`transposedMultiplicationAt`. -/
public theorem pushforwardGradedAlgebra_mul_app
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (left : (f.pushforwardModules.obj (A.piece i)).val.obj U)
    (right : (f.pushforwardModules.obj (A.piece j)).val.obj U) :
    ((pushforwardGradedAlgebra f A).mul i j).app U left right =
      transposedMultiplicationAt f A i j U left right :=
  rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- **The direct image of a graded algebra satisfies its direct-image specification**: its
pieces and operations are the canonical direct images of those of the source. -/
public theorem isPushforwardGradedAlgebra_pushforwardGradedAlgebra
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) :
    IsPushforwardGradedAlgebra f A (pushforwardGradedAlgebra f A) := by
  classical
  refine ⟨(fun _ => rfl), ?_, ?_⟩
  · intro i j
    refine ⟨multiplicationSheafMap A i j, pushedMultiplicationSheafMap f A i j,
      pushforwardProductIso f (underlyingPiece A i) (underlyingPiece A j),
      (fun _ _ => rfl), ?_, pushforwardProductIso_hom_fst f _ _,
      pushforwardProductIso_hom_snd f _ _, ?_⟩
    · intro U element
      exact pushedMultiplicationSheafMap_apply f A i j U element
    · exact transportedMultiplicationMap_comp_pieceComparison f A
        (pushforwardGradedAlgebra f A) (fun _ => rfl) i j
  · refine ⟨unitSheafMap A,
      pushforwardUnitMap f A ≫ (pushedPieceUnderlyingIso f (A.piece 0)).inv,
      pushforwardTerminalIso f, (fun _ _ => rfl), ?_, ?_⟩
    · intro U element
      exact (pushforwardUnitSection_eval f A U element).symm
    · change (pushforwardUnitMap f A ≫
        (pushedPieceUnderlyingIso f (A.piece 0)).inv) ≫
        (pushedPieceUnderlyingIso f (A.piece 0)).hom = _
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- A graded algebra whose pieces and operations are the canonical direct images
of those of the source exists.

This is the pushforward half of Stacks 0FQX. -/
public theorem exists_pushforwardGradedAlgebra
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) :
    ∃ B : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Y).O),
      IsPushforwardGradedAlgebra f A B :=
  ⟨pushforwardGradedAlgebra f A, isPushforwardGradedAlgebra_pushforwardGradedAlgebra f A⟩

/-- A graded algebra together with its direct-image specification.

This is the pushforward half of Stacks 0FQX; see `exists_pushforwardGradedAlgebra`. -/
public noncomputable def pushforwardGradedAlgebraData
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) :
    { B : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Y).O) //
      IsPushforwardGradedAlgebra f A B } :=
  ⟨pushforwardGradedAlgebra f A, isPushforwardGradedAlgebra_pushforwardGradedAlgebra f A⟩

/-! ### The direct image of graded algebras as a functor -/

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- The transposed description of local sections of a direct image of sheaves of modules is the
one for its underlying sheaf of sets. -/
public theorem pushedSectionEquiv_eq_transposedSectionEquiv
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) (U : Y.Cᵒᵖ)
    (x : (f.pushforwardModules.obj M).val.obj U) :
    pushedSectionEquiv f M U x =
      transposedSectionEquiv f U (Stacks.underlyingModuleSheaf X.J M) x :=
  rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- **The transposed description of local sections of a direct image is natural in the sheaf of
modules.** -/
public theorem pushedSectionEquiv_map
    (f : RingedToposHom X Y)
    {M N : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)}
    (g : M ⟶ N) (U : Y.Cᵒᵖ)
    (x : (f.pushforwardModules.obj M).val.obj U) :
    pushedSectionEquiv f N U ((f.pushforwardModules.map g).val.app U x) =
      pushedSectionEquiv f M U x ≫
        (Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)).map g :=
  transposedSectionEquiv_comp f U
    ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)).map g) x

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
