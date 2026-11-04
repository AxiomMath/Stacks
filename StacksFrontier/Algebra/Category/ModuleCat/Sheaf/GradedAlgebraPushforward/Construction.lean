module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.CommRingModuleData
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforward.BilinearMultiplication

/-!
# Pushforward of a graded algebra

A morphism of ringed topoi sends a graded algebra to a graded algebra on the target.
Its homogeneous pieces are the direct images of the original homogeneous pieces,
and its multiplication and unit are induced by those of the original algebra.

## Main definitions

* `pushforwardGradedAlgebra` is the direct image of a graded algebra.
* `pushforwardGradedAlgebraData` is the direct image of a graded algebra together with its
  direct-image specification.

## Main results

* `pushforwardGradedAlgebra_piece`: the homogeneous pieces of the direct image are the direct
  images of the homogeneous pieces of the source.
* `isPushforwardGradedAlgebra_pushforwardGradedAlgebra`: the direct image satisfies
  `IsPushforwardGradedAlgebra`.
* `exists_pushforwardGradedAlgebra`: a graded algebra satisfying the direct-image specification
  exists.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/



@[expose] public section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.GradedAlgebraPushforward

universe u u' v v' w w' x x'

attribute [local irreducible] transposedMultiplicationAt

/-- Over equal indices, two elements of a family of types are heterogeneously equal if their
images under a family of equivalences are. -/
lemma heq_of_equiv_heq {Index : Sort v}
    {Source : Index → Type w} {Target : Index → Type w'}
    (equiv : ∀ index, Source index ≃ Target index) {first second : Index}
    (index_eq : first = second) {left : Source first} {right : Source second}
    (value_eq : HEq (equiv first left) (equiv second right)) : HEq left right := by
  subst second
  exact heq_of_eq ((equiv first).injective (eq_of_heq value_eq))

/-- Morphisms of sheaves of sets into equal targets are heterogeneously equal when they are so
on every section. -/
lemma sheaf_hom_heq_of_pointwise
    {C : Type u} [Category.{v, u} C] {J : GrothendieckTopology C}
    {Source Left Right : Sheaf J (Type w)} (object_eq : Left = Right)
    (left : Source ⟶ Left) (right : Source ⟶ Right)
    (value_eq : ∀ (object : Cᵒᵖ) (element : Source.obj.obj object),
      HEq (left.hom.app object element) (right.hom.app object element)) :
    HEq left right := by
  subst Right
  apply heq_of_eq
  ext object element
  exact eq_of_heq (value_eq object element)

/-- Over equal degrees, two local sections of the direct image of the pieces of a graded algebra
are heterogeneously equal if the corresponding maps agree on every section. -/
private lemma heq_of_pushedSectionEquiv_hom_app_heq
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (U : Y.Cᵒᵖ) {i j : ℤ} (index_eq : i = j)
    {left : (f.pushforwardModules.obj (A.piece i)).val.obj U}
    {right : (f.pushforwardModules.obj (A.piece j)).val.obj U}
    (value_eq : ∀ (V : X.Cᵒᵖ) (element : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type u')).obj (yoneda.obj U.unop))).obj.obj V),
      HEq ((pushedSectionEquiv f (A.piece i) U left).hom.app V element)
        ((pushedSectionEquiv f (A.piece j) U right).hom.app V element)) :
    HEq left right := by
  apply heq_of_equiv_heq
    (Source := fun degree => (f.pushforwardModules.obj (A.piece degree)).val.obj U)
    (Target := fun degree => f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type u')).obj (yoneda.obj U.unop)) ⟶ underlyingPiece A degree)
    (fun degree => pushedSectionEquiv f (A.piece degree) U) index_eq
  exact sheaf_hom_heq_of_pointwise (congrArg (underlyingPiece A) index_eq) _ _ value_eq

/-- The multiplication of the direct image of a graded algebra is associative. -/
public lemma transposedMultiplicationAt_assoc
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
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
  apply heq_of_pushedSectionEquiv_hom_app_heq f A U (add_assoc i j k)
  intro V element
  rw [transposedMultiplicationAt_apply f A (i + j) k U _ _ V element,
    transposedMultiplicationAt_apply f A i (j + k) U _ _ V element,
    transposedMultiplicationAt_apply f A i j U left middle V element,
    transposedMultiplicationAt_apply f A j k U middle right V element]
  exact A.mul_assoc i j k V _ _ _

private lemma pushedUnitSection_apply
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (U : Y.Cᵒᵖ) (V : X.Cᵒᵖ)
    (element : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type u')).obj (yoneda.obj U.unop))).obj.obj V) :
    (pushedSectionEquiv f (A.piece 0) U
      ((pushforwardUnitSection f A).eval U)).hom.app V element = A.one.eval V := by
  let terminalElement : (⊤_ (Sheaf Y.J (Type u'))).obj.obj U :=
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

/-- The unit of the direct image of a graded algebra is a left identity. -/
public lemma transposedMultiplicationAt_one_mul
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (i : ℤ) (U : Y.Cᵒᵖ)
    (value : (f.pushforwardModules.obj
      (A.piece i)).val.obj U) :
    HEq (transposedMultiplicationAt f A 0 i U
      ((pushforwardUnitSection f A).eval U) value) value := by
  apply heq_of_pushedSectionEquiv_hom_app_heq f A U (zero_add i)
  intro V element
  rw [transposedMultiplicationAt_apply f A 0 i U _ value V element,
    pushedUnitSection_apply f A U V element]
  exact A.one_mul i V _

/-- The unit of the direct image of a graded algebra is a right identity. -/
public lemma transposedMultiplicationAt_mul_one
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (i : ℤ) (U : Y.Cᵒᵖ)
    (value : (f.pushforwardModules.obj
      (A.piece i)).val.obj U) :
    HEq (transposedMultiplicationAt f A i 0 U value
      ((pushforwardUnitSection f A).eval U)) value := by
  apply heq_of_pushedSectionEquiv_hom_app_heq f A U (add_zero i)
  intro V element
  rw [transposedMultiplicationAt_apply f A i 0 U value _ V element,
    pushedUnitSection_apply f A U V element]
  exact A.mul_one i V _

/-- **The direct image of a graded algebra under a morphism of ringed topoi.** Its homogeneous
pieces are the direct images of the homogeneous pieces of the source, on the nose, and its
multiplication and unit are the induced ones. -/
public noncomputable def pushforwardGradedAlgebra
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) :
    SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite Y).O) where
  piece degree := f.pushforwardModules.obj (A.piece degree)
  mul := pushforwardBilinearMap f A
  one := pushforwardUnitSection f A
  mul_assoc := transposedMultiplicationAt_assoc f A
  one_mul := transposedMultiplicationAt_one_mul f A
  mul_one := transposedMultiplicationAt_mul_one f A

/-- The homogeneous pieces of the direct image of a graded algebra are the direct images of the
homogeneous pieces of the source. -/
public theorem pushforwardGradedAlgebra_piece
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) (n : ℤ) :
    (pushforwardGradedAlgebra f A).piece n = f.pushforwardModules.obj (A.piece n) :=
  rfl

/-- The multiplication of the direct image of a graded algebra, on local sections, is
`transposedMultiplicationAt`. -/
public theorem pushforwardGradedAlgebra_mul_app
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (left : (f.pushforwardModules.obj (A.piece i)).val.obj U)
    (right : (f.pushforwardModules.obj (A.piece j)).val.obj U) :
    ((pushforwardGradedAlgebra f A).mul i j).app U left right =
      transposedMultiplicationAt f A i j U left right :=
  rfl

/-- **The direct image of a graded algebra satisfies its direct-image specification**: its
pieces and operations are the canonical direct images of those of the source. -/
public theorem isPushforwardGradedAlgebra_pushforwardGradedAlgebra
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) :
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

/-- A graded algebra whose pieces and operations are the canonical direct images
of those of the source exists. -/
@[stacks 0FQX "graded_algebra_pushforward"]
public theorem exists_pushforwardGradedAlgebra
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) :
    ∃ B : SheafOfModules.GradedAlgebra
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite Y).O),
      IsPushforwardGradedAlgebra f A B :=
  ⟨pushforwardGradedAlgebra f A, isPushforwardGradedAlgebra_pushforwardGradedAlgebra f A⟩

/-- A graded algebra together with its direct-image specification. -/
@[stacks 0FQX "graded_algebra_pushforward"]
public noncomputable def pushforwardGradedAlgebraData
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) :
    { B : SheafOfModules.GradedAlgebra
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite Y).O) //
      IsPushforwardGradedAlgebra f A B } :=
  ⟨pushforwardGradedAlgebra f A, isPushforwardGradedAlgebra_pushforwardGradedAlgebra f A⟩

/-! ### Naturality of the transposed description of local sections -/

/-- The transposed description of local sections of a direct image is the one for the underlying
sheaf of sets, because the underlying sheaf of sets of a direct image of sheaves of modules *is*
the direct image of the underlying sheaf of sets. -/
public theorem pushedSectionEquiv_eq_transposedSectionEquiv
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) (U : Y.Cᵒᵖ)
    (x : (f.pushforwardModules.obj M).val.obj U) :
    pushedSectionEquiv f M U x =
      transposedSectionEquiv f U (Stacks.underlyingModuleSheaf X.J M) x :=
  rfl

/-- **The transposed description of local sections of a direct image is natural in the sheaf of
modules.** -/
public theorem pushedSectionEquiv_map
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    {M N : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)} (g : M ⟶ N)
    (U : Y.Cᵒᵖ)
    (x : (f.pushforwardModules.obj M).val.obj U) :
    pushedSectionEquiv f N U ((f.pushforwardModules.map g).val.app U x) =
      pushedSectionEquiv f M U x ≫
        (Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)).map g :=
  transposedSectionEquiv_comp f U
    ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)).map g) x

end Stacks.Sheaves.GradedAlgebraPushforward
