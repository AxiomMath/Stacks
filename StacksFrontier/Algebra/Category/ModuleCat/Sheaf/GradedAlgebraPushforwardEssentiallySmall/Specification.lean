module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.CommRingModuleData
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.SheafSectionEssentiallySmall
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic

/-!
# Pushforward of a graded algebra at unrelated universes: the specification

The direct image of a sheaf of graded algebras along a morphism of ringed topoi `X ⟶ Y`, where
the objects, morphisms and structure-sheaf sections of each of `X` and `Y` lie in three unrelated
universes, the target site being essentially small (`CategoryTheory.EssentiallySmall.{w'} Y.C`).
This covers the small étale ringed topos `AlgebraicGeometry.Space.smallEtaleRingedTopos` of an
algebraic space, which `Stacks.Sheaves.GradedAlgebraPushforward.pushforwardGradedAlgebra` does
not, since it asks the three universes of a ringed topos to coincide.

## Main definitions

* `ringedSite` views a ringed topos as its underlying ringed site, at unrelated universes.
* `IsPushforwardGradedAlgebra`: the specification of the direct image of a sheaf of graded
  algebras.
* `transposedSectionEquiv` and `pushedSectionEquiv`: local sections of a direct image, read as
  morphisms out of the inverse image of a sheafified small representable.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
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

/-- A ringed topos, viewed as its underlying ringed site. -/
public abbrev ringedSite (Z : RingedTopos.{v, u₁, w}) :
    RingedSite.{u₁, v, w} :=
  { C := Z.C, J := Z.J, O := Z.O }

/-- The underlying sheaf of a homogeneous piece. -/
public noncomputable abbrev underlyingPiece
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (n : ℤ) :
    Sheaf X.J (Type w) :=
  Stacks.underlyingModuleSheaf X.J (A.piece n)

/-- The canonical comparison between the underlying sheaf of a specified
pushforward piece and the direct image of the source piece. -/
public noncomputable def pieceComparison
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Y).O))
    (h : ∀ n, B.piece n =
      f.pushforwardModules.obj
        (A.piece n)) (n : ℤ) :
    underlyingPiece B n ≅ f.toToposHom.pushforward.obj (underlyingPiece A n) :=
  (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).mapIso
      (eqToIso (h n)) ≪≫
    f.pushforwardModulesUnderlyingIso.app
      (A.piece n)

/-- Multiplication and unit of a graded algebra are the canonical direct images
of the corresponding operations, with the degreewise module identifications. -/
public def IsPushforwardGradedAlgebra
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Y).O)) :
    Prop :=
  ∃ h : ∀ n, B.piece n =
      f.pushforwardModules.obj
        (A.piece n),
    (∀ i j : ℤ, ∃ (sourceMul :
        underlyingPiece A i ⨯ underlyingPiece A j ⟶ underlyingPiece A (i + j))
      (targetMul :
        underlyingPiece B i ⨯ underlyingPiece B j ⟶ underlyingPiece B (i + j))
      (productIso :
        f.toToposHom.pushforward.obj
            (underlyingPiece A i ⨯ underlyingPiece A j) ≅
          f.toToposHom.pushforward.obj (underlyingPiece A i) ⨯
            f.toToposHom.pushforward.obj (underlyingPiece A j)),
      (∀ (U : X.Cᵒᵖ) (z : (underlyingPiece A i ⨯ underlyingPiece A j).obj.obj U),
        sourceMul.hom.app U z =
          (A.mul i j).app U
            ((Limits.prod.fst : underlyingPiece A i ⨯ underlyingPiece A j ⟶
              underlyingPiece A i).hom.app U z)
            ((Limits.prod.snd : underlyingPiece A i ⨯ underlyingPiece A j ⟶
              underlyingPiece A j).hom.app U z)) ∧
      (∀ (U : Y.Cᵒᵖ) (z : (underlyingPiece B i ⨯ underlyingPiece B j).obj.obj U),
        targetMul.hom.app U z =
          (B.mul i j).app U
            ((Limits.prod.fst : underlyingPiece B i ⨯ underlyingPiece B j ⟶
              underlyingPiece B i).hom.app U z)
            ((Limits.prod.snd : underlyingPiece B i ⨯ underlyingPiece B j ⟶
              underlyingPiece B j).hom.app U z)) ∧
      (productIso.hom ≫ Limits.prod.fst =
        f.toToposHom.pushforward.map (Limits.prod.fst :
          underlyingPiece A i ⨯ underlyingPiece A j ⟶ underlyingPiece A i)) ∧
      (productIso.hom ≫ Limits.prod.snd =
        f.toToposHom.pushforward.map (Limits.prod.snd :
          underlyingPiece A i ⨯ underlyingPiece A j ⟶ underlyingPiece A j)) ∧
      (targetMul ≫ (pieceComparison f A B h (i + j)).hom =
        Limits.prod.lift
          (Limits.prod.fst ≫ (pieceComparison f A B h i).hom)
          (Limits.prod.snd ≫ (pieceComparison f A B h j).hom) ≫
          productIso.inv ≫ f.toToposHom.pushforward.map sourceMul)) ∧
    (∃ (sourceUnit : (⊤_ (Sheaf X.J (Type w))) ⟶ underlyingPiece A 0)
      (targetUnit : (⊤_ (Sheaf Y.J (Type w'))) ⟶ underlyingPiece B 0)
      (terminalIso : f.toToposHom.pushforward.obj (⊤_ (Sheaf X.J (Type w))) ≅
        (⊤_ (Sheaf Y.J (Type w')))),
      (∀ (U : X.Cᵒᵖ) (z : (⊤_ (Sheaf X.J (Type w))).obj.obj U),
        sourceUnit.hom.app U z = A.one.eval U) ∧
      (∀ (U : Y.Cᵒᵖ) (z : (⊤_ (Sheaf Y.J (Type w'))).obj.obj U),
        targetUnit.hom.app U z = B.one.eval U) ∧
      (targetUnit ≫ (pieceComparison f A B h 0).hom =
        terminalIso.inv ≫ f.toToposHom.pushforward.map sourceUnit))

/-- The multiplication of a graded algebra, as a morphism from the product of the underlying
sheaves of sets of two homogeneous pieces to the underlying sheaf of sets of their sum. -/
public noncomputable def multiplicationSheafMap
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) :
    underlyingPiece A i ⨯ underlyingPiece A j ⟶ underlyingPiece A (i + j) := by
  refine ObjectProperty.homMk { app := fun U => ?_, naturality := ?_ }
  · exact ↾fun z => (A.mul i j).app U
      ((Limits.prod.fst : underlyingPiece A i ⨯ underlyingPiece A j ⟶
        underlyingPiece A i).hom.app U z)
      ((Limits.prod.snd : underlyingPiece A i ⨯ underlyingPiece A j ⟶
        underlyingPiece A j).hom.app U z)
  · intro U V g
    ext z
    have hf := congrArg (fun h => (ConcreteCategory.hom h) z)
      ((Limits.prod.fst : underlyingPiece A i ⨯ underlyingPiece A j ⟶
        underlyingPiece A i).hom.naturality g)
    have hs := congrArg (fun h => (ConcreteCategory.hom h) z)
      ((Limits.prod.snd : underlyingPiece A i ⨯ underlyingPiece A j ⟶
        underlyingPiece A j).hom.naturality g)
    simp only [CategoryTheory.comp_apply] at hf hs
    change (A.mul i j).app V
      ((Limits.prod.fst : underlyingPiece A i ⨯ underlyingPiece A j ⟶
        underlyingPiece A i).hom.app V
        ((underlyingPiece A i ⨯ underlyingPiece A j).obj.map g z))
      ((Limits.prod.snd : underlyingPiece A i ⨯ underlyingPiece A j ⟶
        underlyingPiece A j).hom.app V
        ((underlyingPiece A i ⨯ underlyingPiece A j).obj.map g z)) =
      (underlyingPiece A (i + j)).obj.map g
        ((A.mul i j).app U
          ((Limits.prod.fst : underlyingPiece A i ⨯ underlyingPiece A j ⟶
            underlyingPiece A i).hom.app U z)
          ((Limits.prod.snd : underlyingPiece A i ⨯ underlyingPiece A j ⟶
            underlyingPiece A j).hom.app U z))
    rw [hf, hs]
    exact ((A.mul i j).naturality g
      ((Limits.prod.fst : underlyingPiece A i ⨯ underlyingPiece A j ⟶
        underlyingPiece A i).hom.app U z)
      ((Limits.prod.snd : underlyingPiece A i ⨯ underlyingPiece A j ⟶
        underlyingPiece A j).hom.app U z)).symm

noncomputable def unitSheafMap
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) :
    (⊤_ (Sheaf X.J (Type w))) ⟶ underlyingPiece A 0 :=
  moduleSectionSheafMap (A.piece 0) A.one

noncomputable def pushforwardMultiplicationMap
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) :
    f.toToposHom.pushforward.obj (underlyingPiece A i) ⨯
      f.toToposHom.pushforward.obj (underlyingPiece A j) ⟶
        f.toToposHom.pushforward.obj (underlyingPiece A (i + j)) :=
  (pushforwardProductIso f (underlyingPiece A i) (underlyingPiece A j)).inv ≫
    f.toToposHom.pushforward.map (multiplicationSheafMap A i j)

/-- The underlying sheaf of sets of a direct image of sheaves of modules is the direct image of
the underlying sheaf of sets. -/
public noncomputable def pushedPieceUnderlyingIso
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    Stacks.underlyingModuleSheaf Y.J
      (f.pushforwardModules.obj M) ≅
        f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J M) := by
  exact
    f.pushforwardModulesUnderlyingIso.app M


noncomputable def pushedMultiplicationSheafMap
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) :
    Stacks.underlyingModuleSheaf Y.J
        (f.pushforwardModules.obj
          (A.piece i)) ⨯
      Stacks.underlyingModuleSheaf Y.J
        (f.pushforwardModules.obj
          (A.piece j)) ⟶
      Stacks.underlyingModuleSheaf Y.J
        (f.pushforwardModules.obj
          (A.piece (i + j))) :=
  Limits.prod.map (pushedPieceUnderlyingIso f (A.piece i)).hom
      (pushedPieceUnderlyingIso f (A.piece j)).hom ≫
    pushforwardMultiplicationMap f A i j ≫
    (pushedPieceUnderlyingIso f (A.piece (i + j))).inv

private noncomputable def pushedMultiplicationAt
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ)
    (U : Y.Cᵒᵖ)
    (x : ((f.pushforwardModules.obj
      (A.piece i)).val.obj U))
    (y : ((f.pushforwardModules.obj
      (A.piece j)).val.obj U)) :
    ((f.pushforwardModules.obj
      (A.piece (i + j))).val.obj U) :=
  (pushedMultiplicationSheafMap f A i j).hom.app U
    ((sheafProductSectionsIso
      (Stacks.underlyingModuleSheaf Y.J
        (f.pushforwardModules.obj
          (A.piece i)))
      (Stacks.underlyingModuleSheaf Y.J
        (f.pushforwardModules.obj
          (A.piece j))) U).inv (typeProductElement x y))

noncomputable def pushforwardUnitMap
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) :
    (⊤_ (Sheaf Y.J (Type w'))) ⟶
      f.toToposHom.pushforward.obj (underlyingPiece A 0) :=
  (pushforwardTerminalIso f).inv ≫
    f.toToposHom.pushforward.map (unitSheafMap A)

/-- **The unit of the direct image of a graded algebra**: the global degree-zero section
obtained from the unit of the source algebra through the terminal-object comparison of the
direct image. -/
@[no_expose] public noncomputable def pushforwardUnitSection
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) :
    (f.pushforwardModules.obj
      (A.piece 0)).sections :=
  sectionOfUnderlyingMap _
    (pushforwardUnitMap f A ≫
      f.pushforwardModulesUnderlyingIso.inv.app
        (A.piece 0))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w'} Y.C] in
omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [EssentiallySmall.{w} X.C] in
private lemma moduleSectionSheafMap_pushforwardUnitSection
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) :
    moduleSectionSheafMap
        (f.pushforwardModules.obj
          (A.piece 0))
        (pushforwardUnitSection f A) =
      pushforwardUnitMap f A ≫
        f.pushforwardModulesUnderlyingIso.inv.app
          (A.piece 0) :=
  moduleSectionSheafMap_sectionOfUnderlyingMap _ _

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w'} Y.C] in
omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [EssentiallySmall.{w} X.C] in
lemma pushforwardUnitSection_eval
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (U : Y.Cᵒᵖ) (z : (⊤_ (Sheaf Y.J (Type w'))).obj.obj U) :
    (pushforwardUnitSection f A).eval U =
      (pushforwardUnitMap f A ≫
        f.pushforwardModulesUnderlyingIso.inv.app
          (A.piece 0)).hom.app U z := by
  have h := congrArg (fun k => k.hom.app U z)
    (moduleSectionSheafMap_pushforwardUnitSection f A)
  change (pushforwardUnitSection f A).eval U =
    (pushforwardUnitMap f A ≫
      f.pushforwardModulesUnderlyingIso.inv.app
        (A.piece 0)).hom.app U z
  change (pushforwardUnitSection f A).eval U =
    (pushforwardUnitMap f A ≫
      f.pushforwardModulesUnderlyingIso.inv.app
        (A.piece 0)).hom.app U z at h
  exact h

private noncomputable def transportedUnitMap
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Y).O))
    (h : ∀ n, B.piece n =
      f.pushforwardModules.obj
        (A.piece n)) :
    (⊤_ (Sheaf Y.J (Type w'))) ⟶ underlyingPiece B 0 :=
  pushforwardUnitMap f A ≫ (pieceComparison f A B h 0).inv

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] [EssentiallySmall.{w'} Y.C] in
private lemma transportedUnitMap_comp_pieceComparison
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Y).O))
    (h : ∀ n, B.piece n =
      f.pushforwardModules.obj
        (A.piece n)) :
    transportedUnitMap f A B h ≫ (pieceComparison f A B h 0).hom =
      (pushforwardTerminalIso f).inv ≫
        f.toToposHom.pushforward.map (unitSheafMap A) := by
  simp [transportedUnitMap, pushforwardUnitMap, Category.assoc]

/-- **Local sections of a direct image of sheaves of sets, transposed.** A section over `U` of
the direct image of a sheaf of sets is the same thing as a morphism to that sheaf from the
inverse image of the sheafified Yoneda object of `U`. -/
public noncomputable def transposedSectionEquiv
    (f : RingedToposHom X Y) (U : Y.Cᵒᵖ) (M : Sheaf X.J (Type w)) :
    (f.toToposHom.pushforward.obj M).obj.obj U ≃
      (f.toToposHom.inverseImage.obj
        ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop)) ⟶ M) :=
  (sectionEquivSmall Y.J U _).trans (f.toToposHom.adj.homEquiv _ _).symm

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget
    AddCommGrpCat.{w'})] [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective
    AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective
    AddCommGrpCat.{w'}] [EssentiallySmall.{w} X.C] in
/-- The transposed identification of local sections of a direct image is natural in the
sheaf. -/
public lemma transposedSectionEquiv_comp
    (f : RingedToposHom X Y) (U : Y.Cᵒᵖ)
    {M N : Sheaf X.J (Type w)} (morphism : M ⟶ N)
    (element : (f.toToposHom.pushforward.obj M).obj.obj U) :
    transposedSectionEquiv f U N
      ((f.toToposHom.pushforward.map morphism).hom.app U element) =
        transposedSectionEquiv f U M element ≫ morphism := by
  dsimp [transposedSectionEquiv]
  rw [sectionEquivSmall_comp, Adjunction.homEquiv_naturality_right_symm]

/-- **Local sections of a direct image of sheaves of modules, transposed.** A section over `U`
of the direct image of a sheaf of modules is the same thing as a morphism from the inverse image
of the sheafified Yoneda object of `U` to the underlying sheaf of sets of the module. -/
public noncomputable def pushedSectionEquiv
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) (U : Y.Cᵒᵖ) :
    (f.pushforwardModules.obj M).val.obj U ≃
      (f.toToposHom.inverseImage.obj
        ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop)) ⟶
          Stacks.underlyingModuleSheaf X.J M) :=
  ((Functor.mapIso ((sheafToPresheaf Y.J (Type w')) ⋙
    (evaluation Y.Cᵒᵖ (Type w')).obj U) (pushedPieceUnderlyingIso f M)).toEquiv).trans
    (transposedSectionEquiv f U _)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget
    AddCommGrpCat.{w'})] [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective
    AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective
    AddCommGrpCat.{w'}] [EssentiallySmall.{w} X.C] in
private lemma transposedSectionEquiv_pair
    (f : RingedToposHom X Y) (U : Y.Cᵒᵖ)
    (M N : Sheaf X.J (Type w))
    (element : (f.toToposHom.pushforward.obj (M ⨯ N)).obj.obj U) :
    transposedSectionEquiv f U (M ⨯ N) element =
      prod.lift
        (transposedSectionEquiv f U M
          ((f.toToposHom.pushforward.map prod.fst).hom.app U element))
        (transposedSectionEquiv f U N
          ((f.toToposHom.pushforward.map prod.snd).hom.app U element)) := by
  apply prod.hom_ext <;> simp [← transposedSectionEquiv_comp]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget
    AddCommGrpCat.{w'})] [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective
    AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective
    AddCommGrpCat.{w'}] [EssentiallySmall.{w} X.C] in
lemma transposedSectionEquiv_binary
    (f : RingedToposHom X Y) (U : Y.Cᵒᵖ)
    (M N P : Sheaf X.J (Type w)) (operation : M ⨯ N ⟶ P)
    (element : (f.toToposHom.pushforward.obj M ⨯
      f.toToposHom.pushforward.obj N).obj.obj U) :
    transposedSectionEquiv f U P
      (((pushforwardProductIso f M N).inv ≫
        f.toToposHom.pushforward.map operation).hom.app U element) =
      prod.lift
        (transposedSectionEquiv f U M
          ((prod.fst : _ ⨯ _ ⟶ f.toToposHom.pushforward.obj M).hom.app U element))
        (transposedSectionEquiv f U N
          ((prod.snd : _ ⨯ _ ⟶ f.toToposHom.pushforward.obj N).hom.app U element)) ≫
        operation := by
  change transposedSectionEquiv f U P
    ((f.toToposHom.pushforward.map operation).hom.app U
      ((pushforwardProductIso f M N).inv.hom.app U element)) = _
  rw [transposedSectionEquiv_comp, transposedSectionEquiv_pair]
  congr 2
  · congr 1
    have equality : (pushforwardProductIso f M N).inv ≫
        f.toToposHom.pushforward.map prod.fst = prod.fst := by
      rw [← pushforwardProductIso_hom_fst, Iso.inv_hom_id_assoc]
    exact congrArg (fun morphism => morphism.hom.app U element) equality
  · congr 1
    have equality : (pushforwardProductIso f M N).inv ≫
        f.toToposHom.pushforward.map prod.snd = prod.snd := by
      rw [← pushforwardProductIso_hom_snd, Iso.inv_hom_id_assoc]
    exact congrArg (fun morphism => morphism.hom.app U element) equality

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
