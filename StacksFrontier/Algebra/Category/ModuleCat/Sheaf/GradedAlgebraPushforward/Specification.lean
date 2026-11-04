module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.CommRingModuleData
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforward.TransportedAddition

/-!
# Pushforward of a graded algebra: the direct-image specification

The specification of the direct image of a graded algebra, and the canonical maps it is built
from: the underlying sheaves of sets of the homogeneous pieces, their comparison with the direct
images of the source pieces, the multiplication as a morphism of sheaves of sets, and the
direct-image multiplication and unit. A local section of a direct image is identified with a
morphism out of the inverse image of a sheafified Yoneda object.

## Main definitions

* `RingedTopos.ringedSite` views a ringed topos as its underlying ringed site.
* `IsPushforwardGradedAlgebra` specifies the direct-image multiplication and unit by the
  canonical product and terminal comparisons of the right adjoint.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.GradedAlgebraPushforward

universe u u' v v' w w' x x'

/-- A ringed topos, viewed as its underlying ringed site. -/
public abbrev RingedTopos.ringedSite (X : RingedTopos.{u, u, u}) :
    RingedSite.{u, u, u} :=
  { C := X.C, J := X.J, O := X.O }

/-- The underlying sheaf of a homogeneous piece. -/
public noncomputable abbrev underlyingPiece
    {X : RingedTopos.{u, u, u}}
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) (n : ℤ) :
    Sheaf X.J (Type u) :=
  Stacks.underlyingModuleSheaf X.J (A.piece n)

/-- The canonical comparison between the underlying sheaf of a specified
pushforward piece and the direct image of the source piece. -/
public noncomputable def pieceComparison
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite Y).O))
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
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite Y).O)) : Prop :=
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
    (∃ (sourceUnit : (⊤_ (Sheaf X.J (Type u))) ⟶ underlyingPiece A 0)
      (targetUnit : (⊤_ (Sheaf Y.J (Type u'))) ⟶ underlyingPiece B 0)
      (terminalIso : f.toToposHom.pushforward.obj (⊤_ (Sheaf X.J (Type u))) ≅
        (⊤_ (Sheaf Y.J (Type u')))),
      (∀ (U : X.Cᵒᵖ) (z : (⊤_ (Sheaf X.J (Type u))).obj.obj U),
        sourceUnit.hom.app U z = A.one.eval U) ∧
      (∀ (U : Y.Cᵒᵖ) (z : (⊤_ (Sheaf Y.J (Type u'))).obj.obj U),
        targetUnit.hom.app U z = B.one.eval U) ∧
      (targetUnit ≫ (pieceComparison f A B h 0).hom =
        terminalIso.inv ≫ f.toToposHom.pushforward.map sourceUnit))

/-- The multiplication of a graded algebra, as a morphism from the product of the underlying
sheaves of sets of two homogeneous pieces to the underlying sheaf of sets of their sum. -/
public noncomputable def multiplicationSheafMap
    {X : RingedTopos.{u, u, u}}
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
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

/-- A global section of a sheaf of modules, as a map from the terminal sheaf of sets to the
underlying sheaf of sets. -/
noncomputable def moduleSectionSheafMap
    {X : RingedTopos.{v, u, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) (s : M.sections) :
    (⊤_ (Sheaf X.J (Type w))) ⟶ Stacks.underlyingModuleSheaf X.J M := by
  refine ObjectProperty.homMk { app := fun U => ?_, naturality := ?_ }
  · exact ↾fun _ => s.eval U
  · intro U V g
    ext z
    change s.eval V = M.val.map g (s.eval U)
    exact (PresheafOfModules.sections_property s g).symm

/-- The sheaf of sets with value `PUnit` is the terminal sheaf of sets. -/
noncomputable def terminalPUnitIso {X : RingedTopos.{v, u, w}} :
    Sheaf.terminal X.J Types.isTerminalPUnit ≅ ⊤_ (Sheaf X.J (Type w)) :=
  (Sheaf.isTerminalTerminal X.J Types.isTerminalPUnit).uniqueUpToIso
    (terminalIsTerminal (C := Sheaf X.J (Type w)))

noncomputable def unitSheafMap
    {X : RingedTopos.{u, u, u}}
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) :
    (⊤_ (Sheaf X.J (Type u))) ⟶ underlyingPiece A 0 :=
  moduleSectionSheafMap (A.piece 0) A.one

/-- The global section of a sheaf of modules given by a map from the terminal sheaf of sets to the
underlying sheaf of sets. -/
noncomputable def sectionOfUnderlyingMap
    {X : RingedTopos.{v, u, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    (s : (⊤_ (Sheaf X.J (Type w))) ⟶
      Stacks.underlyingModuleSheaf X.J M) : M.sections := by
  let T : Sheaf X.J (Type w) := Sheaf.terminal X.J Types.isTerminalPUnit
  let η : T ⟶ ⊤_ (Sheaf X.J (Type w)) := (terminalPUnitIso (X := X)).hom
  refine PresheafOfModules.sectionsMk (fun U =>
    (η ≫ s).hom.app U (by dsimp [T, Sheaf.terminal]; exact PUnit.unit)) ?_
  intro U V g
  let tU : T.obj.obj U := by dsimp [T, Sheaf.terminal]; exact PUnit.unit
  let tV : T.obj.obj V := by dsimp [T, Sheaf.terminal]; exact PUnit.unit
  have hn := congrArg (fun h => (ConcreteCategory.hom h) tU)
    ((η ≫ s).hom.naturality g)
  simp only [CategoryTheory.comp_apply] at hn
  change (Stacks.underlyingModuleSheaf X.J M).obj.map g
      ((η ≫ s).hom.app U tU) =
    (η ≫ s).hom.app V tV
  simpa [T, Sheaf.terminal, tU, tV] using hn.symm

/-- `sectionOfUnderlyingMap` is a right inverse of `moduleSectionSheafMap`. -/
lemma moduleSectionSheafMap_sectionOfUnderlyingMap
    {X : RingedTopos.{v, u, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    (s : (⊤_ (Sheaf X.J (Type w))) ⟶
      Stacks.underlyingModuleSheaf X.J M) :
    moduleSectionSheafMap M (sectionOfUnderlyingMap M s) = s := by
  ext U x
  let e := terminalPUnitIso (X := X)
  have hcomp (z : (⊤_ (Sheaf X.J (Type w))).obj.obj U) :
      e.hom.hom.app U (e.inv.hom.app U z) = z := by
    have h := congrArg
      (fun k => (ConcreteCategory.hom (k.hom.app U)) z) e.inv_hom_id
    change (e.inv.hom.app U ≫ e.hom.hom.app U) z = z at h
    simpa only [CategoryTheory.comp_apply] using h
  have hx : x = e.hom.hom.app U PUnit.unit := by
    have : Subsingleton ((Sheaf.terminal X.J Types.isTerminalPUnit).obj.obj U) := by
      change Subsingleton PUnit
      infer_instance
    calc
      x = e.hom.hom.app U (e.inv.hom.app U x) := (hcomp x).symm
      _ = e.hom.hom.app U PUnit.unit := congrArg (e.hom.hom.app U) (Subsingleton.elim _ _)
  subst x
  have heta : e.hom = (terminalIsTerminal (C := Sheaf X.J (Type w))).from
      (Sheaf.terminal X.J Types.isTerminalPUnit) :=
    (terminalIsTerminal (C := Sheaf X.J (Type w))).hom_ext _ _
  rw [heta]
  rfl

/-- The direct image of sheaves of sets preserves binary products. -/
noncomputable def pushforwardProductIso
    {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    (f : RingedToposHom X Y)
    (M N : Sheaf X.J (Type w)) :
    f.toToposHom.pushforward.obj (M ⨯ N) ≅
      f.toToposHom.pushforward.obj M ⨯ f.toToposHom.pushforward.obj N := by
  have : f.toToposHom.pushforward.IsRightAdjoint := f.toToposHom.adj.isRightAdjoint
  exact asIso (Limits.prodComparison f.toToposHom.pushforward M N)

/-- The direct image of sheaves of sets preserves the terminal object. -/
noncomputable def pushforwardTerminalIso
    {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    (f : RingedToposHom X Y) :
    f.toToposHom.pushforward.obj (⊤_ (Sheaf X.J (Type w))) ≅
      ⊤_ (Sheaf Y.J (Type w')) := by
  have : f.toToposHom.pushforward.IsRightAdjoint := f.toToposHom.adj.isRightAdjoint
  exact asIso (Limits.terminalComparison f.toToposHom.pushforward)

/-- The first projection after `pushforwardProductIso` is the direct image of the first projection. -/
@[reassoc]
lemma pushforwardProductIso_hom_fst
    {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    (f : RingedToposHom X Y)
    (M N : Sheaf X.J (Type w)) :
    (pushforwardProductIso f M N).hom ≫ Limits.prod.fst =
      f.toToposHom.pushforward.map (Limits.prod.fst : M ⨯ N ⟶ M) := by
  simp [pushforwardProductIso]

/-- The second projection after `pushforwardProductIso` is the direct image of the second
projection. -/
@[reassoc]
lemma pushforwardProductIso_hom_snd
    {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    (f : RingedToposHom X Y)
    (M N : Sheaf X.J (Type w)) :
    (pushforwardProductIso f M N).hom ≫ Limits.prod.snd =
      f.toToposHom.pushforward.map (Limits.prod.snd : M ⨯ N ⟶ N) := by
  simp [pushforwardProductIso]

noncomputable def pushforwardMultiplicationMap
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) (i j : ℤ) :
    f.toToposHom.pushforward.obj (underlyingPiece A i) ⨯
      f.toToposHom.pushforward.obj (underlyingPiece A j) ⟶
        f.toToposHom.pushforward.obj (underlyingPiece A (i + j)) :=
  (pushforwardProductIso f (underlyingPiece A i) (underlyingPiece A j)).inv ≫
    f.toToposHom.pushforward.map (multiplicationSheafMap A i j)

/-- The underlying sheaf of sets of a direct image of sheaves of modules is the direct image of
the underlying sheaf of sets. -/
public noncomputable def pushedPieceUnderlyingIso
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    Stacks.underlyingModuleSheaf Y.J
      (f.pushforwardModules.obj M) ≅
        f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J M) := by
  exact
    f.pushforwardModulesUnderlyingIso.app M


noncomputable def pushedMultiplicationSheafMap
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) (i j : ℤ) :
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
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) (i j : ℤ)
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
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) :
    (⊤_ (Sheaf Y.J (Type u'))) ⟶
      f.toToposHom.pushforward.obj (underlyingPiece A 0) :=
  (pushforwardTerminalIso f).inv ≫
    f.toToposHom.pushforward.map (unitSheafMap A)

/-- **The unit of the direct image of a graded algebra**: the global degree-zero section
obtained from the unit of the source algebra through the terminal-object comparison of the
direct image. -/
@[no_expose] public noncomputable def pushforwardUnitSection
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) :
    (f.pushforwardModules.obj
      (A.piece 0)).sections :=
  sectionOfUnderlyingMap (X := Y) _
    (pushforwardUnitMap f A ≫
      f.pushforwardModulesUnderlyingIso.inv.app
        (A.piece 0))

private lemma moduleSectionSheafMap_pushforwardUnitSection
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O)) :
    moduleSectionSheafMap
        (f.pushforwardModules.obj
          (A.piece 0))
        (pushforwardUnitSection f A) =
      pushforwardUnitMap f A ≫
        f.pushforwardModulesUnderlyingIso.inv.app
          (A.piece 0) :=
  moduleSectionSheafMap_sectionOfUnderlyingMap (X := Y) _ _

lemma pushforwardUnitSection_eval
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (U : Y.Cᵒᵖ) (z : (⊤_ (Sheaf Y.J (Type u'))).obj.obj U) :
    (pushforwardUnitSection f A).eval U =
      (pushforwardUnitMap f A ≫
        f.pushforwardModulesUnderlyingIso.inv.app
          (A.piece 0)).hom.app U z := by
  exact congrArg (fun k => k.hom.app U z)
    (moduleSectionSheafMap_pushforwardUnitSection f A)

noncomputable def transportedMultiplicationMap
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite Y).O))
    (h : ∀ n, B.piece n =
      f.pushforwardModules.obj
        (A.piece n)) (i j : ℤ) :
    underlyingPiece B i ⨯ underlyingPiece B j ⟶ underlyingPiece B (i + j) :=
  Limits.prod.map (pieceComparison f A B h i).hom (pieceComparison f A B h j).hom ≫
    pushforwardMultiplicationMap f A i j ≫
    (pieceComparison f A B h (i + j)).inv

lemma transportedMultiplicationMap_comp_pieceComparison
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite Y).O))
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

private noncomputable def transportedUnitMap
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite Y).O))
    (h : ∀ n, B.piece n =
      f.pushforwardModules.obj
        (A.piece n)) :
    (⊤_ (Sheaf Y.J (Type u'))) ⟶ underlyingPiece B 0 :=
  pushforwardUnitMap f A ≫ (pieceComparison f A B h 0).inv

private lemma transportedUnitMap_comp_pieceComparison
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite X).O))
    (B : SheafOfModules.GradedAlgebra
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.ringedSite Y).O))
    (h : ∀ n, B.piece n =
      f.pushforwardModules.obj
        (A.piece n)) :
    transportedUnitMap f A B h ≫ (pieceComparison f A B h 0).hom =
      (pushforwardTerminalIso f).inv ≫
        f.toToposHom.pushforward.map (unitSheafMap A) := by
  simp [transportedUnitMap, pushforwardUnitMap, Category.assoc]

/-- **Local sections of a sheaf of sets are morphisms out of a sheafified Yoneda object.** A
section over `U` of a sheaf of sets is the same thing as a morphism to it from the
sheafification of the presheaf represented by `U`. -/
public noncomputable def sheafSectionEquiv
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (U : Cᵒᵖ) (M : Sheaf J (Type u)) :
    M.obj.obj U ≃ ((presheafToSheaf J (Type u)).obj (yoneda.obj U.unop) ⟶ M) :=
  yonedaEquiv.symm.trans ((sheafificationAdjunction J (Type u)).homEquiv _ _).symm

/-- The identification of local sections with morphisms out of a sheafified Yoneda object is
natural in the sheaf. -/
public lemma sheafSectionEquiv_comp
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (U : Cᵒᵖ) {M N : Sheaf J (Type u)} (morphism : M ⟶ N) (element : M.obj.obj U) :
    sheafSectionEquiv J U N (morphism.hom.app U element) =
      sheafSectionEquiv J U M element ≫ morphism := by
  dsimp [sheafSectionEquiv]
  rw [← yonedaEquiv_symm_naturality_right]
  exact (sheafificationAdjunction J (Type u)).homEquiv_naturality_right_symm _ _

/-- **Local sections of a direct image of sheaves of sets, transposed.** A section over `U` of
the direct image of a sheaf of sets is the same thing as a morphism to that sheaf from the
inverse image of the sheafified Yoneda object of `U`. -/
public noncomputable def transposedSectionEquiv
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y) (U : Y.Cᵒᵖ) (M : Sheaf X.J (Type u)) :
    (f.toToposHom.pushforward.obj M).obj.obj U ≃
      (f.toToposHom.inverseImage.obj
        ((presheafToSheaf Y.J (Type u')).obj (yoneda.obj U.unop)) ⟶ M) :=
  (sheafSectionEquiv Y.J U _).trans (f.toToposHom.adj.homEquiv _ _).symm

/-- The transposed identification of local sections of a direct image is natural in the
sheaf. -/
public lemma transposedSectionEquiv_comp
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y) (U : Y.Cᵒᵖ)
    {M N : Sheaf X.J (Type u)} (morphism : M ⟶ N)
    (element : (f.toToposHom.pushforward.obj M).obj.obj U) :
    transposedSectionEquiv f U N
      ((f.toToposHom.pushforward.map morphism).hom.app U element) =
        transposedSectionEquiv f U M element ≫ morphism := by
  dsimp [transposedSectionEquiv]
  rw [sheafSectionEquiv_comp, Adjunction.homEquiv_naturality_right_symm]

/-- **Local sections of a direct image of sheaves of modules, transposed.** A section over `U`
of the direct image of a sheaf of modules is the same thing as a morphism from the inverse image
of the sheafified Yoneda object of `U` to the underlying sheaf of sets of the module. -/
public noncomputable def pushedSectionEquiv
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) (U : Y.Cᵒᵖ) :
    (f.pushforwardModules.obj M).val.obj U ≃
      (f.toToposHom.inverseImage.obj
        ((presheafToSheaf Y.J (Type u')).obj (yoneda.obj U.unop)) ⟶
          Stacks.underlyingModuleSheaf X.J M) :=
  ((Functor.mapIso ((sheafToPresheaf Y.J (Type u')) ⋙
    (evaluation Y.Cᵒᵖ (Type u')).obj U) (pushedPieceUnderlyingIso f M)).toEquiv).trans
    (transposedSectionEquiv f U _)

end Stacks.Sheaves.GradedAlgebraPushforward
