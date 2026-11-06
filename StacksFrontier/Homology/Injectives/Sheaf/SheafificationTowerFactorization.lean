module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Presentable.OrthogonalReflection
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Factoring maps into the sheafification tower through earlier stages

Let `C` be a small category with a Grothendieck topology `J`, let `Ab(C) = Sheaf J AddCommGrpCat`
be the category of abelian sheaves on `C`, let `i : Ab(C) ⥤ PAb(C)` be the inclusion into abelian
presheaves and `(-)#` sheafification. Abelian presheaves have a functorial injective embedding; we
fix one, `E = canonicalEmbedding`. Transfinite iteration of `J₁ = (-)# ∘ E.func ∘ i`, with its
monomorphism `u : 𝟭 ⟶ J₁`, gives a tower of abelian sheaves `J_α(F)`, functorial in `F`, with
`J_0(F) = F`, `J_{α+1}(F) = J₁(J_α(F))`, `J_β(F) = colim_{α<β} J_α(F)` at limit stages, and
monomorphic transition maps `ι_{α,α'} : J_α(F) ⟶ J_{α'}(F)`.

For a set of abelian sheaves `{G_i}_{i ∈ I}` there is an ordinal `β` such that every morphism
`G_i ⟶ J_β(F)` factors through `J_α(F)` for some `α < β`. Moreover, for a monomorphism
`G₁ ⟶ G₂`, every morphism `G₁ ⟶ J_α(F)` followed by `ι_{α,α+1}` extends to `G₂`.

## Main definitions

* `FunctorialInjectiveEmbedding`: an endofunctor `func` with a natural monomorphism `𝟭 ⟶ func`
  whose values are injective.
* `canonicalEmbedding`: the fixed functorial injective embedding of abelian presheaves.
* `towerStage`: the tower `α ↦ J_α`, as a functor `Set.Iic β ⥤ (Ab(C) ⥤ Ab(C))`.
* `towerObj`, `towerIota`, `towerTop`: the stages `J_α(F)`, the transition maps `ι_{α,α'}` and
  the top stage `J_β(F)`.
* `TowerFactorsThrough`: a morphism into `J_{α'}(F)` factors through `J_α(F)`.

## Main results

* `exists_functorialInjectiveEmbedding_presheaf`: abelian presheaves on a small category have a
  functorial injective embedding.
* `mono_towerIota`: the transition maps of the tower are monomorphisms.
* `exists_extension_towerIota_succ`: the extension property of the successor step of the tower.
* `abSheaf_isCardinalPresentable`: every abelian sheaf is `κ`-presentable for some regular
  cardinal `κ`.
* `exists_ordinal_towerFactorsThrough`: morphisms from a set of abelian sheaves into `J_β(F)`
  factor through earlier stages.

## References

* [Stacks Project, Tag 01DN](https://stacks.math.columbia.edu/tag/01DN)
* [Stacks Project, Tag 01DM](https://stacks.math.columbia.edu/tag/01DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.SmallObject CategoryTheory.Limits

universe u

namespace Stacks.Injectives.SheafificationTowerFactorization

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The category of abelian sheaves `Ab(C) = Sheaf J AddCommGrpCat`. -/
abbrev AbSheaf := Sheaf J AddCommGrpCat.{u}

/-- `AbSheaf J` admits transfinite iterations indexed by `Set.Iic β`. -/
noncomputable instance abSheafIterIic (β : Ordinal.{u}) :
    HasIterationOfShape (Set.Iic β) (AbSheaf J) where

/-- The endofunctor category of `AbSheaf J` admits transfinite iterations indexed by
`Set.Iic β`. -/
noncomputable instance abSheafFunIterIic (β : Ordinal.{u}) :
    HasIterationOfShape (Set.Iic β) (AbSheaf J ⥤ AbSheaf J) :=
  instHasIterationOfShapeFunctor (Set.Iic β) (AbSheaf J) (AbSheaf J)

/-- `AbSheaf J` has coproducts indexed by any `I : Type u`, computed as the
sheafification of the presheaf coproduct. -/
noncomputable instance abSheafHasCoproducts (I : Type u) :
    HasColimitsOfShape (Discrete I) (AbSheaf J) :=
  haveI : HasColimitsOfShape (Discrete I) (Cᵒᵖ ⥤ AddCommGrpCat.{u}) := inferInstance
  ⟨fun F => HasColimit.mk
    ⟨Sheaf.sheafifyCocone (colimit.cocone (F ⋙ sheafToPresheaf J _)),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩


/-- The endofunctor `M ↦ (CharacterModule M → ℚ/ℤ)` of `AddCommGrpCat`, with
`ℚ/ℤ = AddCircle 1`. -/
private noncomputable def baseFunc : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj := fun M => AddCommGrpCat.of (CharacterModule (↑M : Type u) → AddCircle (1:ℚ))
  map := fun {M N} f => AddCommGrpCat.ofHom
    { toFun := fun x => fun ψ => x (ψ.comp (ConcreteCategory.hom f))
      map_zero' := by ext ψ; rfl
      map_add' := fun a b => by ext ψ; rfl }
  map_id := by
    intro M; apply AddCommGrpCat.hom_ext; ext x ψ; rfl
  map_comp := by
    intro M N K f g; apply AddCommGrpCat.hom_ext; ext x ψ; rfl

/-- The natural embedding `𝟭 ⟶ baseFunc`, `m ↦ (φ ↦ φ m)`. -/
private noncomputable def baseEmb : 𝟭 AddCommGrpCat.{u} ⟶ baseFunc where
  app := fun M => AddCommGrpCat.ofHom
    { toFun := fun m => fun φ => φ m
      map_zero' := by ext φ; simp
      map_add' := fun a b => by ext φ; simp }
  naturality := by
    intro M N f; apply AddCommGrpCat.hom_ext; ext m; rfl

/-- Each value `baseFunc.obj M` is injective. -/
private theorem baseInjective_obj (M : AddCommGrpCat.{u}) : Injective (baseFunc.obj M) := by
  have instInjQ : Module.Injective ℤ (AddCircle (1:ℚ)) :=
    Module.Baer.injective (Module.Baer.of_divisible (AddCircle (1:ℚ)))
  show Injective (AddCommGrpCat.of (CharacterModule (↑M : Type u) → AddCircle (1:ℚ)))
  rw [← AddCommGrpCat.injective_as_module_iff]
  exact Module.injective_object_of_injective_module ℤ _

/-- Each embedding component `baseEmb.app M` is a monomorphism. -/
private theorem baseMono_emb (M : AddCommGrpCat.{u}) : Mono (baseEmb.app M) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b hab
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hd
  apply hc
  have hcab := congrFun hab c
  change c a = c b at hcab
  rw [map_sub, hcab, sub_self]

/- Auxiliary constructions for the presheaf transport step. Given a
base functorial injective embedding `(I, η)` on `A`, we build the coinduced
embedding on `Cᵒᵖ ⥤ A` as the product over `c : Cᵒᵖ` of the right adjoints
`Rc c = evaluationRightAdjoint A c` applied to `I (G c)`. -/
namespace FunctorialInjectiveEmbeddingPresheaf

variable {C : Type u} [SmallCategory C] {A : Type (u + 1)} [Category.{u} A]
  [HasLimitsOfSize.{u, u} A]
variable (I : A ⥤ A) (η : 𝟭 A ⟶ I)

/-- Right adjoint of evaluation at `c`. -/
private noncomputable def Rc (c : Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A) := evaluationRightAdjoint A c
/-- Evaluation at `c`. -/
private noncomputable def evc (c : Cᵒᵖ) : (Cᵒᵖ ⥤ A) ⥤ A := (evaluation Cᵒᵖ A).obj c
/-- The adjunction `evc c ⊣ Rc c`. -/
private noncomputable def adjc (c : Cᵒᵖ) : evc (A:=A) c ⊣ Rc (A:=A) c := evaluationAdjunctionLeft A
    c
/-- One factor of the product functor: `evc c ⋙ I ⋙ Rc c`. -/
private noncomputable def Tc (c : Cᵒᵖ) : (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) := evc c ⋙ I ⋙ Rc c

private instance evcPresMono (c : Cᵒᵖ) : (evc (A := A) c).PreservesMonomorphisms := by
  unfold evc; infer_instance
private instance RcPresMono (c : Cᵒᵖ) : (Rc (A := A) c).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_adjunction (adjc (A:=A) c)

/-- The pointwise embedding `𝟭 ⟶ Tc c`, from the adjunction unit and `η`. -/
private noncomputable def embc (c : Cᵒᵖ) : 𝟭 (Cᵒᵖ ⥤ A) ⟶ Tc I c :=
  (adjc c).unit ≫ Functor.whiskerLeft (evc c) (Functor.whiskerRight η (Rc c))
/-- The transported endofunctor `func.obj G = ∏_c Rc c (I (G c))`. -/
private noncomputable def funcF : (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) := ∏ᶜ (fun c : Cᵒᵖ => Tc I c)
/-- The transported embedding `𝟭 ⟶ funcF`. -/
private noncomputable def embF : 𝟭 (Cᵒᵖ ⥤ A) ⟶ funcF I := Pi.lift (fun c => embc I η c)

/-- Each value `funcF.obj G` is injective. -/
private theorem injective_funcF_obj (hI : ∀ X, Injective (I.obj X)) (G : Cᵒᵖ ⥤ A) :
    Injective ((funcF I).obj G) := by
  have key : ∀ c, Injective ((Tc I c).obj G) := by
    intro c
    have h1 : Injective (I.obj ((evc c).obj G)) := hI _
    exact Injective.injective_of_adjoint (adjc (A := A) c) (I.obj ((evc c).obj G))
  have hprod : Injective (∏ᶜ (fun c : Cᵒᵖ => (Tc I c).obj G)) := Injective.instPiObj _
  exact Injective.of_iso (Limits.piObjIso (fun c : Cᵒᵖ => Tc I c) G).symm hprod

/-- Each embedding component `embF.app G` is a monomorphism. -/
private theorem mono_embF_app (hmono : ∀ X, Mono (η.app X)) (G : Cᵒᵖ ⥤ A) :
    Mono ((embF I η).app G) := by
  rw [NatTrans.mono_iff_mono_app]
  intro x
  have hlift : embF I η ≫ Pi.π (fun c : Cᵒᵖ => Tc I c) x = embc I η x :=
    Pi.lift_comp_π (fun c => embc I η c) x
  have hfac2 : ((embF I η).app G).app x ≫ ((Pi.π (fun c : Cᵒᵖ => Tc I c) x).app G).app x
      = ((embc I η x).app G).app x :=
    NatTrans.congr_app (NatTrans.congr_app hlift G) x
  have hrhs : Mono (((embc I η x).app G).app x) := by
    rw [show (embc I η x).app G = ((adjc x).unit.app G) ≫ (Rc x).map (η.app (G.obj x)) from rfl]
    rw [NatTrans.comp_app]
    refine @mono_comp _ _ _ _ _ _ ?_ _ ?_
    · have : IsSplitMono (((adjc (A:=A) x).unit.app G).app x) := by
        refine ⟨⟨((adjc (A:=A) x).counit.app ((evc x).obj G)), ?_⟩⟩
        show ((adjc (A:=A) x).unit.app G).app x ≫ _ = 𝟙 _
        rw [show ((adjc (A:=A) x).unit.app G).app x
              = (evc (A:=A) x).map ((adjc (A:=A) x).unit.app G) from rfl]
        exact (adjc (A:=A) x).left_triangle_components (X := G)
      infer_instance
    · have := hmono (G.obj x)
      have hm : Mono ((Rc (A:=A) x).map (η.app (G.obj x))) := Functor.map_mono _ _
      rw [NatTrans.mono_iff_mono_app] at hm
      exact hm x
  exact mono_of_mono_fac hfac2

end FunctorialInjectiveEmbeddingPresheaf

/-- A functorial injective embedding on a category `A` is a functor `func : A ⥤ A`
with a natural transformation `emb : 𝟭 A ⟶ func` such that each `func.obj X` is
injective and each `emb.app X` is a monomorphism. -/
structure FunctorialInjectiveEmbedding (A : Type*) [Category A] where
  /-- The endofunctor sending an object to an injective object containing it. -/
  func : A ⥤ A
  /-- The natural embedding `𝟭 A ⟶ func`. -/
  emb : 𝟭 A ⟶ func
  /-- Each value `func.obj X` is injective. -/
  injective_obj : ∀ X, Injective (func.obj X)
  /-- Each embedding component `emb.app X` is a monomorphism. -/
  mono_emb : ∀ X, Mono (emb.app X)

/-- The abelian category of abelian presheaves on a small category has a functorial injective
embedding. -/
theorem exists_functorialInjectiveEmbedding_presheaf :
    Nonempty (FunctorialInjectiveEmbedding (Cᵒᵖ ⥤ AddCommGrpCat.{u})) :=
  ⟨{
    func := FunctorialInjectiveEmbeddingPresheaf.funcF baseFunc
    emb := FunctorialInjectiveEmbeddingPresheaf.embF baseFunc baseEmb
    injective_obj := fun G =>
      FunctorialInjectiveEmbeddingPresheaf.injective_funcF_obj baseFunc baseInjective_obj G
    mono_emb := fun G =>
      FunctorialInjectiveEmbeddingPresheaf.mono_embF_app baseFunc baseEmb baseMono_emb G }⟩

/-- A fixed functorial injective embedding of abelian presheaves, from which the tower `J_•` is
built. -/
noncomputable def canonicalEmbedding :
    FunctorialInjectiveEmbedding (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (exists_functorialInjectiveEmbedding_presheaf (C := C)).some

/-- The endofunctor `J₁ = (-)# ∘ E.func ∘ i` of abelian sheaves, `F ↦ (E.func (iF))#`, for the
canonical embedding `E = canonicalEmbedding`. -/
noncomputable def jOne : AbSheaf J ⥤ AbSheaf J :=
  sheafToPresheaf J _ ⋙ (canonicalEmbedding (C := C)).func ⋙ presheafToSheaf J _

/-- The natural transformation `u : 𝟭 ⟹ J₁`: at an abelian sheaf `F`, the inverse of the counit
isomorphism `(iF)# ≅ F` followed by the sheafification of `E.emb : iF ⟶ E.func (iF)`. -/
noncomputable def uNat : 𝟭 (AbSheaf J) ⟶ jOne J :=
  inv (sheafificationAdjunction J AddCommGrpCat.{u}).counit ≫
    Functor.whiskerLeft (sheafToPresheaf J _)
      (Functor.whiskerRight (canonicalEmbedding (C := C)).emb (presheafToSheaf J _))

/-- The successor structure on the functor category `Ab(C) ⥤ Ab(C)` built from the
pointed endofunctor `u : 𝟭 ⟹ J₁`. Its transfinite iteration is the tower
`J_•`. -/
noncomputable def towerSucc : SuccStruct (AbSheaf J ⥤ AbSheaf J) :=
  SuccStruct.ofNatTrans (uNat J)

/-- The tower `J_•`: the transfinite iteration of `towerSucc`, as a functor
`Set.Iic β ⥤ (Ab(C) ⥤ Ab(C))`. The object `(towerStage β).obj α` is the stage endofunctor `J_α`,
and the action on morphisms gives the transition maps `ι_{α,α'} : J_α ⟹ J_{α'}`. -/
noncomputable def towerStage (β : Ordinal.{u}) :
    Set.Iic β ⥤ (AbSheaf J ⥤ AbSheaf J) :=
  (towerSucc J).iterationFunctor (Set.Iic β)

/-- `J_α(F)` for `α ≤ β`. -/
noncomputable def towerObj (β : Ordinal.{u}) (α : Set.Iic β) (F : AbSheaf J) :
    AbSheaf J :=
  ((towerStage J β).obj α).obj F

/-- The transition morphism `ι_{α,α'} : J_α(F) → J_{α'}(F)` for `α ≤ α'`. It is a
monomorphism (see `mono_towerIota`). -/
noncomputable def towerIota (β : Ordinal.{u}) {α α' : Set.Iic β} (h : α ≤ α')
    (F : AbSheaf J) : towerObj J β α F ⟶ towerObj J β α' F :=
  ((towerStage J β).map (homOfLE h)).app F

/-- `J_β(F)`, the top stage. -/
noncomputable def towerTop (β : Ordinal.{u}) (F : AbSheaf J) : AbSheaf J :=
  towerObj J β ⟨β, le_refl β⟩ F

/-- Functoriality of the stage `J_α` in the sheaf `F`: the induced morphism
`J_α(F) → J_α(F')` for `f : F → F'`. -/
noncomputable def towerMapF (β : Ordinal.{u}) (α : Set.Iic β) {F F' : AbSheaf J}
    (f : F ⟶ F') : towerObj J β α F ⟶ towerObj J β α F' :=
  ((towerStage J β).obj α).map f

/-- `φ : G → J_{α'}(F)` factors through `J_α(F)` (for `α ≤ α'`) if there is
`ψ : G → J_α(F)` with `φ = ψ ≫ ι_{α,α'}`. -/
def TowerFactorsThrough (β : Ordinal.{u}) {α α' : Set.Iic β} (h : α ≤ α')
    (F G : AbSheaf J) (φ : G ⟶ towerObj J β α' F) : Prop :=
  ∃ ψ : G ⟶ towerObj J β α F, φ = ψ ≫ towerIota J β h F

/-- **Zero step.** `J_0 ≅ 𝟭` (so `J_0(F) ≅ F`), naturally in `F`. -/
noncomputable def towerStage_obj_bot (β : Ordinal.{u}) :
    (towerStage J β).obj ⊥ ≅ 𝟭 (AbSheaf J) :=
  (towerSucc J).iterationFunctorObjBotIso (Set.Iic β)

/-- **Successor step.** `J_{α+1} ≅ J_α ⋙ J₁`. -/
noncomputable def towerStage_obj_succ (β : Ordinal.{u}) (α : Set.Iic β)
    (hα : ¬ IsMax α) :
    (towerStage J β).obj (Order.succ α) ≅ (towerStage J β).obj α ⋙ jOne J :=
  (towerSucc J).iterationFunctorObjSuccIso α hα

/-- **Successor transition map.** The transition `J_α → J_{α+1}` is the canonical
map `u` (i.e. `toSucc`, modulo the successor isomorphism). -/
theorem towerStage_map_succ (β : Ordinal.{u}) (α : Set.Iic β) (hα : ¬ IsMax α) :
    (towerStage J β).map (homOfLE (Order.le_succ α)) =
      (towerSucc J).toSucc ((towerStage J β).obj α) ≫
        ((towerSucc J).iterationFunctorObjSuccIso α hα).inv :=
  (towerSucc J).iterationFunctor_map_succ α hα

/-- **Limit step (functor-category level).** At limit stages the tower is the
colimit of the earlier stages (well-order-continuity). -/
theorem towerStage_isWellOrderContinuous (β : Ordinal.{u}) :
    (towerStage J β).IsWellOrderContinuous := by
  unfold towerStage
  infer_instance

/-- **Limit step (per-sheaf level).** For a fixed abelian sheaf `F` and a limit stage `m ≤ β`,
the value `J_m(F)` is the colimit of the earlier stages `J_α(F)` for `α < m`, i.e.
`J_m(F) = colim_{α < m} J_α(F)` in `Ab(C)`. -/
noncomputable def towerObj_isColimit_of_isSuccLimit (β : Ordinal.{u})
    (m : Set.Iic β) (hm : Order.IsSuccLimit m) (F : AbSheaf J) :
    IsColimit (((CategoryTheory.evaluation (AbSheaf J) (AbSheaf J)).obj F).mapCocone
      ((Set.principalSegIio m).cocone (towerStage J β))) :=
  haveI := towerStage_isWellOrderContinuous J β
  isColimitOfPreserves ((CategoryTheory.evaluation (AbSheaf J) (AbSheaf J)).obj F)
    ((towerStage J β).isColimitOfIsWellOrderContinuous m hm)

/-- Each component of `u` is a monomorphism. -/
theorem mono_uNat_app (F : AbSheaf J) : Mono ((uNat J).app F) := by
  have h1 : Mono ((inv (sheafificationAdjunction J AddCommGrpCat.{u}).counit).app F) :=
    inferInstance
  have : Mono ((canonicalEmbedding (C := C)).emb.app
      ((sheafToPresheaf J AddCommGrpCat.{u}).obj F)) :=
    (canonicalEmbedding (C := C)).mono_emb _
  have : (presheafToSheaf J AddCommGrpCat.{u}).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape (presheafToSheaf J AddCommGrpCat)
  have h2 : Mono ((presheafToSheaf J AddCommGrpCat.{u}).map
      ((canonicalEmbedding (C := C)).emb.app
        ((sheafToPresheaf J AddCommGrpCat.{u}).obj F))) :=
    Functor.map_mono _ _
  exact @mono_comp _ _ _ _ _ _ h1 _ h2

open MorphismProperty in
/-- In `AbSheaf J`, monomorphisms are stable under transfinite composition of shape `K`, for any
`u`-small well-ordered `K : Type (u + 1)`. -/
theorem mono_stableOfShape (K : Type (u + 1)) [LinearOrder K] [SuccOrder K] [OrderBot K]
    [WellFoundedLT K] [Small.{u} K] :
    (monomorphisms (AbSheaf J)).IsStableUnderTransfiniteCompositionOfShape K := by
  have : @IsStableUnderTransfiniteComposition.{u, u, u+1} (AbSheaf J) _
      (monomorphisms (AbSheaf J)) :=
    IsGrothendieckAbelian.instIsStableUnderTransfiniteCompositionMonomorphisms
  rw [isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso (monomorphisms (AbSheaf J))
    (orderIsoShrink.{u} K)]
  infer_instance

open MorphismProperty in
/-- Each transition map `ι_{α,α'} : J_α(F) → J_{α'}(F)` is a monomorphism. -/
theorem mono_towerIota (β : Ordinal.{u}) {α α' : Set.Iic β} (h : α ≤ α')
    (F : AbSheaf J) : Mono (towerIota J β h F) := by
  unfold towerIota towerObj towerStage
  set E := (evaluation (AbSheaf J) (AbSheaf J)).obj F with hE
  have : PreservesColimitsOfShape (Set.Iic β) E := inferInstance
  have : PreservesWellOrderContinuousOfShape (Set.Iic β) E := ⟨fun _ _ => inferInstance⟩
  have hle : (towerSucc J).prop ≤ (monomorphisms (AbSheaf J)).inverseImage E := by
    rw [towerSucc, SuccStruct.prop, ofHoms_le_iff]
    intro G0
    show Mono (E.map (SuccStruct.toSucc _ G0))
    rw [hE, evaluation_obj_map, SuccStruct.ofNatTrans_toSucc]
    show Mono ((uNat J).app (G0.obj F))
    exact mono_uNat_app J (G0.obj F)
  have := mono_stableOfShape J (↑(Set.Ici (⟨α, leOfHom (homOfLE h)⟩ : Set.Iic α')))
  -- Push the iteration's transfinite-composition structure through `E` and read off
  -- the transition map `α ⟶ α'` (replicating `TransfiniteCompositionOfShape.mem_map`,
  -- which we cannot invoke directly because the shape `Set.Iic β` lives in `Type (u+1)`
  -- while the Grothendieck stability instance is at universe `u`).
  have hmono : (monomorphisms (AbSheaf J))
      (((((towerSucc J).transfiniteCompositionOfShapeιIteration (Set.Iic β)).ofLE hle).map
        (F := E)).F.map (homOfLE h)) :=
    (monomorphisms (AbSheaf J)).transfiniteCompositionsOfShape_le _ _
      (((((((towerSucc J).transfiniteCompositionOfShapeιIteration (Set.Iic β)).ofLE hle).map
        (F := E)).iic α').ici ⟨α, leOfHom (homOfLE h)⟩).mem)
  rw [monomorphisms.iff] at hmono
  exact hmono

/-- Let `adj : L ⊣ R` be an adjunction whose counit is invertible, so that `c⁻¹ : 𝟭 ⟹ R ⋙ L`
is available. Let `ι : G₁ ⟶ G₂` be a morphism with `R.map ι` a monomorphism, let `φ : G₁ ⟶ H`, and
let `e : R.obj H ⟶ P` have an injective object `P` as target. Then `φ` extends along `ι` after
composing with `c⁻¹_H ≫ L.map e : H ⟶ L.obj P`. -/
private theorem exists_extension_of_injective {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [IsIso adj.counit] {G₁ G₂ H : B} {P : A}
    [Injective P] (ι : G₁ ⟶ G₂) [Mono (R.map ι)] (φ : G₁ ⟶ H) (e : R.obj H ⟶ P) :
    ∃ g : G₂ ⟶ L.obj P, ι ≫ g = φ ≫ ((inv adj.counit).app H ≫ L.map e) := by
  obtain ⟨k, hk⟩ := Injective.factors (R.map φ ≫ e) (R.map ι)
  refine ⟨(inv adj.counit).app G₂ ≫ L.map k, ?_⟩
  calc ι ≫ ((inv adj.counit).app G₂ ≫ L.map k)
      = (ι ≫ (inv adj.counit).app G₂) ≫ L.map k := (Category.assoc _ _ _).symm
    _ = ((inv adj.counit).app G₁ ≫ L.map (R.map ι)) ≫ L.map k :=
          congrArg (· ≫ L.map k) ((inv adj.counit).naturality ι)
    _ = (inv adj.counit).app G₁ ≫ (L.map (R.map ι) ≫ L.map k) := Category.assoc _ _ _
    _ = (inv adj.counit).app G₁ ≫ L.map (R.map ι ≫ k) :=
          congrArg ((inv adj.counit).app G₁ ≫ ·) (L.map_comp _ _).symm
    _ = (inv adj.counit).app G₁ ≫ L.map (R.map φ ≫ e) :=
          congrArg (fun x => (inv adj.counit).app G₁ ≫ L.map x) hk
    _ = (inv adj.counit).app G₁ ≫ (L.map (R.map φ) ≫ L.map e) :=
          congrArg ((inv adj.counit).app G₁ ≫ ·) (L.map_comp _ _)
    _ = ((inv adj.counit).app G₁ ≫ L.map (R.map φ)) ≫ L.map e := (Category.assoc _ _ _).symm
    _ = (φ ≫ (inv adj.counit).app H) ≫ L.map e :=
          congrArg (· ≫ L.map e) ((inv adj.counit).naturality φ).symm
    _ = φ ≫ ((inv adj.counit).app H ≫ L.map e) := Category.assoc _ _ _

/-- Let `ι : G₁ ⟶ G₂` be a monomorphism of abelian sheaves, `H` an abelian sheaf, and
`f : G₁ ⟶ H` any morphism. Then `f` extends along `ι` after composing with the canonical map
`u_H : H ⟶ J₁(H)`: there is `g : G₂ ⟶ J₁(H)` with `ι ≫ g = f ≫ u_H`. -/
theorem exists_extension_uNat (H : AbSheaf J) {G₁ G₂ : AbSheaf J} (ι : G₁ ⟶ G₂) [Mono ι]
    (f : G₁ ⟶ H) :
    ∃ g : G₂ ⟶ (jOne J).obj H, ι ≫ g = f ≫ (uNat J).app H := by
  have hmono : Mono ((sheafToPresheaf J AddCommGrpCat.{u}).map ι) := inferInstance
  have hinj : Injective ((canonicalEmbedding (C := C)).func.obj
      ((sheafToPresheaf J AddCommGrpCat.{u}).obj H)) :=
    (canonicalEmbedding (C := C)).injective_obj _
  exact exists_extension_of_injective (sheafificationAdjunction J AddCommGrpCat.{u}) ι f
    ((canonicalEmbedding (C := C)).emb.app ((sheafToPresheaf J AddCommGrpCat.{u}).obj H))

/-- Let `F` be an abelian sheaf and `α ≤ β` a non-maximal stage of the tower, so that
`α + 1 ≤ β` as well. Let `ι : G₁ ⟶ G₂` be an injective (i.e. monomorphic) map of abelian sheaves
and let `f : G₁ ⟶ J_α(F)` be a morphism. Then there is a morphism `g : G₂ ⟶ J_{α+1}(F)` making
the square with the transition map `ι_{α,α+1} : J_α(F) ⟶ J_{α+1}(F)` commute, i.e.
`ι ≫ g = f ≫ ι_{α,α+1}`. -/
@[stacks 01DM]
theorem exists_extension_towerIota_succ (β : Ordinal.{u}) (α : Set.Iic β) (hα : ¬ IsMax α)
    (F : AbSheaf J) {G₁ G₂ : AbSheaf J} (ι : G₁ ⟶ G₂) [Mono ι]
    (f : G₁ ⟶ towerObj J β α F) :
    ∃ g : G₂ ⟶ towerObj J β (Order.succ α) F,
      ι ≫ g = f ≫ towerIota J β (Order.le_succ α) F := by
  obtain ⟨g₀, hg₀⟩ := exists_extension_uNat J (towerObj J β α F) ι f
  have hiota : towerIota J β (Order.le_succ α) F =
      (uNat J).app (towerObj J β α F) ≫ ((towerStage_obj_succ J β α hα).inv).app F :=
    NatTrans.congr_app (towerStage_map_succ J β α hα) F
  refine ⟨g₀ ≫ ((towerStage_obj_succ J β α hα).inv).app F, ?_⟩
  rw [hiota]
  calc ι ≫ (g₀ ≫ ((towerStage_obj_succ J β α hα).inv).app F)
      = (ι ≫ g₀) ≫ ((towerStage_obj_succ J β α hα).inv).app F := (Category.assoc _ _ _).symm
    _ = (f ≫ (uNat J).app (towerObj J β α F)) ≫
          ((towerStage_obj_succ J β α hα).inv).app F :=
          congrArg (· ≫ ((towerStage_obj_succ J β α hα).inv).app F) hg₀
    _ = f ≫ ((uNat J).app (towerObj J β α F) ≫
          ((towerStage_obj_succ J β α hα).inv).app F) := Category.assoc _ _ _

/-! ### Factoring through an earlier stage -/

/-- If `T : Set.Iic β ⥤ Type u` is a diagram of sets whose value at the top `β` is the colimit
of the strictly earlier stages (`hcolim`), and `β` has cofinality strictly larger than `#S`, then
any function `f : S → T(β)` lifts through some earlier stage: there are `α < β` and
`g : S → T(α)` with `T(α ≤ β) ∘ g = f`. -/
theorem factor_set_map_through_stage_of_lt_cof
    (β : Ordinal.{u})
    (T : Set.Iic β ⥤ Type u)
    (hcolim : IsColimit ((Set.principalSegIio (⟨β, le_refl β⟩ : Set.Iic β)
      |>.cocone T)))
    {S : Type u} (hcard : Cardinal.mk S < β.cof) (f : S → T.obj ⟨β, le_refl β⟩) :
    ∃ (α : Set.Iic β) (h : (α : Ordinal) < β) (g : S → T.obj α),
      (T.map (homOfLE (le_of_lt (show α < (⟨β, le_refl β⟩ : Set.Iic β) from h)))) ∘ g = f := by
  classical
  have hsurj : ∀ s : S, ∃ (k : Set.Iio (⟨β, le_refl β⟩ : Set.Iic β))
      (z : T.obj (k : Set.Iic β)),
      T.map (homOfLE (le_of_lt (Set.mem_Iio.mp k.2))) z = f s := by
    intro s
    obtain ⟨k, z, hz⟩ := Types.jointly_surjective _ hcolim (f s)
    rw [PrincipalSeg.cocone_ι_app] at hz
    exact ⟨k, z, hz⟩
  choose j y hy using hsurj
  have hlt : ∀ s, ((j s).1 : Ordinal) < β := fun s => (j s).2
  set μ : Ordinal.{u} := ⨆ s, ((j s).1 : Ordinal) with hμ
  have hμβ : μ < β := Ordinal.iSup_lt_of_lt_cof hcard hlt
  have hle : ∀ s, (j s).1 ≤ (⟨μ, le_of_lt hμβ⟩ : Set.Iic β) := by
    intro s
    show ((j s).1 : Ordinal) ≤ μ
    exact Ordinal.le_iSup _ s
  refine ⟨⟨μ, le_of_lt hμβ⟩, hμβ, fun s => T.map (homOfLE (hle s)) (y s), ?_⟩
  funext s
  simp only [Function.comp_apply]
  rw [← Functor.map_comp_apply]
  exact hy s

/-- `AddCommGrpCat.{u}` is `κ`-locally presentable for every regular cardinal `κ`. -/
@[sga "4 I 2.3.2" "more general"]
theorem addCommGrpCat_isCardinalLocallyPresentable_forall
    (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsCardinalLocallyPresentable AddCommGrpCat.{u} κ := by
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  refine ⟨ObjectProperty.singleton (AddCommGrpCat.of (ULift.{u} ℤ)), inferInstance, ?_, ?_⟩
  · have hsep : IsSeparator (AddCommGrpCat.of (ULift.{u} ℤ)) := by
      rw [isSeparator_iff_faithful_coyoneda_obj]
      exact Functor.Faithful.of_iso AddCommGrpCat.coyonedaObjIsoForget.symm
    rw [ObjectProperty.isStrongGenerator_iff]
    refine ⟨hsep, ?_⟩
    intro X Y i hi hsurj
    have hepi : Epi i := by
      rw [Preadditive.epi_iff_cancel_zero]
      intro Z g hg
      apply (isSeparator_def _).mp hsep
      intro h
      obtain ⟨h', rfl⟩ := hsurj _ ((ObjectProperty.singleton_iff _ _).mpr rfl) h
      simp [Category.assoc, hg]
    exact isIso_of_mono_of_epi i
  · intro X hX
    obtain rfl := (ObjectProperty.singleton_iff _ _).mp hX
    rw [isCardinalPresentable_iff,
      isCardinalPresentable_iff_isCardinalAccessible_coyoneda_obj]
    apply Functor.IsCardinalAccessible.mk
    intro J _ _
    have : PreservesColimitsOfShape J (forget AddCommGrpCat.{u}) := by
      have hpf := AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits.{u}
      have hfil : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
      exact hpf.preserves_filtered_colimits J
    exact preservesColimitsOfShape_of_natIso AddCommGrpCat.coyonedaObjIsoForget.symm

/-- `AddCommGrpCat.{u}` is `κ`-locally presentable for some regular cardinal `κ`. -/
theorem addCommGrpCat_isCardinalLocallyPresentable :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular),
      IsCardinalLocallyPresentable AddCommGrpCat.{u} κ := by
  have : Fact (Cardinal.aleph0.{u}).IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  exact ⟨Cardinal.aleph0.{u}, ⟨Cardinal.isRegular_aleph0⟩,
    addCommGrpCat_isCardinalLocallyPresentable_forall Cardinal.aleph0.{u}⟩

/-- The sectionwise free-abelian-group (linearization) functor on type-valued presheaves,
obtained by postcomposing with `AddCommGrpCat.free`. -/
noncomputable abbrev freePresheaf :
    (Cᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free

/-- The small generating family `W₀` for the abelian sheaf condition: the free abelian
group on the (linearized) covering-sieve inclusions, indexed by the `u`-small set of pairs
`(X, S)` with `S ∈ J X`. -/
noncomputable def smallGeneratingFamily : MorphismProperty (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  MorphismProperty.ofHoms (fun i : (Σ X : C, {S : Sieve X // S ∈ J X}) =>
    (freePresheaf (C := C)).map (Sieve.shrinkFunctor.{u, u, u} i.2.1).ι)

/-- `smallGeneratingFamily` is `u`-small (it is an `ofHoms` over a `u`-small index). -/
theorem smallGeneratingFamily_isSmall :
    MorphismProperty.IsSmall.{u} (smallGeneratingFamily J) :=
  MorphismProperty.isSmall_ofHoms _

/-- An abelian presheaf is `J.W`-local if and only if it is a sheaf. -/
theorem isLocal_JW_iff_isSheaf (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (J.W (A := AddCommGrpCat.{u})).isLocal F ↔ Presheaf.IsSheaf J F := by
  have hsheaf : ∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{u}, Presheaf.IsSheaf J G →
      (J.W (A := AddCommGrpCat.{u})).isLocal G := fun G hG => by
    rw [GrothendieckTopology.W_eq_isLocal_range_sheafToPresheaf_obj J AddCommGrpCat.{u}]
    exact ObjectProperty.le_isLocal_isLocal _ G ⟨⟨G, hG⟩, rfl⟩
  refine ⟨fun h0 => ?_, hsheaf F⟩
  set adj := sheafificationAdjunction J AddCommGrpCat.{u}
  have hiso : IsIso (adj.unit.app F) :=
    (ObjectProperty.isLocal_iff_isIso _ _ h0 (hsheaf _ ((presheafToSheaf J _).obj F).property)).1
      (MorphismProperty.le_isLocal_isLocal _ _ (J.W_adj_unit_app adj F))
  exact (Presheaf.isSheaf_of_iso_iff (asIso (adj.unit.app F))).mpr
    ((presheafToSheaf J AddCommGrpCat.{u}).obj F).property

/-- An abelian presheaf is local for `smallGeneratingFamily J` if and only if it is a sheaf. -/
theorem smallGeneratingFamily_isLocal_iff_isSheaf (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (smallGeneratingFamily J).isLocal F ↔ Presheaf.IsSheaf J F := by
  let adjP : (freePresheaf (C := C)) ⊣
      (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj (forget AddCommGrpCat.{u}) :=
    Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj
  have transfer : ∀ {A B : Cᵒᵖ ⥤ Type u} (ι : A ⟶ B),
      Function.Bijective (fun g : (freePresheaf (C := C)).obj B ⟶ F =>
          (freePresheaf (C := C)).map ι ≫ g)
      ↔ Function.Bijective (fun h : B ⟶ (F ⋙ forget AddCommGrpCat.{u}) => ι ≫ h) := by
    intro A B ι
    set e1 := adjP.homEquiv B F with he1
    set e2 := adjP.homEquiv A F with he2
    have hcomp : (fun g : (freePresheaf (C := C)).obj B ⟶ F => (freePresheaf (C := C)).map ι ≫ g)
        = e2.symm ∘ (fun h : B ⟶ (F ⋙ forget AddCommGrpCat.{u}) => ι ≫ h) ∘ e1 := by
      funext g
      simp only [Function.comp_apply]
      rw [← adjP.homEquiv_naturality_left ι g, Equiv.symm_apply_apply]
    rw [hcomp, Equiv.comp_bijective]
    exact Equiv.bijective_comp e1 _
  rw [Presheaf.isSheaf_iff_isSheaf_forget J F (forget AddCommGrpCat.{u}),
    isSheaf_iff_isSheaf_of_type, MorphismProperty.isLocal_iff]
  constructor
  · intro h X S hS
    have hmem : smallGeneratingFamily J
        ((freePresheaf (C := C)).map (Sieve.shrinkFunctor.{u,u,u} S).ι) :=
      MorphismProperty.ofHoms.mk (⟨X, ⟨S, hS⟩⟩ : (Σ X : C, {S : Sieve X // S ∈ J X}))
    have hbij := h _ hmem
    rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp,
      ← transfer (Sieve.shrinkFunctor.{u,u,u} S).ι]
    exact hbij
  · intro h _ _ m hm
    obtain ⟨i⟩ := hm
    rw [transfer (Sieve.shrinkFunctor.{u,u,u} i.2.1).ι,
      ← Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
    exact h i.2.1 i.2.2

/-- There is a `u`-small morphism property of abelian presheaves with the same local objects as
`J.W`. -/
theorem exists_smallGenerating_isLocal_eq :
    ∃ (W₀ : MorphismProperty (Cᵒᵖ ⥤ AddCommGrpCat.{u})),
      MorphismProperty.IsSmall.{u} W₀ ∧ W₀.isLocal = (J.W (A := AddCommGrpCat.{u})).isLocal := by
  refine ⟨smallGeneratingFamily J, smallGeneratingFamily_isSmall J, ?_⟩
  funext F
  exact propext ((smallGeneratingFamily_isLocal_iff_isSheaf J F).trans
    (isLocal_JW_iff_isSheaf J F).symm)

/-- For a `u`-small morphism property `W₀` of abelian presheaves there is a regular cardinal `κ`
for which the source and the target of every `W₀`-morphism are `κ`-presentable. -/
theorem exists_regular_isCardinalPresentable_endpoints
    (W₀ : MorphismProperty (Cᵒᵖ ⥤ AddCommGrpCat.{u})) (hsmall : MorphismProperty.IsSmall.{u} W₀) :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular),
      ∀ ⦃X Y : Cᵒᵖ ⥤ AddCommGrpCat.{u}⦄ (f : X ⟶ Y), W₀ f →
        IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ := by
  have : Fact (Cardinal.aleph0.{u}).IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have : IsCardinalLocallyPresentable AddCommGrpCat.{u} Cardinal.aleph0.{u} :=
    addCommGrpCat_isCardinalLocallyPresentable_forall Cardinal.aleph0.{u}
  have : IsCardinalLocallyPresentable (Cᵒᵖ ⥤ AddCommGrpCat.{u}) Cardinal.aleph0.{u} :=
    Presheaf.instIsCardinalLocallyPresentableFunctorOppositeOfHasPullbacks
      Cardinal.aleph0.{u} C
  have : IsLocallyPresentable (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    ⟨⟨Cardinal.aleph0.{u}, ⟨Cardinal.isRegular_aleph0⟩, inferInstance⟩⟩
  have : IsAccessibleCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    instIsAccessibleCategoryOfIsLocallyPresentable _
  have hpres_obj : ∀ X : Cᵒᵖ ⥤ AddCommGrpCat.{u},
      ∃ (κ : Cardinal.{u}), ∃ (_ : Fact κ.IsRegular), IsCardinalPresentable X κ :=
    fun X => (instIsPresentableOfIsAccessibleCategory _ X).exists_cardinal
  choose κfun κreg κpres using hpres_obj
  have hsm : Small.{u} ↑W₀.toSet := hsmall.small_toSet
  set g : ↑W₀.toSet → Cardinal.{u} :=
    fun a => max (κfun a.1.left) (κfun a.1.right) with hg
  have hbdd : BddAbove (Set.range g) := Cardinal.bddAbove_of_small
  set s : Cardinal.{u} := ⨆ a, g a with hs
  set κ : Cardinal.{u} := Order.succ (max Cardinal.aleph0.{u} s) with hκdef
  have hκreg : Fact κ.IsRegular := ⟨Cardinal.isRegular_succ (le_max_left _ _)⟩
  refine ⟨κ, hκreg, ?_⟩
  intro X Y f hf
  have hmem : Arrow.mk f ∈ W₀.toSet := hf
  set a : ↑W₀.toSet := ⟨Arrow.mk f, hmem⟩ with ha
  have hgle : g a ≤ κ :=
    (le_ciSup hbdd a).trans ((le_max_right _ _).trans (Order.le_succ _))
  have hXle : κfun X ≤ κ := (le_max_left _ _ : κfun (Arrow.mk f).left ≤ g a).trans hgle
  have hYle : κfun Y ≤ κ := (le_max_right _ _ : κfun (Arrow.mk f).right ≤ g a).trans hgle
  have := κreg X
  have := κreg Y
  have := κpres X
  have := κpres Y
  exact ⟨isCardinalPresentable_of_le X hXle, isCardinalPresentable_of_le Y hYle⟩

/-- There is a regular cardinal `κ` for which the inclusion `J.W.isLocal.ι` of the `J.W`-local
abelian presheaves is `κ`-accessible. -/
theorem exists_isCardinalAccessible_isLocal_ι :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular),
      (J.W (A := AddCommGrpCat.{u})).isLocal.ι.IsCardinalAccessible κ := by
  obtain ⟨W₀, hsmall, hWloc⟩ := exists_smallGenerating_isLocal_eq.{u} J
  obtain ⟨κ, hκ, hpres⟩ := exists_regular_isCardinalPresentable_endpoints.{u} W₀ hsmall
  have := hκ
  refine ⟨κ, hκ, ?_⟩
  rw [← hWloc]
  exact MorphismProperty.isCardinalAccessible_ι_isLocal W₀ κ hpres

/-- If the inclusion `J.W.isLocal.ι` of the `J.W`-local abelian presheaves is `κ`-accessible,
then so is `sheafToPresheaf J AddCommGrpCat`. -/
theorem sheafToPresheaf_isCardinalAccessible_of_isLocal_ι
    (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (h : (J.W (A := AddCommGrpCat.{u})).isLocal.ι.IsCardinalAccessible κ) :
    (sheafToPresheaf J AddCommGrpCat.{u}).IsCardinalAccessible κ := by
  refine Functor.IsCardinalAccessible.mk (fun K _ _ => ?_)
  have hpc := h.preservesColimitOfShape (J := K)
  have hF : ∀ X : AbSheaf J, (J.W (A := AddCommGrpCat.{u})).isLocal
      ((sheafToPresheaf J AddCommGrpCat.{u}).obj X) :=
    fun X => (isLocal_JW_iff_isSheaf J _).2 X.property
  set L := (J.W (A := AddCommGrpCat.{u})).isLocal.lift (sheafToPresheaf J AddCommGrpCat.{u}) hF
      with hL
  have e : L ⋙ (J.W (A := AddCommGrpCat.{u})).isLocal.ι ≅ sheafToPresheaf J AddCommGrpCat.{u} :=
    (J.W (A := AddCommGrpCat.{u})).isLocal.liftCompιIso (sheafToPresheaf J AddCommGrpCat.{u}) hF
  have : (L ⋙ (J.W (A := AddCommGrpCat.{u})).isLocal.ι).Full := Functor.Full.of_iso e.symm
  have : (L ⋙ (J.W (A := AddCommGrpCat.{u})).isLocal.ι).Faithful := Functor.Faithful.of_iso e.symm
  have : L.Faithful := Functor.Faithful.of_comp L (J.W (A := AddCommGrpCat.{u})).isLocal.ι
  have : L.Full := Functor.Full.of_comp_faithful L (J.W (A := AddCommGrpCat.{u})).isLocal.ι
  have : L.EssSurj := by
    refine ⟨fun Y => ?_⟩
    set adj := sheafificationAdjunction J AddCommGrpCat.{u}
    have hiso : IsIso (adj.unit.app Y.obj) :=
      (ObjectProperty.isLocal_iff_isIso _ _ Y.2 (hF _)).1
        (MorphismProperty.le_isLocal_isLocal _ _ (J.W_adj_unit_app adj Y.obj))
    exact ⟨_, ⟨(J.W (A := AddCommGrpCat.{u})).isLocal.ι.preimageIso
      (asIso (adj.unit.app Y.obj)).symm⟩⟩
  have : L.IsEquivalence := Functor.IsEquivalence.mk
  have : PreservesColimitsOfShape K L := inferInstance
  have : PreservesColimitsOfShape K (L ⋙ (J.W (A := AddCommGrpCat.{u})).isLocal.ι) := inferInstance
  exact preservesColimitsOfShape_of_natIso e

/-- There is a regular cardinal `κ` for which the inclusion of abelian sheaves into abelian
presheaves is `κ`-accessible. -/
theorem sheafToPresheaf_exists_isCardinalAccessible :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular),
      (sheafToPresheaf J AddCommGrpCat.{u}).IsCardinalAccessible κ := by
  obtain ⟨κ, hκ, h⟩ := exists_isCardinalAccessible_isLocal_ι.{u} J
  have := hκ
  exact ⟨κ, hκ, sheafToPresheaf_isCardinalAccessible_of_isLocal_ι J κ h⟩

/-- There is a regular cardinal `κ` such that `AddCommGrpCat` is `κ`-locally presentable and
the inclusion `sheafToPresheaf J AddCommGrpCat` is `κ`-accessible, i.e. preserves `κ`-filtered
colimits. -/
theorem sheafToPresheaf_isCardinalAccessible :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular),
      IsCardinalLocallyPresentable AddCommGrpCat.{u} κ ∧
        (sheafToPresheaf J AddCommGrpCat.{u}).IsCardinalAccessible κ := by
  obtain ⟨κ, hκ, hacc⟩ := sheafToPresheaf_exists_isCardinalAccessible.{u} J
  have := hκ
  exact ⟨κ, hκ, addCommGrpCat_isCardinalLocallyPresentable_forall κ, hacc⟩

/-- Every abelian sheaf `G₀` is `κ`-presentable for some regular cardinal `κ`. -/
theorem abSheaf_isCardinalPresentable (G₀ : AbSheaf J) :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular), IsCardinalPresentable G₀ κ := by
  obtain ⟨κ, hκ, hlp, hacc⟩ := sheafToPresheaf_isCardinalAccessible.{u} J
  have := hκ
  have := hlp
  have := hacc
  have hpsh : IsCardinalLocallyPresentable (Cᵒᵖ ⥤ AddCommGrpCat.{u}) κ :=
    Presheaf.instIsCardinalLocallyPresentableFunctorOppositeOfHasPullbacks κ C
  have hsh : IsCardinalLocallyPresentable (Sheaf J AddCommGrpCat.{u}) κ :=
    (sheafificationAdjunction J AddCommGrpCat.{u}).isCardinalLocallyPresentable κ
  have : IsLocallyPresentable (Sheaf J AddCommGrpCat.{u}) := ⟨⟨κ, hκ, hsh⟩⟩
  have : IsAccessibleCategory (Sheaf J AddCommGrpCat.{u}) :=
    instIsAccessibleCategoryOfIsLocallyPresentable _
  have : IsPresentable G₀ := instIsPresentableOfIsAccessibleCategory _ G₀
  exact (‹IsPresentable G₀›).exists_cardinal

/-- If `G₀` is `κ`-presentable for a regular cardinal `κ`, there is a succ-limit ordinal `β`
with `1 < β.cof` such that for every `F`, `Hom(G₀, -)` carries the tower colimit cocone
`J_β(F) = colim_{α<β} J_α(F)` to a colimit cocone of Hom sets. -/
theorem hom_colimit_of_isCardinalPresentable (G₀ : AbSheaf J)
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hpres : IsCardinalPresentable G₀ κ) :
    ∃ β : Ordinal.{u}, Order.IsSuccLimit β ∧ (1 : Cardinal.{u}) < β.cof ∧
      Nonempty (∀ (F : AbSheaf J),
        IsColimit ((Set.principalSegIio (⟨β, le_refl β⟩ : Set.Iic β)).cocone
          (towerStage J β ⋙ (CategoryTheory.evaluation (AbSheaf J) (AbSheaf J)).obj F
            ⋙ coyoneda.obj (Opposite.op G₀)))) := by
  have := hpres
  set a : Cardinal.{u} := max Cardinal.aleph0 κ with ha_def
  set β : Ordinal.{u} := ((2 : Cardinal.{u}) ^ a).ord with hβ_def
  have ha : Cardinal.aleph0 ≤ a := le_max_left _ _
  have hκa : κ ≤ a := le_max_right _ _
  have hcof : a < β.cof := Cardinal.lt_cof_ord_power ha (by norm_num)
  have h1a : (1 : Cardinal.{u}) ≤ a := le_trans Cardinal.one_le_aleph0 ha
  have h1cof : (1 : Cardinal.{u}) < β.cof := lt_of_le_of_lt h1a hcof
  have hβlim : Order.IsSuccLimit β := Ordinal.one_lt_cof_iff.mp h1cof
  have hκcof : κ < β.cof := lt_of_le_of_lt hκa hcof
  set m : Set.Iic β := ⟨β, le_refl β⟩ with hm_def
  set K : Type (u+1) := ↑(Set.Iio m) with hK_def
  have hsmall : Small.{u} K := by rw [hK_def]; infer_instance
  have hfilt : @IsCardinalFiltered (Shrink.{u} K) (Preorder.smallCategory (Shrink.{u} K)) κ _ := by
    apply isCardinalFiltered_preorder
    intro K' s hcard
    set s' : K' → K := fun k => (orderIsoShrink.{u} K).symm (s k) with hs'
    have hlt : ∀ k, ((s' k : Set.Iic β) : Ordinal) < β := by
      intro k
      have h2 : (s' k : Set.Iic β) < m := (s' k).2
      exact h2
    set μ : Ordinal.{u} := ⨆ k, ((s' k : Set.Iic β) : Ordinal) with hμ
    have hμβ : μ < β := Ordinal.iSup_lt_of_lt_cof (lt_trans hcard hκcof) hlt
    have hmem : (⟨μ, le_of_lt hμβ⟩ : Set.Iic β) ∈ Set.Iio m := hμβ
    refine ⟨orderIsoShrink.{u} K ⟨⟨μ, le_of_lt hμβ⟩, hmem⟩, ?_⟩
    intro k
    have hle : s' k ≤ (⟨⟨μ, le_of_lt hμβ⟩, hmem⟩ : K) := by
      show ((s' k : Set.Iic β) : Ordinal) ≤ μ
      exact Ordinal.le_iSup _ k
    calc s k = orderIsoShrink.{u} K (s' k) := by
              rw [hs']; exact ((orderIsoShrink.{u} K).apply_symm_apply (s k)).symm
      _ ≤ orderIsoShrink.{u} K ⟨⟨μ, le_of_lt hμβ⟩, hmem⟩ :=
            (orderIsoShrink.{u} K).map_rel_iff.mpr hle
  have hpres2 : PreservesColimitsOfShape K (coyoneda.obj (Opposite.op G₀)) := by
    have h0 := preservesColimitsOfShape_of_isCardinalPresentable G₀ κ (Shrink.{u} K)
    exact preservesColimitsOfShape_of_equiv (orderIsoShrink.{u} K).symm.equivalence _
  have hβm : Order.IsSuccLimit m := by
    refine ⟨?_, ?_⟩
    · rw [not_isMin_iff]
      refine ⟨⟨0, bot_le.trans (le_refl β)⟩, ?_⟩
      show (0 : Ordinal) < β
      obtain ⟨x, hx⟩ := not_isMin_iff.mp hβlim.1
      exact lt_of_le_of_lt (bot_le : (0:Ordinal) ≤ x) hx
    · intro b hb
      rw [covBy_iff_lt_and_eq_or_eq] at hb
      refine hβlim.2 (b : Ordinal) ?_
      rw [covBy_iff_lt_and_eq_or_eq]
      refine ⟨Subtype.coe_lt_coe.mpr hb.1, ?_⟩
      intro c hbc hcβ
      have hcmem : c ≤ β := hcβ
      have hcc := hb.2 (⟨c, hcmem⟩) (Subtype.coe_le_coe.mp hbc) (Subtype.coe_le_coe.mp hcβ)
      rcases hcc with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  refine ⟨β, hβlim, h1cof, ⟨fun F => ?_⟩⟩
  have hsheafcol := towerObj_isColimit_of_isSuccLimit J β m hβm F
  exact isColimitOfPreserves (coyoneda.obj (Opposite.op G₀)) hsheafcol

/-- There is a succ-limit ordinal `β` with `1 < β.cof` such that for every `F`, `Hom(G₀, -)`
carries the tower colimit cocone at `β` to a colimit cocone of Hom sets. -/
theorem exists_stage_hom_colimit (G₀ : AbSheaf J) :
    ∃ β : Ordinal.{u}, Order.IsSuccLimit β ∧ (1 : Cardinal.{u}) < β.cof ∧
      Nonempty (∀ (F : AbSheaf J),
        IsColimit ((Set.principalSegIio (⟨β, le_refl β⟩ : Set.Iic β)).cocone
          (towerStage J β ⋙ (CategoryTheory.evaluation (AbSheaf J) (AbSheaf J)).obj F
            ⋙ coyoneda.obj (Opposite.op G₀)))) := by
  obtain ⟨κ, hκ, hpres⟩ := abSheaf_isCardinalPresentable J G₀
  have := hκ
  exact hom_colimit_of_isCardinalPresentable J G₀ κ hpres

/-- For an abelian sheaf `G₀` there is an ordinal `β` such that every morphism
`φ : G₀ → J_β(F)` factors through `J_α(F)` for some `α < β`. -/
theorem exists_ordinal_towerFactorsThrough_single (G₀ : AbSheaf J) :
    ∃ β : Ordinal.{u},
      ∀ (F : AbSheaf J) (φ : G₀ ⟶ towerTop J β F),
        ∃ (α : Set.Iic β) (h : (α : Ordinal) < β),
          TowerFactorsThrough J β
            (le_of_lt (show α < (⟨β, le_refl β⟩ : Set.Iic β) from h)) F G₀ φ := by
  obtain ⟨β, _, hβcof, ⟨hcol⟩⟩ := exists_stage_hom_colimit J G₀
  refine ⟨β, fun F φ => ?_⟩
  set T : Set.Iic β ⥤ Type u :=
    towerStage J β ⋙ (CategoryTheory.evaluation (AbSheaf J) (AbSheaf J)).obj F
      ⋙ coyoneda.obj (Opposite.op G₀) with hT
  have hcolim : IsColimit ((Set.principalSegIio (⟨β, le_refl β⟩ : Set.Iic β)).cocone T) := hcol F
  have hcard : Cardinal.mk PUnit.{u+1} < β.cof := by simpa using hβcof
  have hfval : T.obj ⟨β, le_refl β⟩ = (G₀ ⟶ towerTop J β F) := rfl
  obtain ⟨α, hα, g, hg⟩ := factor_set_map_through_stage_of_lt_cof β T hcolim
    (S := PUnit.{u+1}) hcard (fun _ => (hfval ▸ φ))
  refine ⟨α, hα, g PUnit.unit, ?_⟩
  have hgu := congrFun hg PUnit.unit
  show φ = g PUnit.unit ≫ towerIota J β _ F
  exact hgu.symm

/-- Let `{G i}_{i : I}` be a set of abelian sheaves on `C`. There is an ordinal `β`, depending
only on `J` and the family `{G i}`, such that for every abelian sheaf `F`, every index `i`, and
every morphism `φ : G i → J_β(F)`, there is an ordinal `α < β` such that `φ` factors through
`J_α(F)`. -/
@[stacks 01DN]
theorem exists_ordinal_towerFactorsThrough {I : Type u} (G : I → AbSheaf J) :
    ∃ β : Ordinal.{u},
      ∀ (F : AbSheaf J) (i : I) (φ : G i ⟶ towerTop J β F),
        ∃ (α : Set.Iic β) (h : (α : Ordinal) < β),
          TowerFactorsThrough J β
            (le_of_lt (show α < (⟨β, le_refl β⟩ : Set.Iic β) from h)) F (G i) φ := by
  classical
  obtain ⟨β, hβ⟩ := exists_ordinal_towerFactorsThrough_single J (∐ fun i => G i)
  refine ⟨β, fun F i φ => ?_⟩
  set ψ₀ : (∐ fun i => G i) ⟶ towerTop J β F :=
    Sigma.desc (Pi.single i φ) with hψ₀
  have hext : Sigma.ι (fun i => G i) i ≫ ψ₀ = φ := by
    rw [hψ₀, Limits.colimit.ι_desc]
    simp [Pi.single_eq_same]
  obtain ⟨α, hα, χ, hχ⟩ := hβ F ψ₀
  refine ⟨α, hα, Sigma.ι (fun i => G i) i ≫ χ, ?_⟩
  rw [← hext, hχ]
  exact (Category.assoc _ _ _).symm

end Stacks.Injectives.SheafificationTowerFactorization
