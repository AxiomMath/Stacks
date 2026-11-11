module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Germ naturality at a point of a site

For a functor `P : C ⥤ Type u` which is continuous for the trivial topology on `Type u` and whose
sheaf pushforward is a right adjoint, pushing the germ of a section `s ∈ F(U)` at `x ∈ P U` along a
sheaf morphism `φ : F ⟶ G` gives the germ of the pushed section `φ s` (`stalkSet_map_germ`). The
file also records that the stalk-set functor preserves pushouts, so that it carries the codiagonal
`G ⨿_F G ⟶ G` of a morphism which is an isomorphism on stalks to an isomorphism.

These are auxiliary facts about a single point. Stacks 00YM itself, the characterization of
conservative families of points by germs separating sections, is
`CategoryTheory.GrothendieckTopology.isConservativeFamily_iff_exists_toPresheafFiber_ne` in
`StacksFrontier/CategoryTheory/Sites/Point/SeparatingGerms.lean`.
-/
@[expose] public section

open CategoryTheory Opposite Limits


universe u

noncomputable section

/-- The pullback / inverse-image functor of a point `P : C ⥤ Type u`. -/
def pullbackFunctor {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (P : C ⥤ Type u)
    [P.IsContinuous J (GrothendieckTopology.trivial (Type u))]
    [(P.sheafPushforwardContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).IsRightAdjoint] :
    Sheaf J (Type u) ⥤ Sheaf (GrothendieckTopology.trivial (Type u)) (Type u) :=
  P.sheafPullback (Type u) J (GrothendieckTopology.trivial (Type u))

/-- The stalk *type* of a sheaf at the point `P`. -/
def stalkType {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (P : C ⥤ Type u)
    [P.IsContinuous J (GrothendieckTopology.trivial (Type u))]
    [(P.sheafPushforwardContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).IsRightAdjoint]
    (F : Sheaf J (Type u)) : Type u :=
  ((pullbackFunctor J P).obj F).obj.obj (Opposite.op PUnit.{u + 1})

/-- The stalk-set functor `stalkSet J P : Sheaf J (Type u) ⥤ Type u`. -/
def stalkSet {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (P : C ⥤ Type u)
    [P.IsContinuous J (GrothendieckTopology.trivial (Type u))]
    [(P.sheafPushforwardContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).IsRightAdjoint] :
    Sheaf J (Type u) ⥤ Type u :=
  pullbackFunctor J P
    ⋙ sheafToPresheaf (GrothendieckTopology.trivial (Type u)) (Type u)
    ⋙ (CategoryTheory.evaluation (Type u)ᵒᵖ (Type u)).obj (op PUnit.{u + 1})

/-- The germ of a section `s : F(U)` at a point `x : P U` of the stalk. -/
def germ00YM {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (P : C ⥤ Type u)
    [P.IsContinuous J (GrothendieckTopology.trivial (Type u))]
    [(P.sheafPushforwardContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).IsRightAdjoint]
    (F : Sheaf J (Type u)) (U : C)
    (s : F.obj.obj (Opposite.op U)) (x : P.obj U) : stalkType J P F :=
  let η := (P.sheafAdjunctionContinuous (Type u) J
      (GrothendieckTopology.trivial (Type u))).unit
  let v : ((pullbackFunctor J P).obj F).obj.obj (Opposite.op (P.obj U)) :=
    (η.app F).hom.app (Opposite.op U) s
  ((pullbackFunctor J P).obj F).obj.map
    (Quiver.Hom.op (↾(fun (_ : PUnit.{u + 1}) => x))) v

/-- Naturality of the unit of the pullback ⊣ pushforward adjunction at
a sheaf morphism `φ : F ⟶ G`, evaluated on a section `s : F(U)`. -/
lemma germ_naturality_unit {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (P : C ⥤ Type u)
    [P.IsContinuous J (GrothendieckTopology.trivial (Type u))]
    [(P.sheafPushforwardContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).IsRightAdjoint]
    {F G : Sheaf J (Type u)} (φ : F ⟶ G) (U : C)
    (s : F.obj.obj (Opposite.op U)) :
    ((pullbackFunctor J P).map φ).hom.app (Opposite.op (P.obj U))
        (((P.sheafAdjunctionContinuous (Type u) J
              (GrothendieckTopology.trivial (Type u))).unit.app F).hom.app
            (Opposite.op U) s)
      = ((P.sheafAdjunctionContinuous (Type u) J
            (GrothendieckTopology.trivial (Type u))).unit.app G).hom.app
          (Opposite.op U) (φ.hom.app (Opposite.op U) s) :=
  (congrArg (fun f : F ⟶ _ => f.hom.app (Opposite.op U) s)
    ((P.sheafAdjunctionContinuous (Type u) J
      (GrothendieckTopology.trivial (Type u))).unit.naturality φ)).symm

/-- Naturality of `((pullbackFunctor J P).map φ).val` at the restriction
morphism `Quiver.Hom.op (fun _ => x) : op PUnit ⟶ op (P.obj U)`. -/
lemma germ_naturality_pullback {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (P : C ⥤ Type u)
    [P.IsContinuous J (GrothendieckTopology.trivial (Type u))]
    [(P.sheafPushforwardContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).IsRightAdjoint]
    {F G : Sheaf J (Type u)} (φ : F ⟶ G) (U : C) (x : P.obj U)
    (v : ((pullbackFunctor J P).obj F).obj.obj (Opposite.op (P.obj U))) :
    ((pullbackFunctor J P).map φ).hom.app (Opposite.op PUnit.{u + 1})
        (((pullbackFunctor J P).obj F).obj.map
          (Quiver.Hom.op (↾(fun (_ : PUnit.{u + 1}) => x))) v)
      = ((pullbackFunctor J P).obj G).obj.map
          (Quiver.Hom.op (↾(fun (_ : PUnit.{u + 1}) => x)))
          (((pullbackFunctor J P).map φ).hom.app (Opposite.op (P.obj U)) v) :=
  NatTrans.naturality_apply ((pullbackFunctor J P).map φ).hom
    (Quiver.Hom.op (↾(fun (_ : PUnit.{u + 1}) => x))) v

/-- The action of `(stalkSet J P).map φ` on a stalk element unfolds to
`((pullbackFunctor J P).map φ).val.app (op PUnit)`. -/
lemma stalkSet_map_apply {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (P : C ⥤ Type u)
    [P.IsContinuous J (GrothendieckTopology.trivial (Type u))]
    [(P.sheafPushforwardContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).IsRightAdjoint]
    {F G : Sheaf J (Type u)} (φ : F ⟶ G)
    (y : ((pullbackFunctor J P).obj F).obj.obj (Opposite.op PUnit.{u + 1})) :
    (stalkSet J P).map φ y
      = ((pullbackFunctor J P).map φ).hom.app (Opposite.op PUnit.{u + 1}) y :=
  rfl

/-- **Germ naturality.** Pushing the germ at `x ∈ P U` of a section `s ∈ F(U)` along a sheaf
morphism `φ : F ⟶ G` gives the germ at `x` of `φ s`. This is an auxiliary naturality fact; Stacks
00YM is `CategoryTheory.GrothendieckTopology.isConservativeFamily_iff_exists_toPresheafFiber_ne`. -/
lemma stalkSet_map_germ {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (P : C ⥤ Type u)
    [P.IsContinuous J (GrothendieckTopology.trivial (Type u))]
    [(P.sheafPushforwardContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).IsRightAdjoint]
    {F G : Sheaf J (Type u)} (φ : F ⟶ G) (U : C)
    (s : F.obj.obj (Opposite.op U)) (x : P.obj U) :
    (stalkSet J P).map φ (germ00YM J P F U s x)
      = germ00YM J P G U (φ.hom.app (Opposite.op U) s) x :=
  (germ_naturality_pullback J P φ U x
    (((P.sheafAdjunctionContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).unit.app F).hom.app
      (Opposite.op U) s)).trans
    (congrArg (((pullbackFunctor J P).obj G).obj.map
      (Quiver.Hom.op (↾fun (_ : PUnit.{u + 1}) => x))) (germ_naturality_unit J P φ U s))

/-! ### Auxiliary categorical input

Codiagonal-of-iso facts of the kind used in the source's proof of Stacks 00YM:
`stalkSet J P` preserves pushouts, and a pushout-preserving functor carries the codiagonal of
an iso to an iso. -/

/-- The category `Sheaf J (Type u)` has pushouts. -/
instance hasPushouts_sheaf_type {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) :
    HasPushouts (Sheaf J (Type u)) :=
  inferInstance

/-- `sheafToPresheaf` for the trivial topology preserves pushouts. -/
theorem sheafToPresheaf_trivial_preservesPushouts.{v} :
    PreservesColimitsOfShape WalkingSpan
      (sheafToPresheaf (GrothendieckTopology.trivial (Type v)) (Type v)) := by
  rw [GrothendieckTopology.trivial_eq_bot, ← sheafBotEquivalence_functor]
  infer_instance

/-- Evaluation at `op PUnit` preserves pushouts of `Type`-valued presheaves. -/
theorem evaluation_op_PUnit_preservesPushouts.{v} :
    PreservesColimitsOfShape WalkingSpan
      ((CategoryTheory.evaluation (Type v)ᵒᵖ (Type v)).obj (op PUnit.{v + 1})) :=
  inferInstance

/-- The stalk-set functor preserves pushouts. -/
theorem stalkSet_preservesPushouts {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C)
    (P : C ⥤ Type u)
    [P.IsContinuous J (GrothendieckTopology.trivial (Type u))]
    [(P.sheafPushforwardContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).IsRightAdjoint] :
    PreservesColimitsOfShape WalkingSpan (stalkSet J P) := by
  have h1 : PreservesColimitsOfShape WalkingSpan
      (P.sheafPullback (Type u) J (GrothendieckTopology.trivial (Type u))) :=
    ((P.sheafAdjunctionContinuous (Type u) J
      (GrothendieckTopology.trivial (Type u))).leftAdjoint_preservesColimits
        ).preservesColimitsOfShape
  have := sheafToPresheaf_trivial_preservesPushouts.{u}
  have := evaluation_op_PUnit_preservesPushouts.{u}
  unfold stalkSet pullbackFunctor
  infer_instance

/-- Codiagonal of pushout of an iso is iso. -/
theorem isIso_pushout_codiagonal_of_isIso
    {C : Type*} [Category.{u} C] {X Y : C} (f : X ⟶ Y) [HasPushout f f]
    [IsIso f] :
    IsIso (pushout.desc (𝟙 Y) (𝟙 Y) rfl : pushout f f ⟶ Y) := by
  have h : (pushout.inl f f : Y ⟶ pushout f f) = pushout.inr f f :=
    (cancel_epi f).mp pushout.condition
  refine ⟨pushout.inl f f, ?_, pushout.inl_desc _ _ _⟩
  apply pushout.hom_ext <;> simp [← h]

/-- Image of codiagonal under a pushout-preserving functor coincides with
the codiagonal in the target. -/
theorem preservesPushout_iso_hom_comp_Fmap_codiagonal
    {𝒜 : Type*} [Category.{u} 𝒜] {ℬ : Type*} [Category.{u} ℬ]
    {X Y : 𝒜} (φ : X ⟶ Y) [HasPushout φ φ]
    (F : 𝒜 ⥤ ℬ) [HasPushout (F.map φ) (F.map φ)]
    [PreservesColimit (span φ φ) F] :
    (PreservesPushout.iso F φ φ).hom ≫
      F.map (pushout.desc (𝟙 Y) (𝟙 Y) rfl : pushout φ φ ⟶ Y) =
    (pushout.desc (𝟙 (F.obj Y)) (𝟙 (F.obj Y)) rfl :
      pushout (F.map φ) (F.map φ) ⟶ F.obj Y) := by
  apply pushout.hom_ext <;> simp

/-- A pushout-preserving functor maps the codiagonal of an iso to an iso. -/
theorem isIso_map_codiagonal_of_isIso
    {𝒜 : Type*} [Category.{u} 𝒜] {ℬ : Type*} [Category.{u} ℬ]
    {X Y : 𝒜} (φ : X ⟶ Y) [HasPushout φ φ]
    (F : 𝒜 ⥤ ℬ) [HasPushout (F.map φ) (F.map φ)]
    [PreservesColimit (span φ φ) F]
    (hφ : IsIso (F.map φ)) :
    IsIso (F.map (pushout.desc (𝟙 Y) (𝟙 Y) rfl : pushout φ φ ⟶ Y)) := by
  have := isIso_pushout_codiagonal_of_isIso (F.map φ)
  rw [← Iso.inv_hom_id_assoc (PreservesPushout.iso F φ φ)
      (F.map (pushout.desc (𝟙 Y) (𝟙 Y) rfl : pushout φ φ ⟶ Y)),
    preservesPushout_iso_hom_comp_Fmap_codiagonal]
  infer_instance

/-- Codiagonal of the pushout `φ ⨿ φ ⟶ G` has an iso image under
`stalkSet J P` whenever `(stalkSet J P).map φ` is iso. -/
lemma codiagonal_stalkSet_isIso {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C)
    (P : C ⥤ Type u)
    [P.IsContinuous J (GrothendieckTopology.trivial (Type u))]
    [(P.sheafPushforwardContinuous (Type u) J
        (GrothendieckTopology.trivial (Type u))).IsRightAdjoint]
    {F G : Sheaf J (Type u)} (φ : F ⟶ G)
    (hφ : IsIso ((stalkSet J P).map φ)) :
    IsIso ((stalkSet J P).map
      (pushout.desc (𝟙 G) (𝟙 G) rfl : (pushout φ φ : Sheaf J (Type u)) ⟶ G)) := by
  have := stalkSet_preservesPushouts J P
  exact isIso_map_codiagonal_of_isIso φ (stalkSet J P) hφ

end

