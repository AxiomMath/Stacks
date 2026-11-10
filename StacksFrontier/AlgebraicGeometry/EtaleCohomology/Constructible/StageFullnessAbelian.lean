module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageColimitCompletion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFullness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructible abelian sheaves on a limit of schemes: Tag 09YU, clause (2)

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms inside a big étale site. This file proves Tag 09YU,
clause (2): the category of constructible abelian sheaves on `X_étale` is the colimit of the
categories of constructible abelian sheaves on the `(X_i)_étale`, in the elementwise form
`AlgebraicGeometry.SmallEtaleStagesColimit` in which clause (1) is stated
(`AlgebraicGeometry.smallEtaleStagesColimit_isConstructibleSetSheaf`). Faithfulness is already in
the library (`AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleAbelianSheaf`); this file
adds fullness and essential surjectivity.

## The argument

The source deduces clause (2) from clause (3) through the identification of abelian sheaves
killed by `n` with sheaves of `Z/nZ`-modules. The argument here instead reduces clause (2) to
clause (1) along the passage to underlying sheaves of sets.

* *Fullness.* Passing to underlying sheaves of sets commutes with inverse image (Stacks 00YT,
  `AlgebraicGeometry.smallEtaleUnderlyingSetPullbackIso`), compatibly with the comparisons of
  inverse images through two stages
  (`CategoryTheory.Functor.sheafPullbackComp'_hom_app_comp_sheafPullbackSheafComposeHom`). The
  sheaves of sets underlying constructible abelian sheaves are constructible, so the map of sets
  underlying a map on `X` comes from a stage by clause (1). It is additive on `X`. Additivity is the
  equality of two maps out of the sheaf of sets underlying `F ⊞ F`
  (`CategoryTheory.Sheaf.forgetAddLeft` and `CategoryTheory.Sheaf.forgetAddRight`), so by
  faithfulness for sheaves of sets it holds at a later stage, where the map is therefore a map of
  abelian sheaves.
* *Essential surjectivity.* A constructible abelian sheaf `F` on the quasi-compact
  quasi-separated `X` is killed by some `N > 0` (Stacks 09YT). It is therefore a quotient of the
  copower sheaf by `Z/NZ` on its sheaf of sets, which is constructible (Stacks 03S8). Applying
  this to the kernel as well presents `F` as the cokernel of a map between two copower sheaves on
  constructible sheaves of sets. Those sheaves of sets come from a stage by clause (1), the
  copower sheaf commutes with inverse image, the map comes from a stage by fullness, and inverse
  image carries the cokernel at that stage to `F`.

## Main results

* `CategoryTheory.Functor.sheafPullbackSheafComposeHom_naturality` and
  `CategoryTheory.Functor.sheafPullbackComp'_hom_app_comp_sheafPullbackSheafComposeHom`: the
  comparison between inverse image and change of coefficients is natural and compatible with the
  composition of inverse images.
* `AlgebraicGeometry.smallEtaleStagesFull_isConstructibleAbelianSheaf`: **Tag 09YU, clause (2),
  the fullness assertion.**
* `AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleAbelianSheaf`: **Tag 09YU, clause
  (2), the essential surjectivity assertion.**
* `AlgebraicGeometry.smallEtaleStagesColimit_isConstructibleAbelianSheaf`: **Tag 09YU, clause
  (2).**

## References

* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 00YT](https://stacks.math.columbia.edu/tag/00YT)
* [Stacks Project, Tag 09YT](https://stacks.math.columbia.edu/tag/09YT)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅ u

namespace CategoryTheory.Functor

section Naturality

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [HasWeakSheafify K A] [∀ P : Cᵒᵖ ⥤ A, F.op.HasLeftKanExtension P]
  {A' : Type u₄} [Category.{v₄} A'] (Φ : A ⥤ A')
  [HasWeakSheafify K A'] [∀ P : Cᵒᵖ ⥤ A', F.op.HasLeftKanExtension P]
  [J.HasSheafCompose Φ] [K.HasSheafCompose Φ]

omit [HasWeakSheafify K A] [∀ P : Cᵒᵖ ⥤ A, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K A'] [∀ P : Cᵒᵖ ⥤ A', F.op.HasLeftKanExtension P] in
/-- Changing coefficients commutes with pushforward on the nose. -/
public theorem sheafCompose_map_sheafPushforwardContinuous_map {T T' : Sheaf K A} (y : T ⟶ T') :
    (sheafCompose J Φ).map ((F.sheafPushforwardContinuous A J K).map y) =
      (F.sheafPushforwardContinuous A' J K).map ((sheafCompose K Φ).map y) :=
  rfl

/-- The adjoint transpose of the comparison `F^*(Φ ∘ S) ⟶ Φ ∘ F^*(S)` is `Φ` applied to the unit. -/
public theorem homEquiv_sheafPullbackSheafComposeHom (S : Sheaf J A) :
    (F.sheafAdjunctionContinuous A' J K).homEquiv _ _ (F.sheafPullbackSheafComposeHom A J K Φ S) =
      (sheafCompose J Φ).map ((F.sheafAdjunctionContinuous A J K).unit.app S) := by
  rw [sheafPullbackSheafComposeHom, Equiv.apply_symm_apply]
  exact Category.comp_id _

/-- The comparison `F^*(Φ ∘ S) ⟶ Φ ∘ F^*(S)` transposed through the unit is `Φ` applied to the
unit. -/
public theorem unit_comp_pushforward_map_sheafPullbackSheafComposeHom' (S : Sheaf J A) :
    (F.sheafAdjunctionContinuous A' J K).unit.app ((sheafCompose J Φ).obj S) ≫
        (F.sheafPushforwardContinuous A' J K).map (F.sheafPullbackSheafComposeHom A J K Φ S) =
      (sheafCompose J Φ).map ((F.sheafAdjunctionContinuous A J K).unit.app S) := by
  rw [unit_comp_pushforward_map_sheafPullbackSheafComposeHom]
  exact Category.comp_id _

/-- **Naturality of the comparison `F^*(Φ ∘ S) ⟶ Φ ∘ F^*(S)`** in the sheaf `S`. -/
@[reassoc]
public theorem sheafPullbackSheafComposeHom_naturality {S S' : Sheaf J A} (x : S ⟶ S') :
    (F.sheafPullback A' J K).map ((sheafCompose J Φ).map x) ≫
        F.sheafPullbackSheafComposeHom A J K Φ S' =
      F.sheafPullbackSheafComposeHom A J K Φ S ≫
        (sheafCompose K Φ).map ((F.sheafPullback A J K).map x) := by
  apply ((F.sheafAdjunctionContinuous A' J K).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_sheafPullbackSheafComposeHom, homEquiv_sheafPullbackSheafComposeHom,
    ← sheafCompose_map_sheafPushforwardContinuous_map]
  refine ((sheafCompose J Φ).map_comp _ _).symm.trans
    (Eq.trans ?_ ((sheafCompose J Φ).map_comp _ _))
  exact congrArg _ ((F.sheafAdjunctionContinuous A J K).unit.naturality x)

end Naturality

section Comp

variable {C : Type u₁} {D : Type u₂} {E : Type u₅} [Category.{v₁} C] [Category.{v₂} D]
  [Category.{v₅} E] {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} (eFG : F ⋙ G ≅ FG)
  (A : Type u₃) [Category.{v₃} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [F.IsContinuous J K] [G.IsContinuous K L] [FG.IsContinuous J L]

/-- The adjoint transpose of the composition comparison of inverse images is the unit followed by
the composition comparison of pushforwards. -/
public theorem comp_homEquiv_sheafPullbackComp'_hom_app
    [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(G.sheafPushforwardContinuous A K L).IsRightAdjoint]
    [(FG.sheafPushforwardContinuous A J L).IsRightAdjoint] (X : Sheaf J A) :
    ((F.sheafAdjunctionContinuous A J K).comp (G.sheafAdjunctionContinuous A K L)).homEquiv _ _
        ((sheafPullbackComp' eFG A J K L).hom.app X) =
      (FG.sheafAdjunctionContinuous A J L).unit.app X ≫
        (sheafPushforwardContinuousComp' eFG A J K L).inv.app
          ((FG.sheafPullback A J L).obj X) := by
  rw [Adjunction.homEquiv_unit]
  exact (unit_conjugateEquiv_symm (FG.sheafAdjunctionContinuous A J L)
    ((F.sheafAdjunctionContinuous A J K).comp (G.sheafAdjunctionContinuous A K L))
    (sheafPushforwardContinuousComp' eFG A J K L).inv X).symm

variable {A' : Type u₄} [Category.{v₄} A'] (Φ : A ⥤ A')
  [J.HasSheafCompose Φ] [K.HasSheafCompose Φ] [L.HasSheafCompose Φ]

omit [K.HasSheafCompose Φ] in
/-- Changing coefficients commutes with the composition comparison of pushforwards. -/
public theorem sheafCompose_map_sheafPushforwardContinuousComp'_inv_app (T : Sheaf L A) :
    (sheafCompose J Φ).map ((sheafPushforwardContinuousComp' eFG A J K L).inv.app T) =
      (sheafPushforwardContinuousComp' eFG A' J K L).inv.app ((sheafCompose L Φ).obj T) := by
  ext X : 3
  simp only [sheafCompose_map_hom, Functor.whiskerRight_app,
    sheafPushforwardContinuousComp'_inv_app_hom_app]
  rfl

variable [HasWeakSheafify K A] [HasWeakSheafify L A] [HasWeakSheafify K A']
  [HasWeakSheafify L A']
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasLeftKanExtension P] [∀ P : Dᵒᵖ ⥤ A, G.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A, FG.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A', F.op.HasLeftKanExtension P] [∀ P : Dᵒᵖ ⥤ A', G.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A', FG.op.HasLeftKanExtension P]

/-- **The change-of-coefficients comparison is compatible with the composition comparison of
inverse images.** For `e : F ⋙ G ≅ FG`, the two ways from `G^*F^*(Φ ∘ S)` to `Φ ∘ FG^*S` — through
the composition comparison and then the comparison for `FG`, or through the comparisons for `F`
and `G` and then the composition comparison — agree. -/
public theorem sheafPullbackComp'_hom_app_comp_sheafPullbackSheafComposeHom (S : Sheaf J A) :
    (sheafPullbackComp' eFG A' J K L).hom.app ((sheafCompose J Φ).obj S) ≫
        FG.sheafPullbackSheafComposeHom A J L Φ S =
      (G.sheafPullback A' K L).map (F.sheafPullbackSheafComposeHom A J K Φ S) ≫
        G.sheafPullbackSheafComposeHom A K L Φ ((F.sheafPullback A J K).obj S) ≫
        (sheafCompose L Φ).map ((sheafPullbackComp' eFG A J K L).hom.app S) := by
  apply (((F.sheafAdjunctionContinuous A' J K).comp
    (G.sheafAdjunctionContinuous A' K L)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, comp_homEquiv_sheafPullbackComp'_hom_app,
    Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right, homEquiv_sheafPullbackSheafComposeHom,
    homEquiv_sheafPullbackSheafComposeHom]
  have hnat := (sheafPushforwardContinuousComp' eFG A' J K L).inv.naturality
    (FG.sheafPullbackSheafComposeHom A J L Φ S)
  dsimp only [Functor.comp_map] at hnat ⊢
  rw [Category.assoc, ← hnat, ← Category.assoc,
    unit_comp_pushforward_map_sheafPullbackSheafComposeHom',
    ← sheafCompose_map_sheafPushforwardContinuousComp'_inv_app]
  refine ((sheafCompose J Φ).map_comp _ _).symm.trans ?_
  rw [← comp_homEquiv_sheafPullbackComp'_hom_app, Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  rfl

end Comp

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf

/-- Equal maps of sheaves of sets agree on every section. -/
private theorem hom_app_apply_congr {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {Z Z' : Sheaf J (Type u₂)} {x y : Z ⟶ Z'} (h : x = y) (V : Cᵒᵖ) (z : Z.obj.obj V) :
    x.hom.app V z = y.hom.app V z := by
  rw [h]

section Additive

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{u₂})]

/-- A map between the sheaves of sets underlying two abelian sheaves, evaluated on a section, as an
element of the group of sections of the target. -/
public abbrev forgetHomApp {F G : Sheaf J AddCommGrpCat.{u₂}} (ψ :
    (sheafCompose J (forget AddCommGrpCat.{u₂})).obj F ⟶
    (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) (V : Cᵒᵖ)
    (x : F.obj.obj V) : G.obj.obj V :=
  ψ.hom.app V x

/-- A map from a sheaf of sets to the sheaf of sets underlying an abelian sheaf, evaluated on a
section, as an element of the group of sections of the target. -/
public abbrev forgetHomApp' {Z : Sheaf J (Type u₂)} {G : Sheaf J AddCommGrpCat.{u₂}}
    (α : Z ⟶ (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) (V : Cᵒᵖ) (z : Z.obj.obj V)
        : G.obj.obj V :=
  α.hom.app V z

/-- A map between the sheaves of sets underlying two abelian sheaves is *additive* when it is
additive on every group of sections. -/
public def ForgetAdditive {F G : Sheaf J AddCommGrpCat.{u₂}} (ψ :
    (sheafCompose J (forget AddCommGrpCat.{u₂})).obj F ⟶
    (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) : Prop :=
  ∀ (V : Cᵒᵖ) (x y : F.obj.obj V),
    forgetHomApp ψ V (x + y) = forgetHomApp ψ V x + forgetHomApp ψ V y

/-- An additive map between the underlying sheaves of sets is a map of abelian sheaves. -/
public def homOfForgetAdditive {F G : Sheaf J AddCommGrpCat.{u₂}} (ψ :
    (sheafCompose J (forget AddCommGrpCat.{u₂})).obj F ⟶
    (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G)
    (hψ : ForgetAdditive ψ) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun V => AddCommGrpCat.ofHom (AddMonoidHom.mk' (forgetHomApp ψ V) (hψ V))
      naturality := fun V W f => by
        ext x
        exact ConcreteCategory.congr_hom (ψ.hom.naturality f) x }

@[simp]
public theorem sheafCompose_map_homOfForgetAdditive {F G : Sheaf J AddCommGrpCat.{u₂}}
    (ψ : (sheafCompose J (forget AddCommGrpCat.{u₂})).obj F ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) (hψ : ForgetAdditive ψ) :
    (sheafCompose J (forget AddCommGrpCat.{u₂})).map (homOfForgetAdditive ψ hψ) = ψ :=
  rfl

/-- Passing to underlying sheaves of sets is faithful. -/
public theorem sheafCompose_forget_map_injective {F G : Sheaf J AddCommGrpCat.{u₂}} {x y : F ⟶ G}
    (h : (sheafCompose J (forget AddCommGrpCat.{u₂})).map x =
        (sheafCompose J (forget AddCommGrpCat.{u₂})).map y) : x = y := by
  ext V z
  exact hom_app_apply_congr h V z

/-- The map underlying a map of abelian sheaves is additive. -/
public theorem forgetAdditive_map {F G : Sheaf J AddCommGrpCat.{u₂}} (a : F ⟶ G) :
    ForgetAdditive ((sheafCompose J (forget AddCommGrpCat.{u₂})).map a) :=
  fun V x y => map_add (a.hom.app V).hom x y

/-- The map of sheaves of sets `z ↦ i₁(α z) + i₂(β z)` into the sheaf of sets underlying an
abelian sheaf `H`, for maps `i₁ i₂ : G ⟶ H` of abelian sheaves and maps `α β` of sheaves of sets
into the sheaf underlying `G`. -/
public def forgetLift {Z : Sheaf J (Type u₂)} {G H : Sheaf J AddCommGrpCat.{u₂}} (i₁ i₂ : G ⟶ H)
    (α β : Z ⟶ (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) : Z ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj H :=
  ObjectProperty.homMk
    { app := fun V => ↾fun z => (i₁.hom.app V (forgetHomApp' α V z) +
        i₂.hom.app V (forgetHomApp' β V z) : H.obj.obj V)
      naturality := fun V W f => by
        ext z
        have hα : forgetHomApp' α W (Z.obj.map f z) = G.obj.map f (forgetHomApp' α V z) :=
          ConcreteCategory.congr_hom (α.hom.naturality f) z
        have hβ : forgetHomApp' β W (Z.obj.map f z) = G.obj.map f (forgetHomApp' β V z) :=
          ConcreteCategory.congr_hom (β.hom.naturality f) z
        change (i₁.hom.app W (forgetHomApp' α W (Z.obj.map f z)) +
            i₂.hom.app W (forgetHomApp' β W (Z.obj.map f z)) : H.obj.obj W) =
          H.obj.map f (i₁.hom.app V (forgetHomApp' α V z) + i₂.hom.app V (forgetHomApp' β V z))
        rw [hα, hβ, map_add, NatTrans.naturality_apply, NatTrans.naturality_apply] }

public theorem forgetLift_app {Z : Sheaf J (Type u₂)} {G H : Sheaf J AddCommGrpCat.{u₂}}
    (i₁ i₂ : G ⟶ H) (α β : Z ⟶ (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) (V : Cᵒᵖ) (z
        : Z.obj.obj V) :
    forgetHomApp' (forgetLift i₁ i₂ α β) V z =
      i₁.hom.app V (forgetHomApp' α V z) + i₂.hom.app V (forgetHomApp' β V z) :=
  rfl

/-- Precomposition with a map of sheaves of sets. -/
public theorem comp_forgetLift {Z Z' : Sheaf J (Type u₂)} {G H : Sheaf J AddCommGrpCat.{u₂}}
    (γ : Z' ⟶ Z) (i₁ i₂ : G ⟶ H) (α β : Z ⟶ (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) :
    γ ≫ forgetLift i₁ i₂ α β = forgetLift i₁ i₂ (γ ≫ α) (γ ≫ β) :=
  rfl

omit [J.HasSheafCompose (forget AddCommGrpCat.{u₂})] in
/-- Pointwise form of an identity `i ≫ p = q` of maps of abelian sheaves. -/
public theorem hom_app_hom_app_of_comp_eq {G H G' : Sheaf J AddCommGrpCat.{u₂}} {i : G ⟶ H}
    {p : H ⟶ G'} {q : G ⟶ G'} (h : i ≫ p = q) (V : Cᵒᵖ) (w : G.obj.obj V) :
    p.hom.app V (i.hom.app V w) = q.hom.app V w := by
  rw [← h]
  rfl

omit [J.HasSheafCompose (forget AddCommGrpCat.{u₂})] in
/-- Pointwise form of a sum of maps of abelian sheaves. -/
public theorem add_hom_app_apply {G H : Sheaf J AddCommGrpCat.{u₂}} (p q : G ⟶ H) (V : Cᵒᵖ)
    (w : G.obj.obj V) : (p + q).hom.app V w = p.hom.app V w + q.hom.app V w :=
  rfl

/-- `forgetLift` followed by the map underlying `p`, when `i₁ ≫ p = 𝟙` and `i₂ ≫ p = 0`. -/
public theorem forgetLift_comp_map {Z : Sheaf J (Type u₂)} {G H : Sheaf J AddCommGrpCat.{u₂}}
    {i₁ i₂ : G ⟶ H} {p : H ⟶ G} (h₁ : i₁ ≫ p = 𝟙 G) (h₂ : i₂ ≫ p = 0) (α β : Z ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) :
    forgetLift i₁ i₂ α β ≫ (sheafCompose J (forget AddCommGrpCat.{u₂})).map p = α := by
  ext V z
  change p.hom.app V (i₁.hom.app V (forgetHomApp' α V z) + i₂.hom.app V (forgetHomApp' β V z)) =
    forgetHomApp' α V z
  rw [map_add, hom_app_hom_app_of_comp_eq h₁, hom_app_hom_app_of_comp_eq h₂]
  simp

/-- `forgetLift` followed by the map underlying `p`, when `i₁ ≫ p = 0` and `i₂ ≫ p = 𝟙`. -/
public theorem forgetLift_comp_map' {Z : Sheaf J (Type u₂)} {G H : Sheaf J AddCommGrpCat.{u₂}}
    {i₁ i₂ : G ⟶ H} {p : H ⟶ G} (h₁ : i₁ ≫ p = 0) (h₂ : i₂ ≫ p = 𝟙 G) (α β : Z ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) :
    forgetLift i₁ i₂ α β ≫ (sheafCompose J (forget AddCommGrpCat.{u₂})).map p = β := by
  ext V z
  change p.hom.app V (i₁.hom.app V (forgetHomApp' α V z) + i₂.hom.app V (forgetHomApp' β V z)) =
    forgetHomApp' β V z
  rw [map_add, hom_app_hom_app_of_comp_eq h₁, hom_app_hom_app_of_comp_eq h₂]
  simp

/-- **The two projections of a biproduct are jointly monic on underlying sheaves of sets.** -/
public theorem forget_hom_ext_of_total {Z : Sheaf J (Type u₂)}
    {G₁ G₂ H : Sheaf J AddCommGrpCat.{u₂}} {p₁ : H ⟶ G₁} {p₂ : H ⟶ G₂} {i₁ : G₁ ⟶ H}
    {i₂ : G₂ ⟶ H} (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 H) {x y : Z ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj H}
    (h₁ : x ≫ (sheafCompose J (forget AddCommGrpCat.{u₂})).map p₁ = y ≫
        (sheafCompose J (forget AddCommGrpCat.{u₂})).map p₁) (h₂ : x ≫
        (sheafCompose J (forget AddCommGrpCat.{u₂})).map p₂ = y ≫
        (sheafCompose J (forget AddCommGrpCat.{u₂})).map p₂) : x = y := by
  ext V z
  have t : ∀ w : H.obj.obj V,
      w = i₁.hom.app V (p₁.hom.app V w) + i₂.hom.app V (p₂.hom.app V w) := fun w =>
    (congrArg (fun q : H ⟶ H => q.hom.app V w) htot).symm
  have e₁ : p₁.hom.app V (forgetHomApp' x V z) = p₁.hom.app V (forgetHomApp' y V z) :=
    hom_app_apply_congr h₁ V z
  have e₂ : p₂.hom.app V (forgetHomApp' x V z) = p₂.hom.app V (forgetHomApp' y V z) :=
    hom_app_apply_congr h₂ V z
  change forgetHomApp' x V z = forgetHomApp' y V z
  rw [t (forgetHomApp' x V z), t (forgetHomApp' y V z), e₁, e₂]

/-- The first of the two maps whose equality expresses additivity of `ψ`: `ψ` precomposed with the
map underlying the sum `F ⊕ F ⟶ F` of the two projections of a bicone. -/
public abbrev forgetAddLeft {F G : Sheaf J AddCommGrpCat.{u₂}} (b : BinaryBicone F F)
    (ψ : (sheafCompose J (forget AddCommGrpCat.{u₂})).obj F ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) :
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj b.pt ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G :=
  (sheafCompose J (forget AddCommGrpCat.{u₂})).map (b.fst + b.snd) ≫ ψ

/-- The second of the two maps whose equality expresses additivity of `ψ`: `ψ` applied to the two
components, followed by the sum. -/
public abbrev forgetAddRight {F G : Sheaf J AddCommGrpCat.{u₂}} (b : BinaryBicone F F)
    (c : BinaryBicone G G) (ψ : (sheafCompose J (forget AddCommGrpCat.{u₂})).obj F ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) :
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj b.pt ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G :=
  forgetLift c.inl c.inr ((sheafCompose J (forget AddCommGrpCat.{u₂})).map b.fst ≫
      ψ) ((sheafCompose J (forget AddCommGrpCat.{u₂})).map b.snd ≫ ψ) ≫
      (sheafCompose J (forget AddCommGrpCat.{u₂})).map (c.fst + c.snd)

/-- An additive `ψ` makes the two maps agree. -/
public theorem forgetAddLeft_eq_forgetAddRight {F G : Sheaf J AddCommGrpCat.{u₂}}
    (b : BinaryBicone F F) (c : BinaryBicone G G) (ψ :
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj F ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G)
    (hψ : ForgetAdditive ψ) : forgetAddLeft b ψ = forgetAddRight b c ψ := by
  ext V z
  have key : ∀ z : b.pt.obj.obj V, forgetHomApp ψ V ((b.fst + b.snd).hom.app V z) =
      (c.fst + c.snd).hom.app V (c.inl.hom.app V (forgetHomApp ψ V (b.fst.hom.app V z)) +
        c.inr.hom.app V (forgetHomApp ψ V (b.snd.hom.app V z))) := by
    intro z
    rw [add_hom_app_apply, hψ, add_hom_app_apply, map_add, map_add,
      hom_app_hom_app_of_comp_eq c.inl_fst, hom_app_hom_app_of_comp_eq c.inl_snd,
      hom_app_hom_app_of_comp_eq c.inr_fst, hom_app_hom_app_of_comp_eq c.inr_snd]
    simp
  exact key z

/-- Agreement of the two maps makes `ψ` additive. -/
public theorem forgetAdditive_of_forgetAddLeft_eq_forgetAddRight
    {F G : Sheaf J AddCommGrpCat.{u₂}} (b : BinaryBicone F F) (c : BinaryBicone G G)
    (ψ : (sheafCompose J (forget AddCommGrpCat.{u₂})).obj F ⟶
        (sheafCompose J (forget AddCommGrpCat.{u₂})).obj G) (h
        : forgetAddLeft b ψ = forgetAddRight b c ψ) :
    ForgetAdditive ψ := by
  intro V x y
  have hz := Sheaf.hom_app_apply_congr h V (b.inl.hom.app V x + b.inr.hom.app V y)
  change forgetHomApp ψ V ((b.fst + b.snd).hom.app V (b.inl.hom.app V x + b.inr.hom.app V y)) =
    (c.fst + c.snd).hom.app V (c.inl.hom.app V (forgetHomApp ψ V (b.fst.hom.app V
      (b.inl.hom.app V x + b.inr.hom.app V y))) +
      c.inr.hom.app V (forgetHomApp ψ V (b.snd.hom.app V (b.inl.hom.app V x + b.inr.hom.app V y))))
    at hz
  simp only [add_hom_app_apply, map_add, hom_app_hom_app_of_comp_eq b.inl_fst,
    hom_app_hom_app_of_comp_eq b.inl_snd, hom_app_hom_app_of_comp_eq b.inr_fst,
    hom_app_hom_app_of_comp_eq b.inr_snd, hom_app_hom_app_of_comp_eq c.inl_fst,
    hom_app_hom_app_of_comp_eq c.inl_snd, hom_app_hom_app_of_comp_eq c.inr_fst,
    hom_app_hom_app_of_comp_eq c.inr_snd] at hz
  simpa using hz

end Additive

end CategoryTheory.Sheaf

namespace CategoryTheory.Abelian

/-- In an abelian category, the cokernel of a conjugate `e₁ ≫ (p ≫ kernel.ι q) ≫ e₂⁻¹` of the
composite of an epimorphism `p` onto the kernel of an epimorphism `q` with the inclusion of that
kernel is the target of `q`. -/
public theorem nonempty_cokernel_iso_of_eq_conj_comp_kernel_ι {C : Type*} [Category* C]
    [Abelian C] {A' B' A B Y : C} (q : B ⟶ Y) [Epi q] (p : A ⟶ kernel q) [Epi p] (e₁ : A' ≅ A)
    (e₂ : B' ≅ B) {f : A' ⟶ B'} (h : f = e₁.hom ≫ (p ≫ kernel.ι q) ≫ e₂.inv) :
    Nonempty (cokernel f ≅ Y) :=
  ⟨cokernelIsoOfEq h ≪≫ cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ cokernelEpiComp _ _ ≪≫
    (cokernelIsCokernel (kernel.ι q)).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι q) (kernel.condition q))
        (kernelIsKernel q))⟩

end CategoryTheory.Abelian

namespace AlgebraicGeometry

section Underlying

variable (B : BigEtaleSite.{u})

/-- Inverse image of presheaves along small étale base change exists pointwise, the comma
categories computing it being essentially small. -/
public theorem smallEtaleBaseChange_op_hasPointwiseLeftKanExtension (A : Type (u + 2))
    [Category.{u + 1} A] [HasColimitsOfSize.{u + 1, u + 1} A] {S T : B.Scheme} (g : T ⟶ S)
    (P : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ A) :
    (smallEtaleBaseChange B g).op.HasPointwiseLeftKanExtension P := fun Y => by
  let _ := hasColimitsOfShape_of_essentiallySmall.{u + 1}
    (CostructuredArrow (smallEtaleBaseChange B g).op Y) A
  infer_instance

/-- The forgetful functor from abelian groups preserves the colimits computing inverse image
along small étale base change, these being filtered. -/
public theorem smallEtaleBaseChange_preservesColimitsOfShape_forget {S T : B.Scheme} (g : T ⟶ S)
    (Y : (SmallEtale B T.obj T.property)ᵒᵖ) :
    PreservesColimitsOfShape (CostructuredArrow (smallEtaleBaseChange B g).op Y)
      (forget AddCommGrpCat.{u + 1}) := by
  let _ : IsFiltered (CostructuredArrow (smallEtaleBaseChange B g).op Y) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange B g) Y.unop)
  let _ : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1}
      (forget AddCommGrpCat.{u + 1})
  exact PreservesFilteredColimitsOfSize.preserves_filtered_colimits _

attribute [local instance] smallEtaleBaseChange_op_hasPointwiseLeftKanExtension
  smallEtaleBaseChange_preservesColimitsOfShape_forget

variable [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **Inverse image commutes with passing to the underlying sheaf of sets** (Stacks 00YT), as the
canonical isomorphism `CategoryTheory.Functor.sheafPullbackSheafComposeIso`. -/
public def smallEtaleUnderlyingSetPullbackIso {S T : B.Scheme} (g : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}) :
    (smallEtaleSheafPullback B (Type (u + 1)) g).obj ((smallEtaleUnderlyingSetSheaf B S).obj F) ≅
      (smallEtaleUnderlyingSetSheaf B T).obj
        ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).obj F) :=
  (smallEtaleBaseChange B g).sheafPullbackSheafComposeIso AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
    (forget AddCommGrpCat.{u + 1}) F

/-- Naturality of `AlgebraicGeometry.smallEtaleUnderlyingSetPullbackIso`. -/
@[reassoc]
public theorem smallEtaleUnderlyingSetPullbackIso_hom_naturality {S T : B.Scheme} (g : T ⟶ S)
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}} (x : F ⟶ G) :
    (smallEtaleSheafPullback B (Type (u + 1)) g).map ((smallEtaleUnderlyingSetSheaf B S).map x) ≫
        (smallEtaleUnderlyingSetPullbackIso B g G).hom =
      (smallEtaleUnderlyingSetPullbackIso B g F).hom ≫
        (smallEtaleUnderlyingSetSheaf B T).map
          ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).map x) :=
  Functor.sheafPullbackSheafComposeHom_naturality _ _ _ _ _ x

/-- Naturality of the inverse of `AlgebraicGeometry.smallEtaleUnderlyingSetPullbackIso`. -/
@[reassoc]
public theorem smallEtaleUnderlyingSetPullbackIso_inv_naturality {S T : B.Scheme} (g : T ⟶ S)
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}} (x : F ⟶ G) :
    (smallEtaleUnderlyingSetSheaf B T).map
          ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).map x) ≫
        (smallEtaleUnderlyingSetPullbackIso B g G).inv =
      (smallEtaleUnderlyingSetPullbackIso B g F).inv ≫
        (smallEtaleSheafPullback B (Type (u + 1)) g).map
          ((smallEtaleUnderlyingSetSheaf B S).map x) := by
  rw [Iso.comp_inv_eq, Category.assoc, smallEtaleUnderlyingSetPullbackIso_hom_naturality,
    Iso.inv_hom_id_assoc]

/-- **The comparison with underlying sheaves of sets is compatible with the composition of inverse
images** along a named composite `f ≫ g = h`. -/
public theorem smallEtaleUnderlyingSetPullbackIso_comp {X Y Z : B.Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h)
    (F : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1}) :
    (smallEtaleSheafPullbackCompIso' B (Type (u + 1)) f g h e).hom.app
          ((smallEtaleUnderlyingSetSheaf B Z).obj F) ≫
        (smallEtaleUnderlyingSetPullbackIso B h F).hom =
      (smallEtaleSheafPullback B (Type (u + 1)) f).map
          (smallEtaleUnderlyingSetPullbackIso B g F).hom ≫
        (smallEtaleUnderlyingSetPullbackIso B f
          ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).obj F)).hom ≫
        (smallEtaleUnderlyingSetSheaf B X).map
          ((smallEtaleSheafPullbackCompIso' B AddCommGrpCat.{u + 1} f g h e).hom.app F) := by
  rw [smallEtaleSheafPullbackCompIso'_eq, smallEtaleSheafPullbackCompIso'_eq]
  exact Functor.sheafPullbackComp'_hom_app_comp_sheafPullbackSheafComposeHom _ _ _ _ _ _ F

/-- Transport of a map between the sheaves of sets underlying two abelian sheaves along inverse
image: inverse image of the map, read through the comparisons with underlying sheaves of sets. -/
public abbrev smallEtaleUnderlyingSetTransport {S T : B.Scheme} (g : T ⟶ S)
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (ψ : (smallEtaleUnderlyingSetSheaf B S).obj F ⟶ (smallEtaleUnderlyingSetSheaf B S).obj G) :
    (smallEtaleUnderlyingSetSheaf B T).obj
        ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).obj F) ⟶
      (smallEtaleUnderlyingSetSheaf B T).obj
        ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).obj G) :=
  (smallEtaleUnderlyingSetPullbackIso B g F).inv ≫
    (smallEtaleSheafPullback B (Type (u + 1)) g).map ψ ≫
    (smallEtaleUnderlyingSetPullbackIso B g G).hom

public theorem smallEtaleUnderlyingSetTransport_map {S T : B.Scheme} (g : T ⟶ S)
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}} (a : F ⟶ G) :
    smallEtaleUnderlyingSetTransport B g ((smallEtaleUnderlyingSetSheaf B S).map a) =
      (smallEtaleUnderlyingSetSheaf B T).map
        ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).map a) := by
  rw [smallEtaleUnderlyingSetTransport, smallEtaleUnderlyingSetPullbackIso_hom_naturality,
    Iso.inv_hom_id_assoc]

public theorem smallEtaleUnderlyingSetTransport_comp {S T : B.Scheme} (g : T ⟶ S)
    {F G H : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (ψ : (smallEtaleUnderlyingSetSheaf B S).obj F ⟶ (smallEtaleUnderlyingSetSheaf B S).obj G)
    (ψ' : (smallEtaleUnderlyingSetSheaf B S).obj G ⟶ (smallEtaleUnderlyingSetSheaf B S).obj H) :
    smallEtaleUnderlyingSetTransport B g (ψ ≫ ψ') =
      smallEtaleUnderlyingSetTransport B g ψ ≫ smallEtaleUnderlyingSetTransport B g ψ' := by
  simp [smallEtaleUnderlyingSetTransport]

public theorem smallEtaleUnderlyingSetTransport_injective {S T : B.Scheme} (g : T ⟶ S)
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    {ψ ψ' : (smallEtaleUnderlyingSetSheaf B S).obj F ⟶ (smallEtaleUnderlyingSetSheaf B S).obj G}
    (h : smallEtaleUnderlyingSetTransport B g ψ = smallEtaleUnderlyingSetTransport B g ψ') :
    (smallEtaleSheafPullback B (Type (u + 1)) g).map ψ =
      (smallEtaleSheafPullback B (Type (u + 1)) g).map ψ' := by
  simpa [smallEtaleUnderlyingSetTransport] using h

public theorem smallEtaleUnderlyingSetTransport_congr {S T : B.Scheme} (g : T ⟶ S)
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    {ψ ψ' : (smallEtaleUnderlyingSetSheaf B S).obj F ⟶ (smallEtaleUnderlyingSetSheaf B S).obj G}
    (h : (smallEtaleSheafPullback B (Type (u + 1)) g).map ψ =
      (smallEtaleSheafPullback B (Type (u + 1)) g).map ψ') :
    smallEtaleUnderlyingSetTransport B g ψ = smallEtaleUnderlyingSetTransport B g ψ' := by
  rw [smallEtaleUnderlyingSetTransport, h]

/-- Transport of the first additivity map. -/
public theorem smallEtaleUnderlyingSetTransport_forgetAddLeft {S T : B.Scheme} (g : T ⟶ S)
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (b : BinaryBicone F F)
    (ψ : (smallEtaleUnderlyingSetSheaf B S).obj F ⟶ (smallEtaleUnderlyingSetSheaf B S).obj G) :
    smallEtaleUnderlyingSetTransport B g (Sheaf.forgetAddLeft b ψ) =
      Sheaf.forgetAddLeft ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).mapBinaryBicone b)
        (smallEtaleUnderlyingSetTransport B g ψ) := by
  dsimp only [Sheaf.forgetAddLeft]
  rw [smallEtaleUnderlyingSetTransport_comp,
    smallEtaleUnderlyingSetTransport_map, Functor.map_add]
  rfl

/-- Transport of the second additivity map. -/
public theorem smallEtaleUnderlyingSetTransport_forgetAddRight {S T : B.Scheme} (g : T ⟶ S)
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (b : BinaryBicone F F) (c : BinaryBicone G G) (hc : c.fst ≫ c.inl + c.snd ≫ c.inr = 𝟙 c.pt)
    (ψ : (smallEtaleUnderlyingSetSheaf B S).obj F ⟶ (smallEtaleUnderlyingSetSheaf B S).obj G) :
    smallEtaleUnderlyingSetTransport B g (Sheaf.forgetAddRight b c ψ) =
      Sheaf.forgetAddRight ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).mapBinaryBicone b)
        ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).mapBinaryBicone c)
        (smallEtaleUnderlyingSetTransport B g ψ) := by
  set q := smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g
  have hq : q.map c.fst ≫ q.map c.inl + q.map c.snd ≫ q.map c.inr = 𝟙 (q.obj c.pt) := by
    rw [← q.map_comp, ← q.map_comp, ← q.map_add, hc, q.map_id]
  dsimp only [Sheaf.forgetAddRight]
  rw [smallEtaleUnderlyingSetTransport_comp,
    smallEtaleUnderlyingSetTransport_map, Functor.map_add]
  congr 1
  refine Sheaf.forget_hom_ext_of_total hq ?_ ?_
  · have e₁ : smallEtaleUnderlyingSetTransport B g (Sheaf.forgetLift
          (Z := (smallEtaleUnderlyingSetSheaf B S).obj b.pt) c.inl c.inr
          ((smallEtaleUnderlyingSetSheaf B S).map b.fst ≫ ψ)
          ((smallEtaleUnderlyingSetSheaf B S).map b.snd ≫ ψ)) ≫
          (smallEtaleUnderlyingSetSheaf B T).map (q.map c.fst) =
        (smallEtaleUnderlyingSetSheaf B T).map (q.map b.fst) ≫
          smallEtaleUnderlyingSetTransport B g ψ := by
      rw [← smallEtaleUnderlyingSetTransport_map B g c.fst,
        ← smallEtaleUnderlyingSetTransport_comp, Sheaf.forgetLift_comp_map c.inl_fst c.inr_fst,
        smallEtaleUnderlyingSetTransport_comp, smallEtaleUnderlyingSetTransport_map]
    have e₂ := Sheaf.forgetLift_comp_map (G := q.obj G) (H := q.obj c.pt) (p := q.map c.fst)
      (i₁ := q.map c.inl) (i₂ := q.map c.inr)
      (by rw [← q.map_comp, c.inl_fst, q.map_id]) (by rw [← q.map_comp, c.inr_fst, q.map_zero])
      ((smallEtaleUnderlyingSetSheaf B T).map (q.map b.fst) ≫
        smallEtaleUnderlyingSetTransport B g ψ)
      ((smallEtaleUnderlyingSetSheaf B T).map (q.map b.snd) ≫
        smallEtaleUnderlyingSetTransport B g ψ)
    exact e₁.trans e₂.symm
  · have e₁ : smallEtaleUnderlyingSetTransport B g (Sheaf.forgetLift
          (Z := (smallEtaleUnderlyingSetSheaf B S).obj b.pt) c.inl c.inr
          ((smallEtaleUnderlyingSetSheaf B S).map b.fst ≫ ψ)
          ((smallEtaleUnderlyingSetSheaf B S).map b.snd ≫ ψ)) ≫
          (smallEtaleUnderlyingSetSheaf B T).map (q.map c.snd) =
        (smallEtaleUnderlyingSetSheaf B T).map (q.map b.snd) ≫
          smallEtaleUnderlyingSetTransport B g ψ := by
      rw [← smallEtaleUnderlyingSetTransport_map B g c.snd,
        ← smallEtaleUnderlyingSetTransport_comp, Sheaf.forgetLift_comp_map' c.inl_snd c.inr_snd,
        smallEtaleUnderlyingSetTransport_comp, smallEtaleUnderlyingSetTransport_map]
    have e₂ := Sheaf.forgetLift_comp_map' (G := q.obj G) (H := q.obj c.pt) (p := q.map c.snd)
      (i₁ := q.map c.inl) (i₂ := q.map c.inr)
      (by rw [← q.map_comp, c.inl_snd, q.map_zero]) (by rw [← q.map_comp, c.inr_snd, q.map_id])
      ((smallEtaleUnderlyingSetSheaf B T).map (q.map b.fst) ≫
        smallEtaleUnderlyingSetTransport B g ψ)
      ((smallEtaleUnderlyingSetSheaf B T).map (q.map b.snd) ≫
        smallEtaleUnderlyingSetTransport B g ψ)
    exact e₁.trans e₂.symm

/-- The homomorphism `Z/NZ ⟶ A` sending `1` to an element `x` of `A` killed by `N`. -/
public def uliftZModHomOfNsmulEqZero {A : AddCommGrpCat.{u + 1}} (N : ℕ) (x : A)
    (hx : N • x = 0) : AddCommGrpCat.of (ULift.{u + 1} (ZMod N)) ⟶ A :=
  AddCommGrpCat.ofHom ((ZMod.lift N ⟨zmultiplesHom A x, by simpa using hx⟩).comp
    AddEquiv.ulift.toAddMonoidHom)

public theorem uliftZModHomOfNsmulEqZero_apply_intCast {A : AddCommGrpCat.{u + 1}} (N : ℕ)
    (x : A) (hx : N • x = 0) (n : ℤ) :
    uliftZModHomOfNsmulEqZero N x hx (ULift.up (n : ZMod N)) = n • x :=
  (ZMod.lift_coe N ⟨zmultiplesHom A x, by simpa using hx⟩ n).trans (zmultiplesHom_apply _ x n)

public theorem uliftZModHomOfNsmulEqZero_apply_one {A : AddCommGrpCat.{u + 1}} (N : ℕ) (x : A)
    (hx : N • x = 0) : uliftZModHomOfNsmulEqZero N x hx (ULift.up 1) = x := by
  simpa using uliftZModHomOfNsmulEqZero_apply_intCast N x hx 1

public theorem uliftZModHomOfNsmulEqZero_comp {A A' : AddCommGrpCat.{u + 1}} (N : ℕ) (x : A)
    (hx : N • x = 0) (φ : A ⟶ A') :
    uliftZModHomOfNsmulEqZero N x hx ≫ φ =
      uliftZModHomOfNsmulEqZero N (φ x) (by rw [← map_nsmul, hx, map_zero]) := by
  ext ⟨y⟩
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y
  rw [ConcreteCategory.comp_apply, uliftZModHomOfNsmulEqZero_apply_intCast,
    uliftZModHomOfNsmulEqZero_apply_intCast, map_zsmul]

attribute [local instance] AddCommGrpCat.coyonedaObj_isRightAdjoint

/-- For an abelian sheaf `F` killed by `N`, the map from its sheaf of sets to the sheaf of
homomorphisms out of `Z/NZ` sending a section `x` to the homomorphism `1 ↦ x`. -/
public def smallEtaleTorsionSectionsHom (X : B.Scheme) (N : ℕ)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : ∀ (V : (SmallEtale B X.obj X.property)ᵒᵖ) (x : F.obj.obj V), N • x = 0) :
    (smallEtaleUnderlyingSetSheaf B X).obj F ⟶
      (sheafCompose (SmallEtale.topology B X.obj X.property)
        (coyoneda.obj (op (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))))).obj F :=
  ObjectProperty.homMk
    { app := fun V => ↾fun x => uliftZModHomOfNsmulEqZero N (x : F.obj.obj V) (hF V x)
      naturality := fun V W f => by
        ext x
        exact (uliftZModHomOfNsmulEqZero_comp N (x : F.obj.obj V) (hF V x) (F.obj.map f)).symm }

omit [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint] in
/-- **A constructible abelian sheaf killed by `N` is a quotient of the copower sheaf by `Z/NZ` on
its sheaf of sets**: the adjoint transpose of
`AlgebraicGeometry.smallEtaleTorsionSectionsHom` is an epimorphism, since two maps out of `F` that
agree after it agree on every section `x`, the image of the generator of the summand at `x`. -/
public theorem epi_homEquiv_symm_smallEtaleTorsionSectionsHom (X : B.Scheme) (N : ℕ)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : ∀ (V : (SmallEtale B X.obj X.property)ᵒᵖ) (x : F.obj.obj V), N • x = 0) :
    Epi (((Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
      (AddCommGrpCat.copowerAdj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).homEquiv _ _).symm
        (smallEtaleTorsionSectionsHom B X N F hF)) := by
  constructor
  intro Q g h hgh
  have e := congrArg ((Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
    (AddCommGrpCat.copowerAdj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).homEquiv _ _) hgh
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply] at e
  ext V x
  have ex := ConcreteCategory.congr_hom (Sheaf.hom_app_apply_congr e V x) (ULift.up 1)
  change g.hom.app V (uliftZModHomOfNsmulEqZero N x (hF V x) (ULift.up 1)) =
    h.hom.app V (uliftZModHomOfNsmulEqZero N x (hF V x) (ULift.up 1)) at ex
  rwa [uliftZModHomOfNsmulEqZero_apply_one] at ex

omit [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}] in
/-- An abelian sheaf killed by `N` has every section killed by `N`. -/
public theorem nsmul_eq_zero_of_nsmul_id_eq_zero (X : B.Scheme)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} {N : ℕ}
    (h : N • 𝟙 F = 0) (V : (SmallEtale B X.obj X.property)ᵒᵖ) (x : F.obj.obj V) : N • x = 0 := by
  have key : ∀ (n : ℕ) (y : F.obj.obj V), (n • 𝟙 F).hom.app V y = n • y := by
    intro n y
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [succ_nsmul, succ_nsmul, ← ih]
      rfl
  rw [← key, h]
  rfl

section Stages

variable {I : Type u} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- The sheaf of sets underlying the stage comparison of abelian sheaves, through the
comparisons with underlying sheaves of sets, is the stage comparison of sheaves of sets. -/
public theorem smallEtaleUnderlyingSetSheaf_map_stageComparison_hom {i j : I} (h : i ≤ j)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      AddCommGrpCat.{u + 1}) :
    (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map
        (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h F).hom =
      (smallEtaleUnderlyingSetPullbackIso B (coneStageHom B Dg c hX j)
          ((smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).obj F)).inv ≫
        (smallEtaleStageProjection B (Type (u + 1)) Dg c hX j).map
          (smallEtaleUnderlyingSetPullbackIso B (systemStageHom B Dg h) F).inv ≫
        (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h
          ((smallEtaleUnderlyingSetSheaf B (Dg.obj (op i))).obj F)).hom ≫
        (smallEtaleUnderlyingSetPullbackIso B (coneStageHom B Dg c hX i) F).hom := by
  rw [smallEtaleStageComparison_eq, smallEtaleStageComparison_eq]
  simp only [Iso.app_hom]
  rw [smallEtaleUnderlyingSetPullbackIso_comp B (coneStageHom B Dg c hX j)
    (systemStageHom B Dg h) (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX h) F]
  simp

/-- **Additivity descends.** A map between the sheaves of sets underlying two constructible
abelian sheaves at a stage whose transport to the vertex is additive has additive transport to some
later stage. Additivity is the equality of two maps out of the sheaf of sets underlying `F ⊞ F`,
which is constructible, so faithfulness for sheaves of sets (Tag 09YU, clause (1)) applies. -/
public theorem exists_forgetAdditive_smallEtaleUnderlyingSetTransport
    (hfaith : SmallEtaleStagesFaithful B (Type (u + 1)) Dg c hX
      (fun Y => IsConstructibleSetSheaf B Y)) {j : I}
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
      AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleAbelianSheaf B (Dg.obj (op j)) F)
    (hG : IsConstructibleAbelianSheaf B (Dg.obj (op j)) G)
    (ψ : (smallEtaleUnderlyingSetSheaf B (Dg.obj (op j))).obj F ⟶
      (smallEtaleUnderlyingSetSheaf B (Dg.obj (op j))).obj G)
    (a : (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX j).obj F ⟶
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX j).obj G)
    (ha : smallEtaleUnderlyingSetTransport B (coneStageHom B Dg c hX j) ψ =
      (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map a) :
    ∃ (k : I) (h : j ≤ k) (d : (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).obj F ⟶
        (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).obj G),
      (smallEtaleUnderlyingSetSheaf B (Dg.obj (op k))).map d =
        smallEtaleUnderlyingSetTransport B (systemStageHom B Dg h) ψ := by
  let b := BinaryBiproduct.bicone F F
  let b' := BinaryBiproduct.bicone G G
  have hb' : b'.fst ≫ b'.inl + b'.snd ≫ b'.inr = 𝟙 b'.pt := biprod.total
  have hbs : IsConstructibleSetSheaf B _ ((smallEtaleUnderlyingSetSheaf B _).obj b.pt) :=
    isConstructibleSetSheaf_underlying B _ (smallEtaleUnderlyingSetCommutes B _)
      (isConstructibleAbelianSheaf_of_shortExact B _
        (ShortComplex.Splitting.ofHasBinaryBiproduct F F).shortExact hF hF)
  have hGs : IsConstructibleSetSheaf B _ ((smallEtaleUnderlyingSetSheaf B _).obj G) :=
    isConstructibleSetSheaf_underlying B _ (smallEtaleUnderlyingSetCommutes B _) hG
  have := additive_smallEtaleAbelianPullback B (coneStageHom B Dg c hX j)
  have hvert := Sheaf.forgetAddLeft_eq_forgetAddRight
    ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX j)).mapBinaryBicone b)
    ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1}
      (coneStageHom B Dg c hX j)).mapBinaryBicone b')
    _ (Sheaf.forgetAdditive_map a)
  rw [← ha, ← smallEtaleUnderlyingSetTransport_forgetAddLeft,
    ← smallEtaleUnderlyingSetTransport_forgetAddRight _ _ _ _ hb'] at hvert
  obtain ⟨k, h, hk⟩ := hfaith j _ _ hbs hGs _ _
    (smallEtaleUnderlyingSetTransport_injective B _ hvert)
  have := additive_smallEtaleAbelianPullback B (systemStageHom B Dg h)
  have hk' : Sheaf.forgetAddLeft
      ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} (systemStageHom B Dg h)).mapBinaryBicone b)
      (smallEtaleUnderlyingSetTransport B (systemStageHom B Dg h) ψ) =
    Sheaf.forgetAddRight
      ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} (systemStageHom B Dg h)).mapBinaryBicone b)
      ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} (systemStageHom B Dg h)).mapBinaryBicone b')
      (smallEtaleUnderlyingSetTransport B (systemStageHom B Dg h) ψ) := by
    rw [← smallEtaleUnderlyingSetTransport_forgetAddLeft,
      ← smallEtaleUnderlyingSetTransport_forgetAddRight _ _ _ _ hb']
    exact smallEtaleUnderlyingSetTransport_congr B _ hk
  exact ⟨k, h, Sheaf.homOfForgetAdditive.{u, u + 1, u + 1} _
    (Sheaf.forgetAdditive_of_forgetAddLeft_eq_forgetAddRight.{u, u + 1, u + 1} _ _ _ hk'), rfl⟩

/-- **A realization of the underlying map of sheaves of sets gives a transport.** If a map `b` of
sheaves of sets at the stage `j` realizes the map underlying `a`, read through the comparisons
with underlying sheaves of sets, then the corresponding map between the sheaves of sets underlying
the inverse images of `F` and `G` to the stage `j` transports to the vertex as the map underlying
`a`, read through the comparisons of abelian sheaves. -/
public theorem smallEtaleUnderlyingSetTransport_of_realizes {i j : I} (h : i ≤ j)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      AddCommGrpCat.{u + 1}}
    (a : (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).obj G)
    (b : (smallEtaleStageTransition B (Type (u + 1)) Dg h).obj
        ((smallEtaleUnderlyingSetSheaf B (Dg.obj (op i))).obj F) ⟶
      (smallEtaleStageTransition B (Type (u + 1)) Dg h).obj
        ((smallEtaleUnderlyingSetSheaf B (Dg.obj (op i))).obj G))
    (hb : (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h
          ((smallEtaleUnderlyingSetSheaf B (Dg.obj (op i))).obj F)).inv ≫
        (smallEtaleStageProjection B (Type (u + 1)) Dg c hX j).map b ≫
        (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h
          ((smallEtaleUnderlyingSetSheaf B (Dg.obj (op i))).obj G)).hom =
      (smallEtaleUnderlyingSetPullbackIso B (coneStageHom B Dg c hX i) F).hom ≫
        (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map a ≫
        (smallEtaleUnderlyingSetPullbackIso B (coneStageHom B Dg c hX i) G).inv) :
    smallEtaleUnderlyingSetTransport B (coneStageHom B Dg c hX j)
        ((smallEtaleUnderlyingSetPullbackIso B (systemStageHom B Dg h) F).inv ≫ b ≫
          (smallEtaleUnderlyingSetPullbackIso B (systemStageHom B Dg h) G).hom) =
      (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map
        ((smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h F).hom ≫ a ≫
          (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h G).inv) := by
  rw [← cancel_mono ((smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map
    (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h G).hom), ← Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Functor.map_comp (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX))
      (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h F).hom a,
    smallEtaleUnderlyingSetSheaf_map_stageComparison_hom,
    smallEtaleUnderlyingSetSheaf_map_stageComparison_hom]
  rw [Iso.inv_comp_eq] at hb
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_map_assoc]
  rw [reassoc_of% hb]
  simp

/-- **A transport realized at a later stage gives a realization.** -/
public theorem realizes_of_smallEtaleUnderlyingSetTransport {j k : I} (h : j ≤ k)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
      AddCommGrpCat.{u + 1}}
    (ψ : (smallEtaleUnderlyingSetSheaf B (Dg.obj (op j))).obj F ⟶
      (smallEtaleUnderlyingSetSheaf B (Dg.obj (op j))).obj G)
    (a : (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX j).obj F ⟶
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX j).obj G)
    (ha : smallEtaleUnderlyingSetTransport B (coneStageHom B Dg c hX j) ψ =
      (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map a)
    (d : (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).obj F ⟶
      (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).obj G)
    (hd : (smallEtaleUnderlyingSetSheaf B (Dg.obj (op k))).map d =
      smallEtaleUnderlyingSetTransport B (systemStageHom B Dg h) ψ) :
    (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h F).inv ≫
        (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX k).map d ≫
        (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h G).hom = a := by
  rw [Iso.inv_comp_eq]
  apply Sheaf.sheafCompose_forget_map_injective
  have hnat : (smallEtaleStageProjection B (Type (u + 1)) Dg c hX k).map
        ((smallEtaleStageTransition B (Type (u + 1)) Dg h).map ψ) ≫
        (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h
          ((smallEtaleUnderlyingSetSheaf B (Dg.obj (op j))).obj G)).hom =
      (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h
          ((smallEtaleUnderlyingSetSheaf B (Dg.obj (op j))).obj F)).hom ≫
        (smallEtaleStageProjection B (Type (u + 1)) Dg c hX j).map ψ := by
    simp only [smallEtaleStageComparison_eq, Iso.app_hom]
    exact (smallEtaleSheafPullbackCompIso' B _ _ _ _
      (coneStageHom_comp B Dg c hX h)).hom.naturality ψ
  rw [Functor.map_comp, Functor.map_comp]
  change (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map
      ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX k)).map d) ≫
      (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map
        (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h G).hom =
    (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map
        (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h F).hom ≫
      (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map a
  rw [← smallEtaleUnderlyingSetTransport_map, hd, ← ha,
    smallEtaleUnderlyingSetSheaf_map_stageComparison_hom,
    smallEtaleUnderlyingSetSheaf_map_stageComparison_hom]
  simp only [smallEtaleUnderlyingSetTransport, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_map_assoc]
  rw [reassoc_of% hnat]

/-- **Stacks 09YU, clause (2), the fullness assertion.** Let `X = lim X_i` be the limit of a
directed inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms inside a big étale site. Every map between the inverse images to `X_étale` of two
constructible abelian sheaves on `(X_i)_étale` is the inverse image of a map between their inverse
images to some later stage, read through the canonical comparisons.

The map of underlying sheaves of sets comes from a stage by clause (1), the underlying sheaves of
sets being constructible; its additivity, which holds on `X`, holds at a later stage by
`AlgebraicGeometry.exists_forgetAdditive_smallEtaleUnderlyingSetTransport`, where it is therefore a
map of abelian sheaves; and that map realizes the given one because passing to underlying sheaves
of sets is faithful and compatible with inverse image and with its comparisons. -/
public theorem smallEtaleStagesFull_isConstructibleAbelianSheaf [Nonempty I]
    [IsDirected I (· ≤ ·)] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFull B AddCommGrpCat.{u + 1} Dg c hX
      (fun Y => IsConstructibleAbelianSheaf B Y) := by
  intro i F G hF hG a
  have hFs := isConstructibleSetSheaf_underlying B _ (smallEtaleUnderlyingSetCommutes B _) hF
  have hGs := isConstructibleSetSheaf_underlying B _ (smallEtaleUnderlyingSetCommutes B _) hG
  obtain ⟨j, h, b, hb⟩ := smallEtaleStagesFull_isConstructibleSetSheaf B Dg c hX hc haff hqc hqs
    i _ _ hFs hGs ((smallEtaleUnderlyingSetPullbackIso B (coneStageHom B Dg c hX i) F).hom ≫
      (smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).map a ≫
      (smallEtaleUnderlyingSetPullbackIso B (coneStageHom B Dg c hX i) G).inv)
  have hψ := smallEtaleUnderlyingSetTransport_of_realizes B Dg c hX h a b hb
  obtain ⟨k, hjk, d, hd⟩ := exists_forgetAdditive_smallEtaleUnderlyingSetTransport B Dg c hX
    (smallEtaleStagesFaithful_isConstructibleSetSheaf B Dg c hX hc haff hqc hqs)
    (isConstructibleFiniteSheaf_pullback B (systemStageHom B Dg h) F hF)
    (isConstructibleFiniteSheaf_pullback B (systemStageHom B Dg h) G hG) _ _ hψ
  have hreal := realizes_of_smallEtaleUnderlyingSetTransport B Dg c hX hjk _ _ hψ d hd
  obtain ⟨m, him, him', b', hb'⟩ := SmallEtaleVertexHomLifts.of_conj_comparison h h
    (a := a) ⟨k, hjk, hjk, d, hreal⟩
  exact ⟨m, him, b', hb'⟩

/-- **Stacks 09YU, clause (2), the essential surjectivity assertion.** Let `X = lim X_i` be the
limit of a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms inside a big étale site. Every constructible abelian sheaf on `X_étale` is
isomorphic to the inverse image of a constructible abelian sheaf on `(X_i)_étale` for some `i`.

A constructible abelian sheaf `F` on the quasi-compact quasi-separated `X` is killed by some
`N > 0`, so it is a quotient of the copower sheaf by `Z/NZ` on its sheaf of sets, which is a
constructible abelian sheaf; applying this to the kernel too presents `F` as the cokernel of a map
between two such copower sheaves. Their sheaves of sets come from a stage by clause (1), the
copower sheaf commutes with inverse image, the map between them comes from a stage by the fullness
assertion `AlgebraicGeometry.smallEtaleStagesFull_isConstructibleAbelianSheaf`, and inverse image,
being exact, carries the cokernel at that stage to `F`. -/
public theorem smallEtaleStagesEssSurj_isConstructibleAbelianSheaf [Nonempty I]
    [IsDirected I (· ≤ ·)] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B AddCommGrpCat.{u + 1} Dg c hX
      (fun Y => IsConstructibleAbelianSheaf B Y) := by
  have haff' : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) :=
    fun e => haff e
  have hqc' : ∀ p : Iᵒᵖ, CompactSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqc p.unop
  have hqs' : ∀ p : Iᵒᵖ, QuasiSeparatedSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqs p.unop
  obtain ⟨hcpt, hqpt⟩ := compactSpace_and_quasiSeparatedSpace_pt (Dg ⋙ B.inclusion) c hc
  have : HasCokernels (Sheaf (SmallEtale.topology B c.pt hX) AddCommGrpCat.{u + 1}) :=
    inferInstance
  have : HasCokernels (Sheaf (SmallEtale.topology B (B.obj c.pt hX).obj
      (B.obj c.pt hX).property) AddCommGrpCat.{u + 1}) := inferInstance
  intro F hF
  -- a constructible abelian sheaf on `X` is a quotient of a copower sheaf on its sheaf of sets
  have gen : ∀ Q : Sheaf (SmallEtale.topology B c.pt hX) AddCommGrpCat.{u + 1},
      IsConstructibleAbelianSheaf B (B.obj c.pt hX) Q → ∃ (N : ℕ) (_ : NeZero N)
        (p : (Sheaf.composeAndSheafify (SmallEtale.topology B c.pt hX)
          (AddCommGrpCat.copower (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).obj
            ((smallEtaleUnderlyingSetSheaf B (B.obj c.pt hX)).obj Q) ⟶ Q), Epi p := by
    intro Q hQ
    obtain ⟨N, hN, hNQ⟩ := exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf B
      (B.obj c.pt hX) hcpt hqpt Q hQ
    exact ⟨N, ⟨hN.ne'⟩, _, epi_homEquiv_symm_smallEtaleTorsionSectionsHom B (B.obj c.pt hX) N Q
      (nsmul_eq_zero_of_nsmul_id_eq_zero B (B.obj c.pt hX) hNQ)⟩
  obtain ⟨N₁, hN₁, p₁, hp₁⟩ := gen F hF
  have hFs := isConstructibleSetSheaf_underlying B _ (smallEtaleUnderlyingSetCommutes B _) hF
  have hL₁ := isConstructibleAbelianSheaf_composeAndSheafify_copower B (B.obj c.pt hX)
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod N₁))) _ hFs
  have hK := isConstructibleAbelianSheaf_kernel B (B.obj c.pt hX) p₁ hL₁ hF
  obtain ⟨N₂, hN₂, p₂, hp₂⟩ := gen _ hK
  have hKs := isConstructibleSetSheaf_underlying B _ (smallEtaleUnderlyingSetCommutes B _) hK
  -- the two sheaves of sets come from a common stage
  obtain ⟨i, P, hP, ⟨eP⟩⟩ :=
    smallEtaleStagesEssSurj_isConstructibleSetSheaf B Dg c hX hc haff hqc hqs _ hFs
  obtain ⟨l, Q, hQ, ⟨eQ⟩⟩ :=
    smallEtaleStagesEssSurj_isConstructibleSetSheaf B Dg c hX hc haff hqc hqs _ hKs
  obtain ⟨m, him, hlm⟩ := directed_of (· ≤ ·) i l
  have hP' := isConstructibleFiniteSheaf_pullback B (systemStageHom B Dg him) P hP
  have hQ' := isConstructibleFiniteSheaf_pullback B (systemStageHom B Dg hlm) Q hQ
  have : Finite (AddCommGrpCat.of (ULift.{u + 1} (ZMod N₁))) := by
    change Finite (ULift (ZMod N₁)); infer_instance
  have : Finite (AddCommGrpCat.of (ULift.{u + 1} (ZMod N₂))) := by
    change Finite (ULift (ZMod N₂)); infer_instance
  have hA₁ := isConstructibleAbelianSheaf_composeAndSheafify_copower B (Dg.obj (op m))
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod N₁))) _ hP'
  have hA₂ := isConstructibleAbelianSheaf_composeAndSheafify_copower B (Dg.obj (op m))
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod N₂))) _ hQ'
  -- the copower sheaves on them are inverse images of copower sheaves at the stage
  let φ₁ := (Sheaf.composeAndSheafifyCopowerSheafPullbackIso
      (SmallEtale.topology B (Dg.obj (op m)).obj (Dg.obj (op m)).property)
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N₁))) (SmallEtale.topology B c.pt hX)
      (smallEtaleBaseChange B (coneStageHom B Dg c hX m))).app
        ((smallEtaleStageTransition B (Type (u + 1)) Dg him).obj P) ≪≫
    (Sheaf.composeAndSheafify (SmallEtale.topology B c.pt hX)
      (AddCommGrpCat.copower (AddCommGrpCat.of (ULift.{u + 1} (ZMod N₁))))).mapIso
      (smallEtaleStageComparison B (Type (u + 1)) Dg c hX him P ≪≫ eP)
  let φ₂ := (Sheaf.composeAndSheafifyCopowerSheafPullbackIso
      (SmallEtale.topology B (Dg.obj (op m)).obj (Dg.obj (op m)).property)
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N₂))) (SmallEtale.topology B c.pt hX)
      (smallEtaleBaseChange B (coneStageHom B Dg c hX m))).app
        ((smallEtaleStageTransition B (Type (u + 1)) Dg hlm).obj Q) ≪≫
    (Sheaf.composeAndSheafify (SmallEtale.topology B c.pt hX)
      (AddCommGrpCat.copower (AddCommGrpCat.of (ULift.{u + 1} (ZMod N₂))))).mapIso
      (smallEtaleStageComparison B (Type (u + 1)) Dg c hX hlm Q ≪≫ eQ)
  -- the presenting map comes from a stage
  obtain ⟨m', h, β, hβ⟩ := smallEtaleStagesFull_isConstructibleAbelianSheaf B Dg c hX hc haff hqc
    hqs m _ _ hA₂ hA₁ (φ₂.hom ≫ (p₂ ≫ kernel.ι p₁) ≫ φ₁.inv)
  refine ⟨m', cokernel β, isConstructibleAbelianSheaf_cokernel B _ β
    (isConstructibleFiniteSheaf_pullback B _ _ hA₂)
    (isConstructibleFiniteSheaf_pullback B _ _ hA₁), ?_⟩
  have := preservesFiniteColimits_smallEtaleAbelianPullback B (coneStageHom B Dg c hX m')
  have hβ' : (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX m').map β =
      (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h _).hom ≫
        ((φ₂.hom ≫ (p₂ ≫ kernel.ι p₁) ≫ φ₁.inv) ≫
        (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h _).inv) := by
    rw [← hβ]
    simp
  obtain ⟨e⟩ := Abelian.nonempty_cokernel_iso_of_eq_conj_comp_kernel_ι p₁ p₂
    (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h _ ≪≫ φ₂)
    (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h _ ≪≫ φ₁)
    (f := (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX m').map β) (by
      rw [hβ']
      simp)
  exact ⟨PreservesCokernel.iso (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX m') β ≪≫
    e⟩

/-- **Stacks 09YU, clause (2).** Let `X = lim X_i` be the limit of a directed inverse system of
quasi-compact and quasi-separated schemes with affine transition morphisms inside a big étale
site. The category of constructible abelian sheaves on `X_étale` is the colimit of the categories
of constructible abelian sheaves on the `(X_i)_étale`, along étale inverse image: the comparison is
faithful (`AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleAbelianSheaf`), full
(`AlgebraicGeometry.smallEtaleStagesFull_isConstructibleAbelianSheaf`) and essentially surjective
(`AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleAbelianSheaf`), which over a directed
index is the assertion that the category on the limit is the filtered colimit of the categories at
the stages. -/
@[stacks 09YU "clause (2)"]
public theorem smallEtaleStagesColimit_isConstructibleAbelianSheaf [Nonempty I]
    [IsDirected I (· ≤ ·)] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesColimit B AddCommGrpCat.{u + 1} Dg c hX
      (fun Y => IsConstructibleAbelianSheaf B Y) where
  faithful := by
    have : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
        ((SmallEtale.topology B T.obj T.property).over V).WEqualsLocallyBijective
          AddCommGrpCat.{u + 1} := fun _ _ => inferInstance
    exact smallEtaleStagesFaithful_isConstructibleAbelianSheaf B Dg c hX hc haff hqc hqs
  full := smallEtaleStagesFull_isConstructibleAbelianSheaf B Dg c hX hc haff hqc hqs
  essSurj := smallEtaleStagesEssSurj_isConstructibleAbelianSheaf B Dg c hX hc haff hqc hqs

end Stages

end Underlying

end AlgebraicGeometry
