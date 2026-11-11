module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The abstract change of rings adjunction for presheaves of modules

Let `α : 𝒪₁ ⟶ 𝒪₂` be a morphism of presheaves of commutative rings on a small category `C`.
This file packages Mathlib's adjunction
`PresheafOfModules.pullbackPushforwardAdjunction` (specialised to `F = 𝟭 C`) between
Mathlib's pullback `PresheafOfModules.pullback`, an abstract left adjoint of restriction of
scalars obtained from `Functor.leftAdjoint`, and restriction of scalars.

Stacks 006R (Lemma 6.6.2) asserts the universal property of the *explicit* sectionwise tensor
product presheaf `U ↦ 𝒪₂(U) ⊗_{𝒪₁(U)} 𝒢(U)`; that statement is
`Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafAdjunction` and
`Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafHomEquiv`, which carry the tag. The
adjunction of this file holds by construction of `PresheafOfModules.pullback`, so it does not by
itself state 006R. On the site of opens of a topological space, Mathlib's pullback is identified
with the sectionwise tensor product presheaf by `tensorPresheafIsoTensorPresheafFunctor`
(`StacksFrontier/Topology/Sheaves/Presheaf/ModuleChangeOfRingsComparison.lean`).

## Formalization strategy

The index category `C` is an arbitrary small category. A presheaf of commutative rings is a
functor `Cᵒᵖ ⥤ CommRingCat`; we pass to `Cᵒᵖ ⥤ RingCat` (the underlying presheaf of rings) via
`forget₂` whenever the Mathlib API for `PresheafOfModules` is invoked. For `F = 𝟭 C`, the
`pushforward φ` is restriction of scalars along `φ`.
-/

@[expose] public section

universe u


open CategoryTheory PresheafOfModules

variable {C : Type u} [SmallCategory C]

/-- The presheaf of (general) rings underlying a presheaf of commutative rings. -/
abbrev toRingCat (R : Cᵒᵖ ⥤ CommRingCat.{u}) : Cᵒᵖ ⥤ RingCat.{u} :=
  R ⋙ forget₂ CommRingCat RingCat

/-- The morphism of presheaves of (general) rings underlying a morphism of
presheaves of commutative rings.

The target type is `(𝟭 C).op ⋙ toRingCat 𝒪₂` rather than `toRingCat 𝒪₂` (which
is definitionally equal) so that this map plugs directly into Mathlib's
`F`-indexed pullback/pushforward API with `F = 𝟭 C`. -/
abbrev toRingCatMap {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂) :
    toRingCat 𝒪₁ ⟶ (𝟭 C).op ⋙ toRingCat 𝒪₂ :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

/-- **Definition (Presheaf of modules).** The category of presheaves of `R`-modules
over a presheaf of commutative rings `R : Cᵒᵖ ⥤ CommRingCat`. -/
@[sga "4 II 6.7" "special case", sga "7 VI 3.1(a)" "more general"]
abbrev PModuleStruct (R : Cᵒᵖ ⥤ CommRingCat.{u}) : Type _ :=
  PresheafOfModules.{u} (toRingCat R)

/-- **Definition (Restriction of scalars).** Restriction of scalars along a morphism
of presheaves of (commutative) rings `α : 𝒪₁ ⟶ 𝒪₂` is the functor
`PModuleStruct 𝒪₂ ⥤ PModuleStruct 𝒪₁`.

Sectionwise, `((restrictionFunctor α).obj ℱ).obj U` is the abelian group `ℱ(U)`
with the `𝒪₁(U)`-module structure obtained from the `𝒪₂(U)`-module structure on
`ℱ(U)` by restriction along the ring morphism `α.app U : 𝒪₁(U) ⟶ 𝒪₂(U)`. -/
@[sga "4 XVIII 3.1.12.1" "partial"]
noncomputable abbrev restrictionFunctor
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂) :
    PModuleStruct 𝒪₂ ⥤ PModuleStruct 𝒪₁ :=
  PresheafOfModules.pushforward.{u} (F := 𝟭 C) (toRingCatMap α)

/-- **Definition (Tensor product / change-of-rings functor).** Given a morphism
`α : 𝒪₁ ⟶ 𝒪₂` of presheaves of commutative rings, the change-of-rings functor
`𝒪₂ ⊗_{p, 𝒪₁} (-) : PModuleStruct 𝒪₁ ⥤ PModuleStruct 𝒪₂`.

Constructed as Mathlib's `PresheafOfModules.pullback`, an abstract left adjoint of the
restriction functor; nothing in this definition computes its sections. On the site of opens of a
topological space it is isomorphic to the explicit sectionwise tensor product presheaf
`U ↦ 𝒪₂(U) ⊗_{𝒪₁(U)} 𝒢(U)`, by `tensorPresheafIsoTensorPresheafFunctor`. -/
noncomputable abbrev tensorPresheaf
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂) :
    PModuleStruct 𝒪₁ ⥤ PModuleStruct 𝒪₂ :=
  PresheafOfModules.pullback.{u} (F := 𝟭 C) (toRingCatMap α)

/-- The abstract change of rings adjunction: given a morphism `α : 𝒪₁ ⟶ 𝒪₂` of presheaves of
commutative rings on a small category `C`, Mathlib's pullback `tensorPresheaf α` is left adjoint
to the restriction-of-scalars functor `restrictionFunctor α = (-)_{𝒪₁}`.

This is Mathlib's `PresheafOfModules.pullbackPushforwardAdjunction`, specialised to `F = 𝟭 C`,
and holds by construction of the pullback. Stacks 006R, about the explicit sectionwise tensor
product presheaf, is `Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafAdjunction`. -/
noncomputable def tensorPresheafAdj
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂) :
    PresheafOfModules.pullback.{u} (F := 𝟭 C) (toRingCatMap α) ⊣
      PresheafOfModules.pushforward.{u} (F := 𝟭 C) (toRingCatMap α) :=
  PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := 𝟭 C) (toRingCatMap α)

/-- The hom-set bijection `Hom(tensorPresheaf α 𝒢, ℱ) ≃ Hom_{𝒪₁}(𝒢, ℱ_{𝒪₁})` of the abstract
adjunction `tensorPresheafAdj`, natural in both variables `𝒢` and `ℱ`. Stacks 006R, about the
explicit sectionwise tensor product presheaf, is
`Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafHomEquiv`. -/
noncomputable def tensorHomEquiv
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂)
    (𝒢 : PModuleStruct 𝒪₁) (ℱ : PModuleStruct 𝒪₂) :
    ((tensorPresheaf α).obj 𝒢 ⟶ ℱ) ≃ (𝒢 ⟶ (restrictionFunctor α).obj ℱ) :=
  (tensorPresheafAdj α).homEquiv 𝒢 ℱ

/-- Mathlib's pullback `tensorPresheaf α` is a left adjoint; a direct consequence of
`tensorPresheafAdj`. -/
theorem tensorPresheaf_isLeftAdjoint
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂) :
    (tensorPresheaf α).IsLeftAdjoint :=
  (tensorPresheafAdj α).isLeftAdjoint

/-- **Naturality of `tensorHomEquiv` in `ℱ`.**

For a morphism `g : ℱ ⟶ ℱ'` in `PModuleStruct 𝒪₂` and a morphism
`Φ : 𝒪₂ ⊗_{p,𝒪₁} 𝒢 ⟶ ℱ`, postcomposition by `g` corresponds via
`tensorHomEquiv` to postcomposition with `(restrictionFunctor α).map g`. -/
theorem tensorHomEquiv_naturality_right
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂)
    (𝒢 : PModuleStruct 𝒪₁) {ℱ ℱ' : PModuleStruct 𝒪₂} (g : ℱ ⟶ ℱ')
    (Φ : (tensorPresheaf α).obj 𝒢 ⟶ ℱ) :
    tensorHomEquiv α 𝒢 ℱ' (Φ ≫ g) =
      tensorHomEquiv α 𝒢 ℱ Φ ≫ (restrictionFunctor α).map g :=
  (tensorPresheafAdj α).homEquiv_naturality_right Φ g

/-- **Naturality of `tensorHomEquiv` in `𝒢`.**

For a morphism `h : 𝒢 ⟶ 𝒢'` in `PModuleStruct 𝒪₁` and a morphism
`ψ : 𝒢' ⟶ (restrictionFunctor α).obj ℱ`, precomposition by `h` corresponds via
`tensorHomEquiv.symm` to precomposition with `(tensorPresheaf α).map h`. -/
theorem tensorHomEquiv_naturality_left_symm
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂)
    {𝒢 𝒢' : PModuleStruct 𝒪₁} (h : 𝒢 ⟶ 𝒢') (ℱ : PModuleStruct 𝒪₂)
    (ψ : 𝒢' ⟶ (restrictionFunctor α).obj ℱ) :
    (tensorHomEquiv α 𝒢 ℱ).symm (h ≫ ψ) =
      (tensorPresheaf α).map h ≫ (tensorHomEquiv α 𝒢' ℱ).symm ψ :=
  (tensorPresheafAdj α).homEquiv_naturality_left_symm h ψ
