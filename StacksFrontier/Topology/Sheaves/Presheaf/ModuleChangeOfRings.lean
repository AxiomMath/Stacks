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
# Stacks tag 006R (Lemma 6.6.2)

Let `X` be a topological space, let `α : 𝒪₁ ⟶ 𝒪₂` be a morphism of presheaves of
commutative rings on `X`, let `ℱ` be a presheaf of `𝒪₂`-modules, and let `𝒢` be a
presheaf of `𝒪₁`-modules. Then there is a canonical bijection
$$
  \mathrm{Hom}_{𝒪₁}(𝒢, ℱ_{𝒪₁})
  \;\xrightarrow{\sim}\;
  \mathrm{Hom}_{𝒪₂}(𝒪₂ ⊗_{p,𝒪₁} 𝒢, ℱ),
$$
natural in `ℱ ∈ PModuleStruct(𝒪₂)` and in `𝒢 ∈ PModuleStruct(𝒪₁)`.

Equivalently, the change-of-rings (tensor product) functor
`𝒪₂ ⊗_{p,𝒪₁} (-) : PModuleStruct(𝒪₁) → PModuleStruct(𝒪₂)`
is left adjoint to the restriction-of-scalars functor
`(-)_{𝒪₁} : PModuleStruct(𝒪₂) → PModuleStruct(𝒪₁)`.

## Formalization strategy

We work at the level of generality of Mathlib's `PresheafOfModules`: the index
category `C` is an arbitrary small category, so the classical Stacks setting
`C = TopologicalSpace.Opens X` is a special case.

A presheaf of commutative rings is a functor `Cᵒᵖ ⥤ CommRingCat`; we pass to
`Cᵒᵖ ⥤ RingCat` (the underlying presheaf of rings) via `forget₂` whenever the
Mathlib API for `PresheafOfModules` is invoked.

The change-of-rings adjunction is already available in Mathlib as
`PresheafOfModules.pullbackPushforwardAdjunction`: for a functor `F : C ⥤ D`
and a morphism `φ : S ⟶ F.op ⋙ R` of presheaves of rings, the `pullback φ` is
left adjoint to the `pushforward φ`. Specialising to `F = 𝟭 C`, the
`pushforward φ` is naturally identified with `restrictScalars φ`, and the
`pullback φ` is the sectionwise tensor-product/change-of-rings functor.

This file therefore packages the Stacks 006R statement as a thin wrapper around
this Mathlib adjunction. -/

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

Sectionwise: `(𝒪₂ ⊗_{p,𝒪₁} 𝒢)(U) = 𝒪₂(U) ⊗_{𝒪₁(U)} 𝒢(U)`. The restriction maps
are induced by the universal property of the tensor product.

Constructed as the left adjoint of the restriction functor, via Mathlib's
`PresheafOfModules.pullback`. -/
noncomputable abbrev tensorPresheaf
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂) :
    PModuleStruct 𝒪₁ ⥤ PModuleStruct 𝒪₂ :=
  PresheafOfModules.pullback.{u} (F := 𝟭 C) (toRingCatMap α)

/-- **Stacks Project, tag 006R (Lemma 6.6.2), adjunction form.**

Given a morphism `α : 𝒪₁ ⟶ 𝒪₂` of presheaves of commutative rings on a small
category `C`, the change-of-rings functor `tensorPresheaf α = 𝒪₂ ⊗_{p, 𝒪₁} (-)`
is left adjoint to the restriction-of-scalars functor
`restrictionFunctor α = (-)_{𝒪₁}`.

This is the *canonical adjunction* asserted by Lemma 6.6.2. It is provided by
Mathlib's `PresheafOfModules.pullbackPushforwardAdjunction`, specialised to
`F = 𝟭 C`. -/
@[stacks 006R]
noncomputable def tensorPresheafAdj
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂) :
    PresheafOfModules.pullback.{u} (F := 𝟭 C) (toRingCatMap α) ⊣
      PresheafOfModules.pushforward.{u} (F := 𝟭 C) (toRingCatMap α) :=
  PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := 𝟭 C) (toRingCatMap α)

/-- **Stacks Project, tag 006R, hom-set bijection form.**

The canonical bijection
`Hom_{𝒪₂}(𝒪₂ ⊗_{p, 𝒪₁} 𝒢, ℱ) ≃ Hom_{𝒪₁}(𝒢, ℱ_{𝒪₁})`,
which is the hom-set bijection of the adjunction `tensorPresheafAdj`. By
construction, this bijection is natural in both variables `𝒢` and `ℱ`. -/
@[stacks 006R]
noncomputable def tensorHomEquiv
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂)
    (𝒢 : PModuleStruct 𝒪₁) (ℱ : PModuleStruct 𝒪₂) :
    ((tensorPresheaf α).obj 𝒢 ⟶ ℱ) ≃ (𝒢 ⟶ (restrictionFunctor α).obj ℱ) :=
  (tensorPresheafAdj α).homEquiv 𝒢 ℱ

/-- **Stacks Project, tag 006R: change-of-rings is a left adjoint.**

A direct consequence of `tensorPresheafAdj`. -/
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
