module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
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
public import Mathlib.Topology.Sheaves.SheafOfFunctions

/-!
# Stacks 007R — the pointwise product of algebraic structures is a sheaf

Let `(C, F)` be a type of algebraic structure (tag 007M), `X` a topological space and
`A : X → C` a family of objects of `C`, one for each point of `X`. Tag 007R considers the
`C`-valued presheaf `Π` on `X` given by `Π(U) = ∏_{x ∈ U} A_x`, with restriction along
`V ⊆ U` the canonical product morphism induced by the inclusion of index sets `V ↪ U`, and
asserts that `Π` is a sheaf of algebraic structures of type `(C, F)`. This is
`pointwiseProductPresheaf` and `pointwiseProductPresheaf_isSheaf` below.

Faithfulness of `F` is not used. What is needed are exactly the hypotheses of Mathlib's
`TopCat.Presheaf.isSheaf_iff_isSheaf_comp'` (tag 0073): `C` has all small limits, `F` preserves
all small limits, and `F` reflects isomorphisms. That lemma reduces the claim to the sheaf
condition for the presheaf of *sets* `Π ⋙ F`, which `pointwiseProductPresheaf_comp_iso`
identifies with `U ↦ ∏_{x ∈ U} F(A_x)`, i.e. with `TopCat.presheafToTypes X (fun x => F (A x))`.
The latter is a sheaf already in Mathlib, which is the content of tag 006X.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite Limits

universe u v

/-- The pointwise-product presheaf `Π : (Opens X)ᵒᵖ ⥤ C`, given on an open set
`U` by `Π(U) = ∏_{x ∈ U} A_x` (the categorical product in `C` over the subtype of points of `U`),
and on an inclusion of opens by the canonical product-projection morphism induced by the
inclusion of index subtypes.  Here `↥(unop U)` is the subtype `{x : X // x ∈ U}` of points of
the open set `U`, and `∏ᶜ (fun x => A x.1)` is the product in `C` of the family `x ↦ A_x`. -/
noncomputable def pointwiseProductPresheaf
    {C : Type*} [Category C] [HasLimits C] {X : TopCat} (A : X → C) :
    TopCat.Presheaf C X where
  obj U := ∏ᶜ (fun x : ↥(unop U) => A x.1)
  map {U V} i :=
    Pi.lift (fun y : ↥(unop V) => Pi.π (fun x : ↥(unop U) => A x.1) ⟨y.1, (i.unop.le) y.2⟩)
  map_id U := by apply Pi.hom_ext; intro y; simp
  map_comp {U V W} i j := by apply Pi.hom_ext; intro y; simp [Category.assoc]

/-- The identification of the underlying presheaf of sets: `Π ⋙ F`, for `Π` the
pointwise-product presheaf, is naturally isomorphic to the pointwise-product presheaf of *sets*
`U ↦ ∏_{x ∈ U} F(A x)`, that is to `TopCat.presheafToTypes X (fun x => F.obj (A x))`, whose value
at `U` is the dependent function type `(x : ↥(unop U)) → F (A x)`.

The component at `U` is the composite of `PreservesProduct.iso F (fun x : ↥(unop U) => A x.1)`,
available because `F` preserves the product over the index type `↥(unop U)`, with the canonical
identification `Types.productIso` of a product of types with the corresponding dependent function
type. Naturality holds because `PreservesProduct.iso` commutes `F` past the product projections
and `Types.productIso` turns those projections into evaluation, so both ways round the square
send a section to its component at `⟨y.1, i.unop.le y.2⟩`. -/
noncomputable def pointwiseProductPresheaf_comp_iso
    {C : Type u} [Category.{v} C] [HasLimits C]
    (F : C ⥤ Type v) [PreservesLimits F]
    {X : TopCat} (A : X → C) :
    pointwiseProductPresheaf A ⋙ F ≅ TopCat.presheafToTypes X (fun x => F.obj (A x)) :=
  by
  haveI : PreservesLimitsOfSize.{0, 0} F := preservesSmallestLimits_of_preservesLimits F
  refine NatIso.ofComponents
    (fun U =>
      PreservesProduct.iso F (fun x : ↥(unop U) => A x.1) ≪≫
        Types.productIso (fun x : ↥(unop U) => F.obj (A x.1)))
    ?_
  intro U V i
  ext s
  funext y
  change (F.map ((pointwiseProductPresheaf A).map i) ≫
      (piComparison F (fun x : ↥(unop V) => A x.1)) ≫
        (Types.productIso (fun x : ↥(unop V) => F.obj (A x.1))).hom) s y =
    (((piComparison F (fun x : ↥(unop U) => A x.1)) ≫
        (Types.productIso (fun x : ↥(unop U) => F.obj (A x.1))).hom) s) (i.unop y)
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply,
    CategoryTheory.ConcreteCategory.comp_apply]
  rw [Types.productIso_hom_comp_eval_apply (fun x : ↥(unop V) => F.obj (A x.1)) y,
    Types.productIso_hom_comp_eval_apply (fun x : ↥(unop U) => F.obj (A x.1)) (i.unop y),
    piComparison_comp_π_apply F (fun x : ↥(unop U) => A x.1) (i.unop y)]
  erw [piComparison_comp_π_apply F (fun x : ↥(unop V) => A x.1) y]
  erw [← F.map_comp_apply]
  congr 2
  simp only [pointwiseProductPresheaf, Limits.Pi.lift_comp_π]
  rfl

/-- **Stacks 007R.** Let `C` have all small limits and let `F : C ⥤ Type v` preserve all small
limits and reflect isomorphisms. Let `X` be a topological space and `A : X → C` a family of
objects of `C`. Then the pointwise-product presheaf `Π`, with `Π(U) = ∏_{x ∈ U} A_x`, is a sheaf
with values in `C`.

The underlying presheaf of sets `Π ⋙ F` is naturally isomorphic to the set-valued sheaf
`TopCat.sheafToTypes X (fun x => F (A x))` of tag 006X, so the bridge lemma
`TopCat.Presheaf.isSheaf_iff_isSheaf_comp'` (tag 0073) makes `Π` a sheaf. -/
@[stacks 007R]
theorem pointwiseProductPresheaf_isSheaf
    {C : Type u} [Category.{v} C] [HasLimits C]
    (F : C ⥤ Type v) [F.ReflectsIsomorphisms] [PreservesLimits F]
    {X : TopCat} (A : X → C) :
    (pointwiseProductPresheaf A).IsSheaf := by
  -- The carrier of `X : TopCat` lives in `Type 0` while the hom-universe of `C` is `v`, so use
  -- the universe-flexible form of the bridge lemma, after shrinking `PreservesLimits F` to the
  -- small limits it needs. This reduces `Π.IsSheaf` to `(Π ⋙ F).IsSheaf`.
  have : PreservesLimitsOfSize.{0, 0} F := preservesSmallestLimits_of_preservesLimits F
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp' F (pointwiseProductPresheaf A)]
  -- Transport the sheaf property of the set-valued pointwise-product sheaf of tag 006X along the
  -- natural isomorphism `Π ⋙ F ≅ presheafToTypes X (fun x => F (A x))`.
  exact TopCat.Presheaf.isSheaf_of_iso
    (pointwiseProductPresheaf_comp_iso F A).symm
    (TopCat.sheafToTypes X (fun x => F.obj (A x))).property
