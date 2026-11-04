module

public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Topology.Category.TopCat.OpenNhds
public import Mathlib.Topology.Sheaves.Presheaf
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalk of a presheaf with values in a category

Let `C` be a category and let `F : C ⥤ Type v` be a faithful functor that commutes with
filtered (= directed) colimits, and let `ℱ` be a `C`-valued presheaf on a topological
space `X`. For `x : X`, we prove three assertions corresponding to Tag 007H of the
Stacks Project.

* `stalk_exists`: the directed colimit `ℱ_x = colim_{x ∈ U} ℱ(U)` exists in `C`.
* `stalkUnderlyingSetIso`: the canonical comparison morphism
  `F(ℱ_x) → colim_{x ∈ U} F(ℱ(U)) = (F ∘ ℱ)_x` is an isomorphism in `Type v`.
* `stalkFunctor` and `stalkFunctorObjIso`: the construction `ℱ ↦ ℱ_x` extends to a
  functor `TopCat.Presheaf C X ⥤ C` whose object map agrees (up to canonical iso)
  with `colimit (stalkDiagram x ℱ)`.

The diagram whose colimit defines the stalk is `(OpenNhds.inclusion x).op ⋙ ℱ`,
indexed by the filtered category `(OpenNhds x)ᵒᵖ` — this is exactly the
"open neighbourhoods of `x` ordered by reverse inclusion" directed system of the
informal statement, since for `U V : OpenNhds x` the intersection `U ⊓ V` provides
the common refinement, and on the opposite category the resulting morphisms point
`U ⟶ U ⊓ V ⟵ V`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace


universe v u

namespace Stacks.Topology.CategoryStalk

/-- The stalk diagram of a `C`-valued presheaf `ℱ` at a point `x` of `X`: the
composite `(OpenNhds.inclusion x).op ⋙ ℱ : (OpenNhds x)ᵒᵖ ⥤ C`, sending an open
neighbourhood `U` of `x` to `ℱ(U)` with transition maps the restriction maps of `ℱ`. -/
def stalkDiagram {C : Type u} [Category.{v} C] {X : TopCat} (x : X)
    (ℱ : TopCat.Presheaf C X) :
    (OpenNhds x)ᵒᵖ ⥤ C :=
  (OpenNhds.inclusion x).op ⋙ ℱ

/-- The "underlying presheaf of sets" of a `C`-valued presheaf `ℱ` with respect to
a functor `F : C ⥤ Type v`: the composite presheaf `ℱ ⋙ F`. -/
def underlyingPresheafOfSets {C : Type u} [Category.{v} C] {X : TopCat}
    (F : C ⥤ Type v) (ℱ : TopCat.Presheaf C X) :
    TopCat.Presheaf (Type v) X :=
  ℱ ⋙ F

/-- The category `(OpenNhds x)ᵒᵖ` is filtered. -/
instance openNhds_op_isFiltered {X : TopCat} (x : X) :
    IsFiltered (OpenNhds x)ᵒᵖ := by
  infer_instance

/-- **Existence of the stalk.** Assuming filtered colimits of the appropriate size
exist in `C`, the directed colimit
  `ℱ_x = colim_{x ∈ U} ℱ(U)`
exists in `C`. -/
@[stacks 007H]
theorem stalk_exists
    {C : Type u} [Category.{v} C]
    [HasFilteredColimitsOfSize.{v, v} C]
    {X : TopCat.{v}} (x : X) (ℱ : TopCat.Presheaf C X) :
    HasColimit (stalkDiagram x ℱ) := by
  have : HasColimitsOfShape ((OpenNhds x)ᵒᵖ) C :=
    HasFilteredColimitsOfSize.HasColimitsOfShape (OpenNhds x)ᵒᵖ
  infer_instance

/-- The diagrams `stalkDiagram x ℱ ⋙ F` and `stalkDiagram x (ℱ ⋙ F)` are equal, both being
`(OpenNhds.inclusion x).op ⋙ ℱ ⋙ F`. -/
lemma stalkDiagram_comp_eq
    {C : Type u} [Category.{v} C] (F : C ⥤ Type v)
    {X : TopCat} (x : X) (ℱ : TopCat.Presheaf C X) :
    stalkDiagram x ℱ ⋙ F = stalkDiagram x (underlyingPresheafOfSets F ℱ) :=
  rfl

/-- **Underlying set of the stalk.** Applying `F` to the stalk `ℱ_x` yields the stalk
of the underlying presheaf of sets: the canonical comparison morphism furnishes an
isomorphism in `Type v`
  `F(ℱ_x) ≅ colim_{x ∈ U} F(ℱ(U)) = (F ∘ ℱ)_x`.

The isomorphism is `preservesColimitIso F (stalkDiagram x ℱ)` composed with the
identification of the two diagrams from `stalkDiagram_comp_eq`. -/
@[stacks 007H]
noncomputable def stalkUnderlyingSetIso
    {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) [F.Faithful]
    [HasFilteredColimitsOfSize.{v, v} C] [PreservesFilteredColimits.{v} F]
    {X : TopCat.{v}} (x : X) (ℱ : TopCat.Presheaf C X) :
    haveI : HasColimit (stalkDiagram x ℱ) := stalk_exists x ℱ
    haveI : HasColimit (stalkDiagram x (underlyingPresheafOfSets F ℱ)) :=
      stalk_exists (C := Type v) x (underlyingPresheafOfSets F ℱ)
    F.obj (colimit (stalkDiagram x ℱ)) ≅
      colimit (stalkDiagram x (underlyingPresheafOfSets F ℱ)) := by
  haveI : HasColimit (stalkDiagram x ℱ) := stalk_exists x ℱ
  haveI : HasColimit (stalkDiagram x (underlyingPresheafOfSets F ℱ)) :=
    stalk_exists (C := Type v) x (underlyingPresheafOfSets F ℱ)
  haveI : PreservesColimitsOfShape (OpenNhds x)ᵒᵖ F := inferInstance
  exact (preservesColimitIso F (stalkDiagram x ℱ)).trans
    (HasColimit.isoOfNatIso (eqToIso (stalkDiagram_comp_eq F x ℱ)))

/-- **Functoriality.** The stalk construction `ℱ ↦ ℱ_x` extends to a functor
  `(·)_x : TopCat.Presheaf C X ⥤ C`.
Concretely, every morphism of presheaves `φ : ℱ ⟶ 𝒢` induces (by the universal
property of the colimit) a morphism `φ_x : ℱ_x ⟶ 𝒢_x` in `C`, and this assignment
respects identities and composition: the functor is the whiskering by
`(OpenNhds.inclusion x).op` followed by taking the colimit. -/
@[stacks 007H, ega "0 3.1.6"]
noncomputable def stalkFunctor
    (C : Type u) [Category.{v} C]
    [HasFilteredColimitsOfSize.{v, v} C]
    {X : TopCat.{v}} (x : X) :
    TopCat.Presheaf C X ⥤ C :=
  haveI : HasColimitsOfShape ((OpenNhds x)ᵒᵖ) C :=
    HasFilteredColimitsOfSize.HasColimitsOfShape (OpenNhds x)ᵒᵖ
  (((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ C).obj (OpenNhds.inclusion x).op) ⋙
    colim)

/-- The functor `stalkFunctor C x` sends a presheaf `ℱ` to `colimit (stalkDiagram x ℱ)`, the
directed colimit of its restrictions to the open neighbourhoods of `x`. -/
noncomputable def stalkFunctorObjIso
    {C : Type u} [Category.{v} C]
    [HasFilteredColimitsOfSize.{v, v} C]
    {X : TopCat.{v}} (x : X) (ℱ : TopCat.Presheaf C X) :
    haveI : HasColimit (stalkDiagram x ℱ) := stalk_exists x ℱ
    (stalkFunctor C x).obj ℱ ≅ colimit (stalkDiagram x ℱ) := by
  haveI : HasColimitsOfShape ((OpenNhds x)ᵒᵖ) C :=
    HasFilteredColimitsOfSize.HasColimitsOfShape (OpenNhds x)ᵒᵖ
  haveI : HasColimit (stalkDiagram x ℱ) := stalk_exists x ℱ
  exact Iso.refl _

end Stacks.Topology.CategoryStalk
