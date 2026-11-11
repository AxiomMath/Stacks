module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
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
# Strongly cartesian morphisms form a multiplicative class

Stacks 03WQ restricts a fibred category `p : 𝒮 ⥤ 𝒞` to the subcategory `𝒮'` with the same
objects as `𝒮` and only the strongly cartesian morphisms, and shows the restriction
`p' : 𝒮' ⥤ 𝒞` is fibred in groupoids. Here that subcategory is presented as a morphism
property `stronglyCartesianOver p` on `𝒮`, namely the `φ` that are strongly cartesian over
`p.map φ`, and the result here is that this property is multiplicative — it contains the
identities and is stable under composition — so that it does cut out a subcategory.
-/

@[expose] public section

open CategoryTheory MorphismProperty


/-- For a functor `p : 𝒮 ⥤ 𝒞`, the morphism property on `𝒮` consisting of those
morphisms `φ : x ⟶ y` that are strongly cartesian over `p.map φ`. The subcategory
`𝒮'` of `𝒮` from the Stacks lemma — same objects as `𝒮`, morphisms are the
strongly cartesian morphisms — is precisely the subcategory carved out by this
morphism property. -/
@[sga "1 VI 6.8" "partial"]
def stronglyCartesianOver
    {𝒞 : Type*} [Category 𝒞] {𝒮 : Type*} [Category 𝒮] (p : 𝒮 ⥤ 𝒞) :
    MorphismProperty 𝒮 :=
  fun _ _ φ => Functor.IsStronglyCartesian p (p.map φ) φ

/-- Identities are strongly cartesian over their `p`-image, so `stronglyCartesianOver p`
contains the identities. This is one of the two halves of the multiplicativity that makes the
subcategory `𝒮'` of strongly cartesian morphisms well-defined. -/
lemma stronglyCartesianOver_id
    {𝒞 : Type*} [Category 𝒞] {𝒮 : Type*} [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) (X : 𝒮) :
    stronglyCartesianOver p (𝟙 X) := by
  unfold stronglyCartesianOver
  infer_instance

/-- A composite of morphisms strongly cartesian over their `p`-images is again strongly
cartesian over its own, so `stronglyCartesianOver p` is stable under composition. This is the
other half of the multiplicativity making `𝒮'` a subcategory. -/
@[sga "1 VI 6.13" "more general", sga "1 VI 6.8" "partial", sga "4 VI 6.4" "Fr1"]
lemma stronglyCartesianOver_comp
    {𝒞 : Type*} [Category 𝒞] {𝒮 : Type*} [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) {X Y Z : 𝒮} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : stronglyCartesianOver p f) (hg : stronglyCartesianOver p g) :
    stronglyCartesianOver p (f ≫ g) := by
  unfold stronglyCartesianOver at *
  rw [p.map_comp]
  have := hf
  have := hg
  infer_instance

/-- The subcategory `𝒮'` of Stacks 03WQ is well defined: the morphism property
`stronglyCartesianOver p` (strongly cartesian morphisms over their image) contains identities and
is closed under composition. That `p' : 𝒮' ⥤ 𝒞` is fibred in groupoids is
`CategoryTheory.Functor.isFiberedInGroupoids_stronglyCartesianOver`. -/
@[sga "1 VI 6.13", sga "1 VI 6.8" "Well-definedness of F̃", sga "4 VI 6.4" "Fr1"]
theorem stronglyCartesianOver_isMultiplicative
    {𝒞 : Type*} [Category 𝒞] {𝒮 : Type*} [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) [p.IsFibered] :
    (stronglyCartesianOver p).IsMultiplicative :=
  have : (stronglyCartesianOver p).ContainsIdentities :=
    ⟨stronglyCartesianOver_id p⟩
  have : (stronglyCartesianOver p).IsStableUnderComposition :=
    ⟨stronglyCartesianOver_comp p⟩
  ⟨⟩

