module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.Coverage
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

/-!
# The sheaf condition along a refinement of families of arrows

Let `{Uᵢ ⟶ U}` and `{Vⱼ ⟶ U}` be families of morphisms with common target, where each `Vⱼ ⟶ U`
factors through some `Uᵢ ⟶ U`. A presheaf of types which is a sheaf for `{Vⱼ ⟶ U}` is a sheaf
for `{Uᵢ ⟶ U}`, provided that each restriction map `ℱ(Uᵢ) ⟶ ∏ⱼ ℱ(Uᵢ ×_U Vⱼ)` is injective.

## Main results

* `isSheafFor_ofArrows_of_refinement`: If `ℱ` is a sheaf for `{Vⱼ ⟶ U}`, the family `{Vⱼ ⟶ U}`
  refines `{Uᵢ ⟶ U}`, and each map `ℱ(Uᵢ) ⟶ ∏ⱼ ℱ(Uᵢ ×_U Vⱼ)` is injective, then `ℱ` is a sheaf
  for `{Uᵢ ⟶ U}`.
-/

@[expose] public section

open CategoryTheory Opposite Limits

/--
A refinement criterion for the sheaf condition on explicit families of arrows: if each `πV j`
factors as `f j ≫ πU (α j)`, `P` is a sheaf for `{πV j}`, and `P` is separated for each family
`{uvToU i j : UV i j ⟶ Uᵢ i}ⱼ`, then `P` is a sheaf for `{πU i}`.
-/
private theorem isSheafFor_trans_ofArrows
    {C : Type*} [Category C] {P : Cᵒᵖ ⥤ Type*} {U : C}
    {I J : Type*} {Uᵢ : I → C} {V : J → C} {UV : I → J → C}
    {πU : ∀ i, Uᵢ i ⟶ U} {πV : ∀ j, V j ⟶ U}
    (α : J → I) (f : ∀ j, V j ⟶ Uᵢ (α j))
    (hf : ∀ j, f j ≫ πU (α j) = πV j)
    (uvToV : ∀ i j, UV i j ⟶ V j) (uvToU : ∀ i j, UV i j ⟶ Uᵢ i)
    (huv : ∀ i j, uvToV i j ≫ πV j = uvToU i j ≫ πU i)
    (hV : Presieve.IsSheafFor P (Presieve.ofArrows V πV))
    (hsep : ∀ i, Presieve.IsSeparatedFor P (Presieve.ofArrows (UV i) (uvToU i))) :
    Presieve.IsSheafFor P (Presieve.ofArrows Uᵢ πU) := by
  refine Presieve.isSheafFor_of_factorsThru (S := Presieve.ofArrows V πV) P ?_ hV ?_
  · rintro Z g ⟨j⟩
    exact ⟨Uᵢ (α j), f j, πU (α j), Presieve.ofArrows.mk (α j), hf j⟩
  · rintro Y g ⟨i⟩
    refine ⟨Presieve.ofArrows (UV i) (uvToU i), hsep i, ?_⟩
    rintro Z k ⟨j⟩
    exact ⟨V j, uvToV i j, πV j, Presieve.ofArrows.mk j, huv i j⟩

/--
Let `{πU i : Uᵢ i ⟶ U}` and `{πV j : V j ⟶ U}` be families of morphisms such that each `πV j`
factors as `f j ≫ πU (α j)`, and let `UV i j` be a pullback of `πU i` and `πV j`. If `ℱ` is a
sheaf for `{πV j}` and, for each `i`, the restriction maps `ℱ(Uᵢ i) ⟶ ℱ(UV i j)` are jointly
injective, then `ℱ` is a sheaf for `{πU i}`.
-/
@[stacks 0G1L]
theorem isSheafFor_ofArrows_of_refinement
    {C : Type*} [Category C] {U : C}
    {I J : Type*} (Uᵢ : I → C) (V : J → C) (UV : I → J → C)
    (πU : ∀ i, Uᵢ i ⟶ U) (πV : ∀ j, V j ⟶ U)
    (α : J → I) (f : ∀ j, V j ⟶ Uᵢ (α j))
    (hf : ∀ j, f j ≫ πU (α j) = πV j)
    (uvToV : ∀ i j, UV i j ⟶ V j) (uvToU : ∀ i j, UV i j ⟶ Uᵢ i)
    (huv : ∀ i j, uvToV i j ≫ πV j = uvToU i j ≫ πU i)
    (hpbUU : ∀ i i', HasPullback (πU i) (πU i'))
    (hpbUV : ∀ i j, IsLimit (PullbackCone.mk (uvToV i j) (uvToU i j) (huv i j)))
    (hpbVV : ∀ j j', HasPullback (πV j) (πV j'))
    (ℱ : Cᵒᵖ ⥤ Type*)
    (hV : Presieve.IsSheafFor ℱ (Presieve.ofArrows V πV))
    (hinj : ∀ i, Function.Injective fun s : ℱ.obj (op (Uᵢ i)) =>
      fun j : J => ℱ.map (uvToU i j).op s) :
    Presieve.IsSheafFor ℱ (Presieve.ofArrows Uᵢ πU) := by
  let _ := hpbUU
  let _ := hpbUV
  let _ := hpbVV
  exact isSheafFor_trans_ofArrows α f hf uvToV uvToU huv hV fun i _ _ _ ht₁ ht₂ =>
    hinj i <| funext fun j => (ht₁ _ (.mk j)).trans (ht₂ _ (.mk j)).symm

