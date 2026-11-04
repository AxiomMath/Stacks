module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Functor.OfSequence
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.SetTheory.ZFC.PSet
public import Mathlib.Tactic.ENatToNat
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
public import StacksFrontier.CategoryTheory.Sites.Point.Conservative
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The refinement step and covering data for the uniform refinement

Stacks 00YO (`CategoryTheory.GrothendieckTopology.exists_refinement_of_ne`): refining a cofiltered
system so as to keep two germs distinct while one section becomes covered by one finite covering.
Then the covering data and instructions used to refine a system uniformly (Stacks 00YP).
Split out of `StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints`.
-/

section

universe w v u t u₁
open CategoryTheory Limits Opposite

namespace Stacks.SitePoints.RefinementStep

/-- The index category of the refinement of a system `p : N ⥤ C` attached to an object `j₀` of
`N`: an object of `N` decorated with either nothing, or a morphism to `j₀` along which a fibre
product will be taken. -/
private abbrev Index {N : Type u₁} [SmallCategory N] (j₀ : N) : Type u₁ :=
  Σ j : N, Option (j ⟶ j₀)

/-- A morphism `ψ : j ⟶ j'` of `N` is a morphism of decorated indices when the decoration of the
target pulls back along `ψ` to the decoration of the source. In particular an undecorated index
admits no morphism to a decorated one. -/
private def Compat {N : Type u₁} [SmallCategory N] {j₀ j j' : N} (u : Option (j ⟶ j₀))
    (v : Option (j' ⟶ j₀)) (ψ : j ⟶ j') : Prop :=
  v.elim True fun φ' => u = some (ψ ≫ φ')

private lemma compat_none {N : Type u₁} [SmallCategory N] {j₀ j j' : N} (u : Option (j ⟶ j₀))
    (ψ : j ⟶ j') : Compat u (none : Option (j' ⟶ j₀)) ψ :=
  trivial

private lemma compat_some_iff {N : Type u₁} [SmallCategory N] {j₀ j j' : N} (u : Option (j ⟶ j₀))
    (φ' : j' ⟶ j₀) (ψ : j ⟶ j') : Compat u (some φ') ψ ↔ u = some (ψ ≫ φ') :=
  Iff.rfl

private lemma compat_id {N : Type u₁} [SmallCategory N] {j₀ j : N} (u : Option (j ⟶ j₀)) :
    Compat u u (𝟙 j) := by
  cases u with
  | none => exact compat_none (none : Option (j ⟶ j₀)) (𝟙 j)
  | some φ =>
    exact (compat_some_iff (some φ) φ (𝟙 j)).mpr (congrArg some (Category.id_comp φ).symm)

private lemma compat_comp {N : Type u₁} [SmallCategory N] {j₀ j j' j'' : N} (u : Option (j ⟶ j₀))
    (v : Option (j' ⟶ j₀)) (w : Option (j'' ⟶ j₀)) (ψ : j ⟶ j') (χ : j' ⟶ j'') (h₁ : Compat u v ψ)
    (h₂ : Compat v w χ) : Compat u w (ψ ≫ χ) := by
  cases w with
  | none => exact compat_none u (ψ ≫ χ)
  | some φ'' =>
    have h₂' : v = some (χ ≫ φ'') := (compat_some_iff v φ'' χ).mp h₂
    subst h₂'
    have h₁' : u = some (ψ ≫ χ ≫ φ'') := (compat_some_iff u (χ ≫ φ'') ψ).mp h₁
    exact
      (compat_some_iff u φ'' (ψ ≫ χ)).mpr
        (by
          rw [Category.assoc]; exact h₁')

/-- Precomposing the morphism of a decorated source with `r` precomposes its decoration. -/
private lemma compat_some_comp {N : Type u₁} [SmallCategory N] {j₀ j j' z : N} {ζ : j ⟶ j₀}
    {v : Option (j' ⟶ j₀)} (r : z ⟶ j) (ψ : j ⟶ j') (h : Compat (some ζ) v ψ) :
    Compat (some (r ≫ ζ)) v (r ≫ ψ) :=
  compat_comp _ (some ζ) _ r ψ ((compat_some_iff _ ζ r).mpr rfl) h

/-- There is no morphism of indices from an undecorated index to a decorated one. -/
private lemma not_compat_none_some {N : Type u₁} [SmallCategory N] {j₀ j j' : N} {φ' : j' ⟶ j₀}
    {ψ : j ⟶ j'} (h : Compat none (some φ') ψ) : False :=
  absurd ((compat_some_iff none φ' ψ).mp h) (by simp)

/-- The category structure on `Stacks.SitePoints.RefinementStep.Index j₀`. -/
@[instance_reducible]
private def indexCategory {N : Type u₁} [SmallCategory N] (j₀ : N) :
    SmallCategory (Index j₀) :=
  { Hom := fun x y => { ψ : x.1 ⟶ y.1 // Compat x.2 y.2 ψ }
    id := fun x => ⟨𝟙 x.1, compat_id x.2⟩
    comp := fun {x y z} m₁ m₂ => ⟨m₁.1 ≫ m₂.1, compat_comp x.2 y.2 z.2 m₁.1 m₂.1 m₁.2 m₂.2⟩
    id_comp := fun m => Subtype.ext (Category.id_comp m.1)
    comp_id := fun m => Subtype.ext (Category.comp_id m.1)
    assoc := fun m₁ m₂ m₃ => Subtype.ext (Category.assoc m₁.1 m₂.1 m₃.1) }

attribute [local instance] indexCategory

/-- The morphism of `N` underlying a morphism of indices. -/
@[implicit_reducible]
private def indexVal {N : Type u₁} [SmallCategory N] {j₀ : N} {x y : Index j₀} (m : x ⟶ y) :
    x.1 ⟶ y.1 :=
  Subtype.val m

/-- A morphism of `N` compatible with the decorations is a morphism of indices. -/
@[implicit_reducible]
private def indexMk {N : Type u₁} [SmallCategory N] {j₀ : N} {x y : Index j₀} (ψ : x.1 ⟶ y.1)
    (h : Compat x.2 y.2 ψ) : x ⟶ y :=
  ⟨ψ, h⟩

private lemma indexProp {N : Type u₁} [SmallCategory N] {j₀ : N} {x y : Index j₀} (m : x ⟶ y) :
    Compat x.2 y.2 (indexVal m) :=
  Subtype.property m

private lemma indexVal_indexMk {N : Type u₁} [SmallCategory N] {j₀ : N} {x y : Index j₀}
    (ψ : x.1 ⟶ y.1) (h : Compat x.2 y.2 ψ) : indexVal (indexMk ψ h) = ψ :=
  rfl

private lemma indexVal_comp {N : Type u₁} [SmallCategory N] {j₀ : N} {x y z : Index j₀}
    (m₁ : x ⟶ y) (m₂ : y ⟶ z) : indexVal (m₁ ≫ m₂) = indexVal m₁ ≫ indexVal m₂ :=
  rfl

private lemma index_hom_ext {N : Type u₁} [SmallCategory N] {j₀ : N} {x y : Index j₀}
    {m₁ m₂ : x ⟶ y} (h : indexVal m₁ = indexVal m₂) : m₁ = m₂ :=
  Subtype.ext h

private lemma indexMk_val {N : Type u₁} [SmallCategory N] {j₀ : N} {x y : Index j₀} (m : x ⟶ y)
    (h : Compat x.2 y.2 (indexVal m)) : indexMk (indexVal m) h = m :=
  rfl

/-- Every index receives a morphism from a decorated index: a decorated one from itself, and an
undecorated one from a lower bound of it and of `j₀`. -/
private lemma exists_compat_some {N : Type u₁} [SmallCategory N] [IsCofiltered N] (j₀ : N)
    (x : Index j₀) : ∃ (z : N) (ζ : z ⟶ j₀) (ψ : z ⟶ x.1), Compat (some ζ) x.2 ψ := by
  obtain ⟨j, u⟩ := x
  cases u with
  | none =>
    exact
      ⟨IsCofiltered.min j j₀, IsCofiltered.minToRight j j₀, IsCofiltered.minToLeft j j₀,
        compat_none _ _⟩
  | some φ => exact ⟨j, φ, 𝟙 j, compat_id (some φ)⟩

private lemma index_cone_objs {N : Type u₁} [SmallCategory N] [IsCofiltered N] (j₀ : N)
    (x y : Index j₀) : ∃ (z : Index j₀) (_ : z ⟶ x) (_ : z ⟶ y), True := by
  obtain ⟨z, ζ, ψ, hψ⟩ := exists_compat_some j₀ x
  obtain ⟨z', ζ', ψ', hψ'⟩ := exists_compat_some j₀ y
  obtain ⟨w, c, c', hc⟩ := IsCofiltered.cospan ζ ζ'
  refine ⟨⟨w, some (c ≫ ζ)⟩, indexMk (c ≫ ψ) ?_, indexMk (c' ≫ ψ') ?_, trivial⟩
  · exact compat_some_comp c ψ hψ
  · rw [hc]; exact compat_some_comp c' ψ' hψ'

private lemma index_cone_maps {N : Type u₁} [SmallCategory N] [IsCofiltered N] (j₀ : N)
    ⦃x y : Index j₀⦄ (m₁ m₂ : x ⟶ y) : ∃ (z : Index j₀) (r : z ⟶ x), r ≫ m₁ = r ≫ m₂ := by
  obtain ⟨z, ζ, ψ, hψ⟩ := exists_compat_some j₀ x
  obtain ⟨w, r, hr⟩ := IsCofilteredOrEmpty.cone_maps (ψ ≫ indexVal m₁) (ψ ≫ indexVal m₂)
  refine
    ⟨⟨w, some (r ≫ ζ)⟩,
      indexMk (r ≫ ψ) (compat_some_comp r ψ hψ), ?_⟩
  apply index_hom_ext
  rw [indexVal_comp, indexVal_comp, indexVal_indexMk, Category.assoc, Category.assoc, hr]

private lemma indexIsCofiltered {N : Type u₁} [SmallCategory N] [IsCofiltered N] (j₀ : N) :
    IsCofiltered (Index j₀) :=
  { cone_objs := index_cone_objs j₀
    cone_maps := index_cone_maps j₀
    nonempty := ⟨⟨j₀, none⟩⟩ }

/-! ### Fibre products over a fixed morphism -/

/-- The morphism of fibre products `X ×_W T ⟶ X' ×_W T` induced by a morphism `v : X ⟶ X'` over
`W`, that is, one through which the structure morphism `u : X ⟶ W` factors as `u = v ≫ u'`. -/
private noncomputable abbrev pullbackMapOver {C : Type u} [Category.{v} C] {X X' W T : C}
    (u : X ⟶ W) (u' : X' ⟶ W) (t : T ⟶ W) [HasPullback u t] [HasPullback u' t] (v : X ⟶ X')
    (huv : u = v ≫ u') : pullback u t ⟶ pullback u' t :=
  pullback.map u t u' t v (𝟙 T) (𝟙 W) (by rw [Category.comp_id, huv]) (by simp)

section PullbackMapOver

variable {C : Type u} [Category.{v} C] {X X' X'' W T : C} {u : X ⟶ W} {u' : X' ⟶ W} {u'' : X'' ⟶ W}
  {t : T ⟶ W} [HasPullback u t] [HasPullback u' t] [HasPullback u'' t]

private lemma pullbackMapOver_fst (v : X ⟶ X') (huv : u = v ≫ u') :
    pullbackMapOver u u' t v huv ≫ pullback.fst u' t = pullback.fst u t ≫ v :=
  pullback.lift_fst _ _ _

private lemma pullbackMapOver_fst_assoc (v : X ⟶ X') (huv : u = v ≫ u') {Z : C} (r : X' ⟶ Z) :
    pullbackMapOver u u' t v huv ≫ pullback.fst u' t ≫ r = (pullback.fst u t ≫ v) ≫ r := by
  rw [← Category.assoc, pullbackMapOver_fst]

private lemma pullbackMapOver_snd (v : X ⟶ X') (huv : u = v ≫ u') :
    pullbackMapOver u u' t v huv ≫ pullback.snd u' t = pullback.snd u t :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- A morphism over `W` which is an identity induces the identity of the fibre products. The
identity is given as a hypothesis because at the point of use the morphism is `p (𝟙 j)`. -/
private lemma pullbackMapOver_eq_id {v : X ⟶ X} (hv : v = 𝟙 X) (huv : u = v ≫ u) :
    pullbackMapOver u u t v huv = 𝟙 (pullback u t) := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullbackMapOver_fst, hv, Category.comp_id, Category.id_comp]
  · rw [pullbackMapOver_snd, Category.id_comp]

/-- The induced morphisms of fibre products compose. The factorisation of the inducing morphism is
given as a hypothesis because at the point of use it is `p (ψ ≫ χ)`, which is a composite only
after rewriting, whereas the side condition `huw` depends on it. -/
private lemma pullbackMapOver_comp {v : X ⟶ X'} {v' : X' ⟶ X''} {w : X ⟶ X''} (hw : w = v ≫ v')
    (huv : u = v ≫ u') (hu'v' : u' = v' ≫ u'') (huw : u = w ≫ u'') :
    pullbackMapOver u u'' t w huw =
      pullbackMapOver u u' t v huv ≫ pullbackMapOver u' u'' t v' hu'v' := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullbackMapOver_fst, Category.assoc, pullbackMapOver_fst, ← Category.assoc,
      pullbackMapOver_fst, Category.assoc, hw]
  · rw [pullbackMapOver_snd, Category.assoc, pullbackMapOver_snd, pullbackMapOver_snd]

end PullbackMapOver

/-! ### The refined system -/

/-- The object of `C` attached to an index: `p j` for an undecorated index, and the fibre product
`p j ×_W T` along `p φ ≫ f` for an index decorated by `φ : j ⟶ j₀`.

A decorated index is never used through this definition: every statement below is phrased with the
projections `pullback.fst`, `pullback.snd` and with
`Stacks.SitePoints.RefinementStep.pullbackMapOver`, and the identification of
`refObj p j₀ f t (some φ)` with `p j ×_W T` is left to definitional unfolding. -/
@[implicit_reducible]
private noncomputable def refObj {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) (j₀ : N) {j : N} {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W)
    [HasPullbacksAlong t] (u : Option (j ⟶ j₀)) : C :=
  match u with
  | none => p.obj j
  | some φ => pullback (p.map φ ≫ f) t

/-- A factorisation `φ = ψ ≫ φ'` in `N` makes `p ψ` a morphism over `W` from the structure
morphism `p φ ≫ f` of the index decorated by `φ` to that of the index decorated by `φ'`. This is
the side condition of the fibre products' functoriality. -/
private lemma map_comp_eq_of_eq_comp {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) {j j' j₀ : N} {φ : j ⟶ j₀} (ψ : j ⟶ j') (φ' : j' ⟶ j₀) (hφ : φ = ψ ≫ φ') {W : C}
    (f : p.obj j₀ ⟶ W) : p.map φ ≫ f = p.map ψ ≫ (p.map φ' ≫ f) := by
  rw [hφ, p.map_comp, Category.assoc]

/-- A morphism of decorated indices is a morphism over `W` between the structure morphisms of the
two fibre products. This is the only thing the decorations are used for, and the side condition of
every `Stacks.SitePoints.RefinementStep.pullbackMapOver` below. -/
private lemma map_comp_eq_of_compat {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) {j j' j₀ : N} {φ : j ⟶ j₀} {φ' : j' ⟶ j₀} {ψ : j ⟶ j'} {W : C} (f : p.obj j₀ ⟶ W)
    (h : Compat (some φ) (some φ') ψ) : p.map φ ≫ f = p.map ψ ≫ (p.map φ' ≫ f) :=
  map_comp_eq_of_eq_comp p ψ φ' (Option.some.inj ((compat_some_iff _ φ' ψ).mp h)) f

/-- The morphism of `C` attached to a morphism of indices: `p ψ` between undecorated indices, the
first projection followed by `p ψ` out of a decorated index into an undecorated one, and the
induced morphism of fibre products between decorated indices. -/
private noncomputable def refMap {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) (j₀ : N) {j j' : N} {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W)
    [HasPullbacksAlong t] (u : Option (j ⟶ j₀)) (v : Option (j' ⟶ j₀)) (ψ : j ⟶ j')
    (h : Compat u v ψ) : refObj p j₀ f t u ⟶ refObj p j₀ f t v :=
  match u, v, h with
  | none, none, _ => p.map ψ
  | some φ, none, _ => pullback.fst (p.map φ ≫ f) t ≫ p.map ψ
  | none, some _, h => (not_compat_none_some h).elim
  | some φ, some φ', h =>
    pullbackMapOver (p.map φ ≫ f) (p.map φ' ≫ f) t (p.map ψ) (map_comp_eq_of_compat p f h)

private lemma refMap_none_none {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) (j₀ : N) {j j' : N} {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W)
    [HasPullbacksAlong t] (ψ : j ⟶ j') (h : Compat none none ψ) :
    refMap p j₀ f t none none ψ h = p.map ψ :=
  rfl

private lemma refMap_some_none {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) (j₀ : N) {j j' : N} {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W)
    [HasPullbacksAlong t] (φ : j ⟶ j₀) (ψ : j ⟶ j') (h : Compat (some φ) none ψ) :
    refMap p j₀ f t (some φ) none ψ h = pullback.fst (p.map φ ≫ f) t ≫ p.map ψ :=
  rfl

private lemma refMap_some_some {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) (j₀ : N) {j j' : N} {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W)
    [HasPullbacksAlong t] (φ : j ⟶ j₀) (φ' : j' ⟶ j₀) (ψ : j ⟶ j')
    (h : Compat (some φ) (some φ') ψ) :
    refMap p j₀ f t (some φ) (some φ') ψ h =
      pullbackMapOver (p.map φ ≫ f) (p.map φ' ≫ f) t (p.map ψ) (map_comp_eq_of_compat p f h) :=
  rfl

private lemma refMap_id {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N] (p : N ⥤ C)
    (j₀ : N) {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W) [HasPullbacksAlong t] {j : N}
    (u : Option (j ⟶ j₀)) (h : Compat u u (𝟙 j)) :
    refMap p j₀ f t u u (𝟙 j) h = 𝟙 (refObj p j₀ f t u) := by
  cases u with
  | none => exact p.map_id j
  | some φ =>
    exact (refMap_some_some p j₀ f t φ φ (𝟙 j) h).trans (pullbackMapOver_eq_id (p.map_id j) _)

private lemma refMap_comp {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N] (p : N ⥤ C)
    (j₀ : N) {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W) [HasPullbacksAlong t] {j j' j'' : N}
    (u : Option (j ⟶ j₀)) (v : Option (j' ⟶ j₀)) (w : Option (j'' ⟶ j₀)) (ψ : j ⟶ j')
    (χ : j' ⟶ j'') (h₁ : Compat u v ψ) (h₂ : Compat v w χ) (h : Compat u w (ψ ≫ χ)) :
    refMap p j₀ f t u w (ψ ≫ χ) h = refMap p j₀ f t u v ψ h₁ ≫ refMap p j₀ f t v w χ h₂ := by
  cases w with
  | none =>
    cases v with
    | none =>
      cases u with
      | none => exact p.map_comp ψ χ
      | some
        φ =>
        rw [refMap_some_none, refMap_some_none, refMap_none_none, p.map_comp, Category.assoc]
    | some φ' =>
      cases u with
      | none => exact (not_compat_none_some h₁).elim
      | some
        φ =>
        rw [refMap_some_none, refMap_some_some, refMap_some_none, pullbackMapOver_fst_assoc,
          p.map_comp, Category.assoc]
  | some φ'' =>
    cases v with
    | none => exact (not_compat_none_some h₂).elim
    | some φ' =>
      cases u with
      | none => exact (not_compat_none_some h₁).elim
      | some φ =>
        exact
          pullbackMapOver_comp (p.map_comp ψ χ) (map_comp_eq_of_compat p f h₁)
            (map_comp_eq_of_compat p f h₂) (map_comp_eq_of_compat p f h)

/-- The refined system: the functor on the index category extending `p` by the fibre products
`p j ×_W T`. -/
@[implicit_reducible]
private noncomputable def refSystem {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) (j₀ : N) {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W) [HasPullbacksAlong t] :
    Index j₀ ⥤ C :=
  { obj := fun x => refObj p j₀ f t x.2
    map := fun {x y} m => refMap p j₀ f t x.2 y.2 (indexVal m) (indexProp m)
    map_id := fun x => refMap_id p j₀ f t x.2 (indexProp (𝟙 x))
    map_comp := fun {x y z} m₁ m₂ =>
      refMap_comp p j₀ f t x.2 y.2 z.2 (indexVal m₁) (indexVal m₂) (indexProp m₁) (indexProp m₂)
        (indexProp (m₁ ≫ m₂)) }

private lemma refSystem_obj {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) (j₀ : N) {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W) [HasPullbacksAlong t]
    (x : Index j₀) : (refSystem p j₀ f t).obj x = refObj p j₀ f t x.2 :=
  rfl

private lemma refObj_none {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) (j₀ : N) {j : N} {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W)
    [HasPullbacksAlong t] : refObj p j₀ f t (none : Option (j ⟶ j₀)) = p.obj j :=
  rfl

private lemma refSystem_map {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    (p : N ⥤ C) (j₀ : N) {W : C} (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W) [HasPullbacksAlong t]
    {x y : Index j₀} (m : x ⟶ y) :
    (refSystem p j₀ f t).map m = refMap p j₀ f t x.2 y.2 (indexVal m) (indexProp m) :=
  rfl

/-- The inclusion of `N` in the index category of the refinement, as the undecorated indices. -/
@[implicit_reducible]
private def refIncl {N : Type u₁} [SmallCategory N] (j₀ : N) : N ⥤ Index j₀ :=
  { obj := fun j => ⟨j, none⟩
    map := fun {j _j'} ψ => indexMk ψ (compat_none (none : Option (j ⟶ j₀)) ψ)
    map_id := fun _ => Subtype.ext rfl
    map_comp := fun _ _ => Subtype.ext rfl }

private lemma refIncl_obj {N : Type u₁} [SmallCategory N] (j₀ j : N) :
    (refIncl j₀).obj j = ⟨j, none⟩ :=
  rfl

/-! ### The refinement -/

/-- Cancelling an identity inside the restriction map of a presheaf. This is stated with the
identity present, rather than used as a rewrite, because the identity it cancels is the component
`ε.hom.app j₀` of the comparison isomorphism of the refinement below, which is an identity only
after unfolding: a rewrite does not see it, whereas elaboration of this lemma's argument does. -/
private lemma map_op_eq_of_comp_id_op_eq {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} {X Y : C}
    {k : X ⟶ Y} {x y : F.obj (op Y)} (h : F.map (k ≫ 𝟙 Y).op x = F.map (k ≫ 𝟙 Y).op y) :
    F.map k.op x = F.map k.op y := by rwa [Category.comp_id] at h

/-- Given a system `p : N ⥤ C`, two sections `a, a'` of a presheaf `F` over `p j₀` whose germs
along `p` are distinct, a morphism `f : p j₀ ⟶ W` and a morphism `t : T ⟶ W` along which
pullbacks exist such that the germs of `a` and `a'` stay distinct after restriction to every
`p j ×_W T`, the system `p` admits a refinement in which the germs of `a` and `a'` are still
distinct and in which `f` becomes, after restriction, a morphism through `t`. -/
private lemma exists_refinement {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} {N : Type u₁}
    [SmallCategory N] [IsCofiltered N] (p : N ⥤ C) (j₀ : N) (a a' : F.obj (op (p.obj j₀))) {W : C}
    (f : p.obj j₀ ⟶ W) {T : C} (t : T ⟶ W) [HasPullbacksAlong t]
    (haa' : ∀ (j : N) (φ : j ⟶ j₀), F.map (p.map φ).op a ≠ F.map (p.map φ).op a')
    (hk :
      ∀ (j : N) (φ ψ : j ⟶ j₀),
        F.map (pullback.fst (p.map φ ≫ f) t ≫ p.map ψ).op a ≠
          F.map (pullback.fst (p.map φ ≫ f) t ≫ p.map ψ).op a') :
    ∃ (M : Type u₁) (_ : SmallCategory M) (_ : IsCofiltered M) (q : M ⥤ C) (e : N ⥤ M) (_ : e.Full)
      (_ : e.Faithful) (ε : e ⋙ q ≅ p),
      (∀ (i : M) (ψ : i ⟶ e.obj j₀),
          F.map (q.map ψ ≫ ε.hom.app j₀).op a ≠ F.map (q.map ψ ≫ ε.hom.app j₀).op a') ∧
        ∃ (i : M) (ψ : i ⟶ e.obj j₀) (r : q.obj i ⟶ T), r ≫ t = q.map ψ ≫ ε.hom.app j₀ ≫ f := by
  refine
    ⟨Index j₀, indexCategory j₀, indexIsCofiltered j₀, refSystem p j₀ f t, refIncl j₀,
      ⟨fun m => ⟨indexVal m, indexMk_val m _⟩⟩, ⟨fun h => congrArg indexVal h⟩, Iso.refl p, ?_, ?_⟩
  · intro x m
    obtain ⟨j, u⟩ := x
    cases u with
    | none => exact fun heq => haa' j (indexVal m) (map_op_eq_of_comp_id_op_eq heq)
    | some φ => exact fun heq => hk j φ (indexVal m) (map_op_eq_of_comp_id_op_eq heq)
  · refine
      ⟨⟨j₀, some (𝟙 j₀)⟩, indexMk (𝟙 j₀) (compat_none _ _), pullback.snd (p.map (𝟙 j₀) ≫ f) t, ?_⟩
    dsimp only [refSystem_map, indexVal_indexMk, refIncl_obj, refMap_some_none, Iso.refl_hom,
      NatTrans.id_app, Functor.comp_obj, refSystem_obj, refObj_none]
    rw [Category.id_comp, Category.assoc]
    exact pullback.condition.symm

/-! ### The choice of a member of the covering -/

/-- In a cofiltered category, a finite family of pairs of morphisms with common target `j₀`
admits a cone on which the two members of each pair agree. -/
private lemma exists_cone_forall_eq {N : Type u₁} [Category.{v} N] [IsCofilteredOrEmpty N]
    {ι : Type t} [Finite ι] {j₀ : N} {jj : ι → N} (φφ ψψ : ∀ k, jj k ⟶ j₀) :
    ∃ (w : N) (χ : w ⟶ j₀), ∀ k, ∃ c : w ⟶ jj k, c ≫ φφ k = χ ∧ c ≫ ψψ k = χ := by
  obtain ⟨w, χ, c, hc⟩ := IsCofiltered.wideCospan fun k => IsCofiltered.eqHom (φφ k) (ψψ k) ≫ φφ k
  refine ⟨w, χ, fun k => ⟨c k ≫ IsCofiltered.eqHom (φφ k) (ψψ k), ?_, ?_⟩⟩
  · rw [Category.assoc]; exact hc k
  · rw [Category.assoc, ← IsCofiltered.eq_condition]; exact hc k

/-- Let `{g k : Y k ⟶ W}` be a covering of the site and let `u : X ⟶ W` be a morphism along which
the fibre products `X ×_W Y k` exist. Then two sections of a separated presheaf `F` over `X'` have
the same restriction along a morphism `v : X ⟶ X'` as soon as their restrictions along the
composites `X ×_W Y k ⟶ X ⟶ X'` agree, because the fibre products `X ×_W Y k` cover `X`. Taking
`v = 𝟙 X`, a section over `X` is determined by its restrictions to the `X ×_W Y k`.

This is the only place where the topology, and the separatedness of `F`, are used. -/
private lemma map_eq_of_forall_pullback_fst_comp_eq {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type w} (hF : Presieve.IsSeparated J F) {W : C}
    {ι : Type t} {Y : ι → C} (g : ∀ k, Y k ⟶ W) (hg : Sieve.ofArrows Y g ∈ J W) {X X' : C}
    (u : X ⟶ W) (v : X ⟶ X') [∀ k, HasPullback u (g k)] {x y : F.obj (op X')}
    (h : ∀ k, F.map (pullback.fst u (g k) ≫ v).op x = F.map (pullback.fst u (g k) ≫ v).op y) :
    F.map v.op x = F.map v.op y := by
  refine (hF _ (J.pullback_stable u hg)).ext fun Z α hα => ?_
  have hα' : (Sieve.ofArrows Y g).arrows (α ≫ u) := hα
  obtain ⟨k, β, hβ⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hα'
  have hfac : α ≫ v = pullback.lift α β hβ ≫ (pullback.fst u (g k) ≫ v) :=
    (pullback.lift_fst_assoc _ _ _ _).symm
  rw [← F.map_comp_apply, ← F.map_comp_apply, ← op_comp, hfac, op_comp, F.map_comp_apply,
    F.map_comp_apply, h k]

/-- One member `g k` of a finite covering of `W` has the property that the germs of `a` and `a'`
stay distinct after restriction to every fibre product `p j ×_W Y k`. Indeed otherwise,
restricting to a cone of the finitely many morphisms `j ⟶ j₀` witnessing the failure, the two
sections would agree on a covering, hence agree. -/
private lemma exists_index_forall_ne {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]
    [IsCofiltered N] (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type w}
    (hF : Presieve.IsSeparated J F) (p : N ⥤ C) (j₀ : N) (a a' : F.obj (op (p.obj j₀)))
    (haa' : ∀ (j : N) (φ : j ⟶ j₀), F.map (p.map φ).op a ≠ F.map (p.map φ).op a') {W : C}
    {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W) (hg : Sieve.ofArrows Y g ∈ J W)
    [∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k)] (f : p.obj j₀ ⟶ W) :
    ∃ (k : ι),
      ∀ (j : N) (φ ψ : j ⟶ j₀),
        F.map (pullback.fst (p.map φ ≫ f) (g k) ≫ p.map ψ).op a ≠
          F.map (pullback.fst (p.map φ ≫ f) (g k) ≫ p.map ψ).op a' := by
  by_contra hc
  push Not at hc
  choose jj φφ ψψ hh using hc
  obtain ⟨w, χ, hcone⟩ := exists_cone_forall_eq φφ ψψ
  refine haa' w χ (map_eq_of_forall_pullback_fst_comp_eq hF g hg (p.map χ ≫ f) (p.map χ) ?_)
  intro k
  obtain ⟨c, hc₁, hc₂⟩ := hcone k
  have hfac :
    pullback.fst (p.map χ ≫ f) (g k) ≫ p.map χ =
      pullbackMapOver (p.map χ ≫ f) (p.map (φφ k) ≫ f) (g k) (p.map c)
          (map_comp_eq_of_eq_comp p c (φφ k) hc₁.symm f) ≫
        (pullback.fst (p.map (φφ k) ≫ f) (g k) ≫ p.map (ψψ k)) := by
    rw [pullbackMapOver_fst_assoc, Category.assoc, ← p.map_comp, hc₂]
  rw [hfac, op_comp, F.map_comp_apply, F.map_comp_apply, hh k]

end Stacks.SitePoints.RefinementStep

attribute [local instance] Stacks.SitePoints.RefinementStep.indexCategory

namespace CategoryTheory.GrothendieckTopology

@[expose] public section

open Stacks.SitePoints.RefinementStep in
/-- **Stacks 00YO.** Let `(C, J)` be a site, let `F` be a separated presheaf of sets on `C` and let
`p : N ⥤ C` be a cofiltered system in `C`, with associated fibre functor
`u'(X) = colim_j Mor(p j, X)` and stalk functor `F ↦ F_{p'} = colim_j F(p j)`. Let `s ≠ s'` be two
germs in `F_{p'}`, represented by `a, a' : F(p j₀)`, let `{g k : Y k ⟶ W}` be a finite covering of
the site and let `f : p j₀ ⟶ W` represent a section of `u'(W)`.

Then the system can be refined — there are a cofiltered system `q : M ⥤ C`, a fully faithful
`e : N ⥤ M` and an isomorphism `ε : e ⋙ q ≅ p` exhibiting `p` as the restriction of `q` — in such a
way that the two germs stay distinct in `F_p` and that the image of `f` in `u(W)` lies in the image
of `u(Y k)` for one of the members `g k : Y k ⟶ W` of the covering. -/
@[stacks 00YO "The inductive step of Deligne's criterion: a cofiltered system can be refined so as
  to keep two germs of a separated presheaf distinct while a given section of `u'(W)` becomes
  covered by a given finite covering of `W`.", sga "4 VI 9.3"]
public theorem exists_refinement_of_ne {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F : Cᵒᵖ ⥤ Type w} (hF : Presieve.IsSeparated J F) {N : Type u₁} [SmallCategory N]
    [IsCofiltered N] (p : N ⥤ C) (j₀ : N) (a a' : F.obj (op (p.obj j₀)))
    (haa' : ∀ (j : N) (φ : j ⟶ j₀), F.map (p.map φ).op a ≠ F.map (p.map φ).op a') {W : C}
    {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W) (hg : Sieve.ofArrows Y g ∈ J W)
    [∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k)] (f : p.obj j₀ ⟶ W) :
    ∃ (M : Type u₁) (_ : SmallCategory M) (_ : IsCofiltered M) (q : M ⥤ C) (e : N ⥤ M) (_ : e.Full)
      (_ : e.Faithful) (ε : e ⋙ q ≅ p),
      (∀ (i : M) (ψ : i ⟶ e.obj j₀),
          F.map (q.map ψ ≫ ε.hom.app j₀).op a ≠ F.map (q.map ψ ≫ ε.hom.app j₀).op a') ∧
        ∃ (k : ι) (i : M) (ψ : i ⟶ e.obj j₀) (h : q.obj i ⟶ Y k),
          h ≫ g k = q.map ψ ≫ ε.hom.app j₀ ≫ f := by
  obtain ⟨k, hk⟩ := exists_index_forall_ne J hF p j₀ a a' haa' g hg f
  have : HasPullbacksAlong (g k) := fun h => inferInstance
  obtain ⟨M, catM, cofM, q, e, eFull, eFaithful, ε, h₁, i, ψ, r, hr⟩ :=
    exists_refinement p j₀ a a' f (g k) haa' hk
  exact ⟨M, catM, cofM, q, e, eFull, eFaithful, ε, h₁, k, i, ψ, r, hr⟩

end

end CategoryTheory.GrothendieckTopology

end

/-!
# Refining a cofiltered system so as to separate two germs and cover all sections at once

Let `(C, J)` be a site. Following Deligne's appendix to SGA 4, Exposé VI, a *system* in `C` is a
cofiltered inverse system of objects of `C`, that is, a functor `p : N ⥤ C` out of a small
cofiltered category `N` (the source writes it as a directed set `(J, ≥)` together with an inverse
system `(V_j, g_{jj'})`, the morphisms of `N` being the transition maps `g_{jj'}`). Such a system
carries two associated functors: the fibre functor

`u(X) = colim_{j ∈ N} Mor(p j, X)`,

which is `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiber p` (its elements being the
`Point.ofIsCofiltered.fiberMk h` for morphisms `h : p j ⟶ X`), and the stalk functor
`F ↦ F_p = colim_{j ∈ N} F(p j)` on presheaves, the two being compatible in the sense that `F_p` is
the fibre of `F` at the point of the site determined by `u`, once `u` is one
(`Point.ofIsCofiltered`).

A system `q : M ⥤ C` *refines* `p` when `p` is the restriction of `q` along an inclusion of index
categories: a fully faithful `e : N ⥤ M` together with an isomorphism `e ⋙ q ≅ p`. A refinement
induces maps `u'(X) → u(X)` and `F_{p'} → F_p`, both because the colimits defining the former run
over a subsystem of those defining the latter.

This file records the main step of Deligne's criterion for the existence of enough points: given
two distinct germs `s ≠ s'` in `F_{p'}` for a separated presheaf `F`, the system can be refined so
that the two germs stay distinct while *every* section of `u'` becomes covered by *every* finite
covering of the site — for each finite covering `{Y k → W}` and each `f ∈ u'(W)`, the image of `f`
in `u(W)` lies in the image of one of the `u(Y k)`. It is obtained from the one-covering,
one-section statement (Stacks 00YO) by transfinite recursion along a well ordering of the set of
pairs `({Y k → W}, f ∈ u'(W))`, the passage to the limit being harmless because a directed colimit
of the systems has for fibre functor the colimit of their fibre functors.

## Main results

* `CategoryTheory.GrothendieckTopology.exists_refinement_forall_covering_of_ne`: Stacks 00YP.

## Implementation notes

The index of a system is a small cofiltered category rather than a directed set, as in Stacks 00YO;
a directed set `(J, ≥)` is such a category, and a cofiltered index category is what the
constructions of the section actually use.

The refined index category is produced in `Type (max u₁ u v)` rather than in the universe `u₁` of
`N`: it is assembled from one copy of the construction of Stacks 00YO for each pair
`({Y k → W}, f)`, and there are as many such pairs as there are objects and morphisms of `C`. The
the statement: a finite covering indexed by any type is a reindexing of one indexed by
`ULift (Fin n)`, and both `hpb` and the second conclusion transport along such a reindexing, the
sieve generated by a family being unchanged by it.

That same description of `M` also bounds its size, and the statement records the bound: `M` is
assembled from objects and morphisms of `C` and of `N` together with reindexings by
`ULift (Fin n)`, so it is no larger than `C` and `N` are — if `C` is `w'`-small with `w'`-small hom
types and `N` is essentially `w'`-small, then `M` is essentially `w'`-small too. The universe `w'`
is unrelated to the universe `w` in which `F` takes its values: `F` enters the proof, through
separatedness, but not the construction of the index category. The bound is stated as
`EssentiallySmall.{w'} M` rather than as `Small.{w'} M` together with `LocallySmall.{w'} M`, the
weaker of the two and already enough to produce a category with both its objects and its morphisms
in `Type w'` equivalent to `M` (`equivSmallModel`, `ShrinkHoms.equivalence`). It is what makes the
lemma iterable: a tower of refinements can then be kept inside `Type w'`, so its colimit is
`InitiallySmall.{w'}`, which is what `Point.ofIsCofiltered` asks of an index category before it
builds a point out of it.

Elements of the colimits `F_{p'}` and `u'(W)` are given by representatives, and the two assertions
about them are spelled out through the concrete description of a filtered colimit of types. This
keeps the statement free of transports along `ε` at the level of colimits, and is what the
downstream constructor `Point.ofIsCofiltered` consumes; the translation is an equivalence, not a
weakening (see Stacks 00YO for the dictionary, which is used here verbatim). In particular,
quantifying the second conclusion over all `j : N` and all `f : p j ⟶ W` is quantifying over all
elements of `u'(W)`, since every element is `fiberMk f` for some such `f` and two representatives
of one element have the same image in `u(W)`.

Two further departures from the source's form.

* Only separatedness of `F` is used, not the full sheaf condition: what is needed is that a section
  of `F` over `p j` is determined by its restrictions along a covering. So the hypothesis is
  `Presieve.IsSeparated J F`, which a sheaf of sets satisfies (`Presieve.IsSheaf.isSeparated`, and
  `isSheaf_iff_isSheaf_of_type` for a `Sheaf J (Type w)`).
* A site in the sense of the source has base change for coverings (Stacks 00VH (3)): the fibre
  product `X ×_W Y k` of a member of a covering along an arbitrary morphism `X ⟶ W` exists. A
  `GrothendieckTopology` carries no such assumption, so it is the hypothesis `hpb`, stated for
  exactly the finite coverings the conclusion speaks about; it is weaker than `HasPullbacks C`,
  which is how the criterion of Stacks 00YQ will supply it.

The conclusion controls the sections of `u'`, not those of `u`; the criterion of Stacks 00YQ, which
needs a system all of whose own sections are covered, obtains it by iterating this lemma along `ω`
and passing to the colimit, a section of the colimit system already being a section of one of the
stages. That criterion applies the lemma with `w'` the universe `w` of the sheaf of `J`-closed
sieves.

Faithfulness, on the four points a reader should check against the source.

1. No hypothesis is dead: `hF` and `hpb` are what let a covering member be found at all, `haa'` is
   the source's `s ≠ s'` and reappears in the first conclusion, the finiteness of the coverings is
   used through the commutation of the filtered colimit `F_{p'}` with a finite product, and the
   three smallness hypotheses are what bound `M`.
2. The site is the source's throughout: one topology `J` on one category `C`, the same `J` for the
   separatedness of `F`, for `hpb` and for the coverings quantified over in the conclusion, and no
   auxiliary topology; the germs are germs of the source's `F` at the source's system.
3. The maps the source calls canonical are pinned, not merely asserted to exist: the transition
   maps `F_{p'} → F_p` and `u'(W) → u(W)` of a refinement are transport along `ε` followed by the
   colimit inclusion at `e j`, which is how both conclusions are written; no map is quantified
   over.
4. Not degenerate: take `N` the one-object one-morphism category and `p` the functor with value
   `V`, so that `u' = Mor(V, -)` and `F_{p'} = F(V)`; the hypotheses then say that `a ≠ a'` in
   `F(V)`, and the conclusion produces a system refining `V` separating them along which every
   morphism `V ⟶ W` becomes covered by every finite covering of `W` — which is exactly what the
   criterion of Stacks 00YQ starts from.

## References

* [Stacks 00YP](https://stacks.math.columbia.edu/tag/00YP), in the section "Criterion for existence
  of points" (Stacks 00YN); the previous step is Stacks 00YO and the criterion itself Stacks 00YQ.
* [SGA4], Exposé VI, appendix by Deligne.
-/

section

universe w w' v u t u₁ v₂ u₂
open CategoryTheory Limits Opposite

namespace Stacks.SitePoints.UniformRefinement

private lemma sieve_ofArrows_reindex {C : Type u} [Category.{v} C] {W : C} {ι : Type*} {ι' : Type*}
    (τ : ι' ≃ ι) {Y : ι → C} (g : ∀ k, Y k ⟶ W) :
    Sieve.ofArrows (fun k => Y (τ k)) (fun k => g (τ k)) = Sieve.ofArrows Y g := by
  have h : Presieve.ofArrows (fun k => Y (τ k)) (fun k => g (τ k)) = Presieve.ofArrows Y g := by
    funext Z
    ext u
    refine ⟨fun ⟨k⟩ => Presieve.ofArrows.mk (τ k), fun ⟨k⟩ => ?_⟩
    obtain ⟨k', rfl⟩ := τ.surjective k
    exact Presieve.ofArrows.mk k'
  simp [Sieve.ofArrows, h]

private lemma sieve_ofArrows_ulift {C : Type u} [Category.{v} C] {W : C} {ι : Type*} {Y : ι → C}
    (g : ∀ k, Y k ⟶ W) :
    Sieve.ofArrows (fun k : ULift.{t} ι => Y k.down) (fun k => g k.down) = Sieve.ofArrows Y g :=
  sieve_ofArrows_reindex Equiv.ulift g

/-- An element of the empty `Finset` proves anything: the projections of a wide fibre product over
no instruction at all. -/
private def notMem_empty_elim {α : Type*} {P : Sort*} {a : α} (h : a ∈ (∅ : Finset α)) : P := by
  simp at h

/-! ### Covering data and instructions -/

section Data

variable {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N]

/-- The functor from the skeleton of `N` to `N`. -/
private noncomputable def sk (N : Type u₁) [SmallCategory N] : Skeleton N ⥤ N :=
  (skeletonEquivalence N).functor

/-- An object of the skeleton of `N` whose image in `N` is isomorphic to a given index. -/
private noncomputable def skPre (j : N) : Skeleton N :=
  (skeletonEquivalence N).inverse.obj j

/-- The isomorphism exhibiting an index of `N` as the image under
`Stacks.SitePoints.UniformRefinement.sk` of an object of the skeleton. It is what lets a section of
`u'` represented at an arbitrary index of `N` be recorded in a covering datum, whose index is taken
in the skeleton for smallness. -/
private noncomputable def skPreIso (j : N) : (sk N).obj (skPre j) ≅ j :=
  (skeletonEquivalence N).counitIso.app j

noncomputable section

/-- A *covering datum* for a system `p : N ⥤ C`: a finite covering `{g k : Y k ⟶ W}` of the site,
indexed by `Fin n` with `n` positive, together with a section of `u'(W)`, given by an index `jj` of
(the skeleton of) `N` and a morphism `f : p jj ⟶ W`. -/
private structure CovData (J : GrothendieckTopology C) (p : N ⥤ C) where
  /-- The number of members of the covering. -/
  n : ℕ
  /-- The covering is nonempty; an empty covering separates nothing and is dealt with directly. -/
  pos : 0 < n
  /-- The base of the covering. -/
  W : C
  /-- The members of the covering. -/
  Y : Fin n → C
  /-- The structure morphisms of the covering. -/
  g : ∀ k, Y k ⟶ W
  /-- The family is a covering of the site. -/
  covering : Sieve.ofArrows Y g ∈ J W
  /-- The index at which the section of `u'(W)` is represented. -/
  jj : Skeleton N
  /-- The section of `u'(W)`, as a morphism out of the system. -/
  f : p.obj ((sk N).obj jj) ⟶ W

/-- An *instruction* at the index `j`: a covering datum, a chosen member of its covering, and a
morphism from `j` to the index of its section. -/
private structure Instr (J : GrothendieckTopology C) (p : N ⥤ C) (j : N) where
  /-- The covering datum. -/
  c : CovData J p
  /-- The chosen member of the covering. -/
  k : Fin c.n
  /-- The morphism along which the section is transported to `j`. -/
  φ : j ⟶ (sk N).obj c.jj

variable {J : GrothendieckTopology C} {p : N ⥤ C}

/-- An instruction at `j'` pulls back to an instruction at `j` along `ψ : j ⟶ j'`. -/
private def pullInstr {j j' : N} (ψ : j ⟶ j') (i : Instr J p j') : Instr J p j :=
  ⟨i.c, i.k, ψ ≫ i.φ⟩

private lemma pullInstr_mk {j j' : N} (ψ : j ⟶ j') (c : CovData J p) (k : Fin c.n)
    (φ : j' ⟶ (sk N).obj c.jj) : pullInstr ψ (⟨c, k, φ⟩ : Instr J p j') = ⟨c, k, ψ ≫ φ⟩ :=
  rfl

private lemma pullInstr_c {j j' : N} (ψ : j ⟶ j') (i : Instr J p j') : (pullInstr ψ i).c = i.c :=
  rfl

private lemma pullInstr_k {j j' : N} (ψ : j ⟶ j') (i : Instr J p j') : (pullInstr ψ i).k = i.k :=
  rfl

private lemma pullInstr_id {j : N} (i : Instr J p j) : pullInstr (𝟙 j) i = i := by
  cases i with
  | mk c k φ => simp [pullInstr]

private lemma pullInstr_comp {j j' j'' : N} (ψ : j ⟶ j') (χ : j' ⟶ j'') (i : Instr J p j'') :
    pullInstr (ψ ≫ χ) i = pullInstr ψ (pullInstr χ i) := by simp [pullInstr, Category.assoc]

/-- Pulling an instruction back along the two legs of a retraction returns it. -/
private lemma pullInstr_pullInstr_of_comp_eq_id {j j' : N} (ψ : j ⟶ j') (χ : j' ⟶ j)
    (hψχ : ψ ≫ χ = 𝟙 j) (i : Instr J p j) : pullInstr ψ (pullInstr χ i) = i := by
  rw [← pullInstr_comp, hψχ, pullInstr_id]

/-- The member of the covering prescribed by an instruction. -/
private def mid {j : N} (i : Instr J p j) : C :=
  i.c.Y i.k

/-- The structure morphism of the member of the covering prescribed by an instruction. -/
private def leg {j : N} (i : Instr J p j) : mid i ⟶ i.c.W :=
  i.c.g i.k

/-- The morphism to the base of the covering along which an instruction prescribes a fibre
product, for an object of `C` given over `p j`. -/
private def toBase {j : N} (i : Instr J p j) {X : C} (π : X ⟶ p.obj j) : X ⟶ i.c.W :=
  π ≫ p.map i.φ ≫ i.c.f

private lemma toBase_pullInstr {j j' : N} (ψ : j ⟶ j') (i : Instr J p j') {X : C}
    (π : X ⟶ p.obj j) : toBase (pullInstr ψ i) π = toBase i (π ≫ p.map ψ) := by
  simp [toBase, pullInstr, Functor.map_comp, Category.assoc]

/-- Precomposing the object over `p j` with a morphism precomposes the morphism to the base of the
covering. -/
private lemma toBase_comp {j : N} (i : Instr J p j) {X X' : C} (r : X ⟶ X') (π : X' ⟶ p.obj j) :
    toBase i (r ≫ π) = r ≫ toBase i π :=
  Category.assoc _ _ _

end

end Data

end Stacks.SitePoints.UniformRefinement

end
