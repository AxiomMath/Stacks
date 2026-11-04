module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Tfae
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference
public import StacksFrontier.Topology.Dimension.FiniteSpaces
public import StacksCore.Tactic.StacksAttribute

/-!
# Dimension over a Jacobson base

Let `S` be a Jacobson base scheme for Chow homology whose dimension function vanishes at every
closed point, and let `X` be locally of finite type over `S`. Then for an integral closed
subscheme `Z` of `X` the three numbers

* the relative dimension of the base dimension function at the generic point of `Z`,
* the dimension of `Z`,
* the dimension of the local ring of `Z` at any closed point of `Z`,

all agree, and the first of them is nonnegative.

## Main results

* `Stacks.Chow.relativeDimension_eq_zero_of_isClosed` — the relative dimension vanishes at a
  closed point.
* `Stacks.Chow.relativeDimension_nonneg` — the relative dimension is nonnegative.
* `Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat` — the dimension of an integral
  closed subscheme is the relative dimension at its generic point.
* `Stacks.Chow.topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed` — that dimension is also
  the dimension of the local ring at any closed point.

## Implementation notes

Topological and ring Krull dimensions take values in `WithBot ℕ∞`, whereas a dimension function
is integer valued. Nonnegativity of the relative dimension is what makes `Int.toNat` lossless,
so the two statements together express the equality of integers in the source, and the
displayed dimension equality also records finiteness. A closed subscheme is represented by a
closed immersion `i : Z ⟶ X`, and its generic point is a generic point of the whole underlying
space of `Z`.

The order on the points of a scheme is the specialization preorder, for which `y ≤ x` unfolds to
`x ⤳ y`; it is a partial order because a scheme is `T0`, but that partial order is not an
instance. The auxiliary estimate `Stacks.Chow.toNat_dimensionFunction_le_height` therefore takes
the strict-order comparison it needs as a hypothesis rather than a `PartialOrder` instance,
which lets it be used both on a scheme and on an upper set of one.

## References

* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace Stacks.Chow

/-! ### Dimension functions along a closed embedding and on an upper set -/

/-- A closed embedding carries an immediate specialization to an immediate specialization: an
intermediate point of the images lies in the (closed) range, being a specialization of a point
of the range, hence is the image of an intermediate point. -/
private theorem isImmediateSpecialization_map_of_isClosedEmbedding {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {e : X → Y} (he : Topology.IsClosedEmbedding e)
    {x y : X} (h : IsImmediateSpecialization x y) :
    IsImmediateSpecialization (e x) (e y) := by
  refine ⟨he.isInducing.specializes_iff.mpr h.1, fun eq => h.2.1 (he.injective eq), ?_⟩
  intro z hxz hzy
  obtain ⟨w, rfl⟩ : z ∈ Set.range e := hxz.mem_closed he.isClosed_range (Set.mem_range_self _)
  rcases h.2.2 w (he.isInducing.specializes_iff.mp hxz)
      (he.isInducing.specializes_iff.mp hzy) with hw | hw
  · exact .inl (congrArg e hw)
  · exact .inr (congrArg e hw)

/-- A dimension function pulls back along a closed embedding. Both defining properties transfer
because a closed embedding reflects specializations and preserves immediateness. -/
private def dimensionFunctionComap {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {e : X → Y} (he : Topology.IsClosedEmbedding e)
    (d : DimensionFunction Y) : DimensionFunction X where
  toFun := d ∘ e
  strictAnti_specializes := fun _ _ hxy hne =>
    d.strictAnti_specializes (he.isInducing.specializes_iff.mpr hxy)
      fun eq => hne (he.injective eq)
  step_immediate := fun _ _ hxy =>
    d.step_immediate (isImmediateSpecialization_map_of_isClosedEmbedding he hxy)

/-- A dimension function on a scheme restricts to the upper set of points specializing a given
one. An intermediate point of a specialization between two points of that upper set is itself in
the upper set, the specialization order being transitive. -/
private def dimensionFunctionIci {Z : Scheme.{u}} (d : DimensionFunction Z) (z : Z) :
    DimensionFunction (Set.Ici z) where
  toFun x := d x.1
  strictAnti_specializes := fun _ _ hxy hne =>
    d.strictAnti_specializes ((subtype_specializes_iff _ _).mp hxy)
      fun heq => hne (Subtype.ext heq)
  step_immediate := fun _ y hxy => by
    refine d.step_immediate ⟨(subtype_specializes_iff _ _).mp hxy.1,
      fun heq => hxy.2.1 (Subtype.ext heq), fun w hxw hwy => ?_⟩
    rcases hxy.2.2 (⟨w, y.2.trans (show (y : Z) ≤ w from hwy)⟩ : Set.Ici z)
        ((subtype_specializes_iff _ _).mpr hxw)
        ((subtype_specializes_iff _ _).mpr hwy) with hw | hw
    · exact .inl (congrArg Subtype.val hw)
    · exact .inr (congrArg Subtype.val hw)

/-- The value of a dimension function at a point specializing to a point of value zero is a
lower bound for the height of that point, the order being one in which a nontrivial
specialization strictly decreases. The bound is proved by induction on the value, stepping down
along an immediate specialization. -/
private theorem toNat_dimensionFunction_le_height {Z : Type u} [TopologicalSpace Z] [Preorder Z]
    (hlt : ∀ {a b : Z}, a ⤳ b → a ≠ b → b < a) (d : DimensionFunction Z)
    {x z : Z} (hxz : x ⤳ z) (hz : d z = 0) :
    ((d x).toNat : ℕ∞) ≤ Order.height x := by
  have aux : ∀ (n : ℕ) (x : Z), x ⤳ z → (d x).toNat ≤ n →
      ((d x).toNat : ℕ∞) ≤ Order.height x := by
    intro n
    induction n with
    | zero => intro x _ hle; simp [Nat.eq_zero_of_le_zero hle]
    | succ n ih =>
      intro x hxz hle
      by_cases heq : x = z
      · subst x; simp [hz]
      obtain ⟨y, himm, hyz⟩ := d.exists_isImmediateSpecialization hxz heq
      have hstep := d.step_immediate himm
      have hnonneg : 0 ≤ d y := by
        by_cases hy : y = z
        · simp [hy, hz]
        · have := d.strictAnti_specializes hyz hy; omega
      have hcast : (d x).toNat = (d y).toNat + 1 := by omega
      rw [hcast, Nat.cast_add, Nat.cast_one]
      exact (add_le_add (ih y hyz (by omega)) le_rfl).trans
        (Order.height_add_one_le (hlt himm.1 himm.2.1))
  exact aux _ x hxz le_rfl

/-- On a scheme a nontrivial specialization is strict for the specialization order: the
underlying space is `T0`, so two points specializing to each other are equal. -/
private theorem lt_of_specializes {Z : Scheme.{u}} {a b : Z} (h : a ⤳ b) (hne : a ≠ b) :
    b < a :=
  lt_iff_le_not_ge.mpr ⟨h, fun h' => hne (Specializes.antisymm h h').eq⟩

/-- The topological Krull dimension of a scheme is the Krull dimension of its specialization
order, since irreducible closed subsets correspond to points. -/
private theorem topologicalKrullDim_eq_krullDim (Z : Scheme.{u}) :
    topologicalKrullDim Z = Order.krullDim Z :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-! ### The dimension of an integral scheme carrying a dimension function -/

/-- An integral scheme with a nonnegative dimension function vanishing at some point has
dimension the value of that function at a generic point. The upper bound comes from the
strictly monotone map to `Fin (n + 1)` given by the dimension function, the lower bound from
`Stacks.Chow.toNat_dimensionFunction_le_height` at the generic point. -/
private theorem topologicalKrullDim_eq_toNat_of_isGenericPoint {Z : Scheme.{u}} [IsIntegral Z]
    (d : DimensionFunction Z) (hnonneg : ∀ x : Z, 0 ≤ d x) (z : Z) (hzdim : d z = 0)
    (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z)) :
    topologicalKrullDim Z = (d ξ).toNat := by
  have hξmax : ∀ x : Z, d x ≤ d ξ := by
    intro x
    by_cases heq : ξ = x
    · simp [← heq]
    · exact le_of_lt (d.strictAnti_specializes (hξ.specializes (by simp)) heq)
  have hupper : Order.krullDim Z ≤ (((d ξ).toNat : ℕ) : WithBot ℕ∞) := by
    have hr : StrictMono fun x : Z =>
        (⟨(d x).toNat, by have := hnonneg x; have := hξmax x; have := hnonneg ξ; omega⟩ :
          Fin ((d ξ).toNat + 1)) := by
      intro x y hxy
      have hlt := d.strictAnti_specializes hxy.le (Ne.symm (ne_of_lt hxy))
      have hx := hnonneg x
      have hy := hnonneg y
      exact Fin.mk_lt_mk.mpr (by omega)
    simpa [Order.krullDim_fin] using Order.krullDim_le_of_strictMono _ hr
  have hlower : (((d ξ).toNat : ℕ) : WithBot ℕ∞) ≤ Order.krullDim Z := by
    rw [← Order.height_top_eq_krullDim, ← show ξ = (⊤ : Z) from hξ.eq (genericPoint_spec Z)]
    exact_mod_cast toNat_dimensionFunction_le_height lt_of_specializes d
      (hξ.specializes (by simp)) hzdim
  rw [topologicalKrullDim_eq_krullDim]
  exact le_antisymm hupper hlower

/-- An integral scheme with a nonnegative dimension function vanishing at a point `z` has
dimension the dimension of its local ring at `z`. The local ring dimension is the coheight of
`z`, which is bounded below by the height of the generic point in the upper set `Set.Ici z`. -/
private theorem topologicalKrullDim_eq_ringKrullDim_stalk_of_dimensionFunction {Z : Scheme.{u}}
    [IsIntegral Z] (d : DimensionFunction Z) (hnonneg : ∀ x : Z, 0 ≤ d x) (z : Z)
    (hzdim : d z = 0) :
    topologicalKrullDim Z = ringKrullDim (Z.presheaf.stalk z) := by
  have hξ : IsGenericPoint (genericPoint Z) (Set.univ : Set Z) := genericPoint_spec Z
  have hξz : genericPoint Z ⤳ z := hξ.specializes (by simp)
  have hdim := topologicalKrullDim_eq_toNat_of_isGenericPoint d hnonneg z hzdim _ hξ
  have hzmem : z ∈ Set.Ici z := Set.mem_Ici.mpr le_rfl
  have hηζ : (⟨genericPoint Z, hξz⟩ : Set.Ici z) ⤳ (⟨z, hzmem⟩ : Set.Ici z) :=
    (subtype_specializes_iff _ _).mpr hξz
  have hzdim' : (dimensionFunctionIci d z) ⟨z, hzmem⟩ = 0 := hzdim
  have hbound := @toNat_dimensionFunction_le_height (Set.Ici z) _ _
    (fun h hne => lt_of_specializes ((subtype_specializes_iff _ _).mp h)
      fun heq => hne (Subtype.ext heq)) (dimensionFunctionIci d z) _ _ hηζ hzdim'
  have hheight : ((d (genericPoint Z)).toNat : ℕ∞) ≤
      Order.height (⟨genericPoint Z, hξz⟩ : Set.Ici z) := hbound
  have hcoheight : ((d (genericPoint Z)).toNat : ℕ∞) ≤ Order.coheight z := by
    rw [show (⟨genericPoint Z, hξz⟩ : Set.Ici z) = ⊤ from
      Subtype.ext (hξ.eq (genericPoint_spec Z))] at hheight
    have hh : (((d (genericPoint Z)).toNat : ℕ∞) : WithBot ℕ∞) ≤
        ((Order.height (⊤ : Set.Ici z) : ℕ∞) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr hheight
    rw [Order.height_top_eq_krullDim, ← Order.coheight_eq_krullDim_Ici] at hh
    exact WithBot.coe_le_coe.mp hh
  rw [ringKrullDim_stalk_eq_coheight]
  refine le_antisymm (hdim ▸ WithBot.coe_le_coe.mpr hcoheight) ?_
  rw [topologicalKrullDim_eq_krullDim]
  exact Order.coheight_le_krullDim z

/-! ### Dimension over a Jacobson base -/

variable (C : ChowSituation.{u}) [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)

include hδ

/-- Over a Jacobson base whose dimension function vanishes at closed points, the relative
dimension of a scheme locally of finite type vanishes at every closed point: the image point is
closed and the residue field extension is finite, hence of transcendence degree zero. -/
theorem relativeDimension_eq_zero_of_isClosed {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    relativeDimension C.dimensionFunction f x = 0 := by
  have hmap := ((jacobsonSpace_finiteTypePoints_tfae C.S).out 1 4).mp ‹JacobsonSpace C.S›
  obtain ⟨hbase, hfinite⟩ := hmap X f x hx
  let := (f.residueFieldMap x).hom.toAlgebra
  let : Module.Finite (C.S.residueField (f x)) (X.residueField x) := hfinite
  let : Algebra.IsAlgebraic (C.S.residueField (f x)) (X.residueField x) :=
    Algebra.IsAlgebraic.of_finite _ _
  simp [relativeDimension, hδ _ hbase, trdeg_eq_zero]

/-- **Stacks Project, Tag 02QO.** Over a Jacobson base whose dimension function vanishes at
closed points, the relative dimension of a scheme locally of finite type is nonnegative. Every
point specializes to a closed point of the closure of its singleton, where the relative
dimension vanishes, and a dimension function strictly decreases along specialization. -/
@[stacks 02QO "nonnegativity of the relative dimension"]
theorem relativeDimension_nonneg {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (x : X) :
    0 ≤ relativeDimension C.dimensionFunction f x := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨z, hz, hzclosed⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set X))
    ⟨x, subset_closure (Set.mem_singleton x)⟩ isClosed_closure.isLocallyClosed
  have hzdim := relativeDimension_eq_zero_of_isClosed C hδ f z hzclosed
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction f
  by_cases h : x = z
  · simp [h, hzdim]
  · have hlt := d.strictAnti_specializes (by simpa [specializes_iff_mem_closure] using hz) h
    rw [hd x, hd z, hzdim] at hlt
    omega

/-- **Stacks Project, Tag 02QO.** The dimension of an integral closed subscheme of a scheme
locally of finite type over a Jacobson base is the relative dimension at its generic point. The
latter is converted to a natural number; its nonnegativity is
`Stacks.Chow.relativeDimension_nonneg`. -/
@[stacks 02QO "relative dimension equals the dimension of the closed subscheme"]
theorem topologicalKrullDim_eq_relativeDimension_toNat {X Z : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z)) :
    topologicalKrullDim Z = (relativeDimension C.dimensionFunction f (i ξ)).toNat := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction f
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let : JacobsonSpace Z := JacobsonSpace.of_isClosedEmbedding i.isClosedEmbedding
  obtain ⟨z, -, hzclosed⟩ :=
    nonempty_inter_closedPoints (Z := (Set.univ : Set Z)) Set.univ_nonempty
      isClosed_univ.isLocallyClosed
  have hizclosed : IsClosed ({i z} : Set X) := by
    simpa [Set.image_singleton] using i.isClosedEmbedding.isClosed_iff_image_isClosed.mp hzclosed
  have hmain := topologicalKrullDim_eq_toNat_of_isGenericPoint
    (dimensionFunctionComap i.isClosedEmbedding d)
    (fun x => by simpa [dimensionFunctionComap, hd] using relativeDimension_nonneg C hδ f (i x))
    z (by simpa [dimensionFunctionComap, hd] using
      relativeDimension_eq_zero_of_isClosed C hδ f (i z) hizclosed) ξ hξ
  change topologicalKrullDim Z = (d (i ξ)).toNat at hmain
  rwa [hd] at hmain

/-- **Stacks Project, Tag 02QO.** The dimension of an integral closed subscheme of a scheme
locally of finite type over a Jacobson base equals the dimension of its local ring at every
closed point. -/
@[stacks 02QO "dimension of the local ring at a closed point", ega "IV 10.6.1" "(i)"]
theorem topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed {X Z : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (z : Z)
    (hz : IsClosed ({z} : Set Z)) :
    topologicalKrullDim Z = ringKrullDim (Z.presheaf.stalk z) := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction (i ≫ f)
  refine topologicalKrullDim_eq_ringKrullDim_stalk_of_dimensionFunction d
    (fun x => by simpa [hd] using relativeDimension_nonneg C hδ (i ≫ f) x) z ?_
  simpa [hd] using relativeDimension_eq_zero_of_isClosed C hδ (i ≫ f) z hz

end Stacks.Chow
