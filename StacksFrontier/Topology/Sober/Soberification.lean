module

public import Mathlib.Order.CompletePartialOrder
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
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The soberification of a topological space

The points of the soberification `Soberification X` of a topological space `X` are the
irreducible closed subsets of `X`; its opens are the sets `openOf U = {Z | Z ∩ U ≠ ∅}` for `U`
open in `X`, and the canonical map `c : X → Soberification X` sends `x` to `closure {x}`.

The soberification is sober, the assignment `V ↦ c ⁻¹' V` is a bijection between the opens of
`Soberification X` and the opens of `X` commuting with finite intersections and arbitrary
unions, and `c` is universal among continuous maps from `X` to sober spaces. The image `c(X)`
is Kolmogorov, and `c : X → c(X)` is universal among continuous maps from `X` to Kolmogorov
spaces.

## Main definitions

* `Soberification`: the irreducible closed subsets of `X`, topologised by the sets `openOf U`.
* `Soberification.openOf`: the irreducible closed subsets of `X` meeting a given subset.
* `Soberification.c`: the canonical map `x ↦ closure {x}`.
* `Soberification.openEquiv`: the bijection `Opens (Soberification X) ≃ Opens X`.
* `Soberification.lift`: the factorisation through `Soberification X` of a continuous map from
  `X` to a sober space, sending `Z` to the generic point of `closure (f '' Z)`.
* `Soberification.image`: the range of `c`.

## Main results

* `Soberification.quasiSober`, `Soberification.t0Space`: `Soberification X` is sober.
* `Soberification.openEquiv_symm_top`, `Soberification.openEquiv_symm_inf`,
  `Soberification.openEquiv_symm_iSup`: the bijection on opens commutes with finite
  intersections and arbitrary unions.
* `Soberification.lift_c`, `Soberification.lift_continuous`, `Soberification.lift_unique`:
  the universal property of `c` among sober spaces.
* `exists_universal_quasiSober`: all of the above, packaged as a single existential statement.
-/

@[expose] public section

universe u v

open Set TopologicalSpace

/-! ### Construction of the soberification -/

variable (X : Type u) [TopologicalSpace X]

/-- An irreducible closed subset of `X`. The points of the soberification. -/
@[sga "4 IV 4.2.1", sga "4 IV 7.1" "partial"]
structure Soberification where
  /-- The underlying set. -/
  carrier : Set X
  /-- The carrier is irreducible. -/
  isIrreducible' : IsIrreducible carrier
  /-- The carrier is closed. -/
  isClosed' : IsClosed carrier

namespace Soberification

variable {X}

/-- Two points of the soberification are equal as soon as their underlying sets are. -/
@[ext] lemma ext {Z W : Soberification X} (h : Z.carrier = W.carrier) : Z = W := by
  cases Z; cases W; cases h; rfl

/-- The underlying set of a point of the soberification is irreducible. -/
lemma isIrreducible_carrier (Z : Soberification X) : IsIrreducible Z.carrier := Z.isIrreducible'

/-- The underlying set of a point of the soberification is closed. -/
lemma isClosed_carrier (Z : Soberification X) : IsClosed Z.carrier := Z.isClosed'

/-- The underlying set of a point of the soberification is nonempty. -/
lemma nonempty_carrier (Z : Soberification X) : Z.carrier.Nonempty :=
    Z.isIrreducible_carrier.nonempty

/-- The open of `Soberification X` associated to a set `U` of `X`:
the set of irreducible closed subsets of `X` which meet `U`. -/
@[sga "4 IV 4.2.1"]
def openOf (U : Set X) : Set (Soberification X) := {Z | (Z.carrier ∩ U).Nonempty}

/-- A point `Z` lies in `openOf U` exactly when `Z.carrier` meets `U`. -/
@[simp] lemma mem_openOf {U : Set X} {Z : Soberification X} :
    Z ∈ openOf U ↔ (Z.carrier ∩ U).Nonempty := Iff.rfl

/-- An irreducible closed subset misses `openOf U` exactly when it avoids `U`. -/
lemma notMem_openOf_iff {U : Set X} {Z : Soberification X} :
    Z ∉ openOf U ↔ Z.carrier ⊆ Uᶜ :=
  ⟨fun h x hx hxU => h ⟨x, hx, hxU⟩, fun h ⟨_, hx, hxU⟩ => h hx hxU⟩

/-- The complement of `openOf U` is the set of irreducible closed subsets contained in `Uᶜ`. -/
lemma compl_openOf (U : Set X) :
    (openOf U)ᶜ = {Z : Soberification X | Z.carrier ⊆ Uᶜ} :=
  Set.ext fun _ => notMem_openOf_iff

/-- The empty set of `X` gives the empty set of the soberification. -/
@[simp] lemma openOf_empty : openOf (∅ : Set X) = ∅ := by
  ext Z; simp [openOf]

/-- The whole space `X` gives the whole soberification. -/
@[simp] lemma openOf_univ : openOf (Set.univ : Set X) = Set.univ := by
  ext Z
  simp only [openOf, inter_univ, mem_ofPred_eq, mem_univ, iff_true]
  exact Z.nonempty_carrier

/-- `openOf` turns the intersection of two opens of `X` into the intersection of the
corresponding sets of irreducible closed subsets. -/
lemma openOf_inter (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    openOf (U ∩ V) = openOf U ∩ openOf V := by
  ext Z
  refine ⟨fun ⟨x, hxZ, hxU, hxV⟩ => ⟨⟨x, hxZ, hxU⟩, ⟨x, hxZ, hxV⟩⟩, ?_⟩
  rintro ⟨hU', hV'⟩
  exact Z.isIrreducible_carrier.isPreirreducible U V hU hV hU' hV'

/-- `openOf` turns an arbitrary union of subsets of `X` into the corresponding union. -/
lemma openOf_iUnion {ι : Sort*} (U : ι → Set X) :
    openOf (⋃ i, U i) = ⋃ i, openOf (U i) := by
  ext Z
  simp [openOf, Set.inter_iUnion]

/-- The topology on `Soberification X`. The opens are precisely the sets of the form
`openOf U` for `U` open in `X`. -/
@[sga "4 IV 4.2.1"]
instance topologicalSpace : TopologicalSpace (Soberification X) where
  IsOpen V := ∃ U : Set X, IsOpen U ∧ V = openOf U
  isOpen_univ := ⟨Set.univ, isOpen_univ, openOf_univ.symm⟩
  isOpen_inter := by
    rintro V W ⟨U, hU, rfl⟩ ⟨U', hU', rfl⟩
    exact ⟨U ∩ U', hU.inter hU', (openOf_inter U U' hU hU').symm⟩
  isOpen_sUnion := by
    intro S hS
    choose U hU hUeq using hS
    refine ⟨⋃ (V : S), U V V.2, isOpen_iUnion (fun V => hU V V.2), ?_⟩
    rw [openOf_iUnion]
    ext Z
    simp only [mem_sUnion, mem_iUnion]
    refine ⟨fun ⟨V, hVS, hZ⟩ => ⟨⟨V, hVS⟩, ?_⟩, fun ⟨V, hZ⟩ => ⟨V.1, V.2, ?_⟩⟩
    · rwa [← hUeq V hVS]
    · rwa [hUeq V.1 V.2]

/-- A subset of `Soberification X` is open exactly when it is `openOf U` for some open
`U ⊆ X`. -/
@[sga "4 IV 4.2.1" "partial"]
lemma isOpen_iff {V : Set (Soberification X)} :
    IsOpen V ↔ ∃ U : Set X, IsOpen U ∧ V = openOf U := Iff.rfl

/-- `openOf U` is open in `Soberification X` whenever `U` is open in `X`. -/
@[sga "4 IV 4.2.1" "U′ is open"]
lemma isOpen_openOf {U : Set X} (hU : IsOpen U) : IsOpen (openOf U) := ⟨U, hU, rfl⟩

/-- The canonical map `c : X → Soberification X` sending `x` to `closure {x}`. -/
@[sga "4 IV 4.2.1"]
def c (x : X) : Soberification X :=
  { carrier := closure ({x} : Set X)
    isIrreducible' := isIrreducible_singleton.closure
    isClosed' := isClosed_closure }

/-- The underlying set of `c x` is `closure {x}`. -/
@[simp] lemma c_carrier (x : X) : (c x).carrier = closure ({x} : Set X) := rfl

/-- A point of `U` is sent by `c` into `openOf U`. -/
lemma c_mem_openOf {U : Set X} {x : X} (hx : x ∈ U) : c x ∈ openOf U :=
  ⟨x, subset_closure rfl, hx⟩

/-- For `U` open in `X`, `c⁻¹(openOf U) = U`. -/
@[sga "4 IV 4.2.1" "φ⁻¹(U′) = U"]
lemma c_preimage_openOf (U : Set X) (hU : IsOpen U) : c ⁻¹' (openOf U) = U := by
  ext x
  simp only [openOf, mem_preimage, mem_ofPred_eq, c_carrier]
  refine ⟨?_, fun hx => ⟨x, subset_closure rfl, hx⟩⟩
  rintro ⟨y, hyc, hyU⟩
  rw [mem_closure_iff] at hyc
  obtain ⟨z, hzU, rfl⟩ := hyc U hU hyU
  exact hzU

/-- For `U` open in `X`, the point `c x` meets `U` exactly when `x` does. -/
lemma c_mem_openOf_iff {U : Set X} (hU : IsOpen U) {x : X} : c x ∈ openOf U ↔ x ∈ U :=
  Set.ext_iff.mp (c_preimage_openOf U hU) x

/-- The canonical map `c : X → Soberification X` is continuous. -/
@[sga "4 IV 4.2.1" "continuity of φ"]
lemma continuous_c : Continuous (c : X → Soberification X) := by
  rw [continuous_def]
  rintro V ⟨U, hU, rfl⟩
  rwa [c_preimage_openOf U hU]

/-- `openOf` is injective on the open subsets of `X`. -/
lemma openOf_injOn :
    Set.InjOn (openOf : Set X → Set (Soberification X)) {U | IsOpen U} := by
  intro U hU V hV h
  simpa only [c_preimage_openOf U hU, c_preimage_openOf V hV] using congrArg (c ⁻¹' ·) h

/-- The closure of a point `Z` of the soberification is the set of irreducible closed subsets
contained in `Z.carrier`. -/
lemma closure_singleton (Z : Soberification X) :
    closure ({Z} : Set (Soberification X)) = {W : Soberification X | W.carrier ⊆ Z.carrier} := by
  ext W
  rw [mem_closure_iff]
  simp only [mem_ofPred_eq]
  refine ⟨fun hW => ?_, fun hWZ V hV hWV => ?_⟩
  · by_contra hWnsub
    obtain ⟨x, hxW, hxZ⟩ := Set.not_subset.mp hWnsub
    obtain ⟨Z', hZ'mem, hZ'eq⟩ :=
      hW _ (isOpen_openOf Z.isClosed_carrier.isOpen_compl) ⟨x, hxW, hxZ⟩
    rw [mem_singleton_iff] at hZ'eq
    exact notMem_openOf_iff.mpr (by simp) (hZ'eq ▸ hZ'mem)
  · refine ⟨Z, ?_, rfl⟩
    obtain ⟨U, -, rfl⟩ := hV
    obtain ⟨x, hxW, hxU⟩ := hWV
    exact ⟨x, hWZ hxW, hxU⟩

/-- The image of `Z.carrier` under `c` is dense in the closure of the point `Z`. -/
lemma closure_singleton_eq_closure_image_c (Z : Soberification X) :
    closure ({Z} : Set (Soberification X)) = closure (c '' Z.carrier) := by
  refine subset_antisymm ?_ (closure_minimal (fun W hW => ?_) isClosed_closure)
  · rw [closure_singleton]
    intro W hW
    rw [mem_closure_iff]
    rintro V ⟨U, -, rfl⟩ hWV
    obtain ⟨x, hxW, hxU⟩ := hWV
    exact ⟨c x, c_mem_openOf hxU, mem_image_of_mem _ (hW hxW)⟩
  · obtain ⟨x, hxZ, rfl⟩ := hW
    rw [closure_singleton]
    exact Z.isClosed_carrier.closure_subset_iff.mpr (singleton_subset_iff.mpr hxZ)

/-- If the closed set `(openOf U)ᶜ` of the soberification is irreducible, then so is the closed
set `Uᶜ` of `X`. -/
lemma isIrreducible_compl_of_isIrreducible_compl_openOf {U : Set X} (hU : IsOpen U)
    (hT : IsIrreducible ((openOf U)ᶜ : Set (Soberification X))) : IsIrreducible (Uᶜ : Set X) := by
  refine ⟨?_, fun V₁ V₂ hV₁ hV₂ ⟨z₁, hz₁, hz₁V₁⟩ ⟨z₂, hz₂, hz₂V₂⟩ => ?_⟩
  · obtain ⟨W, hW⟩ := hT.nonempty
    obtain ⟨x, hx⟩ := W.nonempty_carrier
    exact ⟨x, notMem_openOf_iff.mp hW hx⟩
  · obtain ⟨W, hW, hWV₁, hWV₂⟩ :=
      hT.isPreirreducible _ _ (isOpen_openOf hV₁) (isOpen_openOf hV₂)
        ⟨c z₁, fun h => hz₁ ((c_mem_openOf_iff hU).mp h), c_mem_openOf hz₁V₁⟩
        ⟨c z₂, fun h => hz₂ ((c_mem_openOf_iff hU).mp h), c_mem_openOf hz₂V₂⟩
    obtain ⟨w, hw, hw₁, hw₂⟩ :=
      W.isIrreducible_carrier.isPreirreducible V₁ V₂ hV₁ hV₂ hWV₁ hWV₂
    exact ⟨w, notMem_openOf_iff.mp hW hw, hw₁, hw₂⟩

/-- `Soberification X` is quasi-sober: every irreducible closed subset has a generic point. -/
@[sga "4 IV 4.2.1" "partial"]
instance quasiSober : QuasiSober (Soberification X) where
  sober := by
    intro T hT hTcl
    obtain ⟨U, hU, hUeq⟩ := hTcl.isOpen_compl
    have hT_eq : T = (openOf U)ᶜ := by rw [← hUeq, compl_compl]
    subst hT_eq
    refine ⟨⟨Uᶜ, isIrreducible_compl_of_isIrreducible_compl_openOf hU hT, hU.isClosed_compl⟩, ?_⟩
    rw [compl_openOf]
    exact closure_singleton _

/-- `Soberification X` is `T0`. -/
@[sga "4 IV 4.2.1" "partial"]
instance t0Space : T0Space (Soberification X) := by
  refine ⟨fun Z W h => ext ?_⟩
  rw [inseparable_iff_closure_eq, closure_singleton, closure_singleton, Set.ext_iff] at h
  simp only [mem_ofPred_eq] at h
  exact Set.Subset.antisymm ((h Z).mp subset_rfl) ((h W).mpr subset_rfl)

/-! ### The open–open bijection -/

/-- The forward map of the bijection between opens of `Soberification X` and opens of `X`:
sends an open `V` of `Soberification X` (which is `openOf U` for some open `U`) to its
preimage `c⁻¹(V) = U`. -/
@[sga "4 IV 4.2.1" "partial"]
def openEquiv : TopologicalSpace.Opens (Soberification X) ≃ TopologicalSpace.Opens X where
  toFun V :=
    { carrier := c ⁻¹' V.carrier
      is_open' := V.is_open'.preimage continuous_c }
  invFun U := ⟨openOf U.carrier, isOpen_openOf U.is_open'⟩
  left_inv V := by
    apply TopologicalSpace.Opens.ext
    rcases V with ⟨V, hV⟩
    rcases hV with ⟨U, hU, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk]
    rw [c_preimage_openOf U hU]
    rfl
  right_inv U := TopologicalSpace.Opens.ext (c_preimage_openOf U.carrier U.is_open')

/-- The open of `X` corresponding to `V` is the preimage `c ⁻¹' V`. -/
@[simp] lemma openEquiv_apply (V : TopologicalSpace.Opens (Soberification X)) :
    (openEquiv V : Set X) = c ⁻¹' (V : Set (Soberification X)) := rfl

/-- The open of `Soberification X` corresponding to `U` is `openOf U`. -/
@[simp] lemma openEquiv_symm_apply (U : TopologicalSpace.Opens X) :
    (openEquiv.symm U : Set (Soberification X)) = openOf (U : Set X) := rfl

/-- The inverse of `openEquiv` commutes with binary intersections. -/
lemma openEquiv_symm_inf (U V : TopologicalSpace.Opens X) :
    openEquiv.symm (U ⊓ V) = openEquiv.symm U ⊓ openEquiv.symm V :=
  TopologicalSpace.Opens.ext (openOf_inter _ _ U.is_open' V.is_open')

/-- The inverse of `openEquiv` sends the largest open of `X` to the largest open. -/
lemma openEquiv_symm_top :
    openEquiv.symm (⊤ : TopologicalSpace.Opens X) = ⊤ :=
  TopologicalSpace.Opens.ext openOf_univ

/-- The inverse of `openEquiv` commutes with arbitrary unions. -/
lemma openEquiv_symm_iSup {ι : Sort*} (U : ι → TopologicalSpace.Opens X) :
    openEquiv.symm (⨆ i, U i) = ⨆ i, openEquiv.symm (U i) := by
  apply TopologicalSpace.Opens.ext
  rw [openEquiv_symm_apply, TopologicalSpace.Opens.coe_iSup,
      TopologicalSpace.Opens.coe_iSup]
  ext Z
  simp only [openEquiv_symm_apply, mem_iUnion]
  rw [openOf_iUnion]
  simp [mem_iUnion]

/-- Taking preimages under `c` sends the largest open to the largest open. -/
lemma openEquiv_top : openEquiv (⊤ : TopologicalSpace.Opens (Soberification X)) = ⊤ :=
  TopologicalSpace.Opens.ext (by simp)

/-- Taking preimages under `c` commutes with binary intersections. -/
lemma openEquiv_inf (V W : TopologicalSpace.Opens (Soberification X)) :
    openEquiv (V ⊓ W) = openEquiv V ⊓ openEquiv W :=
  TopologicalSpace.Opens.ext (by simp)

/-- Taking preimages under `c` commutes with arbitrary unions. -/
lemma openEquiv_iSup {ι : Sort*} (V : ι → TopologicalSpace.Opens (Soberification X)) :
    openEquiv (⨆ i, V i) = ⨆ i, openEquiv (V i) :=
  TopologicalSpace.Opens.ext (by simp)

/-! ### Universal property among sober spaces -/

section UniversalSober

variable {Y : Type v} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
variable (f : X → Y) (hf : Continuous f)

/-- The lift `Soberification X → Y` of a continuous `f : X → Y` to a sober space.
It sends an irreducible closed `Z ⊆ X` to the unique generic point of `closure (f '' Z)`. -/
@[sga "4 IV 4.2.1"]
noncomputable def lift : Soberification X → Y :=
  fun Z => (Z.isIrreducible_carrier.image f hf.continuousOn).genericPoint

omit [T0Space Y] in
/-- `lift f hf Z` is a generic point of `closure (f '' Z.carrier)`. -/
lemma lift_isGenericPoint (Z : Soberification X) :
    IsGenericPoint (lift f hf Z) (closure (f '' Z.carrier)) :=
  (Z.isIrreducible_carrier.image f hf.continuousOn).isGenericPoint_genericPoint_closure

/-- The lift `lift f hf` composed with `c` is `f`. -/
@[simp, sga "4 IV 4.2.1" "partial"] lemma lift_c (x : X) : lift f hf (c x) = f x := by
  have hgen := lift_isGenericPoint f hf (c x)
  rw [c_carrier, closure_image_closure hf, image_singleton] at hgen
  exact hgen.eq isGenericPoint_closure

omit [T0Space Y] in
/-- The preimage under `lift f hf` of an open `V ⊆ Y` is the open of the soberification
associated to `f ⁻¹' V`. -/
lemma lift_preimage {V : Set Y} (hV : IsOpen V) :
    lift f hf ⁻¹' V = openOf (f ⁻¹' V) := by
  ext Z
  rw [Set.mem_preimage, (lift_isGenericPoint f hf Z).mem_open_set_iff hV,
    closure_inter_open_nonempty_iff hV, mem_openOf, image_inter_nonempty_iff]

omit [T0Space Y] in
/-- The lift of a continuous map to a sober space is continuous. -/
@[sga "4 IV 4.2.1" "partial"]
lemma lift_continuous : Continuous (lift f hf) := by
  rw [continuous_def]
  intro V hV
  rw [lift_preimage f hf hV]
  exact isOpen_openOf (hV.preimage hf)

omit [QuasiSober Y] [T0Space Y] in
/-- A continuous map out of the soberification which restricts to `f` along `c` sends the point
`Z` to a generic point of `closure (f '' Z.carrier)`. -/
lemma isGenericPoint_of_comp_c {g : Soberification X → Y} (hg : Continuous g)
    (hgc : ∀ x, g (c x) = f x) (Z : Soberification X) :
    IsGenericPoint (g Z) (closure (f '' Z.carrier)) := by
  change closure {g Z} = _
  rw [← image_singleton (f := g), ← closure_image_closure hg,
    closure_singleton_eq_closure_image_c, closure_image_closure hg, image_image]
  simp only [hgc]

/-- Uniqueness of the lift: if `g : Soberification X → Y` is continuous with `g ∘ c = f`,
then `g = lift f hf`. -/
@[sga "4 IV 4.2.1" "partial"]
lemma lift_unique (g : Soberification X → Y) (hg : Continuous g)
    (hgc : ∀ x, g (c x) = f x) : g = lift f hf :=
  funext fun Z => (isGenericPoint_of_comp_c f hg hgc Z).eq (lift_isGenericPoint f hf Z)

end UniversalSober

/-! ### Kolmogorov universal property -/

section UniversalKolmogorov

variable {Y : Type v} [TopologicalSpace Y] [T0Space Y]
variable (f : X → Y) (hf : Continuous f)

/-- The image of `c`. -/
def image : Set (Soberification X) := Set.range c

/-- Every `c x` lies in the image of `c`. -/
lemma c_mem_image (x : X) : c x ∈ (image : Set (Soberification X)) := ⟨x, rfl⟩

/-- The image `c(X)` is `T0`, being a subspace of the `T0` space `Soberification X`. -/
instance : T0Space (Soberification.image (X := X)) := inferInstance

omit [T0Space Y] in
/-- Two points of `X` have the same image under `c` exactly when they are inseparable. -/
lemma c_eq_iff {x y : X} : c x = c y ↔ Inseparable x y :=
  ⟨fun h => inseparable_iff_closure_eq.mpr (congrArg carrier h),
    fun h => ext (inseparable_iff_closure_eq.mp h)⟩

/-- A continuous map to a Kolmogorov space is constant on the fibres of `c`. -/
lemma eq_of_c_eq (hf : Continuous f) {x y : X} (h : c x = c y) : f x = f y :=
  ((c_eq_iff.mp h).map hf).eq

omit [T0Space Y] in
/-- A map out of the image of `c` which restricts to a continuous `f` along `c` is continuous. -/
lemma continuous_of_comp_c (hf : Continuous f)
    {f' : Set.range (c : X → Soberification X) → Y}
    (hf' : ∀ x : X, f' ⟨c x, ⟨x, rfl⟩⟩ = f x) : Continuous f' := by
  rw [continuous_def]
  intro V hV
  have h : f' ⁻¹' V = Subtype.val ⁻¹' openOf (f ⁻¹' V) := by
    ext ⟨z, x, rfl⟩
    simp [hf' x, c_mem_openOf_iff (hV.preimage hf)]
  rw [h]
  exact (isOpen_openOf (hV.preimage hf)).preimage continuous_subtype_val

/-- Universal property of `c : X → c(X)` among Kolmogorov spaces: a continuous map from `X` to a
`T0` space factors uniquely through the image of `c`. -/
lemma exists_unique_lift_image (hf : Continuous f) :
    ∃ f' : Set.range (c : X → Soberification X) → Y, Continuous f' ∧
      (∀ x : X, f' ⟨c x, ⟨x, rfl⟩⟩ = f x) ∧
      ∀ g : Set.range (c : X → Soberification X) → Y, Continuous g →
        (∀ x : X, g ⟨c x, ⟨x, rfl⟩⟩ = f x) → g = f' := by
  have hc : ∀ x : X, f (⟨x, rfl⟩ : ∃ y, c y = c x).choose = f x := fun x =>
    eq_of_c_eq f hf (⟨x, rfl⟩ : ∃ y, c y = c x).choose_spec
  refine ⟨fun z => f z.2.choose, continuous_of_comp_c f hf hc, hc, fun g _ hgc => funext ?_⟩
  rintro ⟨z, x, rfl⟩
  exact (hgc x).trans (hc x).symm

end UniversalKolmogorov

/-! ### The soberification theorem -/

/-- For any topological space `X`, there is a canonical continuous map `c : X → X'` from `X`
to a sober topological space `X'` which is universal among continuous maps from `X` to sober
topological spaces. Moreover, the assignment `U' ↦ c⁻¹(U')` is a bijection between opens of `X'`
and `X` which commutes with finite intersections and arbitrary unions. The image `c(X)` is a
Kolmogorov (`T0`) topological space and the map `c : X → c(X)` is universal for maps of `X` into
Kolmogorov spaces. -/
@[stacks 0A2N, sga "4 IV 4.2.1" "universal property"]
theorem exists_universal_quasiSober :
    -- Sober target with continuous canonical map and universal property
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : QuasiSober X') (_ : T0Space X')
      (c' : X → X') (_ : Continuous c'),
        (-- Universal property among sober spaces
         (∀ (Y : Type u) [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
            (f : X → Y), Continuous f →
              ∃ f' : X' → Y, Continuous f' ∧ f' ∘ c' = f ∧
                ∀ g : X' → Y, Continuous g → g ∘ c' = f → g = f') ∧
         -- Bijection between opens, commuting with finite intersections and arbitrary unions
         (∃ φ : TopologicalSpace.Opens X' ≃ TopologicalSpace.Opens X,
            (∀ V : TopologicalSpace.Opens X', (φ V : Set X) = c' ⁻¹' (V : Set X')) ∧
            (φ ⊤ = ⊤) ∧
            (∀ V W : TopologicalSpace.Opens X', φ (V ⊓ W) = φ V ⊓ φ W) ∧
            (∀ {ι : Sort*} (V : ι → TopologicalSpace.Opens X'),
                φ (⨆ i, V i) = ⨆ i, φ (V i))) ∧
         -- c(X) is T0 (Kolmogorov)
         T0Space (Set.range c') ∧
         -- Universal property for c : X → c(X) into Kolmogorov spaces
         (∀ (Y : Type u) [TopologicalSpace Y] [T0Space Y] (f : X → Y),
            Continuous f →
              ∃ f' : Set.range c' → Y, Continuous f' ∧
                (∀ x : X, f' ⟨c' x, ⟨x, rfl⟩⟩ = f x) ∧
                ∀ g : Set.range c' → Y, Continuous g →
                  (∀ x : X, g ⟨c' x, ⟨x, rfl⟩⟩ = f x) → g = f')) :=
  ⟨Soberification X, Soberification.topologicalSpace, Soberification.quasiSober,
    Soberification.t0Space, Soberification.c, Soberification.continuous_c,
    fun _Y _ _ _ f hf => ⟨Soberification.lift f hf, Soberification.lift_continuous f hf,
      funext (Soberification.lift_c f hf),
      fun g hg hgc => Soberification.lift_unique f hf g hg (congrFun hgc)⟩,
    ⟨Soberification.openEquiv (X := X), fun _ => rfl, Soberification.openEquiv_top,
      Soberification.openEquiv_inf, Soberification.openEquiv_iSup⟩,
    inferInstance, fun _Y _ _ f hf => Soberification.exists_unique_lift_image f hf⟩

end Soberification

