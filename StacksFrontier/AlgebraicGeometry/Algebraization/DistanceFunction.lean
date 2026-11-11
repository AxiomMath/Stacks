module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Distance from a closed subset of a Noetherian scheme

For a Noetherian scheme `Y` and a closed subset `Z`, the distance of a point `y` from `Z`
is the minimum of the weights of all zigzags of integral closed subschemes
`V₀ ⊆ W₀ ⊇ V₁ ⊆ ⋯ ⊇ Vₖ ⊆ Wₖ` starting in `Z` and ending at the closure of `y`.
The value is infinite when there is no such zigzag, equivalently when the connected component
of `y` does not meet `Z`.

## Main definitions

* `Stacks.Algebraization.DistanceSystem` is a zigzag of integral closed subschemes, with
  `Stacks.Algebraization.DistanceSystem.upCodimension`,
  `Stacks.Algebraization.DistanceSystem.downCodimension` and
  `Stacks.Algebraization.DistanceSystem.weight` for its codimensions and weight.
* `Stacks.Algebraization.distanceFunction` is the distance function `δᵞ_Z`.

## Main results

* `Stacks.Algebraization.nonempty_distanceSystem_of_connectedComponent_inter` records that a
  component meeting `Z` admits a zigzag. The defining infimum makes the distance no larger
  than the weight of any system.
* `Stacks.Algebraization.distanceFunction_eq_top_of_disjoint` and
  `Stacks.Algebraization.distanceFunction_eq_iInf_of_nonempty` unfold the two branches of the
  definition.

## Implementation notes

Integral closed subschemes are indexed by their irreducible closed underlying subsets; on a
Noetherian scheme each has a canonical reduced integral scheme structure. Relative codimension
is `IrreducibleClosedsCodim.topCodim`. The theorem `Stacks.Algebraization.topCodim_ne_top`
bounds it by the dimension of the Noetherian local ring at the generic point of the lower
endpoint, so `toNat` records its natural value without losing information. This uses the scheme
structure, not merely the Noetherian topology. The natural codimension is positive for
strict inclusions and increases when the lower endpoint is replaced by a smaller subset,
as recorded by `Stacks.Algebraization.topCodim_toNat_pos_of_lt` and
`Stacks.Algebraization.topCodim_toNat_anti_left`.
Subtraction in the weight is natural-number subtraction. Since the final summand `cₖ` is
nonnegative, taking the maximum makes this equal to the integer formula in the source.
The infimum of the empty family in `ℕ∞` is infinity.

## References

* [Stacks Project, Tag 0EIX](https://stacks.math.columbia.edu/tag/0EIX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Algebraization

/-- Relative codimension in a Noetherian scheme is finite: it is bounded by the dimension
of the local ring at the generic point of the lower endpoint. -/
public theorem topCodim_ne_top (Y : Scheme.{u}) [IsNoetherian Y]
    (V W : IrreducibleCloseds Y) :
    IrreducibleClosedsCodim.topCodim V W ≠ ⊤ := by
  let e := irreducibleSetEquivPoints (α := Y)
  have hbound : IrreducibleClosedsCodim.topCodim V W ≤ Order.coheight V := by
    rw [IrreducibleClosedsCodim.topCodim_le_iff]
    intro p hp _
    simpa [hp] using (Order.length_le_coheight_head (p := p))
  have hdim : Order.coheight (e V) ≠ ⊤ := by
    have h : ringKrullDim (Y.presheaf.stalk (e V)) ≠ ⊤ := ringKrullDim_ne_top
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at h
    exact fun htop => h (by simp [htop])
  rw [← Order.coheight_orderIso e V] at hbound
  exact ne_top_of_le_ne_top hdim hbound

/-- A strict inclusion in a Noetherian scheme has positive natural codimension. -/
public theorem topCodim_toNat_pos_of_lt (Y : Scheme.{u}) [IsNoetherian Y]
    {V W : IrreducibleCloseds Y} (hVW : V < W) :
    0 < (IrreducibleClosedsCodim.topCodim V W).toNat :=
  ENat.toNat_pos (zero_lt_one.trans_le (one_le_topCodim_of_lt V W hVW)).ne'
    (topCodim_ne_top Y V W)

/-- Replacing the lower endpoint by a smaller irreducible closed subset can only
increase the natural codimension, as happens when its generic point specializes. -/
public theorem topCodim_toNat_anti_left (Y : Scheme.{u}) [IsNoetherian Y]
    {V' V W : IrreducibleCloseds Y} (h : V' ≤ V) :
    (IrreducibleClosedsCodim.topCodim V W).toNat ≤
      (IrreducibleClosedsCodim.topCodim V' W).toNat := by
  refine ENat.toNat_le_toNat ?_ (topCodim_ne_top Y V' W)
  rcases h.eq_or_lt with rfl | hlt
  · exact le_rfl
  rw [IrreducibleClosedsCodim.topCodim_le_iff]
  intro p hp hlast
  have hhead : V' < p.head := by simpa only [hp] using hlt
  have hbound := IrreducibleClosedsCodim.length_le_topCodim V' W (p.cons V' hhead)
    (by simp) (by simpa using hlast)
  have hlen : p.length ≤ (p.cons V' hhead).length := by
    change p.length ≤ 0 + p.length + 1
    omega
  exact le_trans (by exact_mod_cast hlen) hbound

/-- A system of integral closed subschemes from `Z` to the generic point `y`. -/
public structure DistanceSystem (Y : Scheme.{u}) (Z : Closeds Y) (y : Y) where
  /-- The number of descending legs of the zigzag. -/
  k : ℕ
  /-- The lower endpoints `Vᵢ` of the zigzag. -/
  V : Fin (k + 1) → IrreducibleCloseds Y
  /-- The upper endpoints `Wᵢ` of the zigzag. -/
  W : Fin (k + 1) → IrreducibleCloseds Y
  /-- Each ascending leg goes up: `Vᵢ ⊆ Wᵢ`. -/
  V_le_W : ∀ i, V i ≤ W i
  /-- Each descending leg goes down: `Vᵢ₊₁ ⊆ Wᵢ`. -/
  V_next_le_W : ∀ i : Fin k, V (Fin.succ i) ≤ W (Fin.castSucc i)
  /-- The zigzag starts inside `Z`. -/
  V_zero_subset : (V ⟨0, Nat.zero_lt_succ k⟩ : Set Y) ⊆ (Z : Set Y)
  /-- The zigzag ends at the closure of `y`. -/
  W_last_eq_closure : (W (Fin.last k) : Set Y) = closure {y}

/-- The last upper endpoint of a system is the closure of the point the system ends at. -/
public theorem DistanceSystem.W_last_eq_closureSingleton {Y : Scheme.{u}} {Z : Closeds Y}
    {y : Y} (s : DistanceSystem Y Z y) :
    s.W (Fin.last s.k) = IrreducibleCloseds.closureSingleton y :=
  SetLike.coe_injective s.W_last_eq_closure

/-- The codimension `cᵢ = codim(Vᵢ,Wᵢ)` of the `i`-th ascending leg. -/
public def DistanceSystem.upCodimension {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {y : Y}
    (s : DistanceSystem Y Z y) (i : Fin (s.k + 1)) : ℕ :=
  (IrreducibleClosedsCodim.topCodim (s.V i) (s.W i)).toNat

/-- The codimension `bᵢ = codim(Vᵢ₊₁,Wᵢ)` of the `i`-th descending leg. -/
public def DistanceSystem.downCodimension {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {y : Y}
    (s : DistanceSystem Y Z y) (i : Fin s.k) : ℕ :=
  (IrreducibleClosedsCodim.topCodim (s.V (Fin.succ i)) (s.W (Fin.castSucc i))).toNat

/-- The natural ascending codimension represents the full topological codimension. -/
public theorem DistanceSystem.upCodimension_natCast {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {y : Y} (s : DistanceSystem Y Z y) (i : Fin (s.k + 1)) :
    (s.upCodimension i : ℕ∞) = IrreducibleClosedsCodim.topCodim (s.V i) (s.W i) :=
  ENat.natCast_toNat (topCodim_ne_top Y _ _)

/-- The natural descending codimension represents the full topological codimension. -/
public theorem DistanceSystem.downCodimension_natCast {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {y : Y} (s : DistanceSystem Y Z y) (i : Fin s.k) :
    (s.downCodimension i : ℕ∞) =
      IrreducibleClosedsCodim.topCodim (s.V (Fin.succ i)) (s.W (Fin.castSucc i)) :=
  ENat.natCast_toNat (topCodim_ne_top Y _ _)

/-- A strict ascending leg has positive represented codimension. -/
public theorem DistanceSystem.upCodimension_pos_of_lt {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {y : Y} (s : DistanceSystem Y Z y) (i : Fin (s.k + 1))
    (h : s.V i < s.W i) : 0 < s.upCodimension i :=
  topCodim_toNat_pos_of_lt Y h

/-- A strict descending leg has positive represented codimension. -/
public theorem DistanceSystem.downCodimension_pos_of_lt {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {y : Y} (s : DistanceSystem Y Z y) (i : Fin s.k)
    (h : s.V (Fin.succ i) < s.W (Fin.castSucc i)) : 0 < s.downCodimension i :=
  topCodim_toNat_pos_of_lt Y h

/-- The weight `k + maxᵢ (cᵢ + ⋯ + cₖ − bᵢ − ⋯ − bₖ₋₁)` of a system. -/
public def DistanceSystem.weight {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {y : Y}
    (s : DistanceSystem Y Z y) : ℕ :=
  s.k + (Finset.univ : Finset (Fin (s.k + 1))).sup (fun i =>
    (∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0) -
    (∑ j : Fin s.k, if i.val ≤ j.val then s.downCodimension j else 0))

/-- **Stacks Project, Tag 0EIX.** The distance from a closed subset of a Noetherian scheme.
It is the minimum weight of all systems of integral closed subschemes from `Z` to `y`, or
infinity if there is no system. -/
@[stacks 0EIX "δ_Z(y): the minimal weight of a zigzag from Z to the closure of y, and ∞ when \
the connected component of y misses Z"]
public def distanceFunction (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y)
    (y : Y) : ℕ∞ := by
  classical
  exact if (connectedComponent y ∩ (Z : Set Y)).Nonempty then
    ⨅ s : DistanceSystem Y Z y, (s.weight : ℕ∞)
  else ⊤

/-- Two points of a scheme are comparable when one specializes to the other. -/
private def comparableBySpecialization {Y : Scheme.{u}} (x y : Y) : Prop :=
  x ⤳ y ∨ y ⤳ x

/-- For comparable points, an irreducible closed subset containing the closures of both. -/
private noncomputable def upperPointClosure {Y : Scheme.{u}} (x y : Y)
    (_h : comparableBySpecialization x y) : IrreducibleCloseds Y := by
  classical
  exact if hx : x ⤳ y then IrreducibleCloseds.closureSingleton x
    else IrreducibleCloseds.closureSingleton y

private lemma closureSingleton_le_upperPointClosure {Y : Scheme.{u}} {x y : Y}
    (h : comparableBySpecialization x y) :
    IrreducibleCloseds.closureSingleton x ≤ upperPointClosure x y h ∧
      IrreducibleCloseds.closureSingleton y ≤ upperPointClosure x y h := by
  classical
  unfold upperPointClosure
  split_ifs with hx
  · exact ⟨le_rfl, hx.closure_subset⟩
  · exact ⟨(h.resolve_left hx).closure_subset, le_rfl⟩

/-- In a space with finitely many irreducible components, a set containing every irreducible
component it meets is clopen. -/
public theorem isClopen_of_forall_mem_irreducibleComponents_subset {X : Type*}
    [TopologicalSpace X] (hfin : (irreducibleComponents X).Finite) {S : Set X}
    (hS : ∀ C ∈ irreducibleComponents X, (C ∩ S).Nonempty → C ⊆ S) : IsClopen S := by
  have hcomp : ∀ z : X, ∃ C ∈ irreducibleComponents X, z ∈ C := fun z => by
    obtain ⟨C, hC, hsub⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {z} isIrreducible_singleton
    exact ⟨C, hC, hsub rfl⟩
  have hclosed : ∀ T : Set X, (∀ C ∈ irreducibleComponents X, (C ∩ T).Nonempty → C ⊆ T) →
      IsClosed T := fun T hT => by
    have : T = ⋃₀ {C | C ∈ irreducibleComponents X ∧ (C ∩ T).Nonempty} := by
      ext z
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · obtain ⟨C, hC, hzC⟩ := hcomp z
        exact Set.mem_sUnion.mpr ⟨C, ⟨hC, z, hzC, hz⟩, hzC⟩
      · obtain ⟨C, hC, hzC⟩ := Set.mem_sUnion.mp hz
        exact hT C hC.1 hC.2 hzC
    rw [this]
    exact (hfin.subset fun C hC => hC.1).isClosed_sUnion
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  refine ⟨hclosed S hS, isClosed_compl_iff.mp (hclosed Sᶜ ?_)⟩
  rintro C hC ⟨a, haC, haS⟩ z hzC hzS
  exact haS (hS C hC ⟨z, hzC, hzS⟩ haC)

/-- On a Noetherian scheme, any two points of one connected component are joined by a finite
chain of specializations, in either direction. The chain is produced by showing that the set
of points reachable from `x` is a union of irreducible components, hence clopen. -/
private lemma exists_specializationChain_of_mem_connectedComponent
    {Y : Scheme.{u}} [IsNoetherian Y]
    {x y : Y} (hy : y ∈ connectedComponent x) :
    Relation.ReflTransGen comparableBySpecialization x y := by
  refine isPreconnected_connectedComponent.subset_isClopen
    (isClopen_of_forall_mem_irreducibleComponents_subset
      (NoetherianSpace.finite_irreducibleComponents (α := Y))
      (S := {z | Relation.ReflTransGen comparableBySpecialization x z})
      fun C hC ⟨a, haC, haS⟩ z hzC => ?_)
    ⟨x, mem_connectedComponent, Relation.ReflTransGen.refl⟩ hy
  obtain ⟨g, hg⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.tail haS (Or.inr (hg.specializes haC)))
    (Or.inl (hg.specializes hzC))

/-- Extend a system by one leg at the bottom, starting at a point of `Z` comparable with the
current starting point. -/
private noncomputable def prependDistanceSystem {Y : Scheme.{u}} {Z : Closeds Y}
    {x z y : Y} (hx : x ∈ (Z : Set Y)) (hxy : comparableBySpecialization x z)
    (s : DistanceSystem Y ⊤ y)
    (hs : s.V ⟨0, Nat.zero_lt_succ s.k⟩ = IrreducibleCloseds.closureSingleton z) :
    DistanceSystem Y Z y := by
  classical
  refine ⟨s.k + 1, Fin.cases (IrreducibleCloseds.closureSingleton x) s.V,
    Fin.cases (upperPointClosure x z hxy) s.W, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => s.V_le_W j) i
    exact (closureSingleton_le_upperPointClosure hxy).1
  · intro i
    refine Fin.cases ?_ (fun j => s.V_next_le_W j) i
    simpa only [Fin.cases_zero, Fin.cases_succ] using
      (hs.symm ▸ (closureSingleton_le_upperPointClosure hxy).2)
  · change closure ({x} : Set Y) ⊆ (Z : Set Y)
    exact closure_minimal (Set.singleton_subset_iff.mpr hx) Z.isClosed
  · change ((Fin.cases (upperPointClosure x z hxy) s.W
      (Fin.last (s.k + 1)) : IrreducibleCloseds Y) : Set Y) = _
    rw [← Fin.succ_last, Fin.cases_succ]
    exact s.W_last_eq_closure

/-- A chain of specializations from a point of `Z` to `y` assembles into a system from `Z`
to `y` starting at the closure of that point. -/
private lemma exists_distanceSystem_of_specializationChain {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {x y : Y} (hpath : Relation.ReflTransGen comparableBySpecialization x y)
    (hx : x ∈ (Z : Set Y)) :
    ∃ s : DistanceSystem Y Z y,
      s.V ⟨0, Nat.zero_lt_succ s.k⟩ = IrreducibleCloseds.closureSingleton x := by
  classical
  induction hpath using Relation.ReflTransGen.head_induction_on generalizing Z with
  | refl =>
      refine ⟨⟨0, fun _ => IrreducibleCloseds.closureSingleton y,
        fun _ => IrreducibleCloseds.closureSingleton y,
        fun _ => le_rfl, fun i => Fin.elim0 i, ?_, rfl⟩, rfl⟩
      change closure ({y} : Set Y) ⊆ (Z : Set Y)
      exact closure_minimal (Set.singleton_subset_iff.mpr hx) Z.isClosed
  | @head a b hab _ ih =>
      obtain ⟨s, hs⟩ := ih (Z := (⊤ : Closeds Y)) (Set.mem_univ b)
      exact ⟨prependDistanceSystem hx hab s hs, rfl⟩

/-- In a Noetherian scheme, a point connected to the closed subset `Z` admits a finite
zigzag of integral closed subschemes beginning in `Z` and ending at that point. -/
@[stacks 0EIX "existence of a zigzag in a connected component meeting Z"]
public theorem nonempty_distanceSystem_of_connectedComponent_inter
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) (y : Y)
    (h : (connectedComponent y ∩ (Z : Set Y)).Nonempty) :
    Nonempty (DistanceSystem Y Z y) := by
  obtain ⟨z, hzy, hzZ⟩ := h
  obtain ⟨s, _⟩ := exists_distanceSystem_of_specializationChain
    (exists_specializationChain_of_mem_connectedComponent
      (connectedComponent_eq hzy ▸ mem_connectedComponent)) hzZ
  exact ⟨s⟩

/-- If the connected component of `y` misses `Z`, its distance is infinite. -/
public theorem distanceFunction_eq_top_of_disjoint (Y : Scheme.{u}) [IsNoetherian Y]
    (Z : Closeds Y) (y : Y)
    (h : ¬ (connectedComponent y ∩ (Z : Set Y)).Nonempty) :
    distanceFunction Y Z y = ⊤ := by
  classical
  simp [distanceFunction, h]

/-- When the connected component of `y` meets `Z`, its distance is the minimum of all
system weights. -/
public theorem distanceFunction_eq_iInf_of_nonempty (Y : Scheme.{u}) [IsNoetherian Y]
    (Z : Closeds Y) (y : Y)
    (h : (connectedComponent y ∩ (Z : Set Y)).Nonempty) :
    distanceFunction Y Z y = ⨅ s : DistanceSystem Y Z y, (s.weight : ℕ∞) := by
  classical
  simp [distanceFunction, h]

end Stacks.Algebraization
