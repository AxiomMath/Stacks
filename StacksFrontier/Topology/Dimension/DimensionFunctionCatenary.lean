module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dimension functions on locally Noetherian sober catenary spaces

Let `X` be a topological space. A *dimension function* on `X` is a map `δ : X → ℤ` that drops
strictly along every non-trivial specialization `x ⤳ y` (i.e. `y ∈ closure {x}` with `x ≠ y`)
and drops by exactly one along every *immediate* specialization, i.e. one admitting no
intermediate point. Such a `δ` need not exist globally, but if `X` is locally Noetherian, sober
and catenary, then every point of `X` has an open neighbourhood carrying a dimension function.

Sobriety (every irreducible closed subset has a *unique* generic point) is the conjunction of
`QuasiSober` (existence) and `T0Space` (uniqueness).

## Main definitions

* `TopologicalSpace.IsLocallyNoetherianSpace`: every point has a Noetherian open neighbourhood.
* `TopologicalSpace.IsImmediateSpecialization`: a non-trivial specialization with no
  intermediate point.
* `TopologicalSpace.IsMaximalIrreducibleClosedChain`: a strictly increasing finite chain of
  irreducible closed sets admitting no refinement.
* `TopologicalSpace.IsTopologicallyCatenary`: between any two nested irreducible closed sets
  there is a maximal chain, and all such chains have the same length.
* `TopologicalSpace.DimensionFunction`: a dimension function on a topological space.
* `TopologicalSpace.codim`: the codimension of one irreducible closed set in another in a
  catenary space.

## Main results

* `TopologicalSpace.isTopologicallyCatenary_of_isOpen`: an open subspace of a sober catenary
  space is catenary.
* `TopologicalSpace.codim_add`: codimension is additive along `T ⊆ T' ⊆ T''`.
* `TopologicalSpace.exists_open_nhd_with_dimension_function`: every point of a locally
  Noetherian sober catenary space has an open neighbourhood carrying a dimension function.

## References

* [Stacks Project, Tag 02IC](https://stacks.math.columbia.edu/tag/02IC)
-/

@[expose] public section

namespace TopologicalSpace

/-- A topological space `X` is *locally Noetherian* if every point of `X` has
an open neighbourhood that is Noetherian in the induced subspace topology. -/
@[ega "0 2.2.1", sga "4 VI 2.15"]
def IsLocallyNoetherianSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ NoetherianSpace U

/-- A non-trivial specialization `x ⤳ y` (with `x ≠ y`) is *immediate* if
there is no intermediate point `z`, i.e. no `z` with `x ⤳ z`, `z ⤳ y` and
both `z ≠ x` and `z ≠ y`. -/
def IsImmediateSpecialization {X : Type*} [TopologicalSpace X] (x y : X) : Prop :=
  x ⤳ y ∧ x ≠ y ∧ ∀ z : X, x ⤳ z → z ⤳ y → z = x ∨ z = y

/-- A finite strictly increasing chain `c : Fin (m+1) → Set X` of irreducible
closed subsets of `X` is *maximal* if for every consecutive pair
`c i.castSucc ⊊ c i.succ` there is no irreducible closed subset `Z` of `X`
strictly between them, i.e. every irreducible closed `Z` with
`c i.castSucc ⊆ Z ⊆ c i.succ` must equal one of the endpoints. -/
def IsMaximalIrreducibleClosedChain {X : Type*} [TopologicalSpace X]
    {m : ℕ} (c : Fin (m + 1) → Set X) : Prop :=
  StrictMono c ∧
  (∀ i, IsIrreducible (c i) ∧ IsClosed (c i)) ∧
  (∀ (i : Fin m) (Z : Set X), IsIrreducible Z → IsClosed Z →
    c i.castSucc ⊆ Z → Z ⊆ c i.succ → Z = c i.castSucc ∨ Z = c i.succ)

/-- `X` is *(topologically) catenary* if for every pair of irreducible closed subsets `T ⊆ T'`
of `X`:

* there exists a maximal chain
  `T = T₀ ⊊ T₁ ⊊ ⋯ ⊊ Tₙ = T'` of irreducible closed subsets, and
* every such maximal chain has the same (finite) length `n`. -/
def IsTopologicallyCatenary (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ ⦃T T' : Set X⦄, IsIrreducible T → IsClosed T → IsIrreducible T' → IsClosed T' →
    T ⊆ T' →
      ∃ n : ℕ,
        (∃ c : Fin (n + 1) → Set X,
            c 0 = T ∧ c (Fin.last n) = T' ∧ IsMaximalIrreducibleClosedChain c) ∧
        (∀ (m : ℕ) (c : Fin (m + 1) → Set X),
            c 0 = T → c (Fin.last m) = T' → IsMaximalIrreducibleClosedChain c → m = n)

/-- A *dimension function* on a topological space `X` is a function
`δ : X → ℤ` such that:

* (a) for every non-trivial specialization `x ⤳ y` with `x ≠ y`,
      `δ y < δ x`;
* (b) for every immediate specialization `x ⤳ y`, `δ x = δ y + 1`. -/
@[sga "6 X 1.6"]
structure DimensionFunction (X : Type*) [TopologicalSpace X] where
  /-- The underlying function `X → ℤ`. -/
  toFun : X → ℤ
  /-- Property (a): strictly decreasing along non-trivial specializations. -/
  strictAnti_specializes : ∀ ⦃x y : X⦄, x ⤳ y → x ≠ y → toFun y < toFun x
  /-- Property (b): drops by exactly one along immediate specializations. -/
  step_immediate : ∀ ⦃x y : X⦄, IsImmediateSpecialization x y → toFun x = toFun y + 1

/-- A dimension function is applied to points of `X` by writing `δ x` for `δ.toFun x`. -/
instance {X : Type*} [TopologicalSpace X] :
    CoeFun (DimensionFunction X) (fun _ => X → ℤ) :=
  ⟨DimensionFunction.toFun⟩

/-- For a subset `S` of an open subspace `V ⊆ X` that is closed in `V`, taking the closure of
`S` in `X` and intersecting back with `V` recovers `S`. -/
@[ega "0 2.1.6" "partial"]
private lemma preimage_val_closure_image_val
    {X : Type*} [TopologicalSpace X]
    {V : Set X} {S : Set V} (hS_cl : IsClosed S) :
    Subtype.val ⁻¹' (closure (Subtype.val '' S)) = S := by
  refine Set.Subset.antisymm (fun x hx_cl => ?_) fun x hxS => subset_closure ⟨x, hxS, rfl⟩
  obtain ⟨F, hF_cl, rfl⟩ := isClosed_induced_iff.mp hS_cl
  exact closure_minimal (Set.image_preimage_subset Subtype.val F) hF_cl hx_cl

/-- The preimage in an open subspace `V` of the closure of a point `g ∈ V` is irreducible. -/
private lemma isIrreducible_preimage_val_closure_singleton
    {X : Type*} [TopologicalSpace X] {V : Set X} {g : X} (hg : g ∈ V) :
    IsIrreducible (Subtype.val ⁻¹' closure {g} : Set V) := by
  have := Topology.IsInducing.closure_eq_preimage_closure_image
    Topology.IsInducing.subtypeVal ({⟨g, hg⟩} : Set V)
  rw [Set.image_singleton] at this
  rw [← this]
  exact isIrreducible_singleton.closure

/-- Pulling a maximal chain back to an open subspace. If `cX` is a maximal chain of irreducible
closed subsets of `X` running from `closure (Subtype.val '' T)` to `closure (Subtype.val '' T')`
for irreducible closed `T`, `T'` in the open subspace `V`, then intersecting `cX` with `V`
produces a maximal chain in `V` from `T` to `T'` of the same length. -/
lemma exists_maximalIrreducibleClosedChain_preimage_val
    {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    {V : Set X} (hV : IsOpen V)
    {T T' : Set V}
    (hT_irr : IsIrreducible T) (hT_cl : IsClosed T)
    (hT'_cl : IsClosed T')
    {n : ℕ} {cX : Fin (n + 1) → Set X}
    (hcX0 : cX 0 = closure (Subtype.val '' T))
    (hcXn : cX (Fin.last n) = closure (Subtype.val '' T'))
    (hcX_max : IsMaximalIrreducibleClosedChain cX) :
    ∃ c : Fin (n + 1) → Set V, c 0 = T ∧ c (Fin.last n) = T' ∧
      IsMaximalIrreducibleClosedChain c := by
  obtain ⟨hcX_mono, hcX_irrcl, hcX_maximal⟩ := hcX_max
  obtain ⟨g0, hg0⟩ := QuasiSober.sober (hcX_irrcl 0).1 (hcX_irrcl 0).2
  have hg0_closure : closure ({g0} : Set X) = cX 0 := isGenericPoint_def.mp hg0
  obtain ⟨t, ht⟩ := hT_irr.nonempty
  have hg0_spec_t : g0 ⤳ (t : X) := by
    rw [specializes_iff_mem_closure, hg0_closure, hcX0]; exact subset_closure ⟨t, ht, rfl⟩
  have hg0_in_V : g0 ∈ V := hg0_spec_t.mem_open hV t.2
  have hgi_in_V : ∀ i : Fin (n + 1), ∃ gi : X, IsGenericPoint gi (cX i) ∧ gi ∈ V := by
    intro i
    obtain ⟨gi, hgi⟩ := QuasiSober.sober (hcX_irrcl i).1 (hcX_irrcl i).2
    have hgi_closure : closure ({gi} : Set X) = cX i := isGenericPoint_def.mp hgi
    refine ⟨gi, hgi, ?_⟩
    have hg0_in_cXi : g0 ∈ cX i := hcX_mono.monotone (Fin.zero_le i) hg0.mem
    exact (specializes_iff_mem_closure.mpr (hgi_closure ▸ hg0_in_cXi)).mem_open hV hg0_in_V
  set c : Fin (n + 1) → Set V := fun i => Subtype.val ⁻¹' (cX i) with hc_def
  have hc_irrcl : ∀ i, IsIrreducible (c i) ∧ IsClosed (c i) := by
    intro i
    obtain ⟨gi, hgi, hgi_V⟩ := hgi_in_V i
    refine ⟨?_, (hcX_irrcl i).2.preimage continuous_subtype_val⟩
    change IsIrreducible (Subtype.val ⁻¹' cX i)
    rw [← isGenericPoint_def.mp hgi]
    exact isIrreducible_preimage_val_closure_singleton hgi_V
  refine ⟨c, ?_, ?_, ?_, hc_irrcl, ?_⟩
  · simpa only [c, hcX0] using preimage_val_closure_image_val hT_cl
  · simpa only [c, hcXn] using preimage_val_closure_image_val hT'_cl
  · intro i j hij
    have hcX_ss := hcX_mono hij
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.preimage_mono hcX_ss.le, fun heq => ?_⟩
    obtain ⟨gj, hgj, hgj_V⟩ := hgi_in_V j
    have hgj_in_cXi : gj ∈ cX i :=
      (heq ▸ (hgj.mem : (⟨gj, hgj_V⟩ : V) ∈ c j) : (⟨gj, hgj_V⟩ : V) ∈ c i)
    exact hcX_ss.ne
      (le_antisymm hcX_ss.le ((hgj.mem_closed_set_iff (hcX_irrcl i).2).mp hgj_in_cXi))
  · intro i Z hZ_irr hZ_cl hZ_lo hZ_hi
    set ZX := closure (Subtype.val '' Z) with hZX_def
    have hZX_irr : IsIrreducible ZX :=
      (hZ_irr.image Subtype.val continuous_subtype_val.continuousOn).closure
    have hZX_lo : cX i.castSucc ⊆ ZX := by
      obtain ⟨gi, hgi, hgi_V⟩ := hgi_in_V i.castSucc
      exact (hgi.mem_closed_set_iff isClosed_closure).mp
        (subset_closure ⟨⟨gi, hgi_V⟩, hZ_lo (hgi.mem : (⟨gi, hgi_V⟩ : V) ∈ c i.castSucc), rfl⟩)
    have hZX_hi : ZX ⊆ cX i.succ :=
      closure_minimal (Set.image_subset_iff.mpr hZ_hi) (hcX_irrcl i.succ).2
    have hZ : Subtype.val ⁻¹' ZX = Z := preimage_val_closure_image_val hZ_cl
    exact (hcX_maximal i ZX hZX_irr isClosed_closure hZX_lo hZX_hi).imp
      (fun h => by rw [← hZ, h]) fun h => by rw [← hZ, h]

/-- Pushing a maximal chain forward from an open subspace: the closures in `X` of the members
of a maximal chain of irreducible closed subsets of an open `V ⊆ X` form a maximal chain of
irreducible closed subsets of `X`. -/
lemma isMaximalIrreducibleClosedChain_closure_image_val
    {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    {V : Set X} (hV : IsOpen V) {m : ℕ}
    {c : Fin (m + 1) → Set V} (hc_max : IsMaximalIrreducibleClosedChain c) :
    IsMaximalIrreducibleClosedChain (fun i => closure (Subtype.val '' c i)) := by
  obtain ⟨hc_mono, hc_irrcl, hc_maximal⟩ := hc_max
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simp only
    have hci_lt_cj := hc_mono hij
    refine Set.ssubset_iff_subset_ne.mpr
      ⟨closure_mono (Set.image_mono hci_lt_cj.le), fun heq => hci_lt_cj.ne ?_⟩
    rw [← preimage_val_closure_image_val (hc_irrcl i).2, heq,
      preimage_val_closure_image_val (hc_irrcl j).2]
  · exact fun i =>
      ⟨((hc_irrcl i).1.image Subtype.val continuous_subtype_val.continuousOn).closure,
        isClosed_closure⟩
  · intro i Z hZ_irr hZ_cl hZ_lo hZ_hi
    simp only at hZ_lo hZ_hi ⊢
    obtain ⟨g, hg⟩ := QuasiSober.sober hZ_irr hZ_cl
    have hclosure_g : closure ({g} : Set X) = Z := isGenericPoint_def.mp hg
    obtain ⟨v, hv⟩ := (hc_irrcl i.castSucc).1.nonempty
    have hg_in_V : g ∈ V :=
      (hg.specializes_iff_mem.mpr (hZ_lo (subset_closure ⟨v, hv, rfl⟩))).mem_open hV v.2
    set ZV : Set V := (Subtype.val : V → X) ⁻¹' Z with hZV_def
    have hZ_cl_V : IsClosed ZV := hZ_cl.preimage continuous_subtype_val
    have hZ_irr_V : IsIrreducible ZV := by
      rw [hZV_def, ← hclosure_g]
      exact isIrreducible_preimage_val_closure_singleton hg_in_V
    have hlo : c i.castSucc ⊆ ZV := fun x hx => hZ_lo (subset_closure ⟨x, hx, rfl⟩)
    have hhi : ZV ⊆ c i.succ := by
      rw [← preimage_val_closure_image_val (hc_irrcl i.succ).2]
      exact Set.preimage_mono hZ_hi
    have hZ_recover : closure (Subtype.val '' ZV) = Z :=
      Set.Subset.antisymm (closure_minimal (fun x ⟨⟨y, _⟩, hy, hyx⟩ => hyx ▸ hy) hZ_cl)
        ((hg.mem_closed_set_iff isClosed_closure).mp
          (subset_closure ⟨⟨g, hg_in_V⟩, (hg.mem : g ∈ Z), rfl⟩))
    exact (hc_maximal i ZV hZ_irr_V hZ_cl_V hlo hhi).imp
      (fun h => by rw [← hZ_recover, h]) fun h => by rw [← hZ_recover, h]

/-- An open subspace of a sober catenary space is catenary. -/
lemma isTopologicallyCatenary_of_isOpen
    {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    (hCat : IsTopologicallyCatenary X)
    (V : Set X) (hV : IsOpen V) :
    IsTopologicallyCatenary V := by
  intro T T' hT_irr hT_cl hT'_irr hT'_cl hTT'
  have hcT_irr : IsIrreducible (closure (Subtype.val '' T) : Set X) :=
    (hT_irr.image Subtype.val continuous_subtype_val.continuousOn).closure
  have hcT'_irr : IsIrreducible (closure (Subtype.val '' T') : Set X) :=
    (hT'_irr.image Subtype.val continuous_subtype_val.continuousOn).closure
  have hcTT' : closure (Subtype.val '' T) ⊆ closure (Subtype.val '' T') :=
    closure_mono (Set.image_mono hTT')
  obtain ⟨n, ⟨cX, hcX0, hcXn, hcX_max⟩, hcX_unique⟩ :=
    hCat hcT_irr isClosed_closure hcT'_irr isClosed_closure hcTT'
  refine ⟨n, ?_, ?_⟩
  · exact exists_maximalIrreducibleClosedChain_preimage_val hV hT_irr hT_cl hT'_cl
      hcX0 hcXn hcX_max
  · intro m c hc0 hcm hc_max
    have hc_X_chain : IsMaximalIrreducibleClosedChain (fun i => closure (Subtype.val '' c i)) :=
      isMaximalIrreducibleClosedChain_closure_image_val hV hc_max
    have hc_start : (fun i => closure (Subtype.val '' c i)) 0 = closure (Subtype.val '' T) := by
      simp [hc0]
    have hc_end : (fun i => closure (Subtype.val '' c i)) (Fin.last m) =
        closure (Subtype.val '' T') := by
      simp [hcm]
    exact hcX_unique m _ hc_start hc_end hc_X_chain

/-- The *codimension* of an irreducible closed set `T` inside an irreducible closed set
`T' ⊇ T` of a catenary space: the common length of every maximal chain of irreducible closed
sets from `T` to `T'`. -/
noncomputable def codim {X : Type*} [TopologicalSpace X]
    (hCat : IsTopologicallyCatenary X)
    (T T' : Set X) (hT : IsIrreducible T) (hcT : IsClosed T)
    (hT' : IsIrreducible T') (hcT' : IsClosed T') (hsub : T ⊆ T') : ℕ :=
  (hCat hT hcT hT' hcT' hsub).choose

/-- The defining property of `codim`: some maximal chain from `T` to `T'` has length
`codim hCat T T' …`, and every maximal chain from `T` to `T'` has that length. -/
lemma codim_spec {X : Type*} [TopologicalSpace X]
    (hCat : IsTopologicallyCatenary X)
    (T T' : Set X) (hT : IsIrreducible T) (hcT : IsClosed T)
    (hT' : IsIrreducible T') (hcT' : IsClosed T') (hsub : T ⊆ T') :
    (∃ c : Fin (codim hCat T T' hT hcT hT' hcT' hsub + 1) → Set X,
        c 0 = T ∧ c (Fin.last _) = T' ∧ IsMaximalIrreducibleClosedChain c) ∧
    (∀ (m : ℕ) (c : Fin (m + 1) → Set X),
        c 0 = T → c (Fin.last m) = T' → IsMaximalIrreducibleClosedChain c →
        m = codim hCat T T' hT hcT hT' hcT' hsub) := by
  exact (hCat hT hcT hT' hcT' hsub).choose_spec

/-- Codimension is additive along `T ⊆ T' ⊆ T''` of irreducible closed sets:
`codim T T'' = codim T T' + codim T' T''`. -/
lemma codim_add {X : Type*} [TopologicalSpace X]
    (hCat : IsTopologicallyCatenary X)
    {T T' T'' : Set X}
    (hT : IsIrreducible T) (hcT : IsClosed T)
    (hT' : IsIrreducible T') (hcT' : IsClosed T')
    (hT'' : IsIrreducible T'') (hcT'' : IsClosed T'')
    (h1 : T ⊆ T') (h2 : T' ⊆ T'') :
    codim hCat T T'' hT hcT hT'' hcT'' (h1.trans h2) =
      codim hCat T T' hT hcT hT' hcT' h1 +
      codim hCat T' T'' hT' hcT' hT'' hcT'' h2 := by
  set n := codim hCat T T' hT hcT hT' hcT' h1
  set m := codim hCat T' T'' hT' hcT' hT'' hcT'' h2
  obtain ⟨⟨c₁, hc₁_start, hc₁_end, hc₁_mono, hc₁_irrcl, hc₁_maximal⟩, _⟩ :=
    codim_spec hCat T T' hT hcT hT' hcT' h1
  obtain ⟨⟨c₂, hc₂_start, hc₂_end, hc₂_mono, hc₂_irrcl, hc₂_maximal⟩, _⟩ :=
    codim_spec hCat T' T'' hT' hcT' hT'' hcT'' h2
  obtain ⟨_, huniq⟩ := codim_spec hCat T T'' hT hcT hT'' hcT'' (h1.trans h2)
  have hjoin : c₁ (Fin.last n) = c₂ 0 := by rw [hc₁_end, hc₂_start]
  suffices h : ∃ c : Fin (n + m + 1) → Set X,
      c 0 = T ∧ c (Fin.last (n + m)) = T'' ∧ IsMaximalIrreducibleClosedChain c by
    obtain ⟨c, hc0, hcn, hcmax⟩ := h
    have := huniq (n + m) c hc0 hcn hcmax; omega
  refine ⟨fun i => if h : i.val ≤ n then c₁ ⟨i.val, by omega⟩ else c₂ ⟨i.val - n, by omega⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [show (0 : Fin (n + m + 1)).val = 0 from rfl,
      show (0 : ℕ) ≤ n from Nat.zero_le n, ↓reduceDIte]
    exact hc₁_start
  · simp only [Fin.val_last]
    split_ifs with h
    · have hm0 : m = 0 := by omega
      have : (⟨n + m, by omega⟩ : Fin (n+1)) = Fin.last n :=
        Fin.ext (by simp only [Fin.val_last, Nat.add_eq_left]; omega)
      have h0last : (0 : Fin (m + 1)) = Fin.last m := by ext; simp [Fin.val_last]; omega
      rw [this, hc₁_end, ← hc₂_start, h0last, hc₂_end]
    · have : (⟨n + m - n, by omega⟩ : Fin (m+1)) = Fin.last m :=
        Fin.ext (by simp [Fin.val_last])
      rw [this]; exact hc₂_end
  · intro a b hab
    simp only
    have hab_val : a.val < b.val := hab
    split_ifs with h1 h2 h2
    · exact hc₁_mono (show (⟨a.val, _⟩ : Fin (n+1)) < ⟨b.val, _⟩ from hab_val)
    · rcases Nat.lt_or_eq_of_le h1 with ha_lt | ha_eq
      · calc c₁ ⟨a.val, _⟩ < c₁ (Fin.last n) :=
              hc₁_mono (show (⟨a.val, _⟩ : Fin (n+1)) < Fin.last n from by
                rw [Fin.lt_def, Fin.val_last]; exact ha_lt)
            _ = c₂ 0 := hjoin
            _ ≤ c₂ ⟨b.val - n, _⟩ := by
              have hbn : 0 < b.val - n := by omega
              exact le_of_lt (hc₂_mono (show (0 : Fin (m+1)) < ⟨b.val - n, _⟩ from by
                rw [Fin.lt_def, Fin.val_zero]; exact hbn))
      · have heq : (⟨a.val, by omega⟩ : Fin (n+1)) = Fin.last n :=
          Fin.ext (by simp only [Fin.val_last]; exact ha_eq)
        rw [heq, hjoin]
        exact hc₂_mono (show (0 : Fin (m+1)) < ⟨b.val - n, _⟩ from by
          rw [Fin.lt_def, Fin.val_zero, Fin.val_mk]; omega)
    · omega
    · exact hc₂_mono (show (⟨a.val - n, _⟩ : Fin (m+1)) < ⟨b.val - n, _⟩ from
        Fin.mk_lt_mk.mpr (by omega))
  · intro i; dsimp only; split_ifs <;> [exact hc₁_irrcl _; exact hc₂_irrcl _]
  · intro ⟨i, hi⟩ Z hZ_irr hZ_cl hZ_lo hZ_hi
    simp only at hZ_lo hZ_hi ⊢
    have hcs_val : (⟨i, hi⟩ : Fin (n+m)).castSucc.val = i := rfl
    have hsu_val : (⟨i, hi⟩ : Fin (n+m)).succ.val = i + 1 := rfl
    by_cases h1 : i + 1 ≤ n
    · have hlo_le : (⟨i, hi⟩ : Fin (n+m)).castSucc.val ≤ n := by rw [hcs_val]; omega
      have hhi_le : (⟨i, hi⟩ : Fin (n+m)).succ.val ≤ n := by rw [hsu_val]; exact h1
      simp only [hlo_le, hhi_le, ↓reduceDIte] at hZ_lo hZ_hi ⊢
      have h_cs : (⟨(⟨i, hi⟩ : Fin (n+m)).castSucc.val, by omega⟩ : Fin (n+1)) =
          (⟨i, by omega⟩ : Fin n).castSucc := Fin.ext (by simp [])
      have h_su : (⟨(⟨i, hi⟩ : Fin (n+m)).succ.val, by omega⟩ : Fin (n+1)) =
          (⟨i, by omega⟩ : Fin n).succ := Fin.ext (by simp [])
      rcases hc₁_maximal ⟨i, by omega⟩ Z hZ_irr hZ_cl (h_cs ▸ hZ_lo) (h_su ▸ hZ_hi) with h | h
      · left; exact h_cs ▸ h
      · right; exact h_su ▸ h
    · by_cases h2 : i ≤ n
      · have hi_eq : i = n := by omega
        have hlo_le : (⟨i, hi⟩ : Fin (n+m)).castSucc.val ≤ n := by rw [hcs_val]; exact h2
        have hhi_nle : ¬ (⟨i, hi⟩ : Fin (n+m)).succ.val ≤ n := by rw [hsu_val]; omega
        simp only [hlo_le, hhi_nle, ↓reduceDIte] at hZ_lo hZ_hi ⊢
        have h_c1_eq : (⟨(⟨i, hi⟩ : Fin (n+m)).castSucc.val, by omega⟩ : Fin (n+1)) = Fin.last n :=
          Fin.ext (by simp only [Fin.castSucc_mk, Fin.val_last]; exact hi_eq)
        have h_c2_eq : (⟨(⟨i, hi⟩ : Fin (n+m)).succ.val - n, by omega⟩ : Fin (m+1)) = ⟨1, by
            omega⟩ :=
          Fin.ext (by dsimp only [Fin.succ_mk]; omega)
        have hm_pos : 0 < m := by omega
        have hZ_lo' : c₂ (⟨0, hm_pos⟩ : Fin m).castSucc ⊆ Z := by
          have hcast : (⟨0, hm_pos⟩ : Fin m).castSucc = (0 : Fin (m+1)) := Fin.ext rfl
          rw [hcast, ← hjoin, ← h_c1_eq]; exact hZ_lo
        have hZ_hi' : Z ⊆ c₂ (⟨0, hm_pos⟩ : Fin m).succ := by
          have hsucc : (⟨0, hm_pos⟩ : Fin m).succ = (⟨1, by omega⟩ : Fin (m+1)) := Fin.ext rfl
          rw [hsucc, ← h_c2_eq]; exact hZ_hi
        rcases hc₂_maximal ⟨0, hm_pos⟩ Z hZ_irr hZ_cl hZ_lo' hZ_hi' with h | h
        · left
          have hcast : (⟨0, hm_pos⟩ : Fin m).castSucc = (0 : Fin (m+1)) := Fin.ext rfl
          rw [h, hcast, ← hjoin, ← h_c1_eq]
        · right
          have hsucc : (⟨0, hm_pos⟩ : Fin m).succ = (⟨1, by omega⟩ : Fin (m+1)) := Fin.ext rfl
          rw [h, hsucc, ← h_c2_eq]
      · have hlo_nle : ¬ (⟨i, hi⟩ : Fin (n+m)).castSucc.val ≤ n := by rw [hcs_val]; omega
        have hhi_nle : ¬ (⟨i, hi⟩ : Fin (n+m)).succ.val ≤ n := by rw [hsu_val]; omega
        simp only [hlo_nle, hhi_nle, ↓reduceDIte] at hZ_lo hZ_hi ⊢
        have hfin_idx : i - n < m := by omega
        have h_cs : (⟨(⟨i, hi⟩ : Fin (n+m)).castSucc.val - n, by omega⟩ : Fin (m+1)) =
            (⟨i - n, hfin_idx⟩ : Fin m).castSucc := Fin.ext (by simp [])
        have h_su : (⟨(⟨i, hi⟩ : Fin (n+m)).succ.val - n, by omega⟩ : Fin (m+1)) =
            (⟨i - n, hfin_idx⟩ : Fin m).succ := Fin.ext (by dsimp only [Fin.succ_mk]; omega)
        rcases hc₂_maximal ⟨i - n, hfin_idx⟩ Z hZ_irr hZ_cl (h_cs ▸ hZ_lo) (h_su ▸ hZ_hi) with h | h
        · left; exact h_cs ▸ h
        · right; exact h_su ▸ h

/-- A strict inclusion `T ⊊ T'` of irreducible closed sets has positive codimension. -/
lemma codim_pos_of_ssubset {X : Type*} [TopologicalSpace X]
    (hCat : IsTopologicallyCatenary X)
    {T T' : Set X}
    (hT : IsIrreducible T) (hcT : IsClosed T)
    (hT' : IsIrreducible T') (hcT' : IsClosed T')
    (hsub : T ⊆ T') (hne : T ≠ T') :
    0 < codim hCat T T' hT hcT hT' hcT' hsub := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  obtain ⟨⟨c, hc0, hcn, _⟩, _⟩ := codim_spec hCat T T' hT hcT hT' hcT' hsub
  have : Fin.last (codim hCat T T' hT hcT hT' hcT' hsub) = (0 : Fin (codim hCat T T' hT hcT hT'
      hcT' hsub + 1)) := by
    simp [Fin.ext_iff, Fin.val_last, h0]
  rw [this] at hcn
  exact hne (hc0.symm.trans hcn)

/-- In a sober catenary space, if `p ⤳ q` is an immediate specialization then `closure {q}`
has codimension one in `closure {p}`. -/
lemma codim_eq_one_of_isImmediateSpecialization {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X]
    (hCat : IsTopologicallyCatenary X)
    {p q : X} (himm : IsImmediateSpecialization p q) :
    codim hCat (closure {q}) (closure {p})
      (isIrreducible_singleton.closure) (isClosed_closure)
      (isIrreducible_singleton.closure) (isClosed_closure)
      (Specializes.closure_subset himm.1) = 1 := by
  obtain ⟨hspec, hne, himm_between⟩ := himm
  obtain ⟨_, huniq⟩ := codim_spec hCat (closure {q}) (closure {p})
    isIrreducible_singleton.closure isClosed_closure
    isIrreducible_singleton.closure isClosed_closure
    (Specializes.closure_subset hspec)
  let c : Fin 2 → Set X := ![closure {q}, closure {p}]
  suffices h : IsMaximalIrreducibleClosedChain c by
    have hc0 : c 0 = closure {q} := by simp [c, Matrix.cons_val_zero]
    have hc1 : c (Fin.last 1) = closure {p} := by
      simp [c, Fin.last, Matrix.cons_val_one]
    exact (huniq 1 c hc0 hc1 h).symm
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    have hij_val : i < j := hij
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 1 := by omega
    simp only [c, show (⟨0, hi⟩ : Fin 2) = 0 from rfl, show (⟨1, hj⟩ : Fin 2) = 1 from rfl]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Set.ssubset_iff_subset_ne.mpr
      ⟨Specializes.closure_subset hspec,
       fun heq => hne (inseparable_iff_closure_eq.mpr heq.symm).eq⟩
  · intro ⟨i, hi⟩
    have : i < 2 := hi
    interval_cases i <;> exact ⟨isIrreducible_singleton.closure, isClosed_closure⟩
  · intro ⟨i, hi⟩ Z hZ_irr hZ_cl hZ_lo hZ_hi
    have hi0 : i = 0 := by omega
    subst hi0
    have hc0_val : c (Fin.castSucc ⟨0, hi⟩) = closure {q} := by
      simp [c, Fin.castSucc, Matrix.cons_val_zero]
    have hc1_val : c (Fin.succ ⟨0, hi⟩) = closure {p} := by
      simp [c, Fin.succ, Matrix.cons_val_one]
    rw [hc0_val] at hZ_lo ⊢
    rw [hc1_val] at hZ_hi ⊢
    obtain ⟨z, hz⟩ := QuasiSober.sober hZ_irr hZ_cl
    have hpz : p ⤳ z := specializes_iff_mem_closure.mpr (hZ_hi hz.mem)
    have hzq : z ⤳ q := hz.specializes_iff_mem.mpr (hZ_lo (subset_closure (Set.mem_singleton q)))
    rcases himm_between z hpz hzq with rfl | rfl
    · exact .inr hz.def.symm
    · exact .inl hz.def.symm

/-- An immediate specialization in an open subspace `U ⊆ X` is an immediate specialization in
`X`. -/
lemma isImmediateSpecialization_val_of_isOpen {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {p q : U}
    (himm : IsImmediateSpecialization p q) :
    IsImmediateSpecialization (p : X) (q : X) := by
  obtain ⟨hspec, hne, himm_no_between⟩ := himm
  refine ⟨(subtype_specializes_iff p q).mp hspec, fun h => hne (Subtype.val_injective h),
    fun z hpz hzq => ?_⟩
  have hz_mem : z ∈ U := hzq.mem_open hU q.2
  exact (himm_no_between ⟨z, hz_mem⟩ ((subtype_specializes_iff p _).mpr hpz)
    ((subtype_specializes_iff _ q).mpr hzq)).imp (congrArg Subtype.val) (congrArg Subtype.val)

/-- In a Noetherian space, every point `x` has an open neighbourhood `W` such that every point
of `W` lies in an irreducible component containing `x`, and every point `p ∈ W` lying in two
irreducible components `C₁`, `C₂` through `x` lies in an irreducible closed `D ⊆ C₁ ∩ C₂`
containing `x`. -/
lemma exists_overlap_controlled_open
    (X : Type*) [TopologicalSpace X] [NoetherianSpace X]
    (x : X) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      (∀ p ∈ W, ∃ C ∈ irreducibleComponents X, x ∈ C ∧ p ∈ C) ∧
      (∀ (C₁ C₂ : Set X), C₁ ∈ irreducibleComponents X → C₂ ∈ irreducibleComponents X →
        x ∈ C₁ → x ∈ C₂ → ∀ p ∈ W, p ∈ C₁ → p ∈ C₂ →
          ∃ D : Set X, IsIrreducible D ∧ IsClosed D ∧ D ⊆ C₁ ∧ D ⊆ C₂ ∧ x ∈ D ∧ p ∈ D) := by
  classical
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have bad_pair : ∀ C₁ C₂ : Set X, C₁ ∈ irreducibleComponents X → C₂ ∈ irreducibleComponents X →
    x ∈ C₁ → x ∈ C₂ →
    ∃ bad₁₂ : Set X, IsClosed bad₁₂ ∧ x ∉ bad₁₂ ∧
      ∀ p ∈ C₁ ∩ C₂, p ∉ bad₁₂ →
        ∃ D : Set X, IsIrreducible D ∧ IsClosed D ∧ D ⊆ C₁ ∧ D ⊆ C₂ ∧ x ∈ D ∧ p ∈ D := by
    intro C₁ C₂ hC₁ hC₂ hxC₁ hxC₂
    have hinter_closed : IsClosed (C₁ ∩ C₂) :=
      (isClosed_of_mem_irreducibleComponents C₁ hC₁).inter (isClosed_of_mem_irreducibleComponents
          C₂ hC₂)
    have hx_inter : x ∈ C₁ ∩ C₂ := ⟨hxC₁, hxC₂⟩
    let x' : ↥(C₁ ∩ C₂) := ⟨x, hx_inter⟩
    set bad_comps := {D ∈ irreducibleComponents (↥(C₁ ∩ C₂)) | x' ∉ D}
    have hbad_comps_fin : bad_comps.Finite :=
      (NoetherianSpace.finite_irreducibleComponents).subset (fun D hD => hD.1)
    refine ⟨⋃ D ∈ bad_comps, (Subtype.val '' D : Set X), ?_, ?_, ?_⟩
    · apply hbad_comps_fin.isClosed_biUnion
      intro D hD
      exact hinter_closed.isClosedEmbedding_subtypeVal.isClosedMap D
        (isClosed_of_mem_irreducibleComponents D hD.1)
    · intro hx_bad
      obtain ⟨D, hD_mem, y, hy_D, hy_eq⟩ := Set.mem_iUnion₂.mp hx_bad
      exact hD_mem.2 ((Subtype.ext hy_eq : y = x') ▸ hy_D)
    · intro p hp hp_not_bad
      let p' : ↥(C₁ ∩ C₂) := ⟨p, hp⟩
      have hp'_in : p' ∈ irreducibleComponent p' := mem_irreducibleComponent
      have hcomp : irreducibleComponent p' ∈ irreducibleComponents (↥(C₁ ∩ C₂)) :=
        irreducibleComponent_mem_irreducibleComponents p'
      have hx'_Dp : x' ∈ irreducibleComponent p' := by
        by_contra h
        exact hp_not_bad (Set.mem_iUnion₂.mpr
          ⟨irreducibleComponent p', ⟨hcomp, h⟩, Set.mem_image_of_mem Subtype.val hp'_in⟩)
      refine ⟨Subtype.val '' (irreducibleComponent p'), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (hcomp.1).image Subtype.val continuous_subtype_val.continuousOn
      · exact hinter_closed.isClosedEmbedding_subtypeVal.isClosedMap _
          (isClosed_of_mem_irreducibleComponents _ hcomp)
      · rintro _ ⟨⟨z', hz'⟩, _, rfl⟩
        exact hz'.1
      · rintro _ ⟨⟨z', hz'⟩, _, rfl⟩
        exact hz'.2
      · exact Set.mem_image_of_mem Subtype.val hx'_Dp
      · exact Set.mem_image_of_mem Subtype.val hp'_in
  set bad1 : Set X := ⋃ C ∈ {C ∈ irreducibleComponents X | x ∉ C}, C
  have hbad1_closed : IsClosed bad1 :=
    (hfin.subset (fun C (hC : C ∈ {C ∈ irreducibleComponents X | x ∉ C}) => hC.1)).isClosed_biUnion
      (fun C hC => isClosed_of_mem_irreducibleComponents C hC.1)
  have hx_not_bad1 : x ∉ bad1 := fun h => by
    obtain ⟨C, ⟨_, hxC⟩, hx_C⟩ := Set.mem_iUnion₂.mp h
    exact hxC hx_C
  let bad_for_pair : Set X × Set X → Set X := fun ⟨C₁, C₂⟩ =>
    if h : C₁ ∈ irreducibleComponents X ∧ C₂ ∈ irreducibleComponents X ∧ x ∈ C₁ ∧ x ∈ C₂ then
      (bad_pair C₁ C₂ h.1 h.2.1 h.2.2.1 h.2.2.2).choose
    else ∅
  have hbad_for_pair_closed : ∀ p : Set X × Set X, IsClosed (bad_for_pair p) := by
    intro ⟨C₁, C₂⟩
    simp only [bad_for_pair]
    split
    next h => exact ((bad_pair C₁ C₂ h.1 h.2.1 h.2.2.1 h.2.2.2).choose_spec).1
    next => exact isClosed_empty
  have hx_not_bad_for_pair : ∀ p : Set X × Set X, x ∉ bad_for_pair p := by
    intro ⟨C₁, C₂⟩
    simp only [bad_for_pair]
    split
    next h => exact ((bad_pair C₁ C₂ h.1 h.2.1 h.2.2.1 h.2.2.2).choose_spec).2.1
    next => exact fun h => h
  have hbad_for_pair_prop : ∀ (C₁ C₂ : Set X), C₁ ∈ irreducibleComponents X →
    C₂ ∈ irreducibleComponents X → x ∈ C₁ → x ∈ C₂ →
    ∀ p ∈ C₁ ∩ C₂, p ∉ bad_for_pair (C₁, C₂) →
      ∃ D : Set X, IsIrreducible D ∧ IsClosed D ∧ D ⊆ C₁ ∧ D ⊆ C₂ ∧ x ∈ D ∧ p ∈ D := by
    intro C₁ C₂ hC₁ hC₂ hxC₁ hxC₂ p hp hnp
    have : bad_for_pair (C₁, C₂) = (bad_pair C₁ C₂ hC₁ hC₂ hxC₁ hxC₂).choose := by
      simp only [bad_for_pair]
      exact dite_eq_left ⟨hC₁, hC₂, hxC₁, hxC₂⟩
    exact ((bad_pair C₁ C₂ hC₁ hC₂ hxC₁ hxC₂).choose_spec).2.2 p hp (by rwa [this] at hnp)
  set bad2 : Set X := ⋃ p ∈ (hfin.toFinset ×ˢ hfin.toFinset), bad_for_pair p
  have hbad2_closed : IsClosed bad2 :=
    (Finset.finite_toSet _).isClosed_biUnion fun p _ => hbad_for_pair_closed p
  have hx_not_bad2 : x ∉ bad2 := fun h => by
    obtain ⟨p, _, hp⟩ := Set.mem_iUnion₂.mp h
    exact hx_not_bad_for_pair p hp
  refine ⟨(bad1 ∪ bad2)ᶜ, ?_, ?_, ?_, ?_⟩
  · exact (hbad1_closed.union hbad2_closed).isOpen_compl
  · exact fun h => h.elim hx_not_bad1 hx_not_bad2
  · intro p hp
    refine ⟨irreducibleComponent p, irreducibleComponent_mem_irreducibleComponents p, ?_,
        mem_irreducibleComponent⟩
    by_contra hxC
    exact hp (Set.mem_union_left _ (Set.mem_iUnion₂.mpr ⟨irreducibleComponent p,
      ⟨irreducibleComponent_mem_irreducibleComponents p, hxC⟩, mem_irreducibleComponent⟩))
  · intro C₁ C₂ hC₁ hC₂ hxC₁ hxC₂ p hp hpC₁ hpC₂
    exact hbad_for_pair_prop C₁ C₂ hC₁ hC₂ hxC₁ hxC₂ p ⟨hpC₁, hpC₂⟩ fun h =>
      hp (Set.mem_union_right _ (Set.mem_iUnion₂.mpr ⟨(C₁, C₂),
        Finset.mk_mem_product (hfin.mem_toFinset.mpr hC₁) (hfin.mem_toFinset.mpr hC₂), h⟩))

/-- If `x` and `p` lie in irreducible closed sets `C₁` and `C₂`, and some irreducible closed
`D ⊆ C₁ ∩ C₂` contains both `x` and `p`, then `codim (closure {p}) C₁ - codim (closure {x}) C₁`
equals `codim (closure {p}) C₂ - codim (closure {x}) C₂`. -/
lemma codim_sub_codim_eq_of_common_subset
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] [T0Space X]
    (hCat : IsTopologicallyCatenary X)
    (x : X) (C₁ C₂ : Set X)
    (hC₁_irr : IsIrreducible C₁) (hC₁_cl : IsClosed C₁)
    (hC₂_irr : IsIrreducible C₂) (hC₂_cl : IsClosed C₂)
    (hx_C₁ : x ∈ C₁) (hx_C₂ : x ∈ C₂)
    (p : X) (hp_C₁ : p ∈ C₁) (hp_C₂ : p ∈ C₂)
    (D : Set X) (hD_irr : IsIrreducible D) (hD_cl : IsClosed D)
    (hD_C₁ : D ⊆ C₁) (hD_C₂ : D ⊆ C₂) (hx_D : x ∈ D) (hp_D : p ∈ D) :
    (codim hCat (closure {p}) C₁
      isIrreducible_singleton.closure isClosed_closure hC₁_irr hC₁_cl
      (closure_minimal (Set.singleton_subset_iff.mpr hp_C₁) hC₁_cl) : ℤ) -
    (codim hCat (closure {x}) C₁
      isIrreducible_singleton.closure isClosed_closure hC₁_irr hC₁_cl
      (closure_minimal (Set.singleton_subset_iff.mpr hx_C₁) hC₁_cl) : ℤ) =
    (codim hCat (closure {p}) C₂
      isIrreducible_singleton.closure isClosed_closure hC₂_irr hC₂_cl
      (closure_minimal (Set.singleton_subset_iff.mpr hp_C₂) hC₂_cl) : ℤ) -
    (codim hCat (closure {x}) C₂
      isIrreducible_singleton.closure isClosed_closure hC₂_irr hC₂_cl
      (closure_minimal (Set.singleton_subset_iff.mpr hx_C₂) hC₂_cl) : ℤ) := by
  have hp_D_C₁ := codim_add hCat isIrreducible_singleton.closure isClosed_closure
    hD_irr hD_cl hC₁_irr hC₁_cl
    (closure_minimal (Set.singleton_subset_iff.mpr hp_D) hD_cl) hD_C₁
  have hx_D_C₁ := codim_add hCat isIrreducible_singleton.closure isClosed_closure
    hD_irr hD_cl hC₁_irr hC₁_cl
    (closure_minimal (Set.singleton_subset_iff.mpr hx_D) hD_cl) hD_C₁
  have hp_D_C₂ := codim_add hCat isIrreducible_singleton.closure isClosed_closure
    hD_irr hD_cl hC₂_irr hC₂_cl
    (closure_minimal (Set.singleton_subset_iff.mpr hp_D) hD_cl) hD_C₂
  have hx_D_C₂ := codim_add hCat isIrreducible_singleton.closure isClosed_closure
    hD_irr hD_cl hC₂_irr hC₂_cl
    (closure_minimal (Set.singleton_subset_iff.mpr hx_D) hD_cl) hD_C₂
  simp only [hp_D_C₁, hx_D_C₁, hp_D_C₂, hx_D_C₂, Nat.cast_add]
  omega

/-- An overlap-controlled open set `W` in a Noetherian sober catenary space carries a dimension
function, namely `δ p = codim (closure {x}) C - codim (closure {p}) C` for any irreducible
component `C` containing both `x` and `p`. -/
@[sga "6 X 1.6" "special case"]
lemma nonempty_dimensionFunction_of_overlap_controlled
    (X : Type*) [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] [T0Space X]
    (hCat : IsTopologicallyCatenary X)
    (x : X) (W : Set X) (hW_open : IsOpen W)
    (hW_covered : ∀ p ∈ W, ∃ C ∈ irreducibleComponents X, x ∈ C ∧ p ∈ C)
    (hW_overlap : ∀ (C₁ C₂ : Set X), C₁ ∈ irreducibleComponents X → C₂ ∈ irreducibleComponents X →
        x ∈ C₁ → x ∈ C₂ → ∀ p ∈ W, p ∈ C₁ → p ∈ C₂ →
          ∃ D : Set X, IsIrreducible D ∧ IsClosed D ∧ D ⊆ C₁ ∧ D ⊆ C₂ ∧ x ∈ D ∧ p ∈ D) :
    Nonempty (DimensionFunction W) := by
  classical
  have choose_comp : ∀ (p : W), ∃ C : Set X, C ∈ irreducibleComponents X ∧ x ∈ C ∧ (p : X) ∈ C :=
    fun p => hW_covered p p.2
  let C_of : W → Set X := fun p => (choose_comp p).choose
  have hC_of_spec : ∀ p : W, C_of p ∈ irreducibleComponents X ∧ x ∈ C_of p ∧ (p : X) ∈ C_of p :=
    fun p => (choose_comp p).choose_spec
  have hC_of_mem : ∀ p : W, C_of p ∈ irreducibleComponents X := fun p => (hC_of_spec p).1
  have hC_of_x : ∀ p : W, x ∈ C_of p := fun p => (hC_of_spec p).2.1
  have hC_of_p : ∀ p : W, (p : X) ∈ C_of p := fun p => (hC_of_spec p).2.2
  have hC_irr : ∀ p : W, IsIrreducible (C_of p) := fun p => (hC_of_mem p).1
  have hC_cl : ∀ p : W, IsClosed (C_of p) :=
    fun p => isClosed_of_mem_irreducibleComponents _ (hC_of_mem p)
  let δ : W → ℤ := fun p =>
    (codim hCat (closure {x}) (C_of p)
      isIrreducible_singleton.closure isClosed_closure (hC_irr p) (hC_cl p)
      (closure_minimal (Set.singleton_subset_iff.mpr (hC_of_x p)) (hC_cl p)) : ℤ) -
    (codim hCat (closure {(p : X)}) (C_of p)
      isIrreducible_singleton.closure isClosed_closure (hC_irr p) (hC_cl p)
      (closure_minimal (Set.singleton_subset_iff.mpr (hC_of_p p)) (hC_cl p)) : ℤ)
  have δ_eq : ∀ (p : W) (C : Set X) (hCm : C ∈ irreducibleComponents X) (hxC : x ∈ C) (hpC : (p :
      X) ∈ C),
    δ p = (codim hCat (closure {x}) C
      isIrreducible_singleton.closure isClosed_closure hCm.1
      (isClosed_of_mem_irreducibleComponents _ hCm)
      (closure_minimal (Set.singleton_subset_iff.mpr hxC)
        (isClosed_of_mem_irreducibleComponents _ hCm)) : ℤ) -
    (codim hCat (closure {(p : X)}) C
      isIrreducible_singleton.closure isClosed_closure hCm.1
      (isClosed_of_mem_irreducibleComponents _ hCm)
      (closure_minimal (Set.singleton_subset_iff.mpr hpC)
        (isClosed_of_mem_irreducibleComponents _ hCm)) : ℤ) := by
    intro p C hCm hxC hpC
    obtain ⟨D, hD_irr, hD_cl, hD_Cp, hD_C, hxD, hpD⟩ :=
      hW_overlap (C_of p) C (hC_of_mem p) hCm (hC_of_x p) hxC (p : X) p.2 (hC_of_p p) hpC
    have h := codim_sub_codim_eq_of_common_subset hCat x (C_of p) C
      (hC_irr p) (hC_cl p) hCm.1 (isClosed_of_mem_irreducibleComponents _ hCm)
      (hC_of_x p) hxC (p : X) (hC_of_p p) hpC D hD_irr hD_cl hD_Cp hD_C hxD hpD
    linarith
  have δ_spec : ∀ (p q : W) (hpq : (p : X) ⤳ (q : X)), δ p = δ q +
      (codim hCat (closure {(q : X)}) (closure {(p : X)})
        isIrreducible_singleton.closure isClosed_closure
        isIrreducible_singleton.closure isClosed_closure hpq.closure_subset : ℤ) := by
    intro p q hpq
    have hq_in_Cp : (q : X) ∈ C_of p :=
      (hC_cl p).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr (hC_of_p p)) hpq.mem_closure
    have h_add := codim_add hCat
      isIrreducible_singleton.closure isClosed_closure
      isIrreducible_singleton.closure isClosed_closure
      (hC_irr p) (hC_cl p) hpq.closure_subset
      (closure_minimal (Set.singleton_subset_iff.mpr (hC_of_p p)) (hC_cl p))
    rw [δ_eq q (C_of p) (hC_of_mem p) (hC_of_x p) hq_in_Cp]
    simp only [δ]
    rw [h_add]
    push_cast
    omega
  refine ⟨⟨δ, ?strictAnti, ?stepImm⟩⟩
  case strictAnti =>
    intro p q hpq hne
    have hpq_X : (p : X) ⤳ (q : X) := (subtype_specializes_iff p q).mp hpq
    have h_pos := codim_pos_of_ssubset hCat
      isIrreducible_singleton.closure isClosed_closure
      isIrreducible_singleton.closure isClosed_closure
      hpq_X.closure_subset fun heq =>
        hne (Subtype.val_injective (inseparable_iff_closure_eq.mpr heq.symm).eq)
    rw [δ_spec p q hpq_X]
    omega
  case stepImm =>
    intro p q himm
    have himm_X := isImmediateSpecialization_val_of_isOpen hW_open himm
    rw [δ_spec p q himm_X.1, codim_eq_one_of_isImmediateSpecialization hCat himm_X]
    push_cast
    rfl

/-- In a Noetherian sober catenary space every point has an open neighbourhood carrying a
dimension function. -/
lemma exists_isOpen_nonempty_dimensionFunction
    (X : Type*) [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] [T0Space X]
    (hCat : IsTopologicallyCatenary X)
    (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Nonempty (DimensionFunction U) := by
  obtain ⟨W, hW_open, hx_W, hW_covered, hW_overlap⟩ := exists_overlap_controlled_open X x
  exact ⟨W, hW_open, hx_W,
    nonempty_dimensionFunction_of_overlap_controlled X hCat x W hW_open hW_covered hW_overlap⟩

/-- For `V : Set X` and `W : Set V`, a dimension function on `W` gives a dimension function on
`Subtype.val '' W ⊆ X`. -/
lemma nonempty_dimensionFunction_image_val {X : Type*} [TopologicalSpace X]
    (V : Set X)
    (W : Set V) (hW : Nonempty (DimensionFunction W)) :
    Nonempty (DimensionFunction (Subtype.val '' W : Set X)) := by
  obtain ⟨δ⟩ := hW
  let fwd : W → (Subtype.val '' W : Set X) :=
    fun w => ⟨(w : V).val, w, w.2, rfl⟩
  have hfwd_val : ∀ w, (fwd w : X) = ((w : V) : X) := fun _ => rfl
  have hfwd_inj : Function.Injective fwd := fun a b h => by
    have heq : ((a : V) : X) = ((b : V) : X) :=
      congr_arg (fun p : (Subtype.val '' W : Set X) => (p : X)) h
    exact Subtype.ext (Subtype.val_injective heq)
  have hfwd_surj : Function.Surjective fwd := fun ⟨x, w, hw, hweq⟩ =>
    ⟨⟨w, hw⟩, Subtype.ext hweq⟩
  let inv : (Subtype.val '' W : Set X) → W := Function.surjInv hfwd_surj
  have hinv_right : ∀ a, fwd (inv a) = a := Function.surjInv_eq hfwd_surj
  have hinv_left : ∀ z, inv (fwd z) = z := fun z => hfwd_inj (hinv_right (fwd z))
  have hinv_spec_val : ∀ a : (Subtype.val '' W : Set X), ((inv a : W) : V).val = (a : X) :=
    fun a => congrArg Subtype.val (hinv_right a)
  have hinv_inj : Function.Injective inv := Function.LeftInverse.injective hinv_right
  have hspec_iff : ∀ a b : (Subtype.val '' W : Set X), a ⤳ b ↔ inv a ⤳ inv b := fun a b => by
    rw [subtype_specializes_iff, subtype_specializes_iff, subtype_specializes_iff,
      hinv_spec_val a, hinv_spec_val b]
  exact ⟨{
    toFun := fun a => δ.toFun (inv a)
    strictAnti_specializes := fun a b hab hne =>
      δ.strictAnti_specializes ((hspec_iff a b).mp hab) fun h => hne (hinv_inj h)
    step_immediate := by
      intro a b ⟨hab_spec, hab_ne, hab_imm⟩
      apply δ.step_immediate
      refine ⟨(hspec_iff a b).mp hab_spec, fun h => hab_ne (hinv_inj h), ?_⟩
      intro z hz1 hz2
      have hfz_spec_a : a ⤳ fwd z := (hspec_iff _ _).mpr (by rwa [hinv_left])
      have hfz_spec_b : fwd z ⤳ b := (hspec_iff _ _).mpr (by rwa [hinv_left])
      exact (hab_imm (fwd z) hfz_spec_a hfz_spec_b).imp
        (fun h => (hinv_left z).symm.trans (congr_arg inv h))
        fun h => (hinv_left z).symm.trans (congr_arg inv h)
  }⟩

/-- Let `X` be a topological space that is locally Noetherian, sober (i.e. `QuasiSober` and
`T0Space`), and catenary. Then every point of `X` has an open neighbourhood `U ⊆ X` such that
the subspace `U` admits a dimension function `δ : U → ℤ`. -/
@[stacks 02IC]
theorem exists_open_nhd_with_dimension_function
    (X : Type*) [TopologicalSpace X]
    [QuasiSober X] [T0Space X]
    (hLN : IsLocallyNoetherianSpace X)
    (hCat : IsTopologicallyCatenary X)
    (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Nonempty (DimensionFunction U) := by
  obtain ⟨V, hVopen, hxV, hVnoeth⟩ := hLN x
  have hV_QS : QuasiSober V :=
    Topology.IsOpenEmbedding.quasiSober (IsOpen.isOpenEmbedding_subtypeVal hVopen)
  have hV_cat : IsTopologicallyCatenary V :=
    isTopologicallyCatenary_of_isOpen hCat V hVopen
  obtain ⟨W, hWopen, hxW, hWdim⟩ :=
    @exists_isOpen_nonempty_dimensionFunction V _ hVnoeth hV_QS inferInstance hV_cat ⟨x, hxV⟩
  exact ⟨Subtype.val '' W, hVopen.isOpenMap_subtype_val W hWopen, ⟨⟨x, hxV⟩, hxW, rfl⟩,
    nonempty_dimensionFunction_image_val V W hWdim⟩

end TopologicalSpace
