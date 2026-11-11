module

public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Limits.FilteredColimitSections

/-!
# A filtered system of sheaves whose sections miss the sections of the colimit (Stacks 009G)

Part (4) of Stacks 009F says that the canonical map
`Ψ : colimᵢ ℱᵢ(U) → (colimᵢ ℱᵢ)(U)` is bijective as soon as `U` has a cofinal system of finite
open coverings with quasi-compact pairwise intersections.  Stacks 009G shows that some such
condition is needed, even for a quasi-compact `U`.

## The example of the source

`QuasiCompactCounterexample` formalizes the example of 009G itself.  The space is
`X = {s₁, s₂, ξ₁, ξ₂, …}` (`QuasiCompactCounterexample.space`), a subset being open if it contains
all of the `ξᵢ` as soon as it contains `s₁` or `s₂`.  With `Uₙ = {ξₙ, ξₙ₊₁, …}` and
`jₙ : Uₙ → X` the inclusion, the system is `ℱₙ = jₙ,* 𝐙` with the restriction maps as transition
maps (`QuasiCompactCounterexample.sheafSystem`, a system of sheaves of sets, the setting of 009F;
`QuasiCompactCounterexample.sheafSystemObjIso` identifies `ℱₙ` with the pushforward of the sheaf
of locally constant `𝐙`-valued functions on `Uₙ`).  For `ℱ = colimₙ ℱₙ` and
`M = colimₙ ∏_{m ≥ n} 𝐙` (`QuasiCompactCounterexample.tailColimit`) we prove:

* `X` is quasi-compact (`QuasiCompactCounterexample.compactSpace_space`);
* the stalks of `ℱ` are trivial at every `ξₙ` and equal to `M` at `s₁` and `s₂`
  (`QuasiCompactCounterexample.subsingleton_stalk_ξ`, `QuasiCompactCounterexample.stalkEquiv`);
* `colimₙ Γ(X, ℱₙ) = M` and `Γ(X, ℱ) = M ⊕ M` (as sets, `M × M`), and under these
  identifications `Ψ` is the diagonal
  (`QuasiCompactCounterexample.colimitGlobalSectionsEquiv`,
  `QuasiCompactCounterexample.globalSectionsEquiv`,
  `QuasiCompactCounterexample.globalSectionsEquiv_canonicalMap`);
* `ℱ` is the direct sum of the skyscraper sheaves with value `M` at `s₁` and `s₂`
  (`QuasiCompactCounterexample.bijective_toSkyscraper`);
* hence `Ψ` on `X` is injective (as 009F (2) predicts) but not surjective.

`QuasiCompactCounterexample.compactSpace_and_canonicalMap_top_injective_not_surjective`
(`@[stacks 009G]`) states all of these together.

## A variant on a discrete space

`SectionsCounterexample` is an older, different example: the same system on the discrete space
`ℕ` (the space of the source with `s₁, s₂` removed).  That space is not quasi-compact, all stalks
of the colimit vanish while its global sections do not, so `Ψ` is not injective there
(`exists_system_canonicalMap_not_bijective`).  It does not formalize 009G: it says nothing
about a quasi-compact space or about surjectivity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

namespace DirectedColimitOfSheaves

namespace SectionsCounterexample

/-- The space of the example: the natural numbers with their (discrete) topology.  Every
subset is open, and the space is not quasi-compact. -/
abbrev space : TopCat.{0} := TopCat.of ℕ

/-- The open subset `{x}` of `space`; a singleton is open because the topology is discrete. -/
def pt (x : ℕ) : Opens space := ⟨{x}, isOpen_discrete _⟩

/-- The point `x` lies in the open set `pt x`. -/
lemma mem_pt (x : ℕ) : x ∈ pt x := rfl

/-- The only point of `pt x` is `x`. -/
lemma eq_of_mem_pt {x y : ℕ} (hy : y ∈ pt x) : y = x := hy

/-- The fibre of the `n`-th sheaf of the system at the point `x`: a copy of `𝐙` when
`n ≤ x`, and a singleton otherwise.  Writing it as a function type out of `PLift (n ≤ x)`
avoids a case distinction: the domain is a singleton when `n ≤ x` and empty otherwise. -/
def fiber (n x : ℕ) : Type := PLift (n ≤ x) → ℤ

/-- The transition map on fibres: for `n ≤ m` it is the identity of `𝐙` at the points
`x ≥ m` and the unique map to a singleton at the points `x < m`. -/
def fiberMap {n m : ℕ} (h : n ≤ m) (x : ℕ) (f : fiber n x) : fiber m x :=
  fun p => f ⟨h.trans p.down⟩

/-- The system `ℱ : ℕ ⥤ TopCat.Sheaf (Type) X` of the example.  `ℱₙ` is the sheaf of sections
of the fibre family `fiber n`, i.e. the pushforward `jₙ,*𝐙` of the constant sheaf along the
inclusion `jₙ : {m : n ≤ m} → ℕ`: its sections over `V` are the `𝐙`-valued functions on
`V ∩ {m : n ≤ m}`.  The transition map `ℱₙ → ℱₘ` for `n ≤ m` restricts a function to the
smaller set. -/
noncomputable def sheafSystem : ℕ ⥤ TopCat.Sheaf (Type) space where
  obj n := TopCat.sheafToTypes space (fiber n)
  map h := { hom := { app := fun _ => ↾fun σ x => fiberMap (leOfHom h) x (σ x) } }

/-- Sections of `ℱₙ` over an open all of whose points are `< n` form a subsingleton: the
fibres of `fiber n` at those points are singletons. -/
lemma sections_eq_of_lt (x n : ℕ) (hn : x < n)
    (σ τ : ((presheafSystem sheafSystem).obj n).obj (op (pt x))) : σ = τ := by
  refine funext fun y => funext fun p => ?_
  have hy : (y : ℕ) = x := eq_of_mem_pt y.2
  exact absurd (le_of_le_of_eq p.down hy) (by omega)

/-- The constant section of value `c` of `ℱ₀` over the whole space. -/
def constSec (c : ℤ) : ((presheafSystem sheafSystem).obj 0).obj (op ⊤) := fun _ _ => c

/-- The image of `constSec c` in `ℱ'(X) = colimₙ ℱₙ(X)`. -/
noncomputable def constSecColim (c : ℤ) : (colimitPresheaf sheafSystem).obj (op ⊤) :=
  (colimit.ι (presheafSystem sheafSystem) 0).app (op ⊤) (constSec c)

/-- Distinct constants give distinct global sections of `ℱ' = colimₙ ℱₙ`: a transition map
sends the constant sequence `c` to the constant sequence `c`, and no transition map out of `0`
identifies two different constants, because the space has points above every index. -/
lemma constSecColim_injective {c c' : ℤ} (h : constSecColim c = constSecColim c') : c = c' := by
  obtain ⟨m, g, hg⟩ :=
    (colimit_eq_iff_eventual sheafSystem ⊤ 0 (constSec c) (constSec c')).mp h
  exact congrFun (congrFun hg ⟨m, trivial⟩) ⟨le_rfl⟩

/-- All germs of the sections `constSecColim c` coincide: at a point `x` the section
restricts to a section over `{x}`, and there it becomes the unique section of `ℱₓ₊₁` over
`{x}`, since the fibre of `fiber (x + 1)` at `x` is a singleton. -/
lemma germ_constSecColim_eq (c c' : ℤ) (x : ℕ) (hx : x ∈ (⊤ : Opens space)) :
    (colimitPresheaf sheafSystem).germ ⊤ x hx (constSecColim c) =
      (colimitPresheaf sheafSystem).germ ⊤ x hx (constSecColim c') := by
  have key : ∀ d : ℤ, (colimitPresheaf sheafSystem).germ ⊤ x hx (constSecColim d) =
      (colimitPresheaf sheafSystem).germ (pt x) x (mem_pt x)
        ((colimit.ι (presheafSystem sheafSystem) 0).app (op (pt x))
          (((presheafSystem sheafSystem).obj 0).map (homOfLE (le_top (a := pt x))).op
            (constSec d))) := fun d => by
    rw [← (colimitPresheaf sheafSystem).germ_res_apply (homOfLE (le_top (a := pt x))) x
      (mem_pt x)]
    exact congrArg _ (ConcreteCategory.congr_hom
      ((colimit.ι (presheafSystem sheafSystem) 0).naturality
        (homOfLE (le_top (a := pt x))).op) (constSec d)).symm
  rw [key c, key c']
  exact congrArg _ ((colimit_eq_iff_eventual sheafSystem (pt x) 0 _ _).mpr
    ⟨x + 1, homOfLE (Nat.zero_le _), sections_eq_of_lt x (x + 1) (Nat.lt_succ_self x) _ _⟩)

/-- The canonical map of 009F identifies the global sections `constSecColim c` for all `c`:
they have the same germ at every point, and the sheafification is separated. -/
lemma canonicalMap_constSecColim_eq (c c' : ℤ) :
    canonicalMap sheafSystem ⊤ (constSecColim c) = canonicalMap sheafSystem ⊤ (constSecColim c') :=
  (canonicalMap_eq_iff sheafSystem ⊤ _ _).mpr fun x hx => germ_constSecColim_eq c c' x hx

/-- The hypothesis of 009F (4) fails for the whole space: the covering by singletons has no
finite refinement, since `ℕ` is infinite. -/
lemma not_hasFiniteCompactCofinalCovers_top :
    ¬ HasFiniteCompactCofinalCovers (X := space) ⊤ := by
  intro h
  obtain ⟨K, hK, W, -, hWcover, hWref, -⟩ :=
    h (fun j : ℕ => pt j) (fun _ => le_top) fun x _ => Opens.mem_iSup.mpr ⟨x, mem_pt x⟩
  have : Finite K := hK
  choose j hj using hWref
  have hsurj : Function.Surjective j := by
    intro x
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hWcover (Opens.mem_top x))
    exact ⟨k, (eq_of_mem_pt (hj k hk)).symm⟩
  have : Finite ℕ := Finite.of_surjective j hsurj
  exact not_finite ℕ

end SectionsCounterexample

/-- A variant of Stacks 009G on a non-quasi-compact space (not the example of the source, which
is `QuasiCompactCounterexample.compactSpace_and_canonicalMap_top_injective_not_surjective`):
there are a space `X` and a system of sheaves of sets `ℱ : ℕ ⥤ TopCat.Sheaf (Type) X` indexed
by the directed set `ℕ` for which the canonical map `Ψ : colimₙ ℱₙ(X) → (colimₙ ℱₙ)(X)` is not
bijective (in fact not injective).

The witness is `SectionsCounterexample.sheafSystem`, the pushforwards `jₙ,*𝐙` of the constant
sheaf along the inclusions of the cofinal subsets `{m : n ≤ m}` of the discrete space `ℕ`.  All
its stalks die in the colimit while its global sections do not, so `Ψ` is not injective; and
`SectionsCounterexample.not_hasFiniteCompactCofinalCovers_top` checks that the hypothesis of
009F (4) really fails here. -/
theorem exists_system_canonicalMap_not_bijective :
    ∃ (X : TopCat) (F : ℕ ⥤ TopCat.Sheaf (Type) X),
      ¬ Function.Bijective (canonicalMap F ⊤) := by
  refine ⟨SectionsCounterexample.space, SectionsCounterexample.sheafSystem, fun hbij => ?_⟩
  have h01 : (0 : ℤ) = 1 :=
    SectionsCounterexample.constSecColim_injective
      (hbij.injective (SectionsCounterexample.canonicalMap_constSecColim_eq 0 1))
  exact zero_ne_one h01

namespace QuasiCompactCounterexample

/-! ### The example of Stacks 009G

The space, the system of sheaves and the computation of the two section sets of the source. -/

/-- The points of the space of the example: two points `s i` (`i : Bool`; these are the points
`s₁, s₂` of the source) and points `ξ n` for `n : ℕ` (the points `ξ₁, ξ₂, …` of the source,
numbered from `0`). -/
inductive Point : Type
  /-- The points `s₁, s₂`. -/
  | s (i : Bool) : Point
  /-- The points `ξ₁, ξ₂, …`. -/
  | ξ (n : ℕ) : Point

/-- The topology of the example: a subset is open if it contains all of the `ξ n` as soon as it
contains `s₁` or `s₂`. -/
instance : TopologicalSpace Point where
  IsOpen V := ∀ i, Point.s i ∈ V → ∀ n, Point.ξ n ∈ V
  isOpen_univ _ _ _ := trivial
  isOpen_inter _ _ hV hW i h n := ⟨hV i h.1 n, hW i h.2 n⟩
  isOpen_sUnion S hS i h n := by
    obtain ⟨V, hVS, hV⟩ := h
    exact ⟨V, hVS, hS V hVS i hV n⟩

/-- A subset of `Point` is open if and only if it contains all of the `ξ n` whenever it
contains `s₁` or `s₂`. -/
lemma isOpen_iff {V : Set Point} : IsOpen V ↔ ∀ i, Point.s i ∈ V → ∀ n, Point.ξ n ∈ V :=
  Iff.rfl

/-- The space `X = {s₁, s₂, ξ₁, ξ₂, …}` of the example. -/
abbrev space : TopCat.{0} := TopCat.of Point

/-- If the open `V` is the smallest open neighbourhood of a point `p ∈ V`, then `V` is
quasi-compact: the member of an open covering that contains `p` already covers `V`. -/
lemma isCompact_of_forall_mem_le {V : Opens space} {p : space} (hp : p ∈ V)
    (hmin : ∀ V' : Opens space, p ∈ V' → V ≤ V') : IsCompact (V : Set space) := by
  refine isCompact_of_finite_subcover fun U hU hVU => ?_
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hVU hp)
  refine ⟨{i}, fun x hx => ?_⟩
  simpa using hmin ⟨U i, hU i⟩ hi hx

/-- If `V` is the smallest open neighbourhood of one of its points, then `V` has a cofinal system
of finite open coverings with quasi-compact pairwise intersections: every open covering of `V`
is refined by the covering `{V}`. -/
lemma hasFiniteCompactCofinalCovers_of_forall_mem_le {V : Opens space} {p : space}
    (hp : p ∈ V) (hmin : ∀ V' : Opens space, p ∈ V' → V ≤ V') :
    HasFiniteCompactCofinalCovers (X := space) V := by
  intro J W _ hcover
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcover hp)
  refine ⟨PUnit, inferInstance, fun _ => V, fun _ => le_rfl,
    fun x hx => Opens.mem_iSup.mpr ⟨PUnit.unit, hx⟩, fun _ => ⟨j, hmin _ hj⟩, fun _ _ => ?_⟩
  simpa [Opens.coe_inf] using isCompact_of_forall_mem_le hp hmin

/-- If `V` is the smallest open neighbourhood of `p`, then the germ map of any presheaf of sets
at `p` is a bijection from the sections over `V` onto the stalk at `p`. -/
lemma bijective_germ_of_forall_mem_le (G : TopCat.Presheaf (Type) space)
    {V : Opens space} {p : space} (hp : p ∈ V) (hmin : ∀ V' : Opens space, p ∈ V' → V ≤ V') :
    Function.Bijective (G.germ V p hp) := by
  refine ⟨fun s t hst => ?_, fun g => ?_⟩
  · obtain ⟨W, hW, iU, iV, h⟩ := G.germ_eq p hp hp s t hst
    obtain rfl : W = V := le_antisymm iU.le (hmin W hW)
    rwa [Subsingleton.elim iU (𝟙 W), Subsingleton.elim iV (𝟙 W), op_id, G.map_id,
      types_id_apply, types_id_apply] at h
  · obtain ⟨U, hU, s, rfl⟩ := G.exists_germ_eq g
    exact ⟨G.map (homOfLE (hmin U hU)).op s, G.germ_res_apply (homOfLE (hmin U hU)) p hp s⟩

/-- The open `{ξ m}`. -/
def pt (m : ℕ) : Opens space := ⟨{Point.ξ m}, fun _ h => Point.noConfusion h⟩

/-- The open `{s i, ξ₁, ξ₂, …}`, i.e. the complement of the other point `s (!i)`; it is the
smallest open neighbourhood of `s i`. -/
def nbhd (i : Bool) : Opens space :=
  ⟨{x | x ≠ Point.s (!i)}, fun _ _ _ h => Point.noConfusion h⟩

lemma mem_pt (m : ℕ) : Point.ξ m ∈ pt m := rfl

lemma s_mem_nbhd (i : Bool) : Point.s i ∈ nbhd i := by
  cases i <;> simp [nbhd]

lemma ξ_mem_nbhd (i : Bool) (m : ℕ) : Point.ξ m ∈ nbhd i := fun h => Point.noConfusion h

/-- `{ξ m}` is the smallest open neighbourhood of `ξ m`. -/
lemma pt_le {m : ℕ} {V : Opens space} (h : Point.ξ m ∈ V) : pt m ≤ V := by
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact h

/-- `nbhd i` is the smallest open neighbourhood of `s i`. -/
lemma nbhd_le {i : Bool} {V : Opens space} (h : Point.s i ∈ V) : nbhd i ≤ V := by
  intro x hx
  cases x with
  | s j =>
    have hji : j = i := by
      cases i <;> cases j <;> simp_all [nbhd]
    exact hji ▸ h
  | ξ n => exact V.2 i h n

/-- The two opens `nbhd i` cover the space. -/
lemma top_le_iSup_nbhd : (⊤ : Opens space) ≤ ⨆ i, nbhd i := by
  intro x _
  refine Opens.mem_iSup.mpr ?_
  cases x with
  | s i => exact ⟨i, s_mem_nbhd i⟩
  | ξ n => exact ⟨true, ξ_mem_nbhd true n⟩

/-- The space of the example is quasi-compact: it is the union of the two quasi-compact opens
`nbhd i`. -/
instance compactSpace_space : CompactSpace space := by
  refine ⟨?_⟩
  have h : (Set.univ : Set space) = (nbhd true : Set space) ∪ (nbhd false : Set space) := by
    ext x
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (top_le_iSup_nbhd (Opens.mem_top x))
    cases i with
    | false => exact Or.inr hi
    | true => exact Or.inl hi
  rw [h]
  exact (isCompact_of_forall_mem_le (s_mem_nbhd true) fun _ => nbhd_le).union
    (isCompact_of_forall_mem_le (s_mem_nbhd false) fun _ => nbhd_le)

/-- `x ∈ Uₙ = {ξₙ, ξₙ₊₁, …}`. -/
def InTail (n : ℕ) : Point → Prop
  | .s _ => False
  | .ξ m => n ≤ m

/-- The subset `Uₙ = {ξₙ, ξₙ₊₁, …}` of the space. -/
def tail (n : ℕ) : Set space := {x | InTail n x}

/-- The index `m` of a point `ξ m` (and `0` for the points `s i`). -/
def Point.idx : Point → ℕ
  | .s _ => 0
  | .ξ m => m

lemma InTail.le_idx {n : ℕ} {x : Point} (h : InTail n x) : n ≤ x.idx := by
  cases x with
  | s i => exact h.elim
  | ξ m => exact h

lemma InTail.mono {n m : ℕ} (hnm : n ≤ m) {x : Point} (h : InTail m x) : InTail n x := by
  cases x with
  | s i => exact h.elim
  | ξ k => exact hnm.trans h

/-- The fibre of `ℱₙ` at `x`: a copy of `𝐙` when `x ∈ Uₙ`, and a singleton otherwise. -/
def fiber (n : ℕ) (x : Point) : Type := PLift (InTail n x) → ℤ

/-- The system `ℱₙ = jₙ,* 𝐙` of the example: `ℱₙ(V)` is the set of `𝐙`-valued functions on
`V ∩ Uₙ` (presented as the sheaf of sections of the fibre family `fiber n`; see
`sheafSystemObjIso` for the identification with the pushforward of the constant sheaf).  The
transition map `ℱₙ → ℱₘ` for `n ≤ m` restricts a function on `V ∩ Uₙ` to `V ∩ Uₘ`. -/
noncomputable def sheafSystem : ℕ ⥤ TopCat.Sheaf (Type) space where
  obj n := TopCat.sheafToTypes space (fiber n)
  map h := { hom := { app := fun _ => ↾fun σ x p => σ x ⟨p.down.mono (leOfHom h)⟩ } }

/-- `Uₙ` is a discrete subspace: each `{ξ m}` is open. -/
instance (n : ℕ) : DiscreteTopology (tail n) := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun x => ?_
  obtain ⟨x, hx⟩ := x
  cases x with
  | s i => exact hx.elim
  | ξ m =>
    refine ⟨{Point.ξ m}, fun _ h => Point.noConfusion h, ?_⟩
    ext ⟨y, hy⟩
    simp [Subtype.ext_iff]

/-- The inclusion `jₙ : Uₙ → X`. -/
def tailIncl (n : ℕ) : TopCat.of (tail n) ⟶ space :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The sections of `ℱₙ` over `V` are the functions on `V ∩ Uₙ`, i.e. the continuous maps from the
discrete space `jₙ⁻¹(V)` to `𝐙`. -/
def sheafSystemSectionsEquiv (n : ℕ) (V : Opens space) :
    ((sheafSystem.obj n).obj.obj (op V)) ≃
      ((Opens.toTopCat _).obj ((Opens.map (tailIncl n)).obj V) ⟶ TopCat.of ℤ) where
  toFun σ := TopCat.ofHom ⟨fun y => σ ⟨y.1.1, y.2⟩ ⟨y.1.2⟩, continuous_of_discreteTopology⟩
  invFun f x p := f ⟨⟨x.1, p.down⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`ℱₙ = jₙ,* 𝐙`.**  The `n`-th sheaf of the system is the pushforward along the inclusion
`jₙ : Uₙ → X` of the constant sheaf `𝐙` on `Uₙ`, the sheaf of locally constant (equivalently,
since `𝐙` is discrete, continuous) `𝐙`-valued functions. -/
noncomputable def sheafSystemObjIso (n : ℕ) :
    sheafSystem.obj n ≅
      (TopCat.Sheaf.pushforward (Type) (tailIncl n)).obj (TopCat.sheafToTop (TopCat.of ℤ)) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun V => (sheafSystemSectionsEquiv n V.unop).toIso) fun _ => by
      ext σ
      rfl)

/-- The system `n ↦ ∏_{m ≥ n} 𝐙`, with the projections as transition maps. -/
def tailProducts : ℕ ⥤ Type where
  obj n := {m // n ≤ m} → ℤ
  map h := ↾fun f m => f ⟨m.1, (leOfHom h).trans m.2⟩

/-- The set `M = colimₙ ∏_{m ≥ n} 𝐙` of the source. -/
abbrev tailColimit : Type := colimit tailProducts

/-- The constant sequences give distinct elements of `M`. -/
lemma colimit_ι_const_injective {c c' : ℤ}
    (h : colimit.ι tailProducts 0 (fun _ => c) = colimit.ι tailProducts 0 (fun _ => c')) :
    c = c' := by
  obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.colimit_eq_iff tailProducts).mp h
  exact congrFun hfg ⟨k, le_rfl⟩

/-- For an open `V` containing all the `ξ m`, the sections of `ℱₙ` over `V` are `∏_{m ≥ n} 𝐙`. -/
def sectionsEquiv (n : ℕ) {V : Opens space} (hV : ∀ m, Point.ξ m ∈ V) :
    ((presheafSystem sheafSystem).obj n).obj (op V) ≃ tailProducts.obj n where
  toFun σ m := σ ⟨Point.ξ m.1, hV m.1⟩ ⟨m.2⟩
  invFun f x p := f ⟨x.1.idx, p.down.le_idx⟩
  left_inv σ := by
    funext ⟨x, hx⟩ p
    cases x with
    | s i => exact p.down.elim
    | ξ m => rfl
  right_inv _ := rfl

/-- For an open `V` containing all the `ξ m`, the system `n ↦ ℱₙ(V)` is `n ↦ ∏_{m ≥ n} 𝐙`. -/
noncomputable def evalSystemIso {V : Opens space} (hV : ∀ m, Point.ξ m ∈ V) :
    evalSystem sheafSystem V ≅ tailProducts :=
  NatIso.ofComponents (fun n => (sectionsEquiv n hV).toIso) fun _ => rfl

/-- For an open `V` containing all the `ξ m`, `colimₙ ℱₙ(V) = M`. -/
noncomputable def colimitSectionsEquiv {V : Opens space} (hV : ∀ m, Point.ξ m ∈ V) :
    (colimitPresheaf sheafSystem).obj (op V) ≃ tailColimit :=
  (colimitObjIsoColimitCompEvaluation (presheafSystem sheafSystem) (op V) ≪≫
    HasColimit.isoOfNatIso (evalSystemIso hV)).toEquiv

lemma colimitSectionsEquiv_ι {V : Opens space} (hV : ∀ m, Point.ξ m ∈ V) (n : ℕ)
    (σ : ((presheafSystem sheafSystem).obj n).obj (op V)) :
    colimitSectionsEquiv hV ((colimit.ι (presheafSystem sheafSystem) n).app (op V) σ) =
      colimit.ι tailProducts n (sectionsEquiv n hV σ) := by
  have h1 := ConcreteCategory.congr_hom
    (colimitObjIsoColimitCompEvaluation_ι_app_hom (presheafSystem sheafSystem) n (op V)) σ
  have h2 := ConcreteCategory.congr_hom (HasColimit.isoOfNatIso_ι_hom (evalSystemIso hV) n) σ
  simp only [ConcreteCategory.comp_apply] at h1 h2
  exact (congrArg (fun y => (HasColimit.isoOfNatIso (evalSystemIso hV)).hom y) h1).trans h2

/-- The identification `colimₙ ℱₙ(V) = M` commutes with restriction. -/
lemma colimitSectionsEquiv_map {V W : Opens space} (hWV : W ≤ V) (hV : ∀ m, Point.ξ m ∈ V)
    (hW : ∀ m, Point.ξ m ∈ W) (t : (colimitPresheaf sheafSystem).obj (op V)) :
    colimitSectionsEquiv hW ((colimitPresheaf sheafSystem).map (homOfLE hWV).op t) =
      colimitSectionsEquiv hV t := by
  obtain ⟨n, σ, -, rfl, -⟩ := exists_common_index sheafSystem V t t
  have hnat : (colimitPresheaf sheafSystem).map (homOfLE hWV).op
      ((colimit.ι (presheafSystem sheafSystem) n).app (op V) σ) =
      (colimit.ι (presheafSystem sheafSystem) n).app (op W)
        (((presheafSystem sheafSystem).obj n).map (homOfLE hWV).op σ) :=
    (ConcreteCategory.congr_hom
      ((colimit.ι (presheafSystem sheafSystem) n).naturality (homOfLE hWV).op) σ).symm
  rw [hnat, colimitSectionsEquiv_ι, colimitSectionsEquiv_ι]
  rfl

/-- Sections of `ℱₙ` over an open containing no point of `Uₙ` form a subsingleton. -/
lemma subsingleton_sections (n : ℕ) {V : Opens space} (h : ∀ x ∈ V, ¬ InTail n x) :
    Subsingleton (((presheafSystem sheafSystem).obj n).obj (op V)) :=
  ⟨fun _ _ => funext fun x => funext fun p => (h x.1 x.2 p.down).elim⟩

/-- `colimₙ ℱₙ({ξ m})` is a subsingleton: `ℱₙ({ξ m})` is a singleton once `n > m`. -/
lemma subsingleton_colimitPresheaf_pt (m : ℕ) :
    Subsingleton ((colimitPresheaf sheafSystem).obj (op (pt m))) := by
  refine ⟨fun t t' => ?_⟩
  obtain ⟨k, sk, tk, rfl, rfl⟩ := exists_common_index sheafSystem (pt m) t t'
  have := subsingleton_sections (max k (m + 1)) (V := pt m) fun x hx hxt => by
    rw [Set.mem_singleton_iff.mp hx] at hxt
    exact absurd (le_trans (le_max_right k (m + 1)) hxt) (by omega)
  exact (colimit_eq_iff_eventual sheafSystem (pt m) k sk tk).mpr
    ⟨max k (m + 1), homOfLE (le_max_left _ _), Subsingleton.elim _ _⟩

/-- On `nbhd i`, the canonical map of 009F is bijective: `nbhd i` is the smallest open
neighbourhood of `s i`, so 009F (4) applies. -/
lemma bijective_canonicalMap_nbhd (i : Bool) :
    Function.Bijective (canonicalMap sheafSystem (nbhd i)) :=
  bijective_canonicalMap_of_hasFiniteCompactCofinalCovers sheafSystem _
    (hasFiniteCompactCofinalCovers_of_forall_mem_le (s_mem_nbhd i) fun _ => nbhd_le)

/-- On `{ξ m}`, the canonical map of 009F is bijective. -/
lemma bijective_canonicalMap_pt (m : ℕ) :
    Function.Bijective (canonicalMap sheafSystem (pt m)) :=
  bijective_canonicalMap_of_hasFiniteCompactCofinalCovers sheafSystem _
    (hasFiniteCompactCofinalCovers_of_forall_mem_le (mem_pt m) fun _ => pt_le)

/-- `ℱ({ξ m})` is a subsingleton, for the colimit sheaf `ℱ = colimₙ ℱₙ`. -/
lemma subsingleton_colimitSheaf_pt (m : ℕ) :
    Subsingleton ((colimitSheaf sheafSystem).obj.obj (op (pt m))) := by
  refine ⟨fun σ τ => ?_⟩
  obtain ⟨s, rfl⟩ := (bijective_canonicalMap_pt m).2 σ
  obtain ⟨t, rfl⟩ := (bijective_canonicalMap_pt m).2 τ
  have := subsingleton_colimitPresheaf_pt m
  rw [Subsingleton.elim s t]

/-- The sections of the colimit sheaf `ℱ` over an open containing neither `s₁` nor `s₂` form a
subsingleton. -/
lemma subsingleton_colimitSheaf {V : Opens space} (hV : ∀ i, Point.s i ∉ V) :
    Subsingleton ((colimitSheaf sheafSystem).obj.obj (op V)) := by
  have hW : ∀ m : {m // Point.ξ m ∈ V}, pt m.1 ≤ V := fun m => pt_le m.2
  refine ⟨fun σ τ => sheafify_eq_of_local_eq sheafSystem V
    (fun m : {m // Point.ξ m ∈ V} => pt m.1) hW (fun x hx => ?_) σ τ fun m => ?_⟩
  · cases x with
    | s i => exact (hV i hx).elim
    | ξ n => exact Opens.mem_iSup.mpr ⟨⟨n, hx⟩, mem_pt n⟩
  · have := subsingleton_colimitSheaf_pt m.1
    exact Subsingleton.elim _ _

/-- **The stalks of `ℱ` at the `ξ n` vanish.** -/
lemma subsingleton_stalk_ξ (m : ℕ) :
    Subsingleton ((colimitSheaf sheafSystem).presheaf.stalk (Point.ξ m)) := by
  have := subsingleton_colimitSheaf_pt m
  exact (bijective_germ_of_forall_mem_le (colimitSheaf sheafSystem).presheaf (mem_pt m)
    fun _ => pt_le).2.subsingleton

/-- The sections of `ℱ` over `nbhd i` are the sections of `ℱ' : V ↦ colimₙ ℱₙ(V)` over it. -/
noncomputable def nbhdSectionsEquiv (i : Bool) :
    (colimitPresheaf sheafSystem).obj (op (nbhd i)) ≃
      (colimitSheaf sheafSystem).obj.obj (op (nbhd i)) :=
  Equiv.ofBijective _ (bijective_canonicalMap_nbhd i)

/-- **The stalk of `ℱ` at `s₁` and at `s₂` is `M = colimₙ ∏_{m ≥ n} 𝐙`.** -/
noncomputable def stalkEquiv (i : Bool) :
    (colimitSheaf sheafSystem).presheaf.stalk (Point.s i) ≃ tailColimit :=
  (Equiv.ofBijective _ (bijective_germ_of_forall_mem_le (colimitSheaf sheafSystem).presheaf
    (s_mem_nbhd i) fun _ => nbhd_le)).symm.trans
    ((nbhdSectionsEquiv i).symm.trans (colimitSectionsEquiv (ξ_mem_nbhd i)))

/-- The value in `M` of a global section of `ℱ` near `s i`: its restriction to `nbhd i`, read in
`ℱ(nbhd i) = colimₙ ℱₙ(nbhd i) = M`. -/
noncomputable def valueAt (i : Bool) (σ : (colimitSheaf sheafSystem).obj.obj (op ⊤)) :
    tailColimit :=
  colimitSectionsEquiv (ξ_mem_nbhd i) ((nbhdSectionsEquiv i).symm
    ((colimitSheaf sheafSystem).obj.map (homOfLE (le_top (a := nbhd i))).op σ))

/-- **`Γ(X, ℱ) = M ⊕ M`.**  A global section of the colimit sheaf `ℱ` is the same as a pair of
elements of `M`, its values near `s₁` and near `s₂`. -/
lemma bijective_valueAt :
    Function.Bijective fun σ : (colimitSheaf sheafSystem).obj.obj (op ⊤) =>
      (valueAt true σ, valueAt false σ) := by
  have hinter : ∀ i j : Bool, i ≠ j →
      Subsingleton ((colimitSheaf sheafSystem).obj.obj (op (nbhd i ⊓ nbhd j))) := by
    intro i j hij
    refine subsingleton_colimitSheaf fun k hk => ?_
    have h1 : Point.s k ≠ Point.s (!i) := hk.1
    have h2 : Point.s k ≠ Point.s (!j) := hk.2
    cases i <;> cases j <;> cases k <;> simp_all
  refine ⟨fun σ τ h => ?_, fun ab => ?_⟩
  · have hres : ∀ i, (colimitSheaf sheafSystem).obj.map (homOfLE (le_top (a := nbhd i))).op σ =
        (colimitSheaf sheafSystem).obj.map (homOfLE (le_top (a := nbhd i))).op τ := by
      intro i
      have hi : valueAt i σ = valueAt i τ := by
        cases i
        · exact congrArg Prod.snd h
        · exact congrArg Prod.fst h
      exact (nbhdSectionsEquiv i).symm.injective ((colimitSectionsEquiv _).injective hi)
    exact sheafify_eq_of_local_eq sheafSystem ⊤ nbhd (fun _ => le_top) top_le_iSup_nbhd σ τ hres
  · let sf : ∀ i, (colimitSheaf sheafSystem).obj.obj (op (nbhd i)) := fun i =>
      nbhdSectionsEquiv i ((colimitSectionsEquiv (ξ_mem_nbhd i)).symm (cond i ab.1 ab.2))
    obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' (colimitSheaf sheafSystem) nbhd ⊤
      (fun _ => homOfLE le_top) top_le_iSup_nbhd sf fun i j => by
        by_cases hij : i = j
        · subst hij
          rw [Subsingleton.elim (Opens.infLELeft (nbhd i) (nbhd i))
            (Opens.infLERight (nbhd i) (nbhd i))]
        · have := hinter i j hij
          exact Subsingleton.elim _ _
    have hv : ∀ i, valueAt i σ = cond i ab.1 ab.2 := fun i => by
      simp only [valueAt]
      rw [hσ i]
      simp [sf]
    exact ⟨σ, Prod.ext (hv true) (hv false)⟩

/-- `Γ(X, ℱ) ≃ M × M`, the set underlying `M ⊕ M`. -/
noncomputable def globalSectionsEquiv :
    (colimitSheaf sheafSystem).obj.obj (op ⊤) ≃ tailColimit × tailColimit :=
  Equiv.ofBijective _ bijective_valueAt

/-- `colimₙ Γ(X, ℱₙ) ≃ M`. -/
noncomputable def colimitGlobalSectionsEquiv :
    (colimitPresheaf sheafSystem).obj (op ⊤) ≃ tailColimit :=
  colimitSectionsEquiv fun _ => trivial

/-- Under the identifications `colimₙ Γ(X, ℱₙ) = M` and `Γ(X, ℱ) = M ⊕ M`, the canonical map
of 009F is the diagonal `M → M ⊕ M`. -/
lemma globalSectionsEquiv_canonicalMap (t : (colimitPresheaf sheafSystem).obj (op ⊤)) :
    globalSectionsEquiv (canonicalMap sheafSystem ⊤ t) =
      (colimitGlobalSectionsEquiv t, colimitGlobalSectionsEquiv t) := by
  have h : ∀ i, valueAt i (canonicalMap sheafSystem ⊤ t) = colimitGlobalSectionsEquiv t := by
    intro i
    have hnat : (colimitSheaf sheafSystem).obj.map (homOfLE (le_top (a := nbhd i))).op
        (canonicalMap sheafSystem ⊤ t) = canonicalMap sheafSystem (nbhd i)
          ((colimitPresheaf sheafSystem).map (homOfLE (le_top (a := nbhd i))).op t) :=
      (ConcreteCategory.congr_hom ((TopCat.Presheaf.toSheafify
        (colimitPresheaf sheafSystem)).naturality (homOfLE (le_top (a := nbhd i))).op) t).symm
    simp only [valueAt, colimitGlobalSectionsEquiv]
    rw [hnat]
    exact ((congrArg (colimitSectionsEquiv (ξ_mem_nbhd i))
      ((nbhdSectionsEquiv i).symm_apply_apply _)).trans
      (colimitSectionsEquiv_map le_top _ _ t))
  exact Prod.ext (h true) (h false)

/-- Membership of `s i` in an open, decided classically (needed to form skyscraper sheaves at
`s i`). -/
noncomputable instance decidableMemOpens (i : Bool) (U : Opens space) :
    Decidable (Point.s i ∈ U) :=
  Classical.dec _

/-- The map from `ℱ` to the skyscraper sheaf at `s i` with value `M`, given on stalks at `s i`
by `stalkEquiv i`. -/
noncomputable def toSkyscraper (i : Bool) :
    (colimitSheaf sheafSystem).presheaf ⟶ skyscraperPresheaf (X := space) (Point.s i) tailColimit :=
  StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf (X := space) (Point.s i)
    (𝓕 := (colimitSheaf sheafSystem).presheaf) (↾fun g => stalkEquiv i g)

lemma toSkyscraper_app_of_mem {i : Bool} {U : Opens space} (h : Point.s i ∈ U)
    (σ : (colimitSheaf sheafSystem).obj.obj (op U)) :
    (toSkyscraper i).app (op U) σ = (eqToIso (ite_eq_left (α := Type) h).symm).hom
      (stalkEquiv i ((colimitSheaf sheafSystem).presheaf.germ U (Point.s i) h σ)) := by
  have key : (toSkyscraper i).app (op U) =
      (colimitSheaf sheafSystem).presheaf.germ U (Point.s i) h ≫ (↾fun g => stalkEquiv i g) ≫
        eqToHom (ite_eq_left (α := Type) h).symm := by
    simp only [toSkyscraper, StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app]
    exact dite_eq_left h
  rw [key]
  rfl

/-- The skyscraper sheaf at `s i` has a single section over an open missing `s i`. -/
lemma subsingleton_skyscraper_of_not_mem {i : Bool} {U : Opens space} (h : Point.s i ∉ U) :
    Subsingleton ((skyscraperPresheaf (X := space) (Point.s i) tailColimit).obj (op U)) := by
  obtain ⟨_, huniq⟩ := Types.isTerminalEquivUnique _ (isTerminalSkyscraperSheafObjObjOfNotMem
    (p₀ := Point.s i) (A := tailColimit) (U := op U) h)
  exact ⟨fun a b => (huniq a).trans (huniq b).symm⟩

/-- Two sections of `ℱ` with the same images in both skyscraper sheaves are equal. -/
lemma toSkyscraper_injective (U : Opens space) :
    Function.Injective fun σ : (colimitSheaf sheafSystem).obj.obj (op U) =>
      ((toSkyscraper true).app (op U) σ, (toSkyscraper false).app (op U) σ) := by
  intro σ τ hστ
  have hcomp : ∀ i, (toSkyscraper i).app (op U) σ = (toSkyscraper i).app (op U) τ := by
    intro i
    cases i
    · exact congrArg Prod.snd hστ
    · exact congrArg Prod.fst hστ
  refine TopCat.Presheaf.section_ext (colimitSheaf sheafSystem) U σ τ fun x hx => ?_
  cases x with
  | s i =>
    have h := hcomp i
    rw [toSkyscraper_app_of_mem hx, toSkyscraper_app_of_mem hx] at h
    exact (stalkEquiv i).injective ((eqToIso _).toEquiv.injective h)
  | ξ m =>
    have := subsingleton_stalk_ξ m
    exact Subsingleton.elim _ _

/-- Every pair of sections of the two skyscraper sheaves comes from a section of `ℱ`. -/
lemma toSkyscraper_surjective (U : Opens space) :
    Function.Surjective fun σ : (colimitSheaf sheafSystem).obj.obj (op U) =>
      ((toSkyscraper true).app (op U) σ, (toSkyscraper false).app (op U) σ) := by
  intro ab
  let J := {i : Bool // Point.s i ∈ U}
  -- the value prescribed at `s i`
  let val : ∀ i : Bool, (skyscraperPresheaf (X := space) (Point.s i) tailColimit).obj (op U) :=
    fun i => by cases i; exacts [ab.2, ab.1]
  suffices hex : ∃ σ : (colimitSheaf sheafSystem).obj.obj (op U),
      ∀ i, (toSkyscraper i).app (op U) σ = val i by
    obtain ⟨σ, hσ⟩ := hex
    exact ⟨σ, Prod.ext (hσ true) (hσ false)⟩
  rcases isEmpty_or_nonempty J with hJ | ⟨⟨j₀, hj₀⟩⟩
  · have hs : ∀ i, Point.s i ∉ U := fun i hi => hJ.false ⟨i, hi⟩
    refine ⟨(colimitSheaf sheafSystem).obj.map (homOfLE le_top).op
      (globalSectionsEquiv.symm (colimit.ι tailProducts 0 fun _ => 0,
        colimit.ι tailProducts 0 fun _ => 0)), fun i => ?_⟩
    have := subsingleton_skyscraper_of_not_mem (hs i)
    exact Subsingleton.elim _ _
  · -- the section over `nbhd j` with the prescribed germ at `s j`
    have hgerm : ∀ j : J, Function.Bijective
        ((colimitSheaf sheafSystem).presheaf.germ (nbhd j.1) (Point.s j.1) (s_mem_nbhd j.1)) :=
      fun j => bijective_germ_of_forall_mem_le _ (s_mem_nbhd j.1) fun _ => nbhd_le
    let sf : ∀ j : J, (colimitSheaf sheafSystem).obj.obj (op (nbhd j.1)) := fun j =>
      (Equiv.ofBijective _ (hgerm j)).symm
        ((stalkEquiv j.1).symm ((eqToIso (ite_eq_left (α := Type) j.2).symm).inv (val j.1)))
    have hcover : U ≤ ⨆ j : J, nbhd j.1 := by
      intro x hx
      refine Opens.mem_iSup.mpr ?_
      cases x with
      | s i => exact ⟨⟨i, hx⟩, s_mem_nbhd i⟩
      | ξ m => exact ⟨⟨j₀, hj₀⟩, ξ_mem_nbhd j₀ m⟩
    obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' (colimitSheaf sheafSystem)
      (fun j : J => nbhd j.1) U (fun j => homOfLE (nbhd_le j.2)) hcover sf fun j k => by
        by_cases hjk : j = k
        · subst hjk
          rw [Subsingleton.elim (Opens.infLELeft (nbhd j.1) (nbhd j.1))
            (Opens.infLERight (nbhd j.1) (nbhd j.1))]
        · obtain ⟨j, hj⟩ := j
          obtain ⟨k, hk⟩ := k
          have hjk' : j ≠ k := fun h => hjk (Subtype.ext h)
          refine @Subsingleton.elim _ (subsingleton_colimitSheaf fun l hl => ?_) _ _
          have h1 : Point.s l ≠ Point.s (!j) := hl.1
          have h2 : Point.s l ≠ Point.s (!k) := hl.2
          cases j <;> cases k <;> cases l <;> simp_all
    refine ⟨σ, fun i => ?_⟩
    by_cases hi : Point.s i ∈ U
    · rw [toSkyscraper_app_of_mem hi,
        ← (colimitSheaf sheafSystem).presheaf.germ_res_apply (homOfLE (nbhd_le hi)) (Point.s i)
          (s_mem_nbhd i) σ]
      have hres := hσ ⟨i, hi⟩
      change (colimitSheaf sheafSystem).presheaf.map (homOfLE (nbhd_le hi)).op σ = _ at hres
      rw [hres]
      have hsf := (Equiv.ofBijective _ (hgerm ⟨i, hi⟩)).apply_symm_apply
        ((stalkEquiv i).symm ((eqToIso (ite_eq_left (α := Type) hi).symm).inv (val i)))
      change (colimitSheaf sheafSystem).presheaf.germ (nbhd i) (Point.s i) (s_mem_nbhd i)
        (sf ⟨i, hi⟩) = _ at hsf
      rw [hsf, Equiv.apply_symm_apply]
      exact (eqToIso (ite_eq_left (α := Type) hi).symm).toEquiv.apply_symm_apply (val i)
    · have := subsingleton_skyscraper_of_not_mem hi
      exact Subsingleton.elim _ _

/-- **`ℱ` is the direct sum of the skyscraper sheaves with value `M` at `s₁` and `s₂`.**  For
every open `U`, the maps `toSkyscraper i` identify `ℱ(U)` with the product of the sections over
`U` of the skyscraper sheaves at `s₁` and at `s₂` (for sheaves of sets the direct sum is the
product). -/
lemma bijective_toSkyscraper (U : Opens space) :
    Function.Bijective fun σ : (colimitSheaf sheafSystem).obj.obj (op U) =>
      ((toSkyscraper true).app (op U) σ, (toSkyscraper false).app (op U) σ) :=
  ⟨toSkyscraper_injective U, toSkyscraper_surjective U⟩

/-- **Stacks 009G.**  Let `X = {s₁, s₂, ξ₁, ξ₂, …}`, where a subset is open if it contains all
of the `ξᵢ` as soon as it contains `s₁` or `s₂`; let `Uₙ = {ξₙ, ξₙ₊₁, …}` and `ℱₙ = jₙ,* 𝐙`
(`sheafSystem`; `sheafSystemObjIso` identifies `ℱₙ` with the pushforward of the constant sheaf),
with the restriction maps as transition maps, and let `ℱ = colimₙ ℱₙ`.  Then:

* `X` is quasi-compact;
* the canonical map `Ψ : colimₙ Γ(X, ℱₙ) → Γ(X, ℱ)` of 009F is injective but not surjective;
* with `M = colimₙ ∏_{m ≥ n} 𝐙` (`tailColimit`), `colimₙ Γ(X, ℱₙ) = M` and `Γ(X, ℱ) = M ⊕ M`,
  and under these identifications `Ψ` is the diagonal;
* the stalk of `ℱ` is zero at every `ξₙ` and is `M` at `s₁` and at `s₂`;
* `ℱ` is the direct sum of the skyscraper sheaves with value `M` at `s₁` and `s₂`: the maps
  `toSkyscraper i` to Mathlib's `skyscraperPresheaf (s i) M` identify `ℱ(U)` with the product
  of their sections over `U`, for every open `U`.

So some condition is necessary in 009F (4), even for a quasi-compact open.  The sheaves are
sheaves of sets, the setting of 009F in this library, so the direct sum `M ⊕ M` is the product
set `M × M`, and the zero stalk is a one-point set; the points `ξ` are numbered from `0`. -/
@[stacks 009G "The example itself: the space `{s₁, s₂, ξ₁, ξ₂, …}`, the system `jₙ,* 𝐙` as \
sheaves of sets, quasi-compactness of the space, injectivity and non-surjectivity of `Ψ` on global \
sections, `colimₙ Γ(X, ℱₙ) = M`, `Γ(X, ℱ) = M ⊕ M` with `Ψ` the diagonal, the stalks of `ℱ`, and \
`ℱ` as the sum of the two skyscraper sheaves."]
theorem compactSpace_and_canonicalMap_top_injective_not_surjective :
    CompactSpace space ∧
      Function.Injective (canonicalMap sheafSystem ⊤) ∧
      ¬ Function.Surjective (canonicalMap sheafSystem ⊤) ∧
      (∃ (e : (colimitPresheaf sheafSystem).obj (op ⊤) ≃ tailColimit)
        (e' : (colimitSheaf sheafSystem).obj.obj (op ⊤) ≃ tailColimit × tailColimit),
        ∀ t, e' (canonicalMap sheafSystem ⊤ t) = (e t, e t)) ∧
      (∀ n, Subsingleton ((colimitSheaf sheafSystem).presheaf.stalk (Point.ξ n))) ∧
      (∀ i, Nonempty ((colimitSheaf sheafSystem).presheaf.stalk (Point.s i) ≃ tailColimit)) ∧
      ∀ U : Opens space, Function.Bijective fun σ : (colimitSheaf sheafSystem).obj.obj (op U) =>
        ((toSkyscraper true).app (op U) σ, (toSkyscraper false).app (op U) σ) := by
  refine ⟨compactSpace_space,
    injective_canonicalMap_of_isCompact sheafSystem ⊤ (by simpa using isCompact_univ),
    fun hsurj => ?_, ⟨colimitGlobalSectionsEquiv, globalSectionsEquiv,
    globalSectionsEquiv_canonicalMap⟩, subsingleton_stalk_ξ, fun i => ⟨stalkEquiv i⟩,
    bijective_toSkyscraper⟩
  obtain ⟨t, ht⟩ := hsurj (globalSectionsEquiv.symm
    (colimit.ι tailProducts 0 fun _ => 0, colimit.ι tailProducts 0 fun _ => 1))
  have h := globalSectionsEquiv_canonicalMap t
  rw [ht, Equiv.apply_symm_apply] at h
  exact zero_ne_one (colimit_ι_const_injective ((congrArg Prod.fst h).trans
    (congrArg Prod.snd h).symm))

end QuasiCompactCounterexample

end DirectedColimitOfSheaves
