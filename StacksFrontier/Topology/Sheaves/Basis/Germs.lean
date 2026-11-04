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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Project, Tag 009M — Sections of a sheaf on a basis via germs

Let `X` be a topological space, `B` a basis for the topology on `X`, and
`F` a sheaf of sets on `B`. For `U ∈ B` the "germ map"
`Φ_U : F(U) → ∏_{x ∈ U} F_x` is injective, and its image is exactly the
set of families `(s_x)_{x ∈ U}` satisfying condition (*):

  for every `x ∈ U` there exists `V ∈ B` with `x ∈ V ⊆ U` and a
  section `σ ∈ F(V)` such that for all `y ∈ V` the germ `s_y` equals
  the class of `(V, σ)` in `F_y`.

This file develops a self-contained theory of presheaves and sheaves of
sets on a basis (`PresheafOnBasisOpenSet`, `PresheafOnBasisOpenSet.IsSheaf`), of the
stalk at a point (`Stalk`, built as a quotient of `StalkDatum`), of the
germ map (`germ`, `germMap`), and of condition (*) (`ConditionStar`), and
proves the three statements: `germMap_injective`,
`germMap_range_eq_conditionStar`, and `germMap_bijection`.

The two non-trivial ingredients are sheaf separation (for injectivity
and for the local-to-global step) and sheaf gluing (for surjectivity
onto the (*)-families).
-/

@[expose] public section

open TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

namespace Stacks.Topology.BasisPresheaf

/-! ## Presheaves on a basis -/

/-- A presheaf of sets on a basis `B ⊆ Set X` assigns to each `U ∈ B` a type
`obj U hU`, together with restriction maps `res hU hV (hVU : V ⊆ U)` between
basis elements which are functorial (compatible with identity and composition
of inclusions). -/
@[ega "0 3.2.1" "special case"]
structure PresheafOnBasisOpenSet (B : Set (Set X)) where
  /-- The set of sections over a basis element `U`. -/
  obj : (U : Set X) → U ∈ B → Type u
  /-- The restriction map between basis elements for an inclusion `V ⊆ U`. -/
  res : ∀ {U V : Set X} (hU : U ∈ B) (hV : V ∈ B), V ⊆ U → obj U hU → obj V hV
  /-- Restriction along identity is identity. -/
  res_self : ∀ {U : Set X} (hU : U ∈ B) (s : obj U hU),
    res hU hU (Set.Subset.refl U) s = s
  /-- Restrictions compose. -/
  res_trans : ∀ {U V W : Set X} (hU : U ∈ B) (hV : V ∈ B) (hW : W ∈ B)
    (hVU : V ⊆ U) (hWV : W ⊆ V) (s : obj U hU),
    res hV hW hWV (res hU hV hVU s) = res hU hW (hWV.trans hVU) s

/-- The sheaf condition for a presheaf on a basis: for every `U ∈ B` and every
covering `U ⊆ ⋃ i, Ui i` by basis elements `Ui i ∈ B` contained in `U`,
separation and gluing hold (overlaps are tested against all basis elements
`W ⊆ Ui i ∩ Ui j`). -/
def PresheafOnBasisOpenSet.IsSheaf {B : Set (Set X)} (F : PresheafOnBasisOpenSet B) : Prop :=
  ∀ {U : Set X} (hU : U ∈ B) {ι : Type u} (Ui : ι → Set X)
    (hUi : ∀ i, Ui i ∈ B) (hsub : ∀ i, Ui i ⊆ U) (_ : U ⊆ ⋃ i, Ui i),
    (∀ (s t : F.obj U hU),
        (∀ i, F.res hU (hUi i) (hsub i) s = F.res hU (hUi i) (hsub i) t) →
        s = t) ∧
    (∀ (s : ∀ i, F.obj (Ui i) (hUi i)),
        (∀ i j (W : Set X) (hW : W ∈ B)
            (hWi : W ⊆ Ui i) (hWj : W ⊆ Ui j),
            F.res (hUi i) hW hWi (s i) = F.res (hUi j) hW hWj (s j)) →
        ∃ t : F.obj U hU, ∀ i, F.res hU (hUi i) (hsub i) t = s i)

/-! ## Stalks at a point -/

/-- A "stalk-datum" at `x ∈ X`: a basis element `V` containing `x` together with
a section `σ ∈ F.obj V`. -/
structure StalkDatum {B : Set (Set X)} (F : PresheafOnBasisOpenSet B) (x : X) where
  /-- A basis element. -/
  V : Set X
  /-- It belongs to the basis. -/
  hV : V ∈ B
  /-- The point `x` lies in `V`. -/
  hxV : x ∈ V
  /-- A section of `F` over `V`. -/
  sec : F.obj V hV

/-- The "germ-equivalence" relation on stalk-data: two pairs `(V, σ)` and
`(V', σ')` are related at `x` if there exists `W ∈ B` with `x ∈ W ⊆ V ∩ V'`
on which the two sections restrict to the same element. -/
def StalkDatum.Rel {B : Set (Set X)} (F : PresheafOnBasisOpenSet B) {x : X}
    (a b : StalkDatum F x) : Prop :=
  ∃ (W : Set X) (hW : W ∈ B) (_ : x ∈ W)
    (hWV : W ⊆ a.V) (hWV' : W ⊆ b.V),
    F.res a.hV hW hWV a.sec = F.res b.hV hW hWV' b.sec

/-- The stalk of `F` at `x` is the quotient of stalk-data by the
germ-equivalence relation. -/
def Stalk {B : Set (Set X)} (F : PresheafOnBasisOpenSet B) (x : X) : Type u :=
  Quot (StalkDatum.Rel F (x := x))

/-- The canonical map `F.obj V hV → Stalk F x` for `x ∈ V`, `V ∈ B`. -/
def germ {B : Set (Set X)} (F : PresheafOnBasisOpenSet B) {V : Set X} (hV : V ∈ B)
    {x : X} (hxV : x ∈ V) (σ : F.obj V hV) : Stalk F x :=
  Quot.mk _ ⟨V, hV, hxV, σ⟩

/-! ## The germ map `Φ_U` and condition (*) -/

/-- The germ map `Φ_U : F.obj U hU → ∀ x : U, Stalk F x.1` sends a section
`s` to the family of its germs. -/
def germMap {B : Set (Set X)} (F : PresheafOnBasisOpenSet B) {U : Set X} (hU : U ∈ B)
    (s : F.obj U hU) : ∀ x : U, Stalk F x.1 :=
  fun x => germ F hU x.2 s

/-- Condition (*): a family `(s_x)_{x ∈ U}` of germs satisfies (*) if for
every `x ∈ U` there is a basis element `V` with `x ∈ V ⊆ U` and a section
`σ` on `V` whose germ at every `y ∈ V` equals `s_y`. -/
def ConditionStar {B : Set (Set X)} (F : PresheafOnBasisOpenSet B) {U : Set X}
    (s : ∀ x : U, Stalk F x.1) : Prop :=
  ∀ x : U, ∃ (V : Set X) (hV : V ∈ B) (_ : (x : X) ∈ V) (hVU : V ⊆ U)
    (σ : F.obj V hV), ∀ (y : X) (hyV : y ∈ V),
    s ⟨y, hVU hyV⟩ = germ F hV hyV σ

/-! ## `StalkDatum.Rel` is an equivalence relation -/

omit [TopologicalSpace X] in
/-- `StalkDatum.Rel F` is reflexive. -/
lemma Rel_refl {B : Set (Set X)} (F : PresheafOnBasisOpenSet B) {x : X}
    (a : StalkDatum F x) : StalkDatum.Rel F a a :=
  ⟨a.V, a.hV, a.hxV, Set.Subset.refl a.V, Set.Subset.refl a.V, rfl⟩

omit [TopologicalSpace X] in
/-- `StalkDatum.Rel F` is symmetric. -/
lemma Rel_symm {B : Set (Set X)} (F : PresheafOnBasisOpenSet B) {x : X}
    {a b : StalkDatum F x} (h : StalkDatum.Rel F a b) :
    StalkDatum.Rel F b a := by
  obtain ⟨W, hW, hxW, hWV, hWV', h_eq⟩ := h
  exact ⟨W, hW, hxW, hWV', hWV, h_eq.symm⟩

/-- `StalkDatum.Rel F` is transitive (using the basis property to refine
the two witness sets into their intersection). -/
lemma Rel_trans {B : Set (Set X)} (hB : IsTopologicalBasis B)
    (F : PresheafOnBasisOpenSet B) {x : X} {a b c : StalkDatum F x}
    (h1 : StalkDatum.Rel F a b) (h2 : StalkDatum.Rel F b c) :
    StalkDatum.Rel F a c := by
  obtain ⟨W₁, hW₁, hxW₁, hW₁a, hW₁b, eq1⟩ := h1
  obtain ⟨W₂, hW₂, hxW₂, hW₂b, hW₂c, eq2⟩ := h2
  obtain ⟨W, hW, hxW, hWsub⟩ :=
    hB.exists_subset_inter W₁ hW₁ W₂ hW₂ x ⟨hxW₁, hxW₂⟩
  have hWW₁ : W ⊆ W₁ := fun y hy => (hWsub hy).1
  have hWW₂ : W ⊆ W₂ := fun y hy => (hWsub hy).2
  have hWa : W ⊆ a.V := hWW₁.trans hW₁a
  have hWb : W ⊆ b.V := hWW₁.trans hW₁b
  have hWc : W ⊆ c.V := hWW₂.trans hW₂c
  refine ⟨W, hW, hxW, hWa, hWc, ?_⟩
  have eq_via_W₁ : F.res a.hV hW hWa a.sec = F.res b.hV hW hWb b.sec := by
    rw [← F.res_trans a.hV hW₁ hW hW₁a hWW₁ a.sec,
      ← F.res_trans b.hV hW₁ hW hW₁b hWW₁ b.sec, eq1]
  have eq_via_W₂ : F.res b.hV hW hWb b.sec = F.res c.hV hW hWc c.sec := by
    rw [← F.res_trans b.hV hW₂ hW hW₂b hWW₂ b.sec,
      ← F.res_trans c.hV hW₂ hW hW₂c hWW₂ c.sec, eq2]
  exact eq_via_W₁.trans eq_via_W₂

/-- Since `StalkDatum.Rel F` is an equivalence relation, the equivalence
closure `Relation.EqvGen (StalkDatum.Rel F)` coincides with
`StalkDatum.Rel F`. -/
lemma eqvGen_rel_iff {B : Set (Set X)} (hB : IsTopologicalBasis B)
    (F : PresheafOnBasisOpenSet B) {x : X} {a b : StalkDatum F x} :
    Relation.EqvGen (StalkDatum.Rel F) a b ↔ StalkDatum.Rel F a b := by
  refine ⟨fun h => ?_, fun h => Relation.EqvGen.rel _ _ h⟩
  induction h with
  | rel _ _ h => exact h
  | refl x => exact Rel_refl F x
  | symm _ _ _ ih => exact Rel_symm F ih
  | trans _ _ _ _ _ ih1 ih2 => exact Rel_trans hB F ih1 ih2

/-- The germ-equality criterion: two stalk-data have equal germs iff they
are `StalkDatum.Rel`-related. -/
lemma germ_eq_iff_rel {B : Set (Set X)} (hB : IsTopologicalBasis B)
    (F : PresheafOnBasisOpenSet B) {x : X} (a b : StalkDatum F x) :
    (Quot.mk (StalkDatum.Rel F (x := x)) a = Quot.mk _ b) ↔
      StalkDatum.Rel F a b :=
  ⟨fun h => (eqvGen_rel_iff hB F).mp (Quot.eqvGen_exact h), Quot.sound⟩

/-! ## Germ-restriction and the local-to-global lemma -/

omit [TopologicalSpace X] in
/-- For a section `s ∈ F.obj U hU` and a basis element `V ⊆ U` containing
`x ∈ V`, the germ of `s` at `x` equals the germ of the restriction
`F.res hU hV hVU s` at `x`. -/
lemma germ_res {B : Set (Set X)} (F : PresheafOnBasisOpenSet B)
    {U V : Set X} (hU : U ∈ B) (hV : V ∈ B) (hVU : V ⊆ U) {x : X}
    (hxV : x ∈ V) (s : F.obj U hU) :
    germ F hU (hVU hxV) s = germ F hV hxV (F.res hU hV hVU s) :=
  Quot.sound ⟨V, hV, hxV, hVU, Set.Subset.refl V, (F.res_self hV (F.res hU hV hVU s)).symm⟩

/-- **Local restriction equality from local germ equality.** If two
sections `σ : F.obj V hV` and `σ' : F.obj V' hV'` have germs that agree at
every point of a basis element `W ⊆ V ∩ V'`, then they restrict to the
same element on `W`. -/
lemma res_eq_of_local_germ_eq {B : Set (Set X)} (hB : IsTopologicalBasis B)
    (F : PresheafOnBasisOpenSet B) (hF : F.IsSheaf)
    {V V' W : Set X} (hV : V ∈ B) (hV' : V' ∈ B) (hW : W ∈ B)
    (hWV : W ⊆ V) (hWV' : W ⊆ V')
    (σ : F.obj V hV) (σ' : F.obj V' hV')
    (hgerm : ∀ z (hz : z ∈ W),
      germ F hV (hWV hz) σ = germ F hV' (hWV' hz) σ') :
    F.res hV hW hWV σ = F.res hV' hW hWV' σ' := by
  -- For each `z ∈ W`, refine to a basis element `U ⊆ W` on which the two
  -- restrictions of `σ` and `σ'` agree directly.
  have hkey : ∀ z : (W : Set X), ∃ (U : Set X) (hU : U ∈ B) (_ : (z : X) ∈ U)
      (hUW : U ⊆ W),
      F.res hV hU (hUW.trans hWV) σ = F.res hV' hU (hUW.trans hWV') σ' := by
    rintro ⟨z, hz⟩
    obtain ⟨Wz, hWz, hzWz, hWzV, hWzV', hres⟩ := (germ_eq_iff_rel hB F
      (⟨V, hV, hWV hz, σ⟩ : StalkDatum F z) ⟨V', hV', hWV' hz, σ'⟩).mp (hgerm z hz)
    obtain ⟨U, hUB, ⟨hzU, hUWzW⟩⟩ :=
      hB.exists_subset_inter Wz hWz W hW z ⟨hzWz, hz⟩
    have hUWz : U ⊆ Wz := fun y hy => (hUWzW hy).1
    have hUW : U ⊆ W := fun y hy => (hUWzW hy).2
    refine ⟨U, hUB, hzU, hUW, ?_⟩
    rw [← F.res_trans hV hWz hUB hWzV hUWz σ, ← F.res_trans hV' hWz hUB hWzV' hUWz σ', hres]
  choose Ufun hUfunB hzUfun hUWfun heqfun using hkey
  have hcov : W ⊆ ⋃ z : (W : Set X), Ufun z := fun y hy =>
    Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hzUfun ⟨y, hy⟩⟩
  refine (hF hW Ufun hUfunB hUWfun hcov).1
    (F.res hV hW hWV σ) (F.res hV' hW hWV' σ') fun z => ?_
  rw [F.res_trans hV hW (hUfunB z) hWV (hUWfun z) σ,
    F.res_trans hV' hW (hUfunB z) hWV' (hUWfun z) σ', heqfun z]

/-! ## The forward direction: range is contained in (*)-families -/

omit [TopologicalSpace X] in
/-- **Forward direction of `germMap_range_eq_conditionStar`.** Any family in
the range of `germMap F hU` satisfies condition (*). -/
lemma germMap_range_subset_conditionStar {B : Set (Set X)} (F : PresheafOnBasisOpenSet B)
    {U : Set X} (hU : U ∈ B) (s : ∀ x : U, Stalk F x.1)
    (h : ∃ t : F.obj U hU, germMap F hU t = s) :
    ConditionStar F s := by
  obtain ⟨t, rfl⟩ := h
  exact fun x => ⟨U, hU, x.2, Set.Subset.refl U, t, fun _ _ => rfl⟩

/-! ## The backward direction: (*)-families are in the range -/

/-- **Backward direction: every `*`-family is in the range of Φ_U.** Given
a family `s` satisfying `ConditionStar`, extract per-point data
`(V_x, σ_x)`. These satisfy the compatibility condition (via
`res_eq_of_local_germ_eq`), so sheaf gluing produces a section `t` whose
germs equal `s`. -/
lemma conditionStar_subset_germMap_range {B : Set (Set X)}
    (hB : IsTopologicalBasis B) (F : PresheafOnBasisOpenSet B) (hF : F.IsSheaf)
    {U : Set X} (hU : U ∈ B) (s : ∀ x : U, Stalk F x.1)
    (h : ConditionStar F s) :
    ∃ t : F.obj U hU, germMap F hU t = s := by
  -- Step 1: Extract per-point data from `ConditionStar`.
  choose V hV hxV hVU σ hgerm using h
  -- Step 2: Verify the cover property.
  have hcov : U ⊆ ⋃ x : ↥U, V x := fun y hy =>
    Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
  -- Step 3: Glue the `σ x`; they are compatible by `res_eq_of_local_germ_eq`.
  obtain ⟨t, ht⟩ := (hF hU V hV hVU hcov).2 σ fun i j W hW hWi hWj =>
    res_eq_of_local_germ_eq hB F hF (hV i) (hV j) hW hWi hWj (σ i) (σ j) fun z hz =>
      (hgerm i z (hWi hz)).symm.trans (hgerm j z (hWj hz))
  -- Step 4: Verify `germMap F hU t = s`. By `germ_res`, the germ of `t` at `x`
  -- equals the germ of its restriction to `V x`; by the gluing data this
  -- restriction is `σ x`; and by condition (*) this germ equals `s x`.
  refine ⟨t, funext fun x => ?_⟩
  have h := germ_res F hU (hV x) (hVU x) (hxV x) t
  rwa [ht x, ← hgerm x x.1 (hxV x)] at h

/-! ## Main statements -/

/-- **Stacks Project 009M, injectivity part.** For any sheaf `F` on a
basis `B`, the germ map `Φ_U` is injective on `F.obj U`. -/
theorem germMap_injective {B : Set (Set X)} (hB : IsTopologicalBasis B)
    (F : PresheafOnBasisOpenSet B) (hF : F.IsSheaf) {U : Set X} (hU : U ∈ B) :
    Function.Injective (germMap F hU) := by
  intro s t hst
  -- Pointwise germ equality gives, for each `x ∈ U`, a witness `W_x ∈ B`
  -- with `x ∈ W_x ⊆ U` on which `s` and `t` restrict equally.
  have hpt : ∀ x : ↥U, ∃ (W : Set X) (hW : W ∈ B) (_ : (x : X) ∈ W)
      (hWU : W ⊆ U), F.res hU hW hWU s = F.res hU hW hWU t := by
    intro x
    obtain ⟨W, hW, hxW, hWU, _, hres⟩ := (germ_eq_iff_rel hB F
      (⟨U, hU, x.2, s⟩ : StalkDatum F x.1) ⟨U, hU, x.2, t⟩).mp (congrFun hst x)
    exact ⟨W, hW, hxW, hWU, hres⟩
  choose W hW hxW hWU hres using hpt
  -- These `W x` cover `U`.
  have hcov : U ⊆ ⋃ x : ↥U, W x := fun y hy =>
    Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩
  -- Sheaf separation now finishes.
  exact (hF hU W hW hWU hcov).1 s t hres

/-- **Stacks Project 009M, image-is-(*) part.** The image of `Φ_U` is
exactly the set of `(*)`-families. -/
theorem germMap_range_eq_conditionStar {B : Set (Set X)}
    (hB : IsTopologicalBasis B) (F : PresheafOnBasisOpenSet B) (hF : F.IsSheaf)
    {U : Set X} (hU : U ∈ B) (s : ∀ x : U, Stalk F x.1) :
    (∃ t : F.obj U hU, germMap F hU t = s) ↔ ConditionStar F s :=
  ⟨germMap_range_subset_conditionStar F hU s, conditionStar_subset_germMap_range hB F hF hU s⟩

/-- **Stacks Project 009M (bijection form).** The germ map `Φ_U` induces
a bijection between `F.obj U hU` and the set of `(*)`-families of germs
over `U`. -/
@[stacks 009M]
theorem germMap_bijection {B : Set (Set X)} (hB : IsTopologicalBasis B)
    (F : PresheafOnBasisOpenSet B) (hF : F.IsSheaf) {U : Set X} (hU : U ∈ B) :
    Function.Bijective
      (fun s : F.obj U hU =>
        (⟨germMap F hU s, by
          rw [← germMap_range_eq_conditionStar hB F hF hU]; exact ⟨s, rfl⟩⟩ :
          {f : ∀ x : U, Stalk F x.1 // ConditionStar F f})) := by
  refine ⟨fun s t hst => germMap_injective hB F hF hU (congrArg Subtype.val hst), ?_⟩
  -- Surjective: any `(*)`-family is in the range of `germMap`.
  rintro ⟨f, hf⟩
  obtain ⟨t, ht⟩ := conditionStar_subset_germMap_range hB F hF hU f hf
  exact ⟨t, Subtype.ext ht⟩

end Stacks.Topology.BasisPresheaf
