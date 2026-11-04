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
# Stacks 009K — Cofinal systems of coverings and the sheaf condition on a basis

Stacks 009K states that a presheaf `F` on a basis `B` for the topology of `X` is a sheaf on `B`
as soon as the sheaf condition `(**)` holds for a *cofinal* system of coverings: a rule assigning
to each `U ∈ B` a set `C U` of coverings of `U` by basis elements such that every covering of `U`
by basis elements is refined by a member of `C U`. This is proved here as `main_theorem009K`, in
the form of an iff; the forward direction is restriction along `C U ⊆ {all coverings}`.

The supporting vocabulary is defined here as well: `BasisCovering` (a family of basis elements
whose union is `U`), `CofinalSystem`, `BasisPresheaf` (a presheaf of sets on `B`),
`IntersectionCoverings` and `GivenIntersectionCoverings` (choices of basis coverings of the
intersections `Uᵢ ⊓ Uⱼ`, which need not themselves lie in `B`), the gluing condition
`SheafConditionStarStar` for one covering, and its two universally quantified forms
`IsSheafOnBasisProp` and `SheafConditionOnCofinalSystem`.

The substance of the proof is in the intermediate lemmas: `separatedness_of_cofinal` extracts
separatedness on *every* basis covering from `(**)` on the cofinal system alone,
`exists_basis_refinement` refines a basis open contained in a union of basis opens by a basis
covering factoring through that union, and `local_to_global_on_subopen`, `pullback_matching`,
`t_eq_s_on_subbasis` and `glued_restricts_to_original` transfer a matching family and its glue
between a covering and a refinement.
-/

@[expose] public section

open TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A *basis covering* of `U ∈ B` is an indexed family of basis elements whose
union equals `U`. -/
structure BasisCovering (B : Set (Opens X)) (U : Opens X) where
  /-- The index type of the covering family. -/
  ι : Type u
  /-- The members of the covering family. -/
  obj : ι → Opens X
  /-- Every member is a basis element. -/
  mem_basis : ∀ i, obj i ∈ B
  /-- The members cover exactly `U`. -/
  isCovering : ⨆ i, obj i = U

namespace BasisCovering

variable {B : Set (Opens X)} {U : Opens X}

/-- Each member of a basis covering is contained in `U`. -/
lemma obj_le (𝒰 : BasisCovering B U) (i : 𝒰.ι) : 𝒰.obj i ≤ U :=
  (le_iSup 𝒰.obj i).trans_eq 𝒰.isCovering

end BasisCovering

/-- A *cofinal system of coverings* assigns to each basis element `U ∈ B` a
collection `C U` of coverings of `U` such that every covering of `U` by basis
elements can be refined by one in `C U`. -/
structure CofinalSystem (B : Set (Opens X)) where
  /-- The distinguished coverings of each basis element. -/
  cov : ∀ U : Opens X, U ∈ B → Set (BasisCovering B U)
  /-- Every basis covering of `U` is refined by a distinguished one. -/
  cofinal : ∀ (U : Opens X) (hU : U ∈ B) (𝒰 : BasisCovering B U),
    ∃ 𝒱 ∈ cov U hU, ∃ r : 𝒱.ι → 𝒰.ι, ∀ j, 𝒱.obj j ≤ 𝒰.obj (r j)

/-- A *presheaf of sets on the basis `B`*. -/
@[ega "0 3.2.1" "special case"]
structure BasisPresheaf (B : Set (Opens X)) where
  /-- The type of sections over each basis element. -/
  obj : ∀ U : Opens X, U ∈ B → Type u
  /-- The restriction map along an inclusion `V ≤ U` of basis elements. -/
  restrict : ∀ {U V : Opens X} (hU : U ∈ B) (hV : V ∈ B) (_ : V ≤ U),
    obj U hU → obj V hV
  /-- Restriction along the identity is the identity. -/
  restrict_id : ∀ (U : Opens X) (hU : U ∈ B) (s : obj U hU),
    restrict hU hU le_rfl s = s
  /-- Restriction is compatible with composition of inclusions. -/
  restrict_comp : ∀ {U V W : Opens X} (hU : U ∈ B) (hV : V ∈ B) (hW : W ∈ B)
      (hVU : V ≤ U) (hWV : W ≤ V) (s : obj U hU),
    restrict hV hW hWV (restrict hU hV hVU s) = restrict hU hW (hWV.trans hVU) s

/-- For a basis covering `𝒰 : U = ⋃ U_i`, a choice of intersection coverings
provides, for each pair `(i,j)`, a covering of `U_i ⊓ U_j` by basis elements. -/
structure IntersectionCoverings (B : Set (Opens X)) {U : Opens X}
    (𝒰 : BasisCovering B U) where
  /-- The index type of the covering of `U_i ⊓ U_j`. -/
  idx : 𝒰.ι → 𝒰.ι → Type u
  /-- The members of the covering of `U_i ⊓ U_j`. -/
  obj : ∀ i j, idx i j → Opens X
  /-- Every member is a basis element. -/
  mem_basis : ∀ i j (k : idx i j), obj i j k ∈ B
  /-- Every member is contained in `U_i`. -/
  le_left : ∀ i j (k : idx i j), obj i j k ≤ 𝒰.obj i
  /-- Every member is contained in `U_j`. -/
  le_right : ∀ i j (k : idx i j), obj i j k ≤ 𝒰.obj j
  /-- The members cover exactly `U_i ⊓ U_j`. -/
  isCovering : ∀ i j, ⨆ k, obj i j k = 𝒰.obj i ⊓ 𝒰.obj j

/-- The sheaf condition `(**)`: a matching family on `𝒰` glues to a *unique*
section over `U`. -/
def SheafConditionStarStar {B : Set (Opens X)} (F : BasisPresheaf B)
    {U : Opens X} (hU : U ∈ B) (𝒰 : BasisCovering B U)
    (𝒰ij : IntersectionCoverings B 𝒰) : Prop :=
  ∀ s : ∀ i, F.obj (𝒰.obj i) (𝒰.mem_basis i),
    (∀ i j (k : 𝒰ij.idx i j),
        F.restrict (𝒰.mem_basis i) (𝒰ij.mem_basis i j k) (𝒰ij.le_left i j k)
            (s i) =
          F.restrict (𝒰.mem_basis j) (𝒰ij.mem_basis i j k) (𝒰ij.le_right i j k)
            (s j)) →
    ∃! t : F.obj U hU,
      ∀ i, F.restrict hU (𝒰.mem_basis i) (𝒰.obj_le i) t = s i

/-- A choice of intersection coverings for every basis covering of every
basis element. -/
structure GivenIntersectionCoverings (B : Set (Opens X)) where
  /-- The chosen intersection coverings for each basis covering. -/
  ij : ∀ (U : Opens X) (_ : U ∈ B) (𝒰 : BasisCovering B U),
    IntersectionCoverings B 𝒰

/-- A presheaf `F` on `B` is a *sheaf on `B`*. -/
@[ega "0 3.2.2", sga "4½ Arcata 1.2.3" "more general"]
def IsSheafOnBasisProp {B : Set (Opens X)} (F : BasisPresheaf B)
    (all : GivenIntersectionCoverings B) : Prop :=
  ∀ (U : Opens X) (hU : U ∈ B) (𝒰 : BasisCovering B U),
    SheafConditionStarStar F hU 𝒰 (all.ij U hU 𝒰)

/-- Condition (2): the sheaf condition holds for every cover in the cofinal system. -/
def SheafConditionOnCofinalSystem {B : Set (Opens X)} (F : BasisPresheaf B)
    (C : CofinalSystem B) (all : GivenIntersectionCoverings B) : Prop :=
  ∀ (U : Opens X) (hU : U ∈ B) (𝒰 : BasisCovering B U)
    (_ : 𝒰 ∈ C.cov U hU),
    SheafConditionStarStar F hU 𝒰 (all.ij U hU 𝒰)

/-- **Separatedness from `(**)` on a cofinal system.** Two sections of `F` over
`V` that agree on every member of a basis cover `𝒲` are equal. -/
lemma separatedness_of_cofinal
    {B : Set (Opens X)}
    (C : CofinalSystem B) (all : GivenIntersectionCoverings B)
    (F : BasisPresheaf B) (hC : SheafConditionOnCofinalSystem F C all)
    {V : Opens X} (hV : V ∈ B) (𝒲 : BasisCovering B V)
    (t₁ t₂ : F.obj V hV)
    (h : ∀ j, F.restrict hV (𝒲.mem_basis j) (𝒲.obj_le j) t₁
            = F.restrict hV (𝒲.mem_basis j) (𝒲.obj_le j) t₂) :
    t₁ = t₂ := by
  obtain ⟨𝒲', h𝒲', r, hr⟩ := C.cofinal V hV 𝒲
  -- The matching family on `𝒲'` obtained by restricting `t₁`.
  set s : ∀ j', F.obj (𝒲'.obj j') (𝒲'.mem_basis j') :=
    fun j' => F.restrict hV (𝒲'.mem_basis j') (𝒲'.obj_le j') t₁ with hs_def
  have hmatching : ∀ i' j' (k : (all.ij V hV 𝒲').idx i' j'),
      F.restrict (𝒲'.mem_basis i') ((all.ij V hV 𝒲').mem_basis i' j' k)
          ((all.ij V hV 𝒲').le_left i' j' k) (s i')
      = F.restrict (𝒲'.mem_basis j') ((all.ij V hV 𝒲').mem_basis i' j' k)
          ((all.ij V hV 𝒲').le_right i' j' k) (s j') := fun i' j' k => by
    simp [hs_def, F.restrict_comp]
  obtain ⟨_, _, htU⟩ := hC V hV 𝒲' h𝒲' s hmatching
  refine (htU t₁ fun _ => rfl).trans (htU t₂ fun j' => ?_).symm
  simp only [hs_def]
  rw [← F.restrict_comp hV (𝒲.mem_basis (r j')) (𝒲'.mem_basis j')
        (𝒲.obj_le (r j')) (hr j') t₂,
      ← F.restrict_comp hV (𝒲.mem_basis (r j')) (𝒲'.mem_basis j')
        (𝒲.obj_le (r j')) (hr j') t₁,
      h (r j')]

/-- **Refinement of a covering by basis elements.** If `W ∈ B` is contained in
`⨆ k, D k` with each `D k ∈ B`, then there is a basis cover of `W` factoring
through `D`. -/
lemma exists_basis_refinement
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {W : Opens X}
    {κ : Type u} (D : κ → Opens X)
    (hWcov : W ≤ ⨆ k, D k) :
    ∃ 𝒲 : BasisCovering B W, ∃ r : 𝒲.ι → κ, ∀ j, 𝒲.obj j ≤ D (r j) := by
  classical
  have key : ∀ x : X, x ∈ W →
      ∃ k : κ, ∃ E : Opens X, E ∈ B ∧ x ∈ E ∧ E ≤ W ⊓ D k := by
    intro x hx
    obtain ⟨k, hxk⟩ := Opens.mem_iSup.mp (hWcov hx)
    obtain ⟨E, hEmem, hxE, hEle⟩ :=
      Opens.isBasis_iff_nbhd.mp hB (show x ∈ W ⊓ D k from ⟨hx, hxk⟩)
    exact ⟨k, E, hEmem, hxE, hEle⟩
  choose kfun Efun hEmem hxE hEle using key
  refine ⟨{ ι := {x : X // x ∈ W}
            obj := fun p => Efun p.1 p.2
            mem_basis := fun p => hEmem p.1 p.2
            isCovering := ?_ }, fun p => kfun p.1 p.2,
          fun p => (hEle p.1 p.2).trans inf_le_right⟩
  apply le_antisymm
  · refine iSup_le ?_
    rintro ⟨x, hx⟩
    exact (hEle x hx).trans inf_le_left
  · intro y hy
    rw [Opens.mem_iSup]
    exact ⟨⟨y, hy⟩, hxE y hy⟩

/-- **Local-to-global on a basis sub-open.** Two sections `a`, `b` agreeing on
each member of an arbitrary basis cover `D` of `A1 ⊓ A2` also agree when
restricted to any basis open `W ⊆ A1 ⊓ A2`. -/
lemma local_to_global_on_subopen
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (C : CofinalSystem B) (all : GivenIntersectionCoverings B)
    (F : BasisPresheaf B) (hC : SheafConditionOnCofinalSystem F C all)
    {A1 A2 : Opens X} (hA1 : A1 ∈ B) (hA2 : A2 ∈ B)
    (a : F.obj A1 hA1) (b : F.obj A2 hA2)
    (κ : Type u) (D : κ → Opens X) (hD : ∀ k, D k ∈ B)
    (hD_le_left : ∀ k, D k ≤ A1) (hD_le_right : ∀ k, D k ≤ A2)
    (hD_cov : ⨆ k, D k = A1 ⊓ A2)
    (hagree : ∀ k, F.restrict hA1 (hD k) (hD_le_left k) a
                 = F.restrict hA2 (hD k) (hD_le_right k) b)
    {W : Opens X} (hW : W ∈ B) (hW_le_left : W ≤ A1) (hW_le_right : W ≤ A2) :
    F.restrict hA1 hW hW_le_left a = F.restrict hA2 hW hW_le_right b := by
  have hWcov : W ≤ ⨆ k, D k := hD_cov ▸ le_inf hW_le_left hW_le_right
  obtain ⟨𝒲, r, hr⟩ := exists_basis_refinement hB D hWcov
  apply separatedness_of_cofinal C all F hC hW 𝒲
  intro j
  rw [F.restrict_comp hA1 hW (𝒲.mem_basis j) hW_le_left (𝒲.obj_le j) a,
      F.restrict_comp hA2 hW (𝒲.mem_basis j) hW_le_right (𝒲.obj_le j) b,
      ← F.restrict_comp hA1 (hD (r j)) (𝒲.mem_basis j) (hD_le_left (r j)) (hr j) a,
      ← F.restrict_comp hA2 (hD (r j)) (𝒲.mem_basis j) (hD_le_right (r j)) (hr j) b,
      hagree (r j)]

/-- A matching family on `𝒰` agrees on any basis open contained in two of its members. -/
private lemma restrict_eq_of_matching
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (C : CofinalSystem B) (all : GivenIntersectionCoverings B)
    (F : BasisPresheaf B) (hC : SheafConditionOnCofinalSystem F C all)
    {U : Opens X} (hU : U ∈ B) (𝒰 : BasisCovering B U)
    (s : ∀ i, F.obj (𝒰.obj i) (𝒰.mem_basis i))
    (hs : ∀ i j (k : (all.ij U hU 𝒰).idx i j),
        F.restrict (𝒰.mem_basis i) ((all.ij U hU 𝒰).mem_basis i j k)
            ((all.ij U hU 𝒰).le_left i j k) (s i) =
          F.restrict (𝒰.mem_basis j) ((all.ij U hU 𝒰).mem_basis i j k)
            ((all.ij U hU 𝒰).le_right i j k) (s j))
    (i j : 𝒰.ι) {W : Opens X} (hW : W ∈ B) (hWi : W ≤ 𝒰.obj i) (hWj : W ≤ 𝒰.obj j) :
    F.restrict (𝒰.mem_basis i) hW hWi (s i) = F.restrict (𝒰.mem_basis j) hW hWj (s j) :=
  local_to_global_on_subopen hB C all F hC
    (𝒰.mem_basis i) (𝒰.mem_basis j) (s i) (s j) _ _
    ((all.ij U hU 𝒰).mem_basis i j) ((all.ij U hU 𝒰).le_left i j)
    ((all.ij U hU 𝒰).le_right i j) ((all.ij U hU 𝒰).isCovering i j) (hs i j) hW hWi hWj

/-- **Pullback matching.** A matching family on `𝒰` restricts to a matching
family on a refinement `𝒱`. -/
lemma pullback_matching
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (C : CofinalSystem B) (all : GivenIntersectionCoverings B)
    (F : BasisPresheaf B) (hC : SheafConditionOnCofinalSystem F C all)
    {U : Opens X} (hU : U ∈ B) (𝒰 : BasisCovering B U)
    (s : ∀ i, F.obj (𝒰.obj i) (𝒰.mem_basis i))
    (hs : ∀ i j (k : (all.ij U hU 𝒰).idx i j),
        F.restrict (𝒰.mem_basis i) ((all.ij U hU 𝒰).mem_basis i j k)
            ((all.ij U hU 𝒰).le_left i j k) (s i) =
          F.restrict (𝒰.mem_basis j) ((all.ij U hU 𝒰).mem_basis i j k)
            ((all.ij U hU 𝒰).le_right i j k) (s j))
    (𝒱 : BasisCovering B U) (r : 𝒱.ι → 𝒰.ι)
    (hr : ∀ j, 𝒱.obj j ≤ 𝒰.obj (r j)) :
    ∀ j₁ j₂ (k : (all.ij U hU 𝒱).idx j₁ j₂),
      F.restrict (𝒱.mem_basis j₁) ((all.ij U hU 𝒱).mem_basis j₁ j₂ k)
          ((all.ij U hU 𝒱).le_left j₁ j₂ k)
          (F.restrict (𝒰.mem_basis (r j₁)) (𝒱.mem_basis j₁) (hr j₁) (s (r j₁)))
      = F.restrict (𝒱.mem_basis j₂) ((all.ij U hU 𝒱).mem_basis j₁ j₂ k)
          ((all.ij U hU 𝒱).le_right j₁ j₂ k)
          (F.restrict (𝒰.mem_basis (r j₂)) (𝒱.mem_basis j₂) (hr j₂) (s (r j₂))) := by
  intro j₁ j₂ k
  have hWmem := (all.ij U hU 𝒱).mem_basis j₁ j₂ k
  rw [F.restrict_comp (𝒰.mem_basis (r j₁)) (𝒱.mem_basis j₁) hWmem (hr j₁)
        ((all.ij U hU 𝒱).le_left j₁ j₂ k) (s (r j₁)),
      F.restrict_comp (𝒰.mem_basis (r j₂)) (𝒱.mem_basis j₂) hWmem (hr j₂)
        ((all.ij U hU 𝒱).le_right j₁ j₂ k) (s (r j₂))]
  exact restrict_eq_of_matching hB C all F hC hU 𝒰 s hs (r j₁) (r j₂) hWmem _ _

/-- **Pointwise equality of `t` and `s i` on a basis sub-open.** -/
lemma t_eq_s_on_subbasis
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (C : CofinalSystem B) (all : GivenIntersectionCoverings B)
    (F : BasisPresheaf B) (hC : SheafConditionOnCofinalSystem F C all)
    {U : Opens X} (hU : U ∈ B) (𝒰 : BasisCovering B U)
    (s : ∀ i, F.obj (𝒰.obj i) (𝒰.mem_basis i))
    (hs : ∀ i j (k : (all.ij U hU 𝒰).idx i j),
        F.restrict (𝒰.mem_basis i) ((all.ij U hU 𝒰).mem_basis i j k)
            ((all.ij U hU 𝒰).le_left i j k) (s i) =
          F.restrict (𝒰.mem_basis j) ((all.ij U hU 𝒰).mem_basis i j k)
            ((all.ij U hU 𝒰).le_right i j k) (s j))
    (𝒱 : BasisCovering B U) (r : 𝒱.ι → 𝒰.ι)
    (hr : ∀ j, 𝒱.obj j ≤ 𝒰.obj (r j))
    (t : F.obj U hU)
    (ht : ∀ j, F.restrict hU (𝒱.mem_basis j) (𝒱.obj_le j) t =
              F.restrict (𝒰.mem_basis (r j)) (𝒱.mem_basis j) (hr j) (s (r j)))
    (i : 𝒰.ι) (j : 𝒱.ι)
    {W : Opens X} (hW : W ∈ B) (hW_le_𝒰i : W ≤ 𝒰.obj i) (hW_le_𝒱j : W ≤ 𝒱.obj j) :
    F.restrict hU hW (hW_le_𝒰i.trans (𝒰.obj_le i)) t =
      F.restrict (𝒰.mem_basis i) hW hW_le_𝒰i (s i) := by
  have step1 : F.restrict hU hW (hW_le_𝒰i.trans (𝒰.obj_le i)) t =
               F.restrict (𝒰.mem_basis (r j)) hW (hW_le_𝒱j.trans (hr j)) (s (r j)) := by
    have key := congr_arg (F.restrict (𝒱.mem_basis j) hW hW_le_𝒱j) (ht j)
    rwa [F.restrict_comp hU (𝒱.mem_basis j) hW (𝒱.obj_le j) hW_le_𝒱j t,
         F.restrict_comp (𝒰.mem_basis (r j)) (𝒱.mem_basis j) hW (hr j) hW_le_𝒱j (s (r j))]
      at key
  exact step1.trans (restrict_eq_of_matching hB C all F hC hU 𝒰 s hs (r j) i hW _ hW_le_𝒰i)

/-- **The glued section restricts to the original.** -/
lemma glued_restricts_to_original
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (C : CofinalSystem B) (all : GivenIntersectionCoverings B)
    (F : BasisPresheaf B) (hC : SheafConditionOnCofinalSystem F C all)
    {U : Opens X} (hU : U ∈ B) (𝒰 : BasisCovering B U)
    (s : ∀ i, F.obj (𝒰.obj i) (𝒰.mem_basis i))
    (hs : ∀ i j (k : (all.ij U hU 𝒰).idx i j),
        F.restrict (𝒰.mem_basis i) ((all.ij U hU 𝒰).mem_basis i j k)
            ((all.ij U hU 𝒰).le_left i j k) (s i) =
          F.restrict (𝒰.mem_basis j) ((all.ij U hU 𝒰).mem_basis i j k)
            ((all.ij U hU 𝒰).le_right i j k) (s j))
    (𝒱 : BasisCovering B U) (r : 𝒱.ι → 𝒰.ι)
    (hr : ∀ j, 𝒱.obj j ≤ 𝒰.obj (r j))
    (t : F.obj U hU)
    (ht : ∀ j, F.restrict hU (𝒱.mem_basis j) (𝒱.obj_le j) t =
              F.restrict (𝒰.mem_basis (r j)) (𝒱.mem_basis j) (hr j) (s (r j))) :
    ∀ i, F.restrict hU (𝒰.mem_basis i) (𝒰.obj_le i) t = s i := by
  intro i
  obtain ⟨𝒲, j_of, h𝒲⟩ :=
    exists_basis_refinement hB 𝒱.obj
      ((𝒰.obj_le i).trans_eq 𝒱.isCovering.symm)
  refine separatedness_of_cofinal C all F hC (𝒰.mem_basis i) 𝒲
    (F.restrict hU (𝒰.mem_basis i) (𝒰.obj_le i) t) (s i) fun m => ?_
  rw [F.restrict_comp hU (𝒰.mem_basis i) (𝒲.mem_basis m) (𝒰.obj_le i) (𝒲.obj_le m)]
  exact t_eq_s_on_subbasis hB C all F hC hU 𝒰 s hs 𝒱 r hr t ht i (j_of m)
    (𝒲.mem_basis m) (𝒲.obj_le m) (h𝒲 m)

/-- **Backward direction.** The sheaf condition on a cofinal system implies the
sheaf condition on the entire basis. -/
lemma sheafCondition_cofinal_implies_basis
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (C : CofinalSystem B)
    (all : GivenIntersectionCoverings B)
    (F : BasisPresheaf B)
    (hC : SheafConditionOnCofinalSystem F C all) :
    IsSheafOnBasisProp F all := by
  intro U hU 𝒰 s hs_match
  obtain ⟨𝒱, h𝒱, r, hr⟩ := C.cofinal U hU 𝒰
  let s' : ∀ j, F.obj (𝒱.obj j) (𝒱.mem_basis j) :=
    fun j => F.restrict (𝒰.mem_basis (r j)) (𝒱.mem_basis j) (hr j) (s (r j))
  obtain ⟨t, ht, _⟩ :=
    hC U hU 𝒱 h𝒱 s' (pullback_matching hB C all F hC hU 𝒰 s hs_match 𝒱 r hr)
  have ht_orig : ∀ i, F.restrict hU (𝒰.mem_basis i) (𝒰.obj_le i) t = s i :=
    glued_restricts_to_original hB C all F hC hU 𝒰 s hs_match 𝒱 r hr t ht
  refine ⟨t, ht_orig, fun t' ht' => ?_⟩
  apply separatedness_of_cofinal C all F hC hU 𝒰
  intro i
  rw [ht' i, ht_orig i]

/-- **Stacks Tag 009K (lemma-cofinal-systems-coverings).** A presheaf on a
basis is a sheaf iff the sheaf condition holds on a cofinal system of
coverings. -/
@[stacks 009K]
theorem main_theorem009K
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (C : CofinalSystem B)
    (all : GivenIntersectionCoverings B)
    (F : BasisPresheaf B) :
    IsSheafOnBasisProp F all ↔ SheafConditionOnCofinalSystem F C all :=
  ⟨fun h U hU 𝒰 _ => h U hU 𝒰,
   sheafCondition_cofinal_implies_basis hB C all F⟩

