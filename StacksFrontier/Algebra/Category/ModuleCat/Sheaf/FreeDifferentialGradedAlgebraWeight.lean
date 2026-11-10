module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.WellFounded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedAlgebraTriangular

/-!
# The weight of a word, and the differential lowers it

Let `(C, O)` be a ringed site and let `𝒮 : I → SheafOfGradedSets J` be a family of sheaves of
graded sets indexed by a linearly ordered set of *levels*. The **weight** of a word `s₁ ⋯ s_r` in
the letters of the family is the finitely supported function `I →₀ ℕ` counting, for each level
`j`, the letters of level `j`. Weights are ordered **colexicographically**: `w < w'` when at the
largest level where they differ `w` is smaller. This is the source's order on `ℤ_{≥0}^{i+1}` in
the proof of Tag 0FU1, extended to an arbitrary well-ordered set of levels; for a well-ordered `I`
it is a well-order.

The source's observation is that **the differential strictly lowers the weight** when the
derivation datum is triangular: in each term of
`d(s₁ ⋯ s_r) = Σ ± s₁ ⋯ δ(s_a) ⋯ s_r` the letter `s_a` of level `j` is replaced by a combination
of words in letters of level `< j`. Since local sections of `O⟨S⟩` are only locally images of the
presentation, the statement is local: `SheafOfModules.IsLocallyIn D z` says that `z` is locally
the image of a presentation element all of whose words have weight in `D`.

## Main definitions

* `Stacks.SheafOfGradedSets.wordWt`: the weight of a word.
* `SheafOfModules.IsPresIn D a` and `SheafOfModules.IsLocallyIn D z`.

## Main results

* `SheafOfModules.wordD_isLocallyIn`: the Leibniz extension of a triangular derivation datum on
  a word of weight `w` is locally a combination of words of weight `< w`.
* `SheafOfModules.algD_isLocallyIn`: the same for the differential on a presentation element.

## References

* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe t v u

namespace Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type t)] {I : Type t} {𝒮 : I → SheafOfGradedSets.{t} J}

/-- The **weight** of a word: for each level `j`, the number of its letters of level `j`. -/
noncomputable def wordWt {U : Cᵒᵖ} (w : Word 𝒮 U) : I →₀ ℕ :=
  (w.map fun x => Finsupp.single x.1 1).sum

/-- The empty word has weight zero. -/
@[simp] theorem wordWt_nil {U : Cᵒᵖ} : wordWt ([] : Word 𝒮 U) = 0 := rfl

/-- Prepending a letter of level `j` adds one at level `j` to the weight. -/
@[simp] theorem wordWt_cons {U : Cᵒᵖ} (x : Letter 𝒮 U) (w : Word 𝒮 U) :
    wordWt (x :: w : Word 𝒮 U) = Finsupp.single x.1 1 + wordWt w := by
  simp [wordWt]

/-- The weight of a concatenation is the sum of the weights. -/
@[simp] theorem wordWt_append {U : Cᵒᵖ} (w w' : Word 𝒮 U) :
    wordWt (w ++ w' : Word 𝒮 U) = wordWt w + wordWt w' := by
  simp [wordWt]

/-- Restricting a word along a morphism does not change its weight. -/
@[simp] theorem wordWt_wordMap {U V : Cᵒᵖ} (f : U ⟶ V) (w : Word 𝒮 U) :
    wordWt (wordMap f w) = wordWt w := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [wordMap_cons, wordWt_cons, wordWt_cons, ih, letterMap_fst]

/-- A word in letters of level `< k` has its weight supported on levels `< k`. -/
theorem wordWt_support_lt_of_wordBelow [LT I] {k : I} {U : Cᵒᵖ} {w : Word 𝒮 U}
    (hw : WordBelow k w) : ∀ j ∈ (wordWt w).support, j < k := by
  classical
  induction w with
  | nil => intro j hj; simp at hj
  | cons x w ih =>
    intro j hj
    rw [wordBelow_cons] at hw
    rw [wordWt_cons] at hj
    rcases Finset.mem_union.mp (Finsupp.support_add hj) with h | h
    · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at h
      exact h ▸ hw.1
    · exact ih hw.2 j h

end Stacks.SheafOfGradedSets

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

section Order

variable {I : Type*} [LinearOrder I]

/-- **The colexicographic order of weights is translation invariant.** -/
theorem wt_add_lt_add_left {a b : I →₀ ℕ} (c : I →₀ ℕ) (h : toColex a < toColex b) :
    toColex (c + a) < toColex (c + b) :=
  add_lt_add_right h (toColex c)

/-- Adding a weight on the right preserves the strict colexicographic order of weights. -/
theorem wt_add_lt_add_right {a b : I →₀ ℕ} (c : I →₀ ℕ) (h : toColex a < toColex b) :
    toColex (a + c) < toColex (b + c) := by
  rw [add_comm a, add_comm b]
  exact wt_add_lt_add_left c h

/-- A weight supported on levels `< k` is smaller than the weight of a single letter of level
`k`. -/
theorem wt_lt_single_of_support {b : I →₀ ℕ} {k : I} (hb : ∀ j ∈ b.support, j < k) :
    toColex b < toColex (Finsupp.single k 1) := by
  refine Finsupp.Colex.lt_iff.mpr ⟨k, fun j hj => ?_, ?_⟩
  · have hj' : j ∉ b.support := fun h => absurd (hb j h) (not_lt.mpr hj.le)
    change b j = Finsupp.single k 1 j
    rw [Finsupp.notMem_support_iff.mp hj', Finsupp.single_eq_of_ne hj.ne']
  · have hk : k ∉ b.support := fun h => lt_irrefl k (hb k h)
    change b k < Finsupp.single k 1 k
    rw [Finsupp.notMem_support_iff.mp hk, Finsupp.single_eq_same]
    exact Nat.one_pos

end Order

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)] [HasWeakSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {I : Type t} {𝒮 : I → SheafOfGradedSets.{t} J}

/-! ### Presentation elements of prescribed weights -/

variable (𝒮) in
/-- A presentation element **has weights in `D`** when every word of its support has weight in
`D`. -/
def IsPresIn (D : Set (I →₀ ℕ)) {n : ℤ} {U : Cᵒᵖ} (a : algSections Osharp 𝒮 n U) : Prop :=
  ∀ w ∈ a.support, wordWt w.1 ∈ D

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- A presentation element has weights in `D` if and only if it is supported on the words of
weight in `D`. -/
theorem isPresIn_iff_mem_supported (D : Set (I →₀ ℕ)) {n : ℤ} {U : Cᵒᵖ}
    (a : algSections Osharp 𝒮 n U) :
    IsPresIn 𝒮 D a ↔ a ∈ Finsupp.supported (secRing Osharp U) (secRing Osharp U)
      {w : WordIdx 𝒮 n U | wordWt w.1 ∈ D} := by
  rw [Finsupp.mem_supported]
  exact ⟨fun h w hw => h w hw, fun h w hw => h hw⟩

namespace IsPresIn

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- The zero presentation element has weights in every set. -/
theorem zero (D : Set (I →₀ ℕ)) {n : ℤ} {U : Cᵒᵖ} :
    IsPresIn 𝒮 D (0 : algSections Osharp 𝒮 n U) := by
  intro w hw
  simp at hw

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- A sum of presentation elements with weights in `D` has weights in `D`. -/
theorem add {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ} {a b : algSections Osharp 𝒮 n U}
    (ha : IsPresIn 𝒮 D a) (hb : IsPresIn 𝒮 D b) : IsPresIn 𝒮 D (a + b) := by
  rw [isPresIn_iff_mem_supported] at ha hb ⊢
  exact Submodule.add_mem _ ha hb

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- A scalar multiple of a presentation element with weights in `D` has weights in `D`. -/
theorem smul {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ} (r : secRing Osharp U)
    {a : algSections Osharp 𝒮 n U} (ha : IsPresIn 𝒮 D a) : IsPresIn 𝒮 D (r • a) := by
  rw [isPresIn_iff_mem_supported] at ha ⊢
  exact Submodule.smul_mem _ r ha

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- Having weights in `D` is monotone in `D`. -/
theorem mono {D E : Set (I →₀ ℕ)} (hDE : D ⊆ E) {n : ℤ} {U : Cᵒᵖ}
    {a : algSections Osharp 𝒮 n U} (ha : IsPresIn 𝒮 D a) : IsPresIn 𝒮 E a :=
  fun w hw => hDE (ha w hw)

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- A multiple of a single word of weight in `D` has weights in `D`. -/
theorem algOf {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ} (w : WordIdx 𝒮 n U)
    (hw : wordWt w.1 ∈ D) (r : secRing Osharp U) :
    IsPresIn 𝒮 D (SheafOfModules.algOf (Osharp := Osharp) 𝒮 n w r) := by
  classical
  intro w' hw'
  rw [SheafOfModules.algOf, Finsupp.mem_support_iff, Finsupp.single_apply] at hw'
  by_cases h : w = w'
  · exact h ▸ hw
  · exact absurd (ite_eq_right h) hw'

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- A finite sum of presentation elements with weights in `D` has weights in `D`. -/
theorem sum {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ} {ι : Type*} (s : Finset ι)
    (a : ι → algSections Osharp 𝒮 n U) (ha : ∀ i ∈ s, IsPresIn 𝒮 D (a i)) :
    IsPresIn 𝒮 D (∑ i ∈ s, a i) := by
  rw [isPresIn_iff_mem_supported]
  exact Submodule.sum_mem _ fun i hi => (isPresIn_iff_mem_supported D (a i)).mp (ha i hi)

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- A presentation element is the sum of the summands of its support. -/
theorem eq_sum {n : ℤ} {U : Cᵒᵖ} (a : algSections Osharp 𝒮 n U) :
    a = ∑ w ∈ a.support, SheafOfModules.algOf (Osharp := Osharp) 𝒮 n w (a w) :=
  (Finsupp.sum_single a).symm

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- The restriction of a presentation element with weights in `D` has weights in `D`. -/
theorem algRestrict {D : Set (I →₀ ℕ)} {n : ℤ} {U V : Cᵒᵖ} (f : U ⟶ V)
    {a : algSections Osharp 𝒮 n U} (ha : IsPresIn 𝒮 D a) :
    IsPresIn 𝒮 D (SheafOfModules.algRestrict 𝒮 n f a) := by
  rw [eq_sum a, map_sum]
  refine sum _ _ fun w hw => ?_
  rw [algRestrict_algOf]
  exact algOf _ ((wordWt_wordMap f w.1).symm ▸ ha w hw) _

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- Transporting a presentation element along an equality of degrees preserves its weights. -/
theorem algCast {D : Set (I →₀ ℕ)} {n n' : ℤ} (h : n = n') {U : Cᵒᵖ}
    {a : algSections Osharp 𝒮 n U} (ha : IsPresIn 𝒮 D a) :
    IsPresIn 𝒮 D (SheafOfModules.algCast 𝒮 h U a) := by
  subst h
  exact ha

/-- The sum set of two sets of weights. -/
def addSet (D E : Set (I →₀ ℕ)) : Set (I →₀ ℕ) := {x | ∃ a ∈ D, ∃ b ∈ E, x = a + b}

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- The product of presentation elements with weights in `D` and in `E` has weights in `D + E`. -/
theorem mulAdd {D E : Set (I →₀ ℕ)} {n i : ℤ} {U : Cᵒᵖ} {a : algSections Osharp 𝒮 n U}
    {b : algSections Osharp 𝒮 i U} (ha : IsPresIn 𝒮 D a) (hb : IsPresIn 𝒮 E b) :
    IsPresIn 𝒮 (addSet D E) (SheafOfModules.mulAdd 𝒮 n i U a b) := by
  rw [eq_sum a, map_sum, AddMonoidHom.finsetSum_apply]
  refine sum _ _ fun w hw => ?_
  rw [eq_sum b, map_sum]
  refine sum _ _ fun w' hw' => ?_
  rw [mulAdd_algOf]
  exact algOf _ (show wordWt (w.1 ++ w'.1) ∈ addSet D E from
    ⟨_, ha w hw, _, hb w' hw', wordWt_append _ _⟩) _

end IsPresIn

/-! ### Local sections of prescribed weights -/

variable (𝒮) in
/-- A local section `z` of the degree-`n` piece of `O⟨S⟩` **is locally of weights in `D`** when,
locally on the site, it is the image of a presentation element with weights in `D`. -/
def IsLocallyIn (D : Set (I →₀ ℕ)) {n : ℤ} {U : Cᵒᵖ}
    (z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) : Prop :=
  ∃ S : Sieve U.unop, S ∈ J U.unop ∧ ∀ ⦃V : C⦄ (f : V ⟶ U.unop), S f →
    ∃ a : algSections Osharp 𝒮 n (op V), IsPresIn 𝒮 D a ∧
      (algToSheaf 𝒮 n).app (op V) a = Stacks.sectionRestrict (algPiece 𝒮 n).val f.op z

/-- The image of a presentation element with weights in `D` is locally of weights in `D`. -/
theorem isLocallyIn_algToSheaf {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ}
    {a : algSections Osharp 𝒮 n U} (ha : IsPresIn 𝒮 D a) :
    IsLocallyIn 𝒮 D ((algToSheaf 𝒮 n).app U a) :=
  ⟨⊤, J.top_mem _, fun _ f _ => ⟨SheafOfModules.algRestrict 𝒮 n f.op a, ha.algRestrict f.op,
    (algToSheaf_naturality 𝒮 n f.op a).symm⟩⟩

namespace IsLocallyIn

/-- The zero section is locally of weights in every set. -/
theorem zero (D : Set (I →₀ ℕ)) {n : ℤ} {U : Cᵒᵖ} :
    IsLocallyIn 𝒮 D (0 : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) := by
  have h := isLocallyIn_algToSheaf (U := U) (IsPresIn.zero (Osharp := Osharp) (𝒮 := 𝒮) D (n := n))
  rwa [← algToSheafAdd_apply, map_zero] at h

/-- A sum of local sections locally of weights in `D` is locally of weights in `D`. -/
theorem add {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ}
    {z z' : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U}
    (hz : IsLocallyIn 𝒮 D z) (hz' : IsLocallyIn 𝒮 D z') : IsLocallyIn 𝒮 D (z + z') := by
  obtain ⟨S, hS, h⟩ := hz
  obtain ⟨S', hS', h'⟩ := hz'
  refine ⟨S ⊓ S', J.intersection_covering hS hS', fun V f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := h f hf.1
  obtain ⟨a', ha', hfa'⟩ := h' f hf.2
  refine ⟨a + a', ha.add ha', ?_⟩
  refine (map_add (algToSheafAdd 𝒮 n (op V)) a a').trans ?_
  rw [algToSheafAdd_apply, algToSheafAdd_apply, hfa, hfa']
  exact (map_add _ z z').symm

/-- A scalar multiple of a local section locally of weights in `D` is locally of weights in `D`. -/
theorem smul {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ} (r : secRing Osharp U)
    {z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U} (hz : IsLocallyIn 𝒮 D z) :
    IsLocallyIn 𝒮 D (r • z) := by
  obtain ⟨S, hS, h⟩ := hz
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := h f hf
  refine ⟨(toRingCat J Osharp).obj.map f.op r • a, ha.smul _, ?_⟩
  refine (((algToSheaf 𝒮 n).app (op V)).hom.map_smul _ a).trans ?_
  refine (congrArg (fun y => (toRingCat J Osharp).obj.map f.op r • y) hfa).trans ?_
  exact (Stacks.sectionRestrict_smul (algPiece (Osharp := Osharp) 𝒮 n).val f.op r z).symm

/-- An integer multiple of a local section locally of weights in `D` is locally of weights in
`D`. -/
theorem zsmul {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ} (m : ℤ)
    {z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U} (hz : IsLocallyIn 𝒮 D z) :
    IsLocallyIn 𝒮 D (m • z) := by
  rw [← Int.cast_smul_eq_zsmul (secRing Osharp U)]
  exact hz.smul _

/-- A finite sum of local sections locally of weights in `D` is locally of weights in `D`. -/
theorem sum {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ} {ι : Type*} (s : Finset ι)
    (z : ι → (algPiece (Osharp := Osharp) 𝒮 n).val.obj U)
    (hz : ∀ i ∈ s, IsLocallyIn 𝒮 D (z i)) : IsLocallyIn 𝒮 D (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact zero D
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hz i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hz j (Finset.mem_insert_of_mem hj))

/-- Being locally of weights in `D` is monotone in `D`. -/
theorem mono {D E : Set (I →₀ ℕ)} (hDE : D ⊆ E) {n : ℤ} {U : Cᵒᵖ}
    {z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U} (hz : IsLocallyIn 𝒮 D z) :
    IsLocallyIn 𝒮 E z := by
  obtain ⟨S, hS, h⟩ := hz
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := h f hf
  exact ⟨a, ha.mono hDE, hfa⟩

/-- Transporting a local section along an equality of degrees preserves being locally of weights in
`D`. -/
theorem castHom {D : Set (I →₀ ℕ)} {n n' : ℤ} (hn : n = n') {U : Cᵒᵖ}
    {z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U} (hz : IsLocallyIn 𝒮 D z) :
    IsLocallyIn 𝒮 D (SheafOfModules.castHom (algPiece (Osharp := Osharp) 𝒮) hn U z) := by
  subst hn
  exact hz

/-- **A product of local sections of weights in `D` and in `E` has weights in `D + E`.** -/
theorem mulAt {D E : Set (I →₀ ℕ)} {m j n : ℤ} (h : m + j = n) {U : Cᵒᵖ}
    {x : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U}
    {y : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U}
    (hx : IsLocallyIn 𝒮 D x) (hy : IsLocallyIn 𝒮 E y) :
    IsLocallyIn 𝒮 (IsPresIn.addSet D E) (SheafOfModules.mulAt 𝒮 h U x y) := by
  refine castHom h ?_
  obtain ⟨S, hS, hx⟩ := hx
  obtain ⟨S', hS', hy⟩ := hy
  refine ⟨S ⊓ S', J.intersection_covering hS hS', fun V f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := hx f hf.1
  obtain ⟨b, hb, hfb⟩ := hy f hf.2
  exact ⟨_, ha.mulAdd hb, (algMul_lift 𝒮 m j U x y f.op a b hfa hfb).symm⟩

/-- A local section locally below level `k` has weights supported on levels `< k`. -/
theorem of_isLocallyBelow [LT I] {k : I} {n : ℤ} {U : Cᵒᵖ}
    {z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U} (hz : IsLocallyBelow 𝒮 k z) :
    IsLocallyIn 𝒮 {b | ∀ j ∈ b.support, j < k} z := by
  obtain ⟨S, hS, h⟩ := hz
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := h f hf
  exact ⟨a, fun w hw => wordWt_support_lt_of_wordBelow (ha w hw), hfa⟩

end IsLocallyIn

/-- The section attached to a word has the weight of the word. -/
theorem isLocallyIn_algSec {U : Cᵒᵖ} (w : Word 𝒮 U) :
    IsLocallyIn 𝒮 {wordWt w} (algSec (Osharp := Osharp) 𝒮 w) := by
  rw [algSec_def]
  exact isLocallyIn_algToSheaf (IsPresIn.algOf _ (Set.mem_singleton _) _)

/-- The generator attached to a letter has the weight of the letter. -/
theorem isLocallyIn_algGen {U : Cᵒᵖ} (x : Letter 𝒮 U) :
    IsLocallyIn 𝒮 {Finsupp.single x.1 1} (algGen (Osharp := Osharp) 𝒮 x) := by
  rw [algGen_def]
  exact isLocallyIn_algToSheaf (IsPresIn.algOf _ (by simp [Set.mem_singleton_iff]) _)

/-! ### The differential lowers the weight -/

section Differential

variable [LinearOrder I] (δ : DerivationDatum (Osharp := Osharp) 𝒮)

/-- **The Leibniz extension of a triangular derivation datum strictly lowers the weight**: on a
word of weight `w` it is locally a combination of words of weight `< w`. -/
theorem wordD_isLocallyIn (htri : DerivationDatum.IsTriangular 𝒮 δ) {U : Cᵒᵖ} (w : Word 𝒮 U) :
    IsLocallyIn 𝒮 {v | toColex v < toColex (wordWt w)} (wordD 𝒮 δ w) := by
  induction w with
  | nil => exact IsLocallyIn.zero _
  | cons x w ih =>
    rw [wordD_cons 𝒮 δ x w (by simp only [wordDeg_cons]; omega)
      (by simp only [wordDeg_cons]; omega)]
    refine IsLocallyIn.add ?_ (IsLocallyIn.zsmul _ ?_)
    · refine IsLocallyIn.mono ?_
        (IsLocallyIn.mulAt _ (IsLocallyIn.of_isLocallyBelow (htri U x)) (isLocallyIn_algSec w))
      rintro v ⟨b, hb, c, rfl, rfl⟩
      rw [Set.mem_ofPred_eq, wordWt_cons]
      exact wt_add_lt_add_right _ (wt_lt_single_of_support hb)
    · refine IsLocallyIn.mono ?_ (IsLocallyIn.mulAt _ (isLocallyIn_algGen x) ih)
      rintro v ⟨b, rfl, c, hc, rfl⟩
      rw [Set.mem_ofPred_eq, wordWt_cons]
      exact wt_add_lt_add_left _ hc

/-- The weights strictly below some weight of `D`. -/
def strictBelow (D : Set (I →₀ ℕ)) : Set (I →₀ ℕ) :=
  {v | ∃ u ∈ D, toColex v < toColex u}

/-- **The differential of `O⟨S⟩` strictly lowers the weight**: on a presentation element with
weights in `D` it is locally a combination of words of weight strictly below some weight of
`D`. -/
theorem algD_isLocallyIn (htri : DerivationDatum.IsTriangular 𝒮 δ) {D : Set (I →₀ ℕ)} {n : ℤ}
    {U : Cᵒᵖ} {a : algSections Osharp 𝒮 n U} (ha : IsPresIn 𝒮 D a) :
    IsLocallyIn 𝒮 (strictBelow D) ((algD 𝒮 δ n).val.app U ((algToSheaf 𝒮 n).app U a)) := by
  rw [algD_toSheaf, ← algDAdd_apply, IsPresIn.eq_sum a, map_sum]
  refine IsLocallyIn.sum _ _ fun w hw => ?_
  rw [algDAdd_apply, algDHom_algOf]
  refine IsLocallyIn.smul _ (IsLocallyIn.castHom _ (IsLocallyIn.mono ?_
    (wordD_isLocallyIn δ htri w.1)))
  intro v hv
  exact ⟨_, ha w hw, hv⟩

end Differential

end SheafOfModules

end
