module

public import StacksFrontier.AlgebraicGeometry.CardinalGeneratedColimit.Basic
public import StacksFrontier.AlgebraicGeometry.GabberColimit.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CrystalTransitionSection

/-!
# Bounded compatible families of sections of a crystal on a system of schemes

Let `(F, α)` be a crystal in quasi-coherent modules on a system of schemes `X = ({X i}, {f φ})`.
A family of sections is indexed by the pairs `(i, U)` of an index of the system and an affine open
of `X i`.  A family of at most `κ` sections over each such pair is enlarged, keeping the bound
`κ`, until its spans are compatible under restriction between nested affine opens of each `X i`
and under the transitions of the system: for `φ` with `j φ = (i, i')` and affine opens `U ⊆ X i`,
`V ⊆ X i'` with `V ⊆ (f φ)⁻¹ U`, the sections present over `V` are spanned by the transitions of
the sections present over `U`, and those transitions are themselves present over `V`.

## Main definitions

* `Stacks.AlgebraicGeometry.Crystals.SchemeSystem.AffineIdx`: the index set of the families, the
  pairs `(i, U)` with `U` an affine open of `X i`.
* `Stacks.AlgebraicGeometry.Crystals.Crystal.Family`: a set of sections of `F i` over `U` for
  every such pair.
* `Stacks.AlgebraicGeometry.Crystals.Crystal.saturationStep` and
  `Stacks.AlgebraicGeometry.Crystals.Crystal.saturation`: one step, and the `ℕ`-indexed limit, of
  the closure.  The step adds the restrictions of the sections present over larger affine opens
  of the same scheme, the chosen expressions of the sections present over smaller affine opens of
  the same scheme, the transitions along every `φ` of the sections present over a compatible
  affine open of the source, and the chosen expressions, as transitions, of the sections present
  over a compatible affine open of the target.

## Main results

* `Stacks.AlgebraicGeometry.Crystals.Crystal.exists_bounded_compatible_family`: if `κ` is
  infinite and bounds the cardinalities of `Φ` and of the set of affine opens of every `X i`,
  then every family of at most `κ` sections over each affine open of each scheme of the system
  is contained in such a family whose spans are compatible both under restriction inside each
  scheme and under the transitions of the system.

## References

* [Stacks Project, Tag 077Z](https://stacks.math.columbia.edu/tag/077Z)
* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.CardinalGeneration
open Stacks.AlgebraicGeometry.GabberColimit

universe u

namespace Stacks.AlgebraicGeometry.Crystals

variable {D : SchemeSystem.{u}}

/-- **An affine open of one of the schemes of the system**: the index set of the families of
sections used in the closure construction. -/
abbrev SchemeSystem.AffineIdx (D : SchemeSystem.{u}) : Type u :=
  Σ i : D.I, (D.X i).affineOpens

namespace Crystal

variable (M : Crystal D)

/-- **A family of sets of sections of a crystal**: a set of sections of `F i` over `U` for every
affine open `U` of every scheme `X i` of the system. -/
abbrev Family : Type u := ∀ p : D.AffineIdx, Set Γ(M.F p.1, p.2.1)

/-! ### Transporting a set of sections along an equality of indices -/

/-- Transport a set of sections along an equality of indices of the system. -/
def castSections {p q : D.AffineIdx} (hpq : p = q) (s : Set Γ(M.F p.1, p.2.1)) :
    Set Γ(M.F q.1, q.2.1) :=
  @Eq.rec D.AffineIdx p (fun r _ => Set Γ(M.F r.1, r.2.1)) s q hpq

/-- Transporting along the identity does nothing. -/
@[simp]
theorem castSections_rfl (p : D.AffineIdx) (s : Set Γ(M.F p.1, p.2.1)) :
    M.castSections (rfl : p = p) s = s := rfl

/-- **A set of sections placed at the index it belongs to.**  It is the transport of `s` when the
index `q` at which `s` lives is the index `p` being evaluated, and the empty set otherwise. -/
def castPart (p q : D.AffineIdx) (s : Set Γ(M.F q.1, q.2.1)) : Set Γ(M.F p.1, p.2.1) :=
  {y | ∃ hpq : q = p, y ∈ M.castSections hpq s}

/-- At its own index, `castPart` is the set itself. -/
@[simp]
theorem castPart_self (q : D.AffineIdx) (s : Set Γ(M.F q.1, q.2.1)) : M.castPart q q s = s :=
  Set.ext fun _ => ⟨fun hy => hy.2, fun hy => ⟨rfl, hy⟩⟩

/-- `castPart` does not increase cardinality. -/
theorem mk_castPart_le (p q : D.AffineIdx) (s : Set Γ(M.F q.1, q.2.1)) {κ : Cardinal.{u}}
    (hs : Cardinal.mk s ≤ κ) : Cardinal.mk (M.castPart p q s) ≤ κ := by
  by_cases hq : q = p
  · subst hq
    rwa [castPart_self]
  · rw [show M.castPart p q s = ∅ from Set.eq_empty_iff_forall_notMem.mpr fun y hy => hq hy.1]
    simp

/-! ### The index types of the closure step -/

/-- The index of the restriction and expression steps at a scheme `X i`: an affine open of `X i`
together with a section of the family over it. -/
abbrev restrIdx (T : M.Family) (i : D.I) : Type u :=
  Σ U : (D.X i).affineOpens, ↥(T ⟨i, U⟩)

/-- The index of the transition step: a transition `φ` of the system, an affine open `U` of its
source, an affine open of its target inside the preimage of `U`, and a section of the family
over `U`. -/
abbrev transIdx (T : M.Family) : Type u :=
  Σ (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens)
    (_ : {V : (D.X (D.j φ).2).affineOpens // V.1 ≤ (D.f φ) ⁻¹ᵁ U.1}), ↥(T ⟨(D.j φ).1, U⟩)

/-- The index of the transition-expression step: a transition `φ` of the system, an affine open
of its source, an affine open of its target, and a section of the family over the latter. -/
abbrev transExprIdx (T : M.Family) : Type u :=
  Σ (φ : D.Φ) (_ : (D.X (D.j φ).1).affineOpens) (V : (D.X (D.j φ).2).affineOpens),
    ↥(T ⟨(D.j φ).2, V⟩)

/-! ### The parts added by one closure step -/

/-- The restriction to the index `p` of the section indexed by `q`, as a set which is empty
unless the affine open of `p` is contained in that of `q`. -/
def restrPart (T : M.Family) (p : D.AffineIdx) (q : M.restrIdx T p.1) :
    Set Γ(M.F p.1, p.2.1) :=
  {y | ∃ h : p.2.1 ≤ q.1.1, (M.F p.1).presheaf.map (homOfLE h).op q.2.1 = y}

/-- `restrPart` is empty or a singleton. -/
theorem subsingleton_restrPart (T : M.Family) (p : D.AffineIdx) (q : M.restrIdx T p.1) :
    (M.restrPart T p q).Subsingleton := by
  rintro y ⟨h1, rfl⟩ z ⟨h2, rfl⟩
  rfl

/-- The transition along `φ` of the section indexed by `q`, placed at the index of the target
affine open. -/
def transPart (T : M.Family) (p : D.AffineIdx) (q : M.transIdx T) : Set Γ(M.F p.1, p.2.1) :=
  M.castPart p ⟨(D.j q.1).2, q.2.2.1.1⟩
    {M.transitionSection q.1 q.2.1.1 q.2.2.1.1.1 q.2.2.1.2 q.2.2.2.1}

/-- The chosen expression, as transitions along `φ`, of the section indexed by `q`, placed at the
index of the source affine open. -/
def transExprPart
    (gT : ∀ (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens) (V : (D.X (D.j φ).2).affineOpens),
      Γ(M.F (D.j φ).2, V.1) → Set Γ(M.F (D.j φ).1, U.1))
    (T : M.Family) (p : D.AffineIdx) (q : M.transExprIdx T) : Set Γ(M.F p.1, p.2.1) :=
  M.castPart p ⟨(D.j q.1).1, q.2.1⟩ (gT q.1 q.2.1 q.2.2.1 q.2.2.2.1)

/-! ### Cardinal arithmetic -/

variable {M}

/-- The index of the restriction step is `κ`-bounded. -/
theorem mk_restrIdx_le {T : M.Family} {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hX : ∀ i : D.I, Cardinal.mk (D.X i).affineOpens ≤ κ)
    (hT : ∀ p, Cardinal.mk (T p) ≤ κ) (i : D.I) : Cardinal.mk (M.restrIdx T i) ≤ κ :=
  mk_sigma_le hκ (hX i) fun U => hT ⟨i, U⟩

/-- The index of the transition step is `κ`-bounded. -/
theorem mk_transIdx_le {T : M.Family} {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hΦ : Cardinal.mk D.Φ ≤ κ) (hX : ∀ i : D.I, Cardinal.mk (D.X i).affineOpens ≤ κ)
    (hT : ∀ p, Cardinal.mk (T p) ≤ κ) : Cardinal.mk (M.transIdx T) ≤ κ :=
  mk_sigma_le hκ hΦ fun φ =>
    mk_sigma_le hκ (hX _) fun U =>
      mk_sigma_le hκ ((Cardinal.mk_subtype_le _).trans (hX _)) fun _ => hT ⟨(D.j φ).1, U⟩

/-- The index of the transition-expression step is `κ`-bounded. -/
theorem mk_transExprIdx_le {T : M.Family} {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hΦ : Cardinal.mk D.Φ ≤ κ) (hX : ∀ i : D.I, Cardinal.mk (D.X i).affineOpens ≤ κ)
    (hT : ∀ p, Cardinal.mk (T p) ≤ κ) : Cardinal.mk (M.transExprIdx T) ≤ κ :=
  mk_sigma_le hκ hΦ fun φ =>
    mk_sigma_le hκ (hX _) fun _ =>
      mk_sigma_le hκ (hX _) fun V => hT ⟨(D.j φ).2, V⟩

/-! ### The closure -/

variable (M)

/-- **One step of the closure construction.**  To the sections already present at an index it
adds: the restrictions of the sections present over larger affine opens of the same scheme; the
chosen expressions of the sections present over smaller affine opens of the same scheme; the
transitions, along every `φ` of the system, of the sections present over a compatible affine
open of the source; and the chosen expressions, as transitions, of the sections present over a
compatible affine open of the target. -/
def saturationStep
    (g : ∀ (i : D.I) (U W : (D.X i).affineOpens), Γ(M.F i, W.1) → Set Γ(M.F i, U.1))
    (gT : ∀ (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens) (V : (D.X (D.j φ).2).affineOpens),
      Γ(M.F (D.j φ).2, V.1) → Set Γ(M.F (D.j φ).1, U.1))
    (T : M.Family) : M.Family := fun p =>
  T p ∪ (⋃ q : M.restrIdx T p.1, M.restrPart T p q)
    ∪ (⋃ q : M.restrIdx T p.1, g p.1 p.2 q.1 q.2.1)
    ∪ (⋃ q : M.transIdx T, M.transPart T p q)
    ∪ (⋃ q : M.transExprIdx T, M.transExprPart gT T p q)

variable
  (g : ∀ (i : D.I) (U W : (D.X i).affineOpens), Γ(M.F i, W.1) → Set Γ(M.F i, U.1))
  (gT : ∀ (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens) (V : (D.X (D.j φ).2).affineOpens),
    Γ(M.F (D.j φ).2, V.1) → Set Γ(M.F (D.j φ).1, U.1))
  (S : M.Family)

/-- **The closure of a family of sets of sections** under the steps of `saturationStep`. -/
def saturation : M.Family := fun p =>
  ⋃ n : ULift.{u} ℕ, (M.saturationStep g gT)^[n.down] S p

/-- The closure contains the original family. -/
theorem subset_saturation (p : D.AffineIdx) : S p ⊆ M.saturation g gT S p := fun _ hx =>
  Set.mem_iUnion.mpr ⟨⟨0⟩, hx⟩

/-- A section produced by one more closure step from an iterate lies in the closure. -/
private theorem mem_saturation_of_mem_step {n : ℕ} {p : D.AffineIdx} {x : Γ(M.F p.1, p.2.1)}
    (hx : x ∈ M.saturationStep g gT ((M.saturationStep g gT)^[n] S) p) :
    x ∈ M.saturation g gT S p :=
  Set.mem_iUnion.mpr ⟨⟨n + 1⟩, by rwa [Function.iterate_succ_apply']⟩

/-- One closure step preserves the bound `κ`, for `κ` infinite bounding the cardinality of `Φ`
and the number of affine opens of every scheme of the system. -/
theorem mk_saturationStep_le (hg : ∀ i U W m, (g i U W m).Finite)
    (hgT : ∀ φ U V m, (gT φ U V m).Finite) {T : M.Family} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hΦ : Cardinal.mk D.Φ ≤ κ)
    (hX : ∀ i : D.I, Cardinal.mk (D.X i).affineOpens ≤ κ) (hT : ∀ p, Cardinal.mk (T p) ≤ κ)
    (p : D.AffineIdx) : Cardinal.mk (M.saturationStep g gT T p) ≤ κ := by
  have hr : Cardinal.mk (M.restrIdx T p.1) ≤ κ := mk_restrIdx_le hκ hX hT p.1
  have ht : Cardinal.mk (M.transIdx T) ≤ κ := mk_transIdx_le hκ hΦ hX hT
  have hte : Cardinal.mk (M.transExprIdx T) ≤ κ := mk_transExprIdx_le hκ hΦ hX hT
  have h1 : Cardinal.mk (⋃ q : M.restrIdx T p.1, M.restrPart T p q) ≤ κ :=
    mk_iUnion_le_of_forall_le hκ hr fun q =>
      ((M.subsingleton_restrPart T p q).finite.lt_aleph0.le).trans hκ
  have h2 : Cardinal.mk (⋃ q : M.restrIdx T p.1, g p.1 p.2 q.1 q.2.1) ≤ κ :=
    mk_iUnion_le_of_forall_le hκ hr fun q => ((hg p.1 p.2 q.1 q.2.1).lt_aleph0.le).trans hκ
  have h3 : Cardinal.mk (⋃ q : M.transIdx T, M.transPart T p q) ≤ κ :=
    mk_iUnion_le_of_forall_le hκ ht fun q =>
      M.mk_castPart_le _ _ _ (by simpa using Cardinal.one_le_aleph0.trans hκ)
  have h4 : Cardinal.mk (⋃ q : M.transExprIdx T, M.transExprPart gT T p q) ≤ κ :=
    mk_iUnion_le_of_forall_le hκ hte fun q =>
      M.mk_castPart_le _ _ _ (((hgT q.1 q.2.1 q.2.2.1 q.2.2.2.1).lt_aleph0.le).trans hκ)
  refine (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hκ ?_ h4)
  refine (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hκ ?_ h3)
  refine (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hκ ?_ h2)
  exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hκ (hT p) h1)

/-- The closure of a `κ`-bounded family is `κ`-bounded. -/
theorem mk_saturation_le (hg : ∀ i U W m, (g i U W m).Finite)
    (hgT : ∀ φ U V m, (gT φ U V m).Finite) {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hΦ : Cardinal.mk D.Φ ≤ κ) (hX : ∀ i : D.I, Cardinal.mk (D.X i).affineOpens ≤ κ)
    (hS : ∀ p, Cardinal.mk (S p) ≤ κ) (p : D.AffineIdx) :
    Cardinal.mk (M.saturation g gT S p) ≤ κ := by
  have key : ∀ (n : ℕ) (p : D.AffineIdx),
      Cardinal.mk ((M.saturationStep g gT)^[n] S p) ≤ κ := by
    intro n
    induction n with
    | zero => exact hS
    | succ n ih =>
      intro p
      rw [Function.iterate_succ_apply']
      exact M.mk_saturationStep_le g gT hg hgT hκ hΦ hX ih p
  exact mk_iUnion_le_of_forall_le hκ (by simpa using hκ) fun n => key n.down p

/-! ### The closure properties -/

/-- The closure is stable under restriction to smaller affine opens of the same scheme. -/
theorem map_mem_saturation {i : D.I} {U W : (D.X i).affineOpens} (h : W.1 ≤ U.1)
    {m : Γ(M.F i, U.1)} (hm : m ∈ M.saturation g gT S ⟨i, U⟩) :
    (M.F i).presheaf.map (homOfLE h).op m ∈ M.saturation g gT S ⟨i, W⟩ := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
  exact M.mem_saturation_of_mem_step g gT S
    (Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨U, ⟨m, hn⟩⟩, ⟨h, rfl⟩⟩)))))

/-- The closure contains the chosen local expressions, inside one scheme, of each of its own
sections. -/
theorem choice_subset_saturation {i : D.I} (U W : (D.X i).affineOpens) {m : Γ(M.F i, W.1)}
    (hm : m ∈ M.saturation g gT S ⟨i, W⟩) : g i U W m ⊆ M.saturation g gT S ⟨i, U⟩ := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
  intro y hy
  exact M.mem_saturation_of_mem_step g gT S
    (Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨W, ⟨m, hn⟩⟩, hy⟩))))

/-- The closure is stable under the transitions of the system. -/
theorem transitionSection_mem_saturation (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens)
    (V : (D.X (D.j φ).2).affineOpens) (h : V.1 ≤ (D.f φ) ⁻¹ᵁ U.1)
    {a : Γ(M.F (D.j φ).1, U.1)} (ha : a ∈ M.saturation g gT S ⟨(D.j φ).1, U⟩) :
    M.transitionSection φ U.1 V.1 h a ∈ M.saturation g gT S ⟨(D.j φ).2, V⟩ := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  refine M.mem_saturation_of_mem_step g gT S
    (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨φ, U, ⟨V, h⟩, ⟨a, hn⟩⟩, ?_⟩)))
  rw [transPart, castPart_self]
  rfl

/-- The closure contains the chosen expressions, as transitions, of each of its own sections. -/
theorem transChoice_subset_saturation (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens)
    (V : (D.X (D.j φ).2).affineOpens) {m : Γ(M.F (D.j φ).2, V.1)}
    (hm : m ∈ M.saturation g gT S ⟨(D.j φ).2, V⟩) :
    gT φ U V m ⊆ M.saturation g gT S ⟨(D.j φ).1, U⟩ := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
  intro y hy
  refine M.mem_saturation_of_mem_step g gT S (Or.inr (Set.mem_iUnion.mpr ⟨⟨φ, U, V, ⟨m, hn⟩⟩, ?_⟩))
  rwa [transExprPart, castPart_self]

/-! ### The two compatibility conditions -/

/-- If `B` is stable under `f`-images into `A` and every element of `A` is spanned by the
`f`-image of a subset of `B`, then `span A = span (f '' B)`. -/
private theorem span_eq_span_image_of {R N P : Type*} [Semiring R] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] (A : Set N) (B : Set P) (f : P → N) (G : N → Set P)
    (hG : ∀ m, m ∈ Submodule.span R (f '' G m)) (hGB : ∀ m ∈ A, G m ⊆ B)
    (hf : ∀ b ∈ B, f b ∈ A) : Submodule.span R A = Submodule.span R (f '' B) :=
  le_antisymm (Submodule.span_le.mpr fun m hm =>
    Submodule.span_mono (Set.image_mono (hGB m hm)) (hG m))
    (Submodule.span_le.mpr (by rintro _ ⟨b, hb, rfl⟩; exact Submodule.subset_span (hf b hb)))

/-- The spans of the closure are compatible under restriction inside each scheme. -/
theorem span_saturation_eq
    (hg : ∀ (i : D.I) (U W : (D.X i).affineOpens) (m : Γ(M.F i, W.1)) (h : W.1 ≤ U.1),
      m ∈ Submodule.span Γ(D.X i, W.1) ((M.F i).presheaf.map (homOfLE h).op '' g i U W m))
    (i : D.I) (U W : (D.X i).affineOpens) (h : W.1 ≤ U.1) :
    Submodule.span Γ(D.X i, W.1) (M.saturation g gT S ⟨i, W⟩)
      = Submodule.span Γ(D.X i, W.1)
        ((M.F i).presheaf.map (homOfLE h).op '' M.saturation g gT S ⟨i, U⟩) := by
  exact span_eq_span_image_of _ _ _ _ (fun m => hg i U W m h)
    (fun _ hm => M.choice_subset_saturation g gT S U W hm)
    fun _ hm => M.map_mem_saturation g gT S h hm

/-- The spans of the closure are compatible under the transitions of the system. -/
theorem span_saturation_transition_eq
    (hgT : ∀ (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens) (V : (D.X (D.j φ).2).affineOpens)
      (m : Γ(M.F (D.j φ).2, V.1)) (h : V.1 ≤ (D.f φ) ⁻¹ᵁ U.1),
      m ∈ Submodule.span Γ(D.X (D.j φ).2, V.1)
        ((fun a => M.transitionSection φ U.1 V.1 h a) '' gT φ U V m))
    (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens) (V : (D.X (D.j φ).2).affineOpens)
    (h : V.1 ≤ (D.f φ) ⁻¹ᵁ U.1) :
    Submodule.span Γ(D.X (D.j φ).2, V.1) (M.saturation g gT S ⟨(D.j φ).2, V⟩)
      = Submodule.span Γ(D.X (D.j φ).2, V.1)
        ((fun a => M.transitionSection φ U.1 V.1 h a) ''
          M.saturation g gT S ⟨(D.j φ).1, U⟩) := by
  exact span_eq_span_image_of _ _ _ _ (fun m => hgT φ U V m h)
    (fun _ hm => M.transChoice_subset_saturation g gT S φ U V hm)
    fun _ ha => M.transitionSection_mem_saturation g gT S φ U V h ha

/-! ### Bounded compatible families -/

/-- **Bounded compatible families of sections.**  Let `(F, α)` be a crystal in quasi-coherent
modules on a system of schemes and let `κ` be an infinite cardinal bounding the cardinality of `Φ`
and the number of affine opens of each `X i`.  Then every family of at most `κ` sections of
`F i` over each affine open of each `X i` is contained in such a family whose spans are
compatible in two senses: inside each scheme, the span over a smaller affine open is the span of
the restrictions from a larger one; and along each transition `φ` of the system, the span over an
affine open of the target is the span of the transitions of the sections over an affine open of
the source containing its image. -/
theorem exists_bounded_compatible_family {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hΦ : Cardinal.mk D.Φ ≤ κ) (hX : ∀ i : D.I, Cardinal.mk (D.X i).affineOpens ≤ κ)
    (S : M.Family) (hS : ∀ p, Cardinal.mk (S p) ≤ κ) :
    ∃ T : M.Family, (∀ p, S p ⊆ T p) ∧ (∀ p, Cardinal.mk (T p) ≤ κ) ∧
      (∀ (i : D.I) (U W : (D.X i).affineOpens) (h : W.1 ≤ U.1),
        Submodule.span Γ(D.X i, W.1) (T ⟨i, W⟩)
          = Submodule.span Γ(D.X i, W.1)
            ((M.F i).presheaf.map (homOfLE h).op '' T ⟨i, U⟩)) ∧
      ∀ (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens) (V : (D.X (D.j φ).2).affineOpens)
        (h : V.1 ≤ (D.f φ) ⁻¹ᵁ U.1),
        Submodule.span Γ(D.X (D.j φ).2, V.1) (T ⟨(D.j φ).2, V⟩)
          = Submodule.span Γ(D.X (D.j φ).2, V.1)
            ((fun a => M.transitionSection φ U.1 V.1 h a) '' T ⟨(D.j φ).1, U⟩) := by
  classical
  have hqc : ∀ i : D.I, (M.F i).IsQuasicoherent := M.isQuasicoherent
  choose g hgfin hgspan using fun (i : D.I) (U W : (D.X i).affineOpens) (m : Γ(M.F i, W.1)) =>
    @GabberColimit.exists_finite_subset_span (D.X i) (M.F i) (hqc i) U W m
  choose gT hgTfin hgTspan using fun (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens)
    (V : (D.X (D.j φ).2).affineOpens) (m : Γ(M.F (D.j φ).2, V.1)) =>
      M.exists_finite_subset_span_transition φ U V m
  exact ⟨M.saturation g gT S, M.subset_saturation g gT S,
    M.mk_saturation_le g gT S hgfin hgTfin hκ hΦ hX hS,
    M.span_saturation_eq g gT S hgspan, M.span_saturation_transition_eq g gT S hgTspan⟩

end Crystal

end Stacks.AlgebraicGeometry.Crystals

end
