module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.RingTheory.LocalProperties.Submodule
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# The closure construction in Gabber's theorem, and the subsheaf it defines

Gabber's theorem (Stacks 077N) says that on a scheme `X` there is a cardinal `κ`, depending
only on `X`, such that every quasi-coherent `𝒪_X`-module `F` is the directed colimit of its
quasi-coherent `κ`-generated submodules.  Both of the theorem's assertions — the directedness
of the system and the colimit — rest on one construction: given a family of at most `κ` chosen
sections of `F` over each affine open, produce a quasi-coherent `κ`-generated submodule of `F`
containing them.  This file carries out the two steps of that construction which are
independent of the sheaf-theoretic bookkeeping:

* the **closure** of a `κ`-bounded family of sets of sections under restriction and under the
  choice of local expressions, which is the content of the source's `𝒮 ↦ 𝒮'` iteration and the
  only place where the cardinal bound is used;
* the passage from a **compatible family** of submodules of the sections over the affine opens
  to an actual submodule sheaf of `F` with those sections.

Neither of the two assertions of tag 077N is proved here, and no stacks attribute is therefore
carried anywhere in this file.  What remains, after this file, in order to produce the objects
of `CardinalGeneratedQuasicoherentSubobject F κ`, is the quasi-coherence of `sheafSubmodule`
and the bound on its local generators.

## Main definitions

* `IsCompatible F N`: a family `N` of submodules `N U ⊆ Γ(F, U)`, indexed by the affine opens
  `U` of `X`, is compatible if for affine `W ≤ U` the submodule `N W` is generated over
  `Γ(X, W)` by the restrictions of the sections of `N U`.  By Stacks 01I9 this is the correct
  "quasi-coherent subsheaf datum": `Γ(F, W) = Γ(F, U) ⊗_{Γ(X, U)} Γ(X, W)`, and the condition
  says that `N` is the base change of `N U` inside that identification.
* `saturationStep` and `saturation`: one step, and the `ℕ`-indexed limit, of the closure
  operation on families of sets of sections.  The step adds all restrictions of the sections
  already present to the smaller affine opens, together with, for every section `m` present
  over a smaller affine open `W ≤ U`, a finite set of sections over `U` whose restrictions
  generate `m`.
* `IsLocallyIn F N s`, `localSections F N U`, `preSubmodule F N` and `sheafSubmodule F N hN`:
  the subsheaf of `F` cut out by a compatible family, through the local condition that every
  restriction to an affine open lies in the family.

## Main results

* `span_range_restrict_eq_top`: for affine opens `W ≤ U` of `X` and `F` quasi-coherent, the
  sections of `F` over `W` are generated over `Γ(X, W)` by the restrictions of the sections
  over `U`.  This is the surjectivity half of Stacks 01I9, in the form
  `Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_restrictₗ`.
* `exists_bounded_compatible_family`: **the closure step of Gabber's argument.** If `κ` is an
  infinite cardinal bounding the number of affine opens of `X`, then every family of sets of
  sections of a quasi-coherent `F` of size at most `κ` is contained in such a family whose
  spans form a compatible family of submodules.  The hypotheses on `κ` are exactly
  `aleph0_le_cardinalBound` and `mk_affineOpens_le_cardinalBound` for `cardinalBound X`.
* `mem_of_cover`: a compatible family satisfies the local-global principle — a section over an
  affine open which lies in the family after restriction to each member of an affine cover
  already lies in the family.  This is proved by localizing at the basic opens of a cover,
  where the compatibility condition becomes the statement that `N` localizes.
* `obj_sheafSubmodule`: the sections of `sheafSubmodule F N hN` over an affine open `U` are
  exactly `N U`.

## Implementation notes

The source covers `X` by a chosen affine open covering and covers each pairwise intersection
again; here the index set is taken to be *all* affine opens of `X` at once, which is legitimate
because `cardinalBound X` bounds their number.  With that choice the compatibility condition
only has to be imposed on nested pairs `W ≤ U` of affine opens: for affine `W ≤ U ⊓ U'` it then
follows for the pair `(U, U')` by comparing both sides with `N W`.  Correspondingly the closure
operation needs only the two steps described above, instead of the source's choice function
indexed by triples.

The two directions of the compatibility condition for `saturation` come from the two halves of
`saturationStep`, and neither needs the family to be increasing in the iteration index: a
section of the saturation appears at some finite stage, and the step applied to that stage
already contains what is needed.

## References

* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.GabberColimit

variable {X : Scheme.{u}} (F : X.Modules)

/-! ### Restriction of sections -/

/-- Restricting twice is restricting once. -/
theorem res_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(F, U)) :
    F.presheaf.map (homOfLE h2).op (F.presheaf.map (homOfLE h1).op x) =
      F.presheaf.map (homOfLE (h2.trans h1)).op x := by
  rw [← Functor.map_comp_apply]
  rfl

/-- Restricting along the identity does nothing. -/
theorem res_self {U : X.Opens} (x : Γ(F, U)) :
    F.presheaf.map (homOfLE (le_refl U)).op x = x := by
  rw [show (homOfLE (le_refl U)).op = 𝟙 _ from rfl, F.presheaf.map_id]
  rfl

/-- For nested affine opens `W ≤ U` of `X` and `F` quasi-coherent, the sections of `F` over `W`
are generated over `Γ(X, W)` by the restrictions of the sections over `U`.  This is the
surjectivity half of Stacks 01I9: `Γ(F, W)` is the base change of `Γ(F, U)` along
`Γ(X, U) → Γ(X, W)`, so the elements `1 ⊗ m` generate it. -/
theorem span_range_restrict_eq_top [F.IsQuasicoherent] {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (h : W ≤ U) :
    Submodule.span Γ(X, W) (Set.range (F.presheaf.map (homOfLE h).op)) = ⊤ := by
  let := algebraOfLE X h
  let := moduleOfLE F h
  let := isScalarTowerOfLE F h
  have hbc := isBaseChange_restrictₗ F hW hU h
  refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
  induction x using hbc.inductionOn with
  | zero => exact zero_mem _
  | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
  | smul s n hn => exact Submodule.smul_mem _ _ hn
  | add a b ha hb => exact Submodule.add_mem _ ha hb

/-- Every section of `F` over an affine open `W` is a finite `Γ(X, W)`-combination of
restrictions of finitely many sections over a larger affine open `U`.  The statement is phrased
so as to be available for every pair of affine opens, vacuously when `W ≰ U`, which makes the
resulting choice function total. -/
theorem exists_finite_subset_span [F.IsQuasicoherent] (U W : X.affineOpens) (m : Γ(F, W.1)) :
    ∃ s : Set Γ(F, U.1), s.Finite ∧ ∀ h : W.1 ≤ U.1,
      m ∈ Submodule.span Γ(X, W.1) (F.presheaf.map (homOfLE h).op '' s) := by
  by_cases h : W.1 ≤ U.1
  · have hm : m ∈ Submodule.span Γ(X, W.1) (Set.range (F.presheaf.map (homOfLE h).op)) := by
      rw [span_range_restrict_eq_top F U.2 W.2 h]; trivial
    obtain ⟨n, c, y, hy⟩ := Submodule.mem_span_set'.mp hm
    refine ⟨Set.range fun i : Fin n ↦ (y i).2.choose, Set.finite_range _, fun h' ↦ ?_⟩
    rw [← hy]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨(y i).2.choose, Set.mem_range_self i, (y i).2.choose_spec⟩
  · exact ⟨∅, Set.finite_empty, fun h' ↦ absurd h' h⟩

/-! ### The closure construction -/

/-- A sum of at most `κ` cardinals, each at most `κ`, is at most `κ`, for `κ` infinite. -/
private theorem sum_mk_le_of_forall_le {ι : Type u} {α : ι → Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hι : Cardinal.mk ι ≤ κ) (hs : ∀ i, Cardinal.mk (α i) ≤ κ) :
    (Cardinal.sum fun i ↦ Cardinal.mk (α i)) ≤ κ := by
  refine (Cardinal.sum_le_sum _ (fun _ ↦ κ) hs).trans ?_
  rw [Cardinal.sum_const']
  calc Cardinal.mk ι * κ ≤ κ * κ := mul_le_mul' hι le_rfl
    _ = κ := Cardinal.mul_eq_self hκ

/-- A union of at most `κ` sets of size at most `κ` has size at most `κ`, for `κ` infinite. -/
theorem mk_iUnion_le_of_forall_le {ι : Type u} {α : Type u} {s : ι → Set α}
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ) (hι : Cardinal.mk ι ≤ κ)
    (hs : ∀ i, Cardinal.mk (s i) ≤ κ) : Cardinal.mk (⋃ i, s i) ≤ κ :=
  Cardinal.mk_iUnion_le_sum_mk.trans (sum_mk_le_of_forall_le hκ hι hs)

/-- The restriction to `V` of the section indexed by `p`, as a set which is empty unless `V` is
contained in the affine open over which that section lives. -/
def restrictionPart (T : ∀ U : X.affineOpens, Set Γ(F, U.1)) (V : X.affineOpens)
    (p : Σ U : X.affineOpens, (T U : Set Γ(F, U.1))) : Set Γ(F, V.1) :=
  {y | ∃ h : V.1 ≤ p.1.1, F.presheaf.map (homOfLE h).op p.2.1 = y}

/-- `restrictionPart` is empty or a singleton. -/
theorem subsingleton_restrictionPart (T : ∀ U : X.affineOpens, Set Γ(F, U.1))
    (V : X.affineOpens) (p : Σ U : X.affineOpens, (T U : Set Γ(F, U.1))) :
    (restrictionPart F T V p).Subsingleton := by
  rintro y ⟨h1, rfl⟩ z ⟨h2, rfl⟩
  rfl

/-- One step of the closure operation of Gabber's argument, relative to a choice function `g`
as provided by `exists_finite_subset_span`.  To the sections already present over `V` it adds
all restrictions to `V` of the sections present over larger affine opens, and, for every
section present over a smaller affine open, a finite set of sections over `V` whose
restrictions generate it. -/
def saturationStep (g : ∀ U W : X.affineOpens, Γ(F, W.1) → Set Γ(F, U.1))
    (T : ∀ U : X.affineOpens, Set Γ(F, U.1)) (V : X.affineOpens) : Set Γ(F, V.1) :=
  T V ∪ (⋃ p, restrictionPart F T V p) ∪
    ⋃ p : Σ U : X.affineOpens, (T U : Set Γ(F, U.1)), g V p.1 p.2.1

/-- One closure step preserves the bound `κ`, provided `κ` is infinite and bounds the number
of affine opens of `X`. -/
theorem mk_saturationStep_le {g : ∀ U W : X.affineOpens, Γ(F, W.1) → Set Γ(F, U.1)}
    (hg : ∀ U W m, (g U W m).Finite) {T : ∀ U : X.affineOpens, Set Γ(F, U.1)}
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hX : Cardinal.mk X.affineOpens ≤ κ) (hT : ∀ U, Cardinal.mk (T U) ≤ κ)
    (V : X.affineOpens) : Cardinal.mk (saturationStep F g T V) ≤ κ := by
  have hidx : Cardinal.mk (Σ U : X.affineOpens, (T U : Set Γ(F, U.1))) ≤ κ := by
    exact (Cardinal.mk_sigma _).le.trans (sum_mk_le_of_forall_le hκ hX hT)
  have hdown : Cardinal.mk (⋃ p, restrictionPart F T V p) ≤ κ :=
    mk_iUnion_le_of_forall_le hκ hidx fun p ↦
      ((subsingleton_restrictionPart F T V p).finite.lt_aleph0.le).trans hκ
  have hup : Cardinal.mk
      (⋃ p : Σ U : X.affineOpens, (T U : Set Γ(F, U.1)), g V p.1 p.2.1) ≤ κ :=
    mk_iUnion_le_of_forall_le hκ hidx fun p ↦ ((hg V p.1 p.2.1).lt_aleph0.le).trans hκ
  refine (Cardinal.mk_union_le _ _).trans ?_
  refine Cardinal.add_le_of_le hκ ((Cardinal.mk_union_le _ _).trans ?_) hup
  exact Cardinal.add_le_of_le hκ (hT V) hdown

variable (g : ∀ U W : X.affineOpens, Γ(F, W.1) → Set Γ(F, U.1))
  (S : ∀ U : X.affineOpens, Set Γ(F, U.1))

/-- The closure of a family of sets of sections under the two steps of `saturationStep`. -/
def saturation (V : X.affineOpens) : Set Γ(F, V.1) :=
  ⋃ n : ULift.{u} ℕ, (saturationStep F g)^[n.down] S V

/-- The closure contains the original family. -/
theorem subset_saturation (V : X.affineOpens) : S V ⊆ saturation F g S V := fun _ hx ↦
  Set.mem_iUnion.mpr ⟨⟨0⟩, hx⟩

/-- The closure of a `κ`-bounded family is `κ`-bounded, for `κ` infinite bounding the number of
affine opens of `X`. -/
theorem mk_saturation_le (hg : ∀ U W m, (g U W m).Finite) {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hX : Cardinal.mk X.affineOpens ≤ κ)
    (hS : ∀ U, Cardinal.mk (S U) ≤ κ) (V : X.affineOpens) :
    Cardinal.mk (saturation F g S V) ≤ κ := by
  have key : ∀ (n : ℕ) (V : X.affineOpens),
      Cardinal.mk ((saturationStep F g)^[n] S V) ≤ κ := by
    intro n
    induction n with
    | zero => exact hS
    | succ n ih =>
      intro V
      rw [Function.iterate_succ_apply']
      exact mk_saturationStep_le F hg hκ hX ih V
  exact mk_iUnion_le_of_forall_le hκ (by simpa using hκ) fun n ↦ key n.down V

/-- The closure is stable under restriction to smaller affine opens. -/
theorem map_mem_saturation {U W : X.affineOpens} (h : W.1 ≤ U.1) {m : Γ(F, U.1)}
    (hm : m ∈ saturation F g S U) :
    F.presheaf.map (homOfLE h).op m ∈ saturation F g S W := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
  refine Set.mem_iUnion.mpr ⟨⟨n.down + 1⟩, ?_⟩
  rw [Function.iterate_succ_apply']
  refine Or.inl (Or.inr ?_)
  exact Set.mem_iUnion.mpr ⟨⟨U, ⟨m, hn⟩⟩, ⟨h, rfl⟩⟩

/-- The closure contains the chosen local expressions for each of its own sections. -/
theorem choice_subset_saturation (U W : X.affineOpens) {m : Γ(F, W.1)}
    (hm : m ∈ saturation F g S W) : g U W m ⊆ saturation F g S U := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
  intro y hy
  refine Set.mem_iUnion.mpr ⟨⟨n.down + 1⟩, ?_⟩
  rw [Function.iterate_succ_apply']
  exact Or.inr (Set.mem_iUnion.mpr ⟨⟨W, ⟨m, hn⟩⟩, hy⟩)

/-- The spans of the closure form a compatible family: over a smaller affine open the span of
the closure agrees with the span of the restrictions from the larger one. -/
theorem span_saturation_eq
    (hg : ∀ (U W : X.affineOpens) (m : Γ(F, W.1)) (h : W.1 ≤ U.1),
      m ∈ Submodule.span Γ(X, W.1) (F.presheaf.map (homOfLE h).op '' g U W m))
    (U W : X.affineOpens) (h : W.1 ≤ U.1) :
    Submodule.span Γ(X, W.1) (saturation F g S W) =
      Submodule.span Γ(X, W.1) (F.presheaf.map (homOfLE h).op '' saturation F g S U) := by
  refine le_antisymm (Submodule.span_le.mpr fun m hm ↦ ?_) (Submodule.span_le.mpr ?_)
  · exact Submodule.span_mono (Set.image_mono (choice_subset_saturation F g S U W hm))
      (hg U W m h)
  · rintro y ⟨m, hm, rfl⟩
    exact Submodule.subset_span (map_mem_saturation F g S h hm)

/-- **The closure step of Gabber's argument** (Stacks 077N).  Let `F` be a quasi-coherent
module on a scheme `X` and let `κ` be an infinite cardinal bounding the number of affine opens
of `X` — both hypotheses hold for `cardinalBound X`.  Then every family of at most `κ` sections
of `F` over each affine open is contained in such a family whose spans are compatible in the
sense of `IsCompatible`, i.e. form the sections of a candidate quasi-coherent submodule. -/
theorem exists_bounded_compatible_family [F.IsQuasicoherent] {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hX : Cardinal.mk X.affineOpens ≤ κ)
    (S : ∀ U : X.affineOpens, Set Γ(F, U.1)) (hS : ∀ U, Cardinal.mk (S U) ≤ κ) :
    ∃ T : ∀ U : X.affineOpens, Set Γ(F, U.1),
      (∀ U, S U ⊆ T U) ∧ (∀ U, Cardinal.mk (T U) ≤ κ) ∧
      ∀ (U W : X.affineOpens) (h : W.1 ≤ U.1),
        Submodule.span Γ(X, W.1) (T W) =
          Submodule.span Γ(X, W.1) (F.presheaf.map (homOfLE h).op '' T U) := by
  choose g hgfin hgspan using exists_finite_subset_span F
  exact ⟨saturation F g S, subset_saturation F g S, mk_saturation_le F g S hgfin hκ hX hS,
    span_saturation_eq F g S fun U W m h ↦ hgspan U W m h⟩

/-! ### Compatible families of submodules -/

variable (N : ∀ U : X.affineOpens, Submodule Γ(X, U.1) Γ(F, U.1))

/-- A family of submodules of the sections of `F` over the affine opens of `X` is *compatible*
if the submodule attached to a smaller affine open is generated by the restrictions of the
sections of the submodule attached to the larger one.  Under the identification
`Γ(F, W) = Γ(F, U) ⊗_{Γ(X, U)} Γ(X, W)` of Stacks 01I9 this says that `N W` is the base change
of `N U`. -/
def IsCompatible : Prop :=
  ∀ (U W : X.affineOpens) (h : W.1 ≤ U.1),
    N W = Submodule.span Γ(X, W.1)
      (F.presheaf.map (homOfLE h).op '' (N U : Set Γ(F, U.1)))

/-- Restricting a span and then spanning again over the smaller ring is the same as spanning
the restrictions of the original generators. -/
theorem span_image_span {U W : X.Opens} (h : W ≤ U) (s : Set Γ(F, U)) :
    Submodule.span Γ(X, W)
        (F.presheaf.map (homOfLE h).op '' (Submodule.span Γ(X, U) s : Set Γ(F, U))) =
      Submodule.span Γ(X, W) (F.presheaf.map (homOfLE h).op '' s) := by
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro y ⟨m, hm, rfl⟩
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [F.map_smul (homOfLE h) r x]
    exact Submodule.smul_mem _ _ hx

/-- The spans of a family of sets of sections whose spans match up after restriction form a
compatible family of submodules. -/
theorem isCompatible_span (T : ∀ U : X.affineOpens, Set Γ(F, U.1))
    (hT : ∀ (U W : X.affineOpens) (h : W.1 ≤ U.1),
      Submodule.span Γ(X, W.1) (T W) =
        Submodule.span Γ(X, W.1) (F.presheaf.map (homOfLE h).op '' T U)) :
    IsCompatible F fun U ↦ Submodule.span Γ(X, U.1) (T U) := fun U W h ↦ by
  rw [span_image_span F h (T U)]
  exact hT U W h

/-- **A compatible family satisfies the local-global principle.**  A section of `F` over an
affine open which, after restriction to each member of an affine cover, lies in a compatible
family already lies in that family.  The cover is refined to a cover by basic opens, which
generate the unit ideal; there the compatibility condition says precisely that the submodule
localizes, so `Submodule.mem_of_isLocalized_span` applies. -/
theorem mem_of_cover [F.IsQuasicoherent] (hN : IsCompatible F N) (V : X.affineOpens)
    (t : Γ(F, V.1))
    (hcov : ∀ x ∈ V.1, ∃ W : X.affineOpens, ∃ hW : W.1 ≤ V.1,
      x ∈ W.1 ∧ F.presheaf.map (homOfLE hW).op t ∈ N W) :
    t ∈ N V := by
  set s : Set Γ(X, V.1) := {a | F.presheaf.map (homOfLE (X.basicOpen_le a)).op t ∈
    N ⟨X.basicOpen a, V.2.basicOpen a⟩} with hsdef
  have hspan : Ideal.span s = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨W, hWV, hxW, hmem⟩ := hcov x hx
    obtain ⟨a, ha1, ha2⟩ := V.2.exists_basicOpen_le (⟨x, hxW⟩ : W.1) hx
    have has : a ∈ s := by
      rw [hsdef, Set.mem_ofPred_eq, hN W ⟨X.basicOpen a, V.2.basicOpen a⟩ ha1,
        show (homOfLE (X.basicOpen_le a) : X.basicOpen a ⟶ V.1) =
          homOfLE ha1 ≫ homOfLE hWV from rfl, op_comp, Functor.map_comp_apply]
      exact Submodule.subset_span ⟨_, hmem, rfl⟩
    exact Opens.mem_iSup.mpr ⟨⟨a, has⟩, ha2⟩
  let _i₁ : ∀ r : s, Module Γ(X, V.1) Γ(F, X.basicOpen (r : Γ(X, V.1))) :=
    fun r ↦ moduleOfLE F (X.basicOpen_le _)
  let _i₃ : ∀ r : s, IsScalarTower Γ(X, V.1) Γ(X, X.basicOpen (r : Γ(X, V.1)))
      Γ(F, X.basicOpen (r : Γ(X, V.1))) :=
    fun r ↦ isScalarTowerOfLE F (X.basicOpen_le _)
  let _i₄ : ∀ r : s, IsLocalization.Away (r : Γ(X, V.1))
      Γ(X, X.basicOpen (r : Γ(X, V.1))) := fun r ↦ V.2.isLocalization_basicOpen _
  let _i₂ : ∀ r : s, IsLocalizedModule.Away (r : Γ(X, V.1))
      (restrictₗ F (X.basicOpen_le (r : Γ(X, V.1)))) :=
    fun r ↦ isLocalizedModule_restrictₗ F V.2 _ rfl _
  refine Submodule.mem_of_isLocalized_span s hspan
    (fun r ↦ Γ(F, X.basicOpen (r : Γ(X, V.1))))
    (fun r ↦ restrictₗ F (X.basicOpen_le (r : Γ(X, V.1)))) fun r ↦ ?_
  have hmem : F.presheaf.map (homOfLE (X.basicOpen_le (r : Γ(X, V.1)))).op t ∈
      N ⟨X.basicOpen (r : Γ(X, V.1)), V.2.basicOpen _⟩ := r.2
  rw [hN V ⟨X.basicOpen (r : Γ(X, V.1)), V.2.basicOpen _⟩ (X.basicOpen_le _)] at hmem
  have key : Submodule.localized₀ (Submonoid.powers (r : Γ(X, V.1)))
      (restrictₗ F (X.basicOpen_le (r : Γ(X, V.1)))) (N V) =
      (Submodule.span Γ(X, X.basicOpen (r : Γ(X, V.1)))
        (restrictₗ F (X.basicOpen_le (r : Γ(X, V.1))) ''
          (N V : Set Γ(F, V.1)))).restrictScalars Γ(X, V.1) := by
    rw [← Submodule.restrictScalars_localized' Γ(X, X.basicOpen (r : Γ(X, V.1))),
      Submodule.localized'_eq_span]
  rw [key, Submodule.restrictScalars_mem]
  exact hmem

/-! ### The subsheaf cut out by a compatible family -/

/-- A section of `F` over an open `U` *lies locally in* `N` if its restriction to every affine
open contained in `U` lies in `N`. -/
def IsLocallyIn {U : X.Opens} (s : Γ(F, U)) : Prop :=
  ∀ (W : X.affineOpens) (h : W.1 ≤ U), F.presheaf.map (homOfLE h).op s ∈ N W

/-- The sections over `U` lying locally in `N` form a `Γ(X, U)`-submodule of `Γ(F, U)`. -/
def localSections (U : X.Opens) : Submodule Γ(X, U) Γ(F, U) where
  carrier := {s | IsLocallyIn F N s}
  add_mem' := by
    intro a b ha hb W h
    simpa using add_mem (ha W h) (hb W h)
  zero_mem' := by
    intro W h
    simp
  smul_mem' := by
    intro c s hs W h
    rw [F.map_smul (homOfLE h) c s]
    exact Submodule.smul_mem _ _ (hs W h)

/-- The sections lying locally in `N`, as a submodule of the underlying presheaf of modules of
`F`: the condition only becomes easier to satisfy after restriction. -/
def preSubmodule : F.val.Submodule where
  obj U := localSections F N U.unop
  map {_ Z} f := by
    rintro s hs W h
    have key := hs W (h.trans f.unop.le)
    rw [← res_res F f.unop.le h s] at key
    exact key

/-- **The subsheaf of `F` cut out by a compatible family.**  Lying locally in `N` is a local
condition: the restriction of a section to an affine open `W` lies in `N W` as soon as it does
so on an affine cover of `W`, by `mem_of_cover`, and such a cover is extracted from any
covering sieve because the affine opens of a scheme form a basis. -/
def sheafSubmodule [F.IsQuasicoherent] (hN : IsCompatible F N) : F.Submodule where
  toSubmodule := preSubmodule F N
  isSheaf := by
    intro Y s hs
    obtain ⟨s, rfl⟩ : ∃ y : Γ(F, Y.unop), y = s := ⟨s, rfl⟩
    intro W hW
    refine mem_of_cover F N hN W _ fun x hxW ↦ ?_
    obtain ⟨Z, f, hf, hxZ⟩ := hs x (hW hxW)
    obtain ⟨-, ⟨W', hW'aff, rfl⟩, hxW', hW'le⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((W.1 ⊓ Z : X.Opens) : Set X) from ⟨hxW, hxZ⟩) (W.1 ⊓ Z).isOpen
    have hle : W' ≤ W.1 ⊓ Z := hW'le
    refine ⟨⟨W', hW'aff⟩, hle.trans inf_le_left, hxW', ?_⟩
    replace hf : F.presheaf.map (homOfLE (hle.trans inf_le_right)).op
        (F.presheaf.map (homOfLE f.le).op s) ∈ N ⟨W', hW'aff⟩ :=
      hf ⟨W', hW'aff⟩ (hle.trans inf_le_right)
    rw [res_res] at hf
    rw [res_res]
    exact hf

/-- The sections of `sheafSubmodule F N hN` over an affine open `U` are exactly `N U`. -/
theorem obj_sheafSubmodule [F.IsQuasicoherent] (hN : IsCompatible F N) (U : X.affineOpens) :
    (sheafSubmodule F N hN).toSubmodule.obj (op U.1) = N U := by
  refine SetLike.ext fun s ↦ ?_
  obtain ⟨s, rfl⟩ : ∃ y : Γ(F, U.1), y = s := ⟨s, rfl⟩
  refine ⟨fun hs ↦ ?_, fun hs W h ↦ ?_⟩
  · have h1 := hs U (le_refl U.1)
    rwa [res_self] at h1
  · rw [hN U W h]
    exact Submodule.subset_span ⟨s, hs, rfl⟩

end Stacks.AlgebraicGeometry.GabberColimit

end
