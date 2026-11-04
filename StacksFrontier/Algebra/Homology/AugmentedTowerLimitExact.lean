module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# The limit of a tower of augmented exact complexes with surjective transitions

Let `K₀ ← K₁ ← K₂ ← ⋯` be a tower of cochain complexes of abelian groups indexed by `ℕ`, each
augmented by a group `Aₙ ⟶ Kₙ⁰` so that `Aₙ ⟶ Kₙ⁰ ⟶ Kₙ¹ ⟶ ⋯` is exact, and assume that the
transition maps `Aₙ₊₁ ⟶ Aₙ` and `Kₙ₊₁ᵖ ⟶ Kₙᵖ` are surjective. Then the inverse limit
`lim Kₙ` is exact in every positive degree.

This is the Mittag-Leffler argument of Homology, Lemma 0598 in the form the computation of the
cohomology of the structure sheaf of a countably indexed affine formal algebraic space uses
(Stacks 0DEL): a compatible family of cocycles is the coboundary of a compatible family, the
family of preimages being corrected stage by stage by a coboundary — or, in degree one, by an
augmentation — lifted along the surjective transition maps.

## Main results

* `Stacks.AugmentedTower.exactAt_succ_of_isLimit`: the statement above, for a cone over the
  tower which is a limit cone degreewise.

## Implementation notes

The limit is an arbitrary cone whose degreewise images are limit cones, rather than the chosen
limit of the tower: the application is to the Čech complex of a limit of presheaves, which is a
limit of Čech complexes degreewise but is not literally the chosen limit. The degreewise limit
property enters only through the two facts that the cone projections are jointly injective and
that every compatible family lifts, which are extracted once from Mathlib's description of
limits of abelian groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v

namespace Stacks.AugmentedTower

variable {K : ℕᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ}

/-- The transition morphism `Kₙ₊₁ ⟶ Kₙ` of a tower of complexes. -/
noncomputable abbrev tr (K : ℕᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ) (n : ℕ) :
    K.obj (op (n + 1)) ⟶ K.obj (op n) :=
  K.map (homOfLE (Nat.le_succ n)).op

/-- The transition maps commute with the differentials, on elements. -/
theorem tr_d_apply (n p q : ℕ) (y : (K.obj (op (n + 1))).X p) :
    (tr K n).f q ((K.obj (op (n + 1))).d p q y) = (K.obj (op n)).d p q ((tr K n).f p y) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (tr K n).comm]

/-- Two consecutive differentials compose to zero, on elements. -/
theorem d_d_apply (L : CochainComplex AddCommGrpCat.{v} ℕ) (p q r : ℕ) (y : L.X p) :
    L.d q r (L.d p q y) = 0 := by
  rw [← ConcreteCategory.comp_apply, L.d_comp_d, AddCommGrpCat.zero_apply]

/-- A cone over a tower of complexes, in which every cocycle family lifts along the tower:
the projections of the cone commute with the differentials, on elements. -/
theorem π_d_apply (c : Cone K) (n p q : ℕ) (x : c.pt.X p) :
    (c.π.app (op n)).f q (c.pt.d p q x) = (K.obj (op n)).d p q ((c.π.app (op n)).f p x) :=
  (ConcreteCategory.congr_hom ((c.π.app (op n)).comm p q) x).symm

/-- The cone projections followed by a transition are the cone projections, on elements. -/
theorem tr_π_apply (c : Cone K) (n p : ℕ) (x : c.pt.X p) :
    (tr K n).f p ((c.π.app (op (n + 1))).f p x) = (c.π.app (op n)).f p x := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, Cone.w]

/-- One step of the Mittag-Leffler argument: a primitive at stage `n` of a compatible family of
cocycles extends to a primitive at stage `n + 1` lying over it. -/
theorem step_exists (A : ℕ → AddCommGrpCat.{v}) (a : ∀ n, A (n + 1) ⟶ A n)
    (ε : ∀ n, A n ⟶ (K.obj (op n)).X 0)
    (hε : ∀ n (s : A (n + 1)), ε n (a n s) = (tr K n).f 0 (ε (n + 1) s))
    (hεd : ∀ n (s : A n), (K.obj (op n)).d 0 1 (ε n s) = 0)
    (hexact₀ : ∀ n (z : (K.obj (op n)).X 0), (K.obj (op n)).d 0 1 z = 0 → ∃ s, ε n s = z)
    (hexact : ∀ n q (z : (K.obj (op n)).X (q + 1)),
      (K.obj (op n)).d (q + 1) (q + 2) z = 0 → ∃ y, (K.obj (op n)).d q (q + 1) y = z)
    (hsurjA : ∀ n, Function.Surjective (a n))
    (hsurj : ∀ n q, Function.Surjective ((tr K n).f q))
    (p : ℕ) (z : ∀ n, (K.obj (op n)).X (p + 1))
    (hztr : ∀ n, (tr K n).f (p + 1) (z (n + 1)) = z n)
    (n : ℕ) (y : (K.obj (op n)).X p) (hy : (K.obj (op n)).d p (p + 1) y = z n)
    (y₀ : (K.obj (op (n + 1))).X p) (hy₀ : (K.obj (op (n + 1))).d p (p + 1) y₀ = z (n + 1)) :
    ∃ y' : (K.obj (op (n + 1))).X p, (K.obj (op (n + 1))).d p (p + 1) y' = z (n + 1) ∧
      (tr K n).f p y' = y := by
  have hdiff : (K.obj (op n)).d p (p + 1) ((tr K n).f p y₀ - y) = 0 := by
    rw [map_sub, ← tr_d_apply, hy₀, hztr, hy, sub_self]
  cases p with
  | zero =>
    obtain ⟨s, hs⟩ := hexact₀ n _ hdiff
    obtain ⟨s', rfl⟩ := hsurjA n s
    refine ⟨y₀ - ε (n + 1) s', ?_, ?_⟩
    · rw [map_sub, hy₀, hεd, sub_zero]
    · rw [map_sub, ← hε, hs, sub_sub_cancel]
  | succ q =>
    obtain ⟨w, hw⟩ := hexact n q _ hdiff
    obtain ⟨w', rfl⟩ := hsurj n q w
    refine ⟨y₀ - (K.obj (op (n + 1))).d q (q + 1) w', ?_, ?_⟩
    · rw [map_sub, hy₀, d_d_apply, sub_zero]
    · rw [map_sub, tr_d_apply, hw, sub_sub_cancel]

/-- **The Mittag-Leffler argument for a tower of augmented exact complexes.** Let `c` be a cone
over a tower `K` of cochain complexes of abelian groups whose projections are jointly injective
in each degree and through which every compatible family lifts. Assume each `Kₙ` is exact in
positive degrees, is augmented by `εₙ : Aₙ ⟶ Kₙ⁰` with image the kernel of the first
differential, compatibly with surjective maps `Aₙ₊₁ ⟶ Aₙ`, and that the transition maps of `K`
are surjective in every degree. Then the cone point is exact in every positive degree. -/
theorem exactAt_succ (c : Cone K)
    (hinj : ∀ (p : ℕ) (x y : c.pt.X p),
      (∀ n, (c.π.app (op n)).f p x = (c.π.app (op n)).f p y) → x = y)
    (hlift : ∀ (p : ℕ) (y : ∀ n, (K.obj (op n)).X p),
      (∀ n, (tr K n).f p (y (n + 1)) = y n) → ∃ x : c.pt.X p, ∀ n, (c.π.app (op n)).f p x = y n)
    (A : ℕ → AddCommGrpCat.{v}) (a : ∀ n, A (n + 1) ⟶ A n)
    (ε : ∀ n, A n ⟶ (K.obj (op n)).X 0)
    (hε : ∀ n (s : A (n + 1)), ε n (a n s) = (tr K n).f 0 (ε (n + 1) s))
    (hεd : ∀ n (s : A n), (K.obj (op n)).d 0 1 (ε n s) = 0)
    (hexact₀ : ∀ n (z : (K.obj (op n)).X 0), (K.obj (op n)).d 0 1 z = 0 → ∃ s, ε n s = z)
    (hexact : ∀ n q (z : (K.obj (op n)).X (q + 1)),
      (K.obj (op n)).d (q + 1) (q + 2) z = 0 → ∃ y, (K.obj (op n)).d q (q + 1) y = z)
    (hsurjA : ∀ n, Function.Surjective (a n))
    (hsurj : ∀ n q, Function.Surjective ((tr K n).f q))
    (p : ℕ) : c.pt.ExactAt (p + 1) := by
  classical
  rw [HomologicalComplex.exactAt_iff' c.pt p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro z hz
  change c.pt.d (p + 1) (p + 2) z = 0 at hz
  -- the images of the cocycle in the tower
  let zₙ : ∀ n, (K.obj (op n)).X (p + 1) := fun n ↦ (c.π.app (op n)).f (p + 1) z
  have hzₙ : ∀ n, (K.obj (op n)).d (p + 1) (p + 2) (zₙ n) = 0 := fun n ↦ by
    rw [← π_d_apply c n (p + 1) (p + 2) z, hz, map_zero]
  -- one step of the construction of a compatible family of primitives
  have step : ∀ (n : ℕ) (y : (K.obj (op n)).X p), (K.obj (op n)).d p (p + 1) y = zₙ n →
      ∃ y' : (K.obj (op (n + 1))).X p, (K.obj (op (n + 1))).d p (p + 1) y' = zₙ (n + 1) ∧
        (tr K n).f p y' = y := fun n y hy ↦
    (hexact (n + 1) p (zₙ (n + 1)) (hzₙ (n + 1))).elim <| step_exists A a ε hε hεd hexact₀ hexact
      hsurjA hsurj p zₙ (fun n ↦ tr_π_apply c n (p + 1) z) n y hy
  choose Z hZ₁ hZ₂ using step
  obtain ⟨y₀, hy₀⟩ := hexact 0 p (zₙ 0) (hzₙ 0)
  let Y : ∀ n, { y : (K.obj (op n)).X p // (K.obj (op n)).d p (p + 1) y = zₙ n } := fun n ↦
    Nat.rec (motive := fun n ↦ { y : (K.obj (op n)).X p // (K.obj (op n)).d p (p + 1) y = zₙ n })
      ⟨y₀, hy₀⟩ (fun n ih ↦ ⟨Z n ih.1 ih.2, hZ₁ n ih.1 ih.2⟩) n
  obtain ⟨x, hx⟩ := hlift p (fun n ↦ (Y n).1) (fun n ↦ hZ₂ n (Y n).1 (Y n).2)
  refine ⟨x, hinj (p + 1) _ _ fun n ↦ ?_⟩
  show (c.π.app (op n)).f (p + 1) (c.pt.d p (p + 1) x) = zₙ n
  rw [π_d_apply, hx, (Y n).2]

/-- The projections of a cone which is a limit cone in degree `p` are jointly injective. -/
theorem injective_of_isLimit (c : Cone K) (p : ℕ)
    (hc : IsLimit ((HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℕ) p).mapCone c))
    (x y : c.pt.X p) (h : ∀ n, (c.π.app (op n)).f p x = (c.π.app (op n)).f p y) : x = y :=
  Concrete.isLimit_ext _ hc _ _ fun ⟨n⟩ ↦ h n

/-- Every compatible family lifts through a cone which is a limit cone in degree `p`. -/
theorem exists_lift_of_isLimit (c : Cone K) (p : ℕ)
    (hc : IsLimit ((HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℕ) p).mapCone c))
    (y : ∀ n, (K.obj (op n)).X p) (hy : ∀ n, (tr K n).f p (y (n + 1)) = y n) :
    ∃ x : c.pt.X p, ∀ n, (c.π.app (op n)).f p x = y n := by
  have hc' := isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{v}) hc
  have hcomp : ∀ (i j : ℕ) (h : i ≤ j), (K.map (homOfLE h).op).f p (y j) = y i := by
    intro i j h
    induction j, h using Nat.le_induction with
    | base =>
      rw [show (homOfLE (le_refl i)).op = 𝟙 (op i) from rfl, K.map_id]
      rfl
    | succ j hij ih =>
      rw [show (homOfLE (hij.trans (Nat.le_succ j))).op =
          (homOfLE (Nat.le_succ j)).op ≫ (homOfLE hij).op from rfl, K.map_comp,
        HomologicalComplex.comp_f, ConcreteCategory.comp_apply, hy j, ih]
  let sec : ((K ⋙ HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℕ) p) ⋙
      CategoryTheory.forget AddCommGrpCat.{v}).sections :=
    ⟨fun j ↦ y j.unop, fun g ↦ hcomp _ _ (leOfHom g.unop)⟩
  exact ⟨(Types.isLimitEquivSections hc').symm sec, fun n ↦
    Types.isLimitEquivSections_symm_apply hc' sec (op n)⟩

end Stacks.AugmentedTower

end
