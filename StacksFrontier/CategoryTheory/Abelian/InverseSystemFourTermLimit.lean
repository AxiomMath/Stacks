module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumCompletedSections

/-!
# Limits of four-term exact sequences of inverse systems of modules

Let `0 → X₁ → X₂ → X₃ → X₄ → 0` be an exact sequence of inverse systems of modules indexed by
`ℕ`, and let `0 → P₁ → P₂ → P₃ → P₄ → 0` be an exact sequence of modules mapping compatibly to
it, i.e. cones `cᵢ` over the `Xᵢ` with points `Pᵢ`. If `c₁`, `c₂` and `c₄` are limit cones and
`X₁` satisfies the Mittag-Leffler condition, then `c₃` is a limit cone.

This is the five lemma combined with the exactness of `lim` on short exact sequences whose kernel
system is Mittag-Leffler; the Mittag-Leffler condition enters only through the vanishing of
`R¹lim X₁`, in the form of the surjectivity of the difference map
`(xₙ) ↦ (xₙ - x_{n+1}|ₙ)` on `∏ₙ X₁(n)`
(`Stacks.Algebraization.epi_milnorDifference_of_isMittagLefflerCategorical`).

## Main results

* `ModuleCat.InverseSystem.nonempty_isLimit_iff` — a cone over an inverse system of modules is a
  limit cone exactly when every family compatible along the successor maps has a unique
  preimage.
* `ModuleCat.InverseSystem.nonempty_isLimit_of_fourTerm` — the statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace ModuleCat.InverseSystem

variable {R : Type u} [Ring R]

/-- A family compatible along the successor maps is compatible along all transition maps. -/
theorem map_eq_of_succ {F : ℕᵒᵖ ⥤ ModuleCat.{u} R} (x : ∀ n : ℕ, F.obj (op n))
    (hx : ∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n)
    {m n : ℕ} (h : n ≤ m) : F.map (homOfLE h).op (x m) = x n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have hcomp : (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := rfl
    rw [hcomp, Functor.map_comp, ModuleCat.comp_apply, hx, ih]

/-- The projections of a cone over `F : ℕᵒᵖ ⥤ ModuleCat R` are compatible along successor maps. -/
private theorem map_succ_apply_π {F : ℕᵒᵖ ⥤ ModuleCat.{u} R} (c : Cone F) (n : ℕ) (p : c.pt) :
    F.map (homOfLE (Nat.le_succ n)).op (c.π.app (op (n + 1)) p) = c.π.app (op n) p :=
  ConcreteCategory.congr_hom (c.w (homOfLE (Nat.le_succ n)).op) p

/-- A point of a cone with the elementwise limit property is determined by its projections. -/
private theorem eq_of_forall_π_eq {F : ℕᵒᵖ ⥤ ModuleCat.{u} R} (c : Cone F)
    (e : ∀ x : ∀ n : ℕ, F.obj (op n),
      (∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n) →
        ∃! p : c.pt, ∀ n : ℕ, c.π.app (op n) p = x n)
    {p q : c.pt} (hpq : ∀ n, c.π.app (op n) p = c.π.app (op n) q) : p = q := by
  obtain ⟨r, -, hr⟩ := e (fun n ↦ c.π.app (op n) q) (map_succ_apply_π c · q)
  exact (hr p hpq).trans (hr q fun _ ↦ rfl).symm

/-- **Limit cones over an inverse system of modules, elementwise.** A cone `c` over
`F : ℕᵒᵖ ⥤ ModuleCat R` is a limit cone exactly when every family `xₙ ∈ F(n)` compatible along
the successor maps is the family of projections of a unique point of `c`. -/
theorem nonempty_isLimit_iff {F : ℕᵒᵖ ⥤ ModuleCat.{u} R} (c : Cone F) :
    Nonempty (IsLimit c) ↔
      ∀ x : ∀ n : ℕ, F.obj (op n),
        (∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n) →
          ∃! p : c.pt, ∀ n : ℕ, c.π.app (op n) p = x n := by
  constructor
  · rintro ⟨hc⟩ x hx
    let hc' := isLimitOfPreserves (forget (ModuleCat.{u} R)) hc
    have hsec : (fun j : ℕᵒᵖ ↦ x j.unop) ∈ (F ⋙ forget (ModuleCat.{u} R)).sections := by
      intro j k f
      have hjk : k.unop ≤ j.unop := leOfHom f.unop
      have hf : f = (homOfLE hjk).op := Subsingleton.elim _ _
      subst hf
      exact map_eq_of_succ x hx hjk
    obtain ⟨p, hp⟩ :=
      ((Types.isLimit_iff_bijective_sectionOfCone _).1 ⟨hc'⟩).2 ⟨_, hsec⟩
    refine ⟨p, fun n ↦ congrArg (fun s ↦ s.1 (op n)) hp, fun q hq ↦ ?_⟩
    refine ((Types.isLimit_iff_bijective_sectionOfCone _).1 ⟨hc'⟩).1 ?_
    rw [hp]
    exact Subtype.ext (funext fun j ↦ hq j.unop)
  · intro h
    have hbij : (Types.sectionOfCone ((forget (ModuleCat.{u} R)).mapCone c)).Bijective := by
      refine ⟨fun p q hpq ↦ ?_, fun s ↦ ?_⟩
      · exact eq_of_forall_π_eq c h fun n ↦ congrFun (congrArg Subtype.val hpq) (op n)
      · obtain ⟨p, hp, -⟩ := h (fun n ↦ s.1 (op n)) (fun n ↦ s.2 _)
        exact ⟨p, Subtype.ext (funext fun j ↦ hp j.unop)⟩
    obtain ⟨hc⟩ := (Types.isLimit_iff_bijective_sectionOfCone _).2 hbij
    exact ⟨isLimitOfReflects (forget (ModuleCat.{u} R)) hc⟩

/-- **The difference map of a Mittag-Leffler system is surjective**, elementwise: for every
family `kₙ ∈ X(n)` there is a family `aₙ` with `aₙ - a_{n+1}|ₙ = kₙ`. -/
theorem exists_sub_map_eq_of_isMittagLefflerCategorical {X : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    (hX : IsMittagLefflerCategorical X) (k : ∀ n : ℕ, X.obj (op n)) :
    ∃ a : ∀ n : ℕ, X.obj (op n),
      ∀ n : ℕ, a n - X.map (homOfLE (Nat.le_succ n)).op (a (n + 1)) = k n := by
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective _).1
    (Stacks.Algebraization.epi_milnorDifference_of_isMittagLefflerCategorical X hX)
    ((ModuleCat.piIsoPi (fun n : ℕ ↦ X.obj (op n))).inv k)
  refine ⟨fun n ↦ Pi.π (fun n : ℕ ↦ X.obj (op n)) n a, fun n ↦ ?_⟩
  have h := congrArg (Pi.π (fun n : ℕ ↦ X.obj (op n)) n) ha
  rw [← ModuleCat.comp_apply, Pi.lift_π, ← ModuleCat.comp_apply,
    ModuleCat.piIsoPi_inv_kernel_ι] at h
  simpa [ModuleCat.comp_apply] using h

/-- **The five lemma for limits of four-term exact sequences of inverse systems.** Let
`0 → X₁ → X₂ → X₃ → X₄ → 0` be exact at every level, let `0 → P₁ → P₂ → P₃ → P₄ → 0` be an
exact sequence of modules, and let `cᵢ` be cones over the `Xᵢ` with points `Pᵢ` compatible with
both sequences. If `c₁`, `c₂` and `c₄` are limit cones and `X₁` is Mittag-Leffler, then `c₃` is a
limit cone. -/
theorem nonempty_isLimit_of_fourTerm {X₁ X₂ X₃ X₄ : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄)
    (hf₁ : ∀ n : ℕ, Function.Injective (f₁.app (op n)))
    (hf₁₂ : ∀ n : ℕ, Function.Exact (f₁.app (op n)) (f₂.app (op n)))
    (hf₂₃ : ∀ n : ℕ, Function.Exact (f₂.app (op n)) (f₃.app (op n)))
    (hX₁ : IsMittagLefflerCategorical X₁)
    (c₁ : Cone X₁) (c₂ : Cone X₂) (c₃ : Cone X₃) (c₄ : Cone X₄)
    (g₁ : c₁.pt ⟶ c₂.pt) (g₂ : c₂.pt ⟶ c₃.pt) (g₃ : c₃.pt ⟶ c₄.pt)
    (hg₁₂ : Function.Exact g₁ g₂) (hg₂₃ : Function.Exact g₂ g₃) (hg₃ : Function.Surjective g₃)
    (w₁ : ∀ n : ℕ, g₁ ≫ c₂.π.app (op n) = c₁.π.app (op n) ≫ f₁.app (op n))
    (w₂ : ∀ n : ℕ, g₂ ≫ c₃.π.app (op n) = c₂.π.app (op n) ≫ f₂.app (op n))
    (w₃ : ∀ n : ℕ, g₃ ≫ c₄.π.app (op n) = c₃.π.app (op n) ≫ f₃.app (op n))
    (h₁ : IsLimit c₁) (h₂ : IsLimit c₂) (h₄ : IsLimit c₄) : Nonempty (IsLimit c₃) := by
  have e₁ := (nonempty_isLimit_iff c₁).1 ⟨h₁⟩
  have e₂ := (nonempty_isLimit_iff c₂).1 ⟨h₂⟩
  have e₄ := (nonempty_isLimit_iff c₄).1 ⟨h₄⟩
  have w₁' : ∀ n x, c₂.π.app (op n) (g₁ x) = f₁.app (op n) (c₁.π.app (op n) x) := fun n x ↦
    ConcreteCategory.congr_hom (w₁ n) x
  have w₂' : ∀ n x, c₃.π.app (op n) (g₂ x) = f₂.app (op n) (c₂.π.app (op n) x) := fun n x ↦
    ConcreteCategory.congr_hom (w₂ n) x
  have w₃' : ∀ n x, c₄.π.app (op n) (g₃ x) = f₃.app (op n) (c₃.π.app (op n) x) := fun n x ↦
    ConcreteCategory.congr_hom (w₃ n) x
  have nat : ∀ {X Y : ℕᵒᵖ ⥤ ModuleCat.{u} R} (f : X ⟶ Y) (n : ℕ) (x : X.obj (op (n + 1))),
      Y.map (homOfLE (Nat.le_succ n)).op (f.app (op (n + 1)) x) =
        f.app (op n) (X.map (homOfLE (Nat.le_succ n)).op x) := fun f n x ↦
    (ConcreteCategory.congr_hom (f.naturality (homOfLE (Nat.le_succ n)).op) x).symm
  refine (nonempty_isLimit_iff c₃).2 fun y hy ↦ ?_
  -- existence
  obtain ⟨p₄, hp₄, -⟩ := e₄ (fun n ↦ f₃.app (op n) (y n)) (fun n ↦ by rw [nat, hy])
  obtain ⟨p₃', rfl⟩ := hg₃ p₄
  set z : ∀ n : ℕ, X₃.obj (op n) := fun n ↦ y n - c₃.π.app (op n) p₃' with hz
  have hz₃ : ∀ n, f₃.app (op n) (z n) = 0 := fun n ↦ by
    rw [hz, map_sub, ← w₃', hp₄, sub_self]
  have hzc : ∀ n, X₃.map (homOfLE (Nat.le_succ n)).op (z (n + 1)) = z n := fun n ↦ by
    simp only [hz, map_sub, hy, map_succ_apply_π]
  choose w hw using fun n ↦ (hf₂₃ n (z n)).1 (hz₃ n)
  have hdef : ∀ n, f₂.app (op n) (w n - X₂.map (homOfLE (Nat.le_succ n)).op (w (n + 1))) = 0 :=
    fun n ↦ by rw [map_sub, ← nat, hw, hw, hzc, sub_self]
  choose k hk using fun n ↦ (hf₁₂ n _).1 (hdef n)
  obtain ⟨a, ha⟩ := exists_sub_map_eq_of_isMittagLefflerCategorical hX₁ k
  set w' : ∀ n : ℕ, X₂.obj (op n) := fun n ↦ w n - f₁.app (op n) (a n) with hw'
  have hw'c : ∀ n, X₂.map (homOfLE (Nat.le_succ n)).op (w' (n + 1)) = w' n := fun n ↦ by
    have h1 := hk n
    rw [← ha n, map_sub, ← nat] at h1
    simp only [hw', map_sub]
    rw [eq_sub_iff_add_eq] at h1 ⊢
    rw [← h1]
    abel
  obtain ⟨q, hq, -⟩ := e₂ w' hw'c
  have hex : ∀ n, c₃.π.app (op n) (p₃' + g₂ q) = y n := fun n ↦ by
    rw [map_add, w₂', hq, hw', map_sub, (hf₁₂ n _).2 ⟨a n, rfl⟩, sub_zero, hw, hz, add_sub_cancel]
  refine ⟨p₃' + g₂ q, hex, fun p hp ↦ ?_⟩
  -- uniqueness: it suffices that a point with zero projections is zero
  suffices h0 : ∀ r : c₃.pt, (∀ n, c₃.π.app (op n) r = 0) → r = 0 from
    sub_eq_zero.1 (h0 _ fun n ↦ by rw [map_sub, hp n, hex n, sub_self])
  intro r hr
  have hr₄ : g₃ r = 0 := eq_of_forall_π_eq c₄ e₄ fun n ↦ by rw [w₃', hr, map_zero, map_zero]
  obtain ⟨t, rfl⟩ := (hg₂₃ r).1 hr₄
  have ht : ∀ n, f₂.app (op n) (c₂.π.app (op n) t) = 0 := fun n ↦ by rw [← w₂', hr]
  choose v hv using fun n ↦ (hf₁₂ n _).1 (ht n)
  have hvc : ∀ n, X₁.map (homOfLE (Nat.le_succ n)).op (v (n + 1)) = v n := fun n ↦ by
    apply hf₁ n
    rw [← nat, hv, hv, map_succ_apply_π]
  obtain ⟨o, ho, -⟩ := e₁ v hvc
  exact (hg₁₂ _).2 ⟨o, eq_of_forall_π_eq c₂ e₂ fun n ↦ by rw [w₁', ho, hv]⟩

end ModuleCat.InverseSystem

end
