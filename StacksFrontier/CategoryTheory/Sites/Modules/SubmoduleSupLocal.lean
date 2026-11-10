module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSiteSections
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteSubfamily
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleFilteredColimitSections

/-!
# Suprema of submodules of a sheaf of modules, and quasi-compact objects

Let `(C, J)` be a site and `M` a sheaf of modules over a sheaf of rings on it.  This file records
two facts about the lattice of submodules of `M` with local membership.

* The supremum `N₁ ⊔ N₂` consists of the sections which are locally sums of a section of `N₁`
  and a section of `N₂`.
* Over a quasi-compact object of the site, a section which lies locally in some member of a
  directed family of submodules lies in one member.

## Main results

* `Stacks.SheafOfModules.sup_eq_sheafifySubmodule`: `N₁ ⊔ N₂` is the closure of the objectwise
  sum.
* `Stacks.SheafOfModules.mem_sup_iff`: the sections of `N₁ ⊔ N₂` are the local sums.
* `Stacks.SheafOfModules.exists_mem_of_isQuasiCompactObject`: a section over a quasi-compact
  object lying locally in members of a directed family lies in one member.

## References

* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public section

open CategoryTheory Opposite

universe w u₁ v₁ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{w} R}

/-- The supremum of two submodules with local membership is the closure of their objectwise
sum. -/
theorem sup_eq_sheafifySubmodule (N₁ N₂ : M.Submodule) :
    N₁ ⊔ N₂ = sheafifySubmodule (N₁.toSubmodule ⊔ N₂.toSubmodule) :=
  le_antisymm
    (sup_le
      ((sheafifySubmodule_toSubmodule N₁).symm.le.trans (sheafifySubmodule_mono le_sup_left))
      ((sheafifySubmodule_toSubmodule N₂).symm.le.trans (sheafifySubmodule_mono le_sup_right)))
    (sheafifySubmodule_le (sup_le
      (_root_.SheafOfModules.Submodule.le_iff.1 le_sup_left)
      (_root_.SheafOfModules.Submodule.le_iff.1 le_sup_right)))

/-- **The sections of `N₁ ⊔ N₂` are the local sums**: a section lies in the supremum of two
submodules with local membership exactly when, along every arrow of some covering sieve, it
restricts to a sum of a section of `N₁` and a section of `N₂`. -/
theorem mem_sup_iff {N₁ N₂ : M.Submodule} {X : Cᵒᵖ} {x : M.val.obj X} :
    x ∈ (N₁ ⊔ N₂).obj X ↔
      ∃ S : Sieve X.unop, S ∈ J X.unop ∧ ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f →
        ∃ a ∈ N₁.obj (op Y), ∃ b ∈ N₂.obj (op Y), a + b = M.val.map f.op x := by
  rw [sup_eq_sheafifySubmodule, mem_sheafifySubmodule_iff]
  exact exists_congr fun S => and_congr_right fun _ => forall₃_congr fun Y _ _ =>
    Submodule.mem_sup (p := N₁.obj (op Y)) (p' := N₂.obj (op Y))

/-- **A section over a quasi-compact object lying locally in members of a directed family of
submodules lies in one of them.**  Finitely many arrows of the covering sieve already cover the
object (Stacks 090H); a member containing the finitely many members used along them contains
the restrictions of the section along a covering family, hence the section, membership being
local. -/
theorem exists_mem_of_isQuasiCompactObject {ι : Type*} [Nonempty ι] (N : ι → M.Submodule)
    (hN : Directed (· ≤ ·) N) {Z : C} (hZ : J.IsQuasiCompactObject Z) (x : M.val.obj (op Z))
    (S : Sieve Z) (hS : S ∈ J Z)
    (hx : ∀ ⦃Y : C⦄ (f : Y ⟶ Z), S f → ∃ i, M.val.map f.op x ∈ (N i).obj (op Y)) :
    ∃ i, x ∈ (N i).obj (op Z) := by
  classical
  obtain ⟨κ, hκ, V, f, hf, hcov⟩ :=
    GrothendieckTopology.exists_finite_ofArrows_mem_of_isQuasiCompactObject hZ S.arrows
      (by rwa [Sieve.generate_sieve])
  choose i hi using fun k => hx (f k) (hf k)
  have := Fintype.ofFinite κ
  obtain ⟨i₀, hi₀⟩ := hN.finset_le (Finset.univ.image i)
  refine ⟨i₀, (N i₀).isSheaf x (J.superset_covering ?_ hcov)⟩
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨k⟩
  exact _root_.SheafOfModules.Submodule.le_iff.1
    (hi₀ (i k) (Finset.mem_image_of_mem _ (Finset.mem_univ k))) _ (hi k)

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

section FiniteType

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The supremum of two submodules of finite type is of finite type.** -/
theorem isFiniteType_sup (N₁ N₂ : M.Submodule) (h₁ : N₁.toSheafOfModules.IsFiniteType)
    (h₂ : N₂.toSheafOfModules.IsFiniteType) : (N₁ ⊔ N₂).toSheafOfModules.IsFiniteType := by
  classical
  obtain ⟨I₁, U₁, hU₁, hg₁⟩ :=
    (isFiniteTypeSections_of_isFiniteType' (J := J) N₁.toSheafOfModules h₁).exists_generators
  obtain ⟨I₂, U₂, hU₂, hg₂⟩ :=
    (isFiniteTypeSections_of_isFiniteType' (J := J) N₂.toSheafOfModules h₂).exists_generators
  choose n₁ s₁ hs₁ using hg₁
  choose n₂ s₂ hs₂ using hg₂
  let K := {Z : C // ∃ i j, Nonempty (Z ⟶ U₁ i) ∧ Nonempty (Z ⟶ U₂ j)}
  choose i₁ i₂ hK using fun k : K => k.2
  let f₁ : ∀ k : K, k.1 ⟶ U₁ (i₁ k) := fun k => (hK k).1.some
  let f₂ : ∀ k : K, k.1 ⟶ U₂ (i₂ k) := fun k => (hK k).2.some
  have hW : J.CoversTop (fun k : K => k.1) := by
    intro Z
    refine J.superset_covering ?_ (J.intersection_covering (hU₁ Z) (hU₂ Z))
    intro T f hf
    obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff U₁ f).mp hf.1
    obtain ⟨j, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff U₂ f).mp hf.2
    exact (Sieve.mem_ofObjects_iff _ f).2 ⟨⟨T, i, j, ⟨a⟩, ⟨b⟩⟩, ⟨𝟙 T⟩⟩
  let e₁ := Submodule.homOfLE (le_sup_left : N₁ ≤ N₁ ⊔ N₂)
  let e₂ := Submodule.homOfLE (le_sup_right : N₂ ≤ N₁ ⊔ N₂)
  let gen : ∀ k : K, Fin (n₁ (i₁ k) + n₂ (i₂ k)) → (N₁ ⊔ N₂).toSheafOfModules.val.obj (op k.1) :=
    fun k => Fin.append
      (fun a => e₁.val.app _ (N₁.toSheafOfModules.val.restrictₛₗ (f₁ k).op (s₁ (i₁ k) a)))
      (fun b => e₂.val.app _ (N₂.toSheafOfModules.val.restrictₛₗ (f₂ k).op (s₂ (i₂ k) b)))
  refine isFiniteType_of_isFiniteTypeSections' _
    ⟨⟨K, fun k => k.1, hW, fun k => ⟨_, gen k, fun V f t => ?_⟩⟩⟩
  obtain ⟨T, hT, hsum⟩ := mem_sup_iff.1 t.2
  choose a ha b hb hab using hsum
  choose S₁ hS₁ c₁ using fun ⦃Y : C⦄ (g : Y ⟶ V) (hg : T g) =>
    generatesLocally_restrict (f₁ k) (hs₁ (i₁ k)) Y (g ≫ f) ⟨a g hg, ha g hg⟩
  choose S₂ hS₂ c₂ using fun ⦃Y : C⦄ (g : Y ⟶ V) (hg : T g) =>
    generatesLocally_restrict (f₂ k) (hs₂ (i₂ k)) Y (g ≫ f) ⟨b g hg, hb g hg⟩
  refine ⟨Sieve.bind T.arrows (fun Y g hg => S₁ g hg ⊓ S₂ g hg),
    J.bind_covering hT fun Y g hg => J.intersection_covering (hS₁ g hg) (hS₂ g hg), ?_⟩
  rintro W _ ⟨Y, h, g, hg, ⟨hh₁, hh₂⟩, rfl⟩
  obtain ⟨d₁, hd₁⟩ := c₁ g hg W h hh₁
  obtain ⟨d₂, hd₂⟩ := c₂ g hg W h hh₂
  refine ⟨Fin.append d₁ d₂, ?_⟩
  have hn : ∀ (N : M.Submodule) (e : N.toSheafOfModules ⟶ (N₁ ⊔ N₂).toSheafOfModules) (U : C)
      (u : k.1 ⟶ U) (x : N.toSheafOfModules.val.obj (op U)),
      (N₁ ⊔ N₂).toSheafOfModules.val.restrictₛₗ ((h ≫ g) ≫ f).op
          (e.val.app _ (N.toSheafOfModules.val.restrictₛₗ u.op x)) =
        e.val.app _ (N.toSheafOfModules.val.restrictₛₗ (h ≫ g ≫ f).op
          (N.toSheafOfModules.val.restrictₛₗ u.op x)) := fun _ e _ u x => by
    rw [Category.assoc]
    exact (PresheafOfModules.naturality_apply e.val _ _).symm
  rw [Fin.sum_univ_add]
  simp only [gen, Fin.append_left, Fin.append_right, hn, ← map_smul, ← map_sum, hd₁, hd₂]
  apply Subtype.ext
  change M.val.map h.op (a g hg) + M.val.map h.op (b g hg) = M.val.map (h ≫ g).op t.1
  rw [← map_add, hab g hg, op_comp]
  exact (M.val.map_comp_apply g.op h.op t.1).symm

end FiniteType

end Stacks.SheafOfModules

end
