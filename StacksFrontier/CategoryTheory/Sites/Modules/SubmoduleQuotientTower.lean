module

public import StacksFrontier.CategoryTheory.Sites.Modules.IdealPowerSmul
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tower of quotients of a sheaf of modules by an antitone family of submodules

Let `(C, J)` be a site, `O` a sheaf of commutative rings on it and `ℱ` a sheaf of `O`-modules.
A decreasing family `N₀ ⊇ N₁ ⊇ ⋯` of submodules of `ℱ` gives a tower `n ↦ ℱ/Nₙ` of quotients,
indexed by `ℕᵒᵖ`, whose transition maps are the maps on quotients induced by the containments.
This file constructs that tower and, for a sheaf of ideals `ℐ ⊆ O`, the case

`n ↦ ℱ/ℐⁿ⁺¹ℱ`

of it, the **adic quotient tower at the coefficient `ℱ`**.

## Main definitions

* `Stacks.SheafOfModules.Submodule.quotientMapOfLE`: the map `ℱ/N₁ ⟶ ℱ/N₂` induced by a
  containment `N₁ ⊆ N₂` of submodules of `ℱ`.
* `Stacks.Sites.submoduleQuotientTower`: the tower `n ↦ ℱ/Nₙ` of an antitone family.
* `Stacks.Sites.adicQuotientTowerOn`: the tower `n ↦ ℱ/ℐⁿ⁺¹ℱ`, and
  `Stacks.Sites.adicQuotientTowerOnπ` its projections from `ℱ`.

## Main results

* `Stacks.SheafOfModules.Submodule.quotientMapOfLE_comp` and
  `Stacks.SheafOfModules.Submodule.quotientMapOfLE_self`: the induced maps compose and the one
  induced by `N ⊆ N` is the identity, which is what makes the tower a functor.
* `Stacks.Sites.adicQuotientTowerOn_map`: its transition maps are the maps on quotients induced
  by the containments.
* `Stacks.Sites.submoduleQuotientTowerπ_comp_map` and
  `Stacks.Sites.adicQuotientTowerOnπ_comp_map`: the projections from `ℱ` are a cone over the
  tower.

## Implementation notes

The quotient is the cokernel, in sheaves of `O`-modules, of the inclusion of the submodule, as
`Stacks.Sites.adicQuotientModule` is; the induced map between two such cokernels is the only
construction needed, and both the identity and the composition law for it follow by cancelling
the epimorphism `cokernel.π`. The index is shifted by one in the adic tower, which is the
convention of `AlgebraicGeometry.RingedSite.adicQuotientTower`, the case `ℱ = O` of
`Stacks.Sites.adicQuotientTowerOn` — the two agree through
`Stacks.Sites.idealPowSmul_top`, not on the nose, because `ℐⁿO` is defined as a product and
`ℐⁿ` as a power.

The existence of the cokernels is carried as a hypothesis on the family rather than imposed on
the ambient category, so that the tower is available over a site whose sheaves of modules are
not known to be abelian.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v₁ u₁ u v

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : _root_.SheafOfModules.{v} R}

/-- **The map `ℱ/N₁ ⟶ ℱ/N₂` induced by a containment `N₁ ⊆ N₂` of submodules of `ℱ`**: the
projection onto the larger quotient kills the smaller submodule. -/
def Submodule.quotientMapOfLE {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂)
    [HasCokernel N₁.ι] [HasCokernel N₂.ι] :
    cokernel N₁.ι ⟶ cokernel N₂.ι :=
  cokernel.desc N₁.ι (cokernel.π N₂.ι) (by
    rw [← Submodule.homOfLE_comp_ι h, Category.assoc, cokernel.condition, comp_zero])

/-- The induced map on quotients is compatible with the projections from `ℱ`. -/
@[reassoc (attr := simp)]
lemma Submodule.π_comp_quotientMapOfLE {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂)
    [HasCokernel N₁.ι] [HasCokernel N₂.ι] :
    cokernel.π N₁.ι ≫ Submodule.quotientMapOfLE h = cokernel.π N₂.ι :=
  cokernel.π_desc _ _ _

/-- Composing the maps induced by two containments is the map induced by the composite
containment: both agree after the epimorphism `cokernel.π`. -/
lemma Submodule.quotientMapOfLE_comp {N₁ N₂ N₃ : M.Submodule} (h₁₂ : N₁ ≤ N₂) (h₂₃ : N₂ ≤ N₃)
    (h₁₃ : N₁ ≤ N₃) [HasCokernel N₁.ι] [HasCokernel N₂.ι] [HasCokernel N₃.ι] :
    Submodule.quotientMapOfLE h₁₂ ≫ Submodule.quotientMapOfLE h₂₃ =
      Submodule.quotientMapOfLE h₁₃ := by
  rw [← cancel_epi (cokernel.π N₁.ι), ← Category.assoc, Submodule.π_comp_quotientMapOfLE,
    Submodule.π_comp_quotientMapOfLE, Submodule.π_comp_quotientMapOfLE]

/-- The map induced by `N ⊆ N` is the identity of `ℱ/N`. -/
lemma Submodule.quotientMapOfLE_self {N : M.Submodule} (h : N ≤ N) [HasCokernel N.ι] :
    Submodule.quotientMapOfLE h = 𝟙 (cokernel N.ι) := by
  rw [← cancel_epi (cokernel.π N.ι), Submodule.π_comp_quotientMapOfLE, Category.comp_id]

end Stacks.SheafOfModules

namespace Stacks.Sites

open Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

section General

variable (M : _root_.SheafOfModules.{v} R) (N : ℕ → M.Submodule)
  (hN : ∀ m n : ℕ, n ≤ m → N m ≤ N n) [∀ n : ℕ, HasCokernel (N n).ι]

/-- **The tower of quotients of a sheaf of modules by an antitone family of submodules.** -/
def submoduleQuotientTower : ℕᵒᵖ ⥤ _root_.SheafOfModules.{v} R where
  obj n := cokernel (N n.unop).ι
  map h := Submodule.quotientMapOfLE (hN _ _ (leOfHom h.unop))
  map_id _ := Submodule.quotientMapOfLE_self _
  map_comp _ _ := (Submodule.quotientMapOfLE_comp _ _ _).symm

/-- The transition maps of the tower are the maps on quotients induced by the containments. -/
theorem submoduleQuotientTower_map {a b : ℕᵒᵖ} (φ : a ⟶ b) :
    (submoduleQuotientTower M N hN).map φ =
      Submodule.quotientMapOfLE (hN _ _ (leOfHom φ.unop)) :=
  rfl

/-- The projection of `ℱ` onto the level `n` of the tower. -/
def submoduleQuotientTowerπ (n : ℕ) : M ⟶ (submoduleQuotientTower M N hN).obj (op n) :=
  cokernel.π (N n).ι

/-- The projection of `ℱ` onto each level of the tower is an epimorphism. -/
instance epi_submoduleQuotientTowerπ (n : ℕ) : Epi (submoduleQuotientTowerπ M N hN n) :=
  inferInstanceAs (Epi (cokernel.π (N n).ι))

/-- **The projections from `ℱ` are a cone over the tower.** -/
@[reassoc (attr := simp)]
theorem submoduleQuotientTowerπ_comp_map {m k : ℕ} (h : k ≤ m) :
    submoduleQuotientTowerπ M N hN m ≫
        (submoduleQuotientTower M N hN).map (homOfLE h).op =
      submoduleQuotientTowerπ M N hN k :=
  Submodule.π_comp_quotientMapOfLE (hN _ _ h)

end General

section Adic

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : RingedSite.{u, v, w}} [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (I : IdealSubsheaf.{v, u, w} X.O)
  (ℱ : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The adic quotient tower at the coefficient `ℱ`**: the tower `n ↦ ℱ/ℐⁿ⁺¹ℱ` of quotients of
a sheaf of modules by the products of it with the positive powers of a sheaf of ideals.

The index is shifted by one, as it is in `AlgebraicGeometry.RingedSite.adicQuotientTower`, which
is the case `ℱ = O` of this tower up to `Stacks.Sites.idealPowSmul_top`. -/
@[ega "III 7.4.7.2" "more general"]
def adicQuotientTowerOn :
    ℕᵒᵖ ⥤ _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  submoduleQuotientTower ℱ (fun n => idealPowSmul (M := ℱ) I (n + 1) ⊤)
    fun _ _ h => idealPowSmul_antitone (M := ℱ) I ⊤ (Nat.succ_le_succ h)

/-- The level `n` of the adic quotient tower at the coefficient `ℱ` is `ℱ/ℐⁿ⁺¹ℱ`. -/
theorem adicQuotientTowerOn_obj (n : ℕ) :
    (adicQuotientTowerOn I ℱ).obj (op n) =
      cokernel (idealPowSmul (M := ℱ) I (n + 1) ⊤).ι :=
  rfl

/-- The transition maps of the adic quotient tower at the coefficient `ℱ` are the maps on
quotients induced by the containments `ℐᵐ⁺¹ℱ ⊆ ℐᵏ⁺¹ℱ`. -/
theorem adicQuotientTowerOn_map {a b : ℕᵒᵖ} (φ : a ⟶ b) :
    (adicQuotientTowerOn I ℱ).map φ =
      Submodule.quotientMapOfLE
        (idealPowSmul_antitone (M := ℱ) I ⊤ (Nat.succ_le_succ (leOfHom φ.unop))) :=
  rfl

/-- The projection of `ℱ` onto the level `n` of the adic quotient tower. -/
def adicQuotientTowerOnπ (n : ℕ) : ℱ ⟶ (adicQuotientTowerOn I ℱ).obj (op n) :=
  cokernel.π (idealPowSmul (M := ℱ) I (n + 1) ⊤).ι

/-- The projection of `ℱ` onto each level of the adic quotient tower is an epimorphism. -/
instance epi_adicQuotientTowerOnπ (n : ℕ) : Epi (adicQuotientTowerOnπ I ℱ n) :=
  inferInstanceAs (Epi (cokernel.π (idealPowSmul (M := ℱ) I (n + 1) ⊤).ι))

/-- **The projections from `ℱ` are a cone over the adic quotient tower.** -/
@[reassoc (attr := simp)]
theorem adicQuotientTowerOnπ_comp_map {m k : ℕ} (h : k ≤ m) :
    adicQuotientTowerOnπ I ℱ m ≫ (adicQuotientTowerOn I ℱ).map (homOfLE h).op =
      adicQuotientTowerOnπ I ℱ k :=
  Submodule.π_comp_quotientMapOfLE
    (idealPowSmul_antitone (M := ℱ) I ⊤ (Nat.succ_le_succ h))

end Adic

end Stacks.Sites

end
