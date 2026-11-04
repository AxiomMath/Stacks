module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsImageProduct

/-!
# Killing the generators of a sections product kills the whole submodule

Let `α : R₁ ⟶ R` be a morphism of sheaves of rings on a site, let `M` be a sheaf of `R`-modules
and let `g : M ⟶ G` be a morphism of sheaves of `R₁`-modules out of `M` with its scalars
restricted along `α`. Let `T` be a restriction-stable family of sections of `R`.

If `g` kills every product `a • m` of a section `a` of the family with a section `m` of `M`,
then `g` kills every section of the submodule `T·M` those products generate — even though `g`
is linear only over `R₁`, so that its kernel is not an `R`-submodule of `M` and the universal
property of `T·M` does not apply to it.

## Main results

* `Stacks.SheafOfModules.apply_eq_zero_of_mem_sectionsProductSubmodule`: the statement for
  `Stacks.SheafOfModules.sectionsProductSubmodule`.
* `Stacks.SheafOfModules.apply_eq_zero_of_mem_imageProductSubmodule`: the same for
  `Stacks.SheafOfModules.imageProductSubmodule`, whose generating family is the sectionwise
  range of a map into the unit module.

## Implementation notes

The kernel of `g` is only an `R₁`-submodule, so the universal property of `T·M` cannot be
applied to it. What *is* an `R`-submodule is the family of sections `m` of `M` such that `g`
kills `c • m|_V` for *every* restriction `m|_V` and every section `c` of `R`: stability under
multiplication by `R` holds because the extra scalar is absorbed into `c`, stability under
restriction because of the quantification over all restrictions, and the membership condition is
local because `G` is a sheaf, hence separated. It contains the generators `a • m` precisely
because `R` is commutative, which lets the scalar `c` be moved past `a`, after which
`c • (a • m)` is again a generator, with `c • m` in place of `m`. The submodule therefore
contains `T·M`, and specialising to the identity restriction and the unit scalar gives the
statement.

Commutativity of `R` is a hypothesis rather than a `CommRingCat`-valued sheaf, so that the
result applies to the sheaf of rings underlying a sheaf of commutative rings with no transport.

Reading a section of `M` as a section of `M` with its scalars restricted along `α` is an
identity on carriers, but not an identity the elaborator sees through at reducible
transparency, so it is named once as `Stacks.SheafOfModules.restrictedApply` together with its
additivity and naturality; the public statements are phrased without it.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u₁ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R R₁ : Sheaf J RingCat.{u}} {α : R₁ ⟶ R} {M : SheafOfModules.{u} R}
  {G : SheafOfModules.{u} R₁}

/-- A section of `M`, pushed through a morphism out of `M` with its scalars restricted along
`α`. -/
noncomputable def restrictedApply (g : (SheafOfModules.restrictScalars α).obj M ⟶ G)
    (U : Cᵒᵖ) (m : M.val.obj U) : G.val.obj U :=
  g.val.app U m

/-- `restrictedApply g U` sends zero to zero. -/
@[simp]
lemma restrictedApply_zero (g : (SheafOfModules.restrictScalars α).obj M ⟶ G) (U : Cᵒᵖ) :
    restrictedApply g U 0 = 0 :=
  map_zero (ConcreteCategory.hom (g.val.app U))

/-- `restrictedApply g U` is additive. -/
lemma restrictedApply_add (g : (SheafOfModules.restrictScalars α).obj M ⟶ G) (U : Cᵒᵖ)
    (m m' : M.val.obj U) :
    restrictedApply g U (m + m') = restrictedApply g U m + restrictedApply g U m' :=
  map_add (ConcreteCategory.hom (g.val.app U)) m m'

/-- `restrictedApply g` commutes with restriction of sections along `h : U ⟶ V`. -/
lemma restrictedApply_restrictₛₗ (g : (SheafOfModules.restrictScalars α).obj M ⟶ G)
    {U V : Cᵒᵖ} (h : U ⟶ V) (m : M.val.obj U) :
    restrictedApply g V (M.val.restrictₛₗ h m) = G.val.restrictₛₗ h (restrictedApply g U m) :=
  PresheafOfModules.naturality_apply g.val h m

/-- The sections of `M` which `g` kills after every restriction and every multiplication by a
section of `R`. This is a family of `R`-submodules even though the kernel of `g` is not one. -/
private noncomputable def annihilatedPresubmodule
    (g : (SheafOfModules.restrictScalars α).obj M ⟶ G) : M.val.Submodule where
  obj U :=
    { carrier := {m : M.val.obj U | ∀ (V : Cᵒᵖ) (h : U ⟶ V) (c : R.obj.obj V),
        restrictedApply g V (c • M.val.restrictₛₗ h m) = 0}
      zero_mem' := fun V h c => by
        rw [map_zero, smul_zero, restrictedApply_zero]
      add_mem' := fun {m m'} hm hm' V h c => by
        rw [map_add, smul_add, restrictedApply_add, hm V h c, hm' V h c, add_zero]
      smul_mem' := fun r {m} hm V h c => by
        rw [(M.val.restrictₛₗ h).map_smulₛₗ, smul_smul]
        exact hm V h (c * R.obj.map h r) }
  map := fun {U U'} k m hm V h c => by
    rw [restrictₛₗ_restrictₛₗ]
    exact hm V (k ≫ h) c

/-- A section in the family multiplies into zero on the nose, not only after a restriction. -/
private lemma apply_smul_eq_zero_of_mem_annihilated
    {g : (SheafOfModules.restrictScalars α).obj M ⟶ G} {U : Cᵒᵖ} {m : M.val.obj U}
    (hm : m ∈ (annihilatedPresubmodule g).obj U) (c : R.obj.obj U) :
    restrictedApply g U (c • m) = 0 := by
  have h := hm U (𝟙 U) c
  rwa [show M.val.restrictₛₗ (𝟙 U) m = m from by simp] at h

/-- The sections `g` kills after every restriction and scalar form a *sheaf* submodule: the
condition quantifies over all restrictions, and `G` is separated. -/
private noncomputable def annihilatedSubmodule
    (g : (SheafOfModules.restrictScalars α).obj M ⟶ G) : M.Submodule where
  toSubmodule := annihilatedPresubmodule g
  isSheaf := by
    intro U m hm V h c
    apply G.isSheaf.isSeparated _ _ (J.pullback_stable h.unop hm)
    intro W k hk
    have hmem : M.val.restrictₛₗ (h ≫ k.op) m ∈ (annihilatedPresubmodule g).obj (op W) := by
      rw [show h ≫ k.op = (k ≫ h.unop).op from rfl]
      exact hk
    change G.val.restrictₛₗ k.op (restrictedApply g V (c • M.val.restrictₛₗ h m)) =
      G.val.restrictₛₗ k.op 0
    rw [map_zero, ← restrictedApply_restrictₛₗ, (M.val.restrictₛₗ k.op).map_smulₛₗ,
      restrictₛₗ_restrictₛₗ]
    exact apply_smul_eq_zero_of_mem_annihilated hmem _

/-- **A map killing the generators of a sections product kills the whole submodule.** The map
`g` is linear only over `R₁`, so its kernel is not an `R`-submodule of `M` and the universal
property of `T·M` does not apply to it; see the implementation notes. -/
theorem apply_eq_zero_of_mem_sectionsProductSubmodule
    (hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (T : ∀ U : Cᵒᵖ, Set (R.obj.obj U))
    (hT : ∀ {U V : Cᵒᵖ} (h : U ⟶ V) {a : R.obj.obj U}, a ∈ T U → R.obj.map h a ∈ T V)
    (g : (SheafOfModules.restrictScalars α).obj M ⟶ G)
    (hg : ∀ (U : Cᵒᵖ) (a : R.obj.obj U), a ∈ T U → ∀ m : M.val.obj U,
      restrictedApply g U (a • m) = 0)
    {U : Cᵒᵖ} {m : M.val.obj U} (hm : m ∈ (sectionsProductSubmodule T M).obj U) :
    restrictedApply g U m = 0 := by
  have hle : sectionsProductSubmodule T M ≤ annihilatedSubmodule g :=
    sectionsProductSubmodule_le fun W a ha n V h c => by
      rw [(M.val.restrictₛₗ h).map_smulₛₗ, smul_smul, hR V c (R.obj.map h a), ← smul_smul]
      exact hg V (R.obj.map h a) (hT h ha) _
  have h := apply_smul_eq_zero_of_mem_annihilated (hle U hm) 1
  rwa [one_smul] at h

/-- **A map killing the products of the sections of `A` kills the submodule they generate.**
The `imageProductSubmodule` form of
`Stacks.SheafOfModules.apply_eq_zero_of_mem_sectionsProductSubmodule`. -/
theorem apply_eq_zero_of_mem_imageProductSubmodule
    (hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    {A : SheafOfModules.{u} R} (φ : A ⟶ SheafOfModules.unit R)
    (g : (SheafOfModules.restrictScalars α).obj M ⟶ G)
    (hg : ∀ (U : Cᵒᵖ) (z : A.val.obj U) (m : M.val.obj U),
      restrictedApply g U (ringValue φ U z • m) = 0)
    {U : Cᵒᵖ} {m : M.val.obj U} (hm : m ∈ (imageProductSubmodule φ M).obj U) :
    restrictedApply g U m = 0 := by
  rw [imageProductSubmodule_eq_sectionsProductSubmodule] at hm
  refine apply_eq_zero_of_mem_sectionsProductSubmodule hR _ (fun {V W} h {a} ha => ?_) g
    (fun V a ha n => by obtain ⟨z, rfl⟩ := ha; exact hg V z n) hm
  obtain ⟨z, rfl⟩ := ha
  exact ⟨A.val.restrictₛₗ h z, ringValue_restrictₛₗ φ h z⟩

end Stacks.SheafOfModules

end
