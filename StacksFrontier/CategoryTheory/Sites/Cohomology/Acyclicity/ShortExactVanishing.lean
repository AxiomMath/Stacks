module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Vanishing of the cohomology of the sub-object of a short exact sequence of sheaves

Let `0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of abelian sheaves on a site. The
covariant long exact sequence of `Ext` out of the constant sheaf `ℤ` is the long exact
sequence of sheaf cohomology

```
⋯ → H^{n₀}(F₃) → H^{n₁}(F₁) → H^{n₁}(F₂) → ⋯,     n₀ + 1 = n₁,
```

so if the cohomology of the quotient vanishes in degree `n₀` and that of the middle term in
degree `n₁`, the cohomology of the sub-object vanishes in degree `n₁`.

Sheaf cohomology `CategoryTheory.Sheaf.H F n` is by definition
`Ext ((constantSheaf J AddCommGrpCat).obj (ULift ℤ)) F n`, so the long exact sequence needed is
literally Mathlib's `CategoryTheory.Abelian.Ext.covariant_sequence_exact₁`, with no comparison
of indexing conventions.

## Main results

* `Stacks.Cohomology.subsingleton_sheafH_X₁_of_shortExact`: `H^{n₁}(F₁) = 0` when `H^{n₁}(F₂)`
  and `H^{n₀}(F₃)` vanish.

## Implementation notes

The analogous statement at the middle term is already in the tree, as
`Stacks.EtaleCohomology.subsingleton_sheafCohomology_X₂_of_shortExact` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimaryVanishing`; it is not
repeated here.

Vanishing is expressed as `Subsingleton`, the convention of the étale-cohomology files that
consume this, rather than as `CategoryTheory.Limits.IsZero`: the groups are types, being `Ext`
groups. The two hypotheses are explicit arguments rather than instances, so that a vanishing
result proved for a specific sheaf can be passed positionally.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w' w v u

namespace Stacks.Cohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)

include hS in
/-- **The cohomology of the sub-object of a short exact sequence of abelian sheaves vanishes in
degree `n₁`** as soon as the cohomology of the middle term vanishes in degree `n₁` and that of
the quotient vanishes in degree `n₀`, where `n₀ + 1 = n₁`. This is exactness of the long exact
sequence of sheaf cohomology at `H^{n₁}(F₁)`. -/
theorem subsingleton_sheafH_X₁_of_shortExact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (Sheaf.H.{w', w} S.X₂ n₁))
    (h₃ : Subsingleton (Sheaf.H.{w', w} S.X₃ n₀)) :
    Subsingleton (Sheaf.H.{w', w} S.X₁ n₁) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ hS x (h₂.elim _ _) h
  rw [← hx₃, h₃.elim x₃ 0, Ext.zero_comp]

end Stacks.Cohomology

end

/-! ### Supplementary declarations -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w' w v u
namespace Stacks.Cohomology
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- **A natural multiple of the identity induces that multiple of the identity on sheaf
cohomology**, in every degree. The map `f ↦ Sheaf.H.map f q` is additive, so this is induction
on `m` from `Sheaf.H.map_id_apply`. -/
theorem sheafH_map_nsmul_id {G : Sheaf J AddCommGrpCat.{w}} (m q : ℕ)
    (y : Sheaf.H.{w', w} G q) : Sheaf.H.map (m • 𝟙 G) q y = m • y := by
  induction m with
  | zero =>
      rw [zero_nsmul, zero_nsmul]
      have h := Sheaf.H.map_add_apply (0 : G ⟶ G) 0 y
      rw [add_zero] at h
      refine (add_left_cancel (a := Sheaf.H.map.{w', w} (0 : G ⟶ G) q y) ?_).symm
      rw [add_zero]
      exact h
  | succ m ih => rw [succ_nsmul, Sheaf.H.map_add_apply, ih, Sheaf.H.map_id_apply, succ_nsmul]

end Stacks.Cohomology
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w' w v u
namespace Stacks.Cohomology
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)

include hS in
/-- **The cohomology of the sub-object of a short exact sequence of abelian sheaves vanishes in
degree `n₁`** as soon as the cohomology of the middle term vanishes in degree `n₁` and the map
`H^{n₀}(F₂) → H^{n₀}(F₃)` is surjective, where `n₀ + 1 = n₁`.

This is exactness of the long exact sequence of sheaf cohomology at `H^{n₁}(F₁)`: a class there
dies in `H^{n₁}(F₂)` for free, so it is the boundary of some class in `H^{n₀}(F₃)`, and a
boundary of something coming from `H^{n₀}(F₂)` is zero because two consecutive maps of the long
exact sequence compose to zero. -/
theorem subsingleton_sheafH_X₁_of_shortExact_of_surjective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (Sheaf.H.{w', w} S.X₂ n₁))
    (hg : Function.Surjective (Sheaf.H.map.{w', w} S.g n₀)) :
    Subsingleton (Sheaf.H.{w', w} S.X₁ n₁) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ hS x (h₂.elim _ _) h
  obtain ⟨x₂, rfl⟩ := hg x₃
  rw [← hx₃, Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
    Ext.comp_zero]

end Stacks.Cohomology
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w' w v u
namespace Stacks.Cohomology
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)

include hS in
/-- **Conversely, vanishing of `H^{n₁}(F₁)` forces `H^{n₀}(F₂) → H^{n₀}(F₃)` to be surjective**,
with no hypothesis on `H^{n₁}(F₂)`. This is exactness of the long exact sequence of sheaf
cohomology at `H^{n₀}(F₃)`: the boundary of any class there lands in `H^{n₁}(F₁)` and so
vanishes, hence the class comes from `H^{n₀}(F₂)`. -/
theorem surjective_sheafH_map_g_of_subsingleton_sheafH_X₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₁ : Subsingleton (Sheaf.H.{w', w} S.X₁ n₁)) :
    Function.Surjective (Sheaf.H.map.{w', w} S.g n₀) := fun x₃ => by
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS x₃ h (h₁.elim _ _)
  exact ⟨x₂, hx₂⟩

end Stacks.Cohomology
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w' w v u
namespace Stacks.Cohomology
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)

include hS in
/-- **`H^{n₁}(F₁)` vanishes exactly when `H^{n₀}(F₂) → H^{n₀}(F₃)` is surjective**, given that
`H^{n₁}(F₂)` vanishes. So, in a range where the middle term has no cohomology, the cohomology of
the sub-object in degree `n₁` measures precisely the failure of surjectivity one degree down. -/
theorem subsingleton_sheafH_X₁_iff_surjective_of_shortExact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (Sheaf.H.{w', w} S.X₂ n₁)) :
    Subsingleton (Sheaf.H.{w', w} S.X₁ n₁) ↔
      Function.Surjective (Sheaf.H.map.{w', w} S.g n₀) :=
  ⟨surjective_sheafH_map_g_of_subsingleton_sheafH_X₁ hS n₀ n₁ h,
    subsingleton_sheafH_X₁_of_shortExact_of_surjective hS n₀ n₁ h h₂⟩

end Stacks.Cohomology
end
