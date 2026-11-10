module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# The formal pullback of a map into a completion on an algebraic space

Let `F` be an algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its
small étale site.  Let `G` be an `𝒪_F`-module, `E` an inverse system of `𝒪_F`-modules and
`α : E ⟶ G^∧ = (G / 𝓘 ⁿ⁺¹ G)_n` a morphism of inverse systems.  This file builds the candidate
algebraization of `α`: the **formal pullback**

`G ×_{lim G / 𝓘 ⁿ⁺¹ G} lim E`,

realized as the kernel of the difference of the two maps out of the biproduct `G ⊞ lim E`.

## Main definitions

* `AlgebraicGeometry.Space.IsSystemKernelCokernelAnnihilatedByPower` — a morphism of inverse
  systems of `𝒪_F`-modules whose levelwise kernels and cokernels are annihilated by one common
  positive power of `𝓘`.  This is the hypothesis of Stacks 08BB, in the levelwise form that the
  source's Stacks 0888 states it in.
* `AlgebraicGeometry.Space.completionToLimit` — the canonical map from a module into the limit
  `lim G / 𝓘 ⁿ⁺¹ G` of its completion.
* `AlgebraicGeometry.Space.formalPullback` — the formal pullback, with its projection
  `AlgebraicGeometry.Space.formalPullbackMap` to `G` and
  `AlgebraicGeometry.Space.formalPullbackProj` to `lim E`.

## Main results

* `AlgebraicGeometry.Space.formalPullback_comm` — **the defining square commutes.**
* `AlgebraicGeometry.Space.lift_comp_formalPullbackDiff` — a pair of maps agreeing on
  `lim G / 𝓘 ⁿ⁺¹ G` kills the difference map, which is what produces a map into the formal
  pullback.
* `AlgebraicGeometry.Space.formalPullback_section_ext` and
  `AlgebraicGeometry.Space.exists_formalPullback_section` — **the elementwise description of the
  sections of the formal pullback over an étale chart**: the two projections are jointly
  injective on them, and every compatible pair of sections of `G` and of `lim E` is the image of
  one.

## Implementation notes

The formal pullback is defined as a kernel rather than as `CategoryTheory.Limits.pullback`
because the sections of a kernel of a morphism of sheaves of modules are the kernel of the map
on sections, `SheafOfModules.exact_kernel_ι_val_app`, which is what makes the elementwise
description available; the pullback would only come with the universal property.  The two
descriptions agree in an abelian category.

The biproduct never has to be resolved into a product of the sections: joint injectivity of the
two projections is `CategoryTheory.Limits.biprod.total` read on sections, and a section is built
from a compatible pair with `CategoryTheory.Limits.biprod.inl` and
`CategoryTheory.Limits.biprod.inr`.

`AlgebraicGeometry.Space.Modules` is a `def` for a category of sheaves of modules, and the two
presentations carry separately declared instances, so a single object can occur in a goal under
two defeq but not syntactically equal spellings.  The cone defining
`AlgebraicGeometry.Space.completionToLimit` is therefore assembled from a natural transformation
whose naturality is proved by a term with the category named explicitly, rather than by `dsimp`.
For the same reason the limit `lim_n G / 𝓘 ⁿ⁺¹ G` is not given a name of its own: a folded and an
unfolded spelling of it on the two sides of the subtraction defining
`AlgebraicGeometry.Space.formalPullbackDiff` leaves the subtraction without an `HSub` instance.

The inverse system is zero-indexed, as `AlgebraicGeometry.Space.IsCoherentAdicSystem` is, so the
term of `G^∧` at `n` is the source's `G / 𝓘 ⁿ⁺¹ G`.

## References

* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### The hypothesis of Stacks 08BB -/

/-- **Tag 0888 (1) on an algebraic space.**  A morphism `α` of inverse systems of `𝒪_F`-modules
has *kernel and cokernel annihilated by a power of `𝓘`* if there is one positive exponent `t`
for which `𝓘 ^ t` annihilates both `Ker(α_k)` and `Coker(α_k)`, simultaneously for every index
`k`.

Kernel and cokernel are taken levelwise, in the abelian category of `𝒪_F`-modules.  This is the
notion the source names, and it is not interchangeable with a kernel formed in
`AlgebraicGeometry.Space.CoherentAdicSystems`: there the cokernel is computed levelwise but the
kernel is not, the discrepancy being the Artin–Rees stabilization.  No abelian structure on a
category of adic systems is therefore presupposed, and a morphism of inverse systems is all that
is required. -/
def IsSystemKernelCokernelAnnihilatedByPower
    {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (α : E ⟶ E') : Prop :=
  ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
    idealPowerMultiple B S hS F hF 𝓘 t (kernel (α.app (op k))) = ⊥ ∧
      idealPowerMultiple B S hS F hF 𝓘 t (cokernel (α.app (op k))) = ⊥

/-! ### Sections and composition -/

/-- Composition of morphisms of `𝒪_F`-modules is composition of the maps on sections, over a
chart of the small étale site named as such.  This is
`AlgebraicGeometry.Space.comp_val_app_apply` with the algebraic space given by its presheaf and
the proof that it is one, rather than as an object of
`AlgebraicGeometry.Space.AlgebraicSpaces`; the two spellings are definitionally equal but not
syntactically so, and `rw` does not see through the difference. -/
theorem comp_val_app_apply_chart {M N P : Modules.{u, u} B S hS F hF} (f : M ⟶ N) (g : N ⟶ P)
    (V : SmallEtale B S hS F) (x : M.val.obj (op V)) :
    (f ≫ g).val.app (op V) x = g.val.app (op V) (f.val.app (op V) x) :=
  rfl

/-! ### The limit of the completion -/

/-- The quotient projections `M ⟶ M / 𝓘 ⁿ⁺¹ M`, as a natural transformation from the constant
system at `M` to the completion of `M`. -/
def completionNatTrans (M : Modules.{u, u} B S hS F hF) :
    (Functor.const ℕᵒᵖ).obj M ⟶ adicQuotientSystem B S hS F hF 𝓘 M where
  app n := cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n.unop + 1) M).ι
  naturality _ n g :=
    (Category.id_comp (obj := Modules.{u, u} B S hS F hF)
        (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n.unop + 1) M).ι)).trans
      (π_comp_idealPowerQuotientMapOfLE B S hS F hF 𝓘
        (Nat.add_le_add_right (leOfHom g.unop) 1) M).symm

/-- The canonical map `M ⟶ lim_n M / 𝓘 ⁿ⁺¹ M`. -/
def completionToLimit (M : Modules.{u, u} B S hS F hF) :
    M ⟶ limit (adicQuotientSystem B S hS F hF 𝓘 M) :=
  limit.lift _ (Cone.mk M (completionNatTrans B S hS F hF 𝓘 M))

/-- The canonical map `M ⟶ lim_n M / 𝓘 ⁿ⁺¹ M` followed by the projection to the `n`-th term is
the quotient map `M ⟶ M / 𝓘 ⁿ⁺¹ M`. -/
@[simp]
theorem completionToLimit_π (M : Modules.{u, u} B S hS F hF) (n : ℕᵒᵖ) :
    completionToLimit B S hS F hF 𝓘 M ≫ limit.π (adicQuotientSystem B S hS F hF 𝓘 M) n =
      cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n.unop + 1) M).ι :=
  limit.lift_π (Cone.mk M (completionNatTrans B S hS F hF 𝓘 M)) n

/-! ### The formal pullback -/

variable {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}

/-- The difference of the two maps `G ⊞ lim E ⟶ lim G / 𝓘 ⁿ⁺¹ G` whose kernel is the formal
pullback. -/
def formalPullbackDiff (G : Modules.{u, u} B S hS F hF)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G) :
    (G ⊞ limit E : Modules.{u, u} B S hS F hF) ⟶ limit (adicQuotientSystem B S hS F hF 𝓘 G) :=
  biprod.fst ≫ completionToLimit B S hS F hF 𝓘 G - biprod.snd ≫ limMap α

/-- **The formal pullback `G ×_{lim G / 𝓘 ⁿ⁺¹ G} lim E`** of a morphism `α : E ⟶ G^∧` of inverse
systems of `𝒪_F`-modules. -/
abbrev formalPullback (G : Modules.{u, u} B S hS F hF)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G) : Modules.{u, u} B S hS F hF :=
  kernel (formalPullbackDiff B S hS F hF 𝓘 G α)

/-- The projection of the formal pullback to `G`. -/
abbrev formalPullbackMap (G : Modules.{u, u} B S hS F hF)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G) :
    formalPullback B S hS F hF 𝓘 G α ⟶ G :=
  kernel.ι (formalPullbackDiff B S hS F hF 𝓘 G α) ≫ biprod.fst

/-- The projection of the formal pullback to `lim E`. -/
abbrev formalPullbackProj (G : Modules.{u, u} B S hS F hF)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G) :
    formalPullback B S hS F hF 𝓘 G α ⟶ limit E :=
  kernel.ι (formalPullbackDiff B S hS F hF 𝓘 G α) ≫ biprod.snd

/-- A pair of maps into `G` and into `lim E` agreeing on `lim G / 𝓘 ⁿ⁺¹ G` kills the difference
map. -/
theorem lift_comp_formalPullbackDiff (G : Modules.{u, u} B S hS F hF)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G) {T : Modules.{u, u} B S hS F hF}
    (u : T ⟶ G) (v : T ⟶ limit E)
    (h : u ≫ completionToLimit B S hS F hF 𝓘 G = v ≫ limMap α) :
    biprod.lift u v ≫ formalPullbackDiff B S hS F hF 𝓘 G α = 0 := by
  change biprod.lift u v ≫ (biprod.fst ≫ completionToLimit B S hS F hF 𝓘 G -
      biprod.snd ≫ limMap α) = 0
  rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc, biprod.lift_fst, biprod.lift_snd,
    h, sub_self]

/-- **The defining square of the formal pullback commutes.** -/
theorem formalPullback_comm (G : Modules.{u, u} B S hS F hF)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G) :
    formalPullbackMap B S hS F hF 𝓘 G α ≫ completionToLimit B S hS F hF 𝓘 G =
      formalPullbackProj B S hS F hF 𝓘 G α ≫ limMap α := by
  have h0 : kernel.ι (formalPullbackDiff B S hS F hF 𝓘 G α) ≫
      (biprod.fst ≫ completionToLimit B S hS F hF 𝓘 G -
        biprod.snd ≫ limMap α) = 0 := kernel.condition _
  rw [Preadditive.comp_sub, sub_eq_zero] at h0
  exact (Category.assoc _ _ _).trans (h0.trans (Category.assoc _ _ _).symm)

/-! ### The sections of the formal pullback over a chart -/

/-- If `f ≫ g = h` then `g` applied to `f` of a section is `h` of that section. -/
private theorem comp_val_app_apply_eq {M N P : Modules.{u, u} B S hS F hF} {f : M ⟶ N}
    {g : N ⟶ P} {h : M ⟶ P} (e : f ≫ g = h) {V : SmallEtale B S hS F} (x : M.val.obj (op V)) :
    g.val.app (op V) (f.val.app (op V) x) = h.val.app (op V) x := by
  rw [← comp_val_app_apply_chart, e]

/-- A section of `G ⊞ lim E` over a chart is determined by its two components. -/
theorem biprod_section_ext {M N : Modules.{u, u} B S hS F hF} (V : SmallEtale B S hS F)
    {x y : (M ⊞ N : Modules.{u, u} B S hS F hF).val.obj (op V)}
    (hfst : (biprod.fst : (M ⊞ N : Modules.{u, u} B S hS F hF) ⟶ M).val.app (op V) x =
      (biprod.fst : (M ⊞ N : Modules.{u, u} B S hS F hF) ⟶ M).val.app (op V) y)
    (hsnd : (biprod.snd : (M ⊞ N : Modules.{u, u} B S hS F hF) ⟶ N).val.app (op V) x =
      (biprod.snd : (M ⊞ N : Modules.{u, u} B S hS F hF) ⟶ N).val.app (op V) y) :
    x = y := by
  have key : ∀ z : (M ⊞ N : Modules.{u, u} B S hS F hF).val.obj (op V),
      (biprod.inl : M ⟶ M ⊞ N).val.app (op V)
          ((biprod.fst : (M ⊞ N : Modules.{u, u} B S hS F hF) ⟶ M).val.app (op V) z) +
        (biprod.inr : N ⟶ M ⊞ N).val.app (op V)
          ((biprod.snd : (M ⊞ N : Modules.{u, u} B S hS F hF) ⟶ N).val.app (op V) z) = z :=
    fun z => congrArg (fun k : (M ⊞ N : Modules.{u, u} B S hS F hF) ⟶ (M ⊞ N) =>
      k.val.app (op V) z) (biprod.total (X := M) (Y := N))
  rw [← key x, ← key y, hfst, hsnd]

/-- **A section of the formal pullback over a chart is determined by its two components.** -/
theorem formalPullback_section_ext (G : Modules.{u, u} B S hS F hF)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G) (V : SmallEtale B S hS F)
    {p q : (formalPullback B S hS F hF 𝓘 G α).val.obj (op V)}
    (hmap : (formalPullbackMap B S hS F hF 𝓘 G α).val.app (op V) p =
      (formalPullbackMap B S hS F hF 𝓘 G α).val.app (op V) q)
    (hproj : (formalPullbackProj B S hS F hF 𝓘 G α).val.app (op V) p =
      (formalPullbackProj B S hS F hF 𝓘 G α).val.app (op V) q) :
    p = q := by
  rw [comp_val_app_apply_chart] at hmap hproj
  exact SheafOfModules.kernel_ι_val_app_injective (formalPullbackDiff B S hS F hF 𝓘 G α) (op V)
    (biprod_section_ext B S hS F hF V hmap hproj)

/-- **Every compatible pair of sections comes from a section of the formal pullback.**  A section
`g` of `G` and a section `y` of `lim E` over a chart which agree in `lim G / 𝓘 ⁿ⁺¹ G` are the two
components of a section of the formal pullback. -/
theorem exists_formalPullback_section (G : Modules.{u, u} B S hS F hF)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G) (V : SmallEtale B S hS F)
    (g : G.val.obj (op V)) (y : (limit E : Modules.{u, u} B S hS F hF).val.obj (op V))
    (h : (completionToLimit B S hS F hF 𝓘 G).val.app (op V) g = (limMap α).val.app (op V) y) :
    ∃ p : (formalPullback B S hS F hF 𝓘 G α).val.obj (op V),
      (formalPullbackMap B S hS F hF 𝓘 G α).val.app (op V) p = g ∧
        (formalPullbackProj B S hS F hF 𝓘 G α).val.app (op V) p = y := by
  set x : (G ⊞ limit E : Modules.{u, u} B S hS F hF).val.obj (op V) :=
    (biprod.inl : G ⟶ G ⊞ limit E).val.app (op V) g +
      (biprod.inr : (limit E : Modules.{u, u} B S hS F hF) ⟶ G ⊞ limit E).val.app (op V) y
      with hx
  have hfst : (biprod.fst : (G ⊞ limit E : Modules.{u, u} B S hS F hF) ⟶ G).val.app (op V) x
      = g := by
    rw [hx, map_add, comp_val_app_apply_eq B S hS F hF biprod.inl_fst g,
      comp_val_app_apply_eq B S hS F hF biprod.inr_fst y]
    exact add_zero g
  have hsnd : (biprod.snd :
      (G ⊞ limit E : Modules.{u, u} B S hS F hF) ⟶ limit E).val.app (op V) x = y := by
    rw [hx, map_add, comp_val_app_apply_eq B S hS F hF biprod.inl_snd g,
      comp_val_app_apply_eq B S hS F hF biprod.inr_snd y]
    exact zero_add y
  have hzero : (formalPullbackDiff B S hS F hF 𝓘 G α).val.app (op V) x = 0 := by
    have hdiff : (formalPullbackDiff B S hS F hF 𝓘 G α).val.app (op V) x =
        (completionToLimit B S hS F hF 𝓘 G).val.app (op V)
            ((biprod.fst : (G ⊞ limit E : Modules.{u, u} B S hS F hF) ⟶ G).val.app (op V) x) -
          (limMap α).val.app (op V)
            ((biprod.snd : (G ⊞ limit E : Modules.{u, u} B S hS F hF) ⟶
              limit E).val.app (op V) x) := rfl
    rw [hdiff, hfst, hsnd, h, sub_self]
  obtain ⟨p, hp⟩ :=
    (SheafOfModules.exact_kernel_ι_val_app (formalPullbackDiff B S hS F hF 𝓘 G α) (op V) x).1 hzero
  refine ⟨p, ?_, ?_⟩
  · rw [comp_val_app_apply_chart, hp]; exact hfst
  · rw [comp_val_app_apply_chart, hp]; exact hsnd

end AlgebraicGeometry.Space

end
