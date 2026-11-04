module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesCotangentCut
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFamilyDivisors

/-!
# Choosing sections whose images in the cotangent space are independent

Let `s_1, …, s_d` be sections of an invertible module `ℒ` vanishing at a closed point `x`; the
question is when their images generate `𝔪_x ℒ_x / 𝔪_x^2 ℒ_x`. Read through a stalk basis `β` of
`ℒ_x`, a germ in `𝔪_x ℒ_x` is `c β` for a unique `c ∈ 𝔪_x`, and the condition is that the classes
of the `c_i` in the cotangent space `𝔪_x/𝔪_x^2` span it. This file makes that condition a
sequence of linear conditions on a `k`-vector space `V` of sections: once `s_1, …, s_j` have
independent images and `j < dim 𝔪_x/𝔪_x^2`, the members of `V` whose image lies in their span form
a *proper* `k`-subspace of `V` — provided the germs of `V` span `𝔪_x ℒ_x`. A choice outside it
keeps the images independent, and `d` independent images span.

## Main results

* `Stacks.Chow.BertiniChain.exists_submodule_linearIndependent_snoc`: the proper subspace to
  avoid at each step.
* `Stacks.Chow.BertiniChain.span_germ_eq_maximalSmul_of_linearIndependent`: `d` sections with
  independent images have germs spanning `𝔪_x ℒ_x`.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite IsLocalRing
open scoped Stacks.ModuleStalk

universe u

namespace Stacks.Chow.BertiniChain

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (M : X.Modules) (x : X)
  {β : M.presheaf.stalk x} (hβ : Stacks.Divisors.IsStalkBasis M x β)

/-- The coefficient against a stalk basis of an element of `𝔪_x M_x` lies in `𝔪_x`. -/
theorem linearEquiv_symm_mem_maximalIdeal (t : M.presheaf.stalk x)
    (ht : t ∈ Stacks.ModuleStalk.maximalSmul M x) :
    hβ.linearEquiv.symm t ∈ maximalIdeal (X.presheaf.stalk x) := by
  rw [← hβ.map_maximalIdeal, Submodule.mem_map] at ht
  obtain ⟨a, ha, rfl⟩ := ht
  rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact ha

/-- The coefficient against a stalk basis of an element of `𝔪_x M_x`, an element of `𝔪_x`. -/
def maximalCoeff (t : M.presheaf.stalk x) (ht : t ∈ Stacks.ModuleStalk.maximalSmul M x) :
    maximalIdeal (X.presheaf.stalk x) :=
  ⟨hβ.linearEquiv.symm t, linearEquiv_symm_mem_maximalIdeal M x hβ t ht⟩

/-- The stalk basis applied to `maximalCoeff M x hβ t ht` recovers `t`. -/
theorem linearEquiv_maximalCoeff (t : M.presheaf.stalk x)
    (ht : t ∈ Stacks.ModuleStalk.maximalSmul M x) :
    hβ.linearEquiv (maximalCoeff M x hβ t ht : X.presheaf.stalk x) = t :=
  hβ.linearEquiv.apply_symm_apply t

variable (V : Submodule k (Stacks.Bertini.globalSections k f M))
  (hvan : ∀ v ∈ V, (M.presheaf.Γgerm x).hom
    ((v : Stacks.Bertini.globalSections k f M) : Γ(M, ⊤)) ∈ Stacks.ModuleStalk.maximalSmul M x)

/-- The germ at `x` of a member of `V`. -/
abbrev germOf (v : V) : M.presheaf.stalk x :=
  (M.presheaf.Γgerm x).hom ((v : Stacks.Bertini.globalSections k f M) : Γ(M, ⊤))

/-- The image in the cotangent space `𝔪_x/𝔪_x^2` of a member of `V`, read through `β`. -/
def cotangentOf (v : V) : CotangentSpace (X.presheaf.stalk x) :=
  (maximalIdeal (X.presheaf.stalk x)).toCotangent
    (maximalCoeff M x hβ (germOf f M x V v) (hvan v v.2))

/-- The germ at `x` is additive on `V`. -/
theorem germOf_add (v w : V) : germOf f M x V (v + w) = germOf f M x V v + germOf f M x V w :=
  map_add (M.presheaf.Γgerm x).hom _ _

/-- The germ at `x` of `a • v` is the germ of `v` scaled by the image of `a` in the local ring. -/
theorem germOf_smul (a : k) (v : V) :
    germOf f M x V (a • v) =
      (X.presheaf.Γgerm x).hom (Stacks.Bertini.baseRingHom k f a) • germOf f M x V v :=
  Stacks.ModuleStalk.Γgerm_smul M x _ _

/-- The image in the cotangent space is additive on `V`. -/
theorem cotangentOf_add (v w : V) :
    cotangentOf f M x hβ V hvan (v + w) =
      cotangentOf f M x hβ V hvan v + cotangentOf f M x hβ V hvan w := by
  rw [cotangentOf, cotangentOf, cotangentOf, ← map_add]
  congr 1
  apply Subtype.ext
  simp only [maximalCoeff, Submodule.coe_add, germOf_add, map_add]

/-- The image in the cotangent space of `a • v` is that of `v` scaled by the image of `a` in the
local ring. -/
theorem cotangentOf_smul (a : k) (v : V) :
    cotangentOf f M x hβ V hvan (a • v) =
      (X.presheaf.Γgerm x).hom (Stacks.Bertini.baseRingHom k f a) •
        cotangentOf f M x hβ V hvan v := by
  rw [cotangentOf, cotangentOf, ← map_smul]
  congr 1
  apply Subtype.ext
  simp only [maximalCoeff, germOf_smul, map_smul, SetLike.mk_smul_mk, smul_eq_mul]

/-- The members of `V` whose image in the cotangent space lies in a given subspace. -/
def cotangentPreimage (S : Submodule (ResidueField (X.presheaf.stalk x))
    (CotangentSpace (X.presheaf.stalk x))) : Submodule k V where
  carrier := {v | cotangentOf f M x hβ V hvan v ∈ S}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_setOf_eq, cotangentOf_add] at hv hw ⊢
    exact S.add_mem hv hw
  zero_mem' := by
    have h0 : cotangentOf f M x hβ V hvan 0 = 0 := by
      simpa using cotangentOf_add f M x hβ V hvan 0 0
    simp only [Set.mem_setOf_eq, h0, S.zero_mem]
  smul_mem' a v hv := by
    simp only [Set.mem_setOf_eq, cotangentOf_smul] at hv ⊢
    exact Submodule.smul_of_tower_mem S _ hv

/-- A family of elements of `𝔪_x M_x` spans it iff the coefficients against a stalk basis span
`𝔪_x`, as a submodule of itself. -/
private theorem span_eq_maximalSmul_iff {ι : Type*} (t : ι → M.presheaf.stalk x)
    (ht : ∀ i, t i ∈ Stacks.ModuleStalk.maximalSmul M x) :
    Submodule.span (X.presheaf.stalk x) (Set.range t) = Stacks.ModuleStalk.maximalSmul M x ↔
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => maximalCoeff M x hβ (t i) (ht i)) = ⊤ := by
  set φ : maximalIdeal (X.presheaf.stalk x) →ₗ[X.presheaf.stalk x] M.presheaf.stalk x :=
    (hβ.linearEquiv : X.presheaf.stalk x →ₗ[X.presheaf.stalk x] M.presheaf.stalk x) ∘ₗ
      (maximalIdeal (X.presheaf.stalk x)).subtype with hφ
  have hinj : Function.Injective φ :=
    hβ.linearEquiv.injective.comp Subtype.val_injective
  have hrange : LinearMap.range φ = Stacks.ModuleStalk.maximalSmul M x := by
    rw [hφ, LinearMap.range_comp, Submodule.range_subtype, ← hβ.map_maximalIdeal]
  have hfun : (⇑φ ∘ fun i => maximalCoeff M x hβ (t i) (ht i)) = t :=
    funext fun i => linearEquiv_maximalCoeff M x hβ _ (ht i)
  rw [← (Submodule.map_injective_of_injective hinj).eq_iff, Submodule.map_span,
    ← Set.range_comp, Submodule.map_top, hrange, hfun]

variable [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- If the germs of `V` span `𝔪_x M_x`, the coefficients of the members of `V` span `𝔪_x`, as
a submodule of itself. -/
theorem span_maximalCoeff_eq_top
    (hspan : Submodule.span (X.presheaf.stalk x) (Set.range (germOf f M x V)) =
      Stacks.ModuleStalk.maximalSmul M x) :
    Submodule.span (X.presheaf.stalk x)
        (Set.range fun v : V => maximalCoeff M x hβ (germOf f M x V v) (hvan v v.2)) = ⊤ :=
  (span_eq_maximalSmul_iff M x hβ (germOf f M x V) fun v => hvan v v.2).mp hspan

/-- **The proper subspace to avoid at one step of the choice.** If the germs of `V` span
`𝔪_x M_x` and `s_1, …, s_j` have linearly independent images in the cotangent space with `j`
less than its dimension, the members of `V` whose image lies in their span form a proper
subspace, and any member outside it extends the family to an independent one. -/
theorem exists_submodule_linearIndependent_snoc
    (hspan : Submodule.span (X.presheaf.stalk x) (Set.range (germOf f M x V)) =
      Stacks.ModuleStalk.maximalSmul M x)
    {j : ℕ} (s : Fin j → V)
    (hs : LinearIndependent (ResidueField (X.presheaf.stalk x))
      (cotangentOf f M x hβ V hvan ∘ s))
    (hj : j < Module.finrank (ResidueField (X.presheaf.stalk x))
      (CotangentSpace (X.presheaf.stalk x))) :
    ∃ P : Submodule k V, P ≠ ⊤ ∧ ∀ v ∉ P,
      LinearIndependent (ResidueField (X.presheaf.stalk x))
        (cotangentOf f M x hβ V hvan ∘ Fin.snoc s v) := by
  set S := Submodule.span (ResidueField (X.presheaf.stalk x))
    (Set.range (cotangentOf f M x hβ V hvan ∘ s))
  have hS : S ≠ ⊤ := by
    intro hS
    have h1 : Module.finrank (ResidueField (X.presheaf.stalk x)) S = j := by
      simpa using finrank_span_eq_card hs
    have h2 := (finrank_top (ResidueField (X.presheaf.stalk x))
      (CotangentSpace (X.presheaf.stalk x))).symm.trans
      (congrArg (fun T : Submodule (ResidueField (X.presheaf.stalk x))
        (CotangentSpace (X.presheaf.stalk x)) =>
          Module.finrank (ResidueField (X.presheaf.stalk x)) T) hS.symm)
    omega
  refine ⟨cotangentPreimage f M x hβ V hvan S, ?_, fun v hv => ?_⟩
  · intro htop
    apply hS
    rw [eq_top_iff, ← (CotangentSpace.span_image_eq_top_iff).mpr
      (span_maximalCoeff_eq_top f M x hβ V hvan hspan)]
    refine Submodule.span_le.mpr ?_
    rintro - ⟨-, ⟨v, rfl⟩, rfl⟩
    have hv : v ∈ cotangentPreimage f M x hβ V hvan S := htop ▸ Submodule.mem_top
    exact hv
  · rw [Fin.comp_snoc]
    exact linearIndependent_fin_snoc.mpr ⟨hs, hv⟩

/-- **Independent images span.** If `d` members of `V` have linearly independent images in the
`d`-dimensional cotangent space, their germs span `𝔪_x M_x`. -/
theorem span_germ_eq_maximalSmul_of_linearIndependent {d : ℕ} (s : Fin d → V)
    (hs : LinearIndependent (ResidueField (X.presheaf.stalk x))
      (cotangentOf f M x hβ V hvan ∘ s))
    (hd : Module.finrank (ResidueField (X.presheaf.stalk x))
      (CotangentSpace (X.presheaf.stalk x)) = d) :
    Submodule.span (X.presheaf.stalk x) (Set.range fun i => germOf f M x V (s i)) =
      Stacks.ModuleStalk.maximalSmul M x := by
  have htop := hs.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hd])
  have himg : Set.range (cotangentOf f M x hβ V hvan ∘ s) =
      (maximalIdeal (X.presheaf.stalk x)).toCotangent ''
        Set.range (fun i => maximalCoeff M x hβ (germOf f M x V (s i)) (hvan _ (s i).2)) := by
    rw [← Set.range_comp]
    rfl
  rw [himg] at htop
  have hspan := (CotangentSpace.span_image_eq_top_iff).mp htop
  exact (span_eq_maximalSmul_iff M x hβ (fun i => germOf f M x V (s i))
    fun i => hvan _ (s i).2).mpr hspan

end Stacks.Chow.BertiniChain

end
