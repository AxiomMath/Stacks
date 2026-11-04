module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionExactSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover

/-!
# Ideal sheaves of the intersection and of the union of two closed subschemes

Let `Z` and `Y` be closed subschemes of a scheme `S`, cut out by ideal sheaves `ℐ_Z` and `ℐ_Y`.
Their scheme-theoretic intersection is cut out by `ℐ_Z + ℐ_Y`, which in the lattice of
`AlgebraicGeometry.Scheme.IdealSheafData` is `Z ⊔ Y`, and their scheme-theoretic union by
`ℐ_Z ∩ ℐ_Y`, which is `Z ⊓ Y`. This file records the consequences of these two descriptions for
the structure sheaves `𝒪_Z = i_* 𝒪_Z` read as modules on `S`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.kernel_ι_sup_comp_eq_zero`: a map out of `𝒪_S` killing
  `ℐ_Z` and `ℐ_Y` kills `ℐ_{Z ⊔ Y}`.
* `AlgebraicGeometry.Scheme.IdealSheafData.nonempty_isColimitRestrictionSup`: the restriction
  `𝒪_Y ⟶ 𝒪_{Z ⊔ Y}` is a cokernel of `ℐ_Z ⟶ 𝒪_S ⟶ 𝒪_Y`, that is, the image of `ℐ_Z` in `𝒪_Y` is
  the ideal of `Z ∩ Y` in `Y`.
* `AlgebraicGeometry.Scheme.IdealSheafData.comp_ambientToClosedSubscheme_inf_eq_zero`: a map into
  `𝒪_S` which dies in `𝒪_A` and in `𝒪_B` dies in `𝒪_{A ⊓ B}`.
* `AlgebraicGeometry.Scheme.IdealSheafData.eq_zero_of_sup_eq_top`: if `A` and `B` are disjoint
  (`A ⊔ B = ⊤`), then `ℐ_Z` is the sum of `ℐ_Z ∩ ℐ_A` and `ℐ_Z ∩ ℐ_B`, in the form that a map out
  of `ℐ_Z` vanishing on both is zero.

## Implementation notes

Each statement is checked on sections over affine opens, where the ideal sheaf of a closed
subscheme has the defining ideal as its sections
(`AlgebraicGeometry.Scheme.IdealSheafData.ambientToClosedSubscheme_app_eq_zero_iff_mem_ideal`), and
`AlgebraicGeometry.Scheme.IdealSheafData.hom_eq_zero_of_app_affineOpens` turns vanishing on affine
sections into vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S : Scheme.{u}}

/-- **A section killed by a morphism of modules comes from its kernel**, at the `Γ` spelling of
sections. -/
lemma exists_kernel_ι_app {M N : S.Modules} (f : M ⟶ N) (U : S.Opens) (x : Γ(M, U))
    (hx : f.app U x = 0) : ∃ y : Γ(kernel f, U), (kernel.ι f).app U y = x :=
  Stacks.SheafOfModules.exists_kernel_section f (op U) x hx

/-- The sections over an affine open of the ideal sheaf of a closed subscheme lie in its defining
ideal. -/
lemma kernel_ι_app_mem_ideal (I : S.IdealSheafData) (U : S.affineOpens)
    (m : Γ(kernel (ambientToClosedSubscheme I), U.1)) :
    (kernel.ι (ambientToClosedSubscheme I)).app U.1 m ∈ I.ideal U :=
  (ambientToClosedSubscheme_app_eq_zero_iff_mem_ideal I U _).1
    ((comp_app_apply _ _ U.1 m).symm.trans (app_apply_of_eq_zero (kernel.condition _) U.1 m))

/-- A map killing the kernel of `f` kills every section on which `f` vanishes. -/
private lemma app_eq_zero_of_kernel_ι_comp_eq_zero {M N T : S.Modules} (f : M ⟶ N) (g : M ⟶ T)
    (hg : kernel.ι f ≫ g = 0) (U : S.Opens) (x : Γ(M, U)) (hx : f.app U x = 0) :
    g.app U x = 0 := by
  obtain ⟨y, rfl⟩ := exists_kernel_ι_app f U x hx
  rw [← comp_app_apply]
  exact app_apply_of_eq_zero hg U y

/-- **The ideal of the scheme-theoretic intersection is the sum of the two ideals**, in the form
that a map out of `𝒪_S` which kills `ℐ_Z` and `ℐ_Y` kills `ℐ_{Z ⊔ Y}`. On an affine open `U` a
section of `ℐ_{Z ⊔ Y}` is an element of `ℐ_Z(U) + ℐ_Y(U)`. -/
theorem kernel_ι_sup_comp_eq_zero (Z Y : S.IdealSheafData) {T : S.Modules}
    (g : ambientStructureSheaf S ⟶ T) (hZ : kernel.ι (ambientToClosedSubscheme Z) ≫ g = 0)
    (hY : kernel.ι (ambientToClosedSubscheme Y) ≫ g = 0) :
    kernel.ι (ambientToClosedSubscheme (Z ⊔ Y)) ≫ g = 0 := by
  apply hom_eq_zero_of_app_affineOpens
  intro U m
  have key : ∀ b : Γ(S, U.1), b ∈ (Z ⊔ Y).ideal U → g.app U.1 b = 0 := by
    intro b hb
    rw [ideal_sup] at hb
    obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hb
    have h1 := app_eq_zero_of_kernel_ι_comp_eq_zero _ g hZ U.1 c
      ((ambientToClosedSubscheme_app_eq_zero_iff_mem_ideal Z U c).2 hc)
    have h2 := app_eq_zero_of_kernel_ι_comp_eq_zero _ g hY U.1 d
      ((ambientToClosedSubscheme_app_eq_zero_iff_mem_ideal Y U d).2 hd)
    have hsplit : g.app U.1 (c + d) = g.app U.1 c + g.app U.1 d := map_add _ _ _
    rw [← hcd, hsplit, h1, h2, add_zero]
  rw [comp_app_apply]
  exact key _ (kernel_ι_app_mem_ideal (Z ⊔ Y) U m)

/-- `𝒪_S ⟶ 𝒪_Y ⟶ 𝒪_{Z ⊔ Y}` is `𝒪_S ⟶ 𝒪_Z ⟶ 𝒪_{Z ⊔ Y}`, so `ℐ_Z ⟶ 𝒪_Y ⟶ 𝒪_{Z ⊔ Y}` vanishes. -/
lemma kernel_ι_comp_ambientToClosedSubscheme_comp_restriction (Z Y : S.IdealSheafData) :
    (kernel.ι (ambientToClosedSubscheme Z) ≫ ambientToClosedSubscheme Y) ≫
      closedSubschemeRestriction (le_sup_right : Y ≤ Z ⊔ Y) = 0 := by
  rw [Category.assoc, ambientToClosedSubscheme_comp_closedSubschemeRestriction,
    ← ambientToClosedSubscheme_comp_closedSubschemeRestriction (le_sup_left : Z ≤ Z ⊔ Y),
    kernel.condition_assoc, zero_comp]

/-- **The image of `ℐ_Z` in `𝒪_Y` is the ideal of `Z ∩ Y` in `Y`**: the restriction
`𝒪_Y ⟶ 𝒪_{Z ⊔ Y}` is a cokernel of `ℐ_Z ⟶ 𝒪_S ⟶ 𝒪_Y`. A map `k : 𝒪_Y ⟶ T` killing `ℐ_Z` gives
a map `𝒪_S ⟶ T` killing `ℐ_Z` and `ℐ_Y`, hence `ℐ_{Z ⊔ Y}`
(`AlgebraicGeometry.Scheme.IdealSheafData.kernel_ι_sup_comp_eq_zero`), which descends to
`𝒪_{Z ⊔ Y}`. -/
theorem nonempty_isColimitRestrictionSup (Z Y : S.IdealSheafData) :
    Nonempty (IsColimit (CokernelCofork.ofπ (closedSubschemeRestriction (le_sup_right : Y ≤ Z ⊔ Y))
      (kernel_ι_comp_ambientToClosedSubscheme_comp_restriction Z Y))) := by
  have := ambientToClosedSubscheme_epi Y
  have := ambientToClosedSubscheme_epi (Z ⊔ Y)
  have : Epi (closedSubschemeRestriction (le_sup_right : Y ≤ Z ⊔ Y)) :=
    epi_of_epi_fac
      (ambientToClosedSubscheme_comp_closedSubschemeRestriction (le_sup_right : Y ≤ Z ⊔ Y))
  refine ⟨CokernelCofork.IsColimit.ofπ' _ _ fun {T} k hk => ?_⟩
  have hk' : kernel.ι (ambientToClosedSubscheme (Z ⊔ Y)) ≫
      (ambientToClosedSubscheme Y ≫ k) = 0 := by
    refine kernel_ι_sup_comp_eq_zero Z Y _ ?_ ?_
    · rwa [← Category.assoc]
    · rw [kernel.condition_assoc, zero_comp]
  refine ⟨Abelian.epiDesc (ambientToClosedSubscheme (Z ⊔ Y)) _ hk', ?_⟩
  apply (cancel_epi (ambientToClosedSubscheme Y)).mp
  rw [ambientToClosedSubscheme_comp_closedSubschemeRestriction_assoc, Abelian.comp_epiDesc]

/-- **The ideal of the scheme-theoretic union is the intersection of the two ideals**, in the
form that a map into `𝒪_S` which dies in `𝒪_A` and in `𝒪_B` dies in `𝒪_{A ⊓ B}`: the pair of
restrictions out of `𝒪_{A ⊓ B}` is a monomorphism. -/
theorem comp_ambientToClosedSubscheme_inf_eq_zero (A B : S.IdealSheafData) {T : S.Modules}
    (a : T ⟶ ambientStructureSheaf S) (hA : a ≫ ambientToClosedSubscheme A = 0)
    (hB : a ≫ ambientToClosedSubscheme B = 0) :
    a ≫ ambientToClosedSubscheme (A ⊓ B) = 0 := by
  have := unionToBiprod_mono A B
  apply (cancel_mono (unionToBiprod A B)).mp
  rw [Category.assoc, ambientToClosedSubscheme_inf_comp_unionToBiprod, zero_comp]
  exact biprod.hom_ext _ _ (by simpa using hA) (by simpa using hB)

/-- **For disjoint closed subschemes `A` and `B`, the ideal `ℐ_Z` is the sum of `ℐ_Z ∩ ℐ_A` and
`ℐ_Z ∩ ℐ_B`**, in the form that a map out of `ℐ_Z` which vanishes on both is zero. Disjointness
is `A ⊔ B = ⊤`, so on an affine open `1 = a + b` with `a ∈ ℐ_A`, `b ∈ ℐ_B`, and every section
`x` of `ℐ_Z` is `a x + b x` with `a x` dying in `𝒪_A` and `b x` in `𝒪_B`. -/
theorem eq_zero_of_sup_eq_top (Z A B : S.IdealSheafData) (hAB : A ⊔ B = ⊤) {T : S.Modules}
    (g : kernel (ambientToClosedSubscheme Z) ⟶ T)
    (hA : kernel.ι (kernel.ι (ambientToClosedSubscheme Z) ≫ ambientToClosedSubscheme A) ≫ g = 0)
    (hB : kernel.ι (kernel.ι (ambientToClosedSubscheme Z) ≫ ambientToClosedSubscheme B) ≫ g = 0) :
    g = 0 := by
  apply hom_eq_zero_of_app_affineOpens
  intro U x
  have h1 : (1 : Γ(S, U.1)) ∈ (A ⊔ B).ideal U := by
    rw [hAB, ideal_top]
    exact Submodule.mem_top
  rw [ideal_sup] at h1
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  have hann : ∀ (C : S.IdealSheafData) (c : Γ(S, U.1)), c ∈ C.ideal U →
      ∀ y : Γ(kernel (ambientToClosedSubscheme Z), U.1),
        (kernel.ι (ambientToClosedSubscheme Z) ≫ ambientToClosedSubscheme C).app U.1 (c • y) = 0 :=
    fun C c hc y => by
      rw [Scheme.Modules.Hom.app_smul]
      exact (Stacks.ClosedImmersion.pushforward_essImage_iff C.subschemeι _).mp
        ((Scheme.Modules.pushforward C.subschemeι).obj_mem_essImage _) U.1 c
        ((ambientToClosedSubscheme_app_eq_zero_iff_mem_ideal C U c).2 hc) _
  have hkill : ∀ (C : S.IdealSheafData) (c : Γ(S, U.1)), c ∈ C.ideal U →
      kernel.ι (kernel.ι (ambientToClosedSubscheme Z) ≫ ambientToClosedSubscheme C) ≫ g = 0 →
      ∀ y : Γ(kernel (ambientToClosedSubscheme Z), U.1), g.app U.1 (c • y) = 0 :=
    fun C c hc hg y =>
      app_eq_zero_of_kernel_ι_comp_eq_zero _ g hg U.1 (c • y) (hann C c hc y)
  have hx : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
  rw [hx, map_add, hkill A a ha hA x, hkill B b hb hB x, add_zero]

end AlgebraicGeometry.Scheme.IdealSheafData

end
