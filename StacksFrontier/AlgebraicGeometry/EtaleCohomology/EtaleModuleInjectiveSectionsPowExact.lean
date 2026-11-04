module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsAcyclic
public import StacksFrontier.Algebra.Module.Injective.ZModPrimePower

/-!
# Sections of injective sheaves of `ℤ/pᵐℤ`-modules

Let `I` be an injective sheaf of `ℤ/pᵐℤ`-modules on the small étale site of a scheme.  For every
object `U` of the site, and every `a ≤ m`, an element of `I(U)` killed by `p^a` is a multiple
of `p^(m - a)`: the sections of `I` are "flat" over `ℤ/pᵐℤ`
(`Stacks.ZModPrimePower.IsPowExact`).  Indeed `I(U)` is `Hom(ℤ/pᵐℤ_U, I)` for the sheafified free
module `ℤ/pᵐℤ_U` on `U`, the sequence `ℤ/pᵐℤ_U --p^(m-a)--> ℤ/pᵐℤ_U --p^a--> ℤ/pᵐℤ_U` is exact
(it is so sectionwise before sheafification, where the modules are free), and `Hom(-, I)` is
exact.

This is the input that identifies `I / p^{m'} I` with `I[p^{m'}]` in the change of coefficients
behind [Tag 03V2].

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

open Stacks.ZModPrimePower

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {X : Scheme.{u}}

/-- The short complex `P --p^(m-a)--> P --p^a--> P` on an object killed by `p^m`. -/
abbrev powShortComplex {C : Type*} [Category* C] [Preadditive C] (P : C) (a : ℕ)
    (h : (p ^ (m - a) * p ^ a) • 𝟙 P = 0) : ShortComplex C :=
  ShortComplex.mk ((p ^ (m - a)) • 𝟙 P) ((p ^ a) • 𝟙 P) (by
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, ← mul_nsmul']
    exact h)

/-- The sheafified free module on `U` has the exactness property in the category of sheaves:
`ℤ/pᵐℤ_U --p^(m-a)--> ℤ/pᵐℤ_U --p^a--> ℤ/pᵐℤ_U` is exact. -/
theorem exact_freeYonedaSheaf_pow (U : X.Etale) (a : ℕ) (ha : a ≤ m)
    (h : (p ^ (m - a) * p ^ a) • 𝟙 (freeYonedaSheaf (Λ := ZMod (p ^ m)) U) = 0) :
    (powShortComplex (freeYonedaSheaf (Λ := ZMod (p ^ m)) U) a h).Exact := by
  let F := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod (p ^ m)))
  let P := freeYonedaPresheaf (Λ := ZMod (p ^ m)) U
  have hP : (p ^ (m - a) * p ^ a) • 𝟙 P = 0 := by
    rw [mul_comm, ← pow_add, Nat.add_sub_cancel' ha]
    ext V x
    show (p ^ m) • x = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ m)), ZMod.natCast_self, zero_smul]
  have hpre : (powShortComplex P a hP).Exact := by
    apply (ShortComplex.exact_iff_isZero_homology _).mpr
    apply (IsZero.iff_id_eq_zero _).mpr
    apply NatTrans.ext
    funext V
    have hV : ((powShortComplex P a hP).map ((CategoryTheory.evaluation _ _).obj V)).Exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      obtain ⟨y, hy⟩ := isPowExact_finsupp (p := p) (m := m) _ a ha x hx
      exact ⟨y, hy⟩
    let ev := (CategoryTheory.evaluation (X.Etaleᵒᵖ) (ModuleCat.{u + 1} (ZMod (p ^ m)))).obj V
    exact ((((powShortComplex P a hP).map ev).exact_iff_isZero_homology.mp hV).of_iso
      ((powShortComplex P a hP).mapHomologyIso ev).symm).eq_of_src _ _
  have hmap := hpre.map F
  refine (ShortComplex.exact_iff_of_iso ?_).1 hmap
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [F, powShortComplex]
  · simp [F, powShortComplex]

/-- **The sections of an injective sheaf of `ℤ/pᵐℤ`-modules are flat**: in `I(U)`, an element
killed by `p^a` is a multiple of `p^(m - a)`. -/
theorem isPowExact_sections_of_injective (I : EtaleModules.{u, 0} (ZMod (p ^ m)) X) [Injective I]
    (U : X.Etale) : IsPowExact p m (I.obj.obj (op U)) := by
  let P := freeYonedaSheaf (Λ := ZMod (p ^ m)) U
  have hP : ∀ a ≤ m, (p ^ (m - a) * p ^ a) • 𝟙 P = 0 := by
    intro a ha
    rw [mul_comm, ← pow_add, Nat.add_sub_cancel' ha]
    apply Sheaf.hom_ext
    ext V x
    show (p ^ m) • x = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ m)), ZMod.natCast_self, zero_smul]
  have hhom : IsPowExact p m (P ⟶ I) := by
    intro a ha f hf
    have hS := exact_freeYonedaSheaf_pow (p := p) U (m - a) (Nat.sub_le m a)
      (hP (m - a) (Nat.sub_le m a))
    have hf' : (powShortComplex P (m - a) (hP (m - a) (Nat.sub_le m a))).f ≫ f = 0 := by
      simp only [powShortComplex]
      rw [Nat.sub_sub_self ha, Preadditive.nsmul_comp, Category.id_comp]
      exact hf
    refine ⟨hS.descToInjective f hf', ?_⟩
    have := hS.comp_descToInjective f hf'
    simp only [powShortComplex] at this
    rwa [Preadditive.nsmul_comp, Category.id_comp] at this
  exact hhom.of_addEquiv
    (((freeYonedaSheafSectionsCorepresentation (Λ := ZMod (p ^ m)) U).app I).symm
      ).addCommGroupIsoToAddEquiv

/-- **The sections of an injective sheaf of `ℤ/pᵐℤ`-modules are injective `ℤ/pᵐℤ`-modules.** -/
theorem injective_sections_of_injective (I : EtaleModules.{u, 0} (ZMod (p ^ m)) X) [Injective I]
    (U : X.Etale) : Module.Injective (ZMod (p ^ m)) (I.obj.obj (op U)) :=
  (baer_of_isPowExact (isPowExact_sections_of_injective I U)).injective

end Stacks.EtaleCohomology

end
