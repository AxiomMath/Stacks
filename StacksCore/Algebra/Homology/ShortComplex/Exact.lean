module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
import StacksCore.Tactic.StacksAttribute

/-! # Exact short complexes

Mirror lemmas about the image `F(S)` of a short complex under a functor `F : D ⥤ C` preserving
zero morphisms, `C` preadditive: if `F(S)` has homology and `F` preserves the kernel of `S.g`
then `F(S)` is exact iff `F(X₁ ⟶ Ker S.g)` is an epimorphism
(`ShortComplex.exact_map_iff_epi_map_kernel_lift`), and dually for the cokernel of `S.f`
(`ShortComplex.exact_map_iff_mono_map_cokernel_desc`); without preservation, in a balanced `C`,
exactness of `F(S)` still makes `F(X₁ ⟶ Ker S.g)` an epimorphism when `F(Ker S.g ⟶ X₂)` is a
monomorphism (`ShortComplex.Exact.epi_map_kernel_lift`), and dually
(`ShortComplex.Exact.mono_map_cokernel_desc`). All four are phrased through Mathlib's
`kernelComparison`/`cokernelComparison`.

In a preadditive balanced category, an exact short complex whose first arrow is a monomorphism is
determined up to isomorphism by its second arrow, and one whose second arrow is an epimorphism by
its first arrow: `ShortComplex.Exact.isoMk₁` builds an isomorphism of short complexes from
isomorphisms of the second and third terms, inducing the first component on the kernels, and
`ShortComplex.Exact.isoMk₃` builds one from isomorphisms of the first and second terms, inducing the
third component on the cokernels. -/

add_to_stacks 010E CategoryTheory.ShortComplex.Exact
add_to_stacks 010F CategoryTheory.ShortComplex.Splitting
add_to_stacks 010G CategoryTheory.ShortComplex.Splitting.ofExactOfSection
add_to_stacks 010G CategoryTheory.ShortComplex.Splitting.ofExactOfRetraction

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D] [Preadditive C] [HasZeroMorphisms D]
  (S : ShortComplex D)
  (F : D ⥤ C) [F.PreservesZeroMorphisms]

section Kernel

variable [HasKernel S.g]

variable {S F} in
/-- If `F(Ker S.g) ⟶ F(X₂)` is a monomorphism and `F(S)` is exact, then `F(X₁ ⟶ Ker S.g)` is an
epimorphism, `C` being balanced: the comparison `F(Ker S.g) ⟶ Ker(F S.g)` is a monomorphism
whose composite with `F(X₁) ⟶ F(Ker S.g)` is the epimorphism `F(X₁) ⟶ Ker(F S.g)` of exactness,
hence an isomorphism. -/
lemma Exact.epi_map_kernel_lift [Balanced C] [Mono (F.map (kernel.ι S.g))]
    (h : (S.map F).Exact) : Epi (F.map (kernel.lift S.g S.f S.zero)) := by
  have := h.hasHomology
  have : HasKernel (F.map S.g) := HasLeftHomology.hasKernel (S.map F)
  have : HasKernel (S.map F).g := ‹HasKernel (F.map S.g)›
  have : Mono (kernelComparison S.g F) := mono_of_mono_fac (kernelComparison_comp_ι S.g F)
  have h₁ : Epi (F.map (kernel.lift S.g S.f S.zero) ≫ kernelComparison S.g F) := by
    rw [map_lift_kernelComparison]
    exact (exact_iff_epi_kernel_lift _).1 h
  have : Epi (kernelComparison S.g F) := epi_of_epi (F.map (kernel.lift S.g S.f S.zero)) _
  have : IsIso (kernelComparison S.g F) := isIso_of_mono_of_epi _
  exact (epi_comp_iff_of_isIso _ _).1 h₁

variable [(S.map F).HasHomology]

/-- If `F` preserves the kernel of `S.g`, then `F(S)` is exact iff `F(X₁ ⟶ Ker S.g)` is an
epimorphism: `F(Ker S.g) ≅ Ker(F S.g)` by the comparison morphism. -/
lemma exact_map_iff_epi_map_kernel_lift [PreservesLimit (parallelPair S.g 0) F] :
    (S.map F).Exact ↔ Epi (F.map (kernel.lift S.g S.f S.zero)) := by
  have : HasKernel (S.map F).g := inferInstanceAs (HasKernel (F.map S.g))
  have e : F.map (kernel.lift S.g S.f S.zero) ≫ kernelComparison S.g F =
      kernel.lift (S.map F).g (S.map F).f (S.map F).zero :=
    map_lift_kernelComparison S.g F S.zero
  rw [exact_iff_epi_kernel_lift, ← e, epi_comp_iff_of_isIso]

end Kernel

section Cokernel

variable [HasCokernel S.f]

variable {S F} [HasCokernel (F.map S.f)] in
/-- If `F(X₂) ⟶ F(Coker S.f)` is an epimorphism and `F(S)` is exact, then `F(Coker S.f ⟶ X₃)` is
a monomorphism, `C` being balanced: the comparison `Coker(F S.f) ⟶ F(Coker S.f)` is an
epimorphism whose composite with `F(Coker S.f) ⟶ F(X₃)` is the monomorphism
`Coker(F S.f) ⟶ F(X₃)` of exactness, hence an isomorphism. -/
lemma Exact.mono_map_cokernel_desc [Balanced C] [Epi (F.map (cokernel.π S.f))]
    (h : (S.map F).Exact) : Mono (F.map (cokernel.desc S.f S.g S.zero)) := by
  have := h.hasHomology
  have : HasCokernel (S.map F).f := ‹HasCokernel (F.map S.f)›
  have : Epi (cokernelComparison S.f F) := epi_of_epi_fac (π_comp_cokernelComparison S.f F)
  have h₁ : Mono (cokernelComparison S.f F ≫ F.map (cokernel.desc S.f S.g S.zero)) := by
    rw [cokernelComparison_map_desc]
    exact (exact_iff_mono_cokernel_desc _).1 h
  have : Mono (cokernelComparison S.f F) := mono_of_mono _ (F.map (cokernel.desc S.f S.g S.zero))
  have : IsIso (cokernelComparison S.f F) := isIso_of_mono_of_epi _
  exact (mono_comp_iff_of_isIso _ _).1 h₁

variable [(S.map F).HasHomology]

/-- If `F` preserves the cokernel of `S.f`, then `F(S)` is exact iff `F(Coker S.f ⟶ X₃)` is a
monomorphism: `Coker(F S.f) ≅ F(Coker S.f)` by the comparison morphism. -/
lemma exact_map_iff_mono_map_cokernel_desc [PreservesColimit (parallelPair S.f 0) F] :
    (S.map F).Exact ↔ Mono (F.map (cokernel.desc S.f S.g S.zero)) := by
  have : HasCokernel (S.map F).f := inferInstanceAs (HasCokernel (F.map S.f))
  have e : cokernelComparison S.f F ≫ F.map (cokernel.desc S.f S.g S.zero) =
      cokernel.desc (S.map F).f (S.map F).g (S.map F).zero :=
    cokernelComparison_map_desc S.f F S.zero
  rw [exact_iff_mono_cokernel_desc, ← e, mono_comp_iff_of_isIso]

end Cokernel

section IsoMk

variable [Balanced C]

/-- An exact short complex whose first arrow is a monomorphism is determined up to isomorphism
by its second arrow: isomorphisms `e₂ : S.X₂ ≅ S'.X₂` and `e₃ : S.X₃ ≅ S'.X₃` with
`e₂.hom ≫ S'.g = S.g ≫ e₃.hom` extend to an isomorphism `S ≅ S'`. Its first component is the
isomorphism `S.X₁ ≅ S'.X₁` that `e₂` induces between the kernels `S.f` of `S.g` and `S'.f` of
`S'.g`. -/
@[simps!]
noncomputable def Exact.isoMk₁ {S S' : ShortComplex C} (hS : S.Exact) (hS' : S'.Exact)
    [Mono S.f] [Mono S'.f] (e₂ : S.X₂ ≅ S'.X₂) (e₃ : S.X₃ ≅ S'.X₃)
    (comm : e₂.hom ≫ S'.g = S.g ≫ e₃.hom) : S ≅ S' :=
  have comm' : e₂.inv ≫ S.g = S'.g ≫ e₃.inv := (CommSq.mk comm).horiz_inv.w
  ShortComplex.isoMk
    { hom := hS'.lift (S.f ≫ e₂.hom) (by rw [Category.assoc, comm, S.zero_assoc, zero_comp])
      inv := hS.lift (S'.f ≫ e₂.inv) (by rw [Category.assoc, comm', S'.zero_assoc, zero_comp])
      hom_inv_id := by simp [← cancel_mono S.f]
      inv_hom_id := by simp [← cancel_mono S'.f] }
    e₂ e₃ (by simp) comm

/-- An exact short complex whose second arrow is an epimorphism is determined up to isomorphism
by its first arrow: isomorphisms `e₁ : S.X₁ ≅ S'.X₁` and `e₂ : S.X₂ ≅ S'.X₂` with
`e₁.hom ≫ S'.f = S.f ≫ e₂.hom` extend to an isomorphism `S ≅ S'`. Its third component is the
isomorphism `S.X₃ ≅ S'.X₃` that `e₂` induces between the cokernels `S.g` of `S.f` and `S'.g` of
`S'.f`. -/
@[simps!]
noncomputable def Exact.isoMk₃ {S S' : ShortComplex C} (hS : S.Exact) (hS' : S'.Exact)
    [Epi S.g] [Epi S'.g] (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂)
    (comm : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) : S ≅ S' :=
  have comm' : e₁.inv ≫ S.f = S'.f ≫ e₂.inv := (CommSq.mk comm).horiz_inv.w
  ShortComplex.isoMk e₁ e₂
    { hom := hS.desc (e₂.hom ≫ S'.g) (by rw [← reassoc_of% comm, S'.zero, comp_zero])
      inv := hS'.desc (e₂.inv ≫ S.g) (by rw [← reassoc_of% comm', S.zero, comp_zero])
      hom_inv_id := by simp [← cancel_epi S.g]
      inv_hom_id := by simp [← cancel_epi S'.g] }
    comm (by simp)

end IsoMk

end CategoryTheory.ShortComplex
