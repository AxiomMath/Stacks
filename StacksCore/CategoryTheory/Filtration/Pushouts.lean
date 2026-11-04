module

public import StacksCore.CategoryTheory.Abelian.Images
public import StacksCore.CategoryTheory.Filtration.GradedExact
import StacksCore.Tactic.StacksAttribute

/-! # Pushouts of filtered objects: Stacks 05SM

Stacks 05SM: let `𝒜` be an abelian category and `f : A ⟶ B`, `g : A ⟶ D` morphisms of `Fil(𝒜)`.
Then the pushout `B ⊔_A D` exists in `Fil(𝒜)`, and if `f` is strict, so is its cobase change
`f' : D ⟶ B ⊔_A D`. Existence is `FilteredObject.hasFiniteColimits`
(`StacksCore.CategoryTheory.Filtration.Limits`). Unlike fibre products (Stacks 05SN), pushouts are
not computed on the steps, `F^i(B ⊔_A D)` being the *image* of `F^iB ⊕ F^iD`; they are computed
on the quotients by the steps: `X ↦ X/F^iX` is right exact (`preservesFiniteColimits_quot`, for
any index category `I` and any additive `𝒜` with cokernels and strong epi images), so
`(B ⊔_A D)/F^i = B/F^iB ⊔_{A/F^iA} D/F^iD` (`isPushout_quot_map`), and the forgetful functor
preserves pushouts as well (`isPushout_hom`).

The proof of the strictness statement is the mirror image of that of 05SN in
`StacksCore.CategoryTheory.Filtration.Pullbacks`, in the calculus of `Subobject.exists`:

* `IsPushout.kernelSubobject_inr`: in an abelian category the kernel of a cobase change is the
  image of the kernel, `Ker(Z ⟶ Y ⊔_X Z) = g(Ker f)` (the dual of `IsPullback.imageSubobject_snd`,
  together with the dual Beck–Chevalley identity `IsPushout.pullback_exists`; in
  `StacksCore.CategoryTheory.Abelian.Images`);
* `FilteredObject.isStrict_iff_kernelSubobject_quot_map_eq`: `f` is strict if and only if on each
  quotient the kernel of `A/F^iA ⟶ B/F^iB` is the image of `Ker f` (the dual of
  `isStrict_iff_imageSubobject_natTrans_app_eq`; in
  `StacksCore.CategoryTheory.Filtration.GradedExact`);
* `FilteredObject.isStrict_pushout_inr`, `isStrict_pushout_inl`: strictness is stable under
  cobase change, and so is cartesianness (`isStrictHom_pushout_inr`), for any index category `I`
  (this file);
* `FilteredObject.mono_quot_map_pushout_inr`: the cobase change of a morphism which is a
  monomorphism on the quotient by a step is a monomorphism on that quotient (pushouts of
  monomorphisms are monomorphisms in `𝒜`), the mirror of `epi_natTrans_app_pullback_snd`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {I : Type*} [Category* I]

namespace FilteredObject

open Filtration

section Abelian

variable [Abelian C] {A B D : FilteredObject C I} (f : A ⟶ B) (g : A ⟶ D)

/-- The cobase change of a morphism which is a monomorphism on the quotient by the step `i` is
a monomorphism on that quotient: the quotients of the pushout are computed level-wise, and
pushouts of monomorphisms are monomorphisms in the abelian category `𝒜`. -/
theorem mono_quot_map_pushout_inr (i : I) [Mono ((quot i).map f)] :
    Mono ((quot i).map (pushout.inr f g)) :=
  Abelian.mono_inr_of_isColimit _ _ (isPushout_quot_map f g i).isColimit

/-- The symmetric version of `mono_quot_map_pushout_inr`, for the first coprojection. -/
theorem mono_quot_map_pushout_inl (i : I) [Mono ((quot i).map g)] :
    Mono ((quot i).map (pushout.inl f g)) :=
  Abelian.mono_inl_of_isColimit _ _ (isPushout_quot_map f g i).isColimit

/-- Cartesian morphisms are stable under cobase change in `Fil(𝒜)`: `pushout.inr f g` is
cartesian when `f` is, being a monomorphism on every quotient `D/F^iD ⟶ (B ⊔_A D)/F^i`
(`isStrictHom_iff_forall_mono_quot_map`). -/
instance isStrictHom_pushout_inr [IsStrictHom f] : IsStrictHom (pushout.inr f g) :=
  isStrictHom_of_forall_mono_quot_map _ fun i =>
    have := mono_quot_map_of_isStrictHom f i
    mono_quot_map_pushout_inr f g i

/-- Cartesian morphisms are stable under cobase change in `Fil(𝒜)`: `pushout.inl f g` is
cartesian when `g` is. -/
instance isStrictHom_pushout_inl [IsStrictHom g] : IsStrictHom (pushout.inl f g) :=
  isStrictHom_of_forall_mono_quot_map _ fun i =>
    have := mono_quot_map_of_isStrictHom g i
    mono_quot_map_pushout_inl f g i

/-- Stacks 05SM: if `f : A ⟶ B` is strict, so is its cobase change `f' : D ⟶ B ⊔_A D` along
any `g : A ⟶ D`. On the quotient by the step `i`, `Ker(D/F^iD ⟶ (B ⊔_A D)/F^i) = g_i(Ker f_i)`
since the quotients of the pushout are computed level-wise and the kernel of a cobase change is
the image of the kernel; by strictness `Ker f_i` is the image of `Ker f` in `A/F^iA`, so this is
the image in `D/F^iD` of `g(Ker f) = Ker f'`, which is the strictness of `f'`. -/
@[stacks 05SM "if `f` is strict, so is its cobase change `f' : D ⟶ B ⊔_A D`, for any `I`"]
instance isStrict_pushout_inr [IsStrict f] : IsStrict (pushout.inr f g) := by
  refine (isStrict_iff_kernelSubobject_quot_map_eq _).2 fun i => ?_
  -- `Ker(D/F^iD ⟶ (B ⊔_A D)/F^i) = g_i(Ker f_i)`, the quotients being computed level-wise
  rw [(isPushout_quot_map f g i).kernelSubobject_inr,
    (isStrict_iff_kernelSubobject_quot_map_eq f).1 ‹_› i, ← Subobject.exists_comp, quotπ_map,
    Subobject.exists_comp, (isPushout_hom f g).kernelSubobject_inr]

/-- Stacks 05SM, symmetrically: if `g : A ⟶ D` is strict, so is its cobase change
`g' : B ⟶ B ⊔_A D` along any `f : A ⟶ B`. -/
@[stacks 05SM "if `g` is strict, so is its cobase change `g' : B ⟶ B ⊔_A D`, for any `I`"]
instance isStrict_pushout_inl [IsStrict g] : IsStrict (pushout.inl f g) := by
  rw [← inr_comp_pushoutSymmetry_hom, isStrict_comp_isIso_iff]
  infer_instance

end Abelian

end FilteredObject

end CategoryTheory
