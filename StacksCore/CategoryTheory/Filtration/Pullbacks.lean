module

public import StacksCore.CategoryTheory.Abelian.Images
public import StacksCore.CategoryTheory.Filtration.Strict
import StacksCore.Tactic.StacksAttribute

/-! # Fibre products of filtered objects: Stacks 05SN

Stacks 05SN: let `𝒜` be an abelian category and `f : B ⟶ A`, `g : D ⟶ A` morphisms of `Fil(𝒜)`.
Then the fibre product `B ×_A D` exists in `Fil(𝒜)`, and if `f` is strict, so is its base
change `f' : B ×_A D ⟶ D`. Existence is `FilteredObject.hasFiniteLimits`, and the filtration of
the fibre product is computed level-wise, `F^i(B ×_A D) = F^iB ×_{F^iA} F^iD`
(`FilteredObject.isPullback_natTrans_app`; both in `StacksCore.CategoryTheory.Filtration.Limits`,
for any index category `I` and any additive `𝒜` with kernels). This file proves the strictness
statement, for any index category `I`:

* `FilteredObject.isStrict_pullback_snd` and `isStrict_pullback_fst`: strictness is stable under
  base change. The proof is the dual of Stacks' proof of 05SM, in the calculus of
  `Subobject.pullback`: on the step `i`, `f'(F^i(B ×_A D)) = g_i⁻¹(f_i(F^iB))`, since the fibre
  product is computed level-wise and the image of a base change is the preimage of the image
  (`IsPullback.imageSubobject_snd`, `StacksCore.CategoryTheory.Abelian.Images`); by strictness
  `f_i(F^iB) = F^iA ∩ f(B)` inside `F^iA` (`isStrict_iff_imageSubobject_natTrans_app_eq`), so this
  is `(F^iD ⟶ A)⁻¹(f(B)) = F^iD ∩ g⁻¹(f(B))`, and `g⁻¹(f(B)) = f'(B ×_A D)`.
* `FilteredObject.epi_natTrans_app_pullback_snd` and `epi_natTrans_app_pullback_fst`: the base
  change of a morphism which is an epimorphism on a step is an epimorphism on that step
  (pullbacks of epimorphisms are epimorphisms in `𝒜`).

Cartesian morphisms (Mathlib's `IsStrictHom`) are stable under base change as well
(`isStrictHom_pullback_snd`, in `StacksCore.CategoryTheory.Filtration.Limits`), and a strict morphism
factors as a strict epimorphism followed by a strict monomorphism
(`exists_isStrict_epi_comp_isStrict_mono`, in `StacksCore.CategoryTheory.Filtration.Strict`); base
changing each factor gives a second proof of 05SN, not carried out here.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {I : Type*} [Category* I]

namespace FilteredObject

open Filtration

section Abelian

variable [Abelian C] {A B D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A)

/-- If `f` is an epimorphism on the step `i`, then so is its base change
`pullback.snd f g : B ×_A D ⟶ D`. -/
theorem epi_natTrans_app_pullback_snd (i : I) [Epi (f.natTrans.app i)] :
    Epi ((pullback.snd f g).natTrans.app i) :=
  Abelian.epi_snd_of_isLimit _ _ (isPullback_natTrans_app f g i).isLimit

/-- If `g` is an epimorphism on the step `i`, then so is its base change
`pullback.fst f g : B ×_A D ⟶ B`. -/
theorem epi_natTrans_app_pullback_fst (i : I) [Epi (g.natTrans.app i)] :
    Epi ((pullback.fst f g).natTrans.app i) :=
  Abelian.epi_fst_of_isLimit _ _ (isPullback_natTrans_app f g i).isLimit

/-- Stacks 05SN: if `f : B ⟶ A` is strict, so is its base change `f' : B ×_A D ⟶ D` along any
`g : D ⟶ A`. -/
@[stacks 05SN "if `f` is strict, so is its base change `f' : B ×_A D ⟶ D`, for any `I`"]
instance isStrict_pullback_snd [IsStrict f] : IsStrict (pullback.snd f g) := by
  refine (isStrict_iff_imageSubobject_natTrans_app_eq _).2 fun i => ?_
  -- `f'(F^i(B ×_A D)) = g_i⁻¹(f_i(F^iB))`, the fibre product being computed level-wise
  have hi : imageSubobject ((pullback.snd f g).natTrans.app i) =
      (Subobject.pullback (g.natTrans.app i)).obj (imageSubobject (f.natTrans.app i)) :=
    (isPullback_natTrans_app f g i).imageSubobject_snd
  rw [hi, (isStrict_iff_imageSubobject_natTrans_app_eq f).1 ‹_› i, ← Subobject.pullback_comp,
    g.comm i, Subobject.pullback_comp, (isPullback_hom f g).imageSubobject_snd]

/-- Stacks 05SN, symmetrically: if `g : D ⟶ A` is strict, so is its base change
`g' : B ×_A D ⟶ B` along any `f : B ⟶ A`. -/
@[stacks 05SN "if `g` is strict, so is its base change `g' : B ×_A D ⟶ B`, for any `I`"]
instance isStrict_pullback_fst [IsStrict g] : IsStrict (pullback.fst f g) := by
  rw [← pullbackSymmetry_hom_comp_snd, isStrict_isIso_comp_iff]
  infer_instance

end Abelian

end FilteredObject

end CategoryTheory
