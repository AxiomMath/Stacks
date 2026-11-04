module

public import StacksFrontier.AlgebraicGeometry.KoszulRegularIdealSheaf.Algebra
public import StacksFrontier.AlgebraicGeometry.H1RegularIdealSheaf.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Koszul-regular sequences of sections

Let `X` be a ringed space, `U ⊆ X` an open set, and `f₀, …, f_{r-1}` sections of `O_X` over `U`.
Stacks tag 063D, part (2), calls the sequence Koszul-regular when the sheaf Koszul complex of
`f` on `U` is exact in every positive degree.  That condition is written out here, as a statement
about sections and no more.

Why the two agree.  The Koszul complex of `f` on `U` is a complex of *free* sheaves of modules:
its degree-`n` term is `⋀ⁿ(O_Uʳ)`, free of rank `C(r, n)`, whose sections over `V ⊆ U` are
`⋀ⁿ(O_X(V)ʳ)` — base change of exterior powers of a finite free module along `O_X(U) → O_X(V)`
is an isomorphism, which is `exists_natEquiv_extRes` of
`StacksFrontier.AlgebraicGeometry.KoszulRegularIdealSheaf.Algebra`.  The differential is the
contraction `Koszul.d` of the section-level sequence, because contraction commutes with base
change (`extRes_d`).  Exactness of a complex of sheaves in degree `n + 1` says that every section
of the kernel over every `V` lies, locally on `V`, in the image of the next differential.  That
is the definition below.

No sheaf Koszul complex, no sheaf exterior power and no sheafification functor is needed to say
this, which is why the definition is available at all: the library has no Koszul complex of
sheaves of modules.  This is the all-degree version of the degree-one condition
`Stacks.AlgebraicGeometry.H1RegularIdealSheaf.IsH1RegularSequenceOn`, which is written out with
the submodule `Koszul.relSpan` of trivial relations in place of `⋀²`; in degree one the two
spellings agree by `Koszul.map_range_d_one`.

## Main definitions

* `resExt X h r n`: a degree-`n` exterior-power chain restricted along an inclusion of opens.
* `IsKoszulRegularSequenceOn X U f`: **Stacks tag 063D, part (2)** for the local sequence `f`.

## Main results

* `resExt_res`: restriction of exterior-power chains is functorial.
* `resExt_d`: restriction commutes with the Koszul differential of the restricted sequence.
* `isKoszulRegularSequenceOn_of_le`: the condition is inherited by smaller opens.

## Implementation notes

The witness open `W` of the definition is required only to contain the given point of `V`, not
to be part of a chosen cover; quantifying over the points of `V` is the same thing and avoids
naming a sieve.  This matches the degree-one definition of
`StacksFrontier.AlgebraicGeometry.H1RegularIdealSheaf.Defs`.

## References

* [Stacks Project, Definition 31.20.1 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped ExteriorAlgebra
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.AlgebraicGeometry.H1RegularIdealSheaf
open Stacks.RingTheory.KoszulRegularIdealSheaf

universe u

namespace Stacks.AlgebraicGeometry.KoszulRegularIdealSheaf

section Restriction

variable (X : RingedSpace.{u}) {r : ℕ}

/-- A degree-`n` chain of the Koszul complex, that is an element of `⋀ⁿ` of the free module of
rank `r`, restricted along an inclusion of open sets.  This is the restriction map of the free
sheaf `⋀ⁿ(O_Xʳ)`. -/
noncomputable def resExt {U V : Opens X} (h : V ≤ U) (r n : ℕ)
    (z : ⋀[X.presheaf.obj (op U)]^n (Fin r → X.presheaf.obj (op U))) :
    ⋀[X.presheaf.obj (op V)]^n (Fin r → X.presheaf.obj (op V)) :=
  extRes (r := r) (X.presheaf.map (homOfLE h).op).hom n z

/-- Restricting the zero chain along an inclusion of open sets gives the zero chain. -/
@[simp]
theorem resExt_zero {U V : Opens X} (h : V ≤ U) (r n : ℕ) :
    resExt X h r n (0 : ⋀[X.presheaf.obj (op U)]^n (Fin r → X.presheaf.obj (op U))) = 0 :=
  extRes_zero (X.presheaf.map (homOfLE h).op).hom n

/-- **Restriction of exterior-power chains is functorial.** -/
theorem resExt_res {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) (r n : ℕ)
    (z : ⋀[X.presheaf.obj (op U)]^n (Fin r → X.presheaf.obj (op U))) :
    resExt X h₂ r n (resExt X h₁ r n z) = resExt X (h₂.trans h₁) r n z := by
  rw [resExt, resExt, resExt, extRes_comp]
  congr 1
  refine RingHom.ext fun s => ?_
  rw [RingHom.comp_apply]
  show (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op) s = _
  rw [← X.presheaf.map_comp]
  rfl

/-- **Restriction commutes with the Koszul differential.** -/
theorem resExt_d {U V : Opens X} (h : V ≤ U) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (n : ℕ)
    (z : ⋀[X.presheaf.obj (op U)]^(n + 1) (Fin r → X.presheaf.obj (op U))) :
    resExt X h r n (Koszul.d (Koszul.seqDual f) n z)
      = Koszul.d (Koszul.seqDual (resFamily X h f)) n (resExt X h r (n + 1) z) :=
  extRes_d (X.presheaf.map (homOfLE h).op).hom f n z

end Restriction

section Defs

variable (X : RingedSpace.{u})

/-- **The local Koszul-regularity condition of Stacks tag 063D, part (2).** The sequence `f` of
sections over `U` is Koszul-regular when, over every open `V ⊆ U`, every Koszul cycle of the
restricted sequence lies locally in the image of the next Koszul differential.  This is the
exactness in positive degrees of the sheaf Koszul complex of `f`, written out in sections; see
the module docstring. -/
@[sga "3 III 4.6.1" "more general"]
def IsKoszulRegularSequenceOn (U : Opens X) {r : ℕ} (f : Fin r → X.presheaf.obj (op U)) : Prop :=
  ∀ (V : Opens X) (hVU : V ≤ U) (n : ℕ)
    (z : ⋀[X.presheaf.obj (op V)]^(n + 1) (Fin r → X.presheaf.obj (op V))),
    Koszul.d (Koszul.seqDual (resFamily X hVU f)) n z = 0 →
      ∀ y : X, y ∈ V → ∃ (W : Opens X) (hWV : W ≤ V) (_ : y ∈ W)
        (w : ⋀[X.presheaf.obj (op W)]^(n + 2) (Fin r → X.presheaf.obj (op W))),
        Koszul.d (Koszul.seqDual (resFamily X (hWV.trans hVU) f)) (n + 1) w
          = resExt X hWV r (n + 1) z

/-- **The Koszul-regular condition is inherited by smaller opens.** -/
theorem isKoszulRegularSequenceOn_of_le (U : Opens X) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (U' : Opens X) (hU' : U' ≤ U)
    (h : IsKoszulRegularSequenceOn X U f) :
    IsKoszulRegularSequenceOn X U' (resFamily X hU' f) := by
  intro V hVU' n z hz y hy
  rw [resFamily_res X hU' hVU' f] at hz
  obtain ⟨W, hWV, hyW, w, hw⟩ := h V (hVU'.trans hU') n z hz y hy
  refine ⟨W, hWV, hyW, w, ?_⟩
  rw [resFamily_res X hU' (hWV.trans hVU') f]
  exact hw

end Defs

end Stacks.AlgebraicGeometry.KoszulRegularIdealSheaf

end
