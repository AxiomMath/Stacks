module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of a quasi-coherent module over a basic open, elementwise

`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ` says that for `V`
an affine open of a scheme, `f : Γ(X, V)` and `F` a quasi-coherent `𝒪_X`-module, the restriction
map `Γ(F, V) → Γ(F, X.basicOpen f)` exhibits the target as the localization of the source away
from `f`. That statement is phrased through `IsLocalizedModule.Away` and through the
`Γ(X, V)`-module structure `moduleOfLE` puts on `Γ(F, X.basicOpen f)`; this file reads off the two
consequences the gluing argument of Stacks Tag 01PW actually uses, in the *native*
`Γ(X, X.basicOpen f)`-module structure and with no `letI` in the statement.

They are the module-valued forms of the two `𝒪_X`-valued Mathlib lemmas that the `𝓕 = 𝒪_X` case of
Tag 01PW runs on:

| `𝓕 = 𝒪_X` (Mathlib) | arbitrary quasi-coherent `𝓕` (here) |
|---|---|
| `AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen` | `exists_pow_smul_eq_res` |
| the `isAffineOpen` annihilator lemma (below) | `exists_pow_smul_eq_zero` |

## Main results

* `Stacks.ModuleSectionExtension.exists_pow_smul_eq_res`: **the local extension.** A section of a
  quasi-coherent module over `X.basicOpen f`, multiplied by a high enough power of `f`, is the
  restriction of a section over the ambient affine open.
* `Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero`: **the annihilator.** A section over an
  affine open that restricts to zero on `X.basicOpen f` is killed by a power of `f`.
* `Stacks.ModuleSectionExtension.exists_pow_smul_eq_of_res_eq`: the difference form of the
  previous one, which is the shape the gluing uses it in.

## Implementation notes

The scalar bookkeeping is the whole content. `moduleOfLE F h` is `Module.compHom` along the
restriction map of the structure sheaf, so a `Γ(X, V)`-scalar acts on `Γ(F, X.basicOpen f)` as its
restriction does — by `rfl`, since `Module.compHom` is an `abbrev` over `SMul.comp`. The
statements below therefore mention only the native action, and each proof is one
`IsLocalizedModule` call plus `map_pow`.

`AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen` is stated for
`𝒪_X` with no quasi-coherence hypothesis, because the structure sheaf is quasi-coherent; here
quasi-coherence of `F` is a hypothesis, as it must be — a non-quasi-coherent module on an affine
scheme has no relation between its sections over `V` and over `X.basicOpen f` at all.

No `@[stacks]` attribute is attached: nothing here is the statement of a tag. Stacks Tag 01I9 and
Tag 01IA are the content of the imported file, which already cites them.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.ModuleSectionExtension

variable {X : Scheme.{u}}

/-- Restriction of a section of an `𝒪_X`-module along an inclusion of opens, written as a
function of the inclusion proof. -/
abbrev res (M : X.Modules) {V W : X.Opens} (h : W ≤ V) (x : Γ(M, V)) : Γ(M, W) :=
  M.presheaf.map (homOfLE h).op x

/-- Restriction of a function along an inclusion of opens. -/
abbrev resR {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) : Γ(X, W) :=
  X.presheaf.map (homOfLE h).op x

/-- Restriction to `X.basicOpen f` is the localization away from `f`, for the module structure
`moduleOfLE`. -/
private theorem isLocalizedModule_away_restrictₗ (F : X.Modules) [F.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) (f : Γ(X, V)) :
    letI := moduleOfLE F (X.basicOpen_le f)
    IsLocalizedModule.Away f (restrictₗ F (X.basicOpen_le f)) :=
  isLocalizedModule_restrictₗ F hV f rfl (X.basicOpen_le f)

/-- **The local extension, module-valued.** For `V` an affine open of a scheme, `F` a
quasi-coherent `𝒪_X`-module and `f : Γ(X, V)`, every section `t` of `F` over `X.basicOpen f`
becomes, after multiplication by a high enough power of `f`, the restriction of a section of `F`
over `V`.

This is `AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen` with the structure sheaf replaced by
an arbitrary quasi-coherent module, and it is the module-valued form of step 2 of the proof of
Stacks Tag 01PW. -/
@[ega "I 1.4.1" "partial"]
theorem exists_pow_smul_eq_res (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (f : Γ(X, V)) (t : Γ(F, X.basicOpen f)) :
    ∃ (e : ℕ) (c : Γ(F, V)),
      resR (X.basicOpen_le f) f ^ e • t = res F (X.basicOpen_le f) c := by
  let := moduleOfLE F (X.basicOpen_le f)
  have := isLocalizedModule_away_restrictₗ F hV f
  obtain ⟨e, c, hc⟩ := IsLocalizedModule.Away.surj (restrictₗ F (X.basicOpen_le f)) f t
  refine ⟨e, c, ?_⟩
  rw [← map_pow]
  exact hc

/-- **The annihilator, module-valued.** For `V` an affine open of a scheme, `F` a quasi-coherent
`𝒪_X`-module and `f : Γ(X, V)`, a section of `F` over `V` which restricts to zero on
`X.basicOpen f` is killed by a power of `f`.

This is `AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen` with
the structure sheaf replaced by an arbitrary quasi-coherent module, and it is the module-valued
form of the injectivity input to step 4 of the proof of Stacks Tag 01PW. -/
@[ega "I 1.4.1" "partial"]
theorem exists_pow_smul_eq_zero (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (f : Γ(X, V)) (c : Γ(F, V))
    (hc : res F (X.basicOpen_le f) c = 0) :
    ∃ e : ℕ, f ^ e • c = 0 := by
  let := moduleOfLE F (X.basicOpen_le f)
  have := isLocalizedModule_away_restrictₗ F hV f
  obtain ⟨⟨-, e, rfl⟩, he⟩ :=
    (IsLocalizedModule.eq_zero_iff (S := Submonoid.powers f)
      (restrictₗ F (X.basicOpen_le f))).mp hc
  exact ⟨e, he⟩

/-- **The annihilator in difference form**, which is how the gluing argument of Stacks Tag 01PW
uses it: two sections of `F` over an affine open agreeing on `X.basicOpen f` agree after
multiplication by a power of `f`. -/
theorem exists_pow_smul_eq_of_res_eq (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (f : Γ(X, V)) (c c' : Γ(F, V))
    (hc : res F (X.basicOpen_le f) c = res F (X.basicOpen_le f) c') :
    ∃ e : ℕ, f ^ e • c = f ^ e • c' := by
  let := moduleOfLE F (X.basicOpen_le f)
  have := isLocalizedModule_away_restrictₗ F hV f
  exact IsLocalizedModule.Away.exists_of_eq (f := restrictₗ F (X.basicOpen_le f)) f hc

end Stacks.ModuleSectionExtension

end
