module

public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtRestrictImageSequence
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerIterate
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The injectivity half of the core case of Stacks 0G2H

Let `X` be a Noetherian scheme, `𝓘` a quasi-coherent sheaf of ideals, `U = X ∖ V(𝓘)` and `𝓐`,
`𝓕` coherent `𝒪_X`-modules. This file proves the **injectivity half of the core case of**
[Stacks, Tag 0G2H] **in every degree**: a class in `Ext^i_X(𝓐, 𝓕)` whose restriction to `U`
vanishes already dies under the inclusion of some member `𝓘^n 𝓐` of the ideal-power filtration
of `𝓐`
(`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleι_comp_eq_zero_of_isCoherent`).
The base case `i = 0` is the first display of [Stacks, Tag 01YB],
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_comp_eq_zero_of_restrictFunctor_map_eq_zero`;
everything else here is the induction step. With the surjectivity half
(`Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_isCoherent`) this is the bijectivity of

`colim_n Ext^i_X(𝓘^n 𝓐, 𝓕) ⟶ Ext^i_U(𝓐|_U, 𝓕|_U)`,

the core case of the tag.

## The step from `i` to `i + 1`

Given `ξ ∈ Ext^{i+1}_X(𝓐, 𝓕)` with `ξ|_U = 0`:

1. the dimension shift `Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_of_pos` produces
   a coherent effacement `α : 𝓔 ⟶ 𝓐`, the short exact sequence
   `S : 0 ⟶ ker α ⟶ 𝓔 ⟶ 𝓐 ⟶ 0` of coherent modules and a class `ξ'` of degree `i` on `ker α`
   with `hS.extClass ∘ ξ' = ξ`;
2. restriction is exact and commutes with the boundary class, so `hS|_U.extClass ∘ ξ'|_U = 0`,
   and the contravariant long exact sequence on `U`
   (`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁`) writes `ξ'|_U` as the pullback
   along `(ker α ⟶ 𝓔)|_U` of a class `θ ∈ Ext^i_U(𝓔|_U, 𝓕|_U)`. **This is the step the induction
   hypothesis cannot supply by itself: `ξ'` need not vanish on `U`, only its boundary does;**
3. the surjectivity half in degree `i`
   (`Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_isCoherent`) lifts `θ` to a class
   `ζ ∈ Ext^i_X(𝓘^k 𝓔, 𝓕)`;
4. the two classes agree on `U` after pullback to `𝓘^k 𝓔 ⊓ ker α` — both become `θ` pulled back
   along the inclusion of that intersection into `𝓔` — so the *difference* of their pullbacks
   restricts to `0` there, and the induction hypothesis in degree `i`, applied to the coherent
   module `𝓘^k 𝓔 ⊓ ker α`, kills it on some `𝓘^m (𝓘^k 𝓔 ⊓ ker α)`;
5. Artin-Rees
   (`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleHomOfLE_inf_comp_eq_zero`)
   converts that into the vanishing on `𝓘^n 𝓔 ⊓ (𝓘^k 𝓔 ⊓ ker α)`, hence — for `N = max n k`, so
   that `𝓘^N 𝓔 ⊆ 𝓘^k 𝓔` — on `𝓘^N 𝓔 ⊓ ker α`: there `ξ'` and `ζ` have the *same* pullback;
6. and that is enough:
   `Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_submoduleι_comp_extClass_comp_eq_zero_of_eq`
   kills `ξ` on `𝓘^N 𝓐`, because the pullback of `ξ'` to the first term of the ideal-power
   sequence `0 ⟶ ker(𝓘^N 𝓔 ⟶ 𝓘^N 𝓐) ⟶ 𝓘^N 𝓔 ⟶ 𝓘^N 𝓐 ⟶ 0` comes from its middle term `𝓘^N 𝓔`
   — namely from `ζ` — and two consecutive maps of the contravariant long exact sequence compose
   to zero.

## Why the vanishing of `ξ'` itself is not what is proved

`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleι_comp_eq_zero_of_pos` assembles
the same step from the hypothesis that `ξ'` *dies* on a member of the ideal-power filtration of
`ker α`. That hypothesis is stronger than the truth: already for `i = 0` and `ξ = 0` the class
`ξ'` is an arbitrary morphism `𝓔 ⟶ 𝓕` restricted to `ker α`, and nothing makes it vanish deep in
the filtration. What does hold is step 5 above — `ξ'` agrees there with a class *extending to the
middle term* — and the boundary of such a class vanishes. So the step proved here replaces the
vanishing hypothesis of that lemma by the comparison with `ζ`, which is
`mk₀_submoduleι_comp_extClass_comp_eq_zero_of_eq`.

## Main results

* `Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp_eq_zero_of_eq`: along a morphism of short exact
  sequences, the boundary class `hS₂.extClass ∘ ξ'` is killed by `φ.τ₃` as soon as `φ.τ₁ ∘ ξ'`
  comes from the middle term of `S₁`.
* `Stacks.ExtEffacement.mapExactFunctor_sub_eq_zero`: **the difference of the two pullbacks
  restricts to zero**, for an arbitrary exact functor between abelian categories.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.isCoherent_idealPowerMultiple_inf_ker`:
  **`𝓘^k 𝓔 ⊓ ker α` is coherent**, which is what lets the induction hypothesis be applied to it.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_submoduleι_comp_extClass_comp_eq_zero_of_eq`:
  **the inductive step, with the vanishing hypothesis of
  `Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_submoduleι_comp_extClass_comp_eq_zero` replaced
  by a comparison with a class on `𝓘^n 𝓔`.**
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleι_comp_eq_zero_of_isCoherent`:
  **the injectivity half of the core case of [Stacks, Tag 0G2H] in every degree**, and its
  variant `exists_mk₀_idealPowSmulMap_comp_eq_zero_of_isCoherent` in the same namespace:
  the same statement for a class on `𝓘^n 𝓖`.

## Implementation notes

Every `Ext`-computation is carried out *abstractly*, for an arbitrary abelian category or an
arbitrary exact functor between two, and applied with a single `exact`. This is not cosmetic:
`AlgebraicGeometry.Scheme.Modules` is a `def` carrying a second copy of the categorical
structure, so over it a `rw` prints its pattern as not found while printing it identically to the
goal subterm, as
`StacksFrontier/AlgebraicGeometry/Duality/ExtensionZeroCoherent/CoherentExtRestrictImageSequence.lean`
records.

For the same reason no step relies on the definitional unfolding of
`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE` at a *concrete* submodule: the
members of the ideal-power filtration are `sInf`s, and the kernel exceeds its heartbeat budget
unfolding them. Each composite of inclusions is therefore supplied as an explicit equation,
proved once with the submodules kept as variables
(`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE_comp₃`,
`Stacks.AlgebraicGeometry.IdealPowerColimit.kerIdealPowerEpiLift_comp_submoduleHomOfLE`, whose
`P` is a variable), and instantiated.

`Mono (submoduleι (𝓘^n M))` is not found by instance search —
`AlgebraicGeometry.Scheme.ringCatSheaf` has a type that is only definitionally the one
`SheafOfModules.Submodule` expects, so the metavariable cannot be assigned — and is passed
explicitly in `Stacks.AlgebraicGeometry.IdealPowerColimit.isCoherent_idealPowSmul`.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA) (Artin-Rees)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe w w' v v' u u'

namespace Stacks.ExtEffacement

section Abstract

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **A boundary class is killed by `φ.τ₃` as soon as the class it comes from, pulled back along
`φ.τ₁`, extends to the middle term of `S₁`.** Let `φ : S₁ ⟶ S₂` be a morphism of short exact
sequences and let `ξ'` be a class of degree `i` on `S₂.X₁`. If `φ.τ₁ ∘ ξ'` is `S₁.f ∘ z` for a
class `z` on `S₁.X₂`, then `φ.τ₃` kills the boundary class `hS₂.extClass ∘ ξ'`.

This is `Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp`, the naturality of the class of a short
exact sequence, followed by `CategoryTheory.ShortComplex.ShortExact.extClass_comp_assoc`: two
consecutive maps of the contravariant long exact sequence of `S₁` compose to zero. It is the
diagram chase of the injectivity half of the core case of [Stacks, Tag 0G2H], isolated from the
geometry; the special case `z = 0` is
`Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp_eq_zero`. -/
theorem mk₀_τ₃_comp_extClass_comp_eq_zero_of_eq {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) {T : C} {i : ℕ} (ξ' : Ext.{w} S₂.X₁ T i)
    (z : Ext.{w} S₁.X₂ T i)
    (hz : (Ext.mk₀ φ.τ₁).comp ξ' (zero_add i) = (Ext.mk₀ S₁.f).comp z (zero_add i)) :
    (Ext.mk₀ φ.τ₃).comp (h₂.extClass.comp ξ' (Nat.add_comm 1 i)) (zero_add (i + 1)) = 0 := by
  rw [mk₀_τ₃_comp_extClass_comp h₁ h₂ φ (Nat.add_comm 1 i) ξ', hz]
  exact h₁.extClass_comp_assoc z

/-- Precomposition by a degree-zero class is additive in the second argument. -/
theorem mk₀_comp_sub {A B T : C} (a : A ⟶ B) {i : ℕ} (θ η : Ext.{w} B T i) :
    (Ext.mk₀ a).comp (θ - η) (zero_add i) =
      (Ext.mk₀ a).comp θ (zero_add i) - (Ext.mk₀ a).comp η (zero_add i) := by
  rw [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg, ← sub_eq_add_neg]

/-- **Two classes whose pullbacks differ by a class killed by `c` have equal pullbacks along
`c`.** Stated with the two composites `c ≫ g₁` and `c ≫ g₂` given as separate morphisms `d₁`,
`d₂`, so that each composite can be identified with a single inclusion of submodules by an
explicit equation rather than by defeq. -/
theorem mk₀_comp_eq_of_sub_eq_zero {V W K P T : C} (c : V ⟶ W) (g₁ : W ⟶ K) (g₂ : W ⟶ P)
    (d₁ : V ⟶ K) (d₂ : V ⟶ P) (hd₁ : c ≫ g₁ = d₁) (hd₂ : c ≫ g₂ = d₂) {i : ℕ}
    (ξ' : Ext.{w} K T i) (ζ : Ext.{w} P T i)
    (h : (Ext.mk₀ c).comp ((Ext.mk₀ g₁).comp ξ' (zero_add i) -
      (Ext.mk₀ g₂).comp ζ (zero_add i)) (zero_add i) = 0) :
    (Ext.mk₀ d₁).comp ξ' (zero_add i) = (Ext.mk₀ d₂).comp ζ (zero_add i) := by
  subst hd₁
  subst hd₂
  rw [mk₀_comp_sub, sub_eq_zero, mk₀_comp_mk₀_comp, mk₀_comp_mk₀_comp] at h
  exact h

/-- **An equality of pullbacks, pulled further back along `l`, exhibits the left side as coming
from `Q`** as soon as `l ≫ g₂` factors as `f ≫ r`. This is the shape the chase needs: `g₁` and
`g₂` are the two inclusions of `𝓘^n 𝓔 ⊓ ker α`, `l` is the inclusion of `ker(𝓘^n 𝓔 ⟶ 𝓘^n 𝓐)`
into it, and `f` is the inclusion of that kernel into `𝓘^n 𝓔`. -/
theorem mk₀_comp_eq_mk₀_comp_of_eq {V₀ V K P Q T : C} (l : V₀ ⟶ V) (g₁ : V ⟶ K) (g₂ : V ⟶ P)
    (f : V₀ ⟶ Q) (r : Q ⟶ P) {i : ℕ} (ξ' : Ext.{w} K T i) (ζ : Ext.{w} P T i)
    (hfac : l ≫ g₂ = f ≫ r)
    (h : (Ext.mk₀ g₁).comp ξ' (zero_add i) = (Ext.mk₀ g₂).comp ζ (zero_add i)) :
    (Ext.mk₀ (l ≫ g₁)).comp ξ' (zero_add i) =
      (Ext.mk₀ f).comp ((Ext.mk₀ r).comp ζ (zero_add i)) (zero_add i) := by
  rw [← mk₀_comp_mk₀_comp, h, mk₀_comp_mk₀_comp, mk₀_comp_mk₀_comp, hfac]

end Abstract

section AbstractRestrict

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]

/-- **The difference of the two pullbacks restricts to zero.** Let `R` be an exact functor, let
`θ` be a class on `R(E)`, and let `ξ'` on `K` and `ζ` on `P` both have `R`-images the pullback of
`θ` along `R(k)` and `R(c)` respectively. If `g₁ ≫ k = g₂ ≫ c`, then the difference of the
pullbacks of `ξ'` along `g₁` and of `ζ` along `g₂` has vanishing `R`-image.

In the chase `R` is restriction to `U`, `K = ker α`, `P = 𝓘^k 𝓔`, and the common target `W` of
`g₁`, `g₂` is the intersection `𝓘^k 𝓔 ⊓ ker α`, both of whose inclusions into `𝓔` are the
inclusion of that intersection. -/
theorem mapExactFunctor_sub_eq_zero (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {W K P E T : C} (g₁ : W ⟶ K) (k : K ⟶ E) (g₂ : W ⟶ P)
    (c : P ⟶ E) (hcomm : g₁ ≫ k = g₂ ≫ c) {i : ℕ} (θ : Ext.{w'} (R.obj E) (R.obj T) i)
    (ξ' : Ext.{w} K T i) (ζ : Ext.{w} P T i)
    (hξ' : Ext.mapExactFunctor R ξ' = (Ext.mk₀ (R.map k)).comp θ (zero_add i))
    (hζ : Ext.mapExactFunctor R ζ = (Ext.mk₀ (R.map c)).comp θ (zero_add i)) :
    Ext.mapExactFunctor R ((Ext.mk₀ g₁).comp ξ' (zero_add i) -
      (Ext.mk₀ g₂).comp ζ (zero_add i)) = 0 := by
  have hsub : Ext.mapExactFunctor R ((Ext.mk₀ g₁).comp ξ' (zero_add i) -
        (Ext.mk₀ g₂).comp ζ (zero_add i)) =
      Ext.mapExactFunctor R ((Ext.mk₀ g₁).comp ξ' (zero_add i)) -
        Ext.mapExactFunctor R ((Ext.mk₀ g₂).comp ζ (zero_add i)) :=
    map_sub (R.mapExtAddHom W T i) _ _
  rw [hsub, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, hξ', Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, hζ, mk₀_comp_mk₀_comp (R.map g₁) (R.map k) θ,
    mk₀_comp_mk₀_comp (R.map g₂) (R.map c) θ, ← R.map_comp, ← R.map_comp, hcomm, sub_self]

end AbstractRestrict

end Stacks.ExtEffacement

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### The intersection `𝓘^k 𝓔 ⊓ ker α` -/

/-- **Mathlib's kernel subsheaf and `Stacks.Algebraization.kernelSubmodule` are the same
submodule.** Both have as sections over an open the sections annihilated by the morphism; the
first is defined as such, the second as the preimage of `⊥`. The identification is what carries
the quasi-coherence of an intersection with a kernel, which is proved for the second spelling,
over to the first, in which `Stacks.AlgebraicGeometry.IdealPowerColimit.kerMod` is stated. -/
theorem ker_eq_kernelSubmodule {M N : X.Modules} (f : M ⟶ N) :
    SheafOfModules.Submodule.ker f = Stacks.Algebraization.kernelSubmodule f := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun W => ?_)
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj]
  rfl

/-- **`𝓘^k 𝓔 ⊓ ker α` is quasi-coherent.** This is
`AlgebraicGeometry.isQuasicoherent_inf_kernelSubmodule` — the intersection of a quasi-coherent
submodule with the sectionwise kernel of a morphism to a quasi-coherent module is the image of a
kernel — read through `Stacks.AlgebraicGeometry.IdealPowerColimit.ker_eq_kernelSubmodule`. -/
theorem isQuasicoherent_idealPowerMultiple_inf_ker {E A : X.Modules} [E.IsQuasicoherent]
    [A.IsQuasicoherent] (I : X.IdealSheafData) (k : ℕ) (α : E ⟶ A) :
    (subMod (Stacks.Algebraization.idealPowerMultiple I k E ⊓
      SheafOfModules.Submodule.ker α)).IsQuasicoherent := by
  rw [ker_eq_kernelSubmodule]
  exact _root_.AlgebraicGeometry.isQuasicoherent_inf_kernelSubmodule _ inferInstance α

/-- **`𝓘^k 𝓔 ⊓ ker α` is coherent** when `𝓔` and `𝓐` are, on a locally Noetherian scheme: it is a
quasi-coherent submodule of the coherent module `𝓔`. This is what lets the degree-`i` injectivity
statement be applied to it, which is the one place the induction step needs the intersection to
be a coherent module in its own right. -/
@[ega "0 5.3.4" "kernel clause"]
theorem isCoherent_idealPowerMultiple_inf_ker [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    {E A : X.Modules} [E.IsCoherent] [A.IsCoherent] (I : X.IdealSheafData) (k : ℕ) (α : E ⟶ A) :
    (subMod (Stacks.Algebraization.idealPowerMultiple I k E ⊓
      SheafOfModules.Submodule.ker α)).IsCoherent :=
  have : E.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent E
  have : A.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent A
  have := isQuasicoherent_idealPowerMultiple_inf_ker I k α
  Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent
    (submoduleι (Stacks.Algebraization.idealPowerMultiple I k E ⊓
      SheafOfModules.Submodule.ker α))

/-- **`𝓘^n 𝓜` is coherent** when `𝓜` is, on a locally Noetherian scheme: it is a quasi-coherent
submodule of `𝓜`. The monomorphism is supplied explicitly, since instance search does not find
`Mono (submoduleι (𝓘^n 𝓜))`; see the implementation notes. -/
theorem isCoherent_idealPowSmul [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) [M.IsCoherent] :
    (idealPowSmul I n M).IsCoherent :=
  have : M.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent M
  @Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent X _ M
    (idealPowSmul I n M) _ _ (submoduleι (Stacks.Algebraization.idealPowerMultiple I n M))
    (mono_submoduleι _)

/-- Three inclusions of submodules compose to the inclusion. Stated with the submodules as
variables, so that the kernel never unfolds
`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE` at a concrete member of the
ideal-power filtration. -/
theorem submoduleHomOfLE_comp₃ {M : X.Modules} {N₁ N₂ N₃ N₄ : M.Submodule} (h₁ : N₁ ≤ N₂)
    (h₂ : N₂ ≤ N₃) (h₃ : N₃ ≤ N₄) (h : N₁ ≤ N₄) :
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE h₁ ≫
        Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE h₂) ≫
      Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE h₃ =
      Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE h := rfl

/-- **The inclusion of `ker(𝓘^n 𝓔 ⟶ 𝓘^n 𝓐)` into `𝓘^n 𝓔 ⊓ ker α`, followed by the inclusion of
that intersection into a submodule `P` containing `𝓘^n 𝓔`, is the inclusion of that kernel into
`𝓘^n 𝓔` followed by the inclusion of `𝓘^n 𝓔` into `P`.** Both composites are the inclusion of
the kernel into `𝓔` corestricted to `P`, so this is
`Stacks.AlgebraicGeometry.IdealPowerColimit.kerIdealPowerEpiLift_comp` after cancelling the
monomorphism `P ⟶ 𝓔`.

It is the factorisation that makes the pullback of `ξ'` to that kernel come from `𝓘^n 𝓔`. `P` is
kept a variable: at `P = 𝓘^k 𝓔` the statement is instantiated, and the kernel then has no
concrete submodule to unfold. -/
theorem kerIdealPowerEpiLift_comp_submoduleHomOfLE (I : X.IdealSheafData) (n : ℕ)
    {E A : X.Modules} (hE : E.IsQuasicoherent) (hA : A.IsQuasicoherent) (α : E ⟶ A) (hα : Epi α)
    {P : E.Submodule} (hP : Stacks.Algebraization.idealPowerMultiple I n E ≤ P) :
    kerIdealPowerEpiLift I n hE hA α hα ≫
        Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
          (inf_le_left.trans hP) =
      kerInclusion (idealPowerEpi I n hE hA α hα) ≫
        Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hP :=
  (cancel_mono (submoduleι P)).mp
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t : subMod (Stacks.Algebraization.idealPowerMultiple I n E ⊓
              SheafOfModules.Submodule.ker α) ⟶ E =>
            kerIdealPowerEpiLift I n hE hA α hα ≫ t)
          (submoduleHomOfLE_ι (inf_le_left.trans hP))).trans
        ((kerIdealPowerEpiLift_comp I n hE hA α hα).trans
          ((congrArg (fun t : subMod (Stacks.Algebraization.idealPowerMultiple I n E) ⟶ E =>
                kerInclusion (idealPowerEpi I n hE hA α hα) ≫ t)
              (submoduleHomOfLE_ι hP)).symm.trans
            (Category.assoc _ _ _).symm))))

/-- **The inductive step of the injectivity chase of [Stacks, Tag 0G2H].** Let `α : 𝓔 ⟶ 𝓐` be an
epimorphism of quasi-coherent modules with short exact sequence
`S : 0 ⟶ ker α ⟶ 𝓔 ⟶ 𝓐 ⟶ 0`, let `ξ'` be a class of degree `i` on `ker α` and let `P` be a
submodule of `𝓔` containing `𝓘^n 𝓔`. If the pullback of `ξ'` to `𝓘^n 𝓔 ⊓ ker α` agrees with the
pullback of a class `ζ` on `P`, then the boundary class `hS.extClass ∘ ξ'` dies under the
inclusion of `𝓘^n 𝓐`.

This is
`Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_submoduleι_comp_extClass_comp_eq_zero` with its
vanishing hypothesis weakened to a comparison, which is what the restriction to `U` actually
provides — see the module documentation. The proof is the morphism
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerShortComplexHom` of short exact sequences
together with `Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp_eq_zero_of_eq`: the hypothesis
says that the first component of that morphism carries `ξ'` to a class coming from the middle
term `𝓘^n 𝓔`, and the boundary of such a class vanishes. -/
theorem mk₀_submoduleι_comp_extClass_comp_eq_zero_of_eq [HasExt.{w} X.Modules]
    (I : X.IdealSheafData) (n : ℕ) {E A : X.Modules} (hE : E.IsQuasicoherent)
    (hA : A.IsQuasicoherent) (α : E ⟶ A) (hα : Epi α) {G : X.Modules}
    (hS : (ShortComplex.mk (kerInclusion α) α (kerInclusion_comp α)).ShortExact) {i : ℕ}
    (ξ' : Ext.{w} (kerMod α) G i) {P : E.Submodule}
    (hP : Stacks.Algebraization.idealPowerMultiple I n E ≤ P) (ζ : Ext.{w} (subMod P) G i)
    (h : (Ext.mk₀ (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
          (inf_le_right : Stacks.Algebraization.idealPowerMultiple I n E ⊓
            SheafOfModules.Submodule.ker α ≤ SheafOfModules.Submodule.ker α))).comp ξ'
        (zero_add i) =
      (Ext.mk₀ (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
        (inf_le_left.trans hP))).comp ζ (zero_add i)) :
    (Ext.mk₀ (submoduleι (Stacks.Algebraization.idealPowerMultiple I n A))).comp
      (hS.extClass.comp ξ' (Nat.add_comm 1 i)) (zero_add (i + 1)) = 0 :=
  Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp_eq_zero_of_eq
    (shortExact_idealPowerEpi I n hE hA α hα) hS (idealPowerShortComplexHom I n hE hA α hα) ξ'
    ((Ext.mk₀ (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hP)).comp ζ
      (zero_add i))
    (Stacks.ExtEffacement.mk₀_comp_eq_mk₀_comp_of_eq
      (kerIdealPowerEpiLift I n hE hA α hα)
      (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
        (inf_le_right : Stacks.Algebraization.idealPowerMultiple I n E ⊓
          SheafOfModules.Submodule.ker α ≤ SheafOfModules.Submodule.ker α))
      (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE (inf_le_left.trans hP))
      (kerInclusion (idealPowerEpi I n hE hA α hα))
      (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hP) ξ' ζ
      (kerIdealPowerEpiLift_comp_submoduleHomOfLE I n hE hA α hα hP) h)

/-! ### The induction -/

/-- **The injectivity half of the core case of [Stacks, Tag 0G2H] in degree `0`**, for an
arbitrary coherent module `𝓐`: a morphism `𝓐 ⟶ 𝓕` vanishing on `U` dies under the inclusion of
some `𝓘^n 𝓐`.

This is the first display of [Stacks, Tag 01YB], in the form
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_comp_eq_zero_of_restrictFunctor_map_eq_zero`,
applied at stage `0` of the filtration of `𝓐`: the composite of the inclusion of `𝓘^0 𝓐` with
the morphism also vanishes on `U`, and the inclusion of `𝓘^{0+N} 𝓐` factors through it. It is
the base case of the induction on the degree. -/
theorem exists_mk₀_submoduleι_comp_eq_zero_of_degreeZero
    [_root_.AlgebraicGeometry.IsNoetherian X] [HasExt.{w} X.Modules] (I : X.IdealSheafData)
    (U : X.Opens) (hU : U = I.support.compl) [HasExt.{w'} U.toScheme.Modules] (F : X.Modules)
    [F.IsQuasicoherent] (A : X.Modules) [A.IsCoherent] (ξ : Ext.{w} A F 0)
    (hξ : extRestrict.{w, w'} U ξ = 0) :
    ∃ n : ℕ, (Ext.mk₀ (submoduleι
      (Stacks.Algebraization.idealPowerMultiple I n A))).comp ξ (zero_add 0) = 0 := by
  obtain ⟨ψ, rfl⟩ := (Ext.mk₀_bijective _ _).2 ξ
  rw [extRestrict_mk₀, ← Ext.mk₀_zero] at hξ
  have h1 : (Scheme.Modules.restrictFunctor U.ι).map ψ = 0 := (Ext.mk₀_bijective _ _).1 hξ
  have h2 : (Scheme.Modules.restrictFunctor U.ι).map
      (submoduleι (Stacks.Algebraization.idealPowerMultiple I 0 A) ≫ ψ) = 0 := by
    rw [Functor.map_comp, h1, Limits.comp_zero]
  obtain ⟨N, hN⟩ := exists_comp_eq_zero_of_restrictFunctor_map_eq_zero I U hU
    (G := A) (n := 0) (ψ := submoduleι (Stacks.Algebraization.idealPowerMultiple I 0 A) ≫ ψ) h2
  refine ⟨0 + N, ?_⟩
  rw [Ext.mk₀_comp_mk₀, show submoduleι (Stacks.Algebraization.idealPowerMultiple I (0 + N) A) ≫
      ψ = idealPowSmulMap I A (Nat.le_add_right 0 N) ≫
        (submoduleι (Stacks.Algebraization.idealPowerMultiple I 0 A) ≫ ψ) from
    ((congrArg (fun t : idealPowSmul I (0 + N) A ⟶ A => t ≫ ψ)
      (idealPowerMultipleMap_comp_ι I A (Nat.le_add_right 0 N)).symm).trans
      (Category.assoc _ _ _)), hN]
  exact Ext.mk₀_zero _ _

/-- **The induction step of the injectivity half of the core case of [Stacks, Tag 0G2H].** Let
`X` be a Noetherian scheme, `𝓘` a quasi-coherent sheaf of ideals, `U = X ∖ V(𝓘)` and `𝓕` a
coherent `𝒪_X`-module. If every class of degree `i` on a coherent module, vanishing on `U`, dies
on a member of the ideal-power filtration of that module, then the same holds in degree `i + 1`.

The proof is the chase of the module documentation: the dimension shift, the contravariant long
exact sequence on `U`, the surjectivity half in degree `i`, the induction hypothesis applied to
the coherent intersection `𝓘^k 𝓔 ⊓ ker α`, Artin-Rees, and
`Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_submoduleι_comp_extClass_comp_eq_zero_of_eq`. -/
theorem exists_mk₀_submoduleι_comp_eq_zero_of_succ [_root_.AlgebraicGeometry.IsNoetherian X]
    [HasExt.{w} X.Modules] (I : X.IdealSheafData) (U : X.Opens) (hU : U = I.support.compl)
    [HasExt.{w'} U.toScheme.Modules] (F : X.Modules) [F.IsCoherent] {i : ℕ}
    (ih : ∀ B : X.Modules, B.IsCoherent → ∀ η : Ext.{w} B F i,
      extRestrict.{w, w'} U η = 0 →
        ∃ n : ℕ, (Ext.mk₀ (submoduleι
          (Stacks.Algebraization.idealPowerMultiple I n B))).comp η (zero_add i) = 0)
    (A : X.Modules) (hA : A.IsCoherent) (ξ : Ext.{w} A F (i + 1))
    (hξ : extRestrict.{w, w'} U ξ = 0) :
    ∃ n : ℕ, (Ext.mk₀ (submoduleι
      (Stacks.Algebraization.idealPowerMultiple I n A))).comp ξ (zero_add (i + 1)) = 0 := by
  have := hA
  obtain ⟨E, α, hE, hα, hker, hS, ξ', hξ'⟩ :=
    Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_of_pos.{w} ξ
  have := hE
  have := hα
  have := hker
  have hEq : E.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent E
  have hAq : A.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent A
  have h0 : ((hS.map_of_exact (Scheme.Modules.restrictFunctor U.ι)).extClass).comp
      (extRestrict.{w, w'} U ξ') (Nat.add_comm 1 i) = 0 := by
    rw [← extRestrict_extClass U hS, ← extRestrict_comp, hξ', hξ]
  obtain ⟨θ, hθ⟩ := Ext.contravariant_sequence_exact₁
    (hS.map_of_exact (Scheme.Modules.restrictFunctor U.ι))
    ((Scheme.Modules.restrictFunctor U.ι).obj F) (extRestrict.{w, w'} U ξ')
    (Nat.add_comm 1 i) h0
  obtain ⟨k, ζ, hζ⟩ :=
    Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_isCoherent.{w, w'} I U hU F i E hE θ
  have hζ' : extRestrict.{w, w'} U ζ =
      (Ext.mk₀ ((Scheme.Modules.restrictFunctor U.ι).map
        (submoduleι (Stacks.Algebraization.idealPowerMultiple I k E)))).comp θ (zero_add i) :=
    Stacks.ExtEffacement.eq_mk₀_hom_comp
      (restrictIdealPowSmulIso I U (disjoint_support_of_eq_supportCompl hU) k E)
      (extRestrict.{w, w'} U ζ) θ hζ
  have hcomm : Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
        (inf_le_right : Stacks.Algebraization.idealPowerMultiple I k E ⊓
          SheafOfModules.Submodule.ker α ≤ SheafOfModules.Submodule.ker α) ≫ kerInclusion α =
      Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
        (inf_le_left : Stacks.Algebraization.idealPowerMultiple I k E ⊓
          SheafOfModules.Submodule.ker α ≤
            Stacks.Algebraization.idealPowerMultiple I k E) ≫
        submoduleι (Stacks.Algebraization.idealPowerMultiple I k E) := rfl
  have hdiff := Stacks.ExtEffacement.mapExactFunctor_sub_eq_zero
    (Scheme.Modules.restrictFunctor U.ι)
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
      (inf_le_right : Stacks.Algebraization.idealPowerMultiple I k E ⊓
        SheafOfModules.Submodule.ker α ≤ SheafOfModules.Submodule.ker α))
    (kerInclusion α)
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
      (inf_le_left : Stacks.Algebraization.idealPowerMultiple I k E ⊓
        SheafOfModules.Submodule.ker α ≤ Stacks.Algebraization.idealPowerMultiple I k E))
    (submoduleι (Stacks.Algebraization.idealPowerMultiple I k E)) hcomm θ ξ' ζ hθ.symm hζ'
  have hWq : (subMod (Stacks.Algebraization.idealPowerMultiple I k E ⊓
      SheafOfModules.Submodule.ker α)).IsQuasicoherent :=
    isQuasicoherent_idealPowerMultiple_inf_ker I k α
  obtain ⟨m, hm⟩ := ih _ (isCoherent_idealPowerMultiple_inf_ker I k α) _ hdiff
  obtain ⟨n, -, hn⟩ := exists_mk₀_submoduleHomOfLE_inf_comp_eq_zero.{w} I
    (Stacks.Algebraization.idealPowerMultiple I k E ⊓ SheafOfModules.Submodule.ker α) hE hWq _ hm
  have hNk : Stacks.Algebraization.idealPowerMultiple I (max n k) E ≤
      Stacks.Algebraization.idealPowerMultiple I k E :=
    Stacks.Algebraization.idealPowerMultiple_antitone I E (le_max_right n k)
  have hle3 : Stacks.Algebraization.idealPowerMultiple I (max n k) E ⊓
        SheafOfModules.Submodule.ker α ≤
      Stacks.Algebraization.idealPowerMultiple I n E ⊓
        (Stacks.Algebraization.idealPowerMultiple I k E ⊓ SheafOfModules.Submodule.ker α) :=
    le_inf (inf_le_left.trans
        (Stacks.Algebraization.idealPowerMultiple_antitone I E (le_max_left n k)))
      (le_inf (inf_le_left.trans hNk) inf_le_right)
  have hvan := Stacks.Cohomology.ColimitsOfCohomology.ext_comp_eq_zero_of_comp
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hle3)
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE inf_le_right) _ hn
  have hkey := Stacks.ExtEffacement.mk₀_comp_eq_of_sub_eq_zero
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hle3 ≫
      Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE inf_le_right)
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
      (inf_le_right : Stacks.Algebraization.idealPowerMultiple I k E ⊓
        SheafOfModules.Submodule.ker α ≤ SheafOfModules.Submodule.ker α))
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
      (inf_le_left : Stacks.Algebraization.idealPowerMultiple I k E ⊓
        SheafOfModules.Submodule.ker α ≤ Stacks.Algebraization.idealPowerMultiple I k E))
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
      (inf_le_right : Stacks.Algebraization.idealPowerMultiple I (max n k) E ⊓
        SheafOfModules.Submodule.ker α ≤ SheafOfModules.Submodule.ker α))
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
      (inf_le_left.trans hNk))
    (submoduleHomOfLE_comp₃ hle3 inf_le_right inf_le_right _)
    (submoduleHomOfLE_comp₃ hle3 inf_le_right inf_le_left _) ξ' ζ hvan
  exact ⟨max n k, hξ' ▸ mk₀_submoduleι_comp_extClass_comp_eq_zero_of_eq I (max n k) hEq hAq α hα
    hS ξ' hNk ζ hkey⟩

/-- **The injectivity half of the core case of [Stacks, Tag 0G2H] in every degree**: for coherent
`𝓐` and `𝓕` on a Noetherian scheme and `U = X ∖ V(𝓘)`, a class in `Ext^i_X(𝓐, 𝓕)` whose
restriction to `U` vanishes dies under the inclusion of some member `𝓘^n 𝓐` of the ideal-power
filtration of `𝓐`.

The base case is the first display of [Stacks, Tag 01YB],
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleι_comp_eq_zero_of_degreeZero`,
and the induction step is
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleι_comp_eq_zero_of_succ`. Note
that the statement runs over *all* coherent `𝓐` at once: the induction step applies it to
`𝓘^k 𝓔 ⊓ ker α`, not to a member of the filtration of `𝓐`. -/
theorem exists_mk₀_submoduleι_comp_eq_zero_of_isCoherent
    [_root_.AlgebraicGeometry.IsNoetherian X] [HasExt.{w} X.Modules] (I : X.IdealSheafData)
    (U : X.Opens) (hU : U = I.support.compl) [HasExt.{w'} U.toScheme.Modules] (F : X.Modules)
    [F.IsCoherent] (i : ℕ) :
    ∀ A : X.Modules, A.IsCoherent → ∀ ξ : Ext.{w} A F i, extRestrict.{w, w'} U ξ = 0 →
      ∃ n : ℕ, (Ext.mk₀ (submoduleι
        (Stacks.Algebraization.idealPowerMultiple I n A))).comp ξ (zero_add i) = 0 := by
  induction i with
  | zero =>
      intro A hA ξ hξ
      have := hA
      have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
      exact exists_mk₀_submoduleι_comp_eq_zero_of_degreeZero I U hU F A ξ hξ
  | succ i ih =>
      intro A hA ξ hξ
      exact exists_mk₀_submoduleι_comp_eq_zero_of_succ I U hU F ih A hA ξ hξ

/-- **The injectivity half of the core case of [Stacks, Tag 0G2H] on a member of the
ideal-power filtration**: a class in `Ext^i_X(𝓘^n 𝓖, 𝓕)` whose image under
`Stacks.AlgebraicGeometry.IdealPowerColimit.extIdealPowRestrict` vanishes dies on `𝓘^{n+N} 𝓖`
for some `N`.

This is
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleι_comp_eq_zero_of_isCoherent`
for the coherent module `𝓘^n 𝓖`, with the conclusion converted back to the filtration of `𝓖` by
`Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_idealPowSmulMap_comp_eq_zero`. -/
theorem exists_mk₀_idealPowSmulMap_comp_eq_zero_of_isCoherent
    [_root_.AlgebraicGeometry.IsNoetherian X] [HasExt.{w} X.Modules] (I : X.IdealSheafData)
    (U : X.Opens) (hU : U = I.support.compl) [HasExt.{w'} U.toScheme.Modules] {G F : X.Modules}
    [G.IsCoherent] [F.IsCoherent] {i n : ℕ} (ζ : Ext.{w} (idealPowSmul I n G) F i)
    (hζ : extIdealPowRestrict.{w, w'} I U (disjoint_support_of_eq_supportCompl hU) ζ = 0) :
    ∃ N : ℕ, (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n N))).comp ζ (zero_add i) = 0 := by
  have : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  have : (idealPowSmul I n G).IsCoherent := isCoherent_idealPowSmul I n G
  have hres : extRestrict.{w, w'} U ζ = 0 :=
    (Stacks.ExtEffacement.eq_mk₀_hom_comp
      (restrictIdealPowSmulIso I U (disjoint_support_of_eq_supportCompl hU) n G)
      (extRestrict.{w, w'} U ζ) 0 hζ).trans (by simp)
  obtain ⟨N, hN⟩ := exists_mk₀_submoduleι_comp_eq_zero_of_isCoherent I U hU F i
    (idealPowSmul I n G) inferInstance ζ hres
  exact ⟨N, mk₀_idealPowSmulMap_comp_eq_zero I n N G ζ hN⟩

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
