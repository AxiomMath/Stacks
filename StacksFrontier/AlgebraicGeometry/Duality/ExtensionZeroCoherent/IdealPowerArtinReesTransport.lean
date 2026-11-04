module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerIterate
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyVanishing

/-!
# The Artin-Rees comparison of `(𝓘^n 𝓕')` with `(𝓕' ∩ 𝓘^n 𝓕'')`, on `Ext`-groups

Let `X` be a Noetherian scheme, `𝓘` a quasi-coherent sheaf of ideals, `𝓕''` a coherent
`𝒪_X`-module and `𝓕'` a quasi-coherent submodule of `𝓕''`. Two descending families of
submodules of `𝓕''` interleave:

`𝓘^n 𝓕' ⊆ 𝓕' ∩ 𝓘^n 𝓕'' ⊆ 𝓘^{n - c} 𝓕'`,

the first inclusion for every `n` and the second, for one constant `c`, for every `n ≥ c`. The
second inclusion is Artin-Rees, `AlgebraicGeometry.exists_idealPowerSub_artinRees`
([Stacks, Tag 01YA]); the first is the affine-local computation
`AlgebraicGeometry.idealPowerSub_le_inf` below. Together they say that the two families are
*pro-isomorphic*: an assertion that something dies on some member of one family is equivalent to
the same assertion for the other family.

This file transports that comparison onto the `Ext`-groups of the core case of
[Stacks, Tag 0G2H], in the shape in which the vanishing assertions of that core case — the
hypothesis `hinj` of `AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem` — are
stated: the vanishing of `CategoryTheory.Abelian.Ext.mk₀` of an inclusion, composed with a class.

It is what the injectivity half of the induction on `i` in the proof of that core case needs. That
induction takes a class `ξ` in `Ext^{i+1}_X(𝓐, 𝓖)` vanishing on `U`, writes it as
`hS.extClass ∘ ξ'` for a short exact sequence `S : 0 ⟶ 𝓕' ⟶ 𝓕'' ⟶ 𝓐 ⟶ 0` of coherent modules
(`Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_of_pos`, whose `𝓕'` is deliberately the
*subsheaf* `Stacks.AlgebraicGeometry.IdealPowerColimit.kerMod` of `𝓕''` rather than the
categorical kernel, precisely so that the intersection `𝓕' ∩ 𝓘^n 𝓕''` is available), and must
convert a vanishing statement about `ξ'` on the ideal-power filtration `(𝓘^m 𝓕')` of `𝓕'` — which
is what the inductive hypothesis in degree `i`, applied to the coherent module `𝓕'`, produces —
into one on `(𝓕' ∩ 𝓘^n 𝓕'')`, which is the first term of the pullback of `S` along the inclusion
`𝓘^n 𝓐 ⟶ 𝓐`. That conversion is
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleHomOfLE_inf_comp_eq_zero`.

## The two spellings of `𝓘^m 𝓕'`

`𝓘^m 𝓕'` occurs here in two guises, and the arithmetic of the two families takes place in the
second:

* as a submodule of `𝓕'`, namely `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple 𝓘 m 𝓕'`,
  which is the guise the `Ext`-statements of the core case are phrased in — their inclusions are
  `Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι` of it;
* as a submodule of `𝓕''`, namely `AlgebraicGeometry.idealPowerSub 𝓘 m 𝓕'`, which is the guise in
  which it is comparable with `𝓕' ∩ 𝓘^n 𝓕''`.

`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerSubIso` identifies the two, and
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerSubIso_hom_comp` says that it does so
compatibly with the inclusions into `𝓕'`; that is all the consumers below use of it. The
identification is the general fact that a monomorphism is isomorphic to the inclusion of its
sectionwise image (`AlgebraicGeometry.imageSubmoduleIso`), applied to the composite
`𝓘^m 𝓕' ⟶ 𝓕' ⟶ 𝓕''`, whose sectionwise image is `AlgebraicGeometry.idealPowerSub 𝓘 m 𝓕'` by
definition.

## Main results

* `AlgebraicGeometry.idealPowerSub_le_inf`: **`𝓘^n 𝓕' ⊆ 𝓕' ∩ 𝓘^n 𝓕''`**, the elementary half of
  the pro-isomorphism.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_submoduleι_idealPowerMultiple_comp_eq_zero`: a
  class on `𝓕'` killed by the inclusion of `𝓕' ∩ 𝓘^n 𝓕''` is killed by the inclusion of
  `𝓘^n 𝓕'`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleHomOfLE_inf_comp_eq_zero`:
  **the Artin-Rees direction** — a class on `𝓕'` killed by the inclusion of `𝓘^m 𝓕'` is killed by
  the inclusion of `𝓕' ∩ 𝓘^n 𝓕''` for some `n ≥ m`.

## Implementation notes

Two spellings of the category of `𝒪_X`-modules meet here, and the `Ext`-groups below are
sensitive to the difference: `AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules`
carrying its own `Category` instance, so a morphism whose type is written
`N.toSheafOfModules ⟶ L` is elaborated in `SheafOfModules`, where the `CategoryTheory.HasExt`
instance in scope is not the one assumed here and the resulting `Ext`-groups live in another
universe. Every inclusion below is therefore spelled with
`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι` and
`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE`, whose declared types are at
`AlgebraicGeometry.Scheme.Modules`; `AlgebraicGeometry.subι` and `AlgebraicGeometry.subHom` are
the same morphisms at the other spelling.
`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE_comp` is
`SheafOfModules.Submodule.homOfLE_comp` re-elaborated at this spelling, as
`StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/SubmoduleKernel.lean` records is necessary for
such facts.

`rw` and `simp` do not see through that `def` at the transparency they use: a goal about a
composite of inclusions of submodules is reported as not type-correct under `implicit`
transparency. As in `StacksFrontier/AlgebraicGeometry/Duality/SheafSubquotient.lean`, every identity
between composites below is therefore an explicit chain of `CategoryTheory.Category.assoc` and
`congrArg` steps, and the passage to `Ext` is a single `congrArg` in the morphism rather than a
rewrite.

The inclusion `𝓘^n 𝓕' ⊆ 𝓕'` is an argument of
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerSubIso_hom_comp` rather than fixed to
`AlgebraicGeometry.idealPowerSub_le`, so that the lemma applies on the nose to whichever proof of
that containment the surrounding computation has produced.

`Stacks.Cohomology.ColimitsOfCohomology.ext_comp_eq_zero_of_comp` is the one-line fact that a
class killed by a morphism is killed by any composite ending in it; it is imported rather than
restated.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe w u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The elementary half of the comparison -/

/-- **`𝓘^n N` is contained in `𝓘^n L ⊓ N`** for a quasi-coherent submodule `N` of a
quasi-coherent module `L`. Over an affine open the sections of `𝓘^n N` are `𝓘(U)^n N(U)`
(`AlgebraicGeometry.idealPowerSub_obj_affine`), which lie both in `N(U)` and in
`𝓘(U)^n L(U)`. -/
lemma idealPowerSub_le_inf (I : X.IdealSheafData) (n : ℕ) {L : X.Modules} (N : L.Submodule)
    (hL : L.IsQuasicoherent) (hN : (subMod N).IsQuasicoherent) :
    idealPowerSub I n N ≤ Stacks.Algebraization.idealPowerMultiple I n L ⊓ N :=
  Stacks.Algebraization.submodule_le_of_affine _ _ fun U => by
    have h1 : secs (idealPowerSub I n N) U.1 = I.ideal U ^ n • secs N U.1 :=
      idealPowerSub_obj_affine I n N hN U
    have h2 : secs (Stacks.Algebraization.idealPowerMultiple I n L ⊓ N) U.1 =
        I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(L, U.1)) ⊓ secs N U.1 := by
      rw [secs_inf, secs_idealPowerMultiple I n L hL U]
    show secs (idealPowerSub I n N) U.1 ≤ secs _ U.1
    rw [h1, h2]
    exact le_inf (Submodule.smul_mono le_rfl le_top) Submodule.smul_le_right

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}

/-! ### `𝓘^n N` as a submodule of `N` and as a submodule of `L` -/

/-- **The inclusions between submodules compose.** This is
`SheafOfModules.Submodule.homOfLE_comp` re-elaborated at the `AlgebraicGeometry.Scheme.Modules`
spelling of the category. -/
theorem submoduleHomOfLE_comp {M : X.Modules} {N₁ N₂ N₃ : M.Submodule} (h₁ : N₁ ≤ N₂)
    (h₂ : N₂ ≤ N₃) :
    submoduleHomOfLE h₁ ≫ submoduleHomOfLE h₂ = submoduleHomOfLE (h₁.trans h₂) := rfl

/-- **`𝓘^n N`, read inside `N`, is `𝓘^n N` read inside `L`.** The inclusion `𝓘^n N ⟶ N ⟶ L` is a
monomorphism and `AlgebraicGeometry.idealPowerSub` is by definition its sectionwise image, so this
is `AlgebraicGeometry.imageSubmoduleIso`. -/
def idealPowerSubIso (I : X.IdealSheafData) (n : ℕ) {L : X.Modules} (N : L.Submodule) :
    subMod (idealPowerMultiple I n (subMod N)) ≅ subMod (idealPowerSub I n N) :=
  imageSubmoduleIso (submoduleι (idealPowerMultiple I n (subMod N)) ≫ submoduleι N)
    (mono_comp _ _)

/-- **The identification of the two spellings of `𝓘^n N` is compatible with their inclusions into
`N`.** This is the only property of
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerSubIso` used below. -/
theorem idealPowerSubIso_hom_comp (I : X.IdealSheafData) (n : ℕ) {L : X.Modules}
    (N : L.Submodule) (h : idealPowerSub I n N ≤ N) :
    (idealPowerSubIso I n N).hom ≫ submoduleHomOfLE h =
      submoduleι (idealPowerMultiple I n (subMod N)) :=
  (cancel_mono (submoduleι N)).mp
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t : subMod (idealPowerSub I n N) ⟶ L =>
            (idealPowerSubIso I n N).hom ≫ t) (submoduleHomOfLE_ι h)).trans
        (imageSubmoduleIso_hom_comp_subι
          (submoduleι (idealPowerMultiple I n (subMod N)) ≫ submoduleι N) (mono_comp _ _))))

/-- The inclusion `𝓘^n N ⟶ N` of submodules of `L`, read through
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerSubIso`, is the inclusion `𝓘^n N ⟶ N` of
submodules of `N`. -/
theorem submoduleHomOfLE_eq_idealPowerSubIso_inv_comp (I : X.IdealSheafData) (n : ℕ)
    {L : X.Modules} (N : L.Submodule) (h : idealPowerSub I n N ≤ N) :
    submoduleHomOfLE h = (idealPowerSubIso I n N).inv ≫
      submoduleι (idealPowerMultiple I n (subMod N)) :=
  (Iso.inv_hom_id_assoc (idealPowerSubIso I n N) (submoduleHomOfLE h)).symm.trans
    (congrArg (fun t : subMod (idealPowerMultiple I n (subMod N)) ⟶ subMod N =>
      (idealPowerSubIso I n N).inv ≫ t) (idealPowerSubIso_hom_comp I n N h))

/-! ### The comparison on `Ext`-groups -/

/-- A class killed by `g` is killed by any morphism that factors through `g`. -/
private theorem mk₀_comp_eq_zero_of_eq_comp [HasExt.{w} X.Modules] {A B C D : X.Modules}
    {k : A ⟶ B} (f : A ⟶ C) (g : C ⟶ B) (hk : k = f ≫ g) {i : ℕ} (θ : Ext.{w} B D i)
    (h : (Ext.mk₀ g).comp θ (zero_add i) = 0) : (Ext.mk₀ k).comp θ (zero_add i) = 0 :=
  (congrArg (fun k : A ⟶ B => (Ext.mk₀ k).comp θ (zero_add i)) hk).trans
    (Stacks.Cohomology.ColimitsOfCohomology.ext_comp_eq_zero_of_comp _ _ θ h)

/-- **The elementary half of the comparison, on `Ext`-groups.** A class on a quasi-coherent
submodule `N` of a quasi-coherent module `L` which dies under the inclusion of `𝓘^n L ⊓ N` also
dies under the inclusion of `𝓘^n N`, because the latter inclusion factors through the former
(`AlgebraicGeometry.idealPowerSub_le_inf`).

For `L` a module `𝓖` and `N` the member `𝓘^n 𝓖` of its ideal-power filtration this is
`Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_idealPowSmulMap_comp_eq_zero` read backwards:
there the two families are the filtration of `𝓘^n 𝓖` and the filtration of `𝓖`, and the
comparison needs no Artin-Rees. -/
theorem mk₀_submoduleι_idealPowerMultiple_comp_eq_zero [HasExt.{w} X.Modules]
    (I : X.IdealSheafData) (n : ℕ) {L : X.Modules} (N : L.Submodule) (hL : L.IsQuasicoherent)
    (hN : (subMod N).IsQuasicoherent) {F : X.Modules} {i : ℕ} (θ : Ext.{w} (subMod N) F i)
    (h : (Ext.mk₀ (submoduleHomOfLE (inf_le_right :
        Stacks.Algebraization.idealPowerMultiple I n L ⊓ N ≤ N))).comp θ (zero_add i) = 0) :
    (Ext.mk₀ (submoduleι (idealPowerMultiple I n (subMod N)))).comp θ (zero_add i) = 0 :=
  have hfac : submoduleι (idealPowerMultiple I n (subMod N)) =
      ((idealPowerSubIso I n N).hom ≫
          submoduleHomOfLE (idealPowerSub_le_inf I n N hL hN)) ≫
        submoduleHomOfLE (inf_le_right :
          Stacks.Algebraization.idealPowerMultiple I n L ⊓ N ≤ N) :=
    (idealPowerSubIso_hom_comp I n N
          ((idealPowerSub_le_inf I n N hL hN).trans inf_le_right)).symm.trans
      ((congrArg (fun t : subMod (idealPowerSub I n N) ⟶ subMod N =>
            (idealPowerSubIso I n N).hom ≫ t)
          (submoduleHomOfLE_comp (idealPowerSub_le_inf I n N hL hN) inf_le_right).symm).trans
        (Category.assoc _ _ _).symm)
  mk₀_comp_eq_zero_of_eq_comp _ _ hfac θ h

/-- **The Artin-Rees half of the comparison, on `Ext`-groups.** Let `L` be a coherent module on a
Noetherian scheme and `N` a quasi-coherent submodule of `L`. A class on `N` which dies under the
inclusion of `𝓘^m N` dies under the inclusion of `𝓘^n L ⊓ N` for some `n ≥ m`.

This is the transport of [Stacks, Tag 01YA], in the form
`AlgebraicGeometry.exists_idealPowerSub_artinRees`, onto the vanishing assertions of the core case
of [Stacks, Tag 0G2H]: the inclusion of `𝓘^n L ⊓ N` factors through that of `𝓘^{n - c} N` once
`n ≥ c`, and `n = m + c` turns `𝓘^{n - c} N` into `𝓘^m N`. -/
theorem exists_mk₀_submoduleHomOfLE_inf_comp_eq_zero
    [_root_.AlgebraicGeometry.IsNoetherian X] [HasExt.{w} X.Modules] (I : X.IdealSheafData)
    {L : X.Modules} (N : L.Submodule) (hL : L.IsCoherent) (hN : (subMod N).IsQuasicoherent)
    {F : X.Modules} {i : ℕ} (θ : Ext.{w} (subMod N) F i) {m : ℕ}
    (hm : (Ext.mk₀ (submoduleι (idealPowerMultiple I m (subMod N)))).comp θ (zero_add i) = 0) :
    ∃ n : ℕ, m ≤ n ∧ (Ext.mk₀ (submoduleHomOfLE (inf_le_right :
      Stacks.Algebraization.idealPowerMultiple I n L ⊓ N ≤ N))).comp θ (zero_add i) = 0 := by
  obtain ⟨c, hc, hAR⟩ := exists_idealPowerSub_artinRees I L hL N hN
  refine ⟨m + c, Nat.le_add_right m c, ?_⟩
  have hle : Stacks.Algebraization.idealPowerMultiple I (m + c) L ⊓ N ≤
      idealPowerSub I m N := by
    have h0 := hAR (m + c) (Nat.le_add_left c m)
    rwa [Nat.add_sub_cancel] at h0
  have hfac : submoduleHomOfLE (inf_le_right :
        Stacks.Algebraization.idealPowerMultiple I (m + c) L ⊓ N ≤ N) =
      (submoduleHomOfLE hle ≫ (idealPowerSubIso I m N).inv) ≫
        submoduleι (idealPowerMultiple I m (subMod N)) :=
    (submoduleHomOfLE_comp hle (idealPowerSub_le I m N)).symm.trans
      ((congrArg (fun t : subMod (idealPowerSub I m N) ⟶ subMod N =>
            submoduleHomOfLE hle ≫ t)
          (submoduleHomOfLE_eq_idealPowerSubIso_inv_comp I m N
            (idealPowerSub_le I m N))).trans
        (Category.assoc _ _ _).symm)
  exact mk₀_comp_eq_zero_of_eq_comp _ _ hfac θ hm

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
