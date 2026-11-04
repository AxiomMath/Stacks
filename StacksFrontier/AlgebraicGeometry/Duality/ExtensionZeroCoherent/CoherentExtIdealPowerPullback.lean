module

public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtDimensionShift
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerArtinReesTransport

/-!
# Restricting a dimension-shifted `Ext`-class to the ideal-power filtration

Let `X` be a scheme, `𝓘` a quasi-coherent sheaf of ideals and `α : 𝓕'' ⟶ 𝓐` an epimorphism of
quasi-coherent `𝒪_X`-modules, with short exact sequence

`S : 0 ⟶ ker α ⟶ 𝓕'' ⟶ 𝓐 ⟶ 0`.

For every `n` the members of the ideal-power filtrations of `𝓕''` and of `𝓐` fit into a short
exact sequence of their own,

`S_n : 0 ⟶ ker(𝓘^n 𝓕'' ⟶ 𝓘^n 𝓐) ⟶ 𝓘^n 𝓕'' ⟶ 𝓘^n 𝓐 ⟶ 0`,

which maps to `S` by the three filtration inclusions, and whose first term is contained in
`𝓘^n 𝓕'' ⊓ ker α`. This file builds that sequence and that morphism, and draws from them the
consequence on `Ext`-groups: **a class `hS.extClass ∘ ξ'` of degree `i + 1` on `𝓐` dies on
`𝓘^n 𝓐` as soon as `ξ'` dies on `𝓘^n 𝓕'' ⊓ ker α`**
(`Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_submoduleι_comp_extClass_comp_eq_zero`).

This is the inductive step of the injectivity half of the core case of [Stacks, Tag 0G2H], the
bijectivity of `colim_n Ext^i_X(𝓘^n𝓖, 𝓕) ⟶ Ext^i_U(𝓖|_U, 𝓕|_U)`: there a class of degree
`i + 1` is written as `hS.extClass ∘ ξ'` with `ker α` the subsheaf
`Stacks.AlgebraicGeometry.IdealPowerColimit.kerMod` of `𝓕''`
(`Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_of_pos`), which is what makes the
intersection `𝓘^n 𝓕'' ⊓ ker α` available.

## The construction

The epimorphism `𝓘^n 𝓕'' ⟶ 𝓘^n 𝓐` is `AlgebraicGeometry.toImageSubmodule` of the composite
`𝓘^n 𝓕'' ⟶ 𝓕'' ⟶ 𝓐`, whose sectionwise image is `𝓘^n 𝓐` because `α` is an epimorphism of
quasi-coherent modules (`AlgebraicGeometry.imageSubmodule_idealPowerMultiple_of_epi`); the
identification of that image with `𝓘^n 𝓐` is an inclusion of submodules in both directions, hence
an isomorphism, which avoids transporting along an equality of submodules.

Its kernel is taken as the *sectionwise* kernel
`Stacks.AlgebraicGeometry.IdealPowerColimit.kerMod`, so that short exactness of `S_n` is
`CategoryTheory.ShortComplex.exact_of_f_is_kernel` applied to
`Stacks.AlgebraicGeometry.IdealPowerColimit.kerIsLimit` and needs no computation. It is *not*
identified with `𝓘^n 𝓕'' ⊓ ker α`: only the inclusion
`Stacks.AlgebraicGeometry.IdealPowerColimit.kerIdealPowerEpiLift` of it into that intersection is
built, which is all the `Ext`-statement needs, since a class killed by a morphism is killed by any
composite ending in it. That inclusion comes from the containment of sectionwise images
`imageSubmodule (ker(𝓘^n𝓕'' ⟶ 𝓘^n𝓐) ⟶ 𝓕'') ≤ 𝓘^n 𝓕'' ⊓ ker α`, whose second half is obtained by
factoring that inclusion of `𝓕''` through the kernel of `α` rather than by a computation with
sections.

The `Ext`-statement itself is Mathlib's naturality of the class of a short exact sequence,
`CategoryTheory.ShortComplex.ShortExact.extClass_naturality`, which is isolated from the geometry
as `Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp_eq_zero`.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerEpi`: **the epimorphism
  `𝓘^n 𝓕'' ⟶ 𝓘^n 𝓐` induced by an epimorphism `𝓕'' ⟶ 𝓐` of quasi-coherent modules.**
* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerShortComplexHom`: the morphism of short
  complexes `S_n ⟶ S`.

## Main results

* `Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp_eq_zero`: along a morphism of short exact
  sequences, a boundary class `hS₂.extClass ∘ ξ'` is killed by `φ.τ₃` as soon as `ξ'` is killed by
  `φ.τ₁`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.shortExact_idealPowerEpi`: **the sequence `S_n` is
  short exact.**
* `Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_submoduleι_comp_extClass_comp_eq_zero`: **the
  inductive step of the injectivity chase of [Stacks, Tag 0G2H].**

## Implementation notes

As in
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerArtinReesTransport`,
every inclusion of submodules below is spelled with
`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι` and
`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE`, whose declared types are at the
`AlgebraicGeometry.Scheme.Modules` spelling of the category rather than at `SheafOfModules`: the
`CategoryTheory.HasExt` instance, and hence the universe of the `Ext`-groups, differs between the
two. For the same reason the identities between composites are explicit chains of
`CategoryTheory.Category.assoc` and `congrArg` steps rather than rewrites.

`Stacks.Cohomology.ColimitsOfCohomology.ext_comp_eq_zero_of_comp` is the fact that a class killed
by a morphism is killed by any composite ending in it.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower

universe w v u

namespace Stacks.ExtEffacement

/-! ### The chase step along a morphism of short exact sequences -/

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **A boundary class is killed by `φ.τ₃` as soon as the class it comes from is killed by
`φ.τ₁`.** Let `φ : S₁ ⟶ S₂` be a morphism of short exact sequences in an abelian category and let
`ξ'` be a class of degree `i` on `S₂.X₁`. If `φ.τ₁` kills `ξ'`, then `φ.τ₃` kills the boundary
class `hS₂.extClass ∘ ξ'` of degree `i + 1` on `S₂.X₃`.

This is Mathlib's `CategoryTheory.ShortComplex.ShortExact.extClass_naturality`: the boundary
class of `S₂`, precomposed with `φ.τ₃`, is the boundary class of `S₁` postcomposed with `φ.τ₁`,
and the latter annihilates `ξ'` by hypothesis. It is the diagram chase of the injectivity half of
the core case of [Stacks, Tag 0G2H], isolated from the geometry that produces `S₁` and `φ`. -/
theorem mk₀_τ₃_comp_extClass_comp_eq_zero {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) {G : C} {i n : ℕ} (hn : 1 + i = n)
    (ξ' : Ext.{w} S₂.X₁ G i) (hξ' : (Ext.mk₀ φ.τ₁).comp ξ' (zero_add i) = 0) :
    (Ext.mk₀ φ.τ₃).comp (h₂.extClass.comp ξ' hn) (zero_add n) = 0 := by
  rw [← Ext.comp_assoc (Ext.mk₀ φ.τ₃) h₂.extClass ξ' (zero_add 1) hn (by lia),
    ← ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ,
    Ext.comp_assoc_of_second_deg_zero, hξ', Ext.comp_zero]

end Stacks.ExtEffacement

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}

/-! ### An equality of submodules as an isomorphism -/

/-- **The inclusion given by an equality of submodules is an isomorphism**, its inverse being the
inclusion the other way. This is how an equality of submodules is used below, rather than by
transporting along it. -/
lemma isIso_submoduleHomOfLE_of_eq {M : X.Modules} {N₁ N₂ : M.Submodule} (h : N₁ = N₂) :
    IsIso (submoduleHomOfLE (le_of_eq h)) :=
  ⟨submoduleHomOfLE (le_of_eq h.symm),
    (submoduleHomOfLE_comp (le_of_eq h) (le_of_eq h.symm)).trans (subInclusion_refl N₁),
    (submoduleHomOfLE_comp (le_of_eq h.symm) (le_of_eq h)).trans (subInclusion_refl N₂)⟩

/-! ### The epimorphism `𝓘^n E ⟶ 𝓘^n A` -/

section

variable (I : X.IdealSheafData) (n : ℕ) {E A : X.Modules} (hE : E.IsQuasicoherent)
  (hA : A.IsQuasicoherent) (α : E ⟶ A) (hα : Epi α)

/-- **The epimorphism `𝓘^n E ⟶ 𝓘^n A` induced by an epimorphism `α : E ⟶ A` of quasi-coherent
modules.** It is the corestriction of `𝓘^n E ⟶ E ⟶ A` to its sectionwise image, which is `𝓘^n A`
by `AlgebraicGeometry.imageSubmodule_idealPowerMultiple_of_epi`. -/
def idealPowerEpi :
    subMod (Stacks.Algebraization.idealPowerMultiple I n E) ⟶
      subMod (Stacks.Algebraization.idealPowerMultiple I n A) :=
  toImageSubmodule (submoduleι (Stacks.Algebraization.idealPowerMultiple I n E) ≫ α) ≫
    submoduleHomOfLE
      (le_of_eq (imageSubmodule_idealPowerMultiple_of_epi I n hE hA α hα))

/-- The corestriction of `p` to its image, followed by an inclusion of the image into a larger
submodule `P` and by the inclusion of `P`, is `p`. -/
private lemma toImageSubmodule_comp_submoduleHomOfLE_comp_submoduleι {M N : X.Modules} (p : M ⟶ N)
    {P : N.Submodule} (h : imageSubmodule p ≤ P) :
    (toImageSubmodule p ≫ submoduleHomOfLE h) ≫ submoduleι P = p :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t : subMod (imageSubmodule p) ⟶ N => toImageSubmodule p ≫ t)
      (submoduleHomOfLE_ι h)).trans (toImageSubmodule_comp_subι p))

/-- **`𝓘^n E ⟶ 𝓘^n A` is compatible with the inclusions into `E` and `A`.** -/
lemma idealPowerEpi_comp_submoduleι :
    idealPowerEpi I n hE hA α hα ≫
        submoduleι (Stacks.Algebraization.idealPowerMultiple I n A) =
      submoduleι (Stacks.Algebraization.idealPowerMultiple I n E) ≫ α :=
  toImageSubmodule_comp_submoduleHomOfLE_comp_submoduleι _
    (le_of_eq (imageSubmodule_idealPowerMultiple_of_epi I n hE hA α hα))

/-- **`𝓘^n E ⟶ 𝓘^n A` is an epimorphism**: a corestriction to a sectionwise image followed by an
isomorphism. -/
lemma epi_idealPowerEpi : Epi (idealPowerEpi I n hE hA α hα) :=
  epi_comp' (epi_toImageSubmodule _)
    (epi_of_isIso_modules _
      (isIso_submoduleHomOfLE_of_eq
        (imageSubmodule_idealPowerMultiple_of_epi I n hE hA α hα)))

/-! ### Its kernel, inside `𝓘^n E ⊓ ker α` -/

/-- The inclusion of the kernel of `𝓘^n E ⟶ 𝓘^n A` into `E`. -/
abbrev kerIdealPowerEpiι : kerMod (idealPowerEpi I n hE hA α hα) ⟶ E :=
  kerInclusion (idealPowerEpi I n hE hA α hα) ≫
    submoduleι (Stacks.Algebraization.idealPowerMultiple I n E)

/-- **`α` annihilates the kernel of `𝓘^n E ⟶ 𝓘^n A`**, read inside `E`: the inclusion of `𝓘^n E`
into `E` followed by `α` is `𝓘^n E ⟶ 𝓘^n A` followed by the inclusion of `𝓘^n A` into `A`. -/
lemma kerIdealPowerEpiι_comp : kerIdealPowerEpiι I n hE hA α hα ≫ α = 0 :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t : subMod (Stacks.Algebraization.idealPowerMultiple I n E) ⟶ A =>
          kerInclusion (idealPowerEpi I n hE hA α hα) ≫ t)
        (idealPowerEpi_comp_submoduleι I n hE hA α hα).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t : kerMod (idealPowerEpi I n hE hA α hα) ⟶
              subMod (Stacks.Algebraization.idealPowerMultiple I n A) =>
            t ≫ submoduleι (Stacks.Algebraization.idealPowerMultiple I n A))
          (kerInclusion_comp (idealPowerEpi I n hE hA α hα))).trans zero_comp)))

/-- **The kernel of `𝓘^n E ⟶ 𝓘^n A`, read inside `E`, lands in `𝓘^n E ⊓ ker α`.** It lands in
`𝓘^n E` because its inclusion into `E` factors through that of `𝓘^n E`, and in `ker α` because
`α` annihilates it, so that the same inclusion factors through the inclusion of `ker α`. -/
lemma imageSubmodule_kerIdealPowerEpiι_le :
    imageSubmodule (kerIdealPowerEpiι I n hE hA α hα) ≤
      Stacks.Algebraization.idealPowerMultiple I n E ⊓ SheafOfModules.Submodule.ker α := by
  refine le_inf ((imageSubmodule_comp_le _ _).trans
    (le_of_eq (imageSubmodule_subι (Stacks.Algebraization.idealPowerMultiple I n E)))) ?_
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (kerIsLimit α)
    (kerIdealPowerEpiι I n hE hA α hα) (kerIdealPowerEpiι_comp I n hE hA α hα)
  exact (le_of_eq (congrArg (fun t : kerMod (idealPowerEpi I n hE hA α hα) ⟶ E =>
        imageSubmodule t) hl.symm)).trans
    ((imageSubmodule_comp_le l (kerInclusion α)).trans
      (le_of_eq (imageSubmodule_subι (SheafOfModules.Submodule.ker α))))

/-- **The inclusion `ker(𝓘^n E ⟶ 𝓘^n A) ⟶ 𝓘^n E ⊓ ker α`.** Only this inclusion is built, not an
isomorphism of the two: on `Ext`-groups a class killed by the inclusion of `𝓘^n E ⊓ ker α` is
killed by any composite ending in it, which is all that is needed. -/
def kerIdealPowerEpiLift : kerMod (idealPowerEpi I n hE hA α hα) ⟶
    subMod (Stacks.Algebraization.idealPowerMultiple I n E ⊓
      SheafOfModules.Submodule.ker α) :=
  toImageSubmodule (kerIdealPowerEpiι I n hE hA α hα) ≫
    submoduleHomOfLE (imageSubmodule_kerIdealPowerEpiι_le I n hE hA α hα)

/-- `kerIdealPowerEpiLift` followed by the inclusion of `𝓘^n E ⊓ ker α` into `E` is the inclusion
of `ker(𝓘^n E ⟶ 𝓘^n A)` into `E`. -/
lemma kerIdealPowerEpiLift_comp :
    kerIdealPowerEpiLift I n hE hA α hα ≫
        submoduleι (Stacks.Algebraization.idealPowerMultiple I n E ⊓
          SheafOfModules.Submodule.ker α) =
      kerIdealPowerEpiι I n hE hA α hα :=
  toImageSubmodule_comp_submoduleHomOfLE_comp_submoduleι _
    (imageSubmodule_kerIdealPowerEpiι_le I n hE hA α hα)

/-- The first component `ker(𝓘^n E ⟶ 𝓘^n A) ⟶ ker α` of the morphism of short exact sequences: the
inclusion into `𝓘^n E ⊓ ker α` followed by the inclusion of that into `ker α`. -/
def kerIdealPowerEpiToKer : kerMod (idealPowerEpi I n hE hA α hα) ⟶ kerMod α :=
  kerIdealPowerEpiLift I n hE hA α hα ≫
    submoduleHomOfLE (inf_le_right : Stacks.Algebraization.idealPowerMultiple I n E ⊓
      SheafOfModules.Submodule.ker α ≤ SheafOfModules.Submodule.ker α)

/-- `kerIdealPowerEpiToKer` followed by the inclusion of `ker α` into `E` is the inclusion of
`ker(𝓘^n E ⟶ 𝓘^n A)` into `E`. -/
lemma kerIdealPowerEpiToKer_comp :
    kerIdealPowerEpiToKer I n hE hA α hα ≫ kerInclusion α =
      kerIdealPowerEpiι I n hE hA α hα :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t : subMod (Stacks.Algebraization.idealPowerMultiple I n E ⊓
          SheafOfModules.Submodule.ker α) ⟶ E =>
        kerIdealPowerEpiLift I n hE hA α hα ≫ t)
      (submoduleHomOfLE_ι (inf_le_right :
        Stacks.Algebraization.idealPowerMultiple I n E ⊓
          SheafOfModules.Submodule.ker α ≤ SheafOfModules.Submodule.ker α))).trans
      (kerIdealPowerEpiLift_comp I n hE hA α hα))

/-! ### The short exact sequence of the ideal powers, and its morphism to that of `α` -/

/-- **The short exact sequence `0 ⟶ ker(𝓘^n E ⟶ 𝓘^n A) ⟶ 𝓘^n E ⟶ 𝓘^n A ⟶ 0`.** Its first map is a
kernel of its second by `Stacks.AlgebraicGeometry.IdealPowerColimit.kerIsLimit`, and its second is
an epimorphism by
`Stacks.AlgebraicGeometry.IdealPowerColimit.epi_idealPowerEpi`. -/
lemma shortExact_idealPowerEpi :
    (ShortComplex.mk (kerInclusion (idealPowerEpi I n hE hA α hα))
      (idealPowerEpi I n hE hA α hα)
      (kerInclusion_comp (idealPowerEpi I n hE hA α hα))).ShortExact :=
  have := epi_idealPowerEpi I n hE hA α hα
  ⟨ShortComplex.exact_of_f_is_kernel _ (kerIsLimit (idealPowerEpi I n hE hA α hα))⟩

/-- **The morphism from the short exact sequence of the ideal powers to that of `α`**, given by
the three inclusions `ker(𝓘^n E ⟶ 𝓘^n A) ⟶ ker α`, `𝓘^n E ⟶ E` and `𝓘^n A ⟶ A`. -/
def idealPowerShortComplexHom :
    ShortComplex.mk (kerInclusion (idealPowerEpi I n hE hA α hα))
        (idealPowerEpi I n hE hA α hα)
        (kerInclusion_comp (idealPowerEpi I n hE hA α hα)) ⟶
      ShortComplex.mk (kerInclusion α) α (kerInclusion_comp α) where
  τ₁ := kerIdealPowerEpiToKer I n hE hA α hα
  τ₂ := submoduleι (Stacks.Algebraization.idealPowerMultiple I n E)
  τ₃ := submoduleι (Stacks.Algebraization.idealPowerMultiple I n A)
  comm₁₂ := kerIdealPowerEpiToKer_comp I n hE hA α hα
  comm₂₃ := (idealPowerEpi_comp_submoduleι I n hE hA α hα).symm

/-! ### The consequence on `Ext`-groups -/

include hE hA hα in
/-- **The inductive step of the injectivity chase of [Stacks, Tag 0G2H].** Let `α : E ⟶ A` be an
epimorphism of quasi-coherent `𝒪_X`-modules with short exact sequence
`S : 0 ⟶ ker α ⟶ E ⟶ A ⟶ 0`, and let `ξ'` be a class of degree `i` on `ker α`. If `ξ'` dies under
the inclusion of `𝓘^n E ⊓ ker α`, then the boundary class `hS.extClass ∘ ξ'` of degree `i + 1` on
`A` dies under the inclusion of `𝓘^n A`.

This is `Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp_eq_zero` for the morphism
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerShortComplexHom` of short exact sequences,
whose first component factors through the inclusion of `𝓘^n E ⊓ ker α`. -/
theorem mk₀_submoduleι_comp_extClass_comp_eq_zero [HasExt.{w} X.Modules] {G : X.Modules}
    (hS : (ShortComplex.mk (kerInclusion α) α (kerInclusion_comp α)).ShortExact)
    {i : ℕ} (ξ' : Ext.{w} (kerMod α) G i)
    (hξ' : (Ext.mk₀ (submoduleHomOfLE (inf_le_right :
      Stacks.Algebraization.idealPowerMultiple I n E ⊓ SheafOfModules.Submodule.ker α ≤
        SheafOfModules.Submodule.ker α))).comp ξ' (zero_add i) = 0) :
    (Ext.mk₀ (submoduleι (Stacks.Algebraization.idealPowerMultiple I n A))).comp
      (hS.extClass.comp ξ' (Nat.add_comm 1 i)) (zero_add (i + 1)) = 0 :=
  Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp_eq_zero
    (shortExact_idealPowerEpi I n hE hA α hα) hS
    (idealPowerShortComplexHom I n hE hA α hα) (Nat.add_comm 1 i) ξ'
    (Stacks.Cohomology.ColimitsOfCohomology.ext_comp_eq_zero_of_comp
      (kerIdealPowerEpiLift I n hE hA α hα) _ ξ' hξ')

end

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
