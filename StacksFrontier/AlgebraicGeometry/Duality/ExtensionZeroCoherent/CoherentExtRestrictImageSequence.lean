module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.ImageCoherent
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SubQuotient
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtIdealPowerPullback
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtRestrictDimensionShift
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtRestrictExtension

/-!
# The surjectivity half of the core case of Stacks 0G2H

Let `X` be a Noetherian scheme, `𝓘` a quasi-coherent sheaf of ideals, `U = X ∖ V(𝓘)` and `𝓖`,
`𝓕` coherent `𝒪_X`-modules. This file proves the **surjectivity half of the core case of**
[Stacks, Tag 0G2H] **in every degree**: every class in `Ext^i_U(𝓖|_U, 𝓕|_U)` is the image of a
class in `Ext^i_X(𝓘^n 𝓖, 𝓕)` for some `n`
(`Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_isCoherent`). The base case `i = 0` is
the first display of [Stacks, Tag 01YB],
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_extIdealPowRestrict_eq`; everything else here
is the induction step.

## The step from `i` to `i + 1`

Given `η ∈ Ext^{i+1}_U(𝓖|_U, 𝓕|_U)`:

1. the coherent effacement on `U`
   (`Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_restrict_of_pos`) writes `η` as the
   boundary class of a short exact sequence `0 ⟶ ker φ ⟶ 𝓗 ⟶ 𝓖|_U ⟶ 0` of coherent
   `𝒪_U`-modules applied to a class `η'` of degree `i`;
2. [Stacks, Tag 01PI] carries `φ : 𝓗 ↠ 𝓖|_U` back across the open immersion
   (`Stacks.ExtEffacement.exists_isCoherent_extension_idealPowerMultiple_le_imageSubmodule`) as a
   morphism `ψ : 𝓔 ⟶ 𝓖` of coherent modules with `ψ|_U` an epimorphism, together with an `m`
   such that `𝓘^m 𝓖 ⊆ Im ψ`;
3. the short exact sequence `S : 0 ⟶ ker ψ ⟶ 𝓔 ⟶ Im ψ ⟶ 0` on `X`
   (`Stacks.ExtEffacement.shortExact_toImageMod`) restricts on `U` to a sequence isomorphic to
   the one of step 1 (`Stacks.ExtEffacement.restrictImageShortComplexHom`), so `η` read through
   `(Im ψ)|_U ≅ 𝓖|_U` is the boundary class of `S|_U` applied to a degree-`i` class on
   `(ker ψ)|_U` — this is
   `Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_restrict_image_of_pos`;
4. the induction hypothesis, applied to the coherent module `ker ψ`, lifts that class to
   `𝓘^n (ker ψ)`;
5. Artin-Rees (`Stacks.ExtEffacement.exists_fac_submoduleHomOfLE_inf`) carries it onto the first
   term of the ideal-power sequence
   `S_N : 0 ⟶ ker(𝓘^N 𝓔 ⟶ 𝓘^N Im ψ) ⟶ 𝓘^N 𝓔 ⟶ 𝓘^N Im ψ ⟶ 0`
   built from `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerEpi`, whose boundary class
   turns it into a class of degree `i + 1` on `𝓘^N Im ψ`;
6. `𝓘^{N+m} 𝓖 ⊆ 𝓘^N Im ψ`
   (`Stacks.ExtEffacement.idealPowerMultiple_le_idealPowerSub`) reads that class on the member
   `𝓘^{N+m} 𝓖` of the ideal-power filtration of `𝓖`, and
   `Stacks.ExtEffacement.mk₀_inv_comp_mapExactFunctor_extClass_comp` — the whole computation,
   carried out for an arbitrary exact functor between abelian categories — says that it restricts
   to `η`.

## What this leaves

The core case of [Stacks, Tag 0G2H], the hypothesis `hcore` of
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core`, is the bijectivity of
`colim_n Ext^i_X(𝓘^n 𝓖, 𝓕) ⟶ Ext^i_U(𝓖|_U, 𝓕|_U)`. Its surjectivity half is the hypothesis
`hsurj` of `AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem` and is what is
proved here; its injectivity half, `hinj`, is
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_idealPowSmulMap_comp_eq_zero_of_isCoherent`;
the statement proved here is one of its two inputs, the other being the contravariant long exact
sequence on `U` (`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁`), which exhibits the
dimension-shifted class as coming from a class on `𝓔|_U` that this statement lifts back to `X`.
With both halves, `hcore` is discharged in
`StacksFrontier/AlgebraicGeometry/Duality/ExtensionZeroCoherent/DeligneSystemCoreCoherent.lean` and
the tag is unconditional.

## The short exact sequence on `X`

The source's chase builds the sequence out of the **preimage of `𝓘^m 𝓖` under `ψ`**, so that its
third term is `𝓘^m 𝓖` on the nose. The sequence built here has third term the sectionwise image
`Im ψ` instead, and is lighter in exactly the way the containment `𝓘^m 𝓖 ⊆ Im ψ` itself was: no
preimage, no pullback square and no transport along an equality of submodules are needed, because
`AlgebraicGeometry.toImageSubmodule` already corestricts `ψ` to `Im ψ` as an epimorphism and
`Stacks.AlgebraicGeometry.IdealPowerColimit.kerIsLimit` already exhibits the sectionwise kernel as
a categorical one. The containment `𝓘^m 𝓖 ⊆ Im ψ` is kept in the conclusion, since it is what
turns the third term back into a member of the ideal-power filtration of `𝓖` further down the
chase.

## The comparison on `U`

The effacement is produced on `U`, as `φ : 𝓗 ↠ 𝓖|_U`, and [Stacks, Tag 01PI] returns it to `X` as
`ψ` together with an isomorphism `e : 𝓔|_U ≅ 𝓗` carrying `φ` to `ψ|_U`. The comparison of the two
sequences is then a morphism of short complexes
`Stacks.ExtEffacement.restrictImageShortComplexHom` whose middle component is `e` and whose third
component is

`(Im ψ)|_U ⟶ 𝓖|_U`,

**an isomorphism** (`Stacks.ExtEffacement.isIso_restrict_submoduleι_imageSubmodule`): it is a
monomorphism because the inclusion of a submodule is one and restriction preserves finite limits,
an epimorphism because `ψ|_U = (ψ|_U corestricted) ≫ it` is one, and `𝒪_U`-modules are balanced.
Its first component is the induced map on kernels, which exists because
`ker ψ|_U ⟶ 𝓔|_U ≅ 𝓗 ⟶ 𝓖|_U` vanishes. No inverse of either isomorphism appears: the conclusion
reads `η` composed with the third component, which is the direction the naturality of the boundary
class produces.

## Main results

* `Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp`: along a morphism of short exact sequences, a
  boundary class `h₂.extClass ∘ ξ'` precomposed with `φ.τ₃` is the boundary class of the first
  sequence applied to `φ.τ₁ ∘ ξ'`. This is Mathlib's
  `CategoryTheory.ShortComplex.ShortExact.extClass_naturality` in the shape the chase uses it; the
  vanishing consequence drawn from it in the injectivity chase is
  `Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp_eq_zero`.
* `Stacks.ExtEffacement.shortExact_toImageMod`: **the short exact sequence
  `0 ⟶ ker ψ ⟶ 𝓔 ⟶ Im ψ ⟶ 0` on `X`**, with `Stacks.ExtEffacement.isCoherent_imageMod` and
  `Stacks.ExtEffacement.isCoherent_kerMod_toImageMod` the coherence of its two outer terms.
* `Stacks.ExtEffacement.isIso_restrict_submoduleι_imageSubmodule`: **`(Im ψ)|_U = 𝓖|_U`** when
  `ψ|_U` is an epimorphism.
* `Stacks.ExtEffacement.restrictImageShortComplexHom`: **the comparison on `U` of the restricted
  sequence of `ψ` with the sequence of the effacement `φ`.**
* `Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_restrict_image_of_pos`: **the geometry
  of the chase in one statement** — a positive-degree class on `U`, read through
  `(Im ψ)|_U ≅ 𝓖|_U`, is the boundary class of the restriction of `S` applied to a class one
  degree lower.
* `Stacks.ExtEffacement.exists_fac_submoduleHomOfLE_inf`: **Artin-Rees in the direction that
  carries a class**, and `Stacks.ExtEffacement.idealPowerMultiple_le_idealPowerSub`:
  **`𝓘^{n+m} 𝓖 ⊆ 𝓘^n P` for a submodule `P` containing `𝓘^m 𝓖`.**
* `Stacks.ExtEffacement.mk₀_inv_comp_mapExactFunctor_extClass_comp`: **the chase as an identity of
  `Ext`-classes**, for an arbitrary exact functor between abelian categories.
* `Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_succ` and
  `Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_isCoherent`: **the induction step, and
  the surjectivity half of the core case of [Stacks, Tag 0G2H] in every degree.**

## Implementation notes

`AlgebraicGeometry.toImageSubmodule` has its declared type at the `SheafOfModules` spelling of the
category, where a different `CategoryTheory.HasExt` instance applies and `Ext` lands in another
universe; `Stacks.ExtEffacement.toImageMod` is the same morphism with its type pinned to
`AlgebraicGeometry.Scheme.Modules`, as `Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι` and
`Stacks.AlgebraicGeometry.IdealPowerColimit.subMod` are. Every `Ext`-statement below is at that
spelling. For the same reason the identities between composites are chains of
`CategoryTheory.Category.assoc` and `congrArg` steps rather than rewrites, as
`StacksFrontier/AlgebraicGeometry/Duality/SheafSubquotient.lean` records.

The `Ext`-computation of the induction step is carried out *abstractly*, in
`Stacks.ExtEffacement.mk₀_inv_comp_mapExactFunctor_extClass_comp`, for an arbitrary exact functor
between abelian categories, and the geometric step applies it in one `exact`. This is not
cosmetic: rewriting the same chain in place over `AlgebraicGeometry.Scheme.Modules` does not work,
because the two `Category` instance paths of that `def` make a lemma instance and a goal
subterm print identically while failing to match, so every `rw` reports its pattern as not found.
In the abstract setting there is one category instance and the rewrites go through.

`AlgebraicGeometry.imageSubmodule` is spelled with its full name throughout: there is a second
declaration of that name in the import closure, as there is for
`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE`.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01PI](https://stacks.math.columbia.edu/tag/01PI)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
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

/-- **Transporting a boundary class along a morphism of short exact sequences.** -/
theorem mk₀_τ₃_comp_extClass_comp {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) {G : C} {i n : ℕ} (hn : 1 + i = n)
    (ξ' : Ext.{w} S₂.X₁ G i) :
    (Ext.mk₀ f.τ₃).comp (h₂.extClass.comp ξ' hn) (zero_add n) =
      h₁.extClass.comp ((Ext.mk₀ f.τ₁).comp ξ' (zero_add i)) hn := by
  rw [← Ext.comp_assoc (Ext.mk₀ f.τ₃) h₂.extClass ξ' (zero_add 1) hn (by lia),
    ← ShortComplex.ShortExact.extClass_naturality h₁ h₂ f,
    Ext.comp_assoc_of_second_deg_zero]

/-- Two degree-zero classes composed on the left of a class compose as morphisms. -/
theorem mk₀_comp_mk₀_comp {A B D T : C} (a : A ⟶ B) (b : B ⟶ D) {i : ℕ} (θ : Ext.{w} D T i) :
    (Ext.mk₀ a).comp ((Ext.mk₀ b).comp θ (zero_add i)) (zero_add i) =
      (Ext.mk₀ (a ≫ b)).comp θ (zero_add i) := by
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

/-- A class recovered from its image under an isomorphism read backwards. -/
theorem eq_mk₀_hom_comp {A B T : C} (ε : A ≅ B) {i : ℕ} (θ : Ext.{w} A T i)
    (ζ : Ext.{w} B T i) (h : (Ext.mk₀ ε.inv).comp θ (zero_add i) = ζ) :
    θ = (Ext.mk₀ ε.hom).comp ζ (zero_add i) := by
  rw [← h, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, ε.hom_inv_id, Ext.mk₀_id_comp]

end Abstract

variable {X : Scheme.{u}}

section Image

variable {E G : X.Modules} (ψ : E ⟶ G)

/-- The corestriction of `ψ` to its sectionwise image. -/
def toImageMod : E ⟶ subMod (_root_.AlgebraicGeometry.imageSubmodule ψ) :=
  _root_.AlgebraicGeometry.toImageSubmodule ψ

/-- The corestriction of `ψ` to its image, followed by the inclusion of that image, is `ψ`. -/
theorem toImageMod_comp_submoduleι :
    toImageMod ψ ≫ submoduleι (_root_.AlgebraicGeometry.imageSubmodule ψ) = ψ :=
  _root_.AlgebraicGeometry.toImageSubmodule_comp_subι ψ

/-- The corestriction of `ψ` to its image is an epimorphism. -/
instance epi_toImageMod : Epi (toImageMod ψ) :=
  ⟨fun a b h => (_root_.AlgebraicGeometry.epi_toImageSubmodule ψ).left_cancellation a b h⟩

/-- **The short exact sequence `0 ⟶ ker ψ ⟶ 𝓔 ⟶ Im ψ ⟶ 0` on `X`.** -/
theorem shortExact_toImageMod :
    (ShortComplex.mk (kerInclusion (toImageMod ψ)) (toImageMod ψ)
      (kerInclusion_comp (toImageMod ψ))).ShortExact :=
  ⟨ShortComplex.exact_of_f_is_kernel _ (kerIsLimit (toImageMod ψ))⟩

/-- **The image of a morphism of coherent modules is coherent**: it is a quasi-coherent quotient
of the source. -/
theorem isCoherent_imageMod [IsLocallyNoetherian X] [E.IsCoherent] [G.IsQuasicoherent] :
    (subMod (_root_.AlgebraicGeometry.imageSubmodule ψ)).IsCoherent :=
  have : E.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent E
  have : (subMod (_root_.AlgebraicGeometry.imageSubmodule ψ)).IsQuasicoherent :=
    _root_.AlgebraicGeometry.isQuasicoherent_imageSubmodule ψ
  Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_epi_of_isQuasicoherent (toImageMod ψ)

/-- **The kernel of a morphism out of a coherent module is coherent**: it is a quasi-coherent
submodule of the source. -/
theorem isCoherent_kerMod_toImageMod [IsLocallyNoetherian X] [E.IsCoherent] [G.IsQuasicoherent] :
    (kerMod (toImageMod ψ)).IsCoherent :=
  have : E.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent E
  have : (subMod (_root_.AlgebraicGeometry.imageSubmodule ψ)).IsQuasicoherent :=
    _root_.AlgebraicGeometry.isQuasicoherent_imageSubmodule ψ
  Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent
    (kerInclusion (toImageMod ψ))

end Image

section Restrict

variable (U : X.Opens) {E G : X.Modules} (ψ : E ⟶ G)

/-- The restriction to `U` of the corestriction of `ψ` to its image, followed by the restriction
of the inclusion of that image, is the restriction of `ψ`. -/
theorem restrict_toImageMod_comp :
    (Scheme.Modules.restrictFunctor U.ι).map (toImageMod ψ) ≫
        (Scheme.Modules.restrictFunctor U.ι).map
          (submoduleι (_root_.AlgebraicGeometry.imageSubmodule ψ)) =
      (Scheme.Modules.restrictFunctor U.ι).map ψ :=
  ((Scheme.Modules.restrictFunctor U.ι).map_comp _ _).symm.trans
    (congrArg ((Scheme.Modules.restrictFunctor U.ι).map) (toImageMod_comp_submoduleι ψ))

/-- **`(Im ψ)|_U = 𝓖|_U` when `ψ|_U` is an epimorphism.** The inclusion of the image is a
monomorphism and restriction preserves finite limits, so its restriction is a monomorphism; it is
an epimorphism because `ψ|_U` factors through it; and `𝒪_U`-modules form a balanced category. -/
theorem isIso_restrict_submoduleι_imageSubmodule
    (hψ : Epi ((Scheme.Modules.restrictFunctor U.ι).map ψ)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (submoduleι (_root_.AlgebraicGeometry.imageSubmodule ψ))) :=
  have := hψ
  have : Epi ((Scheme.Modules.restrictFunctor U.ι).map
      (submoduleι (_root_.AlgebraicGeometry.imageSubmodule ψ))) :=
    epi_of_epi_fac (restrict_toImageMod_comp U ψ)
  isIso_of_mono_of_epi _

end Restrict

section Compare

variable (U : X.Opens) {E G : X.Modules} (ψ : E ⟶ G) {H : U.toScheme.Modules}
  (φ : H ⟶ (Scheme.Modules.restrictFunctor U.ι).obj G)
  (e : (Scheme.Modules.restrictFunctor U.ι).obj E ≅ H)
  (he : e.hom ≫ φ = (Scheme.Modules.restrictFunctor U.ι).map ψ)

/-- `ψ` annihilates the kernel of its corestriction to its image. -/
theorem kerInclusion_toImageMod_comp : kerInclusion (toImageMod ψ) ≫ ψ = 0 :=
  (congrArg (kerInclusion (toImageMod ψ) ≫ ·) (toImageMod_comp_submoduleι ψ).symm).trans
    (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ submoduleι (_root_.AlgebraicGeometry.imageSubmodule ψ))
          (kerInclusion_comp (toImageMod ψ)))).trans zero_comp)

/-- **The short exact sequence `0 ⟶ ker g ⟶ A ⟶ B ⟶ 0` of an epimorphism of `𝒪_U`-modules.**
Its first map is a kernel of its second by
`Stacks.AlgebraicGeometry.IdealPowerColimit.kerIsLimit`. -/
theorem shortExact_kerInclusion {A B : U.toScheme.Modules} (g : A ⟶ B) (hg : Epi g) :
    (ShortComplex.mk (kerInclusion g) g (kerInclusion_comp g)).ShortExact :=
  have := hg
  ⟨ShortComplex.exact_of_f_is_kernel _ (kerIsLimit g)⟩

include he in
/-- The inclusion of `ker ψ|_U` into `𝓔|_U`, followed by the comparison `𝓔|_U ≅ 𝓗`, is
annihilated by `φ`. -/
theorem restrict_kerInclusion_comp_hom_comp :
    ((Scheme.Modules.restrictFunctor U.ι).map (kerInclusion (toImageMod ψ)) ≫ e.hom) ≫ φ = 0 :=
  (Category.assoc _ _ _).trans
    ((congrArg ((Scheme.Modules.restrictFunctor U.ι).map (kerInclusion (toImageMod ψ)) ≫ ·)
          he).trans
      (((Scheme.Modules.restrictFunctor U.ι).map_comp _ _).symm.trans
        ((congrArg ((Scheme.Modules.restrictFunctor U.ι).map)
            (kerInclusion_toImageMod_comp ψ)).trans
          ((Scheme.Modules.restrictFunctor U.ι).map_zero _ _))))

include he in
/-- **The comparison `ker(ψ|_U) ⟶ ker φ`**, the first component of the morphism of short exact
sequences below. -/
def restrictKerToKer : (Scheme.Modules.restrictFunctor U.ι).obj (kerMod (toImageMod ψ)) ⟶
    kerMod φ :=
  (KernelFork.IsLimit.lift' (kerIsLimit φ)
    ((Scheme.Modules.restrictFunctor U.ι).map (kerInclusion (toImageMod ψ)) ≫ e.hom)
    (restrict_kerInclusion_comp_hom_comp U ψ φ e he)).1

include he in
/-- The comparison `ker(ψ|_U) ⟶ ker φ` is compatible with the two kernel inclusions. -/
theorem restrictKerToKer_comp :
    restrictKerToKer U ψ φ e he ≫ kerInclusion φ =
      (Scheme.Modules.restrictFunctor U.ι).map (kerInclusion (toImageMod ψ)) ≫ e.hom :=
  (KernelFork.IsLimit.lift' (kerIsLimit φ)
    ((Scheme.Modules.restrictFunctor U.ι).map (kerInclusion (toImageMod ψ)) ≫ e.hom)
    (restrict_kerInclusion_comp_hom_comp U ψ φ e he)).2

/-- **The comparison, on `U`, of the restricted sequence of `ψ` with the sequence of `φ`.** Its
second and third components are isomorphisms — the comparison `𝓔|_U ≅ 𝓗` and, when `ψ|_U` is an
epimorphism, `(Im ψ)|_U ≅ 𝓖|_U`. -/
def restrictImageShortComplexHom :
    (ShortComplex.mk (kerInclusion (toImageMod ψ)) (toImageMod ψ)
          (kerInclusion_comp (toImageMod ψ))).map (Scheme.Modules.restrictFunctor U.ι) ⟶
      ShortComplex.mk (kerInclusion φ) φ (kerInclusion_comp φ) where
  τ₁ := restrictKerToKer U ψ φ e he
  τ₂ := e.hom
  τ₃ := (Scheme.Modules.restrictFunctor U.ι).map
    (submoduleι (_root_.AlgebraicGeometry.imageSubmodule ψ))
  comm₁₂ := restrictKerToKer_comp U ψ φ e he
  comm₂₃ := he.trans (restrict_toImageMod_comp U ψ).symm

end Compare

section ArtinRees

/-- A submodule inside `𝓘^n P`, lifted into `𝓘^n (subMod P)` and included back into `subMod P`,
is its inclusion into `P`. -/
private theorem submoduleHomOfLE_comp_idealPowerSubIso_inv_comp_ι {L : X.Modules}
    (I : X.IdealSheafData) (n : ℕ) (P : L.Submodule) {Q : L.Submodule}
    (hle : Q ≤ _root_.AlgebraicGeometry.idealPowerSub I n P) :
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hle ≫
        (idealPowerSubIso I n P).inv) ≫
      submoduleι (Stacks.Algebraization.idealPowerMultiple I n (subMod P)) =
    Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
      (hle.trans (_root_.AlgebraicGeometry.idealPowerSub_le I n P)) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t : subMod (_root_.AlgebraicGeometry.idealPowerSub I n P) ⟶ subMod P =>
        Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hle ≫ t)
      (submoduleHomOfLE_eq_idealPowerSubIso_inv_comp I n P
        (_root_.AlgebraicGeometry.idealPowerSub_le I n P)).symm).trans
      (submoduleHomOfLE_comp hle (_root_.AlgebraicGeometry.idealPowerSub_le I n P)))

/-- **Artin-Rees in the non-vanishing direction.** Let `L` be a coherent module on a Noetherian
scheme and `N` a quasi-coherent submodule of `L`. For every `m` there is an `n ≥ m` and a
morphism `𝓘^n L ⊓ N ⟶ 𝓘^m N` whose composite with the inclusion of `𝓘^m N` into `N` is the
inclusion of `𝓘^n L ⊓ N` into `N`.

This is the factorisation underlying
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleHomOfLE_inf_comp_eq_zero`, which
draws from it that a class on `N` killed by the inclusion of `𝓘^m N` is killed by the inclusion
of `𝓘^n L ⊓ N`. The surjectivity chase needs the morphism itself, to *carry* a class from
`𝓘^m N` to `𝓘^n L ⊓ N` rather than to propagate a vanishing. -/
theorem exists_fac_submoduleHomOfLE_inf [IsNoetherian X] (I : X.IdealSheafData) {L : X.Modules}
    (N : L.Submodule) (hL : L.IsCoherent) (hN : (subMod N).IsQuasicoherent) (m : ℕ) :
    ∃ (n : ℕ) (_ : m ≤ n) (w : subMod (Stacks.Algebraization.idealPowerMultiple I n L ⊓ N) ⟶
        subMod (Stacks.Algebraization.idealPowerMultiple I m (subMod N))),
      w ≫ submoduleι (Stacks.Algebraization.idealPowerMultiple I m (subMod N)) =
        Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE (inf_le_right :
          Stacks.Algebraization.idealPowerMultiple I n L ⊓ N ≤ N) := by
  obtain ⟨c, hc, hAR⟩ := _root_.AlgebraicGeometry.exists_idealPowerSub_artinRees I L hL N hN
  have hle : Stacks.Algebraization.idealPowerMultiple I (m + c) L ⊓ N ≤
      _root_.AlgebraicGeometry.idealPowerSub I m N := by
    have h0 := hAR (m + c) (Nat.le_add_left c m)
    rwa [Nat.add_sub_cancel] at h0
  refine ⟨m + c, Nat.le_add_right m c,
    Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hle ≫
      (idealPowerSubIso I m N).inv, ?_⟩
  exact submoduleHomOfLE_comp_idealPowerSubIso_inv_comp_ι I m N hle

/-- **`𝓘^{n+m} 𝓖 ⊆ 𝓘^n P` for every submodule `P` of `𝓖` containing `𝓘^m 𝓖`.** Over an affine
open the sections of the left side are `𝓘(U)^n • (𝓘(U)^m • 𝓖(U))` and those of the right side
are `𝓘(U)^n • P(U)`, and `𝓘(U)^m • 𝓖(U)` is contained in `P(U)` by hypothesis.

It is what turns the third term `𝓘^n (Im ψ)` of the ideal-power sequence of the surjectivity
chase back into a member `𝓘^{n+m} 𝓖` of the ideal-power filtration of `𝓖`. -/
theorem idealPowerMultiple_le_idealPowerSub (I : X.IdealSheafData) (n m : ℕ) {G : X.Modules}
    (hG : G.IsQuasicoherent) (P : G.Submodule) (hP : (subMod P).IsQuasicoherent)
    (h : Stacks.Algebraization.idealPowerMultiple I m G ≤ P) :
    Stacks.Algebraization.idealPowerMultiple I (n + m) G ≤
      _root_.AlgebraicGeometry.idealPowerSub I n P := by
  rw [Stacks.Algebraization.idealPowerMultiple_le_iff]
  intro U
  have h2 : _root_.AlgebraicGeometry.secs (_root_.AlgebraicGeometry.idealPowerSub I n P) U.1 =
      I.ideal U ^ n • _root_.AlgebraicGeometry.secs P U.1 :=
    _root_.AlgebraicGeometry.idealPowerSub_obj_affine I n P hP U
  have h3 : I.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1)) ≤
      _root_.AlgebraicGeometry.secs P U.1 :=
    (Stacks.Algebraization.idealPowerMultiple_le_iff I m G P).1 h U
  have key : I.ideal U ^ (n + m) • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1)) ≤
      _root_.AlgebraicGeometry.secs (_root_.AlgebraicGeometry.idealPowerSub I n P) U.1 := by
    rw [h2, pow_add, Submodule.mul_smul]
    exact Submodule.smul_mono le_rfl h3
  exact key

/-- **A submodule contained in `𝓘^n P`, lifted into `𝓘^n (subMod P)` and read back inside the
ambient module, is itself.** This is what identifies the third term `𝓘^n (Im ψ)` of the
ideal-power sequence of the surjectivity chase, read inside `𝓖`, with a member of the
ideal-power filtration of `𝓖`. -/
theorem fac_idealPowerSub_lift {L : X.Modules} (I : X.IdealSheafData) (n : ℕ) (P : L.Submodule)
    {Q : L.Submodule} (hle : Q ≤ _root_.AlgebraicGeometry.idealPowerSub I n P) :
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hle ≫
          (idealPowerSubIso I n P).inv) ≫
        submoduleι (Stacks.Algebraization.idealPowerMultiple I n (subMod P)) ≫ submoduleι P =
      submoduleι Q :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t : subMod Q ⟶ subMod P => t ≫ submoduleι P)
        (submoduleHomOfLE_comp_idealPowerSubIso_inv_comp_ι I n P hle)).trans
      (submoduleHomOfLE_ι _))

end ArtinRees

section Chase

/-- **The surjectivity chase of [Stacks, Tag 0G2H], reduced to its degree-`i` induction
hypothesis.** Let `X` be a Noetherian scheme, `𝓘` a quasi-coherent sheaf of ideals,
`U = X ∖ V(𝓘)`, and `𝓖`, `𝓕` coherent `𝒪_X`-modules. For every class `η` in
`Ext^{i+1}_U(𝓖|_U, 𝓕|_U)` there are a coherent `𝒪_X`-module `𝓔`, a morphism `ψ : 𝓔 ⟶ 𝓖` whose
restriction to `U` is an epimorphism, an exponent `m` with `𝓘^m 𝓖 ⊆ Im ψ`, and a class `η'` in
`Ext^i_U((ker ψ)|_U, 𝓕|_U)` such that `η`, composed with the isomorphism `(Im ψ)|_U ≅ 𝓖|_U`, is
the boundary class of the restriction to `U` of `0 ⟶ ker ψ ⟶ 𝓔 ⟶ Im ψ ⟶ 0` applied to `η'`.
Both outer terms of that sequence are coherent.

This is the coherent effacement on `U`
(`Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_restrict_of_pos`) followed by its
extension across the open immersion with the containment it makes available
(`Stacks.ExtEffacement.exists_isCoherent_extension_idealPowerMultiple_le_imageSubmodule`), the
two sequences compared by `Stacks.ExtEffacement.restrictImageShortComplexHom` and the comparison
transported onto the boundary classes by `Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp`.

What the induction on `i` still has to do with the conclusion is apply the degree-`i`
surjectivity statement to the coherent module `ker ψ` and carry the class it produces on
`𝓘^n (ker ψ)` back up to `𝓘^{n+m} 𝓖`. -/
theorem exists_shortExact_extClass_comp_eq_restrict_image_of_pos [IsNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens) (hU : U = I.support.compl)
    [HasExt.{w} U.toScheme.Modules] {G F : X.Modules} [G.IsCoherent] [F.IsCoherent] {i : ℕ}
    (η : Ext.{w} ((Scheme.Modules.restrictFunctor U.ι).obj G)
      ((Scheme.Modules.restrictFunctor U.ι).obj F) (i + 1)) :
    ∃ (E : X.Modules) (_ : E.IsCoherent) (ψ : E ⟶ G)
      (_ : Epi ((Scheme.Modules.restrictFunctor U.ι).map ψ)) (m : ℕ)
      (_ : Stacks.Algebraization.idealPowerMultiple I m G ≤
        _root_.AlgebraicGeometry.imageSubmodule ψ)
      (_ : (subMod (_root_.AlgebraicGeometry.imageSubmodule ψ)).IsCoherent)
      (_ : (kerMod (toImageMod ψ)).IsCoherent)
      (η' : Ext.{w} ((Scheme.Modules.restrictFunctor U.ι).obj (kerMod (toImageMod ψ)))
        ((Scheme.Modules.restrictFunctor U.ι).obj F) i),
      (Ext.mk₀ ((Scheme.Modules.restrictFunctor U.ι).map
            (submoduleι (_root_.AlgebraicGeometry.imageSubmodule ψ)))).comp η (zero_add (i + 1)) =
        ((shortExact_toImageMod ψ).map_of_exact
          (Scheme.Modules.restrictFunctor U.ι)).extClass.comp η' (Nat.add_comm 1 i) := by
  obtain ⟨H, φ, hH, hφ, hkerφ, hSU, η₀, hη₀⟩ :=
    exists_shortExact_extClass_comp_eq_restrict_of_pos.{w} U (F := G) (G := F) η
  have := hH
  have := hφ
  obtain ⟨E, hE, ψ, e, m, he, hm⟩ :=
    exists_isCoherent_extension_idealPowerMultiple_le_imageSubmodule I U hU G H φ hφ
  have := hE
  have : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  have hψU : Epi ((Scheme.Modules.restrictFunctor U.ι).map ψ) := by
    rw [← he]; exact epi_comp _ _
  refine ⟨E, hE, ψ, hψU, m, hm, isCoherent_imageMod ψ, isCoherent_kerMod_toImageMod ψ,
    (Ext.mk₀ (restrictKerToKer U ψ φ e he)).comp η₀ (zero_add i), ?_⟩
  rw [← hη₀]
  exact mk₀_τ₃_comp_extClass_comp
    ((shortExact_toImageMod ψ).map_of_exact (Scheme.Modules.restrictFunctor U.ι)) hSU
    (restrictImageShortComplexHom U ψ φ e he) (Nat.add_comm 1 i) η₀

end Chase

section ChaseCore

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]

/-- `Stacks.ExtEffacement.mk₀_τ₃_comp_extClass_comp` with the three components of the morphism of
short exact sequences given separately, which is the shape the chase rewrites with. -/
theorem mk₀_comp_extClass_comp_of_comm {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂) (τ₃ : S₁.X₃ ⟶ S₂.X₃)
    (comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂) (comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃)
    {T : C} {i n : ℕ} (hn : 1 + i = n) (ξ' : Ext.{w} S₂.X₁ T i) :
    (Ext.mk₀ τ₃).comp (h₂.extClass.comp ξ' hn) (zero_add n) =
      h₁.extClass.comp ((Ext.mk₀ τ₁).comp ξ' (zero_add i)) hn :=
  mk₀_τ₃_comp_extClass_comp h₁ h₂ ⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₃⟩ hn ξ'

/-- **The surjectivity chase of [Stacks, Tag 0G2H], as an identity of `Ext`-classes.** -/
theorem mk₀_inv_comp_mapExactFunctor_extClass_comp (R : C ⥤ D) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂) (τ₃ : S₁.X₃ ⟶ S₂.X₃)
    (comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂) (comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃)
    {T Z P Y : C} {i : ℕ} (c : S₂.X₃ ⟶ Z) (p : S₁.X₁ ⟶ P) (q : P ⟶ S₂.X₁) (hpq : p ≫ q = τ₁)
    (b : Y ⟶ S₁.X₃) (d : Y ⟶ Z) (hb : b ≫ τ₃ ≫ c = d)
    (ε : R.obj Y ≅ R.obj Z) (hε : ε.hom = R.map d)
    (η : Ext.{w'} (R.obj Z) (R.obj T) (i + 1))
    (η' : Ext.{w'} (R.obj S₂.X₁) (R.obj T) i)
    (hη : (Ext.mk₀ (R.map c)).comp η (zero_add (i + 1)) =
      (h₂.map_of_exact R).extClass.comp η' (Nat.add_comm 1 i))
    (ξ : Ext.{w} P T i)
    (hξ : Ext.mapExactFunctor R ξ = (Ext.mk₀ (R.map q)).comp η' (zero_add i)) :
    (Ext.mk₀ ε.inv).comp (Ext.mapExactFunctor R
        ((Ext.mk₀ b).comp (h₁.extClass.comp ((Ext.mk₀ p).comp ξ (zero_add i))
          (Nat.add_comm 1 i)) (zero_add (i + 1)))) (zero_add (i + 1)) = η := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, hξ,
    mk₀_comp_mk₀_comp (R.map p) (R.map q) η', ← R.map_comp, hpq,
    ← mk₀_comp_extClass_comp_of_comm (h₁.map_of_exact R) (h₂.map_of_exact R)
      (R.map τ₁) (R.map τ₂) (R.map τ₃)
      (by simp only [ShortComplex.map_f, ← R.map_comp]; rw [comm₁₂])
      (by simp only [ShortComplex.map_g, ← R.map_comp]; rw [comm₂₃])
      (Nat.add_comm 1 i) η',
    ← hη, mk₀_comp_mk₀_comp (R.map τ₃) (R.map c) η, ← R.map_comp,
    mk₀_comp_mk₀_comp (R.map b) (R.map (τ₃ ≫ c)) η, ← R.map_comp, hb, ← hε,
    mk₀_comp_mk₀_comp ε.inv ε.hom η, ε.inv_hom_id, Ext.mk₀_id_comp]

end ChaseCore

section Induction

/-- **The induction step of the surjectivity chase of [Stacks, Tag 0G2H].** Let `X` be a
Noetherian scheme, `𝓘` a quasi-coherent sheaf of ideals, `U = X ∖ V(𝓘)`, and `𝓕` a coherent
`𝒪_X`-module. If every class in `Ext^i_U(𝓐|_U, 𝓕|_U)`, for `𝓐` coherent, is the image of a class
in `Ext^i_X(𝓘^k 𝓐, 𝓕)` for some `k`, then the same holds in degree `i + 1`.

The proof runs the chase:
`Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_restrict_image_of_pos` produces the
short exact sequence `0 ⟶ ker ψ ⟶ 𝓔 ⟶ Im ψ ⟶ 0` on `X` and a degree-`i` class on
`(ker ψ)|_U`; the hypothesis lifts that class to `𝓘^n (ker ψ)`; Artin-Rees
(`Stacks.ExtEffacement.exists_fac_submoduleHomOfLE_inf`) carries it onto the first term of the
ideal-power sequence `0 ⟶ ker(𝓘^N 𝓔 ⟶ 𝓘^N Im ψ) ⟶ 𝓘^N 𝓔 ⟶ 𝓘^N Im ψ ⟶ 0`; the boundary class of
that sequence produces a class on `𝓘^N Im ψ`; and
`Stacks.ExtEffacement.idealPowerMultiple_le_idealPowerSub` reads `𝓘^{N+m} 𝓖` inside it. That the
result restricts to `η` is
`Stacks.ExtEffacement.mk₀_inv_comp_mapExactFunctor_extClass_comp`. -/
theorem exists_extIdealPowRestrict_eq_of_succ [IsNoetherian X] [HasExt.{w} X.Modules]
    (I : X.IdealSheafData) (U : X.Opens) (hU : U = I.support.compl)
    [HasExt.{w'} U.toScheme.Modules] (F : X.Modules) [F.IsCoherent] {i : ℕ}
    (ih : ∀ A : X.Modules, A.IsCoherent →
      ∀ θ : Ext.{w'} ((Scheme.Modules.restrictFunctor U.ι).obj A)
        ((Scheme.Modules.restrictFunctor U.ι).obj F) i,
        ∃ (k : ℕ) (ζ : Ext.{w} (idealPowSmul I k A) F i),
          extIdealPowRestrict.{w, w'} I U (disjoint_support_of_eq_supportCompl hU) ζ = θ)
    (G : X.Modules) [G.IsCoherent]
    (η : Ext.{w'} ((Scheme.Modules.restrictFunctor U.ι).obj G)
      ((Scheme.Modules.restrictFunctor U.ι).obj F) (i + 1)) :
    ∃ (k : ℕ) (ξ : Ext.{w} (idealPowSmul I k G) F (i + 1)),
      extIdealPowRestrict.{w, w'} I U (disjoint_support_of_eq_supportCompl hU) ξ = η := by
  obtain ⟨E, hE, ψ, hψU, m, hm, hImCoh, hKerCoh, η', hη'⟩ :=
    exists_shortExact_extClass_comp_eq_restrict_image_of_pos I U hU η
  have := hE
  have hEq : E.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent E
  have hGq : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  have hAq : (subMod (_root_.AlgebraicGeometry.imageSubmodule ψ)).IsQuasicoherent :=
    _root_.AlgebraicGeometry.isQuasicoherent_imageSubmodule ψ
  have hKq : (kerMod (toImageMod ψ)).IsQuasicoherent := isQuasicoherent_kerMod (toImageMod ψ)
  obtain ⟨n, ξ₁, hξ₁⟩ := ih (kerMod (toImageMod ψ)) hKerCoh η'
  obtain ⟨N, _, w, hw⟩ :=
    exists_fac_submoduleHomOfLE_inf I (SheafOfModules.Submodule.ker (toImageMod ψ)) hE hKq n
  have hα : Epi (toImageMod ψ) := epi_toImageMod ψ
  have hξ₁' := eq_mk₀_hom_comp
    (restrictIdealPowSmulIso I U (disjoint_support_of_eq_supportCompl hU) n
      (kerMod (toImageMod ψ))) (extRestrict.{w, w'} U ξ₁) η' hξ₁
  have hle : Stacks.Algebraization.idealPowerMultiple I (N + m) G ≤
      _root_.AlgebraicGeometry.idealPowerSub I N (_root_.AlgebraicGeometry.imageSubmodule ψ) :=
    idealPowerMultiple_le_idealPowerSub I N m hGq _ hAq hm
  have hv : (kerIdealPowerEpiLift I N hEq hAq (toImageMod ψ) hα ≫ w) ≫
      submoduleι (Stacks.Algebraization.idealPowerMultiple I n (kerMod (toImageMod ψ))) =
      kerIdealPowerEpiToKer I N hEq hAq (toImageMod ψ) hα :=
    (Category.assoc _ _ _).trans
      (congrArg (fun s : subMod (Stacks.Algebraization.idealPowerMultiple I N E ⊓
            SheafOfModules.Submodule.ker (toImageMod ψ)) ⟶ kerMod (toImageMod ψ) =>
          kerIdealPowerEpiLift I N hEq hAq (toImageMod ψ) hα ≫ s) hw)
  refine ⟨N + m, (Ext.mk₀ (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hle ≫
      (idealPowerSubIso I N (_root_.AlgebraicGeometry.imageSubmodule ψ)).inv)).comp
      ((shortExact_idealPowerEpi I N hEq hAq (toImageMod ψ) hα).extClass.comp
        ((Ext.mk₀ (kerIdealPowerEpiLift I N hEq hAq (toImageMod ψ) hα ≫ w)).comp ξ₁
          (zero_add i)) (Nat.add_comm 1 i)) (zero_add (i + 1)), ?_⟩
  exact mk₀_inv_comp_mapExactFunctor_extClass_comp (Scheme.Modules.restrictFunctor U.ι)
    (shortExact_idealPowerEpi I N hEq hAq (toImageMod ψ) hα) (shortExact_toImageMod ψ)
    (kerIdealPowerEpiToKer I N hEq hAq (toImageMod ψ) hα)
    (submoduleι (Stacks.Algebraization.idealPowerMultiple I N E))
    (submoduleι (Stacks.Algebraization.idealPowerMultiple I N
      (subMod (_root_.AlgebraicGeometry.imageSubmodule ψ))))
    (kerIdealPowerEpiToKer_comp I N hEq hAq (toImageMod ψ) hα)
    (idealPowerEpi_comp_submoduleι I N hEq hAq (toImageMod ψ) hα).symm
    (submoduleι (_root_.AlgebraicGeometry.imageSubmodule ψ))
    (kerIdealPowerEpiLift I N hEq hAq (toImageMod ψ) hα ≫ w)
    (submoduleι (Stacks.Algebraization.idealPowerMultiple I n (kerMod (toImageMod ψ)))) hv
    (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE hle ≫
      (idealPowerSubIso I N (_root_.AlgebraicGeometry.imageSubmodule ψ)).inv)
    (submoduleι (Stacks.Algebraization.idealPowerMultiple I (N + m) G))
    (fac_idealPowerSub_lift I N (_root_.AlgebraicGeometry.imageSubmodule ψ) hle)
    (restrictIdealPowSmulIso I U (disjoint_support_of_eq_supportCompl hU) (N + m) G) rfl
    η η' hη' ξ₁ hξ₁'

/-- **Surjectivity of the canonical map `Ext^i_X(𝓘^n 𝓖, 𝓕) ⟶ Ext^i_U(𝓖|_U, 𝓕|_U)` in every
degree**, for coherent `𝓖` and `𝓕` on a Noetherian scheme and `U = X ∖ V(𝓘)`: every class on `U`
is the restriction of a class at some stage `n` of the ideal-power filtration.

This is the surjectivity half of the core case of [Stacks, Tag 0G2H]. The base case is the first
display of [Stacks, Tag 01YB],
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_extIdealPowRestrict_eq`, and the induction
step is `Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_succ`. -/
theorem exists_extIdealPowRestrict_eq_of_isCoherent [IsNoetherian X] [HasExt.{w} X.Modules]
    (I : X.IdealSheafData) (U : X.Opens) (hU : U = I.support.compl)
    [HasExt.{w'} U.toScheme.Modules] (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    ∀ G : X.Modules, G.IsCoherent →
      ∀ η : Ext.{w'} ((Scheme.Modules.restrictFunctor U.ι).obj G)
        ((Scheme.Modules.restrictFunctor U.ι).obj F) i,
        ∃ (k : ℕ) (ξ : Ext.{w} (idealPowSmul I k G) F i),
          extIdealPowRestrict.{w, w'} I U (disjoint_support_of_eq_supportCompl hU) ξ = η := by
  induction i with
  | zero =>
      intro G hG η
      have := hG
      have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
      exact exists_extIdealPowRestrict_eq I U hU G F η
  | succ i ih =>
      intro G hG η
      have := hG
      exact exists_extIdealPowRestrict_eq_of_succ I U hU F ih G η

end Induction

end Stacks.ExtEffacement

end
