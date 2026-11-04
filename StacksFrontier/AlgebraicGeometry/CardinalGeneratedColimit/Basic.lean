module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.GabberColimit.Basic
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.GabberDirected
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local

/-!
# Stacks 077N: a quasi-coherent module is the directed colimit of its bounded subobjects

Gabber's theorem (Stacks 077N) labels three assertions: a cardinal `κ` attached to a scheme
`X`, the directedness of the category of quasi-coherent `κ`-generated subobjects of a
quasi-coherent `𝒪_X`-module `F`, and the statement that the canonical cocone of that category
is colimiting. The first two are formalized, as
`Stacks.AlgebraicGeometry.CardinalGeneration.cardinalBound` and
`Stacks.AlgebraicGeometry.CardinalGeneration.cardinalGeneratedQuasicoherentSubobject_isFiltered`.
This file proves the third.

## Main results

* `isColimit_cardinalGeneratedQuasicoherentSubobjectCocone`, in the namespace
  `Stacks.AlgebraicGeometry.CardinalGeneration`: the colimit assertion of Stacks 077N.
* `Stacks.AlgebraicGeometry.CardinalGeneration.isColimit_cocone_of_locally_mem`: its reduction
  to the statement that every section of `F` is a section of some bounded quasi-coherent
  subobject.
* `Stacks.AlgebraicGeometry.CardinalGeneration.gsOfSpanningFamily`: on an affine open, a family
  of sections spanning `Γ(F, U)` over `Γ(X, U)` generates the restriction `F|_U`, with the same
  index type.
* `Stacks.AlgebraicGeometry.GabberColimit.isQuasicoherent_sheafSubmodule`: the subsheaf cut out
  by a compatible family of submodules of the sections over the affine opens is quasi-coherent.
* `Stacks.AlgebraicGeometry.CardinalGeneration.isCardinalGenerated_sheafSubmodule`: that
  subsheaf is `κ`-generated when the family is a family of `κ`-bounded spans.

## Route

The categorical step is Mathlib's
`CategoryTheory.IsGrothendieckAbelian.mono_of_isColimit_monoOver`: in a Grothendieck abelian
category, the comparison map out of the colimit of a filtered diagram of subobjects is a
monomorphism. `AlgebraicGeometry.Scheme.Modules` is Grothendieck abelian, so for the diagram of
bounded quasi-coherent subobjects the comparison map `colim G ⟶ F` is a monomorphism, and
`isIso_of_mono_of_locallySurjective` upgrades it to an isomorphism as soon as it is locally
surjective on sections. That reduces the colimit assertion to: every section of `F` over an
open `U` is in the image of the sections of some bounded quasi-coherent subobject
(`isColimit_cocone_of_locally_mem`).

The index category is only essentially small — `AlgebraicGeometry.Scheme.Modules` is
well-powered, but its subobjects do not form a `Type u` — whereas Mathlib's lemma wants a
`SmallCategory`. The diagram is therefore replaced by its small model, with
`CategoryTheory.Limits.IsColimit.ofWhiskerEquivalence` transporting the conclusion back.

The content of the local-membership statement is the saturation construction of
`Stacks.AlgebraicGeometry.GabberColimit`. Given a section `s` over `U`, the family
`S W = {s|_W}` for affine `W ≤ U` is saturated by `exists_bounded_compatible_family` into a
compatible family `T` of `κ`-bounded sets, and `sheafSubmodule` turns the spans of `T` into a
subsheaf of `F` containing `s`. Its quasi-coherence is `isQuasicoherent_sheafSubmodule`, and
the bound on its local generators is `isCardinalGenerated_sheafSubmodule`.

Of the three adequacy bounds proved beside `cardinalBound`, this route uses two:
`aleph0_le_cardinalBound` and `mk_affineOpens_le_cardinalBound`, both as hypotheses of
`exists_bounded_compatible_family`. It does **not** use `mk_sections_le_cardinalBound`: the
saturation enlarges each `S W` only by the finitely many sections that
`GabberColimit.exists_finite_subset_span` extracts for each pair of affine opens, so the bound
`aleph0 * mk X.affineOpens ≤ κ` suffices and the cardinality of the rings of sections never
enters. The directedness assertion, by contrast, uses only `aleph0_le_cardinalBound`.

## Implementation notes

Several instances have to be supplied positionally. `AlgebraicGeometry.Scheme.Modules` is a
`def` for `SheafOfModules X.ringCatSheaf` carrying its own `Category` instance, so the
`Mono`/`Epi` instances proved for `SheafOfModules` are not found through it; `Scheme.Modules` is
made `instance_reducible` in the final section for that reason, and the monomorphism of the
submodule inclusion is still produced by hand through
`AlgebraicGeometry.Scheme.Modules.toPresheafOfModules`. `CategoryTheory.Subobject.mk` and
`CategoryTheory.Subobject.underlyingIso` take their `Mono` as an instance argument and are
applied with `@`. `Mono` and `IsIso` obtained by `have` are likewise passed positionally rather
than left to instance search.

A projection written after a line break does not parse: `(sheafSubmodule F N hN)` followed by
`.toSheafOfModules` on the next line is read as a function application, so
`SheafOfModules.Submodule.toSheafOfModules` is spelled out where the line would be too long.

`Stacks.AlgebraicGeometry.GabberColimit.compatibleModule` retypes the subsheaf in `X.Modules`,
and `mkSection`/`valSection` pin the definitional identification of its sections with the
sections of `F` lying locally in the family; without them the anonymous constructor does not
elaborate, exactly as recorded for the torsion subsheaf in
`StacksFrontier/AlgebraicGeometry/TorsionQuasicoherent/Basic.lean`.

## What is not done

No stacks attribute for 077N is attached by this file: the covering set spans three files,
and the placement is left to the maintainer.

## References

* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
* [Stacks Project, Tag 077L](https://stacks.math.columbia.edu/tag/077L)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

universe u

section Generators

open CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE Stacks.AlgebraicGeometry.CoherentFinite

namespace Stacks.AlgebraicGeometry.CardinalGeneration

/-- The image of a spanning family under a linear equivalence is a spanning family. -/
theorem span_range_linearEquiv_symm_eq_top {R A B : Type*} [CommRing R] [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) {ι : Type*} (t : ι → B)
    (ht : Submodule.span R (Set.range t) = ⊤) :
    Submodule.span R (Set.range fun i => e.symm (t i)) = ⊤ := by
  have himg : (Set.range fun i => e.symm (t i)) = (e.symm : B →ₗ[R] A) '' Set.range t :=
    Set.range_comp (e.symm : B →ₗ[R] A) t
  rw [himg, Submodule.span_image, ht, Submodule.map_top, LinearEquiv.range]

variable {X : Scheme.{u}}

/-- **A family of sections spanning `Γ(M, U)` over `Γ(X, U)` generates `M|_U`**, for `U` an
affine open and `M` quasi-coherent. The index type of the resulting generating sections is the
index type of the given family. -/
def gsOfSpanningFamily (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    {ι : Type u} (t : ι → Γ(M, U)) (ht : Submodule.span Γ(X, U) (Set.range t) = ⊤) :
    (M.restrict U.ι).GeneratingSections :=
  GeneratingSections.equivOfIso (restrictIsoSpecTilde M hU).symm
    (generatingSectionsPullbackTilde hU.isoSpec.hom (specModule M hU)
      (tildeGeneratingSections (specModule M hU)
        (fun i => (specSectionsEquiv M hU).symm (t i))
        (span_range_linearEquiv_symm_eq_top (specSectionsEquiv M hU) t ht)))

/-- The generating sections `gsOfSpanningFamily M hU t ht` are indexed by the index type `ι`
of the family `t`. -/
@[simp]
theorem gsOfSpanningFamily_I (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {ι : Type u} (t : ι → Γ(M, U))
    (ht : Submodule.span Γ(X, U) (Set.range t) = ⊤) :
    (gsOfSpanningFamily M hU t ht).I = ι :=
  rfl

/-- **A set of sections spanning `Γ(M, U)` over `Γ(X, U)` gives generating sections of `M|_U`
indexed by that set**, for `U` an affine open and `M` quasi-coherent. -/
theorem exists_generatingSections_of_span_eq_top (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (T : Set Γ(M, U))
    (hT : Submodule.span Γ(X, U) T = ⊤) :
    ∃ σ : (M.restrict U.ι).GeneratingSections, Cardinal.mk σ.I ≤ Cardinal.mk T :=
  ⟨gsOfSpanningFamily M hU (fun x : T => (x : Γ(M, U))) (by rwa [Subtype.range_coe]),
    le_refl (Cardinal.mk T)⟩

/-- A sigma type indexed by a set of size at most `κ`, with fibres of size at most `κ`, has size
at most `κ`, for `κ` infinite.  Mathlib has `Cardinal.mk_sigma` computing `#(Σ i, β i)` as a sum
but no `≤` form under these hypotheses. -/
theorem mk_sigma_le {ι : Type u} {β : ι → Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hι : Cardinal.mk ι ≤ κ) (hβ : ∀ i, Cardinal.mk (β i) ≤ κ) :
    Cardinal.mk (Σ i, β i) ≤ κ := by
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_sum _ (fun _ => κ) hβ).trans ?_
  rw [Cardinal.sum_const']
  calc Cardinal.mk ι * κ ≤ κ * κ := mul_le_mul' hι le_rfl
    _ = κ := Cardinal.mul_eq_self hκ

end Stacks.AlgebraicGeometry.CardinalGeneration

end Generators

section Quasicoherence

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionQuasicoherent

namespace Stacks.AlgebraicGeometry.GabberColimit

/-- Multiplication by `r` is a unit of `Module.End R M` as soon as `r` acts on `M` through a
unit `b` of a second ring of scalars. -/
private theorem isUnit_algebraMap_end_of_smul_eq {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [Module S M] {r : R} {b : S} (hb : IsUnit b)
    (hsmul : ∀ m : M, r • m = b • m) :
    IsUnit (algebraMap R (Module.End R M) r) := by
  obtain ⟨u, rfl⟩ := hb
  refine (Module.End.isUnit_iff _).mpr ⟨fun m₁ m₂ hm ↦ ?_, fun m ↦ ⟨(↑u⁻¹ : S) • m, ?_⟩⟩
  · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, hsmul, hsmul] at hm
    calc m₁ = ((↑u⁻¹ : S) * (u : S)) • m₁ := by rw [u.inv_mul, one_smul]
      _ = ((↑u⁻¹ : S) * (u : S)) • m₂ := by rw [mul_smul, mul_smul, hm]
      _ = m₂ := by rw [u.inv_mul, one_smul]
  · rw [Module.algebraMap_end_apply, hsmul, smul_smul, u.mul_inv, one_smul]

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
  (N : ∀ U : X.affineOpens, Submodule Γ(X, U.1) Γ(F, U.1)) (hN : IsCompatible F N)

/-- The subsheaf of `F` cut out by a compatible family, bundled as an `𝒪_X`-module. -/
def compatibleModule : X.Modules :=
  (sheafSubmodule F N hN).toSheafOfModules

/-- A section of `F` lying locally in `N`, viewed as a section of the subsheaf it cuts out. -/
def mkSection {W : X.Opens} (s : Γ(F, W)) (hs : IsLocallyIn F N s) :
    Γ(compatibleModule F N hN, W) :=
  show ↥(localSections F N W) from ⟨s, hs⟩

/-- The underlying section of `F` of a section of the subsheaf cut out by `N`. -/
def valSection {W : X.Opens} (z : Γ(compatibleModule F N hN, W)) : Γ(F, W) :=
  z.1

/-- A section of the subsheaf cut out by `N` lies locally in `N`. -/
theorem isLocallyIn_valSection {W : X.Opens} (z : Γ(compatibleModule F N hN, W)) :
    IsLocallyIn F N (valSection F N hN z) :=
  z.2

/-- Sections of the subsheaf cut out by `N` are determined by the underlying sections of `F`. -/
theorem valSection_inj {W : X.Opens} {z₁ z₂ : Γ(compatibleModule F N hN, W)}
    (h : valSection F N hN z₁ = valSection F N hN z₂) : z₁ = z₂ :=
  Subtype.ext h

/-- Equal sections of the subsheaf cut out by `N` have equal underlying sections of `F`. -/
theorem valSection_eq {W : X.Opens} {z₁ z₂ : Γ(compatibleModule F N hN, W)} (h : z₁ = z₂) :
    valSection F N hN z₁ = valSection F N hN z₂ := by
  rw [h]

/-- Taking the underlying section of `F` commutes with scalar multiplication. -/
@[simp]
theorem valSection_smul {W : X.Opens} (r : Γ(X, W)) (z : Γ(compatibleModule F N hN, W)) :
    valSection F N hN (r • z) = r • valSection F N hN z :=
  rfl

/-- The underlying section of `F` of the zero section is zero. -/
@[simp]
theorem valSection_zero {W : X.Opens} :
    valSection F N hN (0 : Γ(compatibleModule F N hN, W)) = (0 : Γ(F, W)) :=
  rfl

include hN in
/-- Over an affine open, lying locally in `N` is membership in `N`. This is
`obj_sheafSubmodule` read on elements. -/
theorem isLocallyIn_iff_mem (W : X.affineOpens) (s : Γ(F, W.1)) :
    IsLocallyIn F N s ↔ s ∈ N W :=
  SetLike.ext_iff.mp (obj_sheafSubmodule F N hN W) s

/-- **The sections of the subsheaf cut out by a compatible family localize.** For an affine
open `U` and `a : Γ(X, U)`, the sections over `X.basicOpen a` are the localization away from
`a` of the sections over `U`. -/
theorem isLocalizedModule_compatibleModule {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) :
    letI := moduleOfLE (compatibleModule F N hN) (X.basicOpen_le a)
    IsLocalizedModule.Away a (restrictₗ (compatibleModule F N hN) (X.basicOpen_le a)) := by
  let _mG := moduleOfLE (compatibleModule F N hN) (X.basicOpen_le a)
  let _mF := moduleOfLE F (X.basicOpen_le a)
  have _st : IsScalarTower Γ(X, U) Γ(X, X.basicOpen a) Γ(F, X.basicOpen a) :=
    isScalarTowerOfLE F (X.basicOpen_le a)
  have _il : IsLocalization.Away a Γ(X, X.basicOpen a) := hU.isLocalization_basicOpen a
  have _lF : IsLocalizedModule.Away a (restrictₗ F (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ F hU a rfl (X.basicOpen_le a)
  have hb : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
    X.toRingedSpace.isUnit_res_basicOpen a
  have key : Submodule.localized₀ (Submonoid.powers a) (restrictₗ F (X.basicOpen_le a))
      (N ⟨U, hU⟩) =
      (N ⟨X.basicOpen a, hU.basicOpen a⟩).restrictScalars Γ(X, U) := by
    have h1 : Submodule.localized' Γ(X, X.basicOpen a) (Submonoid.powers a)
        (restrictₗ F (X.basicOpen_le a)) (N ⟨U, hU⟩) =
        N ⟨X.basicOpen a, hU.basicOpen a⟩ := by
      rw [Submodule.localized'_eq_span,
        hN ⟨U, hU⟩ ⟨X.basicOpen a, hU.basicOpen a⟩ (X.basicOpen_le a)]
      rfl
    rw [← Submodule.restrictScalars_localized' Γ(X, X.basicOpen a), h1]
  refine IsLocalizedModule.Away.mk_of_addCommGroup
    (isUnit_algebraMap_end_of_smul_eq hb fun _ ↦ rfl) ?_ ?_
  · intro y
    have hy : valSection F N hN y ∈ Submodule.localized₀ (Submonoid.powers a)
        (restrictₗ F (X.basicOpen_le a)) (N ⟨U, hU⟩) := by
      rw [key, Submodule.restrictScalars_mem]
      exact (isLocallyIn_iff_mem F N hN ⟨X.basicOpen a, hU.basicOpen a⟩ _).mp
        (isLocallyIn_valSection F N hN y)
    rw [Submodule.mem_localized₀] at hy
    obtain ⟨m, hm, s, hmk⟩ := hy
    obtain ⟨n, hn⟩ : ∃ n : ℕ, a ^ n = (s : Γ(X, U)) := s.2
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← hn] at hmk
    exact ⟨n, mkSection F N hN m ((isLocallyIn_iff_mem F N hN ⟨U, hU⟩ m).mpr hm),
      valSection_inj F N hN hmk.symm⟩
  · intro z hz
    have h0 : restrictₗ F (X.basicOpen_le a) (valSection F N hN z) =
        restrictₗ F (X.basicOpen_le a) (0 : Γ(F, U)) := by
      rw [map_zero]
      exact valSection_eq F N hN hz
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq a h0
    refine ⟨n, valSection_inj F N hN ?_⟩
    rw [valSection_smul, hn, smul_zero, valSection_zero]

/-- **The subsheaf of a quasi-coherent module cut out by a compatible family of submodules of
its sections over the affine opens is quasi-coherent.** -/
theorem isQuasicoherent_sheafSubmodule :
    (sheafSubmodule F N hN).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_of_isLocalizedModule_restrictₗ (compatibleModule F N hN)
    fun _ hU a ↦ isLocalizedModule_compatibleModule F N hN hU a

end Stacks.AlgebraicGeometry.GabberColimit

end Quasicoherence

section Colimit

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.CardinalGeneration

namespace Stacks.AlgebraicGeometry.CardinalGeneration

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules) (κ : Cardinal.{u})

/-- The diagram of `κ`-generated quasi-coherent subobjects of `F`, read in `MonoOver F`. -/
public def monoOverDiagram : CardinalGeneratedQuasicoherentSubobject F κ ⥤ MonoOver F :=
  (cardinalGeneratedQuasicoherentSubobjectProperty F κ).ι ⋙ Subobject.representative

/-- The index category replaced by a `Type u`-small model of it. -/
public abbrev smallIndexEquiv :
    SmallModel (CardinalGeneratedQuasicoherentSubobject F κ) ≌
      CardinalGeneratedQuasicoherentSubobject F κ :=
  (equivSmallModel (CardinalGeneratedQuasicoherentSubobject F κ)).symm

/-- The `MonoOver F`-valued diagram over the small model. -/
public def smallMonoOverDiagram :
    SmallModel (CardinalGeneratedQuasicoherentSubobject F κ) ⥤ MonoOver F :=
  (smallIndexEquiv F κ).functor ⋙ monoOverDiagram F κ

/-- The small model of the index category is filtered. -/
public theorem isFiltered_smallModel
    [IsFiltered (CardinalGeneratedQuasicoherentSubobject F κ)] :
    IsFiltered (SmallModel (CardinalGeneratedQuasicoherentSubobject F κ)) :=
  IsFiltered.of_equivalence (equivSmallModel (CardinalGeneratedQuasicoherentSubobject F κ))

/-- The `MonoOver F`-valued diagram over the small model composes with the two forgetful
functors to the whiskered diagram of underlying modules. The equality is definitional, and it
is what lets `CategoryTheory.IsGrothendieckAbelian.mono_of_isColimit_monoOver` be applied to
the colimit cocone of the whiskered diagram. -/
public theorem smallMonoOverDiagram_forget :
    smallMonoOverDiagram F κ ⋙ MonoOver.forget F ⋙ Over.forget F =
      (smallIndexEquiv F κ).functor ⋙
        cardinalGeneratedQuasicoherentSubobjectFunctor F κ := rfl

/-- **The colimit assertion reduced to local membership.** The canonical cocone of the
`κ`-generated quasi-coherent subobjects of `F` is colimiting as soon as every section of `F` is,
locally around each point, a section of one of those subobjects. -/
public def isColimit_cocone_of_locally_mem
    [IsFiltered (CardinalGeneratedQuasicoherentSubobject F κ)]
    (h : ∀ (U : X.Opens) (s : Γ(F, U)) (x : X), x ∈ U →
      ∃ V : X.Opens, ∃ hVU : V ≤ U, x ∈ V ∧
        ∃ G : CardinalGeneratedQuasicoherentSubobject F κ,
          F.presheaf.map (homOfLE hVU).op s ∈ Set.range (G.obj.arrow.app V)) :
    IsColimit (cardinalGeneratedQuasicoherentSubobjectCocone F κ) := by
  have hfil := isFiltered_smallModel F κ
  refine IsColimit.ofWhiskerEquivalence (smallIndexEquiv F κ) ?_
  let Dm := smallMonoOverDiagram F κ ⋙ MonoOver.forget F ⋙ Over.forget F
  let cm : Cocone Dm :=
    (cardinalGeneratedQuasicoherentSubobjectCocone F κ).whisker (smallIndexEquiv F κ).functor
  let f : colimit Dm ⟶ F := colimit.desc Dm cm
  have hf : ∀ j, colimit.ι Dm j ≫ f = ((smallMonoOverDiagram F κ).obj j).obj.hom :=
    fun j => colimit.ι_desc cm j
  have hmono : Mono f :=
    IsGrothendieckAbelian.mono_of_isColimit_monoOver (smallMonoOverDiagram F κ)
      (colimit.isColimit Dm) f hf
  have hiso : IsIso f :=
    @isIso_of_mono_of_locallySurjective X _ _ f hmono (by
      intro U s x hx
      obtain ⟨V, hVU, hxV, G, t, ht⟩ := h U s x hx
      refine ⟨V, hVU, hxV, ?_⟩
      let j := (equivSmallModel (CardinalGeneratedQuasicoherentSubobject F κ)).functor.obj G
      let α : G ⟶ (smallIndexEquiv F κ).functor.obj j :=
        (equivSmallModel (CardinalGeneratedQuasicoherentSubobject F κ)).unitIso.hom.app G
      let g : (Subobject.underlying.obj G.obj) ⟶ Dm.obj j :=
        Subobject.underlying.map ((cardinalGeneratedQuasicoherentSubobjectProperty F κ).ι.map α)
      have e1 : (g ≫ colimit.ι Dm j) ≫ f = G.obj.arrow := by
        rw [Category.assoc, hf j]
        exact Subobject.underlying_arrow _
      refine ⟨(g ≫ colimit.ι Dm j).app V t, ?_⟩
      have e2 := congrArg (fun m : (Subobject.underlying.obj G.obj) ⟶ F => m.app V t) e1
      simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using e2.trans ht)
  exact IsColimit.ofIsoColimit (colimit.isColimit Dm)
    (Cocone.ext (@asIso _ _ _ _ f hiso) fun j => colimit.ι_desc cm j)

/-- Cardinal generation is transported along an isomorphism of modules. -/
public theorem isCardinalGenerated_of_iso {M M' : X.Modules} (e : M ≅ M') :
    IsCardinalGenerated (R := X.ringCatSheaf) M κ →
      IsCardinalGenerated (R := X.ringCatSheaf) M' κ := by
  intro hM
  obtain ⟨I, Uc, hU, σ, hσ⟩ := exists_restrict_generatingSections M hM
  refine isCardinalGenerated_of_restrict M' Uc hU
    (fun i => gsComp (σ i) ((Scheme.Modules.restrictFunctor (Uc i).ι).map e.hom)
      (epi_restrictFunctor_map (Uc i).ι e.hom (CategoryTheory.IsIso.epi_of_iso e.hom)))
    hσ

/-- A compatible family in which a given section lies locally produces an object of the
category of `κ`-generated quasi-coherent subobjects whose sections hit that section. -/
public theorem exists_subobject_of_isLocallyIn [F.IsQuasicoherent]
    (N : ∀ U : X.affineOpens, Submodule Γ(X, U.1) Γ(F, U.1))
    (hN : GabberColimit.IsCompatible F N)
    (hq : (GabberColimit.sheafSubmodule F N hN).toSheafOfModules.IsQuasicoherent)
    (hg : IsCardinalGenerated (R := X.ringCatSheaf)
      (GabberColimit.sheafSubmodule F N hN).toSheafOfModules κ)
    (U : X.Opens) (s : Γ(F, U)) (hs : GabberColimit.IsLocallyIn F N s) :
    ∃ G : CardinalGeneratedQuasicoherentSubobject F κ, s ∈ Set.range (G.obj.arrow.app U) := by
  let M : X.Modules := (GabberColimit.sheafSubmodule F N hN).toSheafOfModules
  let jj : M ⟶ F := (GabberColimit.sheafSubmodule F N hN).ι
  have hm : Mono jj :=
    (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map
      (inferInstanceAs (Mono (GabberColimit.sheafSubmodule F N hN).toSubmodule.ι))
  have hiso : M ≅ ((@Subobject.mk _ _ _ _ jj hm : Subobject F) : X.Modules) :=
    (@Subobject.underlyingIso _ _ _ _ jj hm).symm
  refine ⟨⟨@Subobject.mk _ _ _ _ jj hm,
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso hiso hq,
    isCardinalGenerated_of_iso κ hiso hg⟩, ?_⟩
  have e1 : (@Subobject.underlyingIso _ _ _ _ jj hm).inv ≫
      (@Subobject.mk _ _ _ _ jj hm).arrow = jj :=
    @Subobject.underlyingIso_arrow _ _ _ _ jj hm
  have e3 : jj.app U (show Γ(M, U) from ⟨s, hs⟩) = s := rfl
  refine ⟨(@Subobject.underlyingIso _ _ _ _ jj hm).inv.app U
    (show Γ(M, U) from ⟨s, hs⟩), ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app]
  exact (congrArg (fun m : M ⟶ F => m.app U (show Γ(M, U) from ⟨s, hs⟩)) e1).trans e3

/-! ### The compatible family attached to one section -/

/-- **A compatible family of bounded submodules containing a prescribed section.** For an
infinite `κ` dominating the number of affine opens, every section of `F` over an open `U` lies
locally in a compatible family of `κ`-bounded spans. -/
public theorem exists_isCompatible_isLocallyIn [F.IsQuasicoherent]
    (hκ : Cardinal.aleph0 ≤ κ) (hX : Cardinal.mk X.affineOpens ≤ κ)
    (U : X.Opens) (s : Γ(F, U)) :
    ∃ T : ∀ W : X.affineOpens, Set Γ(F, W.1),
      (∀ W, Cardinal.mk (T W) ≤ κ) ∧
      GabberColimit.IsCompatible F (fun W => Submodule.span Γ(X, W.1) (T W)) ∧
      GabberColimit.IsLocallyIn F (fun W => Submodule.span Γ(X, W.1) (T W)) s := by
  classical
  set S : ∀ W : X.affineOpens, Set Γ(F, W.1) :=
    fun W => {t | ∃ h : W.1 ≤ U, t = F.presheaf.map (homOfLE h).op s} with hS
  have hSb : ∀ W, Cardinal.mk (S W) ≤ κ := by
    intro W
    refine le_trans (Cardinal.mk_le_one_iff_set_subsingleton.mpr ?_)
      (Cardinal.one_le_aleph0.trans hκ)
    rintro a ⟨ha, rfl⟩ b ⟨hb, rfl⟩
    rfl
  obtain ⟨T, hST, hTb, hTspan⟩ :=
    GabberColimit.exists_bounded_compatible_family F hκ hX S hSb
  refine ⟨T, hTb, GabberColimit.isCompatible_span F T hTspan, fun W h => ?_⟩
  exact Submodule.subset_span (hST W ⟨h, rfl⟩)

/-! ### The bound on the local generators -/

/-- Sections of the subsheaf cut out by a compatible family, over an affine open, are spanned
by the chosen generators of the family read as sections of the subsheaf. -/
public theorem span_mkSection_eq_top [F.IsQuasicoherent]
    (N : ∀ W : X.affineOpens, Submodule Γ(X, W.1) Γ(F, W.1))
    (hN : GabberColimit.IsCompatible F N) (W : X.affineOpens) {ι : Type u}
    (t : ι → Γ(F, W.1)) (hspan : Submodule.span Γ(X, W.1) (Set.range t) = N W)
    (hmem : ∀ i, GabberColimit.IsLocallyIn F N (t i)) :
    Submodule.span Γ(X, W.1)
      (Set.range fun i => GabberColimit.mkSection F N hN (t i) (hmem i)) = ⊤ := by
  let L : Γ(GabberColimit.compatibleModule F N hN, W.1) →ₗ[Γ(X, W.1)] Γ(F, W.1) :=
    { toFun := fun y => GabberColimit.valSection F N hN y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hLinj : Function.Injective L := fun _ _ hab => GabberColimit.valSection_inj F N hN hab
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  have hsub : N W ≤ Submodule.map L (Submodule.span Γ(X, W.1)
      (Set.range fun i => GabberColimit.mkSection F N hN (t i) (hmem i))) := by
    rw [← hspan]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨i, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  have hz : L z ∈ N W :=
    (GabberColimit.isLocallyIn_iff_mem F N hN W _).mp
      (GabberColimit.isLocallyIn_valSection F N hN z)
  obtain ⟨q, hq, hqz⟩ := hsub hz
  rwa [← hLinj hqz]

/-- **The subsheaf cut out by a family of `κ`-bounded spans is `κ`-generated.** Over an affine
open the sections of the subsheaf are the span of the given generators, and a spanning family
of the sections of a quasi-coherent module over an affine open generates its restriction. -/
public theorem isCardinalGenerated_sheafSubmodule [F.IsQuasicoherent]
    (T : ∀ W : X.affineOpens, Set Γ(F, W.1)) (hTb : ∀ W, Cardinal.mk (T W) ≤ κ)
    (hN : GabberColimit.IsCompatible F (fun W => Submodule.span Γ(X, W.1) (T W))) :
    IsCardinalGenerated (R := X.ringCatSheaf)
      (GabberColimit.compatibleModule F (fun W => Submodule.span Γ(X, W.1) (T W)) hN) κ := by
  have hMq : (GabberColimit.compatibleModule F
      (fun W => Submodule.span Γ(X, W.1) (T W)) hN).IsQuasicoherent :=
    GabberColimit.isQuasicoherent_sheafSubmodule F _ hN
  have hmemT : ∀ (W : X.affineOpens) (x : T W), GabberColimit.IsLocallyIn F
      (fun W => Submodule.span Γ(X, W.1) (T W)) (x : Γ(F, W.1)) := fun W x =>
    (GabberColimit.isLocallyIn_iff_mem F _ hN W _).mpr (Submodule.subset_span x.2)
  refine isCardinalGenerated_of_restrict _ (fun W : X.affineOpens => W.1)
    (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top X)) (fun W => ?_) (fun W => ?_)
  · exact @gsOfSpanningFamily X _ hMq W.1 W.2 ↥(T W)
      (fun x => GabberColimit.mkSection F _ hN (x : Γ(F, W.1)) (hmemT W x))
      (span_mkSection_eq_top F _ hN W (fun x : T W => (x : Γ(F, W.1)))
        (by rw [Subtype.range_coe]) (hmemT W))
  · exact hTb W

/-! ### Gabber's theorem -/

/-- **Stacks 077N, the colimit assertion.** Every quasi-coherent module on a scheme is the
colimit of the canonical diagram of its quasi-coherent subobjects generated by at most
`cardinalBound X` local sections. -/
@[stacks 077N "colimit"]
public def isColimit_cardinalGeneratedQuasicoherentSubobjectCocone (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] :
    IsColimit (cardinalGeneratedQuasicoherentSubobjectCocone F (cardinalBound X)) := by
  refine isColimit_cocone_of_locally_mem F (cardinalBound X) fun U s x hx => ?_
  obtain ⟨T, hTb, hN, hloc⟩ :=
    exists_isCompatible_isLocallyIn F (cardinalBound X) (aleph0_le_cardinalBound X)
      (mk_affineOpens_le_cardinalBound X) U s
  obtain ⟨G, hG⟩ :=
    exists_subobject_of_isLocallyIn F (cardinalBound X) _ hN
      (GabberColimit.isQuasicoherent_sheafSubmodule F _ hN)
      (isCardinalGenerated_sheafSubmodule F (cardinalBound X) T hTb hN) U s hloc
  refine ⟨U, le_rfl, hx, G, ?_⟩
  rw [GabberColimit.res_self]
  exact hG

end Stacks.AlgebraicGeometry.CardinalGeneration

end Colimit

end
