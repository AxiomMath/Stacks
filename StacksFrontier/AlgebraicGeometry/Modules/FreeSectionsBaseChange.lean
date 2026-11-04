module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafStalkBasis
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusLocality

/-!
# Global sections of free modules, and affine cartesian squares

This file collects the bookkeeping needed to compare global sections of free modules across a
base change of schemes. The global sections of the free module `𝒪_X^m` have the global sections
of the summands as a `Γ(X, ⊤)`-basis, and pulling these sections back along a morphism and
identifying the pullback of a free module with the free module gives the corresponding basis
upstairs. Over an affine base `Spec B` whose ring maps isomorphically to `Γ(X, ⊤)`, such a basis
is also a basis over `B`. Finally, a cartesian square over `Spec A` with affine corner `T` may be
put in model form, with `T` replaced by `Spec Γ(T, ⊤)`, and points of a cartesian square lift to
the fibre product.

## Main definitions

* `AlgebraicGeometry.freeSectionsBasis`: the basis of `Γ(𝒪_X^m, ⊤)` over `Γ(X, ⊤)` given by the
  global sections of the summands.
* `AlgebraicGeometry.baseRingEquiv`: the ring isomorphism `B ≃+* Γ(X, ⊤)` of a scheme over
  `Spec B` whose structure map is bijective on global sections.
* `AlgebraicGeometry.basisOverBase` and `AlgebraicGeometry.basisOfBasisOverBase`: a basis of
  global sections over `Γ(X, ⊤)` is the same as a basis over `B`.

## Main results

* `AlgebraicGeometry.freeSectionsBasis_apply`: the vectors of `freeSectionsBasis`.
* `AlgebraicGeometry.pullbackSectionHom_naturality_apply`: pulling back a section is natural in the
  module.
* `AlgebraicGeometry.schemeModulesPullbackObjFreeIso_hom_pullbackSectionHom`: pulling back the
  free global sections gives the free global sections.
* `AlgebraicGeometry.isPullback_specModel_of_isPullback`: an affine cartesian square in model form.
* `AlgebraicGeometry.isUnit_of_range_subset_basicOpen`: a morphism to `Spec A` landing in `D(g)`
  makes `g` a unit in the global functions.
* `AlgebraicGeometry.IsPullback.exists_preimage`: points of a cartesian square of schemes lift to
  the fibre product.

## Implementation notes

The free module is written `Scheme.Modules.free X ι` rather than `SheafOfModules.free ι`, so that
the instance `Module Γ(X, U) Γ(M, U)` of `AlgebraicGeometry.Scheme.Modules` is found for its
sections. The basis is Stacks' `Stacks.SheafOfModules.freeSheafBasis` over `⊤`, reindexed from
`ULift (Fin m)` to `Fin m`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The basis of global sections of a free module -/

/-- The basis of the global sections of a finite free module, indexed by its own index type:
the global sections of the summands. -/
noncomputable def freeSectionsBasisAux (X : Scheme.{u}) (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Module.Basis ι Γ(X, ⊤) Γ(Scheme.Modules.free X ι, ⊤) :=
  Stacks.SheafOfModules.freeSheafBasis (Osharp := X.sheaf) ⊤

/-- The `i`-th vector of `freeSectionsBasisAux` is the global section of the `i`-th summand. -/
theorem freeSectionsBasisAux_apply (X : Scheme.{u}) (ι : Type u) [Fintype ι] [DecidableEq ι]
    (i : ι) :
    freeSectionsBasisAux X ι i =
      (SheafOfModules.freeSection (R := X.ringCatSheaf) i).eval (op ⊤) :=
  Stacks.SheafOfModules.freeSheafBasis_apply (Osharp := X.sheaf) ⊤ i

/-- The global sections of the free module `𝒪_X^m` form a free `Γ(X, ⊤)`-module, with basis the
global sections of the summands. -/
noncomputable def freeSectionsBasis (X : Scheme.{u}) (m : ℕ) :
    Module.Basis (Fin m) Γ(X, ⊤) Γ(Scheme.Modules.free X (ULift.{u} (Fin m)), ⊤) :=
  (freeSectionsBasisAux X (ULift.{u} (Fin m))).reindex Equiv.ulift

/-- The `j`-th vector of `freeSectionsBasis` is the global section of the `j`-th summand. -/
@[simp]
theorem freeSectionsBasis_apply (X : Scheme.{u}) (m : ℕ) (j : Fin m) :
    freeSectionsBasis X m j =
      (SheafOfModules.freeSection (R := X.ringCatSheaf) (⟨j⟩ : ULift.{u} (Fin m))).eval
        (op ⊤) := by
  rw [freeSectionsBasis, Module.Basis.reindex_apply]
  exact freeSectionsBasisAux_apply X _ _

/-! ### Pulling back sections -/

/-- **Pulling back a section is natural in the module.** -/
theorem pullbackSectionHom_naturality_apply {X Y : Scheme.{u}} (a : Y ⟶ X) {M N : X.Modules}
    (τ : M ⟶ N) (U : X.Opens) (V : Y.Opens) (h : V ≤ a ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((Scheme.Modules.pullback a).map τ).app V (pullbackSectionHom a M U V h s) =
      pullbackSectionHom a N U V h (τ.app U s) :=
  Scheme.Modules.pullbackSection_naturality a τ U V h s

/-- The canonical identification `a^* 𝒪_X ≅ 𝒪_Y` sends the pullback of the global section `1`
to `1`. -/
theorem pullbackObjUnitToUnit_pullbackSectionHom_one {X Y : Scheme.{u}} (a : Y ⟶ X)
    (h : (⊤ : Y.Opens) ≤ a ⁻¹ᵁ ⊤) :
    letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
      (Scheme.Modules.pullbackPushforwardAdjunction a).isRightAdjoint
    (SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom).val.app (op ⊤)
      (pullbackSectionHom a (SheafOfModules.unit X.ringCatSheaf) ⊤ ⊤ h (1 : Γ(X, ⊤))) =
        (1 : Γ(Y, ⊤)) := by
  let _ : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction a).isRightAdjoint
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have heq : (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app O ≫
      (Scheme.Modules.pushforward a).map
        (SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)
  exact (congrArg ((SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom).val.app (op ⊤))
    (Scheme.Modules.pullbackSection_top a O h (1 : Γ(X, ⊤)))).trans
      ((congrArg (fun φ => φ.val.app (op ⊤) (1 : Γ(X, ⊤))) heq).trans
        (map_one (a.toRingCatSheafHom.hom.app (op ⊤)).hom))

/-- **Pulling back the free global sections.** The pullback along `a : Y ⟶ X` of the `j`-th
global section of `𝒪_X^m`, read in `𝒪_Y^m` through `schemeModulesPullbackObjFreeIso`, is the
`j`-th global section of `𝒪_Y^m`. -/
theorem schemeModulesPullbackObjFreeIso_hom_pullbackSectionHom {X Y : Scheme.{u}} (a : Y ⟶ X)
    (m : ℕ) (h : (⊤ : Y.Opens) ≤ a ⁻¹ᵁ ⊤) (j : Fin m) :
    ((schemeModulesPullbackObjFreeIso a (ULift.{u} (Fin m))).hom.app ⊤)
      (pullbackSectionHom a (Scheme.Modules.free X (ULift.{u} (Fin m))) ⊤ ⊤ h
        (freeSectionsBasis X m j)) = freeSectionsBasis Y m j := by
  let _ : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction a).isRightAdjoint
  have : (Opens.map a.base).Final := Stacks.Topology.final_opensMap _
  let i : ULift.{u} (Fin m) := ⟨j⟩
  have hbasis (S : Scheme.{u}) : freeSectionsBasis S m j =
      (SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app (op ⊤) (1 : Γ(S, ⊤)) :=
    (freeSectionsBasis_apply S m j).trans (Stacks.SheafOfModules.freeSection_eval i (op ⊤))
  have hnat := pullbackSectionHom_naturality_apply a
    (SheafOfModules.ιFree (R := X.ringCatSheaf) i : SheafOfModules.unit X.ringCatSheaf ⟶
      Scheme.Modules.free X (ULift.{u} (Fin m))) ⊤ ⊤ h (1 : Γ(X, ⊤))
  have hcomp := congrArg (fun φ => φ.val.app (op ⊤)
      (pullbackSectionHom a (SheafOfModules.unit X.ringCatSheaf) ⊤ ⊤ h (1 : Γ(X, ⊤))))
    (SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom a.toRingCatSheafHom i)
  rw [hbasis X, hbasis Y, ← pullbackObjUnitToUnit_pullbackSectionHom_one a h]
  exact (congrArg _ hnat.symm).trans hcomp

/-! ### Bases over an affine base -/

/-- The global sections of a scheme over `Spec B`, when the structure map on global sections is
bijective: the ring isomorphism `B ≃+* Γ(X, ⊤)`. -/
noncomputable def baseRingEquiv {B : Type u} [CommRing B] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of B)) (hp : Function.Bijective (Stacks.Cech.globalRingHom p).hom) :
    B ≃+* Γ(X, ⊤) :=
  RingEquiv.ofBijective (Stacks.Cech.baseRingHom p ⊤).hom (by
    have h : (Stacks.Cech.baseRingHom p ⊤) = Stacks.Cech.globalRingHom p := by
      rw [Stacks.Cech.baseRingHom, show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op = 𝟙 _ from
        Subsingleton.elim _ _, CategoryTheory.Functor.map_id, Category.comp_id]
    rwa [h])

/-- `baseRingEquiv` is the structural ring map. -/
@[simp]
theorem baseRingEquiv_apply {B : Type u} [CommRing B] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of B)) (hp : Function.Bijective (Stacks.Cech.globalRingHom p).hom) (c : B) :
    baseRingEquiv p hp c = (Stacks.Cech.baseRingHom p ⊤).hom c := rfl

/-- **A basis over the global functions is a basis over the base ring.** If `p : X ⟶ Spec B`
induces a bijection `B ≅ Γ(X, ⊤)`, a `Γ(X, ⊤)`-basis of `Γ(M, ⊤)` is a basis, with the same
vectors, for the `B`-module structure `Stacks.Cech.sectionsModule p M ⊤`. -/
noncomputable def basisOverBase {B : Type u} [CommRing B] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of B)) (hp : Function.Bijective (Stacks.Cech.globalRingHom p).hom)
    (M : X.Modules) {ι : Type*} (b : Module.Basis ι Γ(X, ⊤) Γ(M, ⊤)) :
    letI := Stacks.Cech.sectionsModule p M ⊤
    Module.Basis ι B Γ(M, ⊤) :=
  letI := Stacks.Cech.sectionsModule p M ⊤
  b.mapCoeffs (baseRingEquiv p hp).symm fun c x ↦ by
    change (baseRingEquiv p hp) ((baseRingEquiv p hp).symm c) • x = c • x
    rw [RingEquiv.apply_symm_apply]

/-- The vectors of `basisOverBase` are those of the given basis. -/
@[simp]
theorem coe_basisOverBase {B : Type u} [CommRing B] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of B)) (hp : Function.Bijective (Stacks.Cech.globalRingHom p).hom)
    (M : X.Modules) {ι : Type*} (b : Module.Basis ι Γ(X, ⊤) Γ(M, ⊤)) :
    ⇑(basisOverBase p hp M b) = ⇑b := by
  let _ := Stacks.Cech.sectionsModule p M ⊤
  exact Module.Basis.coe_mapCoeffs _ _ _

/-- **A basis over the base ring is a basis over the global functions.** The converse of
`basisOverBase`. -/
noncomputable def basisOfBasisOverBase {B : Type u} [CommRing B] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of B)) (hp : Function.Bijective (Stacks.Cech.globalRingHom p).hom)
    (M : X.Modules) {ι : Type*}
    (b : letI := Stacks.Cech.sectionsModule p M ⊤; Module.Basis ι B Γ(M, ⊤)) :
    Module.Basis ι Γ(X, ⊤) Γ(M, ⊤) :=
  letI := Stacks.Cech.sectionsModule p M ⊤
  b.mapCoeffs (baseRingEquiv p hp) fun _ _ ↦ rfl

/-- The vectors of `basisOfBasisOverBase` are those of the given basis. -/
@[simp]
theorem coe_basisOfBasisOverBase {B : Type u} [CommRing B] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of B)) (hp : Function.Bijective (Stacks.Cech.globalRingHom p).hom)
    (M : X.Modules) {ι : Type*}
    (b : letI := Stacks.Cech.sectionsModule p M ⊤; Module.Basis ι B Γ(M, ⊤)) :
    ⇑(basisOfBasisOverBase p hp M b) = ⇑b := by
  let _ := Stacks.Cech.sectionsModule p M ⊤
  exact Module.Basis.coe_mapCoeffs _ _ _

/-! ### Affine squares -/

/-- **An affine cartesian square in model form.** If `T` is affine and `t : T ⟶ Spec A`, the
square obtained by replacing `T` with `Spec Γ(T, ⊤)` and `t` with the spectrum of the ring map
`A → Γ(T, ⊤)` it induces is still cartesian. -/
theorem isPullback_specModel_of_isPullback {A : Type u} [CommRing A] {X T X' : Scheme.{u}}
    [IsAffine T]
    {f : X ⟶ Spec (.of A)} {t : T ⟶ Spec (.of A)} {q : X' ⟶ X} {p : X' ⟶ T}
    (H : IsPullback q p f t) :
    IsPullback q (p ≫ T.isoSpec.hom) f
      (Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of A)).inv ≫ t.appTop).hom)) := by
  refine H.of_iso (Iso.refl _) (Iso.refl _) T.isoSpec (Iso.refl _) (by simp) (by simp)
    (by simp) ?_
  rw [Iso.refl_hom, Category.comp_id, CommRingCat.ofHom_hom, Spec.map_comp,
    Scheme.isoSpec_hom_naturality_assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- A morphism `t : T ⟶ Spec A` with image in the basic open `D(g)` makes `g` invertible in
`Γ(T, ⊤)`. -/
theorem isUnit_of_range_subset_basicOpen {A : Type u} [CommRing A] {T : Scheme.{u}}
    (t : T ⟶ Spec (.of A)) (g : A)
    (hg : Set.range t ⊆ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A))) :
    IsUnit (((Scheme.ΓSpecIso (.of A)).inv ≫ t.appTop).hom g) := by
  refine T.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ ↦ ?_
  have h1 : t y ∈ (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv g) := by
    rw [basicOpen_eq_of_affine]
    exact hg ⟨y, rfl⟩
  have h2 : y ∈ T.basicOpen (t.appTop ((Scheme.ΓSpecIso (.of A)).inv g)) := by
    rwa [← Scheme.preimage_basicOpen_top]
  exact (Scheme.mem_basicOpen_top _ _ _).1 h2

/-! ### Points of a cartesian square -/

/-- **Points of a cartesian square of schemes.** Two points of the corners over the same point of
the base come from a point of the fibre product. -/
theorem IsPullback.exists_preimage {X Y Z P : Scheme.{u}} {f : X ⟶ Z} {t : Y ⟶ Z}
    {q : P ⟶ X} {p : P ⟶ Y} (H : IsPullback q p f t) (x : X) (y : Y) (h : f x = t y) :
    ∃ z : P, q z = x ∧ p z = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  refine ⟨H.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, hz₁]
  · rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_snd, hz₂]

end AlgebraicGeometry

end
