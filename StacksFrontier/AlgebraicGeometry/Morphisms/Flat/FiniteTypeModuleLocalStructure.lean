module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Order.CompactlyGenerated.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksCore.Tactic.StacksAttribute

/-!
# The local structure of a finite type module

Let `f : X ⟶ S` be a finite type morphism of affine schemes and let `F` be a quasi-coherent
`𝒪_X`-module of finite type. Then `F` is the direct image of a quasi-coherent finite type module
from a closed subscheme `Z ⊆ X` which is of **finite presentation** over `X`, and which can be
chosen so that its fibre over a prescribed point `s` of `S` is exactly the support of the
restriction of `F` to the fibre `X_s`.

The point of the statement is the finite presentation: the obvious closed subscheme carrying `F`
is the one cut out by the annihilator of the module of sections, which is finitely generated only
under a Noetherian hypothesis.  The fibre `κ(s) ⊗ Γ(X, ⊤)` of a finite type morphism *is*
Noetherian, so finitely many elements of the annihilator already generate its image there; the
subscheme they cut out still carries `F`, and is of finite presentation by construction.

## Main results

* `AlgebraicGeometry.exists_finitePresentation_closedSubscheme_fiber_eq_supp`: the closed
  subscheme of finite presentation carrying `F`, with the prescribed fibre.

## Implementation notes

The closed subscheme is produced as `AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop J` for a
finitely generated ideal `J` of `Γ(X, ⊤)` contained in the annihilator of `Γ(F, ⊤)`.  That `F` is
then a direct image from it is `Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`, the
consumer-facing form of [Stacks, Tag 08KS]: it asks that the kernel of the comorphism annihilate
`F` section by section, over **every** open, and that is reduced to the basic opens — where the
sections of `F` are a localization of `Γ(F, ⊤)` — by the sheaf property of `F`.

Equality of the fibre of the subscheme with the support on the fibre is stated as an equality of
the two subsets of `X` they map onto, which is how the source reads `Z_s = \operatorname{Supp}
(F_s)`.

## References

* [Stacks Project, Tag 057Q](https://stacks.math.columbia.edu/tag/057Q)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry

/-- A finitely generated subideal of `I` whose image under `φ` is all of `I·S`, available
whenever the target of `φ` is Noetherian: the image `I·S` is a compact element of the lattice
of ideals of `S`, hence is already covered by finitely many of the principal ideals generated
by the images of elements of `I`. -/
private theorem exists_span_le_map_eq {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing S] (φ : R →+* S) (I : Ideal R) :
    ∃ t : Finset R, Ideal.span (t : Set R) ≤ I ∧
      Ideal.map φ (Ideal.span (t : Set R)) = Ideal.map φ I := by
  classical
  have hc : IsCompactElement (Ideal.map φ I) :=
    (Submodule.fg_iff_compact _).mp (Ideal.fg_of_isNoetherianRing _)
  have hle : Ideal.map φ I ≤ ⨆ x : I, Ideal.span ({φ x.1} : Set S) := by
    rw [show Ideal.map φ I = Ideal.span (φ '' (I : Set R)) by
      rw [← Ideal.map_span φ (I : Set R)]; simp, Ideal.span_le]
    rintro y ⟨x, hx, rfl⟩
    exact Submodule.mem_iSup_of_mem (⟨x, hx⟩ : I) (Ideal.mem_span_singleton_self _)
  obtain ⟨s, hs⟩ :=
    hc.exists_finset_of_le_iSup _ hle
  have hsub : Ideal.span ((s.image Subtype.val : Finset R) : Set R) ≤ I :=
    Ideal.span_le.mpr fun x hx => by
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact y.2
  refine ⟨s.image Subtype.val, hsub, le_antisymm (Ideal.map_mono hsub) ?_⟩
  rw [Ideal.map_span]
  calc
    Ideal.map φ I ≤ ⨆ x : I, ⨆ (_ : x ∈ s), Ideal.span ({φ x.1} : Set S) := hs
    _ ≤ Ideal.span (φ '' ((s.image Subtype.val : Finset R) : Set R)) := by
      refine iSup_le fun x => iSup_le fun hx => Ideal.span_le.mpr ?_
      rintro _ rfl
      exact Ideal.subset_span ⟨x.1, Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩

/-- Two ideals of `B` with the same image in the fibre `κ(p) ⊗_A B` are contained in exactly the
same primes of `B` lying over `p`: such a prime is the contraction of a prime of the fibre, and
containment in a contraction is containment of the image. -/
private theorem le_iff_of_map_includeRight_eq {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (p : PrimeSpectrum A) (I J : Ideal B)
    (h : I.map (Algebra.TensorProduct.includeRight
          (R := A) (A := p.asIdeal.ResidueField) (B := B)).toRingHom =
        J.map (Algebra.TensorProduct.includeRight
          (R := A) (A := p.asIdeal.ResidueField) (B := B)).toRingHom)
    (q : PrimeSpectrum B) (hq : PrimeSpectrum.comap (algebraMap A B) q = p) :
    I ≤ q.asIdeal ↔ J ≤ q.asIdeal := by
  have hQ : ((PrimeSpectrum.preimageEquivFiber A B p ⟨q, hq⟩).asIdeal).comap
      (Algebra.TensorProduct.includeRight
        (R := A) (A := p.asIdeal.ResidueField) (B := B)).toRingHom = q.asIdeal :=
    congrArg (fun r : (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}) => r.1.asIdeal)
      ((PrimeSpectrum.preimageEquivFiber A B p).left_inv ⟨q, hq⟩)
  rw [← hQ, ← Ideal.map_le_iff_le_comap, ← Ideal.map_le_iff_le_comap, h]

variable {X : Scheme.{u}}

/-- On an affine scheme, a point lies in the vanishing locus of an ideal of global sections
exactly when the ideal is contained in the corresponding prime. -/
private theorem mem_zeroLocus_top_iff [IsAffine X] (I : Ideal Γ(X, ⊤)) (x : X) :
    x ∈ X.zeroLocus (U := ⊤) (I : Set Γ(X, ⊤)) ↔
      I ≤ ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal := by
  refine Iff.trans (Iff.of_eq (congrArg
      (fun y : X => y ∈ X.zeroLocus (U := ⊤) (I : Set Γ(X, ⊤)))
      ((isAffineOpen_top X).fromSpec_primeIdealOf ⟨x, trivial⟩).symm)) ?_
  refine Iff.trans (Iff.of_eq (congrArg
      (fun t : Set (Spec Γ(X, ⊤)) => (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩ ∈ t)
      ((isAffineOpen_top X).fromSpec_preimage_zeroLocus (I : Set Γ(X, ⊤))))) ?_
  exact PrimeSpectrum.mem_zeroLocus _ _

/-- The closed subscheme cut out by an ideal of global sections of an affine scheme has as its
set of points the primes containing that ideal. -/
private theorem mem_range_subschemeι_ofIdealTop_iff [IsAffine X] (J : Ideal Γ(X, ⊤)) (x : X) :
    x ∈ Set.range (Scheme.IdealSheafData.ofIdealTop J).subschemeι ↔
      J ≤ ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal := by
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_ofIdealTop]
  exact mem_zeroLocus_top_iff J x

/-- On an affine scheme, the support of a quasi-coherent module of finite type is the vanishing
locus of the annihilator of its module of global sections. -/
private theorem mem_supp_iff_annihilator_le [IsAffine X] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (x : X) :
    x ∈ SheafOfModules.supp F ↔
      Module.annihilator Γ(X, ⊤) Γ(F, ⊤) ≤
        ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal := by
  have : Module.Finite Γ(X, ⊤) Γ(F, ⊤) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
  rw [← Scheme.Modules.mem_support_sections_iff_mem_supp F ⟨⊤, isAffineOpen_top X⟩ x trivial]
  exact Module.mem_support_iff_of_finite

/-- The prime of `Γ(S, ⊤)` under the prime of `Γ(X, ⊤)` attached to a point of `X` is the one
attached to its image in `S`. -/
private theorem comap_primeIdealOf_appTop {S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S]
    (x : X) :
    PrimeSpectrum.comap (f.appTop).hom ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩) =
      (isAffineOpen_top S).primeIdealOf ⟨f x, trivial⟩ := by
  have hle : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens) := le_rfl
  have h := IsAffineOpen.comap_primeIdealOf_appLE (f := f) (x := x) (⊤ : S.Opens)
    (isAffineOpen_top S) (⊤ : X.Opens) (isAffineOpen_top X) hle trivial
  rwa [show f.appLE (⊤ : S.Opens) (⊤ : X.Opens) hle = f.appTop from
    Scheme.Hom.appLE_eq_app (f := f) (U := (⊤ : S.Opens))] at h

/-- Sections of an ideal of global sections of an affine scheme annihilate the sections of a
quasi-coherent module over a basic open, provided the ideal annihilates the global sections of
the module: over a basic open the sections of the module are a localization of the global ones,
and the annihilator of a localization contains the image of the annihilator. -/
private theorem smul_eq_zero_of_mem_map_basicOpen [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] (J : Ideal Γ(X, ⊤))
    (hJ : J ≤ Module.annihilator Γ(X, ⊤) Γ(F, ⊤)) (g : Γ(X, ⊤))
    (b : Γ(X, X.basicOpen g))
    (hb : b ∈ J.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom)
    (y : Γ(F, X.basicOpen g)) : b • y = 0 := by
  classical
  have hVU : X.basicOpen g ≤ (⊤ : X.Opens) := le_top
  let _ := algebraOfLE X hVU
  let _ := moduleOfLE F hVU
  let _ := isScalarTowerOfLE F hVU
  have hloc : IsLocalizedModule.Away g (restrictₗ F hVU) :=
    isLocalizedModule_restrictₗ F (isAffineOpen_top X) g rfl hVU
  have hlocr : IsLocalization.Away g Γ(X, X.basicOpen g) :=
    (isAffineOpen_top X).isLocalization_basicOpen g
  refine Module.mem_annihilator.mp (Ideal.map_le_iff_le_comap.mpr ?_ hb) y
  intro j hj
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro z
  obtain ⟨⟨m, u⟩, hu⟩ := IsLocalizedModule.surj (Submonoid.powers g) (restrictₗ F hVU) z
  have hw : (u : Γ(X, ⊤)) • (j • z) = 0 := by
    rw [smul_comm, show (u : Γ(X, ⊤)) • z = restrictₗ F hVU m from hu,
      ← map_smul, Module.mem_annihilator.mp (hJ hj) m, map_zero]
  have hjz : j • z = (0 : Γ(F, X.basicOpen g)) :=
    (IsUnit.smul_eq_zero (IsLocalization.map_units Γ(X, X.basicOpen g) u)).mp
      (by rwa [IsScalarTower.algebraMap_smul])
  show (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g)) j • z = 0
  rwa [IsScalarTower.algebraMap_smul]

/-- The kernel of the comorphism of the closed immersion cut out by `J` annihilates a
quasi-coherent module whose global sections are annihilated by `J`, section by section over an
arbitrary open: a section is zero as soon as all its germs are, and every germ is read on a
basic open, where `smul_eq_zero_of_mem_map_basicOpen` applies. -/
private theorem smul_eq_zero_of_app_eq_zero [IsAffine X] (F : X.Modules) [F.IsQuasicoherent]
    (J : Ideal Γ(X, ⊤)) (hJ : J ≤ Module.annihilator Γ(X, ⊤) Γ(F, ⊤)) (U : X.Opens)
    (a : Γ(X, U))
    (ha : ((Scheme.IdealSheafData.ofIdealTop J).subschemeι.app U).hom a = 0)
    (m : Γ(F, U)) : a • m = 0 := by
  classical
  set K : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop J with hK
  refine TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) U (a • m) 0 ?_
  intro x hx
  obtain ⟨g, hgU, hxg⟩ := (isAffineOpen_top X).exists_basicOpen_le (⟨x, hx⟩ : U) trivial
  have hres : F.presheaf.map (homOfLE hgU).op (a • m) = 0 := by
    have hVaff : IsAffineOpen (X.basicOpen g) := (isAffineOpen_top X).basicOpen g
    have hnat : (K.subschemeι.app (X.basicOpen g)).hom
        (X.presheaf.map (homOfLE hgU).op a) = 0 := by
      have hsq := congrArg (fun φ : Γ(X, U) ⟶ _ => φ.hom a)
        (K.subschemeι.naturality (U' := U) (U := X.basicOpen g) (homOfLE hgU).op)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hsq
      rwa [show (K.subschemeι.app U).hom a = 0 from ha, map_zero] at hsq
    have hmem : X.presheaf.map (homOfLE hgU).op a ∈
        J.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom := by
      have hker := K.ker_subschemeι_app ⟨X.basicOpen g, hVaff⟩
      rw [hK, Scheme.IdealSheafData.ofIdealTop_ideal] at hker
      exact hker ▸ hnat
    rw [F.map_smul (homOfLE hgU)]
    exact smul_eq_zero_of_mem_map_basicOpen F J hJ g _ hmem _
  rw [map_zero]
  show (TopCat.Presheaf.germ F.presheaf U x hx).hom (a • m) = 0
  rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hgU) x hxg (a • m), hres, map_zero]

/-- The image in `X` of the fibre over `s` of a composite `Z ⟶ X ⟶ S` is the part of the fibre
of `X` over `s` lying in the image of `Z`. -/
private theorem range_comp_fiberι {Z S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) (s : S) :
    Set.range (fun z : (i ≫ f).fiber s => i ((i ≫ f).fiberι s z)) =
      Set.range i ∩ f ⁻¹' {s} := by
  have h : Set.range (fun z : (i ≫ f).fiber s => i ((i ≫ f).fiberι s z)) =
      i '' ((i ≫ f) ⁻¹' {s}) := by
    rw [← Scheme.Hom.range_fiberι, ← Set.range_comp]
    rfl
  rw [h, Set.inter_comm]
  exact Set.image_preimage_eq_inter_range (f := i) (t := f ⁻¹' {s})

/-- The closed subscheme of an affine scheme cut out by a finitely generated ideal of global
sections is of finite presentation over it. -/
private theorem finitePresentation_subschemeι_ofIdealTop_of_fg [IsAffine X] {J : Ideal Γ(X, ⊤)}
    (hJ : J.FG) : FinitePresentation (Scheme.IdealSheafData.ofIdealTop J).subschemeι := by
  set K : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop J with hK
  have : IsAffine K.subscheme := isAffine_of_isAffineHom K.subschemeι
  have hKideal : K.ideal ⟨⊤, isAffineOpen_top X⟩ = J := by
    rw [hK, Scheme.IdealSheafData.ofIdealTop_ideal]
    simp
  refine FinitePresentation.mk ?_ inferInstance inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  refine RingHom.FinitePresentation.of_surjective _
    (K.subschemeι_app_surjective ⟨⊤, isAffineOpen_top X⟩) ?_
  rw [show RingHom.ker (K.subschemeι.appTop).hom = J from
    (K.ker_subschemeι_app ⟨⊤, isAffineOpen_top X⟩).trans hKideal]
  exact hJ

/-- **[Stacks, Tag 057Q].** Let `f : X ⟶ S` be a finite type morphism of affine schemes and let
`F` be a quasi-coherent `𝒪_X`-module of finite type. For every point `s` of `S` there is a closed
immersion `i : Z ⟶ X` of finite presentation and a quasi-coherent finite type `𝒪_Z`-module `G`
with `i_* G ≅ F` whose fibre over `s` is the support of the restriction of `F` to the fibre of
`X` over `s`.

The equality of the fibre with the support is an equality of subsets of `X`: the image of the
fibre of `Z` is the image of the support of the pullback of `F` to the fibre of `X`. -/
@[stacks 057Q]
theorem exists_finitePresentation_closedSubscheme_fiber_eq_supp {S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsAffine S] [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (s : S) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (G : Z.Modules)
      (_ : (Scheme.Modules.pushforward i).obj G ≅ F),
      IsClosedImmersion i ∧ FinitePresentation i ∧ G.IsQuasicoherent ∧ G.IsFiniteType ∧
        Set.range (fun z : (i ≫ f).fiber s => i ((i ≫ f).fiberι s z)) =
          f.fiberι s '' SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F) := by
  classical
  let _ : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
  have _ : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) := RingHom.finiteType_algebraMap.mp
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance)
  set p : PrimeSpectrum Γ(S, ⊤) := (isAffineOpen_top S).primeIdealOf ⟨s, trivial⟩ with hp
  have _ : Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber Γ(X, ⊤)) :=
    Algebra.FiniteType.baseChange _
  have _ : IsNoetherianRing (p.asIdeal.Fiber Γ(X, ⊤)) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  set I₀ : Ideal Γ(X, ⊤) := Module.annihilator Γ(X, ⊤) Γ(F, ⊤) with hI₀
  obtain ⟨t, htI, hmap⟩ := exists_span_le_map_eq (Algebra.TensorProduct.includeRight
    (R := Γ(S, ⊤)) (A := p.asIdeal.ResidueField) (B := Γ(X, ⊤))).toRingHom I₀
  set J : Ideal Γ(X, ⊤) := Ideal.span (t : Set Γ(X, ⊤)) with hJ
  set K : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop J with hK
  have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction K.subschemeι).unit.app F) :=
    Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero K.subschemeι F fun U a ha m =>
      smul_eq_zero_of_app_eq_zero F J htI U a (hK ▸ ha) m
  have hGft : ((Scheme.Modules.pullback K.subschemeι).obj F).IsFiniteType :=
    @SheafOfModules.pullback_isFiniteType _ _ K.subschemeι.toLRSHom.toShHom F ‹F.IsFiniteType›
  have hsupport : Set.range K.subschemeι ∩ f ⁻¹' {s} =
      SheafOfModules.supp F ∩ f ⁻¹' {s} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, and_congr_left_iff]
    intro hx
    rw [mem_range_subschemeι_ofIdealTop_iff, mem_supp_iff_annihilator_le, ← hI₀]
    refine le_iff_of_map_includeRight_eq p J I₀ hmap _ ?_
    rw [show (algebraMap Γ(S, ⊤) Γ(X, ⊤)) = (f.appTop).hom from rfl,
      comap_primeIdealOf_appTop f x, hp]
    exact congrArg (fun y : S => (isAffineOpen_top S).primeIdealOf ⟨y, trivial⟩) hx
  refine ⟨K.subscheme, K.subschemeι, (Scheme.Modules.pullback K.subschemeι).obj F,
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction K.subschemeι).unit.app F)).symm,
    inferInstance,
    finitePresentation_subschemeι_ofIdealTop_of_fg (Submodule.fg_span t.finite_toSet),
    inferInstance, hGft, ?_⟩
  rw [range_comp_fiberι, Stacks.Modules.supp_pullback (f.fiberι s) F,
    Set.image_preimage_eq_inter_range, Scheme.Hom.range_fiberι, hsupport, Set.inter_comm]

end AlgebraicGeometry

end
