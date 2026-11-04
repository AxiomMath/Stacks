module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Sections
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.ClosedSubspaceScheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending admissible blowups

Let `X` be a quasi-compact and quasi-separated scheme and let `U`, `V ⊆ X` be quasi-compact open
subschemes. Every `U ∩ V`-admissible blowup of `V` extends to a `U`-admissible blowup of `X`
whose restriction to `V` is the given one.

The extension is an extension of *centres*. A `U ∩ V`-admissible blowup of `V` is the blowup of
`V` in a quasi-coherent ideal `I` whose closed subscheme is of finite presentation over `V` and
disjoint from `U ∩ V`. Because the support of `I` avoids `U ∩ V`, the closed immersion
`V(I) ⟶ V` stays closed after enlarging the base to `U ∪ V`, so `I` is also the ideal cut out by
a finitely presented closed subscheme of `U ∪ V` — this is the ideal that Stacks describes as
"equal to `𝒪_U` on `U` and to `I` on `V`". Extending it from the quasi-compact open `U ∪ V` to
all of `X` without losing finite presentation is [Stacks, Tag 01PF]. Blowing up the extended
ideal gives the required blowup of `X`, and the restriction statement is flat base change for
blowups ([Stacks, Tag 0805]) along the open immersion `V ⟶ X`.

## Main results

* `Stacks.Blowup.exists_idealSheafData_comap_eq`: the extension of the centre. A finitely
  presented quasi-coherent ideal on a quasi-compact open `V` whose support avoids `U ∩ V`
  extends to a finitely presented quasi-coherent ideal on `X` whose support avoids `U`.
* `Stacks.Blowup.exists_admissibleBlowup_isPullback`: **Tag 080M.** The extension of an
  admissible blowup, with its restriction to `V` recorded by a cartesian square.

## Implementation notes

The restriction to `V` is expressed by a pullback square rather than by an isomorphism of
`V`-schemes: the square records both the identification of the given blowup with the restriction
and the compatibility of the two morphisms to `V`.

`Stacks.Blowup.IsAdmissibleBlowup` is phrased with the blowup
`Stacks.Blowup.blowUp` of `StacksFrontier/AlgebraicGeometry/Blowup/ReesSheafData.lean`, while flat
base change is available for the parallel construction `AlgebraicGeometry.blowUp`. The two are
compared by `Stacks.Blowup.isAdmissibleBlowup_iff`, which is used here to work on the side where
Tag 0805 lives.

The comparison of the extended ideal with the original one on `V` is made on sections over affine
opens, through `Stacks.Blowup.ker_comap_eq_of_idealSheaf_sections`: a section of the structure
sheaf over an affine open is killed by a closed immersion exactly when it lifts to the ideal
sheaf (`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff_mem_ker_ideal`),
so an isomorphism of ideal sheaves compatible with their inclusions into the structure sheaf
forces the two kernels to agree.

## References

* [Stacks Project, Tag 080M](https://stacks.math.columbia.edu/tag/080M)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.Conormal.AffineCotangent.Sections

universe u

namespace Stacks.Blowup

/-- **The closure of the image of the centre avoids `U`.** If the support of `I` is disjoint from
the inverse image of `U` in `V`, then its image in `X` has closure disjoint from `U`: that image
lies in the closed set `X \ U`. -/
private lemma disjoint_closure_image_support {X : Scheme.{u}} (U V : X.Opens)
    (I : V.toScheme.IdealSheafData)
    (h : Disjoint (V.ι ⁻¹ᵁ U : Set V) (I.support : Set V)) :
    Disjoint (U : Set X) (closure (V.ι.base '' (I.support : Set V))) := by
  refine Set.disjoint_left.mpr fun x hxU hxcl ↦ ?_
  have hsub : V.ι.base '' (I.support : Set V) ⊆ (U : Set X)ᶜ := by
    rintro y ⟨z, hz, rfl⟩
    exact fun hyU ↦ (Set.disjoint_left.mp h) (show z ∈ (V.ι ⁻¹ᵁ U : Set V) from hyU) hz
  exact closure_minimal hsub U.2.isClosed_compl hxcl hxU

/-- The ideal of a quasi-coherent ideal sheaf at two affine opens with equal underlying open is
carried to the other by restriction along the equality. -/
private lemma ideal_comap_presheaf_map_eqToHom {X : Scheme.{u}} (I : X.IdealSheafData)
    (A B : X.affineOpens) (h : (A : X.Opens) = (B : X.Opens)) :
    Ideal.comap (X.presheaf.map (eqToHom h).op).hom (I.ideal A) = I.ideal B := by
  obtain rfl : A = B := Subtype.ext h
  simp

/-- **Pushing forward and pulling back along a quasi-compact open immersion is the identity on
ideal sheaves.** On an affine open `U` of the source the pushforward is a contraction along
`𝒪(f(U)) ⟶ 𝒪(U)`, which the inverse image undoes because `f⁻¹(f(U)) = U`. -/
private lemma comap_map_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] [QuasiCompact f] (I : X.IdealSheafData) :
    (I.map f).comap f = I := by
  refine Scheme.IdealSheafData.ext (funext fun U ↦ ?_)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have hpre : IsAffineOpen (f ⁻¹ᵁ (f ''ᵁ (U : X.Opens))) := by
    rw [f.preimage_image_eq]; exact U.2
  have hcomp : (CommRingCat.Hom.hom (f.app (f ''ᵁ (U : X.Opens)))).comp
        (CommRingCat.Hom.hom (f.appIso U).inv) =
      (X.presheaf.map (eqToHom (f.preimage_image_eq U)).op).hom := by
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (Scheme.Hom.appIso_inv_app f U)
  rw [Scheme.IdealSheafData.ideal_map I f
    ⟨f ''ᵁ (U : X.Opens), U.2.image_of_isOpenImmersion f⟩ hpre, Ideal.comap_comap, hcomp,
    ideal_comap_presheaf_map_eqToHom I ⟨_, hpre⟩ U (f.preimage_image_eq U)]

/-- **The centre is still closed in `U ∪ V`.** The closed subscheme cut out by `I` on `V` has
closed image in `U ⊔ V` once the support of `I` avoids the inverse image of `U`: the closure of
that image misses `U`, hence lies in `V`, where the image is already closed. -/
private lemma isClosed_range_subschemeι_homOfLE {X : Scheme.{u}} (U V : X.Opens)
    (I : V.toScheme.IdealSheafData)
    (h : Disjoint (V.ι ⁻¹ᵁ U : Set V) (I.support : Set V)) :
    IsClosed (Set.range ((I.subschemeι ≫ X.homOfLE (le_sup_right : V ≤ U ⊔ V)).base)) := by
  set W : X.Opens := U ⊔ V with hWdef
  set vW : V.toScheme ⟶ W.toScheme := X.homOfLE (le_sup_right : V ≤ U ⊔ V) with hvW
  have hrange : Set.range ((I.subschemeι ≫ vW).base) = vW.base '' (I.support : Set V) := by
    simp [Set.range_comp, I.range_subschemeι]
  rw [hrange, ← closure_subset_iff_isClosed]
  intro x hx
  have hout : Set.range ((I.subschemeι ≫ vW).base) ⊆
      ((W.ι ⁻¹ᵁ U : W.toScheme.Opens) : Set W.toScheme)ᶜ := by
    rw [hrange]
    rintro y ⟨z, hz, rfl⟩
    refine fun hy ↦ (Set.disjoint_left.mp h) (show z ∈ (V.ι ⁻¹ᵁ U : Set V) from ?_) hz
    show (V.ι z : X) ∈ U
    rw [show (V.ι : V.toScheme ⟶ X) = vW ≫ W.ι by simp [hvW, Scheme.homOfLE_ι],
      Scheme.Hom.comp_apply]
    exact hy
  have hxU : x.1 ∉ U := by
    intro hxU
    refine closure_minimal (hrange ▸ hout) (W.ι ⁻¹ᵁ U).2.isClosed_compl hx
      (show (W.ι x : X) ∈ U from hxU)
  have hxV : x.1 ∈ V := by
    rcases (show x.1 ∈ (U : Set X) ∪ (V : Set X) from x.2) with hxU' | hxV
    · exact absurd hxU' hxU
    · exact hxV
  have hvx : vW ⟨x.1, hxV⟩ = x := Subtype.ext (by simp [hvW, Scheme.homOfLE_apply])
  have hpre : vW.base ⁻¹' (vW.base '' (I.support : Set V)) = (I.support : Set V) :=
    Set.preimage_image_eq _ vW.isOpenEmbedding.injective
  have hycl : (⟨x.1, hxV⟩ : V.toScheme) ∈ (I.support : Set V) := by
    have hmem : (⟨x.1, hxV⟩ : V.toScheme) ∈
        vW.base ⁻¹' closure (vW.base '' (I.support : Set V)) :=
      Set.mem_preimage.mpr (by rw [hvx]; exact hx)
    rw [vW.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage vW.continuous, hpre,
      I.support.isClosed.closure_eq] at hmem
    exact hmem
  exact ⟨⟨x.1, hxV⟩, hycl, hvx⟩

/-- **Two closed immersions with the same ideal sheaf over an open have the same ideal there.**
Let `W ⊆ X` be open, `i : Z ⟶ X` and `k : Z' ⟶ W` be quasi-compact, and suppose the sections of
the ideal sheaf of `i` over `W.ι ''ᵁ Q` and those of the ideal sheaf of `k` over `Q` correspond,
compatibly with their inclusions into the structure sheaf. Then the inverse image of
`AlgebraicGeometry.Scheme.Hom.ker i` on `W` is `AlgebraicGeometry.Scheme.Hom.ker k`.

The correspondence is given by two maps rather than by an isomorphism of sheaves, because that
is all the proof uses: over an affine open a section of the structure sheaf lies in the kernel
exactly when it is the image of a section of the ideal sheaf. -/
private lemma ker_comap_eq_of_idealSheaf_sections {X : Scheme.{u}} (W : X.Opens)
    {Z Z' : Scheme.{u}} (i : Z ⟶ X) (k : Z' ⟶ W.toScheme) [QuasiCompact i] [QuasiCompact k]
    (φ : ∀ Q : W.toScheme.Opens,
      (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (.op (W.ι ''ᵁ Q)) →
        (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj (.op Q))
    (ψ : ∀ Q : W.toScheme.Opens,
      (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj (.op Q) →
        (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (.op (W.ι ''ᵁ Q)))
    (hφ : ∀ (Q : W.toScheme.Opens) x,
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom k.toLRSHom.toShHom))).val.app (.op Q) (φ Q x) =
        (W.ι.appIso Q).hom ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i.toLRSHom.toShHom))).val.app (.op (W.ι ''ᵁ Q)) x))
    (hψ : ∀ (Q : W.toScheme.Opens) y,
      (W.ι.appIso Q).hom ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i.toLRSHom.toShHom))).val.app (.op (W.ι ''ᵁ Q)) (ψ Q y)) =
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom k.toLRSHom.toShHom))).val.app (.op Q) y) :
    i.ker.comap W.ι = k.ker := by
  refine Scheme.IdealSheafData.ext (funext fun Q ↦ ?_)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  refine Ideal.ext fun r ↦ ?_
  rw [Ideal.mem_comap,
    ← exists_idealSheaf_section_iff_mem_ker_ideal i (W.ι ''ᵁ Q.1)
      (Q.2.image_of_isOpenImmersion W.ι),
    ← exists_idealSheaf_section_iff_mem_ker_ideal k Q.1 Q.2]
  have hcancel : (W.ι.appIso Q.1).hom ((W.ι.appIso Q.1).inv.hom r) = r := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨φ Q.1 x, ?_⟩, fun ⟨y, hy⟩ ↦ ⟨ψ Q.1 y, ?_⟩⟩
  · rw [hφ, hx, hcancel]
  · refine (ConcreteCategory.bijective_of_isIso (W.ι.appIso Q.1).hom).1 ?_
    rw [hψ, hy, hcancel]

/-- **[Stacks, Tag 01PF] for a submodule given by a monomorphism.** On a quasi-compact and
quasi-separated scheme, a quasi-coherent finite type module `M` over a quasi-compact open `W`
with a monomorphism into `F|_W` extends to a quasi-coherent finite type submodule of `F`
restricting to `M`.

This is `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension` with the
`CategoryTheory.Subobject` packaging unwound into a monomorphism, which is the shape the ideal
sheaf of a closed immersion comes in. -/
@[ega "I 9.4.3" "special case", ega "I 9.4.7" "more general", sga "6 0 2.11" "more general"]
private theorem exists_module_extension {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (F : X.Modules) (hF : F.IsQuasicoherent) (W : X.Opens)
    (hW : IsCompact (W : Set X)) (M : W.toScheme.Modules) (hMqc : M.IsQuasicoherent)
    (hMft : M.IsFiniteType) (m : M ⟶ F.restrict W.ι) (hm : Mono m) :
    ∃ (N : X.Modules) (j : N ⟶ F), Mono j ∧ N.IsQuasicoherent ∧ N.IsFiniteType ∧
      ∃ e : N.restrict W.ι ≅ M, (Scheme.Modules.restrictFunctor W.ι).map j = e.hom ≫ m := by
  have := hF
  have := hMqc
  have := hMft
  have := hm
  have : ((Subobject.mk m : Subobject (F.restrict W.ι)) :
      W.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso m).symm inferInstance
  have : ((Subobject.mk m : Subobject (F.restrict W.ι)) : W.toScheme.Modules).IsFiniteType :=
    isFiniteType_of_iso_modules (Subobject.underlyingIso m) inferInstance
  obtain ⟨G', hqc, hft, eG, heG⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension F W hW (Subobject.mk m)
  refine ⟨_, G'.arrow, inferInstance, hqc, hft, eG ≪≫ Subobject.underlyingIso m, ?_⟩
  rw [heG, Iso.trans_hom, Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk m]

/-- **The closed subscheme cut out by a finite type submodule of the structure sheaf.** For a
monomorphism `j : N ⟶ 𝒪_X` with `N` of finite type there is a closed immersion `i : Z ⟶ X` whose
ideal sheaf is `N`, compatibly with `j`.

This is [Stacks, Tag 01HN] and [Stacks, Tag 01IN] packaged together:
`Stacks.ClosedImmersion.closedSubscheme` is the closed subspace, which is a scheme, and
`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae` turns the ringed-space
notion of closed immersion it carries into the scheme-theoretic one. -/
private theorem exists_closedImmersion_idealSheaf_iso {X : Scheme.{u}} (N : X.Modules)
    (j : N ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (hmono : Mono j)
    (hft : N.IsFiniteType) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      ∃ ε : N ≅ (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom : X.Modules),
        ε.hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i.toLRSHom.toShHom)) = j := by
  classical
  have : @Mono (SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
      inferInstance N
      (SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace)) j :=
    hmono
  have hgen : Nonempty (SheafOfModules.LocalGeneratorsData N) :=
    ⟨Classical.choose hft.exists_localGeneratorsData⟩
  refine ⟨Stacks.ClosedImmersion.closedSubscheme X N j hgen,
    Stacks.ClosedImmersion.closedSubschemeInclusion X N j hgen, ?_,
    (Stacks.ClosedImmersion.closedSubspace X.toLocallyRingedSpace N j hgen).idealIso,
    (Stacks.ClosedImmersion.closedSubspace X.toLocallyRingedSpace N j hgen).idealIso_compat⟩
  exact ((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae
    (Stacks.ClosedImmersion.closedSubschemeInclusion X N j hgen)).out 6 1).mp
    (Stacks.ClosedImmersion.closedSubspace X.toLocallyRingedSpace N j hgen).isClosedImmersion

/-- Equal morphisms of modules have equal components on sections. -/
private lemma val_app_apply_congr {X : Scheme.{u}} {M N : X.Modules} {f g : M ⟶ N} (h : f = g)
    (Q : X.Opens) (x) : f.val.app (.op Q) x = g.val.app (.op Q) x := by
  rw [h]

/-- **A finitely presented closed subscheme of a quasi-compact open extends to one of the whole
scheme.** For `X` quasi-compact and quasi-separated, `W ⊆ X` a quasi-compact open and
`k : Z' ⟶ W` a closed immersion of finite presentation, there is a quasi-coherent ideal `J` on
`X` with `J.subschemeι` of finite presentation whose inverse image on `W` is the ideal cut out
by `k`.

The ideal sheaf of `k` is quasi-coherent and of finite type ([Stacks, Tag 01TV]), so it extends
over `X` by [Stacks, Tag 01PF]; the extension cuts out a closed subscheme of `X`, and the
extension isomorphism identifies the two ideals on `W`. -/
@[sga "6 IX 1.1" "special case"]
private theorem exists_idealSheafData_comap_eq_ker {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (W : X.Opens) (hW : IsCompact (W : Set X))
    {Z' : Scheme.{u}} (k : Z' ⟶ W.toScheme) [IsClosedImmersion k]
    (hfp : FinitePresentation k) :
    ∃ J : X.IdealSheafData, FinitePresentation J.subschemeι ∧ J.comap W.ι = k.ker := by
  classical
  have hm : Mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom k.toLRSHom.toShHom)) ≫ (Scheme.Modules.restrictUnitIso W.ι).inv) :=
    mono_comp' inferInstance (Scheme.Modules.restrictUnitIso W.ι).isIso_inv.mono_of_iso
  obtain ⟨N, j, hmono, hqc, hft, e, he⟩ :=
    exists_module_extension (SheafOfModules.unit X.ringCatSheaf : X.Modules) inferInstance W hW
      (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom : W.toScheme.Modules)
      (Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf k)
      ((finitePresentation_iff_isFiniteType_idealSheaf k).mp hfp) _ hm
  obtain ⟨Z, i, hicl, eD, hD⟩ := exists_closedImmersion_idealSheaf_iso N j hmono hft
  have := hicl
  have hfpi : FinitePresentation i :=
    (finitePresentation_iff_isFiniteType_idealSheaf i).mpr
      (isFiniteType_of_iso_modules eD.symm hft)
  refine ⟨i.ker, (finitePresentation_subschemeι_iff_isFiniteType i.ker).mpr
    (isFiniteType_ker_of_finitePresentation i hfpi), ?_⟩
  have hcancelE : ∀ (Q : W.toScheme.Opens) (w),
      e.hom.val.app (.op Q) (e.inv.val.app (.op Q) w) = w :=
    fun Q w => val_app_apply_congr e.inv_hom_id Q w
  have h1 : eD.inv ≫ j = kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.toLRSHom.toShHom)) := by
    rw [← hD]
    exact Iso.inv_hom_id_assoc eD _
  have hsec : ∀ (Q : W.toScheme.Opens) x,
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom k.toLRSHom.toShHom))).val.app (.op Q)
          (e.hom.val.app (.op Q) (eD.inv.val.app (.op (W.ι ''ᵁ Q)) x)) =
        (W.ι.appIso Q).hom ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i.toLRSHom.toShHom))).val.app (.op (W.ι ''ᵁ Q)) x) := by
    intro Q x
    have hA : (W.ι.appIso Q).inv ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom k.toLRSHom.toShHom))).val.app (.op Q)
            (e.hom.val.app (.op Q) (eD.inv.val.app (.op (W.ι ''ᵁ Q)) x))) =
          j.val.app (.op (W.ι ''ᵁ Q)) (eD.inv.val.app (.op (W.ι ''ᵁ Q)) x) :=
      (val_app_apply_congr he Q _).symm
    have h1s : j.val.app (.op (W.ι ''ᵁ Q)) (eD.inv.val.app (.op (W.ι ''ᵁ Q)) x) =
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i.toLRSHom.toShHom))).val.app (.op (W.ι ''ᵁ Q)) x :=
      val_app_apply_congr h1 _ x
    rw [h1s] at hA
    exact ((W.ι.appIso Q).inv_hom_id_apply _).symm.trans (congrArg _ hA)
  refine ker_comap_eq_of_idealSheaf_sections W i k
    (fun Q x => e.hom.val.app (.op Q) (eD.inv.val.app (.op (W.ι ''ᵁ Q)) x))
    (fun Q y => eD.hom.val.app (.op (W.ι ''ᵁ Q)) (e.inv.val.app (.op Q) y)) hsec ?_
  intro Q y
  have h := hsec Q (eD.hom.val.app (.op (W.ι ''ᵁ Q)) (e.inv.val.app (.op Q) y))
  have hd : eD.inv.val.app (.op (W.ι ''ᵁ Q))
      (eD.hom.val.app (.op (W.ι ''ᵁ Q)) (e.inv.val.app (.op Q) y)) = e.inv.val.app (.op Q) y :=
    val_app_apply_congr eD.hom_inv_id _ _
  rw [hd, hcancelE] at h
  exact h.symm

/-- **The centre of an admissible blowup extends.** Let `X` be quasi-compact and
quasi-separated, let `U`, `V ⊆ X` be quasi-compact opens and let `I` be a quasi-coherent ideal
on `V` whose closed subscheme is of finite presentation and whose support avoids `U ∩ V`. Then
there is a quasi-coherent ideal `J` on `X` whose closed subscheme is of finite presentation,
whose support avoids `U`, and whose inverse image on `V` is `I`.

This is the content of the Stacks proof of [Stacks, Tag 080M] before blowing up: the ideal on
`U ∪ V` which is the unit ideal on `U` and `I` on `V` is the ideal cut out by the closed
immersion `V(I) ⟶ U ∪ V`, and that ideal extends to `X` by [Stacks, Tag 01PF]. -/
public theorem exists_idealSheafData_comap_eq {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U V : X.Opens) (hU : IsCompact (U : Set X))
    (hV : IsCompact (V : Set X)) (I : V.toScheme.IdealSheafData)
    (hfp : FinitePresentation I.subschemeι)
    (hdisj : Disjoint (V.ι ⁻¹ᵁ U : Set V) (I.support : Set V)) :
    ∃ J : X.IdealSheafData, FinitePresentation J.subschemeι ∧
      Disjoint (U : Set X) (J.support : Set X) ∧ J.comap V.ι = I := by
  have hW : IsCompact ((U ⊔ V : X.Opens) : Set X) := hU.union hV
  have hVcs : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have hWcs : CompactSpace (U ⊔ V : X.Opens).toScheme := isCompact_iff_compactSpace.mp hW
  have hWqs : QuasiSeparatedSpace (U ⊔ V : X.Opens).toScheme :=
    (U ⊔ V : X.Opens).ι.isOpenEmbedding.quasiSeparatedSpace
  have h1 : LocallyOfFinitePresentation I.subschemeι := hfp.1
  have h2 : QuasiCompact I.subschemeι := hfp.2.1
  have h3 : QuasiSeparated I.subschemeι := hfp.2.2
  have hcl : IsClosedImmersion (I.subschemeι ≫ X.homOfLE (le_sup_right : V ≤ U ⊔ V)) :=
    IsClosedImmersion.of_isPreimmersion _ (isClosed_range_subschemeι_homOfLE U V I hdisj)
  have hfpW : FinitePresentation (I.subschemeι ≫ X.homOfLE (le_sup_right : V ≤ U ⊔ V)) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨J, hJfp, hJker⟩ :=
    exists_idealSheafData_comap_eq_ker (U ⊔ V : X.Opens) hW
      (I.subschemeι ≫ X.homOfLE (le_sup_right : V ≤ U ⊔ V)) hfpW
  have hVcomp : X.homOfLE (le_sup_right : V ≤ U ⊔ V) ≫ (U ⊔ V : X.Opens).ι = V.ι := by
    simp [Scheme.homOfLE_ι]
  refine ⟨J, hJfp, ?_, ?_⟩
  · refine Set.disjoint_left.mpr fun x hxU hxJ ↦ ?_
    have hxW : x ∈ ((U ⊔ V : X.Opens) : Set X) := Or.inl hxU
    have hy : (⟨x, hxW⟩ : (U ⊔ V : X.Opens).toScheme) ∈
        ((I.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V))).support :
          Set (U ⊔ V : X.Opens).toScheme) := by
      rw [show I.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V)) = _ from hJker.symm,
        Scheme.IdealSheafData.support_comap]
      exact hxJ
    rw [Scheme.IdealSheafData.support_map] at hy
    have himage : (U ⊔ V : X.Opens).ι.base ⁻¹' (V.ι.base '' (I.support : Set V)) =
        (X.homOfLE (le_sup_right : V ≤ U ⊔ V)).base '' (I.support : Set V) := by
      ext z
      refine ⟨fun ⟨t, ht, hzt⟩ ↦ ⟨t, ht, (U ⊔ V : X.Opens).ι.isOpenEmbedding.injective ?_⟩,
        fun ⟨t, ht, htz⟩ ↦ ⟨t, ht, ?_⟩⟩
      · rw [← Scheme.Hom.comp_apply, hVcomp]; exact hzt
      · rw [← htz, ← Scheme.Hom.comp_apply, hVcomp]
    have hglob : x ∈ closure (V.ι.base '' (I.support : Set V)) := by
      have hpre : (⟨x, hxW⟩ : (U ⊔ V : X.Opens).toScheme) ∈ (U ⊔ V : X.Opens).ι.base ⁻¹'
          closure (V.ι.base '' (I.support : Set V)) := by
        rw [(U ⊔ V : X.Opens).ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
          (U ⊔ V : X.Opens).ι.continuous, himage]
        exact hy
      exact hpre
    exact (Set.disjoint_left.mp (disjoint_closure_image_support U V I hdisj)) hxU hglob
  · calc J.comap V.ι
        = J.comap (X.homOfLE (le_sup_right : V ≤ U ⊔ V) ≫ (U ⊔ V : X.Opens).ι) := by
          rw [hVcomp]
      _ = (J.comap (U ⊔ V : X.Opens).ι).comap (X.homOfLE (le_sup_right : V ≤ U ⊔ V)) := by
          rw [Scheme.IdealSheafData.comap_comp]
      _ = (I.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V))).comap
            (X.homOfLE (le_sup_right : V ≤ U ⊔ V)) := by rw [hJker]; rfl
      _ = I := comap_map_of_isOpenImmersion _ I

/-- **Stacks Project, Tag 080M.** A blowup admissible over the intersection of two quasi-compact
opens extends to a blowup of the ambient scheme admissible over the first open, with its
restriction to the second open given by a cartesian square. -/
@[stacks 080M]
public theorem exists_admissibleBlowup_isPullback
    {X V' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsCompact (U : Set X))
    (hV : IsCompact (V : Set X)) (b : V' ⟶ V.toScheme)
    (hb : IsAdmissibleBlowup (V.ι ⁻¹ᵁ U) b) :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X),
      IsAdmissibleBlowup U f ∧ ∃ g : V' ⟶ X', IsPullback b g V.ι f := by
  obtain ⟨I, hfp, hdisj, eB, heB⟩ := (isAdmissibleBlowup_iff (V.ι ⁻¹ᵁ U) b).mp hb
  obtain ⟨J, hJfp, hJdisj, hJcomap⟩ := exists_idealSheafData_comap_eq U V hU hV I hfp hdisj
  subst hJcomap
  refine ⟨AlgebraicGeometry.blowUp J, AlgebraicGeometry.blowUpToBase J,
    (isAdmissibleBlowup_iff U _).mpr ⟨J, hJfp, hJdisj, Iso.refl _, Category.id_comp _⟩, ?_⟩
  obtain ⟨h₀, hpb₀⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap V.ι J
  have hsq : CommSq b (eB.hom ≫ h₀) V.ι (AlgebraicGeometry.blowUpToBase J) :=
    ⟨by rw [← heB, Category.assoc, Category.assoc, hpb₀.w]⟩
  have hcanon := IsPullback.of_hasPullback V.ι (AlgebraicGeometry.blowUpToBase J)
  refine ⟨eB.hom ≫ h₀, IsPullback.of_iso_pullback hsq
    (eB ≪≫ hpb₀.isoIsPullback _ _ hcanon) ?_ ?_⟩
  · rw [Iso.trans_hom, Category.assoc, hpb₀.isoIsPullback_hom_fst _ _ hcanon, heB]
  · rw [Iso.trans_hom, Category.assoc, hpb₀.isoIsPullback_hom_snd _ _ hcanon]

end Stacks.Blowup

end
