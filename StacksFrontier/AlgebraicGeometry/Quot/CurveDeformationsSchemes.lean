module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyTotalScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Thickenings.NilIdeal
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFiniteness
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Examples.Geometric.SchemesDeformationCategory
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFromThickening
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreBoundary
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecFiniteCover

/-!
# Deformations of a family of curves over a field are deformations of a scheme

Let `x` be a family of curves over the spectrum of a field `k`, with underlying scheme `X` over
`Spec k`. Every deformation of `x` over an object `A` of `𝒞_Λ` has a total space that is a scheme,
and this gives a deformation of `X` over `A`. The resulting functor from the predeformation
category `𝓕_{𝒳,k,x}` to the deformation category of `X` is fully faithful and essentially
surjective.

## Main definitions

* `CurveDeformation.toSchemeDeformationFunctor`: The functor from `𝓕_{𝒳,k,x}` to the
  deformation category of the scheme underlying `x`.

## Main results

* `CurveDeformation.toSchemeDeformationFunctor_faithful`: The functor is faithful.
* `CurveDeformation.toSchemeDeformationFunctor_full`: The functor is full.
* `CurveDeformation.toSchemeDeformationFunctor_essSurj`: Every deformation of the scheme
  underlying `x` is isomorphic to the image of a deformation of `x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

set_option synthInstance.maxHeartbeats 400000 in
/-- Products of presheaves on the big fppf site of the integers (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_CurveDeformationsSchemes
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- A morphism of the underlying schemes of two objects of the big fppf site of the integers is
a morphism of the site: every scheme lies over the terminal scheme `Spec ℤ` in a unique way. -/
def integerSiteHom {U V : BigFppfOver B integerBase hZ}
    (g : (BigFppfOver.toScheme B integerBase hZ).obj U ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj V) : U ⟶ V :=
  Over.homMk (ObjectProperty.homMk g) (by
    apply ObjectProperty.hom_ext
    exact specULiftZIsTerminal.hom_ext _ _)

/-- The morphism of schemes underlying `integerSiteHom g` is `g`. -/
@[simp]
theorem toScheme_map_integerSiteHom {U V : BigFppfOver B integerBase hZ}
    (g : (BigFppfOver.toScheme B integerBase hZ).obj U ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj V) :
    (BigFppfOver.toScheme B integerBase hZ).map (integerSiteHom g) = g := rfl

/-- A morphism of the big fppf site of the integers is `integerSiteHom` of its underlying
morphism of schemes. -/
theorem integerSiteHom_toScheme_map {U V : BigFppfOver B integerBase hZ} (f : U ⟶ V) :
    integerSiteHom ((BigFppfOver.toScheme B integerBase hZ).map f) = f := rfl

namespace CurveFamily

variable {y : CurveFamily B hZ} (hy : y.total.obj.IsRepresentable)

/-- The object of the site representing the total space of a family of curves whose total
space is representable. -/
def totalSite : BigFppfOver B integerBase hZ :=
  haveI := hy
  y.total.obj.reprX

/-- The identification of the total space of a family of curves with the presheaf of points of
the object representing it. -/
def totalSiteIso : yoneda.obj (totalSite hy) ≅ y.total.obj :=
  haveI := hy
  y.total.obj.reprW

/-- The structure morphism of a family of curves with representable total space, as a morphism
of the site. -/
def totalSiteToBase : totalSite hy ⟶ y.base :=
  yoneda.preimage ((totalSiteIso hy).hom ≫ y.toBase.hom)

/-- Under the Yoneda embedding, `totalSiteToBase` is the structure morphism of the family composed
with the identification `totalSiteIso`. -/
theorem yoneda_map_totalSiteToBase :
    yoneda.map (totalSiteToBase hy) = (totalSiteIso hy).hom ≫ y.toBase.hom :=
  yoneda.map_preimage _

variable {x : CurveFamily B hZ} (hx : x.total.obj.IsRepresentable)

/-- The morphism of total spaces of a morphism of families of curves with representable total
spaces, as a morphism of the site. -/
def totalSiteMap (φ : x ⟶ y) : totalSite hx ⟶ totalSite hy :=
  yoneda.preimage ((totalSiteIso hx).hom ≫ φ.totalMap.hom ≫ (totalSiteIso hy).inv)

/-- Under the Yoneda embedding, `totalSiteMap φ` is the morphism of total spaces of `φ`
conjugated by the identifications `totalSiteIso`. -/
theorem yoneda_map_totalSiteMap (φ : x ⟶ y) :
    yoneda.map (totalSiteMap hy hx φ) =
      (totalSiteIso hx).hom ≫ φ.totalMap.hom ≫ (totalSiteIso hy).inv :=
  yoneda.map_preimage _

/-- The square of a morphism of families of curves with representable total spaces, read in the
site, is cartesian. -/
theorem isPullback_totalSite (φ : x ⟶ y) :
    IsPullback (totalSiteMap hy hx φ) (totalSiteToBase hx) (totalSiteToBase hy) φ.baseMap := by
  have h1 := AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
  have h2 : IsPullback (yoneda.map (totalSiteMap hy hx φ)) (yoneda.map (totalSiteToBase hx))
      (yoneda.map (totalSiteToBase hy)) (yoneda.map φ.baseMap) := by
    refine IsPullback.of_iso h1 (totalSiteIso hx).symm (totalSiteIso hy).symm (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [yoneda_map_totalSiteMap]
    · simp only [Iso.refl_hom, Iso.symm_hom, yoneda_map_totalSiteToBase, cancelIso]
      exact Category.comp_id _
    · simp only [Iso.refl_hom, Iso.symm_hom, yoneda_map_totalSiteToBase, cancelIso]
      exact Category.comp_id _
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact IsPullback.of_map yoneda (yoneda.map_injective (by
    simpa only [Functor.map_comp] using h2.w)) h2

/-- `totalSiteMap` is compatible with composition of morphisms of families of curves. -/
theorem totalSiteMap_comp {z : CurveFamily B hZ} (hz : z.total.obj.IsRepresentable)
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    totalSiteMap hy hx φ ≫ totalSiteMap hz hy ψ = totalSiteMap hz hx (φ ≫ ψ) := by
  apply yoneda.map_injective
  rw [Functor.map_comp, yoneda_map_totalSiteMap, yoneda_map_totalSiteMap,
    yoneda_map_totalSiteMap]
  show _ = (totalSiteIso hx).hom ≫ (φ.totalMap.hom ≫ ψ.totalMap.hom) ≫ (totalSiteIso hz).inv
  simp

/-- `totalSiteMap` sends the identity of a family of curves to the identity. -/
theorem totalSiteMap_id : totalSiteMap hy hy (𝟙 y) = 𝟙 (totalSite hy) := by
  apply yoneda.map_injective
  rw [yoneda_map_totalSiteMap, CategoryTheory.Functor.map_id]
  show (totalSiteIso hy).hom ≫ 𝟙 _ ≫ (totalSiteIso hy).inv = 𝟙 _
  simp

/-- A property of morphisms of presheaves respecting isomorphisms that holds for the structure
morphism of a family of curves holds for the Yoneda image of `totalSiteToBase`. -/
private theorem yoneda_map_totalSiteToBase_of_respectsIso
    (P : MorphismProperty ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    (h : P y.toBase.hom) : P (yoneda.map (totalSiteToBase hy)) := by
  rw [yoneda_map_totalSiteToBase]
  exact (P.cancel_left_of_respectsIso (totalSiteIso hy).hom y.toBase.hom).mpr h

/-- The chartwise version of `yoneda_map_totalSiteToBase_of_respectsIso`. -/
private theorem holdsOnEveryEtaleChart_yoneda_map_totalSiteToBase (Q : MorphismProperty Scheme.{u})
    (h : Space.HoldsOnEveryEtaleChart B integerBase hZ Q y.toBase.hom) :
    Space.HoldsOnEveryEtaleChart B integerBase hZ Q (yoneda.map (totalSiteToBase hy)) :=
  haveI := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B integerBase hZ Q
  yoneda_map_totalSiteToBase_of_respectsIso hy
    (fun _ _ g => Space.HoldsOnEveryEtaleChart B integerBase hZ Q g) h

/-- The structure morphism of a family of curves with representable total space is flat as a
morphism of schemes. -/
theorem flat_toScheme_map_totalSiteToBase :
    Flat ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy)) :=
  Space.flat_of_isFlat_yoneda _ _ _ _ _ _
    (holdsOnEveryEtaleChart_yoneda_map_totalSiteToBase hy _ y.flat)

/-- The structure morphism of a family of curves with representable total space is proper as a
morphism of schemes. -/
theorem isProper_toScheme_map_totalSiteToBase :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy)) := by
  have hsep : Space.IsSeparated B integerBase hZ (yoneda.map (totalSiteToBase hy)) :=
    haveI := Space.isSeparated_respectsIso B integerBase hZ
    yoneda_map_totalSiteToBase_of_respectsIso hy (@Space.IsSeparated B integerBase hZ) y.proper.1
  have huc : Space.UniversallyClosed B integerBase hZ (yoneda.map (totalSiteToBase hy)) :=
    haveI := Space.universallyClosed_respectsIso B integerBase hZ
    yoneda_map_totalSiteToBase_of_respectsIso hy (@Space.UniversallyClosed B integerBase hZ)
      y.proper.2.2
  have hlft := holdsOnEveryEtaleChart_yoneda_map_totalSiteToBase hy _ y.proper.2.1.1
  have hrep : yoneda.relativelyRepresentable (yoneda.map (totalSiteToBase hy)) :=
    Functor.relativelyRepresentable.map _ _
  have hUC := (Space.presheaf_yoneda_map_iff B integerBase hZ
    (P := @AlgebraicGeometry.UniversallyClosed.{u}) inferInstance (totalSiteToBase hy)).mp
    ((Space.presheaf_universallyClosed_iff B integerBase hZ (isAlgebraicSpace_yoneda _ _ _ _)
      (isAlgebraicSpace_yoneda _ _ _ _) hrep).mpr huc)
  have : IsSeparated ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy)) :=
    (Space.isSeparated_yoneda_map_iff B integerBase hZ _).mp hsep
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy)) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget _).mp hlft
  exact ⟨⟩

/-- The structure morphism of a family of curves with representable total space is locally of
finite presentation as a morphism of schemes. -/
theorem locallyOfFinitePresentation_toScheme_map_totalSiteToBase :
    LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy)) :=
  (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget _).mp
    (holdsOnEveryEtaleChart_yoneda_map_totalSiteToBase hy _ y.finitePresentation.1)

end CurveFamily

/-- A square of the site whose underlying square of schemes is cartesian represents a cartesian
square of algebraic spaces. -/
theorem isPullback_schemeSpaceMap {S : Scheme.{u}} {hS : B.Contains S}
    {P Q R W : BigFppfOver B S hS} {a : P ⟶ Q} {b : P ⟶ R} {c : Q ⟶ W} {d : R ⟶ W}
    (h : IsPullback a b c d) :
    IsPullback (schemeSpaceMap a) (schemeSpaceMap b) (schemeSpaceMap c) (schemeSpaceMap d) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) (h.map yoneda)

/-- A module of finite length over a local ring is no larger than the countable power of the
larger of `ℵ₀` and the residue field. -/
theorem _root_.Cardinal.mk_le_of_isFiniteLength {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Cardinal.mk M ≤ (max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField R))) ^
      Cardinal.aleph0 := by
  classical
  set κ := max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField R))
  have hκ : Cardinal.aleph0 ≤ κ := le_max_left _ _
  have hκ0 : κ ≠ 0 := ne_of_gt (lt_of_lt_of_le Cardinal.aleph0_pos hκ)
  induction hM with
  | @of_subsingleton M _ _ hsub =>
      exact (Cardinal.le_one_iff_subsingleton.mpr hsub).trans
        (Cardinal.one_le_iff_ne_zero.mpr (Cardinal.power_ne_zero _ hκ0))
  | @of_simple_quotient M _ _ N _ _ ih =>
      obtain ⟨J, hJ, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
        (inferInstance : IsSimpleModule R (M ⧸ N))
      have hq : Cardinal.mk (M ⧸ N) ≤ κ := by
        rw [Cardinal.mk_congr e.toEquiv, IsLocalRing.eq_maximalIdeal hJ]
        exact le_max_right _ _
      have hsplit : Cardinal.mk M ≤ Cardinal.mk (M ⧸ N) * Cardinal.mk N := by
        rw [← Cardinal.mk_congr (AddSubgroup.addGroupEquivQuotientProdAddSubgroup
          (s := N.toAddSubgroup)).symm, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
        rfl
      calc Cardinal.mk M ≤ Cardinal.mk (M ⧸ N) * Cardinal.mk N := hsplit
        _ ≤ κ * κ ^ Cardinal.aleph0 := mul_le_mul' hq ih
        _ = κ ^ 1 * κ ^ Cardinal.aleph0 := by simp
        _ = κ ^ (1 + Cardinal.aleph0) := (Cardinal.power_add κ 1 Cardinal.aleph0).symm
        _ = κ ^ Cardinal.aleph0 := congrArg (fun α : Cardinal => κ ^ α)
          (Cardinal.nat_add_aleph0 (1 : ℕ))

/-- The spectrum of an object of `𝒞_Λ` lies in a big fppf site containing the spectrum of the
residue field. -/
theorem contains_spec_of_artinianLocalAlgCat {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) (hk : B.Contains (Spec (.of k))) :
    B.Contains (Spec (.of A)) := by
  apply Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hk
  have h := Cardinal.mk_le_of_isFiniteLength
    ((isArtinianRing_iff_isFiniteLength A).mp inferInstance)
  rw [Cardinal.mk_congr A.residueEquiv.toEquiv] at h
  refine h.trans (Cardinal.power_le_power_right (max_le (Scheme.aleph0_le_size _) ?_))
  rw [Scheme.size_Spec]
  exact le_max_right _ _

/-- The spectrum of the residue map of an Artinian local ring is a thickening. -/
theorem isThickening_specMap_residueMap {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Stacks.Thickenings.IsThickening
      (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A))) := by
  have hsurj : Function.Surjective (Deformation.Artin.residueMap A) :=
    A.residueEquiv.surjective.comp IsLocalRing.residue_surjective
  refine ⟨IsClosedImmersion.spec_of_surjective _ hsurj, ?_⟩
  have hsub : Subsingleton (PrimeSpectrum A) := by
    refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
    have hp := (IsArtinianRing.isMaximal_of_isPrime p.asIdeal)
    have hq := (IsArtinianRing.isMaximal_of_isPrime q.asIdeal)
    rw [IsLocalRing.eq_maximalIdeal hp, IsLocalRing.eq_maximalIdeal hq]
  intro p
  obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact ⟨t, @Subsingleton.elim (PrimeSpectrum A) hsub _ _⟩

/-- A thickening stays a thickening after composition with isomorphisms on both sides. -/
theorem isThickening_iso_comp_comp_iso {X X' Y Y' : Scheme.{u}} (e : X ≅ X') (g : X' ⟶ Y')
    (e' : Y' ≅ Y) (hg : Stacks.Thickenings.IsThickening g) :
    Stacks.Thickenings.IsThickening (e.hom ≫ g ≫ e'.hom) := by
  have := hg.1
  have : Surjective g := ⟨hg.2⟩
  exact ⟨inferInstance, (inferInstance : Surjective (e.hom ≫ g ≫ e'.hom)).surj⟩

open Deformation.Examples in
/-- Two deformations of a scheme over the same object of `𝒞_Λ` whose total spaces are identified
compatibly with the structure morphisms and the closed immersions of the special fibre are
isomorphic. -/
def _root_.Deformation.Examples.SchemeDeformationCategory.isoOfSchemeIso {Λ k : Type u} [CommRing Λ]
    [Field k] [Algebra Λ k] {X : Over (Spec (.of k))} {Q P : SchemeDeformationCategory (Λ := Λ) X}
    (hb : Q.base = P.base) (ι : Q.scheme ≅ P.scheme)
    (htb : HEq Q.toBase (ι.hom ≫ P.toBase))
    (hsp : Q.specialMap = P.specialMap ≫ ι.inv) : Q ≅ P := by
  obtain ⟨A, Y, t, ht, s, hs⟩ := Q
  obtain ⟨A', Y', t', ht', s', hs'⟩ := P
  change A = A' at hb
  subst hb
  replace htb : t = ι.hom ≫ t' := eq_of_heq htb
  change s = s' ≫ ι.inv at hsp
  exact
    { hom :=
        { base := 𝟙 _
          map := ι.inv
          cartesian := by
            rw [baseSpecMap_id]
            exact IsPullback.of_horiz_isIso ⟨by
              change ι.inv ≫ t = t' ≫ 𝟙 _
              exact (congrArg (ι.inv ≫ ·) htb).trans (by simp)⟩
          special_compat := hsp.symm }
      inv :=
        { base := 𝟙 _
          map := ι.hom
          cartesian := by
            rw [baseSpecMap_id]
            exact IsPullback.of_horiz_isIso ⟨by
              change ι.hom ≫ t' = t ≫ 𝟙 _
              exact (by simp : ι.hom ≫ t' = (ι.hom ≫ t') ≫ 𝟙 _).trans
                (congrArg (· ≫ 𝟙 _) htb.symm)⟩
          special_compat := by
            change s ≫ ι.hom = s'
            exact (congrArg (· ≫ ι.hom) hsp).trans (by simp) }
      hom_inv_id := by
        apply SchemeDeformationCategory.Hom.ext
        · exact Category.comp_id _
        · exact ι.hom_inv_id
      inv_hom_id := by
        apply SchemeDeformationCategory.Hom.ext
        · exact Category.comp_id _
        · exact ι.inv_hom_id }

namespace CurveDeformation

variable (B hZ)

/-- The functor from families of curves to schemes over `Spec ℤ` along which the deformation
category of a family of curves over a field is formed. -/
abbrev projection : CurveFamily B hZ ⥤ Over integerBase :=
  curvesProjectionOver B hZ ⋙ Over.post B.inclusion

variable {B hZ} {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {iΛ : Spec (.of Λ) ⟶ integerBase} (x : CurveFamily B hZ)
  (hx : (projection B hZ).obj x = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The deformations of `x`, the objects of `𝓕_{𝒳,k,x}`. -/
abbrev Obj := Deformation.Artin.DeformationObject iΛ (projection B hZ) x hx

include hx in
/-- The base scheme of `x` is `Spec k`. -/
theorem baseScheme_eq :
    (BigFppfOver.toScheme B integerBase hZ).obj x.base = Spec (.of k) :=
  congrArg Over.left hx

/-- The base scheme of a deformation of `x` is the spectrum of its Artinian local algebra. -/
theorem baseScheme_eq_obj (a : Obj x hx) :
    (BigFppfOver.toScheme B integerBase hZ).obj a.point.base = Spec (.of a.algebra) :=
  congrArg Over.left a.base

include hx in
/-- The total space of `x` is representable by a scheme. -/
theorem isRepresentable_total : x.total.obj.IsRepresentable :=
  x.isRepresentable_total_of_base_eq (baseScheme_eq x hx)

/-- The base map of a deformation of `x` is the residue map of its Artinian local algebra, up to
the identifications of the two base schemes. -/
theorem toScheme_map_baseMap (a : Obj x hx) :
    (BigFppfOver.toScheme B integerBase hZ).map a.arrow.baseMap =
      eqToHom (baseScheme_eq x hx) ≫
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap a.algebra)) ≫
          eqToHom (baseScheme_eq_obj x hx a).symm := by
  rw [← a.arrow_base]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  rfl

/-- The base map of a deformation of `x` is a thickening of schemes. -/
theorem isThickening_baseMap (a : Obj x hx) :
    Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B integerBase hZ).map a.arrow.baseMap) := by
  rw [toScheme_map_baseMap]
  exact isThickening_iso_comp_comp_iso (eqToIso (baseScheme_eq x hx)) _
    (eqToIso (baseScheme_eq_obj x hx a).symm) (isThickening_specMap_residueMap a.algebra)

/-- The total space of a deformation of `x` is representable by a scheme. -/
theorem isRepresentable_total_obj (a : Obj x hx) : a.point.total.obj.IsRepresentable :=
  CurveFamily.isRepresentable_total_of_hom a.arrow (isThickening_baseMap x hx a)
    (isRepresentable_total x hx)

/-- The scheme `X` underlying the family of curves `x` over `Spec k`. -/
abbrev scheme : Over (Spec (.of k)) :=
  Over.mk ((BigFppfOver.toScheme B integerBase hZ).map
    (CurveFamily.totalSiteToBase (isRepresentable_total x hx)) ≫ eqToHom (baseScheme_eq x hx))

open Deformation.Examples in
/-- The scheme deformation of `X` attached to a deformation of the family of curves `x`: its
total space, which is a scheme, over the spectrum of the Artinian local algebra. -/
def toSchemeDeformation (a : Obj x hx) :
    SchemeDeformationCategory (Λ := Λ) (scheme x hx) where
  base := a.algebra
  scheme := (BigFppfOver.toScheme B integerBase hZ).obj
    (CurveFamily.totalSite (isRepresentable_total_obj x hx a))
  toBase := (BigFppfOver.toScheme B integerBase hZ).map
    (CurveFamily.totalSiteToBase (isRepresentable_total_obj x hx a)) ≫
      eqToHom (baseScheme_eq_obj x hx a)
  flat := by
    have := CurveFamily.flat_toScheme_map_totalSiteToBase (isRepresentable_total_obj x hx a)
    infer_instance
  specialMap := (BigFppfOver.toScheme B integerBase hZ).map
    (CurveFamily.totalSiteMap (isRepresentable_total_obj x hx a) (isRepresentable_total x hx)
      a.arrow)
  specialCartesian := by
    have hsq := (CurveFamily.isPullback_totalSite (isRepresentable_total_obj x hx a)
      (isRepresentable_total x hx) a.arrow).map (BigFppfOver.toScheme B integerBase hZ)
    refine IsPullback.of_iso hsq (Iso.refl _) (Iso.refl _) (eqToIso (baseScheme_eq x hx))
      (eqToIso (baseScheme_eq_obj x hx a)) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · simp [scheme]
    · simp
    · rw [toScheme_map_baseMap]
      simp

/-- The morphisms of deformations of `x`. -/
abbrev Hom (a b : Obj x hx) :=
  Deformation.Artin.DeformationMorphism iΛ (projection B hZ) x hx a b

/-- The base map of a morphism of deformations of `x` is the spectrum of its arrow of `𝒞_Λ`, up
to the identifications of the base schemes. -/
theorem toScheme_map_arrow_baseMap {a b : Obj x hx} (m : Hom x hx a b) :
    (BigFppfOver.toScheme B integerBase hZ).map m.arrow.baseMap =
      eqToHom (baseScheme_eq_obj x hx b) ≫
        Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
          eqToHom (baseScheme_eq_obj x hx a).symm := by
  rw [← m.arrow_base]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  rfl

open Deformation.Examples in
/-- The morphism of scheme deformations attached to a morphism of deformations of `x`. -/
def toSchemeDeformationHom {a b : Obj x hx} (m : Hom x hx a b) :
    SchemeDeformationCategory.Hom (toSchemeDeformation x hx a) (toSchemeDeformation x hx b) where
  base := m.ringHom
  map := (BigFppfOver.toScheme B integerBase hZ).map
    (CurveFamily.totalSiteMap (isRepresentable_total_obj x hx a) (isRepresentable_total_obj x hx b)
      m.arrow)
  cartesian := by
    have hsq := (CurveFamily.isPullback_totalSite (isRepresentable_total_obj x hx a)
      (isRepresentable_total_obj x hx b) m.arrow).map (BigFppfOver.toScheme B integerBase hZ)
    refine IsPullback.of_iso hsq (Iso.refl _) (Iso.refl _) (eqToIso (baseScheme_eq_obj x hx b))
      (eqToIso (baseScheme_eq_obj x hx a)) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · simp [toSchemeDeformation]
    · simp [toSchemeDeformation]
    · rw [toScheme_map_arrow_baseMap]
      change (eqToHom (baseScheme_eq_obj x hx b) ≫
          Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
            eqToHom (baseScheme_eq_obj x hx a).symm) ≫ eqToHom (baseScheme_eq_obj x hx a) =
        eqToHom (baseScheme_eq_obj x hx b) ≫ Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom)
      simp
  special_compat := by
    change (BigFppfOver.toScheme B integerBase hZ).map _ ≫
      (BigFppfOver.toScheme B integerBase hZ).map _ =
        (BigFppfOver.toScheme B integerBase hZ).map _
    rw [← Functor.map_comp, CurveFamily.totalSiteMap_comp, m.triangle]

/-- The predeformation category `𝓕_{𝒳,k,x}` of the family of curves `x`. -/
abbrev predeformation :=
  Deformation.Artin.predeformationCategory iΛ (projection B hZ) x hx

open Deformation.Examples in
/-- **Deformations of a family of curves over a field are deformations of a scheme.** The
functor from `𝓕_{𝒳,k,x}` to the deformation category of the scheme underlying `x`. -/
def toSchemeDeformationFunctor :
    letI := (predeformation x hx).category
    (predeformation x hx).carrier ⥤ SchemeDeformationCategory (Λ := Λ) (scheme x hx) :=
  letI := (predeformation x hx).category
  { obj := fun a => toSchemeDeformation x hx a
    map := fun {a b} m => toSchemeDeformationHom x hx m
    map_id := fun a => by
      apply SchemeDeformationCategory.Hom.ext
      · rfl
      · change (BigFppfOver.toScheme B integerBase hZ).map
          (CurveFamily.totalSiteMap _ _ (𝟙 a.point)) = 𝟙 _
        rw [CurveFamily.totalSiteMap_id, CategoryTheory.Functor.map_id]
    map_comp := fun {a b c} f g => by
      apply SchemeDeformationCategory.Hom.ext
      · rfl
      · change (BigFppfOver.toScheme B integerBase hZ).map
          (CurveFamily.totalSiteMap _ _ (g.arrow ≫ f.arrow)) =
          (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap _ _ g.arrow) ≫
            (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap _ _ f.arrow)
        rw [← Functor.map_comp, CurveFamily.totalSiteMap_comp] }

open Deformation.Examples in
/-- The functor `toSchemeDeformationFunctor` commutes with the projections to `𝒞_Λ`. -/
theorem toSchemeDeformationFunctor_comp_projection :
    letI := (predeformation x hx).category
    toSchemeDeformationFunctor x hx ⋙ schemeDeformationCategoryProjection (scheme x hx) =
      (predeformation x hx).projection :=
  rfl

/-! ### Essential surjectivity -/

section EssSurj

open Deformation.Examples

include hx in
/-- The big fppf site contains `Spec k`. -/
theorem contains_spec_residue : B.Contains (Spec (.of k)) :=
  baseScheme_eq x hx ▸ x.base.left.property

variable (P : SchemeDeformationCategory (Λ := Λ) (scheme x hx))

/-- The cartesian finite-order deformation diagram of a scheme deformation of `X`: the scheme
deformation over the thickening `Spec k ⊆ Spec A` of its base. -/
def deformationDiagram : Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.{u} where
  S := Spec (.of k)
  S' := baseSpec P.base
  iS := residueSpecMap P.base
  iS_finiteOrder :=
    Stacks.Thickenings.isFiniteOrderThickening_of_isThickening_of_isNoetherianRing
      (isThickening_specMap_residueMap P.base)
      (isNoetherianRing_of_ringEquiv _
        (Scheme.ΓSpecIso (.of P.base)).symm.commRingCatIsoToRingEquiv)
  X := (scheme x hx).left
  X' := P.scheme
  iX := P.specialMap
  iX_thickening := Stacks.Thickenings.isThickening_of_isPullback P.specialCartesian
    (isThickening_specMap_residueMap P.base)
  Y := Spec (.of k)
  Y' := baseSpec P.base
  iY := residueSpecMap P.base
  iY_thickening := isThickening_specMap_residueMap P.base
  pX := (scheme x hx).hom
  pX' := P.toBase
  pY := 𝟙 _
  pY' := 𝟙 _
  f := (scheme x hx).hom
  f' := P.toBase
  f_over_S := Category.comp_id _
  f'_over_S' := Category.comp_id _
  f_thickening_comm := P.specialCartesian.w.symm
  X_cartesian := P.specialCartesian
  Y_cartesian := IsPullback.of_vert_isIso ⟨by simp⟩
  X'_flat := P.flat

include hx in
/-- The scheme `X` underlying `x` is proper over `Spec k`. -/
theorem isProper_scheme_hom : IsProper (scheme x hx).hom :=
  (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).mpr
    (CurveFamily.isProper_toScheme_map_totalSiteToBase (isRepresentable_total x hx))

include hx in
/-- The scheme `X` underlying `x` is locally of finite presentation over `Spec k`. -/
theorem locallyOfFinitePresentation_scheme_hom :
    LocallyOfFinitePresentation (scheme x hx).hom :=
  @locallyOfFinitePresentation_comp _ _ _ _ _
    (CurveFamily.locallyOfFinitePresentation_toScheme_map_totalSiteToBase
      (isRepresentable_total x hx)) inferInstance

/-- The structure morphism of a scheme deformation of `X` is proper. -/
theorem isProper_toBase : IsProper P.toBase :=
  (deformationDiagram x hx P).isProper_iff.mp (isProper_scheme_hom x hx)

/-- The structure morphism of a scheme deformation of `X` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_toBase : LocallyOfFinitePresentation P.toBase :=
  (deformationDiagram x hx P).locallyOfFinitePresentation_iff.mp
    (locallyOfFinitePresentation_scheme_hom x hx)

/-- The big fppf site contains the base of a scheme deformation of `X`. -/
theorem contains_spec_base : B.Contains (Spec (.of P.base)) :=
  contains_spec_of_artinianLocalAlgCat P.base (contains_spec_residue x hx)

/-- The big fppf site contains the total space of a scheme deformation of `X`. -/
theorem contains_scheme : B.Contains P.scheme := by
  have := isProper_toBase x hx P
  exact lt_of_le_of_lt (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact P.toBase)
    (contains_spec_base x hx P)

include hx in
/-- The scheme `X` underlying `x` has Krull dimension at most one. -/
theorem topologicalKrullDim_scheme_le : topologicalKrullDim (scheme x hx).left ≤ 1 := by
  have hxr := isRepresentable_total x hx
  have h1 := Space.dimension_yoneda_eq_topologicalKrullDim B integerBase hZ
    (CurveFamily.totalSite hxr)
  have h2 := Space.dimension_eq_of_iso B integerBase hZ (isAlgebraicSpace_yoneda _ _ _ _)
    x.total.property (CurveFamily.totalSiteIso hxr)
  have h3 := Space.dimension_eq_iSup_localRingDimension B integerBase hZ x.total.obj
    x.total.property
  show topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj
    (CurveFamily.totalSite hxr)) ≤ 1
  rw [← h1, h2, h3]
  exact iSup_le fun y => by
    exact_mod_cast x.localRingDimension_le_one_of_base_eq (baseScheme_eq x hx) y

/-- The total space of a scheme deformation of `X` has Krull dimension at most one. -/
theorem topologicalKrullDim_le : topologicalKrullDim P.scheme ≤ 1 := by
  have h := IsHomeomorph.topologicalKrullDim_eq _
    ((deformationDiagram x hx P).iX_thickening.homeomorph).isHomeomorph
  calc topologicalKrullDim P.scheme = topologicalKrullDim (scheme x hx).left := h.symm
    _ ≤ 1 := topologicalKrullDim_scheme_le x hx

/-- The base of a scheme deformation, as an object of the site. -/
abbrev baseSiteObj : BigFppfOver B integerBase hZ :=
  (schemeOverIntegers B).obj (B.obj (contains_spec_base x hx P))

/-- The total space of a scheme deformation, as an object of the site. -/
abbrev totalSiteObj : BigFppfOver B integerBase hZ :=
  (schemeOverIntegers B).obj (B.obj (contains_scheme x hx P))

/-- The structure morphism of a scheme deformation, as a morphism of the site. -/
abbrev toBaseSiteObj : totalSiteObj x hx P ⟶ baseSiteObj x hx P :=
  integerSiteHom P.toBase

/-- The family of curves of `curveFamilyOfSchemeMorphism` at a scheme deformation. -/
def curveFamilyAux : CurveFamily B hZ :=
  haveI hp : IsProper ((BigFppfOver.toScheme B integerBase hZ).map (toBaseSiteObj x hx P)) :=
    isProper_toBase x hx P
  curveFamilyOfSchemeMorphism B hZ (toBaseSiteObj x hx P) P.flat hp
    (locallyOfFinitePresentation_toBase x hx P)
    (Space.isQuasiCompact_yoneda_map B integerBase hZ _ inferInstance)
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ _).mpr inferInstance)
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ _).mpr inferInstance)
    (topologicalKrullDim_le x hx P)

/-- **A scheme deformation of `X` is a family of curves.** -/
abbrev curveFamily : CurveFamily B hZ where
  base := baseSiteObj x hx P
  total := schemeSpace (totalSiteObj x hx P)
  toBase := schemeSpaceMap (toBaseSiteObj x hx P)
  flat := (curveFamilyAux x hx P).flat
  proper := (curveFamilyAux x hx P).proper
  finitePresentation := (curveFamilyAux x hx P).finitePresentation
  relativeDimensionLE := (curveFamilyAux x hx P).relativeDimensionLE

/-- The closed immersion of `X` into a scheme deformation, as a morphism of the site. -/
abbrev specialSiteMap :
    CurveFamily.totalSite (isRepresentable_total x hx) ⟶ totalSiteObj x hx P :=
  integerSiteHom P.specialMap

/-- The base map of the family of curves of a scheme deformation: the closed point. -/
def baseMapToCurveFamily : x.base ⟶ baseSiteObj x hx P :=
  integerSiteHom (eqToHom (baseScheme_eq x hx) ≫ residueSpecMap P.base)

/-- The square identifying `x` with the special fibre of the family of curves of a scheme
deformation, in the site. -/
theorem isPullback_site :
    IsPullback (specialSiteMap x hx P)
      (CurveFamily.totalSiteToBase (isRepresentable_total x hx)) (toBaseSiteObj x hx P)
      (baseMapToCurveFamily x hx P) := by
  apply FiniteFreeAlgebra.isPullback_of_isPullback_toScheme
  refine IsPullback.of_iso P.specialCartesian (Iso.refl _) (Iso.refl _)
    (eqToIso (baseScheme_eq x hx).symm) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · simp [scheme]
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · show residueSpecMap P.base ≫ 𝟙 _ =
      eqToHom (baseScheme_eq x hx).symm ≫ (eqToHom (baseScheme_eq x hx) ≫ residueSpecMap P.base)
    simp

/-- The identification of the total space of `x` with the presheaf of points of the scheme
representing it, as an isomorphism of algebraic spaces. -/
def totalIso : schemeSpace (CurveFamily.totalSite (isRepresentable_total x hx)) ≅ x.total :=
  ObjectProperty.isoMk _ (CurveFamily.totalSiteIso (isRepresentable_total x hx))

/-- The morphism from `x` to the family of curves of a scheme deformation. -/
def arrowToCurveFamily : x ⟶ curveFamily x hx P where
  baseMap := baseMapToCurveFamily x hx P
  totalMap := (totalIso x hx).inv ≫ schemeSpaceMap (integerSiteHom (V := totalSiteObj x hx P)
    P.specialMap)
  cartesian := by
    refine IsPullback.of_iso (isPullback_schemeSpaceMap (isPullback_site x hx P)) (totalIso x hx)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc (totalIso x hx) _).symm
    · apply ObjectProperty.hom_ext
      change yoneda.map (CurveFamily.totalSiteToBase (isRepresentable_total x hx)) ≫ 𝟙 _ = _
      rw [Category.comp_id, CurveFamily.yoneda_map_totalSiteToBase]
      rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The deformation of `x` attached to a scheme deformation of `X`. -/
abbrev toObj : Obj x hx where
  algebra := P.base
  point := curveFamily x hx P
  arrow := arrowToCurveFamily x hx P
  base := congrArg Over.mk (specULiftZIsTerminal.hom_ext _ _)
  arrow_base := by
    change eqToHom (baseScheme_eq x hx).symm ≫
      (eqToHom (baseScheme_eq x hx) ≫ residueSpecMap P.base) ≫ eqToHom rfl = _
    simp

/-- The identification of the total space of the family of curves of a scheme deformation with
the scheme of the deformation. -/
def totalSiteIsoOfToObj :
    CurveFamily.totalSite (isRepresentable_total_obj x hx (toObj x hx P)) ≅ totalSiteObj x hx P :=
  Yoneda.fullyFaithful.preimageIso
    (CurveFamily.totalSiteIso (isRepresentable_total_obj x hx (toObj x hx P)))

/-- The structure morphism of the total space of `toObj P` is that of `P`, up to
`totalSiteIsoOfToObj`. -/
theorem totalSiteToBase_toObj :
    CurveFamily.totalSiteToBase (isRepresentable_total_obj x hx (toObj x hx P)) =
      (totalSiteIsoOfToObj x hx P).hom ≫ toBaseSiteObj x hx P := by
  apply yoneda.map_injective
  calc yoneda.map (CurveFamily.totalSiteToBase (isRepresentable_total_obj x hx (toObj x hx P)))
      = (CurveFamily.totalSiteIso (isRepresentable_total_obj x hx (toObj x hx P))).hom ≫
          yoneda.map (toBaseSiteObj x hx P) :=
        CurveFamily.yoneda_map_totalSiteToBase _
    _ = yoneda.map (totalSiteIsoOfToObj x hx P).hom ≫ yoneda.map (toBaseSiteObj x hx P) := by
        congr 1
        exact (Yoneda.fullyFaithful.map_preimage _).symm
    _ = yoneda.map ((totalSiteIsoOfToObj x hx P).hom ≫ toBaseSiteObj x hx P) :=
        (yoneda.map_comp _ _).symm

/-- The morphism of total spaces of the arrow of `toObj P` is the closed immersion of `X` into
`P`, up to `totalSiteIsoOfToObj`. -/
theorem totalSiteMap_toObj :
    CurveFamily.totalSiteMap (isRepresentable_total_obj x hx (toObj x hx P))
        (isRepresentable_total x hx) (toObj x hx P).arrow =
      specialSiteMap x hx P ≫ (totalSiteIsoOfToObj x hx P).inv := by
  apply yoneda.map_injective
  calc yoneda.map (CurveFamily.totalSiteMap (isRepresentable_total_obj x hx (toObj x hx P))
        (isRepresentable_total x hx) (toObj x hx P).arrow)
      = (CurveFamily.totalSiteIso (isRepresentable_total x hx)).hom ≫
          ((CurveFamily.totalSiteIso (isRepresentable_total x hx)).inv ≫
            yoneda.map (specialSiteMap x hx P)) ≫
          (CurveFamily.totalSiteIso (isRepresentable_total_obj x hx (toObj x hx P))).inv :=
        CurveFamily.yoneda_map_totalSiteMap _ _ _
    _ = yoneda.map (specialSiteMap x hx P) ≫
          yoneda.map (totalSiteIsoOfToObj x hx P).inv := by
        have h : yoneda.map (totalSiteIsoOfToObj x hx P).inv =
            (CurveFamily.totalSiteIso (isRepresentable_total_obj x hx (toObj x hx P))).inv :=
          Yoneda.fullyFaithful.map_preimage _
        rw [h]
        exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (Iso.hom_inv_id_assoc _ _)
    _ = _ := (yoneda.map_comp _ _).symm

/-- The identification of the total space of the family of curves of a scheme deformation with
the scheme of the deformation, as an isomorphism of schemes. -/
abbrev schemeIsoOfToObj :
    (toSchemeDeformation x hx (toObj x hx P)).scheme ≅ P.scheme :=
  (BigFppfOver.toScheme B integerBase hZ).mapIso (totalSiteIsoOfToObj x hx P)

/-- The structure morphism of `toSchemeDeformation (toObj P)` is that of `P`, up to
`schemeIsoOfToObj`. -/
theorem toBase_toSchemeDeformation_toObj :
    (toSchemeDeformation x hx (toObj x hx P)).toBase =
      (schemeIsoOfToObj x hx P).hom ≫ P.toBase := by
  show (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteToBase _) ≫
    eqToHom rfl = _
  rw [eqToHom_refl, Category.comp_id, totalSiteToBase_toObj, Functor.map_comp]
  rfl

/-- The closed immersion of `X` into `toSchemeDeformation (toObj P)` is that of `P`, up to
`schemeIsoOfToObj`. -/
theorem specialMap_toSchemeDeformation_toObj :
    (toSchemeDeformation x hx (toObj x hx P)).specialMap =
      P.specialMap ≫ (schemeIsoOfToObj x hx P).inv := by
  show (BigFppfOver.toScheme B integerBase hZ).map
    (CurveFamily.totalSiteMap _ _ (toObj x hx P).arrow) = _
  rw [totalSiteMap_toObj, Functor.map_comp]
  rfl

/-- The isomorphism of scheme deformations exhibiting a scheme deformation of `X` as the image
of a deformation of `x`. -/
def toSchemeDeformationIsoOfToObj : toSchemeDeformation x hx (toObj x hx P) ≅ P :=
  SchemeDeformationCategory.isoOfSchemeIso rfl (schemeIsoOfToObj x hx P)
    (heq_of_eq (toBase_toSchemeDeformation_toObj x hx P))
    (specialMap_toSchemeDeformation_toObj x hx P)

end EssSurj

/-! ### Full faithfulness -/

section FullyFaithful

open Deformation.Examples

/-- Two morphisms of deformations of `x` with the same morphism of scheme deformations are
equal. -/
theorem toSchemeDeformationHom_injective {a b : Obj x hx} {m m' : Hom x hx a b}
    (h : toSchemeDeformationHom x hx m = toSchemeDeformationHom x hx m') : m = m' := by
  have hr : m.ringHom = m'.ringHom := congrArg SchemeDeformationCategory.Hom.base h
  have hmap := congrArg SchemeDeformationCategory.Hom.map h
  change (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap _ _ m.arrow) =
    (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap _ _ m'.arrow) at hmap
  have hsite := congrArg integerSiteHom hmap
  rw [integerSiteHom_toScheme_map, integerSiteHom_toScheme_map] at hsite
  have hy := congrArg yoneda.map hsite
  rw [CurveFamily.yoneda_map_totalSiteMap, CurveFamily.yoneda_map_totalSiteMap] at hy
  have htot : m.arrow.totalMap = m'.arrow.totalMap := by
    apply ObjectProperty.hom_ext
    simpa using hy
  have hbase : m.arrow.baseMap = m'.arrow.baseMap := by
    rw [← integerSiteHom_toScheme_map m.arrow.baseMap,
      ← integerSiteHom_toScheme_map m'.arrow.baseMap, toScheme_map_arrow_baseMap,
      toScheme_map_arrow_baseMap, hr]
  exact Deformation.Artin.DeformationMorphism.ext_of_components _ _ _ _ hr
    (CurveFamily.Hom.ext hbase htot)

variable {a b : Obj x hx}
  (g : SchemeDeformationCategory.Hom (toSchemeDeformation x hx a) (toSchemeDeformation x hx b))

/-- The base map of the preimage of a morphism of scheme deformations. -/
abbrev preimageBaseMap : b.point.base ⟶ a.point.base :=
  integerSiteHom (eqToHom (baseScheme_eq_obj x hx b) ≫
    Spec.map (CommRingCat.ofHom g.base.hom.toRingHom) ≫ eqToHom (baseScheme_eq_obj x hx a).symm)

/-- The morphism of total spaces of the preimage of a morphism of scheme deformations, in the
site. -/
abbrev preimageSiteMap : CurveFamily.totalSite (isRepresentable_total_obj x hx b) ⟶
    CurveFamily.totalSite (isRepresentable_total_obj x hx a) :=
  integerSiteHom g.map

/-- The square of `preimageSiteMap g` and `preimageBaseMap g` over the structure morphisms is
cartesian in the site. -/
theorem isPullback_preimageSite :
    IsPullback (preimageSiteMap x hx g)
      (CurveFamily.totalSiteToBase (isRepresentable_total_obj x hx b))
      (CurveFamily.totalSiteToBase (isRepresentable_total_obj x hx a))
      (preimageBaseMap x hx g) := by
  apply FiniteFreeAlgebra.isPullback_of_isPullback_toScheme
  refine IsPullback.of_iso g.cartesian (Iso.refl _) (Iso.refl _)
    (eqToIso (baseScheme_eq_obj x hx b).symm) (eqToIso (baseScheme_eq_obj x hx a).symm)
    ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · show ((BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteToBase _) ≫
      eqToHom (baseScheme_eq_obj x hx b)) ≫ eqToHom (baseScheme_eq_obj x hx b).symm = 𝟙 _ ≫ _
    simp
  · show ((BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteToBase _) ≫
      eqToHom (baseScheme_eq_obj x hx a)) ≫ eqToHom (baseScheme_eq_obj x hx a).symm = 𝟙 _ ≫ _
    simp
  · show baseSpecMap g.base ≫ eqToHom (baseScheme_eq_obj x hx a).symm =
      eqToHom (baseScheme_eq_obj x hx b).symm ≫ (eqToHom (baseScheme_eq_obj x hx b) ≫
        Spec.map (CommRingCat.ofHom g.base.hom.toRingHom) ≫
          eqToHom (baseScheme_eq_obj x hx a).symm)
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rfl

/-- The identification of the total space of a deformation of `x` with the presheaf of points of
its representing scheme, as an isomorphism of algebraic spaces. -/
abbrev totalIsoObj (c : Obj x hx) :
    schemeSpace (CurveFamily.totalSite (isRepresentable_total_obj x hx c)) ≅ c.point.total :=
  ObjectProperty.isoMk _ (CurveFamily.totalSiteIso (isRepresentable_total_obj x hx c))

/-- The morphism of families of curves of the preimage of a morphism of scheme deformations. -/
def preimageArrow : b.point ⟶ a.point where
  baseMap := preimageBaseMap x hx g
  totalMap := (totalIsoObj x hx b).inv ≫ schemeSpaceMap (preimageSiteMap x hx g) ≫
    (totalIsoObj x hx a).hom
  cartesian := by
    refine IsPullback.of_iso (isPullback_schemeSpaceMap (isPullback_preimageSite x hx g))
      (totalIsoObj x hx b) (totalIsoObj x hx a) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Iso.hom_inv_id_assoc (totalIsoObj x hx b) _).symm
    · apply ObjectProperty.hom_ext
      change yoneda.map (CurveFamily.totalSiteToBase (isRepresentable_total_obj x hx b)) ≫
        𝟙 _ = _
      rw [Category.comp_id, CurveFamily.yoneda_map_totalSiteToBase]
      rfl
    · apply ObjectProperty.hom_ext
      change yoneda.map (CurveFamily.totalSiteToBase (isRepresentable_total_obj x hx a)) ≫
        𝟙 _ = _
      rw [Category.comp_id, CurveFamily.yoneda_map_totalSiteToBase]
      rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- `preimageArrow g` is compatible with the arrows of `a` and `b` from `x`. -/
theorem preimageArrow_triangle : b.arrow ≫ preimageArrow x hx g = a.arrow := by
  apply CurveFamily.Hom.ext
  · show b.arrow.baseMap ≫ preimageBaseMap x hx g = a.arrow.baseMap
    rw [← integerSiteHom_toScheme_map (b.arrow.baseMap ≫ preimageBaseMap x hx g),
      ← integerSiteHom_toScheme_map a.arrow.baseMap]
    congr 1
    rw [Functor.map_comp, toScheme_map_baseMap, toScheme_map_baseMap]
    let g' : a.algebra ⟶ b.algebra := g.base
    have key : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap b.algebra)) ≫
        Spec.map (CommRingCat.ofHom g'.hom.toRingHom) =
          Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap a.algebra)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Deformation.Artin.residueMap_comp]
    show (eqToHom (baseScheme_eq x hx) ≫
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap b.algebra)) ≫
          eqToHom (baseScheme_eq_obj x hx b).symm) ≫
        (eqToHom (baseScheme_eq_obj x hx b) ≫ Spec.map (CommRingCat.ofHom g'.hom.toRingHom) ≫
          eqToHom (baseScheme_eq_obj x hx a).symm) = _
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% key]
  · have hsp := g.special_compat
    change (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap _ _ b.arrow) ≫
      g.map = (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap _ _ a.arrow)
      at hsp
    have hsite : CurveFamily.totalSiteMap (isRepresentable_total_obj x hx b)
        (isRepresentable_total x hx) b.arrow ≫ preimageSiteMap x hx g =
        CurveFamily.totalSiteMap (isRepresentable_total_obj x hx a)
          (isRepresentable_total x hx) a.arrow := congrArg integerSiteHom hsp
    have hy := congrArg yoneda.map hsite
    rw [Functor.map_comp, CurveFamily.yoneda_map_totalSiteMap,
      CurveFamily.yoneda_map_totalSiteMap] at hy
    apply ObjectProperty.hom_ext
    show b.arrow.totalMap.hom ≫ (CurveFamily.totalSiteIso _).inv ≫
      yoneda.map (preimageSiteMap x hx g) ≫ (CurveFamily.totalSiteIso _).hom = a.arrow.totalMap.hom
    simpa using congrArg (fun t => (CurveFamily.totalSiteIso (isRepresentable_total x hx)).inv ≫
      t ≫ (CurveFamily.totalSiteIso (isRepresentable_total_obj x hx a)).hom) hy

/-- The base map of `preimageArrow g` is the spectrum of the arrow of `𝒞_Λ` of `g`, up to the
identifications of the base schemes. -/
theorem preimageArrow_base :
    eqToHom (congrArg Over.left b.base).symm ≫
        ((projection B hZ).map (preimageArrow x hx g)).left ≫
          eqToHom (congrArg Over.left a.base) =
      Spec.map (CommRingCat.ofHom g.base.hom.toRingHom) := by
  show eqToHom (baseScheme_eq_obj x hx b).symm ≫ (eqToHom (baseScheme_eq_obj x hx b) ≫
    Spec.map (CommRingCat.ofHom g.base.hom.toRingHom) ≫ eqToHom (baseScheme_eq_obj x hx a).symm) ≫
      eqToHom (baseScheme_eq_obj x hx a) = _
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc]
  exact (congrArg (_ ≫ ·) ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans
    (Category.comp_id _)

/-- The preimage of a morphism of scheme deformations. -/
def preimageHom : Hom x hx a b where
  ringHom := g.base
  arrow := preimageArrow x hx g
  triangle := preimageArrow_triangle x hx g
  arrow_base := preimageArrow_base x hx g

/-- The morphism of scheme deformations attached to `preimageHom g` is `g`. -/
theorem toSchemeDeformationHom_preimageHom :
    toSchemeDeformationHom x hx (preimageHom x hx g) = g := by
  apply SchemeDeformationCategory.Hom.ext
  · rfl
  · show (BigFppfOver.toScheme B integerBase hZ).map
      (CurveFamily.totalSiteMap _ _ (preimageArrow x hx g)) = g.map
    have : CurveFamily.totalSiteMap (isRepresentable_total_obj x hx a)
        (isRepresentable_total_obj x hx b) (preimageArrow x hx g) = preimageSiteMap x hx g := by
      apply yoneda.map_injective
      rw [CurveFamily.yoneda_map_totalSiteMap]
      show (CurveFamily.totalSiteIso _).hom ≫ ((CurveFamily.totalSiteIso _).inv ≫
        yoneda.map (preimageSiteMap x hx g) ≫ (CurveFamily.totalSiteIso _).hom) ≫
          (CurveFamily.totalSiteIso _).inv = _
      simp
    rw [this]
    rfl

end FullyFaithful

/-- The functor `toSchemeDeformationFunctor` is faithful. -/
theorem toSchemeDeformationFunctor_faithful :
    letI := (predeformation x hx).category
    (toSchemeDeformationFunctor x hx).Faithful :=
  let := (predeformation x hx).category
  ⟨fun h => toSchemeDeformationHom_injective x hx h⟩

/-- The functor `toSchemeDeformationFunctor` is full. -/
theorem toSchemeDeformationFunctor_full :
    letI := (predeformation x hx).category
    (toSchemeDeformationFunctor x hx).Full :=
  let := (predeformation x hx).category
  ⟨fun g => ⟨preimageHom x hx g, toSchemeDeformationHom_preimageHom x hx g⟩⟩

/-- Every deformation of the scheme underlying `x` is isomorphic to the image of a deformation of
`x` under `toSchemeDeformationFunctor`. -/
theorem toSchemeDeformationFunctor_essSurj :
    letI := (predeformation x hx).category
    ∀ P : Deformation.Examples.SchemeDeformationCategory (Λ := Λ) (scheme x hx),
      ∃ a : (predeformation x hx).carrier,
        Nonempty ((toSchemeDeformationFunctor x hx).obj a ≅ P) :=
  fun P => ⟨toObj x hx P, ⟨toSchemeDeformationIsoOfToObj x hx P⟩⟩

end CurveDeformation

end AlgebraicGeometry
