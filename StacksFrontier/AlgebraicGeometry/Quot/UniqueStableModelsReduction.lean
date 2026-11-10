module

public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesSeparated
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOfSchemes
public import StacksFrontier.AlgebraicGeometry.Models.ModelHomUniqueness
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.GroupSpaceTranslation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothStrongLift

/-!
# Uniqueness of stable models for families of curves, from the case of schemes

`AlgebraicGeometry.UniqueStableModels` is the statement of Stacks 0E97 as the proof of Stacks 0E9A
uses it: for families of curves over the spectrum of a discrete valuation ring `R`, whose total
spaces are algebraic spaces. Stacks 0E97 itself is a statement about *models* of a curve
(Semistable Reduction, Section 0C2R), which are schemes. This file reduces the former to the
latter.

The reduction needs, besides the existence half of Stacks 0E97 for schemes, that the total space
of a stable family of curves over `Spec R` is a scheme. Stacks does not state this; the proof of
Stacks 0E9A passes over it when it unwinds the categories of dotted arrows into Stacks 0E97. It
holds (for instance because `ω^{⊗3}` is relatively very ample), but it is not formalized here.

## Main results

* `AlgebraicGeometry.ExistsIsoOfStableModels`: the existence half of Stacks 0E97 for schemes.
* `AlgebraicGeometry.StableFamilyTotalIsScheme`: the total space of a stable family of curves
  over the spectrum of a discrete valuation ring is a scheme.
* `AlgebraicGeometry.uniqueStableModels_of`: `UniqueStableModels` from the two statements above.
  The uniqueness of the isomorphism is proved, not assumed.

## Implementation notes

This file is UNREGISTERED: it carries no `stacks` attribute, and its main result takes the two
statements above as explicit inputs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Models

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The existence half of Stacks 0E97, for schemes.** Let `R` be a discrete valuation ring with
fraction field `K` and `C` a smooth curve over `K`. If `X` and `X'` are models of `C` which are
stable families of curves of genus `g` over `R`, there is an isomorphism of models `X ≅ X'`.

The source also asks that `C` be proper with `H⁰(C, 𝒪_C) = K` and of genus `g`; these follow from
`X` being a stable family of genus `g` with generic fibre `C`. -/
def ExistsIsoOfStableModels (g : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}} (C_to_K : C ⟶ Spec (.of K))
    [Smooth C_to_K] {X X' : Scheme.{u}} {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))}
    {e' : C ≅ pullback p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))},
    IsModel C_to_K p e → IsModel C_to_K p' e' →
    IsStableFamilyOfSchemesOfGenus B hZ g p hR → IsStableFamilyOfSchemesOfGenus B hZ g p' hR →
    ∃ f : X ≅ X', IsModelHom p p' e e' f.hom

/-- **The total space of a stable family of curves over a discrete valuation ring is a scheme.**
Let `R` be a discrete valuation ring and `F` a stable family of curves of genus `g` over
`Spec R`. Then the total space of `F` is (represented by) a scheme. -/
def StableFamilyTotalIsScheme (g : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : B.Contains (Spec (.of R))) (F : CurveFamily B hZ),
    F.base = integerSiteObject B hZ hR → IsStableCurveFamilyOfGenus B hZ g F →
    ∃ (X : Scheme.{u}) (hX : B.Contains X),
      Nonempty (F.total ≅ schemeSpace (integerSiteObject B hZ hX))

variable {B hZ}

/-- Every morphism between the algebraic spaces of objects of the site comes from the site. -/
private theorem exists_schemeSpaceMap_eq {T T' : BigFppfOver B integerBase hZ}
    (f : schemeSpace T ⟶ schemeSpace T') : ∃ m : T ⟶ T', schemeSpaceMap m = f :=
  ⟨_, (schemeSpaceFunctorFullyFaithful B hZ).map_preimage f⟩

/-- A morphism of families of curves lying over `f` has base map `f`. -/
private theorem baseMap_eq_of_isHomLift_self {F F' : CurveFamily B hZ} (φ : F ⟶ F')
    (f : F.base ⟶ F'.base) (hφ : (curvesProjectionOver B hZ).IsHomLift f φ) : φ.baseMap = f := by
  obtain ⟨_, _, h⟩ := CurveFamily.baseMap_eq_of_isHomLift φ f hφ
  simpa using h

/-- The property of an étale-local morphism of algebraic spaces whose source is represented by
`T`, through `ε`, holds for the morphism of schemes underlying the morphism `k` of the site. -/
private theorem property_toScheme_map_of_holdsOnEveryEtaleChart {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) {total : AlgebraicSpaces B integerBase hZ}
    {T V : BigFppfOver B integerBase hZ} {toBase : total ⟶ schemeSpace V}
    (ε : total ≅ schemeSpace T) (k : T ⟶ V) (hε : ε.hom ≫ schemeSpaceMap k = toBase)
    (h : Space.HoldsOnEveryEtaleChart B integerBase hZ P toBase.hom) :
    P ((BigFppfOver.toScheme B integerBase hZ).map k) := by
  let ε' : total.obj ≅ yoneda.obj T := (ObjectProperty.ι _).mapIso ε
  rw [show toBase.hom = ε'.hom ≫ yoneda.map k from (congrArg (fun φ => φ.hom) hε).symm] at h
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ hP k).1
    ((Space.holdsOnEveryEtaleChart_precomp_iso B integerBase hZ P ε' _).2 h)

/-! ### Reading a morphism of families of curves in schemes -/

/-- **A morphism of families of curves whose total spaces are schemes gives a cartesian square of
schemes.** Let `φ : G ⟶ F` be a morphism of families of curves and suppose the total spaces are
represented by `T₀` and `T` over the bases, through `q₀ : T₀ ⟶ G.base` and `q : T ⟶ F.base`. If
`m : T₀ ⟶ T` represents the total map of `φ`, then the square of schemes formed by `m`, `q₀`, `q`
and the base map of `φ` is cartesian. -/
theorem CurveFamily.isPullback_toScheme_of_schemeSpace {G F : CurveFamily B hZ} (φ : G ⟶ F)
    {T₀ T : BigFppfOver B integerBase hZ} (q₀ : T₀ ⟶ G.base) (q : T ⟶ F.base)
    (ε₀ : G.total ≅ schemeSpace T₀) (ε : F.total ≅ schemeSpace T)
    (hε₀ : ε₀.hom ≫ schemeSpaceMap q₀ = G.toBase) (hε : ε.hom ≫ schemeSpaceMap q = F.toBase)
    (m : T₀ ⟶ T) (hm : schemeSpaceMap m = ε₀.inv ≫ φ.totalMap ≫ ε.hom) :
    IsPullback ((BigFppfOver.toScheme B integerBase hZ).map m)
      ((BigFppfOver.toScheme B integerBase hZ).map q₀)
      ((BigFppfOver.toScheme B integerBase hZ).map q)
      ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) := by
  have h : IsPullback (schemeSpaceMap m) (schemeSpaceMap q₀) (schemeSpaceMap q)
      (schemeSpaceMap φ.baseMap) := by
    refine IsPullback.of_iso φ.cartesian ε₀ ε (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [hm, Iso.hom_inv_id_assoc]
    · rw [hε₀, Iso.refl_hom, Category.comp_id]
    · rw [hε, Iso.refl_hom, Category.comp_id]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  exact (isPullback_of_isPullback_schemeSpaceMap h).map (BigFppfOver.toScheme B integerBase hZ)

/-- **A stable family of curves whose total space is a scheme is a stable family of schemes.**
Let `F` be a stable family of curves of genus `g` over a scheme `S` of the site, and suppose its
total space is represented by a scheme `X`, through `ε`, with structure morphism `p : X ⟶ S`.
Then `p` is flat, proper, locally of finite presentation, with fibres of dimension at most one, and
a stable family of curves of genus `g` given by a morphism of schemes: each of these conditions
on the morphism of algebraic spaces is the condition on `p`, the source being representable. -/
theorem isStableFamilyOfSchemesOfGenus_of_schemeSpace {S : Scheme.{u}} (hS : B.Contains S)
    {total : AlgebraicSpaces B integerBase hZ}
    {toBase : total ⟶ schemeSpace (integerSiteObject B hZ hS)}
    {hflat : Space.IsFlat B integerBase hZ toBase.hom}
    {hproper : Space.IsProper B integerBase hZ toBase.hom}
    {hfp : Space.IsFinitePresentation B integerBase hZ toBase.hom}
    {hrel : ∀ x : Space.points B integerBase hZ total.obj, ∃ e : ℕ, e ≤ 1 ∧
      Space.HoldsOnEveryEtaleChartAtPoint B integerBase hZ (@HasFiberDimensionAt.{u} (e : ℕ∞))
        toBase.hom x}
    {g : ℕ} (hF : IsStableCurveFamilyOfGenus B hZ g
      ⟨integerSiteObject B hZ hS, total, toBase, hflat, hproper, hfp, hrel⟩)
    {X : Scheme.{u}} (hX : B.Contains X) (ε : total ≅ schemeSpace (integerSiteObject B hZ hX))
    (p : X ⟶ S) (hε : ε.hom ≫ schemeSpaceMap (integerSiteMap B hZ hX hS p) = toBase) :
    IsStableFamilyOfSchemesOfGenus B hZ g p hS := by
  set k := integerSiteMap B hZ hX hS p
  let ε' : total.obj ≅ yoneda.obj (integerSiteObject B hZ hX) := (ObjectProperty.ι _).mapIso ε
  have hk : toBase.hom = ε'.hom ≫ yoneda.map k := (congrArg (fun φ => φ.hom) hε).symm
  have hk' : yoneda.map k = ε'.inv ≫ toBase.hom := (Iso.eq_inv_comp ε').2 hk.symm
  have hflat' : Flat p := property_toScheme_map_of_holdsOnEveryEtaleChart
    Flat.isEtaleLocalOnSourceAndTarget ε k hε hflat
  have hlfp' : LocallyOfFinitePresentation p := property_toScheme_map_of_holdsOnEveryEtaleChart
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget ε k hε hfp.1
  have hproper' : IsProper p := by
    have h₁ : Space.IsProper B integerBase hZ (yoneda.map k) := by
      rw [hk']
      exact Space.isProper_comp B integerBase hZ (isAlgebraicSpace_yoneda B integerBase hZ _)
        total.property (isAlgebraicSpace_yoneda B integerBase hZ _) ε'.inv toBase.hom
        (Space.isProper_of_isIso B integerBase hZ ε'.inv) hproper
    have : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B integerBase hZ)).IsStableUnderBaseChange :=
      ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @_root_.AlgebraicGeometry.IsProper)
        (hsq.map (BigFppfOver.toScheme B integerBase hZ)) hg⟩
    exact (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B integerBase hZ))).mp
      ((Space.presheaf_isProper_iff B integerBase hZ (yoneda.map k)
        (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
        (Functor.relativelyRepresentable.map yoneda k)).mp h₁)
  have hfib : ∀ x, topologicalKrullDimAt (p.fiber (p x)) (p.asFiber x) ≤ 1 := by
    intro y
    set y' := (Space.pointsEquivScheme B integerBase hZ (integerSiteObject B hZ hX)).symm y
    obtain ⟨e, he, hy⟩ := hrel (Space.pointsMap B integerBase hZ _ ε'.inv y')
    have h₁ := Space.holdsOnEveryEtaleChartAtPoint_of_iso B integerBase hZ
      (@HasFiberDimensionAt.{u} (e : ℕ∞)) ε' (Iso.refl (yoneda.obj (integerSiteObject B hZ hS)))
      toBase.hom (yoneda.map k) (by rw [hk, Iso.refl_hom, Category.comp_id]) _ hy
    have hpt : Space.pointsMap B integerBase hZ _ ε'.hom
        (Space.pointsMap B integerBase hZ _ ε'.inv y') = y' := by
      rw [← Space.pointsMap_comp_apply, Iso.inv_hom_id, Space.pointsMap_id_apply]
    rw [hpt] at h₁
    have h₂ := (Space.holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B integerBase hZ
      (@HasFiberDimensionAt.{u} (e : ℕ∞))
      (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞)) k y').1 h₁
    have hy' : Space.pointsToScheme B integerBase hZ (integerSiteObject B hZ hX) y' = y :=
      (Space.pointsEquivScheme B integerBase hZ (integerSiteObject B hZ hX)).apply_symm_apply y
    rw [hy'] at h₂
    rw [(hasFiberDimensionAt_ofSchemeHom_iff p y (e : ℕ∞)).1 h₂]
    exact_mod_cast he
  refine ⟨hflat', hproper', hlfp', hfib, ?_⟩
  let e : curveFamilyOfFiberDimensionLE B hZ k hflat' hproper' hlfp' hfib ≅
      ⟨integerSiteObject B hZ hS, total, toBase, hflat, hproper, hfp, hrel⟩ :=
    CurveFamily.isoMk (Iso.refl _) ε.symm (by
      change ε.inv ≫ toBase = schemeSpaceMap k ≫ schemeSpaceMap (𝟙 _)
      rw [← hε, Iso.inv_hom_id_assoc,
        show schemeSpaceMap (𝟙 (integerSiteObject B hZ hS)) = 𝟙 _ from
          (schemeSpaceFunctor B integerBase hZ).map_id _, Category.comp_id])
  exact ⟨CurveFamily.isStableCurveFamily_of_hom e.hom hF.1, CurveFamily.hasGenus_of_iso e hF.2⟩

/-- **A family of curves over the spectrum of a field has a scheme as total space**, represented
over the base by a morphism of the site. -/
theorem CurveFamily.exists_schemeSpace_of_base_eq {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (G : CurveFamily B hZ)
    (hG : G.base = integerSiteObject B hZ hK) :
    ∃ (T : BigFppfOver B integerBase hZ) (ε : G.total ≅ schemeSpace T) (q : T ⟶ G.base),
      ε.hom ≫ schemeSpaceMap q = G.toBase := by
  have hrep := G.isRepresentable_total_of_base_eq (K := K)
    (congrArg (BigFppfOver.toScheme B integerBase hZ).obj hG)
  obtain ⟨T, ⟨ε⟩⟩ : ∃ T : BigFppfOver B integerBase hZ, Nonempty (G.total ≅ schemeSpace T) :=
    ⟨G.total.1.reprX, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso G.total.1.reprW.symm⟩⟩
  obtain ⟨q, hq⟩ := exists_schemeSpaceMap_eq (ε.inv ≫ G.toBase)
  exact ⟨T, ε, q, by rw [hq, Iso.hom_inv_id_assoc]⟩

/-- **The smoothness of a family of curves is that of a scheme representing its total space.** -/
theorem CurveFamily.smooth_of_isSmoothFamily_of_schemeSpace (G : CurveFamily B hZ)
    (hG : IsSmoothFamily B hZ G) {T : BigFppfOver B integerBase hZ} (ε : G.total ≅ schemeSpace T)
    (q : T ⟶ G.base) (hε : ε.hom ≫ schemeSpaceMap q = G.toBase) :
    Smooth ((BigFppfOver.toScheme B integerBase hZ).map q) := by
  exact property_toScheme_map_of_holdsOnEveryEtaleChart Smooth.isEtaleLocalOnSourceAndTarget ε q
    hε hG

/-- **A stable family of curves over a discrete valuation ring, as a morphism of schemes.** Given
`StableFamilyTotalIsScheme`, the total space of a stable family of genus `g` over `Spec R` is a
scheme `X`, and its structure morphism `p : X ⟶ Spec R` is a stable family of schemes of genus
`g`. -/
theorem exists_isStableFamilyOfSchemesOfGenus_of_stableFamilyTotalIsScheme {g : ℕ}
    (hA : StableFamilyTotalIsScheme B hZ g) (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hR : B.Contains (Spec (.of R)))
    {total : AlgebraicSpaces B integerBase hZ}
    {toBase : total ⟶ schemeSpace (integerSiteObject B hZ hR)}
    {hflat : Space.IsFlat B integerBase hZ toBase.hom}
    {hproper : Space.IsProper B integerBase hZ toBase.hom}
    {hfp : Space.IsFinitePresentation B integerBase hZ toBase.hom}
    {hrel : ∀ x : Space.points B integerBase hZ total.obj, ∃ e : ℕ, e ≤ 1 ∧
      Space.HoldsOnEveryEtaleChartAtPoint B integerBase hZ (@HasFiberDimensionAt.{u} (e : ℕ∞))
        toBase.hom x}
    (hF : IsStableCurveFamilyOfGenus B hZ g
      ⟨integerSiteObject B hZ hR, total, toBase, hflat, hproper, hfp, hrel⟩) :
    ∃ (X : Scheme.{u}) (hX : B.Contains X) (ε : total ≅ schemeSpace (integerSiteObject B hZ hX))
      (p : X ⟶ Spec (.of R)), ε.hom ≫ schemeSpaceMap (integerSiteMap B hZ hX hR p) = toBase ∧
        IsStableFamilyOfSchemesOfGenus B hZ g p hR := by
  obtain ⟨X, hX, ⟨ε⟩⟩ := hA R hR _ rfl hF
  obtain ⟨q, hq⟩ := exists_schemeSpaceMap_eq (ε.inv ≫ toBase)
  have hε : ε.hom ≫ schemeSpaceMap (integerSiteMap B hZ hX hR
      ((BigFppfOver.toScheme B integerBase hZ).map q)) = toBase := by
    rw [integerSiteMap_toScheme_map, hq, Iso.hom_inv_id_assoc]
  exact ⟨X, hX, ε, _, hε, isStableFamilyOfSchemesOfGenus_of_schemeSpace hR hF hX ε _ hε⟩

/-- **`UniqueStableModels` over the integer site objects, from the case of schemes.** This is the
statement of `AlgebraicGeometry.UniqueStableModels` with the bases normalized to the schemes of the
site read over the integers. -/
theorem existsUnique_hom_of_existsIsoOfStableModels {g : ℕ}
    (hA : StableFamilyTotalIsScheme B hZ g) (hB : ExistsIsoOfStableModels B hZ g)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (gm : integerSiteObject B hZ hK ⟶ integerSiteObject B hZ hR)
    (hgm : (BigFppfOver.toScheme B integerBase hZ).map gm =
      Spec.map (CommRingCat.ofHom (algebraMap R K)))
    {F F' G G' : CurveFamily B hZ} (c : G ⟶ F) (c' : G' ⟶ F') (s : G ⟶ G')
    (hF : IsStableCurveFamilyOfGenus B hZ g F) (hF' : IsStableCurveFamilyOfGenus B hZ g F')
    (hG : IsSmoothH0Family B hZ G)
    (hc : (curvesProjectionOver B hZ).IsHomLift gm c)
    (hc' : (curvesProjectionOver B hZ).IsHomLift gm c')
    (hs : (curvesProjectionOver B hZ).IsHomLift (𝟙 (integerSiteObject B hZ hK)) s) :
    ∃! t : F ⟶ F', (curvesProjectionOver B hZ).IsHomLift (𝟙 (integerSiteObject B hZ hR)) t ∧
      c ≫ t = s ≫ c' := by
  rcases F with ⟨Fb, Ft, Ftb, Ffl, Fpr, Ffp, Frel⟩
  rcases F' with ⟨F'b, F't, F'tb, F'fl, F'pr, F'fp, F'rel⟩
  rcases G with ⟨Gb, Gt, Gtb, Gfl, Gpr, Gfp, Grel⟩
  rcases G' with ⟨G'b, G't, G'tb, G'fl, G'pr, G'fp, G'rel⟩
  have := hc
  have := hc'
  have := hs
  obtain rfl : Fb = integerSiteObject B hZ hR :=
    IsHomLift.codomain_eq (curvesProjectionOver B hZ) gm c
  obtain rfl : F'b = integerSiteObject B hZ hR :=
    IsHomLift.codomain_eq (curvesProjectionOver B hZ) gm c'
  obtain rfl : Gb = integerSiteObject B hZ hK :=
    IsHomLift.domain_eq (curvesProjectionOver B hZ) gm c
  obtain rfl : G'b = integerSiteObject B hZ hK :=
    IsHomLift.domain_eq (curvesProjectionOver B hZ) gm c'
  have hcb : c.baseMap = gm := baseMap_eq_of_isHomLift_self c gm hc
  have hc'b : c'.baseMap = gm := baseMap_eq_of_isHomLift_self c' gm hc'
  have hsb : s.baseMap = 𝟙 _ := baseMap_eq_of_isHomLift_self s _ hs
  -- the total spaces of `F`, `F'` and `G` are schemes
  obtain ⟨X, hX, ε, p, hε, hp⟩ :=
    exists_isStableFamilyOfSchemesOfGenus_of_stableFamilyTotalIsScheme hA R hR hF
  obtain ⟨X', hX', ε', p', hε', hp'⟩ :=
    exists_isStableFamilyOfSchemesOfGenus_of_stableFamilyTotalIsScheme hA R hR hF'
  obtain ⟨T₀, ε₀, q₀, hε₀⟩ := CurveFamily.exists_schemeSpace_of_base_eq hK
    ⟨integerSiteObject B hZ hK, Gt, Gtb, Gfl, Gpr, Gfp, Grel⟩ rfl
  set v := (BigFppfOver.toScheme B integerBase hZ).map q₀
  have hvsm : Smooth v := CurveFamily.smooth_of_isSmoothFamily_of_schemeSpace _ hG.1.1 ε₀ q₀ hε₀
  obtain ⟨hpfl, hppr, hplfp, -, -⟩ := id hp
  obtain ⟨hpfl', hppr', -, -, -⟩ := id hp'
  -- the generic fibres
  obtain ⟨m₀, hm₀⟩ := exists_schemeSpaceMap_eq (ε₀.inv ≫ c.totalMap ≫ ε.hom)
  obtain ⟨m₀', hm₀'⟩ := exists_schemeSpaceMap_eq (ε₀.inv ≫ (s ≫ c').totalMap ≫ ε'.hom)
  have hpb := CurveFamily.isPullback_toScheme_of_schemeSpace c q₀
    (integerSiteMap B hZ hX hR p) ε₀ ε hε₀ hε m₀ hm₀
  have hpb' := CurveFamily.isPullback_toScheme_of_schemeSpace (s ≫ c') q₀
    (integerSiteMap B hZ hX' hR p') ε₀ ε' hε₀ hε' m₀' hm₀'
  have hι : (BigFppfOver.toScheme B integerBase hZ).map c.baseMap = genericPointInclusion R K := by
    rw [hcb, hgm]
  have hι' : (BigFppfOver.toScheme B integerBase hZ).map (s ≫ c').baseMap =
      genericPointInclusion R K := by
    change (BigFppfOver.toScheme B integerBase hZ).map (s.baseMap ≫ c'.baseMap) =
      genericPointInclusion R K
    rw [hsb, hc'b, Category.id_comp, hgm]
  rw [hι] at hpb
  rw [hι'] at hpb'
  change IsPullback _ v p (genericPointInclusion R K) at hpb
  change IsPullback _ v p' (genericPointInclusion R K) at hpb'
  obtain ⟨e, he₁, he₂⟩ : ∃ e : (BigFppfOver.toScheme B integerBase hZ).obj T₀ ≅
      pullback p (genericPointInclusion R K),
      e.hom ≫ pullback.fst p (genericPointInclusion R K) =
        (BigFppfOver.toScheme B integerBase hZ).map m₀ ∧
      e.hom ≫ pullback.snd p (genericPointInclusion R K) = v :=
    ⟨hpb.isoPullback, hpb.isoPullback_hom_fst, hpb.isoPullback_hom_snd⟩
  obtain ⟨e', he₁', he₂'⟩ : ∃ e' : (BigFppfOver.toScheme B integerBase hZ).obj T₀ ≅
      pullback p' (genericPointInclusion R K),
      e'.hom ≫ pullback.fst p' (genericPointInclusion R K) =
        (BigFppfOver.toScheme B integerBase hZ).map m₀' ∧
      e'.hom ≫ pullback.snd p' (genericPointInclusion R K) = v :=
    ⟨hpb'.isoPullback, hpb'.isoPullback_hom_fst, hpb'.isoPullback_hom_snd⟩
  have hmod : IsModel v p e := ⟨hpfl, inferInstance, inferInstance, he₂⟩
  have hmod' : IsModel v p' e' := ⟨hpfl', inferInstance, inferInstance, he₂'⟩
  have : IsSeparated p' := hppr'.toIsSeparated
  have hgfm : ∀ (φ : X ⟶ X') (h : φ ≫ p' = p),
      genericFiberMapOfHomOver (K := K) p p' φ h ≫ pullback.fst p' (genericPointInclusion R K) =
        pullback.fst p (genericPointInclusion R K) ≫ φ :=
    fun _ _ => pullback.lift_fst _ _ _
  have hgfm' : ∀ (φ : X ⟶ X') (h : φ ≫ p' = p),
      genericFiberMapOfHomOver (K := K) p p' φ h ≫ pullback.snd p' (genericPointInclusion R K) =
        pullback.snd p (genericPointInclusion R K) ≫ 𝟙 _ :=
    fun _ _ => pullback.lift_snd _ _ _
  -- a morphism over `R` compatible with the generic fibres is a morphism of models
  have hmodel : ∀ φ : X ⟶ X', φ ≫ p' = p →
      (BigFppfOver.toScheme B integerBase hZ).map m₀ ≫ φ =
        (BigFppfOver.toScheme B integerBase hZ).map m₀' → IsModelHom p p' e e' φ := by
    intro φ h₁ h₂
    refine ⟨h₁, pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, hgfm, ← Category.assoc, he₁]
      exact h₂.trans he₁'.symm
    · rw [Category.assoc, hgfm', Category.comp_id, he₂, he₂']
  -- every solution comes from a morphism of models
  have key : ∀ t₁ : (⟨integerSiteObject B hZ hR, Ft, Ftb, Ffl, Fpr, Ffp, Frel⟩ : CurveFamily B hZ) ⟶
      ⟨integerSiteObject B hZ hR, F't, F'tb, F'fl, F'pr, F'fp, F'rel⟩,
      (curvesProjectionOver B hZ).IsHomLift (𝟙 (integerSiteObject B hZ hR)) t₁ →
      c ≫ t₁ = s ≫ c' →
      ∃ f₁ : integerSiteObject B hZ hX ⟶ integerSiteObject B hZ hX',
        t₁.totalMap = ε.hom ≫ schemeSpaceMap f₁ ≫ ε'.inv ∧
        IsModelHom p p' e e' ((BigFppfOver.toScheme B integerBase hZ).map f₁) := by
    intro t₁ ht₁ htc
    have := ht₁
    have hb₁ : t₁.baseMap = 𝟙 _ := baseMap_eq_of_isHomLift_self t₁ _ ht₁
    obtain ⟨f₁, hf₁⟩ := exists_schemeSpaceMap_eq (ε.inv ≫ t₁.totalMap ≫ ε'.hom)
    refine ⟨f₁, by rw [hf₁]; simp, hmodel _ ?_ ?_⟩
    · have hw : t₁.totalMap ≫ F'tb = Ftb ≫ schemeSpaceMap t₁.baseMap := t₁.cartesian.w
      rw [hb₁, show schemeSpaceMap (𝟙 (integerSiteObject B hZ hR)) = 𝟙 _ from
        (schemeSpaceFunctor B integerBase hZ).map_id _, Category.comp_id] at hw
      have h : f₁ ≫ integerSiteMap B hZ hX' hR p' = integerSiteMap B hZ hX hR p := by
        apply schemeSpaceMap_injective
        rw [schemeSpaceMap_comp, hf₁, Category.assoc, Category.assoc, hε', hw, ← hε,
          Iso.inv_hom_id_assoc]
      exact ((BigFppfOver.toScheme B integerBase hZ).map_comp f₁ _).symm.trans
        (congrArg (BigFppfOver.toScheme B integerBase hZ).map h)
    · have htot : c.totalMap ≫ t₁.totalMap = s.totalMap ≫ c'.totalMap :=
        congrArg CurveFamily.Hom.totalMap htc
      have h : m₀ ≫ f₁ = m₀' := by
        apply schemeSpaceMap_injective
        rw [schemeSpaceMap_comp, hm₀, hf₁, hm₀']
        change ε₀.inv ≫ c.totalMap ≫ ε.hom ≫ ε.inv ≫ t₁.totalMap ≫ ε'.hom =
          ε₀.inv ≫ (s.totalMap ≫ c'.totalMap) ≫ ε'.hom
        rw [Iso.hom_inv_id_assoc, ← htot, Category.assoc]
      exact ((BigFppfOver.toScheme B integerBase hZ).map_comp m₀ f₁).symm.trans
        (congrArg (BigFppfOver.toScheme B integerBase hZ).map h)
  -- uniqueness
  have uniq : ∀ t₁ t₂ : (⟨integerSiteObject B hZ hR, Ft, Ftb, Ffl, Fpr, Ffp, Frel⟩ :
      CurveFamily B hZ) ⟶ ⟨integerSiteObject B hZ hR, F't, F'tb, F'fl, F'pr, F'fp, F'rel⟩,
      ((curvesProjectionOver B hZ).IsHomLift (𝟙 (integerSiteObject B hZ hR)) t₁ ∧
        c ≫ t₁ = s ≫ c') →
      ((curvesProjectionOver B hZ).IsHomLift (𝟙 (integerSiteObject B hZ hR)) t₂ ∧
        c ≫ t₂ = s ≫ c') → t₁ = t₂ := by
    rintro t₁ t₂ ⟨ht₁, htc₁⟩ ⟨ht₂, htc₂⟩
    obtain ⟨f₁, hf₁t, hf₁⟩ := key t₁ ht₁ htc₁
    obtain ⟨f₂, hf₂t, hf₂⟩ := key t₂ ht₂ htc₂
    have hf : f₁ = f₂ :=
      Space.toScheme_map_injective B integerBase hZ
        (@IsModelHom.eq_of_isModel_of_isSeparated _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmod
          hppr'.toIsSeparated _ _ hf₁ hf₂)
    apply CurveFamily.Hom.ext
    · exact (baseMap_eq_of_isHomLift_self t₁ _ ht₁).trans
        (baseMap_eq_of_isHomLift_self t₂ _ ht₂).symm
    · rw [hf₁t, hf₂t, hf]
  -- existence, from the case of schemes
  obtain ⟨f, hf⟩ := @hB R _ _ _ K _ _ _ hR _ v hvsm _ _ _ _ _ _ hmod hmod' hp hp'
  obtain ⟨hfp, -⟩ := id hf
  let iF : integerSiteObject B hZ hX ≅ integerSiteObject B hZ hX' :=
    (schemeOverIntegers B).mapIso (ObjectProperty.isoMk _ f)
  have hiF : iF.hom ≫ integerSiteMap B hZ hX' hR p' = integerSiteMap B hZ hX hR p :=
    Space.toScheme_map_injective B integerBase hZ (by rw [Functor.map_comp]; exact hfp)
  have hmi' : (BigFppfOver.toScheme B integerBase hZ).map m₀ ≫ f.hom =
      (BigFppfOver.toScheme B integerBase hZ).map m₀' :=
    (congrArg (· ≫ f.hom) he₁).symm.trans <| (Category.assoc _ _ _).trans <|
      (congrArg (e.hom ≫ ·) (hgfm f.hom hfp).symm).trans <| (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ pullback.fst p' (genericPointInclusion R K)) hf.2).trans he₁'
  have hmi : m₀ ≫ iF.hom = m₀' :=
    Space.toScheme_map_injective B integerBase hZ
      (((BigFppfOver.toScheme B integerBase hZ).map_comp m₀ iF.hom).trans hmi')
  let tIso : (⟨integerSiteObject B hZ hR, Ft, Ftb, Ffl, Fpr, Ffp, Frel⟩ : CurveFamily B hZ) ≅
      ⟨integerSiteObject B hZ hR, F't, F'tb, F'fl, F'pr, F'fp, F'rel⟩ :=
    CurveFamily.isoMk (Iso.refl _)
      (ε ≪≫ (schemeSpaceFunctor B integerBase hZ).mapIso iF ≪≫ ε'.symm) (by
        change ε.hom ≫ schemeSpaceMap iF.hom ≫ ε'.inv ≫ F'tb =
          Ftb ≫ schemeSpaceMap (𝟙 (integerSiteObject B hZ hR))
        rw [show schemeSpaceMap (𝟙 (integerSiteObject B hZ hR)) = 𝟙 _ from
          (schemeSpaceFunctor B integerBase hZ).map_id _, Category.comp_id, ← hε', ← hε,
          Iso.inv_hom_id_assoc, ← schemeSpaceMap_comp, hiF])
  have ht : (curvesProjectionOver B hZ).IsHomLift (𝟙 (integerSiteObject B hZ hR)) tIso.hom :=
    (inferInstance : (curvesProjectionOver B hZ).IsHomLift
      ((curvesProjectionOver B hZ).map tIso.hom) tIso.hom)
  have htc : c ≫ tIso.hom = s ≫ c' := by
    apply CurveFamily.Hom.ext
    · change c.baseMap ≫ 𝟙 _ = s.baseMap ≫ c'.baseMap
      rw [hcb, hsb, hc'b, Category.comp_id, Category.id_comp]
    · change c.totalMap ≫ ε.hom ≫ schemeSpaceMap iF.hom ≫ ε'.inv = s.totalMap ≫ c'.totalMap
      have h1 : schemeSpaceMap m₀ ≫ schemeSpaceMap iF.hom = schemeSpaceMap m₀' := by
        rw [← schemeSpaceMap_comp, hmi]
      rw [hm₀, hm₀'] at h1
      change (ε₀.inv ≫ c.totalMap ≫ ε.hom) ≫ schemeSpaceMap iF.hom =
        ε₀.inv ≫ (s.totalMap ≫ c'.totalMap) ≫ ε'.hom at h1
      rw [← cancel_epi ε₀.inv, ← cancel_mono ε'.hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h1 ⊢
      exact h1
  exact ⟨tIso.hom, ⟨ht, htc⟩, fun t₁ h₁ => uniq t₁ tIso.hom h₁ ⟨ht, htc⟩⟩

/-- **`UniqueStableModels` from the case of schemes.** If the total space of a stable family of
curves of genus `g` over a discrete valuation ring is a scheme (`StableFamilyTotalIsScheme`) and
two stable models of genus `g` of a smooth curve over the fraction field are isomorphic as models
(`ExistsIsoOfStableModels`, the existence half of Stacks 0E97 for schemes), then
`AlgebraicGeometry.UniqueStableModels` holds: an isomorphism of the generic fibres of two stable
families of genus `g` over a discrete valuation ring extends uniquely. The uniqueness is proved
here: a stable family is separated and its generic fibre is scheme-theoretically dense. -/
theorem uniqueStableModels_of {g : ℕ} (hA : StableFamilyTotalIsScheme B hZ g)
    (hB : ExistsIsoOfStableModels B hZ g) : UniqueStableModels B hZ g := by
  intro R _ _ _ K _ _ _ hR hK base gm hgm F F' G G' c c' s hF hF' hG _ hc hc' hs
  obtain rfl : base = specULiftZIsTerminal.from _ := specULiftZIsTerminal.hom_ext _ _
  generalize Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
    specULiftZIsTerminal.from (Spec (.of R)) = b at gm hgm hc hc' hs ⊢
  obtain rfl : b = specULiftZIsTerminal.from _ := specULiftZIsTerminal.hom_ext _ _
  exact existsUnique_hom_of_existsIsoOfStableModels hA hB R K hR hK gm hgm c c' s hF hF' hG hc
    hc' hs

end AlgebraicGeometry

end
