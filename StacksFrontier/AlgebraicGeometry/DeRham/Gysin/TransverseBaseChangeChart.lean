module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.TransverseBaseChangeRestrict
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ClassMapBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.EquationChartBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartClsAnyCount
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictSections
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.ChartHom
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgePullback
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassAnyModule

/-!
# The chart computation of Tag 0G89

Over an equation chart `W` of `Z ⊆ X`, with its preimage chart `g⁻¹W` of `Z' ⊆ X'`, the right
vertical arrow of [Stacks, Tag 0G89] (`Stacks.Gysin.gysinBaseChangePull`) carries the class map
`c_{f₁,…,f_c}` of [Stacks, Tag 0G7Q] to the class map `c_{g^♯f₁,…,g^♯f_c}`, against the canonical
map of relative forms.  This is [Stacks, Tag 0G7U] read on a chart.

## Main results

* `Stacks.Gysin.restrictSquarePullbackHom_app_pullbackSection`: the restriction square of
  pullbacks `(g|_W)^*(ℱ|_W) ⟶ (g^*ℱ)|_{g⁻¹W}` on pulled-back sections.
* `Stacks.Gysin.classMapToSupport_restrictSquare`: the chart class map against the right
  vertical arrow, in the pullback spelling.
* `Stacks.Gysin.chartClsHomOfClassMap_gysinBaseChangePull`: the same for the chart class maps of
  `Stacks.Gysin.chartClsHomOfClassMap`, in the restriction spelling.
* `Stacks.Gysin.chartClsOfClassMap_gysinBaseChangePull`: the same on sections; this is the field
  `tgt_cls` of `Stacks.Gysin.GysinBaseChange`, proved.

## Implementation notes

The restriction of the right vertical arrow to the preimage chart is
`Stacks.Gysin.supportedBaseChangePull_restrict_forms`; the base change of the class map is
`Stacks.Gysin.classMapToSupport_baseChange`.  The two spellings of the ambient categories,
`X.Modules` and `SheafOfModules (structureSheafRing X.toRingedSpace)`, do not let `rw` cross
them, so every chase is done by a lemma at a variable category, applied with `exact`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Perfect.SupportedFraction (supportPush supportCohomologySheaf
  supportCohomologySheafFunctor)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.FractionClass (classMapToSupport)
open AlgebraicGeometry.RingedSpaceThickening (derivedPullbackSingleObj)
open Stacks.DeRham.GysinCohomologyBaseChange
  (derivedPullbackSingleObj_eq_derivedToOrdinaryPullbackSingle)

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

section Sections

open Scheme.Modules (pullbackSection)

/-- A morphism of sheaves of modules carries the `inv` of an isomorphism back on sections. -/
theorem iso_hom_val_app_of_inv {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B) (V : Y.Opens)
    {x : A.val.obj (op V)} {y : B.val.obj (op V)} (h : e.inv.val.app (op V) y = x) :
    e.hom.val.app (op V) x = y := by
  rw [← h]
  exact congrArg (fun k : B ⟶ B => k.val.app (op V) y) e.inv_hom_id

/-- **The inverse composition law for pullback, on pulled-back sections.** -/
theorem pullbackComp_inv_app_pullbackSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (W : Y.Opens) (V : X.Opens)
    (hg : W ≤ g ⁻¹ᵁ U) (hf : V ≤ f ⁻¹ᵁ W) (h : V ≤ (f ≫ g) ⁻¹ᵁ U)
    (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op V)
        (pullbackSection (f ≫ g) M U V h a) =
      pullbackSection f ((Scheme.Modules.pullback g).obj M) W V hf
        (pullbackSection g M U W hg a) := by
  rw [← Scheme.Modules.pullbackSection_comp f g M U W V hg hf h a]
  show (((Scheme.Modules.pullbackComp f g).hom.app M ≫
    (Scheme.Modules.pullbackComp f g).inv.app M).val.app (op V)) _ = _
  rw [Iso.hom_inv_id_app]
  rfl

/-- A transport along an equality of morphisms carries a pulled-back section to the
pulled-back section. -/
theorem eqToHom_app_pullbackSection {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hf : f = f')
    (M : Y.Modules) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ f' ⁻¹ᵁ U)
    (a : M.val.obj (op U)) :
    (eqToHom (congrArg (fun r : X ⟶ Y => (Scheme.Modules.pullback r).obj M) hf)).val.app (op V)
        (pullbackSection f M U V h a) = pullbackSection f' M U V h' a := by
  subst hf
  rfl

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (W : X.Opens)

/-- **The restriction square of pullbacks, in the restriction spelling**: the comparison
`(g|_W)^*(ℱ|_W) ⟶ (g^*ℱ)|_{g⁻¹W}`, built from `Stacks.Gysin.restrictSquareModuleIso` and
Mathlib's identification of restriction with pullback along an open immersion. -/
def restrictSquarePullbackHom (N : X.Modules) :
    (Scheme.Modules.pullback (g ∣_ W)).obj ((Scheme.Modules.restrictFunctor W.ι).obj N) ⟶
      (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).obj ((Scheme.Modules.pullback g).obj N) :=
  (Scheme.Modules.pullback (g ∣_ W)).map
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app N) ≫
    (restrictSquareModuleIso g W N).inv ≫
    (Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ W).ι).inv.app
      ((Scheme.Modules.pullback g).obj N)

/-- The open of the pulled-back chart lies over the open of the chart. -/
theorem image_le_preimage_image {O : W.toScheme.Opens} {V : (g ⁻¹ᵁ W).toScheme.Opens}
    (h : V ≤ (g ∣_ W) ⁻¹ᵁ O) : (g ⁻¹ᵁ W).ι ''ᵁ V ≤ g ⁻¹ᵁ (W.ι ''ᵁ O) := by
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨(g ∣_ W).base v, h hv, ?_⟩
  exact congrArg (fun φ : (g ⁻¹ᵁ W).toScheme ⟶ X => φ.base v) (morphismRestrict_ι g W)

/-- **The restriction square on pulled-back sections**: it carries the pullback along `g|_W` of a
section of `ℱ|_W` to the pullback along `g` of that section, restricted. -/
theorem restrictSquarePullbackHom_app_pullbackSection (N : X.Modules) (O : W.toScheme.Opens)
    (V : (g ⁻¹ᵁ W).toScheme.Opens) (h : V ≤ (g ∣_ W) ⁻¹ᵁ O)
    (z : ((Scheme.Modules.restrictFunctor W.ι).obj N).val.obj (op O)) :
    (restrictSquarePullbackHom g W N).val.app (op V)
        (pullbackSection (g ∣_ W) ((Scheme.Modules.restrictFunctor W.ι).obj N) O V h z) =
      pullbackSection g N (W.ι ''ᵁ O) ((g ⁻¹ᵁ W).ι ''ᵁ V) (image_le_preimage_image g W h) z := by
  have hO : O ≤ W.ι ⁻¹ᵁ (W.ι ''ᵁ O) := (W.ι.preimage_image_eq O).ge
  have s1 : ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app N).val.app (op O) z =
      pullbackSection W.ι N (W.ι ''ᵁ O) O hO z :=
    iso_hom_val_app_of_inv ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app N) O
      ((Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection W.ι N (W.ι ''ᵁ O) O hO
        le_rfl z).trans (Stacks.Gysin.presheaf_map_le_refl N _ z))
  have s2 := Scheme.Modules.pullbackSection_naturality (g ∣_ W)
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app N) O V h z
  rw [s1] at s2
  have hV1 : V ≤ ((g ∣_ W) ≫ W.ι) ⁻¹ᵁ (W.ι ''ᵁ O) := fun v hv => ⟨_, h hv, rfl⟩
  have hV2 : V ≤ ((g ⁻¹ᵁ W).ι ≫ g) ⁻¹ᵁ (W.ι ''ᵁ O) :=
    fun v hv => image_le_preimage_image g W h ⟨v, hv, rfl⟩
  have s3 := Scheme.Modules.pullbackSection_comp (g ∣_ W) W.ι N (W.ι ''ᵁ O) O V hO h hV1 z
  have s4 := eqToHom_app_pullbackSection (morphismRestrict_ι g W) N (W.ι ''ᵁ O) V hV1 hV2 z
  have hV3 : V ≤ (g ⁻¹ᵁ W).ι ⁻¹ᵁ (g ⁻¹ᵁ (W.ι ''ᵁ O)) :=
    fun v hv => image_le_preimage_image g W h ⟨v, hv, rfl⟩
  have s5 := pullbackComp_inv_app_pullbackSection (g ⁻¹ᵁ W).ι g N (W.ι ''ᵁ O)
    (g ⁻¹ᵁ (W.ι ''ᵁ O)) V le_rfl hV3 hV2 z
  have s6 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection (g ⁻¹ᵁ W).ι
    ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ (W.ι ''ᵁ O)) V hV3
    (image_le_preimage_image g W h) (pullbackSection g N (W.ι ''ᵁ O) (g ⁻¹ᵁ (W.ι ''ᵁ O)) le_rfl z)
  have s7 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink g N (W.ι ''ᵁ O)
    (g ⁻¹ᵁ (W.ι ''ᵁ O))
    ((g ⁻¹ᵁ W).ι ''ᵁ V) le_rfl (image_le_preimage_image g W h) (image_le_preimage_image g W h) z
  refine Eq.trans ?_ (s6.trans ?_)
  · refine congrArg (((Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ W).ι).inv.app
      ((Scheme.Modules.pullback g).obj N)).val.app (op V)) ?_
    refine Eq.trans ?_ s5
    refine congrArg (((Scheme.Modules.pullbackComp (g ⁻¹ᵁ W).ι g).inv.app N).val.app (op V)) ?_
    refine Eq.trans ?_ s4
    refine congrArg ((eqToHom (congrArg (fun r => (Scheme.Modules.pullback r).obj N)
      (morphismRestrict_ι g W))).val.app (op V)) ?_
    refine Eq.trans ?_ s3
    exact congrArg (((Scheme.Modules.pullbackComp (g ∣_ W) W.ι).hom.app N).val.app (op V)) s2
  · exact s7

end Sections

section ClassMap

/-- Cancelling two transports, at a variable category. -/
theorem eqToHom_cancel_formal {𝒞 : Type*} [Category 𝒞] {A C C' : 𝒞} (u : A ⟶ C) (e₁ : C = C')
    (e₂ : C' = C) (x : A ⟶ C') (y : A ⟶ C) (h1 : u ≫ eqToHom e₁ = x)
    (h2 : x ≫ eqToHom e₂ = y) : u = y := by
  subst e₁
  simp only [eqToHom_refl, Category.comp_id] at h1 h2
  rw [← h2, ← h1]

/-- **The class map of [Stacks, Tag 0G7Q] commutes with base change, at any closed subset equal
to the zero locus.**  `Stacks.Gysin.classMapToSupport_baseChange` with the zero locus of the
equations replaced by a closed subset `T` equal to it, which is the spelling the chart class maps
carry. -/
theorem classMapToSupport_baseChange_of_eq {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {c : ℕ}
    (f : Fin c → Γ(Y, ⊤)) (F : Y.Modules) [F.IsQuasicoherent] {T : Set Y} (hT : IsClosed T)
    (hfT : equationsClosedSet f = T)
    (hLE : ((supportPush hT).obj
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F)).IsLE (c : ℤ)) :
    (Scheme.Modules.pullback g).map (classMapToSupport f F hT hfT.le) ≫
      supportedBaseChangePull g.toLRSHom.toShHom T hT (c : ℤ)
        (derivedPullbackSingleObj g.toLRSHom.toShHom F) hLE =
      classMapToSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
        (isClosed_closedSubsetPreimage _ T hT)
        ((Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback g f).trans
          (congrArg (closedSubsetPreimage g.toLRSHom.toShHom) hfT)).le := by
  subst hfT
  have H := classMapToSupport_baseChange g f F hLE
  have H2 := classMapToSupport_comp_eqToHom (fun j => g.appTop (f j))
    ((Scheme.Modules.pullback g).obj F)
    (isClosed_closedSubsetPreimage _ _ (isClosed_equationsClosedSet f))
    (Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback g f) (𝟙 _)
  simp only [Category.comp_id] at H2
  exact eqToHom_cancel_formal _ _ _ _ _ ((Category.assoc _ _ _).trans H) H2

/-- **The class map does not see a transport of its closed subset**, read on the derived
spelling of the transport. -/
theorem classMapToSupport_comp_homology_eqToHom {Y : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(Y, ⊤))
    (M : Y.Modules) {T T' : Set Y} (hTT' : T = T') (hT : IsClosed T) (hT' : IsClosed T')
    (hf : equationsClosedSet f ⊆ T) (hf' : equationsClosedSet f ⊆ T') :
    classMapToSupport f M hT hf ≫
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
          (c : ℤ)).map
        (eqToHom (derivedSupportedPushforward_obj_congr hTT' hT hT'
          ((DerivedCategory.singleFunctor _ 0).obj M))) =
      classMapToSupport f M hT' hf' := by
  subst hTT'
  exact Eq.trans (congrArg (fun t => classMapToSupport f M hT hf ≫ t)
    (((DerivedCategory.homologyFunctor _ (c : ℤ)).congr_map (eqToHom_refl _ _)).trans
      ((DerivedCategory.homologyFunctor _ (c : ℤ)).map_id _))) (Category.comp_id _)

end ClassMap

/-- The chase of `classMapToSupport_restrictSquare`, at a variable category. -/
theorem transverse_chart_formal {𝒞 : Type*} [Category 𝒞]
    {A0 A2 A1 B0 B1 B2 B3 C1 D : 𝒞}
    (Gcl : A0 ⟶ A2) (GSi : A2 ⟶ A1) (GSh : A1 ⟶ A2) (GclSi : A0 ⟶ A1) (Ri : A1 ⟶ B0)
    (Rh : B0 ⟶ A1) (jP : B0 ⟶ B1) (S'h : B1 ⟶ B2) (S'i : B2 ⟶ B1) (SB : A2 ⟶ B3)
    (Heq : B3 ⟶ B2) (SBd : A2 ⟶ C1) (Hβ : C1 ⟶ B3) (cl1 : A0 ⟶ C1) (β : A0 ⟶ D)
    (cl1' : D ⟶ B3) (cl2 : D ⟶ B2)
    (hG : GclSi = Gcl ≫ GSi) (hS : GSi ≫ GSh = 𝟙 A2) (hR : Ri ≫ Rh = 𝟙 A1)
    (hS' : S'h ≫ S'i = 𝟙 B1) (RF : jP ≫ S'h = Rh ≫ GSh ≫ SB ≫ Heq) (PC : SB = SBd ≫ Hβ)
    (BC : Gcl ≫ SBd = cl1) (NAT : β ≫ cl1' = cl1 ≫ Hβ) (TR : cl1' ≫ Heq = cl2) :
    GclSi ≫ Ri ≫ jP = β ≫ cl2 ≫ S'i := by
  have key : GclSi ≫ Ri ≫ jP ≫ S'h = β ≫ cl2 := by
    rw [RF, reassoc_of% hR, hG, Category.assoc, reassoc_of% hS, PC, Category.assoc,
      reassoc_of% BC, ← reassoc_of% NAT, TR]
  simpa [hS'] using key =≫ S'i

section Chart

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (W : X.Opens)

/-- The zero locus of the equations pulled back to the preimage chart is the preimage of the
closed subset. -/
theorem equationsClosedSet_restrict_pullback {c : ℕ} (Zs : Set X) (f : Fin c → Γ(W.toScheme, ⊤))
    (hf : equationsClosedSet f = W.ι ⁻¹' Zs) :
    equationsClosedSet (fun k => (g ∣_ W).appTop (f k)) =
      closedSubsetPreimage (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
        (closedSubsetPreimage g.toLRSHom.toShHom Zs) :=
  ((Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback (g ∣_ W) f).trans
    (congrArg (closedSubsetPreimage (g ∣_ W).toLRSHom.toShHom) hf)).trans
    (closedSubsetPreimage_restrict g W Zs)

/-- **The chart class map commutes with the right vertical arrow of [Stacks, Tag 0G89]**, in the
pullback spelling: on the preimage chart, the class map of the restricted equations followed by
the excision, pulled back along `g|_W` and carried by the restriction square to the pullback of
the right vertical arrow, is the coefficient map followed by the class map of the pulled-back
equations and the excision.  This is [Stacks, Tag 0G7U] read on a chart. -/
theorem classMapToSupport_restrictSquare (c : ℕ) (Zs : Set X) (hZs : IsClosed Zs)
    (F : X.Modules) [F.IsQuasicoherent] {F' : X'.Modules} [F'.IsQuasicoherent]
    (ρ : (Scheme.Modules.pullback g).obj F ⟶ F') (f : Fin c → Γ(W.toScheme, ⊤))
    (hf : equationsClosedSet f = W.ι ⁻¹' Zs)
    (hLE : ((derivedSupportedPushforward X.toRingedSpace Zs hZs).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE (c : ℤ))
    (hLEW₁ : ((derivedSupportedPushforward (X.toRingedSpace.restrict W.isOpenEmbedding)
      (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
      (isClosed_closedSubsetPreimage _ Zs hZs)).obj
        ((derivedPullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))).IsLE (c : ℤ))
    (hLEW₂ : ((derivedSupportedPushforward (X.toRingedSpace.restrict W.isOpenEmbedding)
      (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
      (isClosed_closedSubsetPreimage _ Zs hZs)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj F))).IsLE (c : ℤ)) :
    (Scheme.Modules.pullback (g ∣_ W)).map
        (classMapToSupport f ((Scheme.Modules.pullback W.ι).obj F)
            (isClosed_closedSubsetPreimage _ Zs hZs) hf.le ≫
          (supportCohomologyPullbackIso (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs hZs
            (c : ℤ) F).inv) ≫
      (restrictSquareModuleIso g W _).inv ≫
      (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map
        (supportedBaseChangePull g.toLRSHom.toShHom Zs hZs (c : ℤ)
          (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
            g.toLRSHom.toShHom F 0 ≫ (DerivedCategory.singleFunctor _ 0).map ρ) hLE) =
    ((restrictSquareModuleIso g W F).inv ≫
        (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map ρ) ≫
      classMapToSupport (fun k => (g ∣_ W).appTop (f k))
          ((Scheme.Modules.pullback (g ⁻¹ᵁ W).ι).obj F')
          (isClosed_closedSubsetPreimage _ _ (isClosed_closedSubsetPreimage _ Zs hZs))
          (equationsClosedSet_restrict_pullback g W Zs f hf).le ≫
        (supportCohomologyPullbackIso (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
          (closedSubsetPreimage g.toLRSHom.toShHom Zs) (isClosed_closedSubsetPreimage _ Zs hZs)
          (c : ℤ) F').inv := by
  have : ((Scheme.Modules.pullback W.ι).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback W.ι F
  have : ((Scheme.Modules.pullback (g ∣_ W)).obj
      ((Scheme.Modules.pullback W.ι).obj F)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback (g ∣_ W) _
  have : ((Scheme.Modules.pullback (g ⁻¹ᵁ W).ι).obj F').IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback (g ⁻¹ᵁ W).ι F'
  have RF := supportedBaseChangePull_restrict_forms g W Zs hZs (c : ℤ) F ρ hLE hLEW₁ hLEW₂
  have PC := supportedBaseChangePull_comp_map (restrictHom g W)
    (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
    (isClosed_closedSubsetPreimage _ Zs hZs) (c : ℤ)
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
      (restrictHom g W) ((modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj F) 0)
    ((DerivedCategory.singleFunctor _ 0).map ((restrictSquareModuleIso g W F).inv ≫
      (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map ρ)) hLEW₂
  have hd := derivedPullbackSingleObj_eq_derivedToOrdinaryPullbackSingle
    (restrictHom g W) ((modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj F)
  have hfle := ((Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback
    (g ∣_ W) f).trans (congrArg (closedSubsetPreimage (g ∣_ W).toLRSHom.toShHom) hf)).le
  have BC := classMapToSupport_baseChange_of_eq (g ∣_ W) f ((Scheme.Modules.pullback W.ι).obj F)
    (isClosed_closedSubsetPreimage _ Zs hZs) hf hLEW₂
  have hd' := congrArg (fun a => supportedBaseChangePull (restrictHom g W)
    (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
    (isClosed_closedSubsetPreimage _ Zs hZs) (c : ℤ) a hLEW₂) hd.symm
  let σ : (Scheme.Modules.pullback (g ∣_ W)).obj ((Scheme.Modules.pullback W.ι).obj F) ⟶
      (Scheme.Modules.pullback (g ⁻¹ᵁ W).ι).obj F' :=
    (restrictSquareModuleIso g W F).inv ≫
      (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map ρ
  have NAT := Stacks.Gysin.classMapToSupport_naturality (fun k => (g ∣_ W).appTop (f k)) σ
    (isClosed_closedSubsetPreimage _ _ (isClosed_closedSubsetPreimage _ Zs hZs))
    hfle
    (Stacks.Perfect.FractionClass.fracTermTop_naturality (fun k => (g ∣_ W).appTop (f k)) σ)
  have TR := classMapToSupport_comp_homology_eqToHom (fun k => (g ∣_ W).appTop (f k))
    ((Scheme.Modules.pullback (g ⁻¹ᵁ W).ι).obj F') (closedSubsetPreimage_restrict g W Zs)
    (isClosed_closedSubsetPreimage _ _ (isClosed_closedSubsetPreimage _ Zs hZs))
    (isClosed_closedSubsetPreimage _ _ (isClosed_closedSubsetPreimage _ Zs hZs))
    hfle
    (equationsClosedSet_restrict_pullback g W Zs f hf).le
  exact transverse_chart_formal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((Scheme.Modules.pullback (g ∣_ W)).map_comp _ _)
    ((Scheme.Modules.pullback (g ∣_ W)).map_inv_hom' _)
    (Iso.inv_hom_id _) (Iso.hom_inv_id _) RF (PC.trans (congrArg (· ≫ _) hd')) BC NAT TR

end Chart

/-- A transport along an equality of an object with itself is the identity. -/
theorem comp_eqToHom_self {𝒞 : Type*} [Category 𝒞] {A B : 𝒞} (u : A ⟶ B) (e : B = B) :
    u ≫ eqToHom e = u := by
  simp

/-- The chase of `chartClassMap_restrictSquare`, at variable categories. -/
theorem transverse_chart_restrict_formal {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟)
    {A A' B B' C C' : 𝒞} {D0 D1 D2 D3 E0 E1 E2 E3 E4 E5 : 𝒟}
    (ClsR : A ⟶ C) (clR : A ⟶ B) (sm : B ⟶ B') (si : B' ⟶ C') (ri : C' ⟶ C) (rh : C ⟶ C')
    (rhF : A ⟶ A') (clP : A' ⟶ B')
    (Ψ : G.obj C ⟶ D0) (Rinv : G.obj C' ⟶ D1) (r'i : D1 ⟶ D0) (jRP : D0 ⟶ D2) (jP : D1 ⟶ D3)
    (r'i2 : D3 ⟶ D2) (jP' : D1 ⟶ D3) (ΨF : G.obj A ⟶ E0) (RinvF : G.obj A' ⟶ E1) (r'iF : E1 ⟶ E0)
    (jRρ : E0 ⟶ E2) (jρ : E1 ⟶ E3) (r'iF' : E3 ⟶ E2) (ClsR' : E2 ⟶ D2) (clR' : E2 ⟶ E4)
    (s'm : E4 ⟶ E5) (s'i : E5 ⟶ D3) (cl' : E3 ⟶ E5) (suppr : E5 ⟶ E4)
    (hCls : ClsR = clR ≫ sm ≫ si ≫ ri) (hΨ : Ψ = G.map rh ≫ Rinv ≫ r'i)
    (hΨF : ΨF = G.map rhF ≫ RinvF ≫ r'iF) (hCls' : ClsR' = clR' ≫ s'm ≫ s'i ≫ r'i2)
    (n1 : clR ≫ sm = rhF ≫ clP) (n2 : ri ≫ rh = 𝟙 C') (n3 : r'i ≫ jRP = jP' ≫ r'i2)
    (hjP : jP' = jP)
    (MP : G.map (clP ≫ si) ≫ Rinv ≫ jP = (RinvF ≫ jρ) ≫ cl' ≫ s'i)
    (n4 : r'iF ≫ jRρ = jρ ≫ r'iF') (n5 : r'iF' ≫ clR' = cl' ≫ suppr) (n6 : suppr ≫ s'm = 𝟙 E5) :
    G.map ClsR ≫ Ψ ≫ jRP = ΨF ≫ jRρ ≫ ClsR' := by
  have e1 : G.map ClsR ≫ G.map rh = G.map rhF ≫ G.map (clP ≫ si) := by
    rw [← G.map_comp, ← G.map_comp, hCls]
    congr 1
    simp only [Category.assoc, n2, Category.comp_id]
    rw [← Category.assoc, n1, Category.assoc]
  have e2 : G.map ClsR ≫ Ψ ≫ jRP = G.map rhF ≫ ((RinvF ≫ jρ) ≫ cl' ≫ s'i) ≫ r'i2 := by
    rw [← MP, hΨ]
    simp only [Category.assoc]
    rw [n3, hjP, ← Category.assoc (G.map ClsR), e1]
    simp only [Category.assoc]
  rw [e2, hΨF, hCls']
  simp only [Category.assoc]
  rw [reassoc_of% n4, reassoc_of% n5, reassoc_of% n6]

section ChartRestrict

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (W : X.Opens)

/-- `Stacks.Gysin.supportCohomologyRestrictIso` factor by factor. -/
theorem supportCohomologyRestrictIso_inv_eq {Y : Scheme.{u}} (V : Y.Opens) {T : Set Y}
    (hT : IsClosed T) (hTV : IsClosed (V.ι ⁻¹' T)) (n : ℤ) (M : Y.Modules) :
    (supportCohomologyRestrictIso V hT hTV n M).inv =
      (supportCohomologySheafFunctor hTV n).map
          ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app M) ≫
        (supportCohomologyPullbackIso (Y.toRingedSpace.ofRestrict V.isOpenEmbedding) T hT n M).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app
          ((supportCohomologySheafFunctor hT n).obj M) :=
  rfl

/-- **The chart class map commutes with the right vertical arrow of [Stacks, Tag 0G89]**, in the
restriction spelling in which the Gysin maps of the charts are written. -/
theorem chartClassMap_restrictSquare (c : ℕ) (Zs : Set X) (hZs : IsClosed Zs)
    (F : X.Modules) [F.IsQuasicoherent] {F' : X'.Modules} [F'.IsQuasicoherent]
    (ρ : (Scheme.Modules.pullback g).obj F ⟶ F') (f : Fin c → Γ(W.toScheme, ⊤))
    (hf : equationsClosedSet f = W.ι ⁻¹' Zs) {Zs' : Set X'}
    (hZZ' : closedSubsetPreimage g.toLRSHom.toShHom Zs = Zs') (hZs' : IsClosed Zs')
    (hLE : ((derivedSupportedPushforward X.toRingedSpace Zs hZs).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE (c : ℤ))
    (hLEW₁ : ((derivedSupportedPushforward (X.toRingedSpace.restrict W.isOpenEmbedding)
      (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
      (isClosed_closedSubsetPreimage _ Zs hZs)).obj
        ((derivedPullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))).IsLE (c : ℤ))
    (hLEW₂ : ((derivedSupportedPushforward (X.toRingedSpace.restrict W.isOpenEmbedding)
      (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
      (isClosed_closedSubsetPreimage _ Zs hZs)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj F))).IsLE (c : ℤ)) :
    (Scheme.Modules.pullback (g ∣_ W)).map
        (classMapToSupport f ((Scheme.Modules.restrictFunctor W.ι).obj F)
            (isClosed_closedSubsetPreimage _ Zs hZs) hf.le ≫
          (supportCohomologyRestrictIso W hZs (isClosed_closedSubsetPreimage _ Zs hZs)
            (c : ℤ) F).inv) ≫
      restrictSquarePullbackHom g W _ ≫
      (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).map
        (supportedBaseChangePull g.toLRSHom.toShHom Zs hZs (c : ℤ)
          (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
            g.toLRSHom.toShHom F 0 ≫ (DerivedCategory.singleFunctor _ 0).map ρ) hLE ≫
          eqToHom (homology_supportPush_congr hZZ' (isClosed_closedSubsetPreimage _ Zs hZs) hZs'
            (c : ℤ) _)) =
    restrictSquarePullbackHom g W F ≫ (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).map ρ ≫
      classMapToSupport (fun k => (g ∣_ W).appTop (f k))
          ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).obj F')
          (isClosed_closedSubsetPreimage _ _ hZs')
          ((equationsClosedSet_restrict_pullback g W Zs f hf).trans
            (congrArg _ hZZ')).le ≫
        (supportCohomologyRestrictIso (g ⁻¹ᵁ W) hZs' (isClosed_closedSubsetPreimage _ _ hZs')
          (c : ℤ) F').inv := by
  subst hZZ'
  have : ((Scheme.Modules.pullback W.ι).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback W.ι F
  have : ((Scheme.Modules.pullback (g ⁻¹ᵁ W).ι).obj F').IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback (g ⁻¹ᵁ W).ι F'
  have MP := classMapToSupport_restrictSquare g W c Zs hZs F ρ f hf hLE hLEW₁ hLEW₂
  have n1 := (Stacks.Gysin.classMapToSupport_naturality f
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app F)
    (isClosed_closedSubsetPreimage _ Zs hZs) hf.le
    (Stacks.Perfect.FractionClass.fracTermTop_naturality f _)).symm
  have n5 := Stacks.Gysin.classMapToSupport_naturality (fun k => (g ∣_ W).appTop (f k))
    ((Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ W).ι).inv.app F')
    (isClosed_closedSubsetPreimage _ _ hZs')
    (equationsClosedSet_restrict_pullback g W Zs f hf).le
    (Stacks.Perfect.FractionClass.fracTermTop_naturality _ _)
  exact transverse_chart_restrict_formal (Scheme.Modules.pullback (g ∣_ W)) _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (supportCohomologyRestrictIso_inv_eq _ _ _ _ _ |> congrArg (fun t => _ ≫ t)) rfl rfl
    (supportCohomologyRestrictIso_inv_eq _ _ _ _ _ |> congrArg (fun t => _ ≫ t))
    n1 (Iso.inv_hom_id_app _ _)
    ((Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ W).ι).inv.naturality _).symm
    (congrArg (Scheme.Modules.pullback (g ⁻¹ᵁ W).ι).map (comp_eqToHom_self _ _)) MP
    ((Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ W).ι).inv.naturality _).symm n5
    ((supportCohomologySheafFunctor _ (c : ℤ)).map_inv_hom'
      ((Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ W).ι).app _))

end ChartRestrict

/-- `IsLE` is carried along an equality of objects. -/
theorem isLE_of_eq_obj {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K L : DerivedCategory C} (h : K = L) {n : ℤ} (hK : K.IsLE n) : L.IsLE n :=
  h ▸ hK

section GysinChart

open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.ModuleLimits (pullbackSection_shrink)
open Scheme.Modules (pullbackSection)

variable {Z X S Z' X' S' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (h : Z' ⟶ Z) (g : X' ⟶ X)
  (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)
  [IsClosedImmersion i] [LocallyOfFinitePresentation i] [IsClosedImmersion i']

/-- The zero locus of the pulled-back chart equations is the part of `Z'` over the pulled-back
chart. -/
theorem equationsClosedSet_restrict_pullback_range (hcart : IsPullback h i' i g) (W : X.Opens)
    {c : ℕ} (fW : Fin c → Γ(W.toScheme, ⊤))
    (hfW : equationsClosedSet fW = W.ι ⁻¹' Set.range i.base) :
    equationsClosedSet (fun k => (g ∣_ W).appTop (fW k)) =
      (g ⁻¹ᵁ W).ι ⁻¹' Set.range i'.base :=
  (equationsClosedSet_restrict_pullback g W _ fW hfW).trans
    (congrArg _ (range_base_eq_closedSubsetPreimage i i' h g hcart).symm)

/-- **The chart class maps against the right vertical arrow of [Stacks, Tag 0G89]**: over the
preimage of a chart, the right vertical arrow carries the class map of the chart's equations to
the class map of the pulled-back equations, against the canonical map of relative forms.  This is
[Stacks, Tag 0G7U] on a chart, the restriction of [Stacks, Tag 0G78] to the chart having been
computed by `Stacks.Gysin.supportedBaseChangePull_restrict_forms`. -/
theorem chartClsHomOfClassMap_gysinBaseChangePull (hcart : IsPullback h i' i g)
    (right_comm : g ≫ π = π' ≫ t) {c : ℕ} (p : ℕ) (hE : ConormalRank i c) (W : X.Opens)
    (fW : Fin c → Γ(W.toScheme, ⊤)) (hfW : equationsClosedSet fW = W.ι ⁻¹' Set.range i.base)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hT' : IsClosed ((g ⁻¹ᵁ W).ι ⁻¹' Set.range i'.base)) :
    (Scheme.Modules.pullback (g ∣_ W)).map (chartClsHomOfClassMap i π p W fW hT hfW.le) ≫
      restrictSquarePullbackHom g W _ ≫
      (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).map
        (gysinBaseChangePull i i' h g π π' t hcart right_comm p hE) =
    restrictSquarePullbackHom g W _ ≫
      (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).map
        (relativeDifferentialFormsMap g π π' t right_comm ((p : ℤ) + (c : ℤ))) ≫
      chartClsHomOfClassMap i' π' p (g ⁻¹ᵁ W) (fun k => (g ∣_ W).appTop (fW k)) hT'
        (equationsClosedSet_restrict_pullback_range i i' h g hcart W fW hfW).le := by
  have : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p c
  have : (relativeDifferentialForms π' ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π' p c
  have : ((Scheme.Modules.pullback W.ι).obj
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback W.ι _
  have hLE := isLE_supportPush_range_of_conormalRank i hE
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
  have hN : DerivedCategory.TStructure.t.IsLE ((derivedSupportedPushforward X.toRingedSpace
      (Set.range i.base) (isClosed_range_base i)).obj ((DerivedCategory.singleFunctor _ 0).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) (c : ℤ) := hLE
  have hιN := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj'
    (X.toRingedSpace.ofRestrict W.isOpenEmbedding) _ (c : ℤ) hN
  have : DerivedCategory.TStructure.t.IsLE ((derivedSupportedPushforward X.toRingedSpace
      (Set.range i.base) (isClosed_range_base i) ⋙
        derivedPullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) (c : ℤ) := hιN
  have hLEW₁ := (DerivedCategory.TStructure.t).isLE_of_iso
    ((Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso
      (X.toRingedSpace.ofRestrict W.isOpenEmbedding) (Set.range i.base)
      (isClosed_range_base i)).app ((DerivedCategory.singleFunctor _ 0).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) (c : ℤ)
  have hLEW₂ := isLE_of_eq_obj (derivedSupportedPushforward_obj_congr hfW
    (isClosed_equationsClosedSet fW) (isClosed_closedSubsetPreimage _ _ (isClosed_range_base i))
    ((DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.pullback W.ι).obj
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))))
    (isLE_supportPush_equationsClosedSet fW ((Scheme.Modules.pullback W.ι).obj
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))))
  have key := chartClassMap_restrictSquare g W c (Set.range i.base) (isClosed_range_base i)
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
    (relativeDifferentialFormsMap g π π' t right_comm ((p : ℤ) + (c : ℤ))) fW hfW
    (range_base_eq_closedSubsetPreimage i i' h g hcart).symm (isClosed_range_base i') hLE
    hLEW₁ hLEW₂
  have hd := derivedPullbackSingleObj_eq_derivedToOrdinaryPullbackSingle
    g.toLRSHom.toShHom (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
  have hP : gysinBaseChangePull i i' h g π π' t hcart right_comm p hE =
      supportedBaseChangePull g.toLRSHom.toShHom (Set.range i.base) (isClosed_range_base i)
        (c : ℤ) (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
            g.toLRSHom.toShHom (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) 0 ≫
          (DerivedCategory.singleFunctor _ 0).map
            (relativeDifferentialFormsMap g π π' t right_comm ((p : ℤ) + (c : ℤ)))) hLE ≫
        eqToHom (homology_supportPush_congr
          (range_base_eq_closedSubsetPreimage i i' h g hcart).symm _ (isClosed_range_base i')
          (c : ℤ) _) :=
    congrArg (fun a => supportedBaseChangePull g.toLRSHom.toShHom (Set.range i.base)
        (isClosed_range_base i) (c : ℤ) (a ≫ (DerivedCategory.singleFunctor _ 0).map
          (relativeDifferentialFormsMap g π π' t right_comm ((p : ℤ) + (c : ℤ)))) hLE ≫
        eqToHom (homology_supportPush_congr
          (range_base_eq_closedSubsetPreimage i i' h g hcart).symm _ (isClosed_range_base i')
          (c : ℤ) _)) hd
  rw [hP]
  exact key

open Stacks.Perfect.LocalCohomologyExcision (chartOpen ι_image_chartOpen) in
/-- **The class map of the pulled-back chart lies over the class map of the chart**, on
sections: the right vertical arrow of [Stacks, Tag 0G89], read on `X` through `g^* ⊣ g_*`,
carries `c_{f₁,…,f_c}(y)` to `c_{g^♯f₁,…,g^♯f_c}(g^*y)`.  This is the field `tgt_cls` of
`Stacks.Gysin.GysinBaseChange`, proved. -/
theorem chartClsOfClassMap_gysinBaseChangePull (hcart : IsPullback h i' i g)
    (right_comm : g ≫ π = π' ≫ t) {c : ℕ} (p : ℕ) (hE : ConormalRank i c) (W : X.Opens)
    (fW : Fin c → Γ(W.toScheme, ⊤)) (hfW : equationsClosedSet fW = W.ι ⁻¹' Set.range i.base)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hT' : IsClosed ((g ⁻¹ᵁ W).ι ⁻¹' Set.range i'.base)) (V : X.Opens) (hV : V ≤ W)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V)) :
    (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
        (gysinBaseChangePull i i' h g π π' t hcart right_comm p hE)).val.app (op V))
        (chartClsOfClassMap i π p W fW hT hfW.le V hV y) =
      chartClsOfClassMap i' π' p (g ⁻¹ᵁ W) (fun k => (g ∣_ W).appTop (fW k)) hT'
        (equationsClosedSet_restrict_pullback_range i i' h g hcart W fW hfW).le (g ⁻¹ᵁ V)
        (fun _ hz => hV hz)
        (relativeDifferentialFormsPullback g π π' t right_comm ((p : ℤ) + (c : ℤ)) V y) := by
  have hV' : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ W := fun _ hz => hV hz
  have hU' : chartOpen (g ⁻¹ᵁ W) hV' ≤ (g ∣_ W) ⁻¹ᵁ chartOpen W hV :=
    (congrArg (fun φ : (g ⁻¹ᵁ W).toScheme ⟶ X => φ ⁻¹ᵁ V) (morphismRestrict_ι g W)).ge
  have hle : g ⁻¹ᵁ V ≤ (g ⁻¹ᵁ W).ι ''ᵁ chartOpen (g ⁻¹ᵁ W) hV' :=
    (ι_image_chartOpen (g ⁻¹ᵁ W) hV').ge
  have hh₁ : (g ⁻¹ᵁ W).ι ''ᵁ chartOpen (g ⁻¹ᵁ W) hV' ≤ g ⁻¹ᵁ (W.ι ''ᵁ chartOpen W hV) :=
    image_le_preimage_image g W hU'
  have key := chartClsHomOfClassMap_gysinBaseChangePull i i' h g π π' t hcart right_comm p hE W
    fW hfW hT hT'
  have s1 := Stacks.AlgebraicGeometry.ModuleLimits.homEquiv_val_app g
    (gysinBaseChangePull i i' h g π π' t hcart right_comm p hE) V
    (chartClsOfClassMap i π p W fW hT hfW.le V hV y)
  refine s1.trans ?_
  set y₀ := (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).presheaf.map
    (homOfLE (ι_image_chartOpen W hV).le).op y
  have s2 := Scheme.Modules.pullbackSection_res g (gysinTarget i π c p)
    (ι_image_chartOpen W hV).ge (g ⁻¹ᵁ V) le_rfl
    (((chartClsHomOfClassMap i π p W fW hT hfW.le).val.app (op (chartOpen W hV))) y₀)
  have s3 := pullbackSection_shrink g (gysinTarget i π c p) (W.ι ''ᵁ chartOpen W hV)
    ((g ⁻¹ᵁ W).ι ''ᵁ chartOpen (g ⁻¹ᵁ W) hV') (g ⁻¹ᵁ V) hh₁ hle (hle.trans hh₁)
    (((chartClsHomOfClassMap i π p W fW hT hfW.le).val.app (op (chartOpen W hV))) y₀)
  refine (congrArg _ (s2.trans s3.symm)).trans ?_
  refine (PresheafOfModules.naturality_apply
    (gysinBaseChangePull i i' h g π π' t hcart right_comm p hE).val (homOfLE hle).op _).trans ?_
  refine congrArg (ConcreteCategory.hom ((gysinTarget i' π' c p).val.map (homOfLE hle).op)) ?_
  have s5 := (restrictSquarePullbackHom_app_pullbackSection g W (gysinTarget i π c p)
    (chartOpen W hV) (chartOpen (g ⁻¹ᵁ W) hV') hU'
    (((chartClsHomOfClassMap i π p W fW hT hfW.le).val.app (op (chartOpen W hV))) y₀)).symm
  have s6 := (Scheme.Modules.pullbackSection_naturality (g ∣_ W)
    (chartClsHomOfClassMap i π p W fW hT hfW.le) (chartOpen W hV) (chartOpen (g ⁻¹ᵁ W) hV')
    hU' y₀).symm
  refine (congrArg _ (s5.trans (congrArg _ s6))).trans ?_
  have s7 := congrArg (fun φ => (φ.val.app (op (chartOpen (g ⁻¹ᵁ W) hV')))
      (pullbackSection (g ∣_ W) _ (chartOpen W hV) (chartOpen (g ⁻¹ᵁ W) hV') hU' y₀)) key
  refine s7.trans ?_
  have s8 := restrictSquarePullbackHom_app_pullbackSection g W
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) (chartOpen W hV)
    (chartOpen (g ⁻¹ᵁ W) hV') hU' y₀
  have s9 := Scheme.Modules.pullbackSection_res g (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
    (ι_image_chartOpen W hV).le ((g ⁻¹ᵁ W).ι ''ᵁ chartOpen (g ⁻¹ᵁ W) hV') hh₁ y
  refine (congrArg (fun z => ((chartClsHomOfClassMap i' π' p (g ⁻¹ᵁ W)
      (fun k => (g ∣_ W).appTop (fW k)) hT'
      (equationsClosedSet_restrict_pullback_range i i' h g hcart W fW hfW).le).val.app
        (op (chartOpen (g ⁻¹ᵁ W) hV')))
      (((relativeDifferentialFormsMap g π π' t right_comm ((p : ℤ) + (c : ℤ))).val.app
        (op ((g ⁻¹ᵁ W).ι ''ᵁ chartOpen (g ⁻¹ᵁ W) hV'))) z)) (s8.trans s9)).trans ?_
  refine congrArg (fun z => ((chartClsHomOfClassMap i' π' p (g ⁻¹ᵁ W)
      (fun k => (g ∣_ W).appTop (fW k)) hT'
      (equationsClosedSet_restrict_pullback_range i i' h g hcart W fW hfW).le).val.app
        (op (chartOpen (g ⁻¹ᵁ W) hV'))) z) ?_
  exact (PresheafOfModules.naturality_apply
    (relativeDifferentialFormsMap g π π' t right_comm ((p : ℤ) + (c : ℤ))).val
    (homOfLE (ι_image_chartOpen (g ⁻¹ᵁ W) hV').le).op _)

end GysinChart

end Stacks.Gysin
