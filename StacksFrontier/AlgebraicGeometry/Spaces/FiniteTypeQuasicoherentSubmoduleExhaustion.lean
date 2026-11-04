module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealLattice
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleComap
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleGermSums
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeSubmoduleDirectedFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeSubmoduleEtaleChartStep

/-!
# Exhaustion by finite type quasi-coherent submodules, germ by germ

Let `X` be an algebraic space.  Say that the quasi-coherent `𝒪_X`-modules are *exhausted by their
finite type quasi-coherent submodules at the geometric points* if for every quasi-coherent `ℱ`,
every geometric point `x̄` of `X` and every germ `σ ∈ ℱ_x̄` there is a quasi-coherent submodule
`𝒦 ⊆ ℱ` of finite type with `σ ∈ 𝒦_x̄`.  This file proves:

* the affine case: an affine algebraic space has the property;
* the consequence used by the proof of Stacks 085M: if `X` has the property, then for every étale
  `g : Y ⟶ X` with `Y` quasi-compact and every submodule `𝒢 ⊆ ℱ|_Y` of finite type there is a
  quasi-coherent submodule `𝒦 ⊆ ℱ` of finite type with `𝒢 ⊆ 𝒦|_Y`.

The property is what the colimit assertion of Stacks 0829 says at the geometric points; it is
established for every quasi-compact and quasi-separated algebraic space in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubmoduleExhaustionQcqs`.

## Main definitions

* `AlgebraicGeometry.Space.FiniteTypeGermExhaustion`: the property.

## Main results

* `AlgebraicGeometry.Space.finiteTypeGermExhaustion_of_isAffineSpace`: the affine case.
* `AlgebraicGeometry.Space.exists_le_etaleSubmoduleRestrict_of_finiteTypeGermExhaustion`: the
  containment.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Sup

variable {X : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS X.1 X.2}

/-- The zero submodule is quasi-coherent of finite type. -/
theorem isQuasicoherentOnSite_isFiniteType_bot :
    (⊥ : M.Submodule).toSheafOfModules.IsQuasicoherentOnSite ∧
      (⊥ : M.Submodule).toSheafOfModules.IsFiniteType :=
  ⟨SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (SheafOfModules.Submodule.isZero_toSheafOfModules_bot M),
    Stacks.SheafOfModules.Site.isFiniteType_of_isZero
      (SheafOfModules.Submodule.isZero_toSheafOfModules_bot M)⟩

/-- Membership in a submodule is preserved by restriction along a composite, if it holds along the
second factor. -/
private theorem map_comp_mem_submodule {K : M.Submodule} {V Z W : (SmallEtale B S hS X.1)}
    (f : Z ⟶ V) (h : W ⟶ Z) {s : M.val.obj (op V)} (hs : M.val.map f.op s ∈ K.obj (op Z)) :
    M.val.map (h ≫ f).op s ∈ K.obj (op W) :=
  (PresheafOfModules.map_comp_apply M.val f.op h.op s).symm ▸ K.map_mem h.op hs

end Sup

/-- **Exhaustion of the quasi-coherent modules by their finite type quasi-coherent submodules, at
the geometric points.**  Every germ, at a geometric point, of a local section of a
quasi-coherent `𝒪_X`-module `ℱ` is the germ of a section of some quasi-coherent submodule of `ℱ`
of finite type. -/
def FiniteTypeGermExhaustion (X : AlgebraicSpaces B S hS) : Prop :=
  ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite →
    ∀ (x : GeometricPoint B S hS X.1) (V : SmallEtale B S hS X.1)
      (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj V) (s : F.val.obj (op V)),
      ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
        K.toSheafOfModules.IsFiniteType ∧
        (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber V p
          (etaleModuleSectionsPresheaf B S hS F) s ∈ submoduleGermSet B S hS K x

section Exhaustion

variable {B S hS} {X : AlgebraicSpaces B S hS}

/-- **Local exhaustion after an étale restriction.**  If `X` has
`AlgebraicGeometry.Space.FiniteTypeGermExhaustion` and `g : Y ⟶ X` is étale, every local section
of `ℱ|_Y` lies, along every arrow of some covering sieve, in the restriction of a quasi-coherent
submodule of `ℱ` of finite type. -/
theorem exists_sieve_of_finiteTypeGermExhaustion (hX : FiniteTypeGermExhaustion B S hS X)
    {F : Modules.{u, u} B S hS X.1 X.2} (hF : F.IsQuasicoherentOnSite)
    {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (V : SmallEtale B S hS Y.1)
    (s : ((etaleModulePullback.{u, u} B S hS g hg).obj F).val.obj (op V)) :
    ∃ T : Sieve V, T ∈ SmallEtale.topology B S hS Y.1 V ∧
      ∀ ⦃Z : SmallEtale B S hS Y.1⦄ (f : Z ⟶ V), T f →
        ∃ K : {K : F.Submodule // K.toSheafOfModules.IsQuasicoherentOnSite ∧
            K.toSheafOfModules.IsFiniteType},
          ((etaleModulePullback.{u, u} B S hS g hg).obj F).val.map f.op s ∈
            (etaleSubmoduleRestrict B S hS g hg K.1).obj (op Z) := by
  let Fg := (etaleModulePullback.{u, u} B S hS g hg).obj F
  let T : Sieve V :=
    { arrows := fun Z f => ∃ K : {K : F.Submodule // K.toSheafOfModules.IsQuasicoherentOnSite ∧
          K.toSheafOfModules.IsFiniteType},
        Fg.val.map f.op s ∈ (etaleSubmoduleRestrict B S hS g hg K.1).obj (op Z)
      downward_closed := by
        rintro Z W f ⟨K, hK⟩ h
        exact ⟨K, map_comp_mem_submodule B S hS f h hK⟩ }
  refine ⟨T, smallEtale_sieve_of_pointwise_covering B S hS Y.1 V T fun z => ?_, fun _ _ hf => hf⟩
  obtain ⟨y, p, z', hz'⟩ := exists_geo_lift_at_chart_point B S hS Y.1 V z
  let x : GeometricPoint B S hS X.1 := geometricPointMap g.hom y
  let t : GeometricPointLift B S hS g.hom x := ⟨y.val.value, rfl⟩
  let w : (liftSitePoint B S hS g t).fiber.obj V := p
  obtain ⟨K, hKq, hKf, hK⟩ := hX F hF x _ (pushLift B S hS g hg V t w) s
  rw [← etaleGermSet_etaleSubmoduleRestrict B S hS g hg K t,
    etaleGermSet_eq_image_submoduleGermSet] at hK
  obtain ⟨e', he', hee'⟩ := hK
  let ι := (restrictionPresheafFiberIso (A := Type u) B S hS g hg t).app
    (etaleModuleSectionsPresheaf B S hS F)
  have hι : ι.hom ((liftSitePoint B S hS g t).toPresheafFiber V w
      ((smallEtalePostcomp B S hS g hg).op ⋙ etaleModuleSectionsPresheaf B S hS F) s) =
        (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber _ (pushLift B S hS g hg V t w)
          (etaleModuleSectionsPresheaf B S hS F) s :=
    ConcreteCategory.congr_hom (restrictionPresheafFiberIso_toPresheafFiber (A := Type u)
      B S hS g hg t (etaleModuleSectionsPresheaf B S hS F) V w) s
  have he : e' = (liftSitePoint B S hS g t).toPresheafFiber V w
      ((smallEtalePostcomp B S hS g hg).op ⋙ etaleModuleSectionsPresheaf B S hS F) s :=
    (ConcreteCategory.bijective_of_isIso ι.hom).1 (hee'.trans hι.symm)
  rw [he] at he'
  obtain ⟨V', ψ, p', hp', hmem⟩ := exists_map_mem_of_toPresheafFiber_mem_submoduleGermSet B S hS
    (etaleSubmoduleRestrict B S hS g hg K) p s he'
  refine ⟨V', ψ, ⟨⟨K, hKq, hKf⟩, hmem⟩, (BigFppfOver.toScheme B S hS).map p'.1 z', ?_⟩
  rw [← hz', ← hp']
  change _ = (BigFppfOver.toScheme B S hS).map (p'.1 ≫ (SmallEtale.toOver B S hS Y.1).map ψ) z'
  rw [Functor.map_comp]
  rfl

/-- **A finite type submodule after an étale restriction lies in the restriction of a finite type
quasi-coherent submodule.**  If `X` has `AlgebraicGeometry.Space.FiniteTypeGermExhaustion`,
`g : Y ⟶ X` is étale with `Y` quasi-compact and `𝒢 ⊆ ℱ|_Y` is of finite type, there is a
quasi-coherent submodule `𝒦 ⊆ ℱ` of finite type with `𝒢 ⊆ 𝒦|_Y`. -/
theorem exists_le_etaleSubmoduleRestrict_of_finiteTypeGermExhaustion
    (hX : FiniteTypeGermExhaustion B S hS X)
    {F : Modules.{u, u} B S hS X.1 X.2} (hF : F.IsQuasicoherentOnSite)
    {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (G : ((etaleModulePullback.{u, u} B S hS g hg).obj F).Submodule)
    (hGf : G.toSheafOfModules.IsFiniteType) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧ G ≤ etaleSubmoduleRestrict B S hS g hg K := by
  let ι := {K : F.Submodule // K.toSheafOfModules.IsQuasicoherentOnSite ∧
    K.toSheafOfModules.IsFiniteType}
  have : Nonempty ι := ⟨⟨⊥, isQuasicoherentOnSite_isFiniteType_bot B S hS⟩⟩
  obtain ⟨K, hK⟩ := exists_le_of_isFiniteType_of_isQuasiCompactSpace B S hS hYqc
    (fun K : ι => etaleSubmoduleRestrict B S hS g hg K.1)
    (fun K₁ K₂ => ⟨⟨K₁.1 ⊔ K₂.1, isQuasicoherentOnSite_isFiniteType_sup B S hS hF _ _ K₁.2 K₂.2⟩,
      etaleSubmoduleRestrict_mono B S hS g hg le_sup_left,
      etaleSubmoduleRestrict_mono B S hS g hg le_sup_right⟩)
    (fun V x => exists_sieve_of_finiteTypeGermExhaustion hX hF g hg V x) G hGf
  exact ⟨K.1, K.2.1, K.2.2, hK⟩

/-- **The affine case.**  On an affine algebraic space every germ of a local section of a
quasi-coherent module is the germ of a section of a quasi-coherent submodule of finite type.

Over an affine chart, the sections are the base change of the sections over the terminal chart,
by Descent, Proposition 03DX(2); a section over the terminal chart generates a quasi-coherent
submodule of finite type, the image of the corresponding morphism `𝒪_X ⟶ ℱ`; and a finite sum
of sections of such submodules lies in their supremum, again quasi-coherent of finite type.
Affine charts cover every chart. -/
theorem finiteTypeGermExhaustion_of_isAffineSpace (hXa : IsAffineSpace B S hS X.1) :
    FiniteTypeGermExhaustion B S hS X := by
  classical
  intro F hF x V p s
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := hXa
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 F hF
  have : F.IsQuasicoherentOnSite := hF
  let : Abelian (Modules.{u, u} B S hS X.1 X.2) :=
    SheafOfModules.instAbelian.{u, u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  let Good : ∀ W : SmallEtale B S hS X.1, F.val.obj (op W) → Prop := fun W y =>
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧ y ∈ K.obj (op W)
  have hgen : ∀ (W : SmallEtale B S hS X.1) (n : F.val.obj (op (invIsoChart B S hS e))),
      Good W (F.val.map (toIsoChart B S hS e W).op n) := by
    intro W n
    let u := isoChartSectionHom B S hS X.2 e F n
    let I := imageSubobject u
    obtain ⟨hIq, hIf⟩ := imageSubobject_unit_mem B S hS X.2 F u
    change ∃ K : F.Submodule, _
    let t := Stacks.SheafOfModules.monoRangeIso I.arrow inferInstance
    have : Epi t.hom := @IsIso.epi_of_iso _ _ _ _ t.hom (Iso.isIso_hom t)
    refine ⟨Stacks.SheafOfModules.monoRange I.arrow inferInstance,
      SheafOfModules.IsQuasicoherentOnSite.of_iso t hIq,
      Stacks.SheafOfModules.isFiniteType_of_epi t.hom hIf,
      ⟨(factorThruImageSubobject u).val.app (op W)
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op W)), ?_⟩⟩
    rw [← isoChartSectionHom_app_one B S hS X.2 e F n W]
    exact congrArg (fun φ : _ ⟶ F => (φ.val.app (op W)).hom _) (imageSubobject_arrow_comp u)
  have hzero : ∀ W : SmallEtale B S hS X.1, Good W 0 := fun W =>
    ⟨⊥, (isQuasicoherentOnSite_isFiniteType_bot B S hS).1,
      (isQuasicoherentOnSite_isFiniteType_bot B S hS).2, Submodule.zero_mem _⟩
  have hadd : ∀ (W : SmallEtale B S hS X.1) (y y' : F.val.obj (op W)), Good W y → Good W y' →
      Good W (y + y') := by
    rintro W y y' ⟨K, hKq, hKf, hK⟩ ⟨K', hK'q, hK'f, hK'⟩
    obtain ⟨hq, hf⟩ := isQuasicoherentOnSite_isFiniteType_sup B S hS hF K K' ⟨hKq, hKf⟩
      ⟨hK'q, hK'f⟩
    exact ⟨K ⊔ K', hq, hf, Submodule.add_mem _
      (SheafOfModules.Submodule.le_iff.1 le_sup_left _ hK)
      (SheafOfModules.Submodule.le_iff.1 le_sup_right _ hK')⟩
  have key : ∀ O : ULift.{u + 1} ((chartScheme V).affineOpens),
      Good (openChart B S hS X.1 V O.down.1)
        (F.val.map (openChartInclusion B S hS X.1 V O.down.1).op s) := by
    intro O
    have hW'aff := isAffine_chartScheme_openChart B S hS X.1 V O.down
    let f := toIsoChart B S hS e (openChart B S hS X.1 V O.down.1)
    obtain ⟨y, hy⟩ := (hcart _ _ (isAffine_isoChart B S hS e hT₀) hW'aff f).2
      (F.val.map (openChartInclusion B S hS X.1 V O.down.1).op s)
    rw [← hy]
    clear hy
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact hzero _
    | tmul b n =>
        obtain ⟨K, hKq, hKf, hK⟩ := hgen (openChart B S hS X.1 V O.down.1) n
        rw [chartBaseChange_tmul]
        exact ⟨K, hKq, hKf, Submodule.smul_mem _ b hK⟩
    | add a c ha hc => rw [map_add]; exact hadd _ _ _ ha hc
  obtain ⟨V₁, g, hg, p₁, rfl⟩ := (etaleSitePoint B S hS X.1 x X.2).jointly_surjective _
    (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS X.1 V) p
  obtain ⟨O, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  obtain ⟨K, hKq, hKf, hK⟩ := key O
  refine ⟨K, hKq, hKf, V₁, p₁, F.val.map (a ≫ openChartInclusion B S hS X.1 V O.down.1).op s,
    ?_, ?_⟩
  · exact map_comp_mem_submodule B S hS _ a hK
  · exact (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_w_apply _ p₁
      (etaleModuleSectionsPresheaf B S hS F) s

end Exhaustion

end AlgebraicGeometry.Space

end
