/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorSurjection
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSubfunctorRepresentedProper
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# `Quot^P` along a surjection of modules

Let `φ : F ⟶ G` be a surjection of quasi-coherent `𝒪_X`-modules.  Stacks 0DP5 gives a closed
immersion `Quot_{G/X/B} ⟶ Quot_{F/X/B}`, sending `G_T ⟶ 𝒬` to `F_T ⟶ G_T ⟶ 𝒬`.  The quotient
module is unchanged, so the twisted Euler characteristics are too, and the closed immersion
restricts to `Quot^{P, L}_{G/X/B} ⟶ Quot^{P, L}_{F/X/B}` with `Quot^{P, L}_{G/X/B}` the inverse
image of `Quot^{P, L}_{F/X/B}`.  Hence if `Quot^{P, L}_{F/X/B}` is represented by a scheme `Z`
proper over `B`, then `Quot^{P, L}_{G/X/B}` is represented by the closed subscheme of `Z` over
which the universal quotient comes from `G`, again proper over `B`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.quotSiteInclusion`: the inclusion
  `Quot_{G/X/B} ⟶ Quot_{F/X/B}` on the schemes of the site.
* `AlgebraicGeometry.Space.QuotSituation.mem_hilbertPolynomialQuot_withModule_iff`: a quotient
  of `G_T` has Hilbert polynomial `P` exactly when its image in `Quot_{F/X/B}` has.
* `AlgebraicGeometry.Space.QuotSituation.exists_siteImageLocus_quotSiteInclusion`: the image locus
  of Stacks 0DP5, on the schemes of the site.
* `AlgebraicGeometry.Space.QuotSituation.isRepresentedProper_hilbertPolynomialQuot_withModule`: if
  `Quot^{P, L}_{F/X/B}` is represented by a scheme proper over `B`, so is `Quot^{P, L}_{G/X/B}`.

## References

* [Stacks Project, Tag 0DP5](https://stacks.math.columbia.edu/tag/0DP5)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)
  {G : Modules.{u, u} B S hS D.X.1 D.X.2} {hG : G.IsQuasicoherentOnSite} (φ : D.F ⟶ G) [Epi φ]

/-- The quotient `F_T ⟶ G_T ⟶ 𝒬` over `T ⟶ B` induced by a quotient `G_T ⟶ 𝒬` over `T ⟶ B`. -/
def inclusionFamily {T : BigFppfOver B S hS} (x : QuotFamilyOver (D.withModule G hG) T) :
    QuotFamilyOver D T where
  toBase := x.toBase
  subobject := D.quotientSubobject φ (CostructuredArrow.mk x.toBase) x.subobject
  mem := D.quotientSubobject_mem φ x.mem

/-- The induced quotient commutes with base change along schemes of the site. -/
theorem inclusionFamily_baseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : QuotFamilyOver (D.withModule G hG) T) :
    D.inclusionFamily φ (x.baseChange g) = (D.inclusionFamily φ x).baseChange g := by
  refine QuotFamilyOver.ext rfl (heq_of_eq ?_)
  dsimp only [inclusionFamily, QuotFamilyOver.baseChange]
  exact (D.quotientPullback_quotientSubobject (hG := hG) φ
    (QuotFamilyOver.restrict (D := D) g x.toBase) x.subobject).symm

/-- **The inclusion `Quot_{G/X/B} ⟶ Quot_{F/X/B}` of Stacks 0DP5 on the schemes of the site**: a
quotient `G_T ⟶ 𝒬` over `T ⟶ B` goes to the quotient `F_T ⟶ G_T ⟶ 𝒬` over the same `T ⟶ B`. -/
def quotSiteInclusion : (D.withModule G hG).quotSitePresheaf ⟶ D.quotSitePresheaf where
  app T := TypeCat.ofHom fun (x : QuotFamilyOver (D.withModule G hG) T.unop) =>
    (D.inclusionFamily (hG := hG) φ x : QuotFamilyOver D T.unop)
  naturality _ _ g :=
    ConcreteCategory.hom_ext _ _ fun x => D.inclusionFamily_baseChange φ g.unop x

/-- The inclusion `quotSiteInclusion` does not change the structure morphism `T ⟶ B`. -/
theorem quotSiteInclusion_app_toBase (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (D.withModule G hG).quotSitePresheaf.obj T) :
    ((D.quotSiteInclusion φ).app T x).toBase = x.toBase :=
  rfl

/-- The induced quotient determines the quotient of `G_T`, `φ` being an epimorphism. -/
theorem inclusionFamily_injective (T : BigFppfOver B S hS) :
    Function.Injective (D.inclusionFamily (hG := hG) (T := T) φ) := by
  intro x y h
  have hb : x.toBase = y.toBase := congrArg (QuotFamilyOver.toBase (D := D)) h
  have hsub := congr_arg_heq (QuotFamilyOver.subobject (D := D)) h
  refine QuotFamilyOver.ext hb ?_
  obtain ⟨b, K, hK⟩ := x
  obtain ⟨b', K', hK'⟩ := y
  dsimp only at hb
  subst hb
  dsimp only [inclusionFamily] at hsub
  cases D.quotientSubobject_injective φ _ (eq_of_heq hsub)
  rfl

/-- The inclusion is injective, `φ` being an epimorphism. -/
theorem quotSiteInclusion_injective (T : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Injective ((D.quotSiteInclusion (hG := hG) φ).app T) :=
  D.inclusionFamily_injective φ T.unop

section HilbertPolynomial

/-- The object `(T, G_T/K)` of `Coh_{X/B}` attached to a quotient of `G_T`, read in `Coh_{X/B}` of
the situation of `F`: the two situations have the same morphism `X ⟶ B`. -/
def withModuleCohObject {T : BigFppfOver B S hS} (x : QuotFamilyOver (D.withModule G hG) T) :
    CoherentObject D.toCoherentSituation where
  T := CostructuredArrow.mk x.toBase
  F := (D.withModule G hG).quotientModule (CostructuredArrow.mk x.toBase) x.subobject
  quasicoherent := x.mem.1.1.1
  finitePresentation := x.mem.1.2
  flat := x.mem.1.1.2
  properSupport := ⟨D.isLocallyOfFiniteType_projection _, x.mem.2.1, x.mem.2.2⟩

/-- The objects of `Coh_{X/B}` attached to the induced quotient of `F_T` and to the quotient of
`G_T` are isomorphic over the identity of the test scheme. -/
def inclusionFamilyCohHom {T : BigFppfOver B S hS} (x : QuotFamilyOver (D.withModule G hG) T) :
    CoherentHom (D.inclusionFamily φ x).cohObject (D.withModuleCohObject x) where
  base := 𝟙 _
  fibre := ((D.toCoherentSituation.idComparison (modulePushforwardCoherence B S hS)
      (CostructuredArrow.mk x.toBase)).app (D.withModuleCohObject x).F ≪≫
    (D.quotientSubobjectIso φ (CostructuredArrow.mk x.toBase) x.subobject).symm).hom
  isIso_fibre := Iso.isIso_hom _

variable (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]

/-- **The induced quotient has the same twisted Euler characteristics** as the quotient of
`G_T`. -/
theorem twistedEuler_inclusionFamily {T : BigFppfOver B S hS}
    (x : QuotFamilyOver (D.withModule G hG) T) (t : (BigFppfOver.toScheme B S hS).obj T) (n : ℤ) :
    @CoherentObject.twistedEuler B S hS D.toCoherentSituation L hL
        (D.inclusionFamily φ x).cohObject t n =
      @CoherentObject.twistedEuler B S hS D.toCoherentSituation L hL
        (D.withModuleCohObject x) t n := by
  have : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS D.toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
  exact CoherentHom.twistedEuler_eq (A := (D.inclusionFamily φ x).cohObject)
    (A' := D.withModuleCohObject x) L (D.inclusionFamilyCohHom φ x) t n

variable (P : ℤ → ℤ)

/-- **Membership in `Quot^P` is read on the induced quotient.** -/
theorem mem_hilbertPolynomialQuot_withModule_iff {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : (D.withModule G hG).quotSitePresheaf.obj T) :
    x ∈ ((D.withModule G hG).hilbertPolynomialQuot L P).obj T ↔
      (D.quotSiteInclusion φ).app T x ∈ (D.hilbertPolynomialQuot L P).obj T := by
  rw [mem_hilbertPolynomialQuot_iff, mem_hilbertPolynomialQuot_iff]
  change (∀ (t : (BigFppfOver.toScheme B S hS).obj T.unop) (n : ℤ),
      P n = @CoherentObject.twistedEuler B S hS D.toCoherentSituation L hL
        (D.withModuleCohObject (T := T.unop) x) t n) ↔
    ∀ (t : (BigFppfOver.toScheme B S hS).obj T.unop) (n : ℤ),
      P n = @CoherentObject.twistedEuler B S hS D.toCoherentSituation L hL
        (D.inclusionFamily φ x).cohObject t n
  exact forall_congr' fun t => forall_congr' fun n => by
    rw [D.twistedEuler_inclusionFamily φ L x t n]

end HilbertPolynomial

/-- **The image locus of `Quot_{G/X/B} ⟶ Quot_{F/X/B}` on the schemes of the site** (Stacks 0DP5):
for a quotient `y` over a scheme `T` of the site, the morphisms `t : T' ⟶ T` along which the
pullback of `y` comes from `Quot_{G/X/B}` are those factoring through a fixed closed immersion
`T₀ ⟶ T`. -/
theorem exists_siteImageLocus_quotSiteInclusion (T : BigFppfOver B S hS)
    (y : D.quotSitePresheaf.obj (Opposite.op T)) :
    ∃ (T₀ : BigFppfOver B S hS) (s : T₀ ⟶ T),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s) ∧
      ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T),
        (∃ x : (D.withModule G hG).quotSitePresheaf.obj (Opposite.op T'),
            (D.quotSiteInclusion φ).app (Opposite.op T') x = D.quotSitePresheaf.map t.op y) ↔
          ∃ r : T' ⟶ T₀, r ≫ s = t := by
  obtain ⟨b, s, -, hs, hloc⟩ := D.exists_imageLocus_quotientInclusion (hG := hG) φ
    (CostructuredArrow.mk y.toBase) ⟨y.subobject, y.mem⟩
  refine ⟨b.left, s.left, hs, fun T' t => ?_⟩
  have key := hloc (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ y.toBase))
    (QuotFamilyOver.restrict t y.toBase)
  constructor
  · rintro ⟨⟨xb, xK, xm⟩, hx⟩
    have hb : xb = (schemeSpaceFunctor B S hS).map t ≫ y.toBase :=
      congrArg (QuotFamilyOver.toBase (D := D)) hx
    subst hb
    have hsub := congr_arg_heq (QuotFamilyOver.subobject (D := D)) hx
    dsimp only [inclusionFamily] at hsub
    obtain ⟨r, hr⟩ := key.1 ⟨⟨xK, xm⟩, Subtype.ext (eq_of_heq hsub)⟩
    exact ⟨r.left, congrArg CommaMorphism.left hr⟩
  · rintro ⟨r₀, hr₀⟩
    have hw : (schemeSpaceFunctor B S hS).map r₀ ≫ b.hom =
        (schemeSpaceFunctor B S hS).map t ≫ y.toBase := by
      rw [← CostructuredArrow.w s, ← Category.assoc, ← Functor.map_comp, hr₀]
      rfl
    obtain ⟨⟨K', hK'⟩, hx⟩ := key.2
      ⟨CostructuredArrow.homMk r₀ hw, CostructuredArrow.hom_ext _ _ hr₀⟩
    exact ⟨⟨_, K', hK'⟩, QuotFamilyOver.ext rfl (heq_of_eq (congrArg Subtype.val hx))⟩

/-- The inclusion commutes with the restriction maps. -/
theorem quotSiteInclusion_map {T T' : (BigFppfOver B S hS)ᵒᵖ} (g : T ⟶ T')
    (x : (D.withModule G hG).quotSitePresheaf.obj T) :
    (D.quotSiteInclusion φ).app T' ((D.withModule G hG).quotSitePresheaf.map g x) =
      D.quotSitePresheaf.map g ((D.quotSiteInclusion φ).app T x) :=
  types_congr_hom ((D.quotSiteInclusion φ).naturality g) x

include φ in
/-- **Stacks 0DP5 on `Quot^P`, in terms of representability by proper schemes.**  For a
surjection `φ : F ⟶ G` of quasi-coherent `𝒪_X`-modules, an invertible `L` and `P : ℤ → ℤ`: if
`Quot^{P, L}_{F/X/B}` is represented by a scheme proper over `B`, so is `Quot^{P, L}_{G/X/B}`,
by a closed subscheme of it (the image locus of `Quot_{G/X/B} ⟶ Quot_{F/X/B}`). -/
theorem isRepresentedProper_hilbertPolynomialQuot_withModule_of_epi
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ) (h : D.IsRepresentedProper (D.hilbertPolynomialQuot L P)) :
    (D.withModule G hG).IsRepresentedProper ((D.withModule G hG).hilbertPolynomialQuot L P) := by
  obtain ⟨Z, e, q, he, hq⟩ := h
  let ι := D.quotSiteInclusion (hG := hG) φ
  let u : (D.hilbertPolynomialQuot L P).toFunctor.obj (Opposite.op Z) :=
    e.hom.app (Opposite.op Z) ⟨𝟙 Z⟩
  let y : D.quotSitePresheaf.obj (Opposite.op Z) := u.1
  have e_nat : ∀ {T : BigFppfOver B S hS} (g : T ⟶ Z),
      (e.hom.app (Opposite.op T) ⟨g⟩).1 = D.quotSitePresheaf.map g.op y := by
    intro T g
    have := types_congr_hom (e.hom.naturality g.op) (⟨𝟙 Z⟩ : ULift.{u + 1} (Z ⟶ Z))
    have h1 : (yoneda.obj Z ⋙ uliftFunctor.{u + 1, u}).map g.op ⟨𝟙 Z⟩ = ⟨g⟩ :=
      congrArg ULift.up (Category.comp_id g)
    exact (congrArg (fun w => (e.hom.app (Opposite.op T) w).1) h1.symm).trans
      (congrArg Subtype.val this)
  have e_toBase : ∀ {T : BigFppfOver B S hS} (g : T ⟶ Z),
      yonedaEquiv (D.quotSitePresheaf.map g.op y).toBase.hom = q.app (Opposite.op T) g := by
    intro T g
    rw [← e_nat g]
    exact congrArg ULift.down
      (types_congr_hom (congrArg (fun k => k.app (Opposite.op T)) he) ⟨g⟩)
  obtain ⟨T₀, s, hs, hloc⟩ := D.exists_siteImageLocus_quotSiteInclusion (hG := hG) φ Z y
  have hsmono : Mono s := mono_of_isClosedImmersion_toScheme_map s hs
  obtain ⟨x₀, hx₀⟩ := (hloc T₀ s).2 ⟨𝟙 _, Category.id_comp s⟩
  have hymem : ∀ {T : BigFppfOver B S hS} (g : T ⟶ Z),
      D.quotSitePresheaf.map g.op y ∈ (D.hilbertPolynomialQuot L P).obj (Opposite.op T) := by
    intro T g
    exact e_nat g ▸ (e.hom.app (Opposite.op T) ⟨g⟩).2
  have hx₀mem : x₀ ∈ ((D.withModule G hG).hilbertPolynomialQuot L P).obj (Opposite.op T₀) := by
    rw [D.mem_hilbertPolynomialQuot_withModule_iff φ L P x₀]
    change ι.app _ x₀ ∈ _
    rw [hx₀]
    exact hymem s
  have hιmap : ∀ {T : BigFppfOver B S hS} (g : T ⟶ T₀),
      ι.app (Opposite.op T) ((D.withModule G hG).quotSitePresheaf.map g.op x₀) =
        D.quotSitePresheaf.map (g ≫ s).op y := by
    intro T g
    rw [D.quotSiteInclusion_map φ g.op x₀]
    change D.quotSitePresheaf.map g.op (ι.app _ x₀) = _
    rw [hx₀, op_comp, Functor.map_comp_apply]
  let f : ∀ T : (BigFppfOver B S hS)ᵒᵖ,
      (yoneda.obj T₀ ⋙ uliftFunctor.{u + 1, u}).obj T →
        ((D.withModule G hG).hilbertPolynomialQuot L P).toFunctor.obj T := fun T g =>
    ⟨(D.withModule G hG).quotSitePresheaf.map g.down.op x₀,
      ((D.withModule G hG).hilbertPolynomialQuot L P).map g.down.op hx₀mem⟩
  have hbij : ∀ T, Function.Bijective (f T) := by
    intro T
    constructor
    · rintro ⟨g⟩ ⟨g'⟩ hgg
      have h1 := congrArg (fun w => ι.app T w.1) hgg
      simp only [f, hιmap] at h1
      have h2 : e.hom.app T ⟨g ≫ s⟩ = e.hom.app T ⟨g' ≫ s⟩ :=
        Subtype.ext ((e_nat (g ≫ s)).trans (h1.trans (e_nat (g' ≫ s)).symm))
      have h3 := congrArg ULift.down ((asIso (e.hom.app T)).toEquiv.injective h2)
      exact congrArg ULift.up (hsmono.right_cancellation _ _ h3)
    · rintro ⟨w, hw⟩
      have hιw : ι.app T w ∈ (D.hilbertPolynomialQuot L P).obj T :=
        (D.mem_hilbertPolynomialQuot_withModule_iff φ L P w).1 hw
      let g : T.unop ⟶ Z := (e.inv.app T ⟨ι.app T w, hιw⟩).down
      have hg : D.quotSitePresheaf.map g.op y = ι.app T w := by
        rw [← e_nat g]
        exact congrArg Subtype.val (types_congr_hom (e.inv_hom_id_app T) ⟨ι.app T w, hιw⟩)
      obtain ⟨r, hr⟩ := (hloc T.unop g).1 ⟨w, hg.symm⟩
      refine ⟨⟨r⟩, Subtype.ext ?_⟩
      apply D.quotSiteInclusion_injective (hG := hG) φ T
      refine (hιmap r).trans ?_
      rwa [hr]
  let e₀ : yoneda.obj T₀ ⋙ uliftFunctor.{u + 1, u} ≅
      ((D.withModule G hG).hilbertPolynomialQuot L P).toFunctor :=
    NatIso.ofComponents (fun T => Equiv.toIso (Equiv.ofBijective (f T) (hbij T))) (by
      intro T T' k
      ext ⟨g⟩
      refine Subtype.ext ?_
      change (D.withModule G hG).quotSitePresheaf.map (k.unop ≫ g).op x₀ =
        (D.withModule G hG).quotSitePresheaf.map k
          ((D.withModule G hG).quotSitePresheaf.map g.op x₀)
      rw [op_comp, Functor.map_comp_apply]
      rfl)
  have hsi : IsClosedImmersion B S hS (yoneda.map s) :=
    (presheaf_yoneda_map_iff B S hS inferInstance s).2 hs
  refine ⟨T₀, e₀, yoneda.map s ≫ q, ?_, isProper_comp' B S hS _ _
    (isAlgebraicSpace_yoneda B S hS Z) D.Y.2
    (isProper_of_isClosedImmersion B S hS (isAlgebraicSpace_yoneda B S hS T₀)
      (isAlgebraicSpace_yoneda B S hS Z) _ hsi) hq⟩
  ext T ⟨g⟩
  change ULift.up (yonedaEquiv ((D.withModule G hG).quotSitePresheaf.map g.op x₀).toBase.hom) =
    ULift.up ((yoneda.map s ≫ q).app T g)
  congr 1
  rw [← D.quotSiteInclusion_app_toBase φ, hιmap g]
  exact e_toBase (g ≫ s)

/-- **Stacks 0DP5 on `Quot^P`, in terms of representability by proper schemes**: for a
surjection `φ : F ⟶ G` of quasi-coherent `𝒪_X`-modules, if `Quot^{P, L}_{F/X/B}` is represented
by a scheme proper over `B`, so is `Quot^{P, L}_{G/X/B}`. -/
theorem isRepresentedProper_hilbertPolynomialQuot_withModule (D : QuotSituation B S hS)
    {G : Modules.{u, u} B S hS D.X.1 D.X.2} (hG : G.IsQuasicoherentOnSite) (φ : D.F ⟶ G)
    [Epi φ] (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ) (h : D.IsRepresentedProper (D.hilbertPolynomialQuot L P)) :
    (D.withModule G hG).IsRepresentedProper ((D.withModule G hG).hilbertPolynomialQuot L P) :=
  D.isRepresentedProper_hilbertPolynomialQuot_withModule_of_epi (hG := hG) φ L P h

end AlgebraicGeometry.Space.QuotSituation

end
