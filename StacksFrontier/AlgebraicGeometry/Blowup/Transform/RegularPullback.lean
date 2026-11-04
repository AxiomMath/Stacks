module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.AffineCharts
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Pullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of divisors and of meromorphic functions along a blowup

Let `b : X' ⟶ X` be the blowup of a scheme in a quasi-coherent ideal. Although `b` need not be
flat, it is "nowhere degenerate" enough that nonzerodivisors pull back to nonzerodivisors: on
each standard affine chart `Spec Γ(X, U)[I(U)/a]` of the blowup the structure map is a
localization followed by an inclusion of a subring, both of which preserve nonzerodivisors.
Consequently every effective Cartier divisor on `X` has a defined pullback and pullbacks of
meromorphic functions are defined for `b`.

## Main results

* `AlgebraicGeometry.isSMulRegular_of_forall_germ`: a section of the structure sheaf whose
  germs are all nonzerodivisors is a nonzerodivisor.
* `AlgebraicGeometry.isSMulRegular_germ_blowUpToBase_app`: the germs of the pullback of a
  nonzerodivisor along a blowup morphism are nonzerodivisors.
* `AlgebraicGeometry.isPullbackDefined_blowUpToBase`: **Stacks Tag 0809**, effective Cartier
  divisors.
* `AlgebraicGeometry.pullbacksMeromorphicSections_blowUpToBase`: **Stacks Tag 0809**,
  meromorphic functions.

## Implementation notes

Both conclusions are reduced to one statement about germs,
`AlgebraicGeometry.isSMulRegular_germ_blowUpToBase_app`, which is checked on the affine charts
of Stacks tag 0804 (`AlgebraicGeometry.affineBlowupStandardOpenIso`,
`AlgebraicGeometry.blownUpAffine_chart_cover`): the chart's structure morphism to the base is
`Spec` of the canonical map `Γ(X, U) → Γ(X, U)[I(U)/a]`
(`AlgebraicGeometry.affineBlowupStandardOpenIso_over`), and that map factors through the
localization at `a`, so it preserves nonzerodivisors.

For the divisor statement the affine-local criterion of Stacks tag 01WS
(`Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal`) turns the problem into producing
a local equation for the inverse image, which is the image of a local equation downstairs; for
the meromorphic statement the affine criterion of Stacks tag 02OU
(`AlgebraicGeometry.pullbacksMeromorphicSections_of_affine`) does the same.

## References

* [Stacks Project, Tag 0809](https://stacks.math.columbia.edu/tag/0809)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- A nonzerodivisor of the base stays a nonzerodivisor in an affine blowup algebra: the
structure map factors through the localization at the chosen generator, and the blowup algebra
is a subring of that localization. -/
private theorem isSMulRegular_algebraMap_affineBlowupAlgebra {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (a : R) [IsLocalization.Away a S] (J : Ideal R) {t : R}
    (ht : IsSMulRegular R t) :
    IsSMulRegular (affineBlowupAlgebra J a S) (algebraMap R (affineBlowupAlgebra J a S) t) := by
  have hs : IsSMulRegular S (algebraMap R S t) :=
    IsSMulRegular.of_isLocalization (R := R) S (Submonoid.powers a) ht
  refine IsSMulRegular.of_right_eq_zero_of_smul fun z hz ↦ ?_
  refine Subtype.ext (hs.right_eq_zero_of_smul ?_)
  simpa [Algebra.smul_def] using congrArg (fun w : affineBlowupAlgebra J a S ↦ (w : S)) hz

/-- A section of the structure sheaf of a scheme over an open `U` is a nonzerodivisor as soon
as all of its germs at points of `U` are. -/
theorem isSMulRegular_of_forall_germ {X : Scheme.{u}} (U : X.Opens) (s : Γ(X, U))
    (hs : ∀ (x : X) (hx : x ∈ U),
      IsSMulRegular (X.presheaf.stalk x) (X.presheaf.germ U x hx s)) :
    IsSMulRegular Γ(X, U) s := by
  refine IsSMulRegular.of_right_eq_zero_of_smul fun z hz ↦ ?_
  refine TopCat.Presheaf.section_ext
    (⟨X.presheaf, X.IsSheaf⟩ : TopCat.Sheaf CommRingCat.{u} X.toTopCat) U z 0 fun x hx ↦ ?_
  have he : X.presheaf.germ U x hx s * X.presheaf.germ U x hx z = 0 := by
    simpa only [smul_eq_mul, map_mul, map_zero] using congrArg (X.presheaf.germ U x hx) hz
  simpa using (hs x hx).right_eq_zero_of_smul (by simpa [Algebra.smul_def] using he)

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Every point of the blowup over an affine open `U` of the base lies on one of the standard
charts of Stacks tag 0804 attached to a section of `I(U)`. -/
private theorem exists_affineBlowupChart_point (V : X.affineOpens) (x : blowUp I)
    (hx : x ∈ (blowUpToBase I ⁻¹ᵁ V.1)) :
    letI := (reesSituation I).sectionRingGradedRing V.1
    letI := (reesSituation I).sectionRingGradingGradedRing V.1
    ∃ (a : I.ideal V) (q : (Proj.basicOpen ((reesSituation I).sectionRingGrading V.1)
        (reesDegreeOne I V a).1).toScheme),
      ((Proj.basicOpen ((reesSituation I).sectionRingGrading V.1)
        (reesDegreeOne I V a).1).ι ≫
        Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) V) q = x := by
  let := (reesSituation I).sectionRingGradedRing V.1
  let := (reesSituation I).sectionRingGradingGradedRing V.1
  have hx' : x ∈ (⋃ a : I.ideal V,
      Set.range ((Proj.basicOpen ((reesSituation I).sectionRingGrading V.1)
        (reesDegreeOne I V a).1).ι ≫
        Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) V)) := by
    rw [blownUpAffine_chart_cover]
    exact hx
  obtain ⟨a, q, hq⟩ := Set.mem_iUnion.mp hx'
  exact ⟨a, q, hq⟩

/-- The composite of a standard affine chart of the blowup with the blowup morphism is `Spec`
of the canonical map from `Γ(X, U)` into the affine blowup algebra, followed by the inclusion
of the affine open. -/
private theorem affineBlowupChart_comp_blowUpToBase (V : X.affineOpens) (a : I.ideal V) :
    letI := (reesSituation I).sectionRingGradedRing V.1
    letI := (reesSituation I).sectionRingGradingGradedRing V.1
    (affineBlowupStandardOpenIso I V a).hom ≫
        (Proj.basicOpen ((reesSituation I).sectionRingGrading V.1)
          (reesDegreeOne I V a).1).ι ≫
        Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) V ≫
        blowUpToBase I =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (.op V.1))
        (affineBlowupAlgebra (I.ideal V) (a : X.presheaf.obj (.op V.1))
          (Localization.Away (a : X.presheaf.obj (.op V.1)))))) ≫
        V.2.isoSpec.inv ≫ V.1.ι := by
  let := (reesSituation I).sectionRingGradedRing V.1
  let := (reesSituation I).sectionRingGradingGradedRing V.1
  rw [(Stacks.RelativeProj.Situation.relativeProjChart_isPullback (reesSituation I) V).w]
  exact congrArg (fun k ↦ k ≫ V.1.ι) (affineBlowupStandardOpenIso_over I V a)

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- Transport of a section along `Spec` of a ring map into an affine open: the global section of
`Spec B` obtained by pulling back `s ∈ Γ(X, U)` along `Spec φ` followed by the identification of
`U` with `Spec Γ(X, U)` is the image of `s` under `φ`. -/
private theorem appTop_specMap_comp_isoSpec_inv {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {B : CommRingCat.{u}} (φ : CommRingCat.of Γ(X, U) ⟶ B) (s : Γ(X, U)) :
    (Spec.map φ ≫ hU.isoSpec.inv).appTop (U.topIso.inv s) = (Scheme.ΓSpecIso B).inv (φ s) := by
  show ((Spec.map φ ≫ hU.isoSpec.inv).app ⊤) (U.topIso.inv s) = _
  rw [Scheme.Hom.comp_app]
  show (hU.isoSpec.inv.appTop ≫ (Spec.map φ).appTop) (U.topIso.inv s) = _
  rw [hU.isoSpec_inv_appTop]
  have hnat : φ ≫ (Scheme.ΓSpecIso B).inv =
      (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv ≫ (Spec.map φ).appTop :=
    Scheme.SpecΓIdentity.inv.naturality φ
  show (U.topIso.hom ≫ ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv ≫
    (Spec.map φ).appTop)) (U.topIso.inv s) = (Scheme.ΓSpecIso B).inv (φ s)
  rw [← hnat]
  show (Scheme.ΓSpecIso B).inv (φ (U.topIso.hom (U.topIso.inv s))) =
    (Scheme.ΓSpecIso B).inv (φ s)
  rw [U.topIso.inv_hom_id_apply]

/-- If a ring map carries a section of the structure sheaf on an affine open to a
nonzerodivisor, then the pulled-back global section on `Spec` of the target is a
nonzerodivisor. -/
private theorem isSMulRegular_appTop_specMap_comp_isoSpec_inv {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {B : CommRingCat.{u}} (φ : CommRingCat.of Γ(X, U) ⟶ B) (s : Γ(X, U))
    (hs : IsSMulRegular B (φ s)) :
    IsSMulRegular Γ(Spec B, ⊤) ((Spec.map φ ≫ hU.isoSpec.inv).appTop (U.topIso.inv s)) := by
  rw [appTop_specMap_comp_isoSpec_inv]
  refine IsSMulRegular.of_right_eq_zero_of_smul fun z hz ↦ ?_
  have hmul : φ s * (ConcreteCategory.hom (Scheme.ΓSpecIso B).hom) z = 0 := by
    simpa [Algebra.smul_def] using
      congrArg (fun w ↦ (ConcreteCategory.hom (Scheme.ΓSpecIso B).hom) w) hz
  have hz0 : (ConcreteCategory.hom (Scheme.ΓSpecIso B).hom) z = 0 :=
    hs.right_eq_zero_of_smul (by simpa [Algebra.smul_def] using hmul)
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).hom).1 (by simpa using hz0)

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The germs of the pullback along a blowup morphism of a nonzerodivisor on an affine open of
the base are nonzerodivisors. -/
theorem isSMulRegular_germ_blowUpToBase_app (V : X.affineOpens) (r : Γ(X, V.1))
    (hr : IsSMulRegular Γ(X, V.1) r) (x : blowUp I) (hx : x ∈ (blowUpToBase I ⁻¹ᵁ V.1)) :
    IsSMulRegular ((blowUp I).presheaf.stalk x)
      ((blowUp I).presheaf.germ (blowUpToBase I ⁻¹ᵁ V.1) x hx
        ((blowUpToBase I).app V.1 r)) := by
  let := (reesSituation I).sectionRingGradedRing V.1
  let := (reesSituation I).sectionRingGradingGradedRing V.1
  obtain ⟨a, q, hq⟩ := exists_affineBlowupChart_point I V x hx
  let B := affineBlowupAlgebra (I.ideal V) (a : X.presheaf.obj (.op V.1))
    (Localization.Away (a : X.presheaf.obj (.op V.1)))
  let φ := algebraMap (X.presheaf.obj (.op V.1)) B
  let e := affineBlowupStandardOpenIso I V a
  let Q := Proj.basicOpen ((reesSituation I).sectionRingGrading V.1) (reesDegreeOne I V a).1
  let Z := Spec (.of B)
  let b : blowUp I ⟶ X := blowUpToBase I
  let gV : Z ⟶ V.1.toScheme := Spec.map (CommRingCat.ofHom φ) ≫ V.2.isoSpec.inv
  let g : Z ⟶ blowUp I :=
    e.hom ≫ (Q.ι ≫ Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) V)
  let qZ : Z := e.inv q
  let t₀ := V.1.topIso.inv r
  let t := gV.appTop t₀
  have hgpoint : g qZ = x := by
    dsimp only [g, qZ]
    show (Q.ι ≫ Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) V)
      (e.hom (e.inv q)) = x
    rw [show e.hom (e.inv q) = q from congrArg (fun f ↦ f q) e.inv_hom_id]
    exact hq
  have hbase' : g ≫ b = gV ≫ V.1.ι := by
    dsimp only [g, b, e, Q, gV]
    simpa only [Category.assoc] using affineBlowupChart_comp_blowUpToBase I V a
  have htq : IsSMulRegular (Z.presheaf.stalk qZ) (Z.presheaf.germ ⊤ qZ trivial t) :=
    isSMulRegular_germ_of_isAffineOpen Z (isAffineOpen_top Z)
      (isSMulRegular_appTop_specMap_comp_isoSpec_inv V.2 (CommRingCat.ofHom φ) r
        (isSMulRegular_algebraMap_affineBlowupAlgebra _ _ hr)) ⟨qZ, trivial⟩
  have hι : V.1.ι.appLE V.1 ⊤ V.1.ι_preimage_self.ge r = t₀ := by
    have hm : V.1.ι.appLE V.1 ⊤ V.1.ι_preimage_self.ge = V.1.topIso.inv := by
      ext z
      rw [Scheme.Opens.ι_appLE]
      show X.presheaf.map _ z = X.presheaf.map _ z
      exact congrArg (fun i ↦ (X.presheaf.map i) z) (Subsingleton.elim _ _)
    exact congrArg (fun f ↦ f r) hm
  cases hgpoint
  have hxchart : b (g qZ) ∈ V.1 := hx
  have hpoint : b (g qZ) = (gV ≫ V.1.ι) qZ := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f : Z ⟶ X ↦ f qZ) hbase'
  let heq : Inseparable (b (g qZ)) ((gV ≫ V.1.ι) qZ) := Inseparable.of_eq hpoint
  let ξ := X.presheaf.germ V.1 (b (g qZ)) hxchart r
  let ξ' : X.presheaf.stalk ((gV ≫ V.1.ι) qZ) := X.presheaf.stalkSpecializes heq.ge ξ
  have hinc : (gV ≫ V.1.ι).stalkMap qZ ξ' = Z.presheaf.germ ⊤ qZ (by simp) t := by
    have hv' : (gV ≫ V.1.ι) qZ ∈ V.1 := by
      rw [Scheme.Hom.comp_apply]
      exact (gV qZ).property
    have hvpre : qZ ∈ (gV ≫ V.1.ι) ⁻¹ᵁ V.1 := hv'
    have hxi : ξ' = X.presheaf.germ V.1 ((gV ≫ V.1.ι) qZ) hv' r := by
      dsimp only [ξ', ξ]
      simpa only [CommRingCat.comp_apply] using congrArg (fun f ↦ f r)
        (X.presheaf.germ_stalkSpecializes (U := V.1) (y := b (g qZ)) hxchart
          (x := (gV ≫ V.1.ι) qZ) heq.ge)
    rw [hxi, Scheme.Hom.germ_stalkMap_apply (f := gV ≫ V.1.ι) V.1 qZ hv' r]
    have hpre : (Opens.map (gV ≫ V.1.ι).base).obj V.1 = ⊤ := by
      show gV ⁻¹ᵁ (V.1.ι ⁻¹ᵁ V.1) = ⊤
      simp [V.1.ι_preimage_self]
    let O := (Opens.map (gV ≫ V.1.ι).base).obj V.1
    let tpre : Γ(Z, O) := Z.presheaf.map (homOfLE le_top).op t
    have htop : (⊤ : Z.Opens) ≤ O := by
      dsimp only [O]
      rw [← hpre]
    have hleft : (V.1.ι.appLE V.1 ⊤ V.1.ι_preimage_self.ge ≫ gV.appLE ⊤ ⊤ le_top) r = t := by
      rw [CommRingCat.comp_apply, hι]
      rfl
    have hfinal : ((gV ≫ V.1.ι).appLE V.1 ⊤ htop) r = t :=
      (congrArg (fun f ↦ f r) (Scheme.Hom.appLE_comp_appLE gV V.1.ι V.1 ⊤ ⊤
        V.1.ι_preimage_self.ge le_top)).symm.trans hleft
    let idZ : Z ⟶ Z := 𝟙 Z
    have happ : (gV ≫ V.1.ι).app V.1 r = tpre := by
      have hcompVal' : ((gV ≫ V.1.ι).appLE V.1 ⊤ htop ≫ idZ.appLE ⊤ O le_top) r =
          ((gV ≫ V.1.ι).appLE V.1 O le_rfl) r := by
        simpa only [idZ, Category.id_comp] using congrArg (fun f ↦ f r)
          (Scheme.Hom.appLE_comp_appLE idZ (gV ≫ V.1.ι) V.1 ⊤ O htop le_top)
      rw [← Scheme.Hom.appLE_eq_app, ← hcompVal', CommRingCat.comp_apply, hfinal]
      rfl
    rw [happ]
    show Z.presheaf.germ O qZ hvpre tpre = Z.presheaf.germ ⊤ qZ (by simp) t
    exact Z.presheaf.germ_res_apply (homOfLE le_top) qZ hvpre t
  have hmap : g.stalkMap qZ
      ((blowUp I).presheaf.germ (b ⁻¹ᵁ V.1) (g qZ) hx (b.app V.1 r)) =
      Z.presheaf.germ ⊤ qZ (by simp) t := by
    have hcomp₁ : (g ≫ b).stalkMap qZ ξ = g.stalkMap qZ (b.stalkMap (g qZ) ξ) :=
      congrArg (fun k ↦ k.hom ξ) (Scheme.Hom.stalkMap_comp g b qZ)
    calc
      g.stalkMap qZ ((blowUp I).presheaf.germ (b ⁻¹ᵁ V.1) (g qZ) hx (b.app V.1 r)) =
          g.stalkMap qZ (b.stalkMap (g qZ) ξ) := by
        rw [Scheme.Hom.germ_stalkMap_apply (f := b) V.1 (g qZ) hxchart r]
      _ = (g ≫ b).stalkMap qZ ξ := hcomp₁.symm
      _ = (gV ≫ V.1.ι).stalkMap qZ ξ' :=
            congrArg (fun k ↦ k.hom ξ)
              (Scheme.Hom.stalkMap_congr_hom (g ≫ b) (gV ≫ V.1.ι) hbase' qZ)
      _ = Z.presheaf.germ ⊤ qZ (by simp) t := hinc
  have hgOI : IsOpenImmersion g := by
    have : IsOpenImmersion
        (Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) V) :=
      MorphismProperty.of_isPullback
        (Stacks.RelativeProj.Situation.relativeProjChart_isPullback
          (reesSituation I) V).flip inferInstance
    dsimp only [g]
    infer_instance
  refine IsSMulRegular.of_right_eq_zero_of_smul fun z hz ↦ ?_
  have hmul : (g.stalkMap qZ).hom
        ((blowUp I).presheaf.germ (b ⁻¹ᵁ V.1) (g qZ) hx (b.app V.1 r)) *
      (g.stalkMap qZ).hom z = 0 := by
    simpa [Algebra.smul_def, b] using congrArg (fun w ↦ (g.stalkMap qZ).hom w) hz
  have hz0 : (g.stalkMap qZ).hom z = 0 := by
    refine htq.right_eq_zero_of_smul ?_
    rw [← hmap]
    simpa [Algebra.smul_def] using hmul
  exact (ConcreteCategory.bijective_of_isIso (g.stalkMap qZ)).1 (by simpa using hz0)

/-- **Stacks Project, Tag 0809.** Every effective Cartier divisor on a scheme has a defined
pullback along the blowup of the scheme in any quasi-coherent ideal. -/
@[stacks 0809 "effective Cartier divisors", sga "7 X 2.6" "partial"]
theorem isPullbackDefined_blowUpToBase (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Stacks.Divisors.IsPullbackDefined (blowUpToBase I) D := by
  show Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (blowUpToBase I))
  refine (Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal
    (D.comap (blowUpToBase I))).2 fun x hx ↦ ?_
  set b : blowUp I ⟶ X := blowUpToBase I
  have hySupport : b x ∈ D.support := by
    have h : x ∈ (D.comap b).support :=
      Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hx
    rwa [Scheme.IdealSheafData.support_comap] at h
  obtain ⟨V, hV, hbxV, t, ht, e, he⟩ :=
    (Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal D).mp hD (b x)
      (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr hySupport)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    (blowUp I).isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ b ⁻¹ᵁ V from hbxV) (b ⁻¹ᵁ V).isOpen
  let Va : X.affineOpens := ⟨V, hV⟩
  let Ua : (blowUp I).affineOpens := ⟨U, hU⟩
  have hJideal : (D.comap b).ideal Ua = Ideal.span {(b.appLE Va Ua hUV).hom t} := by
    rw [Stacks.IdealSheaf.ideal_comap_appLE D b Va Ua hUV,
      Stacks.Divisors.ideal_eq_quotient_of_chart D V hV (Ideal.span {t}) e he, Ideal.map_span]
    simp
  have ht' : IsSMulRegular Γ(X, V) t := by
    simpa only [IsSMulRegular, IsLeftRegular, smul_eq_mul] using ht.left
  have htU : IsSMulRegular Γ(blowUp I, U) ((b.appLE Va Ua hUV).hom t) := by
    refine isSMulRegular_of_forall_germ U _ fun y hy ↦ ?_
    have hrestr : (blowUp I).presheaf.germ U y hy (b.appLE Va Ua hUV t) =
        (blowUp I).presheaf.germ (b ⁻¹ᵁ V) y (hUV hy) (b.app Va t) :=
      (blowUp I).presheaf.germ_res_apply (homOfLE hUV) y hy (b.app Va t)
    rw [hrestr]
    exact isSMulRegular_germ_blowUpToBase_app I Va t ht' y (hUV hy)
  obtain ⟨eJ, heJ⟩ := Stacks.Divisors.exists_quotient_chart_of_ideal_span (D.comap b) U hU
    ((b.appLE Va Ua hUV).hom t) hJideal
  exact ⟨U, hU, hxU, (b.appLE Va Ua hUV).hom t,
    (Commute.isRegular_iff fun z ↦ mul_comm _ z).2
      (by simpa only [IsSMulRegular, IsLeftRegular, smul_eq_mul] using htU), eJ, heJ⟩

/-- **Stacks Project, Tag 0809.** Pullbacks of meromorphic functions are defined along the
blowup of a scheme in any quasi-coherent ideal. -/
@[stacks 0809 "meromorphic functions"]
theorem pullbacksMeromorphicSections_blowUpToBase :
    PullbacksMeromorphicSections (blowUpToBase I).toLRSHom := by
  refine pullbacksMeromorphicSections_of_affine _ fun V U hV hU h r hr ↦ ?_
  refine isSMulRegular_of_forall_germ U _ fun x hx ↦ ?_
  have hrestr : (blowUp I).presheaf.germ U x hx (pullbackSection (blowUpToBase I).toLRSHom U V h r)
      = (blowUp I).presheaf.germ ((blowUpToBase I) ⁻¹ᵁ V) x (h hx)
        ((blowUpToBase I).app V r) :=
    (blowUp I).presheaf.germ_res_apply (homOfLE h) x hx ((blowUpToBase I).app V r)
  rw [hrestr]
  exact isSMulRegular_germ_blowUpToBase_app I ⟨V, hV⟩ r hr x (h hx)

end AlgebraicGeometry

end
