module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrChart
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjRepresentsBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualBijective
public import StacksFrontier.AlgebraicGeometry.Morphism.Glue
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.ProjBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.CanonicalSymHom

/-!
# The isomorphism of relative Proj induced by an isomorphism of algebras is Tag 07ZG's morphism

Let `Y` be a scheme and `Φ : 𝒜₁ ⟶ 𝒜₂` a unital homomorphism of quasi-coherent graded
`𝒪_Y`-algebras all of whose components are isomorphisms. The relative homogeneous spectra
`Proj_Y(𝒜₁)` and `Proj_Y(𝒜₂)` represent isomorphic functors (Tags 01NY, 01NZ), and
`...RelativeProjQcohSheaf.relativeProjCongr` is the isomorphism `Proj_Y(𝒜₁) ≅ Proj_Y(𝒜₂)` this
induces; it is defined through the representations alone. This file identifies it with Tag 07ZG's
morphism `r_ψ` for `ψ = Φ⁻¹`, read as `...ProjectiveDeformation.projMapOfEventuallyIso`
(`...RelativeProjQcohSheaf.relativeProjCongr_hom_eq`), and deduces that it is a morphism over `Y`
(`...RelativeProjQcohSheaf.relativeProjCongr_hom_comp_toBase`). Its description on the charts,
`Proj` of the isomorphism `Γ(U, 𝒜₂) ⟶ Γ(U, 𝒜₁)` of graded rings of sections induced by `Φ⁻¹`
followed by the chart of `Proj_Y(𝒜₂)`, is
`...RelativeProjQcohSheaf.chart_comp_relativeProjCongr_hom` in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/RelativeProjCongrChart.lean`.

## The argument

The chart-wise morphism is Tag 07ZG's morphism `r_ψ` for `ψ = Φ⁻¹ : 𝒜₂ ⟶ 𝒜₁`, defined on the
open `U(ψ)`, which is all of `Proj_Y(𝒜₁)` because `ψ` is an isomorphism in every degree (Tag 07ZJ,
`...RelativeProjMapDomain.relativeMapDomain_eq_top_of_eventually_isIso`). Precomposed with the
identification of `Proj_Y(𝒜₁)` with that open it is
`...ProjectiveDeformation.projMapOfEventuallyIso`, whose chart description is the affine-local
characterization of `r_ψ` (`chart_comp_projMapOfEventuallyIso_congrInvHom`).

It remains to see that this morphism is the morphism the representations induce, and that is
the same computation as the one identifying the base-change morphism of Tag 01O3 with the functor
of points (`...RelativeProjQcohSheaf.homEquiv_comp_baseChangeHom_val`): on a chart the morphism
attached to a quadruple is the Tag 01N8 classifying morphism of its Veronese family, the transport
of a quadruple along `Φ⁻¹` precomposes that family with `Φ⁻¹`
(`...RelativeProjQcohSheaf.chartVeronese_algebraTransport_toFun`), and the classifying morphism of
a family precomposed with a homomorphism of graded rings is the classifying morphism followed by
`Proj` of the homomorphism (`...ProjChartGradedClassifying.toProj_classifyingHom_comp_projMap`).
Together these are
`...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_chartClass_comp_projMap_algebraTransport` in
`RelativeProjCongrChart.lean`, stated with `...RelativeProjQcohSheaf.congrSectionHom`, which is
`(congrInvHom Φ hΦ).sectionHom` by definition. The chart-wise equalities glue to
`classifyingMorphism_algebraTransport`, and testing on the affine opens of `Proj_Y(𝒜₁)` gives
`relativeProjCongr_hom_eq`.

## Main results

* `...RelativeProjQcohSheaf.chart_comp_projMapOfEventuallyIso_congrInvHom`: Tag 07ZG's morphism
  for `Φ⁻¹` on the charts.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.classifyingMorphism_algebraTransport`: the
  morphism attached to the transport of a point along `Φ⁻¹` is the morphism attached to the point
  followed by Tag 07ZG's morphism for `Φ⁻¹`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjCongr_hom_eq`: **the isomorphism
  induced by the representations is the chart-wise morphism.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjCongr_hom_comp_toBase`: it lies
  over the base.

## References

* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjTripleClassifying
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

section Congr

variable {Y : Scheme.{u}} {A₁ A₂ : SheafGradedAlgebra Y}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁) (situationAlgebra A₂))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))

/-- `Φ`, read as a homomorphism of sheaf-level graded algebra data. -/
abbrev congrHom : SheafGradedAlgebraHom A₁ A₂ :=
  SheafGradedAlgebraHom.ofUnitalHom Φ

/-- The inverse of `Φ`, read as a homomorphism of sheaf-level graded algebra data. -/
abbrev congrInvHom : SheafGradedAlgebraHom A₂ A₁ :=
  SheafGradedAlgebraHom.ofUnitalHom (unitalHomInverse Φ hΦ)

/-- Every degree component of `congrInvHom Φ hΦ`, the inverse of `Φ`, is an isomorphism. -/
theorem isIso_congrInvHom_app (n : ℤ) : IsIso ((congrInvHom Φ hΦ).app n) :=
  isIso_unitalHomInverse_app Φ hΦ n

/-- `Φ⁻¹` is an isomorphism in every degree, so in particular in all large degrees. -/
theorem eventually_isIso_congrInvHom :
    ∀ᶠ d : ℕ in Filter.atTop, IsIso ((congrInvHom Φ hΦ).app (d : ℤ)) :=
  Filter.Eventually.of_forall fun d => isIso_congrInvHom_app Φ hΦ d

/-- **The chart-wise morphism on a chart**: Tag 07ZG's morphism `Proj_Y(𝒜₁) ⟶ Proj_Y(𝒜₂)` for
`Φ⁻¹`, over an affine open `U` of the base, is `Proj` of the homomorphism `Γ(U, 𝒜₂) ⟶ Γ(U, 𝒜₁)`
induced by `Φ⁻¹`, followed by the chart of `Proj_Y(𝒜₂)`. -/
theorem chart_comp_projMapOfEventuallyIso_congrInvHom (U : Y.Opens) (hU : IsAffineOpen U) :
    (relativeProj A₁).chart U hU ≫
        ProjectiveDeformation.projMapOfEventuallyIso (congrInvHom Φ hΦ)
          (eventually_isIso_congrInvHom Φ hΦ) =
      AlgebraicGeometry.Proj.map ((congrInvHom Φ hΦ).sectionHom U)
          (irrelevant_le_map_congrSectionHom Φ hΦ U) ≫
        (relativeProj A₂).chart U hU := by
  have hirr : HomogeneousIdeal.irrelevant (A₁.grading U) ≤
      (HomogeneousIdeal.irrelevant (A₂.grading U)).map ((congrInvHom Φ hΦ).sectionHom U) :=
    irrelevant_le_map_congrSectionHom Φ hΦ U
  have hdomU : mapDomain (A₂.grading U) (A₁.grading U) ((congrInvHom Φ hΦ).sectionHom U) = ⊤ :=
    mapDomain_eq_top_of_irrelevant_le_map _ _ _ hirr
  rw [ProjectiveDeformation.chart_comp_projMapOfEventuallyIso _ _ U hU
      ((Scheme.topIso _).inv ≫ ((AlgebraicGeometry.Proj (A₁.grading U)).isoOfEq hdomU.symm).hom)
      (by rw [Category.assoc]; exact topIso_inv_isoOfEq_hom_ι _ _ _ hdomU),
    ← mapHomOfTop_eq_map _ _ _ hirr hdomU, mapHomOfTop]
  simp only [Category.assoc]

/-- **The chart-wise morphisms of a quadruple and of its transport agree after
Tag 07ZG's morphism for `Φ⁻¹`.** -/
theorem Fd.chartHom_comp_projMapOfEventuallyIso (V : Y.Opens) (hV : IsAffineOpen V) {k : ℕ}
    (hk : 0 < k) {T : Scheme.{u}} (gV : T ⟶ V.toScheme)
    (P : Quadruple (gV ≫ V.ι) (situationAlgebra A₁) (k : ℤ)) :
    Fd.chartHom A₁ V (relativeProj A₁) hV hk T (Fd.chartClass A₁ V gV (Quotient.mk _ P))
        ≫ ProjectiveDeformation.projMapOfEventuallyIso (congrInvHom Φ hΦ)
          (eventually_isIso_congrInvHom Φ hΦ)
      = Fd.chartHom A₂ V (relativeProj A₂) hV hk T (Fd.chartClass A₂ V gV (Quotient.mk _
          (P.algebraTransport (unitalHomInverse Φ hΦ) (isIso_unitalHomInverse_app Φ hΦ)))) := by
  rw [Fd.chartHom_eq_toProj_comp_chart A₁ V _ hV hk T,
    Fd.chartHom_eq_toProj_comp_chart A₂ V _ hV hk T, Category.assoc,
    chart_comp_projMapOfEventuallyIso_congrInvHom Φ hΦ V hV, ← Category.assoc]
  exact congrArg (· ≫ (relativeProj A₂).chart V hV)
    (Fd.toProj_chartEquiv_chartClass_comp_projMap_algebraTransport Φ hΦ ⟨V, hV⟩ hk gV P)

/-- **The transport of a point of `F_d` along `Φ⁻¹`, on the degree-`d` opens.** The morphism into
`Proj_Y(𝒜₂)` attached to the transport of a point `ξ` of `F_d(W)` for `𝒜₁` is the morphism into
`Proj_Y(𝒜₁)` attached to `ξ`, followed by Tag 07ZG's morphism for `Φ⁻¹`. Over the preimage of an
affine open of the base both are chart-wise morphisms, which
`Fd.chartHom_comp_projMapOfEventuallyIso` compares. -/
theorem Fd.homDegreeOpen_congr {k : ℕ} (hk : 0 < k) {W : Scheme.{u}}
    (ξ : Fd (situationAlgebra A₁) (k : ℤ) W) :
    Fd.homDegreeOpen A₂ (relativeProj A₂) hk
          (Fd.algebraTransport (unitalHomInverse Φ hΦ) (isIso_unitalHomInverse_app Φ hΦ)
            (k : ℤ) ξ)
        ≫ ((relativeProj A₂).degreeOpen k).ι
      = Fd.homDegreeOpen A₁ (relativeProj A₁) hk ξ ≫ ((relativeProj A₁).degreeOpen k).ι
          ≫ ProjectiveDeformation.projMapOfEventuallyIso (congrInvHom Φ hΦ)
          (eventually_isIso_congrInvHom Φ hΦ) := by
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := ξ.1.base x) trivial
  refine ⟨ξ.1 ⁻¹ᵁ U, hxU, ?_⟩
  obtain ⟨η, hη⟩ := Fd.exists_chartClassInv_eq A₁ U (Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ) (ξ.1 ∣_ U)
    (by rw [Fd.pullback_fst]; exact morphismRestrict_ι _ U)
  obtain ⟨gU, q⟩ := η
  obtain ⟨P, hP⟩ := Quotient.exists_rep
    (show Quotient (Quadruple.setoid (gU ≫ Scheme.Opens.ι U) (situationAlgebra A₁) (k : ℤ)) from
      (Fd.chartClassInv A₁ U
        (⟨gU, q⟩ : Fd (situationAlgebra (A₁.restrict (Scheme.Opens.ι U))) (k : ℤ) _)).2)
  have hη' : (⟨gU, q⟩ : Fd (situationAlgebra (A₁.restrict (Scheme.Opens.ι U))) (k : ℤ) _)
      = Fd.chartClass A₁ U gU (Quotient.mk _ P) := by
    rw [hP]
    exact (Fd.chartClass_chartClassInv A₁ U _).symm
  have hinv : Fd.chartClassInv A₁ U
      (⟨gU, q⟩ : Fd (situationAlgebra (A₁.restrict (Scheme.Opens.ι U))) (k : ℤ) _)
      = Fd.mk (gU ≫ Scheme.Opens.ι U) P :=
    (congrArg (Fd.chartClassInv A₁ U) hη').trans (Fd.chartClassInv_chartClass A₁ U gU _)
  set P₂ := P.algebraTransport (unitalHomInverse Φ hΦ) (isIso_unitalHomInverse_app Φ hΦ)
  set η₂ := Fd.chartClass A₂ U gU (Quotient.mk _ P₂)
  have hη₂ : Fd.chartClassInv A₂ U η₂ = Fd.pullback (ξ.1 ⁻¹ᵁ U).ι
      (Fd.algebraTransport (unitalHomInverse Φ hΦ) (isIso_unitalHomInverse_app Φ hΦ)
        (k : ℤ) ξ) := by
    rw [Fd.chartClassInv_chartClass, ← Fd.algebraTransport_pullback, ← hη, hinv]
    rfl
  have hL := Fd.ι_homDegreeOpen A₁ (relativeProj A₁) hk ξ U hU _ hη
  have hR := Fd.ι_homDegreeOpen A₂ (relativeProj A₂) hk
    (Fd.algebraTransport (unitalHomInverse Φ hΦ) (isIso_unitalHomInverse_app Φ hΦ)
      (k : ℤ) ξ) U hU η₂ hη₂
  have hC := Fd.chartHom_comp_projMapOfEventuallyIso Φ hΦ U hU hk gU P
  rw [← hη'] at hC
  refine hR.trans (hC.symm.trans ?_)
  rw [← hL, Category.assoc, Category.assoc]

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism in
/-- **The morphism attached to the transport of a point of `F` along `Φ⁻¹` is the morphism
attached to the point followed by Tag 07ZG's morphism for `Φ⁻¹`.** -/
theorem classifyingMorphism_algebraTransport {W : Scheme.{u}}
    (ζ : F (situationAlgebra A₁) W) :
    F.classifyingMorphism A₂
        (F.algebraTransport (unitalHomInverse Φ hΦ) (isIso_unitalHomInverse_app Φ hΦ) ζ) =
      F.classifyingMorphism A₁ ζ ≫ ProjectiveDeformation.projMapOfEventuallyIso (congrInvHom Φ hΦ)
          (eventually_isIso_congrInvHom Φ hΦ) := by
  obtain ⟨d, hd, Q, hQ⟩ := F.exists_quadruple ζ
  rw [← hQ]
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd.le
  have hk : 0 < k := by exact_mod_cast hd
  have e1 := F.classifyingMorphism_mk A₂ hk
    (Q.algebraTransport (unitalHomInverse Φ hΦ) (isIso_unitalHomInverse_app Φ hΦ))
  have e2 := F.classifyingMorphism_mk A₁ hk Q
  rw [canonicalIso_relativeProj, Iso.refl_inv] at e1 e2
  refine e1.trans ?_
  rw [e2]
  simp only [Category.comp_id, Category.assoc]
  exact Fd.homDegreeOpen_congr Φ hΦ hk (Fd.mk ζ.1 Q)

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism in
/-- **The isomorphism of relative homogeneous spectra induced by the representations is the
chart-wise morphism.** Both send the morphism attached to a point of `F` for `𝒜₁` to the morphism
attached to its transport along `Φ⁻¹`, so they agree after every morphism from a quasi-compact
scheme, and in particular on every affine open of `Proj_Y(𝒜₁)`. -/
theorem relativeProjCongr_hom_eq :
    (relativeProjCongr Φ hΦ).hom =
      ProjectiveDeformation.projMapOfEventuallyIso (congrInvHom Φ hΦ)
        (eventually_isIso_congrInvHom Φ hΦ) := by
  have key : ∀ {W : Scheme.{u}} (hW : CompactSpace W) (w : W ⟶ (relativeProj A₁).scheme),
      w ≫ (relativeProjCongr Φ hΦ).hom =
        w ≫ ProjectiveDeformation.projMapOfEventuallyIso (congrInvHom Φ hΦ)
          (eventually_isIso_congrInvHom Φ hΦ) := by
    intro W hW w
    obtain ⟨ζ, rfl⟩ : ∃ ζ, F.classifyingMorphism A₁ ζ = w :=
      ⟨_, classifyingMorphism_homEquiv_val A₁ hW w⟩
    rw [← classifyingMorphism_algebraTransport]
    apply (relativeProjRepresentableByFunctorUnconditional A₂).homEquiv.injective
    rw [homEquiv_classifyingMorphism]
    refine Scheme.QcExtension.ext (funext fun W₀ => funext fun hW₀ => funext fun w₀ => ?_)
    rw [homEquiv_comp_relativeProjCongr_val, homEquiv_classifyingMorphism]
    exact F.algebraTransport_pullback _ _ w₀ ζ
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have : IsAffine (Scheme.Opens.toScheme (X := (relativeProj A₁).scheme) U) := hU
  exact ⟨U, hxU, key inferInstance (Scheme.Opens.ι (X := (relativeProj A₁).scheme) U)⟩

/-- **The isomorphism induced by an isomorphism of graded algebras lies over the base.** -/
theorem relativeProjCongr_hom_comp_toBase :
    (relativeProjCongr Φ hΦ).hom ≫ (relativeProj A₂).toBase = (relativeProj A₁).toBase := by
  rw [relativeProjCongr_hom_eq]
  exact ProjectiveDeformation.projMapOfEventuallyIso_comp_toBase _ _

end Congr

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
