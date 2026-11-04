module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.Statement
import StacksFrontier.AlgebraicGeometry.SectionPowerOverOpen.Basic
import StacksFrontier.AlgebraicGeometry.VeryAmpleGlue.TwistPullback

/-!
# The open `U(ψ)` and the morphism `r_{ℒ,ψ}` of Tag 01O9 under base change of the source

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `f : X ⟶ S` a morphism, `ℒ` an
invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of graded algebras, and let
`q : W ⟶ X` be an arbitrary morphism of schemes.  The pullback `q^*ψ` is a homomorphism
`(f ∘ q)^*𝒜 ⟶ ⨁_d (q^*ℒ)^{⊗ d}` (`…RelativeProjQcohSheaf.Twisting.pullback`).  This file proves
that the open `U(ψ)` of [Stacks, Tag 01O8] and the morphism `r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` of
[Stacks, Tag 01O9] are compatible with that base change, and deduces clause (2) of Tag 01O9 for an
arbitrary scheme over `X` rather than an open of `X`.  These are the scheme-level inputs of
[Stacks, Tag 0D2Z], whose clauses (2) and (3) are statements about schemes `W ⟶ X` and `X' ⟶ X`.

## Main results

* `…RelativeProjInvertibleMorphism.mem_coveringOpen_iff_exists_epi`: **`U(ψ)` is the union of the
  loci where `f^*𝒜_d ⟶ ℒ^{⊗ d}` is surjective, `d ≥ 1`** — the description of `U(ψ)` the source
  gives in the situation of Tag 0D2Z.
* `…RelativeProjInvertibleMorphism.coveringOpen_pullback`: **`U(q^*ψ) = q^{-1}(U(ψ))`.**
* `…RelativeProjInvertibleMorphism.coveringOpenPullback_globalMorphism`:
  **`r_{q^*ℒ, q^*ψ} = r_{ℒ,ψ} ∘ q|_{U(q^*ψ)}`.**
* `…RelativeProjInvertibleMorphism.preimage_coveringOpen_eq_top_of_epi` and
  `…RelativeProjInvertibleMorphism.clauseTwo_of_epi_pullback`: clause (2) of Tag 01O9 for an
  arbitrary morphism of schemes `q : W ⟶ X`.
* `…RelativeProjInvertibleMorphism.epi_pullback_app_of_preimage_eq_top`: on the open
  `U_{ψ(a)}` attached to a homogeneous section of positive degree `n`, `ψ_n` is surjective.

## Implementation notes

The open: each `U_{ψ(a)}` is a nonvanishing locus, and the value of `q^*ψ` at `a` is the
pullback of the value of `ψ` at `a` (`valueSec_pullback`), so Tag 0H78 for a section over an open
(`Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn`) gives the equality.

The morphism: over an affine open `V` of the base both morphisms are glued from the morphism of
[Stacks, Tag 01NK] of the induced datum.  The datum induced by `q^*ψ` agrees, degree by degree
and up to an isomorphism of the tensor powers, with the inverse image along `q` of the datum
induced by `ψ` (`exists_powIso_affineDatum`): both are a section of `ℒ^{⊗ n}` read through the
unit of the module-pullback adjunction along the same composite, followed by canonical
isomorphisms.  The morphism of Tag 01NK only depends on the ratios of values of the same degree,
so an isomorphism in each degree is enough (`…GradedSections.homOfLE_glued_eq_of_powIso`), and
`…ProjChartGradedPullback.resLE_glued` is the base change of Tag 01NK.

## References

* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections

open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf)
open Stacks.MorphismToProj (HomogeneousRatios)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {R : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L L' : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] [Stacks.Ample.IsInvertibleModule T L']
  (ψ : GradedSections 𝒜 L) (χ : GradedSections 𝒜 L')
  (Φ : ∀ n : ℕ, (natTensorPow L n : T.Modules) ≅ natTensorPow L' n)
  (hΦ : ∀ (n : ℕ) (a : 𝒜 n), (Φ n).hom.app ⊤ (ψ.toFun n a) = χ.toFun n a)

include hΦ

/-- Two data of graded sections whose values correspond, degree by degree, under isomorphisms of
the tensor powers have the same nonvanishing opens. -/
theorem nonvanishingOpenAt_eq_of_powIso (e : ℕ) (g : 𝒜 e) :
    χ.nonvanishingOpenAt e g = ψ.nonvanishingOpenAt e g := by
  rw [nonvanishingOpenAt, nonvanishingOpenAt, ← hΦ e g]
  exact TopologicalSpace.Opens.ext (Stacks.Ample.nonvanishingLocus_congr (Φ e) (ψ.toFun e g))

/-- ... and the same open `U`. -/
theorem coveringOpen_eq_of_powIso : χ.coveringOpen = ψ.coveringOpen :=
  iSup_congr fun p => nonvanishingOpenAt_eq_of_powIso ψ χ Φ hΦ (p.1 + 1) p.2

/-- ... and the same charts. -/
theorem chartToProj_eq_of_powIso {e : ℕ} {g : R} (hg : g ∈ 𝒜 e) (he : 0 < e) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨g, hg⟩))
    (hV' : V ≤ nonvanishingOpen T (natTensorPow L' e) (χ.toFun e ⟨g, hg⟩)) :
    χ.chartToProj hg hV' he = ψ.chartToProj hg hV he := by
  have hext : ∀ R₁ R₂ : HomogeneousRatios 𝒜 hg ↥Γ(T, V), R₁.toFun = R₂.toFun → R₁ = R₂ := by
    intro R₁ R₂ h
    obtain ⟨t, h1, h2, h3⟩ := R₁
    obtain ⟨t', h1', h2', h3'⟩ := R₂
    simp only at h
    subst h
    rfl
  refine congrArg (fun R' : HomogeneousRatios 𝒜 hg ↥Γ(T, V) => R'.chartToProj he)
    (hext _ _ (funext fun n => AddMonoidHom.ext fun a => ?_))
  rw [homogeneousRatios_toFun, homogeneousRatios_toFun]
  have hden : V ≤ nonvanishingOpen T (natTensorPow L' (n * e))
      ((Φ (n * e)).hom.app ⊤ (ψ.toFun (n * e) ⟨g ^ n, HomogeneousRatios.pow_mem hg n⟩)) := by
    rw [hΦ]; exact χ.le_nonvanishingOpen_pow hg hV' n
  refine Eq.trans ?_ (Stacks.AlgebraicGeometry.ProjChartGradedVeronese.ratioOf_iso L L' (Φ (n * e))
    _ _ (ψ.le_nonvanishingOpen_pow hg hV n) hden)
  rw [hΦ (n * e) a]
  exact Stacks.AlgebraicGeometry.ProjChartGradedPullback.ratioOf_den_congr _
    (hΦ (n * e) _).symm _ hden _

/-- ... and the same morphism `r_{L, ψ}` of [Stacks, Tag 01NK]. -/
theorem homOfLE_glued_eq_of_powIso :
    T.homOfLE (le_of_eq (coveringOpen_eq_of_powIso ψ χ Φ hΦ)) ≫ ψ.glued = χ.glued := by
  refine χ.eq_glued_of_homOfLE_eq fun e g hg he => ?_
  have hV : nonvanishingOpen T (natTensorPow L' e) (χ.toFun e ⟨g, hg⟩)
      ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨g, hg⟩) :=
    le_of_eq (nonvanishingOpenAt_eq_of_powIso ψ χ Φ hΦ e ⟨g, hg⟩)
  rw [← Category.assoc, T.homOfLE_homOfLE _ _]
  exact (ψ.homOfLE_glued_of_le hg he hV _).trans
    (chartToProj_eq_of_powIso ψ χ Φ hΦ hg he hV (le_refl _)).symm

end Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S X W : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : X ⟶ S}
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (ψ : Twisting f (situationAlgebra A) 1 L) (q : W ⟶ X)

/-- The open of a value of `ψ'` is the nonvanishing locus of the section of `ℒ^{⊗ n}`-piece it
is read from. -/
private theorem coe_nonvanishingOpenAt_toGradedPowerMap {X' : Scheme.{u}} {f' : X' ⟶ S}
    {L' : X'.Modules} [Stacks.Ample.IsInvertibleModule X' L']
    (ψ' : Twisting f' (situationAlgebra A) 1 L') (n : ℕ) (V : S.Opens)
    (a : Γ(A.piece (n : ℤ), V)) :
    ((toGradedPowerMap ψ').nonvanishingOpenAt n V a : Set X')
      = Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn ((laurent L').piece (n : ℤ))
          (f' ⁻¹ᵁ V)
          (ψ'.sectionHom (n : ℤ) (op V) ((pieceCast (A := A) (n : ℤ)).val.app (op V) a)) :=
  (congrArg (Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn (natTensorPow L' n) (f' ⁻¹ᵁ V))
    (toGradedPowerMap_value ψ' n V a)).trans
    (Stacks.SectionPowerOverOpen.nonvanishingLocusOn_congr (powCompare L' n).symm _ _)

/-- **The open of a value of `q^*ψ` is the preimage of the open of the value of `ψ`.** -/
theorem nonvanishingOpenAt_pullback (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) :
    (toGradedPowerMap (ψ.pullback q)).nonvanishingOpenAt n V a
      = q ⁻¹ᵁ (toGradedPowerMap ψ).nonvanishingOpenAt n V a := by
  set t := ψ.sectionHom (n : ℤ) (op V) ((pieceCast (A := A) (n : ℤ)).val.app (op V) a)
  have hs : (ψ.pullback q).sectionHom (n : ℤ) (op V) ((pieceCast (A := A) (n : ℤ)).val.app (op V) a)
      = (laurentPullback q L (n : ℤ)).val.app _
          (pullbackUnit (ringedSpaceHom q) ((laurent L).piece (n : ℤ)) _ t) :=
    Twisting.sectionHom_pullback ψ q (n : ℤ) (op V) _
  have e2 := Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn q
    ((laurent L).piece (n : ℤ)) (V := f ⁻¹ᵁ V) t
  have e3 := Stacks.SectionPowerOverOpen.nonvanishingLocusOn_congr
    (@asIso _ _ _ _ (laurentPullback q L (n : ℤ)) (isIso_laurentPullback q L (n : ℤ)))
    (q ⁻¹ᵁ (f ⁻¹ᵁ V))
    (pullbackUnit (ringedSpaceHom q) ((laurent L).piece (n : ℤ)) (op (f ⁻¹ᵁ V)) t)
  refine Opens.ext ((coe_nonvanishingOpenAt_toGradedPowerMap (ψ.pullback q) n V a).trans ?_)
  refine Eq.trans ?_ (congrArg (q.base ⁻¹' ·)
    (coe_nonvanishingOpenAt_toGradedPowerMap ψ n V a)).symm
  rw [hs]
  exact e3.trans e2.symm

/-- **On the open `U_{ψ(a)}` attached to a homogeneous section `a` of degree `n ≥ 1`, the
component `ψ_n` is surjective**, and so is that of `q^*ψ` for any `q` landing there. -/
theorem epi_pullback_app_of_preimage_eq_top (p : PositiveSection A)
    (hq : q ⁻¹ᵁ (toGradedPowerMap ψ).openOfPositiveSection p = ⊤) :
    Epi ((ψ.pullback q).app ((p.deg + 1 : ℕ) : ℤ)) := by
  have := isInvertible_piece ((pullbackFunctor (ringedSpaceHom q)).obj L) ((p.deg + 1 : ℕ) : ℤ)
  refine Stacks.VeryAmpleGlue.epi_of_forall_mem_nonvanishingLocusOn _ fun z => ?_
  refine ⟨(q ≫ f) ⁻¹ᵁ p.base, pullbackUnit (ringedSpaceHom (q ≫ f))
    ((situationAlgebra A).piece (((p.deg + 1 : ℕ) : ℤ) * 1)) (op p.base)
    ((pieceCast (A := A) ((p.deg + 1 : ℕ) : ℤ)).val.app (op p.base) p.val), ?_⟩
  have hz : z ∈ (toGradedPowerMap (ψ.pullback q)).nonvanishingOpenAt (p.deg + 1) p.base p.val := by
    rw [nonvanishingOpenAt_pullback, ← GradedPowerMap.openOfPositiveSection, hq]; trivial
  exact coe_nonvanishingOpenAt_toGradedPowerMap (ψ.pullback q) (p.deg + 1) p.base p.val ▸ hz

/-- **`U(ψ)` is the union, over `d ≥ 1`, of the loci where `f^*𝒜_d ⟶ ℒ^{⊗ d}` is surjective**:
a point lies in `U(ψ)` exactly when it has an open neighbourhood on which some positive-degree
component of `ψ` is surjective.  This is the source's own description of `U(ψ)` in
[Stacks, Tag 0D2Y], and it identifies it with the open of [Stacks, Tag 01O8]. -/
theorem mem_coveringOpen_iff_exists_epi (x : X) :
    x ∈ (toGradedPowerMap ψ).coveringOpen ↔
      ∃ (V : X.Opens) (k : ℕ), 0 < k ∧ x ∈ V ∧ Epi ((ψ.pullback V.ι).app (k : ℤ)) := by
  refine ⟨fun hx => ?_, fun ⟨V, k, hk, hx, h⟩ => (clauseTwo ψ hk V).1 hx⟩
  obtain ⟨p, hp⟩ := (toGradedPowerMap ψ).exists_mem_openOfPositiveSection_of_mem_coveringOpen hx
  exact ⟨_, p.deg + 1, Nat.succ_pos _, hp, epi_pullback_app_of_preimage_eq_top ψ _ p
    (top_unique fun y _ => y.2)⟩

/-- **`U(q^*ψ) = q^{-1}(U(ψ))`.** -/
theorem coveringOpen_pullback :
    (toGradedPowerMap (ψ.pullback q)).coveringOpen = q ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen := by
  rw [GradedPowerMap.coveringOpen, GradedPowerMap.coveringOpen, Scheme.Hom.preimage_iSup]
  exact iSup_congr fun p => nonvanishingOpenAt_pullback ψ q (p.deg + 1) p.base p.val

/-- **Clause (2)(a), for an arbitrary morphism of schemes.** -/
theorem preimage_coveringOpen_eq_top_of_epi {k : ℕ} (hk : 0 < k)
    [Epi ((ψ.pullback q).app (k : ℤ))] :
    q ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen = ⊤ := by
  have : Epi (((ψ.pullback q).pullback (⊤ : W.Opens).ι).app (k : ℤ)) :=
    Twisting.epi_pullbackApp _ _ _ inferInstance
  obtain ⟨h, -⟩ := clauseTwo (ψ.pullback q) hk ⊤
  exact top_unique (h.trans (coveringOpen_pullback ψ q).le)

open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul (pullPowSection) in
/-- **The value of `q^*ψ` at a homogeneous section is the pullback of the value of `ψ`.** -/
theorem valueSec_pullback (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) :
    valueSec (ψ.pullback q) n V a = pullPowSection q L n (f ⁻¹ᵁ V) (valueSec ψ n V a) := by
  have hs := Twisting.sectionHom_pullback ψ q (n : ℤ) (op V)
    ((pieceCast (A := A) (n : ℤ)).val.app (op V) a)
  have h2 := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
    (powCompare L n) (f ⁻¹ᵁ V)
    (ψ.sectionHom (n : ℤ) (op V) ((pieceCast (A := A) (n : ℤ)).val.app (op V) a))
  simp only [valueSec, pullPowSection]
  rw [hs]
  exact congrArg (fun z => (powCompare ((Scheme.Modules.pullback q).obj L) n).inv.app
    (q ⁻¹ᵁ f ⁻¹ᵁ V) ((laurentPullback q L (n : ℤ)).val.app _
      (pullbackUnit (ringedSpaceHom q) ((laurent L).piece (n : ℤ)) _ z))) h2.symm

section PowSection

open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul (pullPowSection restrictPowSection)

variable {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]

/-- The isomorphism `k^*(M^{⊗ m}) ≅ (k^*M)^{⊗ m}` through which `pullPowSection` reads the unit
image of a section. -/
def powTransport (m : ℕ) :
    (Scheme.Modules.pullback k).obj (natTensorPow M m) ≅
      natTensorPow ((Scheme.Modules.pullback k).obj M) m :=
  (Scheme.Modules.pullback k).mapIso (powCompare M m) ≪≫
    Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom k) M (m : ℤ) ≪≫
    (powCompare ((Scheme.Modules.pullback k).obj M) m).symm

/-- **`pullPowSection` is an isomorphism applied to the unit image of the section.** -/
theorem pullPowSection_eq_powTransport (m : ℕ) (O : Z.Opens) (x : Γ(natTensorPow M m, O)) :
    pullPowSection k M m O x
      = (powTransport k M m).hom.app (k ⁻¹ᵁ O)
          (pullbackUnit (ringedSpaceHom k) (natTensorPow M m : Z.Modules) (op O) x) := by
  have h := pullbackUnit_naturality (f := ringedSpaceHom k) (powCompare M m).hom (op O) x
  exact (congrArg (fun z => (powCompare ((Scheme.Modules.pullback k).obj M) m).inv.app (k ⁻¹ᵁ O)
    ((Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom k) M (m : ℤ)).hom.val.app
      ((opensMap (ringedSpaceHom k)).op.obj (op O)) z)) h).symm

omit [Stacks.Ample.IsInvertibleModule Z M] in
/-- **Two unit readings of one section along equal morphisms correspond under an isomorphism**,
independent of the section. -/
theorem exists_iso_unitReading {g₁ g₂ : Z' ⟶ Z} (h : g₁ = g₂) {K₁ K₂ : Z'.Modules}
    (Ξ₁ : (Scheme.Modules.pullback g₁).obj M ≅ K₁) (Ξ₂ : (Scheme.Modules.pullback g₂).obj M ≅ K₂)
    (O : Z.Opens) (h₁ : ⊤ ≤ g₁ ⁻¹ᵁ O) (h₂ : ⊤ ≤ g₂ ⁻¹ᵁ O) :
    ∃ E : K₁ ≅ K₂, ∀ x : Γ(M, O),
      E.hom.app ⊤ (K₁.presheaf.map (homOfLE h₁).op
          (Ξ₁.hom.app (g₁ ⁻¹ᵁ O) (pullbackUnit (ringedSpaceHom g₁) M (op O) x)))
        = K₂.presheaf.map (homOfLE h₂).op
          (Ξ₂.hom.app (g₂ ⁻¹ᵁ O) (pullbackUnit (ringedSpaceHom g₂) M (op O) x)) := by
  subst h
  refine ⟨Ξ₁.symm ≪≫ Ξ₂, fun x => ?_⟩
  have hn := ConcreteCategory.congr_hom
    ((Ξ₁.symm ≪≫ Ξ₂).hom.mapPresheaf.naturality (homOfLE h₁).op)
    (Ξ₁.hom.app (g₁ ⁻¹ᵁ O) (pullbackUnit (ringedSpaceHom g₁) M (op O) x))
  refine hn.trans ?_
  exact congrArg (fun z => K₂.presheaf.map (homOfLE h₂).op (Ξ₂.hom.app (g₁ ⁻¹ᵁ O) z))
    (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app Ξ₁.symm _
      (pullbackUnit (ringedSpaceHom g₁) M (op O) x))

/-- The isomorphism `(ι ≫ q)^*(M^{⊗ m}) ≅ (ι^* q^* M)^{⊗ m}` through which a section pulled back
first along `q` and then restricted to `q⁻¹U` is read. -/
def restrictPullTransport (U : Z.Opens) (m : ℕ) :
    (Scheme.Modules.pullback ((k ⁻¹ᵁ U).ι ≫ k)).obj (natTensorPow M m) ≅
      natTensorPow ((Scheme.Modules.pullback (k ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.pullback k).obj M)) m :=
  @asIso _ _ _ _ (Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison
      (ringedSpaceHom k) (ringedSpaceHom (k ⁻¹ᵁ U).ι) (natTensorPow M m : Z.Modules))
      (Stacks.PullbackPseudofunctor.isIso_modulePullbackComparison _ _ _) ≪≫
    (Scheme.Modules.pullback (k ⁻¹ᵁ U).ι).mapIso (powTransport k M m) ≪≫
    powTransport (k ⁻¹ᵁ U).ι ((Scheme.Modules.pullback k).obj M) m

/-- **A section pulled back along `k` and then restricted to `k⁻¹U`, as a unit reading.** -/
theorem restrictPowSection_pullPowSection (U : Z.Opens) (m : ℕ) (x : Γ(natTensorPow M m, U))
    (hU : ⊤ ≤ ((k ⁻¹ᵁ U).ι ≫ k) ⁻¹ᵁ U) :
    restrictPowSection ((Scheme.Modules.pullback k).obj M) (k ⁻¹ᵁ U) m (pullPowSection k M m U x)
      = (natTensorPow ((Scheme.Modules.pullback (k ⁻¹ᵁ U).ι).obj
            ((Scheme.Modules.pullback k).obj M)) m).presheaf.map (homOfLE hU).op
          ((restrictPullTransport k M U m).hom.app (((k ⁻¹ᵁ U).ι ≫ k) ⁻¹ᵁ U)
            (pullbackUnit (ringedSpaceHom ((k ⁻¹ᵁ U).ι ≫ k)) (natTensorPow M m : Z.Modules)
              (op U) x)) := by
  have h1 := Stacks.PullbackCompMonoidal.comparison_pullbackUnit (ringedSpaceHom k)
    (ringedSpaceHom (k ⁻¹ᵁ U).ι) (natTensorPow M m : Z.Modules) (op U) x
  have h2 := pullbackUnit_naturality (f := ringedSpaceHom (k ⁻¹ᵁ U).ι) (powTransport k M m).hom
    ((opensMap (ringedSpaceHom k)).op.obj (op U))
    (pullbackUnit (ringedSpaceHom k) (natTensorPow M m : Z.Modules) (op U) x)
  rw [restrictPowSection, pullPowSection_eq_powTransport, pullPowSection_eq_powTransport]
  refine congrArg (fun z => (natTensorPow ((Scheme.Modules.pullback (k ⁻¹ᵁ U).ι).obj
            ((Scheme.Modules.pullback k).obj M)) m).presheaf.map (homOfLE hU).op
          ((powTransport (k ⁻¹ᵁ U).ι ((Scheme.Modules.pullback k).obj M) m).hom.app _ z)) ?_
  refine h2.symm.trans ?_
  exact congrArg (fun z => (((pullbackFunctor (ringedSpaceHom (k ⁻¹ᵁ U).ι)).map
    (powTransport k M m).hom).val.app _) z) h1.symm

omit [Stacks.Ample.IsInvertibleModule Z M] in
/-- The isomorphism `(j ≫ ι_U)^*(M^{⊗ m}) ≅ (j^* ι_U^* M)^{⊗ m}` through which a section restricted
to `U` and then pulled back along `j` is read. -/
def pullRestrictTransport [Stacks.Ample.IsInvertibleModule Z M] (U : Z.Opens)
    (j : Z' ⟶ U.toScheme) (m : ℕ) :
    (Scheme.Modules.pullback (j ≫ U.ι)).obj (natTensorPow M m) ≅
      natTensorPow ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback U.ι).obj M)) m :=
  @asIso _ _ _ _ (Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison
      (ringedSpaceHom U.ι) (ringedSpaceHom j) (natTensorPow M m : Z.Modules))
      (Stacks.PullbackPseudofunctor.isIso_modulePullbackComparison _ _ _) ≪≫
    (Scheme.Modules.pullback j).mapIso (powTransport U.ι M m) ≪≫
    (Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso j
      ((Scheme.Modules.pullback U.ι).obj M) m).symm

/-- **A section restricted to `U` and then pulled back along `j`, as a unit reading.** -/
theorem pullSection_restrictPowSection (U : Z.Opens) (j : Z' ⟶ U.toScheme) (m : ℕ)
    (x : Γ(natTensorPow M m, U)) (hU : ⊤ ≤ (j ≫ U.ι) ⁻¹ᵁ U) :
    Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection j
        ((Scheme.Modules.pullback U.ι).obj M) m (restrictPowSection M U m x)
      = (natTensorPow ((Scheme.Modules.pullback j).obj
            ((Scheme.Modules.pullback U.ι).obj M)) m).presheaf.map (homOfLE hU).op
          ((pullRestrictTransport M U j m).hom.app ((j ≫ U.ι) ⁻¹ᵁ U)
            (pullbackUnit (ringedSpaceHom (j ≫ U.ι)) (natTensorPow M m : Z.Modules)
              (op U) x)) := by
  have h1 := Stacks.PullbackCompMonoidal.comparison_pullbackUnit (ringedSpaceHom U.ι)
    (ringedSpaceHom j) (natTensorPow M m : Z.Modules) (op U) x
  have h2 := pullbackUnit_naturality (f := ringedSpaceHom j) (powTransport U.ι M m).hom
    ((opensMap (ringedSpaceHom U.ι)).op.obj (op U))
    (pullbackUnit (ringedSpaceHom U.ι) (natTensorPow M m : Z.Modules) (op U) x)
  rw [Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullSection_eq_pullbackUnit,
    restrictPowSection, pullPowSection_eq_powTransport]
  have h3 := (pullbackUnit_restrict (f := ringedSpaceHom j)
    (natTensorPow ((Scheme.Modules.pullback U.ι).obj M) m : U.toScheme.Modules)
    (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).op
    ((powTransport U.ι M m).hom.app (U.ι ⁻¹ᵁ U)
      (pullbackUnit (ringedSpaceHom U.ι) (natTensorPow M m : Z.Modules) (op U) x))).symm
  refine (congrArg (fun w =>
    (Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso
      j ((Scheme.Modules.pullback U.ι).obj M) m).inv.app ⊤ w) h3).trans ?_
  have hn := ConcreteCategory.congr_hom
    ((Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso j
      ((Scheme.Modules.pullback U.ι).obj M) m).inv.mapPresheaf.naturality
      (homOfLE (j.preimage_mono (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U))).op)
    (pullbackUnit (ringedSpaceHom j)
      (natTensorPow ((Scheme.Modules.pullback U.ι).obj M) m : U.toScheme.Modules)
      (op (U.ι ⁻¹ᵁ U)) ((powTransport U.ι M m).hom.app (U.ι ⁻¹ᵁ U)
      (pullbackUnit (ringedSpaceHom U.ι) (natTensorPow M m : Z.Modules) (op U) x)))
  refine hn.trans ?_
  refine congrArg (fun w => (natTensorPow ((Scheme.Modules.pullback j).obj
    ((Scheme.Modules.pullback U.ι).obj M)) m : Z'.Modules).presheaf.map (homOfLE hU).op
    ((Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso j
      ((Scheme.Modules.pullback U.ι).obj M) m).inv.app _ w)) ?_
  refine h2.symm.trans ?_
  exact congrArg (fun w => (((pullbackFunctor (ringedSpaceHom j)).map
    (powTransport U.ι M m).hom).val.app _) w) h1.symm

end PowSection

/-- The factorisation through an open `U` of a morphism of schemes whose preimage of `U` is
everything. -/
def liftOfPreimageEqTop {Z T : Scheme.{u}} (U : Z.Opens) (g : T ⟶ Z) (h : g ⁻¹ᵁ U = ⊤) :
    T ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι g (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x ∈ g ⁻¹ᵁ U := by rw [h]; trivial
    exact hx)

/-- The factorisation is a factorisation. -/
@[reassoc (attr := simp)]
theorem liftOfPreimageEqTop_ι {Z T : Scheme.{u}} (U : Z.Opens) (g : T ⟶ Z) (h : g ⁻¹ᵁ U = ⊤) :
    liftOfPreimageEqTop U g h ≫ U.ι = g :=
  IsOpenImmersion.lift_fac _ _ _

section BaseChange

open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)

/-- The restriction `q^{-1}(f^{-1}V) ⟶ f^{-1}V` of `q` over an open `V` of the base. -/
abbrev partMap (V : S.Opens) : ((q ≫ f) ⁻¹ᵁ V).toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  q.resLE (f ⁻¹ᵁ V) ((q ≫ f) ⁻¹ᵁ V) le_rfl

/-- **Over an open `V` of the base, the datum of [Stacks, Tag 01NK] induced by `q^*ψ` is the
inverse image along `q` of the one induced by `ψ`**, degree by degree up to an isomorphism of the
tensor powers. -/
theorem exists_powIso_affineDatum (V : S.Opens) (n : ℕ) :
    ∃ Φ : (natTensorPow ((Scheme.Modules.pullback (partMap q V)).obj
          ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L)) n : ((q ≫ f) ⁻¹ᵁ V).toScheme.Modules) ≅
        natTensorPow ((Scheme.Modules.pullback ((q ≫ f) ⁻¹ᵁ V).ι).obj
          (toGradedPowerMap (ψ.pullback q)).L) n,
      ∀ a : A.grading V n, Φ.hom.app ⊤ ((((toGradedPowerMap ψ).affineDatum V).pullback
          (partMap q V)).toFun n a)
        = ((toGradedPowerMap (ψ.pullback q)).affineDatum V).toFun n a := by
  have hc : partMap q V ≫ (f ⁻¹ᵁ V).ι = ((q ≫ f) ⁻¹ᵁ V).ι ≫ q := Scheme.Hom.resLE_comp_ι _ _
  have h₁ : ⊤ ≤ (partMap q V ≫ (f ⁻¹ᵁ V).ι) ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [hc]; exact fun x _ => x.2
  have h₂ : ⊤ ≤ (((q ≫ f) ⁻¹ᵁ V).ι ≫ q) ⁻¹ᵁ (f ⁻¹ᵁ V) := fun x _ => x.2
  obtain ⟨E, hE⟩ := exists_iso_unitReading (natTensorPow L n : X.Modules) hc
    (pullRestrictTransport L (f ⁻¹ᵁ V) (partMap q V) n)
    (restrictPullTransport q L (f ⁻¹ᵁ V) n) (f ⁻¹ᵁ V) h₁ h₂
  refine ⟨E, fun a => ?_⟩
  have hv := (toGradedPowerMap_value (ψ.pullback q) n V (A.componentEquiv V n a)).trans
    (valueSec_pullback ψ q n V (A.componentEquiv V n a))
  rw [GradedSections.pullback_toFun, GradedPowerMap.affineDatum_toFun_apply,
    GradedPowerMap.affineDatum_toFun_apply, toGradedPowerMap_value]
  refine (congrArg (fun z => E.hom.app ⊤ z)
    (pullSection_restrictPowSection L (f ⁻¹ᵁ V) (partMap q V) n _ h₁)).trans ?_
  refine (hE _).trans ((restrictPowSection_pullPowSection q L (f ⁻¹ᵁ V) n _ h₂).symm.trans ?_)
  exact congrArg (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection
    (toGradedPowerMap (ψ.pullback q)).L ((q ≫ f) ⁻¹ᵁ V) n) hv.symm

/-- The restriction `U(q^*ψ) ⟶ U(ψ)` of `q`. -/
def coveringOpenPullback :
    (toGradedPowerMap (ψ.pullback q)).coveringOpen.toScheme ⟶
      (toGradedPowerMap ψ).coveringOpen.toScheme :=
  q.resLE _ _ (coveringOpen_pullback ψ q).le

/-- The restriction of `q` lies over `q`. -/
@[reassoc]
theorem coveringOpenPullback_ι :
    coveringOpenPullback ψ q ≫ (toGradedPowerMap ψ).coveringOpen.ι
      = (toGradedPowerMap (ψ.pullback q)).coveringOpen.ι ≫ q :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **`r_{q^*ℒ, q^*ψ} = r_{ℒ,ψ} ∘ q|_{U(q^*ψ)}`**: the morphism of [Stacks, Tag 01O9] commutes with
base change of the source along an arbitrary morphism of schemes. -/
theorem coveringOpenPullback_globalMorphism :
    coveringOpenPullback ψ q ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A)
      = (toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) := by
  refine (toGradedPowerMap (ψ.pullback q)).eq_globalMorphism_of_clauseThree (relativeProj A)
    fun V => ?_
  have hΦ := fun n => (exists_powIso_affineDatum ψ q V.1 n).choose_spec
  have hcov := ProjChartFullGraded.GradedSections.coveringOpen_eq_of_powIso
    (((toGradedPowerMap ψ).affineDatum V.1).pullback (partMap q V.1))
    ((toGradedPowerMap (ψ.pullback q)).affineDatum V.1)
    (fun n => (exists_powIso_affineDatum ψ q V.1 n).choose) hΦ
  have hgl := ProjChartFullGraded.GradedSections.homOfLE_glued_eq_of_powIso
    (((toGradedPowerMap ψ).affineDatum V.1).pullback (partMap q V.1))
    ((toGradedPowerMap (ψ.pullback q)).affineDatum V.1)
    (fun n => (exists_powIso_affineDatum ψ q V.1 n).choose) hΦ
  have hres := ProjChartGradedPullback.resLE_glued (partMap q V.1) _
    ((toGradedPowerMap ψ).affineDatum V.1)
    (((toGradedPowerMap ψ).affineDatum V.1).pullback (partMap q V.1)) (fun _ _ => rfl)
  have hle := ProjChartGradedPullback.coveringOpen_le_preimage (partMap q V.1) _
    ((toGradedPowerMap ψ).affineDatum V.1)
    (((toGradedPowerMap ψ).affineDatum V.1).pullback (partMap q V.1)) (fun _ _ => rfl)
  have hinc : (toGradedPowerMap (ψ.pullback q)).affineDatumInclusion V ≫ coveringOpenPullback ψ q
      = ((q ≫ f) ⁻¹ᵁ V.1).toScheme.homOfLE (le_of_eq hcov)
        ≫ (partMap q V.1).resLE _ _ hle
        ≫ (toGradedPowerMap ψ).affineDatumInclusion V := by
    rw [← cancel_mono (toGradedPowerMap ψ).coveringOpen.ι]
    simp only [Category.assoc, coveringOpenPullback_ι,
      (toGradedPowerMap ψ).affineDatumInclusion_ι V]
    rw [reassoc_of% (toGradedPowerMap (ψ.pullback q)).affineDatumInclusion_ι V,
      Scheme.Hom.resLE_comp_ι_assoc, Scheme.homOfLE_ι_assoc]
    exact congrArg (fun g => _ ≫ g) (Scheme.Hom.resLE_comp_ι q (le_rfl :
      (q ≫ f) ⁻¹ᵁ V.1 ≤ q ⁻¹ᵁ (f ⁻¹ᵁ V.1))).symm
  calc (toGradedPowerMap (ψ.pullback q)).affineDatumInclusion V ≫ coveringOpenPullback ψ q ≫
        (toGradedPowerMap ψ).globalMorphism (relativeProj A)
      = (((q ≫ f) ⁻¹ᵁ V.1).toScheme.homOfLE (le_of_eq hcov)
        ≫ (partMap q V.1).resLE _ _ hle)
        ≫ (toGradedPowerMap ψ).affineDatumInclusion V
        ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A) := by
        rw [← Category.assoc, hinc]; simp only [Category.assoc]
    _ = (((q ≫ f) ⁻¹ᵁ V.1).toScheme.homOfLE (le_of_eq hcov)
        ≫ ((partMap q V.1).resLE _ _ hle ≫ ((toGradedPowerMap ψ).affineDatum V.1).glued))
        ≫ (relativeProj A).chart V.1 V.2 := by
        rw [(toGradedPowerMap ψ).affineDatumInclusion_globalMorphism (relativeProj A) V]
        simp only [Category.assoc]
    _ = ((toGradedPowerMap (ψ.pullback q)).affineDatum V.1).glued
          ≫ (relativeProj A).chart V.1 V.2 := by rw [hres, hgl]

/-- **Clause (2) of [Stacks, Tag 01O9] for an arbitrary morphism of schemes `q : W ⟶ X`.**  If
`(q^*ψ)_k : (f ∘ q)^*𝒜_k ⟶ (q^*ℒ)^{⊗ k}` is surjective for some `k ≥ 1`, then `q` lands in
`U(ψ)`, and the composite of the factorisation `W ⟶ U(ψ)` with `r_{ℒ,ψ}`, read on the open
subscheme `⊤ ≅ W`, is the morphism that the representation of the functor of quadruples by
`Proj_S(𝒜)` attaches to the quadruple `(k, f ∘ q, (q^*ℒ)^{⊗ k}, (q^*ψ)|_{𝒜^{(k)}})`. -/
theorem clauseTwo_of_epi_pullback {k : ℕ} (hk : 0 < k) [Epi ((ψ.pullback q).app (k : ℤ))] :
    ∃ h : Set.range q.base ⊆ Set.range (toGradedPowerMap ψ).coveringOpen.ι.base,
      (⊤ : W.Opens).ι ≫ IsOpenImmersion.lift (toGradedPowerMap ψ).coveringOpen.ι q h
          ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A)
        = F.classifyingMorphism A (F.mk ((⊤ : W.Opens).ι ≫ q ≫ f) (by exact_mod_cast hk)
            (haveI : Epi (((ψ.pullback q).pullback (⊤ : W.Opens).ι).app (k : ℤ)) :=
              Twisting.epi_pullbackApp _ _ _ inferInstance
             restrictQuadruple (ψ.pullback q) ⊤ k)) := by
  have : Epi (((ψ.pullback q).pullback (⊤ : W.Opens).ι).app (k : ℤ)) :=
    Twisting.epi_pullbackApp _ _ _ inferInstance
  obtain ⟨h', e⟩ := clauseTwo (ψ.pullback q) hk ⊤
  have hrange : Set.range q.base ⊆ Set.range (toGradedPowerMap ψ).coveringOpen.ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x ∈ q ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen := by
      rw [preimage_coveringOpen_eq_top_of_epi ψ q hk]; trivial
    exact hx
  refine ⟨hrange, Eq.trans ?_ e⟩
  rw [← coveringOpenPullback_globalMorphism ψ q, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (toGradedPowerMap ψ).coveringOpen.ι, Category.assoc,
    IsOpenImmersion.lift_fac, Category.assoc, coveringOpenPullback_ι, Scheme.homOfLE_ι_assoc]

end BaseChange

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
