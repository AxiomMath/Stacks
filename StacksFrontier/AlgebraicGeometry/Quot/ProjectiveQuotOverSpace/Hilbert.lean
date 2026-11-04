/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Situation
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FibreHilbert
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteReadingConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Quot^P` of a module on `B × ℙⁿ_ℤ`, as a subfunctor of the Quot presheaf

Let `F/X/B` be a Quot situation over `Spec ℤ` with a projective frame `X = B × ℙⁿ_ℤ`
(`AlgebraicGeometry.ProjectiveQuotOverSpace.ProjectiveFrame`).  For a test scheme `T` over `B`
the base change `X_T` is the algebraic space of the scheme `ℙⁿ_T`, and a module on `X_T` is read
as a module on the scheme `ℙⁿ_T` (pullback along `h_{ℙⁿ_T} ≅ X_T`, then the Zariski reading of
`AlgebraicGeometry.Space.representedZariskiModule`).  The Hilbert polynomial with respect to the
pullback `L` of `𝒪_{ℙⁿ}(1)` is then the fibrewise Hilbert polynomial on `ℙⁿ_T`
(`AlgebraicGeometry.ProjectiveQuot.HasFibreHilbertPolynomial`): the condition of Stacks 0DNF
specialised to `I = ℤ`, `E_d = L^{⊗ d}`.

This file defines `Quot^P_{F/X/B}(T)` as the members of `Quot_{F/X/B}(T)` whose quotient has
Hilbert polynomial `P`, proves that the condition is stable under base change (the reading of a
pullback is the scheme pullback of the reading,
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`, and fibrewise Hilbert functions are
invariant under base change), and so obtains `Quot^P` as a subfunctor of
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.reading`: the reading on `ℙⁿ_T` of a module on `X_T`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.hilbertQuotients`: `Quot^P_{F/X/B}(T)`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.hilbertSubfunctor`: `Quot^P_{F/X/B}` as a subfunctor
  of the Quot presheaf.

## References

* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}
  {D : Space.QuotSituation B integerBase B.contains_integerBase}
  (E : ProjectiveFrame B n D)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-! ### The reading on `ℙⁿ_T` -/

/-- **The reading on `ℙⁿ_T` of a module on the base change `X_T`**: pull back along
`h_{ℙⁿ_T} ≅ X_T` and take the Zariski reading on the scheme `ℙⁿ_T`. -/
abbrev reading (T : Space.SchemesOver D.Y) :
    Space.Modules.{u, u} B integerBase B.contains_integerBase (D.space T).1 (D.space T).2 ⥤
      ((𝒯).obj (projectiveSite B n T.left)).Modules :=
  Space.modulePullback B integerBase B.contains_integerBase (spaceIso E T).hom ⋙
    ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (projectiveSite B n T.left)).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property)

/-- The pullback of a quasi-coherent module on `X_T` along `h_{ℙⁿ_T} ≅ X_T` is quasi-coherent. -/
theorem isQuasicoherentOnSite_modulePullback_spaceIso (T : Space.SchemesOver D.Y)
    (M : Space.Modules.{u, u} B integerBase B.contains_integerBase (D.space T).1 (D.space T).2)
    (hM : M.IsQuasicoherentOnSite) :
    ((Space.modulePullback B integerBase B.contains_integerBase (spaceIso E T).hom).obj
      M).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
    B.contains_integerBase (spaceIso E T).hom M hM

/-- **Finite presentation passes to the reading** (Stacks 05VG). -/
theorem isFinitePresentation_reading (T : Space.SchemesOver D.Y)
    (M : Space.Modules.{u, u} B integerBase B.contains_integerBase (D.space T).1 (D.space T).2)
    (hM : M.IsQuasicoherentOnSite) (hfp : SheafOfModules.IsFinitePresentationOnSite M) :
    ((reading E T).obj M).IsFinitePresentation := by
  have hN := isQuasicoherentOnSite_modulePullback_spaceIso E T M hM
  have hfp' := Space.isFinitePresentationOnSite_modulePullback B integerBase
    B.contains_integerBase (spaceIso E T).hom M hfp
  exact SheafOfModules.IsFinitePresentation.of_iso
    (Space.isFinitePresentation_restrictToChart B integerBase B.contains_integerBase
      (schemeSpace (projectiveSite B n T.left)) _ hN hfp' _)
    (representedZariskiRestrictionIsoModule (projectiveSite B n T.left) _ hN)

/-- **The reading of a pullback is the pullback of the reading**: for `h : T' ⟶ T` and a
quasi-coherent module `M` on `X_T`, the reading on `ℙⁿ_{T'}` of `(X_{T'} ⟶ X_T)^* M` is the
inverse image along `ℙⁿ_{T'} ⟶ ℙⁿ_T` of the reading of `M`. -/
def readingPullbackIso {T' T : Space.SchemesOver D.Y} (h : T' ⟶ T)
    (M : Space.Modules.{u, u} B integerBase B.contains_integerBase (D.space T).1 (D.space T).2)
    (hM : M.IsQuasicoherentOnSite) :
    (reading E T').obj ((Space.modulePullback B integerBase B.contains_integerBase
        (D.relativeMap h)).obj M) ≅
      (Scheme.Modules.pullback (projectiveSpaceOverMap n ((𝒯).map h.left))).obj
        ((reading E T).obj M) :=
  ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (projectiveSite B n T'.left)).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj (projectiveSite B n T'.left)) (projectiveSite B n T'.left).left.property).mapIso
    ((Space.modulePullbackSquare B integerBase B.contains_integerBase rfl
      (spaceIso_hom_relativeMap E h).symm).app M) ≪≫
  (Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase
    (projectiveSiteMap B n h.left)
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
    ((Space.modulePullback B integerBase B.contains_integerBase (spaceIso E T).hom).obj M)
    (isQuasicoherentOnSite_modulePullback_spaceIso E T M hM)).symm

/-! ### Hilbert polynomials on `ℙⁿ_T` under isomorphism and base change -/

/-- The fibrewise Hilbert polynomial is invariant under isomorphism. -/
theorem hasFibreHilbertPolynomial_of_iso {P : Polynomial ℚ} {T : Scheme.{u}}
    {G G' : (projectiveSpaceOver n T).Modules} (hG : G.IsFinitePresentation) (e : G ≅ G')
    (h : HasFibreHilbertPolynomial P G) : HasFibreHilbertPolynomial P G' := by
  have := hG
  have : G'.IsFinitePresentation := SheafOfModules.IsFinitePresentation.of_iso hG e
  rw [hasFibreHilbertPolynomial_iff] at h ⊢
  intro t d
  rw [← fibreHilbert_eq_of_iso e t]
  exact h t d

/-- The fibrewise Hilbert polynomial is stable under base change `ℙⁿ_{T'} ⟶ ℙⁿ_T`. -/
@[ega "III 7.9.12" "7.9.12.3"]
theorem hasFibreHilbertPolynomial_pullback {P : Polynomial ℚ} {T' T : Scheme.{u}} (g : T' ⟶ T)
    {G : (projectiveSpaceOver n T).Modules} (hG : G.IsFinitePresentation)
    (h : HasFibreHilbertPolynomial P G) :
    HasFibreHilbertPolynomial P ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj G) := by
  have := hG
  have := Stacks.Modules.isFinitePresentation_pullback (projectiveSpaceOverMap n g) G hG
  rw [hasFibreHilbertPolynomial_iff] at h ⊢
  intro t d
  rw [fibreHilbert_pullback]
  exact h (g t) d

/-! ### `Quot^P` -/

variable (P : Polynomial ℚ)

/-- **`Quot^P_{F/X/B}(T)`** (Stacks 0DP6 at `I = ℤ`, `E_d = L^{⊗ d}`): the members of
`Quot_{F/X/B}(T)` whose quotient, read on `ℙⁿ_T`, has Hilbert polynomial `P` on every fibre. -/
def hilbertQuotients (T : Space.SchemesOver D.Y) : Set (Subobject (D.baseChangeModule T)) :=
  {K | K ∈ D.properlySupportedQuotients T ∧
    HasFibreHilbertPolynomial P ((reading E T).obj (D.quotientModule T K))}

/-- **The Hilbert polynomial condition is stable under base change.** -/
@[ega "III 7.9.12" "7.9.12.3"]
theorem quotientPullback_mem_hilbertQuotients {T' T : Space.SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ hilbertQuotients E P T) :
    D.quotientPullback h K ∈ hilbertQuotients E P T' := by
  refine ⟨D.quotientPullback_mem_properlySupportedQuotients h K hK.1, ?_⟩
  have hqc : (D.quotientModule T K).IsQuasicoherentOnSite := hK.1.1.1.1
  have hfp := isFinitePresentation_reading E T _ hqc hK.1.1.2
  exact hasFibreHilbertPolynomial_of_iso
    (Stacks.Modules.isFinitePresentation_pullback _ _ hfp)
    (((reading E T').mapIso (D.quotientPullbackCokernelIso h K)) ≪≫
      readingPullbackIso E h _ hqc).symm
    (hasFibreHilbertPolynomial_pullback _ hfp hK.2)

/-- **`Quot^P_{F/X/B}` as a subfunctor of the Quot presheaf** of Stacks 09TR on the schemes of
the site: a section `(T ⟶ B, F_T ⟶ Q)` lies in it when `Q` has Hilbert polynomial `P`. -/
def hilbertSubfunctor : Subfunctor D.quotSitePresheaf where
  obj T := {x | x.subobject ∈ hilbertQuotients E P (CostructuredArrow.mk x.toBase)}
  map g x hx := quotientPullback_mem_hilbertQuotients E P
    (Space.QuotFamilyOver.restrict g.unop x.toBase) x.subobject hx

/-- `Quot^P_{F/X/B}`, the presheaf of the subfunctor. -/
abbrev hilbertPresheaf : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ ⥤ Type (u + 1) :=
  (hilbertSubfunctor E P).toFunctor

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
