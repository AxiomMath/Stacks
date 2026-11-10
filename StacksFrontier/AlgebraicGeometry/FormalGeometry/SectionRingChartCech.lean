module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Bijective
public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Multiplicative
public import StacksFrontier.RingTheory.HomogeneousLocalization.GradedLocalizedModule
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayDegreeZeroBaseChange
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.OrderedCechComparison
public import StacksFrontier.RingTheory.Cech.GradedSubcomplex

/-!
# The Čech complex of a quasi-coherent module on the standard opens of an ample section ring

Let `X` be a scheme, `L` an ample invertible `𝒪_X`-module with section ring
`A = Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^⊗n)`, and `ℱ` a quasi-coherent `𝒪_X`-module with graded
`A`-module `M = Γ_*(X, L, ℱ) = ⨁_{m ≥ 0} Γ(X, ℱ ⊗ L^⊗m)`. Fix finitely many homogeneous elements
`g₁, …, g_r` of positive degree, given by global sections `αᵢ` of positive powers of `L`, and let
`Wᵢ = X_{αᵢ}` be their nonvanishing opens.

For a nonempty set `S` of indices, `W_S = ⋂_{i ∈ S} Wᵢ` is the nonvanishing open of a section of a
power of `L` representing `g_S = ∏_{i ∈ S} gᵢ`, and Stacks Tag 01PW identifies `Γ(W_S, ℱ)` with
the degree-zero part of `M_{g_S}`. This file relates the Čech complex of `ℱ` on the covering
`{Wᵢ}` to the Čech complex `C^•(g; M)` of [Stacks, Tag 0A6R]:

* an injective additive map `Γ(W_S, ℱ) → M_{g_S}` whose image is the degree-zero part
  (`Stacks.SectionRingChartCech.chartLift`);
* its compatibility with restriction from `W_S` to `W_T` and the transition map
  `M_{g_S} → M_{g_T}` for `S ⊆ T`;
* an injective map from the ordered Čech cochains of `ℱ` on `{Wᵢ}` to `C^•(g; M)`, commuting
  with the differentials, whose image is the degree-zero part.

## Main definitions

* `Stacks.SectionRingChartCech.chartLift`: the inverse of the division of Tag 01PW, landing in
  the localization.
* `Stacks.SectionRingChartCech.ordCochainLift`: the map from the ordered Čech cochains of `ℱ` to
  the Čech complex of `M`.

## Main results

* `Stacks.SectionRingChartCech.exists_prod_chart`: a section representing `g_S`, with
  nonvanishing open `W_S`.
* `Stacks.SectionRingChartCech.chartLift_injective`: the lift `chartLift` is injective.
* `Stacks.SectionRingChartCech.mem_range_chartLift`: the image of `chartLift` is the degree-zero
  part.
* `Stacks.SectionRingChartCech.chartLift_restrict`: `chartLift` is compatible with restriction.
* `Stacks.SectionRingChartCech.ordCochainLift_injective`,
  `Stacks.SectionRingChartCech.mem_range_ordCochainLift`,
  `Stacks.SectionRingChartCech.ordCochainLift_ordD`: `ordCochainLift` is injective, has image the
  degree-zero part, and commutes with the differentials.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.TwistedSections (twistPow twistSections twistModule)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjQuasicoherent (localDivision)

universe u

attribute [local instance] instVAddNatIntGradedLocalizedModule

namespace Stacks.SectionRingChartCech


section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### Products of homogeneous sections -/

/-- **The product of finitely many homogeneous sections.** For a nonempty set `S` of indices
there is a section `β` of `L ^⊗ (∑_{i ∈ S} dᵢ)` representing `∏_{i ∈ S} gᵢ` in the section ring,
whose nonvanishing open is `⋂_{i ∈ S} X_{αᵢ}`. -/
theorem exists_prod_chart {r : ℕ} {d : Fin r → ℕ} (α : ∀ i, powSections L (d i))
    (S : Finset (Fin r)) (hS : S.Nonempty) :
    ∃ (e : ℕ) (β : powSections L e), e = ∑ i ∈ S, d i ∧
      DirectSum.of (powSections L) e β = ∏ i ∈ S, DirectSum.of (powSections L) (d i) (α i) ∧
      nvOpen L β = ⨅ i ∈ S, nvOpen L (α i) := by
  classical
  induction S using Finset.cons_induction with
  | empty => exact absurd hS (by simp)
  | cons a S ha ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS'
    · exact ⟨d a, α a, by simp, by simp, by simp⟩
    obtain ⟨e, β, he, hof, hnv⟩ := ih hS'
    refine ⟨d a + e, mul (α a) β, by rw [Finset.sum_cons, he], ?_, ?_⟩
    · rw [Stacks.SectionRingChartMap.of_mul_eq, Finset.prod_cons, hof]
    · rw [Stacks.SectionRingChartMap.nvOpen_mul, hnv, Finset.cons_eq_insert,
        Finset.iInf_insert]

/-! ### Transport between localizations at equal elements -/

/-- The identification of the localizations at the powers of two equal elements. -/
def localizedEquivOfEq {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {x y : A} (h : x = y) :
    LocalizedModule (Submonoid.powers x) N ≃+ LocalizedModule (Submonoid.powers y) N := by
  subst h
  exact AddEquiv.refl _

/-- The identification `localizedEquivOfEq` sends the fraction `m / xⁿ` to `m / yⁿ`. -/
theorem localizedEquivOfEq_mk {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N]
    [Module A N] {x y : A} (h : x = y) (m : N) (n : ℕ) :
    localizedEquivOfEq h (LocalizedModule.mk m (⟨x ^ n, n, rfl⟩ : Submonoid.powers x)) =
      LocalizedModule.mk m (⟨y ^ n, n, rfl⟩ : Submonoid.powers y) := by
  subst h
  rfl

/-! ### The inverse of the division of Tag 01PW -/

variable (hL : Stacks.Ample.IsAmple X L) (F : X.Modules) [F.IsQuasicoherent]

/-- **The division of Tag 01PW, as an additive equivalence**: the degree-zero localization of
`Γ_*(X, L, ℱ)` at a homogeneous element `β` of positive degree is `Γ(X_β, ℱ)`. -/
def divisionEquiv {e : ℕ} (he : 0 < e) (β : powSections L e) :
    GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
        (DirectSum.of (powSections L) e β) ≃+ Γ(F, nvOpen L β) :=
  AddEquiv.ofBijective (localDivision L F β (le_refl (nvOpen L β)))
    ⟨Stacks.SectionRingProjQuasicoherent.localDivision_injective L F hL he β,
      Stacks.SectionRingProjQuasicoherent.localDivision_surjective L F hL he β⟩

/-- **The inverse of the division of Tag 01PW**, landing in the localization of
`Γ_*(X, L, ℱ)` at an element `x` equal to the homogeneous element `β`. -/
def chartLift {e : ℕ} (he : 0 < e) (β : powSections L e) {x : sectionRing L}
    (hx : DirectSum.of (powSections L) e β = x) :
    Γ(F, nvOpen L β) →+ LocalizedModule (Submonoid.powers x) (twistModule F L) :=
  (localizedEquivOfEq hx).toAddMonoidHom.comp
    ((GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
        (DirectSum.of (powSections L) e β)).toAddSubgroup.subtype.comp
      (divisionEquiv L hL F he β).symm.toAddMonoidHom)

/-- The lift `chartLift` is injective. -/
theorem chartLift_injective {e : ℕ} (he : 0 < e) (β : powSections L e) {x : sectionRing L}
    (hx : DirectSum.of (powSections L) e β = x) :
    Function.Injective (chartLift L hL F he β hx) :=
  (localizedEquivOfEq hx).injective.comp
    (Subtype.val_injective.comp (divisionEquiv L hL F he β).symm.injective)

/-- **The image of the lift is the degree-zero part.** -/
theorem mem_range_chartLift {e : ℕ} (he : 0 < e) (β : powSections L e) {x : sectionRing L}
    (hx : DirectSum.of (powSections L) e β = x)
    (z : LocalizedModule (Submonoid.powers x) (twistModule F L)) :
    z ∈ (chartLift L hL F he β hx).range ↔
      z ∈ Stacks.GradedLocalization.gradedPiece (grading L)
        (Stacks.TwistedSections.moduleGrading F L) x 0 := by
  subst hx
  have hβ := Stacks.ExternalGrading.of_mem_summand e β
  constructor
  · rintro ⟨y, rfl⟩
    exact (Stacks.GradedLocalization.mem_gradedModuleDegreeZeroLocalization_iff (grading L)
      (Stacks.TwistedSections.moduleGrading F L) hβ _).1
        ((divisionEquiv L hL F he β).symm y).2
  · intro hz
    exact ⟨divisionEquiv L hL F he β
      ⟨z, (Stacks.GradedLocalization.mem_gradedModuleDegreeZeroLocalization_iff (grading L)
        (Stacks.TwistedSections.moduleGrading F L) hβ z).2 hz⟩, by
      simp [chartLift, localizedEquivOfEq]⟩

/-- **The lift on a fraction.** Every value of the lift is a fraction `t / xⁿ` with `t` a twisted
section of degree `n e`, and the division of `t / βⁿ` is the section lifted. -/
theorem exists_chartLift_eq_mk {e : ℕ} (he : 0 < e) (β : powSections L e) {x : sectionRing L}
    (hx : DirectSum.of (powSections L) e β = x) (y : Γ(F, nvOpen L β)) :
    ∃ (n : ℕ) (t : twistSections F L (n * e)),
      chartLift L hL F he β hx y = LocalizedModule.mk
        (DirectSum.of (twistSections F L) (n * e) t) (⟨x ^ n, n, rfl⟩ : Submonoid.powers x) ∧
      ((divisionEquiv L hL F he β).symm y : LocalizedModule.Away
          (DirectSum.of (powSections L) e β) (twistModule F L)) =
        LocalizedModule.mk (DirectSum.of (twistSections F L) (n * e) t)
          (⟨(DirectSum.of (powSections L) e β) ^ n, n, rfl⟩ :
            Submonoid.powers (DirectSum.of (powSections L) e β)) := by
  obtain ⟨n, m, hm, hzm⟩ :=
    Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree (grading L)
      (Stacks.TwistedSections.moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand e β)
      ((divisionEquiv L hL F he β).symm y)
  obtain ⟨t, rfl⟩ := Stacks.TwistedSections.mem_moduleGrading_natCast_iff.1 hm
  refine ⟨n, t, ?_, hzm⟩
  change localizedEquivOfEq hx ((divisionEquiv L hL F he β).symm y).1 = _
  rw [hzm, localizedEquivOfEq_mk]

/-- **The lift is compatible with restriction.** Let `x = β` and `x' = β'` be homogeneous of
degrees `e` and `e'`, with `X_{β'} ⊆ X_β`, and `x h = x'` for some `h` of degree `j` with
`e + j = e'`. Then lifting the restriction of a section from `X_β` to `X_{β'}` is the image of
its lift under any map of localizations sending `m / xⁿ` to `hⁿ m / x'ⁿ` — the transition map of
the Čech complex. -/
theorem chartLift_restrict {e e' j : ℕ} (he : 0 < e) (he' : 0 < e') (β : powSections L e)
    (β' : powSections L e') {x x' h : sectionRing L}
    (hx : DirectSum.of (powSections L) e β = x) (hx' : DirectSum.of (powSections L) e' β' = x')
    (hh : h ∈ grading L j) (hj : e + j = e') (hxh : x * h = x')
    (i : nvOpen L β' ⟶ nvOpen L β)
    (φ : LocalizedModule (Submonoid.powers x) (twistModule F L) →+
      LocalizedModule (Submonoid.powers x') (twistModule F L))
    (hφ : ∀ (m : twistModule F L) (n : ℕ),
      φ (LocalizedModule.mk m (⟨x ^ n, n, rfl⟩ : Submonoid.powers x)) =
        LocalizedModule.mk (h ^ n • m) (⟨x' ^ n, n, rfl⟩ : Submonoid.powers x'))
    (y : Γ(F, nvOpen L β)) :
    chartLift L hL F he' β' hx' (F.presheaf.map i.op y) = φ (chartLift L hL F he β hx y) := by
  obtain ⟨n, t, hlift, hz⟩ := exists_chartLift_eq_mk L hL F he β hx y
  rw [hlift, hφ]
  have hhn : h ^ n ∈ grading L (j * n) := by
    have := SetLike.pow_mem_graded n hh
    rwa [smul_eq_mul, mul_comm] at this
  obtain ⟨c, hc⟩ := Stacks.ExternalGrading.mem_summand_iff.1 hhn
  have hring : DirectSum.of (powSections L) e β ^ n * DirectSum.of (powSections L) (j * n) c =
      DirectSum.of (powSections L) e' β' ^ n := by
    rw [hc, hx, hx', ← mul_pow, hxh]
  have hdeg : e * n + j * n = e' * n := by rw [← hj]; ring
  have hmem : LocalizedModule.mk (DirectSum.of (powSections L) (j * n) c •
        DirectSum.of (twistSections F L) (n * e) t)
      (⟨(DirectSum.of (powSections L) e' β') ^ n, n, rfl⟩ :
        Submonoid.powers (DirectSum.of (powSections L) e' β')) ∈
      GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
        (DirectSum.of (powSections L) e' β') := by
    refine (Stacks.GradedLocalization.mem_gradedModuleDegreeZeroLocalization_iff (grading L)
      (Stacks.TwistedSections.moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand e' β')
      _).2 (Stacks.GradedLocalization.mk_mem_gradedPiece _ _
        (Stacks.ExternalGrading.of_mem_summand e' β') ?_)
    have h1 := SetLike.GradedSMul.smul_mem (A := grading L)
      (B := Stacks.TwistedSections.moduleGrading F L)
      (Stacks.ExternalGrading.of_mem_summand (j * n) c)
      (Stacks.TwistedSections.mem_moduleGrading_natCast_iff.2 ⟨t, rfl⟩ :
        DirectSum.of (twistSections F L) (n * e) t ∈
          Stacks.TwistedSections.moduleGrading F L ((n * e : ℕ) : ℤ))
    convert h1 using 2
    change (0 : ℤ) + n • (e' : ℤ) = ((j * n : ℕ) : ℤ) + ((n * e : ℕ) : ℤ)
    rw [← hj]
    push_cast
    ring
  have hchange := Stacks.SectionRingProjQuasicoherent.localDivision_change L F β β' c
    (le_refl _) (le_refl _) i n n (by rw [mul_comm e n, mul_comm e' n] at hdeg ⊢; linarith)
    hring ((divisionEquiv L hL F he β).symm y) ⟨_, hmem⟩ t hz rfl
  have hy : localDivision L F β (le_refl _) ((divisionEquiv L hL F he β).symm y) = y :=
    (divisionEquiv L hL F he β).apply_symm_apply y
  rw [hy] at hchange
  have : (divisionEquiv L hL F he' β').symm (F.presheaf.map i.op y) = ⟨_, hmem⟩ :=
    (AddEquiv.symm_apply_eq _).2 hchange.symm
  change localizedEquivOfEq hx' ((divisionEquiv L hL F he' β').symm
    (F.presheaf.map i.op y)).1 = _
  rw [this]
  change localizedEquivOfEq hx' (LocalizedModule.mk _ ⟨(DirectSum.of (powSections L) e' β') ^ n,
    n, rfl⟩) = _
  rw [localizedEquivOfEq_mk, hc]

/-! ### The charts of a finite family of homogeneous sections -/

section Charts

variable {r : ℕ} {d : Fin r → ℕ} (hd : ∀ i, 0 < d i) (α : ∀ i, powSections L (d i))

/-- The homogeneous elements `gᵢ` of the section ring given by the sections `αᵢ`. -/
abbrev gen (i : Fin r) : sectionRing L := DirectSum.of (powSections L) (d i) (α i)

/-- The covering by the nonvanishing opens `X_{αᵢ}`, indexed in the universe of the scheme. -/
abbrev chartOpen (i : ULift.{u} (Fin r)) : X.Opens := nvOpen L (α i.down)

/-- The degree of the product chart of a nonempty set of indices. -/
def prodDeg (t : Finset (Fin r)) (ht : t.Nonempty) : ℕ :=
  (exists_prod_chart L α t ht).choose

/-- The product chart of a nonempty set of indices. -/
def prodSec (t : Finset (Fin r)) (ht : t.Nonempty) : powSections L (prodDeg L α t ht) :=
  (exists_prod_chart L α t ht).choose_spec.choose

/-- The degree of the product chart of `t` is `∑_{i ∈ t} dᵢ`. -/
theorem prodDeg_eq (t : Finset (Fin r)) (ht : t.Nonempty) : prodDeg L α t ht = ∑ i ∈ t, d i :=
  (exists_prod_chart L α t ht).choose_spec.choose_spec.1

/-- The product chart of `t` represents `∏_{i ∈ t} gᵢ` in the section ring. -/
theorem of_prodSec (t : Finset (Fin r)) (ht : t.Nonempty) :
    DirectSum.of (powSections L) (prodDeg L α t ht) (prodSec L α t ht) = ∏ i ∈ t, gen L α i :=
  (exists_prod_chart L α t ht).choose_spec.choose_spec.2.1

/-- The nonvanishing open of the product chart of `t` is `⋂_{i ∈ t} X_{αᵢ}`. -/
theorem nvOpen_prodSec (t : Finset (Fin r)) (ht : t.Nonempty) :
    nvOpen L (prodSec L α t ht) = ⨅ i ∈ t, nvOpen L (α i) :=
  (exists_prod_chart L α t ht).choose_spec.choose_spec.2.2

include hd in
/-- If every `dᵢ` is positive, the product chart of a nonempty `t` has positive degree. -/
theorem prodDeg_pos (t : Finset (Fin r)) (ht : t.Nonempty) : 0 < prodDeg L α t ht := by
  rw [prodDeg_eq]
  obtain ⟨i, hi⟩ := ht
  exact (hd i).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)

/-- A finite set of cardinality `p + 1` is nonempty. -/
theorem nonempty_of_card {p : ℕ} (t : {t : Finset (Fin r) // t.card = p + 1}) : t.1.Nonempty :=
  Finset.card_pos.1 (by rw [t.2]; omega)

/-- The intersection of the charts along a strictly increasing tuple is the nonvanishing open of
the product chart of its set of indices. -/
theorem inter_eq_nvOpen_prodSec {p : ℕ} (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p) :
    CechCochains.inter (X := TopCat.of X) (chartOpen L α) σ.1 =
      nvOpen L (prodSec L α (Stacks.LocalCohomology.ordIndexEquiv p σ).1
        (nonempty_of_card (Stacks.LocalCohomology.ordIndexEquiv p σ))) := by
  rw [nvOpen_prodSec]
  apply le_antisymm
  · refine le_iInf₂ fun i hi => ?_
    obtain ⟨k, hk⟩ := (Stacks.LocalCohomology.mem_cechTupleIndices ULift.down σ.1 i).1 hi
    exact (iInf_le _ k).trans (by rw [← hk])
  · exact le_iInf fun k => iInf₂_le (σ.1 k).down
      ((Stacks.LocalCohomology.mem_cechTupleIndices ULift.down σ.1 _).2 ⟨k, rfl⟩)

end Charts

/-! ### The ordered Čech cochains of `ℱ`, read in the Čech complex of `Γ_*(X, L, ℱ)` -/

section Cochains

variable {r : ℕ} {d : Fin r → ℕ} (hd : ∀ i, 0 < d i) (α : ∀ i, powSections L (d i))

open Stacks.LocalCohomology (ordIndexEquiv cechComponent)

/-- The lift of a section over the intersection of the charts along a strictly increasing tuple
into the Čech localization at its set of indices. -/
def tupleLift {p : ℕ} (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p) :
    Γ(F, CechCochains.inter (X := TopCat.of X) (chartOpen L α) σ.1) →+
      Cech.cechMod (gen L α) (twistModule F L) (ordIndexEquiv p σ).1 :=
  (chartLift L hL F (prodDeg_pos L hd α _ (nonempty_of_card (ordIndexEquiv p σ)))
      (prodSec L α _ (nonempty_of_card (ordIndexEquiv p σ)))
      (of_prodSec L α _ (nonempty_of_card (ordIndexEquiv p σ)))).comp
    (F.presheaf.map (eqToHom (inter_eq_nvOpen_prodSec L α σ).symm).op).hom

/-- Restricting along an equality of opens and then along its inverse is the identity. -/
private theorem presheaf_map_eqToHom_op_cancel (G : X.Modules) {U V : X.Opens} (h : U = V)
    (h' : V = U) (y : Γ(G, V)) :
    (G.presheaf.map (eqToHom h').op).hom ((G.presheaf.map (eqToHom h).op).hom y) = y := by
  subst h
  simp

/-- The lift `tupleLift` along a strictly increasing tuple is injective. -/
theorem tupleLift_injective {p : ℕ} (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p) :
    Function.Injective (tupleLift L hL F hd α σ) := by
  refine (chartLift_injective L hL F _ _ _).comp ?_
  intro y y' h
  simpa only [presheaf_map_eqToHom_op_cancel] using
    congrArg (F.presheaf.map (eqToHom (inter_eq_nvOpen_prodSec L α σ)).op).hom h

/-- The image of `tupleLift` along a strictly increasing tuple is the degree-zero part of the
localization at the product of the `gᵢ` over its set of indices. -/
theorem mem_range_tupleLift {p : ℕ} (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p)
    (z : Cech.cechMod (gen L α) (twistModule F L) (ordIndexEquiv p σ).1) :
    z ∈ (tupleLift L hL F hd α σ).range ↔
      z ∈ Stacks.GradedLocalization.gradedPiece (grading L)
        (Stacks.TwistedSections.moduleGrading F L) (∏ i ∈ (ordIndexEquiv p σ).1, gen L α i) 0 := by
  rw [← mem_range_chartLift L hL F (prodDeg_pos L hd α _ (nonempty_of_card (ordIndexEquiv p σ)))
    (prodSec L α _ (nonempty_of_card (ordIndexEquiv p σ)))
    (of_prodSec L α _ (nonempty_of_card (ordIndexEquiv p σ)))]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨F.presheaf.map (eqToHom (inter_eq_nvOpen_prodSec L α σ)).op y, ?_⟩
    simp only [tupleLift, AddMonoidHom.coe_comp, Function.comp_apply]
    congr 1
    exact presheaf_map_eqToHom_op_cancel F _ _ y

/-- **The lift along a face of a tuple.** Restricting from the intersection along a face of a
strictly increasing tuple to the intersection along the tuple, and lifting, is the transition map
of the Čech complex applied to the lift. -/
theorem tupleLift_face {p : ℕ} (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) (p + 1))
    (j : Fin (p + 2))
    (y : Γ(F, CechCochains.inter (X := TopCat.of X) (chartOpen L α) (σ.1 ∘ j.succAbove))) :
    tupleLift L hL F hd α σ
        (CechCochains.restr (Stacks.Cohomology.CechSheaf.abSections F)
          (CechCochains.inter_le_omit (chartOpen L α) σ.1 j) y) =
      Cech.cechι (gen L α) (twistModule F L)
        (Stacks.LocalCohomology.ordIndexEquiv_omit_subset σ j)
        (tupleLift L hL F hd α ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩ y) := by
  classical
  set σj : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p :=
    ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩
  set S := (ordIndexEquiv p σj).1
  set T := (ordIndexEquiv (p + 1) σ).1
  have hST : S ⊆ T := Stacks.LocalCohomology.ordIndexEquiv_omit_subset σ j
  have hS := nonempty_of_card (ordIndexEquiv p σj)
  have hT := nonempty_of_card (ordIndexEquiv (p + 1) σ)
  have hle : nvOpen L (prodSec L α T hT) ≤ nvOpen L (prodSec L α S hS) := by
    rw [← inter_eq_nvOpen_prodSec L α σ, ← inter_eq_nvOpen_prodSec L α σj]
    exact CechCochains.inter_le_omit (chartOpen L α) σ.1 j
  have hh : (∏ i ∈ T \ S, gen L α i) ∈ grading L (∑ i ∈ T \ S, d i) :=
    SetLike.prod_mem_graded (grading L) d (gen L α)
      (fun i _ => Stacks.ExternalGrading.of_mem_summand (d i) (α i))
  have hj : prodDeg L α S hS + ∑ i ∈ T \ S, d i = prodDeg L α T hT := by
    rw [prodDeg_eq, prodDeg_eq, add_comm, Finset.sum_sdiff hST]
  have hxh : (∏ i ∈ S, gen L α i) * (∏ i ∈ T \ S, gen L α i) = ∏ i ∈ T, gen L α i :=
    (mul_comm _ _).trans (Finset.prod_sdiff hST)
  have key := chartLift_restrict L hL F (prodDeg_pos L hd α S hS) (prodDeg_pos L hd α T hT)
    (prodSec L α S hS) (prodSec L α T hT) (of_prodSec L α S hS) (of_prodSec L α T hT) hh hj hxh
    (homOfLE hle) (Cech.cechι (gen L α) (twistModule F L) hST).toAddMonoidHom
    (fun m n => Cech.cechι_mk_pow (gen L α) hST m n)
    (F.presheaf.map (eqToHom (inter_eq_nvOpen_prodSec L α σj).symm).op y)
  refine Eq.trans ?_ key
  change chartLift L hL F _ _ _ (F.presheaf.map _ (F.presheaf.map _ y)) =
    chartLift L hL F _ _ _ (F.presheaf.map _ (F.presheaf.map _ y))
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **The ordered Čech cochains of `ℱ`, read in the Čech complex of `Γ_*(X, L, ℱ)`.** A cochain is
sent to the sum of the lifts of its values, each placed in the summand of
`C^{p+1}(g; Γ_*(X, L, ℱ))` indexed by the set of indices of its tuple. -/
def ordCochainLift (p : ℕ) :
    CechCochains.OrdCochain (X := TopCat.of X) (chartOpen L α)
        (Stacks.Cohomology.CechSheaf.abSections F) p →+
      Cech.cechTerm (gen L α) (twistModule F L) (p + 1) :=
  ∑ σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p,
    ((DirectSum.lof (sectionRing L) {t : Finset (Fin r) // t.card = p + 1}
      (fun t => Cech.cechMod (gen L α) (twistModule F L) t.1)
        (ordIndexEquiv p σ)).toAddMonoidHom.comp
      ((tupleLift L hL F hd α σ).comp
        (Pi.evalAddMonoidHom (fun σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p =>
          Γ(F, CechCochains.inter (X := TopCat.of X) (chartOpen L α) σ.1)) σ)))

/-- The value of `ordCochainLift` on a cochain `s` is the sum over strictly increasing tuples `σ`
of `tupleLift (s σ)`, placed in the summand indexed by the set of indices of `σ`. -/
theorem ordCochainLift_apply (p : ℕ)
    (s : CechCochains.OrdCochain (X := TopCat.of X) (chartOpen L α)
      (Stacks.Cohomology.CechSheaf.abSections F) p) :
    ordCochainLift L hL F hd α p s = ∑ σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p,
      DirectSum.lof (sectionRing L) {t : Finset (Fin r) // t.card = p + 1}
        (fun t => Cech.cechMod (gen L α) (twistModule F L) t.1) (ordIndexEquiv p σ)
        (tupleLift L hL F hd α σ (s σ)) := by
  simp [ordCochainLift]
  rfl

/-- The component of the lift at the set of indices of a tuple is the lift of the value of the
cochain at that tuple. -/
theorem cechComponent_ordCochainLift (p : ℕ)
    (s : CechCochains.OrdCochain (X := TopCat.of X) (chartOpen L α)
      (Stacks.Cohomology.CechSheaf.abSections F) p)
    (σ₀ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p) :
    cechComponent (gen L α) (ModuleCat.of (sectionRing L) (twistModule F L)) (p + 1)
        (ordIndexEquiv p σ₀) (ordCochainLift L hL F hd α p s) =
      tupleLift L hL F hd α σ₀ (s σ₀) :=
  (congrArg _ (ordCochainLift_apply L hL F hd α p s)).trans <|
    (map_sum (cechComponent (gen L α) (ModuleCat.of (sectionRing L) (twistModule F L)) (p + 1)
      (ordIndexEquiv p σ₀)) _ Finset.univ).trans
    ((Finset.sum_eq_single_of_mem σ₀ (Finset.mem_univ _) (fun _ _ hτ =>
      Stacks.LocalCohomology.cechComponent_lof_of_ne _ _ _ _
        (fun h => hτ ((ordIndexEquiv p).injective (Subtype.ext h))) _)).trans
      ((Stacks.LocalCohomology.cechComponent_lof_of_eq _ _ _ _ rfl _).trans
        (Stacks.LocalCohomology.cechι_le_refl_apply _ _ _)))

/-- The map `ordCochainLift` is injective. -/
theorem ordCochainLift_injective (p : ℕ) : Function.Injective (ordCochainLift L hL F hd α p) := by
  intro s s' h
  funext σ
  apply tupleLift_injective L hL F hd α σ
  rw [← cechComponent_ordCochainLift, ← cechComponent_ordCochainLift, h]

/-- **The image of the lift is the degree-zero part of the Čech term.** -/
theorem mem_range_ordCochainLift (p : ℕ) (z : Cech.cechTerm (gen L α) (twistModule F L) (p + 1)) :
    z ∈ (ordCochainLift L hL F hd α p).range ↔
      z ∈ Cech.gradedCechTerm (grading L) (Stacks.TwistedSections.moduleGrading F L)
        (gen L α) 0 (p + 1) := by
  rw [Cech.mem_gradedCechTerm]
  constructor
  · rintro ⟨s, rfl⟩ t
    obtain ⟨σ, rfl⟩ := (ordIndexEquiv p).surjective t
    have := cechComponent_ordCochainLift L hL F hd α p s σ
    change (ordCochainLift L hL F hd α p s) (ordIndexEquiv p σ) ∈ _
    rw [show (ordCochainLift L hL F hd α p s) (ordIndexEquiv p σ) =
      cechComponent (gen L α) (ModuleCat.of (sectionRing L) (twistModule F L)) (p + 1)
        (ordIndexEquiv p σ) (ordCochainLift L hL F hd α p s) from rfl, this]
    exact (mem_range_tupleLift L hL F hd α σ _).1 ⟨_, rfl⟩
  · intro hz
    choose y hy using fun σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p =>
      (mem_range_tupleLift L hL F hd α σ (z (ordIndexEquiv p σ))).2 (hz _)
    refine ⟨y, DirectSum.ext fun t => ?_⟩
    obtain ⟨σ, rfl⟩ := (ordIndexEquiv p).surjective t
    exact (cechComponent_ordCochainLift L hL F hd α p _ σ).trans (hy σ)

/-- **The lift commutes with the differentials.** -/
theorem ordCochainLift_ordD (p : ℕ)
    (s : CechCochains.OrdCochain (X := TopCat.of X) (chartOpen L α)
      (Stacks.Cohomology.CechSheaf.abSections F) p) :
    ordCochainLift L hL F hd α (p + 1)
        (CechCochains.ordD (chartOpen L α) (Stacks.Cohomology.CechSheaf.abSections F) p s) =
      Cech.cechD (gen L α) (twistModule F L) (p + 1) (ordCochainLift L hL F hd α p s) := by
  refine DirectSum.ext fun T => ?_
  obtain ⟨σ, rfl⟩ := (ordIndexEquiv (p + 1)).surjective T
  have hd' : CechCochains.ordD (chartOpen L α) (Stacks.Cohomology.CechSheaf.abSections F) p s σ =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr (Stacks.Cohomology.CechSheaf.abSections F)
          (CechCochains.inter_le_omit (chartOpen L α) σ.1 j)
          (s ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩) := rfl
  have h1 := cechComponent_ordCochainLift L hL F hd α (p + 1)
    (CechCochains.ordD (chartOpen L α) (Stacks.Cohomology.CechSheaf.abSections F) p s) σ
  have h2 := Stacks.LocalCohomology.cechComponent_cechD_ordIndexEquiv (gen L α)
    (ModuleCat.of (sectionRing L) (twistModule F L)) p (ordCochainLift L hL F hd α p s) σ
  have h3 : tupleLift L hL F hd α σ
      (CechCochains.ordD (chartOpen L α) (Stacks.Cohomology.CechSheaf.abSections F) p s σ) =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        Cech.cechι (gen L α) (twistModule F L)
          (Stacks.LocalCohomology.ordIndexEquiv_omit_subset σ j)
          (tupleLift L hL F hd α ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩
            (s ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩)) := by
    refine (congrArg (tupleLift L hL F hd α σ) hd').trans ?_
    refine (map_sum (tupleLift L hL F hd α σ) _ Finset.univ).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (map_zsmul (tupleLift L hL F hd α σ) _ _).trans ?_
    exact congrArg (fun z => ((-1 : ℤ) ^ (j : ℕ)) • z) (tupleLift_face L hL F hd α σ j _)
  refine h1.trans (h3.trans (Eq.trans ?_ h2.symm))
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cechComponent_ordCochainLift]

end Cochains

end Monoidal

end Stacks.SectionRingChartCech

end
