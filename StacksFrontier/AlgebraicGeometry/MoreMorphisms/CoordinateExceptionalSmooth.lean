module

public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupChartPresentation

/-!
# Smoothness of the exceptional divisor of the blowup of affine space along a coordinate subspace

Fix a commutative ring `R` and integers `m, n ≥ 0`. Write affine `(m + n)`-space over `R` as
`Spec A` with `A = R[x₁, …, x_m, y₁, …, y_n]`, the polynomial ring on `Fin m ⊕ Fin n`, and let
`Z = 𝔸^m_R ⟶ 𝔸^{m+n}_R` be the closed immersion setting the last `n` coordinates to zero. This
file proves the last assertion of Stacks Tag 0H1H: the exceptional divisor of the blowup of
`𝔸^{m+n}_R` along `Z` is smooth over `R`.

The source's argument is that on the `i`-th standard chart of the blowup — which is affine
`(m + n)`-space with coordinates `x₁, …, x_m, y_i, t_j` — the exceptional divisor is cut out by
the single equation `y_i = 0`, so that it is again an affine space, of dimension `m + n - 1`.
The chart statement is
`Stacks.MoreMorphisms.exists_coordinateBlowupChartPresentation`; what is added here is the
passage from the ideal of the chart to the closed subscheme it cuts out, and the fact that those
closed subschemes cover the exceptional divisor.

## Main definitions

* `Stacks.MoreMorphisms.dropVar` is the map of polynomial rings setting one variable to zero.
* `Stacks.IdealSheaf.subschemeRestrict` is the restriction of the closed subscheme cut out by an
  ideal sheaf to an open subscheme of the ambient scheme.
* `Stacks.MoreMorphisms.coordinateExceptionalChartι` is the `i`-th standard affine chart of the
  exceptional divisor of the coordinate blowup.

## Main results

* `Stacks.MoreMorphisms.exists_quotientSpanX_algEquiv`: the quotient of a polynomial ring by one
  of its variables is the polynomial ring on the remaining variables.
* `Stacks.IdealSheaf.exists_mem_range_subschemeRestrict_chart`: the affine charts of the
  restrictions of a closed subscheme to an affine open cover of the ambient scheme cover it.
* `Stacks.MoreMorphisms.coordinateExceptionalChartIdeal_top`: on the `i`-th standard chart of
  the blowup the exceptional divisor is cut out by the image of the ideal of the last `n`
  coordinates, which the chart presentation identifies with the single coordinate `y_i`.
* `Stacks.MoreMorphisms.chartQuotient_smooth`: the `i`-th standard chart of the exceptional
  divisor is affine `(m + n - 1)`-space over `R`.
* `Stacks.MoreMorphisms.exceptionalDivisor_smooth_of_pos` and
  `Stacks.MoreMorphisms.exceptionalDivisor_smooth`: the exceptional divisor of the coordinate
  blowup is smooth over `R`.

## Implementation notes

The chart of the exceptional divisor is assembled from two pieces of Mathlib's closed-subscheme
API. The restriction of `I.subscheme` to an open subscheme `f : V ⟶ X` is
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap` for the inverse-image ideal; it is an open
immersion because `AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_snd` exhibits it as the
second projection of the pullback of `f` along `I.subschemeι`. For `V` affine the subscheme of an
ideal sheaf is covered by the single affine `Spec (Γ(V, ⊤) / 𝒥(⊤))`, namely the member of
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeCover` at the top open, whose range is the
whole of the subscheme.

Identifying the ideal `𝒥(⊤)` is `Stacks.IdealSheaf.ideal_comap_top_of_isAffine`, applied to the
structure morphism of the chart over the ambient affine space; that morphism is `Spec` of
`Stacks.MoreMorphisms.coordinateBlowupChartStructureMap`, which is what
`Stacks.MoreMorphisms.coordinateBlowupChart_comp_blowUpToBase` records.

The coordinate ring of the chart is an affine blowup algebra — a subalgebra of a localization of
a polynomial ring — and its ring of global sections adds a structure sheaf on top of that, so
unification against those types is expensive. Every step that touches them is therefore either a
*generic* lemma, whose schemes and rings are variables
(`Stacks.IdealSheaf.subschemeRestrict_chart_comp`,
`Stacks.MoreMorphisms.smooth_quotient_of_ringEquiv_span_X`,
`Stacks.MoreMorphisms.smooth_quotient_map_of_bijective`), or a single application of one, split
into its own declaration. In particular the polynomial presentation of the chart is fed in with
the two halves of the structure map kept apart as `ρ₁` and `ρ₂`, so that no `RingHom.comp` has to
be unfolded against the chart's ring.

`Stacks.MoreMorphisms.exceptionalDivisor_smooth` carries the hypothesis `0 < n` that the source
carries; it is **not used**, and `Stacks.MoreMorphisms.exceptionalDivisor_smooth_of_pos` is the
same theorem without it. For `n = 0` the ideal sheaf of the centre is zero, the blowup is empty
and so is its exceptional divisor, which is how the covering statement discharges that case.

## References

* [Stacks Project, Tag 0H1H](https://stacks.math.columbia.edu/tag/0H1H)
* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial

universe u v

/-! ### The polynomial ring modulo one of its variables -/

namespace Stacks.MoreMorphisms

variable (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (v₀ : σ)

/-- The map of polynomial rings setting the variable `v₀` to zero, with the polynomial ring on
the remaining variables as its target. -/
public def dropVar : MvPolynomial σ R →ₐ[R] MvPolynomial {v : σ // v ≠ v₀} R :=
  aeval fun v ↦ if h : v = v₀ then 0 else X ⟨v, h⟩

/-- `dropVar` kills the dropped variable. -/
public theorem dropVar_X_self : dropVar R v₀ (X v₀) = 0 := by
  simp [dropVar]

/-- `dropVar` fixes every other variable. -/
public theorem dropVar_X_of_ne {v : σ} (h : v ≠ v₀) : dropVar R v₀ (X v) = X ⟨v, h⟩ := by
  simp [dropVar, h]

/-- `dropVar` fixes the constants. -/
public theorem dropVar_C (r : R) : dropVar R v₀ (C r) = C r := by
  rw [dropVar, aeval_C, algebraMap_eq]

/-- Reindexing along the inclusion of the remaining variables is a section of `dropVar`. -/
public theorem dropVar_rename_val (p : MvPolynomial {v : σ // v ≠ v₀} R) :
    dropVar R v₀ (rename Subtype.val p) = p := by
  have hfun : (fun v : σ ↦ if h : v = v₀ then (0 : MvPolynomial {v : σ // v ≠ v₀} R)
      else X ⟨v, h⟩) ∘ (Subtype.val : {v : σ // v ≠ v₀} → σ) = X := by
    funext w
    rw [Function.comp_apply, dif_neg w.2]
  rw [dropVar, aeval_rename, hfun]
  exact aeval_X_left_apply p

/-- `dropVar` is surjective. -/
public theorem dropVar_surjective : Function.Surjective (dropVar R v₀) :=
  fun p ↦ ⟨rename Subtype.val p, dropVar_rename_val R v₀ p⟩

/-- The idempotent endomorphism of the polynomial ring killing the variable `v₀`. -/
private def dropVarRetraction : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  (rename Subtype.val).comp (dropVar R v₀)

/-- The retraction fixes the constants. -/
private theorem dropVarRetraction_C (r : R) : dropVarRetraction R v₀ (C r) = C r := by
  rw [dropVarRetraction, AlgHom.comp_apply, dropVar_C, rename_C]

/-- The retraction kills the dropped variable. -/
private theorem dropVarRetraction_X_self : dropVarRetraction R v₀ (X v₀) = 0 := by
  rw [dropVarRetraction, AlgHom.comp_apply, dropVar_X_self, map_zero]

/-- The retraction fixes every other variable. -/
private theorem dropVarRetraction_X_of_ne {v : σ} (h : v ≠ v₀) :
    dropVarRetraction R v₀ (X v) = X v := by
  rw [dropVarRetraction, AlgHom.comp_apply, dropVar_X_of_ne R v₀ h, rename_X]

/-- Every polynomial agrees with its retraction modulo the dropped variable. -/
private theorem sub_dropVarRetraction_mem (p : MvPolynomial σ R) :
    p - dropVarRetraction R v₀ p ∈ Ideal.span {(X v₀ : MvPolynomial σ R)} := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [dropVarRetraction_C, sub_self]; exact Ideal.zero_mem _
  | add p q hp hq =>
    have hsplit : p + q - dropVarRetraction R v₀ (p + q) =
        (p - dropVarRetraction R v₀ p) + (q - dropVarRetraction R v₀ q) := by
      rw [map_add]; ring
    rw [hsplit]
    exact Ideal.add_mem _ hp hq
  | mul_X p w hp =>
    rcases eq_or_ne w v₀ with hw | hw
    · rw [hw]
      have hz : p * X v₀ - dropVarRetraction R v₀ (p * X v₀) = p * X v₀ := by
        rw [map_mul, dropVarRetraction_X_self, mul_zero, sub_zero]
      rw [hz]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · have hz : p * X w - dropVarRetraction R v₀ (p * X w) =
          (p - dropVarRetraction R v₀ p) * X w := by
        rw [map_mul, dropVarRetraction_X_of_ne R v₀ hw]; ring
      rw [hz]
      exact Ideal.mul_mem_right _ _ hp

/-- The kernel of `dropVar` is the ideal generated by the dropped variable. -/
public theorem ker_dropVar :
    RingHom.ker (dropVar R v₀) = Ideal.span {(X v₀ : MvPolynomial σ R)} := by
  refine le_antisymm (fun p hp ↦ ?_) (Ideal.span_le.2 ?_)
  · have h := sub_dropVarRetraction_mem R v₀ p
    rwa [dropVarRetraction, AlgHom.comp_apply, RingHom.mem_ker.1 hp, map_zero, sub_zero] at h
  · rintro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    simp [RingHom.mem_ker, dropVar_X_self]

omit [DecidableEq σ] in
/-- **The polynomial ring modulo one of its variables.** The quotient of `R[σ]` by the ideal
generated by the variable `v₀` is the polynomial ring on the remaining variables, compatibly
with the constants. -/
public theorem exists_quotientSpanX_algEquiv :
    ∃ E : (MvPolynomial σ R ⧸ Ideal.span {(X v₀ : MvPolynomial σ R)}) ≃ₐ[R]
        MvPolynomial {v : σ // v ≠ v₀} R,
      ∀ r : R, E (Ideal.Quotient.mk _ (C r)) = C r := by
  classical
  refine ⟨(Ideal.quotientEquivAlgOfEq R (ker_dropVar R v₀).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (dropVar_surjective R v₀)), fun r ↦ ?_⟩
  rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk, dropVar_C]

end Stacks.MoreMorphisms

/-! ### Restricting a closed subscheme to an open of the ambient scheme -/

namespace Stacks.IdealSheaf

open Scheme.IdealSheafData

variable {X V : Scheme.{u}} (J : X.IdealSheafData) (f : V ⟶ X) [IsOpenImmersion f]

/-- The restriction of the closed subscheme cut out by `J` to the open subscheme `f`: the closed
subscheme of `V` cut out by the inverse image of `J`, mapping to the one cut out by `J`. -/
public abbrev subschemeRestrict : (J.comap f).subscheme ⟶ J.subscheme :=
  subschemeMap (J.comap f) J f (J.le_map_comap f)

omit [IsOpenImmersion f] in
/-- The restriction is the second projection of the pullback, read through the comparison
isomorphism of the inverse-image subscheme with that pullback. -/
private theorem comapIso_inv_subschemeRestrict :
    (J.comapIso f).inv ≫ subschemeRestrict J f =
      CategoryTheory.Limits.pullback.snd f J.subschemeι := by
  rw [subschemeRestrict, ← comapIso_hom_snd J f, Iso.inv_hom_id_assoc]

/-- The restriction of a closed subscheme to an open subscheme is an open immersion. -/
public instance isOpenImmersion_subschemeRestrict :
    IsOpenImmersion (subschemeRestrict J f) := by
  have h : subschemeRestrict J f =
      (J.comapIso f).hom ≫ CategoryTheory.Limits.pullback.snd f J.subschemeι :=
    (comapIso_hom_snd J f).symm
  rw [h]
  infer_instance

omit [IsOpenImmersion f] in
/-- A point of the closed subscheme cut out by `J` which lies in the open subscheme `f` is in
the range of the restriction of the subscheme to `f`. -/
public theorem exists_preimage_subschemeRestrict (z : J.subscheme) (w : V)
    (hw : f w = J.subschemeι z) : ∃ p, subschemeRestrict J f p = z := by
  obtain ⟨p, -, hp⟩ := Scheme.exists_preimage_of_isPullback
    (CategoryTheory.IsPullback.of_hasPullback f J.subschemeι) w z hw
  refine ⟨(J.comapIso f).inv p, ?_⟩
  rw [← Scheme.Hom.comp_apply, comapIso_inv_subschemeRestrict]
  exact hp

/-! ### The closed subscheme of an ideal sheaf on an affine scheme -/

variable {W : Scheme.{u}} [IsAffine W] (K : W.IdealSheafData)

/-- The single affine chart of the closed subscheme cut out by an ideal sheaf on an affine
scheme is an open immersion. -/
public instance isOpenImmersion_subschemeCover_top :
    IsOpenImmersion (K.subschemeCover.f ⟨⊤, isAffineOpen_top W⟩) :=
  K.subschemeCover.map_prop _

/-- For an affine scheme the closed subscheme cut out by an ideal sheaf is covered by the single
affine `Spec (Γ(W, ⊤) / K(⊤))`. -/
public theorem exists_preimage_subschemeCover_top (z : K.subscheme) :
    ∃ q, K.subschemeCover.f ⟨⊤, isAffineOpen_top W⟩ q = z := by
  have hz : z ∈ (K.subschemeCover.f ⟨⊤, isAffineOpen_top W⟩).opensRange := by
    rw [opensRange_subschemeCover_map K ⟨⊤, isAffineOpen_top W⟩]
    trivial
  exact hz

/-- That single affine chart, composed with the closed immersion into `W`, is `Spec` of the
quotient map. -/
public theorem subschemeCover_top_comp_subschemeι :
    K.subschemeCover.f ⟨⊤, isAffineOpen_top W⟩ ≫ K.subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (K.ideal ⟨⊤, isAffineOpen_top W⟩))) ≫
        (isAffineOpen_top W).fromSpec := by
  rw [subschemeCover_map_subschemeι, glueDataObjι_ι]

/-- **The single affine chart of the restriction of a closed subscheme to an affine open.** The
chart of the restricted closed subscheme, composed with the closed immersion and a morphism `g`
out of the ambient scheme, is `Spec` of the quotient map followed by the morphism `k` that the
affine open induces. -/
public theorem subschemeRestrict_chart_comp {X Y : Scheme.{u}} (J : X.IdealSheafData)
    (f : W ⟶ X) [IsOpenImmersion f] (g : X ⟶ Y) {k : Spec Γ(W, ⊤) ⟶ Y}
    (hk : (isAffineOpen_top W).fromSpec ≫ f ≫ g = k) :
    (J.comap f).subschemeCover.f ⟨⊤, isAffineOpen_top W⟩ ≫
        subschemeRestrict J f ≫ J.subschemeι ≫ g =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((J.comap f).ideal ⟨⊤, isAffineOpen_top W⟩))) ≫ k := by
  have e1 : subschemeRestrict J f ≫ J.subschemeι = (J.comap f).subschemeι ≫ f :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have e3 : (J.comap f).subschemeCover.f ⟨⊤, isAffineOpen_top W⟩ ≫
        subschemeRestrict J f ≫ J.subschemeι ≫ g =
      ((J.comap f).subschemeCover.f ⟨⊤, isAffineOpen_top W⟩ ≫
        (J.comap f).subschemeι) ≫ f ≫ g := by
    rw [reassoc_of% e1, ← Category.assoc]
  refine e3.trans ?_
  rw [subschemeCover_top_comp_subschemeι (J.comap f)]
  exact (Category.assoc _ _ _).trans (congrArg (fun t ↦ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk ((J.comap f).ideal ⟨⊤, isAffineOpen_top W⟩))) ≫ t) hk)

/-- The chart of a restricted closed subscheme is an open immersion into the closed
subscheme. -/
public instance isOpenImmersion_subschemeCover_restrict {X : Scheme.{u}}
    (J : X.IdealSheafData) (f : W ⟶ X) [IsOpenImmersion f] :
    IsOpenImmersion ((J.comap f).subschemeCover.f ⟨⊤, isAffineOpen_top W⟩ ≫
      subschemeRestrict J f) :=
  IsOpenImmersion.comp _ _

/-- **The charts of the restricted closed subschemes cover the closed subscheme.** -/
public theorem exists_mem_range_subschemeRestrict_chart {X : Scheme.{u}} (J : X.IdealSheafData)
    {ι : Type*} (V : ι → Scheme.{u}) [∀ a, IsAffine (V a)] (q : ∀ a, V a ⟶ X)
    [∀ a, IsOpenImmersion (q a)] (hcov : ∀ x : X, ∃ (a : ι) (w : V a), q a w = x)
    (z : J.subscheme) :
    ∃ (a : ι) (p : _), ((J.comap (q a)).subschemeCover.f ⟨⊤, isAffineOpen_top (V a)⟩ ≫
      subschemeRestrict J (q a)) p = z := by
  obtain ⟨a, w, hw⟩ := hcov (J.subschemeι z)
  obtain ⟨y, hy⟩ := exists_preimage_subschemeRestrict J (q a) z w hw
  obtain ⟨p, hp⟩ := exists_preimage_subschemeCover_top (J.comap (q a)) y
  exact ⟨a, p, by rw [Scheme.Hom.comp_apply, hp, hy]⟩

/-- The affine identification of the top open of the spectrum of a ring. -/
public theorem fromSpec_top_spec {A : CommRingCat.{u}} :
    (isAffineOpen_top (Spec A)).fromSpec = Spec.map (Scheme.ΓSpecIso A).inv := by
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

/-- A morphism out of an affine open of the spectrum of a ring, read through the affine
identification: if `f ≫ g` is `Spec` of a ring map `φ`, then precomposing with the affine
identification of the top open gives `Spec` of `φ` followed by that identification. -/
public theorem fromSpec_top_comp_spec {X : Scheme.{u}} {A B : CommRingCat.{u}}
    (f : Spec A ⟶ X) (g : X ⟶ Spec B) {φ : B ⟶ A} (hφ : f ≫ g = Spec.map φ) :
    (isAffineOpen_top (Spec A)).fromSpec ≫ f ≫ g =
      Spec.map (φ ≫ (Scheme.ΓSpecIso A).inv) := by
  rw [fromSpec_top_spec, hφ, ← Spec.map_comp]

end Stacks.IdealSheaf

/-! ### The standard charts of the exceptional divisor of the coordinate blowup -/

namespace Stacks.MoreMorphisms

variable (R : Type u) [CommRing R] (m n : ℕ) (i : Fin n)

/-- The `i`-th standard affine chart of the coordinate blowup, as an open subscheme of it. -/
public abbrev coordinateBlowupChart :
    Spec (.of (coordinateBlowupChartRing R m n i)) ⟶ blowUp (coordinateIdeal R m n) :=
  blowupChartι (coordinateIdeal R m n) (topAffineOpen R m n) (coordinateIdealSection R m n i)

/-- The structure morphism of the `i`-th standard chart of the coordinate blowup over the ambient
affine space is `Spec` of the chart's structure map. -/
public theorem coordinateBlowupChart_comp_blowUpToBase :
    coordinateBlowupChart R m n i ≫ blowUpToBase (coordinateIdeal R m n) =
      Spec.map (CommRingCat.ofHom (coordinateBlowupChartStructureMap R m n i)) := by
  rw [coordinateBlowupChart, blowupChartι_comp_blowUpToBase, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The ideal sheaf of the exceptional divisor of the coordinate blowup, restricted to the `i`-th
standard chart. -/
public abbrev coordinateExceptionalChartIdeal :
    (Spec (.of (coordinateBlowupChartRing R m n i))).IdealSheafData :=
  (exceptionalIdeal (coordinateIdeal R m n)).comap (coordinateBlowupChart R m n i)

/-- The identification of the coordinate ring with the global sections, read as a bare ring
homomorphism. -/
private theorem gammaEquiv_toRingHom :
    (gammaEquiv R m n : MvPolynomial (Fin m ⊕ Fin n) R →+* _) =
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m ⊕ Fin n) R))).inv.hom :=
  RingHom.ext fun _ ↦ rfl

/-- The equation of the exceptional divisor on the `i`-th standard chart: on global sections the
ideal of the restricted exceptional ideal sheaf is the image of the ideal of the last `n`
coordinates under the chart's structure map. -/
public theorem coordinateExceptionalChartIdeal_top :
    (coordinateExceptionalChartIdeal R m n i).ideal
        ⟨⊤, isAffineOpen_top (Spec (.of (coordinateBlowupChartRing R m n i)))⟩ =
      Ideal.map (Scheme.ΓSpecIso (.of (coordinateBlowupChartRing R m n i))).inv.hom
        (Ideal.map (coordinateBlowupChartStructureMap R m n i)
          (coordinateRingIdeal R m n)) := by
  have hcomp : coordinateExceptionalChartIdeal R m n i =
      (coordinateIdeal R m n).comap (Spec.map
        (CommRingCat.ofHom (coordinateBlowupChartStructureMap R m n i))) := by
    rw [coordinateExceptionalChartIdeal, ← coordinateBlowupChart_comp_blowUpToBase,
      Scheme.IdealSheafData.comap_comp]
  have key : (coordinateExceptionalChartIdeal R m n i).ideal
        ⟨⊤, isAffineOpen_top (Spec (.of (coordinateBlowupChartRing R m n i)))⟩ =
      Ideal.map (Spec.map (CommRingCat.ofHom
          (coordinateBlowupChartStructureMap R m n i))).appTop.hom
        ((coordinateIdeal R m n).ideal (topAffineOpen R m n)) :=
    (congrArg (fun K ↦ Scheme.IdealSheafData.ideal K
        ⟨⊤, isAffineOpen_top (Spec (.of (coordinateBlowupChartRing R m n i)))⟩) hcomp).trans
      (Stacks.IdealSheaf.ideal_comap_top_of_isAffine _ _)
  have hring : RingHom.comp
        (Scheme.ΓSpecIso (.of (coordinateBlowupChartRing R m n i))).inv.hom
        (coordinateBlowupChartStructureMap R m n i) =
      RingHom.comp
        (Spec.map (CommRingCat.ofHom
          (coordinateBlowupChartStructureMap R m n i))).appTop.hom
        (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m ⊕ Fin n) R))).inv.hom := by
    have h := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (coordinateBlowupChartStructureMap R m n i))
    have h' := congrArg CommRingCat.Hom.hom h
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using h'
  have hI : (coordinateIdeal R m n).ideal (topAffineOpen R m n) =
      Ideal.map (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m ⊕ Fin n) R))).inv.hom
        (coordinateRingIdeal R m n) := by
    rw [coordinateIdeal_ideal_top, gammaEquiv_toRingHom]
  exact key.trans ((congrArg (Ideal.map (Spec.map (CommRingCat.ofHom
      (coordinateBlowupChartStructureMap R m n i))).appTop.hom) hI).trans
    ((Ideal.map_map _ _).trans ((congrArg (fun φ ↦ Ideal.map φ (coordinateRingIdeal R m n))
      hring.symm).trans (Ideal.map_map _ _).symm)))

/-- The coordinate ring of the `i`-th standard affine chart of the exceptional divisor of the
coordinate blowup. -/
public abbrev coordinateExceptionalChartRing :=
  Γ(Spec (.of (coordinateBlowupChartRing R m n i)), ⊤) ⧸
    (coordinateExceptionalChartIdeal R m n i).ideal
      ⟨⊤, isAffineOpen_top (Spec (.of (coordinateBlowupChartRing R m n i)))⟩

/-- The `i`-th standard affine chart of the exceptional divisor of the coordinate blowup. -/
public abbrev coordinateExceptionalChartι :
    Spec (.of (coordinateExceptionalChartRing R m n i)) ⟶
      exceptionalDivisor (coordinateIdeal R m n) :=
  (coordinateExceptionalChartIdeal R m n i).subschemeCover.f
      ⟨⊤, isAffineOpen_top (Spec (.of (coordinateBlowupChartRing R m n i)))⟩ ≫
    Stacks.IdealSheaf.subschemeRestrict (exceptionalIdeal (coordinateIdeal R m n))
      (coordinateBlowupChart R m n i)

/-- The structure map of the `i`-th standard chart of the exceptional divisor over the base
ring. -/
public def coordinateExceptionalChartStructureMap :
    R →+* coordinateExceptionalChartRing R m n i :=
  (Ideal.Quotient.mk _).comp
    (((Scheme.ΓSpecIso (.of (coordinateBlowupChartRing R m n i))).inv.hom).comp
      ((coordinateBlowupChartStructureMap R m n i).comp
        (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R)))

/-- The structure morphism of the `i`-th standard chart of the exceptional divisor over the base
ring is `Spec` of `Stacks.MoreMorphisms.coordinateExceptionalChartStructureMap`. -/
public theorem coordinateExceptionalChartι_comp :
    coordinateExceptionalChartι R m n i ≫
        (exceptionalIdeal (coordinateIdeal R m n)).subschemeι ≫
        blowUpToBase (coordinateIdeal R m n) ≫
        Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R)) =
      Spec.map (CommRingCat.ofHom (coordinateExceptionalChartStructureMap R m n i)) := by
  have hφ : coordinateBlowupChart R m n i ≫ (blowUpToBase (coordinateIdeal R m n) ≫
        Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R))) =
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R) ≫
        CommRingCat.ofHom (coordinateBlowupChartStructureMap R m n i)) := by
    rw [← Category.assoc, coordinateBlowupChart_comp_blowUpToBase, ← Spec.map_comp]
  refine (Category.assoc _ _ _).trans
    ((Stacks.IdealSheaf.subschemeRestrict_chart_comp
      (exceptionalIdeal (coordinateIdeal R m n)) (coordinateBlowupChart R m n i)
      (blowUpToBase (coordinateIdeal R m n) ≫
        Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R)))
      (Stacks.IdealSheaf.fromSpec_top_comp_spec _ _ hφ)).trans ?_)
  exact (Spec.map_comp _ _).symm.trans
    (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)))

/-! ### Smoothness of the chart -/

/-- A quotient of a ring by an ideal that some isomorphism with a polynomial ring carries onto
the ideal of a single variable is a smooth algebra over the coefficient ring. -/
public theorem smooth_quotient_of_ringEquiv_span_X {Γ S : Type u} [CommRing Γ] [CommRing S]
    {τ : Type v} [DecidableEq τ] [Finite τ] (v₀ : τ) (Jt : Ideal Γ)
    (E : Γ ≃+* MvPolynomial τ R) (ρ₁ : R →+* S) (ρ₂ : S →+* Γ)
    (hE : Ideal.map (E : Γ →+* MvPolynomial τ R) Jt = Ideal.span {MvPolynomial.X v₀})
    (hρ : ∀ r, E (ρ₂ (ρ₁ r)) = MvPolynomial.C r) :
    ((Ideal.Quotient.mk Jt).comp (ρ₂.comp ρ₁)).Smooth := by
  obtain ⟨E₃, hE₃⟩ := exists_quotientSpanX_algEquiv R v₀
  refine smooth_of_mvPolynomial_ringEquiv {v : τ // v ≠ v₀} _
    ((Ideal.quotientEquiv Jt (Ideal.span {MvPolynomial.X v₀}) E hE.symm).trans
      E₃.toRingEquiv) fun r ↦ ?_
  rw [RingEquiv.trans_apply, RingHom.comp_apply, RingHom.comp_apply, Ideal.quotientEquiv_mk, hρ]
  exact hE₃ r

/-- Smoothness of a quotient is unchanged by transporting the ideal along an isomorphism of the
ring that is being divided. -/
public theorem smooth_quotient_map_of_bijective {Γ B : Type u} [CommRing Γ] [CommRing B]
    (ε : B →+* Γ) (hε : Function.Bijective ε) (K : Ideal B) (Jt : Ideal Γ)
    (hJ : Jt = Ideal.map ε K) (ρ₀ : R →+* B)
    (h : ((Ideal.Quotient.mk K).comp ρ₀).Smooth) :
    ((Ideal.Quotient.mk Jt).comp (ε.comp ρ₀)).Smooth := by
  subst hJ
  have hiso : (Ideal.Quotient.mk (Ideal.map ε K)).comp (ε.comp ρ₀) =
      (Ideal.quotientEquiv K (Ideal.map ε K) (RingEquiv.ofBijective ε hε)
        rfl : (B ⧸ K) →+* Γ ⧸ Ideal.map ε K).comp ((Ideal.Quotient.mk K).comp ρ₀) :=
    RingHom.ext fun _ ↦ rfl
  rw [hiso]
  exact RingHom.Smooth.comp h (RingHom.Smooth.of_bijective
    (Ideal.quotientEquiv K (Ideal.map ε K) (RingEquiv.ofBijective ε hε) rfl).bijective)

/-- The image in the `i`-th chart of the ideal sheaf of the centre, read on the coordinate ring
of the ambient affine space. -/
private theorem chartIdeal_map_eq :
    Ideal.map (algebraMap Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)
        (coordinateBlowupChartRing R m n i))
      ((coordinateIdeal R m n).ideal (topAffineOpen R m n)) =
      Ideal.map (coordinateBlowupChartStructureMap R m n i) (coordinateRingIdeal R m n) :=
  (congrArg (Ideal.map _) (coordinateIdeal_ideal_top R m n)).trans (Ideal.map_map _ _)

/-- **The `i`-th chart of the exceptional divisor is affine `(m + n - 1)`-space over `R`.** The
chart of the blowup is affine `(m + n)`-space and the exceptional divisor is cut out there by
the single coordinate `y_i`, so the quotient is a polynomial ring on the other coordinates. -/
public theorem chartQuotient_smooth :
    ((Ideal.Quotient.mk (Ideal.map (coordinateBlowupChartStructureMap R m n i)
        (coordinateRingIdeal R m n))).comp
      ((coordinateBlowupChartStructureMap R m n i).comp
        (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R))).Smooth := by
  obtain ⟨e, he, hideal⟩ := exists_coordinateBlowupChartPresentation R m n i
  rw [chartIdeal_map_eq] at hideal
  refine smooth_quotient_of_ringEquiv_span_X R (Sum.inr i : Fin m ⊕ Fin n) _ e _ _ hideal fun r ↦ ?_
  exact (he (C r)).trans ((MvPolynomial.algHom_C _ r).trans
    (DFunLike.congr_fun (MvPolynomial.algebraMap_eq R (Fin m ⊕ Fin n)) r))

/-- **The structure map of the `i`-th standard chart of the exceptional divisor is smooth.** -/
public theorem coordinateExceptionalChartStructureMap_smooth :
    (coordinateExceptionalChartStructureMap R m n i).Smooth :=
  smooth_quotient_map_of_bijective R
    (Scheme.ΓSpecIso (.of (coordinateBlowupChartRing R m n i))).inv.hom
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of (coordinateBlowupChartRing R m n i))).inv)
    _ _ (coordinateExceptionalChartIdeal_top R m n i) _ (chartQuotient_smooth R m n i)

/-- **The `i`-th standard chart of the exceptional divisor is smooth over the base ring.** -/
public theorem coordinateExceptionalChart_smooth :
    Smooth (coordinateExceptionalChartι R m n i ≫
      (exceptionalIdeal (coordinateIdeal R m n)).subschemeι ≫
      blowUpToBase (coordinateIdeal R m n) ≫
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R))) :=
  Eq.mpr (congrArg (fun t ↦ Smooth t) (coordinateExceptionalChartι_comp R m n i))
    (smooth_specMap _ (coordinateExceptionalChartStructureMap_smooth R m n i))

/-- The `i`-th standard chart of the exceptional divisor is an open immersion. -/
public instance isOpenImmersion_coordinateExceptionalChartι :
    IsOpenImmersion (coordinateExceptionalChartι R m n i) :=
  Stacks.IdealSheaf.isOpenImmersion_subschemeCover_restrict _ _

/-- The standard charts of the exceptional divisor of the coordinate blowup cover it. -/
public theorem exists_mem_range_coordinateExceptionalChart
    (z : exceptionalDivisor (coordinateIdeal R m n)) :
    ∃ (i : Fin n) (q : _), coordinateExceptionalChartι R m n i q = z :=
  Stacks.IdealSheaf.exists_mem_range_subschemeRestrict_chart
    (exceptionalIdeal (coordinateIdeal R m n)) _ (fun i ↦ coordinateBlowupChart R m n i)
    (exists_mem_range_coordinateBlowupChart R m n) z

/-- The exceptional divisor of the blowup of affine `(m + n)`-space along the coordinate affine
`m`-subspace is smooth over the base ring. No positivity hypothesis
on `n` is needed: for `n = 0` the ideal sheaf of the centre is zero and the blowup, hence also
its exceptional divisor, is empty. -/
public theorem exceptionalDivisor_smooth_of_pos :
    Smooth ((exceptionalIdeal (coordinateIdeal R m n)).subschemeι ≫
      blowUpToBase (coordinateIdeal R m n) ≫
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R))) := by
  have _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth)
    (𝒰 := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin n) _
      (fun i ↦ coordinateExceptionalChartι R m n i)
      (exists_mem_range_coordinateExceptionalChart R m n)) fun i ↦ ?_
  exact coordinateExceptionalChart_smooth R m n i

/-- The exceptional divisor of the blowup of affine `(m + n)`-space along the coordinate affine
`m`-subspace is smooth over the base ring.

The hypothesis `0 < n` is the one the source carries and is not used; see
`Stacks.MoreMorphisms.exceptionalDivisor_smooth_of_pos` for the same theorem without it. -/
@[stacks 0H1H "smoothness of the exceptional divisor"]
public theorem exceptionalDivisor_smooth (_hn : 0 < n) :
    Smooth ((exceptionalIdeal (coordinateIdeal R m n)).subschemeι ≫
      blowUpToBase (coordinateIdeal R m n) ≫
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin m ⊕ Fin n) R))) :=
  exceptionalDivisor_smooth_of_pos R m n

end Stacks.MoreMorphisms

end
