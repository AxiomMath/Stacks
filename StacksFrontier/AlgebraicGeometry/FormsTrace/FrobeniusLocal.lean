module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BigSiteNotExact
public import StacksFrontier.AlgebraicGeometry.FormsTrace.FrobeniusChart
public import StacksFrontier.AlgebraicGeometry.FormsTrace.RelativeTrace
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent
public import StacksFrontier.RingTheory.FormsTrace.FrobeniusTrace
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeUniversalHomeomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace on forms of the relative Frobenius, on framed charts

Let `S` be a scheme in characteristic `p`, `X` an `S`-scheme smooth of relative dimension `d`, and
`F : X → X^{(p)}` its relative Frobenius, which is finite syntomic. This file shows that the opens
`U` of `X^{(p)}` over which the trace on relative forms of Stacks, Proposition 0FLC (3),
`Θ_{X/X^{(p)}} : F_*Ω^•_{X/S} → Ω^•_{X^{(p)}/S}`, is computed by a framed algebra on which it
vanishes outside degree `d` and is surjective in degree `d`, form a basis of the topology.

The universal case is the endomorphism `x_i ↦ x_i ^ p` of `Spec ℤ[x_1, …, x_d]`
(`AlgebraicGeometry.specExpand`): on a framed open `O` of it, the sections are torsion free and
`Θ(x^{p-1} dx₁ ∧ ⋯ ∧ dx_d) = dy₁ ∧ ⋯ ∧ dy_d` (`AlgebraicGeometry.frameTrace_specExpand`). Locally
`F` is a base change of the universal case along an étale chart
(`AlgebraicGeometry.exists_isPullback_relativeFrobenius_affineSpace`), which transports this value
and gives the forms of `X^{(p)}` the basis `dy_i`; the ring-level statements of
`StacksFrontier.RingTheory.FormsTrace.FrobeniusTrace` then apply.

## Main results

* `AlgebraicGeometry.frameTrace_specExpand`: the universal value.
* `AlgebraicGeometry.exists_basis_kaehler_of_etale_chart`: étale coordinates give a basis of the
  differentials over every affine open of the chart.
* `AlgebraicGeometry.isPushout_app_of_isPullback`: the rings of functions over a chart of a
  cartesian square form a pushout.
* `AlgebraicGeometry.isFinite_relativeFrobenius`, `AlgebraicGeometry.syntomic_relativeFrobenius`:
  the relative Frobenius is finite syntomic.
* `AlgebraicGeometry.exists_relFramedOpen_relativeFrobenius`: the good framed charts.

## References

* [Stacks Project, Tag 0FW2](https://stacks.math.columbia.edu/tag/0FW2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite KaehlerDifferential exteriorPower
    TopologicalSpace
open Stacks.FormsTrace Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### The universal Frobenius on a framed open -/

section Universal

variable (d : ℕ)

/-- The polynomial ring `ℤ[x_1, …, x_d]` of the universal Frobenius (with `ℤ` lifted to the
universe `u`). -/
abbrev UnivRing : Type u := MvPolynomial (ULift.{u} (Fin d)) (ULift.{u} ℤ)

/-- The coordinate `x_i` on an open `O` of `Spec ℤ[x_1, …, x_d]`. -/
def specCoord (O : (Spec (.of (UnivRing.{u} d))).Opens) (i : Fin d) :
    Γ(Spec (.of (UnivRing.{u} d)), O) :=
  (Spec (.of (UnivRing.{u} d))).presheaf.map (homOfLE le_top).op
    ((Scheme.ΓSpecIso (.of (UnivRing.{u} d))).inv (MvPolynomial.X (ULift.up i)))

variable {d} (p : ℕ)

/-- The universal Frobenius raises the coordinates to their `p`-th powers. -/
theorem specExpand_app_specCoord (O : (Spec (.of (UnivRing.{u} d))).Opens) (i : Fin d) :
    (specExpand (ULift.{u} (Fin d)) p).app O (specCoord d O i) =
      specCoord d (specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O) i ^ p := by
  have h1 := congrArg (fun φ => φ ((Scheme.ΓSpecIso (.of (UnivRing.{u} d))).inv
    (MvPolynomial.X (ULift.up i)))) ((specExpand (ULift.{u} (Fin d)) p).naturality
      (homOfLE (le_top : O ≤ ⊤)).op)
  have h2 := congrArg (fun φ => φ (MvPolynomial.X (ULift.up i)))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (MvPolynomial.expand (σ := ULift.{u} (Fin d)) (R := ULift.{u} ℤ) p).toRingHom))
  change (Scheme.ΓSpecIso (.of (UnivRing.{u} d))).inv
      (MvPolynomial.expand p (MvPolynomial.X (ULift.up i))) =
    (specExpand (ULift.{u} (Fin d)) p).appTop
      ((Scheme.ΓSpecIso (.of (UnivRing.{u} d))).inv (MvPolynomial.X (ULift.up i))) at h2
  rw [MvPolynomial.expand_X, map_pow] at h2
  change (specExpand (ULift.{u} (Fin d)) p).app O ((Spec (.of (UnivRing.{u} d))).presheaf.map
      (homOfLE le_top).op _) = _ at h1
  rw [specCoord, h1]
  change (Spec (.of (UnivRing.{u} d))).presheaf.map _
      ((specExpand (ULift.{u} (Fin d)) p).appTop _) = _
  rw [← h2, map_pow]
  rfl

/-- `ℤ` lifted to any universe is a domain. -/
alias isDomain_uLift_int := AssociatedModuleNotExact.isDomain_uliftInt

/-- **The universal value of the trace on `x^{p-1} dx`.** On a nonempty framed open `O` of
`Spec ℤ[x_1, …, x_d]` for the universal Frobenius `x_i ↦ x_i ^ p`, the trace on forms sends
`x₁^{p-1} ⋯ x_d^{p-1} dx₁ ∧ ⋯ ∧ dx_d` to `dy₁ ∧ ⋯ ∧ dy_d`, where `y_i = x_i ^ p` are the
coordinates of the target. The sections over `O` form a domain in which `p^d ≠ 0`, the forms of
`O` are free, and the sections over the preimage are free of rank `p^d`. -/
theorem frameTrace_specExpand (hp : p ≠ 0) {O : (Spec (.of (UnivRing.{u} d))).Opens}
    (hO : IsFramedOpen (specExpand (ULift.{u} (Fin d)) p) O) [Nonempty O] :
    letI := ((specExpand (ULift.{u} (Fin d)) p).app O).hom.toAlgebra
    frameTrace Γ(Spec (.of (UnivRing.{u} d)), O)
        Γ(Spec (.of (UnivRing.{u} d)), specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O) d
        ((∏ i, specCoord d (specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O) i ^ (p - 1)) •
          ιMulti _ d (fun i => D ℤ _ (specCoord d (specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O) i))) =
      ιMulti _ d (fun i => D ℤ _ (specCoord d O i)) := by
  let := ((specExpand (ULift.{u} (Fin d)) p).app O).hom.toAlgebra
  have : IsAffine O.toScheme := hO.1
  have happ := hasFiniteBasis_app_of_morphismRestrict (specExpand (ULift.{u} (Fin d)) p) O _
    (HasFiniteBasis.of_isPullback_appTop
      (isPullback_morphismRestrict (specExpand (ULift.{u} (Fin d)) p) O).flip _
      (hasFiniteBasis_specExpand_appTop (ULift.{u} (Fin d)) p hp))
  rw [Fintype.card_ulift, Fintype.card_fin] at happ
  obtain ⟨b⟩ := happ
  have := Module.Finite.of_basis b
  have := Module.Free.of_basis b
  have := isDomain_uLift_int.{u}
  -- the sections over `O` form a domain in which `p ^ d ≠ 0`
  have hne : (((p ^ d : ℕ)) : Γ(Spec (.of (UnivRing.{u} d)), O)) ≠ 0 := by
    intro h
    have hinj := map_injective_of_isIntegral (Spec (.of (UnivRing.{u} d)))
      (homOfLE (le_top : O ≤ ⊤))
    have h0 : (((p ^ d : ℕ)) : UnivRing.{u} d) = 0 := by
      apply (Scheme.ΓSpecIso (.of (UnivRing.{u} d))).commRingCatIsoToRingEquiv.symm.injective
      apply hinj
      simpa only [map_natCast, map_zero] using h
    have h1 := congrArg (fun r => ULift.ringEquiv (MvPolynomial.eval 0 r)) h0
    simp only [map_natCast, map_zero] at h1
    exact pow_ne_zero d hp (by exact_mod_cast h1)
  -- the forms of `O` are free
  let φ₀ : MvPolynomial (ULift.{u} (Fin d)) ℤ →+* Γ(Spec (.of (UnivRing.{u} d)), O) :=
    ((Spec (.of (UnivRing.{u} d))).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom.comp
      ((Scheme.ΓSpecIso (.of (UnivRing.{u} d))).inv.hom.comp
        (MvPolynomial.mapEquiv (ULift.{u} (Fin d)) ULift.ringEquiv.symm).toRingHom)
  let φ : MvPolynomial (ULift.{u} (Fin d)) ℤ →ₐ[ℤ] Γ(Spec (.of (UnivRing.{u} d)), O) :=
    ⟨φ₀, fun r => by simp⟩
  have hres : ((Spec (.of (UnivRing.{u} d))).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom.Etale
      := by
    have h := HasRingHomProperty.appLE (P := @Etale) (f := 𝟙 (Spec (.of (UnivRing.{u} d))))
      inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨O, hO.1⟩ le_top
    simpa [Scheme.Hom.appLE] using h
  have e1 : (MvPolynomial.mapEquiv (ULift.{u} (Fin d))
      (ULift.ringEquiv.{0, u} (R := ℤ)).symm).toRingHom.Etale :=
    RingHom.Etale.of_bijective (RingEquiv.bijective _)
  have e2 : (Scheme.ΓSpecIso (.of (UnivRing.{u} d))).inv.hom.Etale :=
    RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have hφ₀ : φ₀.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ e1 e2) hres
  have hbΩ := exists_basis_kaehler_of_etale (Λ := ℤ)
    (A := Γ(Spec (.of (UnivRing.{u} d)), O)) (ι := ULift.{u} (Fin d)) φ hφ₀
  have htr : trace Γ(Spec (.of (UnivRing.{u} d)), O)
      Γ(Spec (.of (UnivRing.{u} d)), specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O) 1 =
      ((p ^ d : ℕ) : Γ(Spec (.of (UnivRing.{u} d)), O)) := by
    rw [trace_one_of_basis b, Fintype.card_fin]
  have htors : ∀ ω : ⋀[Γ(Spec (.of (UnivRing.{u} d)), O)]^d
      Ω[Γ(Spec (.of (UnivRing.{u} d)), O)⁄ℤ],
      ((p ^ d : ℕ) : Γ(Spec (.of (UnivRing.{u} d)), O)) • ω = 0 → ω = 0 := fun ω hω =>
    eq_zero_of_natCast_smul_exteriorPower (hbΩ.choose.reindex Equiv.ulift) hne ω hω
  exact frameTrace_prod_pow_smul_ιMulti_D (A₀ := Γ(Spec (.of (UnivRing.{u} d)), O))
    (B₀ := Γ(Spec (.of (UnivRing.{u} d)), specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O))
    (framed_or_subsingleton_of_isFramedOpen _ hO) (specCoord d O)
    (specCoord d (specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O))
    (fun i => specExpand_app_specCoord p O i) htr htors

end Universal

/-! ### Charts -/

section Charts

/-- Every open lies in the preimage of the whole scheme, as an inequality of opens stated with the
preimage itself (and not only up to definitional unfolding). -/
theorem Scheme.Hom.le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) :
    U ≤ f ⁻¹ᵁ ⊤ :=
  le_top.trans_eq (Scheme.Hom.preimage_top f).symm

variable {T S : Scheme.{u}} (g : T ⟶ S) {V : S.Opens} {W : T.Opens}

/-- An open of the chart `W`, seen in `T`, lies over `V`. -/
theorem image_le_preimage_of_le (hWV : W ≤ g ⁻¹ᵁ V) (U₀ : W.toScheme.Opens) :
    W.ι ''ᵁ U₀ ≤ g ⁻¹ᵁ V :=
  (W.ι_image_le U₀).trans hWV

/-- Sections of a composite over `U₀`, from `⊤`, factor through the sections of the second map. -/
private theorem comp_appLE_top {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U₀ : X.Opens) :
    (f ≫ g).appLE ⊤ U₀ ((f ≫ g).le_preimage_top U₀) =
      g.appTop ≫ f.appLE ⊤ U₀ (f.le_preimage_top U₀) := by
  rw [Scheme.Hom.comp_appLE]
  rfl

/-- **Étale coordinates give a basis of the differentials.** Let `α : W → 𝔸ⁿ_V` be an étale
`V`-morphism from an open `W` of `T` lying over an affine open `V` of `S`. On every affine open
`U₀` of `W`, the differentials of `Γ(T, U₀)` over `Γ(S, V)` are free on the differentials of the
coordinates `α^* x_i` (transported to `T` along `Γ(T, U₀) ≅ Γ(W, U₀)`). -/
@[sga "1 II 4.8" "Necessity direction", sga "7 XVI 1.3" "partial"]
theorem exists_basis_kaehler_of_etale_chart (hWV : W ≤ g ⁻¹ᵁ V) (hV : IsAffineOpen V)
    {n : Type u} (α : W.toScheme ⟶ 𝔸(n; V.toScheme)) [Etale α]
    (hα : α ≫ 𝔸(n; V.toScheme) ↘ V.toScheme = g.resLE V W hWV) {U₀ : W.toScheme.Opens}
    (hU₀ : IsAffineOpen U₀) :
    letI := (g.appLE V (W.ι ''ᵁ U₀) (image_le_preimage_of_le g hWV U₀)).hom.toAlgebra
    ∃ b : Module.Basis n Γ(T, W.ι ''ᵁ U₀) Ω[Γ(T, W.ι ''ᵁ U₀)⁄Γ(S, V)], ∀ i,
      b i = D Γ(S, V) Γ(T, W.ι ''ᵁ U₀)
        ((W.ι.appIso U₀).inv (α.appLE ⊤ U₀ (α.le_preimage_top U₀) (AffineSpace.coord V.toScheme
            i))) := by
  let := (g.appLE V (W.ι ''ᵁ U₀) (image_le_preimage_of_le g hWV U₀)).hom.toAlgebra
  have : IsAffine V.toScheme := hV
  let jV := V.ι.appLE V ⊤ V.ι_preimage_self.ge
  let κ : Γ(S, V) →+* Γ(𝔸(n; V.toScheme), ⊤) :=
    (𝔸(n; V.toScheme) ↘ V.toScheme).appTop.hom.comp jV.hom
  let θ : MvPolynomial n Γ(S, V) →+* Γ(𝔸(n; V.toScheme), ⊤) :=
    MvPolynomial.eval₂Hom κ (AffineSpace.coord V.toScheme)
  let ψ : MvPolynomial n Γ(S, V) →+* Γ(T, W.ι ''ᵁ U₀) :=
    (W.ι.appIso U₀).inv.hom.comp ((α.appLE ⊤ U₀ (α.le_preimage_top U₀)).hom.comp θ)
  -- the constants: `α` lies over `V`
  have hα' : (α ≫ 𝔸(n; V.toScheme) ↘ V.toScheme) ≫ V.ι = W.ι ≫ g := by
    rw [hα, Scheme.Hom.resLE_comp_ι]
  have e₀ : U₀ ≤ (W.ι ≫ g) ⁻¹ᵁ V := (W.ι.preimage_image_eq U₀).ge.trans
    (W.ι.preimage_mono (image_le_preimage_of_le g hWV U₀))
  have e₀' : U₀ ≤ ((α ≫ 𝔸(n; V.toScheme) ↘ V.toScheme) ≫ V.ι) ⁻¹ᵁ V := hα' ▸ e₀
  have h1 : jV ≫ (𝔸(n; V.toScheme) ↘ V.toScheme).appTop ≫ α.appLE ⊤ U₀ (α.le_preimage_top U₀) =
      g.appLE V (W.ι ''ᵁ U₀) (image_le_preimage_of_le g hWV U₀) ≫ (W.ι.appIso U₀).hom :=
    calc jV ≫ (𝔸(n; V.toScheme) ↘ V.toScheme).appTop ≫ α.appLE ⊤ U₀ (α.le_preimage_top U₀)
        _ = jV ≫ (α ≫ 𝔸(n; V.toScheme) ↘ V.toScheme).appLE ⊤ U₀
            ((α ≫ 𝔸(n; V.toScheme) ↘ V.toScheme).le_preimage_top U₀) := by rw [comp_appLE_top]
        _ = ((α ≫ 𝔸(n; V.toScheme) ↘ V.toScheme) ≫ V.ι).appLE V U₀ e₀' :=
          Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
        _ = (W.ι ≫ g).appLE V U₀ e₀ := Scheme.Hom.appLE_congr_hom hα' _ _ _ _
        _ = g.appLE V (W.ι ''ᵁ U₀) (image_le_preimage_of_le g hWV U₀) ≫
            W.ι.appLE (W.ι ''ᵁ U₀) U₀ (W.ι.preimage_image_eq U₀).ge :=
          (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
        _ = _ := by rw [Scheme.Hom.appIso_hom']
  -- `θ` is bijective
  have hθ : Function.Bijective θ := by
    have hjV : IsIso jV := inferInstanceAs (IsIso (V.ι.appLE V ⊤ V.ι_preimage_self.ge))
    have hθ' : θ = (MvPolynomial.eval₂Hom (𝔸(n; V.toScheme) ↘ V.toScheme).appTop.hom
        (AffineSpace.coord V.toScheme)).comp
        (MvPolynomial.mapEquiv n (asIso jV).commRingCatIsoToRingEquiv).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp [θ, κ]
      · simp [θ]
    have hev : (MvPolynomial.eval₂Hom (𝔸(n; V.toScheme) ↘ V.toScheme).appTop.hom
        (AffineSpace.coord V.toScheme)) =
        ((Scheme.ΓSpecIso _).inv ≫ (AffineSpace.isoOfIsAffine n V.toScheme).hom.appTop).hom := by
      rw [AffineSpace.isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]
    have : IsIso (AffineSpace.isoOfIsAffine n V.toScheme).hom.appTop :=
      inferInstanceAs (IsIso (Scheme.Γ.map (AffineSpace.isoOfIsAffine n V.toScheme).hom.op))
    rw [hθ', RingHom.coe_comp, hev, CommRingCat.hom_comp, RingHom.coe_comp]
    exact ((ConcreteCategory.bijective_of_isIso _).comp
      (ConcreteCategory.bijective_of_isIso _)).comp (RingEquiv.bijective _)
  have hψ : ψ.Etale :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hθ)
        (HasRingHomProperty.appLE (P := @Etale) (f := α) inferInstance
          ⟨⊤, isAffineOpen_top _⟩ ⟨U₀, hU₀⟩ (α.le_preimage_top U₀)))
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _))
  have hC : ∀ r, ψ (MvPolynomial.C r) =
      (g.appLE V (W.ι ''ᵁ U₀) (image_le_preimage_of_le g hWV U₀)).hom r := fun r => by
    have := congrArg (fun k => ((W.ι.appIso U₀).inv.hom (k.hom r))) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← CommRingCat.comp_apply (W.ι.appIso U₀).hom, Iso.hom_inv_id, CommRingCat.id_apply] at this
    rw [← this]
    simp only [ψ, θ, κ, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
  let φ : MvPolynomial n Γ(S, V) →ₐ[Γ(S, V)] Γ(T, W.ι ''ᵁ U₀) :=
    ⟨ψ, fun r => by rw [MvPolynomial.algebraMap_eq]; exact hC r⟩
  obtain ⟨b, hb⟩ := exists_basis_kaehler_of_etale (Λ := Γ(S, V)) (A := Γ(T, W.ι ''ᵁ U₀)) (ι := n)
    φ hψ
  refine ⟨b, fun i => ?_⟩
  rw [hb]
  congr 1
  change (W.ι.appIso U₀).inv.hom ((α.appLE ⊤ U₀ (α.le_preimage_top U₀)).hom (θ (MvPolynomial.X i)))
      = _
  simp [θ]

/-- The identification of the functions on the preimage of an open of a chart with those on the
corresponding open of the restricted scheme. -/
def morphismRestrictAppIso {X T : Scheme.{u}} (F : X ⟶ T) (W : T.Opens) (U₀ : W.toScheme.Opens) :
    Γ(X, F ⁻¹ᵁ (W.ι ''ᵁ U₀)) ≅ Γ((F ⁻¹ᵁ W).toScheme, (F ∣_ W) ⁻¹ᵁ U₀) :=
  X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage F W U₀)).op ≪≫
    (F ⁻¹ᵁ W).ι.appIso _

/-- The identifications of the functions on a chart with those on the restricted scheme are
compatible with `F`. -/
theorem app_comp_morphismRestrictAppIso_hom {X T : Scheme.{u}} (F : X ⟶ T) (W : T.Opens)
    (U₀ : W.toScheme.Opens) :
    F.app (W.ι ''ᵁ U₀) ≫ (morphismRestrictAppIso F W U₀).hom =
      (W.ι.appIso U₀).hom ≫ (F ∣_ W).app U₀ := by
  have h := morphismRestrict_ι F W
  rw [morphismRestrictAppIso, Iso.trans_hom, Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom',
    Functor.mapIso_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, ← Category.assoc,
    Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact (Scheme.Hom.appLE_congr_hom h _ _ _ _).symm

/-- **The rings of functions over a chart form a pushout.** Let `F : X ⟶ T` be affine and, over an
open `W` of `T`, let `F ∣_ W` be the base change of an affine `f : Z₁ ⟶ Z₂` along `α : W → Z₂`.
For affine opens `D` of `Z₂` and `U₀ ⊆ α⁻¹D` of `W`, the square
`Γ(Z₂, D) → Γ(Z₁, f⁻¹D)`, `Γ(Z₂, D) → Γ(T, U₀)`, `Γ(T, U₀) → Γ(X, F⁻¹U₀)` is a pushout. -/
theorem isPushout_app_of_isPullback {X T Z₁ Z₂ : Scheme.{u}} (F : X ⟶ T) [IsAffineHom F]
    {W : T.Opens} {β : (F ⁻¹ᵁ W).toScheme ⟶ Z₁} {α : W.toScheme ⟶ Z₂} {f : Z₁ ⟶ Z₂}
    [IsAffineHom f] (H : IsPullback β (F ∣_ W) f α) {D : Z₂.Opens} (hD : IsAffineOpen D)
    {U₀ : W.toScheme.Opens} (hU₀ : IsAffineOpen U₀) (hU₀D : U₀ ≤ α ⁻¹ᵁ D) :
    IsPushout (f.app D) (α.appLE D U₀ hU₀D ≫ (W.ι.appIso U₀).inv)
      (β.appLE (f ⁻¹ᵁ D) ((F ∣_ W) ⁻¹ᵁ U₀) (by
          rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
          exact (F ∣_ W).preimage_mono hU₀D) ≫
        (morphismRestrictAppIso F W U₀).inv)
      (F.app (W.ι ''ᵁ U₀)) := by
  have hle := preimage_le_preimage_of_comm H.w.symm hU₀D
  have : IsAffineHom (F ∣_ W) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict F W).flip ‹IsAffineHom F›
  have P1 := isPushout_appLE_of_isPullback_of_isAffineOpen H D hD U₀ hU₀ hU₀D (f ⁻¹ᵁ D)
    (hD.preimage f) le_rfl ((F ∣_ W) ⁻¹ᵁ U₀) (inf_eq_right.mpr hle).symm (hU₀.preimage (F ∣_ W))
  simp only [CommRingCat.ofHom_hom] at P1
  refine P1.flip.of_iso (Iso.refl _) (Iso.refl _) (W.ι.appIso U₀).symm
    (morphismRestrictAppIso F W U₀).symm ?_ ?_ ?_ ?_
  · simp [Scheme.Hom.app_eq_appLE]
  · rw [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
  · rw [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
  · rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Scheme.Hom.app_eq_appLE, ← Category.assoc,
      ← app_comp_morphismRestrictAppIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Charts

/-! ### The relative Frobenius -/

section Frobenius

variable (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (X : Over S)
  (d : ℕ) [SmoothOfRelativeDimension d X.hom]

include d in
/-- The relative Frobenius of a morphism smooth of relative dimension `d` is finite (Stacks 0CCD).
-/
theorem isFinite_relativeFrobenius : IsFinite (relativeFrobenius S p hS X).left :=
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  inferInstance

include d in
/-- **The relative Frobenius of a smooth morphism is syntomic**: locally on the twist it is a base
change of the universal Frobenius `x_i ↦ x_i ^ p` of `Spec ℤ[x_1, …, x_d]`, which is syntomic. -/
theorem syntomic_relativeFrobenius : Syntomic (relativeFrobenius S p hS X).left := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @Syntomic) fun x => ?_
  obtain ⟨V, hV, W, hW, hxW, hWV, α, β, -, -, hpb⟩ :=
    exists_isPullback_relativeFrobenius_affineSpace S p hS X d x
  have H := hpb.paste_horiz (isPullback_specExpand (ULift.{u} (Fin d)) p V.toScheme)
  exact ⟨W, hxW, MorphismProperty.of_isPullback (P := @Syntomic) H
    (syntomic_specExpand (ULift.{u} (Fin d)) p hp)⟩

/-- **Around every point of the Frobenius twist there are framed charts on which the trace on
relative forms vanishes outside degree `d` and is surjective in degree `d`.** For every point `x`
of `X^{(p)}` and every open `N ∋ x`, there is a framed affine open `U ⊆ N` containing `x`, lying
over an affine open of `S`, on which the descended local trace
`Θ : Ω^•_{Γ(X, F⁻¹U)/Γ(S, V)} → Ω^•_{Γ(X^{(p)}, U)/Γ(S, V)}` is zero in every degree `k ≠ d` and
surjective in degree `d`. -/
theorem exists_relFramedOpen_relativeFrobenius (x : ((frobeniusTwist S p hS).obj X).left)
    (N : ((frobeniusTwist S p hS).obj X).left.Opens) (hxN : x ∈ N) :
    haveI := isFinite_relativeFrobenius S p hS X d
    ∃ i : (relativeFrobenius S p hS X).left.RelFramedOpen ((frobeniusTwist S p hS).obj X).hom,
      x ∈ i.U ∧ i.U ≤ N ∧ (∀ k ≠ d, ∀ η, Scheme.Hom.relLocalTrace i k η = 0) ∧
        Function.Surjective (Scheme.Hom.relLocalTrace i d) := by
  have := isFinite_relativeFrobenius S p hS X d
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hc := exists_isPullback_relativeFrobenius_affineSpace S p hS X d x
  obtain ⟨V, hV, W, hW, hxW, hWV, α, β, hαet, hαV, hpb⟩ := hc
  have H := hpb.paste_horiz (isPullback_specExpand (ULift.{u} (Fin d)) p V.toScheme)
  have := isFinite_specExpand (ULift.{u} (Fin d)) p hp
  have := flat_specExpand (ULift.{u} (Fin d)) p hp
  have : LocallyOfFinitePresentation (specExpand (ULift.{u} (Fin d)) p) :=
    locallyOfFinitePresentation (syntomic_specExpand _ p hp)
  let x₀ : W.toScheme := ⟨x, hxW⟩
  have hO' := Opens.isBasis_iff_nbhd.mp
    (isBasis_framedOpens (specExpand (ULift.{u} (Fin d)) p) (syntomic_specExpand _ p hp))
    (show (α ≫ AffineSpace.toSpecMvPoly (ULift.{u} (Fin d)) V.toScheme) x₀ ∈
      (⊤ : (Spec (.of (UnivRing.{u} d))).Opens) from trivial)
  obtain ⟨O, hO, hxO, -⟩ := hO'
  have : Nonempty O := ⟨⟨_, hxO⟩⟩
  have hU₀' := Opens.isBasis_iff_nbhd.mp W.toScheme.isBasis_affineOpens
    (show x₀ ∈ (α ≫ AffineSpace.toSpecMvPoly (ULift.{u} (Fin d)) V.toScheme) ⁻¹ᵁ O ⊓
      W.ι ⁻¹ᵁ N from ⟨hxO, hxN⟩)
  obtain ⟨U₀, hU₀, hxU₀, hU₀le⟩ := hU₀'
  have hP := isPushout_app_of_isPullback (relativeFrobenius S p hS X).left H hO.1 hU₀
    (hU₀le.trans inf_le_left)
  -- the open `U` of the twist and its index
  have hUaff : IsAffineOpen (W.ι ''ᵁ U₀) := hU₀.image_of_isOpenImmersion W.ι
  have hUV : W.ι ''ᵁ U₀ ≤ ((frobeniusTwist S p hS).obj X).hom ⁻¹ᵁ V := image_le_preimage_of_le _
      hWV U₀
  have hxU : x ∈ W.ι ''ᵁ U₀ := ⟨x₀, hxU₀, rfl⟩
  have hUN : W.ι ''ᵁ U₀ ≤ N := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hU₀le hz).2
  -- the pushout square of rings
  let : Algebra Γ(Spec (.of (UnivRing.{u} d)), O)
      Γ(Spec (.of (UnivRing.{u} d)), specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O) :=
    ((specExpand (ULift.{u} (Fin d)) p).app O).hom.toAlgebra
  let a := (α ≫ AffineSpace.toSpecMvPoly (ULift.{u} (Fin d)) V.toScheme).appLE O U₀ (hU₀le.trans
      inf_le_left) ≫ (W.ι.appIso U₀).inv
  let b := (β ≫ AffineSpace.toSpecMvPoly (ULift.{u} (Fin d)) V.toScheme).appLE (specExpand
      (ULift.{u} (Fin d)) p ⁻¹ᵁ O) (((relativeFrobenius S p hS X).left ∣_ W) ⁻¹ᵁ U₀)
      (preimage_le_preimage_of_comm H.w.symm (hU₀le.trans inf_le_left)) ≫
    (morphismRestrictAppIso (relativeFrobenius S p hS X).left W U₀).inv
  let : Algebra Γ(Spec (.of (UnivRing.{u} d)), O) Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ
      U₀) := a.hom.toAlgebra
  let : Algebra Γ(Spec (.of (UnivRing.{u} d)), specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O)
      Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)) := b.hom.toAlgebra
  let : Algebra Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ U₀) Γ(X.left, (relativeFrobenius S
      p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)) := ((relativeFrobenius S p hS X).left.app (W.ι ''ᵁ
      U₀)).hom.toAlgebra
  let : Algebra Γ(Spec (.of (UnivRing.{u} d)), O) Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ
      (W.ι ''ᵁ U₀)) :=
    (a ≫ (relativeFrobenius S p hS X).left.app (W.ι ''ᵁ U₀)).hom.toAlgebra
  have : IsScalarTower Γ(Spec (.of (UnivRing.{u} d)), O) Γ(((frobeniusTwist S p hS).obj X).left,
      W.ι ''ᵁ U₀)
      Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)) :=
          IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(Spec (.of (UnivRing.{u} d)), O)
      Γ(Spec (.of (UnivRing.{u} d)), specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O)
      Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (a ≫ (relativeFrobenius S p hS X).left.app (W.ι ''ᵁ U₀)).hom r =
        b.hom (((specExpand (ULift.{u} (Fin d)) p).app O).hom r)
      rw [← hP.w]
      rfl
  have : Algebra.IsPushout Γ(Spec (.of (UnivRing.{u} d)), O)
      Γ(Spec (.of (UnivRing.{u} d)), specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O)
      Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ U₀) Γ(X.left, (relativeFrobenius S p hS
          X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)) :=
    CommRingCat.isPushout_iff_isPushout.mp hP
  -- frames
  have hB₀ := framed_or_subsingleton_of_isFramedOpen (specExpand (ULift.{u} (Fin d)) p) hO
  have hB : Subsingleton Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)) ∨ Nonempty
      (AnyFrame Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ U₀) Γ(X.left, (relativeFrobenius S
      p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀))) := by
    rcases hB₀ with h | hF₀
    · left
      have h1 : (1 : Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀))) = 0 := by
        rw [← map_one b.hom, Subsingleton.elim (1 : Γ(Spec (.of (UnivRing.{u} d)), specExpand
            (ULift.{u} (Fin d)) p ⁻¹ᵁ O)) 0, map_zero]
      exact subsingleton_of_zero_eq_one h1.symm
    · obtain ⟨F₀⟩ := hF₀
      exact Or.inr ⟨⟨F₀.rank, F₀.frame.baseChange Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ
          U₀) Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀))⟩⟩
  have hframed : IsFramedOpen (relativeFrobenius S p hS X).left (W.ι ''ᵁ U₀) := by
    refine ⟨hUaff, ?_⟩
    rcases hB with h | hF'
    · exact Or.inl h
    · obtain ⟨F'⟩ := hF'
      exact Or.inr ⟨F'.rank, F'.neZero, ⟨F'.frame⟩⟩
  let i : (relativeFrobenius S p hS X).left.RelFramedOpen ((frobeniusTwist S p hS).obj X).hom :=
      ⟨(W.ι ''ᵁ U₀, ⟨V, hV⟩), hframed, hUV⟩
  refine ⟨i, hxU, hUN, ?_⟩
  -- the ring-level data
  let : Algebra Γ(S, V) Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ U₀) := (((frobeniusTwist S
      p hS).obj X).hom.appLE V (W.ι ''ᵁ U₀) hUV).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)) :=
    (((relativeFrobenius S p hS X).left ≫ ((frobeniusTwist S p hS).obj X).hom).appLE V
        ((relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)) i.le_comp).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ U₀) Γ(X.left,
      (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)) := i.isScalarTower
  have hE := exists_basis_kaehler_of_etale_chart ((frobeniusTwist S p hS).obj X).hom hWV hV α hαV
      hU₀
  obtain ⟨bA, hbA⟩ := hE
  have hy : ∀ j : Fin d, a.hom (specCoord d O j) = (W.ι.appIso U₀).inv.hom
      ((α.appLE ⊤ U₀ (α.le_preimage_top U₀)).hom (AffineSpace.coord V.toScheme (ULift.up j))) := by
    intro j
    have m1 : (Spec (.of (UnivRing.{u} d))).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op ≫
        (α ≫ AffineSpace.toSpecMvPoly (ULift.{u} (Fin d)) V.toScheme).appLE O U₀
          (hU₀le.trans inf_le_left) =
        (α ≫ AffineSpace.toSpecMvPoly (ULift.{u} (Fin d)) V.toScheme).appLE ⊤ U₀
          ((α ≫ AffineSpace.toSpecMvPoly (ULift.{u} (Fin d)) V.toScheme).le_preimage_top U₀) :=
      Scheme.Hom.map_appLE _ _ _
    change (W.ι.appIso U₀).inv.hom
      (((Spec (.of (UnivRing.{u} d))).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op ≫
        (α ≫ AffineSpace.toSpecMvPoly (ULift.{u} (Fin d)) V.toScheme).appLE O U₀
          (hU₀le.trans inf_le_left)).hom
        ((Scheme.ΓSpecIso (.of (UnivRing.{u} d))).inv (MvPolynomial.X (ULift.up j)))) = _
    rw [m1, comp_appLE_top]
    rfl
  let bA' := bA.reindex Equiv.ulift
  have hbA' : ∀ j, bA' j = D Γ(S, V) Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ U₀) (a.hom
      (specCoord d O j)) := by
    intro j
    rw [Module.Basis.reindex_apply, hbA, hy]
    rfl
  have hxy : ∀ j : Fin d, algebraMap Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ U₀) Γ(X.left,
      (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)) (a.hom (specCoord d O j)) =
      b.hom (specCoord d (specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O) j) ^ p := by
    intro j
    change (a ≫ (relativeFrobenius S p hS X).left.app (W.ι ''ᵁ U₀)).hom (specCoord d O j) = _
    rw [← hP.w, CommRingCat.comp_apply, specExpand_app_specCoord, map_pow]
  have hpB : (p : Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀))) = 0 := by
    have h := congrArg (X.left.presheaf.map (homOfLE (le_top : (relativeFrobenius S p hS X).left
        ⁻¹ᵁ (W.ι ''ᵁ U₀) ≤ ⊤)).op).hom
      (isInCharacteristic_of_hom X.hom p hS)
    simpa only [map_natCast, map_zero] using h
  have hmap := kaehlerMap_eq_zero_of_eq_pow (Λ := Γ(S, V)) (A := Γ(((frobeniusTwist S p hS).obj
      X).left, W.ι ''ᵁ U₀)) (B := Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀))) bA'
    (fun j => a.hom (specCoord d O j)) hbA'
    (fun j => b.hom (specCoord d (specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O) j)) hxy hpB
  have h0 := frameTrace_specExpand p hp hO
  have htop := relativeTrace_prod_pow_smul_ιMulti_D_of_isPushout (Λ := Γ(S, V)) (A :=
      Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ U₀))
    (B := Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀))) (A₀ := Γ(Spec (.of
        (UnivRing.{u} d)), O)) (B₀ := Γ(Spec (.of (UnivRing.{u} d)), specExpand (ULift.{u} (Fin d))
        p ⁻¹ᵁ O)) hB₀ hB (specCoord d O)
    (specCoord d (specExpand (ULift.{u} (Fin d)) p ⁻¹ᵁ O)) h0
  refine ⟨fun k hk η => ?_, ?_⟩
  · exact LinearMap.congr_fun (relativeTrace_eq_zero_of_ne (Λ := Γ(S, V)) (frameTrace
      Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ U₀) Γ(X.left, (relativeFrobenius S p hS
      X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)))
      (isWedgeLinear_frameTrace hB) bA' hmap hk) η
  · refine relativeTrace_surjective_of_eq (Λ := Γ(S, V)) (frameTrace Γ(((frobeniusTwist S p hS).obj
      X).left, W.ι ''ᵁ U₀) Γ(X.left, (relativeFrobenius S p hS X).left ⁻¹ᵁ (W.ι ''ᵁ U₀)))
      (isWedgeLinear_frameTrace hB) bA' _ (htop.trans ?_)
    exact congrArg (ιMulti Γ(((frobeniusTwist S p hS).obj X).left, W.ι ''ᵁ U₀) d) (funext fun j =>
        (hbA' j).symm)

end Frobenius

end AlgebraicGeometry
