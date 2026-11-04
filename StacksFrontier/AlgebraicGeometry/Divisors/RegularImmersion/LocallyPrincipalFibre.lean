module

public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FibrePrincipalDictionary
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.Chart
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A locally principal closed subscheme with Cartier fibre

Let `f : X ⟶ S` be flat and locally of finite presentation, let `Z` be a closed subscheme of `X`
and let `x` be a point of `Z` whose fibre `Z_{f x}` is an effective Cartier divisor in a
neighbourhood of `x`.  If `Z` is locally principal near `x`, then `Z` agrees, on an affine open
neighbourhood of `x`, with a relative effective Cartier divisor over `S`.

## Main results

* `Stacks.Divisors.isRelativeEffectiveCartierDivisor_comap_of_ideal_eq_span`: a closed subscheme
  cut out on an affine open `V` lying over an affine open `W` of the base by a nonzerodivisor
  whose quotient is flat over `Γ(S, W)` restricts to a relative effective Cartier divisor on `V`.
* `Stacks.Divisors.exists_affineOpen_isRegular_flat_quotient_of_mem_ideal`: a section of the
  ideal of `Z` near `x` whose germ is a nonzerodivisor in the local ring of the fibre is, on a
  smaller affine open lying over an affine open `W` of the base, a nonzerodivisor with quotient
  flat over `Γ(S, W)`.
* `Stacks.Divisors.exists_isRelativeEffectiveCartierDivisor_of_ideal_isPrincipal`: if the ideal
  of `Z` is principal on an affine open neighbourhood of `x`, then `Z` restricts to a relative
  effective Cartier divisor over `S` on an affine open neighbourhood of `x`.
* `Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres`: a locally
  principal closed subscheme all of whose fibres are effective Cartier divisors is a relative
  effective Cartier divisor over `S`.

## References

* [Stacks Project, Tag 062Y, part (3)](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry
open Stacks.RingTheory.SpreadingOut

universe u

namespace Stacks.Divisors

variable {X S : Scheme.{u}}

/-! ### The affine-chart criterion -/

/-- **Flatness of a surjection with prescribed kernel, read on the quotient.**  If `ψ` is
surjective with kernel `I`, then `ψ ∘ φ` is flat exactly when the projection onto `B ⧸ I`
composed with `φ` is. -/
private theorem ringHom_flat_comp_of_ker_eq {A B T : Type*} [CommRing A] [CommRing B]
    [CommRing T] (φ : A →+* B) (ψ : B →+* T) (hψ : Function.Surjective ψ) (I : Ideal B)
    (hker : RingHom.ker ψ = I)
    (hflat : RingHom.Flat ((Ideal.Quotient.mk I).comp φ)) : RingHom.Flat (ψ.comp φ) := by
  set e : (B ⧸ I) ≃+* T :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hψ) with he
  have hemk : ∀ z : B, e (Ideal.Quotient.mk I z) = ψ z := by
    intro z
    show (RingHom.quotientKerEquivOfSurjective hψ)
      (Ideal.quotEquivOfEq hker.symm (Ideal.Quotient.mk I z)) = ψ z
    rw [Ideal.quotEquivOfEq_mk]
    exact RingHom.kerLift_mk ψ z
  have hcomp : ψ.comp φ = e.toRingHom.comp ((Ideal.Quotient.mk I).comp φ) := by
    refine RingHom.ext fun z => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact (hemk (φ z)).symm
  rw [hcomp]
  exact (RingHom.Flat.comp_iff_of_bijective_left e.bijective).mpr hflat

/-- **A closed subscheme cut out on an affine chart by a nonzerodivisor with flat quotient is a
relative effective Cartier divisor there.**  Let `V` be an affine open of `X` lying over an affine
open `W` of `S`, let `D` be a closed subscheme of `V` whose ideal of global sections is generated
by the restriction of a nonzerodivisor `a : Γ(X, V)`, and let the quotient of `Γ(X, V)` by `a` be
flat over `Γ(S, W)`.  Then `D` is a relative effective Cartier divisor over `S`. -/
theorem isRelativeEffectiveCartierDivisor_of_ideal_top_eq_span (f : X ⟶ S)
    {W : S.Opens} (hW : IsAffineOpen W) {V : X.Opens}
    (hV : IsAffineOpen V) (hVW : V ≤ f ⁻¹ᵁ W) (D : V.toScheme.IdealSheafData)
    (hT : IsAffineOpen (⊤ : V.toScheme.Opens)) (a : Γ(X, V)) (hareg : IsRegular a)
    (hideal : D.ideal ⟨⊤, hT⟩ = Ideal.span {V.topIso.inv.hom a})
    (hflat : RingHom.Flat
      ((Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE W V hVW).hom)) :
    IsRelativeEffectiveCartierDivisor (V.ι ≫ f) D := by
  have hVa : IsAffine V.toScheme := hV
  have hWa : IsAffine W.toScheme := hW
  set ε : Γ(X, V) ≃+* Γ(V.toScheme, ⊤) :=
    V.topIso.symm.commRingCatIsoToRingEquiv with hε
  set εh : Γ(X, V) →+* Γ(V.toScheme, ⊤) := (ε : Γ(X, V) →+* Γ(V.toScheme, ⊤)) with hεh
  have hcomap : D.ideal ⟨⊤, hT⟩ = Ideal.span {εh a} := hideal
  refine ⟨isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun y =>
    ⟨⊤, hT, trivial, εh a, isRegular_ringEquiv ε hareg, hcomap⟩, ?_⟩
  have hcomp : D.subschemeι ≫ V.ι ≫ f
      = (D.subschemeι ≫ f.resLE W V hVW) ≫ W.ι := by
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι]
  have hDa : IsAffine D.subscheme :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine D.subschemeι).1
  set σ : Γ(V.toScheme, ⊤) ⟶ Γ(D.subscheme, ⊤) :=
    D.subschemeι.appTop with hσ
  set τ : Γ(X, V) →+* Γ(D.subscheme, ⊤) := σ.hom.comp εh with hτ
  have hσsurj : Function.Surjective σ.hom :=
    D.subschemeι_app_surjective ⟨⊤, hT⟩
  have hτsurj : Function.Surjective τ := hσsurj.comp ε.surjective
  have hkerσ : RingHom.ker σ.hom = Ideal.span {εh a} :=
    (D.ker_subschemeι_app ⟨⊤, hT⟩).trans hcomap
  have hmapspan : Ideal.span {εh a} = Ideal.map εh (Ideal.span {a}) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hkerτ : RingHom.ker τ = Ideal.span {a} := by
    rw [hτ, ← RingHom.comap_ker, hkerσ, hmapspan,
      Ideal.comap_map_of_surjective εh ε.surjective,
      Ideal.comap_bot_of_injective εh ε.injective, sup_bot_eq]
  have hres : (f.resLE W V hVW).appTop = W.topIso.hom ≫ f.appLE W V hVW ≫ V.topIso.inv :=
    Scheme.Hom.resLE_app_top f hVW
  have hflat' : Flat (D.subschemeι ≫ f.resLE W V hVW) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
    have hap : (D.subschemeι ≫ f.resLE W V hVW).appTop
        = W.topIso.hom ≫ (f.appLE W V hVW ≫ V.topIso.inv ≫ σ) := by
      rw [Scheme.Hom.comp_appTop, hres, hσ]
      simp only [Category.assoc]
    rw [hap, CommRingCat.hom_comp]
    refine (RingHom.Flat.comp_iff_of_bijective_right
      (ConcreteCategory.bijective_of_isIso W.topIso.hom)).mpr ?_
    exact ringHom_flat_comp_of_ker_eq (f.appLE W V hVW).hom τ hτsurj (Ideal.span {a}) hkerτ hflat
  rw [hcomp]
  have _ := hflat'
  infer_instance

/-- **The affine-chart criterion for the restriction of a closed subscheme.**  The special case of
`Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_ideal_top_eq_span` in which the divisor is
the restriction of a closed subscheme `Z` of `X` whose ideal on `V` is generated by `a`. -/
theorem isRelativeEffectiveCartierDivisor_comap_of_ideal_eq_span (f : X ⟶ S)
    (Z : X.IdealSheafData) {W : S.Opens} (hW : IsAffineOpen W) {V : X.Opens}
    (hV : IsAffineOpen V) (hVW : V ≤ f ⁻¹ᵁ W) (a : Γ(X, V)) (hareg : IsRegular a)
    (hideal : Z.ideal ⟨V, hV⟩ = Ideal.span {a})
    (hflat : RingHom.Flat
      ((Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE W V hVW).hom)) :
    IsRelativeEffectiveCartierDivisor (V.ι ≫ f) (Z.comap V.ι) := by
  have hVa : IsAffine V.toScheme := hV
  refine isRelativeEffectiveCartierDivisor_of_ideal_top_eq_span f hW hV hVW _
    (isAffineOpen_top V.toScheme) a hareg ?_ hflat
  rw [Stacks.IdealSheaf.ideal_comap_ι_top Z hV (isAffineOpen_top V.toScheme), hideal,
    Ideal.map_span, Set.image_singleton]

/-- **Flatness of the closed subscheme over the base, from the affine chart.**  Under the
hypotheses of `Stacks.Divisors.isRelativeEffectiveCartierDivisor_comap_of_ideal_eq_span`, the
structure morphism of the closed subscheme is flat over `S` after restricting its source to the
part lying over `V` and its target to `W`. -/
theorem flat_resLE_subschemeι_of_ideal_eq_span (f : X ⟶ S) (Z : X.IdealSheafData)
    {W : S.Opens} (hW : IsAffineOpen W) {V : X.Opens} (hV : IsAffineOpen V)
    (hVW : V ≤ f ⁻¹ᵁ W) (a : Γ(X, V)) (hideal : Z.ideal ⟨V, hV⟩ = Ideal.span {a})
    (hflat : RingHom.Flat
      ((Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE W V hVW).hom)) :
    Flat ((Z.subschemeι ≫ f).resLE W (Z.subschemeι ⁻¹ᵁ V) (fun _ hz => hVW hz)) := by
  have hWa : IsAffine W.toScheme := hW
  have hPa : IsAffine (Z.subschemeι ⁻¹ᵁ V).toScheme := hV.preimage Z.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  have hres : ((Z.subschemeι ≫ f).resLE W (Z.subschemeι ⁻¹ᵁ V) (fun _ hz => hVW hz)).appTop
      = W.topIso.hom ≫ (Z.subschemeι ≫ f).appLE W (Z.subschemeι ⁻¹ᵁ V) (fun _ hz => hVW hz)
        ≫ (Z.subschemeι ⁻¹ᵁ V).topIso.inv :=
    Scheme.Hom.resLE_app_top (Z.subschemeι ≫ f) (fun _ hz => hVW hz)
  have happ : (Z.subschemeι ≫ f).appLE W (Z.subschemeι ⁻¹ᵁ V) (fun _ hz => hVW hz)
      = f.appLE W V hVW ≫ Z.subschemeι.app V := by
    rw [Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE Z.subschemeι f W V (Z.subschemeι ⁻¹ᵁ V) hVW le_rfl).symm
  rw [hres, happ]
  simp only [Category.assoc, CommRingCat.hom_comp]
  have hkey : RingHom.Flat ((Z.subschemeι.app V).hom.comp (f.appLE W V hVW).hom) :=
    ringHom_flat_comp_of_ker_eq (f.appLE W V hVW).hom (Z.subschemeι.app V).hom
      (Z.subschemeι_app_surjective ⟨V, hV⟩) (Ideal.span {a})
      ((Z.ker_subschemeι_app ⟨V, hV⟩).trans hideal) hflat
  have hfull := (RingHom.Flat.comp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso W.topIso.hom)) hkey).comp
      (RingHom.Flat.of_bijective
        (ConcreteCategory.bijective_of_isIso (Z.subschemeι ⁻¹ᵁ V).topIso.inv))
  simpa only [RingHom.comp_assoc] using hfull

/-! ### The chart -/

/-- **An affine chart for a prescribed section of the ideal.** Let `f : X ⟶ S` be flat and locally
of finite presentation, let `Z` be a closed subscheme of `X`, let `x` be a point of `Z`, and let
`c` be a section of the ideal of `Z` on an affine open neighbourhood `U₀` of `x` whose germ is a
nonzerodivisor in the local ring of the fibre through `x`. Then there is an affine open `V` with
`x ∈ V ≤ U₀`, lying over an affine open `W` of the base, on which the restriction of `c` is a
nonzerodivisor whose quotient is flat over `Γ(S, W)`. -/
theorem exists_affineOpen_isRegular_flat_quotient_of_mem_ideal (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (Z : X.IdealSheafData) (x : X) (hx : x ∈ Z.support)
    {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀) (hxU₀ : x ∈ U₀) (c : Γ(X, U₀))
    (hc : c ∈ Z.ideal ⟨U₀, hU₀⟩)
    (hreg : IsSMulRegular
      (X.presheaf.stalk x ⧸ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
      (Ideal.Quotient.mk
        (Ideal.map (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
        ((X.presheaf.germ U₀ x hxU₀).hom c))) :
    ∃ (W : S.Opens) (_hW : IsAffineOpen W) (V : X.Opens) (_hV : IsAffineOpen V)
      (hVW : V ≤ f ⁻¹ᵁ W) (hVU₀ : V ≤ U₀), x ∈ V ∧ ∃ a : Γ(X, V),
        a = (X.presheaf.map (homOfLE hVU₀).op).hom c ∧ IsRegular a ∧ RingHom.Flat
          ((Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE W V hVW).hom) := by
  classical
  obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show f x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ U₀ ⊓ f ⁻¹ᵁ W from ⟨hxU₀, hxW⟩)
  have hUU₀ : U ≤ U₀ := fun _ hz => (hUle hz).1
  have hUW : U ≤ f ⁻¹ᵁ W := fun _ hz => (hUle hz).2
  set h : Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom c with hhdef
  have hhU : h ∈ Z.ideal ⟨U, hU⟩ := by
    rw [hhdef, ← Z.map_ideal (U := ⟨U, hU⟩) (V := ⟨U₀, hU₀⟩) hUU₀]
    exact Ideal.mem_map_of_mem _ hc
  have hgerm : (X.presheaf.germ U x hxU).hom h = (X.presheaf.germ U₀ x hxU₀).hom c := by
    rw [hhdef, ← CommRingCat.comp_apply, X.presheaf.germ_res (homOfLE hUU₀) x hxU]
  let _ : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  have _ : Module.Flat Γ(S, W) Γ(X, U) := f.flat_appLE hW hU hUW
  have _ : Algebra.FinitePresentation Γ(S, W) Γ(X, U) := f.finitePresentation_appLE hW hU hUW
  set q : Ideal Γ(X, U) := (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal with hqdef
  have _ : q.IsPrime := (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).isPrime
  have hhq : h ∈ q := ideal_le_primeIdealOf Z hU hxU hx hhU
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x) q := hU.isLocalization_stalk ⟨x, hxU⟩
  let _ : Algebra Γ(S, W) (X.presheaf.stalk x) :=
    ((X.presheaf.germ U x hxU).hom.comp (f.appLE W U hUW).hom).toAlgebra
  have _ : IsScalarTower Γ(S, W) Γ(X, U) (X.presheaf.stalk x) := .of_algebraMap_eq fun _ => rfl
  have halg : ∀ t : Γ(S, W), algebraMap Γ(S, W) (X.presheaf.stalk x) t
      = (f.stalkMap x).hom ((S.presheaf.germ W (f x) hxW).hom t) := fun t =>
    (RingHom.congr_fun (stalkMap_hom_comp_germ f hUW hxU hxW) t).symm
  have hcomap : q.comap (algebraMap Γ(S, W) Γ(X, U))
      = (hW.primeIdealOf (⟨f x, hxW⟩ : ↥W)).asIdeal :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W hW U hU hUW hxU)
  let _ : Algebra Γ(S, W) (S.presheaf.stalk (f x)) :=
    S.presheaf.algebra_section_stalk ⟨f x, hxW⟩
  have _ : IsLocalization.AtPrime (S.presheaf.stalk (f x))
      (hW.primeIdealOf (⟨f x, hxW⟩ : ↥W)).asIdeal := hW.isLocalization_stalk ⟨f x, hxW⟩
  have _ : (hW.primeIdealOf (⟨f x, hxW⟩ : ↥W)).asIdeal.IsPrime :=
    (hW.primeIdealOf (⟨f x, hxW⟩ : ↥W)).isPrime
  let _ : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have _ : IsScalarTower Γ(S, W) (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    .of_algebraMap_eq halg
  have hP : Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
      = (q.comap (algebraMap Γ(S, W) Γ(X, U))).map
          (algebraMap Γ(S, W) (X.presheaf.stalk x)) := by
    rw [hcomap]
    exact map_maximalIdeal_eq_map_of_isLocalization _
  have hregO : IsSMulRegular
      (X.presheaf.stalk x ⧸ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
      (Ideal.Quotient.mk
        (Ideal.map (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
        (algebraMap Γ(X, U) (X.presheaf.stalk x) h)) := by
    rw [show algebraMap Γ(X, U) (X.presheaf.stalk x) h
      = (X.presheaf.germ U₀ x hxU₀).hom c from hgerm]
    exact hreg
  set p : Ideal Γ(S, W) := q.comap (algebraMap Γ(S, W) Γ(X, U)) with hpdef
  set eL : Localization.AtPrime q ≃ₐ[Γ(X, U)] X.presheaf.stalk x :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (X.presheaf.stalk x) with heL
  have heLbase : ∀ t : Γ(S, W), eL (algebraMap Γ(S, W) (Localization.AtPrime q) t)
      = algebraMap Γ(S, W) (X.presheaf.stalk x) t := by
    intro t
    rw [IsScalarTower.algebraMap_apply Γ(S, W) Γ(X, U) (Localization.AtPrime q),
      IsScalarTower.algebraMap_apply Γ(S, W) Γ(X, U) (X.presheaf.stalk x)]
    exact eL.commutes _
  have hPmap : Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
      = Ideal.map (eL : Localization.AtPrime q →+* X.presheaf.stalk x)
        (p.map (algebraMap Γ(S, W) (Localization.AtPrime q))) := by
    rw [hP, Ideal.map_map]
    exact congrArg (fun φ : Γ(S, W) →+* X.presheaf.stalk x => Ideal.map φ p)
      (RingHom.ext heLbase).symm
  set PK : Ideal (Localization.AtPrime q) :=
    p.map (algebraMap Γ(S, W) (Localization.AtPrime q)) with hPK
  set PO : Ideal (X.presheaf.stalk x) := Ideal.map (f.stalkMap x).hom
    (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) with hPO
  set eQ : (Localization.AtPrime q ⧸ PK) ≃+* (X.presheaf.stalk x ⧸ PO) :=
    Ideal.quotientEquiv PK PO eL.toRingEquiv hPmap with heQ
  have hfibreg : IsSMulRegular (Localization.AtPrime q ⧸ PK)
      (algebraMap Γ(X, U) (Localization.AtPrime q) h) := by
    have hmk : eQ (Ideal.Quotient.mk PK (algebraMap Γ(X, U) (Localization.AtPrime q) h))
        = Ideal.Quotient.mk PO (algebraMap Γ(X, U) (X.presheaf.stalk x) h) :=
      congrArg (Ideal.Quotient.mk PO) (eL.commutes h)
    have hregQ : IsRegular (Ideal.Quotient.mk PK
        (algebraMap Γ(X, U) (Localization.AtPrime q) h)) := by
      have h1 : IsRegular (eQ (Ideal.Quotient.mk PK
          (algebraMap Γ(X, U) (Localization.AtPrime q) h))) := by
        rw [hmk]
        exact isRegular_of_isSMulRegular hregO
      have h2 := isRegular_ringEquiv eQ.symm h1
      rwa [eQ.symm_apply_apply] at h2
    refine isSMulRegular_of_isRegular_algebraMap (R := Localization.AtPrime q)
      (A := Localization.AtPrime q ⧸ PK) ?_
    rw [Ideal.Quotient.algebraMap_eq]
    exact hregQ
  obtain ⟨g, hgq, hgreg, hgflat⟩ :=
    exists_notMem_isSMulRegular_and_flat_quotient_away (A := Γ(S, W)) q h hhq hfibreg
  have hV : IsAffineOpen (X.basicOpen g) := hU.basicOpen g
  have hVU : X.basicOpen g ≤ U := X.basicOpen_le g
  have hxV : x ∈ X.basicOpen g := by
    rw [X.mem_basicOpen g x hxU]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) q g).mpr hgq
  have hVW : X.basicOpen g ≤ f ⁻¹ᵁ W := hVU.trans hUW
  set a : Γ(X, X.basicOpen g) := (X.presheaf.map (homOfLE hVU).op).hom h with hadef
  have hadef' : a = (X.presheaf.map (homOfLE (hVU.trans hUU₀)).op).hom c := by
    rw [hadef, hhdef, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have _ : IsLocalization.Away g Γ(X, X.basicOpen g) := hU.isLocalization_basicOpen g
  let _ : Algebra Γ(S, W) Γ(X, X.basicOpen g) :=
    ((X.presheaf.map (homOfLE hVU).op).hom.comp (f.appLE W U hUW).hom).toAlgebra
  have _ : IsScalarTower Γ(S, W) Γ(X, U) Γ(X, X.basicOpen g) :=
    .of_algebraMap_eq fun _ => rfl
  set eA : Localization.Away g ≃ₐ[Γ(X, U)] Γ(X, X.basicOpen g) :=
    IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
      Γ(X, X.basicOpen g) with heA
  have halgbo : algebraMap Γ(X, U) Γ(X, X.basicOpen g)
      = (X.presheaf.map (homOfLE hVU).op).hom := RingHom.algebraMap_toAlgebra _
  have hamap : (eA : Localization.Away g →+* Γ(X, X.basicOpen g))
      (algebraMap Γ(X, U) (Localization.Away g) h) = a := by
    rw [hadef, halgbo.symm]
    exact eA.commutes h
  refine ⟨W, hW, X.basicOpen g, hV, hVW, hVU.trans hUU₀, hxV, a, hadef', ?_, ?_⟩
  · -- `a` is a nonzerodivisor
    have h1 : IsRegular ((eA : Localization.Away g →+* Γ(X, X.basicOpen g))
        (algebraMap Γ(X, U) (Localization.Away g) h)) :=
      isRegular_ringEquiv eA.toRingEquiv (isRegular_of_isSMulRegular hgreg)
    rwa [hamap] at h1
  · -- the quotient of the chart is flat over the base
    have hspan : Ideal.span {a}
        = Ideal.map (eA : Localization.Away g →+* Γ(X, X.basicOpen g))
          (Ideal.span {algebraMap Γ(X, U) (Localization.Away g) h}) := by
      rw [Ideal.map_span, Set.image_singleton, hamap]
    have hflatmod : Module.Flat Γ(S, W) (Γ(X, X.basicOpen g) ⧸ Ideal.span {a}) := by
      have _ := hgflat
      exact Module.Flat.of_linearEquiv (Ideal.quotientEquivAlg
        (Ideal.span {algebraMap Γ(X, U) (Localization.Away g) h}) (Ideal.span {a})
        (eA.restrictScalars Γ(S, W)) hspan).symm.toLinearEquiv
    have hmk : (Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE W (X.basicOpen g) hVW).hom
        = algebraMap Γ(S, W) (Γ(X, X.basicOpen g) ⧸ Ideal.span {a}) := by
      refine RingHom.ext fun t => ?_
      rw [IsScalarTower.algebraMap_apply Γ(S, W) Γ(X, X.basicOpen g)
        (Γ(X, X.basicOpen g) ⧸ Ideal.span {a}), Ideal.Quotient.algebraMap_eq]
      refine congrArg (Ideal.Quotient.mk (Ideal.span {a})) ?_
      have hmapLE := congrArg CommRingCat.Hom.hom
        (f.appLE_map (U := W) (V := U) hUW (homOfLE hVU).op)
      exact (RingHom.congr_fun hmapLE t).symm
    rw [hmk, RingHom.flat_algebraMap_iff]
    exact hflatmod

/-- **An affine chart for a locally principal ideal.** Let `f : X ⟶ S` be flat and locally of
finite presentation, let `Z` be a closed subscheme of `X` and let `x` be a point of `Z` whose fibre
over `f x` is an effective Cartier divisor in a neighbourhood of `x`. If the ideal of `Z` is
principal on some affine open neighbourhood of `x`, then there is an affine open `V ∋ x` lying over
an affine open `W` of the base on which the ideal of `Z` is generated by a nonzerodivisor with flat
quotient. -/
theorem exists_affineOpen_isRegular_ideal_eq_span_of_fibre (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (Z : X.IdealSheafData) (x : X) (hx : x ∈ Z.support)
    (hprin : ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ (Z.ideal U).IsPrincipal)
    (hfib : ∃ V : (f.fiber (f x)).Opens, f.asFiber x ∈ V ∧
      IsEffectiveCartierDivisor ((Z.comap (f.fiberι (f x))).comap V.ι)) :
    ∃ (W : S.Opens) (_hW : IsAffineOpen W) (V : X.Opens) (hV : IsAffineOpen V)
      (hVW : V ≤ f ⁻¹ᵁ W), x ∈ V ∧ ∃ a : Γ(X, V), IsRegular a ∧
        Z.ideal ⟨V, hV⟩ = Ideal.span {a} ∧ RingHom.Flat
          ((Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE W V hVW).hom) := by
  obtain ⟨U₀, hxU₀, h₀, hh₀⟩ := hprin
  have hc : h₀ ∈ Z.ideal U₀ := by
    rw [hh₀]
    exact Ideal.mem_span_singleton_self h₀
  have hstalk : stalkIdeal Z x hx
      = Ideal.span {(X.presheaf.germ (U₀ : X.Opens) x hxU₀).hom h₀} := by
    rw [stalkIdeal_eq_map_germ Z x hx U₀.2 hxU₀, hh₀, Ideal.map_span, Set.image_singleton]
  obtain ⟨W, hW, V, hV, hVW, hVU₀, hxV, a, hadef, hareg, hflat⟩ :=
    exists_affineOpen_isRegular_flat_quotient_of_mem_ideal f Z x hx U₀.2 hxU₀ h₀ hc
      (isSMulRegular_quotient_of_isEffectiveCartierDivisor_fibre f Z x hx hfib _ hstalk)
  refine ⟨W, hW, V, hV, hVW, hxV, a, hareg, ?_, hflat⟩
  rw [hadef, ← Z.map_ideal (U := ⟨V, hV⟩) (V := U₀) hVU₀, hh₀, Ideal.map_span,
    Set.image_singleton]
  rfl

/-! ### The local statement -/

/-- Let `f : X ⟶ S` be flat and locally of finite presentation, let
`Z` be a closed subscheme of `X` and let `x` be a point of `Z` whose fibre over `f x` is an
effective Cartier divisor in a neighbourhood of `x`.  If the ideal of `Z` is principal on some
affine open neighbourhood of `x`, then `Z` restricts to a relative effective Cartier divisor over
`S` on an affine open neighbourhood of `x`. -/
@[stacks 062Y "locally_principal_case"]
theorem exists_isRelativeEffectiveCartierDivisor_of_ideal_isPrincipal (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (Z : X.IdealSheafData) (x : X) (hx : x ∈ Z.support)
    (hprin : ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ (Z.ideal U).IsPrincipal)
    (hfib : ∃ V : (f.fiber (f x)).Opens, f.asFiber x ∈ V ∧
      IsEffectiveCartierDivisor ((Z.comap (f.fiberι (f x))).comap V.ι)) :
    ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧
      IsRelativeEffectiveCartierDivisor (V.ι ≫ f) (Z.comap V.ι) := by
  obtain ⟨W, hW, V, hV, hVW, hxV, a, hareg, hideal, hflat⟩ :=
    exists_affineOpen_isRegular_ideal_eq_span_of_fibre f Z x hx hprin hfib
  exact ⟨V, hxV, hV, isRelativeEffectiveCartierDivisor_comap_of_ideal_eq_span
    f Z hW hV hVW a hareg hideal hflat⟩

/-! ### The global statement -/

/-- A locally principal closed subscheme of a scheme flat and locally of finite presentation over
`S`, all of whose fibres are effective Cartier divisors, is a relative effective Cartier divisor
over `S`. -/
@[stacks 062Y "locally_principal_global_case", ega "IV 21.15.3.3" "forward direction"]
theorem isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (Z : X.IdealSheafData) (hZ : IsLocallyPrincipal Z)
    (hfib : ∀ s : S, IsEffectiveCartierDivisor (Z.comap (f.fiberι s))) :
    IsRelativeEffectiveCartierDivisor f Z := by
  have hchart : ∀ x : X, x ∈ Z.support →
      ∃ (W : S.Opens) (_hW : IsAffineOpen W) (V : X.Opens) (hV : IsAffineOpen V)
        (hVW : V ≤ f ⁻¹ᵁ W), x ∈ V ∧ ∃ a : Γ(X, V), IsRegular a ∧
          Z.ideal ⟨V, hV⟩ = Ideal.span {a} ∧ RingHom.Flat
            ((Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE W V hVW).hom) := by
    intro x hx
    refine exists_affineOpen_isRegular_ideal_eq_span_of_fibre f Z x hx (hZ x) ?_
    exact ⟨⊤, trivial, isPullbackDefined_of_flat (⊤ : (f.fiber (f x)).Opens).ι _ (hfib (f x))⟩
  refine ⟨isEffectiveCartierDivisor_of_forall_mem_support Z fun x hx => ?_, ?_⟩
  · obtain ⟨W, hW, V, hV, hVW, hxV, a, hareg, hideal, -⟩ := hchart x hx
    exact ⟨⟨V, hV⟩, a, hxV, hideal, isRegular_iff_mem_nonZeroDivisors.mp hareg⟩
  · let _ : IsZariskiLocalAtSource (@Flat) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
    choose W hW V hV hVW hxV a hareg hideal hflat using
      fun z : Z.subscheme => hchart (Z.subschemeι z) z.2
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat)
      (fun z : Z.subscheme => Z.subschemeι ⁻¹ᵁ V z) ?_ fun z => ?_
    · refine eq_top_iff.2 fun w _ => TopologicalSpace.Opens.mem_iSup.2 ⟨w, hxV w⟩
    · have h1 := flat_resLE_subschemeι_of_ideal_eq_span f Z (hW z) (hV z) (hVW z) (a z)
        (hideal z) (hflat z)
      have h2 : (Z.subschemeι ⁻¹ᵁ V z).ι ≫ Z.subschemeι ≫ f
          = (Z.subschemeι ≫ f).resLE (W z) (Z.subschemeι ⁻¹ᵁ V z)
            (fun w hw => hVW z hw) ≫ (W z).ι :=
        (Scheme.Hom.resLE_comp_ι (Z.subschemeι ≫ f) (fun w hw => hVW z hw)).symm
      rw [h2]
      have _ := h1
      infer_instance

end Stacks.Divisors

end
