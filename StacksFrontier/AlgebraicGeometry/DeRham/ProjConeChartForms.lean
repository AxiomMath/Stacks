module

public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalizationChart
public import StacksFrontier.RingTheory.Kaehler.FormsTransport
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChart
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.BaseSectionDictionary
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquareRing
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechFiltration
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangleInputs

/-!
# The relative forms of the cone over a standard open, as Kähler forms

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded `R`-algebra, `P = Proj A` and `L = Proj(⨁_d A_{≥ d})` the cone
of [Stacks, Tag 0EKG], both over `S = Spec R`. Over a standard open `D₊(g)` of `P` the cone is the
affine open `D₊(ψ g)` of `L`, with ring of functions `B₍ψ g₎`, and the relative forms of `L`
over `S` on it are the Kähler forms of `B₍ψ g₎` over `R`
(`Stacks.ProjConeChartForms.chartForms`). This file establishes that identification and its two
compatibilities: with restriction to a smaller standard open, and with pulling forms back along
the zero section, which on rings is the map `B₍ψ g₎ → A₍g₎` induced by `τ`.

## Main definitions

* `Stacks.ProjConeChartForms.baseL`, `Stacks.ProjConeChartForms.baseP`: the structure morphisms
  of `L` and of `P` over `Spec R`.
* `Stacks.ProjConeChartForms.chartForms`: the relative `p`-forms of `L` over `D₊(ψ g)` as the
  Kähler forms of `B₍ψ g₎` over `R`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation

universe u

namespace Stacks.ProjConeChartForms

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [_root_.GradedAlgebra 𝒜]

/-- The structure morphism `L ⟶ Spec R` of the cone. -/
abbrev baseL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R) :=
  Stacks.AlgebraicGeometry.ProjAndSpec.toSpecA (truncationConeData 𝒜) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- The structure morphism `P ⟶ Spec R`. -/
abbrev baseP : AlgebraicGeometry.Proj 𝒜 ⟶ Spec (CommRingCat.of R) :=
  AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))

variable {𝒜}

/-- `Spec` of a ring map, on global sections, is the ring map. -/
theorem specMap_appLE_top {S T : CommRingCat.{u}} (f : S ⟶ T) (e) :
    (Spec.map f).appLE ⊤ ⊤ e = (Scheme.ΓSpecIso S).hom ≫ f ≫ (Scheme.ΓSpecIso T).inv := by
  rw [Stacks.AlgebraicGeometry.ProjChartSections.appLE_top_top, ← Category.assoc,
    ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The structure morphism of `P` on a standard open**: through `A₍g₎ ≅ Γ(P, D₊(g))` it is the
`R`-algebra structure of `A₍g₎`. -/
theorem baseP_appLE {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) (e) :
    (baseP 𝒜).appLE ⊤ (AlgebraicGeometry.Proj.basicOpen 𝒜 g) e =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        CommRingCat.ofHom (algebraMap R (Away 𝒜 g)) ≫ AlgebraicGeometry.Proj.awayToSection 𝒜 g := by
  rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ _ (by simp) (by simp)]
  refine (congrArg₂ (fun a b => a ≫ b) (specMap_appLE_top _ _)
    (Stacks.BaseSectionDictionary.toSpecZero_appLE_basicOpen 𝒜 hg hd _)).trans ?_
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The structure morphism `L ⟶ Spec A` on a standard open `D₊(ψ g)`. -/
theorem toSpecA_appLE {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) (e) :
    (Stacks.AlgebraicGeometry.ProjAndSpec.toSpecA (truncationConeData 𝒜)).appLE ⊤
        (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) e =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
        CommRingCat.ofHom (((sigma 𝒜 : A ≃+* grading 𝒜 0) : A →+* grading 𝒜 0)) ≫
          CommRingCat.ofHom (fromZeroRingHom (grading 𝒜) (Submonoid.powers (psi 𝒜 g))) ≫
            AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 g) := by
  have hψ : psi 𝒜 g ∈ grading 𝒜 d := (psi 𝒜).map_mem hg
  rw [Stacks.AlgebraicGeometry.ProjAndSpec.toSpecA,
    ← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ _ (by simp) (by simp)]
  refine (congrArg₂ (fun a b => a ≫ b) (specMap_appLE_top _ _)
    (Stacks.BaseSectionDictionary.toSpecZero_appLE_basicOpen (grading 𝒜) hψ hd _)).trans ?_
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- **The structure morphism of `L` on a standard open**: through `B₍ψ g₎ ≅ Γ(L, D₊(ψ g))` it is
the `R`-algebra structure of `B₍ψ g₎`. -/
theorem baseL_appLE {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) (e) :
    (baseL 𝒜).appLE ⊤ (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) e =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        CommRingCat.ofHom (algebraMap R (Away (grading 𝒜) (psi 𝒜 g))) ≫
          AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 g) := by
  rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ _ (by simp) (by simp)]
  refine (congrArg₂ (fun a b => a ≫ b) (specMap_appLE_top _ _) (toSpecA_appLE hg hd _)).trans ?_
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-! ### Transported forms on a scheme over `Spec R` -/

section Generic

variable {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of R))

/-- **The relative forms of a scheme over `Spec R` on an affine open `V`, as the Kähler forms of an
`R`-algebra `C` identified with `Γ(X, V)`.** -/
def transportedForms {V : X.Opens} (hV : IsAffineOpen V) {C : Type u} [CommRing C] [Algebra R C]
    (e : C ≃+* Γ(X, V))
    (h : ∀ l, q.appLE ⊤ V (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top q V) l =
      e (algebraMap R C ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv l)))
    (p : ℕ) (ω : Γ(Scheme.Hom.relativeDifferentialForms q (p : ℤ), V)) :
    ⋀[C]^p (Ω[C⁄R]) :=
  KaehlerDifferential.formsTransport _ _ e h p
    (AlgebraicGeometry.DeRhamKatzOdaCech.formsEquiv q hV p ω)

/-- The transport of relative forms to Kähler forms of `C` is injective. -/
theorem transportedForms_injective {V : X.Opens} (hV : IsAffineOpen V) {C : Type u} [CommRing C]
    [Algebra R C] (e : C ≃+* Γ(X, V)) (h) (p : ℕ) :
    Function.Injective (transportedForms q hV e h p) := fun _ _ hω =>
  (AlgebraicGeometry.DeRhamKatzOdaCech.formsEquiv q hV p).injective
    ((KaehlerDifferential.formsTransport _ _ e h p).injective hω)

/-- The transport of relative forms to Kähler forms of `C` is surjective. -/
theorem transportedForms_surjective {V : X.Opens} (hV : IsAffineOpen V) {C : Type u} [CommRing C]
    [Algebra R C] (e : C ≃+* Γ(X, V)) (h) (p : ℕ) :
    Function.Surjective (transportedForms q hV e h p) := fun η => by
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.formsTransport _ _ e h p).surjective η
  obtain ⟨ω, rfl⟩ := (AlgebraicGeometry.DeRhamKatzOdaCech.formsEquiv q hV p).surjective y
  exact ⟨ω, rfl⟩

/-- The transport of relative forms to Kähler forms of `C` sends `0` to `0`. -/
theorem transportedForms_zero {V : X.Opens} (hV : IsAffineOpen V) {C : Type u} [CommRing C]
    [Algebra R C] (e : C ≃+* Γ(X, V)) (h) (p : ℕ) : transportedForms q hV e h p 0 = 0 := by
  unfold transportedForms
  rw [AddEquiv.map_zero, AddEquiv.map_zero]

/-- The transport of relative forms to Kähler forms of `C` is additive. -/
theorem transportedForms_add {V : X.Opens} (hV : IsAffineOpen V) {C : Type u} [CommRing C]
    [Algebra R C] (e : C ≃+* Γ(X, V)) (h) (p : ℕ) (ω ω') :
    transportedForms q hV e h p (ω + ω') =
      transportedForms q hV e h p ω + transportedForms q hV e h p ω' := by
  unfold transportedForms
  rw [AddEquiv.map_add, AddEquiv.map_add]

/-- **Transported forms commute with restriction**, for any scheme over `Spec R` and any two
affine opens `V' ≤ V` whose rings are identified with `R`-algebras `C₂`, `C₁` compatibly with a
map `C₁ → C₂`. -/
theorem transportedForms_restrict {V V' : X.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (hle : V' ≤ V) {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra R C₁] [Algebra R C₂] (e₁ : C₁ ≃+* Γ(X, V)) (e₂ : C₂ ≃+* Γ(X, V')) (h₁) (h₂)
    (ρ : C₁ →ₐ[R] C₂) (hρ : ∀ c, e₂ (ρ c) = X.presheaf.map (homOfLE hle).op (e₁ c)) (p : ℕ)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms q (p : ℤ), V)) :
    transportedForms q hV' e₂ h₂ p
        ((Scheme.Hom.relativeDifferentialForms q (p : ℤ)).presheaf.map (homOfLE hle).op ω) =
      KaehlerDifferential.formsₛₗ ρ p (transportedForms q hV e₁ h₁ p ω) := by
  unfold transportedForms
  rw [AlgebraicGeometry.DeRhamKatzOdaCech.formsEquiv_restrict q hV hV' hle p ω]
  exact KaehlerDifferential.formsTransport_formsMap _ _ _ _ _ _ _ _ _ ρ hρ p _

/-- **Transported forms commute with pulling back along a morphism over `Spec R`**: for
`f : X' ⟶ X` and affine opens `U ⊆ X`, `f⁻¹U ⊆ X'` with rings identified with `C` and `E`
compatibly with a map `ε : C → E`, the pullback of forms is the map of Kähler forms along `ε`. -/
theorem transportedForms_pullback {X' : Scheme.{u}} (f : X' ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen (f ⁻¹ᵁ U)) {C E : Type u} [CommRing C] [CommRing E]
    [Algebra R C] [Algebra R E] (eC : C ≃+* Γ(X, U)) (eE : E ≃+* Γ(X', f ⁻¹ᵁ U)) (hC) (hE)
    (ε : C →ₐ[R] E) (hε : ∀ c, eE (ε c) = f.app U (eC c)) (p : ℕ)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms q (p : ℤ), U)) :
    transportedForms (f ≫ q) hU' eE hE p
        (((Scheme.Hom.deRhamFormsPushforwardHom f q (f ≫ q) (𝟙 _)
          (Category.comp_id _).symm).app (p : ℤ)).val.app (op U) ω) =
      KaehlerDifferential.formsₛₗ ε p (transportedForms q hU eC hC p ω) := by
  have h0 := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_deRhamFormsPushforwardHom
    f q (f ≫ q) hU hU' (isAffineOpen_top _)
    (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top q U)
    (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top (f ≫ q) (f ⁻¹ᵁ U))
    (Category.comp_id _).symm p
    (AlgebraicGeometry.DeRhamKatzOdaCech.formsEquiv q hU p ω)
  have hinv : (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso q hU (isAffineOpen_top _)
      (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top q U) p).inv
        (AlgebraicGeometry.DeRhamKatzOdaCech.formsEquiv q hU p ω) = ω :=
    (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso q hU (isAffineOpen_top _)
      (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top q U)
        p).toLinearEquiv.symm_apply_apply ω
  rw [hinv] at h0
  unfold transportedForms
  refine (congrArg (KaehlerDifferential.formsTransport _ _ eE hE p) h0).trans ?_
  exact KaehlerDifferential.formsTransport_formsMap _ _ (f.app U)
    (Stacks.AlgebraicGeometry.AffineOpenDeRham.appLE_comp_app_eq_appLE f q (f ≫ q)
      (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top q U)
      (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top (f ≫ q) (f ⁻¹ᵁ U))
      (Category.comp_id _).symm) _ _ _ _ _ ε hε p _

end Generic

/-! ### The forms on a chart -/

variable (𝒜)

/-- The isomorphism `Γ(Spec R, ⊤) ≅ R`. -/
abbrev baseRingEquiv : Γ(Spec (CommRingCat.of R), ⊤) ≃+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv

/-- The identification `B₍ψ g₎ ≅ Γ(L, D₊(ψ g))`. -/
abbrev chartRingEquiv {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) :
    Away (grading 𝒜) (psi 𝒜 g) ≃+*
      Γ(AlgebraicGeometry.Proj (grading 𝒜),
        AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) :=
  (AlgebraicGeometry.Proj.basicOpenIsoAway (grading 𝒜) (psi 𝒜 g) ((psi 𝒜).map_mem hg)
    hd).commRingCatIsoToRingEquiv

variable {𝒜}

/-- The identification `B₍ψ g₎ ≅ Γ(L, D₊(ψ g))` is `Proj.awayToSection`. -/
theorem chartRingEquiv_apply {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d)
    (c : Away (grading 𝒜) (psi 𝒜 g)) :
    chartRingEquiv 𝒜 hg hd c = AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 g) c :=
  rfl

/-- The structure map of `L` over `D₊(ψ g)` is the `R`-algebra structure of `B₍ψ g₎`. -/
theorem chart_hyp (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R))
    (hsL : sL = baseL 𝒜) {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) (e) (l) :
    sL.appLE ⊤ (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) e l =
      chartRingEquiv 𝒜 hg hd (algebraMap R (Away (grading 𝒜) (psi 𝒜 g))
        (baseRingEquiv l)) := by
  subst hsL
  rw [baseL_appLE hg hd e]
  rfl

/-- The chart `D₊(ψ g)` is affine. -/
theorem isAffineOpen_chart {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) :
    IsAffineOpen (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) :=
  AlgebraicGeometry.Proj.isAffineOpen_basicOpen (grading 𝒜) (psi 𝒜 g) ((psi 𝒜).map_mem hg) hd

/-- **The relative forms of `L` over `D₊(ψ g)` are the Kähler forms of `B₍ψ g₎` over `R`**: the
identification of the forms over an affine open with Kähler forms, followed by the transport along
`Γ(Spec R, ⊤) ≅ R` and `B₍ψ g₎ ≅ Γ(L, D₊(ψ g))`. -/
abbrev chartForms (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R))
    (hsL : sL = baseL 𝒜) {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) (p : ℕ) :
    Γ(Scheme.Hom.relativeDifferentialForms sL (p : ℤ),
        AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) →
      ⋀[Away (grading 𝒜) (psi 𝒜 g)]^p (Ω[Away (grading 𝒜) (psi 𝒜 g)⁄R]) :=
  transportedForms sL (isAffineOpen_chart hg hd) (chartRingEquiv 𝒜 hg hd)
    (chart_hyp sL hsL hg hd _) p

/-- The restriction `B₍ψ g₎ → B₍ψ (g c)₎` of functions on the cone, as a map of `R`-algebras. -/
def chartAwayMap {g c g' : A} {dc : ℕ} (hc : c ∈ 𝒜 dc) (hx : g' = g * c) :
    Away (grading 𝒜) (psi 𝒜 g) →ₐ[R] Away (grading 𝒜) (psi 𝒜 g') where
  __ := awayMap (grading 𝒜) ((psi 𝒜).map_mem hc) (by rw [hx, map_mul]; rfl)
  commutes' r := awayMap_fromZeroRingHom _ _ _ _

/-- The map `chartAwayMap` is the map `awayMap` of homogeneous localizations. -/
theorem chartAwayMap_apply {g c g' : A} {dc : ℕ} (hc : c ∈ 𝒜 dc) (hx : g' = g * c)
    (z : Away (grading 𝒜) (psi 𝒜 g)) :
    chartAwayMap hc hx z = awayMap (grading 𝒜) ((psi 𝒜).map_mem hc) (by rw [hx, map_mul]; rfl) z :=
  rfl

/-- The localization map `A_g → A_{g'}` for `g ∣ g'`, as a map of `R`-algebras. -/
def locMap {g g' : A} (hdiv : g ∣ g') : Localization.Away g →ₐ[R] Localization.Away g' :=
  IsLocalization.liftAlgHom (M := Submonoid.powers g)
    (f := IsScalarTower.toAlgHom R A (Localization.Away g')) (fun y => by
      obtain ⟨_, k, rfl⟩ := y
      change IsUnit (algebraMap A (Localization.Away g') (g ^ k))
      rw [map_pow]
      exact (isUnit_of_dvd_unit (map_dvd (algebraMap A (Localization.Away g')) hdiv)
        (IsLocalization.Away.algebraMap_isUnit g')).pow k)

/-- The localization map `A_g → A_{g'}` is compatible with the maps from `A`. -/
theorem locMap_algebraMap {g g' : A} (hdiv : g ∣ g') (a : A) :
    locMap (R := R) hdiv (algebraMap A _ a) = algebraMap A _ a :=
  IsLocalization.lift_eq _ _

/-- **Restriction of functions on the cone is localization on the punctured cone**: the map
`B₍ψ g₎ → B₍ψ (gc)₎` followed by `B₍ψ (gc)₎ → A_{gc}` is `B₍ψ g₎ → A_g → A_{gc}`. -/
theorem restrictAlg_chartAwayMap {g c g' : A} {d dc d' : ℕ} (hgd : g ∈ 𝒜 (d + 1))
    (hc : c ∈ 𝒜 dc) (hgd' : g' ∈ 𝒜 (d' + 1)) (hx : g' = g * c)
    (z : Away (grading 𝒜) (psi 𝒜 g)) :
    Stacks.Truncation.Chart.restrictAlg hgd' (chartAwayMap hc hx z) =
      locMap (R := R) ⟨c, hx⟩ (Stacks.Truncation.Chart.restrictAlg hgd z) := by
  rw [Stacks.Truncation.Chart.restrictAlg_apply, Stacks.Truncation.Chart.restrictAlg_apply,
    chartAwayMap_apply, awayToLocalization, awayToLocalization, RingHom.comp_apply,
    RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_awayMap]
  have key : (Localization.awayLift ((algebraMap A (Localization.Away g')).comp
        (forgetDegree 𝒜)) (psi 𝒜 g')
        (isUnit_iff_exists_inv.mpr ⟨awayFrac g' 1 1, comp_psi_mul_awayFrac 𝒜⟩)).comp
      (Localization.awayLift (algebraMap (TruncationRing 𝒜) (Localization.Away (psi 𝒜 g')))
        (psi 𝒜 g) (isUnit_of_dvd_unit
          (map_dvd (algebraMap (TruncationRing 𝒜) (Localization.Away (psi 𝒜 g')))
            (⟨psi 𝒜 c, by rw [hx, map_mul]⟩ : psi 𝒜 g ∣ psi 𝒜 g'))
          (IsLocalization.Away.algebraMap_isUnit _))) =
      (locMap (R := R) ⟨c, hx⟩ : Localization.Away g →+* Localization.Away g').comp
        (Localization.awayLift ((algebraMap A (Localization.Away g)).comp (forgetDegree 𝒜))
          (psi 𝒜 g) (isUnit_iff_exists_inv.mpr ⟨awayFrac g 1 1, comp_psi_mul_awayFrac 𝒜⟩)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (psi 𝒜 g)) (RingHom.ext fun b => ?_)
    simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, Localization.awayLift]
    exact (locMap_algebraMap (R := R) ⟨c, hx⟩ _).symm
  exact RingHom.congr_fun key _

/-- The chart identification commutes with restriction of functions. -/
theorem chartRingEquiv_chartAwayMap {g c g' : A} {d dc d' : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d)
    (hc : c ∈ 𝒜 dc) (hg' : g' ∈ 𝒜 d') (hd' : 0 < d') (hx : g' = g * c)
    (hle : AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g') ≤
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))
    (z : Away (grading 𝒜) (psi 𝒜 g)) :
    chartRingEquiv 𝒜 hg' hd' (chartAwayMap hc hx z) =
      (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map (homOfLE hle).op
        (chartRingEquiv 𝒜 hg hd z) := by
  rw [chartRingEquiv_apply, chartRingEquiv_apply, chartAwayMap_apply]
  have h := AlgebraicGeometry.Proj.awayMap_awayToSection (grading 𝒜) ((psi 𝒜).map_mem hc)
    (f := psi 𝒜 g) (x := psi 𝒜 g') (by rw [hx, map_mul]; rfl)
  have h' := ConcreteCategory.congr_hom h z
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h'
  exact h'

/-- **The chart identification of the forms commutes with restriction** to a smaller standard
open. -/
theorem chartForms_restrict (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R))
    (hsL : sL = baseL 𝒜) {g c g' : A} {d dc d' : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) (hc : c ∈ 𝒜 dc)
    (hg' : g' ∈ 𝒜 d') (hd' : 0 < d') (hx : g' = g * c)
    (hle : AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g') ≤
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) (p : ℕ)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms sL (p : ℤ),
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))) :
    chartForms sL hsL hg' hd' p
        ((Scheme.Hom.relativeDifferentialForms sL (p : ℤ)).presheaf.map (homOfLE hle).op ω) =
      KaehlerDifferential.formsₛₗ (chartAwayMap hc hx) p (chartForms sL hsL hg hd p ω) :=
  transportedForms_restrict sL (isAffineOpen_chart hg hd) (isAffineOpen_chart hg' hd')
    hle (chartRingEquiv 𝒜 hg hd) (chartRingEquiv 𝒜 hg' hd') _ _ (chartAwayMap hc hx)
    (chartRingEquiv_chartAwayMap hg hd hc hg' hd' hx hle) p ω

/-! ### The zero section on a chart -/

/-- The zero section, as Mathlib's morphism of `Proj` induced by `τ`. -/
abbrev zeroMap : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (grading 𝒜) :=
  AlgebraicGeometry.Proj.map (truncationConeData 𝒜).tau
    (Stacks.AlgebraicGeometry.ProjAndSpec.irrelevant_le_map_tau (truncationConeData 𝒜))

variable (𝒜) in
/-- The zero section followed by the structure morphism of `L` is the structure morphism of `P`. -/
theorem zeroMap_comp_baseL : zeroMap (𝒜 := 𝒜) ≫ baseL 𝒜 = baseP 𝒜 := by
  rw [zeroMap,
    ← Stacks.AlgebraicGeometry.ProjAndSpec.zeroSection_eq_projMap (truncationConeData 𝒜), baseL,
    ← Category.assoc, Stacks.AlgebraicGeometry.ProjAndSpec.zeroSection_comp_toSpecA,
    Stacks.AlgebraicGeometry.ProjAndSpec.zToX, Category.assoc, ← Spec.map_comp, baseP]
  congr 2
  ext r
  show (DirectSum.decompose 𝒜 (algebraMap R A r) 0 : A) = algebraMap R A r
  exact DirectSum.decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 r)

/-- The open `D₊(τ (ψ g))` of `P` is `D₊(g)`. -/
theorem basicOpen_tau_psi (g : A) :
    AlgebraicGeometry.Proj.basicOpen 𝒜 ((truncationConeData 𝒜).tau ((truncationConeData 𝒜).psi g)) =
      AlgebraicGeometry.Proj.basicOpen 𝒜 g := by
  show AlgebraicGeometry.Proj.basicOpen 𝒜 (tau 𝒜 (psi 𝒜 g)) = _
  rw [tau_psi_apply]

/-- The ring of `D₊(τ (ψ g)) = D₊(g)` is `A₍g₎`. -/
abbrev zeroRingEquiv {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) :
    Away 𝒜 g ≃+* Γ(AlgebraicGeometry.Proj 𝒜, AlgebraicGeometry.Proj.basicOpen 𝒜
      ((truncationConeData 𝒜).tau ((truncationConeData 𝒜).psi g))) :=
  (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 g hg hd).commRingCatIsoToRingEquiv.trans
    ((AlgebraicGeometry.Proj 𝒜).presheaf.mapIso
      (eqToIso (basicOpen_tau_psi g)).op).commRingCatIsoToRingEquiv

/-- Sections over equal standard opens, read through `HomogeneousLocalization.map τ`. -/
theorem awayToSection_map_tau {g y : A} (hy : y = g)
    (h₁ : Submonoid.powers (psi 𝒜 g) ≤ (Submonoid.powers y).comap (tau 𝒜))
    (c : Away (grading 𝒜) (psi 𝒜 g)) :
    AlgebraicGeometry.Proj.awayToSection 𝒜 y (HomogeneousLocalization.map (tau 𝒜) h₁ c) =
      (AlgebraicGeometry.Proj 𝒜).presheaf.map (eqToHom (by rw [hy])).op
        (AlgebraicGeometry.Proj.awayToSection 𝒜 g (Stacks.Truncation.Chart.zeroHom g c)) := by
  subst hy
  rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The zero section on functions is the restriction `B₍ψ g₎ → A₍g₎` induced by `τ`.** -/
theorem zeroRingEquiv_zeroAlg {g : A} {d : ℕ} (hg : g ∈ 𝒜 (d + 1))
    (c : Away (grading 𝒜) (psi 𝒜 g)) :
    zeroRingEquiv hg (Nat.succ_pos d) (Stacks.Truncation.Chart.zeroAlg hg c) =
      (zeroMap (𝒜 := 𝒜)).app (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))
        (chartRingEquiv 𝒜 hg (Nat.succ_pos d) c) := by
  have h := AlgebraicGeometry.Proj.awayToSection_comp_appLE (truncationConeData 𝒜).tau
    (Stacks.AlgebraicGeometry.ProjAndSpec.irrelevant_le_map_tau (truncationConeData 𝒜))
    ((psi 𝒜).map_mem hg)
  have h' := ConcreteCategory.congr_hom h c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h'
  rw [Scheme.Hom.app_eq_appLE, chartRingEquiv_apply]
  exact (awayToSection_map_tau (tau_psi_apply 𝒜 g) _ c).symm.trans h'.symm

/-- The structure morphism of `P` over `D₊(τ (ψ g))`, through `zeroRingEquiv`. -/
theorem zero_hyp (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R))
    (hsL : sL = baseL 𝒜) {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) (e) (l) :
    (zeroMap (𝒜 := 𝒜) ≫ sL).appLE ⊤ (AlgebraicGeometry.Proj.basicOpen 𝒜
        ((truncationConeData 𝒜).tau ((truncationConeData 𝒜).psi g))) e l =
      zeroRingEquiv hg hd (algebraMap R (Away 𝒜 g) (baseRingEquiv l)) := by
  subst hsL
  rw [Stacks.AlgebraicGeometry.ProjChartSections.appLE_congr_hom (zeroMap_comp_baseL 𝒜) _ _ e
    (by simp), ← Scheme.Hom.appLE_map (baseP 𝒜) (U := ⊤)
      (V := AlgebraicGeometry.Proj.basicOpen 𝒜 g) (by simp)
      (eqToHom (basicOpen_tau_psi (𝒜 := 𝒜) g)).op]
  refine (congrArg (fun φ => (φ ≫ (AlgebraicGeometry.Proj 𝒜).presheaf.map
    (eqToHom (basicOpen_tau_psi (𝒜 := 𝒜) g)).op) l) (baseP_appLE hg hd _)).trans ?_
  rfl

/-- The preimage of the chart `D₊(ψ g)` under the zero section is affine. -/
private theorem isAffineOpen_zeroMap_preimage {g : A} {d : ℕ} (hg : g ∈ 𝒜 (d + 1)) :
    IsAffineOpen ((zeroMap (𝒜 := 𝒜)) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) :=
  AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 _
    ((truncationConeData 𝒜).tau.map_mem ((truncationConeData 𝒜).psi.map_mem hg)) (Nat.succ_pos d)

/-- Transported forms on `P` of the pullback along the zero section are the Kähler forms of
`zeroAlg` applied to the transported forms on the cone. -/
private theorem transportedForms_zeroMap
    (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R))
    (hsL : sL = baseL 𝒜) {g : A} {d : ℕ} (hg : g ∈ 𝒜 (d + 1)) (p : ℕ)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms sL (p : ℤ),
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))) :
    transportedForms (zeroMap ≫ sL) (isAffineOpen_zeroMap_preimage hg)
        (zeroRingEquiv hg (Nat.succ_pos d)) (zero_hyp sL hsL hg (Nat.succ_pos d) _) p
        (((Scheme.Hom.deRhamFormsPushforwardHom (zeroMap (𝒜 := 𝒜)) sL (zeroMap ≫ sL) (𝟙 _)
          (Category.comp_id _).symm).app (p : ℤ)).val.app
            (op (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))) ω) =
      KaehlerDifferential.formsₛₗ (Stacks.Truncation.Chart.zeroAlg hg) p
        (chartForms sL hsL hg (Nat.succ_pos d) p ω) :=
  transportedForms_pullback sL (zeroMap (𝒜 := 𝒜))
    (isAffineOpen_chart hg (Nat.succ_pos d)) (isAffineOpen_zeroMap_preimage hg)
    (chartRingEquiv 𝒜 hg (Nat.succ_pos d)) (zeroRingEquiv hg (Nat.succ_pos d))
    (chart_hyp sL hsL hg (Nat.succ_pos d) _) (zero_hyp sL hsL hg (Nat.succ_pos d) _)
    (Stacks.Truncation.Chart.zeroAlg hg) (zeroRingEquiv_zeroAlg hg) p ω

/-- **Pulling a form on the cone back to `P` along the zero section, on a chart, is the map of
Kähler forms along `B₍ψ g₎ → A₍g₎`.** In particular it vanishes exactly when that map kills the
form. -/
theorem pushforwardHom_zeroMap_eq_zero_iff
    (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R))
    (hsL : sL = baseL 𝒜) {g : A} {d : ℕ} (hg : g ∈ 𝒜 (d + 1)) (p : ℕ)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms sL (p : ℤ),
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))) :
    ((Scheme.Hom.deRhamFormsPushforwardHom (zeroMap (𝒜 := 𝒜)) sL (zeroMap ≫ sL) (𝟙 _)
        (Category.comp_id _).symm).app (p : ℤ)).val.app
          (op (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))) ω = 0 ↔
      KaehlerDifferential.formsₛₗ (Stacks.Truncation.Chart.zeroAlg hg) p
        (chartForms sL hsL hg (Nat.succ_pos d) p ω) = 0 := by
  rw [← transportedForms_zeroMap sL hsL hg p ω]
  exact ((transportedForms_injective _ _ _ _ p).eq_iff' (transportedForms_zero _ _ _ _ p)).symm

/-- `pushforwardHom_zeroMap_eq_zero_iff` for the canonical map `Ω^p_{L/S} ⟶ 0_*Ω^p_{P/S}` of any
morphism equal to the zero section. -/
theorem formsDirectImageComparison_app_eq_zero_iff
    (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R))
    (hsL : sL = baseL 𝒜) (z : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (grading 𝒜))
    (hz : z = zeroMap) {g : A} {d : ℕ} (hg : g ∈ 𝒜 (d + 1)) (p : ℕ)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms sL (p : ℤ),
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))) :
    (Scheme.Hom.formsDirectImageComparison z sL (p : ℤ)).app
        (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) ω = 0 ↔
      KaehlerDifferential.formsₛₗ (Stacks.Truncation.Chart.zeroAlg hg) p
        (chartForms sL hsL hg (Nat.succ_pos d) p ω) = 0 := by
  subst hz
  rw [Stacks.DeRham.BlowupTriangle.formsDirectImageComparison_eq]
  exact pushforwardHom_zeroMap_eq_zero_iff sL hsL hg p ω

/-- `formsDirectImageComparison_app_eq_zero_iff` for the zero section of the cone data itself. -/
theorem formsDirectImageComparison_zeroSection_app_eq_zero_iff
    (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R))
    (hsL : sL = baseL 𝒜) {g : A} {d : ℕ} (hg : g ∈ 𝒜 (d + 1)) (p : ℕ)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms sL (p : ℤ),
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))) :
    (Scheme.Hom.formsDirectImageComparison
        (Stacks.AlgebraicGeometry.ProjAndSpec.zeroSection (truncationConeData 𝒜)) sL (p : ℤ)).app
        (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) ω = 0 ↔
      KaehlerDifferential.formsₛₗ (Stacks.Truncation.Chart.zeroAlg hg) p
        (chartForms sL hsL hg (Nat.succ_pos d) p ω) = 0 :=
  formsDirectImageComparison_app_eq_zero_iff sL hsL _
    (Stacks.AlgebraicGeometry.ProjAndSpec.zeroSection_eq_projMap _) hg p ω

variable (𝒜) in
/-- The standard open `D₊(ψ g)` of the cone over which `chartForms` is stated. -/
abbrev chartOpen (g : A) : (AlgebraicGeometry.Proj (grading 𝒜)).Opens :=
  AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)

section ChartFormsMaps

variable (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R)) (hsL : sL = baseL 𝒜)
  {g : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hd : 0 < d) (p : ℕ)

/-- The identification `chartForms` of forms over `D₊(ψ g)` is additive. -/
theorem chartForms_add (ω ω' : Γ(Scheme.Hom.relativeDifferentialForms sL (p : ℤ),
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))) :
    chartForms sL hsL hg hd p (ω + ω') =
      chartForms sL hsL hg hd p ω + chartForms sL hsL hg hd p ω' :=
  transportedForms_add _ _ _ _ p ω ω'

/-- The identification `chartForms` of forms over `D₊(ψ g)` is injective. -/
theorem chartForms_injective : Function.Injective (chartForms sL hsL hg hd p) :=
  transportedForms_injective _ _ _ _ p

/-- The identification `chartForms` of forms over `D₊(ψ g)` is surjective. -/
theorem chartForms_surjective : Function.Surjective (chartForms sL hsL hg hd p) :=
  transportedForms_surjective _ _ _ _ p

end ChartFormsMaps

/-- **Restricting forms on the punctured cone commutes with restriction to a smaller chart**:
`B₍ψ g₎ → B₍ψ (gc)₎ → A_{gc}` is `B₍ψ g₎ → A_g → A_{gc}` on forms. -/
theorem formsₛₗ_restrictAlg_chartAwayMap {g c g' : A} {d dc d' : ℕ} (hgd : g ∈ 𝒜 (d + 1))
    (hc : c ∈ 𝒜 dc) (hgd' : g' ∈ 𝒜 (d' + 1)) (hx : g' = g * c) (p : ℕ)
    (w : ⋀[Away (grading 𝒜) (psi 𝒜 g)]^p (Ω[Away (grading 𝒜) (psi 𝒜 g)⁄R])) :
    KaehlerDifferential.formsₛₗ (Stacks.Truncation.Chart.restrictAlg hgd') p
        (KaehlerDifferential.formsₛₗ (chartAwayMap hc hx) p w) =
      KaehlerDifferential.formsₛₗ (locMap (R := R) ⟨c, hx⟩) p
        (KaehlerDifferential.formsₛₗ (Stacks.Truncation.Chart.restrictAlg hgd) p w) := by
  have h : (Stacks.Truncation.Chart.restrictAlg hgd').comp (chartAwayMap hc hx) =
      (locMap (R := R) ⟨c, hx⟩).comp (Stacks.Truncation.Chart.restrictAlg hgd) :=
    AlgHom.ext fun z => restrictAlg_chartAwayMap hgd hc hgd' hx z
  exact (KaehlerDifferential.formsₛₗ_comp _ _ p w).trans
    ((congrArg (fun φ => KaehlerDifferential.formsₛₗ φ p w) h).trans
      (KaehlerDifferential.formsₛₗ_comp _ _ p w).symm)

/-- **Pulling forms back along the zero section is surjective on a chart** `D₊(ψ g)` with
`g = u h`, `u` of degree one: a form on `D₊(g) ⊆ P` is the restriction of its pullback along
`A₍g₎ → A₍g₎[X] = B₍ψ g₎`. -/
theorem surjective_pushforwardHom_zeroMap
    (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R))
    (hsL : sL = baseL 𝒜) {u h g : A} {d : ℕ} (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g)
    (p : ℕ) :
    Function.Surjective (((Scheme.Hom.deRhamFormsPushforwardHom (zeroMap (𝒜 := 𝒜)) sL
        (zeroMap ≫ sL) (𝟙 _) (Category.comp_id _).symm).app (p : ℤ)).val.app
          (op (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)))) := by
  have hgd := Stacks.GradedLaurent.mem_of_mul_eq 𝒜 hu hh hg
  have hinc : (Stacks.Truncation.Chart.zeroAlg hgd).comp
      ((Stacks.Truncation.Chart.polyAlgEquiv hu hh hg : Polynomial (Away 𝒜 g) →ₐ[R] _).comp
        (PolynomialDeRham.inclAlg R (Away 𝒜 g))) = AlgHom.id R _ :=
    (AlgHom.comp_assoc _ _ _).symm.trans
      ((congrArg (fun φ => φ.comp (PolynomialDeRham.inclAlg R (Away 𝒜 g)))
        (Stacks.Truncation.Chart.zeroAlg_comp_polyAlgEquiv hu hh hg)).trans
        PolynomialDeRham.evalZeroAlg_comp_inclAlg)
  have hU' := isAffineOpen_zeroMap_preimage (𝒜 := 𝒜) hgd
  intro η
  have e := chartForms_surjective sL hsL hgd (Nat.succ_pos d) p
    (KaehlerDifferential.formsₛₗ ((Stacks.Truncation.Chart.polyAlgEquiv hu hh hg :
      Polynomial (Away 𝒜 g) →ₐ[R] _).comp (PolynomialDeRham.inclAlg R (Away 𝒜 g))) p
      (transportedForms (zeroMap ≫ sL) hU' (zeroRingEquiv hgd (Nat.succ_pos d))
        (zero_hyp sL hsL hgd (Nat.succ_pos d) _) p η))
  refine ⟨e.choose, transportedForms_injective (zeroMap ≫ sL) hU'
    (zeroRingEquiv hgd (Nat.succ_pos d)) (zero_hyp sL hsL hgd (Nat.succ_pos d) _) p ?_⟩
  exact (transportedForms_zeroMap sL hsL hgd p e.choose).trans
    ((congrArg (KaehlerDifferential.formsₛₗ (Stacks.Truncation.Chart.zeroAlg hgd) p)
      e.choose_spec).trans ((KaehlerDifferential.formsₛₗ_comp _ _ p _).trans
        ((congrArg (fun φ => KaehlerDifferential.formsₛₗ φ p _) hinc).trans
          (KaehlerDifferential.formsₛₗ_id p _))))

/-- `surjective_pushforwardHom_zeroMap` for the comparison map of the zero section of the cone
data. -/
theorem surjective_formsDirectImageComparison_zeroSection_app
    (sL : AlgebraicGeometry.Proj (grading 𝒜) ⟶ Spec (CommRingCat.of R))
    (hsL : sL = baseL 𝒜) {u h g : A} {d : ℕ} (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g)
    (p : ℕ) :
    Function.Surjective ((Scheme.Hom.formsDirectImageComparison
        (Stacks.AlgebraicGeometry.ProjAndSpec.zeroSection (truncationConeData 𝒜)) sL (p : ℤ)).app
        (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g))) := by
  rw [Stacks.AlgebraicGeometry.ProjAndSpec.zeroSection_eq_projMap,
    Stacks.DeRham.BlowupTriangle.formsDirectImageComparison_eq]
  exact surjective_pushforwardHom_zeroMap sL hsL hu hh hg p

end Stacks.ProjConeChartForms

end
