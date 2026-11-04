module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeConormal
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEtaleSection
public import StacksFrontier.AlgebraicGeometry.FormsTrace.RelativeSections
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AffineFractionBoundary
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassSpellings
public import StacksFrontier.RingTheory.Kaehler.EquationWedgeColon
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Stalk

/-!
# The Gysin map of a rational point is not zero

Let `π : X ⟶ Spec k` be smooth of relative dimension `d` over a field and let `i : Z ⟶ X` be a
closed immersion with `Z ≅ Spec k` over `k`, the reduced closed subscheme of a `k`-rational point
`x`. The sheaf-level Gysin map

`γ^0 : i_*𝒪_Z = i_*Ω^0_{Z/k} ⟶ i_*ℋ^d_Z(Ω^d_{X/k})`

of [Stacks, Tag 0G86] is not zero. This is the local computation at the end of the proof of
[Stacks, Tag 0G8E]: on an affine neighbourhood `U = Spec R` of `x` on which `f₁, …, f_d` generate
the ideal of `x`, the map `γ^0` sends `1` to the class of `d f₁ ∧ ⋯ ∧ d f_d / (f₁ ⋯ f_d)` in the
top local cohomology `H^d_{(f₁, …, f_d)}(Ω^d_R)`, and that class is not zero.

## Main results

* `Stacks.Gysin.conormalGysinHom_ne_zero_of_isIso`: **the Gysin map `γ^0` of a rational point is
  not zero**, at every relative dimension `d`.
* `Stacks.Gysin.chartGysin_eq_zero_of_conormalGysinHom_eq_zero`: if the Gysin map of
  [Stacks, Tag 0G86] vanishes, so does the Gysin map of [Stacks, Tag 0G83] of every equation chart.
* `Stacks.Gysin.gysinFormulaHom_ne_zero`: on an affine chart whose ring `B` is Noetherian, with a
  Koszul-regular system of equations of an `A`-rational point and `Ω_{B/A}` free of rank `c ≥ 1`,
  the Gysin formula of [Stacks, Tag 0G83] in degree `0` is not zero.
* `Stacks.Gysin.gysinFormulaHom_empty_ne_zero`: the same with no equations, on a nonempty scheme.
* `Stacks.Gysin.conormalGysinHom_ne_zero_of_conormalRank_zero`: the case `d = 0`, over any base.

## Implementation notes

At positive rank the chart is chosen in two steps: an affine neighbourhood on which `Z` is cut out
by a Koszul-regular family of exactly `d` equations
(`Stacks.DeRham.GysinCohomologyDeRhamKoszul.exists_affineOpen_koszulRegular_equations`), shrunk to
an affine open on which `Ω_{X/k}` has a basis
(`Stacks.Discriminant.exists_isAffineOpen_basis_kaehlerDifferential`). On that chart a vanishing
`γ^0` makes the class of `d f₁ ∧ ⋯ ∧ d f_d / (f₁ ⋯ f_d)` vanish in the cokernel of the last
differential of the extended alternating Čech complex, the class map of [Stacks, Tag 0G7Q] being
that class followed by isomorphisms; on an affine scheme this gives
`(f₁ ⋯ f_d)^n · d f₁ ∧ ⋯ ∧ d f_d ∈ (f₁^{n+1}, …, f_d^{n+1}) Γ(Ω^d)`
(`Stacks.Perfect.SupportedFraction.exists_prod_pow_smul_mem_of_cokernelπ_fractionHom_eq_zero`);
read in `⋀^d Ω_{B/A}` through [Stacks, Tag 01UT] and [Stacks, Tag 01I8], that relation is
impossible by `KaehlerDifferential.prod_pow_smul_ιMulti_D_notMem`.

## References

* [Stacks Project, Tag 0G8E](https://stacks.math.columbia.edu/tag/0G8E)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ConormalEquations
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The ordered product of degree-one relative differential forms is their ordered product in the
underlying graded algebra of presheaves. -/
theorem prodDegOne_eq_homogeneousProd {Y S : Scheme.{u}} (q : Y ⟶ S) (U : Y.Opensᵒᵖ) (n : ℕ)
    (z : Fin n → ((relativeDifferentialFormsAlgebra q).piece 1).val.obj U) :
    (relativeDifferentialFormsAlgebra q).prodDegOne U n z =
      (relativeDifferentialFormsAlgebra q).toPresheafGradedAlgebra.homogeneousProd U n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [SheafOfModules.GradedAlgebra.prodDegOne_succ, ih]
    rfl

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

attribute [local instance 10000] HasDerivedCategory.standard

private theorem isIso_eqToHom' {𝒞 : Type*} [Category* 𝒞] {A B : 𝒞} (h : A = B) :
    IsIso (eqToHom h) :=
  inferInstance

/-- **A vanishing Gysin map vanishes on every chart.** If the Gysin map `γ^p` of
[Stacks, Tag 0G86] is zero, then so is the Gysin map of [Stacks, Tag 0G83] of the equations of
every equation chart: by the chart formula, `γ^p` is that map read on sections through two
isomorphisms. -/
theorem chartGysin_eq_zero_of_conormalGysinHom_eq_zero (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ} (p : ℕ) (hE : ConormalRank i c)
    (h0 : Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π p hE = 0)
    (a : EquationChart i c) :
    chartGysin i π a.ambient a.equations p (isCutOutByEquationsOn_equationChart i a) = 0 := by
  have hloc : chartLocHom i π p a.ambient a.equations (isCutOutByEquationsOn_equationChart i a)
      (equationsClosedSet_equationChart i a) = 0 := by
    refine Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_ext fun U hU m => ?_
    have h1 := Stacks.DeRham.CohomologicalGysin.conormalGysinHom_app i π p hE a U hU m
    rw [h0] at h1
    calc Stacks.AlgebraicGeometry.ModuleLimits.restrictSections _ U hU m
        = chartLoc i π p a.ambient a.equations (isCutOutByEquationsOn_equationChart i a)
            (equationsClosedSet_equationChart i a) U hU m := rfl
      _ = 0 := h1.symm.trans rfl
      _ = _ := by
        rw [Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_apply]
        exact (map_zero _).symm
  have hT : IsIso (chartTargetHom i π p a.ambient (restrictEquations a.ambient a.equations)
      (equationsClosedSet_equationChart i a)) := by
    unfold chartTargetHom
    exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' (Functor.map_isIso _ _)
      (IsIso.comp_isIso' (isIso_eqToHom' _) (Iso.isIso_inv _)))
  unfold chartLocHom at hloc
  rw [← Category.assoc] at hloc
  have h2 := (cancel_mono _).1 (hloc.trans (zero_comp (f := chartTargetHom i π p a.ambient
    (restrictEquations a.ambient a.equations) (equationsClosedSet_equationChart i a))).symm)
  exact (cancel_epi _).1 (h2.trans comp_zero.symm)

/-- A linear map carries a relation `r • x ∈ I • ⊤` to the relation `r • φ x ∈ I • ⊤`. -/
private theorem smul_map_mem_ideal_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (φ : M ≃ₗ[R] N) (I : Ideal R) (r : R) {x : M}
    (hx : r • x ∈ (I • ⊤ : Submodule R M)) : r • φ x ∈ (I • ⊤ : Submodule R N) := by
  have h := Submodule.mem_map_of_mem (f := φ.toLinearMap) hx
  rw [Submodule.map_smul'', LinearMap.map_smul, LinearEquiv.coe_coe] at h
  exact Submodule.smul_mono le_rfl le_top h

/-- Relations `r • x ∈ I • ⊤` pass along an equality of degrees in a family of sheaves of modules,
between sections that agree up to that equality. -/
private theorem smul_mem_of_heq {Y : Scheme.{u}} (M : ℤ → Y.Modules) {a b : ℤ} (hab : a = b)
    {x : Γ(M a, ⊤)} {y : Γ(M b, ⊤)} (hxy : HEq x y) (r : Γ(Y, ⊤)) (I : Ideal Γ(Y, ⊤))
    (hx : r • x ∈ (I • ⊤ : Submodule Γ(Y, ⊤) Γ(M a, ⊤))) :
    r • y ∈ (I • ⊤ : Submodule Γ(Y, ⊤) Γ(M b, ⊤)) := by
  subst hab
  rwa [← eq_of_heq hxy]

open Stacks.Perfect.SupportedFraction in
/-- **The Gysin formula in degree `0` is the fraction class of the equation wedge, up to
isomorphisms.** If the Gysin formula of [Stacks, Tag 0G83] vanishes in degree `0`, then so does the
class of `ω ∧ d g₁ ∧ ⋯ ∧ d g_c / (g₁ ⋯ g_c)` in the cokernel of the last differential of the
extended alternating Čech complex: the two differ by the comparison of [Stacks, Tag 0G7L], which
is an isomorphism, and the identification of the two spellings of the target. -/
theorem gysinWedgeHom_comp_fractionHom_comp_cokernelπ_eq_zero {Y S : Scheme.{u}} (q : Y ⟶ S)
    {e : ℕ} (g : Fin (e + 1) → Γ(Y, ⊤)) (h0 : gysinFormulaHom q g ((0 : ℕ) : ℤ) = 0) :
    gysinWedgeHom q g ((0 : ℕ) : ℤ) ≫
        fractionHom g (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))) e ≫
          cokernel.π (lastDif g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))) = 0 := by
  have h := Stacks.Perfect.supportedFractionSource_comp_supportCohomologyToPushforward g
    (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))
  have h' : supportedFractionSource g
      (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))
      (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet g) subset_rfl =
      fractionHom g (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))) e ≫
        cokernel.π (lastDif g (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))) ≫
          cokernelLastDifToSupport g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))
            (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet g) subset_rfl := by
    rw [supportedFractionSource, ← Category.assoc, cokernelπ_comp_supportedFractionClass,
      Category.assoc]
  have := isIso_cokernelLastDifToSupport g
    (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))
    (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet g) subset_rfl subset_rfl
  have key : gysinFormulaHom q g ((0 : ℕ) : ℤ) =
      gysinWedgeHom q g ((0 : ℕ) : ℤ) ≫
        (supportedFractionSource g
          (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))
          (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet g) subset_rfl ≫
          (Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))).hom) := by
    rw [h]
    rfl
  rw [key, h'] at h0
  simp only [Category.assoc] at h0
  rw [← Category.assoc, ← Category.assoc] at h0
  exact (cancel_mono _).1 (h0.trans zero_comp.symm)

/-- **The Gysin wedge of the unit form is the equation wedge**, up to the identification of
degrees `0 + c = c`. -/
theorem gysinWedgeHom_app_one_heq {Y S : Scheme.{u}} (q : Y ⟶ S) {c : ℕ}
    (g : Fin c → Γ(Y, ⊤)) :
    HEq ((gysinWedgeHom q g ((0 : ℕ) : ℤ)).app ⊤
      ((relativeDifferentialFormsAlgebra q).one.eval (op ⊤)))
      ((relativeDifferentialFormsAlgebra q).prodDegOne (op ⊤) c fun j =>
        exactOneForm q (op ⊤) (Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op (g j))) :=
  (relativeDifferentialFormsAlgebra q).one_mul (c : ℤ) (op ⊤) _

/-- **The equation wedge on an affine chart is the wedge of the Kähler differentials** under the
identification `Γ(Y, Ω^c_{Y/S}) = ⋀^c Ω_{B/A}` of [Stacks, Tag 01UT] and [Stacks, Tag 01I8],
`B = Γ(Y, 𝒪_Y)`, `A = Γ(S, 𝒪_S)`. -/
theorem relativeFormsSectionsEquiv_prodDegOne_exactOneForm {Y S : Scheme.{u}} (q : Y ⟶ S)
    [IsAffine Y] [IsAffine S] (hle : (⊤ : Y.Opens) ≤ q ⁻¹ᵁ ⊤) {c : ℕ} (g : Fin c → Γ(Y, ⊤)) :
    letI := (q.appLE ⊤ ⊤ hle).hom.toAlgebra
    AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv q (isAffineOpen_top Y)
      (isAffineOpen_top S) hle c ((relativeDifferentialFormsAlgebra q).prodDegOne (op ⊤) c fun j =>
        exactOneForm q (op ⊤) (Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op (g j))) =
      exteriorPower.ιMulti Γ(Y, ⊤) c (fun j => KaehlerDifferential.D Γ(S, ⊤) Γ(Y, ⊤) (g j)) := by
  let := (q.appLE ⊤ ⊤ hle).hom.toAlgebra
  have hz : (fun j => exactOneForm q (op ⊤)
        (Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op (g j))) =
      fun j =>
        (Stacks.AlgebraicGeometry.AffineOpenDifferentialForms.relativeDifferentialFormsGenerator
          q).val.app (op ⊤) ((universalRelativeDerivation q).d
          (Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op (g j))) := rfl
  rw [prodDegOne_eq_homogeneousProd, hz,
    AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv_homogeneousProd_d q
      (isAffineOpen_top Y) (isAffineOpen_top S) hle c
      (fun j => Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op (g j))]
  congr 1
  funext j
  rw [structurePresheaf_map_le_refl]

/-- **The equation wedge on an affine chart, read in the exterior power of the Kähler
differentials.** On an affine `Y` over an affine `S`, a relation
`r · (1 ∧ d g₁ ∧ ⋯ ∧ d g_c) ∈ I · Γ(Y, Ω^c_{Y/S})` becomes the relation
`r · (D g₁ ∧ ⋯ ∧ D g_c) ∈ I · ⋀^c Ω_{B/A}`. -/
theorem smul_ιMulti_D_mem_of_smul_gysinWedgeHom_one_mem {Y S : Scheme.{u}} (q : Y ⟶ S)
    [IsAffine Y] [IsAffine S] (hle : (⊤ : Y.Opens) ≤ q ⁻¹ᵁ ⊤) {c : ℕ} (g : Fin c → Γ(Y, ⊤))
    (r : Γ(Y, ⊤)) (I : Ideal Γ(Y, ⊤))
    (h : r • (gysinWedgeHom q g ((0 : ℕ) : ℤ)).app ⊤
        ((relativeDifferentialFormsAlgebra q).one.eval (op ⊤)) ∈
      (I • ⊤ : Submodule Γ(Y, ⊤)
        Γ(relativeDifferentialForms q (((0 : ℕ) : ℤ) + (c : ℤ)), ⊤))) :
    letI := (q.appLE ⊤ ⊤ hle).hom.toAlgebra
    r • exteriorPower.ιMulti Γ(Y, ⊤) c (fun j => KaehlerDifferential.D Γ(S, ⊤) Γ(Y, ⊤) (g j)) ∈
      (I • ⊤ : Submodule Γ(Y, ⊤) (⋀[Γ(Y, ⊤)]^c Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)])) := by
  have hx := smul_mem_of_heq (relativeDifferentialFormsAlgebra q).piece
    (show ((0 : ℕ) : ℤ) + (c : ℤ) = (c : ℤ) by simp) (gysinWedgeHom_app_one_heq q g) r I h
  have hmap := smul_map_mem_ideal_smul_top (AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv
    q (isAffineOpen_top Y) (isAffineOpen_top S) hle c) I r hx
  convert hmap using 2
  exact (relativeFormsSectionsEquiv_prodDegOne_exactOneForm q hle g).symm

/-- **The Gysin formula of a regular system of equations of a rational point is not zero.** Let
`q : Y ⟶ S` be a morphism of affine schemes, `B = Γ(Y, 𝒪_Y)`, `A = Γ(S, 𝒪_S)`, and let
`g₁, …, g_c ∈ B`, `c ≥ 1`, be a Koszul-regular sequence lying in a maximal ideal `𝔪` of the
Noetherian ring `B`, generating `𝔪` after localizing at `𝔪`, with `A → B/𝔪` surjective. If
`Ω_{B/A}` is free of rank `c`, the Gysin formula `ω ↦ [ω ∧ d g₁ ∧ ⋯ ∧ d g_c / (g₁ ⋯ g_c)]` of
[Stacks, Tag 0G83] in degree `0` is not the zero map: its value on `1` is not zero. -/
theorem gysinFormulaHom_ne_zero {Y S : Scheme.{u}} (q : Y ⟶ S) [IsAffine Y] [IsAffine S]
    {e : ℕ} (g : Fin (e + 1) → Γ(Y, ⊤)) [IsNoetherianRing Γ(Y, ⊤)] (m : Ideal Γ(Y, ⊤))
    [m.IsMaximal] (hgm : ∀ j, g j ∈ m)
    (hgen : ∀ x ∈ m, ∃ h ∉ m, h * x ∈ Ideal.span (Set.range g))
    (hreg : Koszul.IsKoszulRegular g) (hle : (⊤ : Y.Opens) ≤ q ⁻¹ᵁ ⊤)
    (hsurj : letI := (q.appLE ⊤ ⊤ hle).hom.toAlgebra
      Function.Surjective (algebraMap Γ(S, ⊤) (Γ(Y, ⊤) ⧸ m)))
    (b : letI := (q.appLE ⊤ ⊤ hle).hom.toAlgebra
      Module.Basis (Fin (e + 1)) Γ(Y, ⊤) Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]) :
    gysinFormulaHom q g ((0 : ℕ) : ℤ) ≠ 0 := by
  intro h0
  have h2 := congrArg (fun φ => (φ.app ⊤) ((relativeDifferentialFormsAlgebra q).one.eval (op ⊤)))
    (gysinWedgeHom_comp_fractionHom_comp_cokernelπ_eq_zero q g h0)
  obtain ⟨n, hn⟩ :=
    Stacks.Perfect.SupportedFraction.exists_prod_pow_smul_mem_of_cokernelπ_fractionHom_eq_zero
      _ g _ h2
  exact @KaehlerDifferential.prod_pow_smul_ιMulti_D_notMem _ _ _ _
    (q.appLE ⊤ ⊤ hle).hom.toAlgebra _ m _ (e + 1) g hreg hgm hgen hsurj b n
    (smul_ιMulti_D_mem_of_smul_gysinWedgeHom_one_mem q hle g _ _ hn)

/-! ### The ideal of a point on an affine chart -/

/-- **On an affine chart, the ideal of a closed subscheme cut out by global equations is generated
by them near each of its points.** Let `j : Z' ⟶ Y` be cut out by global functions `g₁, …, g_c`
of an affine scheme `Y`, and suppose the kernel `𝔪` of `Γ(Y, 𝒪_Y) ⟶ Γ(Z', 𝒪_{Z'})` is prime and
`Z'` is nonempty. Then every `x ∈ 𝔪` has a multiple `h x ∈ (g₁, …, g_c)` with `h ∉ 𝔪`. -/
theorem exists_mul_mem_span_of_mem_ker {Y Z' : Scheme.{u}} [IsAffine Y] (j : Z' ⟶ Y) {c : ℕ}
    (g : Fin c → Γ(Y, ⊤)) (hcut : IsCutOutByEquations j g) (z : Z')
    (hprime : (RingHom.ker j.appTop.hom).IsPrime) (x : Γ(Y, ⊤))
    (hx : x ∈ RingHom.ker j.appTop.hom) :
    ∃ h ∉ RingHom.ker j.appTop.hom, h * x ∈ Ideal.span (Set.range g) := by
  classical
  obtain ⟨V, hVU, hzV, cc, hcc⟩ := hcut.exists_eq_sum ⊤ x hx (j.base z) trivial
  obtain ⟨h, hhV, hzh⟩ := (isAffineOpen_top Y).exists_basicOpen_le ⟨j.base z, hzV⟩ trivial
  have hh : h ∉ RingHom.ker j.appTop.hom := by
    intro h0
    have hz : z ∈ j ⁻¹ᵁ Y.basicOpen h := hzh
    rwa [Scheme.preimage_basicOpen_top, show j.appTop h = 0 from h0, Scheme.basicOpen_zero] at hz
  -- the relation, restricted to `D(h)`
  let res : Γ(Y, ⊤) →+* Γ(Y, Y.basicOpen h) := algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen h)
  have hres : ∀ a : Γ(Y, ⊤), res a = Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op a :=
    fun _ => rfl
  let ccD : Fin c → Γ(Y, Y.basicOpen h) := fun l => Y.presheaf.map (homOfLE hhV).op (cc l)
  have hrel : res x = ∑ l, ccD l * res (g l) := by
    have h1 := congrArg (Y.presheaf.map (homOfLE hhV).op).hom hcc
    rw [map_sum] at h1
    rw [hres, ← Stacks.Perfect.SupportedFraction.ringMap_collapse (homOfLE hVU) (homOfLE hhV), h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, hres, Stacks.Perfect.SupportedFraction.ringMap_collapse]
  -- clear the denominators of the coefficients
  obtain ⟨⟨t, ht⟩, hN⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers h)
    Finset.univ ccD
  choose b hb using fun l => hN l (Finset.mem_univ l)
  have hrel' : res (t * x) = res (∑ l, b l * g l) := by
    rw [map_mul, hrel, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hbl : res (b l) = res t * ccD l := (hb l).trans (Algebra.smul_def t (ccD l))
    rw [map_mul, hbl, mul_assoc]
  obtain ⟨N, rfl⟩ := ht
  obtain ⟨⟨_, M, rfl⟩, hM⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers h) hrel'
  refine ⟨h ^ (M + N), fun hmem => hh (hprime.mem_of_pow_mem _ hmem), ?_⟩
  have : h ^ (M + N) * x = ∑ l, (h ^ M * b l) * g l := by
    rw [pow_add, mul_assoc]
    simp only [mul_assoc, ← Finset.mul_sum]
    exact hM
  rw [this]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)

/-- **A rational point.** Let `q : Y ⟶ S` with `Γ(S, 𝒪_S)` a field, and let `j : Z' ⟶ Y` be such
that `j ≫ q` is an isomorphism and `Z'` is nonempty. Then the kernel `𝔪` of
`Γ(Y, 𝒪_Y) ⟶ Γ(Z', 𝒪_{Z'})` is a maximal ideal and `Γ(S, 𝒪_S) ⟶ Γ(Y, 𝒪_Y)/𝔪` is surjective. -/
theorem isMaximal_ker_appTop_and_surjective {Y Z' S : Scheme.{u}} (q : Y ⟶ S) (j : Z' ⟶ Y)
    [IsIso (j ≫ q)] [Nonempty Z'] (hS : IsField Γ(S, ⊤)) (hle : (⊤ : Y.Opens) ≤ q ⁻¹ᵁ ⊤) :
    (RingHom.ker j.appTop.hom).IsMaximal ∧
      letI := (q.appLE ⊤ ⊤ hle).hom.toAlgebra
      Function.Surjective (algebraMap Γ(S, ⊤) (Γ(Y, ⊤) ⧸ RingHom.ker j.appTop.hom)) := by
  have hcomp : j.appTop.hom.comp (q.appLE ⊤ ⊤ hle).hom = ((j ≫ q).appTop).hom := by
    rw [Scheme.Hom.comp_appTop, show q.appLE ⊤ ⊤ hle = q.appTop from Scheme.Hom.appLE_eq_app q,
      CommRingCat.hom_comp]
  have hbij : Function.Bijective (j.appTop.hom.comp (q.appLE ⊤ ⊤ hle).hom) := by
    rw [hcomp]
    have : IsIso (j ≫ q).appTop := inferInstanceAs (IsIso ((j ≫ q).app ⊤))
    exact ConcreteCategory.bijective_of_isIso ((j ≫ q).appTop)
  have hsurjφ : Function.Surjective j.appTop.hom := fun w => by
    obtain ⟨a, ha⟩ := hbij.2 w
    exact ⟨_, ha⟩
  have hfield : IsField Γ(Z', ⊤) :=
    MulEquiv.isField hS (RingEquiv.ofBijective _ hbij).symm.toMulEquiv
  let := hfield.toField
  refine ⟨RingHom.ker_isMaximal_of_surjective _ hsurjφ, ?_⟩
  let := (q.appLE ⊤ ⊤ hle).hom.toAlgebra
  intro w
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨a, ha⟩ := hbij.2 (j.appTop.hom y)
  refine ⟨a, ?_⟩
  rwa [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]

/-- Two successive restriction maps of the structure sheaf are the restriction along the
composite. -/
private theorem presheaf_map_map_eq {X : Scheme.{u}} {A B C : X.Opensᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
    (h : A ⟶ C) (y : X.presheaf.obj A) :
    X.presheaf.map g (X.presheaf.map f y) = X.presheaf.map h y := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (f ≫ g) h]

/-- **A basis of the Kähler differentials of an affine open, read on the open subscheme.** The
sections of the structure sheaf over an open `W` and the global sections of the open subscheme
`W` are identified by `AlgebraicGeometry.Scheme.Opens.topIso`, compatibly with the structure maps
from `Γ(S, 𝒪_S)`, so a basis of `Ω_{Γ(X, W)/Γ(S, 𝒪_S)}` transports to a basis of
`Ω_{Γ(W, 𝒪_W)/Γ(S, 𝒪_S)}`. -/
theorem nonempty_basis_kaehlerDifferential_toScheme {X S : Scheme.{u}} (π : X ⟶ S)
    (W : X.Opens) (hWV : W ≤ π ⁻¹ᵁ ⊤) (hle : (⊤ : W.toScheme.Opens) ≤ (W.ι ≫ π) ⁻¹ᵁ ⊤) {n : ℕ}
    (bX : letI := Stacks.Smooth.algebraAppLE π hWV
      Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄Γ(S, ⊤)]) :
    letI := ((W.ι ≫ π).appLE ⊤ ⊤ hle).hom.toAlgebra
    Nonempty (Module.Basis (Fin n) Γ(W.toScheme, ⊤) Ω[Γ(W.toScheme, ⊤)⁄Γ(S, ⊤)]) := by
  let iX : Algebra Γ(S, ⊤) Γ(X, W) := Stacks.Smooth.algebraAppLE π hWV
  let iW : Algebra Γ(S, ⊤) Γ(W.toScheme, ⊤) := ((W.ι ≫ π).appLE ⊤ ⊤ hle).hom.toAlgebra
  let eB : Γ(X, W) ≃+* Γ(W.toScheme, ⊤) := W.topIso.symm.commRingCatIsoToRingEquiv
  have hWι : W.ι ''ᵁ ⊤ ≤ π ⁻¹ᵁ ⊤ := W.ι_image_top.le.trans hWV
  have hcompat : ∀ r, eB (algebraMap Γ(S, ⊤) Γ(X, W) r) =
      algebraMap Γ(S, ⊤) Γ(W.toScheme, ⊤) (RingEquiv.refl Γ(S, ⊤) r) := fun r => by
    change X.presheaf.map _ (X.presheaf.map _ ((π.app ⊤) r)) =
      X.presheaf.map _ (X.presheaf.map _ ((π.app ⊤) r))
    exact (presheaf_map_map_eq _ _ (homOfLE hWι).op _).trans
      (presheaf_map_map_eq _ _ (homOfLE hWι).op _).symm
  let e := AlgebraicGeometry.SheafOfModules.kaehlerDifferentialRingEquiv
    (RingEquiv.refl Γ(S, ⊤)) eB hcompat
  let : Module Γ(X, W) Ω[Γ(W.toScheme, ⊤)⁄Γ(S, ⊤)] := Module.compHom _ eB.toRingHom
  exact ⟨(bX.map e).mapCoeffs eB fun _ _ => rfl⟩

/-! ### Conormal rank zero -/

open Stacks.Perfect.SupportedFraction in
/-- **The comparison of [Stacks, Tag 0G7L] is invertible in every degree** when `ℱ` is
quasi-coherent and `T` is the common zero locus of the equations. -/
theorem isIso_cechHomologyToSupport {Y : Scheme.{u}} {m : ℕ} (e : Fin m → Γ(Y, ⊤))
    (G : Y.Modules) [G.IsQuasicoherent] {T : Set Y} (hT : IsClosed T)
    (hTe : Stacks.Perfect.CechDerivedSupport.equationsClosedSet e ⊆ T)
    (hTsub : T ⊆ Stacks.Perfect.CechDerivedSupport.equationsClosedSet e) (p : ℕ) :
    IsIso (cechHomologyToSupport e G hT hTe p) := by
  have := isIso_cechToSupport e G hT hTe hTsub
  rw [cechHomologyToSupport, extendHomologyToSupport]
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' (Iso.isIso_inv _)
    (Functor.map_isIso (DerivedCategory.homologyFunctor Y.Modules (p : ℤ))
      (cechToSupport e G hT hTe)))

/-- **With no equations the Gysin formula of [Stacks, Tag 0G83] in degree `0` is not zero** on a
nonempty scheme: the class map of [Stacks, Tag 0G7Q] of an empty family is an isomorphism and the
wedge with the empty family of differentials is the identity, so the value on `1` is not zero. -/
theorem gysinFormulaHom_empty_ne_zero {Y S : Scheme.{u}} (q : Y ⟶ S) [Nonempty Y]
    (g : Fin 0 → Γ(Y, ⊤)) : gysinFormulaHom q g ((0 : ℕ) : ℤ) ≠ 0 := by
  intro h0
  have hcls := Stacks.Perfect.FractionClass.classMapToSupport_comp_supportCohomologyToPushforward
    g (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)))
  have := isIso_cechHomologyToSupport g
    (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)))
    (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet g) subset_rfl subset_rfl 0
  have hiso : IsIso (formFractionClass q g (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ))) := by
    have h : formFractionClass q g (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) =
        Stacks.Perfect.FractionClass.classMap g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ))) ≫
          Stacks.Perfect.SupportedFraction.cechHomologyToSupport g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)))
            (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet g) subset_rfl 0 ≫
          (Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)))).hom := by
      have h' : Stacks.Perfect.FractionClass.classMap g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ))) ≫
          Stacks.Perfect.SupportedFraction.cechHomologyToSupport g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)))
            (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet g) subset_rfl 0 ≫
          (Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)))).hom =
          Stacks.Perfect.FractionClass.classMapToSupport g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)))
            (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet g) subset_rfl ≫
          (Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward g
            (relativeDifferentialForms q (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)))).hom := by
        rw [Stacks.Perfect.FractionClass.classMapToSupport, Category.assoc]
      rw [h', hcls]
      rfl
    rw [h]
    infer_instance
  rw [gysinFormulaHom] at h0
  have h1 := (cancel_mono _).1 (h0.trans zero_comp.symm)
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨Classical.arbitrary Y, trivial⟩⟩
  let θ := relativeDifferentialFormsZeroIso q
  let ω : (relativeDifferentialForms q ((0 : ℕ) : ℤ)).val.obj (op ⊤) :=
    θ.inv.val.app (op ⊤) (show Γ(Y, ⊤) from 1)
  have hω : ω ≠ 0 := by
    intro hω0
    have hbij := ConcreteCategory.bijective_of_isIso
      ((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).mapIso θ).inv
    exact one_ne_zero (α := Γ(Y, ⊤)) (hbij.1 (hω0.trans (map_zero _).symm))
  have hheq := gysinWedgeHom_empty_apply q g ((0 : ℕ) : ℤ) (op ⊤) ω
  rw [h1] at hheq
  exact hω (eq_of_heq hheq).symm

/-! ### The Gysin map of Tag 0G86 is not zero -/

/-- If the Gysin map `γ^0` vanishes, the Gysin formula of the equations of every equation chart
vanishes in degree `0`. -/
private theorem gysinFormulaHom_eq_zero_of_conormalGysinHom_eq_zero (i : Z ⟶ X)
    [IsClosedImmersion i] [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ}
    (hE : ConormalRank i c) (h0 : Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE = 0)
    (a : EquationChart i c) :
    gysinFormulaHom (a.ambient.ι ≫ π) (restrictEquations a.ambient a.equations) ((0 : ℕ) : ℤ) =
      0 := by
  rw [← chartGysin_formula i π a.ambient a.equations 0 (isCutOutByEquationsOn_equationChart i a),
    chartGysin_eq_zero_of_conormalGysinHom_eq_zero i π 0 hE h0 a, comp_zero]

/-- **At conormal rank `0` the Gysin map of [Stacks, Tag 0G86] is not zero** as soon as the closed
subscheme is nonempty: on an equation chart around a point of `Z` the equations are the empty
family, and there the Gysin map is an isomorphism onto the degree-`0` local cohomology. -/
theorem conormalGysinHom_ne_zero_of_conormalRank_zero (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) (hE : ConormalRank i 0) [Nonempty Z] :
    Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE ≠ 0 := by
  intro h0
  obtain ⟨z⟩ := ‹Nonempty Z›
  obtain ⟨W, hW, hxW, f, -, hgen, -⟩ := exists_affineOpen_equations_of_conormalRank i 0 hE z
  let a : EquationChart i 0 := ⟨W, f, hgen, fun _ _ j => j.elim0⟩
  have hform := gysinFormulaHom_eq_zero_of_conormalGysinHom_eq_zero i π hE h0 a
  have : Nonempty W.toScheme := ⟨⟨i.base z, hxW⟩⟩
  exact gysinFormulaHom_empty_ne_zero (W.ι ≫ π) _ hform

/-- Koszul-regularity of a family of sections over an affine open passes to its restriction to a
smaller affine open. -/
private theorem isKoszulRegular_presheaf_map_of_le {X : Scheme.{u}} {W W₀ : X.Opens}
    (hW : IsAffineOpen W) (hW₀ : IsAffineOpen W₀) (hWW₀ : W ≤ W₀) {n : ℕ} {f₀ : Fin n → Γ(X, W₀)}
    (hreg₀ : Koszul.IsKoszulRegular f₀) :
    Koszul.IsKoszulRegular fun j => X.presheaf.map (homOfLE hWW₀).op (f₀ j) := by
  refine (AlgebraicGeometry.forall_isKoszulRegular_germFamily_iff X hW _).1 fun y hy => ?_
  rw [Stacks.AlgebraicGeometry.RegularIdealSheaf.germFamily_res W₀ W hWW₀ f₀ y hy]
  exact (AlgebraicGeometry.forall_isKoszulRegular_germFamily_iff X hW₀ f₀).2 hreg₀ y (hWW₀ hy)

/-- Sections in the ideal of a closed immersion over an open vanish on the closed subscheme after
restriction to any smaller open. -/
private theorem app_presheaf_map_eq_zero_of_le {Z X : Scheme.{u}} (i : Z ⟶ X) {W W₀ : X.Opens}
    (hWW₀ : W ≤ W₀) {n : ℕ} {f₀ : Fin n → Γ(X, W₀)}
    (hmem₀ : ∀ j, f₀ j ∈
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom i).obj (op W₀))
    (V : X.Opens) (hV : V ≤ W) (j : Fin n) :
    (i.app V).hom (X.presheaf.map (homOfLE hV).op (X.presheaf.map (homOfLE hWW₀).op (f₀ j))) =
      0 := by
  have h1 := Stacks.RingedSpace.restrict_mem _ (homOfLE (hV.trans hWW₀)) (hmem₀ j)
  rw [Stacks.AlgebraicGeometry.RegularIdealSheaf.mem_definingIdealOfHom_iff_app_eq_zero] at h1
  rwa [Stacks.Perfect.SupportedFraction.ringMap_collapse (homOfLE hWW₀) (homOfLE hV)
    (homOfLE (hV.trans hWW₀))]

/-- **At positive conormal rank the Gysin map of a rational point is not zero.** Let
`π : X ⟶ Spec k` be smooth of relative dimension `e + 1` and `i : Z ⟶ X` a closed immersion with
`Z ≅ Spec k` over `k`. Then the Gysin map `γ^0` of [Stacks, Tag 0G86] is not zero. On an affine
chart around the point, small enough that the equations are a Koszul-regular sequence and that
`Ω_{X/k}` is free there, `γ^0` is the Gysin map of [Stacks, Tag 0G83] of those equations, and its
value on `1` is the nonzero class of `d f₁ ∧ ⋯ ∧ d f_c / (f₁ ⋯ f_c)`. -/
theorem conormalGysinHom_ne_zero_of_isIso_succ {k : Type u} [Field k] (π : X ⟶ Spec (.of k))
    (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i] (e : ℕ)
    [SmoothOfRelativeDimension (e + 1) π] [IsIso (i ≫ π)] (hE : ConormalRank i (e + 1)) :
    Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE ≠ 0 := by
  intro h0
  have : Smooth π := SmoothOfRelativeDimension.smooth (e + 1) π
  have : Nonempty Z := ⟨(inv (i ≫ π)).base (Classical.arbitrary _)⟩
  obtain ⟨z⟩ := ‹Nonempty Z›
  have hsub : ∀ z' : Z, z' = z := fun z' =>
    (Scheme.homeoOfIso (asIso (i ≫ π))).injective (Subsingleton.elim _ _)
  obtain ⟨W₀, hW₀, hxW₀, f₀, hmem₀, hgen₀, hreg₀⟩ :=
    Stacks.DeRham.GysinCohomologyDeRhamKoszul.exists_affineOpen_koszulRegular_equations i
      (isKoszulRegularImmersion_of_smooth_of_smooth i π)
      (e + 1) (Nat.succ_ne_zero e) hE (i.base z)
  have hTW : W₀ ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  obtain ⟨W, hW, hxW, hWW₀, ⟨bX⟩⟩ :=
    Stacks.Discriminant.exists_isAffineOpen_basis_kaehlerDifferential (n := e + 1) π (i.base z)
      (isAffineOpen_top (Spec (.of k))) hxW₀ hTW
  -- the chart
  let f : Fin (e + 1) → Γ(X, W) := fun j => X.presheaf.map (homOfLE hWW₀).op (f₀ j)
  let a : EquationChart i (e + 1) :=
    ⟨W, f, Stacks.AlgebraicGeometry.RegularIdealSheaf.isGeneratedByOn_of_le W₀ f₀ hgen₀ W hWW₀,
      app_presheaf_map_eq_zero_of_le i hWW₀ hmem₀⟩
  have hcut : IsCutOutByEquationsOn i W f := isCutOutByEquationsOn_equationChart i a
  have hform := gysinFormulaHom_eq_zero_of_conormalGysinHom_eq_zero i π hE h0 a
  -- the equations of the chart are Koszul-regular
  have hregY : Koszul.IsKoszulRegular (restrictEquations W f) :=
    Stacks.AlgebraicGeometry.isKoszulRegular_map_ringEquiv
      W.topIso.symm.commRingCatIsoToRingEquiv (isKoszulRegular_presheaf_map_of_le hW hW₀ hWW₀ hreg₀)
  -- the ring of the chart
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsAffine W.toScheme := hW
  have : IsNoetherianRing Γ(W.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian (X := W.toScheme) ⟨⊤, isAffineOpen_top _⟩
  have : Nonempty (i ⁻¹ᵁ W).toScheme := ⟨⟨z, hxW⟩⟩
  have : IsIso (i ⁻¹ᵁ W).ι := (isIso_iff_isOpenImmersion_and_surjective _).2
    ⟨inferInstance, ⟨fun z' => ⟨⟨z', by rw [hsub z']; exact hxW⟩, rfl⟩⟩⟩
  have : IsIso ((i ∣_ W) ≫ (W.ι ≫ π)) := by
    rw [← chartComm i π W]
    infer_instance
  have hS : IsField Γ(Spec (.of k), ⊤) :=
    MulEquiv.isField (Field.toIsField k)
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  have hle : (⊤ : W.toScheme.Opens) ≤ (W.ι ≫ π) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  obtain ⟨hmax, hsurj⟩ := isMaximal_ker_appTop_and_surjective (W.ι ≫ π) (i ∣_ W) hS hle
  obtain ⟨b⟩ := nonempty_basis_kaehlerDifferential_toScheme π W (hWW₀.trans hTW) hle bX
  exact gysinFormulaHom_ne_zero (W.ι ≫ π) (restrictEquations W f)
    (RingHom.ker (i ∣_ W).appTop.hom) (fun jj => hcut.morphismRestrict.appTop_eq_zero jj)
    (fun x hx => exists_mul_mem_span_of_mem_ker (i ∣_ W) (restrictEquations W f)
      hcut.morphismRestrict ⟨z, hxW⟩ hmax.isPrime x hx)
    hregY hle hsurj b hform

/-- **The Gysin map of a rational point is not zero.** Let `π : X ⟶ Spec k` be smooth of
relative dimension `d` over a field and `i : Z ⟶ X` a closed immersion with `Z ≅ Spec k` over
`k`, so that the conormal sheaf of `i` is locally free of rank `d`. Then the Gysin map
`γ^0 : i_*Ω^0_{Z/k} ⟶ i_*ℋ^d_Z(Ω^d_{X/k})` of [Stacks, Tag 0G86] is not zero. -/
theorem conormalGysinHom_ne_zero_of_isIso {k : Type u} [Field k] (π : X ⟶ Spec (.of k))
    (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i] (d : ℕ)
    [SmoothOfRelativeDimension d π] [IsIso (i ≫ π)] (hE : ConormalRank i d) :
    Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE ≠ 0 := by
  cases d with
  | zero =>
    have : Nonempty Z := ⟨(inv (i ≫ π)).base (Classical.arbitrary _)⟩
    exact conormalGysinHom_ne_zero_of_conormalRank_zero i π hE
  | succ e => exact conormalGysinHom_ne_zero_of_isIso_succ π i e hE

end Stacks.Gysin

end
