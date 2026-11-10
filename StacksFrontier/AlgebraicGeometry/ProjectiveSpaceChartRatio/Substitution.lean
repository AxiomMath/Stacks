module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSubstitution
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.PolynomialModel
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.HomogeneousRescale
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.UnitRescale

/-!
# A linear substitution moves the morphism of [Stacks, Tag 01ND] by the automorphism it induces

Let `L` be an invertible `𝒪_X`-module on a scheme `X` over `Spec k`, let `s₀, …, sₙ` and
`s'₀, …, s'ₙ` be two generating families of global sections of `L`, and let `φ` be a graded ring
automorphism of `k[T₀, …, Tₙ]` fixing the constants — a linear substitution in the homogeneous
coordinates, for instance `AlgebraicGeometry.basisChangeGradedHom`. This module proves

`φ_{(ℒ, s')} = φ_{(ℒ, s)} ≫ Proj.map φ`

read in the polynomial model `Proj k[T₀, …, Tₙ]`, under the hypothesis that the two chart
families are related by the substitution up to a unit on each overlap `X_{sᵢ} ⊓ X_{s'ⱼ}` of the
refined cover.

That hypothesis is exactly the local statement that `s'` is obtained from `s` by the substitution
`φ`, with the ambiguity by a unit that comparing the two *different* trivializations `sᵢ` and
`s'ⱼ` forces. It mentions no `Proj` and no morphism of schemes, and it is **discharged below**,
so the identity is also available unconditionally.

## Main results

* `Stacks.ProjectiveSpaceChartRatio.homOfLE_ι_toPolynomialModel`: the morphism of
  [Stacks, Tag 01ND], restricted to an open inside the `i`-th chart, is
  `AlgebraicGeometry.Proj.fromOfGlobalSections` of the restricted ratio family.
* `Stacks.ProjectiveSpaceChartRatio.fromOfGlobalSections_eval₂Hom_unit_mul`: rescaling the family
  by a unit does not change the morphism. This is
  `AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit` fed by
  `MvPolynomial.IsHomogeneous.eval₂Hom_const_mul`.
* `Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map`: **the identity**, under the
  hypothesis `hagree`.
* `Stacks.ProjectiveSpaceChartRatio.baseRingHom_ι`: the base ring structure of an open subscheme
  is the restriction of the base ring structure of `X`.
* `Stacks.ProjectiveSpaceChartRatio.ratioUnit`: the ratio of two nonvanishing global sections, as
  a unit on an open inside both nonvanishing opens.
* `Stacks.ProjectiveSpaceChartRatio.resO_ratio_eq_div_mul_sum`: **the local comparison of the two
  ratio families**, and `…exists_unit_resOfLE_chartRatio_eq`: **`hagree`, discharged.**
* `Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map_of_sum` and
  `…toPolynomialModel_comp_map_basisChangeGradedHom`: **the identity with no hypothesis**, for
  two families related by a linear substitution and by a change of basis respectively.
* `Stacks.ProjectiveSpaceChartRatio.isImmersion_toPolynomialModel_iff`: being an immersion is the
  same for the glued morphism and for its reading in the polynomial model.

## How `hagree` is discharged

For `s = ψ ∘ b`, `s' = ψ ∘ b'` and `φ = AlgebraicGeometry.basisChangeGradedHom b b'`: on the
overlap `W = X_{sᵢ} ⊓ X_{s'ⱼ}` both `sᵢ` and `s'ⱼ` trivialize `ℒ`, so
`Stacks.NonvanishingTrivialize.bijective_smul` — at this spelling,
`Stacks.ProjectiveFromSections.eq_of_smul_eq_smul` and `div` — produces a unique
`c ∈ Γ(W, 𝒪)` with `c • s'ⱼ = sᵢ`, invertible because the same applies with the roles exchanged
(`ratioUnit`); and `hagree` then follows from injectivity of `· • s'ⱼ` together with
`AlgebraicGeometry.basisChangeGradedHom_X` and the `k`-linearity of `ψ`.

The one input that is not about ratios is the compatibility of the `Γ(X, ⊤)`-action on
`Γ(ℒ, W)` with `baseRingHom` under restriction, and that is `baseRingHom_ι`, which is
`baseRingHom_comp` for `W.ι` together with `ι_appTop_apply`: restricting a global function of `X`
to `W` and reading it as a global function of the open subscheme `W` is `W.ι` on global sections,
both being the image under the structure sheaf of the unique inclusion `W.ι ''ᵁ ⊤ ≤ ⊤`.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveFromSections Stacks.SectionsToProjectiveSpace

namespace Stacks.ProjectiveSpaceChartRatio

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [CommRing k] {n : ℕ}

/-! ### Restriction of the base ring structure and of an evaluation homomorphism -/

/-- The `k`-algebra structure of global sections is natural in the scheme over `Spec k`. -/
theorem baseRingHom_comp {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (h : Y ⟶ Spec (CommRingCat.of k)) :
    g.appTop.hom.comp (baseRingHom h) = baseRingHom (g ≫ h) := by
  rw [baseRingHom, baseRingHom, Scheme.Hom.comp_appTop]
  rfl

/-- Restricting an evaluation homomorphism along a scheme morphism is evaluating at the restricted
family, over the restricted base ring structure. -/
theorem appTop_comp_eval₂Hom {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (κ : k →+* Γ(Y, ⊤))
    (r : Fin (n + 1) → Γ(Y, ⊤)) :
    g.appTop.hom.comp (MvPolynomial.eval₂Hom κ r) =
      MvPolynomial.eval₂Hom (g.appTop.hom.comp κ) (fun m => g.appTop.hom (r m)) :=
  MvPolynomial.ringHom_ext
    (fun a => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply])
    (fun m => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X'])

/-! ### The morphism on a smaller open -/

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s) (f : X ⟶ Spec (CommRingCat.of k))

/-- The restricted ratio family spans the unit ideal: one of its members is `1`. -/
theorem span_range_resOfLE_chartRatio {i : Fin (n + 1)} {W : X.Opens} (hW : W ≤ nvCover s i) :
    Ideal.span (Set.range fun m => resOfLE hW (chartRatio s i m)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  refine Ideal.subset_span ⟨i, ?_⟩
  change resOfLE hW (chartRatio s i i) = 1
  rw [chartRatio_self]
  exact map_one _

/-- **The morphism of [Stacks, Tag 01ND] restricted to an open inside the `i`-th chart** is
`AlgebraicGeometry.Proj.fromOfGlobalSections` of the restricted ratio family. -/
theorem homOfLE_ι_toPolynomialModel {i : Fin (n + 1)} {W : X.Opens} (hW : W ≤ nvCover s i) :
    W.ι ≫ toPolynomialModel s hs f =
      AlgebraicGeometry.Proj.fromOfGlobalSections (polyGrading k n)
        (MvPolynomial.eval₂Hom (baseRingHom (W.ι ≫ f))
          (fun m => resOfLE hW (chartRatio s i m)))
        (map_irrelevant_eval₂Hom_eq_top _ _ (span_range_resOfLE_chartRatio s hW)) := by
  have hfac : W.ι ≫ toPolynomialModel s hs f =
      X.homOfLE hW ≫ (nvCover s i).ι ≫ toPolynomialModel s hs f := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  rw [hfac, ι_toPolynomialModel s hs f i,
    AlgebraicGeometry.Proj.comp_fromOfGlobalSections (polyGrading k n) (X.homOfLE hW)
      (MvPolynomial.eval₂Hom (baseRingHom ((nvCover s i).ι ≫ f)) (chartRatio s i))
      (map_irrelevant_eval₂Hom_eq_top _ _ (span_range_chartRatio s i))
      (AlgebraicGeometry.Proj.map_irrelevant_comp_appTop_eq_top _ _ _
        (map_irrelevant_eval₂Hom_eq_top _ _ (span_range_chartRatio s i)))]
  refine AlgebraicGeometry.Proj.fromOfGlobalSections_congr ?_ _ _
  rw [appTop_comp_eval₂Hom, baseRingHom_comp, ← Category.assoc, Scheme.homOfLE_ι]

/-! ### Rescaling the family by a unit -/

variable {Y : Scheme.{u}}

/-- **Rescaling the family by a unit does not change the morphism to `Proj k[T₀, …, Tₙ]`.** A
homogeneous polynomial of degree `d` picks up `uᵈ` in numerator and denominator alike, which is
the hypothesis `AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit` consumes. -/
theorem fromOfGlobalSections_eval₂Hom_unit_mul (κ : k →+* Γ(Y, ⊤))
    (r r' : Fin (n + 1) → Γ(Y, ⊤)) (u : Γ(Y, ⊤)ˣ) (hrr' : ∀ m, r' m = (u : Γ(Y, ⊤)) * r m)
    (hr : Ideal.span (Set.range r) = ⊤) (hr' : Ideal.span (Set.range r') = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections (polyGrading k n)
        (MvPolynomial.eval₂Hom κ r') (map_irrelevant_eval₂Hom_eq_top κ r' hr') =
      AlgebraicGeometry.Proj.fromOfGlobalSections (polyGrading k n)
        (MvPolynomial.eval₂Hom κ r) (map_irrelevant_eval₂Hom_eq_top κ r hr) := by
  refine (AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit (polyGrading k n)
    (MvPolynomial.eval₂Hom κ r) (MvPolynomial.eval₂Hom κ r') u (fun d a ha => ?_) _ _).symm
  rw [show r' = fun m => (u : Γ(Y, ⊤)) * r m from funext hrr']
  exact ((MvPolynomial.mem_homogeneousSubmodule d a).1 ha).eval₂Hom_const_mul κ r _

/-! ### The identity -/

/-- Substituting in the variables before evaluating is evaluating at the substituted family, for
any graded homomorphism fixing the constants. -/
theorem eval₂Hom_comp_gradedHom (φ : polyGrading k n →+*ᵍ polyGrading k n)
    (hφC : ∀ a : k, φ (MvPolynomial.C a) = MvPolynomial.C a) (κ : k →+* Γ(Y, ⊤))
    (r : Fin (n + 1) → Γ(Y, ⊤)) :
    (MvPolynomial.eval₂Hom κ r).comp φ.toRingHom =
      MvPolynomial.eval₂Hom κ
        (fun m => MvPolynomial.eval₂Hom κ r (φ (MvPolynomial.X m))) :=
  MvPolynomial.ringHom_ext
    (fun a => by rw [RingHom.comp_apply, GradedRingHom.coe_toRingHom, hφC a,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C])
    (fun m => by rw [RingHom.comp_apply, GradedRingHom.coe_toRingHom, MvPolynomial.eval₂Hom_X'])

/-- The nonvanishing opens of two generating families refine to an open cover of `X`. -/
theorem isOpenCover_inf_nvCover {s' : Fin (n + 1) → Γ(L, ⊤)} (hs : GeneratesStalks s)
    (hs' : GeneratesStalks s') :
    IsOpenCover fun p : Fin (n + 1) × Fin (n + 1) =>
      (nvCover s p.1 ⊓ nvCover s' p.2 : X.Opens) := by
  rw [IsOpenCover, ← iSup_inf_iSup,
    (isOpenCover_nvCover_of_generatesStalks s hs).iSup_eq_top,
    (isOpenCover_nvCover_of_generatesStalks s' hs').iSup_eq_top, top_inf_eq]

/-- **A linear substitution in the homogeneous coordinates moves the morphism of
[Stacks, Tag 01ND] by the automorphism of projective space it induces.**

The hypothesis `hagree` is the local comparison of the two families: on the overlap of the `i`-th
chart of `s` with the `j`-th chart of `s'`, the family `s'` read in the trivialization `s'ⱼ` is,
up to a unit, the family `s` read in the trivialization `sᵢ` and substituted by `φ`. The unit is
unavoidable — it is the ratio `sᵢ / s'ⱼ` of the two trivializations — and it is harmless, by
`Stacks.ProjectiveSpaceChartRatio.fromOfGlobalSections_eval₂Hom_unit_mul`.

`Stacks.ProjectiveSpaceChartRatio.exists_unit_resOfLE_chartRatio_eq` discharges `hagree` for two
families related by a linear substitution, and
`Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map_of_sum` is this identity with the
hypothesis gone. -/
theorem toPolynomialModel_comp_map (φ : polyGrading k n →+*ᵍ polyGrading k n)
    (hφ : HomogeneousIdeal.irrelevant (polyGrading k n) ≤
      (HomogeneousIdeal.irrelevant (polyGrading k n)).map φ)
    (hφC : ∀ a : k, φ (MvPolynomial.C a) = MvPolynomial.C a)
    {s' : Fin (n + 1) → Γ(L, ⊤)} (hs' : GeneratesStalks s')
    (hagree : ∀ i j : Fin (n + 1),
      ∃ u : Γ((nvCover s i ⊓ nvCover s' j : X.Opens).toScheme, ⊤)ˣ, ∀ m,
        resOfLE (inf_le_right : nvCover s i ⊓ nvCover s' j ≤ nvCover s' j) (chartRatio s' j m) =
          (u : Γ((nvCover s i ⊓ nvCover s' j : X.Opens).toScheme, ⊤)) *
            MvPolynomial.eval₂Hom
              (baseRingHom ((nvCover s i ⊓ nvCover s' j : X.Opens).ι ≫ f))
              (fun l => resOfLE (inf_le_left : nvCover s i ⊓ nvCover s' j ≤ nvCover s i)
                (chartRatio s i l))
              (φ (MvPolynomial.X m))) :
    toPolynomialModel s' hs' f =
      toPolynomialModel s hs f ≫ AlgebraicGeometry.Proj.map φ hφ := by
  refine (X.openCoverOfIsOpenCover _ (isOpenCover_inf_nvCover s hs hs')).hom_ext _ _ fun p => ?_
  obtain ⟨i, j⟩ := p
  obtain ⟨u, hu⟩ := hagree i j
  have hone : resOfLE (inf_le_right : nvCover s i ⊓ nvCover s' j ≤ nvCover s' j)
      (chartRatio s' j j) = 1 := by
    rw [chartRatio_self]; exact map_one _
  have hunit : IsUnit (MvPolynomial.eval₂Hom
      (baseRingHom ((nvCover s i ⊓ nvCover s' j : X.Opens).ι ≫ f))
      (fun l => resOfLE (inf_le_left : nvCover s i ⊓ nvCover s' j ≤ nvCover s i)
        (chartRatio s i l)) (φ (MvPolynomial.X j))) :=
    IsUnit.of_mul_eq_one (u : Γ((nvCover s i ⊓ nvCover s' j : X.Opens).toScheme, ⊤))
      (by rw [mul_comm, ← hu j, hone])
  have hsub : Ideal.span (Set.range fun m => MvPolynomial.eval₂Hom
      (baseRingHom ((nvCover s i ⊓ nvCover s' j : X.Opens).ι ≫ f))
      (fun l => resOfLE (inf_le_left : nvCover s i ⊓ nvCover s' j ≤ nvCover s i)
        (chartRatio s i l)) (φ (MvPolynomial.X m))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) hunit
  change (nvCover s i ⊓ nvCover s' j : X.Opens).ι ≫ toPolynomialModel s' hs' f =
    (nvCover s i ⊓ nvCover s' j : X.Opens).ι ≫
      toPolynomialModel s hs f ≫ AlgebraicGeometry.Proj.map φ hφ
  rw [homOfLE_ι_toPolynomialModel s' hs' f (inf_le_right : _ ≤ nvCover s' j), ← Category.assoc,
    homOfLE_ι_toPolynomialModel s hs f (inf_le_left : _ ≤ nvCover s i),
    AlgebraicGeometry.Proj.fromOfGlobalSections_comp_map φ hφ _ _
      (by rw [eval₂Hom_comp_gradedHom φ hφC]
          exact map_irrelevant_eval₂Hom_eq_top _ _ hsub),
    AlgebraicGeometry.Proj.fromOfGlobalSections_congr (eval₂Hom_comp_gradedHom φ hφC _ _) _
      (map_irrelevant_eval₂Hom_eq_top _ _ hsub)]
  exact fromOfGlobalSections_eval₂Hom_unit_mul _ _ _ u hu hsub
    (span_range_resOfLE_chartRatio s' (inf_le_right : _ ≤ nvCover s' j))

/-! ### Discharging the local comparison -/

/-- **Restricting a global function of `X` to an open and reading it as a global function of the
open subscheme is `AlgebraicGeometry.Scheme.Opens.ι` on global sections.** Both are the image
under the structure sheaf of the unique inclusion `W.ι ''ᵁ ⊤ ≤ ⊤`. -/
theorem ι_appTop_apply (W : Y.Opens) (a : Γ(Y, ⊤)) :
    W.ι.appTop a = W.topIso.inv (resO (le_top : W ≤ ⊤) a) := by
  have h : (homOfLE (x := W.ι ''ᵁ ⊤) le_top).op =
      (homOfLE (le_top : W ≤ ⊤)).op ≫ (eqToHom W.ι_image_top).op :=
    Subsingleton.elim _ _
  have h2 := congrArg (fun g => Y.presheaf.map g a) h
  simp only [CategoryTheory.Functor.map_comp,
    CategoryTheory.ConcreteCategory.comp_apply] at h2
  exact h2

/-- **The base ring structure of an open subscheme is the restriction of the base ring structure
of `X`.** -/
theorem baseRingHom_ι (W : Y.Opens) (g : Y ⟶ Spec (CommRingCat.of k)) (c : k) :
    baseRingHom (W.ι ≫ g) c = W.topIso.inv (resO (le_top : W ≤ ⊤) (baseRingHom g c)) := by
  rw [← baseRingHom_comp W.ι g, RingHom.comp_apply]
  exact ι_appTop_apply W (baseRingHom g c)

/-- A unit of `Γ(X, W)` read as a unit of the global functions of the open subscheme `W`. -/
def topIsoUnit {W : X.Opens} (v : Γ(X, W)ˣ) : Γ(W.toScheme, ⊤)ˣ where
  val := W.topIso.inv (v : Γ(X, W))
  inv := W.topIso.inv (↑v⁻¹ : Γ(X, W))
  val_inv := by rw [← map_mul, v.mul_inv]; exact map_one _
  inv_val := by rw [← map_mul, v.inv_mul]; exact map_one _

/-- The value of `topIsoUnit v` is the image of the value of `v` under `W.topIso.inv`. -/
@[simp] theorem topIsoUnit_val {W : X.Opens} (v : Γ(X, W)ˣ) :
    (topIsoUnit v : Γ(W.toScheme, ⊤)) = W.topIso.inv (v : Γ(X, W)) := rfl

/-- **The ratio `t/t'` of two nonvanishing global sections is a unit** on any open inside both
nonvanishing opens, its inverse being the ratio taken the other way round. -/
def ratioUnit (t t' : Γ(L, ⊤)) {W : X.Opens} (ht : W ≤ nvOpen L t) (ht' : W ≤ nvOpen L t') :
    Γ(X, W)ˣ where
  val := div t' ht' (resT W t)
  inv := div t ht (resT W t')
  val_inv := eq_of_smul_eq_smul t ht (by rw [mul_smul, div_smul, div_smul, one_smul])
  inv_val := eq_of_smul_eq_smul t' ht' (by rw [mul_smul, div_smul, div_smul, one_smul])

/-- The value of `ratioUnit t t' ht ht'` is the ratio `t/t'` on `W`. -/
@[simp] theorem ratioUnit_val (t t' : Γ(L, ⊤)) {W : X.Opens} (ht : W ≤ nvOpen L t)
    (ht' : W ≤ nvOpen L t') :
    (ratioUnit t t' ht ht' : Γ(X, W)) = div t' ht' (resT W t) := rfl

omit [Ample.IsInvertibleModule X L] in
/-- Restriction of a global section of an `𝒪_X`-module is additive. -/
theorem resT_sum (W : X.Opens) (g : Fin (n + 1) → Γ(L, ⊤)) :
    resT W (∑ l, g l) = ∑ l, resT W (g l) :=
  map_sum (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom g Finset.univ

/-- **The combination of the ratios is the ratio of the combination.** On an open inside the
`i`-th chart of `s`, the section `∑ₗ aₗ sₗ` — the coefficients `aₗ` of the base ring acting
through the structure morphism — is `(∑ₗ aₗ (sₗ/sᵢ)) · sᵢ`. -/
theorem sum_mul_resO_ratio_smul {i : Fin (n + 1)} {W : X.Opens} (hW : W ≤ nvCover s i)
    (a : Fin (n + 1) → k) :
    (∑ l, resO (le_top : W ≤ ⊤) (baseRingHom f (a l)) * resO hW (ratio s i l)) • resT W (s i) =
      resT W (∑ l, baseRingHom f (a l) • s l) := by
  rw [Finset.sum_smul, resT_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_smul, resO_ratio_smul s hW l]
  exact (resM_smul (le_top : W ≤ ⊤) (baseRingHom f (a l)) (s l)).symm

/-- **The local comparison of the two ratio families, in the sections-of-`𝒪_X` spelling.** Let
`s'ₘ = ∑ₗ aₘₗ sₗ`. On an open on which both `sᵢ` and `s'ⱼ` trivialize `ℒ`, the ratio `s'ₘ/s'ⱼ` is
the ratio `sᵢ/s'ⱼ` — one unit independent of `m` — times the substituted ratios
`∑ₗ aₘₗ (sₗ/sᵢ)`.

Both `sᵢ` and `s'ⱼ` trivialize `ℒ` there, so multiplication by either is injective
(`Stacks.ProjectiveFromSections.eq_of_smul_eq_smul`, which is
`Stacks.NonvanishingTrivialize.bijective_smul` at this spelling); the identity is checked by
multiplying both sides by `s'ⱼ`. No `Proj` and no morphism of schemes occurs. -/
theorem resO_ratio_eq_div_mul_sum {s' : Fin (n + 1) → Γ(L, ⊤)} {i j : Fin (n + 1)} {W : X.Opens}
    (hi : W ≤ nvCover s i) (hj : W ≤ nvCover s' j) (a : Fin (n + 1) → Fin (n + 1) → k)
    (hss' : ∀ m, s' m = ∑ l, baseRingHom f (a m l) • s l) (m : Fin (n + 1)) :
    resO hj (ratio s' j m) =
      div (s' j) hj (resT W (s i)) *
        ∑ l, resO (le_top : W ≤ ⊤) (baseRingHom f (a m l)) * resO hi (ratio s i l) := by
  have hE : (∑ l, resO (le_top : W ≤ ⊤) (baseRingHom f (a m l)) * resO hi (ratio s i l)) •
      resT W (s i) = resT W (s' m) := by
    rw [sum_mul_resO_ratio_smul s f hi (a m), hss' m]
  refine eq_of_smul_eq_smul (s' j) hj ?_
  rw [resO_ratio_smul s' hj m, mul_comm (div (s' j) hj (resT W (s i))), mul_smul, div_smul, hE]

/-- Evaluating a linear form in the homogeneous coordinates at a family of sections. -/
theorem eval₂Hom_sum_smul_X (κ : k →+* Γ(Y, ⊤)) (r : Fin (n + 1) → Γ(Y, ⊤))
    (a : Fin (n + 1) → k) :
    MvPolynomial.eval₂Hom κ r (∑ l, a l • MvPolynomial.X (R := k) l) = ∑ l, κ (a l) * r l := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun l _ => by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

/-- A restricted chart ratio is the ratio read in the global functions of the open subscheme. -/
private theorem resOfLE_chartRatio_eq_topIso_inv {i : Fin (n + 1)} {W : X.Opens}
    (hW : W ≤ nvCover s i) (m : Fin (n + 1)) :
    resOfLE hW (chartRatio s i m) = W.topIso.inv (resO hW (ratio s i m)) := by
  simp only [resOfLE, chartRatio, Stacks.ProjectiveFromSections.homOfLE_appTop_topIso_inv]

/-- **The hypothesis `hagree` of
`Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map`, discharged** for two families
related by the linear substitution `φ`. -/
theorem exists_unit_resOfLE_chartRatio_eq (φ : polyGrading k n →+*ᵍ polyGrading k n)
    (a : Fin (n + 1) → Fin (n + 1) → k)
    (hφX : ∀ m, φ (MvPolynomial.X m) = ∑ l, a m l • MvPolynomial.X (R := k) l)
    {s' : Fin (n + 1) → Γ(L, ⊤)}
    (hss' : ∀ m, s' m = ∑ l, baseRingHom f (a m l) • s l) (i j : Fin (n + 1)) :
    ∃ u : Γ((nvCover s i ⊓ nvCover s' j : X.Opens).toScheme, ⊤)ˣ, ∀ m,
      resOfLE (inf_le_right : nvCover s i ⊓ nvCover s' j ≤ nvCover s' j) (chartRatio s' j m) =
        (u : Γ((nvCover s i ⊓ nvCover s' j : X.Opens).toScheme, ⊤)) *
          MvPolynomial.eval₂Hom
            (baseRingHom ((nvCover s i ⊓ nvCover s' j : X.Opens).ι ≫ f))
            (fun l => resOfLE (inf_le_left : nvCover s i ⊓ nvCover s' j ≤ nvCover s i)
              (chartRatio s i l))
            (φ (MvPolynomial.X m)) := by
  refine ⟨topIsoUnit (ratioUnit (s i) (s' j) inf_le_left inf_le_right), fun m => ?_⟩
  have hR : ∀ l, baseRingHom ((nvCover s i ⊓ nvCover s' j : X.Opens).ι ≫ f) (a m l) *
        resOfLE (inf_le_left : nvCover s i ⊓ nvCover s' j ≤ nvCover s i) (chartRatio s i l) =
      (nvCover s i ⊓ nvCover s' j : X.Opens).topIso.inv
        (resO (le_top : (nvCover s i ⊓ nvCover s' j : X.Opens) ≤ ⊤) (baseRingHom f (a m l)) *
          resO (inf_le_left : nvCover s i ⊓ nvCover s' j ≤ nvCover s i) (ratio s i l)) := by
    intro l
    rw [map_mul, baseRingHom_ι, resOfLE_chartRatio_eq_topIso_inv]
  rw [hφX m, eval₂Hom_sum_smul_X, resOfLE_chartRatio_eq_topIso_inv, topIsoUnit_val, ratioUnit_val,
    Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hR l), ← map_sum, ← map_mul,
    resO_ratio_eq_div_mul_sum s f inf_le_left inf_le_right a hss' m]

/-! ### The identity without the hypothesis -/

/-- **A linear substitution in the homogeneous coordinates moves the morphism of
[Stacks, Tag 01ND] by the automorphism of projective space it induces**, with no hypothesis on
the overlaps of the refined cover: `Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map`
with `hagree` discharged by
`Stacks.ProjectiveSpaceChartRatio.exists_unit_resOfLE_chartRatio_eq`.

The two families are related by the matrix `a` of the substitution, the coefficients acting on
the sections of `ℒ` through the structure morphism of `X` over `Spec k`. -/
theorem toPolynomialModel_comp_map_of_sum (φ : polyGrading k n →+*ᵍ polyGrading k n)
    (hφ : HomogeneousIdeal.irrelevant (polyGrading k n) ≤
      (HomogeneousIdeal.irrelevant (polyGrading k n)).map φ)
    (hφC : ∀ c : k, φ (MvPolynomial.C c) = MvPolynomial.C c)
    (a : Fin (n + 1) → Fin (n + 1) → k)
    (hφX : ∀ m, φ (MvPolynomial.X m) = ∑ l, a m l • MvPolynomial.X (R := k) l)
    {s' : Fin (n + 1) → Γ(L, ⊤)} (hs' : GeneratesStalks s')
    (hss' : ∀ m, s' m = ∑ l, baseRingHom f (a m l) • s l) :
    toPolynomialModel s' hs' f =
      toPolynomialModel s hs f ≫ AlgebraicGeometry.Proj.map φ hφ :=
  toPolynomialModel_comp_map s hs f φ hφ hφC hs'
    (exists_unit_resOfLE_chartRatio_eq s f φ a hφX hss')

/-- **The identity for the substitution of a change of basis.** If `s` and `s'` are the images
under a linear system of two bases `b` and `b'` of `V`, the morphisms of [Stacks, Tag 01ND] they
determine differ by `AlgebraicGeometry.Proj.map` of
`AlgebraicGeometry.basisChangeGradedHom b b'`, which is an automorphism of
`Proj k[T₀, …, Tₙ]`. -/
theorem toPolynomialModel_comp_map_basisChangeGradedHom {V : Type u} [AddCommGroup V]
    [Module k V] (b b' : Module.Basis (Fin (n + 1)) k V)
    {s' : Fin (n + 1) → Γ(L, ⊤)} (hs' : GeneratesStalks s')
    (hss' : ∀ m, s' m = ∑ l, baseRingHom f (b.repr (b' m) l) • s l) :
    toPolynomialModel s' hs' f =
      toPolynomialModel s hs f ≫
        AlgebraicGeometry.Proj.map (AlgebraicGeometry.basisChangeGradedHom b b')
          (AlgebraicGeometry.irrelevant_le_map_basisChangeGradedHom b b') :=
  toPolynomialModel_comp_map_of_sum s hs f _
    (AlgebraicGeometry.irrelevant_le_map_basisChangeGradedHom b b')
    (AlgebraicGeometry.basisChangeGradedHom_C b b') (fun m l => b.repr (b' m) l)
    (AlgebraicGeometry.basisChangeGradedHom_X b b') hs' hss'

/-- **Being an immersion is the same for the glued morphism of [Stacks, Tag 01ND] and for its
reading in the polynomial model**: the two differ by the comparison isomorphism of the two models
of `ℙⁿ_k`. -/
theorem isImmersion_toPolynomialModel_iff :
    IsImmersion (toPolynomialModel s hs f) ↔ IsImmersion (toProjectiveSpaceOver s hs f) := by
  rw [toPolynomialModel]
  exact IsImmersion.comp_iff _ _

end Stacks.ProjectiveSpaceChartRatio

end
