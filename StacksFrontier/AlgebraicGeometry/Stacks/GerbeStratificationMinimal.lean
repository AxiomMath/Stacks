module

public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeAutomorphismFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOverSchemeWithGroup
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationStrata
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedSourceLocallyClosedFactorization
public import StacksFrontier.RingTheory.WeightedStabilizerNotFlat
public import StacksFrontier.Topology.Stratification.Partition

/-!
# Minimality of the stratification of the weighted quotient stack

Let `k` be a field (a domain suffices), `p` a prime (`1 < p` suffices), `U = Spec k[x_0, x_1, …]`
with `𝐆_m` acting with weights `p^i`, and `𝒳 = [U/𝐆_m]`, stratified by the strata `𝒳_a`,
`a ∈ ℕ ∪ {∞}`. The last sentence of **Stacks 06RE** says that there is no coarser stratification
of `𝒳` by reduced locally closed substacks which are gerbes over schemes. This file proves it.

## Main results

* `AlgebraicGeometry.PPowerWeighted.not_stratumPoints_union_subset`: the points of a locally
  closed substack of `𝒳` which is a gerbe never contain two strata `|𝒳_a|`, `|𝒳_b|`, `a < b`.
* `AlgebraicGeometry.PPowerWeighted.eq_range_stratumPoints_of_refines`: **Stacks 06RE,
  minimality**: a partition of `|𝒳|` into locally closed sets, each the set of points of a
  reduced locally closed substack which is a gerbe over a scheme, which is refined by the strata,
  is the stratification by the strata.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbeOverScheme.isGerbe`: a gerbe over a scheme is a
  gerbe in the sense of Stacks 06QC.

## Proof

Let `a < b`, and suppose the points of a locally closed gerbe `Q ⊆ 𝒳` contain `|𝒳_a| ∪ |𝒳_b|`.
Over the line `T = Spec k[s]` take the point of `U` with `x_a = s`, `x_b = 1` and all other
coordinates `0` (for `b = ∞`: `x_a = s`, all others `0`;
`AlgebraicGeometry.PPowerWeighted.testCoords`). Where `s` is invertible it lies in `X_a`, where
`s = 0` in `X_b`, so every point of `T` lands in `|Q|`; as `T` is reduced, its chart object `ξ`
lies in `Q` (`AlgebraicGeometry.Stack.prop_of_forall_pointsMap_mem`, Stacks 050B). The
automorphism sheaf of `ξ` on `(Sch/T)` is, through the chart
(`AlgebraicGeometry.PPowerWeighted.chartIsomEquiv`), the sheaf of units `γ` with `γ^{p^b} = 1`
and `s γ^{p^a} = s` (resp. `s γ^{p^a} = s`), represented by the spectrum of the stabilizer
algebra `k[s][t, t⁻¹] / (t^{p^b} - 1, s (t^{p^a} - 1))` (resp. `k[s][t, t⁻¹] / (s (t^{p^a} - 1))`).
Automorphism sheaves of gerbes are flat (Stacks 06QJ, in the form of
`flat_and_locallyOfFinitePresentation_of_isGerbe_fullSubcategoryAlgebraicStack`), but these
algebras are not flat over `k[s]`
(`AlgebraicGeometry.PPowerWeighted.not_flat_stabilizerAlgebra_pow`), a contradiction
(`AlgebraicGeometry.PPowerWeighted.not_prop_chartObj_linePoint`).

Minimality follows: a member of the coarser partition is a union of strata, the strata covering
`|𝒳|` and refining it; it contains no two of them, so it is a single stratum
(`AlgebraicGeometry.PPowerWeighted.eq_range_of_refines_of_forall_subset`).

## References

* [Stacks Project, Tag 06RE](https://stacks.math.columbia.edu/tag/06RE)
* [Stacks Project, Tag 050B](https://stacks.math.columbia.edu/tag/050B)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A gerbe over a scheme is a gerbe.** The scheme stack `(Sch/T)_fppf` is representable by
the algebraic space `T`, so a gerbe over it is a gerbe in the absolute sense of Stacks 06QC. -/
theorem IsGerbeOverScheme.isGerbe {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
    (h : IsGerbeOverScheme B S hS 𝒳) : IsGerbe B S hS 𝒳 := by
  obtain ⟨T, f, hf⟩ := h
  exact ⟨schemeStack.{u, w} B S hS T,
    isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS T, f, hf⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

open Polynomial

namespace AlgebraicGeometry.PPowerWeighted

attribute [local instance 100] ULift.algebra'

/-- The base `Spec ℤ` of the site. -/
local macro "𝒵" : term => `(Spec (CommRingCat.of (ULift ℤ)))

variable {𝒞 : BigFppfSite.{u}}

/-! ### Affine objects of the site over an affine object -/

section AlgebraSite

variable {R : Type u} [CommRing R] (hR : 𝒞.Contains (Spec (.of R)))
  (A : Type u) [CommRing A] [Algebra R A] (hA : 𝒞.Contains (Spec (.of A)))

/-- `Spec A` as an object of the site over `Spec ℤ`. -/
noncomputable abbrev algSiteObject : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) :=
  siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hA (specULiftZIsTerminal.from _)

/-- The morphism `Spec A ⟶ Spec R` of the site defined by the structure map of the algebra. -/
noncomputable def algSiteHom :
    algSiteObject A hA ⟶ siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hR
      (specULiftZIsTerminal.from _) :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (by
    ext
    exact specULiftZIsTerminal.hom_ext _ _)

/-- The underlying morphism of schemes of `algSiteHom` is `Spec.map` of the structure map. -/
theorem toScheme_map_algSiteHom :
    (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map (algSiteHom hR A hA) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  rfl

/-- The ring map of a composite with `algSiteHom`. -/
theorem siteHomEquiv_comp_algSiteHom {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (m : V ⟶ algSiteObject A hA) :
    siteHomEquiv hR _ V (m ≫ algSiteHom hR A hA) =
      CommRingCat.ofHom (algebraMap R A) ≫ siteHomEquiv hA _ V m :=
  specRingHom_comp_specMap ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map m)
    (CommRingCat.ofHom (algebraMap R A))

/-- The `R`-algebra structure on the global sections of an object `W` over `Spec R`. -/
noncomputable abbrev overAlgebra
    (W : Over (siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hR (specULiftZIsTerminal.from _))) :
    Algebra R Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤) :=
  (siteHomEquiv hR _ W.left W.hom).hom.toAlgebra

/-- **Morphisms over `Spec R` into `Spec A` are `R`-algebra maps out of `A`**: for an object `W`
of the site over `Spec R`, a morphism `W ⟶ Spec A` over `Spec R` is an `R`-algebra map
`A ⟶ Γ(W)`, for the algebra structure on `Γ(W)` given by the structure morphism of `W`. -/
noncomputable def overHomEquiv
    (W : Over (siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hR (specULiftZIsTerminal.from _))) :
    letI := overAlgebra hR W
    (W ⟶ Over.mk (algSiteHom hR A hA)) ≃
      (A →ₐ[R] Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤)) :=
  letI := overAlgebra hR W
  { toFun m :=
      { toRingHom := (siteHomEquiv hA _ W.left m.left).hom
        commutes' r := by
          have hw : m.left ≫ algSiteHom hR A hA = W.hom := Over.w m
          have e := congrArg (fun φ => φ.hom r) (siteHomEquiv_comp_algSiteHom hR A hA m.left)
          rw [hw] at e
          exact e.symm }
    invFun ψ := Over.homMk ((siteHomEquiv hA _ W.left).symm (CommRingCat.ofHom ψ.toRingHom))
      ((siteHomEquiv hR _ W.left).injective ((siteHomEquiv_comp_algSiteHom hR A hA _).trans (by
        rw [Equiv.apply_symm_apply]
        ext r
        exact ψ.commutes r)))
    left_inv m := Over.OverMorphism.ext ((congrArg (siteHomEquiv hA _ W.left).symm
      (CommRingCat.ofHom_hom _)).trans (Equiv.symm_apply_apply _ _))
    right_inv ψ := AlgHom.ext fun x => congrArg (fun φ => φ.hom x)
      (Equiv.apply_symm_apply (siteHomEquiv hA _ W.left) (CommRingCat.ofHom ψ.toRingHom)) }

/-- The algebra map attached to a morphism over `Spec R` is its ring map. -/
theorem overHomEquiv_apply
    (W : Over (siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hR (specULiftZIsTerminal.from _)))
    (m : W ⟶ Over.mk (algSiteHom hR A hA)) (x : A) :
    overHomEquiv hR A hA W m x = (siteHomEquiv hA _ W.left m.left).hom x :=
  rfl

/-- **Naturality of `overHomEquiv`**: precomposition with a morphism `u` over `Spec R` is
restriction of functions along `u`. -/
theorem overHomEquiv_comp
    {W₁ W₂ : Over (siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hR (specULiftZIsTerminal.from _))}
    (u : W₁ ⟶ W₂) (m : W₂ ⟶ Over.mk (algSiteHom hR A hA)) (x : A) :
    overHomEquiv hR A hA W₁ (u ≫ m) x = restrict u.left (overHomEquiv hR A hA W₂ m x) := by
  rw [overHomEquiv_apply, overHomEquiv_apply, Over.comp_left, siteHomEquiv_comp]
  rfl

/-- `Spec A ⟶ Spec R` is flat exactly when `A` is a flat `R`-module. -/
theorem flat_toScheme_map_algSiteHom_iff :
    Flat ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map (algSiteHom hR A hA)) ↔
      Module.Flat R A := by
  rw [toScheme_map_algSiteHom, HasRingHomProperty.Spec_iff (P := @Flat),
    CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]

include hR in
variable {A} in
/-- `Spec A` belongs to the site as soon as `Spec R` does and `A` is of finite type over `R`. -/
theorem contains_of_finiteType [Algebra.FiniteType R A] : 𝒞.Contains (Spec (.of A)) := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) hR

end AlgebraSite

/-! ### The affine line and its points of `U` -/

section Line

variable {k : Type u} [CommRing k]

/-- The affine line `Spec k[s]` belongs to the site as soon as `U` does: it is the closed
subscheme `x_1 = x_2 = ⋯ = 0` of `U`. -/
theorem contains_line (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    𝒞.Contains (Spec (.of k[X])) := by
  let φ : MvPolynomial ℕ k →ₐ[k] k[X] := MvPolynomial.aeval fun j => if j = 0 then X else 0
  have hφ : Function.Surjective φ := fun q => ⟨Polynomial.aeval (MvPolynomial.X 0) q, by
    rw [← Polynomial.aeval_algHom_apply]
    simp [φ]⟩
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (φ : MvPolynomial ℕ k →+* k[X])) hφ
  exact Scheme.size_lt_of_isClosedImmersion
    (Spec.map (CommRingCat.ofHom (φ : MvPolynomial ℕ k →+* k[X]))) hU

/-- The affine line `Spec k[s]` as an object of the site over `Spec ℤ`. -/
noncomputable abbrev lineSiteObject (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) :=
  siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (contains_line hU) (specULiftZIsTerminal.from _)

variable {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- The point of `U` over the affine line `Spec k[s]` with coordinates the given polynomials. -/
noncomputable def linePoint (c : ℕ → k[X]) : lineSiteObject hU ⟶ totalSiteObject 𝒞 k hU :=
  pointOfCoords ((Scheme.ΓSpecIso (.of k[X])).inv.hom.comp Polynomial.C)
    (fun j => (Scheme.ΓSpecIso (.of k[X])).inv.hom (c j))

/-- The coordinates of the restriction of `linePoint c` to an object `W` over the line are the
images of the polynomials `c j` in `Γ(W)`. -/
theorem coord_comp_linePoint (W : Over (lineSiteObject hU)) (c : ℕ → k[X]) (j : ℕ) :
    coord (W.hom ≫ linePoint c) j = (siteHomEquiv (contains_line hU) _ W.left W.hom).hom (c j) := by
  rw [coord_comp, linePoint, coord_pointOfCoords]
  rfl

/-- The reduced line: `Spec k[s]` is reduced over a domain. -/
theorem isReduced_lineSiteObject [IsDomain k] :
    IsReduced ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj (lineSiteObject hU)) :=
  inferInstanceAs (IsReduced (Spec (.of k[X])))

end Line

/-- A unit `γ` fixes a `W`-point `h` of `U` exactly when it fixes each of its coordinates,
`γ ^ p ^ j * h_j = h_j`. -/
theorem actMap_eq_self_iff_forall_coord (p : ℕ) {k : Type u} [CommRing k]
    {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}
    {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    actMap p γ h = h ↔ ∀ j, γ.val ^ p ^ j * coord h j = coord h j :=
  ⟨fun e j => by rw [← coord_actMap, e], fun H => hom_ext_coord (scalarMap_actMap p γ h)
    (fun j => by rw [coord_actMap, H])⟩

/-! ### The stabilizer of the test points -/

section Stabilizer

variable (p : ℕ) {k : Type u} [CommRing k] {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- The coordinates of the test point over the affine line `Spec k[s]` joining the strata `X_a`
and `X_b`: `x_a = s`, `x_b = 1` when `b` is finite, and all other coordinates `0`. Away from
`s = 0` it lies in `X_a`, and at `s = 0` in `X_b`. -/
noncomputable def testCoords (a : ℕ) (b : WithTop ℕ) : ℕ → k[X] := fun j =>
  if j = a then X else if (j : WithTop ℕ) = b then 1 else 0

/-- **The stabilizer of the test point.** Over an object `W` of the site over `Spec k[s]`, a unit
`γ` of `Γ(W)` fixes the test point joining `X_a` and `X_b` exactly when `γ ^ p ^ b = 1` (for `b`
finite) and `s γ ^ p ^ a = s`. -/
theorem actMap_comp_linePoint_eq_self_iff {a : ℕ} {b : WithTop ℕ} (hab : (a : WithTop ℕ) ≠ b)
    (W : Over (lineSiteObject hU))
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤))ˣ) :
    letI := overAlgebra (contains_line hU) W
    actMap p γ (W.hom ≫ linePoint (testCoords a b)) = W.hom ≫ linePoint (testCoords a b) ↔
      (∀ n : ℕ, (n : WithTop ℕ) = b → γ ^ p ^ n = 1) ∧
        algebraMap k[X] Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤)
            X * ((γ ^ p ^ a : _ˣ) : _) =
          algebraMap k[X] Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤)
            X := by
  let := overAlgebra (contains_line hU) W
  have hc : ∀ j, coord (W.hom ≫ linePoint (testCoords a b)) j =
      algebraMap k[X] _ (testCoords a b j) := fun j => coord_comp_linePoint W _ j
  rw [actMap_eq_self_iff_forall_coord]
  simp only [hc]
  constructor
  · intro H
    refine ⟨fun n hn => ?_, ?_⟩
    · have hna : n ≠ a := fun h => hab (h ▸ hn)
      have := H n
      rw [testCoords, ite_eq_right hna, ite_eq_left hn, map_one, mul_one] at this
      exact Units.val_eq_one.mp (by rwa [Units.val_pow_eq_pow_val])
    · have := H a
      rw [testCoords, ite_eq_left rfl] at this
      rwa [Units.val_pow_eq_pow_val, mul_comm]
  · rintro ⟨H₁, H₂⟩ j
    by_cases hja : j = a
    · subst hja
      rwa [testCoords, ite_eq_left rfl, mul_comm, ← Units.val_pow_eq_pow_val]
    · by_cases hjb : (j : WithTop ℕ) = b
      · rw [testCoords, ite_eq_right hja, ite_eq_left hjb, map_one, mul_one,
          ← Units.val_pow_eq_pow_val, H₁ j hjb, Units.val_one]
      · rw [testCoords, ite_eq_right hja, ite_eq_right hjb, map_zero, mul_zero]

/-- The stabilizer of the test point joining `X_a` and `X_b`, for `a < b` finite, is corepresented
by the stabilizer algebra `k[s][t, t⁻¹] / (t^{p^b} - 1, s (t^{p^a} - 1))`. -/
noncomputable def stabilizerEquiv {a b : ℕ} (hab : a ≠ b) (W : Over (lineSiteObject hU)) :
    letI := overAlgebra (contains_line hU) W
    (StabilizerAlgebra k (p ^ a) (p ^ b) →ₐ[k[X]]
        Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤)) ≃
      {γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤))ˣ //
        actMap p γ (W.hom ≫ linePoint (testCoords a b)) = W.hom ≫ linePoint (testCoords a b)} :=
  letI := overAlgebra (contains_line hU) W
  (stabilizerAlgebraHomEquiv _ _ _).trans <| Equiv.subtypeEquivRight fun γ => by
    rw [actMap_comp_linePoint_eq_self_iff p (by exact_mod_cast hab)]
    exact and_congr_left' ⟨fun h n hn => by
      obtain rfl : n = b := by exact_mod_cast hn
      exact h,
      fun h => h b rfl⟩

/-- The stabilizer of the test point joining `X_a` and `X_∞` is corepresented by the stabilizer
algebra `k[s][t, t⁻¹] / (s (t^{p^a} - 1))`. -/
noncomputable def stabilizerEquivInfty (a : ℕ) (W : Over (lineSiteObject hU)) :
    letI := overAlgebra (contains_line hU) W
    (StabilizerAlgebraInfty k (p ^ a) →ₐ[k[X]]
        Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤)) ≃
      {γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤))ˣ //
        actMap p γ (W.hom ≫ linePoint (testCoords a ⊤)) = W.hom ≫ linePoint (testCoords a ⊤)} :=
  letI := overAlgebra (contains_line hU) W
  (stabilizerAlgebraInftyHomEquiv _ _).trans <| Equiv.subtypeEquivRight fun γ => by
    rw [actMap_comp_linePoint_eq_self_iff p WithTop.coe_ne_top]
    exact ⟨fun h => ⟨fun n hn => absurd hn WithTop.coe_ne_top, h⟩, fun h => h.2⟩

/-- The unit attached by `stabilizerEquiv` to an algebra map is the image of `t`. -/
theorem stabilizerEquiv_apply_val {a b : ℕ} (hab : a ≠ b) (W : Over (lineSiteObject hU))
    (ψ : letI := overAlgebra (contains_line hU) W
      StabilizerAlgebra k (p ^ a) (p ^ b) →ₐ[k[X]]
        Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤)) :
    ((stabilizerEquiv p hab W ψ).1 : _) = ψ (Ideal.Quotient.mk _ (LaurentPolynomial.T 1)) :=
  rfl

/-- The unit attached by `stabilizerEquivInfty` to an algebra map is the image of `t`. -/
theorem stabilizerEquivInfty_apply_val (a : ℕ) (W : Over (lineSiteObject hU))
    (ψ : letI := overAlgebra (contains_line hU) W
      StabilizerAlgebraInfty k (p ^ a) →ₐ[k[X]]
        Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W.left, ⊤)) :
    ((stabilizerEquivInfty p a W ψ).1 : _) = ψ (Ideal.Quotient.mk _ (LaurentPolynomial.T 1)) :=
  rfl

end Stabilizer

/-! ### Automorphism sheaves corepresented over an affine base are flat -/

section Flat

variable {R : Type u} [CommRing R] (hR : 𝒞.Contains (Spec (.of R)))
  (A : Type u) [CommRing A] [Algebra R A] (hA : 𝒞.Contains (Spec (.of A)))

open Stack.AlgebraicStacks in
/-- **An automorphism sheaf of a gerbe corepresented by an algebra is flat.** Let `x` be an object
of an algebraic stack `𝒳` over `Spec ℤ`, lying over `Spec R` and in a full substack `Q` which is
a gerbe. If the automorphism sheaf `Isom(x, x)` on the site over `Spec R` is represented by
`Spec A`, through a family of bijections natural in the test object, then `A` is flat over `R`.

This is `flat_and_locallyOfFinitePresentation_of_isGerbe_fullSubcategoryAlgebraicStack` (in the
namespace `AlgebraicGeometry.Stack.AlgebraicStacks`) at the morphism `Spec A ⟶ Spec R`, read
through `AlgebraicGeometry.PPowerWeighted.flat_toScheme_map_algSiteHom_iff`. -/
theorem module_flat_of_isGerbe {𝒳 : Stack.AlgebraicStacks.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (Q : ObjectProperty 𝒳.val.val.obj)
    (hQ : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased 𝒳 Q))
    (hgerbe : Stack.AlgebraicStacks.IsGerbe 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryAlgebraicStack 𝒳 Q hQ))
    (x : 𝒳.val.val.p.Fiber
      (siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hR (specULiftZIsTerminal.from _)))
    (hx : Q x.1) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    ∀ (e : ∀ W, (W ⟶ Over.mk (algSiteHom hR A hA)) ≃ (𝒳.val.val.p.isomPresheaf x x).obj (op W)),
      (∀ ⦃W₁ W₂⦄ (u : W₁ ⟶ W₂) (m : W₂ ⟶ Over.mk (algSiteHom hR A hA)),
        e W₁ (u ≫ m) = (𝒳.val.val.p.isomPresheaf x x).map u.op (e W₂ m)) →
      Module.Flat R A := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  intro e he
  rw [← flat_toScheme_map_algSiteHom_iff hR A hA]
  exact (flat_and_locallyOfFinitePresentation_of_isGerbe_fullSubcategoryAlgebraicStack 𝒳 Q hQ
    hgerbe _ x hx (algSiteHom hR A hA)
    (NatIso.ofComponents (fun W => (e W.unop).toIso) (fun u => by
      ext m
      exact he u.unop m))).1

end Flat

/-! ### Coarsenings of a partition -/

section Coarsening

variable {X : Type*} {ι : Type*}

/-- **A coarsening of a covering family in which no member contains two of its sets is the
family itself.** Let `σ` be a family of subsets covering `X` and `Qs` a partition of `X` refined
by the sets of `σ`. If no member of `Qs` contains two distinct sets of the family, then `Qs` is
exactly the set of sets of the family. -/
theorem eq_range_of_refines_of_forall_subset {σ : ι → Set X} (hσ : ∀ x, ∃ a, x ∈ σ a)
    {Qs : Set (Set X)} (hQs : Setoid.IsPartition Qs)
    (href : ∀ s ∈ Set.range σ, ∃ t ∈ Qs, s ⊆ t)
    (hsep : ∀ t ∈ Qs, ∀ a b, σ a ⊆ t → σ b ⊆ t → a = b) :
    Qs = Set.range σ := by
  have key : ∀ a, ∀ t ∈ Qs, σ a ⊆ t → t = σ a := fun a t ht hat => by
    refine subset_antisymm (fun x hx => ?_) hat
    obtain ⟨b, hb⟩ := hσ x
    obtain ⟨t', ht', hbt'⟩ := href _ ⟨b, rfl⟩
    have htt' : t' = t := (hQs.2 x).unique ⟨ht', hbt' hb⟩ ⟨ht, hx⟩
    rw [hsep t ht a b hat (htt' ▸ hbt')]
    exact hb
  ext t
  constructor
  · intro ht
    obtain ⟨x, hx⟩ : t.Nonempty := Set.nonempty_iff_ne_empty.mpr fun he => hQs.1 (he ▸ ht)
    obtain ⟨a, ha⟩ := hσ x
    obtain ⟨t', ht', hat'⟩ := href _ ⟨a, rfl⟩
    have htt' : t' = t := (hQs.2 x).unique ⟨ht', hat' ha⟩ ⟨ht, hx⟩
    exact ⟨a, (key a t ht (htt' ▸ hat')).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨t, ht, hat⟩ := href _ ⟨a, rfl⟩
    rwa [← key a t ht hat]

end Coarsening

/-- The stabilizer algebra over the line belongs to the site. -/
theorem contains_stabilizerAlgebra {k : Type u} [CommRing k]
    (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) (m N : ℕ) :
    𝒞.Contains (Spec (.of (StabilizerAlgebra k m N))) :=
  contains_of_finiteType (contains_line hU)

/-- The stabilizer algebra without root of unity over the line belongs to the site. -/
theorem contains_stabilizerAlgebraInfty {k : Type u} [CommRing k]
    (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) (m : ℕ) :
    𝒞.Contains (Spec (.of (StabilizerAlgebraInfty k m))) :=
  contains_of_finiteType (contains_line hU)

/-! ### The test object over the line is not in a gerbe -/

section Core

variable (p : ℕ) {k : Type u} [CommRing k] {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- `AlgebraicGeometry.PPowerWeighted.chartIsomEquiv_naturality` along an arbitrary morphism of
the slice. -/
theorem chartIsomEquiv_map {T : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h h' : T ⟶ totalSiteObject 𝒞 k hU) {W₁ W₂ : Over T} (u : W₁ ⟶ W₂)
    (s : ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.isomPresheaf (chartFiber.{u, w} p h)
        (chartFiber.{u, w} p h')).obj (op W₂)) :
    (chartIsomEquiv.{u, w} p h h' W₁.hom
        (((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.isomPresheaf (chartFiber.{u, w} p h)
          (chartFiber.{u, w} p h')).map u.op s)).1 =
      Units.map (restrict u.left).toMonoidHom (chartIsomEquiv.{u, w} p h h' W₂.hom s).1 := by
  have key : ∀ {V V' : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (f₂ : V ⟶ T)
      (g : V' ⟶ V) (f₁ : V' ⟶ T) (e : g ≫ f₂ = f₁)
      (s : ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.isomPresheaf
        (chartFiber.{u, w} p h) (chartFiber.{u, w} p h')).obj (op (Over.mk f₂))),
      (chartIsomEquiv.{u, w} p h h' f₁
        (((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.isomPresheaf (chartFiber.{u, w} p h)
          (chartFiber.{u, w} p h')).map (Over.homMk g e : Over.mk f₁ ⟶ Over.mk f₂).op s)).1 =
        Units.map (restrict g).toMonoidHom (chartIsomEquiv.{u, w} p h h' f₂ s).1 := by
    rintro V V' f₂ g _ rfl s
    exact chartIsomEquiv_naturality.{u, w} p h h' f₂ g s
  exact key W₂.hom u.left W₁.hom (Over.w u) s

/-- **The test object joining two strata does not lie in a gerbe.** Let `Q` cut out a full
substack of `𝒳 = [U/𝐆_m]` which is an algebraic stack and a gerbe, `1 < p`, and `a < b`. Then
the object of `𝒳` over the line `Spec k[s]` given by the point `x_a = s`, `x_b = 1`, all other
coordinates `0` (for `b = ∞`: `x_a = s`, all others `0`) is not in `Q`: its automorphism sheaf
is represented by the spectrum of the stabilizer algebra
`k[s][t, t⁻¹] / (t^{p^b} - 1, s (t^{p^a} - 1))` (resp. `k[s][t, t⁻¹] / (s (t^{p^a} - 1))`),
which is not flat over `k[s]`, whereas automorphism sheaves of gerbes are flat. -/
theorem not_prop_chartObj_linePoint [Nontrivial k] (hp : 1 < p)
    (Q : ObjectProperty (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj)
    (hQ : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU) Q))
    (hgerbe : Stack.AlgebraicStacks.IsGerbe 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU) Q hQ))
    {a : ℕ} {b : WithTop ℕ} (hab : (a : WithTop ℕ) < b) :
    ¬ Q (chartObj.{u, w} p (linePoint (hU := hU) (testCoords a b))) := by
  intro hx
  induction b using WithTop.recTopCoe
  on_goal 1 =>
    apply not_flat_stabilizerAlgebraInfty_pow (k := k) a hp
    refine module_flat_of_isGerbe (contains_line hU) _ (contains_stabilizerAlgebraInfty hU _) Q hQ
      hgerbe (chartFiber.{u, w} p (linePoint (testCoords a ⊤))) hx
      (fun W => ((overHomEquiv _ _ _ W).trans (stabilizerEquivInfty p a W)).trans
        (chartIsomEquiv.{u, w} p _ _ W.hom).symm) ?_
  on_goal 2 =>
    rename_i n
    have han : a < n := WithTop.coe_lt_coe.mp hab
    apply not_flat_stabilizerAlgebra_pow (k := k) hp han
    refine module_flat_of_isGerbe (contains_line hU) _ (contains_stabilizerAlgebra hU _ _) Q hQ
      hgerbe (chartFiber.{u, w} p (linePoint (testCoords a n))) hx
      (fun W => ((overHomEquiv _ _ _ W).trans (stabilizerEquiv p han.ne W)).trans
        (chartIsomEquiv.{u, w} p _ _ W.hom).symm) ?_
  all_goals
    intro W₁ W₂ u m
    apply (chartIsomEquiv.{u, w} p _ _ W₁.hom).injective
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    apply Subtype.ext
    rw [chartIsomEquiv_map]
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    apply Units.ext
    simp only [Units.coe_map, stabilizerEquiv_apply_val, stabilizerEquivInfty_apply_val,
      overHomEquiv_comp]
    rfl

end Core

/-! ### The points of the test object -/

section TestPoints

variable (p : ℕ) {k : Type u} [CommRing k] {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- The field-valued point of `𝒳 = [U/𝐆_m]` attached to a field-valued point `q` of the scheme
stack of `W` and a `W`-point `h` of `U`: the chart object of the composite `q ⟶ W ⟶ U`, in the
form of `AlgebraicGeometry.PPowerWeighted.chartPointMap_base_eq`. -/
noncomputable def chartFieldPoint {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    (q : Stack.FieldValuedPoint 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) W).val.val) :
    Stack.FieldValuedPoint 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val where
  carrier := q.carrier
  base := q.obj.left
  isSpec := (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).mapIso (eqToIso q.over) ≪≫
    q.isSpec
  obj := chartObj.{u, w} p (𝟙 q.obj.left ≫ q.obj.hom ≫ h)
  «over» := Functor.congr_obj (chart.{u, w} 𝒞 k p hU).hom.hom.w
    (Over.mk (𝟙 q.obj.left ≫ q.obj.hom ≫ h))

/-- **The points of the 1-morphism named by a chart object.** The image of the point of the
scheme stack of `W` represented by a field-valued point `q` under the 1-morphism
`(Sch/W) ⟶ 𝒳` named by the chart object of `h : W ⟶ U` is the class of the chart object of the
composite `q ⟶ W ⟶ U`. -/
theorem pointsMap_fibreObjectStackMap_chartFiber
    {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (h : W ⟶ totalSiteObject 𝒞 k hU)
    (q : Stack.FieldValuedPoint 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) W).val.val) :
    Stack.AlgebraicStacks.pointsMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (Bicategory.InducedBicategory.mkHom
          (X := Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) W)
          (Y := weightedQuotientStack.{u, w} 𝒞 k p hU)
          (Stack.fibreObjectFibredMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
            (weightedQuotientStack.{u, w} 𝒞 k p hU).val W (chartFiber.{u, w} p h)))
        (Stack.pointClass 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _ q) =
      Stack.pointClass 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _ (chartFieldPoint.{u, w} p h q) := by
  refine (Stack.pointsMap_class _ _ _ _ _ _ _ _).trans
    ((Stack.class_eq_class_iff_hasCommonExtension _ _ _ _ _ _ _).2
      ⟨chartFieldPoint.{u, w} p h q, ⟨?_⟩, ⟨𝟙 _⟩⟩)
  let L := Functor.TwoYoneda.chosenLift (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.isFiberedInGroupoids W (chartFiber.{u, w} p h)
    q.obj
  have hL : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsStronglyCartesian q.obj.hom L.φ :=
    L.isStronglyCartesian
  exact (Functor.IsStronglyCartesian.map (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
    q.obj.hom L.φ (f' := 𝟙 _ ≫ q.obj.hom) (g := 𝟙 _) rfl
    (chartHom.{u, w} p (𝟙 _ ≫ q.obj.hom) (Category.assoc _ _ _)) :
      chartObj.{u, w} p (𝟙 q.obj.left ≫ q.obj.hom ≫ h) ⟶ L.y)

/-- Over a field, the test point joining `X_a` and `X_b` lies in `X_a` or in `X_b`: in `X_a`
where `s` is invertible, in `X_b` where `s = 0`. -/
theorem isPointInStratumAt_testCoords {F : Type*} [CommRing F] (hF : IsField F) (φ : k[X] →+* F)
    {a : ℕ} {b : WithTop ℕ} (hab : (a : WithTop ℕ) < b) :
    IsPointInStratumAt a (fun j => φ (testCoords a b j)) ∨
      IsPointInStratumAt b (fun j => φ (testCoords a b j)) := by
  by_cases hs : φ X = 0
  · right
    induction b using WithTop.recTopCoe with
    | top =>
      intro j
      dsimp only
      rw [testCoords]
      split_ifs with h₁ h₂
      · exact hs
      · exact absurd h₂ WithTop.coe_ne_top
      · exact map_zero φ
    | coe n =>
      refine (isPointInStratumAt_coe n _).mpr ⟨fun j hj => ?_, ?_⟩
      · dsimp only
        rw [testCoords]
        split_ifs with h₁ h₂
        · exact hs
        · exact absurd (WithTop.coe_eq_coe.mp h₂) hj.ne
        · exact map_zero φ
      · dsimp only
        have han : n ≠ a := fun h => (lt_irrefl (a : WithTop ℕ)) (h ▸ hab)
        simp [testCoords, han]
  · left
    rw [isPointInStratumAt_coe]
    refine ⟨fun j hj => ?_, ?_⟩
    · dsimp only
      have hjb : (j : WithTop ℕ) ≠ b := ((WithTop.coe_lt_coe.mpr hj).trans hab).ne
      rw [testCoords, ite_eq_right hj.ne, ite_eq_right hjb, map_zero]
    · dsimp only
      rw [testCoords, ite_eq_left rfl]
      exact IsUnit.of_mul_eq_one _ (hF.mul_inv_cancel hs).choose_spec

end TestPoints

/-! ### No locally closed gerbe contains two strata -/

section TwoStrata

variable (p : ℕ) {k : Type u} [CommRing k] {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- Every point of the line maps, under the test point joining `X_a` and `X_b`, into
`|𝒳_a| ∪ |𝒳_b|`. -/
theorem pointsMap_chartFiber_linePoint_mem {a : ℕ} {b : WithTop ℕ} (hab : (a : WithTop ℕ) < b)
    (q : Stack.AlgebraicStacks.points 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (lineSiteObject hU))) :
    Stack.AlgebraicStacks.pointsMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (Bicategory.InducedBicategory.mkHom
          (X := Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (lineSiteObject hU))
          (Y := weightedQuotientStack.{u, w} 𝒞 k p hU)
          (Stack.fibreObjectFibredMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
            (weightedQuotientStack.{u, w} 𝒞 k p hU).val (lineSiteObject hU)
            (chartFiber.{u, w} p (linePoint (testCoords a b))))) q ∈
      stratumPoints.{u, w} 𝒞 k p hU a ∪ stratumPoints.{u, w} 𝒞 k p hU b := by
  induction q using Quotient.inductionOn with
  | h q =>
    rw [pointsMap_fibreObjectStackMap_chartFiber]
    let e : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj q.obj.left ≅
        Spec (.of q.carrier) :=
      (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).mapIso (eqToIso q.over) ≪≫ q.isSpec
    let x := e.inv.base (IsLocalRing.closedPoint q.carrier)
    have hF := isField_of_iso_spec e
    have hpt : Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) (((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map
          (q.obj.hom ≫ linePoint (testCoords a b))).base x) =
        Stack.pointClass 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
          (chartFieldPoint.{u, w} p (linePoint (testCoords a b)) q) :=
      chartPointMap_base_eq.{u, w} p e (q.obj.hom ≫ linePoint (testCoords a b)) x
    have hmem : ∀ (c : WithTop ℕ) (z : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
        (totalSiteObject 𝒞 k hU)), Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵
          (Space.contains_specULiftZ 𝒞) _ _ (chart.{u, w} 𝒞 k p hU) z ∈
            stratumPoints.{u, w} 𝒞 k p hU c ↔ totalHomeomorph 𝒞 k hU z ∈ stratumSet k c :=
      fun c z => by rw [← Set.mem_preimage, preimage_stratumPoints, Set.mem_preimage]
    rw [← hpt, Set.mem_union, hmem, hmem, ← mem_stratumSubfunctor_iff_of_isField hF,
      ← mem_stratumSubfunctor_iff_of_isField hF, mem_stratumSubfunctor_iff,
      mem_stratumSubfunctor_iff]
    have hc : coord (q.obj.hom ≫ linePoint (testCoords a b)) =
        fun j => (siteHomEquiv (contains_line hU) _ q.obj.left q.obj.hom).hom (testCoords a b j) :=
      funext (coord_comp_linePoint q.obj _)
    rw [hc]
    exact isPointInStratumAt_testCoords hF _ hab

/-- **Stacks 06RE, the core of minimality: no locally closed gerbe contains two strata.** Let `k`
be a domain (for instance a field), `1 < p`, and let `Q` cut out a locally closed substack of
`𝒳 = [U/𝐆_m]` which is a gerbe. Then the points of `Q` do not contain two strata `|𝒳_a|` and
`|𝒳_b|` with `a < b`.

Over the reduced line `Spec k[s]`, the point `x_a = s`, `x_b = 1` (and `x_a = s` alone when
`b = ∞`) has all its points in `|𝒳_a| ∪ |𝒳_b|`, so it lies in `Q`
(`AlgebraicGeometry.Stack.prop_of_forall_pointsMap_mem`); but its automorphism sheaf is not flat
(`AlgebraicGeometry.PPowerWeighted.not_prop_chartObj_linePoint`). -/
theorem not_stratumPoints_union_subset [IsDomain k] (hp : 1 < p)
    (Q : ObjectProperty (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj)
    (hQlc : Stack.IsLocallyClosedSubstack (weightedQuotientStack.{u, w} 𝒞 k p hU) Q)
    (hQ : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU) Q))
    (hgerbe : Stack.AlgebraicStacks.IsGerbe 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU) Q hQ))
    {a b : WithTop ℕ} (hab : a < b) :
    ¬ stratumPoints.{u, w} 𝒞 k p hU a ∪ stratumPoints.{u, w} 𝒞 k p hU b ⊆
      Set.range (Stack.AlgebraicStacks.pointsMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (Stack.fullSubcategoryInclusion (weightedQuotientStack.{u, w} 𝒞 k p hU) Q hQ)) := by
  intro hsub
  obtain ⟨i, rfl⟩ := WithTop.ne_top_iff_exists.mp hab.ne_top
  exact not_prop_chartObj_linePoint p hp Q hQ hgerbe hab
    (Stack.prop_of_forall_pointsMap_mem 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hQlc
      isReduced_lineSiteObject (chartFiber.{u, w} p (linePoint (testCoords i b)))
      (fun q => hsub (pointsMap_chartFiber_linePoint_mem p hab q)))

end TwoStrata

/-! ### Minimality -/

section Minimal

variable (p : ℕ) {k : Type u} [CommRing k] {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- **The strata cover `|𝒳|`**: every point of `𝒳 = [U/𝐆_m]` lies in some stratum `|𝒳_a|`, being
the image of a point of `U`, which lies in some stratum `X_a`. -/
theorem exists_mem_stratumPoints
    (x : Stack.AlgebraicStacks.points 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU)) :
    ∃ a, x ∈ stratumPoints.{u, w} 𝒞 k p hU a := by
  obtain ⟨z, rfl⟩ := Stack.AlgebraicStacks.surjective_chartPointMap 𝒞 𝒵 _ _ _ _
    (isSurjective_chart 𝒞 k p hU) x
  have hz : totalHomeomorph 𝒞 k hU z ∈ (⋃ i, stratum k i) ∪ stratumInf k := by
    rw [iUnion_stratum_union_stratumInf]
    trivial
  have hmem : ∀ c, totalHomeomorph 𝒞 k hU z ∈ stratumSet k c →
      Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) z ∈ stratumPoints.{u, w} 𝒞 k p hU c := fun c hc => by
    rwa [← Set.mem_preimage, preimage_stratumPoints]
  rcases hz with hz | hz
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact ⟨i, hmem i hi⟩
  · exact ⟨⊤, hmem ⊤ hz⟩

/-- **Stacks 06RE, minimality of the stratification by gerbes.** Let `k` be a domain (for
instance a field) and `1 < p` (for instance `p` prime). Let `Qs` be a partition of the space of
points `|𝒳|` of `𝒳 = [U/𝐆_m]` into locally closed subsets, each of which is the set of points of
a reduced locally closed substack of `𝒳` which is a gerbe over a scheme. If the strata
`|𝒳_a|`, `a ∈ ℕ ∪ {∞}`, refine `Qs`, then `Qs` is the stratification `{|𝒳_a|}` itself: there is
no coarser stratification with the same properties.

A member of `Qs` is a union of strata, as the strata cover `|𝒳|` and refine `Qs`; it cannot
contain two strata `|𝒳_a|`, `|𝒳_b|`, `a < b`, by
`AlgebraicGeometry.PPowerWeighted.not_stratumPoints_union_subset`, since a gerbe over a scheme is a
gerbe. Reducedness of the members is part of "the same properties" but is not needed. -/
theorem eq_range_stratumPoints_of_refines [IsDomain k] (hp : 1 < p) :
    letI := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val
    ∀ Qs : Set (Set (Stack.AlgebraicStacks.points 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (weightedQuotientStack.{u, w} 𝒞 k p hU))),
      IsTopologicalPartition Qs →
      (∀ s ∈ Qs, ∃ (W : ObjectProperty (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj)
          (_ : Stack.IsLocallyClosedSubstack (weightedQuotientStack.{u, w} 𝒞 k p hU) W),
        (∀ hA, Stack.IsReducedStack 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
            (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU) W hA) ∧
          Stack.AlgebraicStacks.IsGerbeOverScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
            (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU) W hA)) ∧
        ∀ hA, Set.range (Stack.AlgebraicStacks.pointsMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
          (Stack.fullSubcategoryInclusion (weightedQuotientStack.{u, w} 𝒞 k p hU) W hA)) = s) →
      local_Refines (Set.range (stratumPoints.{u, w} 𝒞 k p hU)) Qs →
      Qs = Set.range (stratumPoints.{u, w} 𝒞 k p hU) := by
  intro Qs hQs hmem href
  refine eq_range_of_refines_of_forall_subset (exists_mem_stratumPoints p) hQs.1 href ?_
  intro t ht a b hat hbt
  by_contra hne
  obtain ⟨W, hW, hgW, hrW⟩ := hmem t ht
  have key : ∀ {c d : WithTop ℕ}, c < d → stratumPoints.{u, w} 𝒞 k p hU c ⊆ t →
      stratumPoints.{u, w} 𝒞 k p hU d ⊆ t → False := fun hcd hc hd =>
    not_stratumPoints_union_subset p hp W hW hW.2.choose (hgW _).2.isGerbe hcd
      ((hrW hW.2.choose).symm ▸ Set.union_subset hc hd)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key h hat hbt
  · exact key h hbt hat

end Minimal

end AlgebraicGeometry.PPowerWeighted

end
