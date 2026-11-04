module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Global sections of the chart morphism `D(f t) ⟶ D₊(t)` of `Proj`

Let `𝒜 : ℕ → σ` be a graded ring, `X` a scheme and `f : A →+* Γ(X, ⊤)`. For `t` homogeneous of
positive degree `d`, Mathlib's `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` is the
morphism `X_{f t} ⟶ D₊(t)` out of the nonvanishing locus of `f t` into the standard chart of
`Proj 𝒜`, and `AlgebraicGeometry.Proj.fromOfGlobalSections` glues those charts into the morphism
`X ⟶ Proj 𝒜`. Mathlib records how the glued morphism restricts to a chart
(`Proj.fromOfGlobalSections_resLE`), which chart a basic open pulls back to
(`Proj.fromOfGlobalSections_preimage_basicOpen`) and the composite to `Spec 𝒜₀`
(`Proj.fromOfGlobalSections_toSpecZero`), but **not what the chart morphism does on sections**.

This file computes it. Both source and target are affine, so the chart morphism *is* its effect
on global sections, and the content of the file is the single identity

* `Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop`,

which says that, read through the canonical isomorphism
`AlgebraicGeometry.Proj.basicOpenIsoAway` of `(A_t)₀` with `Γ(Proj 𝒜, D₊(t))`, the map on
sections is the obvious one: the fraction `p / tᵏ` of `p` homogeneous of degree `k • d` goes to
`(f p)|_{X_{f t}} · ((f t)|_{X_{f t}})⁻ᵏ`, the inverse existing because the restriction of a
section to its own nonvanishing locus is a unit
(`AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`).

## Main definitions

* `Stacks.ProjGlobalSectionsAppTop.resLift`: for `r : Γ(X, ⊤)`, the ring homomorphism
  `Γ(X, ⊤)_r →+* Γ(X, X_r)` extending restriction, which exists because `r|_{X_r}` is a unit.
* `Stacks.ProjGlobalSectionsAppTop.projAwayHom`: **the ring homomorphism
  `(A_t)₀ →+* Γ(X, X_{f t})` of the title**, `p / tᵏ ↦ (f p)|_{X_{f t}} · ((f t)|_{X_{f t}})⁻ᵏ`.

## Main results

* `Stacks.ProjGlobalSectionsAppTop.toSpecΓ_resLE_basicOpenIsoSpecAway`: the open subscheme `X_r`
  maps to `Spec (Γ(X, ⊤)_r)` compatibly with `X ⟶ Spec Γ(X, ⊤)`. This is the one geometric input
  and it is a statement about an arbitrary scheme, with no grading in sight.
* `Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom`: the chart
  morphism, composed with `Proj.basicOpenIsoSpec`, is `Spec` of `projAwayHom`. This is the
  identity of scheme morphisms that the identity on sections is read off from.
* `Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop`: **the computation of
  `Scheme.Hom.appTop` of the chart morphism.**
* `Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk_of_mul_eq_one` and
  `projAwayHom_apply_mk`: the value of `projAwayHom` on a fraction, which is what makes the
  formula usable.
* `Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext`: two ring homomorphisms out of `(A_t)₀` that
  agree on every fraction `p / tᵏ` are equal.
* `Stacks.ProjGlobalSectionsAppTop.away_mk_zero`, `…away_mk_add`, `…away_mk_neg` and
  `…away_mk_mul`: the fraction `p / tᵏ` is additive in `p` at a fixed `k`, and multiplying two
  fractions adds the exponents. These are what let an *additive* generation statement for the
  homogeneous pieces of `𝒜` be transported to the fractions, which is how the extensionality
  above is refined to a test in bounded degree — see
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.away_ringHom_ext_degree_one`.
* `Stacks.ProjGlobalSectionsAppTop.eq_toBasicOpenOfGlobalSections`: the chart morphism is the
  *unique* morphism `X_{f t} ⟶ D₊(t)` with that effect on sections, which is how a competing
  morphism is identified with it.
* `Stacks.ProjGlobalSectionsAppTop.ι_comp_fromOfGlobalSections`: the inclusion of the chart
  followed by `Proj.fromOfGlobalSections` is the chart morphism followed by the inclusion of
  `D₊(t)`.

## Implementation notes

**The target ring is `Γ(X, X_{f t})`, not `Γ((X_{f t} : Scheme), ⊤)`.** The two are identified by
`AlgebraicGeometry.Scheme.Opens.topIso`, and the second is what `Scheme.Hom.appTop` produces, so
the identity below has a `topIso.inv` on its right-hand side. The first spelling is used because
`Γ(X, U)` is where restriction of sections of `𝒪_X` lives, hence where the formula is stated
without any transport; it is also the spelling `Scheme.Opens.toSpecΓ` is indexed by.

**No compiler option is relaxed, and that costs two rewrites.** `D(r) ⊆ Spec Γ(X, ⊤)` has two
spellings — `TopologicalSpace.Opens (PrimeSpectrum Γ(X, ⊤))` and `(Spec Γ(X, ⊤)).Opens` — which
are not the same expression at `implicit` transparency, so a goal mentioning
`AlgebraicGeometry.Scheme.Opens.ι (PrimeSpectrum.basicOpen r)` is reported as not type-correct and
`rw` refuses to fire on it; Mathlib's own neighbours
(`AlgebraicGeometry.basicOpenIsoSpecAway_inv_homOfLE`,
`AlgebraicGeometry.Proj.homOfLE_toBasicOpenOfGlobalSections_ι`) relax
`backward.isDefEq.respectTransparency` for exactly this. Here the two steps that would need it —
`AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` and
`AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top` — are applied as *terms* under
`exact`, which elaborates at default transparency, so nothing is rewritten and no option is set.

**`AlgebraicGeometry.Scheme.Hom.resLE`, not `∣_`.** The chart morphism's first factor is
`(X.isoOfEq _).inv ≫ X.toSpecΓ ∣_ D(f t)`, which is by definition
`X.toSpecΓ.resLE (D (f t)) (X_{f t}) _`; at that spelling the compatibility with the inclusion is
`Scheme.Hom.resLE_comp_ι`, whose statement never names `X.toSpecΓ ⁻¹ᵁ D(f t)`.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open HomogeneousLocalization

universe u

namespace Stacks.ProjGlobalSectionsAppTop

/-! ### Restriction to a nonvanishing locus as a localization -/

variable {X : Scheme.{u}}

/-- Restriction of a global section of `𝒪_X` to an open subset, as a ring homomorphism. -/
abbrev resTop (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top (a := U))).op).hom

/-- The restriction of a global section to its own nonvanishing locus is a unit. -/
theorem isUnit_resTop_basicOpen (r : Γ(X, ⊤)) : IsUnit (resTop (X.basicOpen r) r) :=
  X.toRingedSpace.isUnit_res_basicOpen r

/-- The inverse of `r|_{X_r}`. -/
abbrev resTopBasicOpenInv (r : Γ(X, ⊤)) : Γ(X, X.basicOpen r) :=
  ↑(isUnit_resTop_basicOpen r).unit⁻¹

/-- Restricting a global section to `V` and then to a smaller `W` is restricting it to `W`. -/
theorem resTop_comp {V W : X.Opens} (h : W ≤ V) :
    X.presheaf.map (homOfLE (le_top (a := V))).op ≫ X.presheaf.map (homOfLE h).op =
      X.presheaf.map (homOfLE (le_top (a := W))).op := by
  rw [← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- `resTop_comp` applied to a section. -/
theorem resTop_resTop {V W : X.Opens} (h : W ≤ V) (a : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resTop V a) = resTop W a :=
  CategoryTheory.ConcreteCategory.congr_hom (resTop_comp h) a

/-- **Restriction to the nonvanishing locus of `r`, extended to the localization `Γ(X, ⊤)_r`.**
It exists because `r|_{X_r}` is a unit; `X_r` need not be affine, so this need not be an
isomorphism. -/
def resLift (r : Γ(X, ⊤)) : Localization.Away r →+* Γ(X, X.basicOpen r) :=
  IsLocalization.Away.lift r (isUnit_resTop_basicOpen r)

/-- `resLift r` composed with the localization map `Γ(X, ⊤) → Γ(X, ⊤)_r` is the restriction
`Γ(X, ⊤) → Γ(X, X_r)`. -/
@[simp] theorem resLift_comp (r : Γ(X, ⊤)) :
    (resLift r).comp (algebraMap Γ(X, ⊤) (Localization.Away r)) = resTop (X.basicOpen r) :=
  IsLocalization.Away.lift_comp _ _

/-- **The nonvanishing locus `X_r` maps to `Spec (Γ(X, ⊤)_r)` compatibly with
`X ⟶ Spec Γ(X, ⊤)`.** -/
theorem toSpecΓ_resLE_basicOpenIsoSpecAway (r : Γ(X, ⊤)) :
    X.toSpecΓ.resLE (PrimeSpectrum.basicOpen r) (X.basicOpen r)
        (X.toSpecΓ_preimage_basicOpen r).ge ≫ (basicOpenIsoSpecAway r).hom =
      (X.basicOpen r).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (resLift r)) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, ⊤) (Localization.Away r))))]
  simp only [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, resLift_comp]
  exact (Scheme.Hom.resLE_comp_ι X.toSpecΓ _).trans
    (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top (X.basicOpen r)).symm

/-- A morphism to an affine scheme is `Spec` of its effect on sections. The form used below: if a
morphism out of an open subscheme `U` factors as `U.toSpecΓ ≫ Spec.map ψ`, then `ψ` *is* its
effect on global sections, read through `Scheme.Opens.topIso`. -/
theorem ΓSpecIso_inv_appTop_of_eq {R : CommRingCat.{u}} {U : X.Opens}
    {c : U.toScheme ⟶ Spec R} {ψ : R ⟶ Γ(X, U)} (h : c = U.toSpecΓ ≫ Spec.map ψ) :
    (Scheme.ΓSpecIso R).inv ≫ c.appTop = ψ ≫ U.topIso.inv := by
  subst h
  rw [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality_assoc,
    Iso.inv_hom_id_assoc]

/-! ### The ring homomorphism attached to a graded ring map -/

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (f : A →+* Γ(X, ⊤)) {t : A} {d : ℕ}

/-- `f` maps the powers of `t` into the powers of `f t`. -/
theorem powers_le :
    Submonoid.powers t ≤ (Submonoid.powers (f t)).comap (f : A →+* Γ(X, ⊤)) := by
  rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]

/-- The map `A_t →+* Γ(X, ⊤)_{f t}` of localizations induced by `f`. -/
abbrev awayLocMap : Localization.Away t →+* Localization.Away (f t) :=
  IsLocalization.map (M := Submonoid.powers t) (T := Submonoid.powers (f t))
    (Localization.Away (f t)) (f : A →+* Γ(X, ⊤)) (powers_le f)

/-- **The canonical ring homomorphism `(A_t)₀ →+* Γ(X, X_{f t})`**: the degree-zero fraction
`p / tᵏ` goes to `(f p)|_{X_{f t}} · ((f t)|_{X_{f t}})⁻ᵏ`. See `projAwayHom_apply_mk`. -/
def projAwayHom : Away 𝒜 t →+* Γ(X, X.basicOpen (f t)) :=
  ((resLift (f t)).comp (awayLocMap f)).comp (algebraMap (Away 𝒜 t) (Localization.Away t))

/-- `projAwayHom` factors through restriction to `X_{f t}` on elements of `A`. -/
theorem resLift_awayLocMap_comp :
    ((resLift (f t)).comp (awayLocMap f)).comp (algebraMap A (Localization.Away t)) =
      (resTop (X.basicOpen (f t))).comp (f : A →+* Γ(X, ⊤)) := by
  rw [RingHom.comp_assoc, IsLocalization.map_comp, ← RingHom.comp_assoc, resLift_comp]

/-- `projAwayHom` is `Localization.awayLift` of restriction, precomposed with the inclusion of
the degree-zero part of `A_t` into `A_t`. -/
theorem resLift_awayLocMap :
    (resLift (f t)).comp (awayLocMap f) =
      Localization.awayLift ((resTop (X.basicOpen (f t))).comp (f : A →+* Γ(X, ⊤))) t
        (isUnit_resTop_basicOpen (f t)) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers t) ?_
  rw [resLift_awayLocMap_comp, IsLocalization.Away.lift_comp]

/-- **The value of `projAwayHom` on the fraction `p / tᵏ`**, with an inverse of
`(f t)|_{X_{f t}}` supplied by the caller. This is the form the consumers use: the inverse is
hardly ever met as `IsUnit.unit⁻¹`, but always as something whose product with `(f t)|_{X_{f t}}`
is `1`. -/
theorem projAwayHom_apply_mk_of_mul_eq_one (hd : t ∈ 𝒜 d) (k : ℕ) (p : A) (hp : p ∈ 𝒜 (k • d))
    {v : Γ(X, X.basicOpen (f t))} (hv : resTop (X.basicOpen (f t)) (f t) * v = 1) :
    projAwayHom 𝒜 f (Away.mk 𝒜 hd k p hp) = resTop (X.basicOpen (f t)) (f p) * v ^ k := by
  rw [projAwayHom, RingHom.comp_apply, resLift_awayLocMap, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  exact Localization.awayLift_mk ((resTop (X.basicOpen (f t))).comp (f : A →+* Γ(X, ⊤))) t p _ hv k

/-- **The value of `projAwayHom` on the fraction `p / tᵏ`.** -/
theorem projAwayHom_apply_mk (hd : t ∈ 𝒜 d) (k : ℕ) (p : A) (hp : p ∈ 𝒜 (k • d)) :
    projAwayHom 𝒜 f (Away.mk 𝒜 hd k p hp) =
      resTop (X.basicOpen (f t)) (f p) * resTopBasicOpenInv (f t) ^ k :=
  projAwayHom_apply_mk_of_mul_eq_one 𝒜 f hd k p hp
    (isUnit_resTop_basicOpen (f t)).unit.mul_inv

/-- **Two ring homomorphisms out of `(A_t)₀` agreeing on every fraction `p / tᵏ` are equal.** -/
theorem away_ringHom_ext {P : Type*} [CommRing P] (hd : t ∈ 𝒜 d) {φ ψ : Away 𝒜 t →+* P}
    (h : ∀ (k : ℕ) (p : A) (hp : p ∈ 𝒜 (k • d)),
      φ (Away.mk 𝒜 hd k p hp) = ψ (Away.mk 𝒜 hd k p hp)) : φ = ψ := by
  refine RingHom.ext fun z => ?_
  obtain ⟨k, p, hp, rfl⟩ := Away.mk_surjective 𝒜 hd z
  exact h k p hp

/-! ### Fractions with a fixed denominator -/

/- The four identities below say that `HomogeneousLocalization.Away.mk 𝒜 hd k · ·` is additive in
its numerator at a fixed power of the denominator, and that raising the exponent adds. They are
what turns an additive generation statement for the homogeneous pieces of `𝒜` into one for the
fractions, which is how `away_ringHom_ext` is refined to a test on fractions of bounded degree.
`Stacks.GradedRationalPoint.awayFraction_add` is the case `d = k = 1` through that file's
subtype-valued wrapper. -/

/-- **The fraction `0 / tᵏ` is zero.** -/
theorem away_mk_zero (hd : t ∈ 𝒜 d) (k : ℕ) : Away.mk 𝒜 hd k 0 (zero_mem _) = 0 := by
  rw [ext_iff_val, HomogeneousLocalization.val_zero, Away.val_mk, Localization.mk_zero]

/-- **Fractions with a fixed denominator add in the numerator.** -/
theorem away_mk_add (hd : t ∈ 𝒜 d) (k : ℕ) {p p' : A} (hp : p ∈ 𝒜 (k • d))
    (hp' : p' ∈ 𝒜 (k • d)) :
    Away.mk 𝒜 hd k (p + p') (add_mem hp hp') =
      Away.mk 𝒜 hd k p hp + Away.mk 𝒜 hd k p' hp' := by
  rw [ext_iff_val, HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk,
    Localization.add_mk_self]

/-- **Fractions with a fixed denominator negate in the numerator.** -/
theorem away_mk_neg (hd : t ∈ 𝒜 d) (k : ℕ) {p : A} (hp : p ∈ 𝒜 (k • d)) :
    Away.mk 𝒜 hd k (-p) (neg_mem hp) = -Away.mk 𝒜 hd k p hp := by
  rw [ext_iff_val, HomogeneousLocalization.val_neg, Away.val_mk, Away.val_mk, Localization.neg_mk]

/-- **Multiplying two fractions adds the exponents and multiplies the numerators.** The
membership of the product is an argument rather than built from `SetLike.mul_mem_graded`: at the
graded rings of sections of a sheaf of graded algebras that synthesis is prohibitive, as the
transparency note of `StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing` records. -/
theorem away_mk_mul (hd : t ∈ 𝒜 d) (k l : ℕ) {p p' : A} (hp : p ∈ 𝒜 (k • d))
    (hp' : p' ∈ 𝒜 (l • d)) (hpp : p * p' ∈ 𝒜 ((k + l) • d)) :
    Away.mk 𝒜 hd (k + l) (p * p') hpp =
      Away.mk 𝒜 hd k p hp * Away.mk 𝒜 hd l p' hp' := by
  rw [ext_iff_val, HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk, Away.val_mk,
    Localization.mk_mul]
  exact congrArg (Localization.mk (p * p')) (Subtype.ext (pow_add t k l))

/-- **A degree-zero fraction is a ratio of two elements of degree `d`.** Multiplying numerator
and denominator by `t` turns `a / t⁰` into `(a · t) / t¹`, so a test on the fractions with a
degree-`d` numerator already covers the image of `𝒜 0`. -/
theorem away_mk_zero_eq_mk_one (hd : t ∈ 𝒜 d) {a : A} (ha : a ∈ 𝒜 (0 • d))
    (hat : a * t ∈ 𝒜 (1 • d)) :
    Away.mk 𝒜 hd 0 a ha = Away.mk 𝒜 hd 1 (a * t) hat := by
  rw [ext_iff_val, Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by ring⟩

/-! ### The chart morphism on sections -/

/-- `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` unfolded, with its first two factors
collected into a single `AlgebraicGeometry.Scheme.Hom.resLE`. -/
theorem toBasicOpenOfGlobalSections_eq (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      X.toSpecΓ.resLE (PrimeSpectrum.basicOpen (f t)) (X.basicOpen (f t))
          (X.toSpecΓ_preimage_basicOpen (f t)).ge ≫
        (basicOpenIsoSpecAway (f t)).hom ≫
        Spec.map (CommRingCat.ofHom ((awayLocMap f).comp
          (algebraMap (Away 𝒜 t) (Localization.Away t)))) ≫
        (Proj.basicOpenIsoSpec 𝒜 t hd h0d).inv := rfl

/-- **The chart morphism `X_{f t} ⟶ D₊(t)`, composed with `Proj.basicOpenIsoSpec`, is `Spec` of
`projAwayHom`.** -/
theorem toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd ≫ (Proj.basicOpenIsoSpec 𝒜 t hd h0d).hom =
      (X.basicOpen (f t)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (projAwayHom 𝒜 f)) := by
  have hψ : CommRingCat.ofHom (projAwayHom 𝒜 f) =
      CommRingCat.ofHom ((awayLocMap f).comp (algebraMap (Away 𝒜 t) (Localization.Away t))) ≫
        CommRingCat.ofHom (resLift (f t)) := CommRingCat.ofHom_comp _ _
  rw [toBasicOpenOfGlobalSections_eq 𝒜 f h0d hd, hψ, Spec.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc, toSpecΓ_resLE_basicOpenIsoSpecAway (f t)]

/-- **The chart morphism `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` on global
sections.** Read through `AlgebraicGeometry.Proj.basicOpenIsoAway`, which identifies `(A_t)₀` with
`Γ(Proj 𝒜, D₊(t))`, it is `projAwayHom`: the fraction `p / tᵏ` goes to
`(f p)|_{X_{f t}} · ((f t)|_{X_{f t}})⁻ᵏ`. -/
@[reassoc]
theorem toBasicOpenOfGlobalSections_appTop (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    (Proj.basicOpenIsoAway 𝒜 t hd h0d).hom ≫ (Proj.basicOpen 𝒜 t).topIso.inv ≫
        (Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd).appTop =
      CommRingCat.ofHom (projAwayHom 𝒜 f) ≫ (X.basicOpen (f t)).topIso.inv := by
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 t))).hom ≫
      (Proj.basicOpenIsoAway 𝒜 t hd h0d).hom ≫ (Proj.basicOpen 𝒜 t).topIso.inv =
      (Proj.basicOpenIsoSpec 𝒜 t hd h0d).hom.appTop := by
    rw [Proj.basicOpenIsoAway_hom, Proj.basicOpenIsoSpec_hom]
    exact (Proj.basicOpenToSpec_app_top 𝒜 t).symm
  have h1 : (Proj.basicOpenIsoAway 𝒜 t hd h0d).hom ≫ (Proj.basicOpen 𝒜 t).topIso.inv =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 t))).inv ≫
        (Proj.basicOpenIsoSpec 𝒜 t hd h0d).hom.appTop :=
    ((Iso.inv_comp_eq _).mpr h0.symm).symm
  rw [← Category.assoc, h1, Category.assoc, ← Scheme.Hom.comp_appTop]
  exact ΓSpecIso_inv_appTop_of_eq
    (toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom 𝒜 f h0d hd)

/-! ### Recognizing the chart morphism -/

/-- The chart `D₊(t)` of `Proj 𝒜` is affine for `t` homogeneous of positive degree, so two
morphisms into it agreeing on global sections are equal. -/
theorem ext_of_appTop_basicOpen (h0d : 0 < d) (hd : t ∈ 𝒜 d) {W : Scheme.{u}}
    {c₁ c₂ : W ⟶ (Proj.basicOpen 𝒜 t).toScheme} (h : c₁.appTop = c₂.appTop) : c₁ = c₂ :=
  have : IsAffine (Proj.basicOpen 𝒜 t).toScheme := Proj.isAffineOpen_basicOpen 𝒜 t hd h0d
  AlgebraicGeometry.ext_of_isAffine h

/-- **`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` is the unique morphism
`X_{f t} ⟶ D₊(t)` whose effect on sections is `projAwayHom`.** This is the shape the two
statements about `Proj.fromOfGlobalSections` are discharged through: produce a competing morphism,
compute its effect on sections, and compare ring homomorphisms. -/
theorem eq_toBasicOpenOfGlobalSections (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (c : (X.basicOpen (f t)).toScheme ⟶ (Proj.basicOpen 𝒜 t).toScheme)
    (h : (Proj.basicOpenIsoAway 𝒜 t hd h0d).hom ≫ (Proj.basicOpen 𝒜 t).topIso.inv ≫ c.appTop =
      CommRingCat.ofHom (projAwayHom 𝒜 f) ≫ (X.basicOpen (f t)).topIso.inv) :
    c = Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd := by
  refine ext_of_appTop_basicOpen 𝒜 h0d hd ?_
  rw [← cancel_epi ((Proj.basicOpen 𝒜 t).topIso.inv),
    ← cancel_epi ((Proj.basicOpenIsoAway 𝒜 t hd h0d).hom), h,
    toBasicOpenOfGlobalSections_appTop 𝒜 f h0d hd]

/-- The inclusion of the chart `X_{f t}` composed with
`AlgebraicGeometry.Proj.fromOfGlobalSections` is the chart morphism followed by the inclusion
of `D₊(t)`. -/
theorem ι_comp_fromOfGlobalSections (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    (X.basicOpen (f t)).ι ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd ≫ (Proj.basicOpen 𝒜 t).ι := by
  rw [← Proj.fromOfGlobalSections_resLE 𝒜 f hf h0d hd, Scheme.Hom.resLE_comp_ι]

end Stacks.ProjGlobalSectionsAppTop

end
