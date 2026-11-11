module

public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraizationCartesian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.GrothendieckAlgebraization
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf

/-!
# Algebraization of the formal neighbourhood of a curve

Let `D` be an effective Cartier divisor on a scheme `X`, cutting out `C`, let
`A = lim Γ(Cₙ, 𝒪)` be the ring of formal functions along `C` and `I ⊆ A` an ideal vanishing on `C`
for which `A` is Noetherian and `I`-adically complete, and let `M : ℕ → ℕ` be monotone with
`D(V)^{M n + 1} ⊆ Iⁿ⁺¹ Γ(X, V) + D(V)^{M (n + 1) + 1}` on affine opens `V`. The adic tower
`Xₙ = C_{M n} ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)` is then cartesian
(`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_adicTowerSucc`). This file checks the
remaining hypotheses of Grothendieck's algebraization theorem (Stacks 089A) for the tower with
the restrictions `ℒₙ` of `𝒪_X(-C)`:

* if `X` maps to an affine scheme `Spec R` with `C_{M 0}` proper over `Spec R`, then `X₀` is
  proper over `Spec (A ⧸ I)`: `A` is an `R`-algebra through `Γ(X, 𝒪) ⟶ A`, and
  `Spec (A ⧸ I) ⟶ Spec R` is separated;
* `C ⊆ X₀` is a closed immersion which is a homeomorphism, so `ℒ₀` is ample on `X₀` as soon as
  `𝒪_X(-C)|_C` is ample on `C` (Stacks 09MW);

and applies it: there is a proper `Y ⟶ Spec A` whose adic thickenings are the `Xₙ`, with an ample
invertible module restricting to the `ℒₙ`. This is the algebraization step in the construction of
the formal contraction of a curve with positive conormal bundle needed for Stacks 0D5E.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.globalToFormalNeighborhood`: `Γ(X, 𝒪) ⟶ A`.
* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodToSpec`: `Spec A ⟶ Spec R` for
  `X ⟶ Spec R`.
* `AlgebraicGeometry.Scheme.IdealSheafData.subschemeToAdicTower`: `C ⟶ X₀`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isProper_adicTowerToThickening`: `Xₙ ⟶ Spec (A ⧸ Iⁿ⁺¹)`
  is proper.
* `AlgebraicGeometry.Scheme.IdealSheafData.isHomeomorph_subschemeToAdicTower`: `C ⟶ X₀` is a
  homeomorphism.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_isProper_algebraization`: the algebraization.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- On global sections, `Spec S ⟶ Spec R` is `R ⟶ S`, elementwise. -/
theorem Spec_map_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (a : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv a) = (Scheme.ΓSpecIso S).inv (φ a) := by
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  exact h.symm

/-- On global sections, `Y ⟶ Spec Γ(Y, 𝒪) ⟶ Spec R` is `R ⟶ Γ(Y, 𝒪)`, elementwise. -/
theorem toSpecΓ_comp_Spec_map_appTop_ΓSpecIso_inv {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (a : R) :
    (Y.toSpecΓ ≫ Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv a) = φ a := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Spec_map_appTop_ΓSpecIso_inv,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply]

/-- A morphism `Y ⟶ Spec (A ⧸ Iⁿ⁺¹)` from a ring map `A ⟶ Γ(Y, 𝒪)` killing `Iⁿ⁺¹`. -/
def adicThickeningLift (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) {Y : Scheme.{u}}
    (φ : A →+* Γ(Y, ⊤)) (hφ : I ^ (n + 1) ≤ RingHom.ker φ) : Y ⟶ adicThickening A I n :=
  Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (n + 1)) φ fun _ ha => hφ ha))

/-- `Y ⟶ Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec A` is `Y ⟶ Spec Γ(Y, 𝒪) ⟶ Spec A`. -/
@[reassoc]
theorem adicThickeningLift_ι (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) {Y : Scheme.{u}}
    (φ : A →+* Γ(Y, ⊤)) (hφ : I ^ (n + 1) ≤ RingHom.ker φ) :
    adicThickeningLift A I n φ hφ ≫ adicThickeningι A I n =
      Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [adicThickeningLift, adicThickeningι, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 3

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-! ### The ring of formal functions is an algebra over the global functions -/

/-- Restricting a global function to the `(n + 2)`-nd thickening and then to the `(n + 1)`-st
restricts it to the `(n + 1)`-st. -/
theorem thickeningRestriction_subschemeι_appTop (n : ℕ) (a : Γ(X, ⊤)) :
    thickeningRestriction D n ((D ^ (n + 1 + 1)).subschemeι.appTop a) =
      (D ^ (n + 1)).subschemeι.appTop a := by
  rw [thickeningRestriction_eq_inclusion_appTop D n (pow_succ_le_pow_succ D (Nat.le_succ n))]
  conv_rhs => rw [← inclusion_subschemeι (pow_succ_le_pow_succ D (Nat.le_succ n))]
  rfl

/-- **Restriction of global functions to the formal neighbourhood**: `Γ(X, 𝒪) ⟶ A`, sending a
function to the compatible family of its restrictions to the thickenings `Cₙ`. -/
def globalToFormalNeighborhood : Γ(X, ⊤) →+* formalNeighborhoodRing D :=
  (RingHom.pi fun n => ((D ^ (n + 1)).subschemeι.appTop).hom).codRestrict _ fun a n =>
    thickeningRestriction_subschemeι_appTop D n a

/-- The projection of the restriction of a global function to the `n`-th thickening is its
restriction. -/
@[simp]
theorem formalNeighborhoodProjection_globalToFormalNeighborhood (n : ℕ) (a : Γ(X, ⊤)) :
    formalNeighborhoodProjection D n (globalToFormalNeighborhood D a) =
      (D ^ (n + 1)).subschemeι.appTop a :=
  rfl

/-- For a morphism `X ⟶ Spec R`, the morphism `Spec A ⟶ Spec R` given by
`R ⟶ Γ(X, 𝒪) ⟶ A`. -/
def formalNeighborhoodToSpec {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    Spec (.of (formalNeighborhoodRing D)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom
    ((globalToFormalNeighborhood D).comp ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom))

/-- The thickenings lie over `Spec R` compatibly with `Spec A ⟶ Spec R`. -/
@[reassoc]
theorem thickeningToSpec_formalNeighborhoodToSpec {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    (n : ℕ) :
    thickeningToSpec D n ≫ formalNeighborhoodToSpec D f = (D ^ (n + 1)).subschemeι ≫ f := by
  apply AlgebraicGeometry.ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso R).inv]
  ext a
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply,
    formalNeighborhoodToSpec, Spec_map_appTop_ΓSpecIso_inv, thickeningToSpec_appTop_ΓSpecIso_inv,
    CommRingCat.ofHom_apply, RingHom.comp_apply,
    formalNeighborhoodProjection_globalToFormalNeighborhood]
  rfl

/-! ### Properness of the members of the tower -/

variable (I : Ideal (formalNeighborhoodRing D)) (M : ℕ → ℕ)

/-- `Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec A` is a closed immersion. -/
instance isClosedImmersion_adicThickeningι_formalNeighborhoodRing (n : ℕ) :
    IsClosedImmersion (adicThickeningι (formalNeighborhoodRing D) I n) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- **The members of the adic tower are proper.** If `X` maps to an affine scheme `Spec R` and
the thickening `C_{M n}` is proper over `Spec R`, then
`Xₙ = C_{M n} ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec (A ⧸ Iⁿ⁺¹)` is proper: `Xₙ ⟶ Spec R` is proper,
being a closed subscheme of `C_{M n}`, and `Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec R` is separated. -/
theorem isProper_adicTowerToThickening {R : CommRingCat.{u}} (f : X ⟶ Spec R) (n : ℕ)
    [IsProper ((D ^ (M n + 1)).subschemeι ≫ f)] :
    IsProper (adicTowerToThickening D I M n) := by
  have hc : adicTowerToThickening D I M n ≫
      (adicThickeningι (formalNeighborhoodRing D) I n ≫ formalNeighborhoodToSpec D f) =
      pullback.fst _ _ ≫ ((D ^ (M n + 1)).subschemeι ≫ f) := by
    rw [← thickeningToSpec_formalNeighborhoodToSpec, ← pullback.condition_assoc]
  have : IsProper (adicTowerToThickening D I M n ≫
      (adicThickeningι (formalNeighborhoodRing D) I n ≫ formalNeighborhoodToSpec D f)) := by
    rw [hc]
    infer_instance
  exact IsProper.of_comp _
    (adicThickeningι (formalNeighborhoodRing D) I n ≫ formalNeighborhoodToSpec D f)

/-! ### The curve inside the first member of the tower -/

/-- The restriction `A ⟶ Γ(C, 𝒪)` of formal functions to `C`. -/
def formalNeighborhoodToSubscheme : formalNeighborhoodRing D →+* Γ(D.subscheme, ⊤) :=
  (inclusion (pow_succ_le_self D 0)).appTop.hom.comp (formalNeighborhoodProjection D 0)

variable {I}

/-- An ideal `I ⊆ F₁` of `A` vanishes on `C`. -/
theorem pow_le_ker_formalNeighborhoodToSubscheme (hI : I ≤ formalNeighborhoodFiltration D 1)
    (n : ℕ) : I ^ (n + 1) ≤ RingHom.ker (formalNeighborhoodToSubscheme D) := fun a ha => by
  have h0 : formalNeighborhoodProjection D 0 a = 0 := hI (Ideal.pow_le_self (by omega) ha)
  change (inclusion (pow_succ_le_self D 0)).appTop.hom (formalNeighborhoodProjection D 0 a) = 0
  rw [h0, map_zero]

/-- For an ideal `I ⊆ F₁` of `A`, the morphism `C ⟶ Spec Γ(C, 𝒪) ⟶ Spec (A ⧸ Iⁿ⁺¹)`. -/
def subschemeToAdicThickening (hI : I ≤ formalNeighborhoodFiltration D 1) (n : ℕ) :
    D.subscheme ⟶ adicThickening (formalNeighborhoodRing D) I n :=
  adicThickeningLift _ I n (formalNeighborhoodToSubscheme D)
    (pow_le_ker_formalNeighborhoodToSubscheme D hI n)

/-- `C ⟶ C_N` is `C ⟶ C₀ ⟶ C_N`. -/
theorem inclusion_pow_succ_le_self_eq (N : ℕ) :
    inclusion (pow_succ_le_self D N) =
      inclusion (pow_succ_le_self D 0) ≫ thickeningInclusion D (Nat.zero_le N) := by
  rw [thickeningInclusion, inclusion_comp]

/-- `C ⟶ C_N ⟶ Spec A` is `C ⟶ Spec Γ(C, 𝒪) ⟶ Spec A`. -/
theorem inclusion_thickeningToSpec (N : ℕ) :
    inclusion (pow_succ_le_self D N) ≫ thickeningToSpec D N =
      D.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (formalNeighborhoodToSubscheme D)) := by
  rw [inclusion_pow_succ_le_self_eq D N, Category.assoc, thickeningInclusion_thickeningToSpec,
    thickeningToSpec, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc]
  congr 1
  exact (Spec.map_comp _ _).symm

/-- `C ⟶ Spec (A ⧸ Iⁿ⁺¹)` and `C ⟶ C_N ⟶ Spec A` agree over `Spec A`. -/
theorem inclusion_thickeningToSpec_eq (hI : I ≤ formalNeighborhoodFiltration D 1) (N n : ℕ) :
    inclusion (pow_succ_le_self D N) ≫ thickeningToSpec D N =
      subschemeToAdicThickening D hI n ≫ adicThickeningι (formalNeighborhoodRing D) I n := by
  rw [inclusion_thickeningToSpec, subschemeToAdicThickening, adicThickeningLift_ι]
  rfl

/-- **The curve `C` inside `X₀ = C_{M 0} ×_{Spec A} Spec (A ⧸ I)`**, for an ideal `I ⊆ F₁`. -/
def subschemeToAdicTower (hI : I ≤ formalNeighborhoodFiltration D 1) :
    D.subscheme ⟶ adicTower D I M 0 :=
  pullback.lift (inclusion (pow_succ_le_self D (M 0))) (subschemeToAdicThickening D hI 0)
    (inclusion_thickeningToSpec_eq D hI (M 0) 0)

/-- `C ⟶ X₀ ⟶ C_{M 0}` is the inclusion. -/
@[reassoc (attr := simp)]
theorem subschemeToAdicTower_fst (hI : I ≤ formalNeighborhoodFiltration D 1) :
    subschemeToAdicTower D M hI ≫ adicTowerToThickeningOfD D I M 0 =
      inclusion (pow_succ_le_self D (M 0)) :=
  pullback.lift_fst _ _ _

/-- `C ⟶ X₀` is a closed immersion. -/
instance isClosedImmersion_subschemeToAdicTower (hI : I ≤ formalNeighborhoodFiltration D 1) :
    IsClosedImmersion (subschemeToAdicTower D M hI) := by
  have : IsClosedImmersion (inclusion (pow_succ_le_self D (M 0)) ≫
      (D ^ (M 0 + 1)).subschemeι) := by
    rw [inclusion_subschemeι]
    infer_instance
  have : IsClosedImmersion (inclusion (pow_succ_le_self D (M 0))) :=
    IsClosedImmersion.of_comp_isClosedImmersion _ (D ^ (M 0 + 1)).subschemeι
  have : IsClosedImmersion (subschemeToAdicTower D M hI ≫ adicTowerToThickeningOfD D I M 0) := by
    rw [subschemeToAdicTower_fst]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (adicTowerToThickeningOfD D I M 0)

/-- `C ⟶ X₀` is surjective: `X₀` lies in `C_{M 0}`, which has the same points as `C`. -/
theorem surjective_subschemeToAdicTower (hI : I ≤ formalNeighborhoodFiltration D 1) :
    Function.Surjective (subschemeToAdicTower D M hI) := by
  intro p
  have hp : (D ^ (M 0 + 1)).subschemeι (adicTowerToThickeningOfD D I M 0 p) ∈
      Set.range D.subschemeι := by
    rw [range_subschemeι, ← support_pow_succ D (M 0), ← range_subschemeι]
    exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := hp
  refine ⟨c, (adicTowerToThickeningOfD D I M 0).isClosedEmbedding.injective
    ((D ^ (M 0 + 1)).subschemeι.isClosedEmbedding.injective ?_)⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, subschemeToAdicTower_fst_assoc,
    inclusion_subschemeι, hc]

/-- `C ⟶ X₀` is a homeomorphism. -/
theorem isHomeomorph_subschemeToAdicTower (hI : I ≤ formalNeighborhoodFiltration D 1) :
    IsHomeomorph (subschemeToAdicTower D M hI).base :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(subschemeToAdicTower D M hI).isClosedEmbedding.isEmbedding,
      surjective_subschemeToAdicTower D M hI⟩

/-! ### The invertible modules on the tower -/

variable (I)

open Stacks.Divisors in
/-- `𝒪_X(-C)` is invertible, in the spelling `Stacks.Ample.IsInvertibleModule` of the ampleness
theory: `Stacks.Divisors.isInvertible_negativeTwist`, found by instance search. -/
instance isInvertibleModule_negativeTwist' [IsEffectiveCartierDivisor D] :
    Stacks.Ample.IsInvertibleModule X (negativeTwist' D) :=
  isInvertible_negativeTwist D

/-- The morphism `Xₙ ⟶ C_{M n} ⟶ X` from the `n`-th member of the adic tower. -/
abbrev adicTowerToScheme (n : ℕ) : adicTower D I M n ⟶ X :=
  adicTowerToThickeningOfD D I M n ≫ (D ^ (M n + 1)).subschemeι

variable {M}

/-- The transition maps of the adic tower lie over `X`. -/
@[reassoc]
theorem adicTowerSucc_adicTowerToScheme (hM : Monotone M) (n : ℕ) :
    adicTowerSucc D I hM n ≫ adicTowerToScheme D I M (n + 1) = adicTowerToScheme D I M n := by
  rw [adicTowerToScheme, adicTowerSucc_adicTowerToThickeningOfD_assoc, thickeningInclusion,
    inclusion_subschemeι]

variable (M)

open Stacks.Divisors in
/-- The restriction `ℒₙ` of `𝒪_X(-C)` to the `n`-th member of the adic tower. -/
abbrev adicTowerModule (n : ℕ) : (adicTower D I M n).Modules :=
  (Scheme.Modules.pullback (adicTowerToScheme D I M n)).obj (negativeTwist' D)

open Stacks.Divisors in
/-- `ℒₙ` is invertible. (Instance search does not find
`Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback` at `negativeTwist'`.) -/
instance isInvertibleModule_adicTowerModule [IsEffectiveCartierDivisor D] (n : ℕ) :
    Stacks.Ample.IsInvertibleModule _ (adicTowerModule D I M n) :=
  Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _

open Stacks.Divisors in
/-- The conormal sheaf `𝒪_X(-C)|_C` of `C`. -/
abbrev conormalModule : D.subscheme.Modules :=
  (Scheme.Modules.pullback D.subschemeι).obj (negativeTwist' D)

open Stacks.Divisors in
/-- The conormal sheaf `𝒪_X(-C)|_C` is invertible. -/
instance isInvertibleModule_conormalModule [IsEffectiveCartierDivisor D] :
    Stacks.Ample.IsInvertibleModule _ (conormalModule D) :=
  Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _

variable {M}

open Stacks.Divisors in
/-- The identifications `iₙ^* ℒₙ₊₁ ≅ ℒₙ` of the restrictions of `𝒪_X(-C)` along the tower. -/
def adicTowerModuleIso (hM : Monotone M) (n : ℕ) :
    (Scheme.Modules.pullback (adicTowerSucc D I hM n)).obj (adicTowerModule D I M (n + 1)) ≅
      adicTowerModule D I M n :=
  (Scheme.Modules.pullbackComp _ _).app (negativeTwist' D) ≪≫
    (Scheme.Modules.pullbackCongr (adicTowerSucc_adicTowerToScheme D I hM n)).app _

variable (M)

/-- `C ⟶ X₀ ⟶ X` is the inclusion of `C`. -/
theorem subschemeToAdicTower_adicTowerToScheme (hI : I ≤ formalNeighborhoodFiltration D 1) :
    subschemeToAdicTower D M hI ≫ adicTowerToScheme D I M 0 = D.subschemeι := by
  rw [adicTowerToScheme, subschemeToAdicTower_fst_assoc, inclusion_subschemeι]

open Stacks.Ample Stacks.Divisors in
/-- **`ℒ₀` is ample on `X₀` when `𝒪_X(-C)|_C` is ample on `C`** ([Stacks, Tag 09MW]): `C ⟶ X₀` is
a closed immersion and a homeomorphism, along which `ℒ₀` restricts to `𝒪_X(-C)|_C`. -/
theorem isAmple_adicTowerModule_zero [IsEffectiveCartierDivisor D]
    (hI : I ≤ formalNeighborhoodFiltration D 1)
    (hC : IsAmple D.subscheme (conormalModule D)) :
    IsAmple (adicTower D I M 0) (adicTowerModule D I M 0) := by
  have e : (Scheme.Modules.pullback (subschemeToAdicTower D M hI)).obj
      (adicTowerModule D I M 0) ≅
        conormalModule D :=
    (Scheme.Modules.pullbackComp _ _).app (negativeTwist' D) ≪≫
      (Scheme.Modules.pullbackCongr (subschemeToAdicTower_adicTowerToScheme D I M hI)).app _
  refine (Stacks.AmpleThickeningAscent.isAmple_modulePullback_iff (subschemeToAdicTower D M hI)
    (isHomeomorph_subschemeToAdicTower D M hI) (adicTowerModule D I M 0)).mp ?_
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr hC

/-! ### Algebraization -/

open Stacks.Ample Stacks.Divisors in
/-- **Algebraization of the formal neighbourhood of a curve** (Stacks 089A applied to the adic
tower). Let `D` be an effective Cartier divisor on a scheme `X` proper over an affine scheme
`Spec R`, with subscheme `C` and ring of formal functions `A = lim Γ(Cₙ, 𝒪)`. Let `I ⊆ A` be an
ideal vanishing on `C` with `A` Noetherian and `I`-adically complete, and `M` monotone with
`D(V)^{M n + 1} ⊆ Iⁿ⁺¹ Γ(X, V) + D(V)^{M (n + 1) + 1}` on every member `V` of an affine open cover
of `X` (on the members missing `C` this is automatic:
`AlgebraicGeometry.Scheme.IdealSheafData.pow_le_comap_map_formalNeighborhoodChart_of_ideal_eq_top`).
If `𝒪_X(-C)|_C` is ample, there are a proper `Y ⟶ Spec A`, an ample invertible `𝒪_Y`-module `𝒩`
and morphisms `kₙ : Xₙ ⟶ Y` from the adic tower `Xₙ = C_{M n} ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)`, compatible with the
transition maps, exhibiting each `Xₙ` as `Y ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)`, with
`𝒩|_{Xₙ} ≅ 𝒪_X(-C)|_{Xₙ}`
compatibly with the transition maps. -/
theorem exists_isProper_algebraization [IsEffectiveCartierDivisor D] {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [IsProper f] [IsNoetherianRing (formalNeighborhoodRing D)]
    [IsAdicComplete I (formalNeighborhoodRing D)] (hI : I ≤ formalNeighborhoodFiltration D 1)
    (hM : Monotone M) {ι : Type*} (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤)
    (hcof : ∀ (n : ℕ) (i : ι), D.ideal (U i) ^ (M n + 1) ≤
      Ideal.comap (Ideal.Quotient.mk (D.ideal (U i) ^ (M (n + 1) + 1)))
        (Ideal.map (formalNeighborhoodChart D (U i) (M (n + 1))) (I ^ (n + 1))))
    (hC : IsAmple D.subscheme (conormalModule D)) :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of (formalNeighborhoodRing D))), IsProper fY ∧
      ∃ (N : Y.Modules) (hN : IsInvertibleModule Y N), @IsAmple Y N hN ∧
        ∃ (k : ∀ n, adicTower D I M n ⟶ Y) (hk : ∀ n, adicTowerSucc D I hM n ≫ k (n + 1) = k n),
          (∀ n, IsPullback (k n) (adicTowerToThickening D I M n) fY
            (adicThickeningι (formalNeighborhoodRing D) I n)) ∧
          ∃ e : ∀ n, adicTowerModule D I M n ≅ (Scheme.Modules.pullback (k n)).obj N,
            ∀ n, (adicTowerModuleIso D I hM n).hom ≫ (e n).hom =
              (Scheme.Modules.pullback (adicTowerSucc D I hM n)).map (e (n + 1)).hom ≫
                (Scheme.Modules.pullbackComp (adicTowerSucc D I hM n) (k (n + 1))).hom.app N ≫
                  (Scheme.Modules.pullbackCongr (hk n)).hom.app N := by
  have : IsProper ((D ^ (M 0 + 1)).subschemeι ≫ f) := inferInstance
  exact Stacks.GrothendieckAlgebraization.exists_isProper_isAmple_algebraization
    (formalNeighborhoodRing D) I (adicTowerToThickening D I M) (adicTowerSucc D I hM)
    (isPullback_adicTowerSucc D I hM U hU hcof) (adicTowerModule D I M)
    (isInvertibleModule_adicTowerModule D I M)
    (adicTowerModuleIso D I hM) (isProper_adicTowerToThickening D I M f 0)
    (isAmple_adicTowerModule_zero D I M hI hC)

variable {D}

open Stacks.Ample Stacks.Divisors in
/-- **Algebraization of the formal neighbourhood of a curve with positive conormal bundle.** Let
`C ⊆ X` be an effective Cartier divisor on a scheme proper over an affine scheme, with positive
conormal bundle `L = 𝒪_X(-C)|_C` (in the sense of
`AlgebraicGeometry.Scheme.IdealSheafData.IsPositiveConormal`), `L` ample and `L^{N+1}` globally
generated. Then the `𝔪`-adic tower `Xₙ = C_{(N+1)(n+1)} ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)` of the complete
local ring `A = lim Γ(Cₙ, 𝒪)` algebraizes: there are a proper `Y ⟶ Spec A`, an ample invertible
`𝒩` on `Y` and compatible `kₙ : Xₙ ⟶ Y` exhibiting `Xₙ = Y ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)`, with
`𝒩|_{Xₙ} ≅ 𝒪_X(-C)|_{Xₙ}` compatibly with the transition maps. -/
theorem IsPositiveConormal.exists_isProper_algebraization [IsEffectiveCartierDivisor D] {c : ℕ}
    (hD : IsPositiveConormal D c) {N : ℕ}
    (hgg : ∀ V : X.affineOpens, D.ideal V ^ (N + 1) ≤
      Ideal.span (chartGlobalSymbols D V N) ⊔ D.ideal V ^ (N + 2))
    {R : CommRingCat.{u}} (f : X ⟶ Spec R) [IsProper f]
    (hC : IsAmple D.subscheme (conormalModule D)) :
    letI := hD.isLocalRing
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of (formalNeighborhoodRing D))), IsProper fY ∧
      ∃ (𝒩 : Y.Modules) (h𝒩 : IsInvertibleModule Y 𝒩), @IsAmple Y 𝒩 h𝒩 ∧
        ∃ (k : ∀ n, adicTower D (IsLocalRing.maximalIdeal _) (positiveConormalTowerIndex N) n ⟶ Y)
          (hk : ∀ n, adicTowerSucc D _ (monotone_positiveConormalTowerIndex N) n ≫ k (n + 1) =
            k n),
          (∀ n, IsPullback (k n)
            (adicTowerToThickening D (IsLocalRing.maximalIdeal _) (positiveConormalTowerIndex N) n)
            fY (adicThickeningι (formalNeighborhoodRing D) (IsLocalRing.maximalIdeal _) n)) ∧
          ∃ e : ∀ n, adicTowerModule D (IsLocalRing.maximalIdeal _) (positiveConormalTowerIndex N) n
              ≅ (Scheme.Modules.pullback (k n)).obj 𝒩,
            ∀ n, (adicTowerModuleIso D _ (monotone_positiveConormalTowerIndex N) n).hom ≫
                (e n).hom =
              (Scheme.Modules.pullback
                  (adicTowerSucc D _ (monotone_positiveConormalTowerIndex N) n)).map
                  (e (n + 1)).hom ≫
                (Scheme.Modules.pullbackComp
                  (adicTowerSucc D _ (monotone_positiveConormalTowerIndex N) n)
                  (k (n + 1))).hom.app 𝒩 ≫
                  (Scheme.Modules.pullbackCongr (hk n)).hom.app 𝒩 := by
  let _ := hD.isLocalRing
  have h := hD.isNoetherianCompleteLocalRing
  have : IsNoetherianRing (formalNeighborhoodRing D) := h.isNoetherian
  have : IsAdicComplete (IsLocalRing.maximalIdeal (formalNeighborhoodRing D))
      (formalNeighborhoodRing D) := h.isComplete
  exact Scheme.IdealSheafData.exists_isProper_algebraization D _ (positiveConormalTowerIndex N) f
    hD.maximalIdeal_eq.le (monotone_positiveConormalTowerIndex N)
    (fun V : X.affineOpens => V) (iSup_affineOpens_eq_top X)
    (hD.pow_le_comap_map_positiveConormalTowerIndex hgg) hC

end Scheme.IdealSheafData

end AlgebraicGeometry

end
