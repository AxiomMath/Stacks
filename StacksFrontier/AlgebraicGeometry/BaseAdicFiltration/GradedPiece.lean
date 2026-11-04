module

public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.IdealPowerDirectSum
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.RingTheory.Flat.MaximalIdealGradedPiece
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The adic filtration of a flat family over a local base, and its graded pieces

Let `A` be a commutative ring, `I ⊆ A` an ideal, `U` a scheme and `p : U ⟶ Spec A` a morphism.
Every quasi-coherent `𝒪_U`-module `ℱ` carries the `I`-adic filtration

```
… ⊆ I² ℱ ⊆ I ℱ ⊆ ℱ
```

by the subsheaves `Iⁱ ℱ = Iⁱ 𝒪_U · ℱ`.  This file identifies its graded pieces when `ℱ` is flat
over `A`, `A` is Noetherian and `I` is maximal: writing `κ = A/I` and `k = dim_κ Iⁿ/Iⁿ⁺¹`,

```
Iⁿ ℱ / Iⁿ⁺¹ ℱ  ≅  ⨁_{i < k} ℱ/Iℱ .
```

The graded piece is `Iⁿ (ℱ/Iⁿ⁺¹ℱ)`, the `n`-th step of the filtration of the quotient
`ℱ/Iⁿ⁺¹ℱ`, rather than `Iⁿℱ/Iⁿ⁺¹ℱ` presented as a cokernel; the two agree, and the former makes
the filtration sequence a kernel-cokernel sequence of a subsheaf rather than a composite of two
cokernels.

The right-hand side is `k` copies of `ℱ/Iℱ` rather than `(ℱ/Iℱ) ⊗_κ Iⁿ/Iⁿ⁺¹`, which is what the
source writes.  The two differ only by a choice of a `κ`-basis of `Iⁿ/Iⁿ⁺¹`, isolated
independently of the module in `Stacks.Flatness.exists_pi_linearEquiv_gradedPiece`; once it is
made, `(ℱ/Iℱ) ⊗_κ Iⁿ/Iⁿ⁺¹` *is* `⨁_{i<k} ℱ/Iℱ`.  The biproduct form is the one a consumer wants:
an additive functor — the direct image, and each of its right derived functors — carries it to
the biproduct of the images, so the vanishing of `R¹f_*` on the graded pieces reduces to its
vanishing on `ℱ/Iℱ`.  This is the presentation
`Stacks.Algebraization.exists_isoDirectSum_idealPowerSub` uses for the analogous decomposition in
[Stacks, Tag 0EJU].

The hypotheses are Noetherian local, not Artinian local: the filtration argument of
[Stacks, Tag 0E3X] is run over an Artinian local base, where it terminates because `𝔪` is
nilpotent, but nothing in the identification of a single graded piece uses nilpotence.

Flatness enters exactly once, through
`Stacks.Flatness.exists_lift_basis_smul_of_flat_tower`, which needs the stalk `ℱ_x` to be a flat
`A`-module for the `A`-action through `𝒪_{U,x}`.  That is what
`Stacks.BaseAdicFiltration.FlatStalks` records, and for `ℱ = 𝒪_U` it is a consequence of
flatness of `p` (`Stacks.BaseAdicFiltration.flat_stalk_of_flat`).

## Main definitions

* `Stacks.BaseAdicFiltration.adicFiltration`, `adicQuotient`, `adicProj` — the subsheaf `Iⁿ ℱ`,
  the quotient `ℱ/Iⁿℱ` and the projection onto it.
* `Stacks.BaseAdicFiltration.specialFibre` — the quotient `ℱ/Iℱ`, which for `ℱ = 𝒪_U` and
  `I = 𝔪` is the structure sheaf of the special fibre.
* `Stacks.BaseAdicFiltration.gradedPiece` — the graded piece `Iⁿ(ℱ/Iⁿ⁺¹ℱ)`.
* `Stacks.BaseAdicFiltration.adicFiltration_eq_bot` and
  `exists_adicFiltration_eq_bot_of_isArtinianRing` — where the filtration reaches zero, which
  over an Artinian local base is the only use of nilpotence of `𝔪`.
* `Stacks.BaseAdicFiltration.specialFibreIso` — the identification
  `(ℱ/Iⁿ⁺¹ℱ)/I(ℱ/Iⁿ⁺¹ℱ) ≅ ℱ/Iℱ`, with the compatibility of the projections out of `ℱ`.
* `Stacks.BaseAdicFiltration.FlatStalks` — the flatness hypothesis.
* `Stacks.BaseAdicFiltration.gradedDesc` — the comparison morphism
  `⨁_{i<k} ℱ/Iℱ ⟶ Iⁿ(ℱ/Iⁿ⁺¹ℱ)`, whose `i`-th component is multiplication by `a i ∈ Iⁿ`.

## Main results

* `Stacks.BaseAdicFiltration.ker_stalk_adicProj` and `range_stalk_adicFiltration_ι` — the stalk
  of `ℱ ⟶ ℱ/Iⁿℱ` is surjective with kernel `(I𝒪_{U,x})ⁿ ℱ_x`, and the stalk of `Iⁿℱ ⟶ ℱ` has
  that same image.
* `Stacks.BaseAdicFiltration.bijective_stalk_gradedDesc` — **the comparison morphism is bijective
  on every stalk**, which is where flatness is used.
* `Stacks.BaseAdicFiltration.exists_isIso_gradedDesc` — **the graded piece identified, with the
  morphism kept**.
* `Stacks.BaseAdicFiltration.exists_isoDirectSum_gradedPiece` — the same, forgetting the
  morphism.
* `Stacks.BaseAdicFiltration.exists_isoDirectSum_gradedPiece_of_isArtinianRing` — the form
  [Stacks, Tag 0E3X] uses, over an Artinian local base.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Algebraization Stacks.ModuleSkyscraper
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.BaseAdicFiltration

attribute [local instance] hasFiniteBiproducts_schemeModules

variable {A : Type u} [CommRing A] {U : Scheme.{u}}

/-! ### The filtration, its quotients and its graded pieces -/

section Defs

variable (p : U ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ) (F : U.Modules)

/-- The `n`-th step `Iⁿ ℱ` of the `I`-adic filtration of a sheaf of modules, for an ideal `I` of
the base ring of `p : U ⟶ Spec A`. -/
@[ega "0 15.2.1" "special case"]
abbrev adicFiltration : F.Submodule :=
  idealPowerMultiple (baseIdeal p I) n F

/-- The quotient `ℱ/Iⁿℱ`. -/
abbrev adicQuotient : U.Modules :=
  idealPowerQuotient (baseIdeal p I) n F

/-- The projection `ℱ ⟶ ℱ/Iⁿℱ`. -/
abbrev adicProj : F ⟶ adicQuotient p I n F :=
  cokernel.π (C := U.Modules) (adicFiltration p I n F).ι

/-- The quotient `ℱ/Iℱ`.  For `ℱ = 𝒪_U` and `I` the maximal ideal of a local base this is the
structure sheaf of the special fibre, transported to `U`; the two schemes have the same
underlying space when `I` is nilpotent. -/
@[ega "0 15.2.1" "special case"]
abbrev specialFibre : U.Modules :=
  adicQuotient p I 1 F

/-- **The `n`-th graded piece `Iⁿ(ℱ/Iⁿ⁺¹ℱ)` of the `I`-adic filtration**, presented as the
`n`-th step of the filtration of `ℱ/Iⁿ⁺¹ℱ` rather than as the subquotient `Iⁿℱ/Iⁿ⁺¹ℱ`. -/
abbrev gradedPiece : (adicQuotient p I (n + 1) F).Submodule :=
  adicFiltration p I n (adicQuotient p I (n + 1) F)

/-- The filtration is decreasing. -/
theorem adicFiltration_antitone {m n : ℕ} (h : m ≤ n) :
    adicFiltration p I n F ≤ adicFiltration p I m F :=
  idealPowerMultiple_antitone (baseIdeal p I) F h

/-- `Iⁿ⁺¹` annihilates `ℱ/Iⁿ⁺¹ℱ`, which is the hypothesis the multiplication morphisms out of
`ℱ/Iⁿ⁺¹ℱ` are built under. -/
theorem adicFiltration_adicQuotient_eq_bot [F.IsQuasicoherent] :
    adicFiltration p I (n + 1) (adicQuotient p I (n + 1) F) = ⊥ :=
  idealPowerMultiple_idealPowerQuotient_eq_bot (baseIdeal p I) (n + 1) F

end Defs

/-! ### Where the filtration terminates -/

section Terminates

variable (p : U ⟶ Spec (CommRingCat.of A)) (F : U.Modules)

/-- **The filtration terminates where the ideal does.** If `Iⁿ = 0` then `Iⁿℱ = 0`.

The ideal of `I 𝒪_U` on an affine open is generated by the image of `I`
(`Stacks.BaseAdicFiltration.baseIdeal_ideal`), so its `n`-th power is generated by the image of
`Iⁿ`; the affine-local universal property of the subsheaf then gives the statement with no
hypothesis on `ℱ`. -/
theorem adicFiltration_eq_bot {I : Ideal A} {n : ℕ} (hI : I ^ n = ⊥) :
    adicFiltration p I n F = ⊥ := by
  refine le_antisymm ((idealPowerMultiple_le_iff _ _ _ _).2 fun V => ?_) bot_le
  have hzero : (baseIdeal p I).ideal V ^ n = ⊥ := by
    rw [baseIdeal_ideal, ← Ideal.map_pow, hI, Ideal.map_bot]
  rw [hzero, Submodule.bot_smul]
  exact bot_le

/-- **Over an Artinian local base the `𝔪`-adic filtration reaches zero.** The maximal ideal of an
Artinian local ring is nilpotent, so `𝔪ⁿℱ = 0` for some `n`.

This is the leftmost term of the filtration

```
0 = 𝔪_A^n 𝒪_U ⊆ 𝔪_A^{n-1} 𝒪_U ⊆ … ⊆ 𝔪_A 𝒪_U ⊆ 𝒪_U
```

displayed in [Stacks, Tag 0E3X], and it is the only place nilpotence of `𝔪` is used: it is what
makes the induction up the filtration finite, the graded pieces themselves needing only that `A`
be Noetherian and `𝔪` maximal. -/
theorem exists_adicFiltration_eq_bot_of_isArtinianRing [IsArtinianRing A] [IsLocalRing A] :
    ∃ n : ℕ, adicFiltration p (IsLocalRing.maximalIdeal A) n F = ⊥ := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).1 ‹IsArtinianRing A›
  exact ⟨n, adicFiltration_eq_bot p F hn⟩

end Terminates

/-! ### The special fibre as a quotient of a quotient

`Stacks.Algebraization.idealPowerDesc` produces a morphism out of a direct sum of copies of
`𝒩` for any `𝒩` identified with `(ℱ/Iⁿ⁺¹ℱ)/I(ℱ/Iⁿ⁺¹ℱ)`.  Dividing by `Iⁿ⁺¹` first is invisible
modulo `I`, so that double quotient is `ℱ/Iℱ`; this section records the identification and the
compatibility of the projections that the stalk computation consumes.
-/

section SpecialFibreIso

variable (p : U ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ) (F : U.Modules)
  [F.IsQuasicoherent]

/-- **The special fibre read off the `(n+1)`-st quotient.** The `I`-quotient of `ℱ/Iⁿ⁺¹ℱ` is
`ℱ/Iℱ`, and under that identification the two projections out of `ℱ` compose to the projection
`ℱ ⟶ ℱ/Iℱ`.

This is `Stacks.Algebraization.doubleIdealPowerQuotientIso` for `Iⁿ⁺¹ ⊆ I`. -/
def specialFibreIso :
    {e : adicQuotient p I 1 (adicQuotient p I (n + 1) F) ≅ specialFibre p I F //
      adicProj p I (n + 1) F ≫ adicProj p I 1 (adicQuotient p I (n + 1) F) ≫ e.hom =
        adicProj p I 1 F} := by
  haveI : IsIso (idealPowerQuotientMap (baseIdeal p I) (baseIdeal p I) 1 1 le_rfl
      (adicProj p I 1 F)) :=
    isIso_idealPowerQuotientMap_cokernel_π (baseIdeal p I) (baseIdeal p I) 1 1 le_rfl F
  exact doubleIdealPowerQuotientIso (baseIdeal p I) (baseIdeal p I) 1 (n + 1)
    (Scheme.IdealSheafData.pow_le_pow_of_le (baseIdeal p I) (Nat.le_add_left 1 n))
    (adicProj p I 1 F) (idealPowerMultiple_idealPowerQuotient_eq_bot (baseIdeal p I) 1 F)

end SpecialFibreIso

/-! ### The filtration on stalks -/

section Stalks

variable (p : U ⟶ Spec (CommRingCat.of A)) (F : U.Modules) (x : U)

/-- The `A`-module structure on the stalk of a sheaf of modules, obtained from the module
structure over `𝒪_{U,x}` by restriction along `Stacks.BaseAdicFiltration.stalkAlgebra`. -/
@[instance_reducible]
def stalkBaseModule : Module A ((modulesStalkFunctor U x).obj F) :=
  letI := stalkAlgebra p x
  Module.compHom _ (algebraMap A (U.presheaf.stalk x))

/-- The scalar action of `A` on a stalk is the action of its image in the local ring. -/
theorem stalkBaseModule_smul (a : A) (m : (modulesStalkFunctor U x).obj F) :
    letI := stalkAlgebra p x
    letI := stalkBaseModule p F x
    a • m = algebraMap A (U.presheaf.stalk x) a • m :=
  rfl

/-- The `A`-action on a stalk is compatible with the action of the local ring. -/
instance isScalarTower_stalk :
    letI := stalkAlgebra p x
    letI := stalkBaseModule p F x
    IsScalarTower A (U.presheaf.stalk x) ((modulesStalkFunctor U x).obj F) :=
  letI := stalkAlgebra p x
  letI := stalkBaseModule p F x
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- **The flatness hypothesis.** Every stalk of `ℱ` is a flat `A`-module for the action through
the local ring.  For `ℱ = 𝒪_U` this holds whenever `p` is flat, by
`Stacks.BaseAdicFiltration.flat_stalk_of_flat`. -/
def FlatStalks : Prop :=
  ∀ x : U,
    letI := stalkBaseModule p F x
    Module.Flat A ((modulesStalkFunctor U x).obj F)

variable (I : Ideal A) (n : ℕ)

/-- **The stalk of `Iⁿ ℱ`.** The image of the stalk of the inclusion `Iⁿℱ ⟶ ℱ` is
`(I 𝒪_{U,x})ⁿ ℱ_x`. -/
theorem range_stalk_adicFiltration_ι [F.IsQuasicoherent] :
    letI := stalkAlgebra p x
    LinearMap.range ((modulesStalkFunctor U x).map (C := U.Modules)
        (adicFiltration p I n F).ι).hom =
      (I.map (algebraMap A (U.presheaf.stalk x))) ^ n •
        (⊤ : Submodule (U.presheaf.stalk x) ((modulesStalkFunctor U x).obj F)) := by
  let := stalkAlgebra p x
  rw [stalk_idealPowerMultiple (baseIdeal p I) n F x, stalk_baseIdeal]

/-- The stalk of the inclusion `Iⁿℱ ⟶ ℱ` is injective. -/
theorem injective_stalk_adicFiltration_ι :
    Function.Injective ((modulesStalkFunctor U x).map (C := U.Modules)
      (adicFiltration p I n F).ι).hom := by
  have : Mono (C := U.Modules) (adicFiltration p I n F).ι :=
    inferInstanceAs (Mono (C := _root_.SheafOfModules U.ringCatSheaf)
      (adicFiltration p I n F).ι)
  exact (ModuleCat.mono_iff_injective _).mp (Functor.map_mono _ _)

/-- The stalk of the projection `ℱ ⟶ ℱ/Iⁿℱ` is surjective. -/
theorem surjective_stalk_adicProj :
    Function.Surjective ((modulesStalkFunctor U x).map (C := U.Modules)
      (adicProj p I n F)).hom :=
  surjective_stalk_cokernel_π (adicFiltration p I n F) x

/-- **The kernel of the stalk of `ℱ ⟶ ℱ/Iⁿℱ`** is `(I 𝒪_{U,x})ⁿ ℱ_x`. -/
theorem ker_stalk_adicProj [F.IsQuasicoherent] :
    letI := stalkAlgebra p x
    LinearMap.ker ((modulesStalkFunctor U x).map (C := U.Modules) (adicProj p I n F)).hom =
      (I.map (algebraMap A (U.presheaf.stalk x))) ^ n •
        (⊤ : Submodule (U.presheaf.stalk x) ((modulesStalkFunctor U x).obj F)) := by
  let := stalkAlgebra p x
  rw [← range_stalk_submodule_ι_eq_ker_stalk_cokernel_π]
  exact range_stalk_adicFiltration_ι p F x I n

/-- The stalk of `ℱ ⟶ ℱ/Iⁿℱ` carries `(I𝒪_{U,x})ᵐ ℱ_x` onto `(I𝒪_{U,x})ᵐ (ℱ/Iⁿℱ)_x`: a
surjection carries an ideal multiple onto the ideal multiple of the image. -/
theorem map_stalk_adicProj_smul_top (m : ℕ) :
    letI := stalkAlgebra p x
    Submodule.map ((modulesStalkFunctor U x).map (C := U.Modules) (adicProj p I n F)).hom
        ((I.map (algebraMap A (U.presheaf.stalk x))) ^ m •
          (⊤ : Submodule (U.presheaf.stalk x) ((modulesStalkFunctor U x).obj F))) =
      (I.map (algebraMap A (U.presheaf.stalk x))) ^ m •
        (⊤ : Submodule (U.presheaf.stalk x)
          ((modulesStalkFunctor U x).obj (adicQuotient p I n F))) := by
  let := stalkAlgebra p x
  rw [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.2 (surjective_stalk_adicProj p F x I n)]

end Stalks

/-! ### The comparison morphism -/

section Desc

variable (p : U ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ) (F : U.Modules)
  [F.IsQuasicoherent]

/-- **The comparison morphism `⨁_{i<k} ℱ/Iℱ ⟶ Iⁿ(ℱ/Iⁿ⁺¹ℱ)`.** Its `i`-th component is
multiplication by `a i ∈ Iⁿ`: that carries `ℱ/Iⁿ⁺¹ℱ` into the `n`-th step of its own filtration
and kills the first step, because `Iⁿ⁺¹` annihilates `ℱ/Iⁿ⁺¹ℱ`, so it factors through
`(ℱ/Iⁿ⁺¹ℱ)/I(ℱ/Iⁿ⁺¹ℱ)`, which `e` identifies with `ℱ/Iℱ`.

This is `Stacks.Algebraization.idealPowerDesc` for the global functions on `U` determined by the
`a i`. -/
def gradedDesc {k : ℕ} (a : Fin k → A) (ha : ∀ i, a i ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) F) ≅ specialFibre p I F) :
    (⨁ fun _ : Fin k => specialFibre p I F) ⟶ (gradedPiece p I n F).toSheafOfModules :=
  idealPowerDesc (adicQuotient p I (n + 1) F) n
    (adicFiltration_adicQuotient_eq_bot p I n F)
    (fun i V => restrictMemIdealPow_baseScalarMap p n (ha i) V) e

/-- **The comparison is injective on a stalk.**  Every projection of a stalk section `u` of the
direct sum lifts along `ℱ_x ⟶ (ℱ/Iℱ)_x` to some `mᵢ`; if the comparison kills `u` then
`∑ aᵢ mᵢ` lies in `(I𝒪_{U,x})ⁿ⁺¹ℱ_x`, so flatness of `ℱ_x` puts every `mᵢ` in `(I𝒪_{U,x})ℱ_x`
and each projection of `u` vanishes. -/
private theorem injective_stalk_gradedDesc
    [IsNoetherianRing A] [I.IsMaximal] (x : U)
    (hflatx : letI := stalkBaseModule p F x
      Module.Flat A ((modulesStalkFunctor U x).obj F))
    {k : ℕ} (e₀ : (↥(I ^ n) ⧸ (I • (⊤ : Submodule A ↥(I ^ n)))) ≃ₗ[A] (Fin k → (A ⧸ I)))
    (rep : Fin k → ↥(I ^ n))
    (hrep : ∀ i, e₀.symm (Pi.single i (1 : A ⧸ I)) = Submodule.Quotient.mk (rep i))
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) F) ≅ specialFibre p I F)
    (qH : ((modulesStalkFunctor U x).obj F) →ₗ[U.presheaf.stalk x]
      ((modulesStalkFunctor U x).obj (adicQuotient p I (n + 1) F)))
    (tH : ((modulesStalkFunctor U x).obj (adicQuotient p I (n + 1) F)) →ₗ[U.presheaf.stalk x]
      ((modulesStalkFunctor U x).obj (specialFibre p I F)))
    (rH : ((modulesStalkFunctor U x).obj F) →ₗ[U.presheaf.stalk x]
      ((modulesStalkFunctor U x).obj (specialFibre p I F)))
    (iH : ((modulesStalkFunctor U x).obj ((gradedPiece p I n F).toSheafOfModules))
      →ₗ[U.presheaf.stalk x] ((modulesStalkFunctor U x).obj (adicQuotient p I (n + 1) F)))
    (hcompat : ∀ m, tH (qH m) = rH m)
    (hvalue : letI := stalkAlgebra p x
      ∀ w : Fin k → ((modulesStalkFunctor U x).obj (adicQuotient p I (n + 1) F)),
      iH (((modulesStalkFunctor U x).map (C := U.Modules)
            (gradedDesc p I n F (fun i => (rep i : A)) (fun i => (rep i).2) e)).hom
          (stalkOfTuple x (specialFibre p I F) fun i => tH (w i))) =
        ∑ i, algebraMap A (U.presheaf.stalk x) ((rep i : A)) • w i)
    (hsum : letI := stalkAlgebra p x
      letI := stalkBaseModule p F x
      ∀ m : Fin k → ((modulesStalkFunctor U x).obj F),
      qH (∑ i, ((rep i : A)) • m i) =
        ∑ i, algebraMap A (U.presheaf.stalk x) ((rep i : A)) • qH (m i))
    (hkerq : letI := stalkAlgebra p x
      LinearMap.ker qH =
      (I.map (algebraMap A (U.presheaf.stalk x))) ^ (n + 1) •
        (⊤ : Submodule (U.presheaf.stalk x) ((modulesStalkFunctor U x).obj F)))
    (hkerr : letI := stalkAlgebra p x
      LinearMap.ker rH =
      (I.map (algebraMap A (U.presheaf.stalk x))) •
        (⊤ : Submodule (U.presheaf.stalk x) ((modulesStalkFunctor U x).obj F)))
    (hrsurj : Function.Surjective rH) :
    Function.Injective
      ((modulesStalkFunctor U x).map (C := U.Modules)
        (gradedDesc p I n F (fun i => (rep i : A)) (fun i => (rep i).2) e)).hom := by
  classical
  let := stalkAlgebra p x
  let := stalkBaseModule p F x
  have := hflatx
  refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun u hu => ?_)
  choose m hm using fun i : Fin k => hrsurj (((modulesStalkFunctor U x).map (C := U.Modules)
    (biproduct.π (fun _ : Fin k => specialFibre p I F) i)).hom u)
  have htuple : (stalkOfTuple x (specialFibre p I F) fun i => tH (qH (m i))) = u := by
    refine Eq.trans (congrArg (stalkOfTuple x (specialFibre p I F))
      (funext fun i => (hcompat (m i)).trans (hm i))) ?_
    exact stalkOfTuple_stalk_π x (specialFibre p I F) u
  have hzero : qH (∑ i, ((rep i : A)) • m i) = 0 := by
    rw [hsum]
    refine Eq.trans ?_ (map_zero iH)
    rw [← hvalue fun i => qH (m i), htuple, hu]
  have hmem : (∑ i, ((rep i : A)) • m i) ∈
      (I.map (algebraMap A (U.presheaf.stalk x))) ^ (n + 1) •
        (⊤ : Submodule (U.presheaf.stalk x) ((modulesStalkFunctor U x).obj F)) := by
    rw [← hkerq]
    exact hzero
  have hall := Stacks.Flatness.mem_smul_top_of_sum_smul_mem I
    ((modulesStalkFunctor U x).obj F) (U.presheaf.stalk x) n e₀ rep hrep m hmem
  have hzero0 : ∀ i, ((modulesStalkFunctor U x).map (C := U.Modules)
      (biproduct.π (fun _ : Fin k => specialFibre p I F) i)).hom u = 0 := by
    intro i
    have hker : m i ∈ LinearMap.ker rH := by rw [hkerr]; exact hall i
    rw [← hm i]
    exact LinearMap.mem_ker.1 hker
  calc u = stalkOfTuple x (specialFibre p I F) (fun i =>
          ((modulesStalkFunctor U x).map (C := U.Modules)
            (biproduct.π (fun _ : Fin k => specialFibre p I F) i)).hom u) :=
        (stalkOfTuple_stalk_π x (specialFibre p I F) u).symm
    _ = stalkOfTuple x (specialFibre p I F) (fun _ => 0) :=
        congrArg _ (funext hzero0)
    _ = 0 := by simp [stalkOfTuple]

/-- **The comparison is surjective on a stalk.**  A stalk section of the graded piece lies in
`(I𝒪_{U,x})ⁿ (ℱ/Iⁿ⁺¹ℱ)_x`, hence lifts to an element of `(I𝒪_{U,x})ⁿ ℱ_x`, and flatness of
`ℱ_x` writes that element as `∑ aᵢ mᵢ` modulo `(I𝒪_{U,x})ⁿ⁺¹ℱ_x`; the tuple of the classes of
the `mᵢ` is then a preimage. -/
private theorem surjective_stalk_gradedDesc
    [IsNoetherianRing A] [I.IsMaximal] (x : U)
    (hflatx : letI := stalkBaseModule p F x
      Module.Flat A ((modulesStalkFunctor U x).obj F))
    {k : ℕ} (e₀ : (↥(I ^ n) ⧸ (I • (⊤ : Submodule A ↥(I ^ n)))) ≃ₗ[A] (Fin k → (A ⧸ I)))
    (rep : Fin k → ↥(I ^ n))
    (hrep : ∀ i, e₀.symm (Pi.single i (1 : A ⧸ I)) = Submodule.Quotient.mk (rep i))
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) F) ≅ specialFibre p I F)
    (qH : ((modulesStalkFunctor U x).obj F) →ₗ[U.presheaf.stalk x]
      ((modulesStalkFunctor U x).obj (adicQuotient p I (n + 1) F)))
    (tH : ((modulesStalkFunctor U x).obj (adicQuotient p I (n + 1) F)) →ₗ[U.presheaf.stalk x]
      ((modulesStalkFunctor U x).obj (specialFibre p I F)))
    (iH : ((modulesStalkFunctor U x).obj ((gradedPiece p I n F).toSheafOfModules))
      →ₗ[U.presheaf.stalk x] ((modulesStalkFunctor U x).obj (adicQuotient p I (n + 1) F)))
    (hqH : qH = ((modulesStalkFunctor U x).map (C := U.Modules)
      (adicProj p I (n + 1) F)).hom)
    (hiH : iH = ((modulesStalkFunctor U x).map (C := U.Modules)
      (gradedPiece p I n F).ι).hom)
    (hvalue : letI := stalkAlgebra p x
      ∀ w : Fin k → ((modulesStalkFunctor U x).obj (adicQuotient p I (n + 1) F)),
      iH (((modulesStalkFunctor U x).map (C := U.Modules)
            (gradedDesc p I n F (fun i => (rep i : A)) (fun i => (rep i).2) e)).hom
          (stalkOfTuple x (specialFibre p I F) fun i => tH (w i))) =
        ∑ i, algebraMap A (U.presheaf.stalk x) ((rep i : A)) • w i)
    (hsum : letI := stalkAlgebra p x
      letI := stalkBaseModule p F x
      ∀ m : Fin k → ((modulesStalkFunctor U x).obj F),
      qH (∑ i, ((rep i : A)) • m i) =
        ∑ i, algebraMap A (U.presheaf.stalk x) ((rep i : A)) • qH (m i))
    (hkerq : letI := stalkAlgebra p x
      LinearMap.ker qH =
      (I.map (algebraMap A (U.presheaf.stalk x))) ^ (n + 1) •
        (⊤ : Submodule (U.presheaf.stalk x) ((modulesStalkFunctor U x).obj F)))
    (hiinj : Function.Injective iH) :
    Function.Surjective
      ((modulesStalkFunctor U x).map (C := U.Modules)
        (gradedDesc p I n F (fun i => (rep i : A)) (fun i => (rep i).2) e)).hom := by
  classical
  let := stalkAlgebra p x
  let := stalkBaseModule p F x
  have := hflatx
  intro z
  have hz : iH z ∈ (I.map (algebraMap A (U.presheaf.stalk x))) ^ n •
      (⊤ : Submodule (U.presheaf.stalk x)
        ((modulesStalkFunctor U x).obj (adicQuotient p I (n + 1) F))) := by
    rw [← range_stalk_adicFiltration_ι p (adicQuotient p I (n + 1) F) x I n]
    exact ⟨z, by rw [hiH]⟩
  rw [← map_stalk_adicProj_smul_top p F x I (n + 1) n] at hz
  obtain ⟨u₀, hu₀mem, hu₀⟩ := Submodule.mem_map.1 hz
  obtain ⟨m, hmsub⟩ := Stacks.Flatness.exists_sum_smul_sub_mem I
    ((modulesStalkFunctor U x).obj F) (U.presheaf.stalk x) n e₀ rep hrep hu₀mem
  have hqeq : qH u₀ = ∑ i, algebraMap A (U.presheaf.stalk x) ((rep i : A)) • qH (m i) := by
    rw [← hsum]
    have hker : (u₀ - ∑ i, ((rep i : A)) • m i) ∈ LinearMap.ker qH := by
      rw [hkerq]; exact hmsub
    have := LinearMap.mem_ker.1 hker
    rw [map_sub, sub_eq_zero] at this
    exact this
  refine ⟨stalkOfTuple x (specialFibre p I F) fun i => tH (qH (m i)), hiinj ?_⟩
  rw [hvalue fun i => qH (m i), ← hqeq, hqH]
  exact hu₀

/-- **The comparison morphism is bijective on every stalk.**

At a point `x` the three stalk modules are read over `T = 𝒪_{U,x}`: the stalk of `ℱ ⟶ ℱ/Iⁿ⁺¹ℱ`
is a surjection `ℱ_x → (ℱ/Iⁿ⁺¹ℱ)_x` with kernel `(IT)ⁿ⁺¹ℱ_x`, that of `ℱ ⟶ ℱ/Iℱ` a surjection
with kernel `(IT)ℱ_x`, and `Stacks.Algebraization.stalk_idealPowerDesc_apply` says the morphism
sends a tuple of classes of `mᵢ ∈ ℱ_x` to the class of `∑ aᵢ mᵢ`.  Injectivity and surjectivity
are then exactly the two statements `Stacks.Flatness.mem_smul_top_of_sum_smul_mem` and
`Stacks.Flatness.exists_sum_smul_sub_mem` extract from flatness of `ℱ_x` over `A`, transported
along those two surjections.

Unlike the analogous step of [Stacks, Tag 0EJU] there is no case distinction on the support of
`I 𝒪_U`: flatness is assumed at every point, and the argument is uniform in `𝒪_{U,x}`. -/
theorem bijective_stalk_gradedDesc [IsNoetherianRing A] [I.IsMaximal] (hflat : FlatStalks p F)
    {k : ℕ} (e₀ : (↥(I ^ n) ⧸ (I • (⊤ : Submodule A ↥(I ^ n)))) ≃ₗ[A] (Fin k → (A ⧸ I)))
    (rep : Fin k → ↥(I ^ n))
    (hrep : ∀ i, e₀.symm (Pi.single i (1 : A ⧸ I)) = Submodule.Quotient.mk (rep i))
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) F) ≅ specialFibre p I F)
    (he : adicProj p I (n + 1) F ≫ adicProj p I 1 (adicQuotient p I (n + 1) F) ≫ e.hom =
      adicProj p I 1 F)
    (x : U) :
    Function.Bijective ((modulesStalkFunctor U x).map (C := U.Modules)
      (gradedDesc p I n F (fun i => (rep i : A)) (fun i => (rep i).2) e)).hom := by
  classical
  let := stalkAlgebra p x
  let := stalkBaseModule p F x
  have : Module.Flat A ((modulesStalkFunctor U x).obj F) := hflat x
  -- The four stalk maps in play.
  set qH := ((modulesStalkFunctor U x).map (C := U.Modules)
    (adicProj p I (n + 1) F)).hom with hqH
  set tM : adicQuotient p I (n + 1) F ⟶ specialFibre p I F :=
    adicProj p I 1 (adicQuotient p I (n + 1) F) ≫ e.hom with htM
  set tH := ((modulesStalkFunctor U x).map (C := U.Modules) tM).hom with htH
  set rH := ((modulesStalkFunctor U x).map (C := U.Modules) (adicProj p I 1 F)).hom with hrH
  set iH := ((modulesStalkFunctor U x).map (C := U.Modules)
    (gradedPiece p I n F).ι).hom with hiH
  -- `ℱ ⟶ ℱ/Iⁿ⁺¹ℱ ⟶ ℱ/Iℱ` is `ℱ ⟶ ℱ/Iℱ`.
  have hcompat : ∀ m, tH (qH m) = rH m := by
    intro m
    rw [htH, hqH, hrH, stalk_comp_apply x (adicProj p I (n + 1) F) tM m, htM, he]
  -- The value of the morphism on stalks.
  have hvalue : ∀ w : Fin k → ((modulesStalkFunctor U x).obj (adicQuotient p I (n + 1) F)),
      iH (((modulesStalkFunctor U x).map (C := U.Modules)
          (gradedDesc p I n F (fun i => (rep i : A)) (fun i => (rep i).2) e)).hom
        (stalkOfTuple x (specialFibre p I F) fun i => tH (w i))) =
        ∑ i, algebraMap A (U.presheaf.stalk x) ((rep i : A)) • w i := by
    intro w
    refine Eq.trans (stalk_idealPowerDesc_apply (adicQuotient p I (n + 1) F) n
      (adicFiltration_adicQuotient_eq_bot p I n F)
      (fun i V => restrictMemIdealPow_baseScalarMap p n ((rep i).2) V) e rfl x w) ?_
    exact Finset.sum_congr rfl fun i _ =>
      congrArg (· • w i) (stalkAlgebra_algebraMap p x ((rep i : A))).symm
  -- The scalar action of `A` on the two stalks, through the local ring.
  have hsmulQ : ∀ (i : Fin k) (m : (modulesStalkFunctor U x).obj F),
      qH (((rep i : A)) • m) = algebraMap A (U.presheaf.stalk x) ((rep i : A)) • qH m := by
    intro i m
    rw [stalkBaseModule_smul p F x, map_smul]
  have hsum : ∀ m : Fin k → ((modulesStalkFunctor U x).obj F),
      qH (∑ i, ((rep i : A)) • m i) =
        ∑ i, algebraMap A (U.presheaf.stalk x) ((rep i : A)) • qH (m i) := by
    intro m
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hsmulQ i (m i)
  have hkerq : LinearMap.ker qH =
      (I.map (algebraMap A (U.presheaf.stalk x))) ^ (n + 1) •
        (⊤ : Submodule (U.presheaf.stalk x) ((modulesStalkFunctor U x).obj F)) :=
    ker_stalk_adicProj p F x I (n + 1)
  have hkerr : LinearMap.ker rH =
      (I.map (algebraMap A (U.presheaf.stalk x))) •
        (⊤ : Submodule (U.presheaf.stalk x) ((modulesStalkFunctor U x).obj F)) := by
    rw [hrH, ker_stalk_adicProj p F x I 1, pow_one]
  have hrsurj : Function.Surjective rH := surjective_stalk_adicProj p F x I 1
  have hiinj : Function.Injective iH :=
    injective_stalk_adicFiltration_ι p (adicQuotient p I (n + 1) F) x I n
  constructor
  · exact injective_stalk_gradedDesc p I n F x (hflat x) e₀ rep hrep e qH tH rH iH hcompat
      hvalue hsum hkerq hkerr hrsurj
  · exact surjective_stalk_gradedDesc p I n F x (hflat x) e₀ rep hrep e qH tH iH hqH hiH hvalue
      hsum hkerq hiinj

/-! ### The decomposition -/

/-- **The graded pieces of the `I`-adic filtration of a flat module, with the morphism kept.**
For `A` Noetherian, `I` maximal and `ℱ` flat over `A` at every point, there are `k` elements
`aᵢ ∈ Iⁿ` — representatives of a `κ`-basis of `Iⁿ/Iⁿ⁺¹`, so `k = dim_κ Iⁿ/Iⁿ⁺¹` — for which
multiplication by the `aᵢ` is an isomorphism `⨁_{i<k} ℱ/Iℱ ≅ Iⁿ(ℱ/Iⁿ⁺¹ℱ)`.

The identification `e` of `(ℱ/Iⁿ⁺¹ℱ)/I(ℱ/Iⁿ⁺¹ℱ)` with `ℱ/Iℱ` is an argument; the canonical one
is `Stacks.BaseAdicFiltration.specialFibreIso`. -/
theorem exists_isIso_gradedDesc [IsNoetherianRing A] [I.IsMaximal] (hflat : FlatStalks p F)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) F) ≅ specialFibre p I F)
    (he : adicProj p I (n + 1) F ≫ adicProj p I 1 (adicQuotient p I (n + 1) F) ≫ e.hom =
      adicProj p I 1 F) :
    ∃ (k : ℕ) (a : Fin k → A) (ha : ∀ i, a i ∈ I ^ n), IsIso (gradedDesc p I n F a ha e) := by
  classical
  obtain ⟨k, ⟨e₀⟩⟩ := Stacks.Flatness.exists_pi_linearEquiv_gradedPiece I n
  choose rep hrep using fun i : Fin k =>
    Submodule.Quotient.mk_surjective (I • (⊤ : Submodule A ↥(I ^ n)))
      (e₀.symm (Pi.single i (1 : A ⧸ I)))
  refine ⟨k, fun i => (rep i : A), fun i => (rep i).2, ?_⟩
  refine AlgebraicGeometry.isIso_of_forall_modulesStalk _ fun x => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_stalk_gradedDesc p I n F hflat e₀ rep (fun i => (hrep i).symm) e he x

/-- **The graded pieces of the `I`-adic filtration of a flat module.** For `A` Noetherian, `I`
maximal and `ℱ` flat over `A` at every point, the graded piece `Iⁿ(ℱ/Iⁿ⁺¹ℱ)` is a direct sum of
`k = dim_{A/I} Iⁿ/Iⁿ⁺¹` copies of `ℱ/Iℱ`.

This is the identification `Iⁿℱ/Iⁿ⁺¹ℱ ≅ (ℱ/Iℱ) ⊗_{A/I} Iⁿ/Iⁿ⁺¹` of [Stacks, Tag 063Y] and
[Stacks, Tag 08LI], with the tensor factor replaced by the biproduct it becomes once a basis of
`Iⁿ/Iⁿ⁺¹` is chosen; see the discussion at the head of this file. -/
theorem exists_isoDirectSum_gradedPiece [IsNoetherianRing A] [I.IsMaximal]
    (hflat : FlatStalks p F) :
    ∃ k : ℕ, Nonempty ((⨁ fun _ : Fin k => specialFibre p I F) ≅
      (gradedPiece p I n F).toSheafOfModules) := by
  obtain ⟨k, a, ha, hiso⟩ := exists_isIso_gradedDesc p I n F hflat
    (specialFibreIso p I n F).1 (specialFibreIso p I n F).2
  exact ⟨k, ⟨asIso (gradedDesc p I n F a ha (specialFibreIso p I n F).1)⟩⟩

end Desc

/-- **The graded pieces of the `𝔪`-adic filtration over an Artinian local base**, the form in
which the filtration argument of [Stacks, Tag 0E3X] uses them: for `A` Artinian local with
maximal ideal `𝔪` and residue field `κ`, and `ℱ` flat over `A` at every point, the graded piece
`𝔪ⁿ(ℱ/𝔪ⁿ⁺¹ℱ)` is `dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹` copies of the special fibre `ℱ/𝔪ℱ`.

Nilpotence of `𝔪` is not used: an Artinian local ring is Noetherian and its maximal ideal is
maximal, which is all that is needed.  Nilpotence is what makes the *filtration* finite. -/
theorem exists_isoDirectSum_gradedPiece_of_isArtinianRing [IsArtinianRing A] [IsLocalRing A]
    (p : U ⟶ Spec (CommRingCat.of A)) (n : ℕ) (F : U.Modules) [F.IsQuasicoherent]
    (hflat : FlatStalks p F) :
    ∃ k : ℕ, Nonempty ((⨁ fun _ : Fin k => specialFibre p (IsLocalRing.maximalIdeal A) F) ≅
      (gradedPiece p (IsLocalRing.maximalIdeal A) n F).toSheafOfModules) :=
  exists_isoDirectSum_gradedPiece p (IsLocalRing.maximalIdeal A) n F hflat

end Stacks.BaseAdicFiltration

end
