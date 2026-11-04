module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtension
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthFiniteExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
import StacksCore.Tactic.StacksAttribute

/-!
# The local rings of the extension have depth at least two

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` an open immersion whose complement consists
of points at which `𝒪_X` has depth at least two, and `π : V ⟶ U` a finite étale morphism. The
extension `Spec_X(𝓑)` of the cover, for `𝓑 = (π ≫ j)_* 𝒪_V`, is finite over `X`
(`Stacks.FundamentalGroup.ExtendedEtaleFold.isFinite_extendedEtaleToBase`) and the stalks of `𝓑`
have depth at least two over the local rings of `X` off the cover
(`Stacks.FundamentalGroup.ExtendedEtaleFold.two_le_depth_stalk_extendedEtaleAlgebra`). This file
closes the remaining gap: the **local rings of `Spec_X(𝓑)` itself** have depth at least two above
every point of `X` outside the cover, which is the depth clause of [Stacks, Tag 0EY6].

The step from the base-side bound to the clause is [Stacks, Tag 0AUK]
(`Module.depth_eq_iInf_depth_isLocalized_maximal`), which computes the depth of a module over a
finite algebra as the infimum of the depths of its localizations at the maximal ideals, together
with the geometric identification of the local rings of a scheme affine over `X` above a point `x`
with localizations of the sections of the pushed-forward structure algebra. That identification is
the content of `depth_stalk_pushforwardAlgebra_le_depth_stalk` below, and it is read off a single
affine chart rather than from the relative-spectrum gluing datum.

## Main results

* `Module.depth_eq_of_isLocalizedModule` — the depth of a localization of a module at a prime
  depends on neither the chosen model of the localized ring nor the chosen model of the localized
  module.
* `Module.depth_le_depth_of_isLocalization_atPrime` — for a finite algebra `B` over a Noetherian
  ring `A` and a prime `q` of `B` over a prime `p` of `A`, the depth of the localization of `B` at
  `p` over the localization of `A` at `p` is at most the self-depth of the localization of `B` at
  `q`. Both localizations are taken at arbitrary models.
* `Stacks.FundamentalGroup.ExtendedEtaleFold.depth_stalk_pushforwardAlgebra_le_depth_stalk` — for
  an affine morphism `f : Y ⟶ X` onto a locally Noetherian scheme whose pushed-forward structure
  algebra has underlying module of finite type, the depth of the stalk of that module at `f y` is
  at most the depth of the local ring of `Y` at `y`.
* `Stacks.FundamentalGroup.ExtendedEtaleFold.extendedEtale_depth_ge_two` — the depth clause of
  [Stacks, Tag 0EY6]: the local rings of `Spec_X(𝓑)` have depth at least two above every point of
  `X` off the cover.

## Implementation notes

`extendedEtale_depth_ge_two` carries `@[stacks 0EY6 "unique_extension"]`: it is the depth
conjunct of the `unique_extension` clause of the multi-clause tag `0EY6`, whose other three
conjuncts are proved in the neighbouring files of this directory. The clause string records that
the attribute covers that one clause, not the whole tag.

The two `Module` lemmas are pure commutative algebra. They are stated at **arbitrary** models of
the localizations — any ring with `IsLocalization.AtPrime` and any module with
`IsLocalizedModule` — precisely so that the local ring of a scheme at a point and the stalk of a
quasi-coherent module can be plugged in with no transport, which is the same design decision as
`Module.depth_eq_iInf_depth_isLocalized_maximal`. `Module.depth_le_depth_at_prime_over` is stated
at the concrete `Localization.AtPrime`/`LocalizedModule` models, and
`Module.depth_eq_of_isLocalizedModule` is what moves it to arbitrary ones; it is proved by
combining `IsLocalization.algEquiv`, `IsLocalizedModule.linearEquiv`,
`LinearEquiv.extendScalarsOfIsLocalization`, `Module.depth_eq_depth_of_linearEquiv` and
`Module.depth_eq_depth_map_algebraMap`.

The `IsLocalizedModule` hypotheses of both lemmas are **explicit arguments rather than instance
arguments**. At the geometric use site the germ map is `AlgebraicGeometry.affineGerm`, whose
source carries the sections module structure of a `Scheme.Modules` object, while the lemma's
source carries `Algebra.toModule` of the algebra structure on the same sections. The two are
definitionally equal — so the term elaborates — but instance search does not cross between them,
so the hypothesis has to be passed positionally.

For the geometric step the affine chart is produced by
`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset` on `X` and pulled back with
`AlgebraicGeometry.IsAffineOpen.preimage`; the prime of the chart of `Y` contracts to the prime of
the chart of `X` by `AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`, and both stalks are
localizations by `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` while the stalk of the
pushed-forward module is a localized module by `AlgebraicGeometry.affineGerm_isLocalized`.
Finiteness of the sections comes from `AlgebraicGeometry.moduleFinite_sections_on_affine`
([Stacks, Tag 01PB]) and uses that the sections of the underlying module of `f_* 𝒪_Y` over `W`
*are* `Γ(Y, f⁻¹ W)`, with the algebra structure inducing the same module structure — both by
`rfl`.

Passing from `f_* 𝒪_Y` for `f` the structure morphism of the relative spectrum back to the
algebra `𝓑` it was built from uses `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`
([Stacks, Tag 01LX]) and the functor
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleFunctor`, which turn the identification of
algebra sheaves into an isomorphism of `𝒪_X`-modules and hence a linear equivalence of stalks.
That linear equivalence of stalks is `AlgebraicGeometry.moduleStalkLinearEquiv`; importing its
module costs exactly **one** additional repository module over this file's other imports, which
is cheaper than re-proving it here.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0AUK](https://stacks.math.columbia.edu/tag/0AUK)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Module

/-- **The depth of a localization does not depend on the chosen models.** Let `p` be a prime of a
commutative ring `A` and let `N` be an `A`-module. If `R₁` and `R₂` both present the localization
of `A` at `p`, and `M₁` and `M₂` both present the localization of `N` at `p`, over `R₁` and `R₂`
respectively, then the depths of `M₁` over `R₁` and of `M₂` over `R₂` along the maximal ideals
agree. -/
public theorem depth_eq_of_isLocalizedModule
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    {N : Type u} [AddCommGroup N] [Module A N]
    (R₁ : Type u) [CommRing R₁] [Algebra A R₁] [IsLocalization.AtPrime R₁ p]
    (M₁ : Type u) [AddCommGroup M₁] [Module A M₁] [Module R₁ M₁] [IsScalarTower A R₁ M₁]
    (f₁ : N →ₗ[A] M₁) (hf₁ : IsLocalizedModule p.primeCompl f₁)
    (R₂ : Type u) [CommRing R₂] [Algebra A R₂] [IsLocalization.AtPrime R₂ p]
    (M₂ : Type u) [AddCommGroup M₂] [Module A M₂] [Module R₂ M₂] [IsScalarTower A R₂ M₂]
    (f₂ : N →ₗ[A] M₂) (hf₂ : IsLocalizedModule p.primeCompl f₂) :
    letI : IsLocalRing R₁ := IsLocalization.AtPrime.isLocalRing R₁ p
    letI : IsLocalRing R₂ := IsLocalization.AtPrime.isLocalRing R₂ p
    Module.depth R₁ (IsLocalRing.maximalIdeal R₁) M₁ =
      Module.depth R₂ (IsLocalRing.maximalIdeal R₂) M₂ := by
  have _ := hf₁
  have _ := hf₂
  let _ : IsLocalRing R₁ := IsLocalization.AtPrime.isLocalRing R₁ p
  let _ : IsLocalRing R₂ := IsLocalization.AtPrime.isLocalRing R₂ p
  show Module.depth R₁ (IsLocalRing.maximalIdeal R₁) M₁ =
      Module.depth R₂ (IsLocalRing.maximalIdeal R₂) M₂
  let e : R₁ ≃ₐ[A] R₂ := IsLocalization.algEquiv p.primeCompl R₁ R₂
  let _ : Algebra R₁ R₂ := RingHom.toAlgebra (e : R₁ →+* R₂)
  let _ : Module R₁ M₂ := Module.compHom M₂ (algebraMap R₁ R₂)
  have _ : IsScalarTower R₁ R₂ M₂ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : IsScalarTower A R₁ M₂ := by
    refine IsScalarTower.of_algebraMap_smul fun a m => ?_
    show (algebraMap R₁ R₂) (algebraMap A R₁ a) • m = a • m
    rw [show (algebraMap R₁ R₂) (algebraMap A R₁ a) = algebraMap A R₂ a from e.commutes a]
    exact algebraMap_smul R₂ a m
  have hsurj : Function.Surjective (algebraMap R₁ R₂) := e.surjective
  have h1 : Module.depth R₁ (IsLocalRing.maximalIdeal R₁) M₂ =
      Module.depth R₂ (IsLocalRing.maximalIdeal R₂) M₂ := by
    rw [Module.depth_eq_depth_map_algebraMap (A := R₁) (B := R₂) hsurj,
      IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R₁ R₂) hsurj]
  refine Eq.trans ?_ h1
  exact Module.depth_eq_depth_of_linearEquiv _
    ((IsLocalizedModule.linearEquiv p.primeCompl f₁ f₂).extendScalarsOfIsLocalization
      p.primeCompl R₁)

/-- **Depth grows when passing from a prime of the base to a prime above it, at arbitrary models
of the localizations.** Let `B` be a finite algebra over a Noetherian ring `A`, let `q` be a prime
of `B` contracting to a prime `p` of `A`, let `Ap` present the localization of `A` at `p`, let
`Bp` present the localization of `B` at `p` as an `A`-module, and let `Bq` present the
localization of `B` at `q`. Then the depth of `Bp` over `Ap` is at most the self-depth of `Bq`.

This is `Module.depth_le_depth_at_prime_over` ([Stacks, Tag 0AUK] for the decomposition it rests
on), moved off the concrete `Localization.AtPrime`/`LocalizedModule` models by
`Module.depth_eq_of_isLocalizedModule`. -/
@[ega "IV 5.7.9" "(5.7.9.2) for M = B"]
public theorem depth_le_depth_of_isLocalization_atPrime
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Finite A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap A B) = p)
    (Ap : Type u) [CommRing Ap] [Algebra A Ap] [IsLocalization.AtPrime Ap p]
    (Bp : Type u) [AddCommGroup Bp] [Module A Bp] [Module Ap Bp] [IsScalarTower A Ap Bp]
    (g : B →ₗ[A] Bp) (hg : IsLocalizedModule p.primeCompl g)
    (Bq : Type u) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q] :
    letI : IsLocalRing Ap := IsLocalization.AtPrime.isLocalRing Ap p
    letI : IsLocalRing Bq := IsLocalization.AtPrime.isLocalRing Bq q
    Module.depth Ap (IsLocalRing.maximalIdeal Ap) Bp ≤
      Module.depth Bq (IsLocalRing.maximalIdeal Bq) Bq := by
  let _ : IsLocalRing Ap := IsLocalization.AtPrime.isLocalRing Ap p
  let _ : IsLocalRing Bq := IsLocalization.AtPrime.isLocalRing Bq q
  show Module.depth Ap (IsLocalRing.maximalIdeal Ap) Bp ≤
      Module.depth Bq (IsLocalRing.maximalIdeal Bq) Bq
  have hL : Module.depth Ap (IsLocalRing.maximalIdeal Ap) Bp =
      Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl B) :=
    depth_eq_of_isLocalizedModule p Ap Bp g hg (Localization.AtPrime p)
      (LocalizedModule p.primeCompl B) (LocalizedModule.mkLinearMap p.primeCompl B) inferInstance
  have hR : Module.depth (Localization.AtPrime q)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (LocalizedModule q.primeCompl B) =
      Module.depth Bq (IsLocalRing.maximalIdeal Bq) Bq :=
    depth_eq_of_isLocalizedModule q (Localization.AtPrime q) (LocalizedModule q.primeCompl B)
      (LocalizedModule.mkLinearMap q.primeCompl B) inferInstance Bq Bq
      (Algebra.linearMap B Bq) inferInstance
  rw [hL, ← hR]
  exact Module.depth_le_depth_at_prime_over (M := B) p q hq

end Module

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

/-- **The local ring of a scheme affine over `X` has depth at least that of the stalk of its
pushed-forward structure algebra.** For an affine morphism `f : Y ⟶ X` onto a locally Noetherian
scheme whose algebra `f_* 𝒪_Y` has underlying module of finite type, and for `y` a point of `Y`,
the depth of the stalk of that module at `f y` over `𝒪_{X, f y}` is at most the depth of
`𝒪_{Y, y}` over itself.

On an affine open `W` of `X` containing `f y` the preimage `f⁻¹ W` is an affine open of `Y`, the
sections of the underlying module of `f_* 𝒪_Y` over `W` are `Γ(Y, f⁻¹ W)`, a finite
`Γ(X, W)`-module, and the two stalks are the localizations of `Γ(X, W)` and of `Γ(Y, f⁻¹ W)` at
the primes of `f y` and of `y`, the second contracting to the first. -/
public theorem depth_stalk_pushforwardAlgebra_le_depth_stalk {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (f : Y ⟶ X) [IsAffineHom f]
    [SheafOfModules.IsFiniteType.{u, u, u}
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra f))]
    (y : Y) :
    Module.depth (X.presheaf.stalk (f y))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (f y)))
        ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f)).presheaf.stalk (f y))
      ≤ Module.depth (Y.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) := by
  have hqc : (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)).IsQuasicoherent :=
    isQuasicoherent_pushforwardAlgebra f
  obtain ⟨W, hW, hxW, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (x := f y)
      (U := (⊤ : X.Opens)) trivial
  have hV : IsAffineOpen (f ⁻¹ᵁ W) := hW.preimage f
  have hyV : y ∈ f ⁻¹ᵁ W := hxW
  let _ : Algebra Γ(X, W) Γ(Y, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  have _ : IsNoetherianRing Γ(X, W) :=
    IsLocallyNoetherian.component_noetherian (X := X) ⟨W, hW⟩
  have hfin : Module.Finite Γ(X, W)
      Γ(AlgebraSheaf.underlyingModule (pushforwardAlgebra f), W) :=
    AlgebraicGeometry.moduleFinite_sections_on_affine _ W hW
  have _ : Module.Finite Γ(X, W) Γ(Y, f ⁻¹ᵁ W) := hfin
  let _ : Algebra Γ(X, W) (X.presheaf.stalk (f y)) :=
    X.presheaf.algebra_section_stalk (U := W) ⟨f y, hxW⟩
  let _ : Algebra Γ(Y, f ⁻¹ᵁ W) (Y.presheaf.stalk y) :=
    Y.presheaf.algebra_section_stalk (U := f ⁻¹ᵁ W) ⟨y, hyV⟩
  let _ := affineStalkModule (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)) W (f y) hxW
  have _ : IsScalarTower Γ(X, W) (X.presheaf.stalk (f y))
      ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f)).presheaf.stalk (f y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : IsLocalization.AtPrime (X.presheaf.stalk (f y))
      (hW.primeIdealOf ⟨f y, hxW⟩).asIdeal := hW.isLocalization_stalk ⟨f y, hxW⟩
  have _ : IsLocalization.AtPrime (Y.presheaf.stalk y)
      (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := hV.isLocalization_stalk ⟨y, hyV⟩
  have hq : (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.comap
        (algebraMap Γ(X, W) Γ(Y, f ⁻¹ᵁ W))
      = (hW.primeIdealOf ⟨f y, hxW⟩).asIdeal := by
    have h0 := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W hW (f ⁻¹ᵁ W) hV le_rfl hyV)
    rwa [Scheme.Hom.appLE_eq_app] at h0
  exact Module.depth_le_depth_of_isLocalization_atPrime
    (hW.primeIdealOf ⟨f y, hxW⟩).asIdeal (hV.primeIdealOf ⟨y, hyV⟩).asIdeal hq
    (X.presheaf.stalk (f y))
    ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f)).presheaf.stalk (f y))
    (affineGerm (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)) W (f y) hxW)
    (affineGerm_isLocalized
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)) W hW (f y) hxW)
    (Y.presheaf.stalk y)

variable {U X V : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
  (π : V ⟶ U) [IsFinite π] [Etale π]
  (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))

include hdepth in
/-- **The depth clause of [Stacks, Tag 0EY6].** The local rings of the extension
`Spec_X(𝓑)` of a finite étale cover across a depth-two complement have depth at least two above
every point of `X` outside the cover.

The stalk of `𝓑` at such a point has depth at least two over the local ring of the base
(`two_le_depth_stalk_extendedEtaleAlgebra`); the local ring of `Spec_X(𝓑)` at a point above it is
a localization of that stalk at a maximal ideal, so its depth is at least as large
(`depth_stalk_pushforwardAlgebra_le_depth_stalk`). The identification of `𝓑` with the structure
algebra of its own relative spectrum is
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`. -/
@[stacks 0EY6 "unique_extension"]
public theorem extendedEtale_depth_ge_two :
    let Y := (relativeSpectrum (extendedEtaleSituation j π hdepth)).scheme
    let f := (relativeSpectrum (extendedEtaleSituation j π hdepth)).toBase
    ∀ y : Y, f y ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
        (Y.presheaf.stalk y) := by
  intro Y f y hy
  have hcoh : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  have hqcB : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have hftB : SheafOfModules.IsFiniteType.{u, u, u}
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  have _ : IsAffineHom (extendedEtaleToBase j π hdepth) :=
    isAffineHom_extendedEtaleToBase j π hdepth
  have e : AlgebraSheaf.underlyingModule
        (pushforwardAlgebra (extendedEtaleToBase j π hdepth)) ≅
      AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j)) :=
    (AlgebraSheaf.underlyingModuleFunctor X).mapIso
      (pushforwardAlgebraIso (pushforwardAlgebra (π ≫ j)))
  have _ : SheafOfModules.IsFiniteType.{u, u, u}
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (extendedEtaleToBase j π hdepth))) :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} e.symm
  have htr : Module.depth (X.presheaf.stalk (extendedEtaleToBase j π hdepth y))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (extendedEtaleToBase j π hdepth y)))
        ((AlgebraSheaf.underlyingModule
            (pushforwardAlgebra (extendedEtaleToBase j π hdepth))).presheaf.stalk
          (extendedEtaleToBase j π hdepth y))
      = Module.depth (X.presheaf.stalk (extendedEtaleToBase j π hdepth y))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (extendedEtaleToBase j π hdepth y)))
        ((AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))).presheaf.stalk
          (extendedEtaleToBase j π hdepth y)) :=
    Module.depth_eq_depth_of_linearEquiv _
      (AlgebraicGeometry.moduleStalkLinearEquiv e (extendedEtaleToBase j π hdepth y))
  exact le_trans
    ((two_le_depth_stalk_extendedEtaleAlgebra j π hdepth
      (extendedEtaleToBase j π hdepth y) hy).trans_eq htr.symm)
    (depth_stalk_pushforwardAlgebra_le_depth_stalk (extendedEtaleToBase j π hdepth) y)

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
