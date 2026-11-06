module

public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.EtalePushout
public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.ColimitPresentation.Canonical
public import StacksFrontier.RingTheory.IndZariski.Defs

import StacksCore.Tactic.StacksAttribute

/-!
# Composition of ind-Zariski ring maps

A ring map is *ind-Zariski* when its target is a filtered colimit, as an algebra over the
source, of local isomorphisms (Definition 096N, `Algebra.IsIndZariski`). This file proves that
ind-Zariski ring maps are stable under composition.

## Main definitions

* `CommRingCat.localIso`: being a local isomorphism, as a morphism property on `CommRingCat`;
  the analogue for `Algebra.IsLocalIso` of the repository's `CommRingCat.etale`.

## Main results

* `Algebra.IsIndZariski.comp`: Lemma 096Q, the composition of two ind-Zariski ring maps is
  ind-Zariski, with the three rings in independent universes.
* `Algebra.IsIndZariski.of_equiv`: ind-Zariski-ness transports along a commuting square of ring
  equivalences, with all four universes independent.
* `Algebra.IsLocalIso.etale`: a local isomorphism is étale, hence of finite presentation.
* `Algebra.IsStandardOpenImmersion.of_surjective_of_flat`: a surjective flat ring map of finite
  presentation is a standard open immersion.

## Implementation notes

The source omits the proof. The argument is the one the source gives for the ind-étale analogue
0BSI: by the factorization criterion of Lemma 07C3 it suffices to factor every `A`-algebra map
from a finitely presented algebra into `C` through a local isomorphism over `A`, which follows
from the *spreading out* of local isomorphisms over a filtered colimit. The whole formal content
is therefore `CategoryTheory.MorphismProperty.PreIndSpreads` for local isomorphisms, which
Mathlib's `MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads` then turns into the
statement, local isomorphisms being of finite presentation and stable under composition and
cobase change.

Spreading out is proved in two steps. A local isomorphism is étale, so by item (8) of Lemma
00U2 (Mathlib's `Algebra.Etale.exists_subalgebra_fg`) it is the base change of an étale algebra
`T₀` over a subalgebra `A₀ ⊆ B` of finite type over `ℤ`. What remains is to descend the
*local-isomorphism* property, and for that the property is first rewritten as finitely many
equations: `Algebra.IsLocalIso R S` holds as soon as finitely many elements `g` generate the
unit ideal of `S` and, in each `S_g`, every generator of `S` and the inverse of `g` is a
fraction `a / r ^ n` with `a : R` and a fixed `r : R` — the equations of
`isLocalIso_of_equations`, whose sufficiency rests on
`Algebra.IsStandardOpenImmersion.of_surjective_of_flat`: a surjective flat map of finite
presentation is a localization at an idempotent. Those finitely many equations involve finitely
many elements of `B`, so they live over a subalgebra `A ⊆ B` of finite type over `ℤ` containing
`A₀`; they *hold* there because `A ⊗[A₀] T₀ → B ⊗[A₀] T₀` is injective, `T₀` being flat over
`A₀`. Finally `A` is of finite presentation over `ℤ`, hence a finitely presentable object of
`CommRingCat`, so `A → B` factors through a stage of the colimit, and the local isomorphism is
carried along by base change.

Universes are handled as in `StacksDraft.IndEtale`: `Algebra.IsIndZariski.of_equiv` moves the
condition between universes by rewriting it into the factorization criterion, which is
universe-insensitive because a finitely presented algebra, and a local isomorphism, can be
shrunk into the universe of the base (`Algebra.FiniteType.small`). The composition statement is
then obtained by lifting the three rings into a common universe with `ULift`.

## References

* [Stacks Project, Tag 096Q](https://stacks.math.columbia.edu/tag/096Q)
* [Stacks Project, Tag 096N](https://stacks.math.columbia.edu/tag/096N)
* [Stacks Project, Tag 00U2](https://stacks.math.columbia.edu/tag/00U2)
* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [Stacks Project, Tag 0BSI](https://stacks.math.columbia.edu/tag/0BSI)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

/-! ## Local isomorphisms: the elementary permanence properties -/

/-- A surjective flat ring map of finite presentation is a standard open immersion:
its kernel is a finitely generated idempotent ideal, hence generated by an idempotent. -/
theorem Algebra.IsStandardOpenImmersion.of_surjective_of_flat {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    (h : Function.Surjective (algebraMap R S)) :
    Algebra.IsStandardOpenImmersion R S := by
  have hfg : (RingHom.ker (algebraMap R S)).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId R S) h
  have hpure : (RingHom.ker (algebraMap R S)).Pure :=
    Module.Flat.of_linearEquiv
      (e := (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) h).toLinearEquiv)
  have hidem : IsIdempotentElem (RingHom.ker (algebraMap R S)) :=
    Ideal.isIdempotentElem_of_pure _
  rw [Ideal.isIdempotentElem_iff_of_fg _ hfg] at hidem
  obtain ⟨e, he, hker⟩ := hidem
  exact ⟨1 - e, IsLocalization.away_of_isIdempotentElem he.one_sub (by rw [hker]; simp) h⟩

/-- If `R → S` is flat and of finite presentation, if `r : R` has invertible image in `S` and
every element of `S` is a fraction `a / r ^ n` with `a : R`, then `S` is a standard open
immersion over `R`: it is the quotient of the localization `R_r` by an idempotent. -/
theorem Algebra.IsStandardOpenImmersion.of_fraction_away {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] [Algebra.FinitePresentation R S] (r : R)
    (hr : IsUnit (algebraMap R S r))
    (hfrac : ∀ x : S, ∃ (a : R) (n : ℕ), x * algebraMap R S r ^ n = algebraMap R S a) :
    Algebra.IsStandardOpenImmersion R S := by
  let _ : Algebra (Localization.Away r) S :=
    (Localization.awayLift (algebraMap R S) r hr).toAlgebra
  have hcomp : (algebraMap (Localization.Away r) S).comp
      (algebraMap R (Localization.Away r)) = algebraMap R S :=
    IsLocalization.Away.lift_comp r hr
  have : IsScalarTower R (Localization.Away r) S :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  have : Module.Flat (Localization.Away r) S :=
    (Module.flat_iff_of_isLocalization (Localization.Away r) (Submonoid.powers r) S).mpr
      inferInstance
  have : Algebra.FinitePresentation (Localization.Away r) S := by
    apply RingHom.finitePresentation_algebraMap.mp
    refine RingHom.FinitePresentation.of_comp_finiteType
      (algebraMap R (Localization.Away r)) ?_ ?_
    · rw [hcomp]
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance
    · exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hsurj : Function.Surjective (algebraMap (Localization.Away r) S) := by
    intro x
    obtain ⟨a, n, hx⟩ := hfrac x
    refine ⟨IsLocalization.mk' _ a (⟨r ^ n, n, rfl⟩ : Submonoid.powers r), ?_⟩
    have h1 := congrArg (algebraMap (Localization.Away r) S)
      (IsLocalization.mk'_spec (Localization.Away r) a (⟨r ^ n, n, rfl⟩ : Submonoid.powers r))
    simp only [map_mul, ← RingHom.comp_apply, hcomp, map_pow] at h1
    exact (IsUnit.mul_left_inj (hr.pow n)).mp (h1.trans hx.symm)
  have : Algebra.IsStandardOpenImmersion (Localization.Away r) S :=
    Algebra.IsStandardOpenImmersion.of_surjective_of_flat hsurj
  exact Algebra.IsStandardOpenImmersion.trans R (Localization.Away r) S

/-- A standard open immersion is étale. -/
theorem RingHom.IsStandardOpenImmersion.etale {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.IsStandardOpenImmersion) : f.Etale := by
  algebraize [f]
  obtain ⟨r, _⟩ := hf.toAlgebra
  exact Algebra.Etale.of_isLocalizationAway r

/-- A local isomorphism is `RingHom.Locally RingHom.IsStandardOpenImmersion`. -/
theorem Algebra.isLocalIso_iff_locally {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IsLocalIso R S ↔
      RingHom.Locally RingHom.IsStandardOpenImmersion (algebraMap R S) := by
  rw [Algebra.IsLocalIso.iff_span_isStandardOpenImmersion_eq_top,
    RingHom.locally_iff_span_eq_top]
  have hs : {g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)} =
      {g : S | RingHom.IsStandardOpenImmersion
        ((algebraMap S (Localization.Away g)).comp (algebraMap R S))} := by
    ext g
    simp only [Set.mem_ofPred_eq, ← IsScalarTower.algebraMap_eq R S (Localization.Away g),
      RingHom.isStandardOpenImmersion_algebraMap]
  rw [hs]

/-- **A local isomorphism is étale.** -/
instance Algebra.IsLocalIso.etale {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsLocalIso R S] : Algebra.Etale R S := by
  rw [← RingHom.etale_algebraMap,
    ← RingHom.locally_iff_of_localizationSpanTarget RingHom.Etale.respectsIso
      RingHom.Etale.ofLocalizationSpanTarget]
  exact RingHom.locally_of_locally (fun h ↦ h.etale)
    (Algebra.isLocalIso_iff_locally.mp ‹_›)

/-- Local isomorphisms of rings are stable under composition, in the `RingHom.Locally`
spelling. -/
theorem RingHom.Locally.isStandardOpenImmersion_comp {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : RingHom.Locally RingHom.IsStandardOpenImmersion f)
    (hg : RingHom.Locally RingHom.IsStandardOpenImmersion g) :
    RingHom.Locally RingHom.IsStandardOpenImmersion (g.comp f) := by
  algebraize [f, g, g.comp f]
  have hf' : Algebra.IsLocalIso R S := Algebra.isLocalIso_iff_locally.mpr hf
  have hg' : Algebra.IsLocalIso S T := Algebra.isLocalIso_iff_locally.mpr hg
  exact Algebra.isLocalIso_iff_locally.mp (Algebra.IsLocalIso.trans R S T)

namespace CommRingCat

/-- The morphism property of local isomorphisms of commutative rings. -/
def localIso : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty (RingHom.Locally RingHom.IsStandardOpenImmersion)

/-- Unfolding of `CommRingCat.localIso`. -/
@[simp] lemma localIso_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    localIso f ↔ RingHom.Locally RingHom.IsStandardOpenImmersion f.hom := .rfl

/-- Local isomorphisms respect isomorphisms. -/
instance : (localIso.{u}).RespectsIso :=
  RingHom.toMorphismProperty_respectsIso_iff.mp
    (RingHom.locally_respectsIso RingHom.IsStandardOpenImmersion.respectsIso)

/-- Local isomorphisms are stable under composition. -/
instance : (localIso.{u}).IsStableUnderComposition where
  comp_mem _ _ hf hg := RingHom.Locally.isStandardOpenImmersion_comp hf hg

/-- Local isomorphisms are stable under cobase change. -/
instance : (localIso.{u}).IsStableUnderCobaseChange := by
  rw [localIso, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.locally_isStableUnderBaseChange RingHom.IsStandardOpenImmersion.respectsIso
    RingHom.IsStandardOpenImmersion.isStableUnderBaseChange

end CommRingCat

/-- A local isomorphism of rings is of finite presentation. -/
theorem RingHom.Locally.isStandardOpenImmersion_finitePresentation {R S : Type u} [CommRing R]
    [CommRing S] {f : R →+* S} (hf : RingHom.Locally RingHom.IsStandardOpenImmersion f) :
    f.FinitePresentation := by
  algebraize [f]
  have : Algebra.IsLocalIso R S := Algebra.isLocalIso_iff_locally.mpr hf
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- Local isomorphisms are of finite presentation, in the `MorphismProperty.underObj`
spelling that the factorization criterion of Lemma 07C3 rewrites with. -/
lemma localIso_underObj_le_finitePresentation {X : CommRingCat.{u}} :
    (CommRingCat.localIso.{u}).underObj (X := X) ≤
      fun D : Under X ↦ D.hom.hom.FinitePresentation :=
  fun _ hD ↦ RingHom.Locally.isStandardOpenImmersion_finitePresentation hD

/-! ## A criterion for a local isomorphism in terms of finitely many equations

The conditions of `Algebra.isLocalIso_of_equations` are finitely many equations in the algebra
and finitely many elements of the base, which is what makes them descend along a filtered
colimit of base rings. -/

/-- An element of `S` vanishes in `S_g` exactly when a power of `g` kills it. -/
private lemma away_map_eq_zero_iff {S : Type*} [CommRing S] (g w : S) :
    algebraMap S (Localization.Away g) w = 0 ↔ ∃ m : ℕ, g ^ m * w = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers g)]
  exact ⟨fun ⟨⟨_, k, rfl⟩, h⟩ ↦ ⟨k, h⟩, fun ⟨k, h⟩ ↦ ⟨⟨_, k, rfl⟩, h⟩⟩

/-- If every element of a generating set of `S` over `R`, and the inverse of `g`, is a fraction
`a / r ^ n` in the localization `S_g`, then `S_g` is a standard open immersion over `R`. The
hypotheses are stated as equations in `S`: an equality `z = a / r ^ n` in `S_g` is an equation
`g ^ m * (z * r ^ n - a) = 0` in `S`. -/
private lemma isStandardOpenImmersion_away_of_equations {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] (g : S) (r : R) (u : S) (N : ℕ)
    (hru : algebraMap R S r * u = g ^ N)
    (sgen : Set S) (hgen : Algebra.adjoin R sgen = ⊤)
    (hy : ∀ y ∈ sgen, ∃ (a : R) (n m : ℕ),
      g ^ m * (y * algebraMap R S r ^ n - algebraMap R S a) = 0)
    (hinv : ∃ (b : R) (n m : ℕ),
      g ^ m * (algebraMap R S r ^ n - g * algebraMap R S b) = 0) :
    Algebra.IsStandardOpenImmersion R (Localization.Away g) := by
  classical
  set L := Localization.Away g with hL
  have hEt : Algebra.Etale S L := Algebra.Etale.of_isLocalizationAway g
  have : Algebra.Etale R L := Algebra.Etale.comp R S L
  -- the image of `g` is a unit in `L`
  have hgu : IsUnit (algebraMap S L g) := IsLocalization.Away.algebraMap_isUnit g
  have htower : ∀ x : R, algebraMap S L (algebraMap R S x) = algebraMap R L x := fun x ↦
    (IsScalarTower.algebraMap_apply R S L x).symm
  -- `r` is a unit in `L`
  have hru' : algebraMap R L r * algebraMap S L u = algebraMap S L g ^ N := by
    rw [← htower, ← map_mul, hru, map_pow]
  have hrunit : IsUnit (algebraMap R L r) :=
    isUnit_of_mul_isUnit_left (by rw [hru']; exact hgu.pow N)
  -- the fractions `a / r ^ n` form a subalgebra of `L`
  let FL : Subalgebra R L :=
    { carrier := {z : L | ∃ (a : R) (n : ℕ), z * algebraMap R L r ^ n = algebraMap R L a}
      mul_mem' := by
        rintro z w ⟨a, n, hz⟩ ⟨b, m, hw⟩
        refine ⟨a * b, n + m, ?_⟩
        rw [map_mul, ← hz, ← hw, pow_add]
        ring
      one_mem' := ⟨1, 0, by simp⟩
      add_mem' := by
        rintro z w ⟨a, n, hz⟩ ⟨b, m, hw⟩
        refine ⟨a * r ^ m + b * r ^ n, n + m, ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hz, ← hw, pow_add]
        ring
      zero_mem' := ⟨0, 0, by simp⟩
      algebraMap_mem' := fun x ↦ ⟨x, 0, by simp⟩ }
  have hmemFL : ∀ z : L, ∃ (a : R) (n : ℕ), z * algebraMap R L r ^ n = algebraMap R L a := by
    have hS : ∀ y : S, algebraMap S L y ∈ FL := by
      have hle : Algebra.adjoin R sgen ≤ FL.comap (IsScalarTower.toAlgHom R S L) := by
        refine Algebra.adjoin_le ?_
        rintro y hy'
        obtain ⟨a, n, m, hyeq⟩ := hy y hy'
        refine ⟨a, n, ?_⟩
        have := (away_map_eq_zero_iff g _).2 ⟨m, hyeq⟩
        rw [map_sub, map_mul, map_pow, htower, htower, sub_eq_zero] at this
        exact this
      intro y
      rw [hgen] at hle
      exact hle trivial
    have hinvmem : ↑(hgu.unit⁻¹) ∈ FL := by
      obtain ⟨b, n, m, hbeq⟩ := hinv
      refine ⟨b, n, ?_⟩
      have h0 := (away_map_eq_zero_iff g _).2 ⟨m, hbeq⟩
      rw [map_sub, map_pow, map_mul, htower, htower, sub_eq_zero] at h0
      rw [h0, ← mul_assoc, hgu.val_inv_mul, one_mul]
    intro z
    obtain ⟨k, y, h2⟩ := IsLocalization.Away.surj g z
    have hzval : z = algebraMap S L y * (↑(hgu.unit⁻¹) : L) ^ k := by
      calc z = z * (algebraMap S L g ^ k * (↑(hgu.unit⁻¹) : L) ^ k) := by
                rw [← mul_pow, hgu.mul_val_inv, one_pow, mul_one]
        _ = algebraMap S L y * (↑(hgu.unit⁻¹) : L) ^ k := by rw [← mul_assoc, h2]
    rw [hzval]
    exact FL.mul_mem (hS y) (FL.pow_mem hinvmem k)
  exact Algebra.IsStandardOpenImmersion.of_fraction_away r hrunit hmemFL

/-- The equations of `isStandardOpenImmersion_away_of_equations` are also necessary. -/
private lemma exists_equations_of_isStandardOpenImmersion {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (g : S)
    [hstd : Algebra.IsStandardOpenImmersion R (Localization.Away g)] :
    ∃ (r : R) (u : S) (N : ℕ), algebraMap R S r * u = g ^ N ∧
      (∀ y : S, ∃ (a : R) (n m : ℕ),
        g ^ m * (y * algebraMap R S r ^ n - algebraMap R S a) = 0) ∧
      ∃ (b : R) (n m : ℕ), g ^ m * (algebraMap R S r ^ n - g * algebraMap R S b) = 0 := by
  classical
  set L := Localization.Away g with hL
  obtain ⟨r, hr⟩ := Algebra.IsStandardOpenImmersion.exists_away R L
  have hgu : IsUnit (algebraMap S L g) := IsLocalization.Away.algebraMap_isUnit g
  have htower : ∀ x : R, algebraMap S L (algebraMap R S x) = algebraMap R L x := fun x ↦
    (IsScalarTower.algebraMap_apply R S L x).symm
  have hfrac : ∀ z : L, ∃ (a : R) (n : ℕ), z * algebraMap R L r ^ n = algebraMap R L a := by
    intro z
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj r z
    exact ⟨a, n, h⟩
  -- (1) `r` divides a power of `g`
  obtain ⟨u, N, hru⟩ : ∃ (u : S) (N : ℕ), algebraMap R S r * u = g ^ N := by
    have hrunit : IsUnit (algebraMap R L r) :=
      IsLocalization.map_units (M := Submonoid.powers r) L ⟨r, 1, pow_one r⟩
    obtain ⟨k, w, hw⟩ := IsLocalization.Away.surj g (↑hrunit.unit⁻¹ : L)
    have h1 : algebraMap S L (algebraMap R S r) * algebraMap S L w = algebraMap S L g ^ k := by
      rw [← hw, htower, ← mul_assoc, hrunit.mul_val_inv, one_mul]
    obtain ⟨m, hm⟩ := (away_map_eq_zero_iff g (algebraMap R S r * w - g ^ k)).1 (by
      rw [map_sub, map_mul, map_pow, h1, sub_self])
    refine ⟨g ^ m * w, m + k, ?_⟩
    have : g ^ m * (algebraMap R S r * w) - g ^ m * g ^ k = 0 := by
      rw [← mul_sub]; exact hm
    rw [pow_add]
    linear_combination this
  -- (2) every element of `S` is a fraction over `r` in `S_g`
  have hy : ∀ y : S, ∃ (a : R) (n m : ℕ),
      g ^ m * (y * algebraMap R S r ^ n - algebraMap R S a) = 0 := by
    intro y
    obtain ⟨a, n, ha⟩ := hfrac (algebraMap S L y)
    obtain ⟨m, hm⟩ := (away_map_eq_zero_iff g (y * algebraMap R S r ^ n - algebraMap R S a)).1 (by
      rw [map_sub, map_mul, map_pow, htower, htower, ha, sub_self])
    exact ⟨a, n, m, hm⟩
  -- (3) the inverse of `g` is a fraction over `r` in `S_g`
  obtain ⟨b, n, m, hb⟩ : ∃ (b : R) (n m : ℕ),
      g ^ m * (algebraMap R S r ^ n - g * algebraMap R S b) = 0 := by
    obtain ⟨b, n, hbn⟩ := hfrac (↑hgu.unit⁻¹ : L)
    have h1 : algebraMap S L (algebraMap R S r ^ n) =
        algebraMap S L (g * algebraMap R S b) := by
      rw [map_mul, htower, ← hbn, map_pow, htower, ← mul_assoc, hgu.mul_val_inv, one_mul]
    obtain ⟨m, hm⟩ := (away_map_eq_zero_iff g (algebraMap R S r ^ n - g * algebraMap R S b)).1 (by
      rw [map_sub, h1, sub_self])
    exact ⟨b, n, m, hm⟩
  exact ⟨r, u, N, hru, hy, b, n, m, hb⟩

/-- **Local isomorphisms are cut out by finitely many equations.** If `S` is étale over `R`,
is generated over `R` by `sgen`, and the elements of a spanning set `G` of `S` each carry the
fraction data of `isStandardOpenImmersion_away_of_equations`, then `S` is a local isomorphism
over `R`. -/
private lemma isLocalIso_of_equations {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (sgen : Set S) (hgen : Algebra.adjoin R sgen = ⊤)
    (G : Set S) (hspan : Ideal.span G = ⊤)
    (hdata : ∀ g ∈ G, ∃ (r : R) (u : S) (N : ℕ), algebraMap R S r * u = g ^ N ∧
      (∀ y ∈ sgen, ∃ (a : R) (n m : ℕ),
        g ^ m * (y * algebraMap R S r ^ n - algebraMap R S a) = 0) ∧
      ∃ (b : R) (n m : ℕ), g ^ m * (algebraMap R S r ^ n - g * algebraMap R S b) = 0) :
    Algebra.IsLocalIso R S := by
  refine Algebra.IsLocalIso.of_span_eq_top hspan fun g hg ↦ ?_
  obtain ⟨r, u, N, h1, h2, h3⟩ := hdata g hg
  have := isStandardOpenImmersion_away_of_equations g r u N h1 sgen hgen h2 h3
  infer_instance

/-! ## Descending a local isomorphism to a subalgebra of finite type

A local isomorphism `B → T` is the base change of an étale algebra `T₀` over a subalgebra
`A₀ ⊆ B` of finite type over `ℤ` (Lemma 00U2 (8), Mathlib's
`Algebra.Etale.exists_subalgebra_fg`). The finitely many equations of
`isLocalIso_of_equations` then descend to a larger subalgebra of finite type, because `T₀` is
flat over `A₀`, so `A ⊗[A₀] T₀ → B ⊗[A₀] T₀` is injective for every intermediate `A`. -/

open scoped TensorProduct

/-- The subalgebra of `B` over `A₀` generated by a finite set. -/
private noncomputable def interAlg (A₀ B : Type u) [CommRing A₀] [CommRing B] [Algebra A₀ B]
    (s : Finset B) : Subalgebra A₀ B :=
  Algebra.adjoin A₀ (↑s : Set B)

/-- The comparison map from the base change to `interAlg A₀ B s` to the base change to `B`. -/
private noncomputable def interMap (A₀ B T₀ : Type u) [CommRing A₀] [CommRing B] [CommRing T₀]
    [Algebra A₀ B] [Algebra A₀ T₀] (s : Finset B) :
    (↥(interAlg A₀ B s) ⊗[A₀] T₀) →ₐ[A₀] (B ⊗[A₀] T₀) :=
  Algebra.TensorProduct.map (interAlg A₀ B s).val (AlgHom.id A₀ T₀)

/-- The comparison map is injective, because `T₀` is flat over `A₀`. -/
private lemma interMap_injective (A₀ B T₀ : Type u) [CommRing A₀] [CommRing B] [CommRing T₀]
    [Algebra A₀ B] [Algebra A₀ T₀] [Module.Flat A₀ T₀] (s : Finset B) :
    Function.Injective (interMap A₀ B T₀ s) := by
  have h2 : Function.Injective
      (LinearMap.rTensor T₀ (interAlg A₀ B s).val.toLinearMap) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hagree : ∀ z : ↥(interAlg A₀ B s) ⊗[A₀] T₀,
      interMap A₀ B T₀ s z = LinearMap.rTensor T₀ (interAlg A₀ B s).val.toLinearMap z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [interMap]
    | add x y hx hy => simp [hx, hy]
  intro x y hxy
  exact h2 (by rw [← hagree, ← hagree, hxy])

/-- An element in the image of one stage is in the image of any larger stage. -/
private lemma exists_interMap_eq_mono {A₀ B T₀ : Type u} [CommRing A₀] [CommRing B]
    [CommRing T₀] [Algebra A₀ B] [Algebra A₀ T₀] {s s' : Finset B} (h : s ⊆ s')
    {ξ : B ⊗[A₀] T₀} (hξ : ∃ x, interMap A₀ B T₀ s x = ξ) :
    ∃ x, interMap A₀ B T₀ s' x = ξ := by
  obtain ⟨x, hx⟩ := hξ
  have hle : interAlg A₀ B s ≤ interAlg A₀ B s' := Algebra.adjoin_mono (by simpa using h)
  refine ⟨Algebra.TensorProduct.map (Subalgebra.inclusion hle) (AlgHom.id A₀ T₀) x, ?_⟩
  rw [← hx, interMap, interMap, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
    Subalgebra.val_comp_inclusion, AlgHom.id_comp]

/-- Every element of `B ⊗[A₀] T₀` comes from some stage. -/
private lemma exists_interMap_eq {A₀ B T₀ : Type u} [CommRing A₀] [CommRing B] [CommRing T₀]
    [Algebra A₀ B] [Algebra A₀ T₀] (ξ : B ⊗[A₀] T₀) :
    ∃ s : Finset B, ∃ x, interMap A₀ B T₀ s x = ξ := by
  classical
  induction ξ using TensorProduct.induction_on with
  | zero => exact ⟨∅, 0, by rw [map_zero]⟩
  | tmul b t =>
      refine ⟨{b}, (⟨b, Algebra.subset_adjoin (by simp)⟩ : ↥(interAlg A₀ B {b})) ⊗ₜ t, ?_⟩
      rw [interMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.val_apply]
  | add x y hx hy =>
      obtain ⟨s₁, hx⟩ := hx
      obtain ⟨s₂, hy⟩ := hy
      obtain ⟨x', hx'⟩ := exists_interMap_eq_mono (Finset.subset_union_left (s₂ := s₂)) hx
      obtain ⟨y', hy'⟩ := exists_interMap_eq_mono (Finset.subset_union_right (s₁ := s₁)) hy
      exact ⟨s₁ ∪ s₂, x' + y', by rw [map_add, hx', hy']⟩

/-- Finitely many elements of `B ⊗[A₀] T₀` come from a common intermediate stage. -/
private lemma exists_interMap_eq_finset {A₀ B T₀ : Type u} [CommRing A₀] [CommRing B]
    [CommRing T₀] [Algebra A₀ B] [Algebra A₀ T₀] (S : Finset (B ⊗[A₀] T₀)) :
    ∃ s : Finset B, ∀ ξ ∈ S, ∃ x, interMap A₀ B T₀ s x = ξ := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨∅, by simp⟩
  | insert ξ S hξ ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨s', hs'⟩ := exists_interMap_eq (A₀ := A₀) (B := B) (T₀ := T₀) ξ
      refine ⟨s ∪ s', ?_⟩
      intro η hη
      rcases Finset.mem_insert.mp hη with rfl | hη
      · exact exists_interMap_eq_mono Finset.subset_union_right hs'
      · exact exists_interMap_eq_mono Finset.subset_union_left (hs η hη)

/-- The base change of a generating set generates the base change. -/
private lemma adjoin_tmul_image_eq_top {A₀ A T₀ : Type u} [CommRing A₀] [CommRing A]
    [CommRing T₀] [Algebra A₀ A] [Algebra A₀ T₀] (s₀ : Set T₀)
    (hs₀ : Algebra.adjoin A₀ s₀ = ⊤) :
    Algebra.adjoin A ((fun t => (1 : A) ⊗ₜ[A₀] t) '' s₀) = ⊤ := by
  set C := Algebra.adjoin A ((fun t => (1 : A) ⊗ₜ[A₀] t) '' s₀) with hC
  have h1 : ∀ t : T₀, (1 : A) ⊗ₜ[A₀] t ∈ C := by
    intro t
    have ht : t ∈ Algebra.adjoin A₀ s₀ := hs₀ ▸ Algebra.mem_top
    induction ht using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap x =>
        rw [← Algebra.TensorProduct.algebraMap_apply',
          IsScalarTower.algebraMap_apply A₀ A (A ⊗[A₀] T₀) x]
        exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
    | mul x y _ _ hx hy =>
        rw [show (1 : A) ⊗ₜ[A₀] (x * y) = ((1 : A) ⊗ₜ[A₀] x) * ((1 : A) ⊗ₜ[A₀] y) from by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
        exact mul_mem hx hy
  have h2 : ∀ ξ : A ⊗[A₀] T₀, ξ ∈ C := by
    intro ξ
    induction ξ using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a t =>
        rw [show a ⊗ₜ[A₀] t = (algebraMap A (A ⊗[A₀] T₀) a) * ((1 : A) ⊗ₜ[A₀] t) from by
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul, Algebra.algebraMap_self_apply]]
        exact mul_mem (Subalgebra.algebraMap_mem _ a) (h1 t)
    | add x y hx hy => exact add_mem hx hy
  exact eq_top_iff.mpr fun ξ _ => h2 ξ

/-- The comparison map commutes with the structure maps. -/
private lemma interMap_algebraMap (A₀ B T₀ : Type u) [CommRing A₀] [CommRing B] [CommRing T₀]
    [Algebra A₀ B] [Algebra A₀ T₀] (s : Finset B) (x : ↥(interAlg A₀ B s)) :
    interMap A₀ B T₀ s (algebraMap (↥(interAlg A₀ B s)) (↥(interAlg A₀ B s) ⊗[A₀] T₀) x) =
      algebraMap B (B ⊗[A₀] T₀) (x : B) := by
  rw [Algebra.TensorProduct.algebraMap_apply, interMap, Algebra.TensorProduct.map_tmul,
    Subalgebra.val_apply, map_one, Algebra.TensorProduct.algebraMap_apply]
  simp

/-- The comparison map on the elements coming from `T₀`. -/
private lemma interMap_one_tmul (A₀ B T₀ : Type u) [CommRing A₀] [CommRing B] [CommRing T₀]
    [Algebra A₀ B] [Algebra A₀ T₀] (s : Finset B) (y : T₀) :
    interMap A₀ B T₀ s ((1 : ↥(interAlg A₀ B s)) ⊗ₜ[A₀] y) = (1 : B) ⊗ₜ[A₀] y := by
  rw [interMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.val_apply,
    Subalgebra.coe_one]

/-- The comparison map on a product with a structure element. -/
private lemma interMap_mul_algebraMap (A₀ B T₀ : Type u) [CommRing A₀] [CommRing B]
    [CommRing T₀] [Algebra A₀ B] [Algebra A₀ T₀] (s : Finset B) (α : ↥(interAlg A₀ B s))
    (x : ↥(interAlg A₀ B s) ⊗[A₀] T₀) :
    interMap A₀ B T₀ s (algebraMap _ _ α * x) =
      algebraMap B (B ⊗[A₀] T₀) (α : B) * interMap A₀ B T₀ s x := by
  rw [map_mul, interMap_algebraMap]

/-- The comparison map on a power. -/
private lemma interMap_pow (A₀ B T₀ : Type u) [CommRing A₀] [CommRing B] [CommRing T₀]
    [Algebra A₀ B] [Algebra A₀ T₀] (s : Finset B) (x : ↥(interAlg A₀ B s) ⊗[A₀] T₀) (N : ℕ) :
    interMap A₀ B T₀ s (x ^ N) = (interMap A₀ B T₀ s x) ^ N := map_pow _ _ _

/-- The comparison map on the equations testing a generator. -/
private lemma interMap_shape2 (A₀ B T₀ : Type u) [CommRing A₀] [CommRing B] [CommRing T₀]
    [Algebra A₀ B] [Algebra A₀ T₀] (s : Finset B) (α β : ↥(interAlg A₀ B s))
    (x y : ↥(interAlg A₀ B s) ⊗[A₀] T₀) (n m : ℕ) :
    interMap A₀ B T₀ s (x ^ m * (y * algebraMap _ _ α ^ n - algebraMap _ _ β)) =
      (interMap A₀ B T₀ s x) ^ m * (interMap A₀ B T₀ s y *
        algebraMap B (B ⊗[A₀] T₀) (α : B) ^ n - algebraMap B (B ⊗[A₀] T₀) (β : B)) := by
  rw [map_mul, map_pow, map_sub, map_mul, map_pow, interMap_algebraMap, interMap_algebraMap]

/-- The comparison map on the equations testing the inverse of `g`. -/
private lemma interMap_shape3 (A₀ B T₀ : Type u) [CommRing A₀] [CommRing B] [CommRing T₀]
    [Algebra A₀ B] [Algebra A₀ T₀] (s : Finset B) (α β : ↥(interAlg A₀ B s))
    (x : ↥(interAlg A₀ B s) ⊗[A₀] T₀) (n m : ℕ) :
    interMap A₀ B T₀ s (x ^ m * (algebraMap _ _ α ^ n - x * algebraMap _ _ β)) =
      (interMap A₀ B T₀ s x) ^ m * (algebraMap B (B ⊗[A₀] T₀) (α : B) ^ n -
        interMap A₀ B T₀ s x * algebraMap B (B ⊗[A₀] T₀) (β : B)) := by
  rw [map_mul, map_pow, map_sub, map_pow, map_mul, interMap_algebraMap, interMap_algebraMap]

/-- The stage verification of `exists_intermediate_isLocalIso`, with the intermediate
subalgebra kept abstract so that the terms stay small. -/
private lemma isLocalIso_interAlg {A₀ B T₀ : Type u} [CommRing A₀] [CommRing B] [CommRing T₀]
    [Algebra A₀ B] [Algebra A₀ T₀] [Algebra.Etale A₀ T₀] [Module.Flat A₀ T₀]
    (s : Finset B) (s₀ : Finset T₀) (hs₀ : Algebra.adjoin A₀ (↑s₀ : Set T₀) = ⊤)
    (G : Finset (B ⊗[A₀] T₀)) (r b : (B ⊗[A₀] T₀) → B)
    (u c : (B ⊗[A₀] T₀) → B ⊗[A₀] T₀) (N n' m' : (B ⊗[A₀] T₀) → ℕ)
    (a : (B ⊗[A₀] T₀) → (B ⊗[A₀] T₀) → B) (n m : (B ⊗[A₀] T₀) → (B ⊗[A₀] T₀) → ℕ)
    (lift : (B ⊗[A₀] T₀) → ↥(interAlg A₀ B s) ⊗[A₀] T₀)
    (hliftG : ∀ g ∈ G, interMap A₀ B T₀ s (lift g) = g)
    (hliftu : ∀ g ∈ G, interMap A₀ B T₀ s (lift (u g)) = u g)
    (hliftc : ∀ g ∈ G, interMap A₀ B T₀ s (lift (c g)) = c g)
    (hrmem : ∀ g ∈ G, r g ∈ interAlg A₀ B s) (hbmem : ∀ g ∈ G, b g ∈ interAlg A₀ B s)
    (hamem : ∀ g ∈ G, ∀ t ∈ s₀, a g ((1 : B) ⊗ₜ[A₀] t) ∈ interAlg A₀ B s)
    (hc : ∑ g ∈ G, c g * g = 1)
    (hru : ∀ g ∈ G, algebraMap B (B ⊗[A₀] T₀) (r g) * u g = g ^ N g)
    (ha : ∀ g ∈ G, ∀ t ∈ s₀, g ^ m g ((1 : B) ⊗ₜ[A₀] t) *
      (((1 : B) ⊗ₜ[A₀] t) * algebraMap B (B ⊗[A₀] T₀) (r g) ^ n g ((1 : B) ⊗ₜ[A₀] t) -
        algebraMap B (B ⊗[A₀] T₀) (a g ((1 : B) ⊗ₜ[A₀] t))) = 0)
    (hb : ∀ g ∈ G, g ^ m' g * (algebraMap B (B ⊗[A₀] T₀) (r g) ^ n' g -
      g * algebraMap B (B ⊗[A₀] T₀) (b g)) = 0) :
    Algebra.IsLocalIso ↥(interAlg A₀ B s) (↥(interAlg A₀ B s) ⊗[A₀] T₀) := by
  have hsum : ∑ g ∈ G, lift (c g) * lift g = (1 : ↥(interAlg A₀ B s) ⊗[A₀] T₀) := by
    apply interMap_injective A₀ B T₀ s
    rw [map_one, map_sum, ← hc]
    refine Finset.sum_congr rfl fun g hg ↦ ?_
    rw [map_mul, hliftc g hg, hliftG g hg]
  have hspan : Ideal.span ((fun g ↦ lift g) '' (↑G : Set (B ⊗[A₀] T₀))) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun g hg ↦
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, hg, rfl⟩)
  refine isLocalIso_of_equations
    ((fun t ↦ (1 : ↥(interAlg A₀ B s)) ⊗ₜ[A₀] t) '' (↑s₀ : Set T₀))
    (adjoin_tmul_image_eq_top _ hs₀) _ hspan ?_
  rintro x ⟨g, hg, rfl⟩
  refine ⟨⟨r g, hrmem g hg⟩, lift (u g), N g, ?_, ?_, ?_⟩
  · apply interMap_injective A₀ B T₀ s
    rw [interMap_mul_algebraMap, interMap_pow, hliftu g hg, hliftG g hg]
    exact hru g hg
  · rintro y ⟨t, ht, rfl⟩
    refine ⟨⟨a g ((1 : B) ⊗ₜ[A₀] t), hamem g hg t ht⟩,
      n g ((1 : B) ⊗ₜ[A₀] t), m g ((1 : B) ⊗ₜ[A₀] t), ?_⟩
    apply interMap_injective A₀ B T₀ s
    rw [interMap_shape2, map_zero, interMap_one_tmul, hliftG g hg]
    exact ha g hg t ht
  · refine ⟨⟨b g, hbmem g hg⟩, n' g, m' g, ?_⟩
    apply interMap_injective A₀ B T₀ s
    rw [interMap_shape3, map_zero, hliftG g hg]
    exact hb g hg

/-- The finitely many equations witnessing that `Ξ` is a local isomorphism over `B`, for a
prescribed finite set `Y` of test elements. -/
private lemma exists_finite_cover_equations {B Ξ : Type u} [CommRing B] [CommRing Ξ]
    [Algebra B Ξ] [Algebra.IsLocalIso B Ξ] (Y : Finset Ξ) :
    ∃ G : Finset Ξ, Ideal.span (↑G : Set Ξ) = ⊤ ∧
      ∀ g ∈ G, ∃ (r : B) (u : Ξ) (N : ℕ), algebraMap B Ξ r * u = g ^ N ∧
        (∀ y ∈ Y, ∃ (a : B) (n m : ℕ),
          g ^ m * (y * algebraMap B Ξ r ^ n - algebraMap B Ξ a) = 0) ∧
        ∃ (b : B) (n m : ℕ), g ^ m * (algebraMap B Ξ r ^ n - g * algebraMap B Ξ b) = 0 := by
  have h1 : (1 : Ξ) ∈ Ideal.span
      {g : Ξ | Algebra.IsStandardOpenImmersion B (Localization.Away g)} := by
    rw [Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top B Ξ]
    exact Submodule.mem_top
  obtain ⟨G, hGsub, hG1⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨G, (Ideal.eq_top_iff_one _).mpr hG1, fun g hg ↦ ?_⟩
  have : Algebra.IsStandardOpenImmersion B (Localization.Away g) := hGsub hg
  obtain ⟨r, u, N, hru, hy, hinv⟩ := exists_equations_of_isStandardOpenImmersion (R := B) g
  exact ⟨r, u, N, hru, fun y _ ↦ hy y, hinv⟩

/-- **A local isomorphism descends to a subalgebra of finite type over `ℤ`.** If `T` is a local
isomorphism over `B`, then there is a ring `A` of finite type over `ℤ` with a map to `B` and a
local isomorphism `A → T'` whose base change along `A → B` is `T`. -/
private lemma exists_intermediate_isLocalIso (B T : Type u) [CommRing B] [CommRing T]
    [Algebra B T] [Algebra.IsLocalIso B T] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra A B) (T' : Type u) (_ : CommRing T')
      (_ : Algebra A T'), Algebra.FiniteType ℤ A ∧ Algebra.IsLocalIso A T' ∧
      Nonempty (T ≃ₐ[B] B ⊗[A] T') := by
  classical
  obtain ⟨A₀, T₀, _, _, hA₀fg, hT₀et, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ B T
  have hLI : Algebra.IsLocalIso B (B ⊗[A₀] T₀) := Algebra.IsLocalIso.of_algEquiv e
  obtain ⟨s₀, hs₀⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ↥A₀ T₀).FG)
  obtain ⟨G, hGspan, hdata⟩ := exists_finite_cover_equations (B := B) (Ξ := B ⊗[A₀] T₀)
    (s₀.image (fun t ↦ (1 : B) ⊗ₜ[A₀] t))
  choose! r u N hru hy hinv using hdata
  choose! a n m ha using hy
  choose! b n' m' hb using hinv
  -- the coefficients of the partition of unity
  obtain ⟨c, hc⟩ : ∃ c : (B ⊗[A₀] T₀) → (B ⊗[A₀] T₀), ∑ g ∈ G, c g * g = 1 := by
    have h1 := (Ideal.eq_top_iff_one _).mp hGspan
    rw [Submodule.mem_span_finset] at h1
    obtain ⟨f, hf⟩ := h1
    exact ⟨f, by simpa using hf.2⟩
  -- all the data lives over one subalgebra of finite type
  obtain ⟨s₁, hs₁⟩ := exists_interMap_eq_finset (A₀ := ↥A₀) (B := B) (T₀ := T₀)
    (G ∪ G.image u ∪ G.image c)
  set sfin : Finset B := s₁ ∪ (G.image r ∪ G.image b ∪
    (G ×ˢ s₀.image (fun t ↦ (1 : B) ⊗ₜ[A₀] t)).image (fun q ↦ a q.1 q.2)) with hsfin
  have hmemA : ∀ x ∈ sfin, x ∈ interAlg ↥A₀ B sfin := fun x hx ↦
    Algebra.subset_adjoin (by simpa using hx)
  have hliftex : ∀ ξ ∈ G ∪ G.image u ∪ G.image c,
      ∃ x : ↥(interAlg ↥A₀ B sfin) ⊗[↥A₀] T₀, interMap ↥A₀ B T₀ sfin x = ξ := fun ξ hξ ↦
    exists_interMap_eq_mono Finset.subset_union_left (hs₁ ξ hξ)
  choose! lift hlift using hliftex
  -- membership bookkeeping
  have hgmem : ∀ g ∈ G, g ∈ G ∪ G.image u ∪ G.image c := fun g hg ↦ by
    simp only [Finset.mem_union]; exact Or.inl (Or.inl hg)
  have humem : ∀ g ∈ G, u g ∈ G ∪ G.image u ∪ G.image c := fun g hg ↦ by
    simp only [Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inr ⟨g, hg, rfl⟩)
  have hcmem : ∀ g ∈ G, c g ∈ G ∪ G.image u ∪ G.image c := fun g hg ↦ by
    simp only [Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨g, hg, rfl⟩
  have hrmem : ∀ g ∈ G, r g ∈ interAlg ↥A₀ B sfin := fun g hg ↦ by
    refine hmemA _ ?_
    simp only [hsfin, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inl (Or.inl ⟨g, hg, rfl⟩))
  have hbmem : ∀ g ∈ G, b g ∈ interAlg ↥A₀ B sfin := fun g hg ↦ by
    refine hmemA _ ?_
    simp only [hsfin, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inl (Or.inr ⟨g, hg, rfl⟩))
  have hamem : ∀ g ∈ G, ∀ t ∈ s₀, a g ((1 : B) ⊗ₜ[↥A₀] t) ∈ interAlg ↥A₀ B sfin :=
    fun g hg t ht ↦ by
      refine hmemA _ ?_
      simp only [hsfin, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr ⟨(g, (1 : B) ⊗ₜ[↥A₀] t),
        Finset.mem_product.mpr ⟨hg, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩, rfl⟩)
  have hLIdown : Algebra.IsLocalIso ↥(interAlg ↥A₀ B sfin)
      (↥(interAlg ↥A₀ B sfin) ⊗[↥A₀] T₀) :=
    isLocalIso_interAlg sfin s₀ hs₀ G r b u c N n' m' a n m lift
      (fun g hg ↦ hlift g (hgmem g hg)) (fun g hg ↦ hlift (u g) (humem g hg))
      (fun g hg ↦ hlift (c g) (hcmem g hg)) hrmem hbmem hamem hc hru
      (fun g hg t ht ↦ ha g hg _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)) hb
  -- finite type over `ℤ`
  have hftA : Algebra.FiniteType ℤ ↥(interAlg ↥A₀ B sfin) := by
    have h0 : Algebra.FiniteType ℤ ↥A₀ := ⟨A₀.fg_top.mpr hA₀fg⟩
    have h1 : Algebra.FiniteType ↥A₀ ↥(interAlg ↥A₀ B sfin) :=
      ⟨(Subalgebra.fg_top _).mpr ⟨sfin, rfl⟩⟩
    exact Algebra.FiniteType.trans h0 h1
  exact ⟨↥(interAlg ↥A₀ B sfin), inferInstance, inferInstance, _, inferInstance, inferInstance,
    hftA, hLIdown,
    ⟨e.trans (Algebra.TensorProduct.cancelBaseChange ↥A₀ ↥(interAlg ↥A₀ B sfin) B B T₀).symm⟩⟩

/-! ## Spreading out a local isomorphism over a filtered colimit -/

/-- **A local isomorphism out of a filtered colimit spreads out.** Let `B = colim Bᵢ` be a
filtered colimit of rings and let `B → E` be a local isomorphism. Then `E` is the base change
of a local isomorphism `Bᵢ → E'` for some `i`.

This is `CategoryTheory.MorphismProperty.PreIndSpreads` for the property of being a local
isomorphism. -/
private lemma exists_isPushout_localIso {J : Type u} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ CommRingCat.{u}} {c : Cocone D} (hc : IsColimit c) {T : CommRingCat.{u}}
    (f : c.pt ⟶ T) (hf : CommRingCat.localIso.{u} f) :
    ∃ (j : J) (T' : CommRingCat.{u}) (f' : D.obj j ⟶ T') (g : T' ⟶ T),
      IsPushout (c.ι.app j) f' f g ∧ CommRingCat.localIso.{u} f' := by
  algebraize [f.hom]
  have hLI : Algebra.IsLocalIso (c.pt : Type u) (T : Type u) :=
    Algebra.isLocalIso_iff_locally.mpr hf
  obtain ⟨A, _, _, E, _, _, hft, hLI', ⟨e⟩⟩ :=
    exists_intermediate_isLocalIso (c.pt : Type u) (T : Type u)
  have : IsFinitelyPresentable.{u} (CommRingCat.of A) :=
    isFinitelyPresentable_of_finitePresentation _
      (Algebra.FinitePresentation.of_finiteType.mp hft)
  obtain ⟨j, ψ, hψ⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc
    (CommRingCat.ofHom (algebraMap A (c.pt : Type u)))
  have sq := isPushout_of_algEquiv_tensorProduct A
    (c.pt : Type u) E (T : Type u) e
  rw [← hψ] at sq
  refine ⟨j, _, _, _, IsPushout.of_left' sq (IsPushout.of_hasPushout ψ _), ?_⟩
  refine MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (IsPushout.of_hasPushout ψ (CommRingCat.ofHom (algebraMap A E))) ?_
  exact Algebra.isLocalIso_iff_locally.mp hLI'

/-! ## Composition of ind-Zariski ring maps -/

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The `R`-algebras of finite type over `R` are essentially small. -/
@[ega "IV 18.6.1" "partial"]
public alias CommRingCat.essentiallySmall_finiteType :=
  Stacks.AlgebraCategory.IndFactorization.essentiallySmall_finiteType

/-- The category `Under R` of `R`-algebras is finitely accessible: it has filtered colimits, and
the `R`-algebras of finite presentation over `R` form an essentially small family of finitely
presentable objects which generates `Under R` under filtered colimits. -/
public instance CommRingCat.isFinitelyAccessibleCategory_under (R : CommRingCat.{u}) :
    IsFinitelyAccessibleCategory.{u} (Under R) := by
  have : ObjectProperty.EssentiallySmall.{u}
      (fun B : Under R ↦ B.hom.hom.FinitePresentation) :=
    have := CommRingCat.essentiallySmall_finiteType R
    .of_le fun _ ↦ RingHom.FiniteType.of_finitePresentation
  have hBUF :=
    CommRingCat.isFiltered_costructuredArrow_and_isDenseAt_finitePresentation (R := R)
  have : (ObjectProperty.ι fun B : Under R ↦ B.hom.hom.FinitePresentation).IsDense :=
    ⟨fun A ↦ (hBUF A).2⟩
  have (A : Under R) : IsCardinalFiltered (CostructuredArrow
      (ObjectProperty.ι fun B : Under R ↦ B.hom.hom.FinitePresentation) A) Cardinal.aleph0 :=
    (isCardinalFiltered_aleph0_iff _).2 (hBUF A).1
  have hle : (fun B : Under R ↦ B.hom.hom.FinitePresentation) ≤
      isCardinalPresentable (Under R) Cardinal.aleph0 := by
    rw [← ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
    exact fun B hB ↦ ((CommRingCat.isFinitelyPresentable_under_tfae B).out 1 2).mp hB
  exact { toHasCardinalFilteredGenerator :=
    (CategoryTheory.IsCardinalFilteredGenerator.of_isDense_ι _ Cardinal.aleph0
      hle).hasCardinalFilteredGenerator }

/-- **Local isomorphisms spread out over filtered colimits**, as the `PreIndSpreads`
instance. -/
private instance : MorphismProperty.PreIndSpreads.{u} CommRingCat.localIso.{u} where
  exists_isPushout := by
    intro J _ _ D c hc T f hf
    exact exists_isPushout_localIso hc f hf

/-- A local isomorphism is a finitely presentable morphism. -/
lemma localIso_le_isFinitelyPresentable :
    CommRingCat.localIso.{u} ≤ MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} :=
  fun _ _ f hf ↦ CommRingCat.isFinitelyPresentable_hom f
    (RingHom.Locally.isStandardOpenImmersion_finitePresentation hf)

/-- **The composition of two ind-local-isomorphisms is an ind-local-isomorphism.** This is
Mathlib's `MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads` for the property of
being a local isomorphism: local isomorphisms are of finite presentation, stable under
composition and under cobase change, and they spread out. -/
private lemma ind_localIso_comp {X Y Z : CommRingCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : MorphismProperty.ind.{u} CommRingCat.localIso.{u} f)
    (hg : MorphismProperty.ind.{u} CommRingCat.localIso.{u} g) :
    MorphismProperty.ind.{u} CommRingCat.localIso.{u} (f ≫ g) := by
  have := CommRingCat.isFinitelyAccessibleCategory_under
  have := MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads
    (P := CommRingCat.localIso.{u}) localIso_le_isFinitelyPresentable
  exact MorphismProperty.comp_mem _ f g hf hg

/-! ## Ind-Zariski algebras, with the base and the algebra in independent universes -/

/-- Ind-Zariski-ness of an algebra is ind-local-isomorphism of its structure map. -/
private theorem ind_localIso_iff_ind_algebraMap {R Λ : Type u} [CommRing R] [CommRing Λ]
    [Algebra R Λ] :
    (CommAlgCat.localIso.{u, u} R).ind.{u} (CommAlgCat.of R Λ) ↔
      MorphismProperty.ind.{u} CommRingCat.localIso.{u}
        (CommRingCat.ofHom (algebraMap R Λ)) := by
  have hinv : (CommAlgCat.localIso.{u, u} R) = (CommRingCat.localIso.{u}).underObj.inverseImage
      (commAlgCatEquivUnder (CommRingCat.of R)).functor := by
    ext S
    show Algebra.IsLocalIso R S ↔
      RingHom.Locally RingHom.IsStandardOpenImmersion (algebraMap R S)
    exact Algebra.isLocalIso_iff_locally
  rw [MorphismProperty.ind_iff_ind_underMk,
    ← ObjectProperty.ind_iff_of_equivalence (CommRingCat.localIso.{u}).underObj
      (commAlgCatEquivUnder (CommRingCat.of R)) (Under.mk (CommRingCat.ofHom (algebraMap R Λ))),
    ← hinv]
  exact (ObjectProperty.ind.{u} (CommAlgCat.localIso.{u, u} R)).prop_iff_of_iso
    ((commAlgCatEquivUnder (CommRingCat.of R)).unitIso.app (CommAlgCat.of R Λ))

/-- Ind-Zariski-ness in the form of the factorization criterion of Lemma 07C3: every map into
`B` from a finitely presented `A`-algebra factors through a local isomorphism over `A`. Unlike
`(CommAlgCat.localIso A).ind`, this form does not mention the ambient category, which is what
makes it possible to change the universe. -/
private theorem ind_localIso_iff_factorization {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] :
    (CommAlgCat.localIso.{u, u} A).ind.{u} (CommAlgCat.of A B) ↔
      ∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra.FinitePresentation A C]
        (f : C →ₐ[A] B), ∃ (E : Type u) (_ : CommRing E) (_ : Algebra A E),
          Algebra.IsLocalIso A E ∧ ∃ (g : C →ₐ[A] E) (h : E →ₐ[A] B), h.comp g = f := by
  rw [ind_localIso_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk,
    CommRingCat.ind_under_iff_exists_factorization _ localIso_underObj_le_finitePresentation]
  constructor
  · intro H C _ _ _ f
    obtain ⟨E, g, h, he, hli⟩ := H
      (Under.mk (CommRingCat.ofHom (algebraMap A C)))
      (show (algebraMap A C).FinitePresentation from
        RingHom.finitePresentation_algebraMap.mpr inferInstance)
      (Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext x; exact f.commutes x))
    let _ := E.hom.hom.toAlgebra
    refine ⟨E.right, inferInstance, inferInstance,
      Algebra.isLocalIso_iff_locally.mpr hli,
      ⟨g.right.hom, fun x ↦ congr($(Under.w g).hom x)⟩,
      ⟨h.right.hom, fun x ↦ congr($(Under.w h).hom x)⟩, ?_⟩
    ext x
    exact congr($(congrArg Under.Hom.right he).hom x)
  · intro H C hC f
    let _ := C.hom.hom.toAlgebra
    let _ : Algebra.FinitePresentation A C.right :=
      RingHom.finitePresentation_algebraMap.mp hC
    obtain ⟨E, _, _, hli, g, h, he⟩ := H C.right
      ⟨f.right.hom, fun x ↦ congr($(Under.w f).hom x)⟩
    refine ⟨Under.mk (CommRingCat.ofHom (algebraMap A E)),
      Under.homMk (CommRingCat.ofHom g.toRingHom) (by ext x; exact g.commutes x),
      Under.homMk (CommRingCat.ofHom h.toRingHom) (by ext x; exact h.commutes x),
      ?_, show RingHom.Locally RingHom.IsStandardOpenImmersion (algebraMap A E) from
        Algebra.isLocalIso_iff_locally.mp hli⟩
    ext x
    exact AlgHom.congr_fun he x

/-- A local isomorphism stays one after transporting the base along a ring equivalence, in any
universes. -/
private theorem isLocalIso_changeBase {A : Type u} {A' : Type*} {E : Type*} [CommRing A]
    [CommRing A'] [CommRing E] [Algebra A E] [Algebra A' E] (eA : A ≃+* A')
    (he : ∀ a, algebraMap A E a = algebraMap A' E (eA a)) [Algebra.IsLocalIso A E] :
    Algebra.IsLocalIso A' E := by
  let _ : Algebra A' A := eA.symm.toRingHom.toAlgebra
  have h1 : Algebra.IsStandardOpenImmersion A' A :=
    Algebra.IsStandardOpenImmersion.of_bijective eA.symm.bijective
  have h2 : IsScalarTower A' A E := IsScalarTower.of_algebraMap_eq fun a' ↦ by
    show algebraMap A' E a' = algebraMap A E (eA.symm a')
    rw [he, eA.apply_symm_apply]
  exact Algebra.IsLocalIso.trans A' A E

/-- Ind-Zariski-ness of a fixed algebra is invariant under a ring equivalence of the base, the
universe of the algebra being untouched. -/
private theorem ind_localIso_changeScalars {A : Type u} {B : Type v} {T : Type w}
    [CommRing A] [CommRing B] [CommRing T] [Algebra A T] [Algebra B T]
    (e : A ≃+* B) (he : ∀ a, algebraMap A T a = algebraMap B T (e a))
    (hi : (CommAlgCat.localIso.{u, w} A).ind.{w} (CommAlgCat.of A T)) :
    (CommAlgCat.localIso.{v, w} B).ind.{w} (CommAlgCat.of B T) := by
  obtain ⟨J, _, _, pres, hp⟩ := hi
  let E := StacksDraft.commAlgChangeScalarsEquivalence.{u, v, w} e
  have ht : (CommAlgCat.localIso.{v, w} B).ind.{w} (E.functor.obj (CommAlgCat.of A T)) := by
    refine ⟨J, inferInstance, inferInstance, pres.map E.functor, fun j ↦ ?_⟩
    exact @isLocalIso_changeBase A B (pres.diag.obj j) _ _ _ (pres.diag.obj j).algebra
      ((StacksDraft.commAlgChangeScalars e).obj (pres.diag.obj j)).algebra e (fun a ↦ by
        show algebraMap A (pres.diag.obj j) a =
          algebraMap A (pres.diag.obj j) (e.symm (e a))
        rw [e.symm_apply_apply]) (hp j)
  refine (CommAlgCat.localIso.{v, w} B).ind.prop_of_iso ?_ ht
  exact @CommAlgCat.isoMk B _ (E.functor.obj (CommAlgCat.of A T)) T
    _ _ (E.functor.obj (CommAlgCat.of A T)).algebra _
    { toRingEquiv := RingEquiv.refl T
      commutes' := by
        intro b
        show algebraMap A T (e.symm b) = algebraMap B T b
        rw [he, e.apply_symm_apply] }

/-- Ind-Zariski-ness transports along a commuting square of ring equivalences, even when the two
sides live in different universes: the factorization criterion is checked after shrinking the
finitely presented test algebra, respectively the local isomorphism it factors through, into the
universe of the base. -/
private theorem isIndZariski_ofEquivAux {A B : Type u} {A' B' : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    [CommRing A'] [CommRing B'] [Algebra A' B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (he : ∀ a, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    (hi : (CommAlgCat.localIso.{u, u} A).ind.{u} (CommAlgCat.of A B)) :
    (CommAlgCat.localIso.{v, v} A').ind.{v} (CommAlgCat.of A' B') := by
  classical
  rw [ind_localIso_iff_factorization] at hi ⊢
  intro C _ _ _ f
  let _ : Algebra A C := ((algebraMap A' C).comp eA.toRingHom).toAlgebra
  have hfp : Algebra.FinitePresentation A C :=
    RingHom.finitePresentation_algebraMap.mp <| RingHom.FinitePresentation.comp
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
      (RingHom.FinitePresentation.of_bijective eA.bijective)
  let _ : Small.{u} C := Algebra.FiniteType.small (R := A) (S := C)
  let eC : Shrink.{u} C ≃ₐ[A] C := Shrink.algEquiv A C
  let f' : Shrink.{u} C →ₐ[A] B :=
    { toRingHom := eB.symm.toRingHom.comp (f.toRingHom.comp eC.toRingEquiv.toRingHom)
      commutes' := by
        intro a
        show eB.symm (f (eC (algebraMap A (Shrink C) a))) = _
        rw [eC.commutes]
        show eB.symm (f (algebraMap A' C (eA a))) = _
        rw [f.commutes, ← he, eB.symm_apply_apply] }
  let _ : Algebra.FinitePresentation A (Shrink.{u} C) :=
    Algebra.FinitePresentation.equiv eC.symm
  obtain ⟨E, _, _, hli, g, h, hgh⟩ := hi _ f'
  let _ : Algebra A' E := ((algebraMap A E).comp eA.symm.toRingHom).toAlgebra
  have hli' : Algebra.IsLocalIso A' E := isLocalIso_changeBase eA (fun a ↦ by
    show algebraMap A E a = algebraMap A E (eA.symm (eA a))
    rw [eA.symm_apply_apply])
  let _ : Algebra A' A := eA.symm.toRingHom.toAlgebra
  have htower : IsScalarTower A' A E := IsScalarTower.of_algebraMap_eq' rfl
  have hftA' : Algebra.FiniteType A' A :=
    RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_surjective _ eA.symm.surjective)
  have hftA'E : Algebra.FiniteType A' E := Algebra.FiniteType.trans hftA' inferInstance
  let _ : Small.{v} E := Algebra.FiniteType.small (R := A') (S := E)
  let eE : Shrink.{v} E ≃ₐ[A'] E := Shrink.algEquiv A' E
  have hliE : Algebra.IsLocalIso A' (Shrink.{v} E) := Algebra.IsLocalIso.of_algEquiv eE.symm
  refine ⟨Shrink.{v} E, inferInstance, inferInstance, hliE,
    { toRingHom := eE.symm.toRingEquiv.toRingHom.comp
        (g.toRingHom.comp eC.symm.toRingEquiv.toRingHom)
      commutes' := ?_ },
    { toRingHom := eB.toRingHom.comp (h.toRingHom.comp eE.toRingEquiv.toRingHom)
      commutes' := ?_ }, ?_⟩
  · intro a
    apply eE.injective
    show eE (eE.symm (g (eC.symm (algebraMap A' C a)))) = _
    rw [eE.apply_symm_apply, eE.commutes]
    have hc : algebraMap A' C a = algebraMap A C (eA.symm a) := by
      show _ = algebraMap A' C (eA (eA.symm a))
      rw [eA.apply_symm_apply]
    rw [hc, eC.symm.commutes, g.commutes]
    rfl
  · intro a
    show eB (h (eE (algebraMap A' (Shrink E) a))) = _
    rw [eE.commutes]
    show eB (h (algebraMap A E (eA.symm a))) = _
    rw [h.commutes, he, eA.apply_symm_apply]
  · ext c
    show eB (h (eE (eE.symm (g (eC.symm c))))) = f c
    rw [eE.apply_symm_apply, ← AlgHom.comp_apply, hgh]
    show eB (eB.symm (f (eC (eC.symm c)))) = f c
    rw [eC.apply_symm_apply, eB.apply_symm_apply]

/-- Ind-Zariski-ness of `A → B` is ind-Zariski-ness of the fully lifted map `ULift A → ULift B`,
which lives in a single universe. -/
private theorem isIndZariski_iff_lift {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] :
    Algebra.IsIndZariski A B ↔
      let _ : Algebra (ULift.{v} A) (ULift.{u} B) := ULift.algebra' A _
      (CommAlgCat.localIso.{max u v, max u v} (ULift.{v} A)).ind.{max u v}
        (CommAlgCat.of (ULift.{v} A) (ULift.{u} B)) := by
  let _ : Algebra (ULift.{v} A) (ULift.{u} B) := ULift.algebra' A _
  exact ⟨ind_localIso_changeScalars ULift.ringEquiv.symm (fun _ ↦ rfl),
    ind_localIso_changeScalars ULift.ringEquiv (fun _ ↦ rfl)⟩

attribute [local instance] ULift.algebra' in
/-- **Ind-Zariski-ness transports along a commuting square of ring equivalences**, with all four
universes independent. -/
theorem Algebra.IsIndZariski.of_equiv {A B A' B' : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [CommRing A'] [CommRing B'] [Algebra A' B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (he : ∀ a, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    (hi : Algebra.IsIndZariski A B) : Algebra.IsIndZariski A' B' := by
  rw [isIndZariski_iff_lift] at hi ⊢
  exact isIndZariski_ofEquivAux
    (ULift.ringEquiv.trans (eA.trans ULift.ringEquiv.symm))
    (ULift.ringEquiv.trans (eB.trans ULift.ringEquiv.symm))
    (fun a ↦ ULift.ext (he a.down)) hi

/-- The composition of two ind-Zariski algebra maps, in a single universe. -/
private theorem commAlgCat_ind_localIso_comp {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hB : (CommAlgCat.localIso.{u, u} A).ind.{u} (CommAlgCat.of A B))
    (hC : (CommAlgCat.localIso.{u, u} B).ind.{u} (CommAlgCat.of B C)) :
    (CommAlgCat.localIso.{u, u} A).ind.{u} (CommAlgCat.of A C) := by
  rw [ind_localIso_iff_ind_algebraMap] at hB hC ⊢
  rw [show CommRingCat.ofHom (algebraMap A C) =
      CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom (algebraMap B C) from by
    ext x; exact IsScalarTower.algebraMap_apply A B C x]
  exact ind_localIso_comp _ _ hB hC

attribute [local instance] ULift.algebra' in
/-- **Stacks 096Q.** If `B` is ind-Zariski over `A` and `C` is ind-Zariski over `B`, then `C` is
ind-Zariski over `A`. -/
@[stacks 096Q]
theorem Algebra.IsIndZariski.comp (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : Algebra.IsIndZariski A B) (hBC : Algebra.IsIndZariski B C) :
    Algebra.IsIndZariski A C := by
  have hb : Algebra.IsIndZariski (ULift.{max v w} A) (ULift.{max u w} B) :=
    Algebra.IsIndZariski.of_equiv ULift.ringEquiv.symm ULift.ringEquiv.symm (fun _ ↦ rfl) hAB
  have hc : Algebra.IsIndZariski (ULift.{max u w} B) (ULift.{max u v} C) :=
    Algebra.IsIndZariski.of_equiv ULift.ringEquiv.symm ULift.ringEquiv.symm (fun _ ↦ rfl) hBC
  have hac : Algebra.IsIndZariski (ULift.{max v w} A) (ULift.{max u v} C) :=
    Algebra.isIndZariski_iff.mpr
      (commAlgCat_ind_localIso_comp (Algebra.isIndZariski_iff.mp hb)
        (Algebra.isIndZariski_iff.mp hc))
  exact Algebra.IsIndZariski.of_equiv ULift.ringEquiv ULift.ringEquiv (fun _ ↦ rfl) hac

/-- With the base and the algebra in one universe, an algebra is ind-Zariski exactly when its
structure map is an ind-local-isomorphism of commutative rings. This is the form in which the
permanence properties of `CommRingCat.localIso` — stability under composition and under cobase
change — apply to ind-Zariski algebras. -/
theorem Algebra.isIndZariski_iff_ind_localIso {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] :
    Algebra.IsIndZariski A B ↔
      MorphismProperty.ind.{u} CommRingCat.localIso.{u}
        (CommRingCat.ofHom (algebraMap A B)) :=
  Algebra.isIndZariski_iff.trans ind_localIso_iff_ind_algebraMap

end
