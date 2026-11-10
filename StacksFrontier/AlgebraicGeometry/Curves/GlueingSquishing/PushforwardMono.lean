module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic

/-!
# `𝒪_Y ⊂ f_*𝒪_X` from injectivity on an affine open cover

Let `f : X ⟶ Y` be an affine morphism of schemes. The inclusion `𝒪_Y ⊂ f_*𝒪_X` of
[Stacks, Tag 0C1L] — a monomorphism in the sheaves of commutative rings on `Y` — is a condition
on the sections over *every* open of `Y`, while the hypotheses one has in practice say something
about the sections over a *cover*. The passage from one to the other is this file: for an affine
morphism it is enough to know that `f.app U` is injective for one affine open `U` around each
point of `Y`.

A cover is not a basis, so the passage is not formal. What makes it work is that the sections
over a basic open `D(a)` of an affine open `U` are a localisation of the sections over `U`, on
both sides of `f`, and that localisation is exact: injectivity of `Γ(Y, U) ⟶ Γ(X, f⁻¹U)` is
inherited by `Γ(Y, D(a)) ⟶ Γ(X, f⁻¹D(a))`, and the basic opens of the members of an affine open
cover *do* form a basis.

## Main results

* `Stacks.GlueSquishFactor.injective_of_isLocalization_away` — the commutative algebra: a square
  of localisations away from `a` and from `g a` over an injective `g` has injective top edge.
* `Stacks.GlueSquishFactor.map_eq_zero_of_map_app_eq_zero` — `𝒪_Y ⊂ f_*𝒪_X` read on germs: a
  section whose image dies on the preimage of a smaller open already dies there. This is the
  injectivity clause of `AlgebraicGeometry.IsGlueingTwoPoints`.
* `Stacks.GlueSquishFactor.injective_app_basicOpen` — injectivity of `f.app U` for an affine `U`
  with affine preimage passes to the basic opens of `U`.
* `Stacks.GlueSquishFactor.injective_app_of_locally` — injectivity of `f.app` is local on the
  target: if every point of every open `W` has a neighbourhood inside `W` on which `f.app` is
  injective, then `f.app W` is injective.
* `Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_of_injective_app` — **the criterion**:
  for an affine morphism `f`, injectivity of `f.app U` for one affine open `U` around each point
  of the target gives `𝒪_Y ⊂ f_*𝒪_X`.
* `Stacks.GlueSquishFactor.injective_app_of_mono_hom_pushforwardAlgebra` — **the converse**:
  `𝒪_Y ⊂ f_*𝒪_X` gives injectivity of `f.app W` for *every* open `W`, for an arbitrary morphism
  `f`. This is what reads the clause `Mono (pushforwardAlgebra f).hom` of
  `Stacks.GlueSquishFactor.IsAlmostIso` as the sectionwise hypothesis its consumers ask for.

## Implementation notes

**Why the basic opens.** `Stacks.GlueSquishFactor.injective_app_basicOpen` is stated for an
affine open `U` whose preimage is affine, which for an affine morphism is every affine open. The
two localisations are `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen` applied to `U`
and to `f ⁻¹ᵁ U`, and they match up because `f ⁻¹ᵁ Y.basicOpen a = X.basicOpen (f.app U a)`
(`AlgebraicGeometry.Scheme.preimage_basicOpen`). That equality is used as an inequality rather
than rewritten: the conclusion is first proved for
`Scheme.Hom.appLE f (Y.basicOpen a) (X.basicOpen (f.app U a))`, whose codomain is literally the
basic open carrying the localisation instance, and then `f.app (Y.basicOpen a)` is recovered as
its left factor. Rewriting along the equality instead would ask Lean to transport the `Algebra`
instance on the sections of a basic open, which is not stated for a general open.

**The commuting square.** `Stacks.GlueSquishFactor.map_comp_appLE` is the naturality of `f.c` in
the shape the localisation lemma consumes, with all three opens abstract so that the rewrite of
`Scheme.Hom.appLE_eq_app` has no dependent occurrences to trip over.

**Monomorphisms of sheaves of rings.** `Mono` in `TopCat.Sheaf CommRingCat Y` is obtained from
`Mono` of the underlying morphism of presheaves, because `TopCat.Sheaf.forget` is faithful and a
faithful functor reflects monomorphisms; `Mono` of a morphism of presheaves follows from `Mono`
of each of its components, and `Mono` in `CommRingCat` from injectivity. So the whole statement
really is "injective on the sections over every open", and that is what is proved.

Each of those three steps is reversible, which is
`Stacks.GlueSquishFactor.injective_app_of_mono_hom_pushforwardAlgebra`: `TopCat.Sheaf.forget`
*creates* limits over a category with limits, evaluation at an open preserves them because
limits of presheaves are computed objectwise, and the forgetful functor of `CommRingCat`
preserves them too, so all three preserve pullbacks and hence monomorphisms. The direction
proved here is the one that needs the geometry — a cover is not a basis — and the direction
proved there is formal.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GlueSquishFactor

/-! ### Localisation is exact -/

/-- **Injectivity passes to a localisation.** Let `g : R →+* P` be injective, let `S` be a
localisation of `R` away from `a` and `Q` a localisation of `P` away from `g a`, and let
`φ : S →+* Q` extend `g`. Then `φ` is injective.

An element of `S` killed by `φ` is `r / aⁿ` for some `r : R`; its image is `g r / (g a)ⁿ`, so
`(g a)ᵐ * g r = 0` for some `m`, that is `g (aᵐ * r) = 0`, so `aᵐ * r = 0`; since `aᵐ` becomes a
unit in `S` this forces `r` to die in `S`, hence the element to vanish. -/
theorem injective_of_isLocalization_away {R S P Q : Type*} [CommRing R] [CommRing S]
    [CommRing P] [CommRing Q] [Algebra R S] [Algebra P Q] (a : R)
    [IsLocalization.Away a S] (g : R →+* P) [IsLocalization.Away (g a) Q]
    (φ : S →+* Q) (hcomm : ∀ r : R, φ (algebraMap R S r) = algebraMap P Q (g r))
    (hg : Function.Injective g) : Function.Injective φ := by
  have hua : IsUnit (algebraMap R S a) := IsLocalization.map_units S ⟨a, Submonoid.mem_powers a⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, ⟨b, hb⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers a) x
  have h1 : algebraMap P Q (g r) = 0 := by
    rw [← hcomm, ← hr, map_mul, hx, zero_mul]
  obtain ⟨⟨c, m, hm⟩, hc2⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (g a)) Q (g r)).mp h1
  have hm' : g a ^ m = c := hm
  have hgz : g (a ^ m * r) = 0 := by
    rw [map_mul, map_pow, hm']; exact hc2
  have h3 : a ^ m * r = 0 := hg (by rw [hgz, map_zero])
  have hu : IsUnit (algebraMap R S (a ^ m)) := by rw [map_pow]; exact hua.pow m
  have h4 : algebraMap R S r = 0 :=
    hu.mul_right_eq_zero.mp (by rw [← map_mul, h3, map_zero])
  have hub : IsUnit (algebraMap R S b) := IsLocalization.map_units S ⟨b, hb⟩
  rw [h4] at hr
  exact hub.mul_left_eq_zero.mp hr

/-! ### Naturality of the maps on sections -/

/-- Restricting on the target and then taking sections over a smaller open of the source is
taking sections over the larger open of the target and then restricting on the source: the
naturality of `f.c`, written with `Scheme.Hom.appLE`. -/
theorem map_comp_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} {W : X.Opens}
    (hVU : V ≤ U) (hW : W ≤ f ⁻¹ᵁ V) (hW' : W ≤ f ⁻¹ᵁ U) :
    Y.presheaf.map (homOfLE hVU).op ≫ f.appLE V W hW
      = f.app U ≫ X.presheaf.map (homOfLE hW').op := by
  rw [Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_eq_app (f := f) (U := U), Scheme.Hom.appLE_map]

/-- The naturality of `f.c` between the sections over an open of the target and over a smaller
one. -/
theorem map_comp_app {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U) :
    Y.presheaf.map (homOfLE hVU).op ≫ f.app V
      = f.app U ≫ X.presheaf.map (homOfLE (fun _ hx => hVU hx :
        f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U)).op := by
  have h := map_comp_appLE f hVU (le_rfl : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V)
    (fun _ hx => hVU hx : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U)
  rwa [Scheme.Hom.appLE_eq_app] at h

/-- `f.app` commutes with restriction, on elements. -/
private theorem app_restrict_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U)
    (s : Γ(Y, U)) :
    (f.app V).hom ((Y.presheaf.map (homOfLE hVU).op).hom s)
      = (X.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom ((f.app U).hom s) :=
  congrArg (fun t : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ V) => t.hom s) (map_comp_app f hVU)

/-- **`𝒪_Y ⊂ f_*𝒪_X` read on germs.** If `f.app` is injective on the sections over every open
and a section `s` of `𝒪_Y` over `U` has `f.app U s` restricting to `0` on `f ⁻¹ᵁ V` for some
`V ≤ U`, then `s` already restricts to `0` on `V`.

This is the *injectivity* clause of `AlgebraicGeometry.IsGlueingTwoPoints` — the left-hand end
of the short exact sequence `0 → 𝒪_X → f_*𝒪_{X'} → x_*k → 0` written in germ-local form — for
the morphism of that predicate: the clause asks for *some* open around the glued point on which
`s` vanishes, and this lemma returns the given `V`, so no shrinking is needed and the point plays
no role. It is therefore the one germ-level clause of the predicate which follows from the
hypothesis `𝒪_X ⊂ f_*𝒪_{X'}` of [Stacks, Tag 0C1L] alone, with no reference to the fibre: the
restriction of `f.app U s` to `f ⁻¹ᵁ V` is `f.app V` of the restriction of `s`
(`Stacks.GlueSquishFactor.map_comp_app`), and `f.app V` is injective. -/
theorem map_eq_zero_of_map_app_eq_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hinj : ∀ W : Y.Opens, Function.Injective (f.app W).hom) {U V : Y.Opens} (hVU : V ≤ U)
    (s : Γ(Y, U))
    (hs : (X.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom ((f.app U).hom s) = 0) :
    (Y.presheaf.map (homOfLE hVU).op).hom s = 0 := by
  refine hinj V ?_
  rw [app_restrict_apply, hs, map_zero]

/-! ### From an affine open to its basic opens -/

/-- **Injectivity on sections passes to the basic opens of an affine open.** If `U` and
`f ⁻¹ᵁ U` are affine and `f.app U` is injective, then `f.app (Y.basicOpen a)` is injective for
every section `a` of `𝒪_Y` over `U`.

Both sides are localisations — of `Γ(Y, U)` away from `a` and of `Γ(X, f ⁻¹ᵁ U)` away from
`f.app U a` — and the preimage of `Y.basicOpen a` is the basic open of `f.app U a`, so this is
exactness of localisation. -/
theorem injective_app_basicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (hfU : IsAffineOpen (f ⁻¹ᵁ U))
    (hinj : Function.Injective (f.app U).hom) (a : Γ(Y, U)) :
    Function.Injective (f.app (Y.basicOpen a)).hom := by
  have hpre : f ⁻¹ᵁ Y.basicOpen a = X.basicOpen ((f.app U).hom a) :=
    Scheme.preimage_basicOpen f a
  have e : X.basicOpen ((f.app U).hom a) ≤ f ⁻¹ᵁ Y.basicOpen a := le_of_eq hpre.symm
  have : IsLocalization.Away a Γ(Y, Y.basicOpen a) := hU.isLocalization_basicOpen a
  have : IsLocalization.Away ((f.app U).hom a) Γ(X, X.basicOpen ((f.app U).hom a)) :=
    hfU.isLocalization_basicOpen _
  have hsq := map_comp_appLE f (Y.basicOpen_le a) e (X.basicOpen_le ((f.app U).hom a))
  have key : Function.Injective
      (f.appLE (Y.basicOpen a) (X.basicOpen ((f.app U).hom a)) e).hom :=
    injective_of_isLocalization_away a (f.app U).hom _
      (fun r => congrArg (fun t : Γ(Y, U) ⟶ _ => t.hom r) hsq) hinj
  have hcomp : ⇑(f.appLE (Y.basicOpen a) (X.basicOpen ((f.app U).hom a)) e).hom
      = ⇑(X.presheaf.map (homOfLE e).op).hom ∘ ⇑(f.app (Y.basicOpen a)).hom := rfl
  rw [hcomp] at key
  exact key.of_comp

/-! ### Injectivity on sections is local on the target -/

/-- **Injectivity on sections is local on the target.** If every point of every open `W` of the
target has a neighbourhood inside `W` on which `f.app` is injective, then `f.app W` is injective
for every `W`.

Two sections of `𝒪_Y` over `W` with the same image agree on each such neighbourhood, hence have
the same germ at each point of `W`, hence are equal because `𝒪_Y` is a sheaf. -/
theorem injective_app_of_locally {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (W : Y.Opens) (y : Y), y ∈ W → ∃ V : Y.Opens, ∃ _ : V ≤ W, y ∈ V ∧
      Function.Injective (f.app V).hom) (W : Y.Opens) :
    Function.Injective (f.app W).hom := by
  intro s t hst
  refine TopCat.Presheaf.section_ext Y.sheaf W s t fun y hy => ?_
  change (Y.presheaf.germ W y hy).hom s = (Y.presheaf.germ W y hy).hom t
  obtain ⟨V, hVW, hyV, hinj⟩ := h W y hy
  have hres : (Y.presheaf.map (homOfLE hVW).op).hom s
      = (Y.presheaf.map (homOfLE hVW).op).hom t := by
    refine hinj ?_
    rw [app_restrict_apply, app_restrict_apply, hst]
  have e : ∀ x : Γ(Y, W), (Y.presheaf.germ V y hyV).hom ((Y.presheaf.map (homOfLE hVW).op).hom x)
      = (Y.presheaf.germ W y hy).hom x := fun x => Y.presheaf.germ_res_apply _ _ _ _
  rw [← e, ← e, hres]

/-! ### The criterion for `𝒪_Y ⊂ f_*𝒪_X` -/

/-- **`𝒪_Y ⊂ f_*𝒪_X` from an affine open cover.** Let `f : X ⟶ Y` be an affine morphism such
that every point of `Y` has an affine open neighbourhood `U` with `f.app U` injective. Then
`𝒪_Y ⟶ f_*𝒪_X` is a monomorphism.

This is the inclusion `𝒪_Y ⊂ f_*𝒪_X` of [Stacks, Tag 0C1L] deduced from a cover rather than
from a basis: the basic opens of the neighbourhoods `U` form a basis of `Y`, and injectivity
passes to them by exactness of localisation. -/
theorem mono_hom_pushforwardAlgebra_of_injective_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f]
    (h : ∀ y : Y, ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U ∧
      Function.Injective (f.app U).hom) :
    Mono (pushforwardAlgebra f).hom := by
  have key : ∀ W : Y.Opens, Function.Injective (f.app W).hom := by
    refine injective_app_of_locally f fun W y hy => ?_
    obtain ⟨U, hU, hyU, hinj⟩ := h y
    obtain ⟨a, hle, hya⟩ := hU.exists_basicOpen_le (V := U ⊓ W) ⟨y, ⟨hyU, hy⟩⟩ hyU
    exact ⟨Y.basicOpen a, hle.trans inf_le_right, hya,
      injective_app_basicOpen f hU (hU.preimage f) hinj a⟩
  refine (TopCat.Sheaf.forget CommRingCat.{u} Y.toTopCat).mono_of_mono_map ?_
  exact @NatTrans.mono_of_mono_app _ _ _ _ _ _ _
    (fun W => ConcreteCategory.mono_of_injective _ (key W.unop))

/-! ### From `𝒪_Y ⊂ f_*𝒪_X` back to the sections -/

/-- **`𝒪_Y ⊂ f_*𝒪_X` read on the sections over every open.** If `𝒪_Y ⟶ f_*𝒪_X` is a
monomorphism then `f.app W` is injective for every open `W` of `Y`.

This is the converse of `Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_of_injective_app`,
and it needs nothing of `f`: not affineness, not finiteness. It is what connects the clause
`Mono (pushforwardAlgebra f).hom` of `Stacks.GlueSquishFactor.IsAlmostIso` — the form in which
the hypothesis `𝒪_X ⊂ f_*𝒪_{X'}` of [Stacks, Tag 0C1L] is carried through the
relative-spectrum dictionary — to the sectionwise injectivity that the germ-level clauses of
`AlgebraicGeometry.IsGlueingTwoPoints` are proved from, e.g. the hypothesis `hinj` of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_fibre_algEquiv_prod` and the hypothesis
`hψ` of `Stacks.GlueSquishFactor.exists_split_of_algebraHom`.

The three steps are the three steps of the implementation notes read backwards: sections of
sheaves of commutative rings over a fixed open are the composite of
`TopCat.Sheaf.forget`, which creates limits, with evaluation at that open, so each step
preserves pullbacks and hence monomorphisms, and a monomorphism of `CommRingCat` is injective
because the forgetful functor preserves pullbacks. -/
theorem injective_app_of_mono_hom_pushforwardAlgebra {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : Mono (pushforwardAlgebra f).hom) (W : Y.Opens) :
    Function.Injective (f.app W).hom := by
  have := h
  have : Mono ((TopCat.Sheaf.forget CommRingCat.{u} Y.toTopCat).map
      (pushforwardAlgebra f).hom) :=
    (TopCat.Sheaf.forget CommRingCat.{u} Y.toTopCat).map_mono _
  have : Mono (f.app W) :=
    inferInstanceAs (Mono (((TopCat.Sheaf.forget CommRingCat.{u} Y.toTopCat).map
      (pushforwardAlgebra f).hom).app (op W)))
  exact CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback (f.app W)

end Stacks.GlueSquishFactor

end
