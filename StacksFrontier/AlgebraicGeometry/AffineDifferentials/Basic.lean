module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative

/-!
# Sections of the relative differentials on an open where the base is affine

Let `f : X ⟶ S` be a morphism of schemes, let `V` be an open of `S` and let `U ≤ f ⁻¹ᵁ V` be an
open of `X`, so that `f` induces a ring map `Γ(S, V) ⟶ Γ(X, U)`. This file constructs the
canonical comparison

`Ω_{Γ(X, U) / Γ(S, V)} ⟶ Γ(Ω_{X/S}, U)`,

shows that it is characterized by carrying the ring-theoretic universal derivation to the
universal relative derivation, and shows that Stacks 01UT — the assertion that for `U` and `V`
affine the sections of `Ω_{X/S}` on `U` are *uniquely* isomorphic to those Kähler differentials,
compatibly with the universal derivations — holds exactly when this one map is an isomorphism.

## Main definitions

* `comorphismDerivation` reads a derivation relative to the inverse image of the structure
  sheaf of the base as a derivation relative to the comorphism of `f`.
* `sectionsDerivation` is the universal relative derivation, read on an open `U ≤ f ⁻¹ᵁ V` as a
  ring-theoretic derivation of `Γ(X, U)` over `Γ(S, V)`.
* `kaehlerToSections` is the induced map from the Kähler differentials of `Γ(S, V) ⟶ Γ(X, U)`
  to the sections of `Ω_{X/S}` on `U`.

## Main results

* `d_appLE_eq_zero`: a relative derivation annihilates the image of `Γ(S, V)` in `Γ(X, U)`.
* `kaehlerToSections_d` computes the comparison on the universal differential of a section.
* `iso_unique`: at most one isomorphism `Γ(Ω_{X/S}, U) ≅ Ω_{Γ(X, U) / Γ(S, V)}` carries the
  universal relative derivation to the ring-theoretic one. This is the uniqueness half of
  Stacks 01UT, and it needs neither `U` nor `V` to be affine.
* `existsUnique_affineDifferentialsIso_iff_isIso`: that unique-existence statement is
  equivalent to `kaehlerToSections` being an isomorphism.

## Implementation notes

The route is the universal property of Kähler differentials, in its `CommRingCat` packaging:
`Γ(Ω_{X/S}, U)` is a module over `Γ(X, U)`, and the universal relative derivation of `f`
provides, on the single open `U`, an additive Leibniz map `Γ(X, U) → Γ(Ω_{X/S}, U)`. The one
thing that has to be checked is that this map annihilates the image of `Γ(S, V)`. The relative
derivation of `f` is by definition a derivation relative to the structural map
`f⁻¹ 𝒪_S ⟶ 𝒪_X`, whose vanishing condition is stated on sections of the inverse image sheaf —
a sheafified colimit, so its sections are not directly computable. The vanishing condition on
the comorphism `f.c` is the usable one, and the two are interchanged by the very adjunction
that defines the structural map: transposing back gives the comorphism, which is
`comorphismDerivation`. The Leibniz and restriction-compatibility data are carried over
unchanged, so this costs only the transposition. With the vanishing condition in hand,
`Γ(S, V)` is annihilated because `f.appLE` is the comorphism on `V` followed by a restriction,
and a relative derivation commutes with restriction.

The comparison itself is then Mathlib's `ModuleCat.Derivation.desc`, and both the uniqueness
half and the reduction to an isomorphism come from the fact that the universal differentials
generate: `CommRingCat.KaehlerDifferential.ext`.

The Kähler differentials are spelled `CommRingCat.KaehlerDifferential (f.appLE V U hUV)`. That
is by definition `ModuleCat.of Γ(X, U) Ω[Γ(X, U)⁄Γ(S, V)]` for the algebra structure obtained
from the ring map, and its universal differential is the ring-theoretic one; so this is the
same object as the pair consisting of the carrier and derivation of the module of
differentials of `Γ(S, V) → Γ(X, U)`.

Everything is in a single universe: the schemes are in `Scheme.{u}`, and `X.Modules` is
`SheafOfModules.{u} X.ringCatSheaf`, so the sections on an open live in `ModuleCat.{u}`. No
universe-polymorphic coefficient module is used, and no universe side condition arises.

Three transparency points. First, `comorphismDerivation` is a definition, so
the equality of its underlying additive map with the given one does not hold by instance-level
unfolding; it is recorded as the separate `rfl` lemma `comorphismDerivation_d` and rewritten
explicitly, and a hypothesis introduced by `have` is already too opaque for even that. Second,
the carrier of `Γ(Ω_{X/S}, U)` is reached through the `RingCat` spelling of the structure sheaf
while the Kähler differentials are built over the `CommRingCat` spelling, so the two zeros of
that module come by different instance paths and the closing step of `d_appLE_eq_zero` is a
definitional check rather than a rewrite. Third, and the reason the uniqueness arguments are
written in term mode out of `congrArg` and `Eq.trans` rather than with `rw`: both `TopCat.Sheaf`
and `AlgebraicGeometry.Scheme.Modules` are definitions, so a goal mentioning
`(relativeDifferentials f).val.obj (.op U)` is not type-correct at implicit transparency and
rewriting inside it fails to find patterns that are plainly displayed in the goal. Marking
those two definitions locally implicit-reducible moves the failure rather than removing it
(`Scheme.presheaf` is next), while term-level `congrArg` needs only default transparency and
goes through unchanged.

## What is not done here

Stacks 01UT itself is not proved: `kaehlerToSections` is not shown to be an isomorphism, and
that is exactly the affine content of the tag. The three declarations that the remaining
implication needs are absent from this library at the time of writing: the restriction
comparison for relative differentials (Stacks 01US), the quasi-coherence of `Ω_{X/S}` (Stacks
08S2 together with 01R2), and the global-sections form of Stacks 01UO, which would need a
relative derivation to be *constructed* from ring data and therefore needs the vanishing
condition on the inverse image sheaf in the direction opposite to the one established here.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
* [Stacks Project, Tag 00RO](https://stacks.math.columbia.edu/tag/00RO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineDifferentials

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Reading a relative derivation along the comorphism -/

/-- A derivation of the structure sheaf of `X` relative to the inverse image of the structure
sheaf of `S`, read as a derivation relative to the comorphism of `f`. The underlying additive
maps and the Leibniz and restriction-compatibility data are unchanged; only the vanishing
condition is transported, across the adjunction defining the structural map. -/
noncomputable def comorphismDerivation (M : X.Modules)
    (D : SheafOfModules.SheafDerivation (inverseImageStructureMap f) M) :
    PresheafOfModulesOfCommRing.Derivation M.val f.c := by
  refine { d := D.d, d_mul := D.d_mul, d_map := D.d_map, d_app := fun {V} a => ?_ }
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base
  let fc : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf := ⟨f.c⟩
  have hfc : adj.homEquiv S.sheaf X.sheaf (inverseImageStructureMap f) = fc :=
    (adj.homEquiv S.sheaf X.sheaf).apply_symm_apply fc
  change D.d ((fc.hom.app V).hom a) = 0
  rw [← hfc, adj.homEquiv_unit]
  exact D.d_app (((adj.unit.app S.sheaf).hom.app V).hom a)

/-- Reading a relative derivation along the comorphism does not change its underlying additive
map on an open. -/
theorem comorphismDerivation_d (M : X.Modules)
    (D : SheafOfModules.SheafDerivation (inverseImageStructureMap f) M) (U : X.Opens) :
    (comorphismDerivation f M D).d (X := .op U) = D.d := rfl

/-- A derivation of the structure sheaf of `X` relative to the inverse image of the structure
sheaf of `S` annihilates the image of `Γ(S, V)` in `Γ(X, U)`, for every open `U ≤ f ⁻¹ᵁ V`. -/
theorem d_appLE_eq_zero (M : X.Modules)
    (D : SheafOfModules.SheafDerivation (inverseImageStructureMap f) M)
    (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (r : Γ(S, V)) :
    D.d ((f.appLE V U hUV).hom r) = 0 := by
  have h0 : D.d ((f.app V).hom r) = 0 := by
    rw [← comorphismDerivation_d f M D (f ⁻¹ᵁ V)]
    exact (comorphismDerivation f M D).d_app (X := .op V) r
  have h1 : D.d ((X.presheaf.map (homOfLE hUV).op).hom ((f.app V).hom r)) =
      M.val.map (homOfLE hUV).op (D.d ((f.app V).hom r)) := by
    rw [← comorphismDerivation_d f M D U, ← comorphismDerivation_d f M D (f ⁻¹ᵁ V)]
    exact (comorphismDerivation f M D).d_map (homOfLE hUV).op _
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, h1, h0, map_zero]
  rfl

/-! ### The comparison with the Kähler differentials of the sections -/

variable (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)

/-- The universal relative derivation of `f`, read on an open `U ≤ f ⁻¹ᵁ V` as a derivation of
`Γ(X, U)` relative to the ring map `Γ(S, V) ⟶ Γ(X, U)` induced by `f`. -/
noncomputable def sectionsDerivation :
    ((Scheme.Hom.relativeDifferentials f).val.obj (.op U)).Derivation (f.appLE V U hUV) :=
  ModuleCat.Derivation.mk (fun a => (Scheme.Hom.universalRelativeDerivation f).d a)
    (fun a b => map_add _ a b)
    (fun a b => (Scheme.Hom.universalRelativeDerivation f).d_mul a b)
    (fun r => d_appLE_eq_zero f _ (Scheme.Hom.universalRelativeDerivation f) V U hUV r)

/-- The canonical map from the Kähler differentials of `Γ(S, V) ⟶ Γ(X, U)` to the sections of
the sheaf of relative differentials of `f` on `U`, for any open `U ≤ f ⁻¹ᵁ V`. -/
noncomputable def kaehlerToSections :
    CommRingCat.KaehlerDifferential (f.appLE V U hUV) ⟶
      (Scheme.Hom.relativeDifferentials f).val.obj (.op U) :=
  (sectionsDerivation f V U hUV).desc

/-- The canonical map carries the universal differential of a section of the structure sheaf to
the universal relative differential of that section. -/
theorem kaehlerToSections_d (a : Γ(X, U)) :
    (kaehlerToSections f V U hUV).hom (CommRingCat.KaehlerDifferential.d a) =
      (Scheme.Hom.universalRelativeDerivation f).d a :=
  (sectionsDerivation f V U hUV).desc_d a

/-! ### Uniqueness, and the reduction of Stacks 01UT to one isomorphism -/

/-- If `g ≫ h = 𝟙` and `g x = y`, then `h y = x`. -/
private theorem hom_apply_eq_of_comp_eq_id {R : Type*} [Ring R] {A B : ModuleCat R}
    {g : A ⟶ B} {h : B ⟶ A} (hgh : g ≫ h = 𝟙 A) {x : A} {y : B} (hx : g.hom x = y) :
    h.hom y = x :=
  (congrArg (fun z => ModuleCat.Hom.hom h z) hx).symm.trans
    (congrArg (fun k => ModuleCat.Hom.hom k x) hgh)

/-- An isomorphism from the sections of the relative differentials on `U` to the Kähler
differentials of the sections, carrying the universal relative derivation to the
ring-theoretic one, has an inverse that carries universal differentials to universal relative
differentials. -/
theorem inv_hom_apply_d
    (e : (Scheme.Hom.relativeDifferentials f).val.obj (.op U) ≅
      CommRingCat.KaehlerDifferential (f.appLE V U hUV))
    (he : ∀ a : Γ(X, U), e.hom.hom ((Scheme.Hom.universalRelativeDerivation f).d a) =
      CommRingCat.KaehlerDifferential.d a) (a : Γ(X, U)) :
    e.inv.hom (CommRingCat.KaehlerDifferential.d a) =
      (Scheme.Hom.universalRelativeDerivation f).d a :=
  hom_apply_eq_of_comp_eq_id e.hom_inv_id (he a)

/-- An isomorphism from the sections on `U` of the sheaf of relative differentials to the
Kähler differentials of the sections, compatible with the universal derivations, has the
canonical comparison map as its inverse. -/
theorem kaehlerToSections_eq_inv
    (e : (Scheme.Hom.relativeDifferentials f).val.obj (.op U) ≅
      CommRingCat.KaehlerDifferential (f.appLE V U hUV))
    (he : ∀ a : Γ(X, U), e.hom.hom ((Scheme.Hom.universalRelativeDerivation f).d a) =
      CommRingCat.KaehlerDifferential.d a) :
    kaehlerToSections f V U hUV = e.inv := by
  ext a
  exact (kaehlerToSections_d f V U hUV a).trans
    (inv_hom_apply_d f V U hUV e he a).symm

/-- **Uniqueness half of Stacks Project, Tag 01UT.** There is at most one isomorphism from the
sections on `U` of the sheaf of relative differentials of `f` to the Kähler differentials of
`Γ(S, V) ⟶ Γ(X, U)` carrying the universal relative derivation to the ring-theoretic universal
derivation. Neither `U` nor `V` needs to be affine for this. -/
theorem iso_unique
    (e e' : (Scheme.Hom.relativeDifferentials f).val.obj (.op U) ≅
      CommRingCat.KaehlerDifferential (f.appLE V U hUV))
    (he : ∀ a : Γ(X, U), e.hom.hom ((Scheme.Hom.universalRelativeDerivation f).d a) =
      CommRingCat.KaehlerDifferential.d a)
    (he' : ∀ a : Γ(X, U), e'.hom.hom ((Scheme.Hom.universalRelativeDerivation f).d a) =
      CommRingCat.KaehlerDifferential.d a) :
    e = e' :=
  Iso.ext ((Iso.inv_eq_inv e e').1
    ((kaehlerToSections_eq_inv f V U hUV e he).symm.trans
      (kaehlerToSections_eq_inv f V U hUV e' he')))

/-- **Stacks Project, Tag 01UT, reduced to a single isomorphism.** The sections on `U` of the
sheaf of relative differentials of `f` are uniquely isomorphic to the Kähler differentials of
`Γ(S, V) ⟶ Γ(X, U)`, compatibly with the universal derivations, precisely when the canonical
comparison map `kaehlerToSections` is an isomorphism. The uniqueness is unconditional; it is
the existence that Stacks 01UT asserts for `U` and `V` affine, and this equivalence turns that
assertion into a statement about one explicitly given map. -/
theorem existsUnique_affineDifferentialsIso_iff_isIso :
    (∃! e : (Scheme.Hom.relativeDifferentials f).val.obj (.op U) ≅
        CommRingCat.KaehlerDifferential (f.appLE V U hUV),
      ∀ a : Γ(X, U), e.hom.hom ((Scheme.Hom.universalRelativeDerivation f).d a) =
        CommRingCat.KaehlerDifferential.d a) ↔ IsIso (kaehlerToSections f V U hUV) := by
  refine ⟨fun ⟨e, he, _⟩ => ?_, fun h => ?_⟩
  · have hk : kaehlerToSections f V U hUV = e.inv := kaehlerToSections_eq_inv f V U hUV e he
    exact ⟨⟨e.hom, hk ▸ e.inv_hom_id, hk ▸ e.hom_inv_id⟩⟩
  · have key : ∀ a : Γ(X, U),
        (inv (kaehlerToSections f V U hUV)).hom
            ((Scheme.Hom.universalRelativeDerivation f).d a) =
          CommRingCat.KaehlerDifferential.d a := fun a =>
      hom_apply_eq_of_comp_eq_id (IsIso.hom_inv_id (kaehlerToSections f V U hUV))
        (kaehlerToSections_d f V U hUV a)
    refine ⟨(asIso (kaehlerToSections f V U hUV)).symm, key, fun e' he' => ?_⟩
    exact iso_unique f V U hUV e' _ he' key

end Stacks.AlgebraicGeometry.AffineDifferentials

end
