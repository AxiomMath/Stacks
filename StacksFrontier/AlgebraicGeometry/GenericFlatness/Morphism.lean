module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.RingTheory.Flat.GenericFlatness

/-!
# Generic flatness for an affine morphism of finite type over a reduced base

Stacks 052B says that if `f : X ⟶ S` is of finite type, `S` is reduced and `ℱ` is a finite type
`𝒪_X`-module, then there is a dense open `U ⊆ S` over which `f` becomes flat and of finite
presentation and over which `ℱ` becomes flat and of finite presentation. This file proves the
case `ℱ = 𝒪_X` for an *affine* morphism `f`, by globalizing the ring-theoretic statement
Stacks 051Z (`Algebra.exists_isOpen_dense_isFinitePresentationFreeAway`) over the affine opens
of the base.

That case is what Stacks 0ASY — and hence the generic flatness stratification Stacks 0H3Z, one
of the inputs to Stacks 0ETR — consumes: 0H3Z is 0ASY for `ℱ = 𝒪_X`, and the
morphisms 0ASY feeds to 052B in that case are base changes of the original affine morphism.

## Main results

* `AlgebraicGeometry.IsZariskiLocalAtTarget.of_le_iSup`: a property local at the target holds for
  the restriction of `f` to an open `U` as soon as it holds for the restrictions to a family of
  opens contained in `U` which covers `U`.
* `AlgebraicGeometry.HasRingHomProperty.of_app_morphismRestrict` and
  `AlgebraicGeometry.HasRingHomProperty.of_away_map`: a property of the ring map on sections, or
  of the induced map of away localizations, gives the corresponding property of a restriction of
  the morphism.
* `Stacks.GenericFlatness.flat_and_finitePresentation_away_map`: the condition of Stacks 051U at
  `r` makes the induced map of away localizations at `r` flat and of finite presentation, for any
  models of those localizations.
* `Stacks.GenericFlatness.exists_subset_closure_flat_of_isAffineOpen`: the chart-level statement —
  over an affine open `U` of the base with affine preimage, there is an open `U' ≤ U` which is
  dense in `U` and over which `f` is flat and locally of finite presentation.
* `Stacks.GenericFlatness.exists_dense_flat`: the case `ℱ = 𝒪_X` of Stacks 052B for an affine
  morphism — a dense open of the base over which `f` is flat and locally of finite presentation.

## Implementation notes

`IsZariskiLocalAtTarget @Flat` and `IsZariskiLocalAtTarget @LocallyOfFinitePresentation` are
*not* found by `inferInstance`: the instance exists in Mathlib for a variable morphism property
with a `HasRingHomProperty` instance, but resolving it at the concrete `@Flat` fails, which is
why `Mathlib.AlgebraicGeometry.Morphisms.Flat` proves its own
`Flat (f ∣_ V)` instance under `backward.isDefEq.respectTransparency.types false`. The remedy
used here is to feed the instance as a term through
`AlgebraicGeometry.HasRingHomProperty.isZariskiLocalAtTarget`; no option is set.

The good locus of Stacks 051Z is handed to the assembly step
`Stacks.GenericFlatness.exists_subset_closure_flat_of_isAffineOpen'` as an opaque set of
sections, rather than written out at the point of use. Written out, the `Algebra` instance built
from `f.appLE` gets inlined into every occurrence of the index type and the elaboration exhausts
the heartbeat budget.

Density over an affine open `U` is transported from `Spec Γ(Y, U)` along
`AlgebraicGeometry.IsAffineOpen.fromSpec`, which is an open immersion with range `U` carrying
`PrimeSpectrum.basicOpen r` to `Y.basicOpen r`.

## What the general Stacks 052B still needs

Two things, both independent of the above.

* A **finite type module** `ℱ`: the argument would run the same way, with 051Z applied to the
  pair `(Γ(Y, U) → Γ(X, f ⁻¹ᵁ U), M)` for the finite module `M` presenting `ℱ` on the chart, but
  it additionally needs the transport of `AlgebraicGeometry.IsFlatOver` and of finite
  presentation of a module sheaf across the localization models, and the identification of a
  finite type quasi-coherent module with a finite module on an affine (Stacks 01PB).
* A **non-affine source**: when `f ⁻¹ᵁ U` is not affine one covers it by finitely many affine
  opens `V₁, …, Vₙ` (possible since a morphism of finite type is quasi-compact), applies 051Z to
  each `Γ(Y, U) → Γ(X, Vᵢ)` and intersects the finitely many dense opens obtained. Concluding
  flatness over the intersection then uses locality at the source rather than
  `Stacks.GenericFlatness.exists_subset_closure_flat_of_isAffineOpen`. The quasi-separatedness
  bookkeeping of the Stacks proof (the ideals `I_{ij}` cutting out `Vᵢ ∖ Vᵢ ∩ Vⱼ`) is only needed
  for the *finite presentation* half of 052B, not for flatness.

Because of these two gaps no `@[stacks 052B]` attribute is attached here.

## References

* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
* [Stacks Project, Tag 051Z](https://stacks.math.columbia.edu/tag/051Z)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

namespace HasRingHomProperty

/-- A morphism property with a `HasRingHomProperty` instance is local at the target.

This is Mathlib's own instance, restated as a theorem so that it can be supplied as a *term*:
instance resolution does not find it at a concrete property such as `@Flat`. -/
theorem isZariskiLocalAtTarget (P : MorphismProperty Scheme.{u}) {Q}
    [HasRingHomProperty P Q] : IsZariskiLocalAtTarget P := inferInstance

variable {P : MorphismProperty Scheme.{u}} {Q} [HasRingHomProperty P Q]

/-- If the ring map on sections over an open `W` whose preimage and whose own total space are
affine has `Q`, then the restriction of `f` to `W` has `P`. -/
theorem of_app_morphismRestrict (f : X ⟶ Y) (W : Y.Opens) [IsAffine W.toScheme]
    [IsAffine (f ⁻¹ᵁ W).toScheme] (h : Q (f.app W).hom) : P (f ∣_ W) := by
  rw [HasRingHomProperty.iff_of_isAffine (P := P) (Q := Q), Scheme.Hom.appTop,
    morphismRestrict_app']
  have key : Q (f.appLE W (f ⁻¹ᵁ W) le_rfl).hom := by rwa [Scheme.Hom.appLE_eq_app]
  exact (Scheme.Hom.appLE_congr f le_rfl (Scheme.Opens.ι_image_top W).symm
    (show f ⁻¹ᵁ W = (f ⁻¹ᵁ W).ι ''ᵁ ((f ∣_ W) ⁻¹ᵁ ⊤) by simp) fun g => Q g.hom).mp key

/-- The variant of `AlgebraicGeometry.HasRingHomProperty.of_app_morphismRestrict` whose
hypothesis is about an open `V` of the source that is merely *equal* to the preimage of `W`. -/
theorem of_appLE_morphismRestrict (f : X ⟶ Y) (W : Y.Opens) [IsAffine W.toScheme]
    [IsAffine (f ⁻¹ᵁ W).toScheme] {V : X.Opens} (hV : V = f ⁻¹ᵁ W) (e : V ≤ f ⁻¹ᵁ W)
    (h : Q (f.appLE W V e).hom) : P (f ∣_ W) := by
  refine of_app_morphismRestrict f W ?_
  rw [← Scheme.Hom.appLE_eq_app]
  exact (Scheme.Hom.appLE_congr f e rfl hV fun g => Q g.hom).mp h

/-- If `Q` holds for the map of away localizations at `r : Γ(Y, U)` induced by `f` on an affine
open `U` with affine preimage, then `P` holds for the restriction of `f` to `Y.basicOpen r`. -/
theorem of_away_map (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U))
    (h : let e : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U := le_rfl
         let _ := hU.isLocalization_basicOpen r
         let _ := hV.isLocalization_basicOpen (f.appLE U (f ⁻¹ᵁ U) e r)
         Q (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
             Γ(X, X.basicOpen (f.appLE U (f ⁻¹ᵁ U) e r)) (f.appLE U (f ⁻¹ᵁ U) e).hom r)) :
    P (f ∣_ Y.basicOpen r) := by
  have e : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U := le_rfl
  have _ := hU.isLocalization_basicOpen r
  have _ := hV.isLocalization_basicOpen (f.appLE U (f ⁻¹ᵁ U) e r)
  have hpre : X.basicOpen (f.appLE U (f ⁻¹ᵁ U) e r) = f ⁻¹ᵁ Y.basicOpen r := by
    rw [Scheme.preimage_basicOpen, Scheme.Hom.appLE_eq_app]
  have : IsAffine (Y.basicOpen r).toScheme := hU.basicOpen r
  have : IsAffine (f ⁻¹ᵁ Y.basicOpen r).toScheme := hpre ▸ hV.basicOpen _
  refine of_appLE_morphismRestrict f (Y.basicOpen r) hpre (le_of_eq hpre) ?_
  rwa [hU.appLE_eq_away_map f hV e r]

end HasRingHomProperty

namespace IsZariskiLocalAtTarget

/-- A property local at the target holds for the restriction of `f` to `U` as soon as it holds
for the restrictions to a family of opens contained in `U` which covers `U`. -/
theorem of_le_iSup {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P] {f : X ⟶ Y}
    {U : Y.Opens} {ι : Type*} (V : ι → Y.Opens) (hVU : ∀ i, V i ≤ U) (hU : U ≤ ⨆ i, V i)
    (h : ∀ i, P (f ∣_ V i)) : P (f ∣_ U) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU x.2)
  refine ⟨U.ι ⁻¹ᵁ V i, hi, ?_⟩
  rw [P.arrow_mk_iso_iff (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V i)),
    P.arrow_mk_iso_iff (morphismRestrictEq f
      (show U.ι ''ᵁ (U.ι ⁻¹ᵁ V i) = V i by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
        exact hVU i))]
  exact h i

end IsZariskiLocalAtTarget

end AlgebraicGeometry

namespace Stacks.GenericFlatness

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Model independence of the condition of Stacks 051U, in the form used below.** If `r`
satisfies 051U for `R → S` with the module `S`, then the map of away localizations at `r` that it
induces is flat and of finite presentation, for *any* models of those localizations. -/
theorem flat_and_finitePresentation_away_map {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (r : R) (Rf : Type u) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away r Rf]
    (Sf : Type u) [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [IsScalarTower R S Sf]
    [IsLocalization.Away (algebraMap R S r) Sf]
    (h : Algebra.IsFinitePresentationFreeAway R S S r) :
    RingHom.Flat (IsLocalization.Away.map Rf Sf (algebraMap R S) r) ∧
      RingHom.FinitePresentation (IsLocalization.Away.map Rf Sf (algebraMap R S) r) := by
  let _ : Algebra Rf Sf := (IsLocalization.Away.map Rf Sf (algebraMap R S) r).toAlgebra
  have : IsScalarTower R Rf Sf := .of_algebraMap_eq' <| by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map, IsLocalization.map_comp]
    exact IsScalarTower.algebraMap_eq R S Sf
  obtain ⟨hfp, -, hfree, -⟩ := (Algebra.isFinitePresentationFreeAway_iff r Rf Sf Sf
    (Algebra.linearMap S Sf)).mp h
  have heq : IsLocalization.Away.map Rf Sf (algebraMap R S) r = algebraMap Rf Sf :=
    (RingHom.algebraMap_toAlgebra _).symm
  refine ⟨?_, ?_⟩
  · rw [heq, RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_free
  · rwa [heq, RingHom.finitePresentation_algebraMap]

/-- Flatness and local finite presentation of `f` pass to the restriction over a union of opens
over which they hold. -/
private theorem flat_and_locallyOfFinitePresentation_iSup {ι : Type*} (f : X ⟶ Y)
    (V : ι → Y.Opens) (hflat : ∀ i, Flat (f ∣_ V i))
    (hfp : ∀ i, LocallyOfFinitePresentation (f ∣_ V i)) :
    Flat (f ∣_ ⨆ i, V i) ∧ LocallyOfFinitePresentation (f ∣_ ⨆ i, V i) := by
  have hzf := HasRingHomProperty.isZariskiLocalAtTarget @Flat (Q := RingHom.Flat)
  have hzp := HasRingHomProperty.isZariskiLocalAtTarget @LocallyOfFinitePresentation
    (Q := RingHom.FinitePresentation)
  exact ⟨IsZariskiLocalAtTarget.of_le_iSup V (le_iSup V) le_rfl hflat,
    IsZariskiLocalAtTarget.of_le_iSup V (le_iSup V) le_rfl hfp⟩

/-- The assembly step of the chart-level statement: a set `T` of sections over an affine open `U`
whose basic opens carry flatness and finite presentation, and whose basic opens in
`Spec Γ(Y, U)` are jointly dense, produces an open `U' ≤ U` dense in `U` over which `f` is flat
and locally of finite presentation.

`T` is kept as an opaque parameter on purpose; see the implementation notes of this file. -/
theorem exists_subset_closure_flat_of_isAffineOpen' (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (T : Set Γ(Y, U))
    (hdense : Dense (⋃ r : T, (PrimeSpectrum.basicOpen r.1 : Set (PrimeSpectrum Γ(Y, U)))))
    (hflat : ∀ r : T, Flat (f ∣_ Y.basicOpen r.1))
    (hfp : ∀ r : T, LocallyOfFinitePresentation (f ∣_ Y.basicOpen r.1)) :
    ∃ U' : Y.Opens, U' ≤ U ∧ (U : Set Y) ⊆ closure (U' : Set Y) ∧
      Flat (f ∣_ U') ∧ LocallyOfFinitePresentation (f ∣_ U') := by
  have h := flat_and_locallyOfFinitePresentation_iSup f (fun r : T => Y.basicOpen r.1) hflat hfp
  refine ⟨⨆ r : T, Y.basicOpen r.1, iSup_le fun r => Y.basicOpen_le r.1, ?_, h.1, h.2⟩
  intro y hy
  obtain ⟨a, rfl⟩ : ∃ a, hU.fromSpec a = y := by rwa [← hU.range_fromSpec] at hy
  rw [mem_closure_iff]
  intro V hVopen hyV
  obtain ⟨b, hbV, hbD⟩ := hdense.inter_open_nonempty _
    (hVopen.preimage hU.fromSpec.continuous) ⟨a, hyV⟩
  obtain ⟨r, hbr⟩ := Set.mem_iUnion.mp hbD
  refine ⟨hU.fromSpec b, hbV, ?_⟩
  have hb : b ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen r.1 := by
    rwa [hU.fromSpec_preimage_basicOpen]
  exact Opens.mem_iSup.mpr ⟨r, hb⟩

/-- **The chart-level case `ℱ = 𝒪_X` of Stacks 052B.** Over an affine open `U` of a reduced base
whose preimage under a morphism locally of finite type is affine, there is an open `U' ≤ U`, dense
in `U`, over which the morphism is flat and locally of finite presentation. -/
theorem exists_subset_closure_flat_of_isAffineOpen (f : X ⟶ Y) [IsReduced Y]
    [LocallyOfFiniteType f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen (f ⁻¹ᵁ U)) :
    ∃ U' : Y.Opens, U' ≤ U ∧ (U : Set Y) ⊆ closure (U' : Set Y) ∧
      Flat (f ∣_ U') ∧ LocallyOfFinitePresentation (f ∣_ U') := by
  have e : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U := le_rfl
  let _ : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.appLE U (f ⁻¹ᵁ U) e).hom.toAlgebra
  have hft : Algebra.FiniteType Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    HasRingHomProperty.appLE (Q := RingHom.FiniteType) @LocallyOfFiniteType f ‹_›
      ⟨U, hU⟩ ⟨f ⁻¹ᵁ U, hV⟩ e
  have key : ∀ r : Γ(Y, U),
      Algebra.IsFinitePresentationFreeAway Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ U) r →
      Flat (f ∣_ Y.basicOpen r) ∧ LocallyOfFinitePresentation (f ∣_ Y.basicOpen r) := by
    intro r hr
    have _ := hU.isLocalization_basicOpen r
    have _ := hV.isLocalization_basicOpen (f.appLE U (f ⁻¹ᵁ U) e r)
    let _ : Algebra Γ(Y, U) Γ(X, X.basicOpen (f.appLE U (f ⁻¹ᵁ U) e r)) :=
      (f.appLE U (X.basicOpen (f.appLE U (f ⁻¹ᵁ U) e r)) (X.basicOpen_le _)).hom.toAlgebra
    have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
        Γ(X, X.basicOpen (f.appLE U (f ⁻¹ᵁ U) e r)) := .of_algebraMap_eq' <| by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    obtain ⟨hflat, hfpr⟩ := flat_and_finitePresentation_away_map r Γ(Y, Y.basicOpen r)
      Γ(X, X.basicOpen (f.appLE U (f ⁻¹ᵁ U) e r)) hr
    exact ⟨HasRingHomProperty.of_away_map f hU hV r hflat,
      HasRingHomProperty.of_away_map f hU hV r hfpr⟩
  obtain ⟨W, -, hWdense, hW⟩ := Algebra.exists_isOpen_dense_isFinitePresentationFreeAway
    (R := Γ(Y, U)) (S := Γ(X, f ⁻¹ᵁ U)) (M := Γ(X, f ⁻¹ᵁ U))
  refine exists_subset_closure_flat_of_isAffineOpen' f hU
    {r | Algebra.IsFinitePresentationFreeAway Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ U) r}
    (hWdense.mono fun v hv => ?_) (fun r => (key r.1 r.2).1) (fun r => (key r.1 r.2).2)
  obtain ⟨r, hvr, -, hr⟩ := hW v hv
  exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hvr⟩

/-- **The case `ℱ = 𝒪_X` of Stacks 052B for an affine morphism.** An affine morphism locally of
finite type over a reduced base is flat and locally of finite presentation over a dense open of
the base.

The general statement of Stacks 052B additionally covers a finite type module and a non-affine
source; see the implementation notes of this file. -/
theorem exists_dense_flat (f : X ⟶ Y) [IsAffineHom f] [IsReduced Y] [LocallyOfFiniteType f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Flat (f ∣_ U) ∧ LocallyOfFinitePresentation (f ∣_ U) := by
  choose U' hle hcl hflat hfp using fun V : Y.affineOpens =>
    exists_subset_closure_flat_of_isAffineOpen f V.2 (V.2.preimage f)
  have h := flat_and_locallyOfFinitePresentation_iSup f U' hflat hfp
  refine ⟨⨆ V : Y.affineOpens, U' V, ?_, h.1, h.2⟩
  intro y
  have hy : y ∈ ⨆ V : Y.affineOpens, (V : Y.Opens) := by
    rw [iSup_affineOpens_eq_top Y]
    trivial
  obtain ⟨V, hV⟩ := Opens.mem_iSup.mp hy
  exact closure_mono (show (U' V : Set Y) ⊆ (↑(⨆ V : Y.affineOpens, U' V) : Set Y) from
    fun _ h => Opens.mem_iSup.mpr ⟨V, h⟩) (hcl V hV)

end Stacks.GenericFlatness

end
