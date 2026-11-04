module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.BaseChange
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Fibres
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartFactorization
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneModule.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree

/-!
# Quasi-finite Gorenstein morphisms and the different

Let `f : Y ⟶ X` be a flat locally quasi-finite morphism of locally Noetherian schemes with
relative dualizing module `ω_{Y/X}` and trace element `τ_{Y/X}`.  Such an `f` is Gorenstein
exactly when `ω_{Y/X}` is an invertible `𝒪_Y`-module, and this file collects what the different
`𝔇_f` and the closed subscheme `R ⊆ Y` it cuts out look like in that case.

## Main results

* `Stacks.Discriminant.isInvertible_iff_forall_module_invertible`: an invertible module on a
  scheme is exactly a quasi-coherent module whose sections over every affine open form an
  invertible module over the functions there.
* `Stacks.Discriminant.isInvertible_iff_exists_chart_dualizingModule_invertible`: invertibility
  of `ω_{Y/X}` is the chartwise condition that `ω_{B/A}` be an invertible `B`-module around
  every point, which is conditions (3) and (4) of [Stacks, Tag 0C16].
* `Stacks.Discriminant.exists_affineOpens_different_isPrincipal` and
  `Stacks.Discriminant.isLocallyPrincipal_differentIdealSheaf`: the different is a locally
  principal ideal and `R` is a locally principal closed subscheme.
* `Stacks.Discriminant.different_sections_eq_noetherDifferent_of_isInvertible`: on an affine
  chart the different is the Noether different.
* `Stacks.Discriminant.isIso_different_baseChange_of_gorenstein`: formation of `R` commutes with
  arbitrary base change.

## Implementation notes

The statements about the different are made for a flat quasi-finite morphism with invertible
`ω_{Y/X}`, the setting of [Stacks, Tag 0BWA]; invertibility is condition (3) of
[Stacks, Tag 0C16], which
`Stacks.Discriminant.isInvertible_iff_exists_chart_dualizingModule_invertible` relates to the
chartwise condition (4).  Conditions (1) and (2) of that tag, Gorensteinness of `f` and
Gorensteinness of its fibres, are related to each other by
`AlgebraicGeometry.Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber`, and (1) implies (3)
is `Stacks.Discriminant.isInvertible_of_isGorenstein`, downstream of this file.  The parts of
[Stacks, Tag 0C17], for a quasi-finite Gorenstein morphism, are deduced from the statements here
in `StacksFrontier.AlgebraicGeometry.Different.TheDifferent.GorensteinInvertible`.

## References

* [Stacks Project, Tag 0C17](https://stacks.math.columbia.edu/tag/0C17)
* [Stacks Project, Tag 0C16](https://stacks.math.columbia.edu/tag/0C16)
* [Stacks Project, Tag 0C05](https://stacks.math.columbia.edu/tag/0C05)
* [Stacks Project, Tag 0BW6](https://stacks.math.columbia.edu/tag/0BW6)
* [Stacks Project, Tag 0BW7](https://stacks.math.columbia.edu/tag/0BW7)
* [Stacks Project, Tag 0BWA](https://stacks.math.columbia.edu/tag/0BWA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open scoped AlgebraicGeometry

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.presheaf TopCat.Sheaf structureSheafRing Scheme.Modules

universe u

namespace Stacks.Discriminant

/-! ### Invertibility of a module sheaf is affine-local on sections -/

/-- A quasi-coherent module is invertible once every point has an affine open neighbourhood over
which its sections form an invertible module. -/
private theorem isInvertible_of_forall_exists_module_invertible {Y : Scheme.{u}} (L : Y.Modules)
    [L.IsQuasicoherent]
    (h : ∀ y : Y, ∃ V : Y.affineOpens, y ∈ V.1 ∧ Module.Invertible Γ(Y, V.1) Γ(L, V.1)) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property L := by
  refine (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr ?_
  refine Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one Y L ?_
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff L 1).mp ?_
  refine Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens L 1 fun y ↦ ?_
  obtain ⟨V, hyV, _⟩ := h y
  exact ⟨V, hyV, Module.isFiniteLocallyFreeOfRank_one_of_invertible⟩

/-- **An invertible module is affine-locally an invertible module of sections.** A
quasi-coherent `𝒪_Y`-module `L` on a scheme is invertible exactly when, for every affine open
`V = Spec B` of `Y`, the `B`-module `Γ(L, V)` is invertible.

Invertibility of `L` is the same as being finite locally free of rank one, and that property is
affine-local on sections because the restriction of a quasi-coherent module to `Spec Γ(Y, V)` is
the sheaf associated to `Γ(L, V)`. -/
theorem isInvertible_iff_forall_module_invertible {Y : Scheme.{u}} (L : Y.Modules)
    [L.IsQuasicoherent] :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
        (structureSheafRing
          Y.toRingedSpace).property L ↔
      ∀ V : Y.affineOpens, Module.Invertible Γ(Y, V.1) Γ(L, V.1) := by
  constructor
  · intro h V
    have hAG : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
        Y.ringCatSheaf.property L :=
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mp h
    have hrank : Scheme.Modules.IsFiniteLocallyFreeOfRank L 1 :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff L 1).mpr
        (Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible Y L hAG)
    have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
    refine Module.invertible_of_isFiniteLocallyFreeOfRank_one ?_
    refine (_root_.tilde_isFiniteLocallyFreeOfRank_iff Γ(Y, V.1) Γ(L, V.1) 1).mp ?_
    exact Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
      (Stacks.Modules.tildeIsoRestrictFromSpec L V.2).symm
      (Scheme.Modules.IsFiniteLocallyFreeOfRank.restrict V.2.fromSpec hrank)
  · intro h
    refine isInvertible_of_forall_exists_module_invertible L fun y ↦ ?_
    obtain ⟨V, hyV⟩ := Stacks.Divisors.exists_affineOpens_mem y
    exact ⟨V, hyV, h V⟩

/-! ### Quasi-finite Gorenstein morphisms -/

section Gorenstein

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [LocallyOfFiniteType f]
  [LocallyQuasiFinite f]

omit [Flat f] [LocallyOfFiniteType f] in
/-- The sections of an invertible relative dualizing module over an affine open of the source
form an invertible module over the functions there. -/
theorem module_invertible_sections (ω : RelativeDualizingModuleData f)
    [hinv : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing
        Y.toRingedSpace).property ω.sheaf]
    (V : Y.affineOpens) : Module.Invertible Γ(Y, V.1) Γ(ω.sheaf, V.1) :=
  have := ω.isQuasicoherent
  (isInvertible_iff_forall_module_invertible ω.sheaf).mp hinv V

omit [Flat f] [LocallyOfFiniteType f] in
/-- The algebraic relative dualizing module of a chart of an invertible relative dualizing
module is an invertible module over the coordinate ring of the chart. -/
theorem module_invertible_dualizingModule (ω : RelativeDualizingModuleData f)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing
        Y.toRingedSpace).property ω.sheaf]
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      Module.Invertible Γ(Y, V.1) (dualizingModule F) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  intro F
  have := module_invertible_sections ω V
  exact Module.Invertible.congr (ω.localEquiv U V hVU F)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [LocallyOfFiniteType f]
  [LocallyQuasiFinite f] in
/-- Every point of the source of a morphism lies in an affine open of the source lying over an
affine open of the base. -/
theorem exists_chart (y : Y) :
    ∃ (U : X.affineOpens) (V : Y.affineOpens) (_ : V.1 ≤ f ⁻¹ᵁ U.1), y ∈ V.1 := by
  obtain ⟨U, hU⟩ := Stacks.Divisors.exists_affineOpens_mem (f.base y)
  obtain ⟨V, hyV, hVU⟩ := exists_affine_subset y (f ⁻¹ᵁ U.1) hU
  exact ⟨U, V, hVU, hyV⟩

omit [Flat f] in
/-- **[Stacks, Tag 0C16], conditions (3) and (4).** For a quasi-finite morphism of locally
Noetherian schemes with relative dualizing module `ω_{Y/X}`, the module `ω_{Y/X}` is an
invertible `𝒪_Y`-module exactly when every point of `Y` has an affine open neighbourhood
`V = Spec B` lying over an affine open `U = Spec A` of `X` for which the algebraic relative
dualizing module `ω_{B/A}` is an invertible `B`-module.

Both conditions of the source also ask that `f` be flat; flatness plays no role in the
equivalence of the two readings of invertibility, so it is not assumed here. -/
@[stacks 0C16 "(3) iff (4)"]
theorem isInvertible_iff_exists_chart_dualizingModule_invertible
    (ω : RelativeDualizingModuleData f) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
        (structureSheafRing
          Y.toRingedSpace).property ω.sheaf ↔
      ∀ y : Y, ∃ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1), y ∈ V.1 ∧
        letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
        ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
          Module.Invertible Γ(Y, V.1) (dualizingModule F) := by
  have := ω.isQuasicoherent
  constructor
  · intro h y
    have := h
    obtain ⟨U, V, hVU, hyV⟩ := exists_chart (f := f) y
    exact ⟨U, V, hVU, hyV, module_invertible_dualizingModule ω U V hVU⟩
  · intro h
    refine isInvertible_of_forall_exists_module_invertible ω.sheaf fun y ↦ ?_
    obtain ⟨U, V, hVU, hyV, hF⟩ := h y
    refine ⟨V, hyV, ?_⟩
    let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    obtain ⟨F⟩ := nonempty_relativeDualizingChartFactorization f U V hVU
    have := hF F
    exact Module.Invertible.congr (ω.localEquiv U V hVU F).symm

/-! ### The different of a quasi-finite Gorenstein morphism -/

variable (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω)
  [Stacks.SheafOfModules.IsInvertible Y.presheaf
    (structureSheafRing
      Y.toRingedSpace).property ω.sheaf]

omit [LocallyOfFiniteType f] in
/-- **The different is locally principal.** The different of a flat quasi-finite morphism with
invertible relative dualizing module is a locally principal ideal: every point of `Y` has an
affine open neighbourhood `V = Spec B` on which the ideal of sections of `𝔇_f` is generated by a
single element of `B`.

On an affine open where `ω_{Y/X}` is free of rank one, say `ω_{Y/X} = 𝒪_Y λ`, the trace element
is `τ_{Y/X} = h λ` for a function `h`, and `h` generates the different there.

For a quasi-finite Gorenstein morphism this is [Stacks, Tag 0C17 (1)], stated as
`Stacks.Discriminant.exists_affineOpens_different_isPrincipal_of_isGorenstein`. -/
theorem exists_affineOpens_different_isPrincipal (y : Y) :
    ∃ V : Y.affineOpens, y ∈ (V : Set Y) ∧
      (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)).IsPrincipal :=
  isLocallyPrincipal_different ω τ y

omit [LocallyOfFiniteType f] in
/-- **[Stacks, Tag 0BWA (1)].** The closed subscheme `R ⊆ Y` cut out by the different of a flat
quasi-finite morphism with invertible relative dualizing module is a locally principal closed
subscheme.

For a quasi-finite Gorenstein morphism this is [Stacks, Tag 0C17 (2)], stated as
`Stacks.Discriminant.isLocallyPrincipal_differentIdealSheaf_of_isGorenstein`. -/
theorem isLocallyPrincipal_differentIdealSheaf :
    Stacks.Divisors.IsLocallyPrincipal (differentIdealSheaf ω τ) := by
  intro y
  obtain ⟨V, hyV, hV⟩ := isLocallyPrincipal_different ω τ y
  refine ⟨V, hyV, ?_⟩
  rwa [differentIdealSheaf_ideal ω τ V]

/-- **[Stacks, Tag 0BW6].** On affine opens `V = Spec B ⊆ Y` and `U = Spec A ⊆ X` with
`f(V) ⊆ U`, the different of a flat quasi-finite morphism with invertible relative dualizing
module is the Noether different of `B` over `A`.

Invertibility of `ω_{Y/X}` makes the algebraic relative dualizing module of the chart
invertible, which is the hypothesis of [Stacks, Tag 0BW6].

For a quasi-finite Gorenstein morphism this is [Stacks, Tag 0C17 (3)], stated as
`Stacks.Discriminant.different_sections_eq_noetherDifferent_of_isGorenstein`. -/
theorem different_sections_eq_noetherDifferent_of_isInvertible
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)) =
      noetherDifferent Γ(X, U.1) Γ(Y, V.1) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  obtain ⟨F⟩ := nonempty_relativeDualizingChartFactorization f U V hVU
  exact different_sections_eq_noetherDifferent ω τ U V hVU F
    (module_invertible_dualizingModule ω U V hVU F)

end Gorenstein

/-! ### Base change -/

section BaseChangeGorenstein

variable {X X' Y : Scheme.{u}} (f : Y ⟶ X) (g : X' ⟶ X)
  [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [IsLocallyNoetherian Y]
  [Flat f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]

variable {R R' : Scheme.{u}} (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω)
  (ω' : RelativeDualizingModuleData (pullback.snd f g)) (τ' : RelativeTraceSection ω')
  (i : R ⟶ Y) (i' : R' ⟶ pullback f g) [IsClosedImmersion i] [IsClosedImmersion i']

/-- **The different commutes with base change.** Formation of the closed subscheme `R ⊆ Y` cut
out by the different commutes with base change along an arbitrary morphism `g : X' ⟶ X`: the
closed immersion `R' ⟶ R ×_Y Y'` induced by `Y' ⟶ Y` is an isomorphism.

Invertibility of the relative dualizing module is the case of [Stacks, Tag 0BW7] in which the
inverse image of the different is the different of the base change with no flatness hypothesis
on `g`.

For a quasi-finite Gorenstein morphism this is [Stacks, Tag 0C17 (4)], stated as
`Stacks.Discriminant.isIso_different_baseChange_of_isGorenstein`. -/
theorem isIso_different_baseChange_of_gorenstein
    [Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing
        Y.toRingedSpace).property ω.sheaf]
    (hi : i.ker = differentIdealSheaf ω τ) (hi' : i'.ker = differentIdealSheaf ω' τ')
    (k : R' ⟶ R) (hk : k ≫ i = i' ≫ pullback.fst f g) :
    IsIso (pullback.lift k i' hk) :=
  isIso_different_baseChange_of_invertible f g ω τ ω' τ' i i'
    (fun V ↦ module_invertible_sections ω V) hi hi' k hk

end BaseChangeGorenstein

/-! ### Tag 0C16, conditions (1) and (2)

A quasi-finite morphism of Noetherian schemes is Gorenstein exactly when it is flat and its
fibres are Gorenstein schemes.  This is Tag 0C05, which states it for an arbitrary
morphism with locally Noetherian fibres. -/

add_to_stacks 0C16 "(1) iff (2)"
  AlgebraicGeometry.Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber

end Stacks.Discriminant

end
