module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.Algebra.Category.Ring.PushoutTensorComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SDerivation
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SpecDividedPowerScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability

/-!
# A smooth lifting of the closed fibre is an object of the crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine and `p` nilpotent in
`Γ(S, ⊤)`, let `Y ⟶ S` be smooth and let `X = Y ×_S S₀` be its closed fibre, where `S₀ = V(I)`.
The closed immersion `X ↪ Y` is then a thickening, being the base change of the thickening
`S₀ ↪ S`, and its ideal is on each affine open `U ⊆ Y` the image of `I` under
`Γ(S, ⊤) ⟶ Γ(Y, U)`.  That map is flat, so `γ` extends uniquely to divided powers on the image
ideal, and the extensions on the various charts agree; the resulting divided power scheme
`(Y, I·𝒪_Y, γ)` together with `X ↪ Y`, the map `Y ⟶ S` and the identity of `X` is an object of
`Cris(X/S)`.  This is part (1) of [Stacks, Tag 07MW].

## Main definitions

* `Crystalline.GlobalCrystallineSituation.smoothLiftingDividedPowers` — the extension of `γ` to
  the ideal of `X` in `Y`, [Stacks, Tag 07MW] part (1).
* `Crystalline.GlobalCrystallineSituation.smoothLiftingDividedPowerScheme` — `Y` with that ideal
  and that divided power structure.
* `Crystalline.GlobalCrystallineSituation.smoothLiftingSchemeThickening` — the divided power
  thickening `X ↪ Y`.
* `Crystalline.GlobalCrystallineSituation.smoothLiftingThickening` — the resulting object of the
  big crystalline category `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.smoothLiftingCrystallineThickening` — the resulting
  object `(X, Y, γ)` of the small crystalline site `Cris(X/S)`, [Stacks, Tag 07MW] part (1).

## What is and is not proved

[Stacks, Tag 07MW] is a remark with three assertions.  **Only part (1) is proved here, and the
tag attribute says so.**

Part (1) — that `γ` extends to a divided power structure on the ideal of `X` in `Y` so that
`(X, Y, γ)` is an object of `Cris(X/S)` — is proved in full, as
`smoothLiftingCrystallineThickening`: the object is built from the given data, so that its
thickened scheme is `X`, its ambient scheme is `Y`, its immersion is the given `X ⟶ Y`, its map
to the divided power base is the given `Y ⟶ S` and its map to `X` is the identity, all by
definition and recorded as `rfl` lemmas.  Membership in the small site — that the map to `X` is
an open immersion — is the identity being an open immersion.

Part (2) — that the restriction `F_Y` of a crystal `F` in quasi-coherent `𝒪_{X/S}`-modules to the
smooth lifting carries a canonical integrable connection
`∇ : F_Y ⟶ F_Y ⊗_{𝒪_Y} Ω¹_{Y/S}` — is **not** stated here.  It is a statement about the
restriction functor of [Stacks, Tag 07IN] applied to the object constructed in this file, and
belongs with the crystal-to-connection comparison rather than with the construction of the
object.

Part (3) — that the crystalline cohomology of `F` is the de Rham cohomology of the complex
`F_Y ⟶ F_Y ⊗ Ω¹_{Y/S} ⟶ F_Y ⊗ Ω²_{Y/S} ⟶ ⋯` — is **not** stated here.  The comparison it rests
on is [Stacks, Tag 07LH], proved for the affine situation as
`Crystalline.GlobalCrystallineSituation.SmallSite.smoothPresentationPair_computesCohomology` of
`SmallSite/SmoothPresentationCohomology07LH.lean`; identifying the de Rham complex of the smooth
lifting with the complex `M' ⊗^∧_{D'} Ω^*_{D'}` of that theorem is not done here.

## Implementation notes

The affineness of `S` is what makes the construction short.  The divided power ideal of `S` is an
ideal sheaf datum (`Crystalline.DividedPowerScheme.ideal_obj_eq_ker_ideal_closedFiberι`), so on an
affine open `V ⊆ S` it is the image of `I = Γ(S, ⊤) ∩ I` under restriction
(`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`); the single ring `Γ(S, ⊤)` therefore serves
as the source of every chart comparison, and the chart-by-chart extension of divided powers along
a flat map is the ready-made
`Crystalline.DividedPowerScheme.dividedPowerStructureOfAffineSections`.  What has to be supplied
is the identification of the ideal of `X` in `Y` over an affine open `U ⊆ Y` with the image of `I`
under `Γ(S, ⊤) ⟶ Γ(Y, U)`.  That is an affine computation: the pullback square becomes a pushout
square of rings on affine charts
(`AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`), and the kernel of a pushout of a
surjection is the image of the kernel.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry
open Stacks.Thickenings

universe u

namespace Crystalline

/-! ### Affine preliminaries -/

/-- Sections over an open, pulled back from global sections of the target, factor as the map on
global sections followed by restriction. -/
private theorem appLE_top {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) :
    f.appLE ⊤ U (le_preimage_top f U) =
      f.appTop ≫ X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op :=
  rfl

/-- The ring-homomorphism form of `Crystalline.appLE_top`. -/
private theorem appLE_top_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) :
    (f.appLE ⊤ U (le_preimage_top f U)).hom =
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp f.appTop.hom :=
  rfl

/-- **On affine charts, base change carries the defining ideal of a closed immersion to the
defining ideal of its base change.**  For a cartesian square whose vertical maps `iX` and `iY` are
closed immersions, an affine open `V` of the target of `iX` and an affine open `W` of the target of
`iY` lying over it, the ideal of `iY` on `W` is the image of the ideal of `iX` on `V`.  On affine
charts the cartesian square of schemes is a pushout square of rings, and the kernel of a pushout
of the surjection `iX` is the image of its kernel, `CommRingCat.ker_inr_of_isPushout`. -/
private theorem ker_ideal_map_of_isPullback
    {X₀ X Y₀ Y : Scheme.{u}} (iX : X₀ ⟶ X) (iY : Y₀ ⟶ Y) (f : Y ⟶ X) (g : Y₀ ⟶ X₀)
    [IsClosedImmersion iX] [IsClosedImmersion iY] (h : IsPullback iY g f iX)
    (V : X.affineOpens) (W : Y.affineOpens) (hW : W.1 ≤ f ⁻¹ᵁ V.1) :
    (iX.ker.ideal V).map (f.appLE V.1 W.1 hW).hom = iY.ker.ideal W := by
  have hle : iY ⁻¹ᵁ W.1 ≤ g ⁻¹ᵁ (iX ⁻¹ᵁ V.1) := by
    intro z hz
    have he := congrArg (fun k : Y₀ ⟶ X => k z) h.w
    change f (iY z) = iX (g z) at he
    show iX (g z) ∈ V.1
    rw [← he]
    exact hW hz
  have hUY : iY ⁻¹ᵁ W.1 = g ⁻¹ᵁ (iX ⁻¹ᵁ V.1) ⊓ iY ⁻¹ᵁ W.1 := (inf_eq_right.mpr hle).symm
  have hpush := (isIso_pushoutSection_iff h.flip hW le_rfl hUY).mp
    (isIso_pushoutSection_of_isAffineOpen h.flip hW le_rfl hUY V.2 W.2 (V.2.preimage iX))
  have hsurj : Function.Surjective (iX.appLE V.1 (iX ⁻¹ᵁ V.1) le_rfl) := by
    simpa only [Scheme.Hom.appLE_eq_app] using iX.app_surjective V.1 V.2
  have he := CommRingCat.ker_inr_of_isPushout _ _ _ _ hpush hsurj
  have hX : iX.appLE V.1 (iX ⁻¹ᵁ V.1) le_rfl = iX.app V.1 := iX.appLE_eq_app
  have hY : iY.appLE W.1 (iY ⁻¹ᵁ W.1) le_rfl = iY.app W.1 := iY.appLE_eq_app
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply, ← hX, ← hY]
  exact he.symm

/-- **A flat morphism to an affine scheme is flat on sections over an affine open.**  This is
flatness of `f` applied to the affine opens `⊤` of the target and `U` of the source. -/
theorem flat_appTop_restrict {S Y : Scheme.{u}} [IsAffine S] (f : Y ⟶ S) [Flat f]
    (U : Y.affineOpens) :
    ((Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom.comp f.appTop.hom).Flat := by
  rw [← appLE_top_hom f U.1]
  exact f.flat_appLE (isAffineOpen_top S) U.2 _

/-- **If `p` is nilpotent on global sections then the closed fibre inclusion is a thickening.**
Nilpotence passes to the sections over every affine open by restriction, so this is
`Crystalline.DividedPowerScheme.isThickening_closedFiberι_of_isNilpotent_natCast`. -/
private theorem isThickening_closedFiberι_of_isNilpotent_top (X : DividedPowerScheme.{u})
    {p : ℕ} (hp : p.Prime) (hnil : IsNilpotent (p : Γ(X.scheme, ⊤))) :
    IsThickening (DividedPowerScheme.closedFiberι X) :=
  DividedPowerScheme.isThickening_closedFiberι_of_isNilpotent_natCast X hp fun V => by
    simpa only [map_natCast] using
      hnil.map (X.scheme.presheaf.map (homOfLE (show V.1 ≤ ⊤ from le_top)).op).hom

/-- The divided power ideal of `S` over the affine open `⊤` is the ideal of its closed fibre. -/
private theorem ideal_obj_top_eq_ker_ideal (S : DividedPowerScheme.{u}) [IsAffine S.scheme] :
    S.ideal.obj (op (⊤ : S.scheme.Opens)) =
      (DividedPowerScheme.closedFiberι S).ker.ideal ⟨⊤, isAffineOpen_top S.scheme⟩ :=
  DividedPowerScheme.ideal_obj_eq_ker_ideal_closedFiberι S ⟨⊤, isAffineOpen_top S.scheme⟩

namespace GlobalCrystallineSituation

/-! ### The smooth lifting -/

variable (base : GlobalCrystallineSituation.{u}) [IsAffine base.S.scheme]
  (prime_nilpotent : IsNilpotent (base.p : Γ(base.S.scheme, ⊤)))
  (Y : Scheme.{u}) (toBase : Y ⟶ base.S.scheme) [Smooth toBase] (toY : base.X ⟶ Y)
  (cartesian : IsPullback toY base.toClosedFiber toBase
    (DividedPowerScheme.closedFiberι base.S))

include prime_nilpotent cartesian

omit [IsAffine base.S.scheme] [Smooth toBase] in
/-- **The closed immersion of a smooth lifting is a thickening.**  It is the base change of the
closed fibre inclusion `S₀ ↪ S`, which is a thickening because `p` is nilpotent on `S`, and
thickenings are stable under base change. -/
theorem isThickening_toY : IsThickening toY :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsThickening) cartesian.flip
    (isThickening_closedFiberι_of_isNilpotent_top base.S base.prime.out prime_nilpotent)

omit [Smooth toBase] in
/-- **Over an affine open of the smooth lifting, the ideal of the closed fibre is the image of the
divided power ideal of the base.**  The square is cartesian and both vertical maps are closed
immersions, so this is `Crystalline.ker_ideal_map_of_isPullback` for the affine opens `⊤ ⊆ S` and
`U ⊆ Y`, together with the identification of the divided power ideal of the base with the ideal
of its closed fibre inclusion. -/
theorem ideal_map_appTop_restrict (U : Y.affineOpens) :
    Ideal.map ((Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom.comp
        toBase.appTop.hom) (base.S.ideal.obj (op (⊤ : base.S.scheme.Opens))) =
      Crystalline.sectionIdeal Y.sheaf
        (DividedPowerScheme.idealSheafAsSubmodule toY.ker) (op U.1) := by
  have : IsClosedImmersion toY :=
    (isThickening_toY base prime_nilpotent Y toBase toY cartesian).1
  refine Eq.trans ?_ (DividedPowerScheme.idealSheafAsSubmodule_obj_affine toY.ker U).symm
  rw [← appLE_top_hom toBase U.1, ideal_obj_top_eq_ker_ideal]
  exact ker_ideal_map_of_isPullback (DividedPowerScheme.closedFiberι base.S) toY toBase
    base.toClosedFiber cartesian ⟨⊤, isAffineOpen_top base.S.scheme⟩ U
    (le_preimage_top toBase U.1)

/-- **Stacks Project, Tag 07MW, part (1), the extension of `γ`.**  The divided power structure on
the ideal of the closed fibre `X` in a smooth lifting `Y` obtained by extending the divided powers
`γ` of the base.  Over an affine open `U ⊆ Y` the ideal is the image of the divided power ideal of
`S` under the flat map `Γ(S, ⊤) ⟶ Γ(Y, U)`, so `γ` extends to it uniquely by [Stacks, Tag 07H1],
and the extensions over the various affine opens agree. -/
noncomputable def smoothLiftingDividedPowers :
    DividedPowerStructure.{u, u, u} Y.sheaf
      (DividedPowerScheme.idealSheafAsSubmodule toY.ker) :=
  DividedPowerScheme.dividedPowerStructureOfAffineSections
    (base.S.dividedPowers.toDividedPowerRing (op ⊤)) Y _ toBase.appTop.hom
    (flat_appTop_restrict toBase)
    (ideal_map_appTop_restrict base prime_nilpotent Y toBase toY cartesian)

/-- **The extension of `γ` is compatible with `γ` on affine charts.**  Over affine opens `V ⊆ S`
and `W ⊆ Y` with `W` over `V`, the map on sections is a morphism of divided power rings.  The
divided power ideal of `S` on `V` is the image of its ideal on `⊤`, so this follows from
compatibility over `⊤` by `DividedPowers.IsDPMorphism.of_comp`. -/
theorem isDPMorphism_appLE (VS : base.S.scheme.affineOpens) (W : Y.affineOpens)
    (hW : W.1 ≤ toBase ⁻¹ᵁ VS.1) :
    DividedPowers.IsDPMorphism (base.S.dividedPowers.dividedPowers (op VS.1))
      ((smoothLiftingDividedPowers base prime_nilpotent Y toBase toY cartesian).dividedPowers
        (op W.1))
      (toBase.appLE VS.1 W.1 hW).hom := by
  have hres : base.S.ideal.obj (op VS.1) =
      Ideal.map (base.S.scheme.presheaf.map (homOfLE (show VS.1 ≤ ⊤ from le_top)).op).hom
        (base.S.ideal.obj (op (⊤ : base.S.scheme.Opens))) := by
    rw [DividedPowerScheme.ideal_obj_eq_ker_ideal_closedFiberι base.S VS,
      ideal_obj_top_eq_ker_ideal]
    exact (Scheme.IdealSheafData.map_ideal (U := VS)
      (V := ⟨⊤, isAffineOpen_top base.S.scheme⟩) _ (le_top (a := VS.1))).symm
  have hcomp : (toBase.appLE VS.1 W.1 hW).hom.comp
        (base.S.scheme.presheaf.map (homOfLE (show VS.1 ≤ ⊤ from le_top)).op).hom =
      (toBase.appLE ⊤ W.1 (le_preimage_top toBase W.1)).hom := by
    rw [← CommRingCat.hom_comp,
      toBase.map_appLE hW (homOfLE (show VS.1 ≤ ⊤ from le_top)).op]
  refine DividedPowers.IsDPMorphism.of_comp _ _ _
    (base.S.scheme.presheaf.map (homOfLE (show VS.1 ≤ ⊤ from le_top)).op).hom
    (toBase.appLE VS.1 W.1 hW).hom hres
    (base.S.dividedPowers.naturality (homOfLE (show VS.1 ≤ ⊤ from le_top)).op) ?_
  rw [hcomp, appLE_top_hom toBase W.1]
  exact DividedPowerScheme.dividedPowerStructureOfAffineSections_isDPMorphism
    (base.S.dividedPowers.toDividedPowerRing (op ⊤)) Y _ toBase.appTop.hom
    (flat_appTop_restrict toBase)
    (ideal_map_appTop_restrict base prime_nilpotent Y toBase toY cartesian) W

/-- **Stacks Project, Tag 07MW, part (1).**  A smooth lifting `Y` of the closed fibre, with the
ideal of the closed fibre in it and the extension of `γ` to that ideal, as a divided power
scheme. -/
noncomputable def smoothLiftingDividedPowerScheme : DividedPowerScheme.{u} where
  scheme := Y
  ideal := DividedPowerScheme.idealSheafAsSubmodule toY.ker
  isQuasicoherent := DividedPowerScheme.idealSheafAsSubmodule_isQuasicoherent toY.ker
  dividedPowers := smoothLiftingDividedPowers base prime_nilpotent Y toBase toY cartesian

/-- The underlying scheme of `smoothLiftingDividedPowerScheme` is `Y`. -/
@[simp]
theorem smoothLiftingDividedPowerScheme_scheme :
    (smoothLiftingDividedPowerScheme base prime_nilpotent Y toBase toY cartesian).scheme = Y :=
  rfl

/-- The structure map of a smooth lifting as a morphism of divided power schemes: its maps on
sections carry `γ` to its extension.  Compatibility is checked on affine charts by
`Crystalline.DividedPowerScheme.isDPMorphism_app_of_affine`. -/
noncomputable def smoothLiftingToBase :
    smoothLiftingDividedPowerScheme base prime_nilpotent Y toBase toY cartesian ⟶ base.S where
  hom := toBase
  compatible U :=
    DividedPowerScheme.isDPMorphism_app_of_affine
      (smoothLiftingDividedPowerScheme base prime_nilpotent Y toBase toY cartesian) base.S toBase
      (fun VS W hW => isDPMorphism_appLE base prime_nilpotent Y toBase toY cartesian VS W hW) U

/-- The underlying morphism of schemes of `smoothLiftingToBase` is `toBase`. -/
@[simp]
theorem smoothLiftingToBase_hom :
    (smoothLiftingToBase base prime_nilpotent Y toBase toY cartesian).hom = toBase :=
  rfl

/-- **Stacks Project, Tag 07MW, part (1).**  The closed fibre inside a smooth lifting, as a
divided power thickening of schemes: the immersion is a thickening by base change, and its ideal
is the divided power ideal of the lifting by construction. -/
noncomputable def smoothLiftingSchemeThickening : SchemeThickening.{u} where
  source := base.X
  target := smoothLiftingDividedPowerScheme base prime_nilpotent Y toBase toY cartesian
  immersion := toY
  isThickening := isThickening_toY base prime_nilpotent Y toBase toY cartesian
  ideal_eq_ker V := DividedPowerScheme.idealSheafAsSubmodule_obj_affine toY.ker V

/-- The source of `smoothLiftingSchemeThickening` is the closed fibre `base.X`. -/
@[simp]
theorem smoothLiftingSchemeThickening_source :
    (smoothLiftingSchemeThickening base prime_nilpotent Y toBase toY cartesian).source =
      base.X :=
  rfl

/-- The target of `smoothLiftingSchemeThickening` is `smoothLiftingDividedPowerScheme`. -/
@[simp]
theorem smoothLiftingSchemeThickening_target :
    (smoothLiftingSchemeThickening base prime_nilpotent Y toBase toY cartesian).target =
      smoothLiftingDividedPowerScheme base prime_nilpotent Y toBase toY cartesian :=
  rfl

/-- The immersion of `smoothLiftingSchemeThickening` is `toY`. -/
@[simp]
theorem smoothLiftingSchemeThickening_immersion :
    (smoothLiftingSchemeThickening base prime_nilpotent Y toBase toY cartesian).immersion = toY :=
  rfl

/-- **Stacks Project, Tag 07MW, part (1).**  The object `(X, Y, γ)` of the big crystalline
category `CRIS(X/S)` given by a smooth lifting `Y` of the closed fibre: the thickening `X ↪ Y`
with the extension of `γ`, the structure map `Y ⟶ S` and the identity of `X`. -/
noncomputable def smoothLiftingThickening : Thickening base where
  thickening := smoothLiftingSchemeThickening base prime_nilpotent Y toBase toY cartesian
  toBase := smoothLiftingToBase base prime_nilpotent Y toBase toY cartesian
  toX := 𝟙 base.X
  over_base := by simpa [sourceToBase] using cartesian.w

/-- The divided power thickening of `smoothLiftingThickening` is
`smoothLiftingSchemeThickening`. -/
@[simp]
theorem smoothLiftingThickening_thickening :
    (smoothLiftingThickening base prime_nilpotent Y toBase toY cartesian).thickening =
      smoothLiftingSchemeThickening base prime_nilpotent Y toBase toY cartesian :=
  rfl

/-- The structure map to `S` of `smoothLiftingThickening` is `smoothLiftingToBase`. -/
@[simp]
theorem smoothLiftingThickening_toBase :
    (smoothLiftingThickening base prime_nilpotent Y toBase toY cartesian).toBase =
      smoothLiftingToBase base prime_nilpotent Y toBase toY cartesian :=
  rfl

/-- The map to `X` of `smoothLiftingThickening` is the identity of `base.X`. -/
@[simp]
theorem smoothLiftingThickening_toX :
    (smoothLiftingThickening base prime_nilpotent Y toBase toY cartesian).toX = 𝟙 base.X :=
  rfl

/-- The object `(X, Y, γ)` of the small crystalline site `Cris(X/S)` given by a smooth lifting
`Y` of the closed fibre: the object `smoothLiftingThickening` of `CRIS(X/S)`, whose map to `X` is
the identity. -/
@[stacks 07MW "part (1): γ extends to the ideal of X in Y, and (X, Y, γ) is an object of Cris(X/S)"]
noncomputable def smoothLiftingCrystallineThickening : CrystallineThickening base where
  obj := smoothLiftingThickening base prime_nilpotent Y toBase toY cartesian
  property := by
    change IsOpenImmersion (𝟙 base.X)
    infer_instance

/-- The underlying object of `CRIS(X/S)` of `smoothLiftingCrystallineThickening` is
`smoothLiftingThickening`. -/
@[simp]
theorem smoothLiftingCrystallineThickening_obj :
    (smoothLiftingCrystallineThickening base prime_nilpotent Y toBase toY cartesian).obj =
      smoothLiftingThickening base prime_nilpotent Y toBase toY cartesian :=
  rfl

end GlobalCrystallineSituation

end Crystalline

end
