module

public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Cocycle
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The norm of an invertible module along a finite morphism

Let `f : X ⟶ Y` be a finite morphism of schemes carrying a norm `N` on functions
(`Stacks.Norm.MorphismNormMap`, Tag 0BD1), and let `L` be an invertible `𝒪_X`-module. Cover `Y`
by opens `V` over which `L` becomes trivial on `f⁻¹V`, choose a generating section `s_V` of `L`
on each `f⁻¹V`, and write `s_V = u_{VW} s_W` on an overlap. The units `N(u_{VW})` satisfy the
cocycle condition because a norm is multiplicative, so they glue an invertible `𝒪_Y`-module:
this is `Stacks.Divisors.normInvertible`, the norm of `L`, and this file constructs it together
with the action of the norm on local generators, which is what pins it down.

## Main definitions

* `Stacks.Divisors.HasTrivializingTargetCover`: `Y` is covered by opens `V` over which `L` is
  trivial on `f⁻¹V`.
* `Stacks.Divisors.NormChart`: a target open over which `L` is trivialized upstairs.
* `Stacks.Divisors.normUnitsMap`: the map on units induced by the norm on functions.
* `Stacks.Divisors.normTransitionCocycle`: the normed transition units, as gluing data.
* `Stacks.Divisors.normInvertible`: the norm of `L`, the module glued from those data.
* `Stacks.Divisors.normGenerator`: the norm of a local generator.
* `Stacks.Divisors.NormInvertibleData` and `Stacks.Divisors.normInvertibleData`: the object-level
  norm packaged with its action on local generators and the two laws characterizing it.

## Main results

* `Stacks.Divisors.isInvertible_normInvertible`: the norm of `L` is invertible.
* `Stacks.Divisors.normGenerator_restrict`: the norm of a generator commutes with restriction.
* `Stacks.Divisors.normGenerator_smul`: the norm of a generator scaled by a function is the
  norm of the generator scaled by the norm of the function.
* `Stacks.Divisors.generatorRatioUnit_normGenerator`: the transition unit of two normed
  generators is the norm of the transition unit upstairs.

## Implementation notes

The construction takes a `Stacks.Norm.MorphismNormMap` — a multiplicative map on sections,
compatible with restriction and preserving pointwise vanishing — rather than a
`Stacks.Norm.MorphismNorm` of a specified degree `d`; the degree law `N(f^# g) = g ^ d` is not
used. Nor is `L` assumed invertible: the existence of the trivializing cover of the target, which
for an invertible `L` and finite `f` is `Stacks.Divisors.hasTrivializingTargetCover_of_isFinite`,
is taken as the hypothesis `Stacks.Divisors.HasTrivializingTargetCover`.

The index set of the cover is `NormChart f L`, the *subtype* of target opens admitting a
trivialization upstairs, rather than an abstractly chosen family: the chart data then carry
their own trivialization, the covering property is exactly `HasTrivializingTargetCover`, and no
choice of indexing has to be threaded through the construction. The trivialization of a chart
is turned into a generating section of `L` on the inverse image by `generatorOfIso`, and then
read back across the open immersion `(f ⁻¹ᵁ U).ι` with
`AlgebraicGeometry.Scheme.Modules.restrictAppIso`; this is `normChartSourceGenerator`, the only
place where the open-subscheme presentation of the sections is used.

The gluing is `Stacks.SheafOfModules.UnitTransitionCocycle`, which supplies both the sheaf
condition and the invertibility of the glued module.

A caution on orientation: `normTransitionCocycle`'s transition from chart `i` to chart `j` is
the norm of the ratio of the `j`-th generator to the `i`-th, which is the opposite order to the
one the cocycle field reads, and the cocycle law therefore closes with a `mul_comm`. The section
rings are commutative, so this costs nothing, but the order matters when matching the
coordinates of `normGenerator` against `sectionsSubmodule`'s compatibility condition.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0BUT](https://stacks.math.columbia.edu/tag/0BUT)
* [Stacks Project, Tag 0BD1](https://stacks.math.columbia.edu/tag/0BD1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules

universe u

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

variable {X Y : Scheme.{u}}

/-! ### The induced map on units -/

/-- The norm on functions, as a map of groups of units over an open of the target. -/
noncomputable def normUnitsMap (f : X ⟶ Y) (N : MorphismNormMap f) (U : Y.Opens) :
    (Γ(X, f ⁻¹ᵁ U))ˣ →* (Γ(Y, U))ˣ :=
  Units.map (N.app U)

/-- `normUnitsMap` commutes with restriction to a smaller open of the target. -/
theorem normUnitsMap_naturality (f : X ⟶ Y) (N : MorphismNormMap f)
    {U V : Y.Opens} (i : V ⟶ U) (a : (Γ(X, f ⁻¹ᵁ U))ˣ) :
    normUnitsMap f N V (Units.map (X.presheaf.map ((Opens.map f.base).map i).op).hom a) =
      Units.map (Y.presheaf.map i.op).hom (normUnitsMap f N U a) :=
  Units.ext (N.naturality i a.val)

/-- For a norm of degree `d`, the norm of the pullback of a unit `a` on `U` is `a ^ d`. -/
theorem normUnitsMap_pullback (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d) (U : Y.Opens)
    (a : (Γ(Y, U))ˣ) :
    normUnitsMap f N.toMorphismNormMap U (Units.map (f.app U).hom a) = a ^ d :=
  Units.ext (N.app_pullback U a.val)

/-! ### Charts -/

/-- A target open over which `L` becomes trivial on the inverse image, together with the
trivialization. -/
def NormChart (f : X ⟶ Y) (L : X.Modules) :=
  {U : Y.Opens //
    Nonempty (L.restrict (f ⁻¹ᵁ U).ι ≅ _root_.SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)}

/-- **The conclusion of Stacks Tag 0BUT**, as a hypothesis: every point of the target has an
open neighbourhood over which `L` becomes trivial on the inverse image. For a finite morphism
and an invertible `L` this holds, and that is Tag 0BUT. -/
def HasTrivializingTargetCover (f : X ⟶ Y) (L : X.Modules) : Prop :=
  ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
    Nonempty (L.restrict (f ⁻¹ᵁ U).ι ≅ _root_.SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)

/-- Let `f` be finite and `L` invertible. If every fibre of `f` carries a global section of `L`
vanishing nowhere on that fibre, then the target has a trivializing cover.

This is not a reduction of Tag 0BUT: for `f = 𝟙` on `ℙ¹` and `L = 𝒪(-1)` we have `Γ(L) = 0`, so
the hypothesis fails while `HasTrivializingTargetCover f L` holds. Tag 0BUT itself is
`hasTrivializingTargetCover_of_isFinite`. -/
theorem hasTrivializingTargetCover_of_fibrewise_nonvanishing (f : X ⟶ Y) [IsFinite f]
    (L : X.Modules)
    [IsInvertible X.presheaf
      (structureSheafRing
        X.toRingedSpace).property L]
    (hs : ∀ y : Y, ∃ s : L.sections, ∀ x : X, f.base x = y →
      x ∈ nonvanishingOpen (X := X.toRingedSpace) L s) :
    HasTrivializingTargetCover f L := fun y => by
  obtain ⟨s, hsy⟩ := hs y
  exact exists_isTrivial_preimage_of_fibre_subset_nonvanishingOpen f L s y hsy

/-- The charts cover the target. -/
theorem normChart_cover {f : X ⟶ Y} {L : X.Modules} (hL : HasTrivializingTargetCover f L) :
    (⊤ : Y.Opens) ≤ ⨆ i : NormChart f L, i.val := by
  intro y _
  obtain ⟨U, hy, e⟩ := hL y
  exact Opens.mem_iSup.mpr ⟨⟨U, e⟩, hy⟩

/-- The chart trivialization, read as a generating section of the restricted module on the top
open of the inverse-image subscheme. -/
noncomputable def normChartGenerator (f : X ⟶ Y) (L : X.Modules) (i : NormChart f L) :
    GeneratorSections (f ⁻¹ᵁ i.val).toScheme.toRingedSpace (L.restrict (f ⁻¹ᵁ i.val).ι) ⊤ :=
  generatorOfIso _ (Classical.choice i.property)

/-- The chart basis, read as a section of `L` over the image of the top open. -/
noncomputable def normChartSection (f : X ⟶ Y) (L : X.Modules) (i : NormChart f L) :
    Γ(L, (f ⁻¹ᵁ i.val).ι ''ᵁ (⊤ : ((f ⁻¹ᵁ i.val).toScheme).Opens)) :=
  (L.restrictAppIso (f ⁻¹ᵁ i.val).ι ⊤).hom (normChartGenerator f L i).val

/-- The image of the top open of the inverse-image subscheme is the inverse-image open itself,
so the chart basis is a section over `f ⁻¹ᵁ U`. -/
noncomputable def normChartSectionOnPreimage (f : X ⟶ Y) (L : X.Modules) (i : NormChart f L) :
    Γ(L, f ⁻¹ᵁ i.val) :=
  L.val.map (eqToHom (f ⁻¹ᵁ i.val).ι_image_top.symm).op (normChartSection f L i)

/-- The chart basis, read as a section of `L` on `f ⁻¹ᵁ U`, is a generator there. -/
noncomputable def normChartSourceGenerator (f : X ⟶ Y) (L : X.Modules) (i : NormChart f L) :
    GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ i.val) := by
  classical
  let B := f ⁻¹ᵁ i.val
  let g := normChartGenerator f L i
  refine ⟨normChartSectionOnPreimage f L i, ?_⟩
  intro V hV
  let e := opensRestrict B
  let W : B.toScheme.Opens := e.symm ⟨V, hV⟩
  have hImage : B.ι ''ᵁ W = V := congrArg Subtype.val (e.apply_symm_apply ⟨V, hV⟩)
  clear_value W
  revert hV
  subst V
  intro hV
  let eR := (B.ι.appIso W).commRingCatIsoToRingEquiv
  let eM := L.restrictAppIso B.ι W
  let xW := (L.restrict B.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op g.val
  have hsection : eM.hom xW =
      L.val.restrictₛₗ (homOfLE (B.ι.image_mono
        (leOfHom ((homOfLE (le_top : W ≤ ⊤)).op).unop))).op
        (normChartSection f L i) :=
    congrArg (fun q => q g.val)
      (Scheme.Modules.map_restrictAppIso_hom B.ι L ((homOfLE (le_top : W ≤ ⊤)).op))
  have hbij := g.property W le_top
  let sV : Γ(L, B.ι ''ᵁ W) := L.val.restrictₛₗ
    (homOfLE (B.ι.image_mono (leOfHom ((homOfLE (le_top : W ≤ ⊤)).op).unop))).op
    (normChartSection f L i)
  have hcomp (r : Γ(X, B.ι ''ᵁ W)) :
      eM.hom ((eR r) • xW) = (L.smul r).hom (eM.hom xW) := by
    have hs := Scheme.Modules.smul_restrictAppIso_hom_apply B.ι L W (eR r) xW
    rwa [show (B.ι.appIso W).inv (eR r) = r from eR.symm_apply_apply r] at hs
  have hsection' : eM.hom xW = sV := by
    simpa [sV, normChartSectionOnPreimage] using hsection
  have hsV : L.val.restrictₛₗ (homOfLE hV).op (normChartSectionOnPreimage f L i) = sV :=
    (PresheafOfModules.map_comp_apply L.val (eqToHom B.ι_image_top.symm).op
        (homOfLE hV).op (normChartSection f L i)).symm.trans
      (PresheafOfModules.congr_map_apply L.val (Subsingleton.elim _ _) _)
  have hfun : (fun r : Γ(X, B.ι ''ᵁ W) => r • sV) =
      fun r => eM.hom ((eR r) • xW) := by
    funext r
    rw [← hsection']
    exact (hcomp r).symm
  have hb := (ConcreteCategory.bijective_of_isIso eM.hom).comp
    (hbij.comp eR.bijective)
  rw [hsV]
  exact hfun.symm ▸ hb

/-- The chart basis, restricted over a smaller target open. -/
noncomputable def normChartGeneratorOver (f : X ⟶ Y) (L : X.Modules) (i : NormChart f L)
    (V : Y.Opens) (h : V ≤ i.val) : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V) :=
  generatorRestrict (X := X.toRingedSpace) L ((Opens.map f.base).map (homOfLE h)).le
    (normChartSourceGenerator f L i)

/-- Restricting `normChartGeneratorOver` from `V` to a smaller open `W` gives
`normChartGeneratorOver` over `W`. -/
theorem normChartGeneratorOver_restrict (f : X ⟶ Y) (L : X.Modules) (i : NormChart f L)
    {V W : Y.Opens} (hi : V ≤ i.val) (h : W ≤ V) :
    generatorRestrict (X := X.toRingedSpace) L ((Opens.map f.base).map (homOfLE h)).le
        (normChartGeneratorOver f L i V hi) =
      normChartGeneratorOver f L i W (h.trans hi) :=
  generatorRestrict_trans (X := X.toRingedSpace) L _ _ _

/-! ### The normed transition units -/

/-- The norm of the transition unit comparing two generators over the same target open. -/
noncomputable abbrev normGeneratorRatio (f : X ⟶ Y) (N : MorphismNormMap f)
    (L : X.Modules) (V : Y.Opens)
    (s t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V)) : (Γ(Y, V))ˣ :=
  normUnitsMap f N V (generatorRatioUnit (X := X.toRingedSpace) L (f ⁻¹ᵁ V) s t)

/-- `normGeneratorRatio` of the restrictions of two generators is the restriction of their
`normGeneratorRatio`. -/
theorem normGeneratorRatio_restrict (f : X ⟶ Y) (N : MorphismNormMap f) (L : X.Modules)
    {V W : Y.Opens} (h : W ≤ V) (s t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V)) :
    normGeneratorRatio f N L W
        (generatorRestrict (X := X.toRingedSpace) L ((Opens.map f.base).map (homOfLE h)).le s)
        (generatorRestrict (X := X.toRingedSpace) L ((Opens.map f.base).map (homOfLE h)).le t) =
      Units.map (Y.presheaf.map (homOfLE h).op).hom (normGeneratorRatio f N L V s t) :=
  (congrArg (normUnitsMap f N W)
    (generatorRatioUnit_restrict (X := X.toRingedSpace) L
      ((Opens.map f.base).map (homOfLE h)).le s t)).trans
        (normUnitsMap_naturality f N (homOfLE h) _)

/-- `normGeneratorRatio` is unchanged by transporting both generators along an isomorphism
`L ≅ M`. -/
theorem normGeneratorRatio_mapIso (f : X ⟶ Y) (N : MorphismNormMap f) {L M : X.Modules}
    (e : L ≅ M) (W : Y.Opens) (s t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)) :
    normGeneratorRatio f N M W (generatorMapIso (X := X.toRingedSpace) e (f ⁻¹ᵁ W) s)
        (generatorMapIso (X := X.toRingedSpace) e (f ⁻¹ᵁ W) t) =
      normGeneratorRatio f N L W s t :=
  congrArg (normUnitsMap f N W)
    (generatorRatioUnit_mapIso (X := X.toRingedSpace) e (f ⁻¹ᵁ W) s t)

/-- `normGeneratorRatio_restrict`, for generators known to be the restrictions of `s` and `t`. -/
private theorem normGeneratorRatio_restrict_of_eq (f : X ⟶ Y) (N : MorphismNormMap f)
    (L : X.Modules) {V W : Y.Opens} (h : W ≤ V)
    {s t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V)}
    {s' t' : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)}
    (hs : generatorRestrict (X := X.toRingedSpace) L
      ((Opens.map f.base).map (homOfLE h)).le s = s')
    (ht : generatorRestrict (X := X.toRingedSpace) L
      ((Opens.map f.base).map (homOfLE h)).le t = t') :
    Units.map (Y.presheaf.map (homOfLE h).op).hom (normGeneratorRatio f N L V s t) =
      normGeneratorRatio f N L W s' t' :=
  hs ▸ ht ▸ (normGeneratorRatio_restrict f N L h s t).symm

/-- Applying the norm to transition units preserves the cocycle identity, because a norm is
multiplicative. -/
theorem normUnitsMap_generatorRatio_comp (f : X ⟶ Y) (N : MorphismNormMap f)
    (U : Y.Opens) (L : X.Modules) (s t r : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ U)) :
    normGeneratorRatio f N L U t r * normGeneratorRatio f N L U s t =
      normGeneratorRatio f N L U s r :=
  ((map_mul (normUnitsMap f N U) _ _).symm).trans
    (congrArg (normUnitsMap f N U)
      (generatorRatioUnit_comp (X := X.toRingedSpace) L (f ⁻¹ᵁ U) s t r))

/-- If two generators downstairs differ by the norm of the scalar relating two generators
upstairs, their transition unit is the norm of the transition unit upstairs. -/
theorem normUnitsMap_generatorRatio (f : X ⟶ Y) (N : MorphismNormMap f) (U : Y.Opens)
    (L : X.Modules) (M : Y.Modules)
    (s t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ U))
    (s' t' : GeneratorSections Y.toRingedSpace M U)
    (h : t'.val = @SMul.smul ((structureSheaf Y.sheaf).obj.obj (op U)) (M.val.obj (op U)) _
      (N.app U (generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ U) s t)) s'.val) :
    normGeneratorRatio f N L U s t =
      generatorRatioUnit (X := Y.toRingedSpace) M U s' t' :=
  Units.ext (generatorRatio_unique (X := Y.toRingedSpace) M U s' t'
    (N.app U (generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ U) s t)) h)

/-- The norms of the changes of basis form a unit cocycle on the target. -/
noncomputable def normTransitionCocycle (f : X ⟶ Y) (N : MorphismNormMap f)
    (L : X.Modules) :
    UnitTransitionCocycle Y.toRingedSpace (fun i : NormChart f L => i.val) where
  transition i j V hi hj := normGeneratorRatio f N L V
    (normChartGeneratorOver f L j V hj) (normChartGeneratorOver f L i V hi)
  restrict {i j V W} hi hj h :=
    (normGeneratorRatio_restrict f N L h
        (normChartGeneratorOver f L j V hj) (normChartGeneratorOver f L i V hi)).symm.trans
      (congrArg₂ (normGeneratorRatio f N L W)
        (normChartGeneratorOver_restrict f L j hj h)
        (normChartGeneratorOver_restrict f L i hi h))
  symm i j V hi hj :=
    (congrArg (normUnitsMap f N V)
      (generatorRatioUnit_symm (X := X.toRingedSpace) L (f ⁻¹ᵁ V)
        (normChartGeneratorOver f L j V hj)
        (normChartGeneratorOver f L i V hi))).trans (map_inv _ _)
  cocycle i j k V hi hj hk :=
    (mul_comm _ _).trans (normUnitsMap_generatorRatio_comp f N V L
      (normChartGeneratorOver f L k V hk) (normChartGeneratorOver f L j V hj)
      (normChartGeneratorOver f L i V hi))

/-- **The norm of an invertible module along a finite morphism carrying a norm of degree `d`.**
It is the module glued from the normed transition units of the chart generators. -/
@[ega "II 6.5.2"]
noncomputable def normInvertible (f : X ⟶ Y) (N : MorphismNormMap f) (L : X.Modules) :
    Y.Modules :=
  (normTransitionCocycle f N L).glue

/-- **The norm of an invertible module is invertible.** -/
@[ega "II 6.5.2" "partial"]
theorem isInvertible_normInvertible (f : X ⟶ Y) (N : MorphismNormMap f) (L : X.Modules)
    (hL : HasTrivializingTargetCover f L) :
    IsInvertible Y.presheaf (structureSheaf Y.sheaf).property (normInvertible f N L) :=
  (normTransitionCocycle f N L).isInvertible_glue (normChart_cover hL)

/-! ### The norm of a local generator -/

/-- The coordinates, in the chart `i`, of the norm of a generator `s` of `L` over `f ⁻¹ᵁ W`. -/
noncomputable def normGeneratorCoordinates (f : X ⟶ Y) (N : MorphismNormMap f)
    (L : X.Modules) (W : Y.Opens) (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W))
    (i : NormChart f L) : (Γ(Y, W ⊓ i.val))ˣ :=
  normGeneratorRatio f N L (W ⊓ i.val) (normChartGeneratorOver f L i _ inf_le_right)
    (generatorRestrict (X := X.toRingedSpace) L
      ((Opens.map f.base).map (homOfLE (inf_le_left : W ⊓ i.val ≤ W))).le s)

/-- The chart coordinates of the norm of a generator, restricted to an open `Z` inside the
chart, are the norm of the transition unit between the chart generator over `Z` and the
restriction of `s` to `Z`. -/
theorem normGeneratorCoordinates_restrictLe (f : X ⟶ Y) (N : MorphismNormMap f)
    (L : X.Modules) {W : Y.Opens} (i : NormChart f L) {Z : Y.Opens} (hZ : Z ≤ W ⊓ i.val)
    (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)) :
    Units.map (Y.presheaf.map (homOfLE hZ).op).hom (normGeneratorCoordinates f N L W s i) =
      normGeneratorRatio f N L Z
        (normChartGeneratorOver f L i Z (hZ.trans inf_le_right))
        (generatorRestrict (X := X.toRingedSpace) L
          ((Opens.map f.base).map (homOfLE (hZ.trans inf_le_left))).le s) :=
  normGeneratorRatio_restrict_of_eq f N L hZ
    (normChartGeneratorOver_restrict f L i (inf_le_right : W ⊓ i.val ≤ i.val) hZ)
    (generatorRestrict_trans (X := X.toRingedSpace) L _ _ s)

/-- The chart coordinates of the norm of a generator are compatible: on the overlap of two
charts they differ by the normed transition unit of `normTransitionCocycle`. -/
theorem normGeneratorCoordinates_compatible (f : X ⟶ Y) (N : MorphismNormMap f)
    (L : X.Modules) (W : Y.Opens) (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W))
    (i j : NormChart f L) :
    (normTransitionCocycle f N L).transition i j (W ⊓ i.val ⊓ (W ⊓ j.val))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) *
      Units.map (Y.presheaf.map
        (homOfLE (inf_le_left : W ⊓ i.val ⊓ (W ⊓ j.val) ≤ W ⊓ i.val)).op).hom
        (normGeneratorCoordinates f N L W s i) =
      Units.map (Y.presheaf.map
        (homOfLE (inf_le_right : W ⊓ i.val ⊓ (W ⊓ j.val) ≤ W ⊓ j.val)).op).hom
        (normGeneratorCoordinates f N L W s j) := by
  have hA := normGeneratorCoordinates_restrictLe f N L i
    (inf_le_left : W ⊓ i.val ⊓ (W ⊓ j.val) ≤ W ⊓ i.val) s
  have hB := normGeneratorCoordinates_restrictLe f N L j
    (inf_le_right : W ⊓ i.val ⊓ (W ⊓ j.val) ≤ W ⊓ j.val) s
  rw [hA, hB]
  exact (mul_comm _ _).trans (normUnitsMap_generatorRatio_comp f N _ L _ _ _)

/-- **The norm of a local generator**: a generator of `L` over `f ⁻¹ᵁ W` gives a generator of
the norm of `L` over `W`. -/
noncomputable def normGenerator (f : X ⟶ Y) (N : MorphismNormMap f) (L : X.Modules)
    (hL : HasTrivializingTargetCover f L) (W : Y.Opens)
    (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)) :
    GeneratorSections Y.toRingedSpace (normInvertible f N L) W :=
  (normTransitionCocycle f N L).generatorOfUnitCoordinates (normChart_cover hL) W
    ⟨fun i => (normGeneratorCoordinates f N L W s i).val,
      fun i j => congrArg Units.val (normGeneratorCoordinates_compatible f N L W s i j)⟩
    fun i => (normGeneratorCoordinates f N L W s i).isUnit

/-- The chart coordinates of the norm of a generator over `W`, restricted to `V ≤ W`, are the
chart coordinates of the norm of the restricted generator. -/
theorem normGeneratorCoordinates_restrict (f : X ⟶ Y) (N : MorphismNormMap f)
    (L : X.Modules) {W V : Y.Opens} (h : V ≤ W)
    (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)) (i : NormChart f L) :
    Units.map (Y.presheaf.map (homOfLE (inf_le_inf_right i.val h)).op).hom
        (normGeneratorCoordinates f N L W s i) =
      normGeneratorCoordinates f N L V
        (generatorRestrict (X := X.toRingedSpace) L
          ((Opens.map f.base).map (homOfLE h)).le s) i :=
  normGeneratorRatio_restrict_of_eq f N L (inf_le_inf_right i.val h)
    (normChartGeneratorOver_restrict f L i (inf_le_right : W ⊓ i.val ≤ i.val)
      (inf_le_inf_right i.val h))
    ((generatorRestrict_trans (X := X.toRingedSpace) L _ _ s).trans
      (generatorRestrict_trans (X := X.toRingedSpace) L _ _ s).symm)

/-- **The norm of a generator commutes with restriction.** -/
theorem normGenerator_restrict (f : X ⟶ Y) (N : MorphismNormMap f) (L : X.Modules)
    (hL : HasTrivializingTargetCover f L) {W V : Y.Opens} (h : V ≤ W)
    (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)) :
    (normGenerator f N L hL V
          (generatorRestrict (X := X.toRingedSpace) L
            ((Opens.map f.base).map (homOfLE h)).le s)).val =
      (normInvertible f N L).val.restrictₛₗ (homOfLE h).op
        (normGenerator f N L hL W s).val :=
  Subtype.ext <| funext fun i =>
    congrArg Units.val (normGeneratorCoordinates_restrict f N L h s i).symm

/-- **The norm of a generator scaled by a function** is the norm of the generator scaled by the
norm of the function. -/
theorem normGenerator_smul (f : X ⟶ Y) (N : MorphismNormMap f) (L : X.Modules)
    (hL : HasTrivializingTargetCover f L) (W : Y.Opens)
    (s t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)) (a : Γ(X, f ⁻¹ᵁ W))
    (ha : t.val = @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ W)))
      (L.val.obj (op (f ⁻¹ᵁ W))) _ a s.val) :
    (normGenerator f N L hL W t).val =
      @SMul.smul ((structureSheaf Y.sheaf).obj.obj (op W))
        ((normInvertible f N L).val.obj (op W)) _ (N.app W a)
        (normGenerator f N L hL W s).val := by
  apply Subtype.ext
  funext i
  let h : W ⊓ i.val ≤ W := inf_le_left
  let hs := ((Opens.map f.base).map (homOfLE h)).le
  let b := normChartGeneratorOver f L i (W ⊓ i.val) inf_le_right
  have ht : (generatorRestrict (X := X.toRingedSpace) L hs t).val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ (W ⊓ i.val))))
        (L.val.obj (op (f ⁻¹ᵁ (W ⊓ i.val)))) _
        (X.presheaf.map ((Opens.map f.base).map (homOfLE h)).op a)
        (generatorRestrict (X := X.toRingedSpace) L hs s).val := by
    show L.val.map (homOfLE hs).op t.val = _
    rw [ha]
    exact L.val.map_smul _ _ _
  show N.app (W ⊓ i.val) (generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ (W ⊓ i.val)) b
      (generatorRestrict (X := X.toRingedSpace) L hs t)) =
    Y.presheaf.map (homOfLE h).op (N.app W a) *
      N.app (W ⊓ i.val) (generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ (W ⊓ i.val)) b
        (generatorRestrict (X := X.toRingedSpace) L hs s))
  rw [generatorRatio_smul (X := X.toRingedSpace) L _ b _ _ _ ht]
  exact ((N.app (W ⊓ i.val)).map_mul _ _).trans (congrArg (· * _) (N.naturality (homOfLE h) a))

/-- **The transition unit of two normed generators is the norm of the transition unit
upstairs.** This identity is what makes the construction well defined. -/
theorem generatorRatioUnit_normGenerator (f : X ⟶ Y) (N : MorphismNormMap f)
    (L : X.Modules) (hL : HasTrivializingTargetCover f L) (W : Y.Opens)
    (s t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)) :
    generatorRatioUnit (X := Y.toRingedSpace) (normInvertible f N L) W
        (normGenerator f N L hL W s) (normGenerator f N L hL W t) =
      normGeneratorRatio f N L W s t :=
  (normUnitsMap_generatorRatio f N W L (normInvertible f N L) s t
    (normGenerator f N L hL W s) (normGenerator f N L hL W t)
    (normGenerator_smul f N L hL W s t _
      (generatorRatio_spec (X := X.toRingedSpace) L (f ⁻¹ᵁ W) s t))).symm

/-! ### The bundled data -/

/-- The object-level norm of invertible modules, packaged with its action on local generators
and the two laws that characterize it. -/
structure NormInvertibleData (f : X ⟶ Y) (N : MorphismNormMap f) where
  /-- The norm of a module. -/
  obj (L : X.Modules) : Y.Modules
  /-- The norm of an invertible module is invertible. -/
  obj_invertible (L : X.Modules) (hL : HasTrivializingTargetCover f L) :
    IsInvertible Y.presheaf (structureSheaf Y.sheaf).property (obj L)
  /-- A local generator upstairs gives a local generator downstairs. -/
  generator (L : X.Modules) (hL : HasTrivializingTargetCover f L) (U : Y.Opens) :
    GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ U) → GeneratorSections Y.toRingedSpace (obj L) U
  /-- The norm of a local generator commutes with restriction. -/
  generator_restrict (L : X.Modules) (hL : HasTrivializingTargetCover f L)
      {U V : Y.Opens} (i : V ⟶ U)
      (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ U))
      (t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V))
      (ht : t.val = L.val.restrictₛₗ ((Opens.map f.base).map i).op s.val) :
    (generator L hL V t).val = (obj L).val.restrictₛₗ i.op (generator L hL U s).val
  /-- The ratio of two generators is sent to its function norm. -/
  generator_smul (L : X.Modules) (hL : HasTrivializingTargetCover f L) (U : Y.Opens)
      (s t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ U)) (a : Γ(X, f ⁻¹ᵁ U))
      (ha : t.val = @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ U)))
        (L.val.obj (op (f ⁻¹ᵁ U))) _ a s.val) :
    (generator L hL U t).val = @SMul.smul ((structureSheaf Y.sheaf).obj.obj (op U))
      ((obj L).val.obj (op U)) _ (N.app U a) (generator L hL U s).val

/-- **The norm construction of invertible modules induced by a norm on functions**: the norm of
modules with its action on local generators. -/
@[ega "II 6.5.2"]
noncomputable def normInvertibleData (f : X ⟶ Y) (N : MorphismNormMap f) :
    NormInvertibleData f N where
  obj L := normInvertible f N L
  obj_invertible L hL := isInvertible_normInvertible f N L hL
  generator L hL U s := normGenerator f N L hL U s
  generator_restrict L hL {U V} i s t ht := by
    have hst : t = generatorRestrict (X := X.toRingedSpace) L
        ((Opens.map f.base).map (homOfLE i.le)).le s := Subtype.ext ht
    rw [hst]
    exact normGenerator_restrict f N L hL i.le s
  generator_smul L hL U s t a ha := normGenerator_smul f N L hL U s t a ha

end Stacks.Divisors
