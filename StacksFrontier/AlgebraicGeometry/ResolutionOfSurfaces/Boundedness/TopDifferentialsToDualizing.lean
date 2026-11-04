module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Hull
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksCore.Tactic.StacksAttribute

/-!
# Top differential forms map to the dualizing module along a sequence of point blowups

Let `A` be a regular local ring of dimension two and let `A₀ ⊆ A` be a subring for which
`Ω_{A/A₀}` is free of rank `r`, so that `ω_A = Ω^r_{A/A₀}` is invertible and, `A` being
Gorenstein, is a dualizing module. If `X → Spec A` is the result of a sequence of blowups in
closed points then `X` is regular and proper over `A`, hence carries an invertible dualizing
module `ω_X` normalized relative to `ω_A`, and there is a map

`φ_X : (Ω^r_{X/Spec A₀})^{**} ⟶ ω_X`

extending the identification `(Ω^r_{A/A₀})^{**} = ω_A` at the generic point. The map is built by
induction along the sequence: for a blowup `b : X' ⟶ X` in a closed point, `ω_{X'} = b^!ω_X`, so
a map out of `(Ω^r_{X'/Spec A₀})^{**}` into `ω_{X'}` is a map out of its direct image into `ω_X`,
and that direct image is `(Ω^r_{X/Spec A₀})^{**}` again.

## Main definitions

* `Stacks.ResolutionOfSurfaces.BlowupDualizingData` collects the inputs the construction consumes
  at each blowup of the sequence: the identification of `ω_A` with `Ω^r_{A/A₀}`, the reflexivity
  of `Ω^r_{A/A₀}`, the computation of the direct image of the top forms along one blowup, and the
  duality isomorphism for that blowup.
* `Stacks.ResolutionOfSurfaces.BlowupDualizingData.baseHom` and
  `Stacks.ResolutionOfSurfaces.BlowupDualizingData.step` are the base case and the inductive step
  of the construction.
* `Stacks.ResolutionOfSurfaces.BlowupDualizingData.ofIsFiniteLocallyFreeOfRank` assembles the
  same inputs from the source's own hypothesis on the differentials, the reflexivity field being
  discharged rather than assumed.
* `Stacks.ResolutionOfSurfaces.BlowupDualizingData.ExtendsIdentification` is the property of a
  map `(Ω^n_{X/S₀})^{**} ⟶ ω_X` of extending the identification of `ω_S` with `Ω^n_{S/S₀}`: it
  corresponds, under the duality isomorphism of each blowup of the sequence composed with the
  direct-image identification, to a map one stage down, and at the bottom stage it restricts
  along `Ω^n_{S/S₀} ⟶ (Ω^n_{S/S₀})^{**}` to the given identification.

## Main results

* `Stacks.ResolutionOfSurfaces.BlowupDualizingData.toReflexiveHull_comp_baseHom`: the map at the
  bottom stage is the identification of `ω_A` with `Ω^r_{A/A₀}`.
* `Stacks.ResolutionOfSurfaces.BlowupDualizingData.dualityEquiv_step`: the map produced by one
  step corresponds, under the duality isomorphism of the blowup, to the map of the previous
  stage; this is what makes the family coherent, and anchors it at the identification of `ω_A`
  with `Ω^r_{A/A₀}`.
* `Stacks.ResolutionOfSurfaces.BlowupDualizingData.eq_baseHom_of_toReflexiveHull_comp` and
  `Stacks.ResolutionOfSurfaces.BlowupDualizingData.eq_step_of_dualityEquiv`: each clause of
  `ExtendsIdentification` determines the map it constrains, so the property pins a map rigidly
  rather than merely asking for one.
* `Stacks.ResolutionOfSurfaces.exists_extendsIdentification_hom_reflexiveHull_dualizing`:
  [Stacks, Tag 0B4T], the existence of `φ_X` extending the identification at the generic point,
  for every sequence of blowups in closed points.
* `Stacks.ResolutionOfSurfaces.nonempty_hom_reflexiveHull_relativeDifferentialForms_dualizing`:
  the weakening of the above that forgets the extension property.
* `Stacks.ResolutionOfSurfaces.isReflexive_relativeDifferentialForms_of_isFiniteLocallyFreeOfRank`:
  if `Ω_{S/S₀}` is finite locally free of rank `r` then `Ω^r_{S/S₀}` is reflexive. This is the
  source's reason for `ω_A = Ω^r_{A/A₀}` being invertible, and it discharges the field
  `isReflexive_base` of `BlowupDualizingData`.
* `Stacks.ResolutionOfSurfaces.exists_extendsIdentification_of_isFiniteLocallyFreeOfRank`: the
  existence statement with the reflexivity field replaced by the hypothesis on `Ω_{S/S₀}` that
  the source actually makes.

## Implementation notes

The sheaf `(Ω^n_{X/S})^{**}` is
`Stacks.AlgebraicGeometry.ReflexiveModules.reflexiveHull` of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms`, which is the sheaf the trace map of
[Stacks, Tag 0AX6] already maps into, and the sequence of blowups in closed points is
`Stacks.ResolutionOfSurfaces.PointBlowupChain`.

The dualizing modules themselves are a parameter `ω`, assigning a module to each scheme over
`Spec A`: their existence is [Stacks, Tag 0B4R] together with the regularity of the blowups of
[Stacks, Tag 0AGR] and the Gorenstein property of [Stacks, Tag 0AWX], and the normalization
relative to `ω_A` is the construction of [Stacks, Section 0AU3]. What the construction uses about
them is the duality isomorphism `Hom_{X'}(F, ω_{X'}) ≃ Hom_X(b_*F, ω_X)` for a blowup `b` in a
closed point, which is `ω_{X'} = b^!ω_X` in the form the proof applies it; it is a field of
`BlowupDualizingData`, as is the identification `b_*(Ω^n_{X'/S})^{**} = (Ω^n_{X/S})^{**}` of
[Stacks, Tags 0AGS, 0B4L, 0B3T] (the vanishing of `R^1b_*` is what makes the direct image agree
with the derived one, so no derived functor appears). Both quantify over an arbitrary blowup in a
closed point and neither mentions a map from the top forms to a dualizing module, so the
existence statement is not among the hypotheses.

The base case is not assumed: `Ω^n_{S/S₀}` being reflexive, the canonical map to its reflexive
hull is invertible and its inverse followed by `ω_A = Ω^r_{A/A₀}` is the identification at the
generic point from which the induction starts.

The clause "extending the given identification in the generic point" is expressed by
`ExtendsIdentification` without any appeal to generic points, by descending along the sequence
instead. A blowup `b : X' ⟶ X` in a closed point is an isomorphism away from that point, so a
map on `X'` and the map it corresponds to on `X` agree at the generic point; iterating, a map on
`X` at the top of the sequence is determined at the generic point by the map it descends to on
`S`, and `ExtendsIdentification` requires that one to restrict along
`Ω^n_{S/S₀} ⟶ (Ω^n_{S/S₀})^{**}` to `baseIso.inv`, which is the given identification. The
descent is not a function on sequences — `PointBlowupChain` is a `Prop`, so nothing can recurse
on it to build data — so the property is an inductive `Prop` indexed by the stage, with one
clause per constructor of the sequence. Each clause is an equation between morphisms already
named by `BlowupDualizingData`, and each determines the morphism it constrains
(`eq_baseHom_of_toReflexiveHull_comp`, `eq_step_of_dualityEquiv`), the duality map being a
bijection and the canonical map to the reflexive hull of `Ω^n_{S/S₀}` being invertible. So a map
with the property is unique stage by stage, and in particular the zero morphism has the property
only when the given identification is itself zero.

Of the four fields, `isReflexive_base` is the one this file discharges:
`isReflexive_relativeDifferentialForms_of_isFiniteLocallyFreeOfRank` derives it from the source's
hypothesis that `Ω_{A/A₀}` is free of rank `r`, via the determinant line bundle
`AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self` and
`AlgebraicGeometry.isReflexive_of_isInvertible`, and
`BlowupDualizingData.ofIsFiniteLocallyFreeOfRank` is the resulting constructor. The other three
stay as inputs. `baseIso` is the source's *definition* of `ω_A` and not a theorem about it: `ω` is
an arbitrary family here, and a dualizing module is pinned only up to shift and an invertible
twist, so nothing identifies `ω_S` with `Ω^n_{S/S₀}` except the normalization that this field
records. `pushforwardIso` and `dualityEquiv` quantify over an arbitrary scheme `W` over `S` and an
arbitrary closed point of it, with no regularity hypothesis, and neither has an input in this
repository: `b_*` of a reflexive hull along a blowup appears nowhere else, the exceptional
computation [Stacks, Tag 0B4L] is about `Ω_{X/S}` rather than about `(Ω^n_{X/S₀})^{**}`, the
proved part of [Stacks, Tag 0AGS] is the vanishing of `H^p` for `p ≥ 2` rather than of `R^1b_*`,
and [Stacks, Section 0AU3] has no declaration at all.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.ResolutionOfSurfaces

/-- The inputs the construction of `φ_X` consumes along a sequence of blowups in closed points of
`S`, for a structure morphism `p : S ⟶ S₀` and a degree `n`.

`ω` assigns a dualizing module to each scheme over `S`, normalized relative to
`ω_S = Ω^n_{S/S₀}`. The fields are, in order, the identification of `ω_S` with `Ω^n_{S/S₀}`, the
reflexivity of `Ω^n_{S/S₀}`, the direct image of the top forms along a blowup in a closed point,
and the duality isomorphism of that blowup. -/
public structure BlowupDualizingData {S₀ S : Scheme.{u}} (p : S ⟶ S₀) (n : ℤ)
    (ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules) where
  /-- The source's `ω_A = Ω^r_{A/A₀}`. -/
  baseIso : ω S (𝟙 S) ≅ Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n
  /-- `Ω^n_{S/S₀}` is reflexive. For `Ω_{A/A₀}` free of rank `n` the module `ω_A` is invertible,
  hence reflexive. -/
  isReflexive_base : IsReflexive (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)
  /-- The direct image along a blowup in a closed point of the reflexive hull of the top forms is
  the reflexive hull of the top forms downstairs: [Stacks, Tags 0AGS, 0B4L, 0B3T]. -/
  pushforwardIso : ∀ (W : Scheme.{u}) (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W)),
      (Scheme.Modules.pushforward
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))).obj
          (reflexiveHull (Scheme.Hom.relativeDifferentialForms
            ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) ≫ p) n)) ≅
        reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) n)
  /-- Duality for a blowup in a closed point: `ω_{X'} = b^!ω_X`, in the form
  `Hom_{X'}(F, ω_{X'}) ≃ Hom_X(b_*F, ω_X)`. See [Stacks, Section 0AU3]. -/
  dualityEquiv : ∀ (W : Scheme.{u}) (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W))
      (F : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)).Modules),
      (F ⟶ ω (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)) ≃
        ((Scheme.Modules.pushforward
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))).obj F ⟶ ω W h)

namespace BlowupDualizingData

variable {S₀ S : Scheme.{u}} {p : S ⟶ S₀} {n : ℤ}
  {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules} (D : BlowupDualizingData p n ω)

/-- The identification of `(Ω^n_{S/S₀})^{**}` with `ω_S`, the base case of the construction: the
canonical map to the reflexive hull is invertible, and `ω_S` is `Ω^n_{S/S₀}`. -/
public def baseHom :
    reflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n) ⟶ ω S (𝟙 S) :=
  haveI : IsIso (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 :=
    (isReflexive_iff_isIso_toReflexiveHull
      (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).mp D.isReflexive_base
  inv (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 ≫ D.baseIso.inv

/-- The canonical map to the reflexive hull of the top forms of `S` is invertible. -/
private theorem isIso_toReflexiveHull (D : BlowupDualizingData p n ω) :
    IsIso (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 :=
  (isReflexive_iff_isIso_toReflexiveHull _).mp D.isReflexive_base

/-- The base map is the given identification: precomposing it with the canonical map to the
reflexive hull recovers `ω_S = Ω^n_{S/S₀}`. In particular the induction is anchored at that
identification and not at an arbitrary map. -/
public theorem toReflexiveHull_comp_baseHom :
    (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 ≫ D.baseHom =
      D.baseIso.inv := by
  have := D.isIso_toReflexiveHull
  exact IsIso.hom_inv_id_assoc _ _

/-- One step of the construction: a map from the reflexive hull of the top forms to the dualizing
module is carried along a blowup in a closed point by the duality isomorphism of that blowup,
applied to the composite with the direct-image identification. -/
public def step {W : Scheme.{u}} (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W))
    (φ : reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) n) ⟶ ω W h) :
    reflexiveHull (Scheme.Hom.relativeDifferentialForms
        ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) ≫ p) n) ⟶
      ω (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) :=
  (D.dualityEquiv W h w hw _).symm ((D.pushforwardIso W h w hw).hom ≫ φ)

/-- The map produced by one step corresponds under the duality isomorphism of the blowup to the
map of the previous stage. This is the sense in which the family of maps along a sequence of
blowups is coherent, and hence in which it extends the identification of `ω_S` with
`(Ω^n_{S/S₀})^{**}` fixed by `baseHom`. -/
public theorem dualityEquiv_step {W : Scheme.{u}} (h : W ⟶ S) (w : W)
    (hw : IsClosed ({w} : Set W))
    (φ : reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) n) ⟶ ω W h) :
    D.dualityEquiv W h w hw _ (D.step h w hw φ) = (D.pushforwardIso W h w hw).hom ≫ φ :=
  (D.dualityEquiv W h w hw _).apply_symm_apply _

end BlowupDualizingData

/-- A morphism `φ : (Ω^n_{X/S₀})^{**} ⟶ ω_X`, for `X` a stage of a sequence of blowups in closed
points of `S`, *extends the identification of `ω_S` with `Ω^n_{S/S₀}`* when it descends along the
sequence to that identification. There is one clause per stage:

* at the bottom stage `X = S`, restricting `φ` along the canonical map
  `Ω^n_{S/S₀} ⟶ (Ω^n_{S/S₀})^{**}` gives `baseIso.inv`, the given identification itself;
* at a stage obtained by blowing up a closed point `w` of the previous one, the image of `φ`
  under the duality isomorphism of that blowup is the previous stage's map precomposed with the
  direct-image identification of the top forms.

Since a blowup in a closed point is an isomorphism away from that point, a map and the map it
corresponds to one stage down agree at the generic point; so the clauses say that `φ` agrees at
the generic point with `baseIso.inv`, which is the extension clause of [Stacks, Tag 0B4T].

Each clause determines the morphism it constrains — see `eq_baseHom_of_toReflexiveHull_comp` and
`eq_step_of_dualityEquiv` — so this is a rigid condition on `φ` and not a bookkeeping device: in
particular the zero morphism satisfies it only if `baseIso.inv` is zero. -/
public inductive BlowupDualizingData.ExtendsIdentification {S₀ S : Scheme.{u}} {p : S ⟶ S₀}
    {n : ℤ} {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules} (D : BlowupDualizingData p n ω) :
    ∀ {X : Scheme.{u}} {f : X ⟶ S},
      (reflexiveHull (Scheme.Hom.relativeDifferentialForms (f ≫ p) n) ⟶ ω X f) → Prop
  /-- At the bottom stage the map restricts to the given identification of `ω_S` with
  `Ω^n_{S/S₀}` along the canonical map to the reflexive hull. -/
  | base {φ : reflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n) ⟶ ω S (𝟙 S)}
      (hφ : (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 ≫ φ =
        D.baseIso.inv) :
      D.ExtendsIdentification φ
  /-- At a blowup in a closed point the map corresponds, under the duality isomorphism of that
  blowup, to a map of the previous stage with the same property composed with the direct-image
  identification of the top forms. -/
  | step {W : Scheme.{u}} {h : W ⟶ S}
      {φ : reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) n) ⟶ ω W h}
      (hφ : D.ExtendsIdentification φ) (w : W) (hw : IsClosed ({w} : Set W))
      {ψ : reflexiveHull (Scheme.Hom.relativeDifferentialForms
            ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) ≫ p) n) ⟶
          ω (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)}
      (hψ : D.dualityEquiv W h w hw _ ψ = (D.pushforwardIso W h w hw).hom ≫ φ) :
      D.ExtendsIdentification ψ

/-- The bottom clause of `BlowupDualizingData.ExtendsIdentification` determines the map it
constrains: `baseHom` is the only morphism restricting to the given identification along the
canonical map to the reflexive hull, that map being invertible by `isReflexive_base`. -/
public theorem BlowupDualizingData.eq_baseHom_of_toReflexiveHull_comp {S₀ S : Scheme.{u}}
    {p : S ⟶ S₀} {n : ℤ} {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules}
    (D : BlowupDualizingData p n ω)
    {φ : reflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n) ⟶ ω S (𝟙 S)}
    (hφ : (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 ≫ φ =
      D.baseIso.inv) :
    φ = D.baseHom := by
  have := D.isIso_toReflexiveHull
  rw [← D.toReflexiveHull_comp_baseHom] at hφ
  exact (cancel_epi _).mp hφ

/-- The blowup clause of `BlowupDualizingData.ExtendsIdentification` determines the map it
constrains: `step` is the only morphism corresponding to the previous stage's map under the
duality isomorphism, that isomorphism being a bijection. -/
public theorem BlowupDualizingData.eq_step_of_dualityEquiv {S₀ S : Scheme.{u}} {p : S ⟶ S₀}
    {n : ℤ} {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules} (D : BlowupDualizingData p n ω)
    {W : Scheme.{u}} (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W))
    (φ : reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) n) ⟶ ω W h)
    {ψ : reflexiveHull (Scheme.Hom.relativeDifferentialForms
          ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) ≫ p) n) ⟶
        ω (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)}
    (hψ : D.dualityEquiv W h w hw _ ψ = (D.pushforwardIso W h w hw).hom ≫ φ) :
    ψ = D.step h w hw φ := by
  have hsymm := (D.dualityEquiv W h w hw _).symm_apply_apply ψ
  rw [hψ] at hsymm
  exact hsymm.symm

/-- **Stacks Project, Tag 0B4T.** Let `A` be a regular local ring of dimension two and `A₀ ⊆ A` a
subring with `Ω_{A/A₀}` free of rank `r`, so that `ω_A = Ω^r_{A/A₀}` is invertible and, `A` being
Gorenstein, dualizing. If `X → Spec A` is the result of a sequence of blowups in closed points
then there is a map

`φ_X : (Ω^r_{X/Spec A₀})^{**} ⟶ ω_X`

extending the given identification in the generic point. The extension clause is
`BlowupDualizingData.ExtendsIdentification`: `φ_X` descends along the sequence, by the duality
isomorphism of each blowup and the direct-image identification of the top forms, to the map on
`Spec A` restricting to `baseIso.inv` along `Ω^r_{A/A₀} ⟶ (Ω^r_{A/A₀})^{**}`. By
`eq_baseHom_of_toReflexiveHull_comp` and `eq_step_of_dualityEquiv` that pins `φ_X` uniquely at
every stage, so the conclusion is not inhabited by an arbitrary morphism.

The proof is the induction of the source: the bottom stage is `baseHom`, anchored by
`toReflexiveHull_comp_baseHom`, and one blowup is `step`, whose correspondence to the previous
stage is `dualityEquiv_step`. -/
@[stacks 0B4T "the map extending the given identification at the generic point, by induction
along the sequence of blowups; the invertible dualizing modules of Tags 0B4R and 0AGR and the
Gorenstein property of Tag 0AWX enter as the parameter `ω` together with the field `baseIso`, the
duality isomorphism `ω_{X'} = b^!ω_X` of Section 0AU3 as the field `dualityEquiv`, and the
computation `b_*(Ω^r_{X'})^{**} = (Ω^r_X)^{**}` of Tags 0AGS, 0B4L and 0B3T as the field
`pushforwardIso`, all of `BlowupDualizingData`"]
public theorem exists_extendsIdentification_hom_reflexiveHull_dualizing {S₀ S : Scheme.{u}}
    {p : S ⟶ S₀} {n : ℤ} {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules}
    (D : BlowupDualizingData p n ω)
    {T : Set S} {X : Scheme.{u}} {f : X ⟶ S} (hf : PointBlowupChain S T X f) :
    ∃ φ : reflexiveHull (Scheme.Hom.relativeDifferentialForms (f ≫ p) n) ⟶ ω X f,
      D.ExtendsIdentification φ := by
  induction hf with
  | refl => exact ⟨D.baseHom, .base D.toReflexiveHull_comp_baseHom⟩
  | @step W h hh w hw hwT ih =>
    obtain ⟨φ, hφ⟩ := ih
    exact ⟨D.step h w hw φ, hφ.step w hw (D.dualityEquiv_step h w hw φ)⟩

/-- Existence of *some* morphism `(Ω^n_{X/S₀})^{**} ⟶ ω_X` along a chain of blowups in closed
points: the weakening of `exists_extendsIdentification_hom_reflexiveHull_dualizing` that forgets
the extension property.

This is NOT Stacks 0B4T and carries no `@[stacks]` attribute. 0B4T asserts a map *extending the
identification of `ω_A` with `(Ω^r_{A/A₀})^{**}` at the generic point*, and that extension
property is the content of the tag. The conclusion below states only `Nonempty (_ ⟶ _)`, which
the zero morphism inhabits for any pair of modules — verified by elaborating `⟨0⟩` against this
exact statement. It survives only as the forgetful consequence of the tagged statement, and is
proved from it by discarding the witness's property. -/
public theorem nonempty_hom_reflexiveHull_relativeDifferentialForms_dualizing
    {S₀ S : Scheme.{u}} {p : S ⟶ S₀} {n : ℤ}
    {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules} (D : BlowupDualizingData p n ω)
    {T : Set S} {X : Scheme.{u}} {f : X ⟶ S} (hf : PointBlowupChain S T X f) :
    Nonempty (reflexiveHull (Scheme.Hom.relativeDifferentialForms (f ≫ p) n) ⟶ ω X f) :=
  let ⟨φ, _⟩ := exists_extendsIdentification_hom_reflexiveHull_dualizing D hf
  ⟨φ⟩

/-! ### The reflexivity of the top forms, from the source's hypothesis on the differentials -/

/-- **If `Ω_{S/S₀}` is finite locally free of rank `r` then `Ω^r_{S/S₀}` is reflexive.** The sheaf
`Ω^r_{S/S₀}` is by definition the degree-`r` piece of the exterior algebra of `Ω_{S/S₀}`, so for
`Ω_{S/S₀}` of rank `r` it is the determinant line bundle and hence invertible by
`AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self`; an invertible module on an
integral locally Noetherian scheme is reflexive by
`AlgebraicGeometry.isReflexive_of_isInvertible`.

This is the source's reason for `ω_A = Ω^r_{A/A₀}` being invertible: `A` is a regular local ring
of dimension two, hence `Spec A` is integral and Noetherian, and `Ω_{A/A₀}` is free of rank `r`.
It discharges the field `BlowupDualizingData.isReflexive_base`. -/
public theorem isReflexive_relativeDifferentialForms_of_isFiniteLocallyFreeOfRank
    {S₀ S : Scheme.{u}} [AlgebraicGeometry.IsIntegral S] [IsLocallyNoetherian S]
    (q : S ⟶ S₀) (r : ℕ)
    (hfree : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials q) r) :
    IsReflexive (Scheme.Hom.relativeDifferentialForms q (r : ℤ)) :=
  have := hfree
  have : AlgebraicGeometry.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property
      (Scheme.Hom.relativeDifferentialForms q (r : ℤ)) :=
    (Scheme.Modules.isInvertible_exteriorPower_self
      (Scheme.Hom.relativeDifferentials q) r).toAlgebraicGeometry
  AlgebraicGeometry.isReflexive_of_isInvertible S _

/-- **The inputs of the construction, assembled from the source's hypothesis on the
differentials.** For `S` integral and locally Noetherian and `Ω_{S/S₀}` finite locally free of
rank `r` — the situation of the source, where `S = Spec A` for `A` a regular local ring of
dimension two and `Ω_{A/A₀}` is free of rank `r` — the reflexivity field of
`BlowupDualizingData` is not an assumption but a consequence, by
`isReflexive_relativeDifferentialForms_of_isFiniteLocallyFreeOfRank`.

The three remaining arguments are the fields this repository cannot yet supply. `baseIso` is the
source's definition of `ω_A`, a normalization rather than a theorem. `pushforwardIso` and
`dualityEquiv` quantify over an arbitrary scheme over `S` and an arbitrary closed point of it, and
have no input here: see the implementation notes. -/
public def BlowupDualizingData.ofIsFiniteLocallyFreeOfRank {S₀ S : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral S] [IsLocallyNoetherian S] {p : S ⟶ S₀} {r : ℕ}
    {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules}
    (hfree : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials p) r)
    (baseIso : ω S (𝟙 S) ≅ Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))
    (pushforwardIso : ∀ (W : Scheme.{u}) (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W)),
      (Scheme.Modules.pushforward
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))).obj
          (reflexiveHull (Scheme.Hom.relativeDifferentialForms
            ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) ≫ p)
              (r : ℤ))) ≅
        reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ)))
    (dualityEquiv : ∀ (W : Scheme.{u}) (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W))
      (F : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)).Modules),
      (F ⟶ ω (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)) ≃
        ((Scheme.Modules.pushforward
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))).obj F ⟶ ω W h)) :
    BlowupDualizingData p (r : ℤ) ω where
  baseIso := baseIso
  isReflexive_base :=
    isReflexive_relativeDifferentialForms_of_isFiniteLocallyFreeOfRank (𝟙 S ≫ p) r hfree
  pushforwardIso := pushforwardIso
  dualityEquiv := dualityEquiv

/-- `exists_extendsIdentification_hom_reflexiveHull_dualizing` with the reflexivity of
`Ω^r_{S/S₀}` replaced by the hypothesis the source actually makes, that `Ω_{S/S₀}` is finite
locally free of rank `r`.

This carries no `@[stacks]` attribute: it is the same assertion as the tagged statement with one
of the four inputs discharged, not a closer formalization of [Stacks, Tag 0B4T]. The tag's own
statement remains `exists_extendsIdentification_hom_reflexiveHull_dualizing`, and three inputs —
the normalization `baseIso`, the direct-image computation `pushforwardIso` and the duality
isomorphism `dualityEquiv` — are still hypotheses here. -/
public theorem exists_extendsIdentification_of_isFiniteLocallyFreeOfRank {S₀ S : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral S] [IsLocallyNoetherian S] {p : S ⟶ S₀} {r : ℕ}
    {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules}
    (hfree : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials p) r)
    (baseIso : ω S (𝟙 S) ≅ Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))
    (pushforwardIso : ∀ (W : Scheme.{u}) (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W)),
      (Scheme.Modules.pushforward
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))).obj
          (reflexiveHull (Scheme.Hom.relativeDifferentialForms
            ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) ≫ p)
              (r : ℤ))) ≅
        reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ)))
    (dualityEquiv : ∀ (W : Scheme.{u}) (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W))
      (F : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)).Modules),
      (F ⟶ ω (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)) ≃
        ((Scheme.Modules.pushforward
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))).obj F ⟶ ω W h))
    {T : Set S} {X : Scheme.{u}} {f : X ⟶ S} (hf : PointBlowupChain S T X f) :
    ∃ φ : reflexiveHull (Scheme.Hom.relativeDifferentialForms (f ≫ p) (r : ℤ)) ⟶ ω X f,
      (BlowupDualizingData.ofIsFiniteLocallyFreeOfRank hfree baseIso pushforwardIso
        dualityEquiv).ExtendsIdentification φ :=
  exists_extendsIdentification_hom_reflexiveHull_dualizing _ hf

end Stacks.ResolutionOfSurfaces

end
