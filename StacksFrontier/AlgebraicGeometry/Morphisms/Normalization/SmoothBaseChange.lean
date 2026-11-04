module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty

/-!
# Normalization commutes with smooth base change

Let `φ : X ⟶ Y` be a smooth morphism of schemes and assume every quasi-compact open of `Y` has
finitely many irreducible components. Then the same holds for `X`, and the square

```
X^ν ⟶ Y^ν
 |      |
 v      v
 X  ⟶  Y
```

formed by the normalization morphisms and the morphism of normalizations induced by `φ` is
cartesian: `X^ν` is the base change `X ×_Y Y^ν`.

## Main results

* `AlgebraicGeometry.mem_genericPoints_fiberι`: a generic point of an irreducible component of
  the fibre of a morphism over a generic point of an irreducible component of the target is a
  generic point of an irreducible component of the source.
* `AlgebraicGeometry.mem_genericPoints_pullbackSnd_of_flat`: for `φ` flat and `g` carrying
  generic points of irreducible components to such generic points, the second projection of
  `Z ×_Y X` carries generic points of irreducible components to generic points of irreducible
  components of `X`.
* `AlgebraicGeometry.isPullback_normalizationSchemeMap_of_flat`: the normalization square of a
  flat morphism along which the base change of the normalization morphism of the target is
  normal is cartesian.
* `AlgebraicGeometry.isPullback_normalizationSchemeMap_of_smooth`: the normalization square of a
  smooth morphism is cartesian. Together with
  `AlgebraicGeometry.finite_irreducibleComponents_of_smooth` this is Tag 07TD.

## Implementation notes

Both inclusions `X^ν ⇄ X ×_Y Y^ν` come from the universal property of the normalization of a
scheme, Tag 035Q part (4), available as
`AlgebraicGeometry.Scheme.existsUnique_lift_normalization`: a morphism to `X` from a normal
scheme whose generic points go to generic points factors uniquely through `X^ν`. That argument,
which is the one of
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale`, consumes three facts about
`N = X ×_Y Y^ν`: that finiteness of irreducible components of quasi-compact opens ascends along
`φ`, that `N` is normal, and that the generic points of `N` are carried to generic points of `X`
and of `Y`.

For a *smooth* `φ` the first is `AlgebraicGeometry.finite_irreducibleComponents_of_smooth` and
the second is the ascent half of Tag 033C, `AlgebraicGeometry.isNormal_of_smooth`, applied to
the projection `N ⟶ Y^ν`, a base change of `φ`. The third is the step at which the étale proof
argues that the fibre of `φ` over a generic point of `Y` consists of generic points of `X` — true
for a quasi-finite morphism and false for a smooth one, whose fibres are positive dimensional.

It is proved here for any flat `φ` instead, with no finiteness or quasi-finiteness, as
`AlgebraicGeometry.mem_genericPoints_pullbackSnd_of_flat`. Let `w` be a generic point of
`N = Y^ν ×_Y X`, let `ζ` be its image in `Y^ν` and `y` the image of `ζ` in `Y`. The projection
`p : N ⟶ Y^ν` is flat, being a base change of `φ`, so `ζ` is a generic point of `Y^ν`, and `y` is
then a generic point of `Y` because the normalization morphism carries generic points to generic
points. Now `w` is a generic point of the *fibre* `p⁻¹(ζ)`, and that fibre is the base change of
the fibre `φ⁻¹(y)` along the residue field extension `κ(y) ⟶ κ(ζ)` — this is Mathlib's
`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback` applied to the cartesian
square defining `N`. A base change of the spectrum of a field extension is flat, so the induced
morphism of fibres carries `w` to a generic point of `φ⁻¹(y)`; and a generic point of the fibre
over a *generic* point of the target is a generic point of the source, which is
`AlgebraicGeometry.mem_genericPoints_fiberι`. The image of `w` in `X` is the image of that
generic point of the fibre, hence a generic point of `X`.

## References

* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Generic points of a fibre over a generic point -/

/-- A generic point of an irreducible component of the fibre of `f : X ⟶ Y` over a generic point
of an irreducible component of `Y` is a generic point of an irreducible component of `X`.

A point of `X` specializing to it lies over a point of `Y` specializing to `y`, hence over `y`
itself, so it lies in the fibre; the fibre inclusion is an embedding, so the specialization
happens inside the fibre, where the point is generic. -/
@[ega "0 2.1.8" "partial"]
theorem mem_genericPoints_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (hy : y ∈ genericPoints Y) {z : f.fiber y} (hz : z ∈ genericPoints (f.fiber y)) :
    f.fiberι y z ∈ genericPoints X := by
  refine (TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq _).2 fun x hx ↦ ?_
  have hfz : f (f.fiberι y z) = y := by
    have hmem : f.fiberι y z ∈ f ⁻¹' {y} := (f.range_fiberι y).le ⟨z, rfl⟩
    simpa using hmem
  have hxy : f x = y :=
    (TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq y).1 hy _
      (by simpa only [hfz] using hx.map f.continuous)
  have hlift : f.fiberι y ((f.fiberHomeo y).symm ⟨x, hxy⟩) = x :=
    Scheme.Hom.fiberι_fiberHomeo_symm f y ⟨x, hxy⟩
  have hspec : (f.fiberHomeo y).symm ⟨x, hxy⟩ ⤳ z :=
    (f.fiberι y).isEmbedding.isInducing.specializes_iff.mp (by rwa [hlift])
  rw [← hlift,
    (TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq z).1 hz _ hspec]

/-! ### Generic points of a base change along a flat morphism -/

/-- The second projection of `Z ×_Y X`, for `φ : X ⟶ Y` flat and `g : Z ⟶ Y` carrying generic
points of irreducible components to such generic points, carries generic points of irreducible
components to generic points of irreducible components of `X`.

The first projection is flat, being a base change of `φ`, so a generic point `w` of `Z ×_Y X`
lies over a generic point `ζ` of `Z` and therefore over a generic point `y = g ζ` of `Y`, and `w`
is a generic point of the fibre of the first projection over `ζ`. That fibre is the base change
of the fibre of `φ` over `y` along `κ(y) ⟶ κ(ζ)`, hence flat over it, so the image of `w` is a
generic point of the fibre of `φ` over `y`, and `y` being generic that image is a generic point
of `X`. -/
theorem mem_genericPoints_pullbackSnd_of_flat {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (φ : X ⟶ Y)
    [Flat φ] (hg : ∀ z : Z, z ∈ genericPoints Z → g z ∈ genericPoints Y)
    {w : ↥(pullback g φ)} (hw : w ∈ genericPoints ↥(pullback g φ)) :
    pullback.snd g φ w ∈ genericPoints X := by
  set ζ : Z := pullback.fst g φ w
  have hy : g ζ ∈ genericPoints Y := hg ζ (mem_genericPoints_of_flat (pullback.fst g φ) hw)
  -- The comparison of the fibre of the first projection over `ζ` with the fibre of `φ` over
  -- `g ζ`, which is a base change of `Spec κ(ζ) ⟶ Spec κ(g ζ)`.
  have hfac : (pullback.fst g φ).fiberι ζ ≫ pullback.snd g φ ≫ φ =
      ((pullback.fst g φ).fiberToSpecResidueField ζ ≫ Spec.map (g.residueFieldMap ζ)) ≫
        Y.fromSpecResidueField (g ζ) := by
    rw [Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← pullback.condition, ← Category.assoc, ← Category.assoc,
      Scheme.Hom.fiber_fac (pullback.fst g φ) ζ]
  set μ : (pullback.fst g φ).fiber ζ ⟶ φ.fiber (g ζ) :=
    pullback.lift ((pullback.fst g φ).fiberι ζ ≫ pullback.snd g φ)
      ((pullback.fst g φ).fiberToSpecResidueField ζ ≫ Spec.map (g.residueFieldMap ζ))
      (by rw [Category.assoc]; exact hfac)
  have hsq : IsPullback μ ((pullback.fst g φ).fiberToSpecResidueField ζ)
      (φ.fiberToSpecResidueField (g ζ)) (Spec.map (g.residueFieldMap ζ)) :=
    isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback g φ).flip ζ
  have hfieldflat : Flat (Spec.map (g.residueFieldMap ζ)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField (Y.residueField (g ζ))) _
  have hμflat : Flat μ :=
    MorphismProperty.of_isPullback (P := @Flat) hsq.flip hfieldflat
  -- `w`, read in the fibre of the first projection over `ζ`.
  set w' : (pullback.fst g φ).fiber ζ := ((pullback.fst g φ).fiberHomeo ζ).symm ⟨w, rfl⟩ with hw'
  have hw'generic : w' ∈ genericPoints ((pullback.fst g φ).fiber ζ) :=
    genericPoint_mem_fiber_of_genericPoint (pullback.fst g φ) w hw ζ rfl
  have hcomp : μ ≫ φ.fiberι (g ζ) = (pullback.fst g φ).fiberι ζ ≫ pullback.snd g φ :=
    pullback.lift_fst _ _ _
  have himage : φ.fiberι (g ζ) (μ w') = pullback.snd g φ w := by
    rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply, hw',
      Scheme.Hom.fiberι_fiberHomeo_symm]
  rw [← himage]
  exact mem_genericPoints_fiberι φ hy (mem_genericPoints_of_flat μ hw'generic)

/-! ### The normalization square of a flat morphism -/

section

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) [Flat φ]
  (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
  (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)

/-- A generic point of an irreducible component of the base change of the normalization morphism
of `Y` along a flat `φ` lies over a generic point of an irreducible component of `Y`. -/
private theorem mem_genericPoints_pullbackFst_normalization
    {z : ↥(pullback (Y.normalization hY) φ)}
    (hz : z ∈ genericPoints ↥(pullback (Y.normalization hY) φ)) :
    (pullback.fst (Y.normalization hY) φ ≫ Y.normalization hY) z ∈ genericPoints Y := by
  rw [Scheme.Hom.comp_apply]
  exact Scheme.normalization_mem_genericPoints Y hY
    (mem_genericPoints_of_flat (pullback.fst (Y.normalization hY) φ) hz)

/-- A generic point of an irreducible component of the base change of the normalization morphism
of `Y` along a flat `φ` is carried by the second projection to a generic point of an irreducible
component of `X`. -/
private theorem mem_genericPoints_pullbackSnd_normalization
    {z : ↥(pullback (Y.normalization hY) φ)}
    (hz : z ∈ genericPoints ↥(pullback (Y.normalization hY) φ)) :
    pullback.snd (Y.normalization hY) φ z ∈ genericPoints X :=
  mem_genericPoints_pullbackSnd_of_flat (Y.normalization hY) φ
    (fun _ hz ↦ Scheme.normalization_mem_genericPoints Y hY hz) hz

/-- The normalization square of a flat morphism along which the base change of the normalization
morphism of the target is normal is cartesian: the normalization of the source is the base change
of the normalization of the target.

This is the conclusion of [Stacks, Tag 07TD] for a flat morphism with that one extra property;
for a smooth morphism the property holds, which is
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_smooth`. -/
theorem isPullback_normalizationSchemeMap_of_flat
    (hnormal : IsNormal (pullback (Y.normalization hY) φ)) :
    IsPullback (normalizationSchemeMap φ hX hY) (X.normalization hX) (Y.normalization hY) φ := by
  have hsq : normalizationSchemeMap φ hX hY ≫ Y.normalization hY
      = X.normalization hX ≫ φ := normalizationSchemeMap_normalization φ hX hY
  have := hnormal
  have hXνnormal : IsNormal (X.normalizationScheme hX) := Scheme.isNormal_normalizationScheme X hX
  -- The morphism from the normalization of `X` into the fibre product.
  set lift : X.normalizationScheme hX ⟶ pullback (Y.normalization hY) φ :=
    pullback.lift (normalizationSchemeMap φ hX hY) (X.normalization hX) hsq with hliftdef
  -- The morphism back, from the universal property of the normalization of `X`.
  obtain ⟨u, hu, -⟩ := Scheme.existsUnique_lift_normalization hX
    (pullback.snd (Y.normalization hY) φ)
    (fun η ↦ mem_genericPoints_pullbackSnd_normalization φ hY η.2)
  -- One composite is the identity because only one morphism lifts `ν_X` through itself.
  have hunique := Scheme.existsUnique_lift_normalization hX (X.normalization hX)
    (fun η ↦ Scheme.normalization_mem_genericPoints X hX η.2)
  have hliftu : lift ≫ u = 𝟙 (X.normalizationScheme hX) :=
    hunique.unique (by rw [Category.assoc, hu, hliftdef, pullback.lift_snd])
      (Category.id_comp _)
  -- The other composite is the identity because only one morphism lifts the first projection.
  have huniqueY := Scheme.existsUnique_lift_normalization hY
    (pullback.fst (Y.normalization hY) φ ≫ Y.normalization hY)
    (fun η ↦ mem_genericPoints_pullbackFst_normalization φ hY η.2)
  have hfst : u ≫ normalizationSchemeMap φ hX hY = pullback.fst (Y.normalization hY) φ :=
    huniqueY.unique
      (by rw [Category.assoc, hsq, ← Category.assoc, hu, pullback.condition]) rfl
  have hulift : u ≫ lift = 𝟙 (pullback (Y.normalization hY) φ) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hliftdef, pullback.lift_fst, hfst, Category.id_comp]
    · rw [Category.assoc, hliftdef, pullback.lift_snd, hu, Category.id_comp]
  have : IsIso lift := ⟨u, hliftu, hulift⟩
  exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso lift)
    (by rw [asIso_hom, hliftdef, pullback.lift_fst])
    (by rw [asIso_hom, hliftdef, pullback.lift_snd])

end

/-! ### The normalization square of a smooth morphism -/

/-- **Stacks Project, Tag 07TD, the isomorphism `X^ν = X ×_Y Y^ν`.**
Let `φ : X ⟶ Y` be a smooth morphism of schemes and assume every quasi-compact open of `Y` has
finitely many irreducible components. Then the square formed by the normalization morphisms of
`X` and `Y`, the morphism of normalizations induced by `φ` and `φ` itself is cartesian.

The finiteness hypothesis on `X` is the one ascending along `φ` from `hY`, which is the other
assertion of the tag, `AlgebraicGeometry.finite_irreducibleComponents_of_smooth`. -/
@[stacks 07TD "the isomorphism `X^ν = X ×_Y Y^ν`", sga "3 X 8.9" "more general"]
theorem isPullback_normalizationSchemeMap_of_smooth {X Y : Scheme.{u}} (φ : X ⟶ Y) [Smooth φ]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite) :
    IsPullback
      (normalizationSchemeMap φ (finite_irreducibleComponents_of_smooth φ hY) hY)
      (X.normalization (finite_irreducibleComponents_of_smooth φ hY))
      (Y.normalization hY) φ := by
  have : IsNormal (Y.normalizationScheme hY) := Scheme.isNormal_normalizationScheme Y hY
  exact isPullback_normalizationSchemeMap_of_flat φ
    (finite_irreducibleComponents_of_smooth φ hY) hY
    (isNormal_of_smooth (pullback.fst (Y.normalization hY) φ))

end AlgebraicGeometry

end
