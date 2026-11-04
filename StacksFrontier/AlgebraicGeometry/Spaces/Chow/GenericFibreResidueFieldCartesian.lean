module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreIsField
public import StacksFrontier.AlgebraicGeometry.Spaces.StratumSiteDatum

/-!
# The square of residue fields of a finite morphism is cartesian

Let `p : X ⟶ Y` be a relatively representable *finite* morphism of algebraic spaces over a scheme
`S` of a big fppf site `B`, with `X` and `Y` decent and reduced, and let `x` be a point of `X`
whose image `ξ = p(x)` has local ring of dimension zero and is hit by `|p|` at `x` alone. Then

```
Spec κ(x) ⟶ X
    ↓         ↓ p
Spec κ(ξ) ⟶ Y
```

is **cartesian**.

## Main results

* `AlgebraicGeometry.Space.isIso_residueFibreComparison`: **the comparison morphism
  `Spec κ(x) ⟶ X ×_Y Spec κ(ξ)` is an isomorphism.**
* `AlgebraicGeometry.Space.isPullback_residueFieldMorphism`: **the square of residue fields is
  cartesian**, for a given morphism of the site between the residue field representatives
  over `p`.
* `AlgebraicGeometry.Space.exists_isPullback_residueFieldMorphism`: some morphism of the site
  between the residue field representatives makes the square of residue fields cartesian.

## References

* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The comparison morphism is an isomorphism -/

/-- **The comparison morphism from the residue field point to the fibre is an isomorphism.** For
`p : X ⟶ Y` relatively representable and finite between reduced decent algebraic spaces and `x` a
point of `X` whose image has local ring of dimension zero and no other preimage, the morphism
`AlgebraicGeometry.Space.residueFibreComparison` from `Spec κ(x)` to `X ×_Y Spec κ(p x)` is an
isomorphism. -/
theorem isIso_residueFibreComparison {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hp : IsFinite B S hS p)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y)
    (hredX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hredY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (x : points B S hS X)
    (hdim : localRingDimension B S hS (pointsMap B S hS X p x) = 0)
    (hfib : ∀ y y' : points B S hS X, pointsMap B S hS X p y = pointsMap B S hS X p x →
      pointsMap B S hS X p y' = pointsMap B S hS X p x → y = y')
    (g : (residueFieldRepresentative B S hS X hdecX x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hdecY
        (pointsMap B S hS X p x)).1.siteObject B S hS Y)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x) =
      residueFieldMorphism B S hS X hdecX x ≫ p) :
    IsIso (residueFibreComparison B S hS hrep hdecX hdecY x g hg) := by
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x)))) :=
    isAffine_toScheme_obj_pullback_fieldMorphism B S hS hrep
      (residueFieldRepresentative B S hS Y hdecY (pointsMap B S hS X p x)).1 hp
  have hfield := isField_appTop_pullback_residueFieldMorphism B S hS hrep hp hX hY hdecX hdecY
    hredX hredY x hdim hfib
  let _ : Field ↥Γ((BigFppfOver.toScheme B S hS).obj
    (hrep.pullback (residueFieldMorphism B S hS Y hdecY
      (pointsMap B S hS X p x))), ⊤) := hfield.toField
  obtain ⟨q, ε, hεa⟩ := exists_fieldValuedPoint_comp_eq B S hS
    (hrep.pullback (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x)))
    ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (residueFieldMorphism B S hS Y hdecY
        (pointsMap B S hS X p x)))).isoSpec
    (hrep.fst (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x)))
  have hmonofst : Mono
      (hrep.fst (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x))) :=
    mono_fst_fieldMorphism B S hS hrep _
      (residueFieldRepresentative B S hS Y hdecY (pointsMap B S hS X p x)).2.2
  have hfm : fieldMorphism B S hS X q = yoneda.map ε.inv ≫
      hrep.fst (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x)) := by
    rw [← hεa, ← Category.assoc, ← CategoryTheory.Functor.map_comp, ε.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hclass : q.class B S hS X = x := by
    refine hfib _ _ ?_ rfl
    rw [← pointsMap_fieldMorphism_tautologicalPoint B S hS X q, ← pointsMap_comp_apply, hfm,
      Category.assoc, hrep.w, ← Category.assoc, pointsMap_comp_apply]
    exact pointsMap_residueFieldMorphism_eq B S hS hdecY _ _
  have hmonoq : Mono (fieldMorphism B S hS X q) := by rw [hfm]; infer_instance
  obtain ⟨ν, hν, -⟩ :=
    residueFieldRepresentative_unique B S hS X hX hdecX x q hclass hmonoq
  have key : yoneda.map (residueFibreComparison B S hS hrep hdecX hdecY x g hg) =
      ν.hom ≫ yoneda.map ε.inv := by
    rw [← cancel_mono (hrep.fst
      (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x))),
      yoneda_map_residueFibreComparison_fst, Category.assoc, ← hfm, hν]
  have : IsIso (yoneda.map (residueFibreComparison B S hS hrep hdecX hdecY x g hg)) := by
    rw [key]; infer_instance
  exact isIso_of_reflects_iso _ yoneda

/-! ### The cartesian square -/

/-- **The square of residue fields of a finite morphism at a point with a single preimage is
cartesian.** For `p : X ⟶ Y` relatively representable and finite between reduced decent algebraic
spaces and `x` a point of `X` whose image has local ring of dimension zero and no other
preimage,

```
Spec κ(x) ⟶ X
    ↓         ↓ p
Spec κ(p x) ⟶ Y
```

is a fibre product square. -/
theorem isPullback_residueFieldMorphism {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hp : IsFinite B S hS p)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y)
    (hredX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hredY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (x : points B S hS X)
    (hdim : localRingDimension B S hS (pointsMap B S hS X p x) = 0)
    (hfib : ∀ y y' : points B S hS X, pointsMap B S hS X p y = pointsMap B S hS X p x →
      pointsMap B S hS X p y' = pointsMap B S hS X p x → y = y')
    (g : (residueFieldRepresentative B S hS X hdecX x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hdecY
        (pointsMap B S hS X p x)).1.siteObject B S hS Y)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x) =
      residueFieldMorphism B S hS X hdecX x ≫ p) :
    IsPullback (residueFieldMorphism B S hS X hdecX x) (yoneda.map g) p
      (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x)) :=
  isPullback_residueFieldMorphism_of_isIso B S hS hrep hdecX hdecY x g hg
    (isIso_residueFibreComparison B S hS hrep hp hX hY hdecX hdecY hredX hredY x hdim hfib g hg)

/-- **The square of residue fields of a finite morphism at a point with a single preimage is
cartesian**: under the hypotheses of
`AlgebraicGeometry.Space.isPullback_residueFieldMorphism`, some morphism `g` of the site between
the residue field representatives makes the square of residue fields a fibre product square. -/
theorem exists_isPullback_residueFieldMorphism {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hp : IsFinite B S hS p)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y)
    (hredX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hredY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (x : points B S hS X)
    (hdim : localRingDimension B S hS (pointsMap B S hS X p x) = 0)
    (hfib : ∀ y y' : points B S hS X, pointsMap B S hS X p y = pointsMap B S hS X p x →
      pointsMap B S hS X p y' = pointsMap B S hS X p x → y = y') :
    ∃ g : (residueFieldRepresentative B S hS X hdecX x).1.siteObject B S hS X ⟶
        (residueFieldRepresentative B S hS Y hdecY
          (pointsMap B S hS X p x)).1.siteObject B S hS Y,
      IsPullback (residueFieldMorphism B S hS X hdecX x) (yoneda.map g) p
        (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x)) :=
  exists_isPullback_residueFieldMorphism_of_isIso B S hS hrep hdecX hdecY x hY
    fun g hg => isIso_residueFibreComparison B S hS hrep hp hX hY hdecX hdecY hredX hredY
      x hdim hfib g hg

end AlgebraicGeometry.Space

end
