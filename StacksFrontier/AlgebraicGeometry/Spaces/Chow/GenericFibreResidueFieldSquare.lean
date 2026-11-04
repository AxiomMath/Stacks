module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteBaseChangeChartAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField

/-!
# The fibre of a finite morphism of algebraic spaces over a field-valued point

Let `p : X ⟶ Y` be a relatively representable morphism of algebraic spaces over a scheme `S` of
a big fppf site `B`, and let `q` be a field-valued point of `Y` with field `κ`.  The fibre
`X ×_Y Spec κ` is then represented by an object `W` of the big fppf category over `S`, namely
`Functor.relativelyRepresentable.pullback` of `p` along `fieldMorphism B S hS Y q`, and the
projection `W ⟶ Spec κ` is the morphism `Functor.relativelyRepresentable.snd`.  This file
records what the fibre looks like when `p` is finite, and reduces the question whether

```
Spec κ(x) ⟶ X
    ↓         ↓ p
Spec κ(p x) ⟶ Y
```

is cartesian — the square of residue fields of `AlgebraicGeometry.Space.residueFieldHom` — to
the single question whether one morphism of the site is an isomorphism.

For `X` and `Y` integral and `p` dominant and finite this square is the space-level form of
`Stacks.GenericFibre.isPushout_fractionRing_of_isIntegral`: it says that the generic fibre of
`p` is `Spec R(X)`, where `R(X)` is the field of rational functions, identified with the residue
field at the generic point by `AlgebraicGeometry.Space.rationalFunctionsRingEquiv`.

## Main results

* `AlgebraicGeometry.Space.isFinite_toScheme_map_snd_fieldMorphism`: for `p` finite, the
  projection `X ×_Y Spec κ ⟶ Spec κ` is a finite morphism of *schemes*.
* `AlgebraicGeometry.Space.isAffine_toScheme_obj_pullback_fieldMorphism`: hence the fibre
  `X ×_Y Spec κ` of a finite morphism over a field-valued point is an **affine scheme**,
  `Spec D`, and `AlgebraicGeometry.Space.finite_appTop_pullback_fieldMorphism` says that `D` is
  a finite `κ`-algebra.
* `AlgebraicGeometry.Space.mono_fst_fieldMorphism`: when `Spec κ ⟶ Y` is a monomorphism — which
  it is for the chosen representative of a point of a decent space, by Stacks 0EMW — the
  projection `X ×_Y Spec κ ⟶ X` is a monomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.residueFibreComparison`: the comparison morphism
  `Spec κ(x) ⟶ X ×_Y Spec κ(p x)` of the site, obtained from the commuting square of residue
  fields by the universal property of the fibre.
* `AlgebraicGeometry.Space.isPullback_residueFieldMorphism_iff_isIso`: the square of residue
  fields is cartesian **exactly when** that comparison morphism is an isomorphism, with the two
  directions `AlgebraicGeometry.Space.isPullback_residueFieldMorphism_of_isIso` and
  `AlgebraicGeometry.Space.isIso_residueFibreComparison_of_isPullback`.
* `AlgebraicGeometry.Space.isPullback_residueFieldMorphism_of_isIso_toScheme_map`: it is enough
  that the comparison morphism be an isomorphism of *schemes*, by
  `AlgebraicGeometry.Space.isIso_bigFppfOver_of_isIso_toScheme_map`; for `p` finite both of its
  ends are affine, so this is a statement about one ring homomorphism.
* `AlgebraicGeometry.Space.exists_isPullback_residueFieldMorphism_of_isIso`: the same, with the
  morphism of the site supplied by `AlgebraicGeometry.Space.residueFieldHom_spec` instead of
  being given.

## Implementation notes

Everything about the fibre is read off the representability witness `hrep` of `p`: the object
`hrep.pullback (fieldMorphism B S hS Y q)` of the site, the projections `hrep.fst` and
`hrep.snd`, and the cartesian square `hrep.isPullback`. The comparison morphism is
`Functor.relativelyRepresentable.lift`.

## References

* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The fibre of a finite morphism over a field-valued point -/

section FieldFibre

variable {p : X ⟶ Y} (hrep : yoneda.relativelyRepresentable p)
  (q : FieldValuedPoint B S hS Y)

/-- The spectrum of the field of a field-valued point is an affine scheme. -/
theorem isAffine_toScheme_obj_siteObject :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (q.siteObject B S hS Y)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of q.carrier)))

/-- The fibre of a finite morphism over a field-valued point is finite over the field. For
`p : X ⟶ Y` relatively representable and finite and `q` a field-valued point of `Y` with field
`κ`, the projection `X ×_Y Spec κ ⟶ Spec κ` is a finite morphism of schemes. -/
theorem isFinite_toScheme_map_snd_fieldMorphism (hp : IsFinite B S hS p) :
    _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (fieldMorphism B S hS Y q))) :=
  (presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsFinite.{u})
      inferInstance (hrep.snd (fieldMorphism B S hS Y q))).1
    (presheaf_isFinite_of_isFinite _ (Functor.relativelyRepresentable.map yoneda _)
      (isFinite_of_isPullback B S hS (hrep.isPullback (fieldMorphism B S hS Y q)) hp))

/-- The fibre of a finite morphism of algebraic spaces over a field-valued point is an affine
scheme. For `p : X ⟶ Y` relatively representable and finite and `q` a field-valued point of
`Y` with field `κ`, the object of the site representing `X ×_Y Spec κ` has affine underlying
scheme. -/
theorem isAffine_toScheme_obj_pullback_fieldMorphism (hp : IsFinite B S hS p) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (fieldMorphism B S hS Y q))) :=
  have := isAffine_toScheme_obj_siteObject B S hS q
  have := isFinite_toScheme_map_snd_fieldMorphism B S hS hrep q hp
  isAffine_of_isAffineHom
    ((BigFppfOver.toScheme B S hS).map (hrep.snd (fieldMorphism B S hS Y q)))

/-- The ring of the fibre is a finite algebra over the field of the point. For
`p : X ⟶ Y` relatively representable and finite and `q` a field-valued point of `Y` with field
`κ`, the homomorphism `κ → Γ(X ×_Y Spec κ, 𝒪)` induced by the projection is a finite ring
homomorphism: writing the fibre as `Spec D`, the ring `D` is a finite `κ`-module. -/
theorem finite_appTop_pullback_fieldMorphism (hp : IsFinite B S hS p) :
    RingHom.Finite
      ((BigFppfOver.toScheme B S hS).map
        (hrep.snd (fieldMorphism B S hS Y q))).appTop.hom :=
  have := isAffine_toScheme_obj_siteObject B S hS q
  have := isFinite_toScheme_map_snd_fieldMorphism B S hS hrep q hp
  _root_.AlgebraicGeometry.IsFinite.finite_app
    ((BigFppfOver.toScheme B S hS).map (hrep.snd (fieldMorphism B S hS Y q))) ⊤
    (isAffineOpen_top _)

/-- The fibre over a monomorphic field-valued point embeds in the source. If the morphism
`Spec κ ⟶ Y` presented by a field-valued point is a monomorphism, then so is the projection
`X ×_Y Spec κ ⟶ X`. -/
theorem mono_fst_fieldMorphism (hq : Mono (fieldMorphism B S hS Y q)) :
    Mono (hrep.fst (fieldMorphism B S hS Y q)) :=
  (hrep.isPullback (fieldMorphism B S hS Y q)).mono_fst_of_mono hq

end FieldFibre

/-- A morphism of the big fppf category over `S` whose underlying morphism of schemes is an
isomorphism is itself an isomorphism. -/
theorem isIso_bigFppfOver_of_isIso_toScheme_map {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (h : IsIso ((BigFppfOver.toScheme B S hS).map f)) : IsIso f := by
  have : IsIso (B.inclusion.map f.left) := h
  have : IsIso ((Over.forget (B.obj hS)).map f) := isIso_of_reflects_iso f.left B.inclusion
  exact isIso_of_reflects_iso f (Over.forget (B.obj hS))

/-! ### The square of residue fields -/

section ResidueSquare

variable {p : X ⟶ Y} (hrep : yoneda.relativelyRepresentable p)
  (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
  (x : points B S hS X)

/-- The comparison morphism from the residue field point to the fibre. Given a morphism `g` of
the site making the square of residue fields of `p` at `x` commute, this is the induced morphism
`Spec κ(x) ⟶ X ×_Y Spec κ(p x)` of the site, given by the universal property of the fibre. -/
def residueFibreComparison
    (g : (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hYdec
        (pointsMap B S hS X p x)).1.siteObject B S hS Y)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x) =
      residueFieldMorphism B S hS X hXdec x ≫ p) :
    (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X ⟶
      hrep.pullback (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x)) :=
  hrep.lift (residueFieldMorphism B S hS X hXdec x) g hg.symm

@[simp]
theorem yoneda_map_residueFibreComparison_fst
    (g : (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hYdec
        (pointsMap B S hS X p x)).1.siteObject B S hS Y)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x) =
      residueFieldMorphism B S hS X hXdec x ≫ p) :
    yoneda.map (residueFibreComparison B S hS hrep hXdec hYdec x g hg) ≫
        hrep.fst (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x)) =
      residueFieldMorphism B S hS X hXdec x :=
  hrep.lift_fst _ _ _

@[simp]
theorem residueFibreComparison_snd
    (g : (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hYdec
        (pointsMap B S hS X p x)).1.siteObject B S hS Y)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x) =
      residueFieldMorphism B S hS X hXdec x ≫ p) :
    residueFibreComparison B S hS hrep hXdec hYdec x g hg ≫
        hrep.snd (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x)) = g :=
  hrep.lift_snd _ _ _

/-- The square of residue fields is cartesian when the comparison morphism is an
isomorphism. -/
theorem isPullback_residueFieldMorphism_of_isIso
    (g : (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hYdec
        (pointsMap B S hS X p x)).1.siteObject B S hS Y)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x) =
      residueFieldMorphism B S hS X hXdec x ≫ p)
    (hiso : IsIso (residueFibreComparison B S hS hrep hXdec hYdec x g hg)) :
    IsPullback (residueFieldMorphism B S hS X hXdec x) (yoneda.map g) p
      (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x)) := by
  refine (hrep.isPullback
    (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x))).of_iso'
      (yoneda.mapIso (asIso (residueFibreComparison B S hS hrep hXdec hYdec x g hg)))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [← Functor.map_comp]

/-- The comparison morphism is an isomorphism when the square of residue fields is
cartesian. -/
theorem isIso_residueFibreComparison_of_isPullback
    (g : (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hYdec
        (pointsMap B S hS X p x)).1.siteObject B S hS Y)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x) =
      residueFieldMorphism B S hS X hXdec x ≫ p)
    (hsq : IsPullback (residueFieldMorphism B S hS X hXdec x) (yoneda.map g) p
      (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x))) :
    IsIso (residueFibreComparison B S hS hrep hXdec hYdec x g hg) := by
  set e := hsq.isoIsPullback _ _
    (hrep.isPullback (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x)))
  have hfst : e.hom ≫ hrep.fst
      (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x)) =
      residueFieldMorphism B S hS X hXdec x := hsq.isoIsPullback_hom_fst _ _ _
  have hsnd : e.hom ≫ yoneda.map (hrep.snd
      (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x))) = yoneda.map g :=
    hsq.isoIsPullback_hom_snd _ _ _
  have hpre : (yoneda.preimageIso e).hom =
      residueFibreComparison B S hS hrep hXdec hYdec x g hg := by
    refine hrep.hom_ext ?_ ?_
    · rw [Functor.preimageIso_hom, Functor.map_preimage,
        yoneda_map_residueFibreComparison_fst]
      exact hfst
    · rw [residueFibreComparison_snd]
      refine yoneda.map_injective ?_
      rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage, hsnd]
  rw [← hpre]
  infer_instance

/-- The square of residue fields

```
Spec κ(x) ⟶ X
    ↓         ↓ p
Spec κ(p x) ⟶ Y
```

is cartesian exactly when the comparison morphism `Spec κ(x) ⟶ X ×_Y Spec κ(p x)` is an
isomorphism. -/
theorem isPullback_residueFieldMorphism_iff_isIso
    (g : (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hYdec
        (pointsMap B S hS X p x)).1.siteObject B S hS Y)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x) =
      residueFieldMorphism B S hS X hXdec x ≫ p) :
    IsPullback (residueFieldMorphism B S hS X hXdec x) (yoneda.map g) p
        (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x)) ↔
      IsIso (residueFibreComparison B S hS hrep hXdec hYdec x g hg) :=
  ⟨isIso_residueFibreComparison_of_isPullback B S hS hrep hXdec hYdec x g hg,
    isPullback_residueFieldMorphism_of_isIso B S hS hrep hXdec hYdec x g hg⟩

/-- The square of residue fields is cartesian when the comparison morphism is an isomorphism
of schemes. -/
theorem isPullback_residueFieldMorphism_of_isIso_toScheme_map
    (g : (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hYdec
        (pointsMap B S hS X p x)).1.siteObject B S hS Y)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x) =
      residueFieldMorphism B S hS X hXdec x ≫ p)
    (hiso : IsIso ((BigFppfOver.toScheme B S hS).map
      (residueFibreComparison B S hS hrep hXdec hYdec x g hg))) :
    IsPullback (residueFieldMorphism B S hS X hXdec x) (yoneda.map g) p
      (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x)) :=
  isPullback_residueFieldMorphism_of_isIso B S hS hrep hXdec hYdec x g hg
    (isIso_bigFppfOver_of_isIso_toScheme_map B S hS _ hiso)

/-- For a morphism of decent algebraic spaces, if every comparison morphism at `x` is an
isomorphism, then some morphism `Spec κ(x) ⟶ Spec κ(p x)` of the site makes the square of
residue fields cartesian. -/
theorem exists_isPullback_residueFieldMorphism_of_isIso (hY : IsAlgebraicSpace B S hS Y)
    (hiso : ∀ (g : (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X ⟶
        (residueFieldRepresentative B S hS Y hYdec
          (pointsMap B S hS X p x)).1.siteObject B S hS Y)
      (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x) =
        residueFieldMorphism B S hS X hXdec x ≫ p),
      IsIso (residueFibreComparison B S hS hrep hXdec hYdec x g hg)) :
    ∃ g : (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X ⟶
        (residueFieldRepresentative B S hS Y hYdec
          (pointsMap B S hS X p x)).1.siteObject B S hS Y,
      IsPullback (residueFieldMorphism B S hS X hXdec x) (yoneda.map g) p
        (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X p x)) := by
  obtain ⟨g, -, hg⟩ := residueFieldHom_spec B S hS X Y hY hXdec hYdec p x
  exact ⟨g, isPullback_residueFieldMorphism_of_isIso B S hS hrep hXdec hYdec x g hg (hiso g hg)⟩

end ResidueSquare

end AlgebraicGeometry.Space

end
