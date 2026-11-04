module

public import Mathlib.AlgebraicGeometry.Fiber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre of a base change followed by a second morphism

Let `gL : Z ⟶ W` and `t : X ⟶ W` be morphisms of schemes, let `f : X ⟶ Y` be a second morphism
out of `X`, and let `y` be a point of `Y`. This file identifies the scheme-theoretic fibre over
`y` of

```
h = pr₂ ≫ f : Z ×_{gL, W, t} X ⟶ Y
```

with the base change of `gL` along the fibre: writing `F = f⁻¹(y)` for the scheme-theoretic
fibre of `f` and `ι : F ⟶ X` for its embedding,

```
h⁻¹(y) ≅ Z ×_{gL, W, ι ≫ t} F.
```

This is the geometric half of clause (4) of Stacks 0461. There `gL : Z ⟶ U` is the slice cut out
of an affine chart of the object scheme of a groupoid scheme, `t` is the target map, `f` is the
source map, `W = Y = U`, and `h` is the morphism `U' ×_{g, U, t} R ⟶ U` of the slicing lemma; the
identification says that the fibre of `h` over `u` is the base change of the same slice along the
source fibre `F_u = s⁻¹(u)`.

## Main definitions

* `AlgebraicGeometry.fiberBaseChangeToBaseChange` is the comparison morphism
  `Z ×_{gL, W, ι ≫ t} F ⟶ Z ×_{gL, W, t} X`.
* `AlgebraicGeometry.fiberBaseChangeIso` is the identification of `Z ×_{gL, W, ι ≫ t} F` with
  `h⁻¹(y)`.

## Main results

* `AlgebraicGeometry.isPullback_fiberBaseChangeToBaseChange`: the comparison morphism exhibits
  `Z ×_{gL, W, ι ≫ t} F` as a fibre product of `h` with `Spec(κ(y)) ⟶ Y`, which is what makes it
  the fibre of `h` over `y`.
* `AlgebraicGeometry.fiberBaseChangeIso_hom_fiberι`: the identification composed with the
  embedding of the fibre is the comparison morphism. This pins the identification down, the
  embedding of a fibre being a monomorphism.

## Implementation notes

The identification is obtained by pasting two fibre squares. The comparison morphism sits in a
square over the embedding `ι` of the fibre, which is a pullback by cancellation
(`CategoryTheory.IsPullback.of_right`) against the fibre square defining `Z ×_{gL, W, t} X`; and
`ι` itself sits in the fibre square defining `F`. Pasting the two vertically
(`CategoryTheory.IsPullback.paste_vert`) gives a fibre square over `Spec(κ(y)) ⟶ Y` whose other
vertical leg is `pr₂ ≫ f`, which is the assertion that the vertex is the fibre of `h`.

Nothing here mentions `Scheme.Hom.fiber` or `Scheme.Hom.fiberι` except through their definitions
as the chosen fibre product and its first projection, so the statements are always elaborated
against the fibre product and never rewritten inside the semireducible fibre notation.

## References

* [Stacks Project, Tag 0461](https://stacks.math.columbia.edu/tag/0461)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (t : X ⟶ W) (gL : Z ⟶ W) (y : Y)

/-- The comparison morphism from the base change of `gL` along the fibre of `f` over `y` to the
base change of `gL` along `t`: it is the identity on the `Z`-coordinate and the embedding of the
fibre on the other. -/
public noncomputable def fiberBaseChangeToBaseChange :
    pullback gL (f.fiberι y ≫ t) ⟶ pullback gL t :=
  pullback.lift (pullback.fst gL (f.fiberι y ≫ t))
    (pullback.snd gL (f.fiberι y ≫ t) ≫ f.fiberι y)
    (pullback.condition.trans (Category.assoc _ _ _).symm)

/-- The comparison morphism followed by the first projection is the first projection. -/
@[reassoc (attr := simp)]
public lemma fiberBaseChangeToBaseChange_fst :
    fiberBaseChangeToBaseChange f t gL y ≫ pullback.fst gL t =
      pullback.fst gL (f.fiberι y ≫ t) :=
  pullback.lift_fst _ _ _

/-- The comparison morphism followed by the second projection is the second projection followed
by the embedding of the fibre. -/
@[reassoc (attr := simp)]
public lemma fiberBaseChangeToBaseChange_snd :
    fiberBaseChangeToBaseChange f t gL y ≫ pullback.snd gL t =
      pullback.snd gL (f.fiberι y ≫ t) ≫ f.fiberι y :=
  pullback.lift_snd _ _ _

/-- The comparison morphism does not move the `Z`-coordinate of a point. -/
public lemma fiberBaseChangeToBaseChange_fst_apply (q : ↥(pullback gL (f.fiberι y ≫ t))) :
    pullback.fst gL t (fiberBaseChangeToBaseChange f t gL y q) =
      pullback.fst gL (f.fiberι y ≫ t) q :=
  congrArg (fun φ => φ q) (fiberBaseChangeToBaseChange_fst f t gL y)

/-- The comparison morphism carries the other coordinate of a point into `X` along the embedding
of the fibre. -/
public lemma fiberBaseChangeToBaseChange_snd_apply (q : ↥(pullback gL (f.fiberι y ≫ t))) :
    pullback.snd gL t (fiberBaseChangeToBaseChange f t gL y q) =
      f.fiberι y (pullback.snd gL (f.fiberι y ≫ t) q) :=
  congrArg (fun φ => φ q) (fiberBaseChangeToBaseChange_snd f t gL y)

/-- The comparison morphism and the second projections form a fibre square over the embedding of
the fibre: base changing `pr₂ : Z ×_{gL, W, t} X ⟶ X` along `ι : F ⟶ X` gives
`Z ×_{gL, W, ι ≫ t} F`. -/
public lemma isPullback_fiberBaseChangeToBaseChange_snd :
    IsPullback (fiberBaseChangeToBaseChange f t gL y)
      (pullback.snd gL (f.fiberι y ≫ t)) (pullback.snd gL t) (f.fiberι y) := by
  refine IsPullback.of_right ?_ (fiberBaseChangeToBaseChange_snd f t gL y)
    (IsPullback.of_hasPullback gL t)
  rw [fiberBaseChangeToBaseChange_fst]
  exact IsPullback.of_hasPullback gL (f.fiberι y ≫ t)

/-- The embedding of the scheme-theoretic fibre and the map to the residue field form the fibre
square defining the fibre. -/
@[ega "IV 11.2.8" "partial"]
public lemma isPullback_fiberι :
    IsPullback (f.fiberι y) (f.fiberToSpecResidueField y) f (Y.fromSpecResidueField y) :=
  IsPullback.of_hasPullback _ _

/-- **The base change along a fibre is the fibre of the base change.** The comparison morphism
exhibits `Z ×_{gL, W, ι ≫ t} F` as a fibre product of `pr₂ ≫ f` with `Spec(κ(y)) ⟶ Y`. -/
public lemma isPullback_fiberBaseChangeToBaseChange :
    IsPullback (fiberBaseChangeToBaseChange f t gL y)
      (pullback.snd gL (f.fiberι y ≫ t) ≫ f.fiberToSpecResidueField y)
      (pullback.snd gL t ≫ f) (Y.fromSpecResidueField y) :=
  (isPullback_fiberBaseChangeToBaseChange_snd f t gL y).paste_vert (isPullback_fiberι f y)

/-- **The fibre of `pr₂ ≫ f` is the base change of `gL` along the fibre of `f`.** -/
public noncomputable def fiberBaseChangeIso :
    pullback gL (f.fiberι y ≫ t) ≅ (pullback.snd gL t ≫ f).fiber y :=
  (isPullback_fiberBaseChangeToBaseChange f t gL y).isoPullback

/-- The identification of `fiberBaseChangeIso`, followed by the embedding of the fibre, is the
comparison morphism. -/
public lemma fiberBaseChangeIso_hom_fiberι :
    (fiberBaseChangeIso f t gL y).hom ≫ (pullback.snd gL t ≫ f).fiberι y =
      fiberBaseChangeToBaseChange f t gL y :=
  (isPullback_fiberBaseChangeToBaseChange f t gL y).isoPullback_hom_fst

end AlgebraicGeometry

end
