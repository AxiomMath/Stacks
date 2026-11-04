module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialitySourceTargetCartesian

/-!
# The cartesian source square of a morphism of groupoids, read on points

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B` over a scheme `S` of a big fppf site, written `f : U ⟶ U'` on objects
and `f : R ⟶ R'` on arrows, and assume the **source square**

```
R ---f---> R'
|          |
s          s'
v          v
U ---f---> U'
```

is cartesian, which is the hypothesis of Stacks 04ZN. An algebraic space over `S` is a presheaf
on the big fppf site, and a cartesian square of presheaves of types is cartesian on points, so the
hypothesis says exactly that an arrow of `R` over a test object is the same thing as an arrow of
`R'` over that test object together with a point of `U` lifting its source. This file records that
reading, in the two forms in which the proof of Stacks 04ZN consumes it.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.eq_of_isPullback_source`: an arrow of `R` over
  a test object is determined by its image in `R'` together with its source.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.existsUnique_arrow_of_isPullback_source`: an
  arrow `r'` of `R'` over a test object and a point `u` of `U` with `s'(r') = f(u)` are the image
  and the source of a unique arrow of `R` over that test object. **This is the step of
  Stacks 04ZN that produces the second point of `U` out of the arrow of `R'` that Stacks 044V
  supplies**, local essential surjectivity of the comparison 1-morphism being the half of
  Stacks 04ZN it belongs to.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.eq_identityArrow_of_isPullback_source`: an
  arrow of `R` whose image in `R'` is the identity arrow at the image of its source *is* the
  identity arrow at its source. **This is the step of Stacks 04ZN that collapses an arrow
  compatible with the comparison isomorphism to an identity**, full faithfulness of the
  comparison 1-morphism being the half it belongs to.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.target_eq_source_of_isPullback_source`: the
  consequence of the previous one that the two halves are after — such an arrow has the same
  source and target, so the two points of `U` it connects are equal.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mapArrows_app_identityArrow` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrow_app_source`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrow_app_target`: the pointwise form of
  the three facts about the unit `e : U ⟶ R` that the collapse uses.
* `CategoryTheory.IsPullback.eq_of_points_eq` and
  `CategoryTheory.IsPullback.existsUnique_point`: the reading of a cartesian square of presheaves
  of types on points, which is what the two results above specialise. Both hold for presheaves on
  an arbitrary category.

## Implementation notes

The hypothesis is the cartesian square in the category of presheaves of types on the big fppf
site, in the shape that
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_target_iff_isPullback_source` states
it, so that the source square and the target square may be exchanged freely.

Points are handled through `CategoryTheory.yonedaEquiv` rather than by evaluating the cartesian
square at a test object: a point of a presheaf over `T` is a morphism out of `yoneda.obj T`, and
then the universal property of the cartesian square applies verbatim —
`CategoryTheory.IsPullback.hom_ext` for the first result and `CategoryTheory.IsPullback.lift` for
the second. No pointwise description of pullbacks of presheaves is needed, and in particular the
chosen pullback presheaf never appears.

The content of Stacks 04ZN is the 2-fibre product property of the square of quotient stacks;
the results here are two steps of its proof, stated without quotient stacks.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-! ### Points of a cartesian square of presheaves of types -/

section Presheaves

universe v u'

variable {D : Type u'} [Category.{v} D]

/-- **A cartesian square of presheaves of types is jointly monic on points**: a point of the apex
over a test object is determined by its two projections. A point of a presheaf over `T` is a
morphism out of `yoneda.obj T`, so this is `CategoryTheory.IsPullback.hom_ext`. -/
theorem IsPullback.eq_of_points_eq {P X Y Z : Dᵒᵖ ⥤ Type v}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) {T : D} {p q : P.obj (Opposite.op T)}
    (hfst : fst.app (Opposite.op T) p = fst.app (Opposite.op T) q)
    (hsnd : snd.app (Opposite.op T) p = snd.app (Opposite.op T) q) :
    p = q := by
  apply yonedaEquiv.symm.injective
  refine h.hom_ext ?_ ?_ <;> apply yonedaEquiv.injective <;>
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- **A compatible pair of points of the two factors of a cartesian square of presheaves of types
is the pair of projections of a unique point of the apex.** Points over `T` are morphisms out of
`yoneda.obj T`, so this is `CategoryTheory.IsPullback.lift` together with
`CategoryTheory.IsPullback.eq_of_points_eq`. -/
theorem IsPullback.existsUnique_point {P X Y Z : Dᵒᵖ ⥤ Type v}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) {T : D}
    (x : X.obj (Opposite.op T)) (y : Y.obj (Opposite.op T))
    (hxy : f.app (Opposite.op T) x = g.app (Opposite.op T) y) :
    ∃! p : P.obj (Opposite.op T),
      fst.app (Opposite.op T) p = x ∧ snd.app (Opposite.op T) p = y := by
  have w : yonedaEquiv.symm x ≫ f = yonedaEquiv.symm y ≫ g := by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hxy
  obtain ⟨hx, hy⟩ : fst.app (Opposite.op T) (yonedaEquiv (h.lift _ _ w)) = x ∧
      snd.app (Opposite.op T) (yonedaEquiv (h.lift _ _ w)) = y := by
    constructor <;> simp only [← yonedaEquiv_comp, h.lift_fst, h.lift_snd, Equiv.apply_symm_apply]
  exact ⟨_, ⟨hx, hy⟩, fun p hp => h.eq_of_points_eq (hp.1.trans hx.symm) (hp.2.trans hy.symm)⟩

end Presheaves

end CategoryTheory

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### The unit on points -/

/-- The source of the identity arrow at a point of the object space is that point. -/
theorem identityArrow_app_source (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : G.objects.obj.obj T) :
    G.source.hom.app T ((identityArrow G).hom.app T x) = x := by
  let _ := G.toGroupoidInFunctors.evaluationGroupoid T
  have h := (G.toGroupoidInFunctors.evaluationArrowEquiv T
    (show G.toGroupoidInFunctors.Evaluation T from x) x (𝟙 _)).2.1
  rw [Deformation.GroupoidInFunctors.evaluationArrowEquiv_id] at h
  rwa [identityArrow_hom_app]

/-- The target of the identity arrow at a point of the object space is that point. -/
theorem identityArrow_app_target (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : G.objects.obj.obj T) :
    G.target.hom.app T ((identityArrow G).hom.app T x) = x := by
  let _ := G.toGroupoidInFunctors.evaluationGroupoid T
  have h := (G.toGroupoidInFunctors.evaluationArrowEquiv T
    (show G.toGroupoidInFunctors.Evaluation T from x) x (𝟙 _)).2.2
  rw [Deformation.GroupoidInFunctors.evaluationArrowEquiv_id] at h
  rwa [identityArrow_hom_app]

/-- **A morphism of groupoids in algebraic spaces carries identity arrows to identity arrows**, on
points: this is the `map_identity` clause of a morphism of the underlying groupoids in presheaves,
read through the unit `e : U ⟶ R` of Stacks 06K5. -/
theorem Hom.mapArrows_app_identityArrow (φ : Hom G G')
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : G.objects.obj.obj T) :
    φ.toGroupoidHom.mapArrows.app T ((identityArrow G).hom.app T x) =
      (identityArrow G').hom.app T (φ.toGroupoidHom.mapObjects.app T x) :=
  (congrArg _ (identityArrow_hom_app G T x)).trans
    ((φ.toGroupoidHom.map_id T x).trans (identityArrow_hom_app G' _ _).symm)

/-! ### The cartesian source square on points -/

/-- **An arrow of `R` over a test object is determined by its image in `R'` together with its
source**, when the source square of `φ` is cartesian: the two projections of a cartesian square
are jointly monic, and a point over `T` is a morphism out of `yoneda.obj T`. -/
theorem Hom.eq_of_isPullback_source (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects)
    {T : BigFppfOver C S hS} {r₁ r₂ : G.arrows.obj.obj (op T)}
    (ha : φ.toGroupoidHom.mapArrows.app (op T) r₁ =
      φ.toGroupoidHom.mapArrows.app (op T) r₂)
    (hs : G.source.hom.app (op T) r₁ = G.source.hom.app (op T) r₂) :
    r₁ = r₂ :=
  hφ.eq_of_points_eq ha hs

/-- **An arrow of `R'` over a test object together with a point of `U` lifting its source come
from a unique arrow of `R`**, when the source square of `φ` is cartesian.

This is the step of the proof of Stacks 04ZN that produces the second point of the object space:
Stacks 044V turns the comparison isomorphism of an object of the 2-fibre product into an arrow
`r'` of `R'` out of the image of a point `u` of `U`, and this lifts `r'` to an arrow `r` of `R`
out of `u`, whose target is the point wanted. Its image in `U'` is `t'(r')` by the `map_target`
clause of a morphism of groupoids, with no hypothesis needed. -/
theorem Hom.existsUnique_arrow_of_isPullback_source (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects)
    {T : BigFppfOver C S hS} (u : G.objects.obj.obj (op T))
    (r' : G'.arrows.obj.obj (op T))
    (h : G'.source.hom.app (op T) r' = φ.toGroupoidHom.mapObjects.app (op T) u) :
    ∃! r : G.arrows.obj.obj (op T),
      φ.toGroupoidHom.mapArrows.app (op T) r = r' ∧
        G.source.hom.app (op T) r = u :=
  hφ.existsUnique_point r' u h

/-- **An arrow of `R` whose image in `R'` is an identity arrow is itself an identity arrow**, when
the source square of `φ` is cartesian.

This is the step of the proof of Stacks 04ZN that collapses an arrow to an identity: in the full
faithfulness half, compatibility of a morphism of the 2-fibre product with the comparison
isomorphism forces the image in `R'` of the arrow Stacks 044V produces to be an identity, and the
cartesian source square then forces the arrow itself to be one. The unit `e : U ⟶ R` of
Stacks 06K5 is a section of the source and is carried to the unit of `(U', R', s', t', c')`, so
it provides an arrow with the same image and the same source. -/
theorem Hom.eq_identityArrow_of_isPullback_source (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects)
    {T : BigFppfOver C S hS} (r : G.arrows.obj.obj (op T))
    (h : φ.toGroupoidHom.mapArrows.app (op T) r =
      (identityArrow G').hom.app (op T)
        (φ.toGroupoidHom.mapObjects.app (op T) (G.source.hom.app (op T) r))) :
    r = (identityArrow G).hom.app (op T) (G.source.hom.app (op T) r) := by
  refine Hom.eq_of_isPullback_source φ hφ ?_ ?_
  · rw [h, Hom.mapArrows_app_identityArrow]
  · rw [identityArrow_app_source]

/-- **An arrow of `R` whose image in `R'` is an identity arrow has the same source and target**,
when the source square of `φ` is cartesian: by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.eq_identityArrow_of_isPullback_source` it is an
identity arrow, and an identity arrow has the same source and target. This is the conclusion that
the full faithfulness half of Stacks 04ZN consumes: the two points of the object space that the
arrow connects are equal. -/
theorem Hom.target_eq_source_of_isPullback_source (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects)
    {T : BigFppfOver C S hS} (r : G.arrows.obj.obj (op T))
    (h : φ.toGroupoidHom.mapArrows.app (op T) r =
      (identityArrow G').hom.app (op T)
        (φ.toGroupoidHom.mapObjects.app (op T) (G.source.hom.app (op T) r))) :
    G.target.hom.app (op T) r = G.source.hom.app (op T) r := by
  rw [Hom.eq_identityArrow_of_isPullback_source φ hφ r h, identityArrow_app_target,
    identityArrow_app_source]

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
