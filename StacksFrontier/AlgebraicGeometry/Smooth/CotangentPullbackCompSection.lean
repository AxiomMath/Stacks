module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafAffine

/-!
# The universal differential of a pullback cotangent sheaf under a further pullback

Let `f : X ⟶ S` be a morphism of schemes, `r : T ⟶ X` a second one and `s : T' ⟶ T` a third,
with `s ≫ r = rr`.  Pulling a global section of `r^*Ω_{X/S}` back along `s` and comparing with
`rr^*Ω_{X/S}` — by the composition comparison of inverse images followed by the transport along
`s ≫ r = rr` — gives a map of global sections

`Γ(r^*Ω_{X/S}, ⊤) ⟶ Γ(rr^*Ω_{X/S}, ⊤)`,

and this file proves that it carries the pullback `Stacks.Smooth.pullbackD` of the universal
differential along `r` to the one along `rr`.

## Why this is wanted

It is the chart-independent half of the naturality in the chart of the identification of the
acting sheaf of [Stacks Project, Tag 061D] with the acting group of a chart presentation, which
step (II) of [Stacks Project, Tag 04AM] needs: the acting group is a linear map out of
`Γ(a^*Ω_{W/V}, ⊤)` and the derivation it induces is its value on `Stacks.Smooth.pullbackD`, so a
comparison of the acting groups at two charts has to know what the comparison of the two
cotangent sheaves does to the universal differential.

## Main definitions

* `Stacks.Smooth.pullbackCotangentCompSection`: **the map of global sections** attached to a
  factorization `s ≫ r = rr`.

## Main results

* `Stacks.Smooth.pullbackD_eq_pullbackSection`: the pullback of the universal differential *is*
  `AlgebraicGeometry.Scheme.Modules.pullbackSection` of the universal differential, by `rfl`.
* `Stacks.Smooth.pullbackCotangentCompSection_pullbackD`: **the map of global sections carries
  the universal differential to the universal differential.**

## Implementation notes

The whole content is `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` and
`AlgebraicGeometry.Scheme.Modules.pullbackSection_congr`, once
`Stacks.Smooth.pullbackD` is recognised as a pulled-back section: both
`Stacks.Smooth.pullbackCotangentUnitApp` and `AlgebraicGeometry.Scheme.Modules.pullbackSection`
are the component of the unit of `r^* ⊣ r_*` followed by a restriction of sections, so the two
agree on the nose.

The proof is in **term mode**.  Rewriting with the definition of
`Stacks.Smooth.pullbackCotangentCompSection` leaves a goal that is not type-correct at `implicit`
transparency — the usual symptom of unfolding a semireducible inverse-image comparison — so
`rewrite` refuses to fire afterwards, while `congrArg` keeps every term at the spelling it was
built at.

No `@[stacks]` attribute is claimed: the composition comparison of inverse images and the
universal property of the sheaf of differentials are registered where they are built.

## References

* [Stacks Project, Tag 01UQ](https://stacks.math.columbia.edu/tag/01UQ)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Smooth

open AlgebraicGeometry

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) (r : T ⟶ X) (s : T' ⟶ T) (rr : T' ⟶ X)
  (hrr : s ≫ r = rr)

/-- **The pullback of the universal differential is the pulled-back section of the universal
differential.**  Both `Stacks.Smooth.pullbackD` and
`AlgebraicGeometry.Scheme.Modules.pullbackSection` are the component of the unit of `r^* ⊣ r_*`
followed by a restriction of sections, so there is nothing to prove. -/
theorem pullbackD_eq_pullbackSection (hUW : (⊤ : T.Opens) ≤ r ⁻¹ᵁ (⊤ : X.Opens))
    (x : Γ(X, (⊤ : X.Opens))) :
    pullbackD f r ⊤ hUW x =
      Scheme.Modules.pullbackSection r (cotangentSheaf f) ⊤ ⊤ hUW (universalD f ⊤ x) :=
  rfl

/-- **The comparison of the global sections of two pullback cotangent sheaves along a
factorization `s ≫ r = rr`**: pull a global section of `r^*Ω_{X/S}` back along `s`, collapse the
two inverse images by the composition comparison and transport along the factorization. -/
noncomputable def pullbackCotangentCompSection :
    Γ(pullbackCotangentSheaf f r, (⊤ : T.Opens)) →
      Γ(pullbackCotangentSheaf f rr, (⊤ : T'.Opens)) :=
  fun y =>
    ((Scheme.Modules.pullbackCongr hrr).hom.app (cotangentSheaf f)).val.app (op ⊤)
      (((Scheme.Modules.pullbackComp s r).hom.app (cotangentSheaf f)).val.app (op ⊤)
        (Scheme.Modules.pullbackSection s (pullbackCotangentSheaf f r) ⊤ ⊤ le_top y))

/-- **The comparison of global sections carries the universal differential along `r` to the
universal differential along `rr`.** -/
theorem pullbackCotangentCompSection_pullbackD (x : Γ(X, (⊤ : X.Opens))) :
    pullbackCotangentCompSection f r s rr hrr (pullbackD f r ⊤ le_top x) =
      pullbackD f rr ⊤ le_top x :=
  (congrArg (fun z => (((Scheme.Modules.pullbackCongr hrr).hom.app
        (cotangentSheaf f)).val.app (op (⊤ : T'.Opens))) z)
      (Scheme.Modules.pullbackSection_comp s r (cotangentSheaf f) ⊤ ⊤ ⊤ le_top le_top le_top
        (universalD f ⊤ x))).trans
    (Scheme.Modules.pullbackSection_congr hrr (cotangentSheaf f) ⊤ ⊤ le_top le_top
      (universalD f ⊤ x))

end Stacks.Smooth

end
