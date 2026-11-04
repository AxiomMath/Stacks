module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapRepresentableCalculus
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlasCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismBaseChange

/-!
# The reduction of the relative morphism functor to a representable base

Let `S` be a scheme contained in a big fppf site and let `z : Z ⟶ Q` and `x : X ⟶ Q` be
morphisms of algebraic spaces over `S`. The proof of Stacks 05Y7 — algebraicity of the relative
morphism functor `Mor_Q(Z, X)` of Stacks 05Y2 — has three steps: a reduction of the base `Q` to
an affine one along an étale covering of `Q`, a reduction of the target `X` along an étale
covering of `X`, and the main case, where the functor is built out of Stacks 05Y6 and glued by
the open covering of Stacks 02WR.
`StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsFiniteLocallyFree` proves the
second step. This file proves the **first**.

The step is formal once Stacks 05Y4 is available, and it is: the comparison morphism

```text
Mor_{Q'}(Q' ×_Q Z, Q' ×_Q X) ⟶ Mor_Q(Z, X)
```

is, by the cartesian square of Stacks 05Y4
(`AlgebraicGeometry.Space.isPullback_relativeHomOfBaseChange`), a base change of `q : Q' ⟶ Q`
along the projection `Mor_Q(Z, X) ⟶ Q`. So representability by algebraic spaces, surjectivity
and étaleness of the comparison morphism are those of `q`, by Stacks 046F, and Stacks 03Y3
transports algebraicity down it. In particular **nothing about `z` is used**: the reduction on
the base needs neither finite local freeness nor any other hypothesis on `z`, in contrast with
the reduction on the target, where the finite local freeness of `z` is exactly what makes
Stacks 05Y5 apply.

## Main results

* `AlgebraicGeometry.Space.hasProperty_etaleMorphisms_of_presheaf`: a morphism of presheaves
  which is étale after every represented base change is étale after every represented base
  change in the sense of Stacks 03XZ. This is the étale companion of
  `AlgebraicGeometry.Space.hasProperty_surjectiveMorphismProperty_of_presheaf` and
  `AlgebraicGeometry.Space.hasProperty_smoothMorphismProperty_of_presheaf`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_isAlgebraicSpace_baseChange`: **the
  reduction on the base**, for an arbitrary morphism `q : Q' ⟶ Q` which is representable by
  algebraic spaces, surjective and étale, and for arbitrary realizations of the two relative
  morphism functors.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_atlas`: the reduction read at a
  scheme atlas of `Q`, which is the form the source's first step takes: `Mor_Q(Z, X)` is an
  algebraic space over `S` as soon as `Mor_{V}(V ×_Q Z, V ×_Q X)` is one for every surjective
  étale chart `yoneda.obj V ⟶ Q` of `Q`.

## Implementation notes

The sheaf property of `Mor_Q(Z, X)` that Stacks 03Y3 consumes is part (1) of Stacks 05Y3, in the
form `AlgebraicGeometry.Space.RelativeHomConstruction.isSheaf_functor`, so it is discharged
rather than carried.

The cartesian square of Stacks 05Y4 is stated with the two projections to the bases as its
*horizontal* arrows, so it is already in the shape `CategoryTheory.IsPullback k a' a g` that
`AlgebraicGeometry.Space.HasProperty.of_isPullback` wants with `a = q` and `a'` the comparison
morphism; no flipping is needed.

## References

* [Stacks Project, Tag 05Y7](https://stacks.math.columbia.edu/tag/05Y7)
* [Stacks Project, Tag 05Y4](https://stacks.math.columbia.edu/tag/05Y4)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 046F](https://stacks.math.columbia.edu/tag/046F)
* [Stacks Project, Tag 03Y3](https://stacks.math.columbia.edu/tag/03Y3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves on the big fppf site of `S` which is étale after every represented
base change is étale after every represented base change in the sense of Stacks 03XZ.

The property `CategoryTheory.MorphismProperty.presheaf` of a property of scheme morphisms is
stable under base change (`AlgebraicGeometry.Space.presheaf_of_isPullback`), and a morphism of
presheaves with that property is étale in the sense of Stacks 03FR
(`AlgebraicGeometry.Space.isEtale_of_presheaf_etale`). -/
theorem hasProperty_etaleMorphisms_of_presheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f) :
    HasProperty B S hS (etaleMorphisms B S hS) f hf := fun _ ξ =>
  isEtale_of_presheaf_etale B S hS
    (presheaf_of_isPullback B S hS (IsPullback.of_hasPullback ξ f).flip hetale)

variable {B S hS}

/-- **The reduction of the relative morphism functor to a smaller base.** Let `z : Z ⟶ Q` and
`x : X ⟶ Q` be morphisms of presheaves on the big fppf site of `S` and let `q : Q' ⟶ Q` be
representable by algebraic spaces, surjective and étale. If the relative morphism functor of
the base changes `Q' ×_Q Z ⟶ Q'` and `Q' ×_Q X ⟶ Q'` is an algebraic space over `S`, then so is
the relative morphism functor of `z` and `x`.

This is the first step of the source's proof of Stacks 05Y7. The comparison morphism
`Mor_{Q'}(Z', X') ⟶ Mor_Q(Z, X)` is a base change of `q` by Stacks 05Y4, so it inherits the
three properties of `q` by Stacks 046F, and Stacks 03Y3 transports algebraicity down it. No
hypothesis on `z` or on `x` is used. -/
theorem isAlgebraicSpace_relativeHom_of_isAlgebraicSpace_baseChange
    {Z X Q Q' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q} (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x))
    (hq : IsRepresentableByAlgebraicSpaces B S hS q)
    (hqSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) q hq)
    (hqEtale : HasProperty B S hS (etaleMorphisms B S hS) q hq)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H.functor)
    (hH' : IsAlgebraicSpace B S hS H'.functor) :
    IsAlgebraicSpace B S hS H.functor :=
  have hp := isPullback_relativeHomOfBaseChange q H H'
  isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale hH hH'
    (relativeHomOfBaseChange q H H') (IsRepresentableByAlgebraicSpaces.of_isPullback hp hq)
    (HasProperty.of_isPullback hp hq hqSurj) (HasProperty.of_isPullback hp hq hqEtale)

variable (B S hS)

/-- **The reduction of the relative morphism functor to a representable base**, for the functor
of Stacks 05Y2. Let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over `S`. If
for every scheme atlas `c : yoneda.obj V ⟶ Q` of `Q` the relative morphism functor of the base
changes along `c` is an algebraic space over `S`, then `Mor_Q(Z, X)` is an algebraic space
over `S`.

This is the first step of the source's proof of Stacks 05Y7: it reduces the proposition to a
base which is an object of the site, the remaining content then being Stacks 05Y6 glued by the
open covering of Stacks 02WR. The chart is produced by the algebraicity of `Q`, so the
hypothesis is quantified over charts. -/
theorem isAlgebraicSpace_relativeHom_of_atlas
    (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)
    (hbase : ∀ (V : BigFppfOver B S hS) (c : yoneda.obj V ⟶ Q),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c →
      IsAlgebraicSpace B S hS
        (relativeHom B S hS (pullback c z) (pullback c x) (yoneda.obj V)
          (pullback.fst c z) (pullback.fst c x)
          (isAlgebraicSpace_pullback B S hS c z (isAlgebraicSpace_yoneda B S hS V) hZ hQ)
          (isAlgebraicSpace_pullback B S hS c x (isAlgebraicSpace_yoneda B S hS V) hX hQ)
          (isAlgebraicSpace_yoneda B S hS V))) :
    IsAlgebraicSpace B S hS (relativeHom B S hS Z X Q z x hZ hX hQ) := by
  obtain ⟨V, c, hcS, hcE⟩ := hQ.exists_atlas
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hZ' : IsAlgebraicSpace B S hS (pullback c z) :=
    isAlgebraicSpace_pullback B S hS c z hV hZ hQ
  have hX' : IsAlgebraicSpace B S hS (pullback c x) :=
    isAlgebraicSpace_pullback B S hS c x hV hX hQ
  have hc : IsRepresentableByAlgebraicSpaces B S hS c :=
    IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hcE.rep
  exact isAlgebraicSpace_relativeHom_of_isAlgebraicSpace_baseChange c
    (relativeHomData B S hS Z X Q z x hZ hX hQ)
    (relativeHomData B S hS (pullback c z) (pullback c x) (yoneda.obj V)
      (pullback.fst c z) (pullback.fst c x) hZ' hX' hV)
    hc
    (hasProperty_surjectiveMorphismProperty_of_presheaf B S hS c hcS hc)
    (hasProperty_etaleMorphisms_of_presheaf B S hS c hcE hc)
    (isSheaf_relativeHom B S hS Z X Q z x hZ hX hQ)
    (hbase V c hcS hcE)

end AlgebraicGeometry.Space

end
