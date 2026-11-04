module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.SpecialFibreTransport
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderBiproducts
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.CategoryTheory.Limits.BiproductMatrixFunctor

/-!
# The hypotheses of one step of [Stacks, Tag 05YV], read off the special-fibre square

One step of the deformation argument of [Stacks, Tag 05YV] asks two things about the kernel of
the square-zero extension it extends across: that the first higher direct image along the
morphism of stages kill it, and that its direct image be quasi-coherent.  In the situation of
[Stacks, Tag 0E3X] that kernel is `(i_{X,n})_* 𝒪_X`, or a finite direct sum of copies of it, and
the data available is the commutative square of special fibres

```
X --- f ---> Y
|            |
i_{X,n}     i_{Y,n}
v            v
Uₙ --- gₙ --> Vₙ
```

together with the tag's own hypotheses on `f`, namely `R¹f_*𝒪_X = 0` and `f_*𝒪_X = 𝒪_Y`.  This
file discharges both of 05YV's hypotheses from exactly that input.

## Main results

* `Stacks.BaseAdicFiltration.isZero_rightDerived_one_pushforward_unit_of_square`:
  `R¹(gₙ)_* ((i_{X,n})_* 𝒪_X) = 0`, from `R¹f_*𝒪_X = 0`.
* `Stacks.BaseAdicFiltration.isZero_rightDerived_one_pushforward_biprod_unit_of_square`:
  the same for a finite direct sum of copies of `(i_{X,n})_* 𝒪_X`.
* `Stacks.BaseAdicFiltration.isQuasicoherent_pushforward_pushforward_unit_of_square`:
  `(gₙ)_* ((i_{X,n})_* 𝒪_X)` is quasi-coherent, from invertibility of `𝒪_Y ⟶ f_*𝒪_X`.
* `Stacks.BaseAdicFiltration.isQuasicoherent_pushforward_biprod_unit_of_square`:
  the same for a finite direct sum of copies.

## Implementation notes

**Both proofs spend the square in the same way, and neither one looks inside a scheme.**  The
composite `i_{X,n} ≫ gₙ` is rewritten as `f ≫ i_{Y,n}`, which moves the work from the morphism
`gₙ` of stages — about which nothing is assumed — onto the morphism `f` of special fibres, where
the tag's hypotheses live, and onto the closed immersion `i_{Y,n}`, which is affine.

For the vanishing this is the chain
`Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.isZero_rightDerived_pushforward_iff`
(the degenerate relative Leray collapse for the closed immersion `i_{X,n}`), then
`Stacks.BaseAdicFiltration.isZero_rightDerived_pushforward_congr` to rewrite the composite along
the square, then `Stacks.BaseAdicFiltration.isZero_rightDerived_one_comp_of_isZero`.

For quasi-coherence it is `AlgebraicGeometry.Scheme.Modules.pushforwardComp` in both directions
with the rewrite of the composite in between, and then the hypothesis that
`Scheme.Modules.unitToPushforwardUnit f` is invertible, which replaces `f_*𝒪_X` by `𝒪_Y` and so
removes the one factor that is not affine.  What is left is
`(i_{Y,n})_* 𝒪_Y`, quasi-coherent by
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`
(Tag 02KG) because a closed immersion is an affine morphism.  This is why the quasi-coherence
statements carry the `f_*𝒪_X = 𝒪_Y` hypothesis and the vanishing statements do not: without it
there is nothing affine to reduce to.

The direct-sum versions are the single-copy ones pushed through the additivity of the functor
involved: `CategoryTheory.Functor.isZero_obj_biproduct` for the vanishing, and
`CategoryTheory.Functor.mapBiproduct` together with
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct` for quasi-coherence.  Both need
`⨁` over the modules on a scheme to be reachable by instance search, and
`CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts` — which supplies it from the
abelian structure — is a theorem rather than an instance, so it is activated locally here,
exactly as in
`StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/FiniteOrderBiproducts.lean`.

The invertibility hypothesis is stated with `(C := Ys.Modules)` pinned, because the category
structure on `AlgebraicGeometry.Scheme.Modules` is a different instance from the one on
`SheafOfModules` that it unfolds to, and instance search does not cross between them; the
`asIso` that consumes it is applied with its instance argument explicit for the same reason.
This is the convention of
`Stacks.BaseAdicFiltration.isIso_unitToPushforwardUnit_of_specialFibre`, which is the intended
source of the hypothesis.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.BaseAdicFiltration

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {Xs Ys Un Vn : Scheme.{u}} (fXY : Xs ⟶ Ys) (iXn : Xs ⟶ Un) [IsClosedImmersion iXn]
  (iYn : Ys ⟶ Vn) [IsClosedImmersion iYn] (gn : Un ⟶ Vn)

/-! ### The vanishing hypothesis -/

/-- **`R¹(gₙ)_*` kills the kernel of the extension.** For a commutative square
`i_{X,n} ≫ gₙ = f ≫ i_{Y,n}` with `i_{X,n}` and `i_{Y,n}` closed immersions, the vanishing of
`R¹f_*𝒪_X` gives the vanishing of `R¹(gₙ)_* ((i_{X,n})_* 𝒪_X)`.

This is the first of the two hypotheses one step of [Stacks, Tag 05YV] asks about the kernel of
the square-zero extension. -/
theorem isZero_rightDerived_one_pushforward_unit_of_square (hsq : iXn ≫ gn = fXY ≫ iYn)
    (hR : IsZero (((Scheme.Modules.pushforward fXY).rightDerived 1).obj
      (SheafOfModules.unit Xs.ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward gn).rightDerived 1).obj
      ((Scheme.Modules.pushforward iXn).obj (SheafOfModules.unit Xs.ringCatSheaf))) :=
  (Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.isZero_rightDerived_pushforward_iff
      iXn gn (Scheme.unitModule Xs) 1).mpr
    ((isZero_rightDerived_pushforward_congr hsq (Scheme.unitModule Xs) 1).mpr
      (isZero_rightDerived_one_comp_of_isZero fXY iYn (Scheme.unitModule Xs) hR))

/-- **`R¹(gₙ)_*` kills a finite direct sum of copies of the kernel.** The direct sum version of
`Stacks.BaseAdicFiltration.isZero_rightDerived_one_pushforward_unit_of_square`, which is the form
the step of [Stacks, Tag 05YV] needs when the extension is cut out by finitely many equations: a
right derived functor of an additive functor is additive, hence annihilates a finite biproduct of
objects it annihilates. -/
theorem isZero_rightDerived_one_pushforward_biprod_unit_of_square (hsq : iXn ≫ gn = fXY ≫ iYn)
    (hR : IsZero (((Scheme.Modules.pushforward fXY).rightDerived 1).obj
      (SheafOfModules.unit Xs.ringCatSheaf))) (k : ℕ) :
    IsZero (((Scheme.Modules.pushforward gn).rightDerived 1).obj
      (⨁ fun _ : Fin k => (Scheme.Modules.pushforward iXn).obj
        (SheafOfModules.unit Xs.ringCatSheaf))) :=
  Functor.isZero_obj_biproduct ((Scheme.Modules.pushforward gn).rightDerived 1) _
    fun _ => isZero_rightDerived_one_pushforward_unit_of_square fXY iXn iYn gn hsq hR

/-! ### The quasi-coherence hypothesis -/

/-- Quasi-coherence of modules on a scheme is invariant under isomorphism. -/
private theorem isQuasicoherent_of_iso {S : Scheme.{u}} {M N : S.Modules} (e : M ≅ N)
    (h : M.IsQuasicoherent) : N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso e h

omit [IsClosedImmersion iXn] in
/-- **The direct image of the kernel of the extension is quasi-coherent.** For a commutative
square `i_{X,n} ≫ gₙ = f ≫ i_{Y,n}` with `i_{X,n}` and `i_{Y,n}` closed immersions, if the
comparison `𝒪_Y ⟶ f_*𝒪_X` is invertible then `(gₙ)_* ((i_{X,n})_* 𝒪_X)` is quasi-coherent.

This is the second of the two hypotheses one step of [Stacks, Tag 05YV] asks about the kernel of
the square-zero extension.  Nothing is assumed of `gₙ`: the square moves the question onto
`i_{Y,n}`, which is affine, and the hypothesis on `f` is what allows `f_*𝒪_X` to be replaced by
`𝒪_Y` along the way. -/
theorem isQuasicoherent_pushforward_pushforward_unit_of_square (hsq : iXn ≫ gn = fXY ≫ iYn)
    (h0 : IsIso (C := Ys.Modules) (Scheme.Modules.unitToPushforwardUnit fXY)) :
    ((Scheme.Modules.pushforward gn).obj
        ((Scheme.Modules.pushforward iXn).obj
          (SheafOfModules.unit Xs.ringCatSheaf))).IsQuasicoherent := by
  have hq : ((Scheme.Modules.pushforward iYn).obj (Scheme.unitModule Ys)).IsQuasicoherent :=
    inferInstance
  have h1 := isQuasicoherent_of_iso ((Scheme.Modules.pushforward iYn).mapIso
    (@asIso _ _ _ _ (Scheme.Modules.unitToPushforwardUnit fXY) h0)) hq
  have h2 := isQuasicoherent_of_iso
    ((Scheme.Modules.pushforwardComp fXY iYn).app (Scheme.unitModule Xs)) h1
  rw [← hsq] at h2
  exact isQuasicoherent_of_iso
    ((Scheme.Modules.pushforwardComp iXn gn).app (Scheme.unitModule Xs)).symm h2

omit [IsClosedImmersion iXn] in
/-- **The direct image of a finite direct sum of copies of the kernel is quasi-coherent.** The
direct sum version of
`Stacks.BaseAdicFiltration.isQuasicoherent_pushforward_pushforward_unit_of_square`: `(gₙ)_*` is
additive, so it carries the direct sum to the direct sum of the direct images, each of which is
quasi-coherent by the single-copy statement, and a finite direct sum of quasi-coherent modules is
quasi-coherent. -/
theorem isQuasicoherent_pushforward_biprod_unit_of_square (hsq : iXn ≫ gn = fXY ≫ iYn)
    (h0 : IsIso (C := Ys.Modules) (Scheme.Modules.unitToPushforwardUnit fXY)) (k : ℕ) :
    ((Scheme.Modules.pushforward gn).obj
        (⨁ fun _ : Fin k => (Scheme.Modules.pushforward iXn).obj
          (SheafOfModules.unit Xs.ringCatSheaf))).IsQuasicoherent := by
  have : ((Scheme.Modules.pushforward gn).obj
      ((Scheme.Modules.pushforward iXn).obj
        (SheafOfModules.unit Xs.ringCatSheaf))).IsQuasicoherent :=
    isQuasicoherent_pushforward_pushforward_unit_of_square fXY iXn iYn gn hsq h0
  have hb : (⨁ fun _ : Fin k => (Scheme.Modules.pushforward gn).obj
      ((Scheme.Modules.pushforward iXn).obj
        (SheafOfModules.unit Xs.ringCatSheaf))).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct _
  exact isQuasicoherent_of_iso ((Scheme.Modules.pushforward gn).mapBiproduct _).symm hb

end Stacks.BaseAdicFiltration

end
