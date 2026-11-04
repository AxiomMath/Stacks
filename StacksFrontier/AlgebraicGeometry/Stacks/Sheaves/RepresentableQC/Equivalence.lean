module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.AffineEtaleLiftedCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedCartesianEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedEtaleSliceDescent

/-!
# `QC(𝒳)` of a category represented by an algebraic space (Stacks 0H0K)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids which is represented by an
algebraic space `X` (Stacks 04SV): `X` is the sheaf `F` and `e` an equivalence over the site
between `𝒳` and the category of elements of `F`. **Stacks 0H0K** says that `QC(𝒳)` (Stacks 0H0H)
is canonically equivalent to `D_QCoh(O_X)` (Stacks 071X).

The proof is the source's, carried out on the single-universe lifts of the two ringed sites
(`AlgebraicGeometry.RingedSite.lift`), so that derived categories of modules, derived pullbacks
and direct images are available on both sides:

1. `QC(𝒳)` is the full subcategory of `D(𝒳_{affine, étale}, O)` of the objects `K` with `Rε_*K`
   cartesian (Stacks 0H0J with Stacks 0GZS), on the lift `X↑` of `𝒳_{affine, étale}`:
   `AlgebraicGeometry.Stack.quasiCoherentDerivedLiftedCartesianEquivalence`.
2. The affine étale charts of `X` form a full, cocontinuous subsite of `𝒳_{affine, étale}`
   (Stacks 073M), with the same structure sheaf; the derived pullback `Lf^*` and the direct
   image `f_*` along the morphism `f : X↑ ⟶ Y↑` to the lift `Y↑` of `X_{affine, étale}` restrict
   to mutually inverse equivalences of the 0GZS subcategories
   (`Stacks.Cohomology.SubsiteQuasiCoherentEquivalence.equivalence`, the argument of Stacks
   09J1). Its hypotheses are the unit statement of Stacks 0H0J on the slices
   (`AlgebraicGeometry.Stack.affineLiftedSite_isIso_derivedEpsilonAdjunction_unit`) and descent
   along the étale coverings of an object of `𝒳_{affine}` by charts
   (`AlgebraicGeometry.Stack.nonempty_descentCover`).
3. The 0GZS subcategory of `D(X_{affine, étale}, O_X)` is `D_QCoh(O_X)` (Stacks 0H0J for `X`,
   Stacks 0H06, Descent 03DX):
   `AlgebraicGeometry.Space.cartesianPushforwardEquivalenceQuasicoherentDerived`.

## Main results

* `AlgebraicGeometry.Stack.liftedAffineEtaleCartesianEquivalence`: step 2, `f_*` and `Lf^*` on
  the 0GZS subcategories.
* `AlgebraicGeometry.Stack.representableQuasiCoherentDerivedEquivalence`: **Stacks 0H0K**, the
  equivalence `QC(𝒳) ≌ D_QCoh(O_X)` for `𝒳` represented by `X` through `e`, with its functor and
  inverse described by `representableQuasiCoherentDerivedEquivalence_functor` and `_inverse`.
* `AlgebraicGeometry.Stack.nonempty_quasiCoherentDerived_equivalence`: the same statement for an
  object `𝒳` of the 2-category of categories fibred in groupoids satisfying
  `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace`.

## References

* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

open Stacks.Cohomology.SubsiteQuasiCoherentEquivalence

universe u v w t

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)

/-- **The middle step of Stacks 0H0K**: on the 0GZS subcategories, the direct image `f_*` along
the morphism `f : X↑ ⟶ Y↑` of `AlgebraicGeometry.Stack.liftedAffineEtaleHom` (the affine étale
charts of `F` in the lifted `𝒳_{affine, étale}`) is an equivalence, inverse to the derived
pullback `Lf^*`. This is `Stacks.Cohomology.SubsiteQuasiCoherentEquivalence.equivalence` for `f`:
its functor is full, faithful and cocontinuous by Stacks 073M, the `ε`-units on the slices of `X↑`
are invertible by Stacks 0H0J
(`AlgebraicGeometry.Stack.affineLiftedSite_isIso_derivedEpsilonAdjunction_unit`), and every
object of `X↑` has a descent cover by charts (`AlgebraicGeometry.Stack.nonempty_descentCover`). -/
def liftedAffineEtaleCartesianEquivalence :
    (IsCartesianPushforwardOn
        (Space.affineEtaleLiftedSite.{u, max v w t} B S hS F hF)).FullSubcategory ≌
      (IsCartesianPushforwardOn (affineLiftedSite.{u, v, w, t} B S hS p hp)).FullSubcategory :=
  haveI : (liftedAffineEtaleHom.{u, v, w, t} B S hS p hp F hF e).u.Full :=
    liftedAffineEtaleInclusion_full.{u, v, w, t} B S hS p hp F hF e
  haveI : (liftedAffineEtaleHom.{u, v, w, t} B S hS p hp F hF e).u.Faithful :=
    liftedAffineEtaleInclusion_faithful.{u, v, w, t} B S hS p hp F hF e
  haveI : (liftedAffineEtaleHom.{u, v, w, t} B S hS p hp F hF e).u.IsCocontinuous
      (Space.affineEtaleLiftedSite.{u, max v w t} B S hS F hF).J
      (affineLiftedSite.{u, v, w, t} B S hS p hp).J :=
    liftedAffineEtaleInclusion_isCocontinuous.{u, v, w, t} B S hS p hp F hF e
  equivalence (liftedAffineEtaleHom.{u, v, w, t} B S hS p hp F hF e)
    (affineLiftedSite_isIso_derivedEpsilonAdjunction_unit.{u, v, w, t} B S hS p hp)
    (nonempty_descentCover.{u, v, w, t, 0} B S hS p hp F hF e)

/-- **Stacks 0H0K.** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, represented
by the algebraic space `F` through the equivalence `e` over the site between `𝒳` and the
category of elements of `F` (Stacks 04SV). Then `QC(𝒳)` (Stacks 0H0H) is canonically equivalent
to `D_QCoh(O_F)` (Stacks 071X), with modules in the universe `max v w u t`.

The equivalence is the composite of the three equivalences of the source's proof, on the
single-universe lifts `X↑` of `𝒳_{affine, étale}` and `Y↑` of `F_{affine, étale}`: `ε^*` from
`QC(𝒳)` onto the objects `K` of `D(X↑)` with `Rε_*K` cartesian (Stacks 0H0J, 0GZS); the direct
image `f_*` along the morphism of ringed sites `f : X↑ ⟶ Y↑` given by the affine étale charts of
`F` (Stacks 073M), inverse to the derived pullback `Lf^*` on the 0GZS subcategories (the
argument of Stacks 09J1); and the identification of the 0GZS subcategory of `D(Y↑)` with
`D_QCoh(O_F)` (Stacks 0H0J, 0H06, 03DX). -/
@[stacks 0H0K "QC(𝒳) is canonically equivalent to D_QCoh(O_X) for 𝒳 represented by an \
algebraic space X"]
def representableQuasiCoherentDerivedEquivalence :
    quasiCoherentDerived.{u, v, w, t} B S hS p ≌
      Space.QuasicoherentDerivedCategory.{u, max v w u t} B S hS F hF :=
  (quasiCoherentDerivedLiftedCartesianEquivalence.{u, v, w, t} B S hS p hp).trans <|
    (liftedAffineEtaleCartesianEquivalence.{u, v, w, t} B S hS p hp F hF e).symm.trans
    (Space.cartesianPushforwardEquivalenceQuasicoherentDerived.{u, max v w t} B S hS F hF)

/-- The functor of `AlgebraicGeometry.Stack.representableQuasiCoherentDerivedEquivalence`:
`ε^*` to the lifted `𝒳_{affine, étale}`, then the direct image `f_*` along the affine étale charts
of `F`, then the identification with `D_QCoh(O_F)`. -/
theorem representableQuasiCoherentDerivedEquivalence_functor :
    (representableQuasiCoherentDerivedEquivalence.{u, v, w, t} B S hS p hp F hF e).functor =
      (quasiCoherentDerivedLiftedCartesianEquivalence.{u, v, w, t} B S hS p hp).functor ⋙
        (liftedAffineEtaleCartesianEquivalence.{u, v, w, t} B S hS p hp F hF e).inverse ⋙
        (Space.cartesianPushforwardEquivalenceQuasicoherentDerived.{u, max v w t}
          B S hS F hF).functor :=
  rfl

/-- The inverse of `AlgebraicGeometry.Stack.representableQuasiCoherentDerivedEquivalence`: the
identification of `D_QCoh(O_F)` with the 0GZS subcategory of the lifted `F_{affine, étale}`,
then the derived pullback `Lf^*` along the affine étale charts of `F`, then `Rε_*`. -/
theorem representableQuasiCoherentDerivedEquivalence_inverse :
    (representableQuasiCoherentDerivedEquivalence.{u, v, w, t} B S hS p hp F hF e).inverse =
      (Space.cartesianPushforwardEquivalenceQuasicoherentDerived.{u, max v w t}
          B S hS F hF).inverse ⋙
        (liftedAffineEtaleCartesianEquivalence.{u, v, w, t} B S hS p hp F hF e).functor ⋙
        (quasiCoherentDerivedLiftedCartesianEquivalence.{u, v, w, t} B S hS p hp).inverse :=
  rfl

end

/-- **Stacks 0H0K**, for an object of the 2-category of categories fibred in groupoids: if `𝒳`
is represented by an algebraic space (Stacks 04SV), there is an algebraic space `F` representing
it with `QC(𝒳)` equivalent to `D_QCoh(O_F)`, by
`AlgebraicGeometry.Stack.representableQuasiCoherentDerivedEquivalence`. -/
theorem nonempty_quasiCoherentDerived_equivalence (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (h : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    ∃ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F),
      Nonempty (quasiCoherentDerived.{u, w, v, t} B S hS 𝒳.based.p ≌
        Space.QuasicoherentDerivedCategory.{u, max w v u t} B S hS F hF) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := h
  exact ⟨F, hF, ⟨representableQuasiCoherentDerivedEquivalence.{u, w, v, t} B S hS 𝒳.based.p
    𝒳.isFiberedInGroupoids F hF e⟩⟩

end AlgebraicGeometry.Stack

end
