module

public import StacksFrontier.Deformation.Artin.Infinitesimal.FunctorDataComparison

/-!
# Identifying the tangent functor with a linear functor through the lift classes

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `x` be an
object of `𝒳` over `Spec A`, and let `T` be a tangent functor of `x` in the sense of Stacks 07Y9
(`Deformation.Artin.TangentFunctorData`): an `A`-linear functor on the site modules whose value at
`M` is identified with the isomorphism classes of lifts of `x` to `Spec A[M]`.

The tangent spaces are often computed by other means, as the values `F(M)` of some additive
`A`-linear functor `F` of `A`-modules. In Remark 0D1P of the source, for instance,
`F(M) = Ext¹_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A M)`. Such a computation consists of a bijection between the
lift classes over `A[M]` and `F(M)` for every `M`, compatible with pulling a lift back along
`A[M] ⟶ A[N]`. This file shows that such bijections are automatically `A`-linear for the
structure of `T`, so that they assemble into an isomorphism of `T` with `F`. This is the form in
which the tangent part of a dual deformation situation (Stacks 07YX) is supplied.

## Main definitions

* `Deformation.Artin.tangentLinearEquivOfLiftClassEquiv` — the linear equivalence
  `T(M) ≃ₗ[A] F(M)` attached to a natural family of bijections of lift classes with `F(M)`.

## Main results

* `Deformation.Artin.tangentLinearEquivOfLiftClassEquiv_apply` — it is the given bijection
  composed with the identification of `T(M)` with the lift classes.
* `Deformation.Artin.tangentLinearEquivOfLiftClassEquiv_natural` — it is natural in `M`.

## Implementation notes

Linearity is not a further hypothesis. Addition in the values of an additive functor is
recovered from the two projections and the codiagonal of a biproduct, and scalar
multiplication from the scalar endomorphisms of the source
(`Deformation.isLinearMap_of_naturality`). A family of maps natural for the underlying
set-valued functors therefore respects both. This is the uniqueness half of Stacks 06I6: the
linear structure of a set-valued functor that preserves finite products is determined by the
functor.

The site modules have binary biproducts because they are closed under binary products in
`Mod_A` (`Deformation.Artin.siteModuleHasLimitPair`). That uses that `Spec A` lies in the site,
so it is not an instance.

## References

* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
* [Stacks Project, Tag 06I6](https://stacks.math.columbia.edu/tag/06I6)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w u₁

namespace Deformation.Artin

section Biproducts

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})

/-- The site modules have binary biproducts: they are closed under binary products in `Mod_A`,
which is preadditive. -/
theorem siteModule_hasBinaryBiproducts (hA : B.Contains (Spec (.of A))) :
    HasBinaryBiproducts (SiteModule A B) := by
  have : ∀ M N : SiteModule A B, HasLimit (pair M N) :=
    fun M N => siteModuleHasLimitPair A B hA
  have : HasBinaryProducts (SiteModule A B) := hasBinaryProducts_of_hasLimit_pair _
  exact HasBinaryBiproducts.of_hasBinaryProducts

end Biproducts

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x : X}
  {hx : p.obj x = algebraOver A B S hS toS hA}
  (T : TangentFunctorData A B S hS toS hA p x hx)
  (F : ModuleCat.{u} A ⥤ ModuleCat.{u₁} A) [F.Additive] [F.Linear A]
  (Φ : ∀ M : SiteModule A B, squareZeroLiftClasses A B S hS toS hA p x hx M ≃ F.obj M.obj)
  (hΦ : ∀ {M N : SiteModule A B} (f : M ⟶ N)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M)
    (b : squareZeroLiftClasses A B S hS toS hA p x hx N),
    IsPullbackOfSquareZeroLift A B S hS toS hA p x hx f a b → Φ N b = F.map f.hom (Φ M a))

include hΦ in
/-- The bijections of lift classes with the values of `F`, read on the values of `T`, are
`A`-linear. -/
theorem isLinearMap_liftClassEquiv (M : SiteModule A B) :
    IsLinearMap A (fun z : T.functor.obj M => Φ M (T.liftEquiv M z)) := by
  have := siteModule_hasBinaryBiproducts A B hA
  exact isLinearMap_of_naturality T.functor ((IsSiteModule A B).ι ⋙ F)
    (fun M z => Φ M (T.liftEquiv M z))
    (fun f z => hΦ f _ _ (T.liftEquiv_natural f z)) M

/-- **The tangent functor identified with a linear functor through the lift classes.** Let `F`
be an additive `A`-linear functor of `A`-modules, and suppose that for every site module `M`
the lift classes of `x` over `A[M]` are in bijection with `F(M)`, compatibly with pulling a lift
back along `A[M] ⟶ A[N]` for every module map `M ⟶ N`. Then these bijections, read on the values
of a tangent functor `T` of `x`, are `A`-linear equivalences `T(M) ≃ₗ[A] F(M)`. -/
def tangentLinearEquivOfLiftClassEquiv (M : SiteModule A B) :
    T.functor.obj M ≃ₗ[A] F.obj M.obj where
  toEquiv := (T.liftEquiv M).trans (Φ M)
  map_add' := (isLinearMap_liftClassEquiv T F Φ hΦ M).map_add
  map_smul' := (isLinearMap_liftClassEquiv T F Φ hΦ M).map_smul

/-- The equivalence `T(M) ≃ₗ[A] F(M)` is the given bijection of lift classes with `F(M)`, composed
with the identification of `T(M)` with the lift classes. -/
@[simp]
theorem tangentLinearEquivOfLiftClassEquiv_apply (M : SiteModule A B) (z : T.functor.obj M) :
    tangentLinearEquivOfLiftClassEquiv T F Φ hΦ M z = Φ M (T.liftEquiv M z) :=
  rfl

/-- The equivalences `T(M) ≃ₗ[A] F(M)` are natural in the site module `M`. -/
theorem tangentLinearEquivOfLiftClassEquiv_natural {M N : SiteModule A B} (f : M ⟶ N)
    (z : T.functor.obj M) :
    tangentLinearEquivOfLiftClassEquiv T F Φ hΦ N (T.functor.map f z) =
      F.map f.hom (tangentLinearEquivOfLiftClassEquiv T F Φ hΦ M z) :=
  hΦ f _ _ (T.liftEquiv_natural f z)

end Deformation.Artin

end
