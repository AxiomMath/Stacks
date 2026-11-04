module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.SecondVariableOnSheaves

/-!
# The underived identity of Stacks 08I6 as an isomorphism of bifunctors

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi.  The two sides of the
underived identity of Stacks 08I6,

`(F, G) ↦ F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G`  and  `(F, G) ↦ (F ⊗_O f^*G)|_{f⁻¹O'}`,

are bifunctors from sheaves of `O'`-modules and sheaves of `O`-modules to sheaves of
`f⁻¹O'`-modules, and they are isomorphic.  Both are built by fixing the sheaf of `O'`-modules
and letting the sheaf of `O`-modules vary, so functoriality in the first variable is the
functoriality of tensoring with a morphism of second factors, and the isomorphism between them
is `Stacks.Cohomology.MixedDerivedTensor.underivedTensorInverseImageLinearIso` together with its
naturality in the sheaf of `O'`-modules.

This is the bifunctorial form of the identity that the source's proof of Stacks 08I6 passes to
the derived category; see the implementation notes for what separates it from the derived
statement.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.mixedTensorInverseImage`: the bifunctor
  `(G, F) ↦ F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G`.
* `Stacks.Cohomology.MixedDerivedTensor.mixedTensorPullback`: the bifunctor
  `(G, F) ↦ (F ⊗_O f^*G)|_{f⁻¹O'}`.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.underivedTensorInverseImageBifunctorIso`: **the
  underived identity of Stacks 08I6, bifunctorially.**  Unconditional in `f`.

## Implementation notes

**What a derived form of the tag still needs beyond this.**  Stacks 08I6 asserts an isomorphism
in `D(f⁻¹O')` between `F ⊗^L_O Lf^*G` restricted to `f⁻¹O'` and `F|_{f⁻¹O'} ⊗^L_{f⁻¹O'} f⁻¹G`,
and three things separate that from the isomorphism of bifunctors below.  First, the derived
tensor product of `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct` is computed on
K-flat representatives by the total complex of a tensor double complex formed with the curried
bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`, whereas the bifunctor below is written
with `Stacks.sheafTensorRight`; the two fix opposite factors and are the same tensor product only
after the symmetry of the tensor product of sheaves of modules.  Second, the bifunctor
isomorphism has to be carried to double complexes and then totalised, which asks for additivity
in each variable and for the coproducts of each total degree, as
`Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso` does for the pullback of a total tensor
complex.  Third, the resulting complex-level isomorphism has to be descended, and the inputs for
that are available: restriction of scalars along `f⁻¹O' ⟶ O` is exact,
`Stacks.Cohomology.MixedDerivedTensor.kFlat_pullbackComplex_auxHomG` transfers K-flatness along
`g^*`, and `Stacks.Cohomology.MixedDerivedTensor.derivedPullbackFactorIso` is `Lf^* ≅ Lg^* ⋙ Lh^*`.

**The morphism-of-sites hypothesis.**  Nothing below carries one: the underived statement is
unconditional in `f`.  The derived statement will carry
`CategoryTheory.Functor.IsMorphismOfSites`, the hypothesis under which the library's derived
pullback exists throughout this directory, and that is not a weakening: without it the
underlying continuous functor of `f` need not induce a morphism of topoi at all.

**Universes.**  Everything is at `AlgebraicGeometry.RingedTopos.{u, u, u}`, as in
`StacksPullbackFactorization`.

**No tag is placed in this file.**  The assertion of Stacks 08I6 is about derived categories and
nothing here concludes that.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Cohomology.MixedDerivedTensor

open Stacks Stacks.FlatChangeOfRings StacksPullbackFactorization

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The left-hand bifunctor of Stacks 08I6**: a sheaf `G` of `O'`-modules and a sheaf `F` of
`O`-modules are carried to `F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G`.

Functoriality in `F` is that of tensoring with a fixed second factor, and functoriality in `G`
is that of tensoring with a morphism of second factors, composed with the inverse image of
sheaves of modules. -/
def mixedTensorInverseImage (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) ⥤
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos f).O) :=
  (auxHomG f).pullbackTopos ⋙
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).flip ⋙
    (Functor.whiskeringLeft
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos f).O))
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos f).O))).obj
      (restrictToInvRing f)

/-- **The right-hand bifunctor of Stacks 08I6**: a sheaf `G` of `O'`-modules and a sheaf `F` of
`O`-modules are carried to `(F ⊗_O f^*G)|_{f⁻¹O'}`. -/
def mixedTensorPullback (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) ⥤
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos f).O) :=
  f.pullbackTopos ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip ⋙
    (Functor.whiskeringRight
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos f).O))).obj
      (restrictToInvRing f)

/-- **The underived identity of Stacks 08I6, bifunctorially.**  For a morphism of ringed topoi
`f`, the bifunctor carrying `(G, F)` to `F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G` and the bifunctor carrying
it to `(F ⊗_O f^*G)|_{f⁻¹O'}` are isomorphic.

The components are `underivedTensorInverseImageLinearIso`, which is natural in `F` by
construction, and the naturality in `G` is
`underivedTensorInverseImageLinearIso_hom_naturality_snd`.  No hypothesis on `f` beyond being a
morphism of ringed topoi is used. -/
def underivedTensorInverseImageBifunctorIso (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    mixedTensorInverseImage f ≅ mixedTensorPullback f :=
  NatIso.ofComponents (fun G ↦ underivedTensorInverseImageLinearIso f G)
    (fun γ ↦ underivedTensorInverseImageLinearIso_hom_naturality_snd f γ)

end Stacks.Cohomology.MixedDerivedTensor

end
