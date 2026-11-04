module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionFiberDecomposition

/-!
# The fibre comparison of the projection formula

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `Λ` be a commutative
ring, let `F` be a sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. At a geometric
point `ȳ` of `Y` the fibre of the presheaf `f_{p!}F ⊗_Λ G` is canonically the fibre of
`f_{p!}(F ⊗_Λ f^{-1}G)`: decompose the fibre of `f_{p!}` over the geometric fibre, distribute
the tensor product over that sum, and on each summand use that the fibre functor on presheaves
is monoidal and that the stalk of `f^{-1}G` above a point of the fibre is the stalk of `G` at
`ȳ`.

This is the chain of `AlgebraicGeometry.SmallEtale.modShriekProjectionStalkIso` with the outer
legs replaced by the decompositions of the *presheaf* fibre, which is the fibre the comparison
map of [Stacks, Tag 0GKF] can be computed on.

## Main definitions

* `AlgebraicGeometry.SmallEtale.preservesFilteredColimitsTensorLeftSmall` and
  `AlgebraicGeometry.SmallEtale.preservesFilteredColimitsTensorRightSmall` — tensoring with a
  fixed `Λ`-module preserves the filtered colimits computing a fibre, which is what makes the
  fibre functor on presheaves of `Λ`-modules monoidal.
* `AlgebraicGeometry.SmallEtale.modProjectionFiberSummandIso` — **the summand of the fibre
  comparison** at a point `x̄` of the geometric fibre: `F_x̄ ⊗_Λ G_ȳ ≅ (F ⊗_Λ f^{-1}G)_x̄`.
* `AlgebraicGeometry.SmallEtale.modProjectionFiberIso` — **the fibre comparison of the
  projection formula.**

## Implementation notes

The monoidality used on each summand is that of the fibre functor on *presheaves*, not of the
fibre functor on sheaves: the comparison of the pointwise tensor product with the tensor product
of sheaves then appears explicitly, as
`AlgebraicGeometry.SmallEtale.isIso_presheafFiber_map_moduleToTensorSection`, and the germ
formula for it is
`AlgebraicGeometry.SmallEtale.toPresheafFiber_tensorSupportedSectionsHom_val`. Going through the
sheaf-level monoidality instead would require comparing the two monoidal structures.

The three preservation instances that make the fibre functor monoidal are pinned at the size of
the site, the way `AlgebraicGeometry.SmallEtale.modStalkMonoidal` pins them: left to instance
resolution the sizes are metavariables and the constraints have no unique solution.

Nothing here carries a `stacks` attribute: this is the fibre computation behind
[Stacks, Tag 0GKF] and not that tag, whose statement is that a map of sheaves is an isomorphism.

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped DirectSum

namespace AlgebraicGeometry.SmallEtale

universe u v

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat
attribute [local instance] hasLimitsOfSizeModuleCatSmall

/-- **Tensoring with a fixed `Λ`-module preserves the filtered colimits of the size of the
site**, in the first variable: tensoring has a right adjoint, `Λ`-modules being monoidal closed.
Pinned at that size: left to instance resolution the size is a metavariable and the constraint
has no unique solution. -/
public theorem preservesFilteredColimitsTensorLeftSmall (M : ModuleCat.{max (u + 1) v} Λ) :
    PreservesFilteredColimitsOfSize.{u, u} (tensorLeft M) :=
  ⟨fun _ => inferInstance⟩

/-- **Tensoring with a fixed `Λ`-module preserves the filtered colimits of the size of the
site**, in the second variable. -/
public theorem preservesFilteredColimitsTensorRightSmall (M : ModuleCat.{max (u + 1) v} Λ) :
    PreservesFilteredColimitsOfSize.{u, u} (tensorRight M) :=
  ⟨fun _ => { preservesColimit := inferInstance }⟩

attribute [local instance] preservesFilteredColimitsTensorLeftSmall
attribute [local instance] preservesFilteredColimitsTensorRightSmall

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The summand of the fibre comparison of the projection formula** indexed by a point `x̄` of
the geometric fibre: `F_x̄ ⊗_Λ G_ȳ ≅ (F ⊗_Λ f^{-1}G)_x̄`. The stalk of `G` at `ȳ` is the stalk of
`f^{-1}G` at `x̄` by Stacks 03Q1, the fibre functor on presheaves is monoidal, and the pointwise
tensor product has the same fibre as the tensor product of sheaves. -/
public def modProjectionFiberSummandIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricFiberPoint B f s) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj F ⊗
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G ≅
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) := by
  have hiso := isIso_presheafFiber_map_moduleToTensorSection B Λ X F
    ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) (x.toGeometricPoint B f s)
  exact tensorIso (Iso.refl _) (stalkPullbackFiberIso.{u, v} B Λ f s G x) ≪≫
    Functor.Monoidal.μIso
      ((geometricPointSitePoint B X.obj X.property (x.toGeometricPoint B f s)).presheafFiber)
      F.obj ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj ≪≫
    @asIso _ _ _ _ _ hiso

/-- The summandwise comparison of `AlgebraicGeometry.SmallEtale.modProjectionFiberSummandIso`,
assembled over the geometric fibre. -/
public def modProjectionFiberSummandsIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    ModuleCat.of Λ (⨁ x : GeometricFiberPoint B f s,
        (((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
          (x.toGeometricPoint B f s)).obj F ⊗
            (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G :
              ModuleCat.{max (u + 1) v} Λ) : Type _)) ≅
      modFiberStalks.{u, v, max (u + 1) v} B Λ f s
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) :=
  (DirectSum.congrLinearEquiv (R := Λ)
    (N := fun x : GeometricFiberPoint B f s =>
      (((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
        (x.toGeometricPoint B f s)).obj F ⊗
          (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G :
            ModuleCat.{max (u + 1) v} Λ) : Type _))
    (P := fun x : GeometricFiberPoint B f s =>
      ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) : Type _))
    fun x => (modProjectionFiberSummandIso.{u, v} B Λ f s F G x).toLinearEquiv).toModuleIso

/-- **The fibre comparison of the projection formula.** At a geometric point `ȳ` of `Y` the
fibre of the presheaf `f_{p!}F ⊗_Λ G` is canonically the fibre of `f_{p!}(F ⊗_Λ f^{-1}G)`. -/
public def modProjectionFiberIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.obj
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj) ≅
      (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.obj
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) :=
  (Functor.Monoidal.μIso
      ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber)
      ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj).symm ≪≫
    tensorIso (modFiniteSupportFiberIso B Λ f F s ≪≫
      moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F) (Iso.refl _) ≪≫
    modFiberStalksTensorIso.{u, v} B Λ f s F
      ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G) ≪≫
    modProjectionFiberSummandsIso.{u, v} B Λ f s F G ≪≫
    (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s
      (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).symm ≪≫
    (modFiniteSupportFiberIso B Λ f (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s).symm

end AlgebraicGeometry.SmallEtale

end
