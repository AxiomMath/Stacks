module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoherentMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# The pullback of coherent modules to a point over an affine scheme

Let `𝒳` be an algebraic stack and let `x` be an object of `𝒳` lying over `Spec R`, a morphism
`f : Spec R ⟶ 𝒳`. The pullback `f^* : QCoh(𝒪_𝒳) ⥤ Mod_R`,
`AlgebraicGeometry.Stack.AlgebraicStacks.pointPullback`, carries a coherent module, which is of
finite presentation, to a finitely generated `R`-module
(`AlgebraicGeometry.Stack.AlgebraicStacks.finite_pointPullback_obj`). So its restriction to
`Coh(𝒪_𝒳)` is a functor `Coh(𝒪_𝒳) ⥤ Mod^{fg}_R`, and it is a tensor functor: additive and
braided monoidal for the symmetric monoidal structure of
`AlgebraicGeometry.Stack.isMonoidal_coherentModules` and that of `FGModuleCat R`. These are the
functors of Stacks 0GRR, which says that every right exact tensor functor
`Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` is one of them when `𝒳` is Noetherian with affine diagonal and `R` is
Noetherian.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.coherentPointPullback`: `f^*` on coherent modules, as
  a functor `Coh(𝒪_𝒳) ⥤ FGModuleCat R`, with its tensor structure
  `coherentPointPullbackMonoidal`, `coherentPointPullbackBraided` and its additivity.
* `AlgebraicGeometry.Stack.AlgebraicStacks.coherentPointPullbackCompIso`: followed by the
  inclusion `FGModuleCat R ⥤ ModuleCat R` it is the restriction of `f^*` along
  `Coh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`.

## References

* [Stacks Project, Tag 0GRR](https://stacks.math.columbia.edu/tag/0GRR)
* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] coherentAmbientMonoidal coherentAmbientBraided coherentAmbientSymmetric
  fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric
  coherentQuasicoherentInclusionBraided

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : 𝒳.val.val.obj) {R : Type u} [CommRing R]
  (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R))

/-- **The pullback `f^* : Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` along a point `f : Spec R ⟶ 𝒳`**: the restriction
of `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullback` to coherent modules, whose sections at
the point are finitely generated. -/
def coherentPointPullback : Coh.{u, u, w} B S hS 𝒳 ⥤ FGModuleCat.{u} R :=
  (ModuleCat.isFG R).lift (coherentQuasicoherentInclusion B S hS 𝒳 ⋙ pointPullback B S hS 𝒳 x e)
    fun M =>
      haveI : ((coherentQuasicoherentInclusion B S hS 𝒳).obj M).obj.IsFinitePresentationOnSite :=
        M.property.2
      finite_pointPullback_obj B S hS 𝒳 x e _

/-- Followed by the inclusion of finitely generated modules into all modules,
`AlgebraicGeometry.Stack.AlgebraicStacks.coherentPointPullback` is `f^*` on quasi-coherent
modules restricted to coherent ones. -/
def coherentPointPullbackCompIso :
    coherentPointPullback B S hS 𝒳 x e ⋙ forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ≅
      coherentQuasicoherentInclusion B S hS 𝒳 ⋙ pointPullback B S hS 𝒳 x e :=
  Iso.refl _

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.coherentPointPullback` is a monoidal functor. -/
instance coherentPointPullbackMonoidal : (coherentPointPullback B S hS 𝒳 x e).Monoidal :=
  ObjectProperty.liftMonoidal _ _ _

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.coherentPointPullback` is a braided functor. -/
instance coherentPointPullbackBraided : (coherentPointPullback B S hS 𝒳 x e).Braided :=
  { coherentPointPullbackMonoidal B S hS 𝒳 x e, ObjectProperty.liftLaxBraided _ _ _ with }

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.coherentPointPullback` is additive. -/
instance coherentPointPullbackAdditive : (coherentPointPullback B S hS 𝒳 x e).Additive where
  map_add {_ _ f g} := ObjectProperty.hom_ext _
    ((pointPullback B S hS 𝒳 x e).map_add (f := (coherentQuasicoherentInclusion B S hS 𝒳).map f)
      (g := (coherentQuasicoherentInclusion B S hS 𝒳).map g))

end AlgebraicGeometry.Stack.AlgebraicStacks
