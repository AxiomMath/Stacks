module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective

/-!
# Morphisms of modules bijective over the affine chart diagrams of a morphism

Let `g : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`.  A
morphism of `𝒪_X`-modules on the small étale site of `X` which is bijective on the sections
over every affine étale scheme chart of `X` that is the source of a commutative square of affine
étale scheme charts over `g` is an isomorphism: such charts cover every étale scheme chart of
`X`, by `AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology`, so the morphism is
locally bijective.

## Main results

* `AlgebraicGeometry.Space.isIso_of_bijective_affineChartDiagram`: **a morphism of
  `𝒪_X`-modules bijective over the source charts of the affine chart diagrams over `g` is an
  isomorphism.**
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **A morphism of `𝒪_X`-modules which is bijective on the sections over the source chart of
every affine chart diagram over `g` is an isomorphism.**  Those source charts generate a covering
sieve of every étale scheme chart of `X`
(`AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology`), so the morphism is locally
injective and locally surjective. -/
theorem isIso_of_bijective_affineChartDiagram (g : X ⟶ Y)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : ∀ d : ChartDiagram B S hS X.1 Y.1 g.hom,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
        Function.Bijective (φ.val.app (op d.U)).hom) :
    IsIso φ := by
  have hcov := generate_affineChartDiagram_mem_topology B S hS g (fun _ => True)
    (fun _ _ => trivial)
  have hinj : PresheafOfModules.IsLocallyInjective (smallEtaleRingedSite B S hS X.1 X.2).J
      φ.val := by
    constructor
    intro U x y hxy
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_ (hcov U.unop)
    rintro W b ⟨Z, l, a, ⟨hZ, d, rfl, hV, -⟩, rfl⟩
    refine (Presheaf.equalizerSieve x y).downward_closed ?_ l
    refine (h d hZ hV).1 ?_
    have hx := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map φ.val) a.op x
    have hy := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map φ.val) a.op y
    exact hx.trans ((congrArg (((PresheafOfModules.toPresheaf _).obj N.val).map a.op) hxy).trans
      hy.symm)
  have hsurj : PresheafOfModules.IsLocallySurjective (smallEtaleRingedSite B S hS X.1 X.2).J
      φ.val := by
    constructor
    intro U s
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_ (hcov U)
    rintro W b ⟨Z, l, a, ⟨hZ, d, rfl, hV, -⟩, rfl⟩
    refine (Presheaf.imageSieve _ s).downward_closed ?_ l
    exact (h d hZ hV).2 _
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective φ

end AlgebraicGeometry.Space

end
