module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsModel
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel

/-!
# Algebraic stacks are locally small

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, with morphisms
in an arbitrary universe.  If its diagonal is representable by algebraic spaces, then its
hom-sets are small at the universe `u` of the schemes of the site: the morphisms between two
objects of a fibre over `U` are the sections over `U` of the sheaf `Isom(x, y)`, which is an
algebraic space by Stacks 045G and so has its sections in `Type u`; and a morphism of the total
category is a morphism of the site together with a morphism of a fibre
(`CategoryTheory.Functor.locallySmall_of_small_fiberHom`).  In particular an
algebraic stack is locally small, and so is any category fibred in groupoids with a 1-morphism
representable by algebraic spaces to a locally small one, that 1-morphism being faithful by
Stacks 04Y5.

## Main results

* `AlgebraicGeometry.Stack.small_fiberHom_of_hasRepresentableDiagonal`: the fibre hom-sets of a
  category fibred in groupoids with representable diagonal are small.
* `AlgebraicGeometry.Stack.locallySmall_of_hasRepresentableDiagonal` and
  `AlgebraicGeometry.Stack.locallySmall_of_isAlgebraicStack`: such a category, and in particular
  an algebraic stack, is locally small.
* `AlgebraicGeometry.Stack.locallySmall_of_isRepresentableByAlgebraicSpaces`: local smallness
  transfers back along a 1-morphism representable by algebraic spaces.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w u v t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fibre hom-sets of a category fibred in groupoids with representable diagonal are small**
at the universe of the schemes of the site: they are the sections over the base of the sheaf
`Isom(x, y)`, which is an algebraic space by Stacks 045G. -/
theorem small_fiberHom_of_hasRepresentableDiagonal
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS))
    (h : HasRepresentableDiagonal B S hS 𝒳) (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U) : Small.{u} (x ⟶ y) := by
  have hpf : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨F, -, ⟨e⟩⟩ := (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp
    h U x y
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 _)
  let O₁ : Over U := (Over.iteratedSliceBackward U).obj T₀
  let O₀ : Over U := Over.mk (𝟙 U)
  let ι : O₁ ≅ O₀ :=
    Over.isoMk (Over.isoMk (Iso.refl _) (by dsimp [O₁, O₀, T₀, Over.iteratedSliceBackward]))
      (by
        apply Over.OverMorphism.ext
        dsimp [O₁, O₀, T₀, Over.iteratedSliceBackward]
        simp)
  have h₁ : Small.{u} ((𝒳.val.p.isomPresheaf x y).obj (op O₁)) := by
    have hF : Small.{u} ((F ⋙ uliftFunctor.{v, u}).obj (op T₀)) :=
      (inferInstance : Small.{u} (ULift.{v} (F.obj (op T₀))))
    have : Small.{u} (ULift.{u} ((𝒳.val.p.isomPresheaf x y).obj (op O₁))) :=
      @small_map _ _ hF ((e.app (op T₀)).toEquiv.symm)
    exact small_of_injective (f := ULift.up.{u}) ULift.up_injective
  have h₀ : Small.{u} ((𝒳.val.p.isomPresheaf x y).obj (op O₀)) :=
    @small_map _ _ h₁ (((𝒳.val.p.isomPresheaf x y).mapIso ι.op).toEquiv.symm)
  have hm : Small.{u} ((𝒳.val.p.morPresheaf x y).obj (op O₀)) :=
    @small_map _ _ h₀ (((isomPresheafIsoMorPresheaf 𝒳.val.p 𝒳.isFiberedInGroupoids x y).app
      (op O₀)).toEquiv.symm)
  let E : (x ⟶ y) ≃ (𝒳.val.p.morPresheaf x y).obj (op O₀) :=
    (Functor.pullbackFiberIdIso x).symm.homCongr (Functor.pullbackFiberIdIso y).symm
  exact @small_map _ _ hm E

/-- **A category fibred in groupoids with representable diagonal is locally small** at the
universe of the schemes of the site. -/
theorem locallySmall_of_hasRepresentableDiagonal
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS))
    (h : HasRepresentableDiagonal B S hS 𝒳) : LocallySmall.{u} 𝒳.val.obj := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  exact Functor.locallySmall_of_small_fiberHom 𝒳.val.p
    (small_fiberHom_of_hasRepresentableDiagonal B S hS 𝒳 h)

/-- **Local smallness transfers back along a 1-morphism representable by algebraic spaces**,
which is faithful by Stacks 04Y5. -/
theorem locallySmall_of_isRepresentableByAlgebraicSpaces
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) [LocallySmall.{u} 𝒴.val.obj] :
    LocallySmall.{u} 𝒳.val.obj where
  hom_small a b := by
    have := faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hf
    exact small_of_injective (CatFiberedInGroupoids.homFunctor f).map_injective

end AlgebraicGeometry.Stack

end
