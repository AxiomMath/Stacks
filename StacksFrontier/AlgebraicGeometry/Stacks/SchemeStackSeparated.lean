module

public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackMapProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The algebraic stack of an affine scheme is separated

Let `T` be an object of the big fppf site over `S` whose underlying scheme is affine. The algebraic
stack represented by `T` is separated in the absolute sense of Stacks 050D, part (7). Viewed over
the terminal scheme (Stacks 04X6) it is equivalent to the stack represented by the same scheme over
the terminal scheme, its structure morphism is then the 1-morphism induced by the unique morphism
of the site to the terminal object, and a 1-morphism between algebraic stacks represented by
algebraic spaces is separated exactly when the morphism of representing algebraic spaces is
(Stacks 04YS). That morphism is the Yoneda image of a morphism of schemes out of an affine scheme,
which is separated.

## Main results

* `AlgebraicGeometry.Stack.isSeparatedOver_of_equivalenceOver_yoneda`: a stack equivalent over
  its base to the stack represented by an object of the site whose structure morphism is a
  separated morphism of schemes is separated over the base.
* `AlgebraicGeometry.Stack.isAbsolutelySeparated_schemeStack_of_isAffine`: the algebraic stack
  represented by an object of the site with affine underlying scheme is separated.

## References

* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u})

/-- **A stack equivalent to the stack represented by a separated object of the site is separated
over the base.** If the algebraic stack `𝒵` over `S₀` is equivalent over the site to the stack
represented by an object `T` of the site whose structure morphism to the base object is a
separated morphism of schemes, then `𝒵` is separated over `S₀`: its structure morphism is, read on
representing algebraic spaces, the Yoneda image of that structure morphism (Stacks 04YS). -/
theorem isSeparatedOver_of_equivalenceOver_yoneda {S₀ : Scheme.{u}} (h₀ : B.Contains S₀)
    (𝒵 : AlgebraicStacks.{u, w} B S₀ h₀) (T : BigFppfOver B S₀ h₀)
    (hT : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S₀ h₀).map
      ((Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj h₀)))).from T)))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
      (presheafOfCategories (yoneda.obj T ⋙ typeToCat)).p) :
    IsSeparatedOver.{u, w} B S₀ h₀ 𝒵 := by
  refine (AlgebraicStacks.isSeparated_iff_isSeparated_representingMap B S₀ h₀ (yoneda.obj T)
    (yoneda.obj (Over.mk (𝟙 (B.obj h₀)))) e (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (structureMorphism.{u, w} B S₀ h₀ 𝒵) (isAlgebraicSpace_yoneda B S₀ h₀ T)
    (isAlgebraicSpace_yoneda B S₀ h₀ (Over.mk (𝟙 (B.obj h₀))))).2 ?_
  have hk : representingMap B S₀ h₀ 𝒵.val
      (schemeStack.{u, w} B S₀ h₀ (Over.mk (𝟙 (B.obj h₀)))).val
      (yoneda.obj T) (yoneda.obj (Over.mk (𝟙 (B.obj h₀))))
      e (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (structureMorphism.{u, w} B S₀ h₀ 𝒵).hom =
      yoneda.map (Over.mkIdTerminal.from T) :=
    (Over.mkIdTerminal.isTerminalObj yoneda _).hom_ext _ _
  rw [hk]
  exact (Space.isSeparated_yoneda_map_iff B S₀ h₀ (Over.mkIdTerminal.from T)).2 hT

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- **The algebraic stack of an affine scheme is separated**, in the absolute sense of
Stacks 050D part (7). Its view over the terminal scheme is equivalent over the terminal scheme to
the stack represented by the same affine scheme there
(`AlgebraicGeometry.Stack.factorSliceInverse`), and a morphism of schemes out of an affine scheme
is separated. -/
theorem isAbsolutelySeparated_schemeStack_of_isAffine (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ (schemeStack.{u, w} B S hS T) := by
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (schemeFibredCategory B (⊤_ Scheme.{u}) hZ ((Over.map g).obj T)).isFiberedInGroupoids
    (changeBaseFiberedInGroupoids B S (⊤_ Scheme.{u}) hS hZ g
      (schemeFibredCategory B S hS T)).isFiberedInGroupoids
    (factorSliceInverse B S (⊤_ Scheme.{u}) hS hZ g T).toFunctor
    (factorSliceInverse B S (⊤_ Scheme.{u}) hS hZ g T).w
    (isEquivalence_factorSliceInverse B S (⊤_ Scheme.{u}) hS hZ g T)
  have : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj ((Over.map g).obj T)) := hT
  exact isSeparatedOver_of_equivalenceOver_yoneda.{u, w} B hZ
    (AlgebraicStacks.viewOverIntegers.{u, w} B S hS hZ (schemeStack.{u, w} B S hS T))
    ((Over.map g).obj T) inferInstance
    (k.symm.trans (PresheafOfCategories.sliceElementsEquivalenceOver _))

end AlgebraicGeometry.Stack

end
