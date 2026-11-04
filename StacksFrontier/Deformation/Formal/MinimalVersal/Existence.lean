module

public import StacksFrontier.Deformation.Formal.MinimalVersal.FurtherDescent

/-!
# The smallest base of a versal formal object

A versal formal object in a category cofibered in groupoids satisfying (S1) descends to a formal
object over a complete local subalgebra of its base. After every Artinian base change the descent
over the image subalgebra is minimal, and the descended formal object admits no proper further
descent.

## Main definitions

* `Deformation.smallestDescent`: a chosen smallest descent of a versal formal object.

## Main results

* `Deformation.exists_smallestDescent`: **Stacks Project, Tag 06T2.** A versal formal object
  admits a smallest formal descent.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- **Stacks Project, Tag 06T2.** A versal formal object of a category cofibered in groupoids
satisfying (S1) admits a smallest formal descent: a descent over a complete local subalgebra of
its base that stays minimal after every Artinian base change and admits no proper further
descent. -/
@[stacks 06T2]
public theorem exists_smallestDescent
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (hξ : IsVersal hp ξ) :
    Nonempty (SmallestDescent ξ) := by
  let hbound := stageBaseTower_cotangent_bounded_of_versal hp hS1 ξ hξ
  exact ⟨⟨stageBaseTowerFormalObject hp hS1 ξ hbound,
    stageBaseTowerFormalObjectHom hp hS1 ξ hbound,
    stageBaseTowerBaseHom_injective hp hS1 ξ hbound,
    isMinimalObject_of_stageBaseTowerFormalObject hp hS1 ξ hbound,
    surjective_base_of_hom_to_stageBaseTowerFormalObject hp hS1 ξ hbound⟩⟩

/-- A chosen smallest descent of a versal formal object, with its specification carried
by the fields of `SmallestDescent`. -/
public noncomputable def smallestDescent
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (hξ : IsVersal hp ξ) :
    SmallestDescent ξ :=
  Classical.choice (exists_smallestDescent hp hS1 ξ hξ)

end Deformation

end
