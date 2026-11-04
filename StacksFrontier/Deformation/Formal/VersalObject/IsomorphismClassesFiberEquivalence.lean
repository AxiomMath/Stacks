module

public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClasses

/-!
# Isomorphism classes under a based functor that is an equivalence on a fibre

`Deformation.mapIsomorphismClasses_bijective_of_isIsomorphismClasses` makes the induced map on
isomorphism classes bijective for a based functor realizing the functor of isomorphism classes,
whose fibres are skeletal. The other sufficient condition is recorded here: a based functor
whose comparison on the fibre over `A` is full, faithful and essentially surjective is also
bijective on isomorphism classes over `A`, injectivity now coming from the fact that a fully
faithful functor reflects isomorphy rather than from skeletality.

The three conditions are hypotheses on the fibre and not consequences of the based functor
being an equivalence. The fibre `Functor.Fiber p A` is cut out by the *equality*
`p.obj x = A`, so an equivalence over the base carries an object of one fibre only to an object
lying over a base object *isomorphic* to `A`; fullness and faithfulness on fibres do follow
from fullness and faithfulness of the comparison, but essential surjectivity does not, and a
consumer has to supply it from the structure at hand.

## Main results

* `Deformation.bijective_mapIsomorphismClasses_of_fiberEquivalence`: a based functor that is an
  equivalence on the fibre over `A` is bijective on isomorphism classes over `A`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Deformation

universe u v u₁ v₁ u₂ v₂

section

variable {C : Type u} [Category.{v} C]

/-- **A based functor that is an equivalence on the fibre over `A` is bijective on isomorphism
classes over `A`.** Injectivity is that a fully faithful functor reflects isomorphy, so two
objects of the fibre upstairs whose images are isomorphic there are themselves isomorphic;
surjectivity is essential surjectivity on the fibre. -/
public theorem bijective_mapIsomorphismClasses_of_fiberEquivalence
    {𝓐 : BasedCategory.{v₁, u₁} C} {𝓑 : BasedCategory.{v₂, u₂} C}
    (h𝓐 : IsCofiberedInGroupoids 𝓐.p) (h𝓑 : IsCofiberedInGroupoids 𝓑.p)
    (φ : BasedFunctor 𝓐 𝓑) (A : C)
    (hfull : (fiberFunctor φ A).Full) (hfaithful : (fiberFunctor φ A).Faithful)
    (hess : (fiberFunctor φ A).EssSurj) :
    Function.Bijective (mapIsomorphismClasses h𝓐 h𝓑 φ A) := by
  constructor
  · intro x y hxy
    obtain ⟨x₀, rfl⟩ := classOf_surjective 𝓐 h𝓐 A x
    obtain ⟨y₀, rfl⟩ := classOf_surjective 𝓐 h𝓐 A y
    have hxy' : classOf 𝓑 h𝓑 ((fiberFunctor φ A).obj x₀) =
        classOf 𝓑 h𝓑 ((fiberFunctor φ A).obj y₀) := by
      simpa only [mapIsomorphismClasses_classOf] using hxy
    have hq : Quotient.mk (isIsomorphicSetoid (Fiber 𝓑.p A))
          ((fiberFunctor φ A).obj x₀) =
        Quotient.mk (isIsomorphicSetoid (Fiber 𝓑.p A))
          ((fiberFunctor φ A).obj y₀) := by
      simpa only [classOf_eq] using
        congrArg (cast (isomorphismClasses_obj 𝓑 h𝓑 A)) hxy'
    obtain ⟨e⟩ := Quotient.exact hq
    exact classOf_eq_of_isIsomorphic 𝓐 h𝓐 x₀ y₀
      ⟨(Functor.FullyFaithful.ofFullyFaithful (fiberFunctor φ A)).preimageIso e⟩
  · intro y
    obtain ⟨z, rfl⟩ := classOf_surjective 𝓑 h𝓑 A y
    obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (fiberFunctor φ A) z
    refine ⟨classOf 𝓐 h𝓐 x, ?_⟩
    rw [mapIsomorphismClasses_classOf]
    exact classOf_eq_of_isIsomorphic 𝓑 h𝓑 _ _ ⟨e⟩

end

end Deformation

end
