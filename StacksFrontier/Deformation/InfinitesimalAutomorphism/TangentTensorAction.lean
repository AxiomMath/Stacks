module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentVectorSpace
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TensorAction

/-!
# The acting group of Stacks 06JY, in its two descriptions

Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ` satisfying (RS), let `x' ⟶ x` be a
morphism lying over a surjection `A' → A` whose kernel `I` is annihilated by the maximal
ideal of `A'`, and let `x₀` be a pushforward of `x` to the special fibre. Tag 06JY asserts
that `Inf(x'/x)` carries a free and transitive action by
`T_{id_{x₀}} Aut(x') ⊗_k I = Inf_{x₀}(𝓕) ⊗_k I`.

The equality of the two descriptions of the acting group is what this file proves: the
`k`-vector space `T_{id_{x₀}} Aut(x')` is linearly isomorphic to `T_{id_{x₀}} Aut(x₀)` by
Tag 06JV (2), and the latter is the group `Inf_{x₀}(𝓕)` of infinitesimal automorphisms of the
dual-number pushforward of `x₀`, by the pinning equivalence of Tag 06JV (1). Tensoring both
with `I` therefore gives the same space, so the two spellings in the source statement agree.

The canonical action itself is `Deformation.tangentTensorAction` of
`StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentTensorSplit`, free and transitive by
`Deformation.tangentTensorAction_bijective`, with no hypothesis beyond those of the source.

## Main results

* `Deformation.exists_localizedTangentEquiv_infinitesimalAutomorphismKernel`:
  **Stacks 06JY**, the equality of the two descriptions of the acting group,
  `T_{id_{x₀}} Aut(x') = Inf_{x₀}(𝓕)` as `k`-vector spaces.

## Implementation notes

`Inf_{y₀}(𝓕)` is spelled as `Deformation.infinitesimalAutomorphismKernel Q` at the canonical
reduction `Deformation.tangentReduction`, that is, as the automorphisms of the dual-number
pushforward of `y₀` under its own base that die on reduction to the special fibre. That is the
spelling Tag 06JV uses, and the one its tag clause for Tag 06JX already calls `Inf_{x_0}(F)`.
The other spelling in the development, `Deformation.infinitesimalAutomorphisms` of Tag 06JQ,
takes an arbitrary canonical dual-number pair in `𝒞_Λ` rather than the canonical one under the
base; no bridge between the two spellings is used here.

The chosen-pushforward data `ChosenPushforwardsAt p y` is not an extra mathematical
hypothesis: it is the bookkeeping with which Tag 06JT's automorphism functor, and hence its
tangent space, is defined throughout this development, and it exists for any category
cofibered in groupoids.

## References

* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06JW](https://stacks.math.columbia.edu/tag/06JW)
* [Stacks Project, Tag 06JY](https://stacks.math.columbia.edu/tag/06JY)
-/

@[expose] public section

namespace Deformation

/-! ### The two descriptions of the acting group -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- **Stacks Project, Tag 06JY.** The two descriptions of the acting group agree: for a
morphism `j : y ⟶ y₀` of a category cofibered in groupoids over `𝒞_Λ` satisfying (RS) whose
target lies over the residue field, the `k`-vector space `T_{id_{y₀}} Aut(y)` is linearly
isomorphic to `T_{id_{y₀}} Aut(y₀)`, and the latter is the group `Inf_{y₀}(𝓕)` of
infinitesimal automorphisms of the dual-number pushforward of `y₀` by an equivalence taking
addition to composition. Tensoring with the kernel therefore gives the same space either
way. -/
@[stacks 06JY "the two descriptions of the acting group"]
public theorem exists_localizedTangentEquiv_infinitesimalAutomorphismKernel
    (hrs : SatisfiesRS p) {y y₀ : F} (j : y ⟶ y₀)
    (hbase : p.obj y₀ = residueFieldObject.{u, w, w} Λ k)
    (P : ChosenPushforwardsAt p y) (Q : ChosenPushforwardsAt p y₀) :
    letI := naturalLocalizedTangentAddCommGroup P hrs
    letI := naturalLocalizedTangentModule P hrs
    letI := naturalLocalizedTangentAddCommGroup Q hrs
    letI := naturalLocalizedTangentModule Q hrs
    ∃ (_ : localizedAutomorphismFunctorTangent P ≃ₗ[k]
        localizedAutomorphismFunctorTangent Q)
      (G : localizedAutomorphismFunctorTangent Q ≃
        infinitesimalAutomorphismKernel Q (tangentReduction (p := p) (x := y₀))),
      ∀ a b, G (a + b) = G a * G b :=
  ⟨canonicalLocalizedTangentAutomorphismLinearEquiv hrs j hbase P Q,
    localizedTangentEquivKernel Q, (naturalLocalizedTangentModule_spec Q hrs).1⟩

end

end Deformation

end
