module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.Topology.Maps.ClosureImageSurjectiveOpen

/-!
# Images of preimages along a 2-cartesian square of algebraic stacks

Let
```text
𝒫 --snd--> 𝒬
|           |
fst         f
|           |
𝒳 ---g---> 𝒴
```
be a 2-fibre product square of algebraic stacks over `S`. For a subset `T ⊆ |𝒳|` the image under
`|𝒫| → |𝒬|` of the preimage of `T` in `|𝒫|` is exactly the preimage under `|𝒬| → |𝒴|` of the
image of `T` in `|𝒴|`.

Consequently, if `f` is surjective and open on points and a closed subset `T' ⊆ |𝒬|` contains
`snd '' (fst ⁻¹' T)`, then for any further 1-morphism `π : 𝒴 ⟶ 𝒵` the image under `|𝒴| → |𝒵|` of
the closure of `g '' T` is contained in the image of `T'` under `|𝒬| → |𝒵|`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.image_preimage_eq_preimage_image_of_isTwoFibreProduct`:
  the equality `snd '' (fst ⁻¹' T) = f ⁻¹' (g '' T)` of subsets of `|𝒬|`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.image_closure_image_subset_of_isTwoFibreProduct`: the
  resulting bound `π '' closure (g '' T) ⊆ (f ≫ π) '' T'`.

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 0H29](https://stacks.math.columbia.edu/tag/0H29)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a 2-fibre product square of algebraic stacks over `S` with legs `fst : 𝒫 ⟶ 𝒳` and
`snd : 𝒫 ⟶ 𝒬` over a cospan `g : 𝒳 ⟶ 𝒴`, `f : 𝒬 ⟶ 𝒴`, and for any subset `T` of `|𝒳|`, the
image in `|𝒬|` of the preimage of `T` in `|𝒫|` is the preimage in `|𝒬|` of the image of `T`
in `|𝒴|`. -/
@[stacks 0H29 "the cartesian-square step of the proof, on points"]
theorem image_preimage_eq_preimage_image_of_isTwoFibreProduct
    {𝒳 𝒬 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} {g : 𝒳 ⟶ 𝒴} {f : 𝒬 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (T : Set (points B S hS 𝒳)) :
    pointsMap B S hS P.snd '' (pointsMap B S hS P.fst ⁻¹' T) =
      pointsMap B S hS f ⁻¹' (pointsMap B S hS g '' T) := by
  have hsq : pointsMap B S hS g ∘ pointsMap B S hS P.fst =
      pointsMap B S hS f ∘ pointsMap B S hS P.snd := by
    rw [← pointsMap_comp B S hS P.fst g, ← pointsMap_comp B S hS P.snd f,
      pointsMap_eq_of_hom₂ B S hS P.iso.hom]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨pointsMap B S hS P.fst p, hp, congrFun hsq p⟩
  · rintro y ⟨t, htT, hty⟩
    obtain ⟨p, hp₁, hp₂⟩ :=
      Stack.exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP t y hty
    exact ⟨p, by rwa [Set.mem_preimage, show pointsMap B S hS P.fst p = t from hp₁], hp₂⟩

/-- Let `P` be a 2-fibre product square of algebraic stacks over `S` with legs `fst : 𝒫 ⟶ 𝒳` and
`snd : 𝒫 ⟶ 𝒬` over a cospan `g : 𝒳 ⟶ 𝒴`, `f : 𝒬 ⟶ 𝒴`, with `f` surjective and open on points,
and let `π : 𝒴 ⟶ 𝒵` be a 1-morphism. If a closed subset `T' ⊆ |𝒬|` contains the image of the
preimage of `T ⊆ |𝒳|`, then the image in `|𝒵|` of the closure of the image of `T` in `|𝒴|` is
contained in the image of `T'` in `|𝒵|`. -/
@[stacks 0H29 "the descent step of the proof, along a cartesian square with surjective open legs"]
theorem image_closure_image_subset_of_isTwoFibreProduct
    {𝒳 𝒬 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} {g : 𝒳 ⟶ 𝒴} {f : 𝒬 ⟶ 𝒴} (π : 𝒴 ⟶ 𝒵)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hsurj : Function.Surjective (pointsMap B S hS f))
    (hopen : letI := Stack.pointTopology B S hS 𝒬.val
      letI := Stack.pointTopology B S hS 𝒴.val
      IsOpenMap (pointsMap B S hS f))
    (T : Set (points B S hS 𝒳)) (T' : Set (points B S hS 𝒬))
    (hT' : letI := Stack.pointTopology B S hS 𝒬.val
      IsClosed T')
    (hsub : pointsMap B S hS P.snd '' (pointsMap B S hS P.fst ⁻¹' T) ⊆ T') :
    letI := Stack.pointTopology B S hS 𝒴.val
    pointsMap B S hS π '' closure (pointsMap B S hS g '' T) ⊆
      pointsMap B S hS (f ≫ π) '' T' := by
  let _ := Stack.pointTopology B S hS 𝒬.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  rw [pointsMap_comp B S hS f π]
  exact hopen.image_closure_subset_image_of_preimage_subset
    (Stack.continuous_pointsMap B S hS 𝒬.val 𝒴.val f.hom.hom) hsurj (pointsMap B S hS π) hT'
    ((image_preimage_eq_preimage_image_of_isTwoFibreProduct B S hS P hP T).ge.trans hsub)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
