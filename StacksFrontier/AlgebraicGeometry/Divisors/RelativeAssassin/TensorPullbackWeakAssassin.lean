module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassin.TensorPullback

/-!
# Bourbaki's formula for schemes in the shape of the algebraic-space statement

Let `f : X ⟶ S` be a morphism of schemes, let `F` be a quasi-coherent `𝒪_X`-module flat over
`S` and let `G` be a quasi-coherent `𝒪_S`-module. Stacks 05DB computes the associated points of
`F ⊗_{𝒪_X} f^*G` as the union, over the associated points `s` of `G`, of the images in `X` of
the associated points of `F` on the scheme-theoretic fibre `X_s`. The statement for algebraic
spaces, Stacks 0CV1, writes the same set differently: as the points of the *relative* assassin
`Ass_{X/S}(F)` whose image under `f` is associated to `G`.

## Main results

* `AlgebraicGeometry.iUnion_image_fiberι_inter_preimage`: the union over a subset `A` of the
  base of the images of a family of subsets of the fibres is the union over all of the base
  intersected with `f^{-1}(A)`.
* `AlgebraicGeometry.weaklyAssociatedPoints_tensor_pullback_eq_relativeAssassin`: over a
  locally Noetherian source and base, the weakly associated points of `F ⊗_{𝒪_X} f^*G` are the
  points of the relative assassin `Ass_{X/S}(F)` lying above weakly associated points of `G`.
* `AlgebraicGeometry.relativeWeaklyAssociatedPoints_eq_relativeAssassin_of_isLocallyNoetherian`:
  over locally Noetherian fibres the relative weak assassin is the relative assassin.
* `AlgebraicGeometry.weaklyAssociatedPoints_tensor_pullback_eq_relativeWeaklyAssociatedPoints`:
  the same formula with the relative weak assassin of Stacks 05AV in place of the relative
  assassin.

## References

* [Stacks Project, Tag 05DB](https://stacks.math.columbia.edu/tag/05DB)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
* [Stacks Project, Tag 05AR](https://stacks.math.columbia.edu/tag/05AR)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CV1](https://stacks.math.columbia.edu/tag/0CV1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A point of the scheme-theoretic fibre of `f` over `s` is carried to `s` by `f`. -/
theorem apply_fiberι {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (y : f.fiber s) :
    f (f.fiberι s y) = s := by
  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
    (f.range_fiberι s).le ⟨y, rfl⟩

/-- Selecting the fibres over a subset `A` of the base is the same as intersecting with
`f^{-1}(A)`: for any family `P` of subsets of the fibres of `f`, the union of the images of `P s`
over `s ∈ A` consists of the points of the union over all of `S` whose image lies in `A`. -/
theorem iUnion_image_fiberι_inter_preimage {X S : Scheme.{u}} (f : X ⟶ S)
    (P : ∀ s : S, Set (f.fiber s)) (A : Set S) :
    (⋃ s ∈ A, f.fiberι s '' P s) =
      {x | x ∈ (⋃ s : S, f.fiberι s '' P s) ∧ f x ∈ A} := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨s, hsA, y, hy, rfl⟩
    exact ⟨⟨s, y, hy, rfl⟩, by rwa [apply_fiberι f s y]⟩
  · rintro ⟨⟨s, y, hy, rfl⟩, hA⟩
    rw [apply_fiberι f s y] at hA
    exact ⟨s, hA, y, hy, rfl⟩

/-- Let `f : X ⟶ S` be a morphism of locally Noetherian schemes, let `F` be a quasi-coherent
`𝒪_X`-module flat over `S` and let `G` be a quasi-coherent `𝒪_S`-module. Then the weakly associated
points of `F ⊗_{𝒪_X} f^*G` are exactly the points of the relative assassin `Ass_{X/S}(F)` whose
image under `f` is weakly associated to `G`. -/
theorem weaklyAssociatedPoints_tensor_pullback_eq_relativeAssassin
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : IsFlatOver f.toLRSHom.toShHom F)
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] :
    Stacks.Divisors.weaklyAssociatedPoints
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
            ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
          (((Scheme.Modules.pullback f).obj G)))) =
      {x | x ∈ Stacks.Divisors.relativeAssassin f F ∧
        f x ∈ Stacks.Divisors.weaklyAssociatedPoints G} := by
  refine Eq.trans (associatedPoints_eq_weaklyAssociatedPoints X
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
          ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
        (((Scheme.Modules.pullback f).obj G))))).symm ?_
  refine Eq.trans (associatedPoints_tensor_pullback_eq_relativeAssassin f F G hF) ?_
  refine Eq.trans ?_ (iUnion_image_fiberι_inter_preimage f
    (fun s => Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (f.fiberι s)).obj F))
    (Stacks.Divisors.weaklyAssociatedPoints G))
  rw [associatedPoints_eq_weaklyAssociatedPoints S G]

/-- Over locally Noetherian fibres the relative weak assassin of Stacks 05AV is the relative
assassin of Stacks 05AT. -/
theorem relativeWeaklyAssociatedPoints_eq_relativeAssassin_of_isLocallyNoetherian
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (hfib : ∀ s : S, IsLocallyNoetherian (f.fiber s)) :
    relativeWeaklyAssociatedPoints f F = Stacks.Divisors.relativeAssassin f F := by
  unfold relativeWeaklyAssociatedPoints Stacks.Divisors.relativeAssassin
  congr 1
  funext s
  have := hfib s
  rw [associatedPoints_eq_weaklyAssociatedPoints]

/-- Let `f : X ⟶ S` be a morphism of locally Noetherian schemes with locally Noetherian fibres, let
`F` be a quasi-coherent `𝒪_X`-module flat over `S` and let `G` be a quasi-coherent `𝒪_S`-module.
Then the weakly associated points of `F ⊗_{𝒪_X} f^*G` are exactly the points of the relative weak
assassin `WeakAss_{X/S}(F)` of Stacks 05AV whose image under `f` is weakly associated to `G`. -/
theorem weaklyAssociatedPoints_tensor_pullback_eq_relativeWeaklyAssociatedPoints
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : IsFlatOver f.toLRSHom.toShHom F)
    [IsLocallyNoetherian X] [IsLocallyNoetherian S]
    (hfib : ∀ s : S, IsLocallyNoetherian (f.fiber s)) :
    Stacks.Divisors.weaklyAssociatedPoints
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
            ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
          (((Scheme.Modules.pullback f).obj G)))) =
      {x | x ∈ relativeWeaklyAssociatedPoints f F ∧
        f x ∈ Stacks.Divisors.weaklyAssociatedPoints G} := by
  rw [relativeWeaklyAssociatedPoints_eq_relativeAssassin_of_isLocallyNoetherian f F hfib]
  exact weaklyAssociatedPoints_tensor_pullback_eq_relativeAssassin f F G hF

end AlgebraicGeometry

end
