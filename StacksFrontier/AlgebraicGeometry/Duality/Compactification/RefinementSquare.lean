module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.PreservesInterior

/-!
# The cartesian square of an interior-preserving refinement

Let `X` be a scheme over `S` and let `g : j ⟶ k` be a morphism of compactifications of `X` over
`S`, with underlying morphism of ambient schemes `G = CompactificationOf.Hom.map g`.  Then

```
X --j.immersion--> j.space
|𝟙                  |G
X --k.immersion--> k.space
```

commutes, and it is **cartesian exactly when `g` preserves the interior**: the square is cartesian
iff `G⁻¹(k(X)) = j(X)`, which is
`AlgebraicGeometry.CompactificationOf.PreservesInterior` by definition.

## Main results

All in the namespace `AlgebraicGeometry.CompactificationOf`.

* `immersion_comp_homMap` and `homMap_comp_toBase` — the two commutativities carried by a
  morphism of compactifications.
* `homMap_comp` and `homMap_id` — the underlying morphism of ambient schemes is functorial.
* `isPullback_of_preservesInterior` — the square above is cartesian.
* `isProper_homMap` — a morphism of compactifications is proper.
* `preservesInterior_id` and `preservesInterior_comp` — the interior-preserving morphisms contain
  the identities and are closed under composition.

## References

* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {S : Scheme.{u}} {X : Over S}

/-- A morphism of compactifications commutes with the open immersions: `j(X) ⊆ j.space` is
carried into `k(X) ⊆ k.space`. -/
theorem immersion_comp_homMap {j k : CompactificationOf X} (g : j ⟶ k) :
    j.immersion ≫ Hom.map g = k.immersion := by
  simpa [Hom.map] using congrArg (Over.forget S).map g.hom.w

/-- A morphism of compactifications commutes with the structure morphisms to the base. -/
theorem homMap_comp_toBase {j k : CompactificationOf X} (g : j ⟶ k) :
    Hom.map g ≫ k.toBase = j.toBase := by
  simp [Hom.map, CompactificationOf.toBase]

/-- The underlying morphism of ambient schemes of the identity of a compactification is the
identity of its ambient scheme. -/
@[simp]
theorem homMap_id (j : CompactificationOf X) : Hom.map (𝟙 j) = 𝟙 j.space := rfl

/-- The underlying morphism of ambient schemes of a composite of morphisms of compactifications is
the composite of the underlying morphisms. -/
@[simp]
theorem homMap_comp {j k l : CompactificationOf X} (g : j ⟶ k) (h : k ⟶ l) :
    Hom.map (g ≫ h) = Hom.map g ≫ Hom.map h := rfl

/-- **A morphism of compactifications is proper.**  It is proper over the base, because the
structure morphism of its source is, and the structure morphism of its target is separated. -/
theorem isProper_homMap {j k : CompactificationOf X} (g : j ⟶ k) : IsProper (Hom.map g) := by
  have : IsProper (Hom.map g ≫ k.toBase) := by rw [homMap_comp_toBase]; infer_instance
  exact IsProper.of_comp _ k.toBase

/-- **The square of an interior-preserving morphism of compactifications is cartesian.**  The two
horizontal edges are the open immersions of the two compactifications and the left vertical edge
is the identity of `X`; cartesianness of such a square is exactly the statement that the inverse
image under `G` of the interior of `k` is the interior of `j`, which is
`AlgebraicGeometry.CompactificationOf.PreservesInterior`. -/
theorem isPullback_of_preservesInterior {j k : CompactificationOf X} (g : j ⟶ k)
    (hg : PreservesInterior g) :
    IsPullback (𝟙 X.left) j.immersion k.immersion (Hom.map g) := by
  refine IsOpenImmersion.isPullback (𝟙 X.left) j.immersion k.immersion (Hom.map g)
    (by simpa using immersion_comp_homMap g) ?_
  apply TopologicalSpace.Opens.ext
  simpa [Scheme.Hom.opensRange, PreservesInterior] using hg

/-- The identity of a compactification preserves the interior. -/
theorem preservesInterior_id (j : CompactificationOf X) : PreservesInterior (𝟙 j) := by
  simp [PreservesInterior]

/-- Interior-preserving morphisms of compactifications are closed under composition. -/
theorem preservesInterior_comp {j k l : CompactificationOf X} {g : j ⟶ k} {h : k ⟶ l}
    (hg : PreservesInterior g) (hh : PreservesInterior h) : PreservesInterior (g ≫ h) := by
  rw [PreservesInterior, homMap_comp] at *
  rw [← hg, ← hh, ← Set.preimage_comp]
  rfl

end AlgebraicGeometry.CompactificationOf

end
