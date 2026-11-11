module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyCartesian
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# The object of `Spaces'_{fp, flat, proper}` given by a proper flat scheme over a field

Let `k` be a field with `Spec k` in a big fppf site `B`, and let `f : X ⟶ Spec k` be a flat,
proper morphism of finite presentation. Then `X` belongs to the site (it is of finite type over
`Spec k`), and `X`, viewed as an algebraic space over `Spec k`, is an object of the stack
`Spaces'_{fp, flat, proper}` over the big fppf site of `Spec k` (Stacks 0D1D), lying over the
object `Spec k ⟶ Spec k`. This is the point `x₀` at which the deformation theory of the
stack is studied in the proof of Stacks 0D1R.

## Main definitions

* `AlgebraicGeometry.ProperFlatSpaceOfScheme.siteObj`: `X` as an object of the site over `Spec k`.
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.baseObj`: `Spec k` as an object over itself, in the
  form used by the deformation theory of the stack (`Deformation.Artin.algebraOver`).
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.point`: the object of `Spaces'_{fp, flat, proper}`.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceOfScheme.contains`: the site contains `X`.
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.projection_point`: the point lies over
  `Spec k ⟶ Spec k`, in the form required by the predeformation category at the point.

## References

* [Stacks Project, Tag 0D1D](https://stacks.math.columbia.edu/tag/0D1D)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProperFlatSpaceOfScheme

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

include hk in
/-- A scheme of finite type and quasi-compact over `Spec k` belongs to the big fppf site. -/
theorem contains [LocallyOfFiniteType f] [QuasiCompact f] : B.Contains X :=
  lt_of_le_of_lt (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact f) hk

/-- `X` as an object of the big fppf site over `Spec k`. -/
abbrev siteObj [LocallyOfFiniteType f] [QuasiCompact f] : BigFppfOver B (Spec (.of k)) hk :=
  Over.mk (ObjectProperty.homMk f : B.obj (contains B k hk f) ⟶ B.obj hk)

/-- `Spec k` as an object over itself, through `Spec (k → k) ≫ 𝟙`: the form in which the
deformation theory of `Spaces'_{fp, flat, proper}` presents the object of the base under its
residue field. -/
abbrev baseObj : BigFppfOver B (Spec (.of k)) hk :=
  Deformation.Artin.algebraOver k B (Spec (.of k)) hk
    (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ 𝟙 (Spec (.of k))) hk

/-- The structure morphism of `X` as a morphism of the site to `baseObj`. -/
def toBaseObj [LocallyOfFiniteType f] [QuasiCompact f] :
    siteObj B k hk f ⟶ baseObj B k hk :=
  Over.homMk (ObjectProperty.homMk f) (by
    apply ObjectProperty.hom_ext
    change f ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ 𝟙 (Spec (.of k)) = f
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id,
      Category.comp_id])

/-- The underlying morphism of schemes of `toBaseObj` is `f`. -/
@[simp]
theorem toScheme_map_toBaseObj [LocallyOfFiniteType f] [QuasiCompact f] :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (toBaseObj B k hk f) = f :=
  rfl

/-- **The object of `Spaces'_{fp, flat, proper}` given by a flat, proper morphism of finite
presentation `X ⟶ Spec k`.** -/
def point [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    CartesianProperFlatSpaces B (Spec (.of k)) hk :=
  CartesianProperFlatSpaces.mk' (baseObj B k hk) (yoneda.obj (siteObj B k hk f))
    (isAlgebraicSpace_yoneda B _ hk _) (yoneda.map (toBaseObj B k hk f))
    (Space.isFinitePresentation_yoneda_map B _ hk _ (by
      change FinitePresentation f
      exact ⟨inferInstance, inferInstance, inferInstance⟩))
    (Space.isFlat_yoneda_map B _ hk _ (by change Flat f; infer_instance))
    ((Space.isProper_yoneda_map_iff B _ hk _).2 (by change IsProper f; infer_instance))

/-- **The point lies over `Spec k`**, in the form required by the predeformation category of
`Spaces'_{fp, flat, proper}` at it (with `Λ = k` and `iΛ = 𝟙`). -/
theorem projection_point [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    (cartesianProperFlatProjection B (Spec (.of k)) hk ⋙ Over.post B.inclusion).obj
        (point B k hk f) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ 𝟙 (Spec (.of k))) :=
  rfl

/-- The total space of the point is the presheaf represented by `X`. -/
theorem total_point [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    (point B k hk f).total = yoneda.obj (siteObj B k hk f) :=
  rfl

end AlgebraicGeometry.ProperFlatSpaceOfScheme

end
