module

public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# Tensoring a distinguished triangle whose third vertex is acyclic in two degrees

Let `(X, 𝒪_X)` be a ringed space, let `E` be an object of `D(𝒪_X)` and let `T` be a
distinguished triangle in `D(𝒪_X)`. If `E ⊗^𝐋_{𝒪_X} T_3` has vanishing cohomology in degrees
`n - 1` and `n`, then `E ⊗^𝐋_{𝒪_X} T_1 ⟶ E ⊗^𝐋_{𝒪_X} T_2` is an isomorphism on `H^n`: the
image triangle is distinguished because tensoring with a fixed object is exact and commutes
with the shift, and the long exact sequence then makes that map both injective and surjective
in degree `n`.

## Main results

* `Stacks.AlgebraicGeometry.PerfectCohomology.isIso_homologyMap_derivedTensor_mor₁`: the
  statement above, for the derived tensor product of [Stacks, Tag 06YU] on a ringed space.

## Implementation notes

The shift compatibility and the exactness of `- ⊗^𝐋_{𝒪_X} E` are the `commShift_right` and
`exact_right` fields of the derived tensor product datum of [Stacks, Tag 06YU]. They are
registered as instances, but `Stacks.Cohomology.TorAmplitude.derTensor` is a definition rather
than an abbreviation, so instance search — which unfolds only reducible definitions — does not
see the projection `_.tensor` through it and does not find them. They are therefore passed as
explicit arguments to the abstract step below, whose own category is a variable and whose
triangulated instances are consequently the generic ones.

The statement is in a module of its own, on the imports of `derTensor` alone, because this is
the one step whose instances have to be found rather than matched against an argument.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u d

namespace Stacks.AlgebraicGeometry.PerfectCohomology

/-- **An exact endofunctor of `D(A)` is invertible on `H^n` of the first map of a distinguished
triangle whose third vertex is acyclic in degrees `n - 1` and `n`.** The shift compatibility and
the exactness are explicit arguments: the functor this is used at is a field of a structure, and
instance search does not produce them for it. -/
private theorem isIso_homologyMap_map_mor₁ {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (F : DerivedCategory A ⥤ DerivedCategory A) (hcs : F.CommShift ℤ)
    (hex : letI := hcs; F.IsTriangulated) (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A)) (n : ℤ)
    (hz : IsZero ((DerivedCategory.homologyFunctor A n).obj (F.obj T.obj₃)))
    (hz' : IsZero ((DerivedCategory.homologyFunctor A (n - 1)).obj (F.obj T.obj₃))) :
    IsIso ((DerivedCategory.homologyFunctor A n).map (F.map T.mor₁)) := by
  let := hcs
  let := hex
  have hTd := F.map_distinguished T hT
  have hepi : Epi ((DerivedCategory.homologyFunctor A n).map (F.mapTriangle.obj T).mor₁) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hTd n]
    exact hz.eq_of_tgt _ _
  have hmono : Mono ((DerivedCategory.homologyFunctor A n).map (F.mapTriangle.obj T).mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hTd (n - 1) n (by omega)]
    exact hz'.eq_of_src _ _
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor A n).map
    (F.mapTriangle.obj T).mor₁)

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]

/-- `HasDerivedCategory` at the spelling of the category of `𝒪_X`-modules that the derived
tensor product of [Stacks, Tag 06YU] is stated at. The type is `StrictlyPerfect.OXMod X` by
`rfl`, but an instance proved at one spelling is not found at the other. -/
local instance hasDerivedCategoryModules :
    HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) :=
  inferInstanceAs (HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X))

/-- **Tensoring with a fixed object of `D(𝒪_X)` turns a triangle whose third vertex becomes
acyclic in degrees `n - 1` and `n` into one whose first map is invertible on `H^n`.** -/
theorem isIso_homologyMap_derivedTensor_mor₁
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X))
    (T : Triangle (DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)))
    (hT : T ∈ distTriang (DerivedCategory (StrictlyPerfect.OXMod.{u, u} X))) (n : ℤ)
    (hz : IsZero ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X) n).obj
      (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.obj E).obj T.obj₃)))
    (hz' : IsZero ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X) (n - 1)).obj
      (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.obj E).obj T.obj₃))) :
    IsIso ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X) n).map
      (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.obj E).map T.mor₁)) :=
  isIso_homologyMap_map_mor₁ ((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.obj E)
    ((Stacks.Cohomology.TorAmplitude.derTensor X).commShift_right E)
    ((Stacks.Cohomology.TorAmplitude.derTensor X).exact_right E) T hT n hz hz'

end Stacks.AlgebraicGeometry.PerfectCohomology

end
