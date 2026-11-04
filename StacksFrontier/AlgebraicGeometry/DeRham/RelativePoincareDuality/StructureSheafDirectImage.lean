module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.ProperSmoothBottomDifferential
public import
  StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.ProperSmoothStructureSheafDerivedImage

/-!
# The direct image of the structure sheaf in the relative duality situation

In the situation of relative Poincaré duality ([Stacks, Tag 0G8G]), with `f : X ⟶ S` proper and
smooth:

1. the pushforward `f_*𝒪_X` is a finite étale `𝒪_S`-algebra;
2. locally on `S`, `Rf_*𝒪_X ≅ f_*𝒪_X ⊕ P` in `D(𝒪_S)` with `P` perfect of Tor amplitude in
   `[1, ∞)`;
3. the map `d : f_*𝒪_X ⟶ f_*Ω_{X/S}` is zero.

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.structureSheafDirectImage`: the three statements.

## Implementation notes

A quasi-coherent `𝒪_S`-algebra is finite étale when the structure morphism of its relative
spectrum is finite and étale; this is how clause 1 is stated. In clause 2 the decomposition is
stated after restriction to an open neighbourhood `U` of each point of `S`, in `D(𝒪_U)`; the
derived category is taken at the standard model, the scope `Stacks.StandardDerivedModel`. Clause 3
says that the morphism `f_*d` vanishes, that is, that the degree-zero differential of the relative
de Rham complex `AlgebraicGeometry.Scheme.Hom.deRhamComplex` is zero on sections over `f⁻¹V` for
every open `V` of `S`.

The three clauses are `AlgebraicGeometry.isFinite_and_etale_relativeSpecToBase_pushforwardAlgebra`,
`AlgebraicGeometry.exists_nhds_derivedPushforward_unit_iso_biprod` and
`AlgebraicGeometry.deRhamComplex_d_zero_app_preimage_eq_zero`, which hold for every proper smooth
morphism.

## References

* [Stacks Project, Tag 0G8H](https://stacks.math.columbia.edu/tag/0G8H)
* [Stacks Project, Tag 0G8G](https://stacks.math.columbia.edu/tag/0G8G)
* [Stacks Project, Tag 0G7Y](https://stacks.math.columbia.edu/tag/0G7Y)
-/

@[expose] public section

open scoped Stacks.StandardDerivedModel

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

/-- In the relative duality situation `f : X ⟶ S`:

1. `f_*𝒪_X` is a finite étale `𝒪_S`-algebra: the structure morphism of its relative spectrum
   is finite and étale;
2. locally on `S`, `Rf_*𝒪_X ≅ f_*𝒪_X ⊕ P` in `D(𝒪_S)` with `P` perfect of Tor amplitude in
   `[1, ∞)`: every point of `S` has an open neighbourhood `U` over which this holds in `D(𝒪_U)`;
3. the map `d : f_*𝒪_X ⟶ f_*Ω_{X/S}` is zero: the degree-zero de Rham differential vanishes on
   sections over `f⁻¹V` for every open `V` of `S`. -/
@[stacks 0G8H "the three assertions: (1) f_*O_X is a finite étale O_S-algebra (its relative \
Spec is finite étale over S); (2) locally on S, Rf_*O_X = f_*O_X ⊕ P in D(O_S) with P perfect \
of tor amplitude in [1, ∞); (3) d : f_*O_X → f_*Ω_{X/S} is zero"]
theorem structureSheafDirectImage (D : RelativeDualitySituation.{u}) :
    (letI := isQuasicoherent_pushforwardAlgebra_of_quasiCompact D.f;
      IsFinite (relativeSpecToBase (pushforwardAlgebra D.f)) ∧
        Etale (relativeSpecToBase (pushforwardAlgebra D.f))) ∧
    (∀ s : D.S, ∃ (U : D.S.Opens) (_ : s ∈ U)
      (P : DerivedCategory (StrictlyPerfect.OXMod.{u, u}
        (D.S.toRingedSpace.restrict U.isOpenEmbedding))),
      Stacks.Cohomology.PerfectComplexes.IsPerfect P ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitudeGE
        (D.S.toRingedSpace.restrict U.isOpenEmbedding) P 1 ∧
      Nonempty ((RingedSpace.derivedRestrictModules D.S.toRingedSpace U).obj
          ((derivedPushforward D.f.toLRSHom.toShHom).obj
            (structureSheafDegreeZeroObj D.X)) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((RingedSpace.restrictModules D.S.toRingedSpace U).obj
            ((Scheme.Modules.pushforward D.f).obj (Scheme.unitModule D.X))) ⊞ P)) ∧
    (∀ V : D.S.Opens, ((Scheme.Hom.deRhamComplex D.f).d 0 1).val.app (op (D.f ⁻¹ᵁ V)) = 0) :=
  ⟨isFinite_and_etale_relativeSpecToBase_pushforwardAlgebra D.f,
    exists_nhds_derivedPushforward_unit_iso_biprod D.f,
    fun V => deRhamComplex_d_zero_app_preimage_eq_zero D.f V (Scheme.Hom.deRhamAlgebras D.f)
      (SheafOfModules.deRhamDifferential _)⟩

end AlgebraicGeometry.RelativeDualitySituation

end
