module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Restriction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleFilteredColimitSections

/-!
# Relatively perfect objects on a quasi-compact algebraic space are bounded

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `E` be an object of
`D(𝒪_X)` which, read as an object of `D(f⁻¹𝒪_Y)`, locally has finite Tor dimension. If `X` is
quasi-compact then `E` is bounded: its cohomology sheaves vanish outside a finite interval. In
particular an object of `D(𝒪_X)` perfect relative to `Y` in the sense of Stacks 0DKN is bounded
as soon as `X` is quasi-compact. This is the half of Stacks 0DKP which does not use that the
base is a field.

## Main results

* `AlgebraicGeometry.Space.isZero_of_isZero_scalarRestriction`: restriction of scalars along
  `f⁻¹𝒪_Y ⟶ 𝒪_X` detects zero modules.
* `AlgebraicGeometry.Space.isBounded_of_locallyHasFiniteTorDimension`: an object of `D(𝒪_X)`
  locally of finite Tor dimension over `f⁻¹𝒪_Y` on a quasi-compact `X` is bounded.
* `AlgebraicGeometry.Space.isBounded_of_isPerfectRelativeTo`: an object of `D(𝒪_X)` perfect
  relative to `Y` on a quasi-compact `X` is bounded.

## Implementation notes

The structure sheaf in degree zero is a unit for the derived tensor product,
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso`, so Tor amplitude in `[a, b]` bounds the
cohomology of the object itself to `[a, b]`
(`Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_of_hasTorAmplitude`). That lemma has
free universes, so it applies on the slices of the inverse-image ringed site, a
`RingedSite.{u + 1, u, u}`.

Quasi-compactness enters through an affine étale chart `U ⟶ X` which covers the site by itself
(`AlgebraicGeometry.Space.SmallEtale.exists_affineObject_coversTop`, Stacks 03H6): `U` is a
quasi-compact object of the small étale site
(`AlgebraicGeometry.Space.isQuasiCompactObject_of_isAffine`, Stacks 090H), so the covering of `U`
supplied by locally finite Tor dimension may be cut down to finitely many members carrying one
interval (`exists_finite_covering_hasTorAmplitude_of_locallyHasFiniteTorDimension`, in the
namespace `Stacks.SheafOfModules.DerivedTensorProduct`).
Those members cover the final object of the site, and a sheaf of modules whose restrictions to
the members of such a family vanish is zero (`Stacks.SheafOfModules.isZero_of_coversTop`).
Restriction to a slice and restriction of scalars are exact, so both commute with cohomology
(`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`).

## References

* [Stacks Project, Tag 0DKP](https://stacks.math.columbia.edu/tag/0DKP)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d e

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **Restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X` detects zero modules.** -/
theorem isZero_of_isZero_scalarRestriction (M : Modules.{u, u} B S hS X.1 X.2)
    (h : IsZero ((scalarRestriction B S hS f).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  ext U x
  exact congrArg (fun g => g.val.app U x) h

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **An object locally of finite Tor dimension over `f⁻¹𝒪_Y` on a quasi-compact algebraic space
is bounded.** Let `f : X ⟶ Y` be a morphism of algebraic spaces with `X` quasi-compact, and let
`E` be an object of `D(𝒪_X)` whose restriction of scalars to `D(f⁻¹𝒪_Y)` locally has finite Tor
dimension, measured against any family `T` of derived tensor products on the slices. Then the
cohomology sheaves of `E` vanish outside a finite interval. -/
theorem isBounded_of_locallyHasFiniteTorDimension (hqc : IsQuasiCompactSpace B S hS X.1)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : LocallyHasFiniteTorDimension T ((derivedScalarRestriction B S hS f).obj E)) :
    DerivedCategoryB.IsBounded E := by
  obtain ⟨U, hUaff, hcov⟩ := SmallEtale.exists_affineObject_coversTop B S hS X.1 X.2 hqc
  obtain ⟨ι, -, V, g, a, b, hg, hamp⟩ :=
    exists_finite_covering_hasTorAmplitude_of_locallyHasFiniteTorDimension
      T _ hE U (isQuasiCompactObject_of_isAffine B S hS X.1 U hUaff)
  have hV : (inverseImageRingedSite B S hS f).J.CoversTop
      (fun p : (_ : PUnit.{u + 2}) × ι => V p.2) :=
    Stacks.Sites.coversTop_bind hcov (fun _ => g) fun _ => hg
  have key : ∀ n : ℤ, n ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj E) := by
    intro n hn
    refine isZero_of_isZero_scalarRestriction B S hS f _ ?_
    refine Stacks.SheafOfModules.isZero_of_coversTop hV _ fun p => ?_
    let : HasDerivedCategory.{e} (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
          (inverseImageRingedSite B S hS f).O).over (V p.2))) :=
      inferInstanceAs (HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over (V p.2))))
    exact ((isZero_homology_of_hasTorAmplitude (T (V p.2)) _ (hamp p.2) hn).of_iso
        ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
              (inverseImageRingedSite B S hS f).O) (V p.2)) n).app _).symm).of_iso
      ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
          (inverseImageRingedSite B S hS f).O) (V p.2)).mapIso
        ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
          (scalarRestriction B S hS f) n).app E)).symm
  refine ⟨⟨a, fun n hn => key n ?_⟩, ⟨b, fun n hn => key n ?_⟩⟩ <;>
    simp only [Set.mem_Icc] <;> omega

/-- **An object perfect relative to `Y` on a quasi-compact algebraic space is bounded.** Let
`f : X ⟶ Y` be a flat morphism of algebraic spaces, locally of finite presentation, with `X`
quasi-compact. Then every `Y`-perfect object of `D(𝒪_X)` (Stacks 0DKN) is bounded. -/
theorem isBounded_of_isPerfectRelativeTo (hqc : IsQuasiCompactSpace B S hS X.1)
    (hflat : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : IsPerfectRelativeTo B S hS f hflat hlfp T E) :
    DerivedCategoryB.IsBounded E :=
  isBounded_of_locallyHasFiniteTorDimension B S hS f hqc T E hE.2

end AlgebraicGeometry.Space

end
