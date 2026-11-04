module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.RestrictionBaseRingLinear
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Restriction to an open subspace is linear over a base ring

Restriction of unbounded derived modules to an open subspace `U` of a scheme `X` is `A`-linear,
for a ring map `φ : A ⟶ Γ(X, 𝒪_X)`, for both derived spellings of restriction to an open: the one
built from `ExtensionByZeroModules.jStar`, and the total right derived functor of restriction.
The modules over the restricted sheaf of rings carry the corresponding `A`-linear structure.

## Main results

* `Stacks.DerivedQCoh.linearResRing`: the `A`-linear structure on the modules over
  `ExtensionByZeroModules.resRing U 𝒪_X`.
* `Stacks.DerivedQCoh.linear_of_natIso`: an `A`-linear functor stays `A`-linear along a natural
  isomorphism.
* `Stacks.DerivedQCoh.jStar_linear`: `ExtensionByZeroModules.jStar` is `A`-linear.
* `Stacks.DerivedQCoh.derivedRestriction_linear`:
  `Stacks.ExtensionByZero.derivedRestriction` is `A`-linear.
* `Stacks.DerivedQCoh.derivedRestrictionOpenSubspace_linear`: the same for
  `Stacks.Cohomology.OpenSubspace.derivedRestriction`, which is a *total right derived functor*
  of restriction rather than the functor induced on derived categories by it.

## Implementation notes

The category of `𝒪_U`-modules has two spellings, `U.toScheme.Modules` and the modules over
`ExtensionByZeroModules.resRing U X.ringCatSheaf`, which are the same type with separately
declared instances; `linearResRing` is `AlgebraicGeometry.Scheme.linearOfRingHom` on the open
subscheme, read at the second spelling, and the two sheaves of rings agree closely enough for
that to typecheck without a bridge.

The underived comparison is
`AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor`: restriction of modules to an
open of a ringed space is `ExtensionByZeroModules.jStar`, and on a scheme it is isomorphic to
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` of the open immersion. Linearity moves along
that isomorphism by `linear_of_natIso`, which needs no additivity hypothesis:
`CategoryTheory.Functor.Linear` is the single field `F.map (r • f) = r • F.map f`, and
conjugating by the components of a natural isomorphism is `A`-linear.

For `Stacks.ExtensionByZero.derivedRestriction`, which is `(jStar U 𝒪).mapDerivedCategory`, the
derived statement follows from the underived one by
`CategoryTheory.Localization.functor_linear_iff` at `CategoryTheory.DerivedCategory.Q`, as in
`Stacks.DerivedQCoh.derivedRestrict_linear`. For
`Stacks.Cohomology.OpenSubspace.derivedRestriction` the comparison is instead uniqueness of right
derived functors,
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`, composed with
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`.

## References

* [Stacks Project, Lemma 36.10.12 (Tag 08EJ)](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ExtensionByZeroModules

universe u

namespace Stacks.DerivedQCoh

attribute [local instance 10000] HasDerivedCategory.standard

/-- **An `A`-linear functor stays `A`-linear along a natural isomorphism.** -/
theorem linear_of_natIso {A : Type*} [Semiring A] {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [Linear A C] [Linear A D] {F G : C ⥤ D} (e : F ≅ G)
    (hF : F.Linear A) : G.Linear A := by
  let := hF
  have h : ∀ {M N : C} (u : M ⟶ N), e.inv.app M ≫ F.map u ≫ e.hom.app N = G.map u := by
    intro M N u
    rw [e.hom.naturality u, ← Category.assoc, e.inv_hom_id_app, Category.id_comp]
  refine ⟨fun {M N} g r => ?_⟩
  rw [← h (r • g), ← h g, F.map_smul, Linear.smul_comp, Linear.comp_smul]

variable {A : Type u} [CommRing A]

/-- **Sheaves of modules over `𝒪_X|_U` form an `A`-linear category**, for a ring map from `A` to
the global sections of `𝒪_X`. The scalar acts through its restriction to `U`; the structure is
`AlgebraicGeometry.Scheme.linearOfRingHom` on the open subscheme `U`, read at the spelling of
the sheaf of rings that `ExtensionByZeroModules.jStar` uses. -/
@[instance_reducible]
def linearResRing (X : Scheme.{u}) (U : X.Opens) (φ : A →+* Γ(X, ⊤)) :
    Linear A (SheafOfModules.{u} (resRing U X.ringCatSheaf)) :=
  Scheme.linearOfRingHom U.toScheme A ((U.ι.appTop).hom.comp φ)

/-- **Restriction of modules to an open subspace is `A`-linear.** -/
theorem jStar_linear (X : Scheme.{u}) (U : X.Opens) (φ : A →+* Γ(X, ⊤)) :
    letI : Linear A (SheafOfModules.{u} X.ringCatSheaf) := Scheme.linearOfRingHom X A φ
    letI : Linear A (SheafOfModules.{u} (resRing U X.ringCatSheaf)) := linearResRing X U φ
    Functor.Linear A (jStar U X.ringCatSheaf) := by
  let : Linear A (SheafOfModules.{u} X.ringCatSheaf) := Scheme.linearOfRingHom X A φ
  let : Linear A (SheafOfModules.{u} (resRing U X.ringCatSheaf)) := linearResRing X U φ
  exact linear_of_natIso
    (AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor X U).symm
    (restrictFunctor_linear U.ι φ)

/-- **Restriction of unbounded derived modules to an open subspace is `A`-linear**, for the
derived functor `Stacks.ExtensionByZero.derivedRestriction` induced by
`ExtensionByZeroModules.jStar`. -/
theorem derivedRestriction_linear (X : Scheme.{u}) (U : X.Opens) (φ : A →+* Γ(X, ⊤)) :
    letI : Linear A (SheafOfModules.{u} X.ringCatSheaf) := Scheme.linearOfRingHom X A φ
    letI : Linear A (SheafOfModules.{u} (resRing U X.ringCatSheaf)) := linearResRing X U φ
    Functor.Linear A (Stacks.ExtensionByZero.derivedRestriction X.ringCatSheaf U) := by
  let : Linear A (SheafOfModules.{u} X.ringCatSheaf) := Scheme.linearOfRingHom X A φ
  let : Linear A (SheafOfModules.{u} (resRing U X.ringCatSheaf)) := linearResRing X U φ
  let : Functor.Linear A (jStar U X.ringCatSheaf) := jStar_linear X U φ
  refine (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) A
    ((jStar U X.ringCatSheaf).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (jStar U X.ringCatSheaf).mapDerivedCategory).1 ?_
  infer_instance

/-- **The total right derived functor of restriction to an open subspace is `A`-linear.** -/
theorem derivedRestrictionOpenSubspace_linear (X : Scheme.{u}) (U : X.Opens)
    (φ : A →+* Γ(X, ⊤)) :
    letI : Linear A (SheafOfModules.{u} X.ringCatSheaf) := Scheme.linearOfRingHom X A φ
    letI : Linear A (SheafOfModules.{u} (resRing U X.ringCatSheaf)) := linearResRing X U φ
    Functor.Linear A (Stacks.Cohomology.OpenSubspace.derivedRestriction X.ringCatSheaf U) := by
  let : Linear A (SheafOfModules.{u} X.ringCatSheaf) := Scheme.linearOfRingHom X A φ
  let : Linear A (SheafOfModules.{u} (resRing U X.ringCatSheaf)) := linearResRing X U φ
  exact linear_of_natIso
    ((AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor X U).symm ≪≫
      Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
        (AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace U))
    (derivedRestrict_linear U.ι φ)

end Stacks.DerivedQCoh

end
