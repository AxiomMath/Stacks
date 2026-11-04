module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardBounds
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject

/-!
# The top cohomology of derived sections over an affine inverse image

Let `f : X ⟶ Y` be a morphism of schemes, let `V ⊆ Y` be an open whose inverse image `f⁻¹V` is an
affine open of `X`, and let `E` be an object of `D(𝒪_X)` whose cohomology sheaves are
quasi-coherent and which lives in degrees `≤ d`. Then the canonical comparison identifies the top
cohomology of the derived sections with the sections of the top cohomology:

> `H^d(RΓ(f⁻¹V, E)) = Γ(f⁻¹V, H^d(E))`,

both sides read as modules over `Γ(V, 𝒪_Y)` by restriction of scalars along
`f^♯ : Γ(V, 𝒪_Y) ⟶ Γ(f⁻¹V, 𝒪_X)`, which is the target
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections` and
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections` are stated in.

This is the sections-side companion of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedPullbackTopDegree.lean`, which performs
the same degeneration for the derived pullback, and it is the shape conclusion (c) of
[Stacks, Tag 0EX3] uses when it computes the degree-`d` term of a derived functor from the
degree-`d` cohomology sheaf alone.

The map is the canonical one throughout: `E ⟶ τ_{≥ d}E` is the truncation, `τ_{≥ d}E ≅ H^d(E)[-d]`
holds because `E` has no cohomology above `d`
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncGEIsoSingleHomology`), `RΓ(f⁻¹V, -)` and `H^d`
are applied to that composite, and the resulting
`H^d(RΓ(f⁻¹V, H^d(E)[-d]))` is `Γ(f⁻¹V, H^d(E))` by the comparison of a total right derived
functor with the underived one at an object placed in a single degree.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeDerivedSectionsSingleIso` —
  `H^d(RΓ(f⁻¹V, M[-d])) ≅ Γ(f⁻¹V, M)` for a single sheaf of modules `M` placed in degree `d`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeDerivedSectionsMap` — the canonical map
  `H^d(RΓ(f⁻¹V, E)) ⟶ Γ(f⁻¹V, H^d(E))` for `E` with no cohomology above `d`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeDerivedSectionsIso` — that map as an
  isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preservesFiniteLimits_preimageSections` — sections
  over the inverse image of an open, with scalars restricted, are left exact.
* `isIso_homologyFunctor_map_derivedPreimageSections_truncGEπ`, in the same namespace —
  `H^i(RΓ(f⁻¹V, E)) ⟶ H^i(RΓ(f⁻¹V, τ_{≥ b}E))` is invertible for `i ≥ b`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_topDegreeDerivedSectionsMap` — the canonical
  map is invertible, which is the content of the file.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeDerivedSectionsIso_hom` — the
  isomorphism's forward direction is that canonical map, so consumers may use its naturality.

## Implementation notes

*The single-degree term needs no affineness and no quasi-coherence.* `H^d(RΓ(f⁻¹V, M[-d]))` is
`Γ(f⁻¹V, M)` for every sheaf of modules `M` and every open `V`, by
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso`: a total right derived functor of a
left exact functor agrees with it on the degree in which the argument is concentrated. Left
exactness of `Γ(f⁻¹V, -)` with scalars restricted is
`preservesFiniteLimits_preimageSections` — evaluation of a sheaf of modules at an open preserves
limits, and restriction of scalars along a map of rings is exact. So the affine hypothesis enters
only through the truncation comparison.

*Where the affine hypothesis enters.* `isIso_homologyFunctor_map_derivedPreimageSections_truncGEπ`
is [Stacks, Tag 08D4] part (2) at the functor `Γ(f⁻¹V, -)` with `N = 1`, the integer `N` being `1`
because Serre vanishing ([Stacks, Tag 01XB]) kills the higher right derived functors of
`Γ(f⁻¹V, -)` on quasi-coherent modules when `f⁻¹V` is affine
(`AlgebraicGeometry.isZero_rightDerivedPlus_preimageSections_of_isAffineOpen`). With `N = 1` the
cut `b - N + 1` of the source is `b` itself, so no degree is lost.

*Three instances are supplied positionally*, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardBounds.lean`:
`isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero_rightDerivedPlus`, in the
`AlgebraicGeometry` namespace,
is stated with source category `SheafOfModules X.ringCatSheaf`, while `Γ(f⁻¹V, -)` and its derived
functor are stated with source `SheafOfModules (structureSheafRing X.toRingedSpace)`. The two are
definitionally equal, but additivity, preservation of countable products and the derived-functor
structure mention the `Preadditive` and `HasDerivedCategory` instances of the source and instance
search does not cross the two spellings, so they are handed over as explicit arguments.

*No `@[stacks 0EX3]` attribute is placed.* Tag 0EX3 asserts conclusions (a), (b) and (c) about a
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation`; what is here is the degeneration of
derived sections that the argument for (c) performs, and the covering set of the tag is discussed
in `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedPullbackTopDegree.lean`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedPreimageSections derivedPreimageSectionsUnit preimageSections sectionsOverOpen)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance]
  Stacks.Cohomology.UnboundedHigherDirectImage.isGrothendieckAbelian_moduleSheaves

/-! ### Left exactness of sections over an inverse image -/

/-- **Sections over the inverse image of an open are left exact.** Evaluation of a sheaf of
modules at an open preserves all limits, and restriction of scalars along a map of rings is exact,
so the composite `Γ(f⁻¹V, -)` with its scalars restricted along `f^♯` preserves finite limits.

This is the hypothesis under which a total right derived functor agrees with the underived functor
on an object placed in a single degree. -/
public instance preservesFiniteLimits_preimageSections {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) : PreservesFiniteLimits (preimageSections f V) := by
  have h₁ : PreservesFiniteLimits (sectionsOverOpen X ((opensMap f).obj V)) :=
    ⟨fun _ _ _ ↦ SheafOfModules.evaluationPreservesLimitsOfShape _ _ _⟩
  have h₂ : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{u} ((structureSheafHom f).hom.app (op V)).hom) :=
    ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂

variable {X Y : Scheme.{u}}

/-! ### The single-degree term -/

/-- **`H^d(RΓ(f⁻¹V, M[-d])) = Γ(f⁻¹V, M)`.** For a sheaf of `𝒪_X`-modules `M` placed in degree
`d`, the degree-`d` cohomology of the derived sections over `f⁻¹V` is the ordinary module of
sections of `M` over `f⁻¹V`, with scalars restricted along `f^♯`.

No hypothesis on `M`, on `V` or on `f` is needed: this is
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso` at the left exact functor
`Γ(f⁻¹V, -)`, whose left exactness is `preservesFiniteLimits_preimageSections`. -/
public def topDegreeDerivedSectionsSingleIso (f : X ⟶ Y) (V : Y.Opens)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (d : ℤ) :
    (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) d).obj M)) ≅
      (preimageSections f.toLRSHom.toShHom V).obj M :=
  Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso
    (preimageSections f.toLRSHom.toShHom V)
    (derivedPreimageSections f.toLRSHom.toShHom V)
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective _) M d

/-! ### The truncation comparison over an affine inverse image -/

/-- **[Stacks, Tag 08D4] part (2) at the functor `Γ(f⁻¹V, -)`, with `N = 1`.** Let `V ⊆ Y` be an
open whose inverse image is an affine open of `X` and let `E` be an object of `D(𝒪_X)` with
quasi-coherent cohomology sheaves. Then the canonical comparison
`H^i(RΓ(f⁻¹V, E)) ⟶ H^i(RΓ(f⁻¹V, τ_{≥ b}E))` is an isomorphism for every `i ≥ b`.

The source's cut sits at `b - N + 1`; here `N = 1`, because Serre vanishing
([Stacks, Tag 01XB]) kills the higher right derived functors of `Γ(f⁻¹V, -)` on quasi-coherent
modules over an affine open
(`AlgebraicGeometry.isZero_rightDerivedPlus_preimageSections_of_isAffineOpen`), so the cut is `b`
itself and no degree is lost. Sections over an inverse image preserve countable products, which is
the other hypothesis of the source. -/
public theorem isIso_homologyFunctor_map_derivedPreimageSections_truncGEπ (f : X ⟶ Y)
    (V : Y.Opens) (hV : IsAffineOpen (f ⁻¹ᵁ V))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) i).map
      ((derivedPreimageSections f.toLRSHom.toShHom V).map
        ((DerivedCategory.TStructure.t.truncGEπ b).app E))) := by
  have hirdf : (derivedPreimageSections f.toLRSHom.toShHom V).IsRightDerivedFunctor
      (derivedPreimageSectionsUnit f.toLRSHom.toShHom V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) := inferInstance
  have h := @isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero_rightDerivedPlus
    X _ _ _ _ _ _ (preimageSections f.toLRSHom.toShHom V)
    (Stacks.Cohomology.DerivedSectionsLeray.preimageSections_additive _ _)
    (preservesLimitsOfShape_discrete_nat_preimageSections f V)
    (derivedPreimageSections f.toLRSHom.toShHom V)
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V) hirdf 1
    (fun M hM p hp ↦ isZero_rightDerivedPlus_preimageSections_of_isAffineOpen f V hV M hM p
      (by exact_mod_cast hp)) E hcoh b i hi
  have hb : b - ((1 : ℕ) : ℤ) + 1 = b := by omega
  rw [hb] at h
  exact h

/-! ### The degeneration -/

/-- **The canonical map `H^d(RΓ(f⁻¹V, E)) ⟶ Γ(f⁻¹V, H^d(E))`.** For `E` with no cohomology above
`d`, apply `RΓ(f⁻¹V, -)` and then `H^d` to the composite of the truncation `E ⟶ τ_{≥ d}E` with the
identification `τ_{≥ d}E ≅ H^d(E)[-d]` of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncGEIsoSingleHomology`, and follow it by
`topDegreeDerivedSectionsSingleIso`. -/
public def topDegreeDerivedSectionsMap (f : X ⟶ Y) (V : Y.Opens) (d : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : E.IsLE d) :
    (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj E) ⟶
      (preimageSections f.toLRSHom.toShHom V).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) d).obj E) :=
  (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).map
      ((derivedPreimageSections f.toLRSHom.toShHom V).map
        ((DerivedCategory.TStructure.t.truncGEπ d).app E ≫
          (truncGEIsoSingleHomology E d hE).hom)) ≫
    (topDegreeDerivedSectionsSingleIso f V _ d).hom

/-- **The engine conclusion (c) of [Stacks, Tag 0EX3] needs on the sections side.** Let `f : X ⟶ Y`
be a morphism of schemes, let `V ⊆ Y` be an open whose inverse image is an affine open of `X`, and
let `E` be an object of `D(𝒪_X)` with quasi-coherent cohomology sheaves and no cohomology above
`d`. Then the canonical map `H^d(RΓ(f⁻¹V, E)) ⟶ Γ(f⁻¹V, H^d(E))` is an isomorphism.

Its first factor is invertible by
`isIso_homologyFunctor_map_derivedPreimageSections_truncGEπ` at `i = b = d`, its second is a
functor applied to an isomorphism, and its third is
`topDegreeDerivedSectionsSingleIso`. -/
public theorem isIso_topDegreeDerivedSectionsMap (f : X ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen (f ⁻¹ᵁ V)) (d : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (hE : E.IsLE d) : IsIso (topDegreeDerivedSectionsMap f V d E hE) := by
  have h₁ := isIso_homologyFunctor_map_derivedPreimageSections_truncGEπ f V hV E hcoh d d le_rfl
  have h₂ : IsIso ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).map
      ((derivedPreimageSections f.toLRSHom.toShHom V).map
        (truncGEIsoSingleHomology E d hE).hom)) :=
    ((derivedPreimageSections f.toLRSHom.toShHom V ⋙ DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).mapIso
        (truncGEIsoSingleHomology E d hE)).isIso_hom
  rw [topDegreeDerivedSectionsMap, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **`H^d(RΓ(f⁻¹V, E)) ≅ Γ(f⁻¹V, H^d(E))`**, the canonical map `topDegreeDerivedSectionsMap`
made an isomorphism. -/
public def topDegreeDerivedSectionsIso (f : X ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen (f ⁻¹ᵁ V))
    (d : ℤ) (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (hE : E.IsLE d) :
    (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj E) ≅
      (preimageSections f.toLRSHom.toShHom V).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) d).obj E) :=
  @asIso _ _ _ _ _ (isIso_topDegreeDerivedSectionsMap f V hV d E hcoh hE)

/-- The forward direction of `topDegreeDerivedSectionsIso` is the canonical map
`topDegreeDerivedSectionsMap`, which is what makes the identification usable: a consumer may
replace the isomorphism by the composite of the truncation comparison with the single-degree
comparison and use the naturality of each. -/
public theorem topDegreeDerivedSectionsIso_hom (f : X ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen (f ⁻¹ᵁ V)) (d : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (hE : E.IsLE d) :
    (topDegreeDerivedSectionsIso f V hV d E hcoh hE).hom =
      topDegreeDerivedSectionsMap f V d E hE :=
  rfl

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
