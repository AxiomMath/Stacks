module

public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafificationPresheafBase
public import StacksFrontier.Cotangent.Spaces.CotangentComplex

/-!
# The cotangent complex of an algebraic space over a ring as a sheafification

Let `Λ` be a ring and let `X` be an algebraic space over `Spec Λ`, with a homomorphism
`φ : Λ̲_X ⟶ 𝒪_X` from the constant sheaf of rings with value `Λ` on the small étale site `X_étale`.
With the sections lifted into the universe of the site, as in Tag 08VD, the cotangent complex
`L_{𝒪_X/Λ̲_X}` of `φ` is the sheafification of the rule `U ↦ L_{𝒪_X(U)/Λ}`, the cotangent complexes
of the ring maps `Λ → Λ̲_X(U) → 𝒪_X(U)`. This is Remark 08SX over the constant presheaf `U ↦ Λ`,
which maps to `Λ̲_X` by the unit of sheafification, and it is the form in which the proof of
Tag 08VM, like that of Tag 08T9 for schemes, uses Remark 08SX. It is not the sheafification of
`U ↦ L_{𝒪_X(U)/Λ̲_X(U)}` of Remark 08SX itself: the ring `Λ̲_X(U)` differs from `Λ` when `U` is
disconnected.

The structure map of Tag 08VG is such a `φ`, so for it `L_{𝒪_X/Λ̲_X}` is the cotangent complex
of Tag 08VG.

## Main definitions

* `AlgebraicGeometry.Space.etaleConstantBasePresheaf` is the constant presheaf `U ↦ Λ` of rings
  on `X_étale`, lifted into the universe of the site, and
  `AlgebraicGeometry.Space.etaleConstantBasePresheafToSheaf` its map to the lift of the constant
  sheaf `Λ̲_X`, the lift of the unit of sheafification.
* `AlgebraicGeometry.Space.sectionwiseCotangentComplexConstant` is the complex of presheaves of
  `𝒪_X`-modules `U ↦ L_{𝒪_X(U)/Λ}`.

## Main results

* `AlgebraicGeometry.Space.W_etaleConstantBasePresheafToSheaf`: the map `U ↦ Λ` to `Λ̲_X` is
  inverted by sheafification, also after lifting the sections.
* `AlgebraicGeometry.Space.sectionwiseCotangentComplexConstant_X_obj`: its term in degree `j`
  over `U` is the degree-`j` term of the cotangent complex of the ring map `Λ → 𝒪_X(U)`.
* `AlgebraicGeometry.Space.sheafifiedSectionwiseCotangentComplexConstantIso`: the degreewise
  sheafification of `U ↦ L_{𝒪_X(U)/Λ}` is `L_{𝒪_X/Λ̲_X}`, as complexes of sheaves of
  `𝒪_X`-modules, and `sheafifiedSectionwiseCotangentComplexConstantAbIso` the same statement on
  abelian groups.

## Implementation notes

The constant sheaf `Λ̲_X` and the structure sheaf have their sections in the universe `u` of the
schemes, below the universe `u + 1` of the site `X_étale`; the cotangent complex of a homomorphism
of sheaves of rings is formed for sections in a universe containing the site. Both are therefore
lifted by `AlgebraicGeometry.SheafOfModules.sheafULift`, as in Tag 08VD, and so is the constant
presheaf `U ↦ Λ` and its map to `Λ̲_X`. Over `U` the rings are `ULift Λ` and `ULift 𝒪_X(U)`,
isomorphic to `Λ` and `𝒪_X(U)` through `ULift.ringEquiv`.

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08VD](https://stacks.math.columbia.edu/tag/08VD)
* [Stacks Project, Tag 08VG](https://stacks.math.columbia.edu/tag/08VG)
* [Stacks Project, Tag 08VM](https://stacks.math.columbia.edu/tag/08VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SheafOfModules (commRingCatULift)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ))) (X : AlgebraicSpaces B (Spec (CommRingCat.of Λ)) hS)

/- The instances below are stated for sections in `max u v w`; offered a goal about sections in
`u` or `u + 1` on `X_étale` (objects in `Type (u + 1)`, morphisms in `Type u`) instance search
gets stuck on `u + 1 =?= max (u + 1) ?w` instead of moving on to the instances of the small étale
site (`AlgebraicGeometry.Space.SmallEtale.instHasSheafify`,
`AlgebraicGeometry.Space.hasSheafify_smallEtaleRingedTopos`), so they are switched off here. -/
attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat
  CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat

/-- The constant presheaf `U ↦ Λ` of commutative rings on the small étale site of `X`, with its
sections lifted into the universe of the site. -/
abbrev etaleConstantBasePresheaf :
    (SmallEtale B (Spec (CommRingCat.of Λ)) hS X.1)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (Functor.const _).obj (CommRingCat.of Λ) ⋙ commRingCatULift.{u, u + 1}

/-- The map from the constant presheaf `U ↦ Λ` to the constant sheaf `Λ̲_X` of `X_étale`, both
with their sections lifted into the universe of the site: the lift of the unit of
sheafification. -/
def etaleConstantBasePresheafToSheaf :
    etaleConstantBasePresheaf Λ B hS X ⟶
      ((SheafOfModules.sheafULift.{u, u + 1, u}
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).obj
          ((constantSheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X.1)
            CommRingCat.{u}).obj (CommRingCat.of Λ))).obj :=
  Functor.whiskerRight
    (toSheafify (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X.1)
      ((Functor.const _).obj (CommRingCat.of Λ)))
    commRingCatULift.{u, u + 1}

/-- The map from the constant presheaf `U ↦ Λ` to the constant sheaf `Λ̲_X` is inverted by
sheafification after lifting the sections: the unit of sheafification is locally bijective, and
raising the universe of the sections changes no equalizer or image sieve. -/
theorem W_etaleConstantBasePresheafToSheaf :
    (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X.1).W
      (etaleConstantBasePresheafToSheaf Λ B hS X) := by
  let J := SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X.1
  let η := toSheafify J ((Functor.const (SmallEtale B (Spec (CommRingCat.of Λ)) hS X.1)ᵒᵖ).obj
    (CommRingCat.of Λ))
  have := CategoryTheory.Sheaf.wEqualsLocallyBijective_commRingCat.{u + 1, u, u} J
  have hη : J.W η := J.W_toSheafify _
  have := hη.isLocallyInjective
  have := hη.isLocallySurjective
  have : Presheaf.IsLocallyInjective J (etaleConstantBasePresheafToSheaf Λ B hS X) :=
    ⟨fun {U} x y h => J.superset_covering (fun _ _ hg => congrArg ULift.up hg)
      (Presheaf.equalizerSieve_mem J η x.down y.down (congrArg ULift.down h))⟩
  have : Presheaf.IsLocallySurjective J (etaleConstantBasePresheafToSheaf Λ B hS X) := by
    refine ⟨fun {U} s => J.superset_covering ?_ (Presheaf.imageSieve_mem J η s.down)⟩
    rintro V g ⟨t, ht⟩
    exact ⟨ULift.up t, congrArg ULift.up ht⟩
  exact J.W_of_isLocallyBijective _

variable {Λ B hS X}
variable (φ : (constantSheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X.1)
    CommRingCat.{u}).obj (CommRingCat.of Λ) ⟶
      (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).O)

/-- The complex of presheaves of `𝒪_X`-modules `U ↦ L_{𝒪_X(U)/Λ}` on `X_étale`, sections lifted
into the universe of the site: over `U` it is the cotangent complex of the ring map
`Λ → Λ̲_X(U) → 𝒪_X(U)` given by `φ`, with the maps induced by the restriction maps of `𝒪_X` as
restriction maps. -/
abbrev sectionwiseCotangentComplexConstant :
    CochainComplex (PresheafOfModules.{u + 1}
      (ringSheaf.{u + 1, u, u + 1}
        (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS X)).obj) ℤ :=
  CategoryTheory.Sheaf.presheafBaseCotangentModuleComplex.{u + 1, u, u}
    (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J
    ((SheafOfModules.sheafULift.{u, u + 1, u}
      (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map φ)
    (etaleConstantBasePresheafToSheaf Λ B hS X)

/-- Over `U`, the degree-`j` term of `U ↦ L_{𝒪_X(U)/Λ}` is the degree-`j` term of the cotangent
complex `L_{𝒪_X(U)/Λ}` of the `Λ`-algebra `𝒪_X(U)`, with the structure map `Λ → Λ̲_X(U) → 𝒪_X(U)`
given by `φ`, all sections lifted into the universe of the site. -/
theorem sectionwiseCotangentComplexConstant_X_obj (j : ℤ)
    (U : (SmallEtale B (Spec (CommRingCat.of Λ)) hS X.1)ᵒᵖ) :
    ((sectionwiseCotangentComplexConstant φ).X j).obj U =
      letI : Algebra (ULift.{u + 1} Λ)
          ((smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS X).obj.obj U) :=
        ((etaleConstantBasePresheafToSheaf Λ B hS X).app U ≫
          ((SheafOfModules.sheafULift.{u, u + 1, u}
            (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map φ).hom.app
              U).hom.toAlgebra
      (CommAlgCat.cotangentComplex.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (CommAlgCat.of (ULift.{u + 1} Λ)
          ((smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS X).obj.obj U))).X j :=
  rfl

/-- **Tag 08SX over the base `U ↦ Λ` on `X_étale`, the form used in Tag 08VM.** Let `X` be an
algebraic space over `Spec Λ` and `φ : Λ̲_X ⟶ 𝒪_X` a homomorphism from the constant sheaf. With
the sections lifted into the universe of the site, the cotangent complex `L_{𝒪_X/Λ̲_X}` of `φ` is
the sheafification of `U ↦ L_{𝒪_X(U)/Λ}`: the degreewise sheafification of the complex of
presheaves of `𝒪_X`-modules `U ↦ L_{𝒪_X(U)/Λ}` is isomorphic to `L_{𝒪_X/Λ̲_X}` as a complex of
sheaves of `𝒪_X`-modules, in each degree by the adjunct of the canonical map
`L_{𝒪_X(U)/Λ} ⟶ L_{𝒪_X(U)/Λ̲_X(U)} ⟶ L_{𝒪_X/Λ̲_X}(U)`. -/
def sheafifiedSectionwiseCotangentComplexConstantIso :
    ((PresheafOfModules.sheafification.{u + 1}
        (𝟙 (ringSheaf.{u + 1, u, u + 1} (smallEtaleStructureSheafULift B
          (Spec (CommRingCat.of Λ)) hS X)).obj)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseCotangentComplexConstant φ) ≅
      CategoryTheory.Sheaf.cotangentComplex.{u + 1, u, u}
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J
        ((SheafOfModules.sheafULift.{u, u + 1, u}
          (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map φ) :=
  CategoryTheory.Sheaf.sheafifiedPresheafBaseCotangentComplexIso.{u + 1, u, u} _ _ _
    (W_etaleConstantBasePresheafToSheaf Λ B hS X)

/-- **Tag 08SX over the base `U ↦ Λ` on `X_étale`, on abelian groups.** The sheafification of the
presheaf of complexes of abelian groups `U ↦ L_{𝒪_X(U)/Λ}` is isomorphic to `L_{𝒪_X/Λ̲_X}`, by
the canonical maps followed by the counit of sheafification. -/
def sheafifiedSectionwiseCotangentComplexConstantAbIso :
    ((presheafToSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CategoryTheory.Sheaf.sectionwiseCotangentPresheafComplex.{u + 1, u, u} ⊥
        (CategoryTheory.Sheaf.presheafBaseHom.{u + 1, u, u}
          (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J
          ((SheafOfModules.sheafULift.{u, u + 1, u}
            (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map φ)
          (etaleConstantBasePresheafToSheaf Λ B hS X))) ≅
      CategoryTheory.Sheaf.cotangentComplexAb.{u + 1, u, u}
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J
        ((SheafOfModules.sheafULift.{u, u + 1, u}
          (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map φ) :=
  CategoryTheory.Sheaf.sheafifiedPresheafBaseCotangentPresheafComplexIso.{u + 1, u, u} _ _ _
    (W_etaleConstantBasePresheafToSheaf Λ B hS X)

end AlgebraicGeometry.Space
