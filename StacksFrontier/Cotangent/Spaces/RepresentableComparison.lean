module

public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplexULift
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleGeneral
public import StacksFrontier.Cotangent.SheavesOfRings.HenselianStalkVanishing
public import StacksFrontier.Cotangent.SheavesOfRings.PullbackCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.SquareFunctorialityComp
public import StacksFrontier.Cotangent.Spaces.RepresentableEpsilonSquare
public import StacksFrontier.Cotangent.Spaces.RepresentableStalks

/-!
# The cotangent complex of a morphism of representable algebraic spaces

Let `h : T₁ ⟶ T₂` be a morphism of the big fppf site over `S`, so that
`f : X = yoneda T₁ ⟶ Y = yoneda T₂` is a morphism of algebraic spaces represented by schemes,
with underlying morphism of schemes `f₀ : X₀ ⟶ Y₀`. Stacks 08VF identifies the cotangent
complex `L_{X/Y}` of `f` with `ε^*L_{X₀/Y₀}`, where `ε : (X_étale, 𝒪_X) ⟶ (X₀,Zar, 𝒪_{X₀})`
is the comparison morphism of Derived Categories of Spaces, Section 071P.

This file constructs the canonical map `ε^*L_{X₀/Y₀} ⟶ L_{X/Y}` of the source's proof:

`ε^*L_{X₀/Y₀} = L_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⊗_{ε⁻¹𝒪_{X₀}} 𝒪_X ⟶ L_{𝒪_X/ε⁻¹f₀⁻¹𝒪_{Y₀}}`
`  = L_{𝒪_X/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⟶ L_{𝒪_X/f_small⁻¹𝒪_Y} = L_{X/Y}`,

the first identification being the inverse image of the cotangent complex (Stacks 08SV) read
through the definition of `ε^*`, the two arrows being the canonical arrows of the fundamental
triangles (Stacks 08SZ) of the towers `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ ε⁻¹𝒪_{X₀} ⟶ 𝒪_X` and
`ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ f_small⁻¹𝒪_Y ⟶ 𝒪_X`, and the middle equality the square of Remark 08GH,
`AlgebraicGeometry.Space.representedBaseMap_square`.

## Main definitions

* `AlgebraicGeometry.Space.representedPulledBackCotangentComplex`: `ε^*L_{X₀/Y₀}`, the
  degreewise pullback along `ε` of the cotangent complex of `f₀` of Definition 08T2, its
  sections first lifted to the universe of the small étale site.
* `AlgebraicGeometry.Space.representedCotangentComparison`: the canonical map
  `ε^*L_{X₀/Y₀} ⟶ L_{X/Y}`.
* `AlgebraicGeometry.Space.representedCotangentComplexDerivedIso`: **Stacks 08VF**, the
  canonical identification `ε^*L_{X₀/Y₀} = L_{X/Y}` in `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.quasiIso_representedCotangentComparison`: **Stacks 08VF**, the
  canonical map is a quasi-isomorphism.
* `AlgebraicGeometry.Space.towerCotangentUnit_comp_representedBaseChangedComparison`: the
  canonical map is the one of the source, its transpose being the functoriality of the cotangent
  complex over the square of Remark 08GH (Section 08UQ).
* `AlgebraicGeometry.Space.acyclic_cotangentComplex_representedEpsilon` and
  `AlgebraicGeometry.Space.acyclic_representedBaseChangedCotangentComplex`: the two vanishing
  statements, checked at the geometric points, where the stalk maps are strict henselizations.

## Implementation notes

An algebraic space representable by a scheme is isomorphic to `yoneda.obj T` for an object `T`
of the big fppf site over `S`, and a morphism between two such is `yoneda.map` of a morphism
`T₁ ⟶ T₂` (Yoneda); the statements are made for these, `X₀` and `Y₀` being the schemes
underlying `T₁` and `T₂`.

`ε^*` is the degreewise pullback of sheaves of modules along `ε`, as the source writes it; the
terms of the cotangent complex are base changes of sheaves of differentials of free algebras,
and the source's `ε^*` is exact (Stacks 08H8).

The small étale site of an algebraic space has its objects in `Type (u + 1)`, so `L_{X/Y}` has
its sections in `u + 1`; the cotangent complex of `f₀` of Definition 08T2 has its sections in
`u`, and is lifted to `u + 1` by `CategoryTheory.Sheaf.liftTargetModules`, which changes nothing
but the universe and commutes with the formation of the cotangent complex
(`AlgebraicGeometry.Scheme.Hom.cotangentComplexULiftIso`).

## References

* [Stacks Project, Tag 08VF](https://stacks.math.columbia.edu/tag/08VF)
* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory.Sheaf

universe u₁ v₁ w₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u₁ v₁ w₁}} (g : A ⟶ B) (h : B ⟶ D)

open Pretriangulated in
/-- If `L_{D/B}` is acyclic, the first arrow `L_{B/A} ⊗_B D ⟶ L_{D/A}` of the fundamental triangle
of the tower `A ⟶ B ⟶ D` (Stacks 08SZ) is a quasi-isomorphism. -/
theorem quasiIso_towerCotangentBaseChange_of_acyclic
    (hD : (cotangentComplex.{u₁, v₁, w₁} J h).Acyclic) :
    QuasiIso (towerCotangentBaseChange.{u₁, v₁, w₁} J g h) := by
  let := HasDerivedCategory.standard (targetModules.{u₁, v₁, w₁} J D)
  obtain ⟨δ, hT⟩ := exists_distTriang_towerCotangent.{u₁, v₁, w₁} J g h
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (Stacks.Injectives.isZero_Q_obj_of_acyclic _ hD)

open Pretriangulated in
/-- If `L_{B/A} ⊗_B D` is acyclic, the second arrow `L_{D/A} ⟶ L_{D/B}` of the fundamental
triangle of the tower `A ⟶ B ⟶ D` (Stacks 08SZ) is a quasi-isomorphism. -/
theorem quasiIso_towerCotangentChangeOfBase_of_acyclic
    (hB : (baseChangedCotangentComplex.{u₁, v₁, w₁} J g h).Acyclic) :
    QuasiIso (towerCotangentChangeOfBase.{u₁, v₁, w₁} J g h) := by
  let := HasDerivedCategory.standard (targetModules.{u₁, v₁, w₁} J D)
  obtain ⟨δ, hT⟩ := exists_distTriang_towerCotangent.{u₁, v₁, w₁} J g h
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (Triangle.isZero₁_iff_isIso₂ _ hT).1 (Stacks.Injectives.isZero_Q_obj_of_acyclic _ hB)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T₁ T₂ : BigFppfOver B S hS} (h : T₁ ⟶ T₂)

/-- **`ε^*L_{X₀/Y₀}`.** The degreewise pullback, along the comparison morphism `ε` of
Section 071P for the algebraic space `yoneda T₁` represented by `X₀`, of the cotangent complex
`L_{X₀/Y₀}` of the underlying morphism of schemes `f₀` (Definition 08T2), whose sections are
first lifted to the universe `u + 1` of the small étale site. -/
noncomputable abbrev representedPulledBackCotangentComplex :
    CochainComplex
      (smallEtaleModulesULift B S hS ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩) ℤ :=
  letI := hasSheafify_smallEtaleRingedTopos B S hS
    ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩
  letI := wEqualsLocallyBijective_smallEtaleRingedTopos B S hS
    ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩
  letI := Sheaf.additive_toRingedToposModulesHom_pullbackModules.{u + 1, u, u, u, u, u + 1}
    (representedToZariskiRingedToposHom B S hS T₁)
  (((representedToZariskiRingedToposHom B S hS T₁).toRingedToposModulesHom.pullbackModules
      ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((Sheaf.liftTargetModules.{u, u, u, u + 1}
        (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
        ((BigFppfOver.toScheme B S hS).obj T₁).zariskiRingedTopos.O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((BigFppfOver.toScheme B S hS).map h).cotangentComplex)

/-- The structure map `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ ε⁻¹𝒪_{X₀}`: the inverse image along `ε` of the structure map
of the cotangent complex of `f₀` (Definition 08T2), its sections lifted to `u + 1`. -/
noncomputable abbrev representedInverseImageStructureMap :=
  (representedToZariskiRingedToposHom B S hS T₁).toToposHom.inverseImageRing.map
    ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
      SheafOfModules.commRingCatULift.{u, u + 1}).map
      (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).fSharpInverseImage)

/-- The structure map `f_small⁻¹𝒪_Y ⟶ 𝒪_X` of `L_{X/Y}`, its sections lifted to `u + 1`. -/
noncomputable abbrev representedSpaceStructureMap :=
  (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS (yoneda.obj T₁))).map
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).fSharpInverseImage

/-- **The identification `ε^*L_{X₀/Y₀} = L_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⊗_{ε⁻¹𝒪_{X₀}} 𝒪_X`.** The lift
of `L_{X₀/Y₀}` to the universe of the site is the cotangent complex of the lifted structure map
(`AlgebraicGeometry.Scheme.Hom.cotangentComplexULiftIso`), and the pullback along `ε` of a
cotangent complex is the base change of its inverse image, which is the cotangent complex of the
inverse image (Stacks 08SV, `CategoryTheory.Sheaf.pullbackModulesCotangentComplexIso`). -/
noncomputable def representedPulledBackCotangentComplexIso :
    representedPulledBackCotangentComplex B S hS h ≅
      Sheaf.baseChangedCotangentComplex.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T₁))
        (representedInverseImageStructureMap B S hS h)
        (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage :=
  letI := hasSheafify_smallEtaleRingedTopos B S hS
    ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩
  letI := wEqualsLocallyBijective_smallEtaleRingedTopos B S hS
    ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩
  letI := Sheaf.additive_toRingedToposModulesHom_pullbackModules.{u + 1, u, u, u, u, u + 1}
    (representedToZariskiRingedToposHom B S hS T₁)
  (((representedToZariskiRingedToposHom B S hS T₁).toRingedToposModulesHom.pullbackModules
      ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (Scheme.Hom.cotangentComplexULiftIso ((BigFppfOver.toScheme B S hS).map h)) ≪≫
    Sheaf.pullbackModulesCotangentComplexIso.{u + 1, u, u, u, u, u + 1}
      (representedToZariskiRingedToposHom B S hS T₁)
      ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
        SheafOfModules.commRingCatULift.{u, u + 1}).map
        (Scheme.Hom.zariskiRingedToposHom
          ((BigFppfOver.toScheme B S hS).map h)).fSharpInverseImage)

/-- **The map `L_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⊗_{ε⁻¹𝒪_{X₀}} 𝒪_X ⟶ L_{X/Y}`.** It is the first arrow
of the fundamental triangle (Stacks 08SZ) of the tower `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ ε⁻¹𝒪_{X₀} ⟶ 𝒪_X`, the
identification of the two composites given by the square of Remark 08GH
(`AlgebraicGeometry.Space.representedBaseMap_square`), and the second arrow of the fundamental
triangle of the tower `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ f_small⁻¹𝒪_Y ⟶ 𝒪_X`. Its transpose is the functoriality
map of the cotangent complex over the square (Section 08UQ):
`AlgebraicGeometry.Space.towerCotangentUnit_comp_representedBaseChangedComparison`. -/
noncomputable def representedBaseChangedComparison :
    Sheaf.baseChangedCotangentComplex.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T₁))
        (representedInverseImageStructureMap B S hS h)
        (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage ⟶
      cotangentComplex B S hS (representedSpaceMap B S hS h) :=
  Sheaf.towerCotangentBaseChange.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T₁))
      (representedInverseImageStructureMap B S hS h)
      (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage ≫
    eqToHom (congrArg
      (Sheaf.cotangentComplex.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T₁)))
      (representedBaseMap_square B S hS h)) ≫
    Sheaf.towerCotangentChangeOfBase.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T₁))
      (representedBaseMap B S hS h)
      (representedSpaceStructureMap B S hS h)

/-- **The transpose of `representedBaseChangedComparison` is the functoriality of the cotangent
complex over the square of Remark 08GH.** Precomposed with the unit
`L_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⟶ L_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⊗_{ε⁻¹𝒪_{X₀}} 𝒪_X` and read
`ε⁻¹𝒪_{X₀}`-linearly, it is the map `L_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⟶ L_{𝒪_X/f_small⁻¹𝒪_Y}` that the
canonical map of standard resolutions over the square
`(ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ ε⁻¹𝒪_{X₀}) ⟶ (f_small⁻¹𝒪_Y ⟶ 𝒪_X)` induces (Section 08UQ). So it is the map
the source's proof takes. -/
theorem towerCotangentUnit_comp_representedBaseChangedComparison :
    Sheaf.towerCotangentUnit.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T₁))
        (representedInverseImageStructureMap B S hS h)
        (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage ≫
      ((Sheaf.squareRestrict.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T₁))
          (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (representedBaseChangedComparison B S hS h) =
      Sheaf.squareCotangentComplexMap
        (Sheaf.resolutionSquareMap.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T₁))
          (representedBaseMap B S hS h)
          (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage
          (representedBaseMap_square B S hS h)) :=
  Sheaf.squareCotangentComplexMap_eq_towerCotangent (representedBaseMap_square B S hS h)

/-- **The canonical map `ε^*L_{X₀/Y₀} ⟶ L_{X/Y}` of Stacks 08VF**: the identification
`ε^*L_{X₀/Y₀} = L_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⊗_{ε⁻¹𝒪_{X₀}} 𝒪_X`
(`AlgebraicGeometry.Space.representedPulledBackCotangentComplexIso`, Stacks 08SV) followed by
the map induced on the base change by the functoriality of the cotangent complex over the square
of Remark 08GH (`AlgebraicGeometry.Space.representedBaseChangedComparison`). -/
noncomputable def representedCotangentComparison :
    representedPulledBackCotangentComplex B S hS h ⟶
      cotangentComplex B S hS (representedSpaceMap B S hS h) :=
  (representedPulledBackCotangentComplexIso B S hS h).hom ≫
    representedBaseChangedComparison B S hS h

/-! ### The two vanishing statements -/

/-- **`L_{𝒪_X/ε⁻¹𝒪_{X₀}} = 0`.** The cotangent complex of the structure map `ε⁻¹𝒪_{X₀} ⟶ 𝒪_X` of
`ε` is acyclic: at every geometric point `x̄` of `X` its stalk is the cotangent complex of the
strict henselization `𝒪_{X₀,x} ⟶ 𝒪_{X,x̄}` (Stacks 08T0, 05V1, 04KF), which vanishes
(Stacks 08R2), and the geometric points form a conservative family (Stacks 04K5). -/
theorem acyclic_cotangentComplex_representedEpsilon (T : BigFppfOver B S hS) :
    (Sheaf.cotangentComplex.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T))
      (representedToZariskiRingedToposHom B S hS T).fSharpInverseImage).Acyclic :=
  Sheaf.acyclic_cotangentComplex_of_isHenselizationAt.{u + 1, u, u} _
    (isConservativeFamilyOfPoints_uliftEtaleSitePoint B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T))
    (fun Φ hΦ => representedToZariskiRingedToposHom_stalk_isHenselization_of_mem B S hS T Φ hΦ)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

/-- The first arrow of the comparison, `L_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⊗_{ε⁻¹𝒪_{X₀}} 𝒪_X ⟶
L_{𝒪_X/ε⁻¹f₀⁻¹𝒪_{Y₀}}`, is a quasi-isomorphism: the third vertex `L_{𝒪_X/ε⁻¹𝒪_{X₀}}` of its
fundamental triangle (Stacks 08SZ) vanishes. -/
theorem quasiIso_representedTowerCotangentBaseChange :
    QuasiIso (Sheaf.towerCotangentBaseChange.{u + 1, u, u}
      (SmallEtale.topology B S hS (yoneda.obj T₁)) (representedInverseImageStructureMap B S hS h)
      (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage) :=
  Sheaf.quasiIso_towerCotangentBaseChange_of_acyclic.{u + 1, u, u} _ _ _
    (acyclic_cotangentComplex_representedEpsilon B S hS T₁)

/-- **`L_{f_small⁻¹𝒪_Y/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⊗ 𝒪_X = 0`.** The first vertex of the fundamental triangle of
the tower `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ f_small⁻¹𝒪_Y ⟶ 𝒪_X` is acyclic: at every geometric point `x̄` of `X`,
with image `ȳ` in `Y` lying over `y ∈ Y₀`, the stalk of the base map
`ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ f_small⁻¹𝒪_Y` is the strict henselization `𝒪_{Y₀,y} ⟶ 𝒪_{Y,ȳ}` (Stacks 05V1,
04KF), whose cotangent complex vanishes (Stacks 08R2), and the geometric points form a
conservative family (Stacks 04K5). -/
theorem acyclic_representedBaseChangedCotangentComplex :
    (Sheaf.baseChangedCotangentComplex.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T₁))
      (representedBaseMap B S hS h) (representedSpaceStructureMap B S hS h)).Acyclic :=
  Sheaf.acyclic_baseChangedCotangentComplex_of_isHenselizationAt.{u + 1, u, u} _
    (isConservativeFamilyOfPoints_uliftEtaleSitePoint B S hS (yoneda.obj T₁)
      (isAlgebraicSpace_yoneda B S hS T₁))
    (fun Φ hΦ => representedBaseMap_stalk_isHenselization_of_mem B S hS h Φ hΦ) _

/-- The second arrow of the comparison, `L_{𝒪_X/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⟶ L_{𝒪_X/f_small⁻¹𝒪_Y}`, is a
quasi-isomorphism: the first vertex of its fundamental triangle (Stacks 08SZ) vanishes. -/
theorem quasiIso_representedTowerCotangentChangeOfBase :
    QuasiIso (Sheaf.towerCotangentChangeOfBase.{u + 1, u, u}
      (SmallEtale.topology B S hS (yoneda.obj T₁)) (representedBaseMap B S hS h)
      (representedSpaceStructureMap B S hS h)) :=
  Sheaf.quasiIso_towerCotangentChangeOfBase_of_acyclic.{u + 1, u, u} _ _ _
    (acyclic_representedBaseChangedCotangentComplex B S hS h)

/-- **Stacks 08VF.** Let `f : X ⟶ Y` be the morphism of algebraic spaces over `S` represented by
a morphism `T₁ ⟶ T₂` of the big fppf site, so that `X` and `Y` are representable by the schemes
`X₀` and `Y₀` underlying `T₁` and `T₂`. Then the canonical map `ε^*L_{X₀/Y₀} ⟶ L_{X/Y}`
(`AlgebraicGeometry.Space.representedCotangentComparison`) is a quasi-isomorphism.

The source's proof checks this on stalks at geometric points; here the map is factored through
the two canonical arrows of the fundamental triangles of Stacks 08SZ, and the two vertices that
must vanish, `L_{𝒪_X/ε⁻¹𝒪_{X₀}}` and `L_{f_small⁻¹𝒪_Y/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⊗ 𝒪_X`, vanish because
their stalks at the geometric points are the cotangent complexes of the strict henselizations
`𝒪_{X₀,x} ⟶ 𝒪_{X,x̄}` and `𝒪_{Y₀,y} ⟶ 𝒪_{Y,ȳ}` (Stacks 04K5, 08T0, 05V1, 04KF, 08R2); this is the
content of Lemma 08UN that the source invokes. -/
@[stacks 08VF "the canonical map `ε^*L_{X₀/Y₀} ⟶ L_{X/Y}` is a quasi-isomorphism, for the morphism \
of algebraic spaces represented by a morphism `T₁ ⟶ T₂` of the big fppf site over `S` (so `X` and \
`Y` are represented by the schemes `X₀`, `Y₀` underlying `T₁`, `T₂`); `ε` is the comparison of \
Section 071P (`representedToZariskiRingedToposHom`), `L_{X₀/Y₀}` the cotangent complex of \
Definition 08T2 lifted to the universe of the small étale site, `ε^*` the degreewise pullback of \
sheaves of modules along `ε`. The map is `representedCotangentComparison`; its transpose is the \
functoriality of the cotangent complex over the square of Remark 08GH \
(`towerCotangentUnit_comp_representedBaseChangedComparison`)"]
theorem quasiIso_representedCotangentComparison :
    QuasiIso (representedCotangentComparison B S hS h) := by
  have h₃ : QuasiIso (eqToHom (congrArg
      (Sheaf.cotangentComplex.{u + 1, u, u} (SmallEtale.topology B S hS (yoneda.obj T₁)))
      (representedBaseMap_square B S hS h))) := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso _) (hφ' := quasiIso_comp _ _
    (hφ := quasiIso_representedTowerCotangentBaseChange B S hS h)
    (hφ' := quasiIso_comp _ _ (hφ := h₃)
      (hφ' := quasiIso_representedTowerCotangentChangeOfBase B S hS h)))

universe t in
/-- **Stacks 08VF.** The canonical identification `L_{X/Y} = ε^*L_{X₀/Y₀}` in `D(𝒪_X)`, for the
morphism `f : X ⟶ Y` of algebraic spaces represented by a morphism `T₁ ⟶ T₂` of the big fppf
site over `S`: the image in the derived category of the canonical map
`AlgebraicGeometry.Space.representedCotangentComparison`, which is a quasi-isomorphism
(`AlgebraicGeometry.Space.quasiIso_representedCotangentComparison`). -/
@[stacks 08VF "the canonical identification `ε^*L_{X₀/Y₀} ≅ L_{X/Y}` in `D(𝒪_X)`, for the \
morphism of algebraic spaces represented by a morphism `T₁ ⟶ T₂` of the big fppf site over `S`, \
as the image in the derived category of the canonical map `representedCotangentComparison`; any \
derived category of `Mod(𝒪_X)` may be used"]
noncomputable def representedCotangentComplexDerivedIso
    [HasDerivedCategory.{t}
      (smallEtaleModulesULift B S hS ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩)] :
    DerivedCategory.Q.obj (representedPulledBackCotangentComplex B S hS h) ≅
      cotangentComplexDerived B S hS (representedSpaceMap B S hS h) :=
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_representedCotangentComparison B S hS h)
  asIso (DerivedCategory.Q.map (representedCotangentComparison B S hS h))

universe t in
/-- The identification of Stacks 08VF is the image of the canonical map in the derived
category. -/
theorem representedCotangentComplexDerivedIso_hom
    [HasDerivedCategory.{t}
      (smallEtaleModulesULift B S hS ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩)] :
    (representedCotangentComplexDerivedIso B S hS h).hom =
      DerivedCategory.Q.map (representedCotangentComparison B S hS h) :=
  rfl

end AlgebraicGeometry.Space

end
