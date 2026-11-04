module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.SquareFunctoriality

/-!
# The cotangent complex of a product of two sheaves of rings

Let `C` be a site and let `f : A ⟶ B` and `f' : A ⟶ B'` be homomorphisms of sheaves of
commutative rings on `C`. The product `B ⨯ B'` of the two targets is again a sheaf of
commutative rings and `f`, `f'` induce `A ⟶ B ⨯ B'`. The two projections `B ⨯ B' ⟶ B` and
`B ⨯ B' ⟶ B'` fit into commutative squares over the identity of `A`, so the square
functoriality of the cotangent complex
(`CategoryTheory.Sheaf.squareCotangentComplexMap`) produces two `B ⨯ B'`-linear maps
`L_{B ⨯ B'/A} ⟶ L_{B/A}` and `L_{B ⨯ B'/A} ⟶ L_{B'/A}`, the targets read over `B ⨯ B'` by
restriction of scalars along the respective projection. Their pairing is the canonical map

`L_{B ⨯ B'/A} ⟶ L_{B/A} ⊕ L_{B'/A}`

formed in complexes of sheaves of `B ⨯ B'`-modules, together with its image in the derived
category `D(B ⨯ B')`.

## Main definitions

* `CategoryTheory.Sheaf.prodRingHom` is the homomorphism `A ⟶ B ⨯ B'` induced by `f` and `f'`.
* `CategoryTheory.Sheaf.prodRestrictFst` and `CategoryTheory.Sheaf.prodRestrictSnd` read a sheaf
  of `B`-modules, resp. of `B'`-modules, over `B ⨯ B'` along the corresponding projection.
* `CategoryTheory.Sheaf.prodResolutionSquareFst` and
  `CategoryTheory.Sheaf.prodResolutionSquareSnd` are the two maps of standard resolutions
  attached to the projection squares.
* `CategoryTheory.Sheaf.prodCotangentSummandFst`,
  `CategoryTheory.Sheaf.prodCotangentSummandSnd` and `CategoryTheory.Sheaf.prodCotangentSum` are
  the two summands `L_{B/A}`, `L_{B'/A}` read over `B ⨯ B'` and their direct sum.
* `CategoryTheory.Sheaf.prodCotangentComponentFst` and
  `CategoryTheory.Sheaf.prodCotangentComponentSnd` are the two induced maps of cotangent
  complexes.
* `CategoryTheory.Sheaf.prodCotangentComparison` is the canonical comparison map
  `L_{B ⨯ B'/A} ⟶ L_{B/A} ⊕ L_{B'/A}`, and
  `CategoryTheory.Sheaf.prodCotangentComparisonDerived` is its image in `D(B ⨯ B')`.

## Main results

* `CategoryTheory.Sheaf.prodCotangentComparison_fst` and
  `CategoryTheory.Sheaf.prodCotangentComparison_snd`: the two components of the comparison map
  are the two square-functoriality maps; `CategoryTheory.Sheaf.prodCotangentComparison_unique`
  says that this characterizes it.
* `CategoryTheory.Sheaf.prodCotangentComparison_fst_derivation` and
  `CategoryTheory.Sheaf.prodCotangentComparison_snd_derivation`: in cohomological degree `-n`
  the two components of the comparison map carry the universal derivation of the degree-`n` term
  of the standard resolution of `A ⟶ B ⨯ B'` to the universal derivation of the degree-`n` term
  of the standard resolution of `A ⟶ B`, resp. of `A ⟶ B'`, precomposed with the map of
  standard resolutions. This is the sheaf-level form of `1 ⊗ d p ↦ (1 ⊗ d p₁, 1 ⊗ d p₂)`.
* `CategoryTheory.Sheaf.prodCotangentComparisonDerived_fst` and
  `CategoryTheory.Sheaf.prodCotangentComparisonDerived_snd`: the same characterization of the
  components, in the derived category.

## Implementation notes

The direct sum is the binary biproduct in the category of cochain complexes of sheaves of
`B ⨯ B'`-modules, which exists because that category of sheaves of modules is abelian.

The site-object and site-morphism universes are independent of the universe of sections, as in
`CategoryTheory.Sheaf.cotangentComplex`; the three sheaves of rings share the sections universe.

## References

* [Stacks Project, Tag 08SY](https://stacks.math.columbia.edu/tag/08SY)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08SA](https://stacks.math.columbia.edu/tag/08SA)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w t

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B B' : Sheaf J CommRingCat.{max u v w}}

/-- Cochain complexes of sheaves of modules over a sheaf of rings on the site admit binary
biproducts. -/
private instance (priority := 100000) hasBinaryBiproductCochainComplexTargetModules
    (P : Sheaf J CommRingCat.{max u v w})
    (X Y : CochainComplex (targetModules.{u, v, w} J P) ℤ) : HasBinaryBiproduct X Y :=
  inferInstance

/-! ## The product sheaf of rings and the two projection squares -/

variable (f : A ⟶ B) (f' : A ⟶ B')

/-- The homomorphism `A ⟶ B ⨯ B'` of sheaves of commutative rings induced by two homomorphisms
`f : A ⟶ B` and `f' : A ⟶ B'` out of the same base. -/
noncomputable def prodRingHom : A ⟶ B ⨯ B' := prod.lift f f'

/-- The homomorphism into the product followed by the first projection is the first
homomorphism. -/
lemma prodRingHom_fst : prodRingHom J f f' ≫ prod.fst = f := prod.lift_fst f f'

/-- The homomorphism into the product followed by the second projection is the second
homomorphism. -/
lemma prodRingHom_snd : prodRingHom J f f' ≫ prod.snd = f' := prod.lift_snd f f'

/-- The first projection is the right-hand edge of a commutative square over the identity of the
base sheaf. -/
lemma prodRingHom_square_fst : prodRingHom J f f' ≫ prod.fst = 𝟙 A ≫ f := by
  rw [Category.id_comp, prodRingHom_fst]

/-- The second projection is the right-hand edge of a commutative square over the identity of the
base sheaf. -/
lemma prodRingHom_square_snd : prodRingHom J f f' ≫ prod.snd = 𝟙 A ≫ f' := by
  rw [Category.id_comp, prodRingHom_snd]

/-- Sheaves of `B`-modules read as sheaves of `B ⨯ B'`-modules along the first projection. -/
noncomputable abbrev prodRestrictFst (B B' : Sheaf J CommRingCat.{max u v w}) :
    targetModules.{u, v, w} J B ⥤ targetModules.{u, v, w} J (B ⨯ B') :=
  squareRestrict.{u, v, w} J (prod.fst : B ⨯ B' ⟶ B)

/-- Sheaves of `B'`-modules read as sheaves of `B ⨯ B'`-modules along the second projection. -/
noncomputable abbrev prodRestrictSnd (B B' : Sheaf J CommRingCat.{max u v w}) :
    targetModules.{u, v, w} J B' ⥤ targetModules.{u, v, w} J (B ⨯ B') :=
  squareRestrict.{u, v, w} J (prod.snd : B ⨯ B' ⟶ B')

/-- The map of standard resolutions from that of `A ⟶ B ⨯ B'` to that of `A ⟶ B`, attached to the
square formed by the first projection. -/
noncomputable def prodResolutionSquareFst :
    ResolutionSquareMap.{u, v, w} J (prodRingHom J f f') f (𝟙 A) prod.fst :=
  resolutionSquareMap.{u, v, w} J (𝟙 A) prod.fst (prodRingHom_square_fst J f f')

/-- The map of standard resolutions from that of `A ⟶ B ⨯ B'` to that of `A ⟶ B'`, attached to
the square formed by the second projection. -/
noncomputable def prodResolutionSquareSnd :
    ResolutionSquareMap.{u, v, w} J (prodRingHom J f f') f' (𝟙 A) prod.snd :=
  resolutionSquareMap.{u, v, w} J (𝟙 A) prod.snd (prodRingHom_square_snd J f f')

/-! ## The direct sum of the two cotangent complexes over the product -/

/-- The cotangent complex `L_{B/A}` read over `B ⨯ B'` along the first projection. -/
noncomputable abbrev prodCotangentSummandFst :
    CochainComplex (targetModules.{u, v, w} J (B ⨯ B')) ℤ :=
  ((prodRestrictFst J B B').mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (cotangentComplex.{u, v, w} J f)

/-- The cotangent complex `L_{B'/A}` read over `B ⨯ B'` along the second projection. -/
noncomputable abbrev prodCotangentSummandSnd :
    CochainComplex (targetModules.{u, v, w} J (B ⨯ B')) ℤ :=
  ((prodRestrictSnd J B B').mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (cotangentComplex.{u, v, w} J f')

/-- The direct sum `L_{B/A} ⊕ L_{B'/A}` of complexes of sheaves of `B ⨯ B'`-modules. -/
noncomputable abbrev prodCotangentSum : CochainComplex (targetModules.{u, v, w} J (B ⨯ B')) ℤ :=
  prodCotangentSummandFst J f (B' := B') ⊞ prodCotangentSummandSnd J f' (B := B)

/-- The projection of the direct sum onto `L_{B/A}`. -/
noncomputable abbrev prodCotangentSumFst :
    prodCotangentSum J f f' ⟶ prodCotangentSummandFst J f (B' := B') :=
  biprod.fst (X := prodCotangentSummandFst J f (B' := B'))
    (Y := prodCotangentSummandSnd J f' (B := B))

/-- The projection of the direct sum onto `L_{B'/A}`. -/
noncomputable abbrev prodCotangentSumSnd :
    prodCotangentSum J f f' ⟶ prodCotangentSummandSnd J f' (B := B) :=
  biprod.snd (X := prodCotangentSummandFst J f (B' := B'))
    (Y := prodCotangentSummandSnd J f' (B := B))

/-! ## The comparison map -/

/-- The map `L_{B ⨯ B'/A} ⟶ L_{B/A}` of complexes of sheaves of `B ⨯ B'`-modules induced by the
first projection square. -/
noncomputable def prodCotangentComponentFst :
    cotangentComplex.{u, v, w} J (prodRingHom J f f') ⟶
      prodCotangentSummandFst J f (B' := B') :=
  squareCotangentComplexMap (prodResolutionSquareFst J f f')

/-- The map `L_{B ⨯ B'/A} ⟶ L_{B'/A}` of complexes of sheaves of `B ⨯ B'`-modules induced by the
second projection square. -/
noncomputable def prodCotangentComponentSnd :
    cotangentComplex.{u, v, w} J (prodRingHom J f f') ⟶
      prodCotangentSummandSnd J f' (B := B) :=
  squareCotangentComplexMap (prodResolutionSquareSnd J f f')

/-- The canonical comparison map `L_{B ⨯ B'/A} ⟶ L_{B/A} ⊕ L_{B'/A}` of complexes of sheaves of
`B ⨯ B'`-modules: the pairing of the two maps of cotangent complexes induced by the two projection
squares, each summand read over `B ⨯ B'` by restriction of scalars along the corresponding
projection. -/
@[stacks 08SY "the comparison map"]
noncomputable def prodCotangentComparison :
    cotangentComplex.{u, v, w} J (prodRingHom J f f') ⟶ prodCotangentSum J f f' :=
  biprod.lift (prodCotangentComponentFst J f f') (prodCotangentComponentSnd J f f')

/-- The first component of the comparison map is the map of cotangent complexes induced by the
first projection. -/
lemma prodCotangentComparison_fst :
    prodCotangentComparison J f f' ≫ prodCotangentSumFst J f f' =
      prodCotangentComponentFst J f f' :=
  biprod.lift_fst _ _

/-- The second component of the comparison map is the map of cotangent complexes induced by the
second projection. -/
lemma prodCotangentComparison_snd :
    prodCotangentComparison J f f' ≫ prodCotangentSumSnd J f f' =
      prodCotangentComponentSnd J f f' :=
  biprod.lift_snd _ _

/-- The comparison map is the unique map into the direct sum whose two components are the two
maps of cotangent complexes induced by the projections. -/
lemma prodCotangentComparison_unique
    (φ : cotangentComplex.{u, v, w} J (prodRingHom J f f') ⟶ prodCotangentSum J f f')
    (h₁ : φ ≫ prodCotangentSumFst J f f' = prodCotangentComponentFst J f f')
    (h₂ : φ ≫ prodCotangentSumSnd J f f' = prodCotangentComponentSnd J f f') :
    φ = prodCotangentComparison J f f' :=
  biprod.hom_ext _ _ (h₁.trans (prodCotangentComparison_fst J f f').symm)
    (h₂.trans (prodCotangentComparison_snd J f f').symm)

/-- In cohomological degree `-n` the first component of the comparison map carries the universal
derivation of `P_n`, the degree-`n` term of the standard resolution of `A ⟶ B ⨯ B'`, to the
universal derivation of the degree-`n` term of the standard resolution of `A ⟶ B` precomposed
with the map of standard resolutions: the sheaf-level form of `1 ⊗ d p ↦ 1 ⊗ d p₁`. -/
lemma prodCotangentComparison_fst_derivation (n : ℕ) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J (prodRingHom J f f') (op ⦋n⦌)).obj.obj U) :
    ((cotangentSimplicialModule.{u, v, w} J (prodRingHom J f f')).derivationEquiv (op ⦋n⦌) _
        ((cotangentComplex_degreeIso.{u, v, w} J (prodRingHom J f f') n).inv ≫
          (prodCotangentComparison J f f' ≫ prodCotangentSumFst J f f').f (-(n : ℤ)) ≫
            (prodRestrictFst J B B').map
              (cotangentComplex_degreeIso.{u, v, w} J f n).hom)).d x =
      ((cotangentSimplicialModule.{u, v, w} J f).universalDerivation (op ⦋n⦌)).d
        (((prodResolutionSquareFst J f f').resolution (op ⦋n⦌)).hom.app U x) := by
  rw [prodCotangentComparison_fst]
  exact squareCotangentComplexMap_derivation (prodResolutionSquareFst J f f') n U x

/-- In cohomological degree `-n` the second component of the comparison map carries the universal
derivation of `P_n`, the degree-`n` term of the standard resolution of `A ⟶ B ⨯ B'`, to the
universal derivation of the degree-`n` term of the standard resolution of `A ⟶ B'` precomposed
with the map of standard resolutions: the sheaf-level form of `1 ⊗ d p ↦ 1 ⊗ d p₂`. -/
lemma prodCotangentComparison_snd_derivation (n : ℕ) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J (prodRingHom J f f') (op ⦋n⦌)).obj.obj U) :
    ((cotangentSimplicialModule.{u, v, w} J (prodRingHom J f f')).derivationEquiv (op ⦋n⦌) _
        ((cotangentComplex_degreeIso.{u, v, w} J (prodRingHom J f f') n).inv ≫
          (prodCotangentComparison J f f' ≫ prodCotangentSumSnd J f f').f (-(n : ℤ)) ≫
            (prodRestrictSnd J B B').map
              (cotangentComplex_degreeIso.{u, v, w} J f' n).hom)).d x =
      ((cotangentSimplicialModule.{u, v, w} J f').universalDerivation (op ⦋n⦌)).d
        (((prodResolutionSquareSnd J f f').resolution (op ⦋n⦌)).hom.app U x) := by
  rw [prodCotangentComparison_snd]
  exact squareCotangentComplexMap_derivation (prodResolutionSquareSnd J f f') n U x

/-! ## The comparison map in the derived category -/

/-- The comparison map `L_{B ⨯ B'/A} ⟶ L_{B/A} ⊕ L_{B'/A}` read in the derived category
`D(B ⨯ B')`. -/
@[stacks 08SY "the comparison map in the derived category"]
noncomputable abbrev prodCotangentComparisonDerived
    [HasDerivedCategory.{t} (targetModules.{u, v, w} J (B ⨯ B'))] :
    cotangentComplexDerived.{u, v, w, t} J (prodRingHom J f f') ⟶
      DerivedCategory.Q.obj (prodCotangentSum J f f') :=
  DerivedCategory.Q.map (prodCotangentComparison J f f')

/-- In the derived category the first component of the comparison map is still the map of
cotangent complexes induced by the first projection. -/
lemma prodCotangentComparisonDerived_fst
    [HasDerivedCategory.{t} (targetModules.{u, v, w} J (B ⨯ B'))] :
    prodCotangentComparisonDerived.{u, v, w, t} J f f' ≫
        DerivedCategory.Q.map (prodCotangentSumFst J f f') =
      DerivedCategory.Q.map (prodCotangentComponentFst J f f') := by
  rw [← Functor.map_comp, prodCotangentComparison_fst]

/-- In the derived category the second component of the comparison map is still the map of
cotangent complexes induced by the second projection. -/
lemma prodCotangentComparisonDerived_snd
    [HasDerivedCategory.{t} (targetModules.{u, v, w} J (B ⨯ B'))] :
    prodCotangentComparisonDerived.{u, v, w, t} J f f' ≫
        DerivedCategory.Q.map (prodCotangentSumSnd J f f') =
      DerivedCategory.Q.map (prodCotangentComponentSnd J f f') := by
  rw [← Functor.map_comp, prodCotangentComparison_snd]

end CategoryTheory.Sheaf

end
