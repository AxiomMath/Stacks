module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraExtensionPushoutEquivalence
public import StacksFrontier.Cotangent.Spaces.ModelCotangentHomologyCoherent
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# The cotangent complex of a space of finite type over a Noetherian ring lies in `D^-_{Coh}`

Let `f : X ⟶ T` be a morphism from an algebraic space to an object `T` of the big fppf site with
affine underlying scheme and Noetherian ring of global functions, `f` locally of finite type
(`T = Spec A` with `A` Noetherian). The cotangent complex `L_{X/T}` of Stacks 08SU is formed on
the model of the small étale site of `X` (`AlgebraicGeometry.Space.modelRingedToposHom`). This
file proves that it lies in `D^-_{Coh}(𝒪_X)`
(`AlgebraicGeometry.Space.exists_isCoherent_homology_isBoundedAbove_cotangentComplexDerived`):
there is an object `E` of the derived category of `𝒪_X`-modules on the small étale site of `X`
which the Comparison Lemma carries to `L_{X/T}`, whose cohomology sheaves are coherent and which
is bounded above.

The object is `L_{X/T}` carried back to `X` along the Comparison Lemma
(`AlgebraicGeometry.Space.spaceCotangentComplex`); its cohomology sheaves are those of `L_{X/T}`
carried back, which are coherent
(`AlgebraicGeometry.Space.isCoherent_modelCotangentHomology`: Tags 08VG, 08SX, 08R2, 08PZ and
Descent 03DX), and it vanishes in positive degrees, the cotangent complex being concentrated in
non-positive degrees.

## Main definitions

* `AlgebraicGeometry.Space.spaceCotangentComplex`: `L_{X/T}` as a complex of `𝒪_X`-modules on the
  small étale site of `X`.

## Main results

* `AlgebraicGeometry.Space.exists_isCoherent_homology_isBoundedAbove_cotangentComplexDerived`

## References

* [Stacks Project, Tag 08PZ](https://stacks.math.columbia.edu/tag/08PZ)
* [Stacks Project, Tag 08VG](https://stacks.math.columbia.edu/tag/08VG)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe t t' u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)

/-- **`L_{X/T}` on the small étale site of `X`**: the cotangent complex of the transported
morphism, formed on the model, carried back by the Comparison Lemma. -/
abbrev spaceCotangentComplex : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ :=
  ((modelModulesEquiv B S hS X).inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (modelRingedToposHom f).cotangentComplex

/-- The cohomology sheaves of `L_{X/T}` on `X` are those of `L_{X/T}` on the model, carried
back. -/
def spaceCotangentComplexHomologyIso (i : ℤ) :
    (spaceCotangentComplex f).homology i ≅ (modelModulesEquiv B S hS X).inverse.obj
      ((modelRingedToposHom f).cotangentComplex.homology i) :=
  (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
    (modelModulesEquiv B S hS X).inverse (ComplexShape.up ℤ) i).app _

variable [HasDerivedCategory.{t} (Modules.{u, u} B S hS X.1 X.2)]
  [HasDerivedCategory.{t'} (modelModules X)]

/-- The Comparison Lemma carries `L_{X/T}` on `X` to `L_{X/T}` on the model. -/
def mapDerivedCategoryObjSpaceCotangentComplexIso :
    (modelModulesEquiv B S hS X).functor.mapDerivedCategory.obj
        (DerivedCategory.Q.obj (spaceCotangentComplex f)) ≅
      (modelRingedToposHom f).cotangentComplexDerived :=
  ((modelModulesEquiv B S hS X).functor.mapDerivedCategoryFactors).app _ ≪≫
    DerivedCategory.Q.mapIso (((modelModulesEquiv B S hS X).mapHomologicalComplex
      (ComplexShape.up ℤ)).counitIso.app (modelRingedToposHom f).cotangentComplex)

/-- **(G1) `L_{X/A}` lies in `D^-_{Coh}(𝒪_X)` for `X` locally of finite type over a Noetherian
ring `A`.** Let `f : X ⟶ T` be a morphism from an algebraic space to an object `T` of the big fppf
site with affine underlying scheme whose ring of global functions is Noetherian, `f` locally of
finite type. Then there is an object `E` of the derived category of `𝒪_X`-modules on the small
étale site of `X` which the Comparison Lemma carries to the cotangent complex `L_{X/T}` of
Stacks 08SU formed on the model, whose cohomology sheaves are coherent, and which is bounded
above. -/
theorem exists_isCoherent_homology_isBoundedAbove_cotangentComplexDerived
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) [IsNoetherianRing (baseRing B S hS T)] :
    ∃ (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
      (_ : (modelModulesEquiv B S hS X).functor.mapDerivedCategory.obj E ≅
        (modelRingedToposHom f).cotangentComplexDerived),
      (∀ q : ℤ, IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ q).obj E)) ∧
        DerivedCategoryB.IsBoundedAbove E := by
  let E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
    DerivedCategory.Q.obj (spaceCotangentComplex f)
  have hH : ∀ q : ℤ, (DerivedCategory.homologyFunctor _ q).obj E ≅
      (modelModulesEquiv B S hS X).inverse.obj
        ((modelRingedToposHom f).cotangentComplex.homology q) := fun q =>
    (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫ spaceCotangentComplexHomologyIso f q
  refine ⟨E, mapDerivedCategoryObjSpaceCotangentComplexIso f, fun q => ?_, ⟨0, fun n hn => ?_⟩⟩
  · exact (isCoherent B S hS X.1 X.2).prop_of_iso (hH q).symm
      (isCoherent_modelCotangentHomology f hf hT q)
  · exact IsZero.of_iso (Functor.map_isZero _ (ShortComplex.isZero_homology_of_isZero_X₂ _
      ((modelRingedToposHom f).cotangentComplex_isZero_pos n hn))) (hH n)

end AlgebraicGeometry.Space

end
