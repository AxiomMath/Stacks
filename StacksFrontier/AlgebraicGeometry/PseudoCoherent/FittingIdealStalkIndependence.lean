module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealLocalIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealStalkBasis

/-!
# The ideal of minors does not depend on the chosen finite free model

Let `U` be an affine open of a scheme `X`, let `E` be an object of `D(𝒪_X)` and let `M₁`, `M₂` be
bounded-above finite free models, over `U`, of complexes `K₁`, `K₂` both representing `E`. Then
`M₁` and `M₂` have the same ideal of minors in every degree and at every index. This is the
independence that the local description of [Stacks, Tag 0ESP] asserts, and the source's proof is
reproduced here: reduce to the local rings, and over a local ring appeal to
`Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_derivedIso`, which splits off trivial two-term
complexes and compares the resulting minimal complexes.

The reduction to local rings has three steps.

* **The stalk sees the comparison.** A model represents `K` only after restriction to `U`; but
  the stalk functor at a point `x` of `U` factors through that restriction
  (`Stacks.Duality.affineRestrictStalkNatIso`, read here as
  `AlgebraicGeometry.DerivedFreeModel.openStalkFunctorIso`), and the second factor is exact, so the
  factorization descends to the derived categories
  (`AlgebraicGeometry.DerivedFreeModel.qStalkRestrictIso`) and the stalk of the modelling complex
  is isomorphic in `D(𝒪_{X,x})` to the stalk of `K`
  (`AlgebraicGeometry.DerivedFreeModel.nonempty_stalkIso`).
* **The derived categories.** The stalk functor is exact, hence descends to the derived categories,
  and the descent commutes with the localization functor. Composing that with the identification of
  the stalk complex of a model with its base changed matrices
  (`AlgebraicGeometry.DerivedFreeModel.nonempty_stalkCochain_iso`) gives an isomorphism in
  `D(𝒪_{X,x})` of the two complexes of base changed matrices
  (`AlgebraicGeometry.DerivedFreeModel.nonempty_stalkCochain_derivedIso`), whence the two ideals of
  minors have the same image in `𝒪_{X,x}`
  (`AlgebraicGeometry.DerivedFreeModel.map_germ_fittingIdeal_eq`).
* **From the local rings back to `Γ(X, U)`.** Two ideals of a commutative ring are equal as soon as
  they have the same image in every localization at a maximal ideal
  (`Ideal.eq_of_localization_maximal`), and for `U` affine those localizations are the local rings
  of the points of `U`: a prime of `Γ(X, U)` is the prime of a point of `U`
  (`AlgebraicGeometry.IsAffineOpen.fromSpec`, `AlgebraicGeometry.IsAffineOpen.range_fromSpec`) and
  `𝒪_{X,x}` is the localization there through the germ map
  (`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk'`). This is
  `AlgebraicGeometry.DerivedFreeModel.fittingIdeal_eq_of_isAffineOpen`.

## Main results

* `AlgebraicGeometry.DerivedFreeModel.nonempty_stalkIso`: the stalk at a point of `U` of the
  modelling complex of a model is isomorphic, in `D(𝒪_{X,x})`, to the stalk of the complex it
  models.
* `AlgebraicGeometry.DerivedFreeModel.nonempty_stalkCochain_derivedIso`: the two complexes of base
  changed matrices are isomorphic in `D(𝒪_{X,x})`.
* `AlgebraicGeometry.DerivedFreeModel.map_germ_fittingIdeal_eq`: their ideals of minors agree in
  every local ring of a point of `U`.
* `AlgebraicGeometry.DerivedFreeModel.fittingIdeal_eq_of_isAffineOpen`: **hence they agree in
  `Γ(X, U)`**, for `U` affine.

## Implementation notes

The derived category of `𝒪_{X,x}`-modules is taken at `CategoryTheory.HasDerivedCategory.standard`,
as a local instance, exactly as in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DerivedStalkModel.lean`; the derived
category of `𝒪_X`-modules remains an instance argument, as in
`AlgebraicGeometry.fittingIdealSheafOfDerivedModels`.

`AlgebraicGeometry.DerivedFreeModel.openStalkFunctor` names the composite of the stalk functor of
`U` with the restriction of scalars along the stalk map of `U.ι`, so that its exactness can be
recorded as instances on one head symbol: instance search does not see those instances through the
composite, the two spellings of the point of `U` and of its local ring being identified only up to
unfolding.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u w

namespace AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace DerivedFreeModel

variable {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ} {U : X.Opens}

/-- The stalk at a point `x` of `U` of an `𝒪_U`-module, read over `𝒪_{X,x}` through the stalk map
of the inclusion of `U`. This is the second factor of the presentation
`Stacks.Duality.affineRestrictStalkNatIso` of the stalk functor at a point of `U`. -/
def openStalkFunctor (U : X.Opens) (x : X) (hx : x ∈ U) :
    U.toScheme.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  Stacks.Duality.modulesStalkFunctor (Z := U.toScheme) ⟨x, hx⟩ ⋙
    ModuleCat.restrictScalars.{u} (Stacks.Duality.affineStalkMap x hx).hom

/-- The functor `AlgebraicGeometry.DerivedFreeModel.openStalkFunctor U x hx` is additive. -/
instance openStalkFunctor_additive (U : X.Opens) (x : X) (hx : x ∈ U) :
    (openStalkFunctor U x hx).Additive := by
  have : (Stacks.Duality.modulesStalkFunctor (Z := U.toScheme) ⟨x, hx⟩).Additive :=
    Stacks.Duality.modulesStalkFunctor_additive (Z := U.toScheme) ⟨x, hx⟩
  exact inferInstanceAs ((Stacks.Duality.modulesStalkFunctor (Z := U.toScheme) ⟨x, hx⟩ ⋙
    ModuleCat.restrictScalars.{u} (Stacks.Duality.affineStalkMap x hx).hom).Additive)

/-- The functor `AlgebraicGeometry.DerivedFreeModel.openStalkFunctor U x hx` is left exact. -/
instance openStalkFunctor_preservesFiniteLimits (U : X.Opens) (x : X) (hx : x ∈ U) :
    PreservesFiniteLimits (openStalkFunctor U x hx) := by
  have : PreservesFiniteLimits (Stacks.Duality.modulesStalkFunctor (Z := U.toScheme) ⟨x, hx⟩) :=
    Stacks.Duality.modulesStalkFunctor_preservesFiniteLimits (Z := U.toScheme) ⟨x, hx⟩
  exact comp_preservesFiniteLimits _ _

/-- The functor `AlgebraicGeometry.DerivedFreeModel.openStalkFunctor U x hx` is right exact. -/
instance openStalkFunctor_preservesFiniteColimits (U : X.Opens) (x : X) (hx : x ∈ U) :
    PreservesFiniteColimits (openStalkFunctor U x hx) := by
  have : PreservesFiniteColimits
      (Stacks.Duality.modulesStalkFunctor (Z := U.toScheme) ⟨x, hx⟩) :=
    Stacks.Duality.modulesStalkFunctor_preservesFiniteColimits (Z := U.toScheme) ⟨x, hx⟩
  exact comp_preservesFiniteColimits _ _

/-- **The stalk functor at a point `x` of `U` factors through the restriction to `U`.** This is
`Stacks.Duality.affineRestrictStalkNatIso`, read with the second factor named. -/
def openStalkFunctorIso (U : X.Opens) (x : X) (hx : x ∈ U) :
    Scheme.Modules.restrictFunctor U.ι ⋙ openStalkFunctor U x hx ≅
      Stacks.Duality.modulesStalkFunctor x :=
  Stacks.Duality.affineRestrictStalkNatIso x hx

/-- **The complex of stalk modules at a point of `U`, computed through the restriction to `U`, is
the complex of stalk modules.** This is `Stacks.Duality.affineRestrictStalkNatIso` applied
degreewise. -/
def stalkRestrictComplexIso (U : X.Opens) (x : X) (hx : x ∈ U) (C : CochainComplex X.Modules ℤ) :
    ((openStalkFunctor U x hx).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C) ≅
      ((Stacks.Duality.modulesStalkFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)).obj C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (openStalkFunctorIso U x hx).app (C.X i))
    (fun i j _ => ((openStalkFunctorIso U x hx).hom.naturality (C.d i j)).symm)

/-- **The stalk complex at a point of `U`, computed from the restriction to `U`.** -/
def qStalkRestrictIso (U : X.Opens) (x : X) (hx : x ∈ U) (C : CochainComplex X.Modules ℤ) :
    letI := HasDerivedCategory.standard (U.toScheme).Modules
    DerivedCategory.Q.obj
        (((Stacks.Duality.modulesStalkFunctor x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C) ≅
      (openStalkFunctor U x hx).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (Scheme.Modules.restrictComplex C U)) :=
  letI := HasDerivedCategory.standard (U.toScheme).Modules
  DerivedCategory.Q.mapIso (stalkRestrictComplexIso U x hx C).symm ≪≫
    ((openStalkFunctor U x hx).mapDerivedCategoryFactors.app
      (Scheme.Modules.restrictComplex C U)).symm

/-- **The stalk at a point of `U` of the modelling complex of a finite free model is isomorphic,
in `D(𝒪_{X,x})`, to the stalk of the complex it models.** -/
theorem nonempty_stalkIso (M : DerivedFreeModel K U) {x : X} (hx : x ∈ U) :
    Nonempty (DerivedCategory.Q.obj
        (((Stacks.Duality.modulesStalkFunctor x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M.model) ≅
      DerivedCategory.Q.obj
        (((Stacks.Duality.modulesStalkFunctor x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) := by
  let := HasDerivedCategory.standard (U.toScheme).Modules
  obtain ⟨e⟩ := M.derivedIso
  exact ⟨qStalkRestrictIso U x hx M.model ≪≫
    (openStalkFunctor U x hx).mapDerivedCategory.mapIso e ≪≫
    (qStalkRestrictIso U x hx K).symm⟩


section Derived

variable [HasDerivedCategory.{w} X.Modules]

/-- **The complexes of stalk modules of two finite free models, over `U`, of complexes
representing the same object of `D(𝒪_X)` are isomorphic in `D(𝒪_{X,x})`** at every point `x` of
`U`. -/
theorem nonempty_stalkCochain_derivedIso (E : DerivedCategory X.Modules)
    {K₁ K₂ : CochainComplex X.Modules ℤ} (h₁ : DerivedCategory.Q.obj K₁ ≅ E)
    (h₂ : DerivedCategory.Q.obj K₂ ≅ E) (M₁ : DerivedFreeModel K₁ U) (M₂ : DerivedFreeModel K₂ U)
    {x : X} (hx : x ∈ U) :
    Nonempty (DerivedCategory.Q.obj ((M₁.stalkFreeData hx).toCochain (M₁.stalkFreeData_dd hx)) ≅
      DerivedCategory.Q.obj ((M₂.stalkFreeData hx).toCochain (M₂.stalkFreeData_dd hx))) := by
  obtain ⟨e₁⟩ := M₁.nonempty_stalkCochain_iso hx
  obtain ⟨e₂⟩ := M₂.nonempty_stalkCochain_iso hx
  obtain ⟨s₁⟩ := M₁.nonempty_stalkIso hx
  obtain ⟨s₂⟩ := M₂.nonempty_stalkIso hx
  exact ⟨DerivedCategory.Q.mapIso e₁.symm ≪≫ s₁ ≪≫
    ((Stacks.Duality.modulesStalkFunctor x).mapDerivedCategoryFactors.app K₁).symm ≪≫
    (Stacks.Duality.modulesStalkFunctor x).mapDerivedCategory.mapIso (h₁ ≪≫ h₂.symm) ≪≫
    (Stacks.Duality.modulesStalkFunctor x).mapDerivedCategoryFactors.app K₂ ≪≫
    s₂.symm ≪≫ DerivedCategory.Q.mapIso e₂⟩

/-- **The ideals of minors of two finite free models over `U` of complexes representing the same
object of `D(𝒪_X)` agree in every local ring of a point of `U`.** -/
theorem map_germ_fittingIdeal_eq (E : DerivedCategory X.Modules)
    {K₁ K₂ : CochainComplex X.Modules ℤ} (h₁ : DerivedCategory.Q.obj K₁ ≅ E)
    (h₂ : DerivedCategory.Q.obj K₂ ≅ E) (M₁ : DerivedFreeModel K₁ U) (M₂ : DerivedFreeModel K₂ U)
    {x : X} (hx : x ∈ U) (p k : ℤ) :
    Ideal.map (X.presheaf.germ U x hx).hom (M₁.fittingIdeal p k) =
      Ideal.map (X.presheaf.germ U x hx).hom (M₂.fittingIdeal p k) := by
  obtain ⟨e⟩ := nonempty_stalkCochain_derivedIso E h₁ h₂ M₁ M₂ hx
  rw [← M₁.stalkFreeData_fittingIdeal hx, ← M₂.stalkFreeData_fittingIdeal hx]
  exact Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_derivedIso
    (M₁.stalkFreeData_dd hx) (M₂.stalkFreeData_dd hx) e p k


/-- **The ideal of minors of a finite free model over an affine open does not depend on the model
nor on the representing complex.** -/
theorem fittingIdeal_eq_of_isAffineOpen (hU : IsAffineOpen U) (E : DerivedCategory X.Modules)
    {K₁ K₂ : CochainComplex X.Modules ℤ} (h₁ : DerivedCategory.Q.obj K₁ ≅ E)
    (h₂ : DerivedCategory.Q.obj K₂ ≅ E) (M₁ : DerivedFreeModel K₁ U) (M₂ : DerivedFreeModel K₂ U)
    (p k : ℤ) : M₁.fittingIdeal p k = M₂.fittingIdeal p k := by
  refine Ideal.eq_of_localization_maximal fun P hP => ?_
  have hmem : hU.fromSpec ⟨P, hP.isPrime⟩ ∈ U := by
    have h := Set.mem_range_self (f := ⇑hU.fromSpec)
      (⟨P, hP.isPrime⟩ : PrimeSpectrum Γ(X, U))
    rw [hU.range_fromSpec] at h
    exact h
  let : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) :=
    X.presheaf.algebra_section_stalk (U := U) ⟨hU.fromSpec ⟨P, hP.isPrime⟩, hmem⟩
  have : IsLocalization P.primeCompl (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) :=
    hU.isLocalization_stalk' ⟨P, hP.isPrime⟩ hmem
  have halg : algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) =
      (X.presheaf.germ U (hU.fromSpec ⟨P, hP.isPrime⟩) hmem).hom :=
    TopCat.Presheaf.stalk_open_algebraMap X.presheaf
      (⟨hU.fromSpec ⟨P, hP.isPrime⟩, hmem⟩ : U)
  have hcomm : ∀ I : Ideal Γ(X, U),
      Ideal.map (algebraMap Γ(X, U) (Localization.AtPrime P)) I =
        Ideal.map (IsLocalization.algEquiv P.primeCompl
            (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩))
            (Localization.AtPrime P)).toAlgHom.toRingHom
          (Ideal.map (X.presheaf.germ U (hU.fromSpec ⟨P, hP.isPrime⟩) hmem).hom I) := by
    intro I
    rw [Ideal.map_map]
    refine congrArg (fun φ : Γ(X, U) →+* Localization.AtPrime P => Ideal.map φ I) ?_
    refine RingHom.ext fun a => ?_
    have he := (IsLocalization.algEquiv P.primeCompl
      (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) (Localization.AtPrime P)).commutes a
    rw [halg] at he
    exact he.symm
  rw [hcomm, hcomm, map_germ_fittingIdeal_eq E h₁ h₂ M₁ M₂ hmem p k]

end Derived

end DerivedFreeModel

end

end AlgebraicGeometry

end
