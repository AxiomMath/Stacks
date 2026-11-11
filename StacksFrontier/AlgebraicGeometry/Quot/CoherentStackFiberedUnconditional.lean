module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFinitePresentationStability

/-!
# The category of coherent sheaves with proper support is fibred in groupoids

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over a scheme `S` of a big
fppf site, the standing data of Stacks 08KB.  Stacks 08W5 asserts that the projection
`p : Coh_{X/Y} ⟶ (Sch/S)_fppf`, which sends an object `(T, g, F)` to its test scheme `T`, is
fibred in groupoids.

The lift of a morphism of test schemes is the pullback of the module of an object of
`Coh_{X/Y}`, which is of finite presentation; the base-change stability of modules of finite
presentation it needs is `AlgebraicGeometry.Space.modulePullbackStabilityOfFinitePresentation`.
The category structure on the objects is a parameter.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.pullbackObject'` and
  `AlgebraicGeometry.Space.CoherentSituation.pullbackHom'`: the pullback of an object of
  `Coh_{X/Y}` along a morphism of test schemes, and the morphism to that object.

## Main results

* `AlgebraicGeometry.Space.coherentProjection_isFiberedInGroupoids_schemesOver'`: the projection
  of `Coh_{X/Y}` to the test schemes over `Y` is fibred in groupoids.
* `AlgebraicGeometry.Space.coherentProjection_isFiberedInGroupoids'`: the assertion of
  Stacks 08W5 for any value of `AlgebraicGeometry.Space.CoherentCategoryData`; Stacks 08W5 at the
  constructed category is
  `AlgebraicGeometry.Space.CoherentSituation.projection_isFiberedInGroupoids`.

## Implementation notes

The primed names are the counterparts of the correspondingly named declarations of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackFibered.lean`, with
`AlgebraicGeometry.Space.ModulePullbackStabilityOfFinitePresentation` in place of
`AlgebraicGeometry.Space.ModulePullbackStability`.

The pullback of an object takes the base-change stability as an argument, and the two statements
of Stacks 08W5 supply it, so neither carries it as a hypothesis. Quasi-coherence and finite type
of the pulled-back module are deduced from its finite presentation.

## References

* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
* [Stacks Project, Tag 09WW](https://stacks.math.columbia.edu/tag/09WW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable {D : CoherentSituation B S hS}

/-! ### The pullback of an object along a morphism of test schemes -/

/-- The pullback of an object of `Coh_{X/Y}` along a morphism `h : V ⟶ T` of test schemes over
`Y`: the test scheme `V`, with the inverse image of the module along the induced morphism
`X_h : X_V ⟶ X_T` of base changes. -/
def pullbackObject' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (A : CoherentObject D) {V : SchemesOver D.Y} (h : V ⟶ A.T) : CoherentObject D where
  T := V
  F := (modulePullback B S hS (D.relativeMap h)).obj A.F
  finitePresentation := hst.finitePresentation (D.relativeMap h) A.F A.finitePresentation
  quasicoherent :=
    haveI := hst.finitePresentation (D.relativeMap h) A.F A.finitePresentation
    inferInstance
  flat := hst.flat (isPullback_baseChangeMap D.f h) A.F A.finitePresentation A.flat
  properSupport := by
    obtain ⟨hp, hU, hproper⟩ := A.properSupport
    have := A.finitePresentation
    obtain ⟨hU', hproper'⟩ := hst.properSupport (isPullback_baseChangeMap D.f h) hp A.F
      A.quasicoherent inferInstance hU hproper
    exact ⟨(isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_baseChangeMap D.f h) hp, hU', hproper'⟩

/-- The test scheme of the pullback of an object is the source of the given morphism of test
schemes. -/
@[simp]
theorem pullbackObject_T' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (A : CoherentObject D) {V : SchemesOver D.Y} (h : V ⟶ A.T) :
    (pullbackObject' hst A h).T = V :=
  rfl

/-- The morphism of `Coh_{X/Y}` from the pullback of an object to that object: the given
morphism of test schemes, with the identity as its comparison of modules. -/
def pullbackHom' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (A : CoherentObject D) {V : SchemesOver D.Y} (h : V ⟶ A.T) :
    CoherentHom (pullbackObject' hst A h) A where
  base := h
  fibre := 𝟙 ((modulePullback B S hS (D.relativeMap h)).obj A.F)
  isIso_fibre := IsIso.id _

/-- The base map of the morphism from the pullback of an object is the given morphism of test
schemes. -/
@[simp]
theorem pullbackHom_base' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (A : CoherentObject D) {V : SchemesOver D.Y} (h : V ⟶ A.T) :
    (pullbackHom' hst A h).base = h :=
  rfl

end CoherentSituation

/-! ### The projection to the test schemes over the base -/

/-- **The projection of `Coh_{X/Y}` to the test schemes over `Y` is fibred in groupoids.**

The category structure on the objects, its projection, and the identification of both with the
ones of Stacks 08KB are `cd`; the coherences of Stacks 03LU for the inverse images are `hc`. -/
theorem coherentProjection_isFiberedInGroupoids_schemesOver'
    (hc : ModulePushforwardCoherence B S hS) {D : CoherentSituation B S hS}
    (cd : CoherentCategoryData hc D) :
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    cd.projection.IsFiberedInGroupoids := by
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  have hst := modulePullbackStabilityOfFinitePresentation B S hS
  have key : ∀ {A A' : CoherentObject D} (m : A ⟶ A'),
      ((Equiv.cast (cd.hom_type A A')) m).base =
        eqToHom (cd.projection_obj A).symm ≫ cd.projection.map m ≫
          eqToHom (cd.projection_obj A') := by
    intro A A' m
    rw [cd.projection_map m]
    simp
  constructor
  · intro V U f x hx
    generalize hg : f ≫ eqToHom (hx.symm.trans (cd.projection_obj x)) = g
    refine ⟨CoherentSituation.pullbackObject' hst x g,
      (Equiv.cast (cd.hom_type _ _)).symm (CoherentSituation.pullbackHom' hst x g),
      IsHomLift.of_fac' cd.projection f _ (cd.projection_obj _) hx ?_⟩
    rw [cd.projection_map, Equiv.apply_symm_apply, CoherentSituation.pullbackHom_base', ← hg]
    simp only [CoherentSituation.pullbackObject_T', Category.assoc, eqToHom_trans]
  · intro x y z φ ψ f hf
    generalize hΦ : Equiv.cast (cd.hom_type y x) φ = Φ
    generalize hΨ : Equiv.cast (cd.hom_type z x) ψ = Ψ
    generalize hβ : eqToHom (cd.projection_obj z).symm ≫ f ≫ eqToHom (cd.projection_obj y) = β
    have hbase : β ≫ Φ.base = Ψ.base := by
      rw [← hΦ, ← hΨ, ← hβ, key φ, key ψ, ← hf]
      simp
    obtain ⟨Ψb, Ψf, Ψi⟩ := Ψ
    obtain rfl : β ≫ Φ.base = Ψb := hbase
    refine ⟨(Equiv.cast (cd.hom_type z y)).symm
      (CoherentSituation.fillIn Φ β Ψf), ⟨?_, ?_⟩, ?_⟩
    · rw [cd.projection_map, Equiv.apply_symm_apply, CoherentSituation.fillIn_base, ← hβ]
      simp
    · refine (Equiv.cast (cd.hom_type z x)).injective ?_
      rw [cd.composition, Equiv.apply_symm_apply, hΦ, hΨ]
      exact CoherentSituation.fillIn_comp Φ β Ψf Ψi
    · intro χ hχ
      refine (Equiv.cast (cd.hom_type z y)).injective ?_
      rw [Equiv.apply_symm_apply]
      refine CoherentSituation.eq_fillIn Φ β Ψf Ψi ?_ ?_
      · rw [key χ, hχ.1, hβ]
      · have h₂ := cd.composition χ φ
        rw [hχ.2, hΦ, hΨ] at h₂
        exact h₂.symm

/-! ### Stacks 08W5 -/

/-- In the situation of Stacks 08KB the projection `p : Coh_{X/Y} ⟶ (Sch/S)_fppf`, which sends
an object `(T, g, F)` to its test scheme `T`, is fibred in groupoids, for any value `cd` of the
specification `AlgebraicGeometry.Space.CoherentCategoryData` of the category of Stacks 08KB.

Stacks 08W5 at the constructed category
`AlgebraicGeometry.Space.CoherentSituation.categoryData` is
`AlgebraicGeometry.Space.CoherentSituation.projection_isFiberedInGroupoids`. -/
theorem coherentProjection_isFiberedInGroupoids'
    (hc : ModulePushforwardCoherence B S hS) {D : CoherentSituation B S hS}
    (cd : CoherentCategoryData hc D) :
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    Functor.IsFiberedInGroupoids
      (cd.projection ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y) :=
  let : Category.{u + 1} (CoherentObject D) := cd.category
  Functor.IsFiberedInGroupoids.comp cd.projection
    (CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y)
    (coherentProjection_isFiberedInGroupoids_schemesOver' hc cd)
    (Functor.IsFiberedInGroupoids.costructuredArrow_proj (schemeSpaceFunctor B S hS) D.Y)

end AlgebraicGeometry.Space

end
