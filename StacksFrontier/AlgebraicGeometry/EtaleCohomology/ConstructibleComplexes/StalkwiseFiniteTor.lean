module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatIsFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Stalks
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.RingTheory.RingHom.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally finite Tor dimension read at the stalks

A complex `E` of modules on a ringed site locally has finite Tor dimension, in the sense of
[Stacks, Tag 08FZ] (3), as soon as every object of the site carries a covering on each member
`V` of which one interval bounds the Tor amplitudes of the derived stalks of `E|_V` at the
points of a conservative family of the slice over `V`. This file proves that, and supplies such
conservative families on the slices of a small étale site, relative to universes above that of
the scheme.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_stalkwise`: if
  every object of the site carries a covering on each member `V` of which one interval `[a, b]`
  contains the Tor amplitude of the derived stalk of `E|_V` at every point of the slice over
  `V`, then `E` locally has finite Tor dimension.
* `Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_stalkwise_family`:
  the same with the bound on each member of the covering asked for only at the members of one
  given conservative family of points of the slice over it.
* `AlgebraicGeometry.SmallEtale.hasEnoughPoints_ulift` and
  `AlgebraicGeometry.SmallEtale.hasConservativeFamily_over`: the small étale site, and each of
  its slices, has enough points relative to any universe above the universe of the scheme.
* `AlgebraicGeometry.isConservativeFamilyOfPoints_uliftGeometricSitePoint_over`: the lifts
  `Φ.over x` of the universe lifts of the geometric points form a conservative family of points
  of each slice of the small étale site.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso₃`,
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso₄` and
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso₅`: the descent to derived
  categories of a composite of three, four or five exact functors, read at an object, is the
  descents applied in turn.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso₅₄`: a natural isomorphism
  between a five-fold and a four-fold composite of exact functors, read on the derived
  categories at an object.
* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_of_restrictScalars_iso`: two objects over
  two rings each identified with `Λ` have the same Tor amplitude as soon as they become
  isomorphic in `D(Λ)`.
* `AlgebraicGeometry.uliftPointPresheafFiberNatIso`: the fibre at the universe lift of a point
  is the uplift of the fibre, naturally in the presheaf.
* `AlgebraicGeometry.smallEtalePullbackUpliftedEtaleFiberNatIso`: the ulifted fibre at the
  universe lift of a geometric point of `X` of the inverse image along `f : X ⟶ Y` is the
  ulifted fibre at the universe lift of the image geometric point, naturally in the sheaf.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w r d z tt rr ww uC vC zq wq

/-! ### The descent of a composite of several exact functors, read at an object -/

namespace Stacks.DerivedCategoryComparisons

section Factors

universe d₁ d₂ d₃ d₄ d₅ d₆ e₂ e₃ e₄

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {A₁ : Type*} [Category A₁] [Abelian A₁] [HasDerivedCategory.{d₁} A₁]
  {A₂ : Type*} [Category A₂] [Abelian A₂] [HasDerivedCategory.{d₂} A₂]
  {A₃ : Type*} [Category A₃] [Abelian A₃] [HasDerivedCategory.{d₃} A₃]
  {A₄ : Type*} [Category A₄] [Abelian A₄] [HasDerivedCategory.{d₄} A₄]
  {A₅ : Type*} [Category A₅] [Abelian A₅] [HasDerivedCategory.{d₅} A₅]
  {A₆ : Type*} [Category A₆] [Abelian A₆] [HasDerivedCategory.{d₆} A₆]

/-- The descent to derived categories of a composite of three exact functors, read at an
object, is the three descents applied in turn. -/
public def mapDerivedCategoryCompIso₃ (F₁ : A₁ ⥤ A₂) (F₂ : A₂ ⥤ A₃) (F₃ : A₃ ⥤ A₄)
    [hF₁ : F₁.Additive] [hlF₁ : PreservesFiniteLimits F₁]
    [hcF₁ : PreservesFiniteColimits F₁]
    [hF₂ : F₂.Additive] [hlF₂ : PreservesFiniteLimits F₂]
    [hcF₂ : PreservesFiniteColimits F₂]
    [hF₃ : F₃.Additive] [hlF₃ : PreservesFiniteLimits F₃]
    [hcF₃ : PreservesFiniteColimits F₃]
    (E : DerivedCategory A₁) :
    (F₁ ⋙ F₂ ⋙ F₃).mapDerivedCategory.obj E ≅
      F₃.mapDerivedCategory.obj
        (F₂.mapDerivedCategory.obj (F₁.mapDerivedCategory.obj E)) :=
  (mapDerivedCategoryCompIso F₁ (F₂ ⋙ F₃)).app E ≪≫
    (mapDerivedCategoryCompIso F₂ F₃).app (F₁.mapDerivedCategory.obj E)

/-- The descent to derived categories of a composite of four exact functors, read at an
object, is the four descents applied in turn. -/
public def mapDerivedCategoryCompIso₄ (F₁ : A₁ ⥤ A₂) (F₂ : A₂ ⥤ A₃) (F₃ : A₃ ⥤ A₄)
    (F₄ : A₄ ⥤ A₅)
    [hF₁ : F₁.Additive] [hlF₁ : PreservesFiniteLimits F₁]
    [hcF₁ : PreservesFiniteColimits F₁]
    [hF₂ : F₂.Additive] [hlF₂ : PreservesFiniteLimits F₂]
    [hcF₂ : PreservesFiniteColimits F₂]
    [hF₃ : F₃.Additive] [hlF₃ : PreservesFiniteLimits F₃]
    [hcF₃ : PreservesFiniteColimits F₃]
    [hF₄ : F₄.Additive] [hlF₄ : PreservesFiniteLimits F₄]
    [hcF₄ : PreservesFiniteColimits F₄]
    (E : DerivedCategory A₁) :
    (F₁ ⋙ F₂ ⋙ F₃ ⋙ F₄).mapDerivedCategory.obj E ≅
      F₄.mapDerivedCategory.obj (F₃.mapDerivedCategory.obj
        (F₂.mapDerivedCategory.obj (F₁.mapDerivedCategory.obj E))) :=
  (mapDerivedCategoryCompIso F₁ (F₂ ⋙ F₃ ⋙ F₄)).app E ≪≫
    mapDerivedCategoryCompIso₃ F₂ F₃ F₄ (F₁.mapDerivedCategory.obj E)

/-- The descent to derived categories of a composite of five exact functors, read at an
object, is the five descents applied in turn. -/
public def mapDerivedCategoryCompIso₅ (F₁ : A₁ ⥤ A₂) (F₂ : A₂ ⥤ A₃) (F₃ : A₃ ⥤ A₄)
    (F₄ : A₄ ⥤ A₅) (F₅ : A₅ ⥤ A₆)
    [hF₁ : F₁.Additive] [hlF₁ : PreservesFiniteLimits F₁]
    [hcF₁ : PreservesFiniteColimits F₁]
    [hF₂ : F₂.Additive] [hlF₂ : PreservesFiniteLimits F₂]
    [hcF₂ : PreservesFiniteColimits F₂]
    [hF₃ : F₃.Additive] [hlF₃ : PreservesFiniteLimits F₃]
    [hcF₃ : PreservesFiniteColimits F₃]
    [hF₄ : F₄.Additive] [hlF₄ : PreservesFiniteLimits F₄]
    [hcF₄ : PreservesFiniteColimits F₄]
    [hF₅ : F₅.Additive] [hlF₅ : PreservesFiniteLimits F₅]
    [hcF₅ : PreservesFiniteColimits F₅]
    (E : DerivedCategory A₁) :
    (F₁ ⋙ F₂ ⋙ F₃ ⋙ F₄ ⋙ F₅).mapDerivedCategory.obj E ≅
      F₅.mapDerivedCategory.obj (F₄.mapDerivedCategory.obj (F₃.mapDerivedCategory.obj
        (F₂.mapDerivedCategory.obj (F₁.mapDerivedCategory.obj E)))) :=
  (mapDerivedCategoryCompIso F₁ (F₂ ⋙ F₃ ⋙ F₄ ⋙ F₅)).app E ≪≫
    mapDerivedCategoryCompIso₄ F₂ F₃ F₄ F₅ (F₁.mapDerivedCategory.obj E)

variable {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{e₂} C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory.{e₃} C₃]
  {C₄ : Type*} [Category C₄] [Abelian C₄] [HasDerivedCategory.{e₄} C₄]

/-- A chain of five and a chain of four exact functors with isomorphic composites have
isomorphic iterated descents, read at an object of the derived category of their common
source. -/
public def mapDerivedCategoryCompIso₅₄ (F₁ : A₁ ⥤ A₂) (F₂ : A₂ ⥤ A₃) (F₃ : A₃ ⥤ A₄)
    (F₄ : A₄ ⥤ A₅) (F₅ : A₅ ⥤ A₆) (G₁ : A₁ ⥤ C₂) (G₂ : C₂ ⥤ C₃) (G₃ : C₃ ⥤ C₄) (G₄ : C₄ ⥤ A₆)
    [hF₁ : F₁.Additive] [hlF₁ : PreservesFiniteLimits F₁]
    [hcF₁ : PreservesFiniteColimits F₁]
    [hF₂ : F₂.Additive] [hlF₂ : PreservesFiniteLimits F₂]
    [hcF₂ : PreservesFiniteColimits F₂]
    [hF₃ : F₃.Additive] [hlF₃ : PreservesFiniteLimits F₃]
    [hcF₃ : PreservesFiniteColimits F₃]
    [hF₄ : F₄.Additive] [hlF₄ : PreservesFiniteLimits F₄]
    [hcF₄ : PreservesFiniteColimits F₄]
    [hF₅ : F₅.Additive] [hlF₅ : PreservesFiniteLimits F₅]
    [hcF₅ : PreservesFiniteColimits F₅]
    [hG₁ : G₁.Additive] [hlG₁ : PreservesFiniteLimits G₁]
    [hcG₁ : PreservesFiniteColimits G₁]
    [hG₂ : G₂.Additive] [hlG₂ : PreservesFiniteLimits G₂]
    [hcG₂ : PreservesFiniteColimits G₂]
    [hG₃ : G₃.Additive] [hlG₃ : PreservesFiniteLimits G₃]
    [hcG₃ : PreservesFiniteColimits G₃]
    [hG₄ : G₄.Additive] [hlG₄ : PreservesFiniteLimits G₄]
    [hcG₄ : PreservesFiniteColimits G₄]
    (e : F₁ ⋙ F₂ ⋙ F₃ ⋙ F₄ ⋙ F₅ ≅ G₁ ⋙ G₂ ⋙ G₃ ⋙ G₄) (E : DerivedCategory A₁) :
    F₅.mapDerivedCategory.obj (F₄.mapDerivedCategory.obj (F₃.mapDerivedCategory.obj
        (F₂.mapDerivedCategory.obj (F₁.mapDerivedCategory.obj E)))) ≅
      G₄.mapDerivedCategory.obj (G₃.mapDerivedCategory.obj
        (G₂.mapDerivedCategory.obj (G₁.mapDerivedCategory.obj E))) :=
  (mapDerivedCategoryCompIso₅ F₁ F₂ F₃ F₄ F₅ E).symm ≪≫
    (mapDerivedCategoryIsoOfNatIso _ _ e).app E ≪≫
    mapDerivedCategoryCompIso₄ G₁ G₂ G₃ G₄ E

/-- For a chain of five exact functors whose composite is isomorphic to a composite of two, the
five descents applied in turn are the descent of the composite of the two, read at an object
of the derived category of their common source. -/
public def mapDerivedCategoryCompIso₅₂ (F₁ : A₁ ⥤ A₂) (F₂ : A₂ ⥤ A₃) (F₃ : A₃ ⥤ A₄)
    (F₄ : A₄ ⥤ A₅) (F₅ : A₅ ⥤ A₆) (G₁ : A₁ ⥤ C₂) (G₂ : C₂ ⥤ A₆)
    [hF₁ : F₁.Additive] [hlF₁ : PreservesFiniteLimits F₁]
    [hcF₁ : PreservesFiniteColimits F₁]
    [hF₂ : F₂.Additive] [hlF₂ : PreservesFiniteLimits F₂]
    [hcF₂ : PreservesFiniteColimits F₂]
    [hF₃ : F₃.Additive] [hlF₃ : PreservesFiniteLimits F₃]
    [hcF₃ : PreservesFiniteColimits F₃]
    [hF₄ : F₄.Additive] [hlF₄ : PreservesFiniteLimits F₄]
    [hcF₄ : PreservesFiniteColimits F₄]
    [hF₅ : F₅.Additive] [hlF₅ : PreservesFiniteLimits F₅]
    [hcF₅ : PreservesFiniteColimits F₅]
    [hG₁ : G₁.Additive] [hlG₁ : PreservesFiniteLimits G₁]
    [hcG₁ : PreservesFiniteColimits G₁]
    [hG₂ : G₂.Additive] [hlG₂ : PreservesFiniteLimits G₂]
    [hcG₂ : PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ⋙ F₃ ⋙ F₄ ⋙ F₅ ≅ G₁ ⋙ G₂) (E : DerivedCategory A₁) :
    F₅.mapDerivedCategory.obj (F₄.mapDerivedCategory.obj (F₃.mapDerivedCategory.obj
        (F₂.mapDerivedCategory.obj (F₁.mapDerivedCategory.obj E)))) ≅
      (G₁ ⋙ G₂).mapDerivedCategory.obj E :=
  (mapDerivedCategoryCompIso₅ F₁ F₂ F₃ F₄ F₅ E).symm ≪≫
    (mapDerivedCategoryIsoOfNatIso _ _ e).app E

/-- For a chain of four exact functors whose composite is isomorphic to one exact functor `G`,
the four descents applied in turn are the descent of `G`, read at an object of the derived
category of their common source. -/
public def mapDerivedCategoryCompIso₄₁ (F₁ : A₁ ⥤ A₂) (F₂ : A₂ ⥤ A₃) (F₃ : A₃ ⥤ A₄)
    (F₄ : A₄ ⥤ A₅) (G : A₁ ⥤ A₅)
    [hF₁ : F₁.Additive] [hlF₁ : PreservesFiniteLimits F₁]
    [hcF₁ : PreservesFiniteColimits F₁]
    [hF₂ : F₂.Additive] [hlF₂ : PreservesFiniteLimits F₂]
    [hcF₂ : PreservesFiniteColimits F₂]
    [hF₃ : F₃.Additive] [hlF₃ : PreservesFiniteLimits F₃]
    [hcF₃ : PreservesFiniteColimits F₃]
    [hF₄ : F₄.Additive] [hlF₄ : PreservesFiniteLimits F₄]
    [hcF₄ : PreservesFiniteColimits F₄]
    [hG : G.Additive] [hlG : PreservesFiniteLimits G] [hcG : PreservesFiniteColimits G]
    (e : F₁ ⋙ F₂ ⋙ F₃ ⋙ F₄ ≅ G) (E : DerivedCategory A₁) :
    F₄.mapDerivedCategory.obj (F₃.mapDerivedCategory.obj
        (F₂.mapDerivedCategory.obj (F₁.mapDerivedCategory.obj E))) ≅
      G.mapDerivedCategory.obj E :=
  (mapDerivedCategoryCompIso₄ F₁ F₂ F₃ F₄ E).symm ≪≫
    (mapDerivedCategoryIsoOfNatIso _ _ e).app E

end Factors

end Stacks.DerivedCategoryComparisons

/-! ### Tor amplitude across an isomorphism of the coefficient ring -/

namespace StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

/-- Flatness is preserved by restriction of scalars along a ring isomorphism. -/
public lemma flat_restrictScalars_of_ringEquiv {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] (e : R ≃+* S) (M : ModuleCat.{max u v w} S) [Module.Flat S M] :
    Module.Flat R ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let := e.toRingHom.toAlgebra
  let : Module.Flat R S := RingHom.Flat.of_bijective e.bijective
  let : Module R M := Module.compHom M e.toRingHom
  let : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
  exact Module.Flat.trans R S M

/-- Restriction of scalars along a ring isomorphism sends a complex of flat modules concentrated
in `[a, b]` to one, which then represents its class in the derived category. -/
private lemma hasFlatRepresentative_restrictScalars_complex {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : R ≃+* S) (E : CochainComplex (ModuleCat.{max u v w} S) ℤ)
    {a b : ℤ} (hflat : ∀ n, Module.Flat S (E.X n)) [E.IsStrictlyGE a] [E.IsStrictlyLE b] :
    HasFlatRepresentative.{u, max v w} (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars.{max u v w} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E)) a b := by
  set G := ModuleCat.restrictScalars.{max u v w} e.toRingHom with hG
  refine ⟨_, fun n => ?_, ?_, ?_, ⟨Iso.refl _⟩⟩
  · let := hflat n
    exact flat_restrictScalars_of_ringEquiv.{u, v, w} e (E.X n)
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun n hn => G.map_isZero (E.isZero_of_isStrictlyGE a n hn)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => G.map_isZero (E.isZero_of_isStrictlyLE b n hn)

/-- Restriction of scalars along a ring isomorphism preserves the existence of a flat
representative concentrated in `[a, b]`. -/
public lemma hasFlatRepresentative_restrictScalars_of_ringEquiv {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : R ≃+* S)
    (K : DerivedCategory (ModuleCat.{max u v w} S)) (a b : ℤ)
    (h : HasFlatRepresentative.{v, max u w} K a b) :
    HasFlatRepresentative.{u, max v w}
      ((ModuleCat.restrictScalars.{max u v w} e.toRingHom).mapDerivedCategory.obj K) a b := by
  obtain ⟨E, hflat, hGE, hLE, ⟨i⟩⟩ := h
  set G := ModuleCat.restrictScalars.{max u v w} e.toRingHom with hG
  exact hasFlatRepresentative_of_iso
    (G.mapDerivedCategory.mapIso i ≪≫ G.mapDerivedCategoryFactors.app E).symm
    (hasFlatRepresentative_restrictScalars_complex.{u, v, w} e E hflat)

/-- Let `R` and `S` be two rings each identified with `Λ`, let `A` be an object of `D(R)` and
`A'` one of `D(S)`, and suppose the two become isomorphic in `D(Λ)` after restriction of scalars
along the two identifications. If `A'` has Tor amplitude in `[a, b]` over `S`, then `A` has Tor
amplitude in `[a, b]` over `R`. -/
public theorem hasTorAmplitudeCanonical_of_restrictScalars_iso {Λ : Type rr} [CommRing Λ]
    {R S : Type ww} [CommRing R] [CommRing S] (eR : Λ ≃+* R) (eS : Λ ≃+* S)
    {A : DerivedCategory (ModuleCat.{ww} R)} {A' : DerivedCategory (ModuleCat.{ww} S)}
    (iso : (ModuleCat.restrictScalars.{ww} eR.toRingHom).mapDerivedCategory.obj A ≅
      (ModuleCat.restrictScalars.{ww} eS.toRingHom).mapDerivedCategory.obj A')
    (a b : ℤ) (h : HasTorAmplitudeCanonical S A' a b) :
    HasTorAmplitudeCanonical R A a b := by
  set g : R ≃+* S := eR.symm.trans eS with hg
  have hgcomp : eS.toRingHom = g.toRingHom.comp eR.toRingHom := by
    ext x
    simp [hg]
  set FR := ModuleCat.restrictScalars.{ww} eR.toRingHom with hFR
  set Fg := ModuleCat.restrictScalars.{ww} g.toRingHom with hFg
  have e₁ : ModuleCat.restrictScalars.{ww} eS.toRingHom ≅ Fg ⋙ FR :=
    ModuleCat.restrictScalarsComp'.{ww} eR.toRingHom g.toRingHom eS.toRingHom hgcomp
  have iso₂ : FR.mapDerivedCategory.obj A ≅
      FR.mapDerivedCategory.obj (Fg.mapDerivedCategory.obj A') :=
    iso ≪≫ (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ e₁).app A' ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso Fg FR).app A'
  let : FR.mapDerivedCategory.IsEquivalence :=
    StacksDraft.DerivedRingIso.isEquivalence_mapDerivedCategory
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{rr, ww, ww} eR).functor
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{rr, ww, ww} eR).inverse
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{rr, ww, ww} eR).unitIso
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{rr, ww, ww} eR).counitIso
  refine (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R A a b).2
    (hasFlatRepresentative_of_iso (FR.mapDerivedCategory.preimageIso iso₂).symm ?_)
  exact hasFlatRepresentative_restrictScalars_of_ringEquiv.{ww, ww, ww} g A' a b
    ((hasTorAmplitudeCanonical_iff_hasFlatRepresentative S A' a b).1 h)

/-- Let `R` be a ring identified with `Λ` by `eR`, and let `A` be an object of `D(R)` which,
after restriction of scalars along `eR`, is represented by a complex of flat `Λ`-modules
concentrated in `[a, b]`. Then `A` has Tor amplitude in `[a, b]` over `R`. -/
public theorem hasTorAmplitudeCanonical_of_hasFlatRepresentative_restrictScalars
    {Λ : Type rr} [CommRing Λ] {R : Type (max rr ww)} [CommRing R] (eR : Λ ≃+* R)
    {A : DerivedCategory (ModuleCat.{max rr ww} R)} {a b : ℤ}
    (h : HasFlatRepresentative.{rr, ww}
      ((ModuleCat.restrictScalars.{max rr ww} eR.toRingHom).mapDerivedCategory.obj A) a b) :
    HasTorAmplitudeCanonical R A a b := by
  obtain ⟨E, hflat, hGE, hLE, ⟨i⟩⟩ := h
  set FR := ModuleCat.restrictScalars.{max rr ww} eR.toRingHom with hFR
  set G := ModuleCat.restrictScalars.{max rr ww} eR.symm.toRingHom with hG
  set E' := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj E with hE'
  have hA' : HasTorAmplitudeCanonical R (DerivedCategory.Q.obj E') a b :=
    (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R _ a b).2
      (hasFlatRepresentative_restrictScalars_complex eR.symm E hflat)
  refine hasTorAmplitudeCanonical_of_restrictScalars_iso eR eR (i ≪≫ ?_) a b hA'
  exact DerivedCategory.Q.mapIso
      (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{rr, max rr ww, max rr ww}
        eR).mapHomologicalComplex (ComplexShape.up ℤ)).counitIso.app E).symm ≪≫
    (FR.mapDerivedCategoryFactors.app E').symm

end StacksDraft.TorAmplitude

/-! ### Enough points at a larger universe, on the small étale site and on its slices -/

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The small étale site has enough points relative to any universe above the universe of the
scheme. -/
public theorem hasEnoughPoints_ulift :
    GrothendieckTopology.HasEnoughPoints.{max (u + 1) z} (SmallEtale.topology B S hS) :=
  let : (SmallEtale.topology B S hS).WEqualsLocallyBijective (Type u) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : HasSheafify (SmallEtale.topology B S hS) (Type (max (u + 1) z)) :=
    hasSheafifyEssentiallySmallSite _ _
  GrothendieckTopology.hasEnoughPoints_ulift.{max (u + 1) z, u, u, u + 1} _

/-- Each slice of the small étale site has a conservative family of points relative to any
universe above the universe of the scheme. -/
public theorem hasConservativeFamily_over (V : SmallEtale B S hS) :
    ((SmallEtale.topology B S hS).over V).HasConservativeFamily.{max (u + 1) z} :=
  let : (SmallEtale.topology B S hS).WEqualsLocallyBijective (Type u) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : HasSheafify (SmallEtale.topology B S hS) (Type (max (u + 1) z)) :=
    hasSheafifyEssentiallySmallSite _ _
  let : EssentiallySmall.{max (u + 1) z} (SmallEtale B S hS) :=
    essentiallySmall_lift.{max (u + 1) z, u, u + 1, u} _
  let : (SmallEtale.topology B S hS).WEqualsLocallyBijective (Type (max (u + 1) z)) :=
    GrothendieckTopology.wEqualsLocallyBijective_type.{max (u + 1) z, u + 1, u} _
  let : HasSheafify ((SmallEtale.topology B S hS).over V) (Type (max (u + 1) z)) :=
    hasSheafifyEssentiallySmallSite _ _
  let : GrothendieckTopology.HasEnoughPoints.{max (u + 1) z} (SmallEtale.topology B S hS) :=
    hasEnoughPoints_ulift.{u, z} B S hS
  GrothendieckTopology.HasConservativeFamily.of_hasEnoughPoints _

end AlgebraicGeometry.SmallEtale

/-! ### The stalk of an inverse image, at the universe lift of a geometric point -/

namespace AlgebraicGeometry

section UniverseLiftNatural

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  (p : J.Point.{z}) {R : Type rr} [Ring R]
  [HasColimitsOfSize.{z, z} (ModuleCat.{w} R)]
  [HasColimitsOfSize.{z, z} AddCommGrpCat.{max w wq}]
  [HasColimitsOfSize.{max z zq, max z zq} (ModuleCat.{max w wq} R)]

/-- The fibre at the universe lift of a point is the uplift of the fibre, naturally in the
presheaf. -/
public def uliftPointPresheafFiberNatIso :
    (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{w} R) (ModuleCat.{max w wq} R)).obj
          (ModuleCat.uliftFunctor.{wq} R) ⋙
        (p.ulift.{zq}).presheafFiber (A := ModuleCat.{max w wq} R) ≅
      p.presheafFiber (A := ModuleCat.{w} R) ⋙ ModuleCat.uliftFunctor.{wq} R :=
  NatIso.ofComponents (fun P => uliftPointPresheafFiberIso p P) (fun {P Q} τ => by
    refine (p.ulift.{zq}).presheafFiber_hom_ext (fun X x => ?_)
    obtain ⟨y⟩ := x
    have h₁ := (p.ulift.{zq}).toPresheafFiber_naturality
      (Functor.whiskerRight τ (ModuleCat.uliftFunctor.{wq} R)) X (ULift.up y)
    have h₂ := uliftPointPresheafFiberIso_hom_toPresheafFiber p Q X y
    have h₃ := uliftPointPresheafFiberIso_hom_toPresheafFiber p P X y
    have h₄ := p.toPresheafFiber_naturality τ X y
    have key := Eq.trans
      (Functor.map_comp (ModuleCat.uliftFunctor.{wq} R) (τ.app (Opposite.op X))
        (p.toPresheafFiber X y Q)).symm
      (Eq.trans (congrArg (ModuleCat.uliftFunctor.{wq} R).map h₄.symm)
        (Functor.map_comp (ModuleCat.uliftFunctor.{wq} R) (p.toPresheafFiber X y P)
          (p.presheafFiber.map τ)))
    exact Eq.trans (Category.assoc _ _ _).symm (Eq.trans (h₁ =≫ _)
      (Eq.trans (Category.assoc _ _ _) (Eq.trans (_ ≫= h₂)
        (Eq.trans key (Eq.trans (h₃.symm =≫ _) (Category.assoc _ _ _)))))))

end UniverseLiftNatural

section PullbackStalk

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

/-- At the universe lift of a point, the ulifted fibre functor is the uplift of the fibre
functor on sheaves. -/
public def upliftedEtaleFiberSheafFiberNatIso (X : B.Scheme)
    (p : (SmallEtale.topology B X.obj X.property).Point.{u}) :
    upliftedEtaleFiberFunctor.{u, w, r} B X Λ (p.ulift.{max (u + 1) w r}) ≅
      p.sheafFiber (A := ModuleCat.{w} Λ) ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (uliftPointPresheafFiberNatIso.{w, u, r, _, _, max (u + 1) w r, max (u + 1) r} p)

/-- The ulifted fibre, at the universe lift of a geometric point `s` of `X`, of the inverse image
along `f : X ⟶ Y` of a sheaf of `Λ`-modules on the small étale site of `Y` is its ulifted fibre
at the universe lift of the image geometric point `f ∘ s`, naturally in the sheaf. -/
@[sga "4 VIII 3.4" "(F), special case", sga "4½ Arcata 2.3.3" "special case"]
public def smallEtalePullbackUpliftedEtaleFiberNatIso {X Y : B.Scheme} (f : X ⟶ Y)
    [HasProducts.{u} (ModuleCat.{w} Λ)]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
    (s : GeometricPoint X.obj) :
    (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{w} Λ)
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property) ⋙
        upliftedEtaleFiberFunctor.{u, w, r} B X Λ
          ((geometricSitePoint B X s).ulift.{max (u + 1) w r}) ≅
      upliftedEtaleFiberFunctor.{u, w, r} B Y Λ
        ((geometricSitePoint B Y (s.map (B.inclusion.map f))).ulift.{max (u + 1) w r}) :=
  Functor.isoWhiskerLeft _
      (upliftedEtaleFiberSheafFiberNatIso.{u, w, r} B Λ X (geometricSitePoint B X s)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (smallEtalePullbackSheafFiberIso B f s (ModuleCat.{w} Λ))
      (ModuleCat.uliftFunctor.{max (u + 1) r} Λ) ≪≫
    (upliftedEtaleFiberSheafFiberNatIso.{u, w, r} B Λ Y
      (geometricSitePoint B Y (s.map (B.inclusion.map f)))).symm

end PullbackStalk

end AlgebraicGeometry

/-! ### A covering of an object of the source site, by base change from the target -/

namespace AlgebraicGeometry

/-- Given a covering sieve `S` of the final object of the small étale site of `Y` and a morphism
`f : X ⟶ Y`, every object `U'` of the small étale site of `X` has a covering sieve each of whose
members factors through the base change along `f` of a member of `S`. -/
public theorem exists_covering_factors_smallEtaleBaseChange (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (f : X ⟶ Y)
    (S : Sieve (SmallEtale.final B Y.obj Y.property))
    (hS : S ∈ SmallEtale.topology B Y.obj Y.property (SmallEtale.final B Y.obj Y.property))
    (U' : SmallEtale B X.obj X.property) :
    ∃ R : Sieve U', R ∈ SmallEtale.topology B X.obj X.property U' ∧
      ∀ ⦃V' : SmallEtale B X.obj X.property⦄ (g : V' ⟶ U'), R.arrows g →
        ∃ (V : SmallEtale B Y.obj Y.property)
          (q : V ⟶ SmallEtale.final B Y.obj Y.property),
          S.arrows q ∧ Nonempty (V' ⟶ (smallEtaleBaseChange B f).obj V) := by
  set u := smallEtaleBaseChange B f with hu
  have hcover : CoverPreserving (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property) u :=
    CoverPreserving.of_isContinuous u _ _
  have ht : IsTerminal (u.obj (SmallEtale.final B Y.obj Y.property)) :=
    smallEtaleBaseChange_finalIsTerminal B f
  refine ⟨(Sieve.functorPushforward u S).pullback (ht.from U'), ?_, ?_⟩
  · exact (SmallEtale.topology B X.obj X.property).pullback_stable _ (hcover.cover_preserve hS)
  · intro V' g hg
    obtain ⟨V, p, q, hq, -⟩ := hg
    exact ⟨V, p, hq, ⟨q⟩⟩

end AlgebraicGeometry

/-! ### The conservative family of lifted geometric points on a slice -/

namespace AlgebraicGeometry

set_option linter.checkUnivs false in
/-- The lifts `Φ.over x`, to the slice over `V`, of the universe lifts `Φ` of the geometric points
of `X`, along the elements `x` of their fibres over `V`, are a conservative family of points of
that slice. -/
@[sga "4 IV 6.7.4" "special case"]
public theorem isConservativeFamilyOfPoints_uliftGeometricSitePoint_over
    (B : BigEtaleSite.{u}) (X : B.Scheme) (V : SmallEtale B X.obj X.property) :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun ψ : Σ Φ : (ObjectProperty.ofObj (fun x : ↥X.obj =>
            (geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) w r})).FullSubcategory,
          Φ.obj.fiber.obj V => ψ.1.obj.over ψ.2)) := by
  let : (SmallEtale.topology B X.obj X.property).WEqualsLocallyBijective (Type u) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : HasSheafify (SmallEtale.topology B X.obj X.property)
      (Type (max (u + 1) w r)) :=
    hasSheafifyEssentiallySmallSite _ _
  let : EssentiallySmall.{max (u + 1) w r} (SmallEtale B X.obj X.property) :=
    essentiallySmall_lift.{max (u + 1) w r, u, u + 1, u} _
  let : (SmallEtale.topology B X.obj X.property).WEqualsLocallyBijective
      (Type (max (u + 1) w r)) :=
    GrothendieckTopology.wEqualsLocallyBijective_type.{max (u + 1) w r, u + 1, u} _
  let : HasSheafify ((SmallEtale.topology B X.obj X.property).over V)
      (Type (max (u + 1) w r)) :=
    hasSheafifyEssentiallySmallSite _ _
  exact (isConservativeFamilyOfPoints_uliftGeometricSitePoint.{u, w, r} B X).over V

end AlgebraicGeometry

/-! ### Locally finite Tor dimension and the stalks on the slices -/

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{u, v, w}} [LocallySmall.{w} Z.C]
  [HasSheafify Z.J AddCommGrpCat.{w}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{w}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

/-- A slice of a locally small site is locally small. -/
local instance sliceLocallySmall (U : Z.C) : LocallySmall.{w} (Z.over U).C :=
  ⟨fun X Y => small_of_injective (f := fun g : X ⟶ Y => g.left)
    fun _ _ h => Over.OverMorphism.ext h⟩

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} Z)]
  [hSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, w} (Z.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable
  [∀ U : Z.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{max u v, v, w} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- Suppose every object `U` of the site carries a covering family on each member `V` of which
there is a single interval `[a, b]` containing the Tor amplitude of the derived stalk of `E|_V`
at every point of the slice over `V`. Then `E` locally has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_of_stalkwise
    (T : ∀ U : Z.C, DerivedTensorProduct.{max u v, v, w, d} (Z.over U))
    (E : RingedSite.DerivedModules.{u, v, w, d} Z)
    (hcons : ∀ V : Z.C, (Z.over V).J.HasConservativeFamily.{w})
    (h : ∀ U : Z.C, ∃ S : Presieve U, Sieve.generate S ∈ Z.J U ∧
      ∀ ⦃V : Z.C⦄ (g : V ⟶ U), S g → ∃ a b : ℤ, ∀ Φ : (Z.over V).J.Point.{w},
        letI : HasDerivedCategory.{d}
            (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, max u v, w}
              (Z.over V).O)) := hSliceDerived V
        StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
          ((Φ.presheafFiber (A := CommRingCat.{w})).obj (Z.over V).O.obj)
          ((Stacks.derivedModuleFiber Φ (Z.over V).O).obj
            ((RingedSite.derivedRestriction.{u, v, w, d} Z V).obj E)) a b) :
    LocallyHasFiniteTorDimension T E := by
  intro U
  obtain ⟨S, hS, hbound⟩ := h U
  refine ⟨S, hS, fun {V} g hg => ?_⟩
  obtain ⟨a, b, hΦ⟩ := hbound g hg
  exact ⟨a, b, hasTorAmplitude_of_forall_derivedModuleFiber.{max u v, v, w, d}
    (T V) _ a b (hcons V) hΦ⟩

/-- Suppose every object `U` of the site carries a covering family on each member `V` of which
there is a single interval `[a, b]` containing the Tor amplitude of the derived stalk of `E|_V`
at every member of a given conservative family `p V` of points of the slice over `V`. Then `E`
locally has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_of_stalkwise_family
    (T : ∀ U : Z.C, DerivedTensorProduct.{max u v, v, w, d} (Z.over U))
    (E : RingedSite.DerivedModules.{u, v, w, d} Z)
    {t : Z.C → Type tt} (p : ∀ V : Z.C, t V → (Z.over V).J.Point.{w})
    (hcons : ∀ V : Z.C, (ObjectProperty.ofObj (p V)).IsConservativeFamilyOfPoints)
    (h : ∀ U : Z.C, ∃ S : Presieve U, Sieve.generate S ∈ Z.J U ∧
      ∀ ⦃V : Z.C⦄ (g : V ⟶ U), S g → ∃ a b : ℤ, ∀ k : t V,
        letI : HasDerivedCategory.{d}
            (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, max u v, w}
              (Z.over V).O)) := hSliceDerived V
        StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
          (((p V k).presheafFiber (A := CommRingCat.{w})).obj (Z.over V).O.obj)
          ((Stacks.derivedModuleFiber (p V k) (Z.over V).O).obj
            ((RingedSite.derivedRestriction.{u, v, w, d} Z V).obj E)) a b) :
    LocallyHasFiniteTorDimension T E := by
  intro U
  obtain ⟨S, hS, hbound⟩ := h U
  refine ⟨S, hS, fun {V} g hg => ?_⟩
  obtain ⟨a, b, hk⟩ := hbound g hg
  exact ⟨a, b, hasTorAmplitude_of_forall_derivedModuleFiber_family.{max u v, v, w, d}
    (T V) _ a b (p V) (hcons V) hk⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
