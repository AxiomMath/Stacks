module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Derived extension of scalars along a map precomposed with a ring isomorphism

Let `ε : R ⟶ R₂` be an isomorphism of commutative rings, with inverse `ε'`, and let
`ψ : R₂ →+* R'` be any homomorphism.  Restriction of scalars along `ε'` is an equivalence, so

`(restrictScalars ε')^D ⋙ (- ⊗ᴸ_{R₂} R')`

is again a total left derived functor of termwise extension of scalars — along `ψ ∘ ε` this
time — and uniqueness of left derived functors identifies it with total derived extension of
scalars along `ψ ∘ ε`.

The point of the statement is that the two sides are the two presentations that a geometric
chain of derived stalk comparisons produces.  A square of schemes presents the local ring at the
image of a point in two ways — once through each of the two edges of the square — so the stalk of
a derived pullback is stated over one of them and the stalk of a derived pushforward over the
other, and the two are identified by the comparison of the stalks at two equal points, which is
restriction of scalars along a ring isomorphism.  Composing those comparisons produces derived
extension of scalars along the composite, which is what Stacks 0661 has to be instantiated at.

## Main definitions

* `StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv`: restriction of scalars along a ring
  homomorphism with a two-sided inverse is left adjoint to restriction of scalars along the
  inverse.
* `StacksDraft.DerivedRingIso.mapDerivedCategoryEquivalence`: an exact equivalence of abelian
  categories induces an equivalence of their derived categories.
* `StacksDraft.DerivedRingIso.extendScalarsRestrictIso`: the underived comparison, restriction of
  scalars along `ε'` followed by extension of scalars along `ψ` is extension of scalars along
  `ψ ∘ ε`.
* `StacksDraft.DerivedRingIso.restrictCompComparison`: the comparison of the composite with
  termwise extension of scalars along `ψ ∘ ε`.
* `StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso`: derived restriction of scalars along a
  homomorphism *equal to the identity* is the identity functor.  This is the functor both
  transports of a point reduce to, so that they cancel.

## Main results

* `StacksDraft.DerivedRingIso.isLeftDerivedFunctor_restrictCompComparison`: the composite, with
  that comparison, is a total left derived functor of termwise extension of scalars along
  `ψ ∘ ε`.
* `StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso`: **the comparison.**  Derived
  restriction of scalars along the inverse isomorphism, followed by total derived extension of
  scalars along `ψ`, is total derived extension of scalars along `ψ ∘ ε`.
* `StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso_hom_app_Q_comp_comparison`: that
  isomorphism is compatible with the two comparisons with termwise extension of scalars.  This is
  what makes it usable in a diagram chase: without it the isomorphism is opaque below the
  localization functor.
* `StacksDraft.DerivedRingIso.extendScalarsRestrictIso_hom_app_of_eq_id`: **the degreewise identity
  case.**  For `ε` equal to the identity homomorphism, absorbing `ε` into `ψ` is the collapse of
  restriction of scalars along `ε` followed by the transport from `ψ` to `ψ ∘ ε`.  Uniqueness of
  left adjoints identifies `extendScalarsIsoRestrictScalars` at the identity with
  `ModuleCat.extendScalarsId`, and the left unit law of `ModuleCat.extendScalarsComp` does the
  rest.

## Implementation notes

*Why the isomorphism is given by two homomorphisms and two pointwise equations rather than by a
`RingEquiv`.*  The consumer has the isomorphism in hand as a pair of `CommRingCat` morphisms —
the two directions of `TopCat.Presheaf.stalkCongr` — and the composite `ψ ∘ ε` it needs is the
underlying homomorphism of a composite of `CommRingCat` morphisms.  Taking a `RingEquiv` would
force that consumer to produce one and then to identify its forward homomorphism with the morphism
it started from; with the two homomorphisms as separate arguments the identification is by
construction.  Structure eta makes the `RingEquiv` assembled in the proof have exactly `ε` and
`ε'` as its two homomorphisms, so nothing is lost.

*Why uniqueness of left derived functors and not uniqueness of left adjoints.*  Both are
available: both sides are left adjoint to derived restriction of scalars along `ψ ∘ ε`, by
`adjRestrictScalarsOfInv` together with
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction`, so
`CategoryTheory.Adjunction.leftAdjointUniq` produces an isomorphism as well — and that is how
this file used to produce it.  The adjoint route is shorter, but the isomorphism it produces is
characterized only by the two units, and the consumer needs the isomorphism *below* the
localization functor: it has to cancel against the comparison of
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars` with termwise extension of
scalars, and no equation of units gives that.  The left-derived route gives exactly that equation,
by construction, as `derivedExtensionScalarsRestrictIso_hom_app_Q`.

*What the left-derived route needs that the adjoint route did not.*  That the composite is a total
left derived functor of termwise extension of scalars along `ψ ∘ ε` is the transport of the
left-derived universal property of the chosen model for `ψ` across the equivalence induced by
`ε'`, and that is a transport of a right Kan extension along two equivalences, one on complexes
and one on derived categories.  Mathlib's
`CategoryTheory.Functor.isRightKanExtension_iff_precomp_equivalence` performs it, given both
equivalences; `mapDerivedCategoryEquivalence` supplies the second one, which Mathlib does not
have.

*Why `mapDerivedCategoryEquivalence` takes two functors and two isomorphisms rather than a
`CategoryTheory.Equivalence`.*  The exactness hypotheses have to be stated at the two functors
themselves: at `e.functor` for an abstract `e` they are not found by instance search at a
consumer's spelling of the functor, since `e.functor` is a projection of a term that instance
search does not unfold.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

noncomputable section

namespace StacksDraft.DerivedRingIso

universe w₂ w₁ u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- **An adjunction of exact functors induces an adjunction of the derived functors.**  If `F` and
`G` are exact functors of abelian categories with chosen derived categories and `F ⊣ G`, then the
functors they induce on derived categories are adjoint.

`CategoryTheory.Adjunction.mapHomologicalComplex` gives the adjunction on cochain complexes, and
`CategoryTheory.Adjunction.localization` descends it to the localizations at the
quasi-isomorphisms, the two squares being commutative by
`CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
def mapDerivedCategoryAdjunction
    {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    [Category* D] [Abelian D] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) : F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  letI : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) _ _

/-! ### An exact equivalence induces an equivalence of derived categories -/

section DerivedEquivalence

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₁)

/-- The functor induced on derived categories by the identity functor is the identity. -/
def mapDerivedCategoryIdIso : (𝟭 C₁).mapDerivedCategory ≅ 𝟭 (DerivedCategory C₁) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((𝟭 C₁).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q (𝟭 C₁).mapDerivedCategory (𝟭 _)
    (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫ Functor.leftUnitor _)

/-- **`mapDerivedCategoryIdIso` at the image of a cochain complex.**  It is the canonical
factorization of the derived functor of the identity, then `DerivedCategory.Q` of the degreewise
comparison of `(𝟭).mapHomologicalComplex` with the identity.

The identity case of a derived functor is opaque below the localization functor without this. -/
theorem mapDerivedCategoryIdIso_hom_app_Q (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryIdIso (C₁ := C₁)).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C₁).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app P) := by
  simp [mapDerivedCategoryIdIso]
  all_goals rfl

/-- **An exact equivalence of abelian categories induces an equivalence of derived
categories.**  The equivalence is presented by two functors and two isomorphisms, rather than by
a `CategoryTheory.Equivalence`, so that the exactness hypotheses are stated at the two functors
themselves. -/
abbrev mapDerivedCategoryEquivalence
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : 𝟭 C₁ ≅ F ⋙ G) (ν : G ⋙ F ≅ 𝟭 C₂) :
    DerivedCategory C₁ ≌ DerivedCategory C₂ :=
  CategoryTheory.Equivalence.mk F.mapDerivedCategory G.mapDerivedCategory
    (mapDerivedCategoryIdIso.symm ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ η ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G)
    ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso G F).symm ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ ν ≪≫
      mapDerivedCategoryIdIso)

/-- The derived functor of the forward direction of an exact equivalence is an equivalence. -/
theorem isEquivalence_mapDerivedCategory
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : 𝟭 C₁ ≅ F ⋙ G) (ν : G ⋙ F ≅ 𝟭 C₂) :
    F.mapDerivedCategory.IsEquivalence :=
  (mapDerivedCategoryEquivalence F G η ν).isEquivalence_functor

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] in
/-- The functor induced on cochain complexes by the forward direction of an exact equivalence is
an equivalence. -/
theorem isEquivalence_mapHomologicalComplex [F.Additive] [G.Additive]
    (η : 𝟭 C₁ ≅ F ⋙ G) (ν : G ⋙ F ≅ 𝟭 C₂) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (F.mapHomologicalComplex (ComplexShape.up ℤ))
    (G.mapHomologicalComplex (ComplexShape.up ℤ))
    ((Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).symm ≪≫
      NatIso.mapHomologicalComplex η (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).symm)
    (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex ν (ComplexShape.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso C₂ (ComplexShape.up ℤ))).isEquivalence_functor

end DerivedEquivalence

/-! ### Restriction of scalars along the inverse of a ring isomorphism -/

variable {R R₂ R' : Type u} [CommRing R] [CommRing R₂] [CommRing R']

/-- **Restriction of scalars along a ring isomorphism is left adjoint to restriction of scalars
along its inverse.**  The two functors are the two directions of the equivalence
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv`, which is an adjoint equivalence. -/
def adjRestrictScalarsOfInv (ε : R →+* R₂) (ε' : R₂ →+* R)
    (h₁ : ∀ x, ε' (ε x) = x) (h₂ : ∀ y, ε (ε' y) = y) :
    ModuleCat.restrictScalars.{u, u, u} ε' ⊣ ModuleCat.restrictScalars.{u, u, u} ε :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u}
    ({ ε with invFun := ε', left_inv := h₁, right_inv := h₂ } : R ≃+* R₂)).symm.toAdjunction

variable (ε : R →+* R₂) (ε' : R₂ →+* R) (h₁ : ∀ x, ε' (ε x) = x) (h₂ : ∀ y, ε (ε' y) = y)

include h₁

/-- Restricting scalars along `ε'` and then along `ε` is the identity. -/
def restrictScalarsUnitOfInv :
    𝟭 (ModuleCat.{u} R) ≅
      ModuleCat.restrictScalars.{u, u, u} ε' ⋙ ModuleCat.restrictScalars.{u, u, u} ε :=
  (ModuleCat.restrictScalarsId.{u} R).symm ≪≫
    ModuleCat.restrictScalarsComp'.{u} ε ε' (RingHom.id R) (RingHom.ext fun x => (h₁ x).symm)

omit h₁
include h₂

/-- Restricting scalars along `ε` and then along `ε'` is the identity. -/
def restrictScalarsCounitOfInv :
    ModuleCat.restrictScalars.{u, u, u} ε ⋙ ModuleCat.restrictScalars.{u, u, u} ε' ≅
      𝟭 (ModuleCat.{u} R₂) :=
  (ModuleCat.restrictScalarsComp'.{u} ε' ε (RingHom.id R₂)
    (RingHom.ext fun y => (h₂ y).symm)).symm ≪≫ ModuleCat.restrictScalarsId.{u} R₂

include h₁

/-- Restriction of scalars along the inverse of a ring isomorphism, acting on cochain complexes,
is an equivalence. -/
theorem isEquivalence_mapHomologicalComplex_restrictScalars :
    ((ModuleCat.restrictScalars.{u, u, u} ε').mapHomologicalComplex
      (ComplexShape.up ℤ)).IsEquivalence :=
  isEquivalence_mapHomologicalComplex _ _ (restrictScalarsUnitOfInv ε ε' h₁)
    (restrictScalarsCounitOfInv ε ε' h₂)

/-- Restriction of scalars along the inverse of a ring isomorphism, acting on derived categories,
is an equivalence. -/
theorem isEquivalence_mapDerivedCategory_restrictScalars :
    (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.IsEquivalence :=
  isEquivalence_mapDerivedCategory _ _ (restrictScalarsUnitOfInv ε ε' h₁)
    (restrictScalarsCounitOfInv ε ε' h₂)

/-- **Restriction of scalars along the inverse of a ring isomorphism is extension of scalars
along the isomorphism.**  Both are left adjoint to restriction of scalars along `ε`. -/
def extendScalarsIsoRestrictScalars :
    ModuleCat.restrictScalars.{u, u, u} ε' ≅ ModuleCat.extendScalars.{u, u, u} ε :=
  Adjunction.leftAdjointUniq (adjRestrictScalarsOfInv ε ε' h₁ h₂)
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} ε)

/-- **Extension of scalars along `ψ ∘ ε`, underived.**  Restriction of scalars along the inverse
of `ε` followed by extension of scalars along `ψ` is extension of scalars along `ψ ∘ ε`. -/
def extendScalarsRestrictIso (ψ : R₂ →+* R') :
    ModuleCat.restrictScalars.{u, u, u} ε' ⋙ ModuleCat.extendScalars.{u, u, u} ψ ≅
      ModuleCat.extendScalars.{u, u, u} (ψ.comp ε) :=
  Functor.isoWhiskerRight (extendScalarsIsoRestrictScalars ε ε' h₁ h₂)
      (ModuleCat.extendScalars.{u, u, u} ψ) ≪≫
    (ModuleCat.extendScalarsComp ε ψ).symm

omit h₁ h₂

/-- The comparison of the chosen model of total derived extension of scalars along `ψ` with
termwise extension of scalars, stated with the termwise functor
`(ModuleCat.extendScalars ψ).mapHomologicalComplex (ComplexShape.up ℤ)`. See the implementation
notes of `ClosedImmersionBaseChangeStalkDiagram.lean` (in
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/`) on why the two spellings have to be
distinguished. -/
abbrev alpha (ψ : R₂ →+* R') :
    DerivedCategory.Q ⋙ (totalDerivedExtensionScalars.{u, u, u} ψ).functor ⟶
      (ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (totalDerivedExtensionScalars.{u, u, u} ψ).comparison

/-- The left-derived universal property of the chosen model, re-seated at the spelling of
`alpha`. -/
local instance isLeftDerived_alpha (ψ : R₂ →+* R') :
    (totalDerivedExtensionScalars.{u, u, u} ψ).functor.IsLeftDerivedFunctor (alpha ψ)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R₂) (ComplexShape.up ℤ)) :=
  (totalDerivedExtensionScalars.{u, u, u} ψ).isLeftDerived

include h₁ h₂

/-- `extendScalarsRestrictIso` on cochain complexes, after localization: termwise extension of
scalars along `ψ ∘ ε` is termwise restriction along `ε'` followed by termwise extension along
`ψ`. -/
def extendScalarsRestrictComplexIso (ψ : R₂ →+* R') :
    (ModuleCat.extendScalars.{u, u, u} (ψ.comp ε)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ≅
      (ModuleCat.restrictScalars.{u, u, u} ε').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) :=
  Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (extendScalarsRestrictIso ε ε' h₁ h₂ ψ).symm
          (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (ModuleCat.restrictScalars.{u, u, u} ε' ⋙
            ModuleCat.extendScalars.{u, u, u} ψ)) (ComplexShape.up ℤ)).symm)
      DerivedCategory.Q ≪≫
    Functor.associator _ _ _

/-- **The comparison of the composite with termwise extension of scalars along `ψ ∘ ε`.**
Derived restriction of scalars along `ε'` followed by the chosen model of derived extension of
scalars along `ψ`, compared with termwise extension of scalars along `ψ ∘ ε`: the comparison for
`ψ`, read through the factorization of derived restriction of scalars and through
`extendScalarsRestrictComplexIso`. -/
def restrictCompComparison (ψ : R₂ →+* R') :
    DerivedCategory.Q ⋙ ((ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor) ⟶
      (ModuleCat.extendScalars.{u, u, u} (ψ.comp ε)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
        (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategoryFactors.hom
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
            ((ModuleCat.restrictScalars.{u, u, u} ε').mapHomologicalComplex (ComplexShape.up ℤ))
            (alpha ψ) ≫
          (extendScalarsRestrictComplexIso ε ε' h₁ h₂ ψ).inv

/-- **The composite is a total left derived functor of termwise extension of scalars along
`ψ ∘ ε`.**  Restriction of scalars along `ε'` is an equivalence both on complexes and on derived
categories, and the two localizations are compatible with it, so the left-derived universal
property of the chosen model for `ψ` transports along it. -/
theorem isLeftDerivedFunctor_restrictCompComparison (ψ : R₂ →+* R') :
    ((ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor).IsLeftDerivedFunctor
      (restrictCompComparison ε ε' h₁ h₂ ψ)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  have := isEquivalence_mapHomologicalComplex_restrictScalars ε ε' h₁ h₂
  have := isEquivalence_mapDerivedCategory_restrictScalars ε ε' h₁ h₂
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  refine (Functor.isRightKanExtension_iff_precomp_equivalence
    (restrictCompComparison ε ε' h₁ h₂ ψ) (alpha ψ)
    (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategoryFactors.symm
    (extendScalarsRestrictComplexIso ε ε' h₁ h₂ ψ) (Iso.refl _) ?_).1 ?_
  · simp [restrictCompComparison]
  · exact (Functor.isLeftDerivedFunctor_iff_isRightKanExtension _ (alpha ψ) _).1
      (isLeftDerived_alpha ψ)

/-- `restrictCompComparison` at a cochain complex: the comparison for `ψ` at the termwise
restriction of the complex, preceded by the factorization of derived restriction of scalars and
followed by the underived comparison `extendScalarsRestrictIso`. -/
theorem restrictCompComparison_app (ψ : R₂ →+* R')
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (restrictCompComparison ε ε' h₁ h₂ ψ).app P =
      (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
          ((ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategoryFactors.hom.app P) ≫
        (alpha ψ).app
            (((ModuleCat.restrictScalars.{u, u, u} ε').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (extendScalarsRestrictIso ε ε' h₁ h₂ ψ).hom (ComplexShape.up ℤ)).app P) := by
  simp [restrictCompComparison, extendScalarsRestrictComplexIso, NatIso.mapHomologicalComplex,
    show ∀ X : CochainComplex (ModuleCat.{u} R) ℤ,
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (ModuleCat.restrictScalars.{u, u, u} ε' ⋙
            ModuleCat.extendScalars.{u, u, u} ψ)) (ComplexShape.up ℤ)).hom.app X) =
        CategoryStruct.id _ from fun _ => CategoryTheory.Functor.map_id _ _]

/-- **Derived extension of scalars along `ψ ∘ ε`, for `ε` an isomorphism of rings.**  Derived
restriction of scalars along the inverse of `ε`, followed by total derived extension of scalars
along `ψ`, is total derived extension of scalars along `ψ ∘ ε`.

Both sides are total left derived functors of termwise extension of scalars along `ψ ∘ ε` — the
left-hand side by `isLeftDerivedFunctor_restrictCompComparison`, the right-hand side by
definition — and a total left derived functor is unique up to a unique isomorphism compatible
with the two comparisons.  That compatibility is
`derivedExtensionScalarsRestrictIso_hom_app_Q`. -/
def derivedExtensionScalarsRestrictIso (ψ : R₂ →+* R') :
    (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} (ψ.comp ε)).functor :=
  haveI := isLeftDerivedFunctor_restrictCompComparison ε ε' h₁ h₂ ψ
  Functor.leftDerivedUnique _ _ (restrictCompComparison ε ε' h₁ h₂ ψ) (alpha (ψ.comp ε))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))

/-- **The isomorphism is compatible with the two comparisons with termwise extension of
scalars.**  This is the equation that the left-derived construction of
`derivedExtensionScalarsRestrictIso` supplies and the adjoint construction did not: it computes
the isomorphism at an object in the image of the localization functor, against the comparison of
the chosen model for `ψ ∘ ε`. -/
theorem derivedExtensionScalarsRestrictIso_hom_app_Q (ψ : R₂ →+* R')
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtensionScalarsRestrictIso ε ε' h₁ h₂ ψ).hom.app (DerivedCategory.Q.obj P) ≫
        (alpha (ψ.comp ε)).app P =
      (restrictCompComparison ε ε' h₁ h₂ ψ).app P := by
  have := isLeftDerivedFunctor_restrictCompComparison ε ε' h₁ h₂ ψ
  simp [derivedExtensionScalarsRestrictIso]

/-- `derivedExtensionScalarsRestrictIso_hom_app_Q` with the comparison of the composite spelled
out: this is the form a diagram chase rewrites with. -/
theorem derivedExtensionScalarsRestrictIso_hom_app_Q_comp_comparison (ψ : R₂ →+* R')
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtensionScalarsRestrictIso ε ε' h₁ h₂ ψ).hom.app (DerivedCategory.Q.obj P) ≫
        (alpha (ψ.comp ε)).app P =
      (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
          ((ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategoryFactors.hom.app P) ≫
        (alpha ψ).app
            (((ModuleCat.restrictScalars.{u, u, u} ε').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (extendScalarsRestrictIso ε ε' h₁ h₂ ψ).hom (ComplexShape.up ℤ)).app P) :=
  (derivedExtensionScalarsRestrictIso_hom_app_Q ε ε' h₁ h₂ ψ P).trans
    (restrictCompComparison_app ε ε' h₁ h₂ ψ P)

/-! ### The identity case

`derivedExtensionScalarsRestrictIso` is consumed at the germ comparison of two *equal* points of a
scheme, which is a ring homomorphism equal to the identity.  At such a `σ` restriction of scalars
is the identity functor, and the comparison has to collapse to the transport of
`ψ ∘ σ` against `ψ`.  The collapse is assembled here, in the module that owns the comparison,
from the degreewise statement upwards; the derived statement itself is
`StacksDraft.DerivedRingIso.restrictIsoApp_of_eq_id`, in the module that owns the rigid wrappers a
chase needs. -/

section Identity

omit h₁ h₂

/-- **Restriction of scalars along two homomorphisms equal to the identity, compared.**  The
transport between the two restriction functors absorbs the collapse of either into the identity
functor.  Stated for two free homomorphisms, since it is proved by substituting the identity for
each. -/
theorem restrictScalarsId'_eqToIso (f g : R →+* R) (hf : f = RingHom.id R)
    (hg : g = RingHom.id R)
    (E : ModuleCat.restrictScalars.{u, u, u} f = ModuleCat.restrictScalars.{u, u, u} g)
    (N : ModuleCat.{u} R) :
    (eqToIso E).hom.app N ≫ (ModuleCat.restrictScalarsId'.{u, u} g hg).hom.app N =
      (ModuleCat.restrictScalarsId'.{u, u} f hf).hom.app N := by
  subst hf
  subst hg
  simp

/-- **Degreewise restriction of scalars along a homomorphism equal to the identity is the identity
functor on complexes.** -/
def restrictScalarsIdComplexIso (σ : R →+* R) (hσ : σ = RingHom.id R) :
    (ModuleCat.restrictScalars.{u, u, u} σ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      𝟭 (CochainComplex (ModuleCat.{u} R) ℤ) :=
  NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId'.{u, u} σ hσ)
      (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (ComplexShape.up ℤ)

/-- `restrictScalarsIdComplexIso` at a cochain complex, with its source and target written out. -/
def restrictScalarsIdComplexApp (σ : R →+* R) (hσ : σ = RingHom.id R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.restrictScalars.{u, u, u} σ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ⟶ P :=
  (restrictScalarsIdComplexIso.{u} σ hσ).hom.app P

/-- **Derived restriction of scalars along a homomorphism equal to the identity is the identity
functor.**  The degreewise collapse, carried to derived categories by
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` and `mapDerivedCategoryIdIso`.

This is the functor a chase meets on both sides of the transport of a point: the derived stalk
transport `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkFunctorCongr` at a self-equality
and `derivedExtensionScalarsRestrictIso` at the germ comparison of a point with itself both reduce
to it, so that the two cancel. -/
def restrictScalarsIdDerivedIso (σ : R →+* R) (hσ : σ = RingHom.id R) :
    (ModuleCat.restrictScalars.{u, u, u} σ).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{u} R)) :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (ModuleCat.restrictScalarsId'.{u, u} σ hσ) ≪≫ mapDerivedCategoryIdIso

/-- **`restrictScalarsIdDerivedIso` at the image of a cochain complex**: the canonical
factorization of derived restriction of scalars, then `DerivedCategory.Q` of the degreewise
collapse. -/
theorem restrictScalarsIdDerivedIso_hom_app_Q (σ : R →+* R) (hσ : σ = RingHom.id R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (restrictScalarsIdDerivedIso.{u} σ hσ).hom.app (DerivedCategory.Q.obj P) =
      (ModuleCat.restrictScalars.{u, u, u} σ).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map (restrictScalarsIdComplexApp.{u} σ hσ P) := by
  simp [restrictScalarsIdDerivedIso, restrictScalarsIdComplexApp, restrictScalarsIdComplexIso,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    mapDerivedCategoryIdIso_hom_app_Q]

/-- **The comparison of restriction with extension of scalars at the identity.**  Restriction of
scalars along the identity, read as extension of scalars along the identity by
`extendScalarsIsoRestrictScalars` and then collapsed by `ModuleCat.extendScalarsId`, is the
collapse of restriction of scalars itself.

Both `extendScalarsIsoRestrictScalars` at the identity and `ModuleCat.extendScalarsId` are
instances of `CategoryTheory.Adjunction.leftAdjointUniq` against
`CategoryTheory.Adjunction.id`, so the composite is `leftAdjointUniq` of that adjunction with
itself, which is the identity. -/
theorem extendScalarsIsoRestrictScalars_hom_app_comp_extendScalarsId
    (k₁ k₂ : ∀ y : R, (RingHom.id R) ((RingHom.id R) y) = y) (M : ModuleCat.{u} R) :
    (extendScalarsIsoRestrictScalars.{u} (RingHom.id R) (RingHom.id R) k₁ k₂).hom.app M ≫
        (ModuleCat.extendScalarsId.{u} R).hom.app M =
      (ModuleCat.restrictScalarsId'.{u, u} (RingHom.id R) rfl).hom.app M := by
  let adjI : 𝟭 (ModuleCat.{u} R) ⊣ ModuleCat.restrictScalars.{u, u, u} (RingHom.id R) :=
    Adjunction.id
  let adjE := ModuleCat.extendRestrictScalarsAdj.{u, u, u} (RingHom.id R)
  have key : (adjI.leftAdjointUniq adjE).hom ≫ (adjE.leftAdjointUniq adjI).hom
      = CategoryStruct.id (𝟭 (ModuleCat.{u} R)) := by
    rw [Adjunction.leftAdjointUniq_trans, Adjunction.leftAdjointUniq_refl]
  exact NatTrans.congr_app key M

/-- **The degreewise identity case of `extendScalarsRestrictIso`.**  For `σ` equal to the identity,
absorbing `σ` into `ψ` is the collapse of restriction of scalars along `σ`, followed by the
transport from `ψ` to `ψ ∘ σ`.

Proved by substituting the identity for `σ`, after which the left unit law
`ModuleCat.extendScalars_id_comp` identifies the merge of the identity with `ψ`, and
`extendScalarsIsoRestrictScalars_hom_app_comp_extendScalarsId` closes what is left. -/
theorem extendScalarsRestrictIso_hom_app_of_eq_id (σ : R →+* R) (hσ : σ = RingHom.id R)
    (k₁ : ∀ x, σ (σ x) = x) (k₂ : ∀ y, σ (σ y) = y) (ψ : R →+* R')
    (M : ModuleCat.{u} R) :
    (extendScalarsRestrictIso.{u} σ σ k₁ k₂ ψ).hom.app M =
      (ModuleCat.extendScalars.{u, u, u} ψ).map
          ((ModuleCat.restrictScalarsId'.{u, u} σ hσ).hom.app M) ≫
        eqToHom (congrArg (fun χ => (ModuleCat.extendScalars.{u, u, u} χ).obj M)
          ((congrArg ψ.comp hσ).trans (RingHom.comp_id ψ)).symm) := by
  subst hσ
  have h := NatTrans.congr_app (ModuleCat.extendScalars_id_comp.{u} (R₁ := R) ψ) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    NatTrans.id_app] at h
  have hinv : (ModuleCat.extendScalarsComp.{u, u} (RingHom.id R) ψ).inv.app M =
      (ModuleCat.extendScalars.{u, u, u} ψ).map
        ((ModuleCat.extendScalarsId.{u} R).hom.app M) :=
    ((ModuleCat.extendScalarsComp.{u, u} (RingHom.id R) ψ).app M).inv_ext h
  simp only [extendScalarsRestrictIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, eqToHom_refl, Category.comp_id,
    hinv, ← Functor.map_comp,
    extendScalarsIsoRestrictScalars_hom_app_comp_extendScalarsId]

end Identity

end StacksDraft.DerivedRingIso

end

end
