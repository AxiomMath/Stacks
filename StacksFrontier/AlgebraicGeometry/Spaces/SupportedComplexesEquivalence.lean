module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SupportedDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkAbelian

/-!
# The derived category of a closed subspace as a subcategory of the ambient one

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`. The direct image
`i_*` of abelian sheaves on small étale sites is exact, so it needs no derivation: the functor
`D(Z_étale) ⥤ D(X_étale)` it induces is obtained by applying `i_*` degreewise, and `Ri_* = i_*`.
This file shows that it identifies `D(Z_étale)` with the full subcategory `D_{|Z|}(X_étale)` of
complexes all of whose cohomology sheaves are supported on the point set of `Z`, and that the
quasi-inverse of that equivalence is the inverse image `i^{-1}` restricted to
`D_{|Z|}(X_étale)`.

## Main definitions

* `AlgebraicGeometry.Space.derivedSmallEtaleAbelianInverseImageAdjunction` is the adjunction
  `i^{-1} ⊣ i_*` on unbounded derived categories, both functors being exact.
* `AlgebraicGeometry.Space.derivedSmallEtalePushforwardSupportedEquivalence` is the equivalence
  `D(Z_étale) ≌ D_{|Z|}(X_étale)` induced by `i_*`.

## Main results

* `AlgebraicGeometry.Space.fullyFaithfulDerivedSmallEtaleAbelianPushforward`: the functor
  `D(Z_étale) ⥤ D(X_étale)` induced by `i_*` is fully faithful, the inverse image being a left
  inverse of it.
* `AlgebraicGeometry.Space.cohomologySupportedOn_mapDerivedCategory`: a complex coming from
  `Z_étale` has all its cohomology sheaves supported on `|Z|`, and
  `AlgebraicGeometry.Space.essImage_mapDerivedCategory_of_cohomologySupportedOn` is the converse:
  a complex on `X_étale` whose cohomology sheaves are all supported on `|Z|` is the direct image
  of a complex on `Z_étale`.
* `AlgebraicGeometry.Space.derivedSmallEtalePushforwardSupportedEquivalence_functor` and
  `AlgebraicGeometry.Space.derivedSmallEtalePushforwardSupportedEquivalence_inverse`: the
  equivalence is induced by `i_*` and its quasi-inverse by `i^{-1}`.

## Implementation notes

The derived category used throughout is the standard localization of cochain complexes at the
quasi-isomorphisms, `CategoryTheory.HasDerivedCategory.standard`, installed as a local instance
of high priority; the coefficient universe is `u + 1`, the universe in which the objects of the
small étale site of an algebraic space over `Scheme.{u}` live.

## References

* [Stacks Project, Tag 0AEI](https://stacks.math.columbia.edu/tag/0AEI)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 100000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)

/-! ### Exactness of the inverse image -/

/-- The inverse image of abelian sheaves on small étale sites preserves finite colimits, being
a left adjoint. -/
theorem preservesFiniteColimits_smallEtaleAbelianInverseImage
    (hr : yoneda.relativelyRepresentable i.hom) :
    PreservesFiniteColimits (smallEtaleAbelianInverseImage B S hS i hr) :=
  have : PreservesColimitsOfSize.{0, 0} (smallEtaleAbelianInverseImage B S hS i hr) :=
    (smallEtaleAbelianInverseImageAdjunction B S hS i hr).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The inverse image of abelian sheaves on small étale sites is additive: it preserves finite
limits, in particular binary products. -/
theorem additive_smallEtaleAbelianInverseImage
    (hr : yoneda.relativelyRepresentable i.hom) :
    (smallEtaleAbelianInverseImage B S hS i hr).Additive :=
  have := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hr
  Functor.additive_of_preserves_binary_products _

/-! ### The derived adjunction of a closed immersion -/

variable (hi : IsClosedImmersion B S hS i.hom)

/-- **The adjunction `i^{-1} ⊣ i_*` on unbounded derived categories.** For a closed immersion
`i : Z ⟶ X` of algebraic spaces over `S` both functors on abelian sheaves are exact, so each
induces a functor on unbounded derived categories by applying it degreewise, and the adjunction
between them descends to those categories. -/
def derivedSmallEtaleAbelianInverseImageAdjunction :
    letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    (smallEtaleAbelianInverseImage B S hS i hi.rep).mapDerivedCategory ⊣
      (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategory := by
  letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  exact exactAdjunctionDerived (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep)

/-- **Stacks 0AEI: the pushforward is fully faithful.** For a closed immersion `i : Z ⟶ X` of
algebraic spaces over `S` the functor `D(Z_étale) ⥤ D(X_étale)` induced by the exact direct
image `i_*` of abelian sheaves is fully faithful. -/
@[stacks 0AEI "full faithfulness of the pushforward"]
def fullyFaithfulDerivedSmallEtaleAbelianPushforward :
    letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategory.FullyFaithful := by
  letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  haveI := (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).full
  haveI :=
    (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).faithful
  haveI := exactAdjunctionDerived_counit_isIso
    (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep)
  exact (exactAdjunctionDerived
    (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep)).fullyFaithfulROfIsIsoCounit

/-! ### The subcategory of complexes supported on the closed subspace -/

/-- Being supported on a subset of the point set is invariant under isomorphism in the derived
category, the cohomology sheaves being functorial. -/
theorem cohomologySupportedOn.of_iso {Y : AlgebraicSpaces B S hS}
    {T : Set (points B S hS Y.1)} {K L : smallEtaleDerivedCategory.{u + 1} B S hS Y} (e : K ≅ L)
    (hK : cohomologySupportedOn.{u + 1} B S hS Y T K) :
    cohomologySupportedOn.{u + 1} B S hS Y T L := fun n ↦
  (supportOfSheaf_subset_of_isLocallySurjective B S hS Y.1 Y.property
    ((DerivedCategory.homologyFunctor (abelianSheaves.{u + 1} B S hS Y) n).mapIso e).hom).trans
    (hK n)

/-- A complex of abelian sheaves coming from the closed subspace is supported on it: all the
cohomology sheaves of `i_*K` are supported on the point set of `Z`. -/
theorem cohomologySupportedOn_mapDerivedCategory
    (K : smallEtaleDerivedCategory.{u + 1} B S hS Z) :
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    cohomologySupportedOn.{u + 1} B S hS X (Set.range (pointsMap B S hS Z.1 i.hom))
      ((smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategory.obj K) := by
  let := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  exact fun n ↦ supportOfSheaf_subset_of_essImage B S hS i hi _ (Functor.essImage.ofIso
    (((smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategoryHomologyIso
      n).app K).symm (Functor.obj_mem_essImage _ _))

/-- On a complex supported on the closed subspace the unit of the derived adjunction is
invertible. -/
theorem isIso_derivedUnit_of_cohomologySupportedOn
    (K : smallEtaleDerivedCategory.{u + 1} B S hS X)
    (hK : cohomologySupportedOn.{u + 1} B S hS X
      (Set.range (pointsMap B S hS Z.1 i.hom)) K) :
    letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    IsIso ((derivedSmallEtaleAbelianInverseImageAdjunction B S hS i hi).unit.app K) := by
  let := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  have := (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).full
  have :=
    (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).faithful
  have hM := cohomologySupportedOn.of_iso B S hS
    (DerivedCategory.Q.objObjPreimageIso K).symm hK
  have hQ : IsIso ((derivedSmallEtaleAbelianInverseImageAdjunction B S hS i hi).unit.app
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K))) := by
    refine exactAdjunctionDerived_unit_isIso_of_homology _ _ fun n ↦ ?_
    refine (Adjunction.isIso_unit_app_iff_mem_essImage _).mpr ?_
    refine Functor.essImage.ofIso
      ((DerivedCategory.homologyFunctorFactors (abelianSheaves.{u + 1} B S hS X) n).app
        (DerivedCategory.Q.objPreimage K)) ?_
    exact (smallEtalePushforward_essImage_iff_abelian_of_isClosedImmersion B S hS i hi _).2 (hM n)
  exact ((derivedSmallEtaleAbelianInverseImageAdjunction B S hS i hi).unit.isIso_app_iff_of_iso
    (DerivedCategory.Q.objObjPreimageIso K)).mp hQ

/-- **Stacks 0AEI: essential surjectivity onto the supported subcategory.** A complex of abelian
sheaves on the small étale site of `X` all of whose cohomology sheaves are supported on the
point set of a closed immersion `i : Z ⟶ X` is isomorphic in `D(X_étale)` to the direct image of
a complex on `Z_étale`. -/
@[stacks 0AEI "essential surjectivity onto the supported subcategory"]
theorem essImage_mapDerivedCategory_of_cohomologySupportedOn
    (K : smallEtaleDerivedCategory.{u + 1} B S hS X)
    (hK : cohomologySupportedOn.{u + 1} B S hS X
      (Set.range (pointsMap B S hS Z.1 i.hom)) K) :
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategory.essImage K := by
  let := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  have := isIso_derivedUnit_of_cohomologySupportedOn B S hS i hi K hK
  exact (derivedSmallEtaleAbelianInverseImageAdjunction B S hS i hi).mem_essImage_of_unit_isIso K

include hi in
/-- **Stacks 0AEI: the equivalence.** Direct image along a closed immersion `i : Z ⟶ X` of
algebraic spaces over `S` induces an equivalence of `D(Z_étale)` with the full subcategory
`D_{|Z|}(X_étale)` of `D(X_étale)` of complexes whose cohomology sheaves are all supported on
the point set of `Z`. -/
@[stacks 0AEI "the equivalence of D(Z_étale) with D_{|Z|}(X_étale)"]
def derivedSmallEtalePushforwardSupportedEquivalence :
    smallEtaleDerivedCategory.{u + 1} B S hS Z ≌
      smallEtaleDerivedCategoryOnClosedSubspace.{u + 1} B S hS i := by
  letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  haveI := (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).full
  haveI :=
    (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).faithful
  haveI : IsIso (derivedSmallEtaleAbelianInverseImageAdjunction B S hS i hi).counit :=
    exactAdjunctionDerived_counit_isIso
      (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep)
  exact equivalenceOfUnitIso (derivedSmallEtaleAbelianInverseImageAdjunction B S hS i hi)
    (cohomologySupportedOn.{u + 1} B S hS X (Set.range (pointsMap B S hS Z.1 i.hom)))
    (cohomologySupportedOn_mapDerivedCategory B S hS i hi)
    (isIso_derivedUnit_of_cohomologySupportedOn B S hS i hi)

/-- **Stacks 0AEI: the equivalence is induced by the pushforward.** Composed with the inclusion
of `D_{|Z|}(X_étale)` into `D(X_étale)`, the forward functor of the equivalence is the functor
induced by the exact direct image `i_*`. -/
@[stacks 0AEI "the equivalence is induced by the pushforward"]
def derivedSmallEtalePushforwardSupportedEquivalence_functor :
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    (derivedSmallEtalePushforwardSupportedEquivalence B S hS i hi).functor ⋙
        (cohomologySupportedOn.{u + 1} B S hS X (Set.range (pointsMap B S hS Z.1 i.hom))).ι ≅
      (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategory := by
  letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  exact ObjectProperty.liftCompιIso _ _ _

/-- **Stacks 0AEI: the quasi-inverse is the inverse image.** The quasi-inverse of the
equivalence is the functor induced by the exact inverse image `i^{-1}`, restricted to
`D_{|Z|}(X_étale)`. -/
@[stacks 0AEI "the identification of the quasi-inverse with the inverse image"]
def derivedSmallEtalePushforwardSupportedEquivalence_inverse :
    letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
    (derivedSmallEtalePushforwardSupportedEquivalence B S hS i hi).inverse ≅
      (cohomologySupportedOn.{u + 1} B S hS X
          (Set.range (pointsMap B S hS Z.1 i.hom))).ι ⋙
        (smallEtaleAbelianInverseImage B S hS i hi.rep).mapDerivedCategory := by
  letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  exact Iso.refl _

end AlgebraicGeometry.Space

end
