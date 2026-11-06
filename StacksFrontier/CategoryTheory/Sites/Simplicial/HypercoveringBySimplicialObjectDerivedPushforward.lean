module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace

/-!
# The derived direct image along a hypercovering by a simplicial object of the site

Let `C` be a site with fibre products given by a pretopology `P`, let `X` be an object of `C`,
let `U` be a simplicial object of `C` and let `a : U ⟶ X` be an augmentation which is a
hypercovering of `X` in `C` in the sense of Stacks 09X8, that is, which satisfies the three
covering conditions of
`Stacks.CategoryTheory.Hypercovering.IsHypercoveringAugmentation`. Such an augmentation
determines the one-summand simplicial semi-representable object `n ↦ {U_n ⟶ X}` over `X`, its
total site `(C/U)_total`, and the augmentation of topoi `a : Sh((C/U)_total) ⟶ Sh(C/X)`.

Stacks 0D8N asserts that for every `E` of the unbounded derived category `D(C/X)` of abelian
sheaves on `C/X` the canonical map

`E ⟶ Ra_* a^{-1} E`

is an isomorphism; the source deduces it as a special case of Stacks 0D8L, the same assertion
for an arbitrary hypercovering of `X` by semi-representable objects. That deduction is what is
carried out here, the canonical map being the one of Stacks 0D8L at the associated simplicial
semi-representable object, so no second map is built.

Stacks 0D8L is available in this library only granted two inputs. The specialization discharges
the first of them from the hypercovering conditions on `a` together with local fullness of the
localization functor `j_total`, and weakens the second to a statement about K-injective
complexes only. What remains carried is that local fullness — the clause of Stacks 0D8E which
the library does not prove — and the `Ra_*`-acyclicity of `a^{-1}` of a K-injective complex.
Accordingly nothing unconditional is claimed; see the implementation notes.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.derivedAugmentationUnitAugmented`: the canonical
  map `E ⟶ Ra_* a^{-1} E` on `D(C/X)` for a hypercovering by a simplicial object of the site,
  namely the map of Stacks 0D8L at the associated simplicial semi-representable object.

## Main results

* `CategoryTheory.NatTrans.isIso_mapHomologicalComplex_app`,
  `.isIso_mapHomotopyCategory_app` and `.isIso_mapHomotopyCategory`: an invertible natural
  transformation of additive functors stays invertible degreewise on complexes and on the
  homotopy categories.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_homotopyAugmentationUnitOver`: the
  augmentation unit of Stacks 0D8L read on unbounded homotopy categories is invertible as soon
  as the augmentation unit on abelian sheaves is.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_derivedAugmentationUnitOver_of_isIso_unit`:
  Stacks 0D8L with its first input replaced by invertibility of the underived augmentation unit
  and its second asked only at the K-injective complexes.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_derivedAugmentationUnitAugmented_app`:
  **Stacks 0D8N**, granted local fullness of `j_total` and the `Ra_*`-acyclicity of `a^{-1}` of
  a K-injective complex.

## Implementation notes

The hypothesis that `C` has fibre products is the `HasPullbacks C` instance. It is what makes
`Over X` have pullbacks, hence makes the localized topology `P.toGrothendieck.over X` admit
pullbacks of coverings, which the simplicial family of sites of Stacks 0D8B requires; it also
makes the coskeleta appearing in the hypercovering conditions exist, so that
`IsHypercoveringAugmentation` is well formed at all.

The hypercovering hypothesis `h` is load-bearing and is used exactly once: through
`CategoryTheory.SimplicialSemiRepresentable.isCoverDense_totalForget_augmented`, its
degree-zero clause makes `{U₀ ⟶ X}` a covering family of `X` and hence makes `j_total` cover
dense. Cover density is what, together with local fullness, makes `a^{-1}` fully faithful on
abelian sheaves and so makes the underived unit `F ⟶ a_* a^{-1} F` invertible, which is
Stacks 0DA8 (2) as carried by
`CategoryTheory.SimplicialSemiRepresentable.isIso_abelianUnit_augmented`. Without the
degree-zero clause that unit is not available and the first input of Stacks 0D8L could not be
discharged.

Passing from the underived unit to the hypothesis `hunit` of Stacks 0D8L is the content of
`isIso_homotopyAugmentationUnitOver`: the unit of Stacks 0D8L on unbounded homotopy categories
is the degreewise unit conjugated by two canonical isomorphisms, and an invertible natural
transformation of additive functors stays invertible after `NatTrans.mapHomotopyCategory`,
because its components there are the images under the quotient of morphisms of complexes which
are invertible in every degree.

Two things remain carried, and neither is discharged anywhere here.

* `hlf`, local fullness of `j_total` for the topology of `C/X`. This is the clause of
  Stacks 0D8E which the library does not prove; the implementation notes of
  `StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringObjectDescent.lean` identify it as
  the local existence of a `p`-simplex of the hypercovering carrying two prescribed charts on
  complementary faces, of which the library has only the coskeleton form. It is the same
  hypothesis that every conditional clause of Stacks 0DA8 in
  `StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringBySimplicialObject.lean` carries.
* `hacyclic`, that the direct image of `a^{-1}` of a K-injective complex needs no derivation.
  This is the vanishing of `R^p a_* a^{-1}` in positive degrees, which the source reads off the
  spectral sequence of Stacks 0D7A. That spectral sequence *is* built in this library, as
  `CategoryTheory.SimplicialSiteSituation.Augmentation.spectralSequence` of
  `StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationSpectralSequence.lean`, but it is
  built as a bare first-quadrant spectral sequence of abelian sheaves — pages and differentials
  and nothing else. Its convergence to `R^{p+q} a_* F` is not asserted there and is blocked: the
  total complex of the underlying double complex computes `R a_* F` only once the rows of the
  complex of Stacks 0D79 are exact in positive degrees, and
  `StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationCechComplex.lean` has that exactness
  only in the two lowest degrees, positive-degree exactness needing the resolution of
  Stacks 0D78 together with the injective-resolution argument that applies it; the resolution
  itself is `CategoryTheory.SimplicialSiteSituation.Augmentation.resolution`. Neither is the first page of that sequence
  identified with `R^q a_{p,*} K_p`; the two other Stacks 0D7A clauses in
  `AugmentationFirstPage.lean` and `AugmentationComponentPushforwardAb.lean` supply that term and
  its attachment to the double complex, not the identification. Without convergence the sequence
  says nothing about `R^p a_*`, so `hacyclic` cannot be read off it.

  `hacyclic` is in any case not automatic: `a^{-1}` is a left adjoint, and the comparison
  `a_* ⟶ Ra_*` is invertible at K-injective complexes of the total site, not at the inverse
  images of K-injective complexes of `C/X`. It is asked only at the K-injective complexes, which
  is where the source's argument supplies it; the reduction of the unbounded statement to those
  complexes is `Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives`.

The derived categories are the standard ones, `CategoryTheory.HasDerivedCategory.standard`,
installed as a local instance as in the neighbouring files, and the additivity, exactness and
derived-functor-existence facts of Stacks 0D8L are re-installed as local instances here for the
same reason: no choice of model or of resolution leaks out of this module.

## References

* [Stacks Project, Tag 0D8N](https://stacks.math.columbia.edu/tag/0D8N)
* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0DA8](https://stacks.math.columbia.edu/tag/0DA8)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-! ### Invertible natural transformations on complexes -/

section MapComplexes

variable {ι : Type*} {V : Type*} [Category V] [Preadditive V] {W : Type*} [Category W]
  [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive]

/-- An invertible natural transformation of additive functors induces, on categories of
homological complexes, a natural transformation which is invertible at every complex: its
component at a complex is the original component in every degree. -/
theorem NatTrans.isIso_mapHomologicalComplex_app (α : F ⟶ G) [IsIso α] (c : ComplexShape ι)
    (L : HomologicalComplex V c) :
    IsIso ((NatTrans.mapHomologicalComplex α c).app L) := by
  have : ∀ n : ι, IsIso (((NatTrans.mapHomologicalComplex α c).app L).f n) :=
    fun n => inferInstanceAs (IsIso (α.app (L.X n)))
  exact HomologicalComplex.Hom.isIso_of_components _

/-- An invertible natural transformation of additive functors induces, on homotopy categories, a
natural transformation which is invertible at every object: every object of the homotopy
category is the class of a complex, and there the component is the image under the quotient of
an invertible morphism of complexes. -/
theorem NatTrans.isIso_mapHomotopyCategory_app (α : F ⟶ G) [IsIso α] (c : ComplexShape ι)
    (M : HomotopyCategory V c) :
    IsIso ((NatTrans.mapHomotopyCategory α c).app M) := by
  obtain ⟨M⟩ := M
  have := NatTrans.isIso_mapHomologicalComplex_app α c M
  rw [NatTrans.mapHomotopyCategory_app]
  exact ((HomotopyCategory.quotient W c).mapIso
    (asIso ((NatTrans.mapHomologicalComplex α c).app M))).isIso_hom

/-- An invertible natural transformation of additive functors stays invertible on homotopy
categories. -/
theorem NatTrans.isIso_mapHomotopyCategory (α : F ⟶ G) [IsIso α] (c : ComplexShape ι) :
    IsIso (NatTrans.mapHomotopyCategory α c) :=
  (NatTrans.isIso_iff_isIso_app _).mpr fun M =>
    NatTrans.isIso_mapHomotopyCategory_app α c M

end MapComplexes

end CategoryTheory

namespace CategoryTheory.SimplicialSemiRepresentable

open Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard additive_abelianTotalPushforwardOver
  additive_abelianTotalInverseImageOver preservesFiniteColimits_abelianTotalInverseImageOver
  hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforwardOver
  hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver

/-! ### The first input of Stacks 0D8L from the underived augmentation unit -/

section Over

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C) (X : C)
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- The augmentation unit of Stacks 0D8L read on unbounded homotopy categories is invertible as
soon as the augmentation unit `F ⟶ a_* a^{-1} F` on abelian sheaves is.

The former is the latter conjugated by two canonical isomorphisms, and an invertible natural
transformation of additive functors stays invertible on homotopy categories. -/
theorem isIso_homotopyAugmentationUnitOver
    (hunit : IsIso (abelianTotalAdjunctionOver J X K).unit) :
    IsIso (homotopyAugmentationUnitOver J X K) := by
  have := hunit
  have := NatTrans.isIso_mapHomotopyCategory (abelianTotalAdjunctionOver J X K).unit
    (ComplexShape.up ℤ)
  delta homotopyAugmentationUnitOver
  infer_instance

/-- **Stacks 0D8L** with both of its inputs traded for the statements the source's argument
actually supplies: the canonical map `E ⟶ Ra_* a^{-1} E` on `D(C/X)` is invertible as soon as
the augmentation unit `F ⟶ a_* a^{-1} F` on abelian sheaves is invertible and the direct image
of `a^{-1}` of a *K-injective* complex needs no derivation.

Both hypotheses are carried. What this contributes over
`isIso_derivedAugmentationUnitOver_app` is that the first is now a statement about abelian
sheaves rather than about every complex, and that the second is asked only at the K-injective
complexes: a morphism of functors out of the unbounded derived category is invertible as soon as
it is invertible there, which is how the conclusion still holds at every object of `D(C/X)`. -/
theorem isIso_derivedAugmentationUnitOver_of_isIso_unit
    (hunit : IsIso (abelianTotalAdjunctionOver J X K).unit)
    (hacyclic : ∀ I : CochainComplex (AbelianSheavesOver J X) ℤ, I.IsKInjective →
      IsIso ((derivedAbelianTotalPushforwardOverUnit J X K).app
        (((abelianTotalInverseImageOver J X K).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (AbelianSheavesOver J X)
            (ComplexShape.up ℤ)).obj I)))) :
    IsIso (derivedAugmentationUnitOver J X K) := by
  have := isIso_homotopyAugmentationUnitOver J X K hunit
  refine Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives _ fun I hI => ?_
  have hqh := isIso_derivedAugmentationUnitOverQh_app J X K
    ((HomotopyCategory.quotient (AbelianSheavesOver J X) (ComplexShape.up ℤ)).obj I)
    (NatIso.isIso_app_of_isIso _ _) (hacyclic I hI)
  have hw : IsIso ((Functor.whiskerLeft DerivedCategory.Qh
      (derivedAugmentationUnitOver J X K)).app
        ((HomotopyCategory.quotient (AbelianSheavesOver J X)
          (ComplexShape.up ℤ)).obj I)) := by
    rw [whiskerLeft_derivedAugmentationUnitOver]
    exact hqh
  exact hw

end Over

/-! ### Stacks 0D8N -/

section Augmented

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-- **The canonical map `E ⟶ Ra_* a^{-1} E`** on the unbounded derived category of abelian
sheaves on `C/X`, for the augmentation of the total site of an augmented simplicial object
`a : U ⟶ X` of the site.

It is the map of Stacks 0D8L at the associated one-summand simplicial semi-representable object
`n ↦ {U_n ⟶ X}` over `X`, hence is descended from the unit of the augmentation adjunction
through the universal property of the localization, and is not a chosen map. Nothing here
constrains `a`: the map exists for every augmented simplicial object of the site. -/
abbrev derivedAugmentationUnitAugmented :
    𝟭 (DerivedCategory (AbelianSheavesOver P.toGrothendieck X)) ⟶
      derivedAbelianTotalInverseImageOver P.toGrothendieck X
          (associatedSimplicialObject.{u} U a) ⋙
        derivedAbelianTotalPushforwardOver P.toGrothendieck X
          (associatedSimplicialObject.{u} U a) :=
  derivedAugmentationUnitOver P.toGrothendieck X (associatedSimplicialObject.{u} U a)

/-- **Stacks Project, Tag 0D8N**, granted the two inputs this library does not have. For a site
`C` with fibre products, an object `X` of `C` and a hypercovering `a : U ⟶ X` of `X` in `C` by a
simplicial object `U` of `C`, the canonical map `E ⟶ Ra_* a^{-1} E` is an isomorphism for every
object `E` of the unbounded derived category of abelian sheaves on `C/X`.

`E` is arbitrary: no boundedness is assumed and the coefficients are all abelian sheaves. The
source deduces this from Stacks 0D8L for the associated simplicial semi-representable object
over `X`, and that is the deduction performed, the hypercovering conditions on `a` entering
through cover density of `j_total`.

The two carried hypotheses are the ones discussed in the module docstring. `hlf`, local fullness
of `j_total`, is the clause of Stacks 0D8E which the library does not prove; together with the
degree-zero clause of `h` it supplies the underived unit `F ⟶ a_* a^{-1} F` of Stacks 0DA8 (2),
which is the first input of Stacks 0D8L. `hacyclic` says that the direct image of `a^{-1}` of a
K-injective complex needs no derivation, that is, that `R^p a_* a^{-1}` vanishes in positive
degrees; the source reads that off the spectral sequence of Stacks 0D7A, which this library
builds but without the convergence to `R^{p+q} a_*` that the reading needs. No unconditional
invertibility is claimed. -/
@[stacks 0D8N "granted two inputs this library does not have: local fullness of j_total,
which is the unproved clause of Tag 0D8E, and the Ra_*-acyclicity of a⁻¹ of a K-injective
complex, which is the content of the spectral sequence of Tag 0D7A;
the isomorphism is not proved unconditionally"]
theorem isIso_derivedAugmentationUnitAugmented_app
    (h : IsHypercoveringAugmentation P U a)
    (hlf : (totalForget (associatedSimplicialObject.{u} U a)).IsLocallyFull
      (P.toGrothendieck.over X))
    (hacyclic : ∀ I : CochainComplex (AbelianSheavesOver P.toGrothendieck X) ℤ,
      I.IsKInjective →
        IsIso ((derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X
          (associatedSimplicialObject.{u} U a)).app
            (((abelianTotalInverseImageOver P.toGrothendieck X
              (associatedSimplicialObject.{u} U a)).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj
                  ((HomotopyCategory.quotient (AbelianSheavesOver P.toGrothendieck X)
                    (ComplexShape.up ℤ)).obj I))))
    (E : DerivedCategory (AbelianSheavesOver P.toGrothendieck X)) :
    IsIso ((derivedAugmentationUnitAugmented P U a).app E) :=
  have := isIso_derivedAugmentationUnitOver_of_isIso_unit P.toGrothendieck X
    (associatedSimplicialObject.{u} U a) (isIso_abelianUnit_augmented P U a h hlf) hacyclic
  NatIso.isIso_app_of_isIso _ E

end Augmented

end CategoryTheory.SimplicialSemiRepresentable

end
