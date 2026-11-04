module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectDerivedPushforward

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
  itself is `CategoryTheory.SimplicialSiteSituation.Augmentation.resolution`. Neither is the first
  page of that sequence identified with `R^q a_{p,*} K_p`; the two other Stacks 0D7A clauses in
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

end CategoryTheory

namespace CategoryTheory.SimplicialSemiRepresentable

open Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard additive_abelianTotalPushforwardOver
  additive_abelianTotalInverseImageOver preservesFiniteColimits_abelianTotalInverseImageOver
  hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforwardOver
  hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver

/-! ### The first input of Stacks 0D8L from the underived augmentation unit -/

/-! ### The first input of Stacks 0D8L discharged for a hypercovering -/

section OverHypercovering

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- **The first input of Stacks 0D8L, for a hypercovering of `X` by semi-representable objects.**
The augmentation unit of Stacks 0D8L read on unbounded homotopy categories is invertible, with
nothing carried, as soon as `K` is a hypercovering of `X`.

This is the `hunit` hypothesis of
`CategoryTheory.SimplicialSemiRepresentable.isIso_derivedAugmentationUnitOver_app`: its component
at a complex `M` is `NatIso.isIso_app_of_isIso` of this. What supplies it is the degree-zero
identification `M = a_* a^{-1} M` of Stacks 0D8K (2),
`CategoryTheory.SimplicialSemiRepresentable.isIso_abelianUnit_over`, which the hypercovering
conditions on `K` give through cover density and local fullness of `j_total`; passing from it to
the homotopy categories is `isIso_homotopyAugmentationUnitOver`.

The hypercovering hypothesis is what is doing the work and cannot be dropped: for an arbitrary
simplicial semi-representable object `K` over `X` the inverse image `a^{-1}` is not fully
faithful and this unit is not invertible. -/
theorem isIso_homotopyAugmentationUnitOver_of_isHypercovering (hK : IsHypercovering P K) :
    IsIso (homotopyAugmentationUnitOver P.toGrothendieck X K) :=
  isIso_homotopyAugmentationUnitOver P.toGrothendieck X K (isIso_abelianUnit_over P K hK)

/-- **Stacks Project, Tag 0D8L**, granted the one input this library does not have. For a site
`C` with fibre products, an object `X` of `C` and a hypercovering `K` of `X` by semi-representable
objects, the canonical map `E ⟶ Ra_* a^{-1} E` is an isomorphism for every object `E` of the
unbounded derived category of abelian sheaves on `C/X`.

`E` is arbitrary: no boundedness is assumed and the coefficients are all abelian sheaves.

Of the two inputs carried by `isIso_derivedAugmentationUnitOver_app`, the first is discharged
here from the hypercovering conditions on `K` alone, by
`isIso_homotopyAugmentationUnitOver_of_isHypercovering`; that theorem states the same
invertibility for an arbitrary `K` and so has to carry it. What remains is `hacyclic`, that the
direct image of `a^{-1}` of a K-injective complex needs no derivation, that is, that
`R^p a_* a^{-1}` vanishes in positive degrees; the source reads that off the spectral sequence of
Stacks 0D7A, which this library builds but without the convergence to `R^{p+q} a_*` that the
reading needs. It is asked only at the K-injective complexes, which is where the source's
argument supplies it. No unconditional invertibility is claimed. -/
@[stacks 0D8L "for a hypercovering K of X by semi-representable objects, with the
Ra_*-acyclicity of a⁻¹ of a K-injective complex taken as an explicit input; the degree-zero
identification M = a_*a⁻¹M is discharged here from the hypercovering conditions, being Tag 0D8K
part (2). The acyclicity is discharged, and this tag carried unconditionally, by
...SimplicialSemiRepresentable
.isIso_derivedAugmentationUnitOver_app_of_isHypercovering_unconditional"]
theorem isIso_derivedAugmentationUnitOver_app_of_isHypercovering (hK : IsHypercovering P K)
    (hacyclic : ∀ I : CochainComplex (AbelianSheavesOver P.toGrothendieck X) ℤ,
      I.IsKInjective →
        IsIso ((derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X K).app
          (((abelianTotalInverseImageOver P.toGrothendieck X K).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient (AbelianSheavesOver P.toGrothendieck X)
                (ComplexShape.up ℤ)).obj I))))
    (E : DerivedCategory (AbelianSheavesOver P.toGrothendieck X)) :
    IsIso ((derivedAugmentationUnitOver P.toGrothendieck X K).app E) :=
  have := isIso_derivedAugmentationUnitOver_of_isIso_unit P.toGrothendieck X K
    (isIso_abelianUnit_over P K hK) hacyclic
  NatIso.isIso_app_of_isIso _ E

end OverHypercovering

/-! ### Stacks 0D8N -/

section Augmented

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-- **Stacks Project, Tag 0D8N**, granted the one input this library does not have. For a site
`C` with fibre products, an object `X` of `C` and a hypercovering `a : U ⟶ X` of `X` in `C` by a
simplicial object `U` of `C`, the canonical map `E ⟶ Ra_* a^{-1} E` is an isomorphism for every
object `E` of the unbounded derived category of abelian sheaves on `C/X`.

`E` is arbitrary: no boundedness is assumed and the coefficients are all abelian sheaves. The
source deduces this from Stacks 0D8L for the associated simplicial semi-representable object
over `X`, and that is the deduction performed, the hypercovering conditions on `a` entering
through cover density and local fullness of `j_total`.

The first input of Stacks 0D8L is discharged from the hypercovering conditions alone: it is the
underived unit `F ⟶ a_* a^{-1} F` of Stacks 0DA8 (2),
`CategoryTheory.SimplicialSemiRepresentable.isIso_abelianUnit_augmented'`. What remains carried
is the hypothesis discussed in the module docstring: `hacyclic` says that the direct image of
`a^{-1}` of a K-injective complex needs no derivation, that is, that `R^p a_* a^{-1}` vanishes in
positive degrees; the source reads that off the spectral sequence of Stacks 0D7A, which this
library builds but without the convergence to `R^{p+q} a_*` that the reading needs. No
unconditional invertibility is claimed. -/
@[stacks 0D8N "with the Ra_*-acyclicity of a⁻¹ of a K-injective complex taken as an explicit
input. It is discharged, and this tag carried unconditionally, by
...SimplicialSemiRepresentable.isIso_derivedAugmentationUnitAugmented_app_unconditional"]
theorem isIso_derivedAugmentationUnitAugmented_app'
    (h : IsHypercoveringAugmentation P U a)
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
    (associatedSimplicialObject.{u} U a) (isIso_abelianUnit_augmented' P U a h) hacyclic
  NatIso.isIso_app_of_isIso _ E

end Augmented

end CategoryTheory.SimplicialSemiRepresentable

end
