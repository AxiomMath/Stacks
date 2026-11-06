module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective

/-!
# The right derived functor on `D⁺` is the restriction of the one on `D`

Let `A` and `B` be abelian categories, `A` with enough injectives and with K-injective
resolutions, and let `F : A ⥤ B` be additive. Two right derived functors of `F` are then in
play: `RF⁺ : D⁺(A) ⥤ D⁺(B)`, built from injective resolutions, and an unbounded
`RF : D(A) ⥤ D(B)` with its comparison `α`, built from K-injective ones. This file identifies
them on the bounded below objects: the square

```
D⁺(A) --RF⁺--> D⁺(B)
  |              |
  ι              ι
  v              v
D(A) ---RF----> D(B)
```

commutes up to a canonical isomorphism, pinned by its compatibility with the two comparison maps
out of degreewise `F`.

**Nothing here is new mathematics.** The identification is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/BoundedComparison.lean` with the
sheaf direct image replaced by an arbitrary additive functor — that declaration is this one at
`RingedSpaceModuleAdjunction.modulePushforward`, and no step of its argument used the direct
image. The generality is what a statement about *sections* needs: the two halves of conclusion
(c) of [Stacks, Tag 0EX3] meet the top higher direct image through
`CategoryTheory.Functor.rightDerivedPlus` on one side and through the unbounded model on the
other, and the functors to be crossed there are sections over an open and sections over an
inverse image.

## Main definitions

All in the namespace `CategoryTheory.Functor`.

* `boundedToDerivedCategory`: degreewise `F` on a bounded below complex, read in `D(B)`. Both
  derived functors are right derived functors of this one.
* `boundedUnitPlus` and `boundedUnitBig`: the two comparison maps out of it, through `RF⁺` and
  through `RF`.
* `boundedDerivedIso`: **`RF⁺` followed by `D⁺(B) ⥤ D(B)` is `D⁺(A) ⥤ D(A)` followed by `RF`.**

## Main results

* `isIso_boundedUnitPlus_app` and `isIso_boundedUnitBig_app`: both comparison maps are invertible
  on the bounded below complexes of injective objects.
* `boundedDerivedIso_fac` and `boundedDerivedIso_hom_app`: **the isomorphism carries the
  comparison map through `RF⁺` to the one through `RF`**, which determines it uniquely.

## Where this is specialized

The crossing exists publicly nowhere else at this generality. A convention-independent sweep first
reported seven sites; re-derived, the honest count is **three candidates besides the one already
retired**, and **no instantiation of any of them is yet verified**. None is touched here.

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso` —
  `Topology/Sheaves/Cohomology/DerivedPushforward/BoundedComparison.lean:177`. Retired to
  instantiations of this file; the only verified one.
* `derivedSectionsWithSupportInPlusIso` —
  `RingTheory/LocalCohomology/BaseChangeGeneralSupport.lean:243`.
* `derivedSectionsUnboundedιIso` —
  `AlgebraicGeometry/PseudoCoherent/DerivedSectionsUnbounded.lean:178`. Subsumed only up to
  `Iso.symm`.
* `nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso` —
  `RingTheory/LocalCohomology/BoundedComparison.lean:131`. Carries `@[stacks 0EF4]`, and states
  `Nonempty` of the isomorphism, so at most its **proof** changes and it is never deleted.

Three earlier claims were withdrawn and should not be re-raised:
`localCohomologyFunctorPlusCompιIso`
(`RingTheory/Dualizing/LocalCohomology/CompositionSpectralSequence.lean:186`) is a **t-structure
lift**, a different theorem with a similar type; the three sites in
`Algebra/Homology/DerivedCategory/PlusCoproducts.lean` take their comparison for **arbitrary**
functors, so they are general transfer lemmas that would *call* a crossing rather than consumers
of this one; and the four-named collapse group varies along three independent axes with no
containment.

*A name collision to keep clear of.* `Stacks.DerivedIndexing.rightDerivedPlusCompIso`
(`Homology/DerivedIndexing/Composite.lean:324`) is a different theorem — [Stacks, Tag 015M],
`R(Q ∘ P) ≅ RQ ∘ RP`, with no `Plus.ι` in it — and shares its identifier with the `private`
crossing in `Homology/Tor/DerivedExtensionScalars.lean:1008`. Neither is this.

## Implementation notes

Both composites are right derived functors of one and the same functor `K⁺(A) ⥤ D(B)` —
degreewise `F` followed by localization — along `Qh : K⁺(A) ⥤ D⁺(A)`, so the isomorphism is
`CategoryTheory.Functor.rightDerivedUnique`. That both are right derived functors is the
injective derivability structure of `K⁺`: a comparison map is the unit of a right derived functor
exactly when it is invertible on the bounded below complexes of injective objects. For the `RF⁺`
side that is inherited from the unit of `RF⁺` and preserved by the fully faithful
`D⁺(B) ⥤ D(B)`; for the `RF` side it is because a bounded below complex with injective terms is
K-injective, and K-injective complexes compute the unbounded right derived functor.

The two coherences this rests on hold by `rfl`, so no transport appears in the statements:
`Qh : K⁺ ⥤ D⁺` followed by `D⁺ ⥤ D` is the inclusion `K⁺ ⥤ K` followed by `Qh : K ⥤ D`
(Mathlib's `DerivedCategory.Plus.QhCompιIsoιCompQh` is `Iso.refl`), and degreewise `F` on `K⁺`
followed by `K⁺ ⥤ K` is `K⁺ ⥤ K` followed by degreewise `F` on `K`. That is why no analogue of
the coherence isomorphisms built inside the proof of
`Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic` is needed.

The existence of K-injective resolutions is the hypothesis `hres`, as in
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso`, rather than an instance; over a
Grothendieck abelian category it is
`Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian`.

## References

* [Stacks Project, Tag 05T5](https://stacks.math.columbia.edu/tag/05T5)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v u vB uB wD wE

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wD} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wE} B]
  (F : A ⥤ B) [F.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)

/-- Degreewise `F` on a bounded below complex, read in `D(B)`. Both right derived functors of `F`
are right derived functors of this one. -/
abbrev boundedToDerivedCategory : HomotopyCategory.Plus A ⥤ DerivedCategory B :=
  HomotopyCategory.Plus.ι A ⋙
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

/-- The comparison `F K ⟶ RF⁺ K` from degreewise `F` on a bounded below complex to the right
derived functor computed on `D⁺`, read in `D(B)`. -/
def boundedUnitPlus :
    boundedToDerivedCategory F ⟶
      DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) :=
  Functor.whiskerRight F.rightDerivedFunctorPlusUnith DerivedCategory.Plus.ι

/-- The comparison `F K ⟶ RF K` from degreewise `F` on a bounded below complex to the unbounded
right derived functor. -/
def boundedUnitBig :
    boundedToDerivedCategory F ⟶
      DerivedCategory.Plus.Qh ⋙ (DerivedCategory.Plus.ι ⋙ RF) :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι A) α

/-- The component of `boundedUnitPlus F` at `K` is the image under `D⁺(B) ⥤ D(B)` of the
component at `K` of the unit of `RF⁺`. -/
@[simp]
theorem boundedUnitPlus_app (K : HomotopyCategory.Plus A) :
    (boundedUnitPlus F).app K =
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app K) :=
  rfl

omit [EnoughInjectives A] in
/-- The component of `boundedUnitBig F RF α` at `K` is the component of `α` at the underlying
complex of `K`. -/
@[simp]
theorem boundedUnitBig_app (K : HomotopyCategory.Plus A) :
    (boundedUnitBig F RF α).app K = α.app ((HomotopyCategory.Plus.ι A).obj K) :=
  rfl

/-- The comparison through `RF⁺` is invertible on a bounded below complex of injective objects:
it is the image under the fully faithful `D⁺(B) ⥤ D(B)` of the unit of `RF⁺`, which is invertible
there. -/
instance isIso_boundedUnitPlus_app (Z : HomotopyCategory.Plus (InjectiveObject A)) :
    IsIso ((boundedUnitPlus F).app ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z)) := by
  rw [boundedUnitPlus_app]
  have h : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z)) :=
    (HomotopyCategory.Plus.localizerMorphism_derives
        (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).isIso_of_isRightDerivedFunctor
      F.rightDerivedFunctorPlusUnith Z
  exact @Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Plus.ι _ h

omit [EnoughInjectives A] in
/-- The comparison through the unbounded `RF` is invertible on a bounded below complex of
injective objects: such a complex is K-injective, and K-injective complexes compute the unbounded
right derived functor. -/
theorem isIso_boundedUnitBig_app
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (Z : HomotopyCategory.Plus (InjectiveObject A)) :
    IsIso ((boundedUnitBig F RF α).app
      ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z)) := by
  obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff
    ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z).obj.as).1
    ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z).2
  have := hn
  have hKI : CochainComplex.IsKInjective
      ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z).obj.as :=
    CochainComplex.isKInjective_of_injective _ n
  rw [boundedUnitBig_app]
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres).2
      DerivedCategory.Qh RF α _ hKI

/-- `RF⁺` followed by `D⁺(B) ⥤ D(B)`, with `boundedUnitPlus F`, is a right derived functor of
`boundedToDerivedCategory F` with respect to the quasi-isomorphisms of `K⁺(A)`. -/
instance isRightDerivedFunctor_boundedUnitPlus :
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).IsRightDerivedFunctor
      (boundedUnitPlus F) (HomotopyCategory.Plus.quasiIso A) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (boundedToDerivedCategory F)).isRightDerivedFunctor_of_isIso
    (boundedUnitPlus F) (fun _ => inferInstance)

/-- If every complex admits a quasi-isomorphism to a K-injective complex, then `D⁺(A) ⥤ D(A)`
followed by `RF`, with `boundedUnitBig F RF α`, is a right derived functor of
`boundedToDerivedCategory F` with respect to the quasi-isomorphisms of `K⁺(A)`. -/
theorem isRightDerivedFunctor_boundedUnitBig
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    (DerivedCategory.Plus.ι ⋙ RF).IsRightDerivedFunctor (boundedUnitBig F RF α)
      (HomotopyCategory.Plus.quasiIso A) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (boundedToDerivedCategory F)).isRightDerivedFunctor_of_isIso
    (boundedUnitBig F RF α) (fun Z => isIso_boundedUnitBig_app F RF α hres Z)

/-- **The right derived functor on `D⁺(A)` is the restriction of the one on `D(A)`**: an
isomorphism `RF⁺ ⋙ ι ≅ ι ⋙ RF` of functors `D⁺(A) ⥤ D(B)`. It is the uniqueness isomorphism of
the two right derived functors of degreewise `F` on `K⁺(A)`. -/
def boundedDerivedIso
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ RF :=
  haveI := isRightDerivedFunctor_boundedUnitBig F RF α hres
  Functor.rightDerivedUnique _ _ (boundedUnitPlus F) (boundedUnitBig F RF α)
    (HomotopyCategory.Plus.quasiIso A)

/-- **The comparison that pins the isomorphism**: it carries the comparison map `F K ⟶ RF⁺ K` to
the comparison map `F K ⟶ RF K`. Together with the uniqueness of transformations out of a right
derived functor this determines it. -/
theorem boundedDerivedIso_fac
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    boundedUnitPlus F ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (boundedDerivedIso F RF α hres).hom =
      boundedUnitBig F RF α := by
  have := isRightDerivedFunctor_boundedUnitBig F RF α hres
  simp [boundedDerivedIso]

/-- **The componentwise form of the pinning comparison**: at a bounded below complex `K` the
isomorphism takes the image in `D(B)` of the comparison `F K ⟶ RF⁺ K` to the comparison
`F K ⟶ RF K`. -/
theorem boundedDerivedIso_hom_app
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (K : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        (boundedDerivedIso F RF α hres).hom.app (DerivedCategory.Plus.Qh.obj K) =
      α.app ((HomotopyCategory.Plus.ι A).obj K) :=
  NatTrans.congr_app (boundedDerivedIso_fac F RF α hres) K

end CategoryTheory.Functor

end
