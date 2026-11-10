module

public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraIsoComparison

/-!
# The total space of a line bundle is the vector bundle of its invertible module

`Stacks.LineBundle.Situation.totalSpace` and `AlgebraicGeometry.Scheme.Modules.vectorBundle` are
both the relative spectrum of `Sym(L)` over the scheme on which `L` lives, and both are
`Stacks.AffineAlgebraEquivalence.relativeSpec` of a sheaf of commutative `𝒪_X`-algebras. They are
nevertheless **not** the same scheme on the nose, because the two algebra sheaves are not the
same object: `Stacks.RelativeSpec.ungradedAlgebraSheaf`, which the total space uses, lifts the
objectwise direct sum `⨁ₙ Symⁿ(L)` to `CommRingCat` and then sheafifies there, while
`Stacks.RelativeSpec.gradedAlgebraSheaf`, which the vector bundle uses, sheafifies in `RingCat`
and lifts afterwards. Sheafification and the forgetful functor commute, so the two differ by a
comparison isomorphism and not by any mathematical content; this file constructs that
isomorphism and carries it through the relative spectrum.

The consequence is that the zero-section theory stated for the total space — in particular
`Stacks.Chow.isEffectiveCartierDivisor_ker_zeroSection` and
`Stacks.Chow.ker_zeroSection_eq_zeroScheme` — becomes available for a vector bundle, which is
the shape `Stacks.Conormal.normalBundle` is given in.

## Main definitions

* `Stacks.RelativeSpec.ungradedToGradedRight`: the comparison of the two ungraded realizations,
  as a morphism of sheaves of commutative rings.
* `Stacks.RelativeSpec.ungradedAlgebraSheafIsoGradedAlgebraSheaf`: **the two ungraded
  realizations are isomorphic as sheaves of commutative `𝒪_X`-algebras**, i.e. in
  `Stacks.RelativeSpec.AlgebraSheaf X = CategoryTheory.Under X.sheaf`.
* `Stacks.LineBundle.Situation.totalSpaceIsoVectorBundle`: **the total space of a line bundle is
  the vector bundle of its invertible module.**

## Main results

* `Stacks.RelativeSpec.unit_comp_sheafifyForgetToRingIso_inv`: **the two sheafification units
  agree across `Stacks.ModuleUp.sheafifyForgetToRingIso`** — sheafifying a presheaf of
  commutative rings and then forgetting commutativity has the same unit as forgetting first and
  sheafifying in `RingCat`. This is the one step the comparison needed, and it is Mathlib's
  `CategoryTheory.sheafComposeIso_inv_fac` for `forget₂ CommRingCat RingCat`.
* `Stacks.RelativeSpec.hom_comp_ungradedToGradedRight`: **the comparison is a morphism under the
  structure sheaf** — it carries the structure morphism `r ↦ r · 1` of one realization to the
  other. This is what makes the comparison an isomorphism of *algebra* sheaves rather than of
  bare sheaves of rings, and it is what the relative spectrum consumes.
* `Stacks.LineBundle.Situation.totalSpaceIsoVectorBundle_hom_comp_vectorBundleToBase` and
  `totalSpaceIsoVectorBundle_inv_comp_totalSpaceToBase`: **the comparison of schemes is an
  isomorphism over the base**, in both directions.

## Implementation notes

**Why the comparison is built at `CommRingCat` and not at `RingCat`.**
`Stacks.RelativeSpec.ringSheafIsoUngradedSheaf` already compares the two realizations, but only
as sheaves of possibly noncommutative rings, and the relative spectrum takes an object of
`CategoryTheory.Under X.sheaf`, which lives over `CommRingCat`. `Stacks.CommRingSheaf.homMk`
lifts a morphism of sheaves of rings out of the underlying sheaf of rings of a sheaf of
commutative rings to `CommRingCat` without changing the underlying morphism, which is why
`sheafCompose_map_ungradedToGradedRight` holds by `rfl`; the whole of the work is then the
triangle `hom_comp_ungradedToGradedRight`, and that is checked by applying the faithful functor
`sheafCompose J (forget₂ CommRingCat RingCat)` and reducing to the unit compatibility.

**The implementation note of
`StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent` records this
upgrade as not done, and declines it.** That file needed quasi-coherence of
`Stacks.RelativeSpec.gradedAlgebraSheaf` and obtained it by re-instantiating the generic
comparison `Stacks.GradedAlgebra.directSumIsoUnderlyingModule` at that realization, rather than
transporting quasi-coherence across the `RingCat` iso. Its reasoning stands and nothing here
replaces it: quasi-coherence of both realizations is taken from the existing
`Stacks.RelativeSpec.isQuasicoherent_ungradedAlgebraSheaf` and
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf`, and is not re-derived.
What the upgrade is used for instead is the comparison of the *spectra*, which no amount of
degreewise bookkeeping provides.

**Naming the `PreservesSheafification` instance.** As in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafificationCommRing`, synthesizing
`J.PreservesSheafification (forget₂ CommRingCat RingCat)` exhausts the instance budget, and
naming `CategoryTheory.GrothendieckTopology.instPreservesSheafification` discharges it at once.
`PreservesSheafification` is a `Prop`, so the instance named here and the one baked into
`Stacks.ModuleUp.sheafifyForgetToRingIso` are interchangeable.

**The comparison is the specified one, not an unspecified isomorphism.**
`Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso` is characterized by its universal element,
so `Situation.vectorBundleToTotalSpace_comp_totalSpaceToBase` is the first component of that
element rather than a separate verification, and the base compatibility is part of the API here
instead of being left to the caller.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))

/-- **The comparison of the two ungraded realizations, as a morphism of sheaves of commutative
rings**: the inverse of `Stacks.RelativeSpec.ringSheafIsoUngradedSheaf`, lifted to `CommRingCat`
by `Stacks.CommRingSheaf.homMk`. -/
def ungradedToGradedRight :
    (ungradedAlgebraSheaf X A hA).right ⟶ (gradedAlgebraSheaf X A hA).right :=
  Stacks.CommRingSheaf.homMk _ (A.mul_comm_ungradedSheaf hA)
    (ringSheafIsoUngradedSheaf X A hA).inv

/-- The lift to `CommRingCat` does not change the underlying morphism of sheaves of rings. -/
theorem sheafCompose_map_ungradedToGradedRight :
    (sheafCompose (Opens.grothendieckTopology (X : TopCat))
        (forget₂ CommRingCat.{u} RingCat.{u})).map (ungradedToGradedRight X A hA) =
      (ringSheafIsoUngradedSheaf X A hA).inv :=
  rfl

/-- The sheaf of rings underlying the structure morphism of
`Stacks.RelativeSpec.ungradedAlgebraSheaf` is its structure morphism as an algebra sheaf. -/
theorem sheafCompose_map_hom_ungradedAlgebraSheaf :
    (sheafCompose (Opens.grothendieckTopology (X : TopCat))
        (forget₂ CommRingCat.{u} RingCat.{u})).map (ungradedAlgebraSheaf X A hA).hom =
      AlgebraSheaf.structureMap (ungradedAlgebraSheaf X A hA) :=
  rfl

/-- The sheaf of rings underlying the structure morphism of
`Stacks.RelativeSpec.gradedAlgebraSheaf` is the structure map `r ↦ r · 1` of the ungraded
realization. -/
theorem sheafCompose_map_hom_gradedAlgebraSheaf :
    (sheafCompose (Opens.grothendieckTopology (X : TopCat))
        (forget₂ CommRingCat.{u} RingCat.{u})).map (gradedAlgebraSheaf X A hA).hom =
      A.ungradedStructureMap :=
  rfl

/-- **The two sheafification units agree across `Stacks.ModuleUp.sheafifyForgetToRingIso`.**
Sheafifying a presheaf of commutative rings and then forgetting commutativity has the same unit
as forgetting commutativity first and sheafifying in `RingCat`. -/
theorem unit_comp_sheafifyForgetToRingIso_inv (P : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}) :
    Functor.whiskerRight (toSheafify (Opens.grothendieckTopology (X : TopCat)) P)
          (forget₂ CommRingCat.{u} RingCat.{u}) ≫
        (Stacks.ModuleUp.sheafifyForgetToRingIso
          (Opens.grothendieckTopology (X : TopCat)) P).inv.hom =
      toSheafify (Opens.grothendieckTopology (X : TopCat))
        (P ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  let : (Opens.grothendieckTopology (X : TopCat)).PreservesSheafification
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
    CategoryTheory.GrothendieckTopology.instPreservesSheafification _ _
  sheafComposeIso_inv_fac (Opens.grothendieckTopology (X : TopCat))
    (forget₂ CommRingCat.{u} RingCat.{u}) P

/-- The unit compatibility for the ungraded realization of a sheaf of graded algebras: the
`CommRingCat`-sheafification unit, read in `RingCat` through the comparison, is the
`RingCat`-sheafification unit. -/
theorem ungradedRingUnit_comp_ringSheafIsoUngradedSheaf_inv :
    ungradedRingUnit X A hA ≫ (ringSheafIsoUngradedSheaf X A hA).inv.hom =
      A.toPresheafGradedAlgebra.toTotalSheaf (Opens.grothendieckTopology (X : TopCat)) :=
  unit_comp_sheafifyForgetToRingIso_inv X (ungradedCommPresheaf X A hA)

/-- The comparison carries the structure morphism of
`Stacks.RelativeSpec.ungradedAlgebraSheaf` to the structure map `r ↦ r · 1` of the ungraded
realization, as morphisms of sheaves of rings. -/
theorem structureMap_comp_ringSheafIsoUngradedSheaf_inv :
    AlgebraSheaf.structureMap (ungradedAlgebraSheaf X A hA) ≫
        (ringSheafIsoUngradedSheaf X A hA).inv =
      A.ungradedStructureMap := by
  refine Sheaf.hom_ext ?_
  change (A.toPresheafGradedAlgebra.structureHom ≫ ungradedRingUnit X A hA) ≫
    (ringSheafIsoUngradedSheaf X A hA).inv.hom = _
  rw [Category.assoc, ungradedRingUnit_comp_ringSheafIsoUngradedSheaf_inv]
  rfl

/-- **The comparison is a morphism under the structure sheaf**: it carries the structure
morphism `r ↦ r · 1` of one ungraded realization to that of the other. The underlying functor
`sheafCompose J (forget₂ CommRingCat RingCat)` is faithful, so this reduces to
`Stacks.RelativeSpec.structureMap_comp_ringSheafIsoUngradedSheaf_inv`. -/
theorem hom_comp_ungradedToGradedRight :
    (ungradedAlgebraSheaf X A hA).hom ≫ ungradedToGradedRight X A hA =
      (gradedAlgebraSheaf X A hA).hom :=
  (sheafCompose (Opens.grothendieckTopology (X : TopCat))
      (forget₂ CommRingCat.{u} RingCat.{u})).map_injective
    ((Functor.map_comp _ _ _).trans
      (structureMap_comp_ringSheafIsoUngradedSheaf_inv X A hA))

/-- The comparison of the two ungraded realizations is an isomorphism, because it is one on the
underlying sheaves of rings and `forget₂ CommRingCat RingCat` is fully faithful. -/
theorem isIso_ungradedToGradedRight : IsIso (ungradedToGradedRight X A hA) :=
  have : IsIso ((sheafCompose (Opens.grothendieckTopology (X : TopCat))
      (forget₂ CommRingCat.{u} RingCat.{u})).map (ungradedToGradedRight X A hA)) :=
    inferInstanceAs (IsIso (ringSheafIsoUngradedSheaf X A hA).inv)
  (fullyFaithfulSheafCompose (Opens.grothendieckTopology (X : TopCat))
    CommRingCat.fullyFaithfulForget₂ToRingCat).isIso_of_isIso_map
      (ungradedToGradedRight X A hA)

/-- **The two ungraded realizations of a sheaf of graded algebras are isomorphic as sheaves of
commutative `𝒪_X`-algebras**, i.e. in `Stacks.RelativeSpec.AlgebraSheaf X`. -/
def ungradedAlgebraSheafIsoGradedAlgebraSheaf :
    ungradedAlgebraSheaf X A hA ≅ gradedAlgebraSheaf X A hA :=
  Under.isoMk (@asIso _ _ _ _ _ (isIso_ungradedToGradedRight X A hA))
    (hom_comp_ungradedToGradedRight X A hA)

end Stacks.RelativeSpec

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The algebra sheaf of a line bundle is `Sym(L)` as an algebra sheaf in the sense of Stacks
Tag 01LM**, the input `AlgebraicGeometry.Scheme.Modules.vectorBundle` takes. -/
def Situation.algebraSheafIsoSymmetricAlgebraSheaf :
    D.algebraSheaf ≅ AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf D.X D.L :=
  Stacks.RelativeSpec.ungradedAlgebraSheafIsoGradedAlgebraSheaf D.X D.symmetricAlgebra
    D.symmetricAlgebra_mul_comm

/-- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf` at the line bundle
of a situation.

This is that instance and not a second proof of it; it is restated because the general one is
not found by discrimination-tree lookup through the projection `Situation.L`, and
`Situation.vectorBundleToTotalSpace` below hands it to
`Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso` by name. -/
instance Situation.isQuasicoherent_symmetricAlgebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      (AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf D.X D.L) :=
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf D.X D.L

/-- The comparison morphism from the vector bundle of the invertible module to the total space of
the line bundle, induced by `Situation.algebraSheafIsoSymmetricAlgebraSheaf`. -/
def Situation.vectorBundleToTotalSpace :
    AlgebraicGeometry.Scheme.Modules.vectorBundle D.X D.L ⟶ D.totalSpace :=
  Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso D.relativeSpecSituation
    (AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf D.X D.L)
    D.isQuasicoherent_symmetricAlgebraSheaf D.algebraSheafIsoSymmetricAlgebraSheaf

/-- The comparison morphism `Situation.vectorBundleToTotalSpace` is an isomorphism. -/
instance Situation.isIso_vectorBundleToTotalSpace : IsIso D.vectorBundleToTotalSpace :=
  Stacks.RelativeSpec.isIso_relativeSpectrumMapOfAlgebraIso D.relativeSpecSituation _ _ _

/-- The comparison morphism is a morphism over the base. -/
theorem Situation.vectorBundleToTotalSpace_comp_totalSpaceToBase :
    D.vectorBundleToTotalSpace ≫ D.totalSpaceToBase =
      AlgebraicGeometry.Scheme.Modules.vectorBundleToBase D.X D.L :=
  Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso_toBase D.relativeSpecSituation _ _ _

/-- **The total space of a line bundle is the vector bundle of its invertible module.** -/
def Situation.totalSpaceIsoVectorBundle :
    D.totalSpace ≅ AlgebraicGeometry.Scheme.Modules.vectorBundle D.X D.L :=
  (asIso D.vectorBundleToTotalSpace).symm

/-- The inverse of `Situation.totalSpaceIsoVectorBundle` is the specified comparison morphism. -/
theorem Situation.totalSpaceIsoVectorBundle_inv :
    D.totalSpaceIsoVectorBundle.inv = D.vectorBundleToTotalSpace :=
  rfl

/-- **`Situation.totalSpaceIsoVectorBundle` is an isomorphism over the base**: its inverse
carries the projection of the total space to the projection of the vector bundle. -/
theorem Situation.totalSpaceIsoVectorBundle_inv_comp_totalSpaceToBase :
    D.totalSpaceIsoVectorBundle.inv ≫ D.totalSpaceToBase =
      AlgebraicGeometry.Scheme.Modules.vectorBundleToBase D.X D.L :=
  D.vectorBundleToTotalSpace_comp_totalSpaceToBase

/-- **`Situation.totalSpaceIsoVectorBundle` is an isomorphism over the base**: it carries the
projection of the vector bundle to the projection of the total space. -/
theorem Situation.totalSpaceIsoVectorBundle_hom_comp_vectorBundleToBase :
    D.totalSpaceIsoVectorBundle.hom ≫
        AlgebraicGeometry.Scheme.Modules.vectorBundleToBase D.X D.L = D.totalSpaceToBase := by
  rw [← D.totalSpaceIsoVectorBundle_inv_comp_totalSpaceToBase,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end Stacks.LineBundle

end
