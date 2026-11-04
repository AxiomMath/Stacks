module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
/-!
# Naturality in the object of the degreewise Leray comparison

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors between abelian categories with `𝒜` and
`ℬ` having enough injectives, and suppose `F` carries the injective objects of `𝒜` to objects
right acyclic for `G`.  At an object `M` of `𝒜` right acyclic for `F` the comparison
`Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso` identifies `R ⁿ(G ∘ F)(M)` with
`R ⁿG(F(M))`.  If *every* object of `𝒜` is right acyclic for `F`, that family of isomorphisms
is an isomorphism of functors `R ⁿ(G ∘ F) ≅ F ⋙ R ⁿG`, and that is what is built here.

## Main definitions

* `Stacks.Cohomology.LerayDegreewise.mapHomotopyCategorySingleNatIso`: the comparison
  `K⁺`-free form of `HomologicalComplex.singleMapHomologicalComplex`, i.e. the natural
  isomorphism `(—)[n] ⋙ F∗ ≅ F ⋙ (—)[n]` of functors into the homotopy category of all
  cochain complexes.
* `Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleNatIso`: the same
  comparison in the bounded below homotopy category, the natural-isomorphism form of
  `Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleObjIso`.
* `Stacks.Cohomology.LerayDegreewise.rightDerivedFunctorPlusUnitSingleNatIso`: the unit of
  `RF`, restricted along `M ↦ M[0]`, as a natural isomorphism; its components are invertible
  because every object is right acyclic for `F`.
* `Stacks.Cohomology.LerayDegreewise.rightDerivedFunctorPlusSingleNatIso`: the
  natural-isomorphism form of
  `Stacks.Cohomology.LerayDegreewise.rightDerivedFunctorPlusSingleObjIso`, namely
  `(—)[0] ⋙ RF ≅ F ⋙ (—)[0]`.
* `Stacks.Cohomology.LerayDegreewise.rightDerivedCompNatIso`: the natural-isomorphism form of
  `Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso`, namely
  `R ⁿ(G ∘ F) ≅ F ⋙ R ⁿG`.

## Main results

* `Stacks.Cohomology.LerayDegreewise.ι_map_mapHomotopyCategoryPlusSingleObjIso_hom`: the
  bounded below comparison of `F` with the formation of a complex concentrated in one degree
  is, under the inclusion of the bounded below homotopy category, the unbounded one.
* `Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleNatIso_hom_app`,
  `Stacks.Cohomology.LerayDegreewise.rightDerivedFunctorPlusSingleNatIso_hom_app`,
  `Stacks.Cohomology.LerayDegreewise.rightDerivedCompNatIso_hom_app`: each natural
  isomorphism has for components the object-level isomorphism it is the naturality of.  The
  last of these is what makes the natural comparison usable by the consumers of
  `Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso`.

## Implementation notes

The object-level comparison is a four-fold composite, and rather than prove one naturality
square for the composite each factor is built here as an isomorphism of *functors*, the four
being composed with `Iso.trans`.  Three of the four are applications, whiskerings or
inversions of isomorphisms that are already natural; the components of the fourth, the unit of
`RF` at `M[0]`, are invertible object by object, by right acyclicity, so it becomes natural
through `CategoryTheory.NatIso.ofComponents`.  Because the factors are assembled in the same
order as in the object-level composite, every `..._hom_app` lemma below holds by `rfl`.

The one naturality square that does have to be proved is the one for
`Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleObjIso`, whose components are
preimages under the fully faithful inclusion `K⁺(ℬ) ⥤ K(ℬ)`.  It is proved by applying
`CategoryTheory.Functor.map_injective` for that inclusion and then quoting the naturality of
the unbounded comparison `mapHomotopyCategorySingleNatIso`; the two readings of the source and
target functors agree definitionally, the inclusions of a full subcategory and of the
bounded below complexes into all complexes both being `ObjectProperty.lift`s, so no further
bookkeeping is needed.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.LerayDegreewise

section Natural

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- **An additive functor commutes with the formation of a complex concentrated in degree `n`,
naturally in the object**, read in the homotopy category of all cochain complexes.  It is the
class of `HomologicalComplex.singleMapHomologicalComplex`, the source and target functors being
the ones the quotient by homotopy produces from the corresponding functors on complexes. -/
def mapHomotopyCategorySingleNatIso (n : ℤ) :
    HomotopyCategory.singleFunctor C n ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      F ⋙ HomotopyCategory.singleFunctor D n :=
  Functor.isoWhiskerRight
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n)
    (HomotopyCategory.quotient D (ComplexShape.up ℤ))

omit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] [EnoughInjectives D] in
/-- The bounded below comparison
`Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleObjIso` is, under the fully
faithful inclusion of the bounded below homotopy category in the homotopy category of all
cochain complexes, the unbounded comparison
`Stacks.Cohomology.LerayDegreewise.mapHomotopyCategorySingleNatIso`.  True because the
bounded below one is by definition the preimage of the unbounded one. -/
theorem ι_map_mapHomotopyCategoryPlusSingleObjIso_hom (n : ℤ) (X : C) :
    (HomotopyCategory.Plus.ι D).map (mapHomotopyCategoryPlusSingleObjIso F n X).hom =
      (mapHomotopyCategorySingleNatIso F n).hom.app X :=
  (HomotopyCategory.Plus.ι D).map_preimage _

/-- **An additive functor commutes with the formation of a complex concentrated in degree `n`,
naturally in the object**, read in the bounded below homotopy category.  This is the
natural-isomorphism form of
`Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleObjIso`. -/
def mapHomotopyCategoryPlusSingleNatIso (n : ℤ) :
    HomotopyCategory.Plus.singleFunctor C n ⋙ F.mapHomotopyCategoryPlus ≅
      F ⋙ HomotopyCategory.Plus.singleFunctor D n :=
  NatIso.ofComponents (mapHomotopyCategoryPlusSingleObjIso F n) (fun {_ _} f =>
    (HomotopyCategory.Plus.ι D).map_injective (by
      rw [Functor.map_comp, Functor.map_comp,
        ι_map_mapHomotopyCategoryPlusSingleObjIso_hom,
        ι_map_mapHomotopyCategoryPlusSingleObjIso_hom]
      exact (mapHomotopyCategorySingleNatIso F n).hom.naturality f))

omit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] [EnoughInjectives D] in
/-- The components of
`Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleNatIso` are the object-level
isomorphisms `Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleObjIso`. -/
theorem mapHomotopyCategoryPlusSingleNatIso_hom_app (n : ℤ) (X : C) :
    (mapHomotopyCategoryPlusSingleNatIso F n).hom.app X =
      (mapHomotopyCategoryPlusSingleObjIso F n X).hom :=
  rfl

/-- **The unit of `RF` at the complexes concentrated in degree zero, as a natural
isomorphism.**  The unit of `RF` is a natural transformation, and right acyclicity of every
object of `𝒜` for `F` says exactly that each of its components at a complex `M[0]` is
invertible. -/
def rightDerivedFunctorPlusUnitSingleNatIso (hF : ∀ M : C, F.rightAcyclic M) :
    HomotopyCategory.Plus.singleFunctor C 0 ⋙
        F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      HomotopyCategory.Plus.singleFunctor C 0 ⋙
        DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus :=
  haveI : ∀ M : C, IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) := fun M => hF M
  NatIso.ofComponents
    (fun M => asIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M)))
    (fun _ => F.rightDerivedFunctorPlusUnit.naturality _)

/-- **An abelian category all of whose objects are right acyclic for `F` is computed by `F`
itself, naturally in the object.**  This is the natural-isomorphism form of
`Stacks.Cohomology.LerayDegreewise.rightDerivedFunctorPlusSingleObjIso`: the bounded below
right derived functor `RF` carries `M[0]` to `F(M)[0]`, naturally in `M`. -/
def rightDerivedFunctorPlusSingleNatIso (hF : ∀ M : C, F.rightAcyclic M) :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor D 0 :=
  Functor.isoWhiskerRight (Functor.singleFunctorPlusIsoCompQh (A := C) 0)
      F.rightDerivedFunctorPlus ≪≫
    (rightDerivedFunctorPlusUnitSingleNatIso F hF).symm ≪≫
    Functor.isoWhiskerRight (mapHomotopyCategoryPlusSingleNatIso F 0)
      DerivedCategory.Plus.Qh ≪≫
    Functor.isoWhiskerLeft F (Functor.singleFunctorPlusIsoCompQh (A := D) 0).symm

omit [EnoughInjectives D] in
/-- The components of
`Stacks.Cohomology.LerayDegreewise.rightDerivedFunctorPlusSingleNatIso` are the object-level
isomorphisms `Stacks.Cohomology.LerayDegreewise.rightDerivedFunctorPlusSingleObjIso`. -/
theorem rightDerivedFunctorPlusSingleNatIso_hom_app (hF : ∀ M : C, F.rightAcyclic M) (M : C) :
    (rightDerivedFunctorPlusSingleNatIso F hF).hom.app M =
      (rightDerivedFunctorPlusSingleObjIso F M (hF M)).hom :=
  rfl

/-- **The degreewise right derived functors of a composite, naturally in the object.**  Let
`F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors between abelian categories with `𝒜` and `ℬ`
having enough injectives.  If `F` carries every injective object of `𝒜` to an object right
acyclic for `G`, and every object of `𝒜` is right acyclic for `F`, then
`R ⁿ(G ∘ F) ≅ F ⋙ R ⁿG` as functors `𝒜 ⥤ 𝒞`, in every degree `n`.  This is the
natural-isomorphism form of
`Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso`. -/
def rightDerivedCompNatIso (hFG : ∀ I : C, Injective I → G.rightAcyclic (F.obj I))
    (hF : ∀ M : C, F.rightAcyclic M) (n : ℕ) :
    (F ⋙ G).rightDerived n ≅ F ⋙ G.rightDerived n :=
  Stacks.DerivedIndexing.rightDerivedIso (F ⋙ G) n ≪≫
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
          (Stacks.Cohomology.DerivedPushforwardSections.compIso F G hFG))
        (DerivedCategory.Plus.homologyFunctor E (n : ℤ)) ≪≫
    Functor.isoWhiskerRight
        (Functor.isoWhiskerRight (rightDerivedFunctorPlusSingleNatIso F hF)
          G.rightDerivedFunctorPlus)
        (DerivedCategory.Plus.homologyFunctor E (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft F (Stacks.DerivedIndexing.rightDerivedIso G n).symm

/-- **The natural degreewise comparison of a composite has for components the object-level
comparison.**  Its component at an object `M` is
`Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso` at `M`, so every consumer of the
object-level isomorphism may use the natural one. -/
theorem rightDerivedCompNatIso_hom_app
    (hFG : ∀ I : C, Injective I → G.rightAcyclic (F.obj I))
    (hF : ∀ M : C, F.rightAcyclic M) (n : ℕ) (M : C) :
    (rightDerivedCompNatIso F G hFG hF n).hom.app M =
      (rightDerivedCompObjIso F G hFG M (hF M) n).hom :=
  rfl

end Natural

end Stacks.Cohomology.LerayDegreewise

end
