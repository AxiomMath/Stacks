module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafAsIntModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Unbounded total tensor complexes of abelian sheaves, and the derived tensor product

On a site `(C, J)` whose presheaves of abelian groups admit sheafification, the abelian sheaves
carry the tensor product obtained by localizing the objectwise one,
`CategoryTheory.Sheaf.monoidalCategory`. This file supplies the inputs that the *unbounded*
derived tensor product needs there and that
`StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafMonoidalPreadditive.lean` leaves open: the
total complex of the tensor double complex of an *arbitrary* pair of cochain complexes of
abelian sheaves, and the symmetric monoidal structure on those cochain complexes. With them,
`CochainComplex.KFlatMonoidal.derivedMonoidal` applies to abelian sheaves as soon as K-flat
resolutions are available.

## Main definitions

* `AddCommGrpCat.symmetricCategoryTransported`: **the tensor product of abelian groups is
  symmetric**, the symmetry being transported from the modules over a universe-lifted copy of
  the integers along `AddCommGrpCat.uliftIntEquivalence`, exactly as the braiding of
  `AddCommGrpCat.braidedCategory` is.
* `Stacks.Cohomology.monoidalClosed_abelianSheaves`: **the tensor product of abelian sheaves is
  closed**, by Day's reflection theorem applied to the sheafification adjunction.
* `Stacks.Cohomology.braidedCategoryCochainComplexAbelianSheaves` and
  `Stacks.Cohomology.Leray.braidedCategoryCochainComplexAbelianSheaf`: **the cochain complexes
  of abelian sheaves are braided monoidal** under the total tensor product with the Koszul sign
  convention.
* `Stacks.Cohomology.derivedMonoidalAbelianSheaves`: **the derived category of abelian sheaves
  is monoidal as soon as K-flat resolutions exist there.**

## Main results

* `Stacks.Cohomology.hasCoproducts_abelianSheaves`: the abelian sheaves have all coproducts
  indexed by a type in the lowest universe.
* `Stacks.Cohomology.hasMapBifunctor_curriedTensor_abelianSheaves` and
  `Stacks.Cohomology.Leray.hasMapBifunctor_curriedTensor_abelianSheaf`: **the tensor product of
  *any* two cochain complexes of abelian sheaves has a total complex.** This is the unbounded
  form of `Stacks.Cohomology.Leray.hasMapBifunctor_curriedTensor_of_isZero`, which asks both
  complexes to be bounded below.

## Implementation notes

**Everything is stated at a generic site and specialised at the end, and that is forced.** At
`Opens.grothendieckTopology X` the goal `HasColimitsOfShape (Discrete ℤ) (AbelianSheaf X)`
exhausts the typeclass budget on its own, and raising the budget only moves the failure into
`whnf`. The chain below is written over `{J : GrothendieckTopology C}` with each link named, and
each link is then found by instance search in one step instead of being rediscovered.

Two links are supplied by a term rather than by `inferInstance`, and both are deliberate.

* The coproducts of `Stacks.Cohomology.hasCoproducts_abelianSheaves` are the sheafifications of
  the presheaf coproducts, which is what `CategoryTheory.Sheaf.sheafifyCocone` and
  `CategoryTheory.Sheaf.isColimitSheafifyCocone` say. Mathlib already derives
  `HasColimitsOfShape K (Sheaf J D)` from `HasColimitsOfShape K D` by exactly that cocone, but
  instance search does not reach it here — the goal is reported as a budget timeout, not as a
  failure — whereas writing the cocone down takes about a second.
* `Stacks.Cohomology.isMonoidal_W_addCommGrpCat` names
  `CategoryTheory.GrothendieckTopology.W.monoidal` at `AddCommGrpCat`. Left to search, that
  instance is reached from `CategoryTheory.Sheaf.monoidalCategory`, and whether it is reached
  inside the budget depends on what else the consuming file imports: one further import is enough
  for `(J.W (A := AddCommGrpCat)).IsMonoidal` to time out at 20000 heartbeats. Naming it is what
  makes the monoidal structure usable from a file that also imports the K-flat transport.

**What makes the unbounded total complexes exist** is that tensoring with a fixed abelian sheaf
is a left adjoint, so it commutes with the coproducts over the antidiagonals. That is
`Stacks.Cohomology.monoidalClosed_abelianSheaves`, which is
`CategoryTheory.Monoidal.Reflective.monoidalClosed` — Day's reflection theorem — applied to the
sheafification adjunction, whose left adjoint is monoidal for the localized structure and whose
right adjoint is fully faithful. The presheaf category is monoidal closed by
`CategoryTheory.MonoidalClosed.FunctorCategory.monoidalClosed`, a scoped instance; the
`open scoped` below is what makes it visible, and without it the chain stops at the presheaf
level. The bounded-below form in
`StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafMonoidalPreadditive.lean` needs none of this,
only finitely many summands contributing in each total degree.

**The derived category itself needs nothing new.** `HasDerivedCategory (Sheaf J AddCommGrpCat)`
is `HasDerivedCategory.standard`, Mathlib's construction for an arbitrary abelian category, at
universe `u + 1`; this library already seats it for `Stacks.Cohomology.Leray.AbelianSheaf` in
`StacksFrontier/Topology/Sheaves/Cohomology/Leray/AbelianSheafSpectralSequence.lean`. It is carried
as an instance binder below rather than renamed, because `HasDerivedCategory` is data and a
second instance would be a second derived category.

**Where the hypothesis of `Stacks.Cohomology.derivedMonoidalAbelianSheaves` is discharged.** With
the instances below in scope, every binder of
`CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence` at
`A := Stacks.SheafOfModules.DerivedMonoidal.Mod (constIntCommSheaf J)`,
`A' := Sheaf J AddCommGrpCat`, `F := Stacks.SheafOfModules.Tensor.sheafTensor` and
`F' := MonoidalCategory.curriedTensor` is discharged by instance search, and its hypothesis
`hres` on the `A` side is `Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution`,
which is unconditional. The one input left, the explicit comparison `ε` identifying
`Stacks.SheafOfModules.Tensor.sheafTensor` with the tensor product of abelian sheaves across
`Stacks.Cohomology.intModulesEquivAbelianSheaves` together with its two naturality squares, is
not supplied here: it is
`Stacks.Cohomology.abelianSheafTensorComparison` of
`StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafTensorComparison.lean`, which runs the
transport and concludes `Stacks.Cohomology.exists_kFlat_resolution_abelianSheaves`. So the
hypothesis of `Stacks.Cohomology.derivedMonoidalAbelianSheaves` below is available, and
`Stacks.Cohomology.derivedMonoidalAbelianSheavesOfKFlat` is that packaging.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
open CategoryTheory.Enriched.FunctorCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonoidalClosed.FunctorCategory

universe u v

namespace AddCommGrpCat

attribute [local instance] monoidalCategory uliftIntEquivalenceInverseMonoidal
  uliftIntEquivalenceFunctorMonoidal

/-- **The tensor product of abelian groups is symmetric**, the symmetry being transported from
the modules over a universe-lifted copy of the integers along
`AddCommGrpCat.uliftIntEquivalence`.

This is the symmetric refinement of `AddCommGrpCat.braidedCategory`, and the two agree: both are
obtained from `CategoryTheory.Monoidal.Transported`, where the symmetry is built on the braiding
rather than beside it. It is wanted because the braided monoidal structure on cochain complexes,
`CochainComplex.braidedCategory`, is deduced from the Koszul symmetry and therefore asks for the
symmetry of the base category, not only for a braiding. -/
@[instance_reducible] def symmetricCategoryTransported :
    SymmetricCategory AddCommGrpCat.{v} := by
  change SymmetricCategory (Monoidal.Transported (uliftIntEquivalence.{v}))
  infer_instance

end AddCommGrpCat

namespace Stacks.Cohomology

attribute [local instance] AddCommGrpCat.monoidalCategory
  AddCommGrpCat.uliftIntEquivalenceInverseMonoidal
  AddCommGrpCat.uliftIntEquivalenceFunctorMonoidal
  AddCommGrpCat.symmetricCategoryTransported
  AddCommGrpCat.monoidalClosed MonoidalClosed.enrichedOrdinaryCategorySelf

section Site

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]

/-- **The abelian sheaves on a site have all coproducts indexed by a type in the lowest
universe.** The coproduct is the sheafification of the coproduct of the underlying presheaves,
which is a colimit because sheafification is a left adjoint and the counit of the sheafification
adjunction is an isomorphism. -/
instance hasCoproducts_abelianSheaves : HasCoproducts.{0} (Sheaf J AddCommGrpCat.{u}) := fun _ =>
  ⟨fun _ => HasColimit.mk
    ⟨Sheaf.sheafifyCocone (colimit.cocone _),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/-- **Tensoring a presheaf of abelian groups with a fixed one has an enriched hom**, in both of
the forms the monoidal structure on sheaves consumes. Both are limits in `AddCommGrpCat`, which
has all of them. -/
instance hasFunctorEnrichedHom_addCommGrpCat (F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    HasFunctorEnrichedHom AddCommGrpCat.{u} F₁ F₂ :=
  inferInstance

/-- The companion of `Stacks.Cohomology.hasFunctorEnrichedHom_addCommGrpCat`. -/
instance hasEnrichedHom_addCommGrpCat (F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    HasEnrichedHom AddCommGrpCat.{u} F₁ F₂ :=
  inferInstance

/-- **The local isomorphisms of presheaves of abelian groups are stable under tensoring**, which
is what makes the tensor product descend to sheaves. This is
`CategoryTheory.GrothendieckTopology.W.monoidal`, named at `AddCommGrpCat` so that instance
search finds it in one step; see the implementation notes. -/
instance isMonoidal_W_addCommGrpCat : (J.W (A := AddCommGrpCat.{u})).IsMonoidal :=
  GrothendieckTopology.W.monoidal

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

/-- **The tensor product of abelian sheaves is closed.** By Day's reflection theorem
(`CategoryTheory.Monoidal.Reflective.monoidalClosed`) it is enough that the presheaves of abelian
groups are symmetric monoidal closed and that sheafification is a monoidal left adjoint of a
fully faithful functor, which is the sheafification adjunction. -/
@[sga "7 VIII 1.1"]
instance monoidalClosed_abelianSheaves : MonoidalClosed (Sheaf J AddCommGrpCat.{u}) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction J AddCommGrpCat.{u})

/-- **The tensor product of abelian sheaves on a site is bilinear on morphisms.** This is
`Stacks.Cohomology.Leray.abelianSheafMonoidalPreadditive` at a generic site, by the same
transport `CategoryTheory.monoidalPreadditive_of_additiveSection` along sheafification, whose
additive section is the inclusion of sheaves into presheaves. -/
instance monoidalPreadditive_abelianSheaves :
    MonoidalPreadditive (Sheaf J AddCommGrpCat.{u}) :=
  monoidalPreadditive_of_additiveSection
    (presheafToSheaf J AddCommGrpCat.{u})
    (sheafToPresheaf J AddCommGrpCat.{u})
    inferInstance
    (asIso (sheafificationAdjunction J AddCommGrpCat.{u}).counit)

/-- **The graded tensor products of abelian sheaves exist**: for all `n`, the coproduct of the
`X₁ i ⊗ X₂ j` with `i + j = n` exists, the antidiagonal being a type in the lowest universe. -/
instance hasTensor_abelianSheaves (X₁ X₂ : GradedObject ℤ (Sheaf J AddCommGrpCat.{u})) :
    GradedObject.HasTensor X₁ X₂ :=
  inferInstance

/-- **`- ⊗ X₃ i₃` commutes with the antidiagonal coproducts**, because tensoring with a fixed
abelian sheaf is a left adjoint by `Stacks.Cohomology.monoidalClosed_abelianSheaves`. -/
instance hasGoodTensor₁₂Tensor_abelianSheaves
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf J AddCommGrpCat.{u})) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  inferInstance

/-- The mirror of `Stacks.Cohomology.hasGoodTensor₁₂Tensor_abelianSheaves`. -/
instance hasGoodTensorTensor₂₃_abelianSheaves
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf J AddCommGrpCat.{u})) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  inferInstance

/-- **A morphism out of a fourfold graded tensor product of abelian sheaves is determined on the
summands**, which is the extensionality the pentagon is checked with. -/
instance hasTensor₄ObjExt_abelianSheaves
    (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf J AddCommGrpCat.{u})) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  inferInstance

/-- **Tensoring an abelian sheaf on the right preserves the initial object**, which is what makes
the unitors of the graded tensor product work. -/
instance preservesColimit_empty_curriedTensor_abelianSheaves
    (X₁ : Sheaf J AddCommGrpCat.{u}) :
    PreservesColimit (Functor.empty.{0} (Sheaf J AddCommGrpCat.{u}))
      ((curriedTensor (Sheaf J AddCommGrpCat.{u})).obj X₁) :=
  inferInstance

/-- The mirror of
`Stacks.Cohomology.preservesColimit_empty_curriedTensor_abelianSheaves`. -/
instance preservesColimit_empty_curriedTensor_flip_abelianSheaves
    (X₂ : Sheaf J AddCommGrpCat.{u}) :
    PreservesColimit (Functor.empty.{0} (Sheaf J AddCommGrpCat.{u}))
      ((curriedTensor (Sheaf J AddCommGrpCat.{u})).flip.obj X₂) :=
  inferInstance

/-- **The tensor product of any two cochain complexes of abelian sheaves has a total complex.**

In total degree `n` it is the coproduct of the `K₁^p ⊗ K₂^q` over the pairs with `p + q = n`,
which exists by `Stacks.Cohomology.hasCoproducts_abelianSheaves`, and the differentials are
determined on the summands because tensoring commutes with those coproducts in each variable.

This is the unbounded form of `Stacks.Cohomology.Leray.hasMapBifunctor_curriedTensor_of_isZero`,
which asks both complexes to be bounded below; it is what the *unbounded* derived tensor product
of abelian sheaves needs. -/
instance hasMapBifunctor_curriedTensor_abelianSheaves
    (K₁ K₂ : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (curriedTensor (Sheaf J AddCommGrpCat.{u})) (ComplexShape.up ℤ) :=
  inferInstance

/-- **The cochain complexes of abelian sheaves are braided monoidal** under the total tensor
product, the braiding being the Koszul symmetry of `CochainComplex.braidedCategory`.

This is the second input `CochainComplex.KFlatMonoidal.derivedMonoidal` carries on top of the
existence of K-flat resolutions. Like `CochainComplex.braidedCategory` itself it is not an
instance: the cochain complexes of abelian sheaves have no monoidal structure in scope until one
is seated. The symmetric refinement needs no new name — with the instances above in scope
`CochainComplex.symmetricCategory (Sheaf J AddCommGrpCat.{u})` elaborates directly. -/
@[instance_reducible] def braidedCategoryCochainComplexAbelianSheaves :
    BraidedCategory (CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) :=
  CochainComplex.braidedCategory _

attribute [local instance] braidedCategoryCochainComplexAbelianSheaves

/-- **The derived category of abelian sheaves on a site is monoidal as soon as every cochain
complex of abelian sheaves receives a quasi-isomorphism from a K-flat one.**

This is `CochainComplex.KFlatMonoidal.derivedMonoidal` at the abelian sheaves: the tensor
product is obtained by localizing the K-flat complexes, so on K-flat complexes it is the total
tensor complex and no coherence diagram is checked. Every input of that construction except
`hres` is discharged by the instances of this file; `hres` is left as the hypothesis it is there,
and `Stacks.Cohomology.exists_kFlat_resolution_abelianSheaves` supplies it, by the transport
`CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence` along
`Stacks.Cohomology.intModulesEquivAbelianSheaves`. -/
@[instance_reducible] def derivedMonoidalAbelianSheaves [HasDerivedCategory.{v}
      (Sheaf J AddCommGrpCat.{u})]
    (hres : ∀ G : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ,
      ∃ (P : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (f : P ⟶ G),
        CochainComplex.KFlatBifunctor.KFlat
          (curriedTensor (Sheaf J AddCommGrpCat.{u})) P ∧ QuasiIso f) :
    MonoidalCategory (DerivedCategory (Sheaf J AddCommGrpCat.{u})) :=
  CochainComplex.KFlatMonoidal.derivedMonoidal _ hres

end Site

namespace Leray

attribute [local instance] abelianSheafMonoidalCategory

/-- **The tensor product of any two cochain complexes of abelian sheaves on a topological space
has a total complex.** This is
`Stacks.Cohomology.hasMapBifunctor_curriedTensor_abelianSheaves` at the open-cover topology, and
it is the unbounded form of `Stacks.Cohomology.Leray.hasMapBifunctor_curriedTensor_of_isZero`. -/
instance hasMapBifunctor_curriedTensor_abelianSheaf (X : TopCat.{u})
    (K₁ K₂ : CochainComplex (AbelianSheaf X) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (curriedTensor (AbelianSheaf X)) (ComplexShape.up ℤ) :=
  hasMapBifunctor_curriedTensor_abelianSheaves _ K₁ K₂

/-- **The cochain complexes of abelian sheaves on a topological space are braided monoidal**
under the total tensor product with the Koszul sign convention. This is
`Stacks.Cohomology.braidedCategoryCochainComplexAbelianSheaves` at the open-cover topology. -/
@[instance_reducible] def braidedCategoryCochainComplexAbelianSheaf (X : TopCat.{u}) :
    BraidedCategory (CochainComplex (AbelianSheaf X) ℤ) :=
  braidedCategoryCochainComplexAbelianSheaves (Opens.grothendieckTopology X)

end Leray

end Stacks.Cohomology

end
