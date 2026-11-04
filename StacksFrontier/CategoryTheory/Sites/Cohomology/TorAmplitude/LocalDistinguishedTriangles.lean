module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Locally finite Tor dimension along a distinguished triangle

Let `(C, O)` be a ringed site, let `T` be a family of derived tensor products, one on each
slice of the site, and let `K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle in `D(O)`. Finite
Tor dimension of two of the three vertices forces finite Tor dimension of the third, by Stacks
08G2 with the intervals widened to a common one; and *locally* finite Tor dimension of two of
them forces it of the third as soon as the two witnessing coverings can be refined to a common
one.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.FiniteTorDimensionRestricts`: of a family of
  derived tensor products, one on each slice, that finite Tor dimension over a slice forces
  finite Tor dimension over every smaller slice.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_of_distinguished`: **Stacks
  08G2** for finite Tor dimension, in all three positions.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_of_isZero`: a zero object
  has finite Tor dimension.
* `Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_forall_locally`
  and `locallyHasFiniteTorDimension_of_locally_forall`: two out of three when one of the two
  hypotheses holds over *every* object of the site, so that the covering of the other one
  serves both.
* `locallyHasFiniteTorDimension_of_distinguished_obj₂_forall`: two out of three in a
  distinguished triangle whose middle vertex holds over every object of the site, which needs
  no hypothesis on the family.
* `Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_distinguished`:
  **Stacks 08G2** for locally finite Tor dimension, under
  `FiniteTorDimensionRestricts` for the family.

## Implementation notes

Finite Tor dimension at a single slice is `Stacks.SheafOfModules.DerivedTensorProduct` theory
and needs nothing new: restriction to a slice is induced by an exact functor, hence carries the
triangle to a distinguished triangle of the slice, where Stacks 08G2 applies with the given
datum of the family.

Combining two *local* hypotheses is another matter. Stacks 08FZ (3) is an existential over a
covering of each object, so two hypotheses have to be read over a common refinement, and a
member of the refinement is only an arrow *into* a member of one of the two coverings. The
family of derived tensor products carries no relation between its members — see the
implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/LocallyFiniteTorDimension.lean` —
so nothing transports finite Tor dimension along that arrow, and the transport is stated as
the predicate `FiniteTorDimensionRestricts` on the family. It is the site form of the
hypothesis `AlgebraicGeometry.RingedSpace.FiniteTorDimensionRestricts` of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativelyPerfectTriangulated.lean`, and it is a
theorem — Stacks 08G1 followed by Stacks 0E8J — for the genuine derived tensor product on a
ringed site whose objects, morphisms and sections lie in one universe; on a site whose objects
live one universe above its morphisms, which is the shape of a small étale site, neither of
those two inputs is available, and the hypothesis is what stands in for them.

One case escapes all of this and is proved without the hypothesis: when one of the two local
hypotheses in fact holds over *every* object of the site, the covering witnessing the other one
serves for both, with no refinement at all. That is the case of a zero vertex, and it is what
makes stability under shifts — read off the contractible triangles — unconditional.

## References

* [Stacks Project, Tag 08G2](https://stacks.math.columbia.edu/tag/08G2)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-! ### Finite Tor dimension at a single site -/

section OneSite

variable {Z : RingedSite.{u, v, w}}
  [HasSheafify Z.J AddCommGrpCat.{w}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} Z)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Z.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} Z) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)]

variable (T : DerivedTensorProduct.{u, v, w, d} Z)

/-- **Stacks 08G2 for finite Tor dimension**: two out of three in a distinguished triangle. The
two intervals are widened to a common one, where the three propagation rules of Stacks 08G2
apply. -/
theorem hasFiniteTorDimension_of_distinguished
    (tri : Triangle (RingedSite.DerivedModules.{u, v, w, d} Z))
    (htri : tri ∈ distinguishedTriangles) :
    (HasFiniteTorDimension T tri.obj₁ → HasFiniteTorDimension T tri.obj₂ →
        HasFiniteTorDimension T tri.obj₃) ∧
      (HasFiniteTorDimension T tri.obj₁ → HasFiniteTorDimension T tri.obj₃ →
        HasFiniteTorDimension T tri.obj₂) ∧
      (HasFiniteTorDimension T tri.obj₂ → HasFiniteTorDimension T tri.obj₃ →
        HasFiniteTorDimension T tri.obj₁) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a₁, b₁, h₁⟩ ⟨a₂, b₂, h₂⟩
    exact ⟨min (a₁ - 1) a₂, max (b₁ - 1) b₂, hasTorAmplitude_obj₃ T tri htri _ _
      (h₁.mono (by omega) (by omega)) (h₂.mono (by omega) (by omega))⟩
  · rintro ⟨a₁, b₁, h₁⟩ ⟨a₃, b₃, h₃⟩
    exact ⟨min a₁ a₃, max b₁ b₃, hasTorAmplitude_obj₂ T tri htri _ _
      (h₁.mono (by omega) (by omega)) (h₃.mono (by omega) (by omega))⟩
  · rintro ⟨a₂, b₂, h₂⟩ ⟨a₃, b₃, h₃⟩
    exact ⟨min (a₂ - 1) a₃ + 1, max (b₂ - 1) b₃ + 1, hasTorAmplitude_obj₁ T tri htri _ _
      (h₂.mono (by omega) (by omega)) (h₃.mono (by omega) (by omega))⟩

/-- **A zero object has finite Tor dimension**: each `- ⊗^L_O F[0]` is exact, hence additive,
hence carries a zero object to a zero object. -/
theorem hasFiniteTorDimension_of_isZero {E : RingedSite.DerivedModules.{u, v, w, d} Z}
    (hE : IsZero E) : HasFiniteTorDimension T E :=
  ⟨0, 0, fun F i _ =>
    (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} Z) i).map_isZero
      ((T.tensorModule F).map_isZero hE)⟩

end OneSite

/-! ### Locally finite Tor dimension -/

section SliceFamily

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, w} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max u v, v, w} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- **Restriction to a slice commutes with the shift on derived categories.** It is the functor
induced by an exact functor; stated as an instance because
`AlgebraicGeometry.RingedSite.derivedRestriction` is a definition which instance search does
not unfold. -/
local instance derivedRestrictionCommShift (V : X.C) :
    (RingedSite.derivedRestriction.{u, v, w, d} X V).CommShift ℤ :=
  inferInstanceAs ((SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) V).mapDerivedCategory.CommShift ℤ)

/-- **Restriction to a slice is triangulated on derived categories.** -/
local instance derivedRestrictionIsTriangulated (V : X.C) :
    (RingedSite.derivedRestriction.{u, v, w, d} X V).IsTriangulated :=
  inferInstanceAs ((SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) V).mapDerivedCategory.IsTriangulated)

variable (T : ∀ U : X.C, DerivedTensorProduct.{max u v, v, w, d} (X.over U))

/-- **Finite Tor dimension restricts along the arrows of the site**, for the family `T`: if the
restriction of `E` to the slice over `V` has finite Tor dimension and there is an arrow
`W ⟶ V`, then the restriction of `E` to the slice over `W` has finite Tor dimension.

A family of derived tensor products carries no relation between its members, so this is not
automatic; it is Stacks 08G1 followed by Stacks 0E8J for the genuine derived tensor product.

*On satisfiability.*  The ringed-space analogue of this predicate,
`AlgebraicGeometry.RingedSpace.FiniteTorDimensionRestricts`, comes with a witness,
`AlgebraicGeometry.RingedSpace.finiteTorDimensionRestricts_firstProjection`: it holds for the
family of first-projection certificates.  That witness has no analogue here, and the reason is
the strength of the datum rather than a universe gap.
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` carries its *own* underived
tensor product as a field, so the first projection `(ℰ, ℱ) ↦ ℰ` is an inhabitant of it — its
derived half is the identity functor of `D(𝒪_X)`, which is the total left derivation of the
identity.  `Stacks.SheafOfModules.DerivedTensorProduct` has no such field: its `comparison`,
`comparisonLeft`, `comparisonRight` and `toTensor` pin the value against the *global*
`Stacks.SheafOfModules.Tensor.tensorComplex`, so a first-projection `tensor` would have to
provide `comparison K L : Q K ≅ Q (K ⊗ L)` for every pair of K-flat complexes, which already
fails for `L = 0`.  Every inhabitant of this datum therefore computes the genuine derived
tensor product, and the only construction of one is
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, Stacks 06YU — which is available for a
ringed site whose objects form a type in a universe of their own, independent of the one in
which its morphisms and the sections of its structure sheaf and its modules lie, so a family
on the slices of such a site is constructible and this predicate is not vacuous on one.  For
the small étale site of an algebraic space that family is
`AlgebraicGeometry.Space.canonicalSliceDerivedTensorProduct`. -/
def FiniteTorDimensionRestricts : Prop :=
  ∀ ⦃V W : X.C⦄, (W ⟶ V) → ∀ E : RingedSite.DerivedModules.{u, v, w, d} X,
    HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj E) →
      HasFiniteTorDimension (T W) ((RingedSite.derivedRestriction.{u, v, w, d} X W).obj E)

/-- **Two local hypotheses combined on a common refinement.** If `A` and `B` locally have finite
Tor dimension and, over every object of the site, finite Tor dimension of `A` and of `B` forces
that of `C`, then `C` locally has finite Tor dimension: the intersection of the two covering
sieves is covering, and `FiniteTorDimensionRestricts` transports both hypotheses along the
arrow which exhibits a member of the intersection as factoring through a member of the
covering. -/
theorem locallyHasFiniteTorDimension_of_two (hres : FiniteTorDimensionRestricts T)
    (A B C : RingedSite.DerivedModules.{u, v, w, d} X)
    (hA : LocallyHasFiniteTorDimension T A) (hB : LocallyHasFiniteTorDimension T B)
    (key : ∀ V : X.C,
      HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj A) →
        HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj B) →
          HasFiniteTorDimension (T V)
            ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj C)) :
    LocallyHasFiniteTorDimension T C := by
  intro U
  obtain ⟨S, hS, hdata⟩ := hA U
  obtain ⟨S', hS', hdata'⟩ := hB U
  refine ⟨(Sieve.generate S ⊓ Sieve.generate S').arrows, by
    simpa using X.J.intersection_covering hS hS', fun {V} f hf => ?_⟩
  obtain ⟨⟨Y, p, q, hq, -⟩, ⟨Y', p', q', hq', -⟩⟩ := hf
  exact key V (hres p A (hdata q hq)) (hres p' B (hdata' q' hq'))

/-- **Two out of three when the first hypothesis holds over every object.** The covering
witnessing the local hypothesis for `B` serves for `C` as well, with no refinement. -/
theorem locallyHasFiniteTorDimension_of_forall_locally
    (A B C : RingedSite.DerivedModules.{u, v, w, d} X)
    (hA : ∀ V : X.C,
      HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj A))
    (hB : LocallyHasFiniteTorDimension T B)
    (key : ∀ V : X.C,
      HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj A) →
        HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj B) →
          HasFiniteTorDimension (T V)
            ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj C)) :
    LocallyHasFiniteTorDimension T C := by
  intro U
  obtain ⟨S, hS, hdata⟩ := hB U
  exact ⟨S, hS, fun {V} f hf => key V (hA V) (hdata f hf)⟩

/-- **Two out of three when the second hypothesis holds over every object.** The covering
witnessing the local hypothesis for `A` serves for `C` as well, with no refinement. -/
theorem locallyHasFiniteTorDimension_of_locally_forall
    (A B C : RingedSite.DerivedModules.{u, v, w, d} X)
    (hA : LocallyHasFiniteTorDimension T A)
    (hB : ∀ V : X.C,
      HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj B))
    (key : ∀ V : X.C,
      HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj A) →
        HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj B) →
          HasFiniteTorDimension (T V)
            ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj C)) :
    LocallyHasFiniteTorDimension T C := by
  intro U
  obtain ⟨S, hS, hdata⟩ := hA U
  exact ⟨S, hS, fun {V} f hf => key V (hdata f hf) (hB V)⟩

/-- **Every restriction of a zero object has finite Tor dimension.** Restriction to a slice is
additive, so it carries a zero object to a zero object. -/
theorem forall_hasFiniteTorDimension_of_isZero
    {E : RingedSite.DerivedModules.{u, v, w, d} X} (hE : IsZero E) (V : X.C) :
    HasFiniteTorDimension (T V) ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj E) :=
  hasFiniteTorDimension_of_isZero (T V)
    ((RingedSite.derivedRestriction.{u, v, w, d} X V).map_isZero hE)

/-- **A zero object locally has finite Tor dimension**, by the maximal covering of every
object. -/
theorem locallyHasFiniteTorDimension_of_isZero
    {E : RingedSite.DerivedModules.{u, v, w, d} X} (hE : IsZero E) :
    LocallyHasFiniteTorDimension T E :=
  locallyHasFiniteTorDimension_of_forall T E (forall_hasFiniteTorDimension_of_isZero T hE)

omit [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max u v, v, w} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)] in
/-- **The restriction of a distinguished triangle to a slice is distinguished**, restriction
being induced by an exact functor. -/
theorem mapTriangle_derivedRestriction_distinguished (V : X.C)
    (tri : Triangle (RingedSite.DerivedModules.{u, v, w, d} X))
    (htri : tri ∈ distinguishedTriangles) :
    (RingedSite.derivedRestriction.{u, v, w, d} X V).mapTriangle.obj tri ∈
      distinguishedTriangles :=
  Functor.map_distinguished _ tri htri

/-- **Two out of three for locally finite Tor dimension when the middle vertex holds over every
object of the site.** No refinement of coverings is needed, so no hypothesis on the family: the
covering witnessing the hypothesis for the other vertex serves for the conclusion. The case
this is for is a zero middle vertex, i.e. the contractible triangles. -/
theorem locallyHasFiniteTorDimension_of_distinguished_obj₂_forall
    (tri : Triangle (RingedSite.DerivedModules.{u, v, w, d} X))
    (htri : tri ∈ distinguishedTriangles)
    (h₂ : ∀ V : X.C, HasFiniteTorDimension (T V)
      ((RingedSite.derivedRestriction.{u, v, w, d} X V).obj tri.obj₂)) :
    (LocallyHasFiniteTorDimension T tri.obj₁ → LocallyHasFiniteTorDimension T tri.obj₃) ∧
      (LocallyHasFiniteTorDimension T tri.obj₃ → LocallyHasFiniteTorDimension T tri.obj₁) := by
  have key (V : X.C) := hasFiniteTorDimension_of_distinguished (T V) _
    (mapTriangle_derivedRestriction_distinguished V tri htri)
  exact ⟨fun h₁ => locallyHasFiniteTorDimension_of_locally_forall T _ _ _ h₁ h₂
      fun V => (key V).1,
    fun h₃ => locallyHasFiniteTorDimension_of_forall_locally T _ _ _ h₂ h₃
      fun V => (key V).2.2⟩

/-- **Stacks 08G2 for locally finite Tor dimension**: two out of three in a distinguished
triangle, under `FiniteTorDimensionRestricts` for the family. Over a common refinement of the
two coverings, restriction to a slice carries the triangle to a distinguished triangle, where
Stacks 08G2 applies. -/
theorem locallyHasFiniteTorDimension_of_distinguished (hres : FiniteTorDimensionRestricts T)
    (tri : Triangle (RingedSite.DerivedModules.{u, v, w, d} X))
    (htri : tri ∈ distinguishedTriangles) :
    (LocallyHasFiniteTorDimension T tri.obj₁ → LocallyHasFiniteTorDimension T tri.obj₂ →
        LocallyHasFiniteTorDimension T tri.obj₃) ∧
      (LocallyHasFiniteTorDimension T tri.obj₁ → LocallyHasFiniteTorDimension T tri.obj₃ →
        LocallyHasFiniteTorDimension T tri.obj₂) ∧
      (LocallyHasFiniteTorDimension T tri.obj₂ → LocallyHasFiniteTorDimension T tri.obj₃ →
        LocallyHasFiniteTorDimension T tri.obj₁) := by
  have key (V : X.C) := hasFiniteTorDimension_of_distinguished (T V) _
    (mapTriangle_derivedRestriction_distinguished V tri htri)
  exact ⟨fun h₁ h₂ => locallyHasFiniteTorDimension_of_two T hres _ _ _ h₁ h₂
      fun V => (key V).1,
    fun h₁ h₃ => locallyHasFiniteTorDimension_of_two T hres _ _ _ h₁ h₃
      fun V => (key V).2.1,
    fun h₂ h₃ => locallyHasFiniteTorDimension_of_two T hres _ _ _ h₂ h₃
      fun V => (key V).2.2⟩

end SliceFamily

end Stacks.SheafOfModules.DerivedTensorProduct

end
