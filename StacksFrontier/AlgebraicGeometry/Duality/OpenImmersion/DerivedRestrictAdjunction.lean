module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.CategoryTheory.Triangulated.GeneratorAdjunction
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections

/-!
# The derived adjunction `j^* ⊣ Rj_*` along an open immersion, at an arbitrary model

Let `j : X ⟶ Y` be an open immersion of schemes. Restriction of sheaves of modules along `j` is
exact, so it induces a functor `j^* : D(𝒪_Y) ⥤ D(𝒪_X)` with no derivation required, and its
right adjoint — direct image — has an unbounded right derived functor `Rj_* : D(𝒪_X) ⥤ D(𝒪_Y)`
because `𝒪_X`-modules form a Grothendieck abelian category and therefore have K-injective
resolutions ([Stacks, Tag 079Q]). This file constructs the adjunction `j^* ⊣ Rj_*` for an
arbitrary choice of model of the two derived categories, together with its restriction to full
subcategories and the resulting generation step of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A].

## Main definitions

* `Stacks.Duality.OpenImmersion.derivedRestrict`: the functor `j^* : D(𝒪_Y) ⥤ D(𝒪_X)`.
* `Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction`: the adjunction
  `j^* ⊣ Rj_*`, at an arbitrary model of the derived categories.
* `Stacks.Duality.OpenImmersion.liftDerivedRestrictPushforwardAdjunction`: the same adjunction
  restricted to a pair of full subcategories preserved by the two functors.

## Main results

* `Stacks.Duality.OpenImmersion.isZero_of_rightOrthogonal_of_openImmersion`: an object of `A`
  right orthogonal to all shifts of `Q` and of `K` is zero.
* `Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_openImmersion`: `Q ⊞ K`
  is a weak generator of `A`.
* `Stacks.Duality.OpenImmersion.isLeftAdjoint_derivedRestrict` and
  `Stacks.Duality.OpenImmersion.isRightAdjoint_derivedPushforward`: the two halves as instances.

## Implementation notes

No `@[stacks]` attribute is attached. The adjunction itself is the content of [Stacks, Tag 08DF]
only after one knows that `Rj_*` is extension by zero on complexes supported on a closed subset,
and [Stacks, Tag 0A9A] needs in addition [Stacks, Tag 09IR], [Stacks, Tag 09IM] and
[Stacks, Tag 08DP]. Tag 09IR is
`Stacks.Koszul.Truncation.hom_koszulObject_eq_zero_of_isIso_unit` and
`Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero` in
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineSituation.lean`; Tag 08DP is
`Stacks.Cohomology.ClosedSupportPerfect.isPerfect_derivedPushforward_of_closedSupport` in
`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/ClosedSupportPerfect.lean`.

`derivedRestrict` is `Functor.mapDerivedCategory` of restriction rather than a left derived
functor. The two agree for an exact functor, and `mapDerivedCategory` carries the
`Functor.CommShift` and `Functor.IsTriangulated` instances.

The adjunction is `Stacks.SmallDerivedCategory.derivedAdjunction` applied to
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, with additivity and exactness of
restriction from `StacksFrontier/AlgebraicGeometry/PseudoCoherent/RestrictExact.lean`, `Rj_*` from
`Stacks.Duality.derivedPushforward` and its total-right-derived unit, and the K-injective
resolutions from `AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective`. The derived
category is an instance argument throughout, unlike the adjunctions elaborated under a file-level
`attribute [local instance] HasDerivedCategory.standard`, so the adjunction holds at the locally
small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, in which the direct sums
of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A] exist.

The subcategory form takes the two preservation facts as explicit hypotheses, in the style of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/Exactness.lean`, so that it applies to
any pair of full subcategories preserved by `j^*` and `Rj_*`. For the pair `D_{QCoh,T}(𝒪_Y)`,
`D_{QCoh,T ∩ U}(𝒪_U)` of [Stacks, Tag 0A9A] they are discharged by
`AlgebraicGeometry.isQuasicoherent_derivedPushforward_affineLocal`,
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` and
`Stacks.DerivedQCoh.cohomologySupportedOn_derivedPushforward_scheme` (for `hpush`), and by
`Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrict` and
`Stacks.DerivedQCoh.isQuasicoherent_derivedRestrict` (for `hres`).

The abstract generation step that consumes this adjunction is
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_biprod_of_adjunction` in
`StacksFrontier/CategoryTheory/Triangulated/GeneratorAdjunction.lean`.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe w u

namespace Stacks.Duality.OpenImmersion

section

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- `j^* : D(𝒪_Y) ⥤ D(𝒪_X)`, the functor on unbounded derived categories induced by the exact
functor of restriction of sheaves of modules along an open immersion. -/
abbrev derivedRestrict : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules :=
  (Scheme.Modules.restrictFunctor j).mapDerivedCategory

/-- **The derived adjunction `j^* ⊣ Rj_*` along an open immersion of schemes**, at an arbitrary
model of the two derived categories. -/
def derivedRestrictPushforwardAdjunction :
    derivedRestrict j ⊣ Stacks.Duality.derivedPushforward j :=
  Stacks.SmallDerivedCategory.derivedAdjunction (Scheme.Modules.restrictAdjunction j)
    (Iso.refl _)
    ((Stacks.Duality.homotopyPushforward j).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    (AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X)

/-- `j^* : D(𝒪_Y) ⥤ D(𝒪_X)` is a left adjoint. -/
instance isLeftAdjoint_derivedRestrict : (derivedRestrict j).IsLeftAdjoint :=
  (derivedRestrictPushforwardAdjunction j).isLeftAdjoint

/-- `Rj_* : D(𝒪_X) ⥤ D(𝒪_Y)` is a right adjoint. -/
instance isRightAdjoint_derivedPushforward :
    (Stacks.Duality.derivedPushforward j).IsRightAdjoint :=
  (derivedRestrictPushforwardAdjunction j).isRightAdjoint

end

/-! ### The adjunction between full subcategories -/

section Subcategories

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
  (A : ObjectProperty (DerivedCategory Y.Modules))
  (B : ObjectProperty (DerivedCategory X.Modules))
  (hres : ∀ K : A.FullSubcategory, B ((derivedRestrict j).obj K.obj))
  (hpush : ∀ L : B.FullSubcategory,
    A ((Stacks.Duality.derivedPushforward j).obj L.obj))

/-- `j^*` restricted to a full subcategory `A ⊆ D(𝒪_Y)` whose image it sends into
`B ⊆ D(𝒪_X)`. -/
abbrev liftDerivedRestrict : A.FullSubcategory ⥤ B.FullSubcategory :=
  B.lift (A.ι ⋙ derivedRestrict j) hres

/-- `Rj_*` restricted to a full subcategory `B ⊆ D(𝒪_X)` whose image it sends into
`A ⊆ D(𝒪_Y)`. -/
abbrev liftDerivedPushforward : B.FullSubcategory ⥤ A.FullSubcategory :=
  A.lift (B.ι ⋙ Stacks.Duality.derivedPushforward j) hpush

/-- **The adjunction `j^* ⊣ Rj_*` between full subcategories.** If a strictly full subcategory
`A ⊆ D(𝒪_Y)` is carried into `B ⊆ D(𝒪_X)` by `j^*` and `B` is carried into `A` by `Rj_*`, then
the two restrictions are adjoint. This is
`CategoryTheory.Adjunction.restrictFullyFaithful` applied to
`derivedRestrictPushforwardAdjunction`. -/
def liftDerivedRestrictPushforwardAdjunction :
    liftDerivedRestrict j A B hres ⊣ liftDerivedPushforward j A B hpush :=
  Adjunction.restrictFullyFaithful (derivedRestrictPushforwardAdjunction j) A.fullyFaithfulι
    B.fullyFaithfulι (B.liftCompιIso (A.ι ⋙ derivedRestrict j) hres).symm
    (A.liftCompιIso (B.ι ⋙ Stacks.Duality.derivedPushforward j) hpush).symm

end Subcategories

/-! ### The inductive step of Tags 09IS and 0A9A -/

section GenerationStep

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
  (A : ObjectProperty (DerivedCategory Y.Modules))
  (B : ObjectProperty (DerivedCategory X.Modules))
  [A.IsTriangulated] [B.IsTriangulated]
  (hres : ∀ K : A.FullSubcategory, B ((derivedRestrict j).obj K.obj))
  (hpush : ∀ L : B.FullSubcategory,
    A ((Stacks.Duality.derivedPushforward j).obj L.obj))

/-- **The last paragraph of the proofs of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A], for an open
immersion of schemes.** Let `j : X ⟶ Y` be an open immersion, let `A ⊆ D(𝒪_Y)` and `B ⊆ D(𝒪_X)`
be strictly full triangulated subcategories with `j^* A ⊆ B` and `Rj_* B ⊆ A`, and let `Q`, `K` be
objects of `A` and `P` an object of `B` such that

* `P` is a direct summand of `j^* Q`;
* `P` is a weak generator of `B`;
* an object of `A` right orthogonal to all shifts of `K` has invertible unit
  `E ⟶ Rj_*(j^* E)` (`hunit`).

Then an object of `A` right orthogonal to all shifts of `Q` and to all shifts of `K` is zero.

The hypothesis `hunit` is the geometric input: [Stacks, Tag 09IR], together with the
identification of `Rj_*` with extension by zero, [Stacks, Tag 08DF]. -/
theorem isZero_of_rightOrthogonal_of_openImmersion
    {Q K : A.FullSubcategory} {P : B.FullSubcategory}
    (hret : Retract P ((liftDerivedRestrict j A B hres).obj Q))
    (hP : (ObjectProperty.singleton P).IsWeakTriangulatedGenerator)
    (hunit : ∀ E : A.FullSubcategory,
      ((ObjectProperty.singleton K).shiftClosure ℤ).rightOrthogonal E →
        IsIso ((liftDerivedRestrictPushforwardAdjunction j A B hres hpush).unit.app E))
    (E : A.FullSubcategory)
    (hQ : ((ObjectProperty.singleton Q).shiftClosure ℤ).rightOrthogonal E)
    (hK : ((ObjectProperty.singleton K).shiftClosure ℤ).rightOrthogonal E) :
    IsZero E :=
  ObjectProperty.isZero_of_rightOrthogonal_of_adjunction
    (liftDerivedRestrictPushforwardAdjunction j A B hres hpush) hret hP hunit E hQ hK

/-- **`Q ⊞ K` is a weak generator of `A`**: the inductive step of [Stacks, Tag 09IS] and
[Stacks, Tag 0A9A] for an open immersion of schemes. Let `j : X ⟶ Y` be an open immersion, let
`A ⊆ D(𝒪_Y)` and `B ⊆ D(𝒪_X)` be strictly full triangulated subcategories with `j^* A ⊆ B` and
`Rj_* B ⊆ A`, and let `Q`, `K` be objects of `A` and `P` an object of `B` such that `P` is a
direct summand of `j^* Q` and a weak generator of `B`, and such that every object `E` of `A` right
orthogonal to all shifts of `K` has invertible unit `E ⟶ Rj_*(j^* E)` (`hunit`). Then `Q ⊞ K` is
a weak generator of `A`.

In [Stacks, Tag 0A9A] this is applied with `A = D_{QCoh,T}(𝒪_Y)` and
`B = D_{QCoh,T ∩ X}(𝒪_X)` for a quasi-compact open `X ⊆ Y`, with `Q` the perfect object of
[Stacks, Tag 09IM] extending the generator `P` of `B`, and `K` the pushforward along the
complementary affine of a Koszul complex ([Stacks, Tag 08DP]). -/
theorem isWeakTriangulatedGenerator_biprod_of_openImmersion
    {Q K : A.FullSubcategory} {P : B.FullSubcategory}
    (hret : Retract P ((liftDerivedRestrict j A B hres).obj Q))
    (hP : (ObjectProperty.singleton P).IsWeakTriangulatedGenerator)
    (hunit : ∀ E : A.FullSubcategory,
      ((ObjectProperty.singleton K).shiftClosure ℤ).rightOrthogonal E →
        IsIso ((liftDerivedRestrictPushforwardAdjunction j A B hres hpush).unit.app E)) :
    (ObjectProperty.singleton (Q ⊞ K)).IsWeakTriangulatedGenerator :=
  have : ∀ n : ℤ, (shiftFunctor A.FullSubcategory n).Additive := fun _ => inferInstance
  ObjectProperty.isWeakTriangulatedGenerator_singleton_biprod_of_adjunction
    (liftDerivedRestrictPushforwardAdjunction j A B hres hpush) hret hP hunit

end GenerationStep

end Stacks.Duality.OpenImmersion

end
