module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantPerfectComplexBounded
public import StacksFrontier.CategoryTheory.Sites.Point.FlatModuleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Flat stalks over the constant coefficients, and exactness at the module universe

On the small étale site of a scheme `X` with Noetherian coefficient ring `Λ`, the trivialization
of Tag 09BI by a single finite complex of finite projective `Λ`-modules is
`Stacks.ConstantSheaf.exists_cover_constantFiniteProjectiveComplex_of_point'`, whose remaining
input is a bounded flat representative over `Λ` of the complex of coefficients of a constant
model. Two ingredients of that input are supplied here: the exactness of the fibre functor at a
localized point of the site, at the single module universe the small étale site forces, and the
flatness over `Λ` of the stalk of a flat module over the restricted constant coefficient ring
sheaf.

## Main results

* `AlgebraicGeometry.preservesFiniteLimits_sheafFiberOver` and
  `AlgebraicGeometry.additive_sheafFiberOver`: the fibre functor at a point of the slice over an
  object carrying a point of the site is left exact and additive on sheaves of modules.
* `AlgebraicGeometry.overPullback_preservesFiniteLimits`: restriction of sheaves to a slice site
  preserves finite limits.
* `AlgebraicGeometry.flat_coefficientStalk`: **Stacks 05VB over the coefficient ring.** The
  stalk, at a lift of a point of the small étale site, of a flat module over the restricted
  constant coefficient ring sheaf is a flat `Λ`-module.

## Implementation notes

The exactness statements are proved with the three universes of the site free and instantiated
later, rather than inferred in place. At the small étale site the objects lie in
`Type (u + 1)`, the morphisms in `Type u` and the coefficients in `Type u`, so the module
universe `max u v r` of the generic statements collapses to the single universe `u + 1`; the
instances carrying the exactness of a filtered colimit of modules are stated at
`ModuleCat.{max u v r}`, and an instance search at `ModuleCat.{u + 1}` leaves the universe
equation `max (u + 1) ? = u + 1`, which has no unique solution.

Flatness of the stalk over `Λ` rather than over the stalk of the structure sheaf is Stacks 05VB
(`Stacks.isFlatModuleStalk_of_isFlat`) followed by
`AlgebraicGeometry.flat_of_semilinear_equiv` along
`AlgebraicGeometry.constantCoefficientRingOverFiberEquiv`, which identifies the stalk on a slice
of the constant coefficient ring sheaf with `Λ` itself. The additive equivalence is the identity
on carriers, restriction of scalars changing only the action.

Two steps of Tag 09BI are not proved here, so the tag is not placed in this file. The
Tor-dimension input itself — assembling
`AlgebraicGeometry.exists_hasTorAmplitude_derivedRestriction_of_point`, Stacks 08G1
(`Stacks.SheafOfModules.DerivedTensorProduct.exists_flatRepresentative_of_hasTorAmplitude`), the
stalk comparison `AlgebraicGeometry.moduleSheafOverConstantCoefficientsSheafFiberComplexIso` and
`AlgebraicGeometry.hasFlatRepresentative_restrictScalars` into a flat representative of the
derived fibre — needs the restriction functor `SheafOfModules.overFunctor` to be exact at the
module universe of this site, and
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits` is stated with its
module universe written as a free variable that no argument of the statement pins down here.
Boundedness of the underlying object of the derived category is the other gap: in the source it
is derived from membership of `D_{ctf}` by bounding the cohomology of one restriction through the
Tor amplitude and spreading that bound over the connected base with
`AlgebraicGeometry.isZero_of_isZero_overPullback_of_connectedSpace`. Spreading it also needs the
transport of vanishing across
`AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor`, which is not proved here but is
`AlgebraicGeometry.isZero_overPullback_of_isZero_over_moduleSheafOverConstantCoefficients` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ConstantCoefficientsConservative.lean`.

## References

* [Stacks Project, Tag 09BI](https://stacks.math.columbia.edu/tag/09BI)
* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe r v c m u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits

/-! ### Limits of modules and exactness of the fibre functor -/

/-- Filtered colimits of modules are exact in any module universe containing the ring: the
forgetful functor to that universe is exact and preserves them, the ring having a small model
there. -/
lemma ab5OfSize_moduleCat (Γ : Type r) [Ring Γ] [Small.{m} Γ] :
    AB5OfSize.{m, m} (ModuleCat.{m} Γ) :=
  have : PreservesFilteredColimits (forget (ModuleCat.{m} Γ)) := by
    let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (Shrink.ringEquiv Γ : Shrink.{m} Γ ≃+* Γ)
    show PreservesFilteredColimits (e.functor ⋙ forget (ModuleCat.{m} (Shrink.{m} Γ)))
    infer_instance
  ⟨fun I _ _ => HasExactColimitsOfShape.domain_of_functor I (forget (ModuleCat.{m} Γ))⟩

/-- Modules over a ring have all limits in a carrier universe containing the ring. -/
lemma hasLimits_moduleCat (Γ : Type r) [Ring Γ] :
    HasLimitsOfSize.{max r m, max r m} (ModuleCat.{max r m} Γ) := inferInstance

/-- The fibre functor at a point of the slice over an object carrying a point of the site is
left exact on sheaves of modules at the module universe of the site. -/
lemma preservesFiniteLimits_sheafFiberOver {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (Γ : Type r) [CommRing Γ]
    [∀ W : C, HasSheafify (J.over W) (ModuleCat.{max c v r} Γ)]
    (q : J.Point.{max c v r}) {W : C} (z : q.fiber.obj W) :
    PreservesFiniteLimits ((q.over z).sheafFiber (A := ModuleCat.{max c v r} Γ)) := by
  have : Small.{max c v r} Γ := small_max.{max c v r} Γ
  have : AB5OfSize.{max c v r, max c v r} (ModuleCat.{max c v r} Γ) := ab5OfSize_moduleCat Γ
  have : LocallySmall.{max c v r} C := CategoryTheory.locallySmall_max.{max c v r, v, c}
  have : LocallySmall.{max c v r} (Over W) :=
    CategoryTheory.locallySmall_max.{max c v r, v, max c v}
  infer_instance

/-- The fibre functor at a point of the slice over an object carrying a point of the site is
additive on sheaves of modules at the module universe of the site. -/
lemma additive_sheafFiberOver {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (Γ : Type r) [CommRing Γ]
    [∀ W : C, HasSheafify (J.over W) (ModuleCat.{max c v r} Γ)]
    (q : J.Point.{max c v r}) {W : C} (z : q.fiber.obj W) :
    ((q.over z).sheafFiber (A := ModuleCat.{max c v r} Γ)).Additive :=
  have := preservesFiniteLimits_sheafFiberOver J Γ q z
  Functor.additive_of_preserves_binary_products
    ((q.over z).sheafFiber (A := ModuleCat.{max c v r} Γ))

/-- Restriction of sheaves to a slice site preserves finite limits: on underlying presheaves it
is precomposition with the forgetful functor of the slice, and limits of sheaves are created by
the inclusion into presheaves. -/
lemma overPullback_preservesFiniteLimits {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (A : Type*) [Category* A] [Abelian A] [HasSheafify J A]
    [∀ W : C, HasSheafify (J.over W) A] (W : C) :
    PreservesFiniteLimits (J.overPullback A W) := by
  have : PreservesFiniteLimits (J.overPullback A W ⋙ sheafToPresheaf (J.over W) A) := by
    show PreservesFiniteLimits
      (sheafToPresheaf J A ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget W).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf (J.over W) A)

/-! ### Flat stalks over the constant coefficient ring sheaf -/

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type u) [CommRing Λ]

/-- The stalk, at the lift to the slice over `V` of a point of the small étale site, of a module
over the restricted constant coefficient ring sheaf. -/
abbrev coefficientStalk
    (q : (SmallEtale.topology B X.obj X.property).Point.{u + 1})
    {V : SmallEtale B X.obj X.property} (z : q.fiber.obj V) :=
  Stacks.sheafModuleFiberOfCommRing.{u + 1, u, u + 1} (q.over z)
    ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over V).O

/-- The same stalk, read as a `Λ`-module along the identification of the stalk on a slice of the
constant coefficient ring sheaf with `Λ`. -/
abbrev coefficientStalkOverCoefficients
    (q : (SmallEtale.topology B X.obj X.property).Point.{u + 1})
    {V : SmallEtale B X.obj X.property} (z : q.fiber.obj V) :=
  coefficientStalk B X Λ q z ⋙ ModuleCat.restrictScalars.{u + 1}
    (constantCoefficientRingOverFiberEquiv.{u, u + 1, u} B X Λ q z).toRingHom

/-- **Stacks 05VB over the coefficient ring.** The stalk, at a lift to the slice over `V` of a
point of the small étale site, of a flat module over the restricted constant coefficient ring
sheaf is a flat `Λ`-module: the stalk of that ring sheaf is `Λ`. -/
theorem flat_coefficientStalk
    (q : (SmallEtale.topology B X.obj X.property).Point.{u + 1})
    {V : SmallEtale B X.obj X.property} (z : q.fiber.obj V)
    (M : RingedSite.Modules.{u + 1, u, u + 1}
      ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over V))
    (hM : SheafOfModules.IsFlat.{u, u + 1, u + 1, u + 1}
      (O := ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over V).O) M) :
    Module.Flat Λ ((coefficientStalkOverCoefficients B X Λ q z).obj M) :=
  have := Stacks.isFlatModuleStalk_of_isFlat.{u, u + 1, u + 1}
    (O := ((constantCoefficientRingedSite.{u, u + 1, u} B X Λ).over V).O) M hM (q.over z)
  flat_of_semilinear_equiv (constantCoefficientRingOverFiberEquiv.{u, u + 1, u} B X Λ q z)
    (AddEquiv.refl ((coefficientStalk B X Λ q z).obj M)) fun _ _ => rfl

end AlgebraicGeometry

end
