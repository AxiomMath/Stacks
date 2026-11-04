module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoherentSerreVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExactSingleRight
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# The twists of `ℙⁿ_A` on the derived category

Let `A` be a ring and `X = ℙⁿ_A = Proj A[T₀, …, Tₙ]`. Twisting by `𝒪_X(d)` is an exact
autoequivalence of `𝒪_X`-modules, so it induces a triangulated autoequivalence `K ↦ K(d)` of
`D(𝒪_X)`. This file records that autoequivalence, its values on the twisting sheaves placed in
degree zero, and its agreement with the derived tensor product: `K ⊗^𝐋 𝒪_X(d) ≅ K(d)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistFunctor.twistModules`: the twist `- ⊗ 𝒪(d)` on `X.Modules`.
* `Stacks.AlgebraicGeometry.ProjTwistFunctor.derivedTwist`: the induced autoequivalence of
  `D(𝒪_X)`.
* `Stacks.AlgebraicGeometry.ProjTwistFunctor.derivedTensorTwistIso`: `K ⊗^𝐋 𝒪(d) ≅ K(d)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjTwistFunctor

/-- Abelian-group-valued presheaves on the opens of a topological space admit sheafification. -/
theorem hasSheafify_opens_topCat (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
/-- On the opens of a topological space, the morphisms of abelian-group-valued presheaves
inverted by sheafification are exactly the locally bijective ones. -/
theorem wEqualsLocallyBijective_opens_topCat (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
/-- Abelian-group-valued presheaves on the opens of a scheme admit sheafification. -/
theorem hasSheafify_opens_scheme (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
/-- On the opens of a scheme, the morphisms of abelian-group-valued presheaves inverted by
sheafification are exactly the locally bijective ones. -/
theorem wEqualsLocallyBijective_opens_scheme (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance

attribute [local instance 10000] hasSheafify_opens_topCat wEqualsLocallyBijective_opens_topCat
  hasSheafify_opens_scheme wEqualsLocallyBijective_opens_scheme

variable (A : Type u) [CommRing A] (n : ℕ)

/-- **Twisting by `𝒪(d)` is an autoequivalence of `𝒪_{ℙⁿ_A}`-modules**, for every `n` and `d`:
the standard opens are attached to the degree-one variables, so `𝒪(d)` is invertible
([Stacks, Tag 01MT]). -/
instance isEquivalence_twistFunctor_polyGrading (d : ℤ) :
    (twistFunctor (polyGrading A n) d).IsEquivalence :=
  letI : Stacks.SheafOfModules.IsInvertible
      (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A n)).obj
      (projRingSheaf (polyGrading A n)).property
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
      (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf
        (polyGrading A n) (Stacks.AlgebraicGeometry.ProjTwistRank.degreeOneCover_polyGrading A n) d)
  isEquivalence_twistFunctor (polyGrading A n) d

/-- The twist `- ⊗ 𝒪(d)` on `𝒪_X`-modules, `X = ℙⁿ_A`, at the scheme-level spelling `X.Modules`
of the category of modules. -/
def twistModules (d : ℤ) :
    (AlgebraicGeometry.Proj (polyGrading A n)).Modules ⥤
      (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  twistFunctor (polyGrading A n) d

/-- The twist `- ⊗ 𝒪(d)` on `𝒪_X`-modules is additive. -/
instance (d : ℤ) : (twistModules A n d).Additive :=
  additive_twistFunctor (polyGrading A n) d

/-- The twist `- ⊗ 𝒪(d)` on `𝒪_X`-modules is an equivalence. -/
instance (d : ℤ) : (twistModules A n d).IsEquivalence :=
  isEquivalence_twistFunctor_polyGrading A n d

/-- The twist `- ⊗ 𝒪(d)` on `𝒪_X`-modules preserves finite limits. -/
instance (d : ℤ) : PreservesFiniteLimits (twistModules A n d) := inferInstance

/-- The twist `- ⊗ 𝒪(d)` on `𝒪_X`-modules preserves finite colimits. -/
instance (d : ℤ) : PreservesFiniteColimits (twistModules A n d) := inferInstance

/-- **`𝒪(k)(d) ≅ 𝒪(k + d)`** on `ℙⁿ_A` ([Stacks, Tag 01MO]), the polynomial ring being generated
in degree one. -/
def twistModulesTwistingSheafIso (k d : ℤ) :
    (twistModules A n d).obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) k) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (k + d) :=
  @asIso _ _ _ _ (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
      (polyGrading A n) k d)
    (Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin
      (polyGrading A n) (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A n) k d)

/-- **The twist `K ↦ K(d)` of `D(𝒪_X)`**, `X = ℙⁿ_A`: the triangulated autoequivalence induced by
the exact autoequivalence `- ⊗ 𝒪(d)` of `𝒪_X`-modules. -/
def derivedTwist (d : ℤ) :
    DerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)).Modules ≌
      DerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  letI : (twistModules A n d).asEquivalence.functor.Additive :=
    inferInstanceAs (twistModules A n d).Additive
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (twistModules A n d).asEquivalence

/-- The functor of the twist `K ↦ K(d)` of `D(𝒪_X)` is the functor `- ⊗ 𝒪(d)` induces on
derived categories. -/
theorem derivedTwist_functor (d : ℤ) :
    (derivedTwist A n d).functor = (twistModules A n d).mapDerivedCategory := rfl

/-- The twist `K ↦ K(d)` of `D(𝒪_X)` commutes with the shift. -/
instance (d : ℤ) : (derivedTwist A n d).functor.CommShift ℤ :=
  inferInstanceAs ((twistModules A n d).mapDerivedCategory.CommShift ℤ)

/-- The twist `K ↦ K(d)` of `D(𝒪_X)` is a triangulated functor. -/
instance (d : ℤ) : (derivedTwist A n d).functor.IsTriangulated :=
  inferInstanceAs ((twistModules A n d).mapDerivedCategory.IsTriangulated)

/-- The twist of a module placed in degree zero is its twist placed in degree zero. -/
def derivedTwistSingleIso (d : ℤ) (M : (AlgebraicGeometry.Proj (polyGrading A n)).Modules) :
    (derivedTwist A n d).functor.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((twistModules A n d).obj M) :=
  ((twistModules A n d).mapDerivedCategorySingleFunctor 0).app M

/-- **`𝒪(k)[0](d) ≅ 𝒪(k + d)[0]`** in `D(𝒪_X)`. -/
def derivedTwistTwistingSheafIso (k d : ℤ) :
    (derivedTwist A n d).functor.obj ((DerivedCategory.singleFunctor _ 0).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) k)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (k + d)) :=
  derivedTwistSingleIso A n d _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (twistModulesTwistingSheafIso A n k d)

/-- The structure sheaf of `ℙⁿ_A` is its zeroth twist. -/
def twistingSheafZeroIso :
    ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) 0 ≅
      SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading A n)

/-- **`𝒪[0](-d) ≅ 𝒪(-d)[0]`**: the inverse of the twist by `d` sends the structure sheaf in degree
zero to `𝒪(-d)` in degree zero. -/
def derivedTwistInverseUnitIso (d : ℤ) :
    (derivedTwist A n d).inverse.obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (-d)) :=
  (derivedTwist A n d).inverse.mapIso
      ((derivedTwistTwistingSheafIso A n (-d) d ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (eqToIso (congrArg (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n))
            (neg_add_cancel d)) ≪≫ twistingSheafZeroIso A n)).symm) ≪≫
    ((derivedTwist A n d).unitIso.app _).symm

/-- **`K ⊗^𝐋 𝒪(d) ≅ K(d)`**: the derived tensor product with the twisting sheaf placed in degree
zero is the twist of `D(𝒪_X)`. -/
def derivedTensorTwistIso (d : ℤ)
    (K : DerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)).Modules) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (AlgebraicGeometry.Proj (polyGrading A n)).sheaf).obj K).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)) ≅
      (derivedTwist A n d).functor.obj K :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleRightIsoOfExact
    (Stacks.RingedSpace.toRingedSite (AlgebraicGeometry.Proj (polyGrading A n)).toRingedSpace)
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      (AlgebraicGeometry.Proj (polyGrading A n)).sheaf)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)
    (twistModules A n d) (hFa := inferInstanceAs (twistModules A n d).Additive)
    (hFl := inferInstanceAs (PreservesFiniteLimits (twistModules A n d)))
    (hFc := inferInstanceAs (PreservesFiniteColimits (twistModules A n d))) rfl K

end Stacks.AlgebraicGeometry.ProjTwistFunctor

end
