module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Homology.DerivedIndexing.Basic

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso

/-!
# The Leray collapse over a field

Let `π : Y ⟶ Z` be a morphism of schemes and `M` an `𝒪_Y`-module whose higher direct images
`R^q π_* M` vanish for `q > 0`. Then the cohomology of `M` on `Y` is the cohomology of `π_* M` on
`Z`, in every degree ([Stacks, Tag 01F4] (1)). This file records the comparison as an
isomorphism of modules over `Γ(Z, ⊤)` after restriction of scalars along `π^♯`, and, for `Z` over
a field `k`, as an isomorphism of `k`-vector spaces between the two
`AlgebraicGeometry.cohomologyOverField`s, which is the form in which finite dimensionality is
transported along `π`.

The proof is the one of [Stacks, Tag 089W] with the vanishing hypothesis in place of
affineness: `M` is right acyclic for `π_*`, the direct image of an injective module has acyclic
global sections ([Stacks, Tag 01EX] (2)), so the right derived functor of `Γ(Z, -) ∘ π_*`
collapses onto `Hⁿ(Z, π_* -)` at `M`, and the other side is `Hⁿ(Y, -)` with its scalars
restricted ([Stacks, Tag 01EZ]).

## Main definitions

* `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOfRightAcyclic`: the comparison
  over `Γ(Z, ⊤)` for a right acyclic `M`.
* `AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsZero`: the comparison of
  `k`-vector spaces when the higher direct images vanish.

## References

* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.AffineBase

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.Cohomology.AffineComparison

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/-- **Cohomology is unchanged by a direct image along which the module is acyclic.** For a
morphism of schemes `f : X ⟶ S` and an `𝒪_X`-module `F` right acyclic for `f_*`, the cohomology of
`F` on `X`, read over `Γ(S, ⊤)` along `f^♯`, is the cohomology of `f_* F` on `S`, in every degree.
This is `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward` with the acyclicity of `F`
given rather than deduced from the affineness of `f`. -/
public def cohomologyIsoPushforwardOfRightAcyclic (F : X.Modules)
    (hF : (AlgebraicGeometry.Scheme.Modules.pushforward f).rightAcyclic F) (n : ℕ) :
    (ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F) ≅
      ((moduleGlobalSections S).rightDerived n).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F) :=
  restrictScalarsRightDerivedIso f F n ≪≫
    rightDerivedCollapseIso (AlgebraicGeometry.Scheme.Modules.pushforward f)
      (moduleGlobalSections S) (rightAcyclic_moduleGlobalSections_pushforward_obj f) F hF n

end Stacks.Cohomology.AffineComparison

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {Y Z : Scheme.{u}} (π : Y ⟶ Z)

/-- **[Stacks, Tag 01F4] (1) over a field.** Let `π : Y ⟶ Z` be a morphism of schemes, `g : Z ⟶
Spec k` a scheme over a field, and `M` an `𝒪_Y`-module with `R^q π_* M = 0` for every `q > 0`.
Then `Hⁿ(Y, M) ≅ Hⁿ(Z, π_* M)` as `k`-vector spaces, in every degree. -/
def cohomologyOverFieldPushforwardIsoOfIsZero (g : Z ⟶ Spec (.of k)) (M : Y.Modules)
    (hM : ∀ q : ℕ, 0 < q →
      IsZero (((Scheme.Modules.pushforward π).rightDerivedPlus (q : ℤ)).obj M)) (n : ℕ) :
    cohomologyOverField k (π ≫ g) M n ≅
      cohomologyOverField k g ((Scheme.Modules.pushforward π).obj M) n :=
  ModuleCat.restrictScalarsComp'App
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom
      (π.app (⊤ : Z.Opens)).hom
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (π ≫ g).appLE ⊤ ⊤ (by simp)).hom
      (by
        rw [← CommRingCat.hom_comp]
        refine congrArg CommRingCat.Hom.hom ?_
        rw [Category.assoc, Scheme.Hom.appLE_comp_top π g (by simp) (by simp)]
        rfl) _ ≪≫
    (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom).mapIso
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOfRightAcyclic π M
        ((Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat
          (Scheme.Modules.pushforward π) M).2 fun q hq =>
            (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q M).2 (hM q hq)) n)

/-- Finite dimensionality of cohomology transports along a direct image whose higher direct
images vanish. -/
theorem finiteDimensional_cohomologyOverField_of_pushforward_of_isZero (g : Z ⟶ Spec (.of k))
    (M : Y.Modules)
    (hM : ∀ q : ℕ, 0 < q →
      IsZero (((Scheme.Modules.pushforward π).rightDerivedPlus (q : ℤ)).obj M)) (n : ℕ)
    (h : FiniteDimensional k (cohomologyOverField k (π ≫ g) M n)) :
    FiniteDimensional k (cohomologyOverField k g ((Scheme.Modules.pushforward π).obj M) n) :=
  Module.Finite.equiv (cohomologyOverFieldPushforwardIsoOfIsZero k π g M hM n).toLinearEquiv

end AlgebraicGeometry

end
