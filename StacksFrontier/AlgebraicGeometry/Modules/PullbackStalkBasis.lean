module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# A basis of a stalk of a pullback

Let `p : Y ⟶ X` be a morphism of schemes, `ℒ` a quasi-coherent `𝒪_X`-module, `V` an affine open
of `X` and `(bᵢ)` a basis of the `Γ(X, V)`-module `Γ(ℒ, V)`. At a point `x ∈ V` the germs of the
`bᵢ` form a basis of the `𝒪_{X, x}`-module `ℒ_x`, and at a point `y` with `p(y) ∈ V` the germs of
the pullbacks `p^*bᵢ` form a basis of the `𝒪_{Y, y}`-module `(p^*ℒ)_y`.

## Main definitions

* `Stacks.ModuleStalkSpecialization.stalkBasisOfAffine`: the basis of `ℒ_x` given by the germs of
  a basis of `Γ(ℒ, V)`.
* `Stacks.ModuleStalkSpecialization.pullbackStalkBasis`: the basis of `(p^*ℒ)_y` given by the
  germs of the pullbacks of a basis of `Γ(ℒ, V)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.ModuleStalkSpecialization

variable {X : Scheme.{u}} (L : X.Modules) [L.IsQuasicoherent] {V : X.Opens}
  (hV : IsAffineOpen V) {ι : Type*} (b : Module.Basis ι Γ(X, V) Γ(L, V))

/-- **The germs of a basis of the sections over an affine open form a basis of the stalk.** -/
def stalkBasisOfAffine {x : X} (hx : x ∈ V) :
    letI := stalkModule L x
    Module.Basis ι (X.presheaf.stalk x) (L.presheaf.stalk x) :=
  letI := stalkModule L x
  letI := sectionsStalkModule L hx
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  haveI := isScalarTower_sectionsStalk L hx
  haveI := isLocalizedModule_germₗ L hV hx
  b.ofIsLocalizedModule (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (germₗ L hx)

/-- The `i`-th vector of the stalk basis is the germ at `x` of the `i`-th vector of the given
basis of `Γ(ℒ, V)`. -/
theorem stalkBasisOfAffine_apply {x : X} (hx : x ∈ V) (i : ι) :
    stalkBasisOfAffine L hV b hx i = L.presheaf.germ V x hx (b i) := by
  let := stalkModule L x
  let := sectionsStalkModule L hx
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have := isScalarTower_sectionsStalk L hx
  have := isLocalizedModule_germₗ L hV hx
  exact b.ofIsLocalizedModule_apply (X.presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (germₗ L hx) i

variable {Y : Scheme.{u}} (p : Y ⟶ X)

/-- **The germs of the pullbacks of a basis of the sections over an affine open form a basis of
the stalk of the pullback.** -/
def pullbackStalkBasis {y : Y} (hy : p.base y ∈ V) :
    letI := stalkModule ((Scheme.Modules.pullback p).obj L) y
    Module.Basis ι (Y.presheaf.stalk y) (((Scheme.Modules.pullback p).obj L).presheaf.stalk y) :=
  letI := stalkModule L (p.base y)
  letI : Algebra (X.presheaf.stalk (p.base y)) (Y.presheaf.stalk y) :=
    (p.stalkMap y).hom.toAlgebra
  (Algebra.TensorProduct.basis (Y.presheaf.stalk y) (stalkBasisOfAffine L hV b hy)).map
    (Divisors.pullbackStalkBaseChange p L y).symm

/-- The `i`-th vector of the stalk basis of the pullback is the germ at `y` of the pullback of the
`i`-th vector of the given basis of `Γ(ℒ, V)`. -/
theorem pullbackStalkBasis_apply {y : Y} (hy : p.base y ∈ V) (i : ι) :
    pullbackStalkBasis L hV b p hy i =
      ((Scheme.Modules.pullback p).obj L).presheaf.germ (p ⁻¹ᵁ V) y hy
        (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections p L V (b i)) := by
  let := stalkModule L (p.base y)
  let : Algebra (X.presheaf.stalk (p.base y)) (Y.presheaf.stalk y) :=
    (p.stalkMap y).hom.toAlgebra
  change (Divisors.pullbackStalkBaseChange p L y).symm
    (Algebra.TensorProduct.basis (Y.presheaf.stalk y) (stalkBasisOfAffine L hV b hy) i) = _
  rw [Algebra.TensorProduct.basis_apply, stalkBasisOfAffine_apply, LinearEquiv.symm_apply_eq]
  exact (Divisors.pullbackStalkBaseChange_germ p L y V hy (b i)).symm

end Stacks.ModuleStalkSpecialization
