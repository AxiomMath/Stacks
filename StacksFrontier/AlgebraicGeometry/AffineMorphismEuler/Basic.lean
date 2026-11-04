module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksCore.Tactic.StacksAttribute

/-!
# The Euler characteristic along an affine morphism

Let `k` be a field, `f : X ⟶ Spec k`, `g : Z ⟶ X` an affine morphism and `𝒢` a quasi-coherent
`𝒪_Z`-module. The comparison `Hⁿ(Z, 𝒢) ≅ Hⁿ(X, g_*𝒢)` of
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward` is an isomorphism of `k`-vector
spaces, so the two cohomology groups have the same dimension and, for `f` and `g ≫ f` proper and
`𝒢`, `g_*𝒢` coherent, `χ(X, g_*𝒢) = χ(Z, 𝒢)`.

## Main results

* `AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsAffineHom`: the `k`-linear isomorphism
  `Hⁿ(Z, 𝒢) ≅ Hⁿ(X, g_*𝒢)` for `g` affine and `𝒢` quasi-coherent.
* `AlgebraicGeometry.finrank_cohomologyOverField_pushforward_of_isAffineHom`: the two have the
  same dimension.
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_pushforward_of_isAffineHom`: finite
  dimensionality transports across it.
* `AlgebraicGeometry.eulerCharacteristic_pushforward_of_isAffineHom`: `χ(X, g_*𝒢) = χ(Z, 𝒢)`.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] {Z X : Scheme.{u}} (g : Z ⟶ X)

/-- For an affine morphism `g : Z ⟶ X` over a field `k` and a quasi-coherent module `𝒢` on `Z`,
the isomorphism `Hⁿ(Z, 𝒢) ≅ Hⁿ(X, g_*𝒢)` of `k`-vector spaces. -/
noncomputable def cohomologyOverFieldPushforwardIsoOfIsAffineHom
    [IsAffineHom g] (f : X ⟶ Spec (.of k)) (G : Z.Modules) [G.IsQuasicoherent] (n : ℕ) :
    cohomologyOverField k (g ≫ f) G n ≅
      cohomologyOverField k f ((Scheme.Modules.pushforward g).obj G) n :=
  ModuleCat.restrictScalarsComp'App
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
      (g.app (⊤ : X.Opens)).hom
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ f).appLE ⊤ ⊤ (by simp)).hom
      (by
        rw [← CommRingCat.hom_comp]
        refine congrArg CommRingCat.Hom.hom ?_
        rw [Category.assoc, Scheme.Hom.appLE_comp_top g f (by simp) (by simp)]
        rfl) _ ≪≫
    (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).mapIso
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward g G n)

/-- For an affine morphism `g : Z ⟶ X` over a field `k` and a quasi-coherent module `𝒢` on `Z`,
`Hⁿ(Z, 𝒢)` and `Hⁿ(X, g_*𝒢)` have the same dimension over `k`. -/
theorem finrank_cohomologyOverField_pushforward_of_isAffineHom [IsAffineHom g]
    (f : X ⟶ Spec (.of k)) (G : Z.Modules) [G.IsQuasicoherent] (n : ℕ) :
    Module.finrank k (cohomologyOverField k (g ≫ f) G n) =
      Module.finrank k
        (cohomologyOverField k f ((Scheme.Modules.pushforward g).obj G) n) :=
  (cohomologyOverFieldPushforwardIsoOfIsAffineHom k g f G n).toLinearEquiv.finrank_eq

/-- For an affine morphism `g : Z ⟶ X` over a field `k` and a quasi-coherent module `𝒢` on `Z`,
if `Hⁿ(Z, 𝒢)` is finite-dimensional over `k` then so is `Hⁿ(X, g_*𝒢)`. -/
theorem finiteDimensional_cohomologyOverField_pushforward_of_isAffineHom [IsAffineHom g]
    (f : X ⟶ Spec (.of k)) (G : Z.Modules) [G.IsQuasicoherent] (n : ℕ)
    (h : FiniteDimensional k (cohomologyOverField k (g ≫ f) G n)) :
    FiniteDimensional k (cohomologyOverField k f ((Scheme.Modules.pushforward g).obj G) n) :=
  Module.Finite.equiv
    (cohomologyOverFieldPushforwardIsoOfIsAffineHom k g f G n).toLinearEquiv

/-- The Euler characteristic is unchanged by pushing a coherent module forward along an affine
morphism: `χ(X, g_*𝒢) = χ(Z, 𝒢)`. -/
theorem eulerCharacteristic_pushforward_of_isAffineHom [IsAffineHom g] (f : X ⟶ Spec (.of k))
    [IsProper f] [IsProper (g ≫ f)] (G : Z.Modules) [G.IsQuasicoherent]
    (hG : SheafOfModules.IsCoherent G)
    (hpush : SheafOfModules.IsCoherent ((Scheme.Modules.pushforward g).obj G)) :
    @eulerCharacteristic k _ X f _ ((Scheme.Modules.pushforward g).obj G) hpush =
      @eulerCharacteristic k _ Z (g ≫ f) _ G hG := by
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  exact finsum_congr fun n => by
    rw [finrank_cohomologyOverField_pushforward_of_isAffineHom k g f G n]

end AlgebraicGeometry

end
