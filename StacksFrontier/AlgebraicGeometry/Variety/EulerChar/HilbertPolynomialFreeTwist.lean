module

public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenus
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDuality
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsLinear
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheafAffine
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialHighTwist
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.FreeSheafTwistAcyclic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.KernelRegularityBound
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The global sections of `𝒪(m)` on `ℙⁿ_A` are the degree-`m` forms, and `χ(𝒪(m)^{⊕ r})`

Let `A` be a commutative ring and `m ≥ 0`. On the base-change model
`AlgebraicGeometry.projectiveSpaceOverRing n A` of projective space, the `A`-module of global
sections of `𝒪(m)` is the module of homogeneous polynomials of degree `m` in `T₀, …, Tₙ` over `A`.
Over a field `k` this gives

`χ(ℙⁿ_k, 𝒪(m)^{⊕ r}) = r · (m + n choose n)` for `m ≥ 0`,

uniformly in `k`.

## Main definitions

* `AlgebraicGeometry.twistOverSectionsLinearEquiv`: the canonical identification of the global
  sections of `𝒪(d)` on the two models of `ℙⁿ_A`, as an isomorphism of `A`-modules.
* `AlgebraicGeometry.formsLinearEquivTwistOverSections`: the degree-`m` forms over `A` are
  `Γ(ℙⁿ_A, 𝒪(m))` as `A`-modules, on the base-change model.
* `AlgebraicGeometry.unitHomLinearEquivForms`: over a field `k`, `Hom(𝒪, 𝒪(m))` on `ℙⁿ_k` is the
  space of degree-`m` forms.

## Main results

* `AlgebraicGeometry.finrank_obj_of_isColimit_of_additive`: an additive functor to vector spaces
  carries a finite direct sum to the direct sum of the values.
* `AlgebraicGeometry.finrank_globalSectionsOver_twistOver`:
  `dim_k Γ(ℙⁿ_k, 𝒪(m)) = (m + n choose n)`.
* `AlgebraicGeometry.hilbertPolynomial_freeModules`: `χ(ℙⁿ_k, 𝒪(m)^{⊕ r}) = r · (m + n choose n)`
  for `m ≥ 0`.

## Implementation notes

The identification of the models is `Stacks.ProjectiveCohomology.canonicalTwistGammaTopIso`,
which is semilinear over the map the comparison of models induces on global functions
(`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.canonicalTwistGammaTopIso_hom_smul`).
That map carries the image of a coefficient under the structure morphism of the base-change model
to `Stacks.ProjectiveSpace.Cohomology.coeffScalar`, the scalar action of the `Proj` model's module
of sections, so the identification is `A`-linear for the two structures through the bases. On the
`Proj` side, the degree-`m` forms are the global sections of `𝒪(m)` by
`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSectionLinear`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample (unitModule)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The global sections of `𝒪(m)` on the base-change model -/

section Forms

variable (A : Type u) [CommRing A] (n : ℕ)

/-- **The canonical identification of the global sections of `𝒪(d)` on the two models of
`ℙⁿ_A` is `A`-linear.** The source carries the `A`-module structure through the structure
morphism of the base-change model, the target through the structure morphism of
`Proj A[T₀, …, Tₙ]`. -/
def twistOverSectionsLinearMap (d : ℤ) :
    (globalSectionsOver (projectiveSpaceOverRing n (.of A) ↘ Spec (.of A))).obj
        (twistOver n (Spec (.of A)) d) →ₗ[A]
      Stacks.ProjectiveSpace.Cohomology.twistSectionsModule A n d where
  toFun x := (Stacks.ProjectiveCohomology.canonicalTwistGammaTopIso A n d).hom x
  map_add' x y := map_add _ x y
  map_smul' a x := by
    refine (canonicalTwistGammaTopIso_hom_smul A n d
      ((projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) x).trans ?_
    rw [projModelIso_hom_appTop_structureMorphism_appTop, projModelToSpec_appTop_ΓSpecIso_inv]
    rfl

/-- **The global sections of `𝒪(d)` on the two models of `ℙⁿ_A` agree as `A`-modules**, by the
canonical identification `Stacks.ProjectiveCohomology.canonicalTwistGammaTopIso`. -/
def twistOverSectionsLinearEquiv (d : ℤ) :
    (globalSectionsOver (projectiveSpaceOverRing n (.of A) ↘ Spec (.of A))).obj
        (twistOver n (Spec (.of A)) d) ≃ₗ[A]
      Stacks.ProjectiveSpace.Cohomology.twistSectionsModule A n d :=
  LinearEquiv.ofBijective (twistOverSectionsLinearMap A n d)
    (ConcreteCategory.bijective_of_isIso
      (Stacks.ProjectiveCohomology.canonicalTwistGammaTopIso A n d).hom)

/-- **The degree-`m` forms over `A` are `Γ(ℙⁿ_A, 𝒪(m))`**, as `A`-modules and on the base-change
model `AlgebraicGeometry.projectiveSpaceOverRing`: a form goes to the global section of `𝒪(m)`
it defines on `Proj A[T₀, …, Tₙ]`, read on the base-change model. -/
@[ega "III 2.1.12" "Clause (ii)"]
def formsLinearEquivTwistOverSections (m : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A m ≃ₗ[A]
      (globalSectionsOver (projectiveSpaceOverRing n (.of A) ↘ Spec (.of A))).obj
        (twistOver n (Spec (.of A)) m) :=
  (LinearEquiv.ofBijective (Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear A n m)
    (Stacks.ProjectiveSpace.Cohomology.bijective_degreeSectionLinear n m)).trans
    (twistOverSectionsLinearEquiv A n m).symm

/-- The global section attached to a form is read on the `Proj` model as the section of that
form. -/
theorem twistOverSectionsLinearEquiv_formsLinearEquivTwistOverSections (m : ℕ)
    (a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A m) :
    twistOverSectionsLinearEquiv A n m (formsLinearEquivTwistOverSections A n m a) =
      ProjectiveSpectrum.Proj.degreeSection
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n) m a :=
  (twistOverSectionsLinearEquiv A n m).apply_symm_apply _

end Forms

/-! ### Dimensions over a field -/

/-- **An additive functor to vector spaces carries a finite direct sum to the direct sum of its
values**, read on dimensions, with the direct sum presented by a colimit cocone over a discrete
diagram. -/
theorem finrank_obj_of_isColimit_of_additive {C : Type*} [Category C] [Preadditive C]
    {K : Type u} [Field K] (F : C ⥤ ModuleCat.{u} K) [F.Additive] {ι : Type} [Fintype ι]
    {f : ι → C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t)
    [∀ i, Module.Finite K (F.obj (f i))] :
    Module.finrank K (F.obj t.pt) = ∑ i, Module.finrank K (F.obj (f i)) := by
  let hb := isBilimitOfPreserves F (biconeIsBilimitOfColimitCoconeOfIsColimit ht)
  let e : F.obj t.pt ≅ ModuleCat.of K (∀ i, F.obj (f i)) :=
    biproduct.uniqueUpToIso _ hb ≪≫ ModuleCat.biproductIsoPi _
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

variable (k : Type u) [Field k] (n : ℕ)

/-- **`dim_k Γ(ℙⁿ_k, 𝒪(m)) = (m + n choose n)`** for `m ≥ 0`, on the base-change model: the
degree-`m` forms in `n + 1` variables are free on the degree-`m` monomials. -/
theorem finrank_globalSectionsOver_twistOver (m : ℕ) :
    Module.finrank k ((globalSectionsOver (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))).obj
      (twistOver n (Spec (.of k)) m)) = (m + n).choose n := by
  rw [← (formsLinearEquivTwistOverSections k n m).finrank_eq,
    MvPolynomial.finrank_homogeneousSubmodule, Fintype.card_fin,
    show n + 1 + m - 1 = m + n by omega, Nat.choose_symm_add]

/-- **`Hom(𝒪, 𝒪(m))` on `ℙⁿ_k` is the space of degree-`m` forms** over `k`, as `k`-vector spaces,
on the base-change model: a morphism is its value on the section `1`, a global section of `𝒪(m)`,
and that is the section of a unique form. -/
def unitHomLinearEquivForms (m : ℕ) :
    letI := Scheme.linearOver (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
    (unitModule (projectiveSpaceOverRing n (.of k)) ⟶
        projectiveTwist n (unitModule (projectiveSpaceOverRing n (.of k))) m) ≃ₗ[k]
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k m :=
  letI := Scheme.linearOver (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
  haveI := globalSectionsOver_linearOver (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
  (unitHomLinearEquivGlobalSections (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) _).trans
    ((((globalSectionsOver (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))).mapIso
      (projectiveTwistUnitIso k n m)).toLinearEquiv).trans
      (formsLinearEquivTwistOverSections k n m).symm)

/-- **`χ(ℙⁿ_k, 𝒪(m)^{⊕ r}) = r · (m + n choose n)`** for `m ≥ 0`, uniformly in the field `k`:
the twists of a free module have no higher cohomology, and its global sections are `r` copies of
the degree-`m` forms. -/
theorem hilbertPolynomial_freeModules (r m : ℕ) :
    hilbertPolynomial k n (freeModules k n r) m = r * (m + n).choose n := by
  let f := projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)
  rw [hilbertPolynomial_eq_finrank_cohomologyOverField_zero k n _ _ fun i hi =>
    (isZero_cohomologyOverField_iff_isZero_hgroup k f _ i).2
      (isZero_Hgroup_projectiveTwist_freeModules k n r m (Int.natCast_nonneg m) i hi)]
  let := Scheme.linearOver f
  have := globalSectionsOver_linearOver f
  rw [(cohomologyOverFieldZeroLinearEquivGlobalSectionsOver f _).finrank_eq]
  have h1 : Module.finrank k ((twistFunctorModules k n m ⋙ globalSectionsOver f).obj
      (unitModule (projectiveSpaceOverRing n (.of k)))) = (m + n).choose n :=
    (((globalSectionsOver f).mapIso (projectiveTwistUnitIso k n m)).toLinearEquiv.finrank_eq).trans
      (finrank_globalSectionsOver_twistOver k n m)
  have : Module.Finite k ((twistFunctorModules k n m ⋙ globalSectionsOver f).obj
      (unitModule (projectiveSpaceOverRing n (.of k)))) :=
    Module.finite_of_finrank_pos (h1 ▸ Nat.choose_pos (Nat.le_add_left n m))
  have h := finrank_obj_of_isColimit_of_additive
    (twistFunctorModules k n m ⋙ globalSectionsOver f)
    (colimit.isColimit (Discrete.functor
      fun _ : Fin r => unitModule (projectiveSpaceOverRing n (.of k))))
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  exact_mod_cast h

end AlgebraicGeometry
