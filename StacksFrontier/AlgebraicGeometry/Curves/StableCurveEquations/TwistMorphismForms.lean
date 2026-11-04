module

public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveGeneratorHomGroups
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.DegreeSectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialFreeTwist
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction

/-!
# A morphism `𝒪(d) ⟶ 𝒪(d + 1)` on `ℙⁿ_A` acts on forms as multiplication by a linear form

On the base-change model `ℙⁿ_A = AlgebraicGeometry.projectiveSpaceOverRing n A` the global
sections of `𝒪(d)`, `d ≥ 0`, are the forms of degree `d` over `A`
(`AlgebraicGeometry.formsLinearEquivTwistOverSections`). Every morphism of `𝒪`-modules
`ψ : 𝒪(d) ⟶ 𝒪(d + 1)` acts on them as multiplication by one linear form `p`: transported to
`Proj A[T₀, …, Tₙ]` along the canonical comparison of the two models, `ψ` becomes a morphism of
twisting sheaves, and every such morphism is multiplication by a homogeneous polynomial
(`Stacks.AlgebraicGeometry.ProjectiveGenerator.exists_twistMul_eq`), which multiplies the section
attached to a form `b` into the section attached to `p b`.

This is the form in which the multiplication maps of [Stacks, Tag 08A7] are read on polynomials.

## Main results

* `AlgebraicGeometry.twistMul_app_top_degreeSection`: multiplication by `p` sends the section of
  `b` to the section of `p b`.
* `AlgebraicGeometry.exists_mul_eq_app_formsLinearEquivTwistOverSections`: the statement above.

## References

* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

section Proj

attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} [CommRing S] {σ : Type u} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Multiplication by a homogeneous `p` of degree `c` sends the section attached to `b` to the
section attached to `p b`.** Both are read pointwise: the section of `b` is `b / 1` at every
point, and multiplication by `p` multiplies every value by `p`. -/
theorem twistMul_app_top_degreeSection (c d e : ℕ) (p : S)
    (hp : p ∈ ProjectiveSpectrum.Proj.integerGrading 𝒮 (c : ℤ))
    (he : (c : ℤ) + (d : ℤ) = (e : ℤ)) (b : 𝒮 d) (hpb : p * (b : S) ∈ 𝒮 e) :
    (Stacks.AlgebraicGeometry.ProjectiveGenerator.twistMul 𝒮 p c d e hp he).val.app
        (op ⊤) (ProjectiveSpectrum.Proj.degreeSection 𝒮 d b) =
      ProjectiveSpectrum.Proj.degreeSection 𝒮 e ⟨p * (b : S), hpb⟩ := by
  apply Subtype.ext
  funext x
  refine (Stacks.AlgebraicGeometry.ProjectiveGenerator.twistMul_app_apply 𝒮 p c d e hp he ⊤
    (ProjectiveSpectrum.Proj.degreeSection 𝒮 d b) x).trans ?_
  rw [ProjectiveSpectrum.Proj.degreeSection_val, ProjectiveSpectrum.Proj.degreeSection_val,
    LocalizedModule.smul'_mk, smul_eq_mul]

end Proj

/-- **Transport of global sections across an isomorphism of schemes is natural.** For an
isomorphism `f : X ⟶ Y` of schemes, identifications `e₁ : f^* M ≅ M'`, `e₂ : f^* N ≅ N'` and a
morphism `ψ : M ⟶ N`, transporting `ψ(t)` is applying the transported morphism
`e₁⁻¹ ≫ f^* ψ ≫ e₂` to the transport of `t`. -/
theorem gammaTopIsoOfPullbackIso_hom_app_top {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {M N : Y.Modules} {M' N' : X.Modules} (e₁ : (Scheme.Modules.pullback f).obj M ≅ M')
    (e₂ : (Scheme.Modules.pullback f).obj N ≅ N') (ψ : M ⟶ N) (t : Γ(M, ⊤)) :
    (Scheme.Modules.gammaTopIsoOfPullbackIso f e₂).hom (ψ.app ⊤ t) =
      (e₁.inv ≫ (Scheme.Modules.pullback f).map ψ ≫ e₂.hom).app ⊤
        ((Scheme.Modules.gammaTopIsoOfPullbackIso f e₁).hom t) := by
  rw [Scheme.Modules.gammaTopIsoOfPullbackIso_hom_apply,
    Scheme.Modules.gammaTopIsoOfPullbackIso_hom_apply]
  have hnat := ConcreteCategory.congr_hom
    (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality_app f ψ) t
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
  rw [← hnat, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply, ← CategoryTheory.comp_apply (Scheme.Modules.Hom.app e₁.hom ⊤),
    ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app,
    CategoryTheory.id_apply]

/-- The canonical comparison of the two models of `ℙⁿ_A` carries the global section attached to a
form to the section of that form on `Proj A[T₀, …, Tₙ]`. -/
theorem canonicalTwistGammaTopIso_hom_formsLinearEquivTwistOverSections (A : Type u) [CommRing A]
    (n m : ℕ) (a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A m) :
    (Stacks.ProjectiveCohomology.canonicalTwistGammaTopIso A n m).hom
        (formsLinearEquivTwistOverSections A n m a) =
      ProjectiveSpectrum.Proj.degreeSection
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n) m a :=
  twistOverSectionsLinearEquiv_formsLinearEquivTwistOverSections A n m a

/-- **A morphism `𝒪(d) ⟶ 𝒪(d + 1)` on `ℙⁿ_A` is multiplication by a linear form on forms.** For
every morphism of modules `ψ : 𝒪(d) ⟶ 𝒪(d + 1)` on the base-change model of projective space
there is a linear form `p` with `ψ(b) = p b` for every form `b` of degree `d`, forms being read as
global sections by `AlgebraicGeometry.formsLinearEquivTwistOverSections`. -/
theorem exists_mul_eq_app_formsLinearEquivTwistOverSections (A : Type u) [CommRing A] (n d : ℕ)
    (ψ : twistOver n (Spec (.of A)) (d : ℤ) ⟶ twistOver n (Spec (.of A)) ((d + 1 : ℕ) : ℤ)) :
    ∃ p : MvPolynomial (Fin (n + 1)) A, p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A 1 ∧
      ∀ (b : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d)
        (hb : p * (b : MvPolynomial (Fin (n + 1)) A) ∈
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A (d + 1)),
        ψ.app ⊤ (formsLinearEquivTwistOverSections A n d b) =
          formsLinearEquivTwistOverSections A n (d + 1) ⟨p * b, hb⟩ := by
  let c := Stacks.ProjectiveCohomology.projModelIso A n
  let κ := fun m : ℤ =>
    Stacks.ProjectiveCohomology.canonicalPullbackProjModelIsoHomTwistOverIso A n m
  let Θ := fun m : ℤ => Stacks.ProjectiveCohomology.canonicalTwistGammaTopIso A n m
  let ψ' := (κ (d : ℤ)).inv ≫ (Scheme.Modules.pullback c.hom).map ψ ≫ (κ ((d + 1 : ℕ) : ℤ)).hom
  obtain ⟨p, hp, hpψ⟩ := Stacks.AlgebraicGeometry.ProjectiveGenerator.exists_twistMul_eq A n
    (c := 1) (d := d) (e := ((d + 1 : ℕ) : ℤ)) (by push_cast; ring) (Or.inl zero_le_one) ψ'
  have hp1 : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A 1 := by
    rwa [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, ProjectiveSpectrum.Proj.integerGrading_natCast,
      ProjectiveSpectrum.Proj.mem_homogeneousSubmodule] at hp
  have key : ∀ t : Γ(twistOver n (Spec (.of A)) (d : ℤ), ⊤),
      (Θ ((d + 1 : ℕ) : ℤ)).hom (ψ.app ⊤ t) = ψ'.app ⊤ ((Θ (d : ℤ)).hom t) :=
    gammaTopIsoOfPullbackIso_hom_app_top c.hom (κ (d : ℤ)) (κ ((d + 1 : ℕ) : ℤ)) ψ
  refine ⟨p, hp1, fun b hb => ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (Θ ((d + 1 : ℕ) : ℤ)).hom).1
  refine (key _).trans ?_
  rw [canonicalTwistGammaTopIso_hom_formsLinearEquivTwistOverSections A n d b,
    canonicalTwistGammaTopIso_hom_formsLinearEquivTwistOverSections A n (d + 1) ⟨p * b, hb⟩,
    ← hpψ]
  exact twistMul_app_top_degreeSection (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n)
    1 d (d + 1) p hp (by push_cast; ring) b hb

end AlgebraicGeometry

end
