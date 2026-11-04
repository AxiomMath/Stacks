module

public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveEquations.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveEquations.TwistMorphismForms
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularitySectionMultiplicationArbitraryField
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularityGlobalGeneration

/-!
# The equations of a closed subscheme of `ℙⁿ_k` in one degree come from the degree below

Let `φ : X ⟶ ℙⁿ_k` be a closed immersion over a field and `ℐ` its ideal sheaf. Call a form `b` of
degree `d` an *equation of `X`* when the global section of `𝒪(d)` it defines pulls back to zero
on `X`. If `ℐ` is `d`-regular, every equation of degree `d + 1` is a `k`-linear combination of
products `p b` of linear forms `p` with equations `b` of degree `d`.

This is [Stacks, Tag 08A7] read on polynomials: `H⁰(ℐ(d + 1))` is spanned by the products of
`H⁰(ℐ(d))` with the sections of `𝒪(1)`; the global sections of `ℐ(e)` are the equations of degree
`e` (`AlgebraicGeometry.exists_idealTwistIncl_app_top_eq_iff`), and multiplication by a section of
`𝒪(1)` is, on forms, multiplication by a linear form
(`AlgebraicGeometry.exists_mul_eq_app_formsLinearEquivTwistOverSections`).

## Main results

* `AlgebraicGeometry.twistSectionMul_comp_idealTwistIncl`: multiplication by a section of `𝒪(1)`
  commutes with the inclusion `ℐ(d) ⟶ 𝒪(d)`, by naturality of the monoidal constraints.
* `AlgebraicGeometry.mem_span_mul_of_isMRegular`: the statement above.

## References

* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08A3](https://stacks.math.columbia.edu/tag/08A3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication (twistSectionMul)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra


variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ projectiveSpaceOverRing n (.of k)) [IsClosedImmersion φ]

/-- The left unit constraint `𝒪 ⊗ 𝒪(d) ≅ 𝒪(d)` on `ℙⁿ_k`, at the spelling of
`Stacks.RelativeVeryAmple.tensorModules`. -/
def twistOverUnitIso (d : ℤ) :
    Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n (Spec (.of k)))
        (Stacks.AlgebraicGeometry.PicardBaseChange.unitModule (projectiveSpaceOverRing n (.of k)))
        (twistOver n (Spec (.of k)) d) ≅ twistOver n (Spec (.of k)) d :=
  Stacks.AffineClosedUnion.twistUnitIso (twistOver n (Spec (.of k)) d)

/-- **Multiplication by a global section `s` of `𝒪(1)` on the twists of the structure sheaf**,
`𝒪(d) ⟶ 𝒪(d + 1)`: the arrow `𝒪 ⊗ 𝒪(d) ⟶ 𝒪 ⊗ 𝒪(d + 1)` of
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul` conjugated by the
left unit constraints. -/
def twistOverSectionMul (s : (twistOver n (Spec (.of k)) 1).sections) (d : ℤ) :
    twistOver n (Spec (.of k)) d ⟶ twistOver n (Spec (.of k)) (d + 1) :=
  (twistOverUnitIso (k := k) d).inv ≫
    twistSectionMul n (Spec (.of k))
      (Stacks.AlgebraicGeometry.PicardBaseChange.unitModule (projectiveSpaceOverRing n (.of k)))
        s d ≫
    (twistOverUnitIso (k := k) (d + 1)).hom

section Monoidal

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily.tensorMonoidal

omit [IsClosedImmersion φ] in
/-- `AlgebraicGeometry.idealTwistIncl` in the monoidal vocabulary: the inclusion of the ideal
sheaf whiskered by `𝒪(d)`, then the left unit constraint. -/
theorem idealTwistIncl_eq_whiskerRight (d : ℤ) :
    idealTwistIncl φ d = idealIncl φ ▷ twistOver n (Spec (.of k)) d ≫ (twistOverUnitIso d).hom :=
  rfl

omit [IsClosedImmersion φ] in
/-- **Multiplication by a section of `𝒪(1)` commutes with the inclusion `ℐ(d) ⟶ 𝒪(d)`** of the
twisted ideal sheaf. -/
theorem twistSectionMul_comp_idealTwistIncl (s : (twistOver n (Spec (.of k)) 1).sections) (d : ℤ) :
    twistSectionMul n (Spec (.of k)) (kernel (closedImmersionQuotient φ)) s d ≫
        idealTwistIncl φ (d + 1) =
      idealTwistIncl φ d ≫ twistOverSectionMul s d := by
  have h : idealIncl φ ▷ twistOver n (Spec (.of k)) d ≫
        twistSectionMul n (Spec (.of k))
          (Stacks.AlgebraicGeometry.PicardBaseChange.unitModule (projectiveSpaceOverRing n (.of k)))
          s d =
      twistSectionMul n (Spec (.of k)) (kernel (closedImmersionQuotient φ)) s d ≫
        idealIncl φ ▷ twistOver n (Spec (.of k)) (d + 1) := by
    rw [Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily.twistSectionMul_eq_monoidal,
      Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily.twistSectionMul_eq_monoidal,
      rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, Category.assoc,
      Category.assoc, Category.assoc, associator_naturality_left_assoc, ← whisker_exchange]
  rw [idealTwistIncl_eq_whiskerRight, idealTwistIncl_eq_whiskerRight, twistOverSectionMul,
    Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, ← h, Category.assoc]

end Monoidal

section Linear

variable {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))

/-- **The two `k`-module structures on the global sections of a module agree**: restriction of
scalars along `k ⟶ Γ(Y, 𝒪_Y)` read through `appLE ⊤ ⊤` and through `appTop`. The identity of
`Γ(M, ⊤)` as a `k`-linear equivalence. -/
def restrictScalarsOverBaseLinearEquiv (M : Y.Modules) :
    (restrictScalarsOverBase k g).obj
        ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).obj M) ≃ₗ[k]
      (globalSectionsOver g).obj M :=
  ((ModuleCat.restrictScalarsCongr (congrArg (fun χ => CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (.of k)).inv ≫ χ)) (appLE_top_top_eq_appTop g (by simp)))).app
    ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).obj M)).toLinearEquiv

/-- `AlgebraicGeometry.restrictScalarsOverBaseLinearEquiv` is the identity on sections. -/
theorem restrictScalarsOverBaseLinearEquiv_apply (M : Y.Modules)
    (x : (restrictScalarsOverBase k g).obj
      ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).obj M)) :
    (restrictScalarsOverBaseLinearEquiv g M x : Γ(M, ⊤)) = x :=
  rfl

end Linear

/-- `AlgebraicGeometry.formsLinearEquivTwistOverSections` in degree `d + 1`, with the twist written
`(d : ℤ) + 1` as `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul`
writes it rather than `((d + 1 : ℕ) : ℤ)`. -/
abbrev formsLinearEquivTwistOverSectionsSucc (A : Type u) [CommRing A] (n d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A (d + 1) ≃ₗ[A]
      (globalSectionsOver (projectiveSpaceOverRing n (.of A) ↘ Spec (.of A))).obj
        (twistOver n (Spec (.of A)) ((d : ℤ) + 1)) :=
  formsLinearEquivTwistOverSections A n (d + 1)

/-- The `k`-linear map `H⁰(ℐ(d + 1)) ⟶ k[T]` sending a global section of the twisted ideal sheaf
to the form of degree `d + 1` it defines. -/
private def idealTwistSectionsToForms (d : ℕ) :
    cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n (kernel (closedImmersionQuotient φ)) ((d : ℤ) + 1)) 0 →ₗ[k]
      MvPolynomial (Fin (n + 1)) k :=
  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k (d + 1)).subtype ∘ₗ
    (formsLinearEquivTwistOverSectionsSucc k n d).symm.toLinearMap ∘ₗ
    (restrictScalarsOverBaseLinearEquiv (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
      (twistOver n (Spec (.of k)) ((d : ℤ) + 1))).toLinearMap ∘ₗ
    (cohomologyOverFieldZeroLinearIso k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
      (twistOver n (Spec (.of k)) ((d : ℤ) + 1))).hom.hom ∘ₗ
    (cohomologyOverFieldMap k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
      (idealTwistIncl φ ((d : ℤ) + 1)) 0).hom

/-- `AlgebraicGeometry.idealTwistSectionsToForms` computed on global sections of the twists. -/
private theorem idealTwistSectionsToForms_apply {X' : Scheme.{u}}
    (ψ : X' ⟶ projectiveSpaceOverRing n (.of k)) [IsClosedImmersion ψ] (d : ℕ)
    (x : cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
      (projectiveTwist n (kernel (closedImmersionQuotient ψ)) ((d : ℤ) + 1)) 0) :
    (idealTwistSectionsToForms ψ d x : MvPolynomial (Fin (n + 1)) k) =
      ((formsLinearEquivTwistOverSectionsSucc k n d).symm
        (restrictScalarsOverBaseLinearEquiv (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
          _ ((idealTwistIncl ψ ((d : ℤ) + 1)).app ⊤
            ((cohomologyOverFieldZeroLinearIso k
              (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) _).hom x))) :
        MvPolynomial (Fin (n + 1)) k) :=
  congrArg (fun y => ((formsLinearEquivTwistOverSectionsSucc k n d).symm
    (restrictScalarsOverBaseLinearEquiv (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) _ y) :
      MvPolynomial (Fin (n + 1)) k))
    (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k
      (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (idealTwistIncl ψ ((d : ℤ) + 1)) x)

/-- Every form of degree `d + 1` whose section pulls back to zero on `X` is the image under
`AlgebraicGeometry.idealTwistSectionsToForms` of a global section of `ℐ(d + 1)`. -/
private theorem exists_idealTwistSectionsToForms_eq (d : ℕ)
    (b : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k (d + 1))
    (hb : pullbackGlobalSections φ (twistOver n (Spec (.of k)) ((d + 1 : ℕ) : ℤ))
      (formsLinearEquivTwistOverSections k n (d + 1) b) = 0) :
    ∃ x, idealTwistSectionsToForms φ d x = b := by
  let f := projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)
  let F := kernel (closedImmersionQuotient φ)
  let Z := fun M : (projectiveSpaceOverRing n (.of k)).Modules =>
    cohomologyOverFieldZeroLinearIso k f M
  obtain ⟨a', ha'⟩ := (exists_idealTwistIncl_app_top_eq_iff φ ((d : ℤ) + 1)
    (formsLinearEquivTwistOverSections k n (d + 1) b)).mpr hb
  let x' := (Z (projectiveTwist n F ((d : ℤ) + 1))).inv a'
  refine ⟨x', ?_⟩
  show (idealTwistSectionsToForms φ d x' : MvPolynomial (Fin (n + 1)) k) = b
  rw [idealTwistSectionsToForms_apply, show (Z (projectiveTwist n F ((d : ℤ) + 1))).hom x' = a' from
    Iso.inv_hom_id_apply (Z (projectiveTwist n F ((d : ℤ) + 1))) a', ha']
  exact congrArg Subtype.val ((formsLinearEquivTwistOverSectionsSucc k n d).symm_apply_apply b)

/-- `AlgebraicGeometry.idealTwistSectionsToForms` sends the products of sections of `𝒪(1)` with
sections of `ℐ(d)` into the span of the products `p c` of linear forms `p` with equations `c` of
degree `d`. -/
private theorem map_idealTwistSectionsToForms_mulSectionsSpan_le (d : ℕ) :
    Submodule.map (idealTwistSectionsToForms φ d)
        (mulSectionsSpan k n (kernel (closedImmersionQuotient φ)) d) ≤
      Submodule.span k
        {x | ∃ (p : MvPolynomial (Fin (n + 1)) k)
          (c : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d),
          p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 1 ∧
          pullbackGlobalSections φ (twistOver n (Spec (.of k)) (d : ℤ))
            (formsLinearEquivTwistOverSections k n d c) = 0 ∧ x = p * c} := by
  let f := projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)
  let F := kernel (closedImmersionQuotient φ)
  let Z := fun M : (projectiveSpaceOverRing n (.of k)).Modules =>
    cohomologyOverFieldZeroLinearIso k f M
  rw [mulSectionsSpan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨y, ⟨s, a, rfl⟩, rfl⟩
  obtain ⟨p, hp, hmul⟩ := exists_mul_eq_app_formsLinearEquivTwistOverSections k n d
    (twistOverSectionMul s (d : ℤ))
  let t := (idealTwistIncl φ (d : ℤ)).app ⊤ ((Z (projectiveTwist n F (d : ℤ))).hom a)
  have ht : pullbackGlobalSections φ _ t = 0 :=
    (exists_idealTwistIncl_app_top_eq_iff φ (d : ℤ) t).mp ⟨_, rfl⟩
  let c := (formsLinearEquivTwistOverSections k n d).symm t
  have hc : formsLinearEquivTwistOverSections k n d c = t := LinearEquiv.apply_symm_apply _ _
  have hpc : p * (c : MvPolynomial (Fin (n + 1)) k) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k (d + 1) :=
    Nat.add_comm 1 d ▸ SetLike.mul_mem_graded hp c.2
  refine Submodule.subset_span ⟨p, c, hp, by rwa [hc], ?_⟩
  have h2 := cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f
    (twistSectionMul n (Spec (.of k)) F s d) a
  have h3 : (idealTwistIncl φ ((d : ℤ) + 1)).app ⊤
      ((twistSectionMul n (Spec (.of k)) F s d).app ⊤ ((Z _).hom a)) =
        (twistOverSectionMul s (d : ℤ)).app ⊤ t := by
    have h := congrArg (fun g => Scheme.Modules.Hom.app g ⊤ ((Z _).hom a))
      (twistSectionMul_comp_idealTwistIncl φ s d)
    simp only [Scheme.Modules.Hom.comp_app] at h
    exact h
  have h4 := hmul c hpc
  rw [hc] at h4
  show (idealTwistSectionsToForms φ d (ConcreteCategory.hom (mulSection k n F s d) a) :
    MvPolynomial (Fin (n + 1)) k) = p * c
  rw [idealTwistSectionsToForms_apply]
  show (((formsLinearEquivTwistOverSectionsSucc k n d).symm
    ((idealTwistIncl φ ((d : ℤ) + 1)).app ⊤ ((Z _).hom
      ((cohomologyOverFieldMap k f (twistSectionMul n (Spec (.of k)) F s d) 0) a)))) :
        MvPolynomial (Fin (n + 1)) k) = p * c
  rw [h2, h3, h4]
  exact congrArg Subtype.val ((formsLinearEquivTwistOverSectionsSucc k n d).symm_apply_apply
    ⟨p * c, hpc⟩)

/-- **[Stacks, Tag 08A7] on the equations of a closed subscheme of `ℙⁿ_k`.** If the ideal sheaf
`ℐ` of `φ : X ⟶ ℙⁿ_k` is `d`-regular, every form `b` of degree `d + 1` whose section pulls back to
zero on `X` is a `k`-linear combination of products `p c` of linear forms `p` with forms `c` of
degree `d` whose sections pull back to zero on `X`. -/
theorem mem_span_mul_of_isMRegular (d : ℕ)
    (hreg : IsMRegular k n (kernel (closedImmersionQuotient φ)) d)
    (b : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k (d + 1))
    (hb : pullbackGlobalSections φ (twistOver n (Spec (.of k)) ((d + 1 : ℕ) : ℤ))
      (formsLinearEquivTwistOverSections k n (d + 1) b) = 0) :
    (b : MvPolynomial (Fin (n + 1)) k) ∈ Submodule.span k
      {x | ∃ (p : MvPolynomial (Fin (n + 1)) k)
        (c : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d),
        p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 1 ∧
        pullbackGlobalSections φ (twistOver n (Spec (.of k)) (d : ℤ))
          (formsLinearEquivTwistOverSections k n d c) = 0 ∧ x = p * c} := by
  obtain ⟨x, hx⟩ := exists_idealTwistSectionsToForms_eq φ d b hb
  rw [← hx]
  exact map_idealTwistSectionsToForms_mulSectionsSpan_le φ d ⟨x,
    Submodule.eq_top_iff'.mp
      (span_mulSections_eq_top_of_isMRegular_field k n (kernel (closedImmersionQuotient φ)) d
        hreg) x, rfl⟩

end AlgebraicGeometry

end
