module

public import StacksFrontier.AlgebraicGeometry.CodimOneSubscheme.ProjHeightOne
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.StrHomGradeZero
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GradedRationalPoint

/-!
# The hyperplane of a rational point of the `Proj` of a graded algebra over a field

Let `k` be an infinite field and `A` a sheaf-level graded algebra on `Spec k` whose structure map
is a bijection onto the degree-zero part and whose graded ring of global sections is generated in
degree one. Given a section of the structure morphism of `Proj Γ(Spec k, A)` with image a point
`q`, there is a degree-one homogeneous global section vanishing at `q` and at none of finitely many
other given points.

## Main definitions

* `Stacks.GradedRationalPoint.degreeOneSMul`: the action of `k` on the degree-one part of an
  `ℕ`-graded ring through a ring homomorphism `γ : k →+* 𝒜 0`.
* `Stacks.GradedRationalPoint.degreeOneModule`: the `k`-module structure on the degree-one part
  determined by `γ`.
* `Stacks.SheafGradedRationalPoint.gamma`: the ring homomorphism `k →+* 𝒜 0` given by the
  structure map of the graded algebra and `AlgebraicGeometry.Scheme.ΓSpecIso`.

## Main results

* `Stacks.SheafGradedRationalPoint.isUnit_of_ne_zero`: a nonzero global function on `Spec k` is a
  unit.
* `Stacks.SheafGradedRationalPoint.toSpecBase_gamma_eq`: the morphism to `Spec k` built from
  `gamma` is the structure morphism of the absolute `Proj` of the graded ring of global sections.
* `Stacks.SheafGradedRationalPoint.exists_mem_degreeOne_forall_notMem`: a degree-one homogeneous
  global section vanishing at a rational point of `Proj Γ(Spec k, A)` and at none of finitely many
  other points.

## References

* [Stacks Project, Tag 0B58](https://stacks.math.columbia.edu/tag/0B58)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u w

namespace Stacks.GradedRationalPoint

/-! ### The degree-one part as a vector space over a base field -/

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {k : Type u} [Field k] (γ : k →+* ↥(𝒜 0))

/-- The action of the base field on the degree-one part through a ring homomorphism to the
degree-zero part: multiplication inside the graded ring. -/
@[instance_reducible]
def degreeOneSMul : SMul k ↥(𝒜 1) :=
  ⟨fun c v => ⟨(γ c : A) * (v : A), by
    have h := SetLike.mul_mem_graded (γ c).2 v.2
    rwa [zero_add] at h⟩⟩

/-- The `k`-module structure on the degree-one part determined by a ring homomorphism
`γ : k →+* 𝒜 0`. -/
@[instance_reducible]
def degreeOneModule : Module k ↥(𝒜 1) :=
  letI : SMul k ↥(𝒜 1) := degreeOneSMul 𝒜 γ
  { one_smul := fun v => Subtype.ext (by
      change (γ 1 : A) * (v : A) = (v : A)
      rw [map_one]
      exact one_mul _)
    mul_smul := fun c c' v => Subtype.ext (by
      change (γ (c * c') : A) * (v : A) = (γ c : A) * ((γ c' : A) * (v : A))
      rw [map_mul]
      exact mul_assoc _ _ _)
    smul_zero := fun c => Subtype.ext (by
      change (γ c : A) * (0 : A) = (0 : A)
      exact mul_zero _)
    smul_add := fun c v w => Subtype.ext (by
      change (γ c : A) * ((v : A) + (w : A)) =
        (γ c : A) * (v : A) + (γ c : A) * (w : A)
      exact mul_add _ _ _)
    add_smul := fun c c' v => Subtype.ext (by
      change (γ (c + c') : A) * (v : A) = (γ c : A) * (v : A) + (γ c' : A) * (v : A)
      rw [map_add]
      exact add_mul _ _ _)
    zero_smul := fun v => Subtype.ext (by
      change (γ 0 : A) * (v : A) = (0 : A)
      rw [map_zero]
      exact zero_mul _) }

/-- The action of `degreeOneModule` is multiplication by `γ`. -/
theorem coe_degreeOneModule_smul (c : k) (v : ↥(𝒜 1)) :
    ((@HSMul.hSMul k ↥(𝒜 1) ↥(𝒜 1)
        (@instHSMul k ↥(𝒜 1) (degreeOneModule 𝒜 γ).toSMul) c v : ↥(𝒜 1)) : A) =
      (γ c : A) * (v : A) := rfl

end Stacks.GradedRationalPoint

namespace Stacks.SheafGradedRationalPoint

variable {k : Type u} [Field k] (A : SheafGradedAlgebra (Spec (CommRingCat.of k)))

/-! ### Global functions on `Spec k` -/

/-- A nonzero global function on `Spec k` is a unit. -/
theorem isUnit_of_ne_zero (r : Γ(Spec (CommRingCat.of k), ⊤)) (hr : r ≠ 0) : IsUnit r := by
  have hinv : ∀ s : Γ(Spec (CommRingCat.of k), ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom s) = s :=
    fun s => congrArg (fun g : Γ(Spec (CommRingCat.of k), ⊤) ⟶ Γ(Spec (CommRingCat.of k), ⊤) =>
      g.hom s) (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
  have hne : (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom r ≠ 0 := by
    intro hc
    refine hr ?_
    rw [← hinv r, hc, map_zero]
  rw [← hinv r]
  exact ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).isUnit_map (isUnit_iff_ne_zero.mpr hne)

/-! ### The base field inside the degree-zero part -/

/-- The base field inside the degree-zero part of the graded ring of global sections: the
structure map of the graded algebra, read on global functions through
`AlgebraicGeometry.Scheme.ΓSpecIso` and projected to degree zero. -/
def gamma : k →+* ↥(A.grading (⊤ : (Spec (CommRingCat.of k)).Opens) 0) :=
  ((GradedRing.projZeroRingHom' (A.grading (⊤ : (Spec (CommRingCat.of k)).Opens))).comp
      (A.strHom (⊤ : (Spec (CommRingCat.of k)).Opens))).comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-! ### The structure morphism of the absolute `Proj` -/

/-- The morphism to `Spec k` built from `gamma` is the structure morphism of the absolute `Proj`
of the graded ring of global sections. -/
theorem toSpecBase_gamma_eq (hS : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens)) :
    Stacks.GradedRationalPoint.toSpecBase
        (A.grading (⊤ : (Spec (CommRingCat.of k)).Opens)) (gamma A) =
      projInclusionToOpen A (⊤ : (Spec (CommRingCat.of k)).Opens) hS ≫
        (⊤ : (Spec (CommRingCat.of k)).Opens).ι := by
  have hdef : projInclusionToOpen A (⊤ : (Spec (CommRingCat.of k)).Opens) hS =
      AlgebraicGeometry.Proj.toSpecZero
          (A.grading (⊤ : (Spec (CommRingCat.of k)).Opens)) ≫
        Spec.map (CommRingCat.ofHom
          ((GradedRing.projZeroRingHom' (A.grading (⊤ : (Spec (CommRingCat.of k)).Opens))).comp
            (A.strHom (⊤ : (Spec (CommRingCat.of k)).Opens)))) ≫ hS.isoSpec.inv := rfl
  have hfrom : hS.isoSpec.inv ≫ (⊤ : (Spec (CommRingCat.of k)).Opens).ι =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hcomp : ∀ ψ : Γ(Spec (CommRingCat.of k), ⊤) ⟶
      CommRingCat.of ↥(A.grading (⊤ : (Spec (CommRingCat.of k)).Opens) 0),
      Spec.map ψ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv =
        Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ψ) :=
    fun ψ => (Spec.map_comp _ _).symm
  rw [hdef, Category.assoc, Category.assoc, hfrom, hcomp,
    Stacks.GradedRationalPoint.toSpecBase]
  rfl

/-! ### The degree-one equation of a rational point -/

/-- Over an infinite field `k`, there is a degree-one homogeneous global section vanishing at a
rational point `q` of `Proj Γ(Spec k, A)` and at none of finitely many other points `qs j`.

The hypotheses are: `hbij`, that multiplying the algebra unit by a function on `Spec k` is a
bijection onto the degree-zero local sections; `hgen`, that the graded ring of global sections is
generated in degree one over its degree-zero part; and a section `τ` of the structure morphism of
the absolute `Proj` whose image is `q`. -/
theorem exists_mem_degreeOne_forall_notMem [Infinite k]
    (hS : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens))
    (hbij : Function.Bijective
      (fun r : Γ(Spec (CommRingCat.of k), ⊤) =>
        r • A.one (⊤ : (Spec (CommRingCat.of k)).Opens)))
    (hgen : Algebra.adjoin ↥(A.grading (⊤ : (Spec (CommRingCat.of k)).Opens) 0)
      ((A.grading (⊤ : (Spec (CommRingCat.of k)).Opens) 1 :
        Set (A.sectionRing (⊤ : (Spec (CommRingCat.of k)).Opens)))) = ⊤)
    (q : AlgebraicGeometry.Proj (A.grading (⊤ : (Spec (CommRingCat.of k)).Opens)))
    (τ : Spec (CommRingCat.of k) ⟶
      AlgebraicGeometry.Proj (A.grading (⊤ : (Spec (CommRingCat.of k)).Opens)))
    (hsec : τ ≫ projInclusionToOpen A (⊤ : (Spec (CommRingCat.of k)).Opens) hS ≫
      (⊤ : (Spec (CommRingCat.of k)).Opens).ι = 𝟙 _)
    (hpt : ∀ a, τ.base a = q)
    {ι : Type w} [Finite ι]
    (qs : ι → AlgebraicGeometry.Proj (A.grading (⊤ : (Spec (CommRingCat.of k)).Opens)))
    (hne : ∀ j, q ≠ qs j) :
    ∃ v ∈ A.grading (⊤ : (Spec (CommRingCat.of k)).Opens) 1,
      v ∈ q.asHomogeneousIdeal ∧ ∀ j, v ∉ (qs j).asHomogeneousIdeal := by
  let := Stacks.GradedRationalPoint.degreeOneModule
    (A.grading (⊤ : (Spec (CommRingCat.of k)).Opens)) (gamma A)
  obtain ⟨v, hvq, hvqs⟩ := Stacks.GradedRationalPoint.exists_mem_degreeOne_forall_notMem
    (gamma A)
    (Stacks.GradedRationalPoint.coe_degreeOneModule_smul
      (A.grading (⊤ : (Spec (CommRingCat.of k)).Opens)) (gamma A))
    hgen
    (SheafGradedAlgebra.isUnit_coe_of_ne_zero A (⊤ : (Spec (CommRingCat.of k)).Opens) hbij
      isUnit_of_ne_zero)
    (fun x => AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_mem_degreeOne_notMem
      (A.grading (⊤ : (Spec (CommRingCat.of k)).Opens)) hgen x.not_irrelevant_le)
    q τ (by rw [toSpecBase_gamma_eq A hS]; exact hsec) hpt qs hne
  exact ⟨v, v.2, hvq, hvqs⟩

end Stacks.SheafGradedRationalPoint

end
