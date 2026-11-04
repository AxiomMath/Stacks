module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateConeFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.OrderedCechVanishing

/-!
# The standard cover of the projective bundle of the coordinate situation

In the standard situation of Section 50.16 of the source the projective bundle
`P = Proj(R[x₁, …, x_m, y₁, …, y_n])`, graded by `deg yⱼ = 1`, is covered by the standard opens
`D₊(yⱼ)`, and every finite intersection of them is the standard open of a product of the `yⱼ`,
hence affine. So [Stacks, Tag 01XD] computes the cohomology of a quasi-coherent module on `P` by
the ordered Čech complex of this cover.

## Main definitions

* `Stacks.DeRham.CoordinateCone.bundleCover`: the cover `j ↦ D₊(yⱼ)` of `P`, indexed by
  `ULift (Fin n)` so that it lives in the universe of the scheme.

## Main results

* `Stacks.DeRham.CoordinateCone.iSup_bundleCover`: the `D₊(yⱼ)` cover `P`.
* `Stacks.DeRham.CoordinateCone.iInf_bundleCover`: a finite intersection of them is `D₊` of the
  product.
* `Stacks.DeRham.CoordinateCone.isZero_rightDerived_bundle_of_exact`: the cohomology of a
  quasi-coherent module on `P` vanishes in degree `q + 1` as soon as every ordered Čech cocycle of
  degree `q + 1` of this cover is a coboundary.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace Stacks.DeRham.CoordinateCone

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- **The standard cover `j ↦ D₊(yⱼ)` of the projective bundle `P`.** -/
abbrev bundleCover (j : ULift.{u} (Fin n)) : (coneBundle R m n).Opens :=
  Proj.basicOpen (yGrading R m n) (X (Sum.inr j.down))

/-- **The `D₊(yⱼ)` cover `P`**: the `yⱼ`, together with the degree-zero part, generate `A`. -/
theorem iSup_bundleCover : (⊤ : (coneBundle R m n).Opens) = ⨆ j, bundleCover R m n j := by
  refine (Proj.iSup_basicOpen_eq_top' (yGrading R m n)
    (fun j : ULift.{u} (Fin n) => (X (Sum.inr j.down) : MvPolynomial (Fin m ⊕ Fin n) R))
    (fun j => ⟨1, X_inr_mem_yGrading R m n j.down⟩) ?_).symm
  refine eq_top_iff.2 fun a ha => ?_
  clear ha
  induction a using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _ (⟨C r, isWeightedHomogeneous_C _ r⟩ : yGrading R m n 0)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p v hp =>
    refine mul_mem hp ?_
    rcases v with i | j
    · exact Subalgebra.algebraMap_mem _ (⟨X (Sum.inl i), by
        simpa using isWeightedHomogeneous_X R (yWeight m n) (Sum.inl i)⟩ : yGrading R m n 0)
    · exact Algebra.subset_adjoin ⟨ULift.up j, rfl⟩

/-- A finite intersection of the `D₊(yⱼ)` is `D₊` of the product of the `yⱼ`. -/
theorem iInf_bundleCover {r : ℕ} (s : Fin (r + 1) → ULift.{u} (Fin n)) :
    (⨅ k, bundleCover R m n (s k)) =
      Proj.basicOpen (yGrading R m n) (∏ k, (X (Sum.inr (s k).down) :
        MvPolynomial (Fin m ⊕ Fin n) R)) :=
  Stacks.ProjectiveCohomology.iInf_basicOpen_eq_basicOpen_prod (yGrading R m n) _

/-- A product of `r + 1` of the `yⱼ` is homogeneous of degree `r + 1`. -/
theorem prod_mem_yGrading {r : ℕ} (s : Fin (r + 1) → ULift.{u} (Fin n)) :
    (∏ k, (X (Sum.inr (s k).down) : MvPolynomial (Fin m ⊕ Fin n) R)) ∈ yGrading R m n (r + 1) := by
  simpa using SetLike.prod_mem_graded (A := yGrading R m n) (i := fun _ => 1)
    (g := fun k => (X (Sum.inr (s k).down) : MvPolynomial (Fin m ⊕ Fin n) R))
    (F := Finset.univ) (fun k _ => X_inr_mem_yGrading R m n (s k).down)

/-- Every finite intersection of the `D₊(yⱼ)` is affine. -/
theorem isAffineOpen_iInf_bundleCover (r : ℕ) (s : Fin (r + 1) → ULift.{u} (Fin n)) :
    IsAffineOpen (⨅ k, bundleCover R m n (s k)) := by
  rw [iInf_bundleCover]
  exact Proj.isAffineOpen_basicOpen (yGrading R m n) _ (prod_mem_yGrading R m n s)
    (Nat.succ_pos r)

/-- **The cohomology of a quasi-coherent module on `P` vanishes in degree `q + 1` once every
ordered Čech cocycle of degree `q + 1` of the cover by the `D₊(yⱼ)` is a coboundary.** -/
theorem isZero_rightDerived_bundle_of_exact (F : (coneBundle R m n).Modules) [F.IsQuasicoherent]
    (q : ℕ)
    (hex : ∀ c : CechCochains.OrdCochain (X := TopCat.of (coneBundle R m n))
        (bundleCover R m n) (Stacks.Cohomology.CechSheaf.abSections F) (q + 1),
      CechCochains.ordD (X := TopCat.of (coneBundle R m n)) (bundleCover R m n)
          (Stacks.Cohomology.CechSheaf.abSections F) (q + 1) c = 0 →
        ∃ b, CechCochains.ordD (X := TopCat.of (coneBundle R m n)) (bundleCover R m n)
          (Stacks.Cohomology.CechSheaf.abSections F) q b = c) :
    IsZero
      (((Stacks.Cohomology.sectionsFunctor (coneBundle R m n) ⊤).rightDerived (q + 1)).obj F) :=
  Stacks.Cohomology.OrderedCech.isZero_rightDerived_sections_of_exact (coneBundle R m n)
    (bundleCover R m n) (iSup_bundleCover R m n) (isAffineOpen_iInf_bundleCover R m n) F q hex

end Stacks.DeRham.CoordinateCone

end
