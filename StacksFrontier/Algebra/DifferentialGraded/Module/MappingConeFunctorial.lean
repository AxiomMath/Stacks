module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.Homotopy
public import StacksFrontier.Algebra.DGA.Cone

/-!
# Functoriality of the mapping cone up to homotopy

A square of homomorphisms of right differential graded modules which commutes up to homotopy
extends to a morphism between the mapping-cone triangles of its two horizontal arrows: there is a
homomorphism of the cones making the inclusion square and the shifted-projection square commute
on the nose.

## Main results

* `DifferentialGradedModule.exists_mappingConeMap_of_homotopic_square`: the third map of the
  morphism of cone triangles, together with the two commuting squares.

## Implementation notes

The map between the cones is the matrix `(b, H; 0, a)`, where `H` is the chosen homotopy; this is
the construction of the source. Its two squares with the cone inclusion and the cone projection
commute already as equalities of homomorphisms of differential graded modules, hence in
particular in the homotopy category, where the first square commutes by the assumed homotopy.
The shifted fourth vertical map of the morphism of triangles is `shiftMap a 1`.

## References

* [Stacks Project, Tag 09KD](https://stacks.math.columbia.edu/tag/09KD)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
variable {K₁ L₁ K₂ L₂ : DifferentialGradedModule A}

/-- A square of homomorphisms of differential graded modules commuting up to homotopy extends to
their mapping cones. The inclusion square and the shifted-projection square commute already
before passing to homotopy classes. -/
@[stacks 09KD]
theorem exists_mappingConeMap_of_homotopic_square
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : Homotopic (f₁ ≫ b) (a ≫ f₂)) :
    ∃ c : coneModule f₁ ⟶ coneModule f₂,
      coneInclusion f₁ ≫ c = b ≫ coneInclusion f₂ ∧
      c ≫ coneProjection f₂ = coneProjection f₁ ≫ shiftMap a 1 := by
  rcases h with ⟨H⟩
  refine ⟨{
    toFun := LinearMap.prod
      ((b.toFun.comp (LinearMap.fst R L₁.M K₁.M)) +
        ((H.toLinearMap.restrictScalars R).comp
          (LinearMap.snd R L₁.M K₁.M)))
      (a.toFun.comp (LinearMap.snd R L₁.M K₁.M))
    map_smul := by
      intro x r
      show (b.toFun (MulOpposite.op r • x.1) + H.toLinearMap (MulOpposite.op r • x.2),
        a.toFun (MulOpposite.op r • x.2)) = (MulOpposite.op r • (b.toFun x.1 +
        H.toLinearMap x.2), MulOpposite.op r • a.toFun x.2)
      simp [b.map_smul, a.map_smul, H.toLinearMap.map_smul, smul_add]
    map_grading := by
      intro n x hx
      change L₁.M × K₁.M at x
      change x ∈ coneGrading K₁ L₁ n at hx
      show (b.toFun x.1 + H.toLinearMap x.2, a.toFun x.2) ∈
        coneGrading K₂ L₂ n
      rw [coneGrading_mem] at hx ⊢
      refine ⟨(L₂.grading n).add_mem (b.map_grading n x.1 hx.1) ?_,
        a.map_grading (n + 1) x.2 hx.2⟩
      simpa using H.map_grading (n + 1) x.2 hx.2
    map_d := by
      apply LinearMap.ext; intro x
      change L₁.M × K₁.M at x
      show (b.toFun (L₁.d x.1 + f₁.toFun x.2) +
          H.toLinearMap (-K₁.d x.2), a.toFun (-K₁.d x.2)) =
        (L₂.d (b.toFun x.1 + H.toLinearMap x.2) +
          f₂.toFun (a.toFun x.2), -K₂.d (a.toFun x.2))
      have hb : b.toFun (L₁.d x.1) = L₂.d (b.toFun x.1) := LinearMap.congr_fun b.map_d x.1
      have ha : a.toFun (K₁.d x.2) = K₂.d (a.toFun x.2) := LinearMap.congr_fun a.map_d x.2
      have hcomm : b.toFun (f₁.toFun x.2) - f₂.toFun (a.toFun x.2) =
          L₂.d (H.toLinearMap x.2) + H.toLinearMap (K₁.d x.2) := by
        simpa only [Hom.comp_toFun_apply] using H.homotopy_eq x.2
      rw [sub_eq_iff_eq_add] at hcomm
      apply Prod.ext
      · simp only [map_add, map_neg]; rw [hb, hcomm]; abel
      · simp only [map_neg, ha]
  }, ?_, ?_⟩
  · apply Hom.ext; ext x
    simp only [Hom.comp_toFun_apply]
    show (b.toFun x + (H.toLinearMap.restrictScalars R) 0,
        a.toFun 0) = (b.toFun x, (0 : K₂.M))
    simp
  · apply Hom.ext; ext x
    simp only [Hom.comp_toFun_apply]
    change L₁.M × K₁.M at x
    show (b.toFun x.1 + (H.toLinearMap.restrictScalars R) x.2,
        a.toFun x.2).2 = a.toFun x.2
    rfl

end DifferentialGradedModule
