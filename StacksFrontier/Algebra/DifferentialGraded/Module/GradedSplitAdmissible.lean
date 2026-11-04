module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryComp
public import StacksFrontier.Algebra.DifferentialGraded.Module.DistinguishedTriangle
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# Graded-split short exact sequences of the differential graded category of modules

A `DGCategory.GradedSplitShortExact` in `DifferentialGradedModule.dgCategory A` is the same data
as an admissible short exact sequence of differential graded `A`-modules together with a
compatible pair of graded splittings: the two closed degree-zero arrows are homomorphisms of
differential graded modules, the two unclosed degree-zero arrows are maps of graded modules, and
the four identities of a graded splitting are exactly what admissibility and compatibility ask
for. The connecting morphism agrees on both sides, because `π ∘ s = 0` kills the second term of
the graded commutator defining the Hom differential.

This is the translation between the two encodings of the notion of Tag 09JT: the one used in the
axiomatics of a differential graded category with cones (Tag 09QJ), where the splitting is part
of the structure, and the one used for differential graded modules (Tag 09K8), where
admissibility is a property and the splittings are produced from it.

## Main definitions

* `DifferentialGradedModule.gradedHomOfHomogeneous`: a degree-zero homogeneous right-linear map,
  read as a map of graded modules.
* `DifferentialGradedModule.compatibleSplittings_gradedSplit`: the compatible splittings carried
  by a graded-split short exact sequence.

## Main results

* `DifferentialGradedModule.isAdmissibleShortExact_gradedSplit`: the two closed arrows of a
  graded-split short exact sequence form an admissible short exact sequence.
* `DifferentialGradedModule.connectingHom_gradedSplit`: its connecting homomorphism is the
  connecting morphism `π d(s)` of the differential graded category.
* `DifferentialGradedModule.isDistinguishedTriangle_gradedSplit`: the triangle of a graded-split
  short exact sequence is distinguished, for any homomorphism `M ⟶ K[1]` whose underlying map is
  the connecting morphism.

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT), admissible short exact
  sequences; [Tag 09K8](https://stacks.math.columbia.edu/tag/09K8), their triangles; and
  [Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), the connecting morphism of a graded
  splitting.
-/

@[expose] public section

namespace DifferentialGradedModule

open CategoryTheory

universe u

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- A degree-zero homogeneous right `A`-linear map, read as a map of graded modules. -/
def gradedHomOfHomogeneous {X Y : DifferentialGradedModule A}
    (u : HomogeneousMap A X Y 0) : GradedHom X Y where
  toFun := u.1
  map_smul x a := u.2.2 a x
  map_grading n x hx := by simpa using u.2.1 n x hx

/-- The underlying function of `gradedHomOfHomogeneous A u` is that of `u`. -/
@[simp] theorem gradedHomOfHomogeneous_toFun {X Y : DifferentialGradedModule A}
    (u : HomogeneousMap A X Y 0) : (gradedHomOfHomogeneous A u).toFun = u.1 := rfl

section

variable {X Y Z : DifferentialGradedModule A}
  (E : DGCategory.GradedSplitShortExact (A := dgCategory A) X Y Z)

/-- `π ∘ a = 𝟙`, pointwise. -/
theorem gradedSplit_pi_a (x : X.M) : E.π.1 (E.a.1.1 x) = x :=
  LinearMap.congr_fun (congrArg Subtype.val E.π_a) x

/-- `b ∘ s = 𝟙`, pointwise. -/
theorem gradedSplit_b_s (x : Z.M) : E.b.1.1 (E.s.1 x) = x :=
  LinearMap.congr_fun (congrArg Subtype.val E.b_s) x

/-- `π ∘ s = 0`, pointwise. -/
theorem gradedSplit_pi_s (x : Z.M) : E.π.1 (E.s.1 x) = 0 :=
  LinearMap.congr_fun (congrArg Subtype.val E.π_s) x

/-- `b ∘ a = 0`, pointwise. -/
theorem gradedSplit_b_a (x : X.M) : E.b.1.1 (E.a.1.1 x) = 0 :=
  LinearMap.congr_fun (congrArg Subtype.val (DGCategory.GradedSplitShortExact.comp_zero E)) x

/-- `a ∘ π + s ∘ b = 𝟙`, pointwise. -/
theorem gradedSplit_decomposition (y : Y.M) :
    E.a.1.1 (E.π.1 y) + E.s.1 (E.b.1.1 y) = y :=
  LinearMap.congr_fun (congrArg Subtype.val E.a_π_add_s_b) y

/-- The graded retraction of a graded-split short exact sequence. -/
def gradedSplitPi : GradedHom Y X := gradedHomOfHomogeneous A E.π

/-- The graded section of a graded-split short exact sequence. -/
def gradedSplitS : GradedHom Z Y := gradedHomOfHomogeneous A E.s

/-- **The two closed arrows of a graded-split short exact sequence are an admissible short exact
sequence.** Injectivity, surjectivity and exactness are all consequences of the four identities
of the graded splitting, and the splitting itself witnesses admissibility of the two arrows. -/
@[stacks 09JT "a graded splitting is an admissible short exact sequence"]
theorem isAdmissibleShortExact_gradedSplit :
    IsAdmissibleShortExact (homOfCocycle A E.a) (homOfCocycle A E.b) where
  injective x₁ x₂ h := by
    rw [← gradedSplit_pi_a A E x₁, ← gradedSplit_pi_a A E x₂]
    exact congrArg E.π.1 h
  surjective z := ⟨E.s.1 z, gradedSplit_b_s A E z⟩
  exact := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact LinearMap.mem_ker.mpr (gradedSplit_b_a A E x)
    · intro y hy
      have hb : E.b.1.1 y = 0 := LinearMap.mem_ker.mp hy
      exact ⟨E.π.1 y, by simpa [hb] using gradedSplit_decomposition A E y⟩
  admissibleMono := ⟨gradedSplitPi A E, gradedSplit_pi_a A E⟩
  admissibleEpi := ⟨gradedSplitS A E, gradedSplit_b_s A E⟩

/-- The compatible pair of graded splittings carried by a graded-split short exact sequence. -/
def compatibleSplittings_gradedSplit :
    CompatibleSplittings A (homOfCocycle A E.a) (homOfCocycle A E.b) where
  s := gradedSplitS A E
  π := gradedSplitPi A E
  hs := gradedSplit_b_s A E
  hπ := gradedSplit_pi_a A E
  hker := by
    apply le_antisymm
    · intro y hy
      refine ⟨E.b.1.1 y, ?_⟩
      have h := gradedSplit_decomposition A E y
      rw [show E.π.1 y = 0 from LinearMap.mem_ker.mp hy, map_zero, zero_add] at h
      exact h
    · rintro y ⟨z, rfl⟩
      exact LinearMap.mem_ker.mpr (gradedSplit_pi_s A E z)

/-- **The connecting homomorphism of the admissible sequence is the connecting morphism of the
graded splitting.** Both are `π d(s)`: the Hom differential of the differential graded category
is the graded commutator `d ∘ s - s ∘ d`, and its second term is killed by `π ∘ s = 0`. -/
@[stacks 09P6 "the connecting morphism of a graded splitting is the connecting homomorphism"]
theorem connectingHom_gradedSplit (z : Z.M) :
    (connectingHom (homOfCocycle A E.a) (homOfCocycle A E.b)
        (isAdmissibleShortExact_gradedSplit A E)
        (gradedSplitS A E) (gradedSplitPi A E)
        (gradedSplit_b_s A E) (gradedSplit_pi_a A E)
        (compatibleSplittings_gradedSplit A E).hker).val.toFun z =
      (DGCategory.GradedSplitShortExact.connectingHom E).1 z := by
  refine ((connectingHom (homOfCocycle A E.a) (homOfCocycle A E.b)
    (isAdmissibleShortExact_gradedSplit A E) (gradedSplitS A E) (gradedSplitPi A E)
    (gradedSplit_b_s A E) (gradedSplit_pi_a A E)
    (compatibleSplittings_gradedSplit A E).hker).property z).trans ?_
  rw [DGCategory.GradedSplitShortExact.connectingHom, dgCategory_comp_val, dgCategory_d_val]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, DifferentialGraded.gradedSign_zero,
    one_smul, map_sub]
  rw [gradedSplit_pi_s A E, sub_zero]
  rfl

/-- **The triangle of a graded-split short exact sequence is distinguished.** The third arrow may
be presented by any homomorphism `Z ⟶ X[1]` whose underlying linear map is the connecting
morphism `π d(s)` of the splitting; a homomorphism of differential graded modules is determined
by that map. -/
@[stacks 09K8 "the triangle of a graded splitting is distinguished"]
theorem isDistinguishedTriangle_gradedSplit (δ : Hom Z (shift X 1))
    (hδ : ∀ z : Z.M, δ.toFun z = (DGCategory.GradedSplitShortExact.connectingHom E).1 z) :
    IsDistinguishedTriangle A (Pretriangulated.Triangle.mk
      ((toHomotopyCategory A).map (homOfCocycle A E.a))
      ((toHomotopyCategory A).map (homOfCocycle A E.b))
      ((toHomotopyCategory A).map δ ≫
        eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ X 1).symm)) := by
  have hval : δ = (connectingHom (homOfCocycle A E.a) (homOfCocycle A E.b)
      (isAdmissibleShortExact_gradedSplit A E) (gradedSplitS A E) (gradedSplitPi A E)
      (gradedSplit_b_s A E) (gradedSplit_pi_a A E)
      (compatibleSplittings_gradedSplit A E).hker).val := by
    apply Hom.ext
    apply LinearMap.ext
    intro z
    rw [hδ z, ← connectingHom_gradedSplit A E z]
  rw [hval]
  exact isDistinguishedTriangle_associatedTriangleOfSplittings A _ _
    (isAdmissibleShortExact_gradedSplit A E) (compatibleSplittings_gradedSplit A E)

end

end DifferentialGradedModule
