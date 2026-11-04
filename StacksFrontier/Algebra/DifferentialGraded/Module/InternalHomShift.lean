module

public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPresentation
public import StacksCore.Tactic.StacksAttribute

/-! # The internal hom functor and shifts

Tag 0FQR produces, for *some* pair of presentations of `Hom^•_B(N, P)` and `Hom^•_B(N, P[k])`,
a sign-free isomorphism between the shift of the first and the second. The internal hom functor
of Tag 0FQQ, however, is built on one fixed presentation per module,
`DifferentialGradedModule.homModulePresentation`, and those presentations are chosen
independently for `P` and for `P[k]`. Comparing them is what the shift compatibility of the
internal hom functor needs, and this file does it: the comparison isomorphisms
`DifferentialGradedModule.HomModuleData.compare` between presentations transport the
isomorphism of Tag 0FQR onto *any* chosen pair of presentations, and the resulting map is the
unique one matching the identifications of the graded pieces.

## Main definitions

* `DifferentialGradedModule.HomModuleData.IsShiftComparison`: the property characterizing a
  comparison between the shift of a presentation of `Hom^•_B(N, P)` and a presentation of
  `Hom^•_B(N, P[k])` — corresponding elements have homogeneous maps taking the same values.
* `DifferentialGradedModule.HomModuleData.shiftComparison`: that comparison, for an arbitrary
  pair of presentations.
* `DifferentialGradedModule.homPresentationShiftIso`: the comparison for the presentations the
  internal hom functor actually uses.

## Main results

* `DifferentialGradedModule.HomModuleData.isShiftComparison_shiftComparison` and
  `DifferentialGradedModule.HomModuleData.shiftComparison_unique`: the comparison exists and is
  the only homomorphism with the characterizing property. Uniqueness is what makes the
  comparisons a coherent system: any identity between composites of them that holds after
  applying the identifications holds outright.
* `DifferentialGradedModule.homPresentationShiftIso_apply`: the characterizing property of
  `DifferentialGradedModule.homPresentationShiftIso`.

## Implementation notes

The characterizing property is stated on *values* of the associated homogeneous maps at
homogeneous elements of `N`, exactly as Tag 0FQR states its own conclusion; recovering an
equality of homogeneous maps from it is `DifferentialGradedModule.homogeneousMap_ext`.

The shift of a presentation is not itself presented on the nose — `shift H.module k` has the
right graded pieces only after the degree shift `n ↦ n + k` — which is why the comparison is
phrased as a homomorphism satisfying a property rather than as an equality of presentations.

## References

* [Stacks Project, Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR)
* [Stacks Project, Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}
  {N P : DifferentialGradedModule B} {L : BimoduleStructure A B N}

namespace HomModuleData

/-- The property characterizing a comparison between the `k`-shift of a presentation of
`Hom^•_B(N, P)` and a presentation of `Hom^•_B(N, P[k])`: an element of degree `n + k` on the
left and its image on the right have homogeneous maps taking the same values on `N`. -/
def IsShiftComparison (k : ℤ) (H : HomModuleData A B N P L)
    (Hk : HomModuleData A B N (shift P k) L) (φ : shift H.module k ⟶ Hk.module) : Prop :=
  ∀ (n p : ℤ) (f : H.module.grading (n + k)) (x : N.grading p),
    ((Hk.homogeneousEquiv n
        ⟨φ.toFun (f : H.module.M), φ.map_grading n _ f.property⟩).1 x : P.M) =
      (H.homogeneousEquiv (n + k) f).1 x

/-- At most one homomorphism compares the shift of a presentation of `Hom^•_B(N, P)` with a
presentation of `Hom^•_B(N, P[k])`. -/
theorem shiftComparison_unique {k : ℤ} {H : HomModuleData A B N P L}
    {Hk : HomModuleData A B N (shift P k) L} {φ ψ : shift H.module k ⟶ Hk.module}
    (hφ : IsShiftComparison k H Hk φ) (hψ : IsShiftComparison k H Hk ψ) : φ = ψ := by
  apply Hom.ext
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn (shift H.module k).grading with
  | zero => simp
  | @homogeneous n f =>
    let f' : H.module.grading (n + k) := ⟨f.1, f.property⟩
    have h : (⟨φ.toFun (f' : H.module.M), φ.map_grading n _ f'.property⟩ :
          Hk.module.grading n) =
        ⟨ψ.toFun (f' : H.module.M), ψ.map_grading n _ f'.property⟩ := by
      apply (Hk.homogeneousEquiv n).injective
      exact homogeneousMap_ext fun p x => (hφ n p f' x).trans (hψ n p f' x).symm
    exact congrArg Subtype.val h
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Transport of a Tag 0FQR shift comparison onto an arbitrary pair of presentations, along the
canonical comparisons of presentations. -/
def shiftComparisonOf {k : ℤ} {H₀ : HomModuleData A B N P L}
    {Hk₀ : HomModuleData A B N (shift P k) L} (e : shift H₀.module k ≅ Hk₀.module)
    (H : HomModuleData A B N P L) (Hk : HomModuleData A B N (shift P k) L) :
    shift H.module k ≅ Hk.module :=
  (shiftFunctor A k).mapIso (compare H H₀) ≪≫ e ≪≫ compare Hk₀ Hk

/-- A shift comparison between one pair of presentations, transported along the comparisons of
presentations, is a shift comparison between any other pair. -/
theorem isShiftComparison_shiftComparisonOf {k : ℤ} {H₀ : HomModuleData A B N P L}
    {Hk₀ : HomModuleData A B N (shift P k) L} (e : shift H₀.module k ≅ Hk₀.module)
    (he : IsShiftComparison k H₀ Hk₀ e.hom) (H : HomModuleData A B N P L)
    (Hk : HomModuleData A B N (shift P k) L) :
    IsShiftComparison k H Hk (shiftComparisonOf e H Hk).hom := by
  intro n p f x
  have h1 : (⟨(shiftComparisonOf e H Hk).hom.toFun (f : H.module.M),
        (shiftComparisonOf e H Hk).hom.map_grading n _ f.property⟩ : Hk.module.grading n) =
      ⟨(compareHom Hk₀ Hk).toFun
          (e.hom.toFun ((compareGraded H H₀ (n + k) f : H₀.module.M))),
        (compareHom Hk₀ Hk).map_grading n _
          (e.hom.map_grading n _ (compareGraded H H₀ (n + k) f).property)⟩ := by
    apply Subtype.ext
    show (compareHom Hk₀ Hk).toFun
      (e.hom.toFun ((compareHom H H₀).toFun (f : H.module.M))) = _
    rw [compareHom_apply_grading]
  rw [h1, compareHom_homogeneousEquiv Hk₀ Hk n
      ⟨e.hom.toFun ((compareGraded H H₀ (n + k) f : H₀.module.M)),
        e.hom.map_grading n _ (compareGraded H H₀ (n + k) f).property⟩,
    he n p (compareGraded H H₀ (n + k) f) x]
  exact congrArg (fun g : HomogeneousMap B N P (n + k) => (g.1 : N.M →ₗ[R] P.M) (x : N.M))
    (homogeneousEquiv_compareGraded H H₀ (n + k) f)

/-- The comparison between the `k`-shift of any presentation of `Hom^•_B(N, P)` and any
presentation of `Hom^•_B(N, P[k])`. -/
def shiftComparison (k : ℤ) (H : HomModuleData A B N P L)
    (Hk : HomModuleData A B N (shift P k) L) : shift H.module k ≅ Hk.module :=
  shiftComparisonOf (shiftHomModuleIso A B N P L k).choose_spec.choose_spec.choose H Hk

/-- `shiftComparison k H Hk` has the characterizing property of a shift comparison. -/
theorem isShiftComparison_shiftComparison (k : ℤ) (H : HomModuleData A B N P L)
    (Hk : HomModuleData A B N (shift P k) L) :
    IsShiftComparison k H Hk (shiftComparison k H Hk).hom := by
  refine isShiftComparison_shiftComparisonOf _ ?_ H Hk
  intro n p f x
  exact (shiftHomModuleIso A B N P L k).choose_spec.choose_spec.choose_spec n p f x

end HomModuleData

variable (A B) (N) (L)

/-- The shift comparison for the presentations used by the internal hom functor: the `k`-shift
of `Hom^•_B(N, P)` is canonically isomorphic to `Hom^•_B(N, P[k])`. -/
def homPresentationShiftIso (P : DifferentialGradedModule B) (k : ℤ) :
    shift (homModulePresentation A B N L P).module k ≅
      (homModulePresentation A B N L (shift P k)).module :=
  HomModuleData.shiftComparison k (homModulePresentation A B N L P)
    (homModulePresentation A B N L (shift P k))

/-- The characterizing property of `DifferentialGradedModule.homPresentationShiftIso`. -/
theorem homPresentationShiftIso_apply (P : DifferentialGradedModule B) (k : ℤ) :
    HomModuleData.IsShiftComparison k (homModulePresentation A B N L P)
      (homModulePresentation A B N L (shift P k)) (homPresentationShiftIso A B N L P k).hom :=
  HomModuleData.isShiftComparison_shiftComparison k _ _

end DifferentialGradedModule

end
