module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.LongExactSequence

/-! # Quasi-isomorphisms along an admissible short exact sequence

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. An admissible short
exact sequence `K → L → M` of right differential graded `A`-modules (Tag 09JT) is in particular
a short exact sequence of the underlying cochain complexes: it is injective, surjective and exact
on underlying modules, and each of those three conditions can be read off one homogeneous degree
at a time. A morphism from one admissible short exact sequence to another therefore has a long
exact cohomology ladder, and the five lemma gives the two-out-of-three principle for
quasi-isomorphisms.

This is the form in which a dévissage along a property-(P) filtration consumes the statement:
the property being propagated is that a morphism of *ordinary* tensor products is a
quasi-isomorphism, and the ordinary tensor product is not a functor on the derived category, so
the propagation cannot be read off a distinguished triangle.

## Main definitions

* `DifferentialGradedModule.admissibleCochainShortComplex`: an admissible short exact sequence,
  read as a short complex of cochain complexes of modules over the base ring.

## Main results

* `DifferentialGradedModule.admissibleCochainShortComplex_shortExact`: that short complex is
  short exact.
* `DifferentialGradedModule.quasiIso_τ₂_of_shortExact`: **the middle quasi-isomorphism of a
  morphism of short exact sequences of cochain complexes**, from the outer two.
* `DifferentialGradedModule.quasiIso_natTrans_app_of_isAdmissibleShortExact`: the two-out-of-three
  principle for a morphism of functors into differential graded modules, at a diagram whose
  images under both functors are admissible short exact sequences.

## Implementation notes

*Why short exactness is checked degreewise and not through the abelian structure.*
`DifferentialGradedModule.shortExact_forgetToCochainComplex` already derives short exactness of
the underlying sequence of cochain complexes from short exactness in `Mod_{(A, d)}`, but what an
admissible sequence provides is injectivity, surjectivity and exactness on underlying modules,
not a monomorphism, an epimorphism and an abelian-categorical exactness. Those three elementwise
facts give the degreewise criterion directly: a grading-preserving map commutes with taking
graded components, by `DirectSum.coe_decompose_apply_map`, so each of them descends to every
homogeneous degree.

*Where the middle case comes from.* Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃`
covers the third term of the ladder; the middle term is the same five-lemma argument run on the
two truncations of the five-arrow exact sequence, and is proved here.

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT), admissible short exact
  sequences.
* [Stacks Project, Tag 09JK](https://stacks.math.columbia.edu/tag/09JK), the long exact cohomology
  sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R)

/-! ### An admissible short exact sequence as a short complex of cochain complexes -/

/-- The composite of the two maps of an admissible short exact sequence vanishes. -/
theorem comp_eq_zero_of_isAdmissibleShortExact {X Y Z : DifferentialGradedModule.{u, u, u} A}
    (i : X ⟶ Y) (p : Y ⟶ Z) (h : IsAdmissibleShortExact i p) : i ≫ p = 0 := by
  refine Hom.ext (LinearMap.ext fun x => ?_)
  show p.toFun (i.toFun x) = 0
  have hx : i.toFun x ∈ LinearMap.range i.toFun := ⟨x, rfl⟩
  rw [h.exact] at hx
  exact hx

/-- An admissible short exact sequence of right differential graded `A`-modules, read as a short
complex of cochain complexes of modules over the base ring. -/
def admissibleCochainShortComplex {X Y Z : DifferentialGradedModule.{u, u, u} A}
    (i : X ⟶ Y) (p : Y ⟶ Z) (h : IsAdmissibleShortExact i p) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (ShortComplex.mk i p (comp_eq_zero_of_isAdmissibleShortExact A i p h)).map
    (forgetToCochainComplex A)

/-- **An admissible short exact sequence is short exact on underlying cochain complexes.** Each
of injectivity, surjectivity and exactness descends to every homogeneous degree, because a
grading-preserving map commutes with taking graded components. -/
theorem admissibleCochainShortComplex_shortExact
    {X Y Z : DifferentialGradedModule.{u, u, u} A}
    (i : X ⟶ Y) (p : Y ⟶ Z) (h : IsAdmissibleShortExact i p) :
    (admissibleCochainShortComplex A i p h).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    show Function.Exact (i.gradedMap n) (p.gradedMap n)
    intro y
    refine ⟨fun hy => ?_, ?_⟩
    · have hyv : p.toFun (y : Y.M) = 0 := congrArg Subtype.val hy
      have hy' : (y : Y.M) ∈ LinearMap.range i.toFun := by rw [h.exact]; exact hyv
      obtain ⟨x, hx⟩ := hy'
      refine ⟨DirectSum.decompose X.grading x n, Subtype.ext ?_⟩
      show i.toFun ((DirectSum.decompose X.grading x n : X.M)) = (y : Y.M)
      rw [← DirectSum.coe_decompose_apply_map X.grading Y.grading i.toFun
        (fun j z hz => i.map_grading j z hz) x n, hx,
        DirectSum.decompose_of_mem_same Y.grading y.property]
    · rintro ⟨x, rfl⟩
      refine Subtype.ext ?_
      show p.toFun (i.toFun (x : X.M)) = 0
      exact congrArg (fun f : X ⟶ Z => f.toFun (x : X.M))
        (comp_eq_zero_of_isAdmissibleShortExact A i p h)
  · rw [ModuleCat.mono_iff_injective]
    show Function.Injective (i.gradedMap n)
    intro x y hxy
    exact Subtype.ext (h.injective (congrArg Subtype.val hxy))
  · rw [ModuleCat.epi_iff_surjective]
    show Function.Surjective (p.gradedMap n)
    intro z
    obtain ⟨y, hy⟩ := h.surjective (z : Z.M)
    have hgraded := DirectSum.coe_decompose_apply_map Y.grading Z.grading p.toFun
      (fun j w hw => p.map_grading j w hw) y n
    rw [hy, DirectSum.decompose_of_mem_same Z.grading z.2] at hgraded
    exact ⟨DirectSum.decompose Y.grading y n, Subtype.ext hgraded.symm⟩

/-! ### The two-out-of-three principle -/

/-- **The middle quasi-isomorphism of a morphism of short exact sequences of cochain complexes**,
from the outer two. The two truncations of the five-arrow exact cohomology sequence make the
middle map of cohomology a monomorphism and an epimorphism. -/
theorem quasiIso_τ₂_of_shortExact {V : Type*} [Category V] [Abelian V]
    {S T : ShortComplex (CochainComplex V ℤ)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    (h₁ : QuasiIso f.τ₁) (h₃ : QuasiIso f.τ₃) : QuasiIso f.τ₂ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap f.τ₂ n) := by
    refine Abelian.mono_of_epi_of_mono_of_mono
      ((ComposableArrows.δ₀Functor ⋙ ComposableArrows.δ₀Functor).map
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ f hS hT (n - 1) n (by simp)))
      ((HomologicalComplex.HomologySequence.composableArrows₅_exact hS (n - 1) n
        (by simp)).δ₀.δ₀)
      ((HomologicalComplex.HomologySequence.composableArrows₅_exact hT (n - 1) n
        (by simp)).δ₀.δ₀) ?_ ?_ ?_
    · show Epi (HomologicalComplex.homologyMap f.τ₃ (n - 1)); infer_instance
    · show Mono (HomologicalComplex.homologyMap f.τ₁ n); infer_instance
    · show Mono (HomologicalComplex.homologyMap f.τ₃ n); infer_instance
  have hepi : Epi (HomologicalComplex.homologyMap f.τ₂ n) := by
    refine Abelian.epi_of_epi_of_epi_of_mono
      ((ComposableArrows.δlastFunctor ⋙ ComposableArrows.δlastFunctor).map
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ f hS hT n (n + 1) (by simp)))
      ((HomologicalComplex.HomologySequence.composableArrows₅_exact hS n (n + 1)
        (by simp)).δlast.δlast)
      ((HomologicalComplex.HomologySequence.composableArrows₅_exact hT n (n + 1)
        (by simp)).δlast.δlast) ?_ ?_ ?_
    · show Epi (HomologicalComplex.homologyMap f.τ₁ n); infer_instance
    · show Epi (HomologicalComplex.homologyMap f.τ₃ n); infer_instance
    · show Mono (HomologicalComplex.homologyMap f.τ₁ (n + 1)); infer_instance
  exact isIso_of_mono_of_epi _

/-- **The two-out-of-three principle for a morphism of functors into differential graded
modules.** If a diagram `X → Y → Z` is carried by both functors to an admissible short exact
sequence, then the components of a morphism of the two functors at any two of `X`, `Y`, `Z` being
quasi-isomorphisms forces the third — stated for the third term and for the middle term, the two
cases a dévissage along a property-(P) filtration needs. -/
theorem quasiIso_natTrans_app_of_isAdmissibleShortExact {S : Type*} [Category S]
    {F G : S ⥤ DifferentialGradedModule.{u, u, u} A} (t : F ⟶ G) {X Y Z : S}
    (i : X ⟶ Y) (p : Y ⟶ Z)
    (hF : IsAdmissibleShortExact (F.map i) (F.map p))
    (hG : IsAdmissibleShortExact (G.map i) (G.map p)) :
    (QuasiIso ((forgetToCochainComplex A).map (t.app X)) →
        QuasiIso ((forgetToCochainComplex A).map (t.app Y)) →
        QuasiIso ((forgetToCochainComplex A).map (t.app Z))) ∧
      (QuasiIso ((forgetToCochainComplex A).map (t.app X)) →
        QuasiIso ((forgetToCochainComplex A).map (t.app Z)) →
        QuasiIso ((forgetToCochainComplex A).map (t.app Y))) := by
  let U := forgetToCochainComplex.{u, u, u} A
  have comm : ∀ {a b : S} (j : a ⟶ b),
      U.map (t.app a) ≫ U.map (G.map j) = U.map (F.map j) ≫ U.map (t.app b) := fun j => by
    rw [← U.map_comp, ← U.map_comp, t.naturality]
  let φ : admissibleCochainShortComplex A (F.map i) (F.map p) hF ⟶
      admissibleCochainShortComplex A (G.map i) (G.map p) hG :=
    { τ₁ := U.map (t.app X)
      τ₂ := U.map (t.app Y)
      τ₃ := U.map (t.app Z)
      comm₁₂ := comm i
      comm₂₃ := comm p }
  have hF' := admissibleCochainShortComplex_shortExact A _ _ hF
  have hG' := admissibleCochainShortComplex_shortExact A _ _ hG
  exact ⟨HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hF' hG',
    fun h₁ h₃ => quasiIso_τ₂_of_shortExact φ hF' hG' h₁ h₃⟩

end DifferentialGradedModule

end
