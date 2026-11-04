module

public import StacksFrontier.Algebra.DifferentialGraded.Module.EndomorphismBimodule
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex

/-!
# `Hom(L, K)` as a differential graded bimodule over the two endomorphism algebras

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O`, and let `K`, `L` be complexes of `O`-modules with endomorphism
differential graded `R`-algebras `A = Hom_{Comp^dg(O)}(K, K)` and
`B = Hom_{Comp^dg(O)}(L, L)`. The Hom complex `Hom_{Comp^dg(O)}(L, K)` is a right differential
graded `B`-module, by precomposition (Tag 09LE), and `A` acts on it on the left by
postcomposition; the two actions commute, so `Hom(L, K)` is a differential graded
`(A, B)`-bimodule, equivalently (Tag 0FQJ) a differential graded `A^{opp} ⊗_R B`-module.

## Main definitions

* `AlgebraicGeometry.RingedSite.homLeftAction`: the left action of `A` on `Hom(L, K)` by
  postcomposition.
* `AlgebraicGeometry.RingedSite.homBimodule`: `Hom(L, K)` as a differential graded
  `(A, B)`-bimodule.

## Main results

* `AlgebraicGeometry.RingedSite.homLeftAction_action`: a homogeneous `a ∈ A^n` acts through the
  image of `a` under the differential graded functor `Hom(L, -)`, i.e. by postcomposition.

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
* [Stacks Project, Tag 09SU](https://stacks.math.columbia.edu/tag/09SU)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (R : Type u) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  (K L : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-- The action of the representable differential graded functor `Hom(L, -)` on the degree-`n`
endomorphisms of `K`, as an `R`-linear map into the degree-`n` homogeneous right linear
endomorphisms of `Hom(L, K)`. -/
def homPostcompₗ (n : ℤ) :
    (CompDG.{u, u, u, u, u, u} X R).Hom (liftComplex.{u, u, u, u, u} X K)
        (liftComplex.{u, u, u, u, u} X K) n →ₗ[R]
      HomogeneousMap (Rep.{u, u, u, u, u, u} X R L).algebra
        ((Rep.{u, u, u, u, u, u} X R L).functor.obj (liftComplex.{u, u, u, u, u} X K))
        ((Rep.{u, u, u, u, u, u} X R L).functor.obj (liftComplex.{u, u, u, u, u} X K)) n where
  toFun f := (Rep.{u, u, u, u, u, u} X R L).functor.map f
  map_add' := (Rep.{u, u, u, u, u, u} X R L).functor.map_add
  map_smul' := (Rep.{u, u, u, u, u, u} X R L).functor.map_smul

/-- **The left action of `A = End(K)` on `Hom(L, K)` by postcomposition.** A homogeneous
`a ∈ A^n` acts by the degree-`n` cochain underlying the image of `a` under the representable
differential graded functor `Hom(L, -)`. -/
def homLeftAction : (Rep.{u, u, u, u, u, u} X R K).algebra.LeftAction
    ((Rep.{u, u, u, u, u, u} X R L).functor.obj
      (liftComplex.{u, u, u, u, u} X K)).toCochainComplex where
  action n := (homogeneousMapToCochainₗ (Rep.{u, u, u, u, u, u} X R L).algebra _ _ n).comp
    ((homPostcompₗ X R K L n).comp
      ((Rep.{u, u, u, u, u, u} X R K).algebraHom n).toLinearMap)
  map_one := by
    obtain ⟨e, he, hid⟩ := (Rep.{u, u, u, u, u, u} X R K).algebra_one
    have he' : (⟨1, SetLike.one_mem_graded (Rep.{u, u, u, u, u, u} X R K).algebra.grading⟩ :
        (Rep.{u, u, u, u, u, u} X R K).algebra.grading 0) = e := Subtype.ext he.symm
    change homogeneousMapToCochain _ ((Rep.{u, u, u, u, u, u} X R L).functor.map
      ((Rep.{u, u, u, u, u, u} X R K).algebraHom 0 _)) = _
    rw [he', hid, (Rep.{u, u, u, u, u, u} X R L).functor.map_id]
    exact homogeneousMapToCochain_id _ _
  map_mul n m a b := by
    obtain ⟨c, hc, hcomp⟩ := (Rep.{u, u, u, u, u, u} X R K).algebra_mul n m (n + m) rfl a b
    have hc' : (⟨(a : (Rep.{u, u, u, u, u, u} X R K).algebra.A) * (b : _),
        SetLike.mul_mem_graded a.property b.property⟩ :
          (Rep.{u, u, u, u, u, u} X R K).algebra.grading (n + m)) = c := Subtype.ext hc.symm
    change homogeneousMapToCochain _ ((Rep.{u, u, u, u, u, u} X R L).functor.map
      ((Rep.{u, u, u, u, u, u} X R K).algebraHom (n + m) _)) = _
    rw [hc', hcomp, (Rep.{u, u, u, u, u, u} X R L).functor.map_comp]
    exact homogeneousMapToCochain_comp _ rfl _ _
  map_d n a := by
    change homogeneousMapToCochain _ ((Rep.{u, u, u, u, u, u} X R L).functor.map
      ((Rep.{u, u, u, u, u, u} X R K).algebraHom (n + 1) _)) = _
    rw [(Rep.{u, u, u, u, u, u} X R K).algebra_d n a,
      (Rep.{u, u, u, u, u, u} X R L).functor.map_d]
    exact homogeneousMapToCochain_d _ _

/-- A homogeneous `a ∈ A^n` acts on `Hom(L, K)` by postcomposition with `a`: through the image of
`a` under the representable differential graded functor `Hom(L, -)`. -/
theorem homLeftAction_action (n : ℤ) (a : (Rep.{u, u, u, u, u, u} X R K).algebra.grading n) :
    (homLeftAction X R K L).action n a =
      homogeneousMapToCochain _ ((Rep.{u, u, u, u, u, u} X R L).functor.map
        ((Rep.{u, u, u, u, u, u} X R K).algebraHom n a)) :=
  rfl

/-- **`Hom(L, K)` is a differential graded `(A, B)`-bimodule**, `A = End(K)` acting by
postcomposition and `B = End(L)` by precomposition; by Tag 0FQJ this is a differential graded
`A^{opp} ⊗_R B`-module. -/
abbrev homBimodule : DifferentialGraded.Bimodule (Rep.{u, u, u, u, u, u} X R K).algebra
    (Rep.{u, u, u, u, u, u} X R L).algebra where
  rightModule := (Rep.{u, u, u, u, u, u} X R L).functor.obj (liftComplex.{u, u, u, u, u} X K)
  leftAction := ⟨homLeftAction X R K L, fun _ _ =>
    isRightLinearCochain_homogeneousMapToCochain _ _ _⟩

end AlgebraicGeometry.RingedSite

end
