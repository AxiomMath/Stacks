module

public import StacksCore.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.ConnectingHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.LongExactSequence

/-!
# The connecting homomorphism computes the boundary maps of the long exact sequence

Let `0 → K → L → M → 0` be an admissible short exact sequence of right differential graded
modules and let `s : M → L` and `π : L → K` be compatible graded splittings of it. The
connecting homomorphism `δ = π ∘ d_L ∘ s : M ⟶ K[1]` of
`StacksFrontier.Algebra.DifferentialGraded.Module.ConnectingHom` is a homomorphism of differential
graded modules; this file proves that the map it induces on cohomology is the boundary map of the
long exact cohomology sequence of the sequence.

## Main definitions

* `DifferentialGradedModule.GradedHom.gradedMap`: a graded homomorphism restricted to a
  homogeneous component.
* `DifferentialGradedModule.shiftToCochainComplexIso`: the cochain complex underlying `K[1]` is
  the shift of the cochain complex underlying `K`.
* `DifferentialGradedModule.splittingOfGradedSplittings`: the degreewise splitting of the
  underlying short complex of cochain complexes determined by `s` and `π`.

## Main results

* `DifferentialGradedModule.forgetToCochainComplex_map_connectingHom`: the morphism of cochain
  complexes underlying `δ` is Mathlib's `CochainComplex.homOfDegreewiseSplit` of that degreewise
  splitting.
* `DifferentialGradedModule.homologyMap_connectingHom`: hence `δ` induces the boundary maps of
  the long exact cohomology sequence of 09JK.

## Implementation notes

The two halves being glued here state their splitting hypotheses differently. The source, and
hence `connectingHom`, asks for `g ∘ s = id`, `π ∘ f = id` and `ker π = im s`, whereas a
`CategoryTheory.ShortComplex.Splitting` asks for a full direct-sum decomposition, whose third
field is `π ≫ f + g ≫ s = id`. The comparison is
`DifferentialGradedModule.IsAdmissibleShortExact.decomposition`, which derives that
decomposition from the source's hypotheses; `splittingOfGradedSplittings` is then the degreewise
splitting it provides.

Identifying `(K[1])^•` with `(K^•)[1]` needs no sign: both have `K^{n+1}` in degree `n` and
`-d_K` as differential, the `(-1)^1` of `shift` and the `(-1)^1` of `CochainComplex.shiftFunctor`
being the same sign. So `shiftToCochainComplexIso` is the identity in each degree. It is stated
only for a shift by `1`, where the two index expressions `n + 1 + 1` agree on the nose; a general
shift by `k` would need a transport along `n + 1 + k = n + k + 1`, and nothing here uses one.
`toCochainComplex` is made implicitly reducible for the file so that `simp` can see through
`M.toCochainComplex.X n` to `M^n` when matching the two spellings of a degree.

## References

* [Stacks Project, Tag 09JU](https://stacks.math.columbia.edu/tag/09JU)
* [Stacks Project, Tag 011K](https://stacks.math.columbia.edu/tag/011K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

/-- A graded homomorphism of differential graded modules restricted to a homogeneous component.
This is `DifferentialGradedModule.Hom.gradedMap` for a map which need not commute with the
differentials. -/
def GradedHom.gradedMap {M N : DifferentialGradedModule.{u, v, u} A} (f : GradedHom M N) (n : ℤ) :
    M.grading n →ₗ[R] N.grading n where
  toFun x := ⟨f.toFun x, f.map_grading n x x.property⟩
  map_add' x y := Subtype.ext (f.toFun.map_add (x : M.M) (y : M.M))
  map_smul' r x := Subtype.ext (f.toFun.map_smul r (x : M.M))

/-- The value of `GradedHom.gradedMap f n` at `x`, as an element of `N`, is `f` applied to `x`. -/
@[simp] theorem GradedHom.gradedMap_apply {M N : DifferentialGradedModule.{u, v, u} A}
    (f : GradedHom M N) (n : ℤ) (x : M.grading n) :
    (f.gradedMap n x : N.M) = f.toFun x := rfl

attribute [local implicit_reducible] DifferentialGradedModule.toCochainComplex

/-- The cochain complex underlying the shift `M[1]` is the shift of the cochain complex
underlying `M`: in degree `n` both are `M^{n+1}` and both have differential `-d_M`. -/
noncomputable def shiftToCochainComplexIso (M : DifferentialGradedModule.{u, v, u} A) :
    (shift M 1).toCochainComplex ≅
      (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (1 : ℤ)).obj
        M.toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    obtain rfl : i + 1 = j := hij
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      CochainComplex.shiftFunctor_obj_d', toCochainComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl)

variable (S : ShortComplex (DifferentialGradedModule.{u, v, u} A))

/-- Compatible graded splittings of an admissible short exact sequence of differential graded
modules split the underlying sequence of cochain complexes in every degree. -/
noncomputable def splittingOfGradedSplittings
    (sec : GradedHom S.X₃ S.X₂) (ret : GradedHom S.X₂ S.X₁)
    (hs : ∀ x : S.X₃.M, S.g.toFun (sec.toFun x) = x)
    (hret : ∀ x : S.X₁.M, ret.toFun (S.f.toFun x) = x)
    (hsplit : ∀ y : S.X₂.M, S.f.toFun (ret.toFun y) + sec.toFun (S.g.toFun y) = y)
    (n : ℤ) :
    ((S.map (forgetToCochainComplex A)).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)).Splitting where
  r := ModuleCat.ofHom (ret.gradedMap n)
  s := ModuleCat.ofHom (sec.gradedMap n)
  f_r := ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext (hret _))
  s_g := ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext (hs _))
  id := ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext (hsplit _))

/-- The morphism of cochain complexes underlying the connecting homomorphism `δ : M ⟶ K[1]` is,
after the identification of `(K[1])^•` with `(K^•)[1]`, Mathlib's connecting morphism
`CochainComplex.homOfDegreewiseSplit` of the induced degreewise splitting. Both have
`π ∘ d_L ∘ s` in degree `n`. -/
theorem forgetToCochainComplex_map_connectingHom
    (hfg : IsAdmissibleShortExact S.f S.g)
    (sec : GradedHom S.X₃ S.X₂) (ret : GradedHom S.X₂ S.X₁)
    (hs : ∀ x : S.X₃.M, S.g.toFun (sec.toFun x) = x)
    (hret : ∀ x : S.X₁.M, ret.toFun (S.f.toFun x) = x)
    (hker : LinearMap.ker ret.toFun = LinearMap.range sec.toFun) :
    (forgetToCochainComplex A).map (connectingHom S.f S.g hfg sec ret hs hret hker).val ≫
        (shiftToCochainComplexIso S.X₁).hom =
      CochainComplex.homOfDegreewiseSplit (S.map (forgetToCochainComplex A))
        (splittingOfGradedSplittings S sec ret hs hret
          (hfg.decomposition hs hret hker)) := by
  ext n x
  apply Subtype.ext
  dsimp only [forgetToCochainComplex, CategoryTheory.ShortComplex.map_X₂]
  simp only [HomologicalComplex.comp_f, CochainComplex.homOfDegreewiseSplit_f,
    CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cocycle.mk_coe,
    CochainComplex.HomComplex.Cochain.mk_v, splittingOfGradedSplittings,
    shiftToCochainComplexIso, HomologicalComplex.Hom.isoOfComponents, Iso.refl_hom,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    toCochainComplex_d, Hom.toCochainMap_f, ModuleCat.hom_id, LinearMap.id_coe, id_eq,
    CategoryTheory.ShortComplex.map_X₂]
  exact (connectingHom S.f S.g hfg sec ret hs hret hker).property _

/-- **Stacks 09JU**, second clause: the connecting homomorphism `δ = π ∘ d_L ∘ s : M ⟶ K[1]` of
an admissible short exact sequence of differential graded modules induces the boundary maps of
the long exact cohomology sequence of 09JK.

The boundary map is the `δ` of the short exact sequence of underlying cochain complexes, i.e. the
one appearing in `DifferentialGradedModule.longExactCohomology`; the cohomology of `K[1]` in
degree `n` is identified with that of `K` in degree `n + 1` by the shift isomorphism of
`HomologicalComplex.homologyFunctor`, as in 011H.

The proof transports 011K, the same statement for a degreewise split short exact sequence of
cochain complexes, along `forgetToCochainComplex`. -/
@[stacks 09JU "clause (ii): δ induces the boundary maps of the long exact cohomology sequence"]
theorem homologyMap_connectingHom (hS : S.ShortExact)
    (hfg : IsAdmissibleShortExact S.f S.g)
    (sec : GradedHom S.X₃ S.X₂) (ret : GradedHom S.X₂ S.X₁)
    (hs : ∀ x : S.X₃.M, S.g.toFun (sec.toFun x) = x)
    (hret : ∀ x : S.X₁.M, ret.toFun (S.f.toFun x) = x)
    (hker : LinearMap.ker ret.toFun = LinearMap.range sec.toFun)
    (n m : ℤ) (hnm : (ComplexShape.up ℤ).Rel n m) (hm : 1 + n = m) :
    HomologicalComplex.homologyMap
        ((forgetToCochainComplex A).map
            (connectingHom S.f S.g hfg sec ret hs hret hker).val ≫
          (shiftToCochainComplexIso S.X₁).hom) n ≫
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).shiftIso
          1 n m hm).hom.app S.X₁.toCochainComplex =
      (shortExact_forgetToCochainComplex A S hS).δ n m hnm := by
  rw [forgetToCochainComplex_map_connectingHom S hfg sec ret hs hret hker]
  exact CochainComplex.homologyMap_homOfDegreewiseSplit _ _ _ n m hnm hm

end DifferentialGradedModule
