module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorEquivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.Telescope

/-!
# The telescope of a property-(P) differential graded bimodule

Let `A` and `B` be differential graded algebras over a commutative ring `R` and let `P` be a
differential graded `(A, B)`-bimodule having property (P), with filtration `F_•`. The telescope
of the filtration is the differential graded bimodule `⨁_{i ≥ 0} F_iP` together with the two
homomorphisms

`α : ⨁ F_iP ⟶ ⨁ F_iP`,  `α|_{F_iP} = incl_i - (F_iP ↪ F_{i+1}P)`,
`β : ⨁ F_iP ⟶ P`,  `β|_{F_iP} = (F_iP ↪ P)`,

and `0 → ⨁ F_iP → ⨁ F_iP → P → 0` is a short exact sequence of differential graded
`(A, B)`-bimodules which is split as a sequence of graded `(A, B)`-bimodules.

## Main results

* `DifferentialGraded.Bimodule.exists_admissible_telescope`: the telescoping admissible short
  exact sequence of a property-(P) differential graded bimodule, with its direct sum pinned by
  the universal property and its two maps pinned by their values on each stage.

## Implementation notes

Property (P) for a bimodule is read, as in Tag 0FQK, on the right differential graded module
over `Aᵒᵖ ⊗_R B` that the bimodule is by Tag 0FQJ: the hypothesis is a
`DifferentialGradedModule.PropertyPFiltration` of `DifferentialGraded.Bimodule.toTensorModule`,
and the stages of the filtration are brought back to bimodules by
`DifferentialGraded.Bimodule.ofTensorModule`. The whole statement is then transported from
`DifferentialGradedModule.exists_telescope_of_propertyPFiltration`, the telescope over a single
algebra, along the construction of Tag 0FQJ, which leaves the underlying module, its grading and
its differential unchanged — so every map of the transported sequence has literally the same
underlying function as its counterpart over `Aᵒᵖ ⊗_R B`.

The direct sum `⨁ F_iP` is recorded by the universal property of a coproduct rather than as `∐`,
for the reason given in `StacksFrontier/Algebra/DifferentialGraded/Module/Telescope.lean`: the
category of differential graded modules has coproducts only for index types in the carrier
universe, while the filtration is indexed by `ℕ`. The universal property determines the pair
`(S, ι)` up to a unique isomorphism, and the two displayed formulas pin `α` and `β` exactly as
the source describes them; without them the statement would be weaker than the source, since the
mere existence of an admissible short exact sequence with those outer terms is a different
assertion.

Admissibility is exactness of the underlying modules together with graded bimodule splittings on
both sides, which is the source's "split as a sequence of graded `(A, B)`-bimodules"; the
splittings are produced from the graded splittings over `Aᵒᵖ ⊗_R B` by
`DifferentialGraded.Bimodule.tensorGradedPreimage`.

## References

* [Stacks Project, Tag 0FQL](https://stacks.math.columbia.edu/tag/0FQL)
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
* [Stacks Project, Tag 09KL](https://stacks.math.columbia.edu/tag/09KL)
* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra.{u, u} R)

/-- A graded homomorphism out of a right module over the graded tensor product, read as a graded
homomorphism out of the tensor module of the bimodule that module is. Only the action changes,
and by `tensorActionApply_ofTensorModule` it changes by an equality. -/
private def gradedOfTensorSource {Y Z : DifferentialGradedModule (tensorAlgebra A B)}
    (f : DifferentialGradedModule.GradedHom Y Z) :
    DifferentialGradedModule.GradedHom (toTensorModule A B (ofTensorModule A B Y)) Z where
  toFun := f.toFun
  map_grading := f.map_grading
  map_smul := by
    intro x t
    change f.toFun (tensorActionApply A B (ofTensorModule A B Y) t x) = _
    rw [tensorActionApply_ofTensorModule A B Y t x]
    exact f.map_smul x t

/-- A graded homomorphism from the tensor module of a bimodule into a right module over the
graded tensor product, read as a graded homomorphism of bimodules. -/
private def gradedPreimageOfTensor {M : Bimodule A B}
    {Y : DifferentialGradedModule (tensorAlgebra A B)}
    (f : DifferentialGradedModule.GradedHom (toTensorModule A B M) Y) :
    GradedHom A B M (ofTensorModule A B Y) :=
  tensorGradedPreimage A B
    { toFun := f.toFun
      map_grading := f.map_grading
      map_smul := by
        intro x t
        change f.toFun (tensorActionApply A B M t x) =
          tensorActionApply A B (ofTensorModule A B Y) t (f.toFun x)
        rw [tensorActionApply_ofTensorModule A B Y t (f.toFun x)]
        exact f.map_smul x t }

/-- Homomorphisms of bimodules with the same underlying function are equal. -/
private theorem hom_ext_of_toFun_eq {M N : Bimodule A B} {f g : M ⟶ N}
    (h : f.rightHom.toFun = g.rightHom.toFun) : f = g :=
  Bimodule.Hom.ext (DifferentialGradedModule.Hom.ext h)

/-- **Stacks 0FQL.** *"Let `R` be a ring. Let `(A, d)` and `(B, d)` be differential graded
`R`-algebras. Let `P` be a differential graded `(A, B)`-bimodule having property (P) with
corresponding filtration `F_•`, then we obtain a short exact sequence
`0 → ⨁ F_iP → ⨁ F_iP → P → 0` of differential graded `(A, B)`-bimodules which is split as a
sequence of graded `(A, B)`-bimodules."*

Property (P) is read on the right differential graded `Aᵒᵖ ⊗_R B`-module of Tag 0FQJ, and the
stages of the filtration are brought back to bimodules through the same construction. The direct
sum is recorded by its universal property, the second map is the sum of the inclusions
`F_iP → P`, and the first map is, on the summand `F_iP`, the identity minus the inclusion
`F_iP → F_{i+1}P`. -/
@[stacks 0FQL]
theorem exists_admissible_telescope (P : Bimodule A B)
    (F : DifferentialGradedModule.PropertyPFiltration (toTensorModule A B P)) :
    ∃ (S : Bimodule A B) (ι : ∀ i : ℕ, ofTensorModule A B (F.F i) ⟶ S) (α : S ⟶ S) (β : S ⟶ P),
      (∀ (T : Bimodule A B) (g : ∀ i : ℕ, ofTensorModule A B (F.F i) ⟶ T),
          ∃! h : S ⟶ T, ∀ i : ℕ, ι i ≫ h = g i) ∧
        (∀ (i : ℕ) (x : (F.F i).M),
          β.rightHom.toFun ((ι i).rightHom.toFun x) = (F.ι i).toFun x) ∧
        (∀ (i : ℕ) (x : (F.F i).M), α.rightHom.toFun ((ι i).rightHom.toFun x) =
          (ι i).rightHom.toFun x - (ι (i + 1)).rightHom.toFun ((F.incl i).toFun x)) ∧
        IsAdmissibleShortExact A B α β := by
  obtain ⟨S₀, j, α₀, β₀, huniv, hbeta, halpha, hses⟩ :=
    DifferentialGradedModule.exists_telescope_of_propertyPFiltration F
  set eS := toTensorModuleOfTensorModuleIso A B S₀
  set eF := fun i : ℕ => toTensorModuleOfTensorModuleIso A B (F.F i)
  refine ⟨ofTensorModule A B S₀,
    fun i => tensorMapPreimage A B ((eF i).hom ≫ j i ≫ eS.inv),
    tensorMapPreimage A B (eS.hom ≫ α₀ ≫ eS.inv),
    tensorMapPreimage A B (eS.hom ≫ β₀), ?_, hbeta, halpha, ?_⟩
  · intro T g
    let g' : ∀ i : ℕ, F.F i ⟶ toTensorModule A B T :=
      fun i => (eF i).inv ≫ tensorMap A B (g i)
    obtain ⟨h₀, hh₀, huniq⟩ := huniv (toTensorModule A B T) g'
    refine ⟨tensorMapPreimage A B (eS.hom ≫ h₀), fun i => ?_, fun h' hh' => ?_⟩
    · exact hom_ext_of_toFun_eq A B (congrArg (·.toFun) (hh₀ i))
    · have hk : eS.inv ≫ tensorMap A B h' = h₀ := by
        refine huniq _ fun i => DifferentialGradedModule.Hom.ext (LinearMap.ext fun y => ?_)
        exact congrArg (fun f : ofTensorModule A B (F.F i) ⟶ T => f.rightHom.toFun y) (hh' i)
      exact hom_ext_of_toFun_eq A B (congrArg (·.toFun) hk)
  · obtain ⟨r, hr⟩ := hses.admissibleMono
    obtain ⟨s, hs⟩ := hses.admissibleEpi
    exact
      { injective := hses.injective
        surjective := hses.surjective
        exact := hses.exact
        splitMono := ⟨gradedPreimageOfTensor A B (gradedOfTensorSource A B r), hr⟩
        splitEpi := ⟨gradedPreimageOfTensor A B s, hs⟩ }

end DifferentialGraded.Bimodule

end
