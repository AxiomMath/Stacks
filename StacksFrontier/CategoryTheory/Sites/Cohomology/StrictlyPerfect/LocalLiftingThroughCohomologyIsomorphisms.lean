module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalNullHomotopy
import StacksCore.Tactic.StacksAttribute

/-!
# Local lifting through a map which is a cohomology isomorphism in high degrees

Let `(C, O)` be a ringed site, `U` an object of `C`, and consider a solid diagram of complexes
of `O|_U`-modules
```
E --α--> F
     ↗
    G
```
with `E` strictly perfect, `Eʲ = 0` for `j < a`, and `f : G ⟶ F` inducing an isomorphism on
`Hʲ` for `j > a` and an epimorphism on `Hᵃ`. Then `α` factors through `f`, up to homotopy,
after restriction along the arrows of a covering sieve of `U`.

The argument is the one in the Stacks Project: the hypotheses on `f` say exactly that the
mapping cone `C(f)` has vanishing cohomology in degrees at least `a`, so Stacks 08FP (2)
makes `E ⟶ F ⟶ C(f)` null-homotopic on a covering sieve; restricting the distinguished
triangle `G ⟶ F ⟶ C(f) ⟶ G[1]` to each member of that covering and using that the restricted
homotopy category is pretriangulated then produces the dotted arrow.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_lift_homotopy`: Stacks 08FQ.

Stacks 08FQ is stated twice: `exists_coveringSieve_lift_homotopy_general` has the objects of
the site, its morphisms and the sections of the structure sheaf at independent universes, and
`exists_coveringSieve_lift_homotopy` is its instance at `RingedSite.{u, u, 0}`.

## References

* [Stacks Project, Tag 08FQ](https://stacks.math.columbia.edu/tag/08FQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.RingedSite

section Abelian

variable {A : Type*} [Category A] [Abelian A] {G F : CochainComplex A ℤ}

/-- The first map of the homotopy-category triangle of `f : G ⟶ F` is sent by the `j`-th shift of
the homology functor to a morphism satisfying the isomorphism-stable property `P` as soon as
`Hʲ(f)` does.

The shifted homology functor evaluated on the image of `f` in the homotopy category is
conjugate, by `HomotopyCategory.homologyFunctorFactors`, to `Hʲ(f)` itself. -/
private theorem prop_homologyFunctor_shift_map_triangleh_mor₁ (P : MorphismProperty A)
    [P.RespectsIso] (f : G ⟶ F) (j : ℤ) (hj : P (HomologicalComplex.homologyMap f j)) :
    P (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift j).map
      (CochainComplex.mappingCone.triangleh f).mor₁) := by
  have h0 : P ((HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) j).map f) := by
    rw [← NatIso.naturality_2 (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) j) f]
    rwa [P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact h0

/-- If `f : G ⟶ F` induces an isomorphism on `Hʲ` for every `j > a` and an epimorphism on
`Hᵃ`, then the mapping cone of `f` has vanishing cohomology in every degree `i ≥ a`.

The homology functor on the homotopy category is homological, so the distinguished triangle
`G ⟶ F ⟶ C(f) ⟶ G[1]` gives an exact sequence in which `Hⁱ(C(f))` sits between the cokernel
of `Hⁱ(f)` and the kernel of `Hⁱ⁺¹(f)`; both vanish under the hypotheses. -/
private theorem isZero_homology_mappingCone (f : G ⟶ F) (a : ℤ)
    (hf_gt : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_a : Epi (HomologicalComplex.homologyMap f a)) (i : ℤ) (hi : a ≤ i) :
    IsZero ((CochainComplex.mappingCone f).homology i) := by
  have hepi := prop_homologyFunctor_shift_map_triangleh_mor₁
    (MorphismProperty.epimorphisms A) f i (by
    rcases lt_or_eq_of_le hi with h | h
    · have := hf_gt i h
      infer_instance
    · exact h ▸ hf_a)
  have hmono := prop_homologyFunctor_shift_map_triangleh_mor₁
    (MorphismProperty.monomorphisms A) f (i + 1) (by
    have := hf_gt (i + 1) (by omega)
    infer_instance)
  let H := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0
  have hT : CochainComplex.mappingCone.triangleh f ∈
      distTriang (HomotopyCategory A (ComplexShape.up ℤ)) :=
    HomotopyCategory.mappingCone_triangleh_distinguished f
  have hz := (H.homologySequence_exact₃ _ hT i (i + 1) rfl).isZero_X₂_iff.mpr
    ⟨(H.homologySequence_epi_shift_map_mor₁_iff _ hT i).1 hepi,
      (H.homologySequence_mono_shift_map_mor₁_iff _ hT i (i + 1) rfl).1 hmono⟩
  have hz' : IsZero ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) i).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone f))) := hz
  exact ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i).app
    (CochainComplex.mappingCone f)).isZero_iff.mp hz'

end Abelian

variable (X : RingedSite.{u, v, w}) (U : X.C)
variable [HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {E F G :
    CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}

/-- **Stacks 08FQ**, with the site, its morphisms and the sections of the structure sheaf at
independent universes. Let `(C, O)` be a ringed site and `U` an object of `C`. Given a solid
diagram of complexes of `O|_U`-modules
```
E --α--> F
     ↗
    G
```
with `E` strictly perfect, `Eʲ = 0` for `j < a`, `Hʲ(f)` an isomorphism for `j > a` and an
epimorphism for `j = a`, there is a covering sieve of `U` such that over each of its arrows a
dotted arrow exists making the diagram commute up to homotopy. -/
theorem exists_coveringSieve_lift_homotopy_general (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E)
    (hEa : ∀ j : ℤ, j < a → IsZero (E.X j))
    (hf_gt : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_a : Epi (HomologicalComplex.homologyMap f a)) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (g : V ⟶ U), S g →
        ∃ β : ((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
              (Over.mk g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
          ((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
              (Over.mk g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G,
          Nonempty (Homotopy
            (β ≫ ((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
              (Over.mk g)).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            (((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
              (Over.mk g)).mapHomologicalComplex (ComplexShape.up ℤ)).map α)) := by
  obtain ⟨S, hS, hzero⟩ :=
    exists_coveringSieve_homotopy_zero_of_isZero_homology_general
      (X := X) (U := U) (α := α ≫ CochainComplex.mappingCone.inr f) a hE hEa
      (isZero_homology_mappingCone f a hf_gt hf_a)
  refine ⟨S, hS, ?_⟩
  intro V g hg
  let : HasFiniteBiproducts (SheafOfModules.{w}
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over (Over.mk g))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let : HasBinaryBiproducts (SheafOfModules.{w}
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over (Over.mk g))) :=
    hasBinaryBiproducts_of_finite_biproducts _
  let R := SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
    (Over.mk g)
  let RHC := R.mapHomologicalComplex (ComplexShape.up ℤ)
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{w} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over (Over.mk g)))
    (ComplexShape.up ℤ)
  let fOpen := RHC.map f
  let αOpen := RHC.map α
  let ιOpen := CochainComplex.mappingCone.inr fOpen
  let coneIso := CochainComplex.mappingCone.mapHomologicalComplexIso f R
  have hnull : Q.map (RHC.map α ≫ RHC.map (CochainComplex.mappingCone.inr f)) = 0 := by
    rw [← Functor.map_comp]
    exact (HomotopyCategory.quotient_map_eq_zero_iff _).2 (hzero g hg)
  have hconeInr : RHC.map (CochainComplex.mappingCone.inr f) ≫ coneIso.hom = ιOpen :=
    CochainComplex.mappingCone.map_inr (H := R) (φ := f)
  have hcomp : Q.map αOpen ≫ Q.map ιOpen = 0 := by
    rw [← Functor.map_comp, show αOpen ≫ ιOpen =
        (RHC.map α ≫ RHC.map (CochainComplex.mappingCone.inr f)) ≫ coneIso.hom by
      dsimp only [αOpen]
      rw [← hconeInr, Category.assoc], Functor.map_comp, hnull, zero_comp]
  obtain ⟨βq, hβq⟩ := CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂ _
    (HomotopyCategory.mappingCone_triangleh_distinguished fOpen) (Q.map αOpen) hcomp
  obtain ⟨β, hβ⟩ := Q.map_surjective βq
  change RHC.obj E ⟶ RHC.obj G at β
  obtain ⟨K⟩ := (HomotopyCategory.quotient_map_eq_zero_iff _).1
    (show Q.map (β ≫ fOpen - αOpen) = 0 by
      rw [Functor.map_sub, Functor.map_comp]
      exact sub_eq_zero.mpr (hβ.symm ▸ hβq.symm))
  exact ⟨β, ⟨Homotopy.equivSubZero.symm K⟩⟩

section DiagonalUniverses

variable (X : RingedSite.{u, u, 0}) (U : X.C)
variable [HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
variable {E F G :
    CochainComplex (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}

/-- **Stacks 08FQ.** Let `(C, O)` be a ringed site and `U` an object of `C`. Given a solid
diagram of complexes of `O|_U`-modules
```
E --α--> F
     ↗
    G
```
with `E` strictly perfect, `Eʲ = 0` for `j < a`, `Hʲ(f)` an isomorphism for `j > a` and an
epimorphism for `j = a`, there is a covering sieve of `U` such that over each of its arrows a
dotted arrow exists making the diagram commute up to homotopy. -/
@[stacks 08FQ, sga "6 I 4.2"]
theorem exists_coveringSieve_lift_homotopy (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E)
    (hEa : ∀ j : ℤ, j < a → IsZero (E.X j))
    (hf_gt : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_a : Epi (HomologicalComplex.homologyMap f a)) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (g : V ⟶ U), S g →
        ∃ β : ((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
              (Over.mk g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
          ((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
              (Over.mk g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G,
          Nonempty (Homotopy
            (β ≫ ((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
              (Over.mk g)).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            (((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
              (Over.mk g)).mapHomologicalComplex (ComplexShape.up ℤ)).map α)) :=
  exists_coveringSieve_lift_homotopy_general X U α f a hE hEa hf_gt hf_a

end DiagonalUniverses

end AlgebraicGeometry.RingedSite

end
