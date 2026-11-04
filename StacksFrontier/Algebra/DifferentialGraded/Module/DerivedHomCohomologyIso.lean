module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomHomotopyCommShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomCohomologyNatural
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomComplexExtGeneral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of `Hom(K, -)` is the morphisms of the homotopy category

Let `B` be a preadditive category with morphisms in `Type 0`, let `K` be a cochain complex in `B`
and let `E = End(K)` be its endomorphism differential graded algebra. The functor
`CochainComplex.homToDerivedCategoryForget B K : K(B) ⥤ D(Ab)` sends a complex `Y` to the
differential graded `E`-module `Hom^•(K, Y)` read in the derived category of abelian groups; it is
the functor whose right derived functor Tag 09LK is about. This file computes its cohomology:

`H^n(Hom^•(K, Y)) ≅ Hom_{K(B)}(K, Y[n])`,

naturally in `Y`, and records the identification as an isomorphism of `Type 0`-valued functors on
`K(B)`.

The identification is Tag 09LC for the differential graded category of complexes of Tag 09L9,
assembled from pieces that are already available. The degree-`n` homogeneous component of
`Hom^•(K, Y)` is the group of degree-`n` cochains from `K` to `Y`, and its differential is
Mathlib's `CochainComplex.HomComplex.δ`; so the degree-`n` cocycles are Mathlib's
`CochainComplex.HomComplex.Cocycle` and the coboundaries are Mathlib's
`CochainComplex.HomComplex.coboundaries`. Mathlib's
`CochainComplex.HomComplex.CohomologyClass.homAddEquiv` then identifies the quotient with the
morphisms `K ⟶ Y[n]` of the homotopy category, in every degree at once.

## Main definitions

* `CochainComplex.homGradingEquiv`: the degree-`n` homogeneous component of the differential
  graded `E`-module `Hom^•(K, Y)` is the group of degree-`n` cochains from `K` to `Y`.
* `CochainComplex.homCocyclesEquiv` and `CochainComplex.homCohomologyClassEquiv`: the same
  identification read on cocycles and on cocycles modulo coboundaries.
* `CochainComplex.homologyGradedCohomologyIso`: the degree-`n` cohomology of the
  `D(Ab)`-valued functor, restricted to complexes, is the explicit cohomology of the differential
  graded module `Hom^•(K, Y)`.
* `CochainComplex.homologyHomAddEquiv`: **the identification itself**, an additive bijection
  `H^n(Hom^•(K, Y)) ≃+ Hom_{K(B)}(K, Y[n])` for an object `Y` of the homotopy category.
* `CochainComplex.homologyCoyonedaNatIso`: the identification as an isomorphism of
  `Type 0`-valued functors on `K(B)`, the degree-`n` cohomology of `Hom^•(K, -)` against the
  functor corepresented by `K` composed with the translation.

## Main results

* `CochainComplex.homGradingEquiv_delta` and `CochainComplex.homGradingEquiv_comp`: the
  identification of homogeneous components carries the differential of the differential graded
  module to `δ`, and the map induced by a cochain map to composition with it. Both are stated in
  the form that characterises the value by its underlying element of the direct sum, so that no
  transport along the arithmetic of the grading is needed.
* `CochainComplex.map_homCocyclesEquiv_gradedCoboundaries`: the coboundaries of the differential
  graded module are Mathlib's coboundaries, which is what makes the identification descend to the
  quotients.
* `CochainComplex.homologyHomAddEquiv_naturality`: **the identification is natural in `Y`**. The
  class of a cocycle goes to the homotopy class of the morphism `K ⟶ Y[n]` it is, and that
  assignment commutes with a morphism of the homotopy category.

## Implementation notes

*Why the explicit cohomology is used rather than Mathlib's Hom complex directly.* The value of
the functor at `Y` is the differential graded `E`-module `Hom^•(K, Y)`, whose underlying module is
a direct sum over the degrees and whose degree-`n` homogeneous component is the range of the
`n`-th inclusion into that direct sum; it is not Mathlib's complex of cochains on the nose, and
the two live in different categories, modules over the base ring on one side and abelian groups on
the other. What is available on the differential graded side is
`DifferentialGradedModule.gradedCohomologyFunctorIso`, which identifies the homology of the
underlying cochain complex with cocycles modulo coboundaries, naturally; and on Mathlib's side
`CochainComplex.HomComplex.CohomologyClass`, which is the same quotient for the complex of
cochains. The comparison is therefore made between the two quotients, by
`QuotientAddGroup.congr`, and the only computations are the two compatibilities
`CochainComplex.homGradingEquiv_delta` and `CochainComplex.homGradingEquiv_comp`.

*Why the comparison is stated additively.* The homogeneous components are modules over the base
ring `ℤ`, and the cochain groups carry a second `ℤ`-module structure coming from their additive
group. The comparison of the quotients only uses the additive structure, so it is an `AddEquiv`
throughout and no `ℤ`-module structure has to be matched.

*How the two shifts are matched.* Mathlib's identification has
`Hom_{K(B)}(K, Q(Y[n]))` as its target, where `Q` is the quotient functor, whereas the statement
wanted has `Hom_{K(B)}(K, Q(Y)[n])`. The two objects are equal, but the shift on the homotopy
category is induced from the shift on complexes by a construction that is deliberately made
irreducible, so the equality is not definitional; the comparison inserted is the component of the
`CategoryTheory.Functor.CommShift` of the quotient functor, whose naturality is exactly what the
naturality statement needs.

*No differential graded shift is used.* Mathlib's
`CochainComplex.HomComplex.CohomologyClass.homAddEquiv` is available in every degree, so the
degree-`n` statement is not obtained from the degree-zero one by shifting, and in particular the
shift comparison `CochainComplex.homShiftIso` of the differential graded Hom functor plays no
part here.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9)
* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

universe u w

namespace CochainComplex

variable (B : Type u) [Category.{0} B] [Preadditive B] (K : CochainComplex B ℤ)

/-! ### The homogeneous components of `Hom(K, Y)` -/

/-- **The degree-`n` part of `Hom^•(K, Y)` is the degree-`n` cochains.** The differential graded
`End(K)`-module `Hom^•(K, Y)` of Tag 09LE has the direct sum of the homogeneous morphism groups
of the differential graded category of complexes as underlying module, and its degree-`n`
homogeneous component is the `n`-th summand, which for the differential graded category of
complexes of Tag 09L9 is Mathlib's group of degree-`n` cochains. -/
def homGradingEquiv (Y : CochainComplex B ℤ) (n : ℤ) :
    (DGCategory.representableModule (dgCategory B) K Y).grading n ≃ₗ[ℤ] Cochain K Y n :=
  DirectSum.rangeGradingEquiv ℤ (DGCategory.repFamily (dgCategory B) K Y) n

/-- **The cochain attached to a homogeneous element, read off the direct sum.** A homogeneous
element of degree `n` lies in the `n`-th summand, and the cochain it is is the element of that
summand it comes from. This characterisation is how every statement below computes with
`CochainComplex.homGradingEquiv`. -/
theorem homGradingEquiv_eq_of_coe_eq (Y : CochainComplex B ℤ) {n : ℤ}
    (z : (DGCategory.representableModule (dgCategory B) K Y).grading n) (f : Cochain K Y n)
    (hz : (z : (DGCategory.representableModule (dgCategory B) K Y).M) =
      DirectSum.of (DGCategory.repFamily (dgCategory B) K Y) n f) :
    homGradingEquiv B K Y n z = f :=
  DirectSum.rangeGradingEquiv_eq_of_coe_eq ℤ (DGCategory.repFamily (dgCategory B) K Y) z f hz

/-- A homogeneous element of degree `n` comes from a cochain, which `homGradingEquiv` returns. -/
private theorem exists_coe_eq_of_homGradingEquiv (Y : CochainComplex B ℤ) {n : ℤ}
    (w : (DGCategory.representableModule (dgCategory B) K Y).grading n) :
    ∃ f : Cochain K Y n,
      (w : (DGCategory.representableModule (dgCategory B) K Y).M) =
        DirectSum.of (DGCategory.repFamily (dgCategory B) K Y) n f ∧
      homGradingEquiv B K Y n w = f := by
  obtain ⟨f, hf⟩ := (DirectSum.mem_rangeGrading ℤ (DGCategory.repFamily (dgCategory B) K Y) n
    (w : (DGCategory.representableModule (dgCategory B) K Y).M)).mp w.2
  exact ⟨f, hf, homGradingEquiv_eq_of_coe_eq B K Y w f hf⟩

/-- **The differential of `Hom^•(K, Y)` is `δ`.** If a homogeneous element `z` of degree `n` is
the differential of a homogeneous element `w` of degree `i`, with `i + 1 = n`, then the cochain
attached to `z` is `δ` of the cochain attached to `w`.

The statement characterises `z` by its underlying element of the direct sum rather than naming it
as the image of `w`, which avoids transporting along the equality `i + 1 = n`. -/
theorem homGradingEquiv_delta (Y : CochainComplex B ℤ) {i n : ℤ} (h : i + 1 = n)
    (w : (DGCategory.representableModule (dgCategory B) K Y).grading i)
    (z : (DGCategory.representableModule (dgCategory B) K Y).grading n)
    (hz : (z : (DGCategory.representableModule (dgCategory B) K Y).M) =
      (DGCategory.representableModule (dgCategory B) K Y).d
        (w : (DGCategory.representableModule (dgCategory B) K Y).M)) :
    homGradingEquiv B K Y n z = δ i n (homGradingEquiv B K Y i w) := by
  subst h
  obtain ⟨f, hf, hw⟩ := exists_coe_eq_of_homGradingEquiv B K Y w
  have hzv : (z : (DGCategory.representableModule (dgCategory B) K Y).M) =
      DirectSum.of (DGCategory.repFamily (dgCategory B) K Y) (i + 1) (δ i (i + 1) f) := by
    rw [hz]
    show DGCategory.repDifferential (dgCategory B) K Y
      (w : (DGCategory.representableModule (dgCategory B) K Y).M) = _
    rw [hf, DGCategory.repDifferential_of]
    rfl
  rw [homGradingEquiv_eq_of_coe_eq B K Y z (δ i (i + 1) f) hzv, hw]

/-- **The map `Hom^•(K, Y) ⟶ Hom^•(K, Y')` induced by a cochain map is composition with it.** If a
homogeneous element `x'` of degree `n` of `Hom^•(K, Y')` is the image of a homogeneous element `x`
of degree `n` of `Hom^•(K, Y)` under postcomposition with `φ : Y ⟶ Y'`, then the cochain attached
to `x'` is the cochain attached to `x` composed with `φ`.

As in `CochainComplex.homGradingEquiv_delta`, the image is characterised by its underlying element
of the direct sum, which keeps the degree `0 + n` of the composite from having to be transported
to `n` in the statement. -/
theorem homGradingEquiv_comp {Y Y' : CochainComplex B ℤ} (φ : Y ⟶ Y') (n : ℤ)
    (x : (DGCategory.representableModule (dgCategory B) K Y).grading n)
    (x' : (DGCategory.representableModule (dgCategory B) K Y').grading n)
    (hx : (x' : (DGCategory.representableModule (dgCategory B) K Y').M) =
      DGCategory.repPostcomp (dgCategory B) K (Cochain.ofHom φ)
        (x : (DGCategory.representableModule (dgCategory B) K Y).M)) :
    homGradingEquiv B K Y' n x' =
      (homGradingEquiv B K Y n x).comp (Cochain.ofHom φ) (add_zero n) := by
  obtain ⟨f, hf, hx0⟩ := exists_coe_eq_of_homGradingEquiv B K Y x
  have hval : (x' : (DGCategory.representableModule (dgCategory B) K Y').M) =
      DirectSum.of (DGCategory.repFamily (dgCategory B) K Y') n
        (f.comp (Cochain.ofHom φ) (add_zero n)) := by
    rw [hx, hf, DGCategory.repPostcomp_of]
    exact DGCategory.repOf_comp_degree (dgCategory B) K rfl (zero_add n) (zero_add n)
      (Cochain.ofHom φ) f
  rw [homGradingEquiv_eq_of_coe_eq B K Y' x' (f.comp (Cochain.ofHom φ) (add_zero n)) hval, hx0]

/-! ### Cocycles, coboundaries and cohomology classes -/

/-- **The degree-`n` cocycles of `Hom^•(K, Y)` are Mathlib's degree-`n` cocycles.** A homogeneous
element of degree `n` is killed by the differential of the differential graded module exactly when
the cochain it is is killed by `δ`. -/
def homCocyclesEquiv (Y : CochainComplex B ℤ) (n : ℤ) :
    ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCocycles n) ≃+ Cocycle K Y n where
  toFun z := Cocycle.mk (homGradingEquiv B K Y n z.1) (n + 1) rfl (by
    rw [← homGradingEquiv_delta B K Y (show n + 1 = n + 1 from rfl) z.1
        ((DGCategory.representableModule (dgCategory B) K Y).gradedDifferential n z.1) rfl,
      LinearMap.mem_ker.mp z.2, map_zero])
  invFun c := ⟨(homGradingEquiv B K Y n).symm c.1, by
    refine LinearMap.mem_ker.mpr ((homGradingEquiv B K Y (n + 1)).injective ?_)
    rw [homGradingEquiv_delta B K Y (show n + 1 = n + 1 from rfl)
        ((homGradingEquiv B K Y n).symm c.1)
        ((DGCategory.representableModule (dgCategory B) K Y).gradedDifferential n
          ((homGradingEquiv B K Y n).symm c.1)) rfl,
      map_zero, LinearEquiv.apply_symm_apply]
    exact Cocycle.δ_eq_zero c (n + 1)⟩
  left_inv z := Subtype.ext ((homGradingEquiv B K Y n).symm_apply_apply z.1)
  right_inv c := Cocycle.ext ((homGradingEquiv B K Y n).apply_symm_apply c.1)
  map_add' z z' := Cocycle.ext (map_add (homGradingEquiv B K Y n) z.1 z'.1)

/-- The cochain underlying the cocycle attached to a cocycle of `Hom^•(K, Y)` is the cochain
attached to its underlying homogeneous element. -/
@[simp] theorem homCocyclesEquiv_coe (Y : CochainComplex B ℤ) (n : ℤ)
    (z : ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCocycles n)) :
    ((homCocyclesEquiv B K Y n z : Cocycle K Y n) : Cochain K Y n) =
      homGradingEquiv B K Y n z.1 :=
  rfl

/-- **The coboundaries of `Hom^•(K, Y)` are Mathlib's coboundaries.** A degree-`n` cocycle of the
differential graded module is the differential of a homogeneous element of degree `n - 1` exactly
when the cocycle it is is `δ` of a cochain of degree `n - 1`. -/
theorem map_homCocyclesEquiv_gradedCoboundaries (Y : CochainComplex B ℤ) (n : ℤ) :
    AddSubgroup.map (homCocyclesEquiv B K Y n).toAddMonoidHom
        ((DGCategory.representableModule (dgCategory B) K Y).gradedCoboundaries n).toAddSubgroup =
      coboundaries K Y n := by
  have hn : n - 1 + 1 = n := by omega
  refine AddSubgroup.ext fun c => ⟨?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, rfl⟩ := hz
    refine (mem_coboundaries_iff _ (n - 1) hn).2 ⟨homGradingEquiv B K Y (n - 1) w, ?_⟩
    exact (homGradingEquiv_delta B K Y hn w
      ((DGCategory.representableModule (dgCategory B) K Y).gradedToCocycles hn w).1 rfl).symm
  · intro hc
    obtain ⟨β, hβ⟩ := (mem_coboundaries_iff c (n - 1) hn).1 hc
    refine ⟨(DGCategory.representableModule (dgCategory B) K Y).gradedToCocycles hn
      ((homGradingEquiv B K Y (n - 1)).symm β), ⟨_, rfl⟩, Cocycle.ext ?_⟩
    refine (homGradingEquiv_delta B K Y hn ((homGradingEquiv B K Y (n - 1)).symm β)
      ((DGCategory.representableModule (dgCategory B) K Y).gradedToCocycles hn
        ((homGradingEquiv B K Y (n - 1)).symm β)).1 rfl).trans ?_
    rw [LinearEquiv.apply_symm_apply]
    exact hβ

/-- **The explicit degree-`n` cohomology of `Hom^•(K, Y)` is Mathlib's degree-`n` cohomology
classes.** Cocycles modulo coboundaries of the differential graded module `Hom^•(K, Y)` are
cocycles modulo coboundaries of the complex of cochains from `K` to `Y`. -/
def homCohomologyClassEquiv (Y : CochainComplex B ℤ) (n : ℤ) :
    ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCohomology n) ≃+
      CohomologyClass K Y n :=
  QuotientAddGroup.congr
    ((DGCategory.representableModule (dgCategory B) K Y).gradedCoboundaries n).toAddSubgroup
    (coboundaries K Y n) (homCocyclesEquiv B K Y n)
    (map_homCocyclesEquiv_gradedCoboundaries B K Y n)

/-- The identification of cohomology classes sends the class of a cocycle to the class of the
cocycle it is. -/
@[simp] theorem homCohomologyClassEquiv_mk (Y : CochainComplex B ℤ) (n : ℤ)
    (z : ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCocycles n)) :
    homCohomologyClassEquiv B K Y n (Submodule.Quotient.mk z) =
      CohomologyClass.mk (homCocyclesEquiv B K Y n z) :=
  rfl

/-- **The identification of cocycles is compatible with a cochain map.** The map on degree-`n`
cocycles induced by `Hom(K, φ)` is postcomposition of cocycles with `φ`. -/
theorem homCocyclesEquiv_gradedCocyclesMap {Y Y' : CochainComplex B ℤ} (φ : Y ⟶ Y') (n : ℤ)
    (z : ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCocycles n)) :
    homCocyclesEquiv B K Y' n
        (DifferentialGradedModule.gradedCocyclesMap ((homComplexesFunctor B K).map φ) n z) =
      (homCocyclesEquiv B K Y n z).postcomp φ :=
  Cocycle.ext (homGradingEquiv_comp B K φ n z.1 _ rfl)

/-! ### The cohomology of the functor of Tag 09LK -/

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **The degree-`n` cohomology of `Hom(K, -) : K(B) ⥤ D(Ab)`, on complexes.** Restricted along
the quotient functor, the degree-`n` cohomology of the `D(Ab)`-valued differential graded Hom
functor is the explicit degree-`n` cohomology — cocycles modulo coboundaries — of the differential
graded `End(K)`-module `Hom^•(K, Y)`.

The functor being derived is `Hom(K, -)` followed by the localization and by the forgetful
functor `D(E, d) ⥤ D(Ab)`, so this is the composite of three identifications already available:
`CochainComplex.homHomotopyFunctorQuotientIso`, which says that on complexes the functor of Tag
09LE on homotopy classes is `Hom^•(K, -)` followed by the quotient by homotopy;
`DifferentialGradedModule.derivedForgetHomologyIso`, the compatibility of the forgetful functor
with cohomology; and `DifferentialGradedModule.gradedCohomologyFunctorIso`, the explicit
cohomology of a differential graded module. -/
def homologyGradedCohomologyIso (n : ℤ) :
    HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ homToDerivedCategoryForget B K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n ≅
      homComplexesFunctor B K ⋙
        DifferentialGradedModule.gradedCohomologyFunctor (endAlgebra B K) n :=
  Functor.isoWhiskerRight (homHomotopyFunctorQuotientIso B K)
      ((DifferentialGradedModule.quasiIsomorphisms' (endAlgebra B K)).Q ⋙
        DifferentialGradedModule.derivedForget (endAlgebra B K) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n) ≪≫
    Functor.isoWhiskerLeft (homComplexesFunctor B K)
      (DifferentialGradedModule.derivedForgetHomologyIso (endAlgebra B K) n ≪≫
        DifferentialGradedModule.gradedCohomologyFunctorIso (endAlgebra B K) n)

/-- **`H^n(Hom^•(K, Y)) ≅ Hom_{K(B)}(K, Y[n])` for a complex `Y`.** -/
def homologyHomAddEquivOfComplex (n : ℤ) (Y : CochainComplex B ℤ) :
    ↥((homToDerivedCategoryForget B K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Y)) ≃+
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K ⟶
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Y)⟦n⟧) :=
  ((homologyGradedCohomologyIso B K n).app Y).toLinearEquiv.toAddEquiv.trans
    ((homCohomologyClassEquiv B K Y n).trans
      (CohomologyClass.homAddEquiv.trans
        (DifferentialGradedModule.General.homAddEquivOfIso
          (((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso
            (A := ℤ) n).app Y))))

/-- **`H^n(Hom^•(K, Y)) ≅ Hom_{K(B)}(K, Y[n])`.** The degree-`n` cohomology of the value at `Y` of
the `D(Ab)`-valued differential graded Hom functor `Hom(K, -)` that Tag 09LK right derives is the
group of morphisms `K ⟶ Y[n]` of the homotopy category of complexes in `B`.

This is Tag 09LC for the differential graded category of complexes of Tag 09L9: a degree-`n`
cohomology class of `Hom^•(K, Y)` is a closed degree-`n` cochain modulo coboundaries, a closed
degree-`n` cochain is a morphism of complexes `K ⟶ Y[n]`, and a coboundary is a null-homotopic
one. -/
@[sga "4½ Etat_0 1.3.3" "Final clause at n = 0"]
def homologyHomAddEquiv (n : ℤ) (Y : HomotopyCategory B (ComplexShape.up ℤ)) :
    ↥((homToDerivedCategoryForget B K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y) ≃+
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K ⟶ Y⟦n⟧) :=
  homologyHomAddEquivOfComplex B K n
    (Y : CategoryTheory.Quotient (homotopic B (ComplexShape.up ℤ))).as

/-- At the homotopy class of a complex the identification is the one attached to that complex. -/
theorem homologyHomAddEquiv_quotient_obj (n : ℤ) (Y : CochainComplex B ℤ) :
    homologyHomAddEquiv B K n ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Y) =
      homologyHomAddEquivOfComplex B K n Y :=
  rfl

omit [HasDerivedCategory (ModuleCat ℤ)] in
/-- **The identification of cohomology classes with homotopy classes is compatible with a cochain
map.** The class of a cocycle of `Hom^•(K, Y)` goes to the homotopy class of the morphism
`K ⟶ Y[n]` that the cocycle is, so a cochain map `φ : Y ⟶ Y'` acts on both sides by composition
with the `n`-th shift of `φ`. -/
theorem homAddEquiv_homCohomologyClassEquiv_gradedCohomologyMap {Y Y' : CochainComplex B ℤ}
    (φ : Y ⟶ Y') (n : ℤ)
    (c : ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCohomology n)) :
    CohomologyClass.homAddEquiv (homCohomologyClassEquiv B K Y' n
        (DifferentialGradedModule.gradedCohomologyMap ((homComplexesFunctor B K).map φ) n c)) =
      CohomologyClass.homAddEquiv (homCohomologyClassEquiv B K Y n c) ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map (φ⟦n⟧') := by
  induction c using Submodule.Quotient.induction_on with
  | H z =>
    show CohomologyClass.homAddEquiv (CohomologyClass.mk (homCocyclesEquiv B K Y' n
          (DifferentialGradedModule.gradedCocyclesMap
            ((homComplexesFunctor B K).map φ) n z))) =
        CohomologyClass.homAddEquiv (CohomologyClass.mk (homCocyclesEquiv B K Y n z)) ≫
          (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map (φ⟦n⟧')
    rw [homCocyclesEquiv_gradedCocyclesMap, CohomologyClass.homAddEquiv_apply,
      CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk,
      Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]

/-- The identification, spelled out: a cohomology class is carried to the explicit cohomology of
`Hom^•(K, Y)`, then to a cohomology class of the complex of cochains, then to a morphism of the
homotopy category, and finally composed with the comparison of the two readings of the shift. -/
theorem homologyHomAddEquivOfComplex_apply (n : ℤ) (Y : CochainComplex B ℤ)
    (x : ↥((homToDerivedCategoryForget B K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Y))) :
    homologyHomAddEquivOfComplex B K n Y x =
      CohomologyClass.homAddEquiv (homCohomologyClassEquiv B K Y n
          ((homologyGradedCohomologyIso B K n).hom.app Y x)) ≫
        (((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso
          (A := ℤ) n).app Y).hom :=
  rfl

/-- **The identification is natural in a cochain map.** -/
theorem homologyHomAddEquivOfComplex_naturality (n : ℤ) {Y Y' : CochainComplex B ℤ} (φ : Y ⟶ Y')
    (x : ↥((homToDerivedCategoryForget B K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Y))) :
    homologyHomAddEquivOfComplex B K n Y'
        (((homToDerivedCategoryForget B K ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map φ)) x) =
      homologyHomAddEquivOfComplex B K n Y x ≫
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map φ)⟦n⟧' := by
  have hα : (homologyGradedCohomologyIso B K n).hom.app Y'
        (((homToDerivedCategoryForget B K ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map φ)) x) =
      DifferentialGradedModule.gradedCohomologyMap ((homComplexesFunctor B K).map φ) n
        ((homologyGradedCohomologyIso B K n).hom.app Y x) :=
    ConcreteCategory.congr_hom ((homologyGradedCohomologyIso B K n).hom.naturality φ) x
  rw [homologyHomAddEquivOfComplex_apply, homologyHomAddEquivOfComplex_apply, hα, Category.assoc]
  exact (congrArg (· ≫ _)
    (homAddEquiv_homCohomologyClassEquiv_gradedCohomologyMap B K φ n _)).trans
    ((Category.assoc _ _ _).trans (congrArg _
      (((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso (A := ℤ) n).hom.naturality
        φ)))

/-- **The identification is natural in `Y`.** For a morphism `φ : Y ⟶ Y'` of the homotopy
category, the degree-`n` cohomology of `Hom(K, φ)` corresponds to composition with the `n`-th
shift of `φ`. -/
theorem homologyHomAddEquiv_naturality (n : ℤ) {Y Y' : HomotopyCategory B (ComplexShape.up ℤ)}
    (φ : Y ⟶ Y')
    (x : ↥((homToDerivedCategoryForget B K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y)) :
    homologyHomAddEquiv B K n Y'
        (((homToDerivedCategoryForget B K ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map φ) x) =
      homologyHomAddEquiv B K n Y x ≫ φ⟦n⟧' := by
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map_surjective φ
  exact homologyHomAddEquivOfComplex_naturality B K n φ x

/-- **`H^n(Hom^•(K, -)) ≅ Hom_{K(B)}(K, (-)[n])` as functors.** The degree-`n` cohomology of the
`D(Ab)`-valued differential graded Hom functor `Hom(K, -)` that Tag 09LK right derives, read as a
functor to sets, is the functor corepresented by the homotopy class of `K` composed with the
`n`-th translation of the homotopy category of complexes in `B`. -/
@[stacks 09LC "the cohomology of the differential graded Hom module Hom(K, -) of 09LE, in every \
degree, as the functor corepresented by K composed with the translation",
  sga "4½ Etat_0 1.3.3" "The final clause of 3.3"]
def homologyCoyonedaNatIso (n : ℤ) :
    homToDerivedCategoryForget B K ⋙ DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n ⋙
        forget (ModuleCat.{0} ℤ) ≅
      CategoryTheory.shiftFunctor (HomotopyCategory B (ComplexShape.up ℤ)) n ⋙
        coyoneda.obj (Opposite.op ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K)) :=
  NatIso.ofComponents (fun Y => Equiv.toIso (homologyHomAddEquiv B K n Y).toEquiv) (by
    intro Y Y' φ
    ext x
    exact homologyHomAddEquiv_naturality B K n φ x)

end CochainComplex

end
