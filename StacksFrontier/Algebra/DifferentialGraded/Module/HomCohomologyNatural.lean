module

public import StacksFrontier.Algebra.DifferentialGraded.Module.HomCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# The explicit cohomology of a differential graded module is functorial

`StacksFrontier/Algebra/DifferentialGraded/Module/HomCohomology.lean` computes the degree-`n`
cohomology of a right differential graded `A`-module `X` as the explicit quotient
`DifferentialGradedModule.gradedCohomology`, cocycles modulo coboundaries, and identifies it with
the homology of the underlying cochain complex by
`DifferentialGradedModule.gradedCohomologyIso`. This file makes both constructions functorial: a
homomorphism of differential graded modules induces maps on cocycles and on the explicit
cohomology, and the identification with the homology of the underlying cochain complex is natural.

Naturality is what a consumer of the explicit description needs, since the cohomology functor it
has to match — `DifferentialGradedModule.degreeZeroCohomologyOnHomotopy'` of Tag 09KW, and its
descent to the derived category — is the homology of the underlying cochain complex.

## Main definitions

* `DifferentialGradedModule.gradedCocyclesMap` and
  `DifferentialGradedModule.gradedCohomologyMap`: the maps induced on the degree-`n` cocycles and
  on the explicit degree-`n` cohomology.

## Main results

* `DifferentialGradedModule.gradedCyclesIso_hom_subtype`: the identification of the degree-`n`
  cycles of the underlying cochain complex with the degree-`n` cocycles is compatible with the two
  inclusions into the degree-`n` homogeneous component. This pins that identification down.
* `DifferentialGradedModule.gradedCyclesIso_naturality` and
  `DifferentialGradedModule.gradedCohomologyIso_naturality`: both identifications are natural.

## Implementation notes

*How the identifications are pinned down.* Neither
`DifferentialGradedModule.gradedCyclesIso` nor `DifferentialGradedModule.gradedCohomologyIso` is
given by a formula: the first is Mathlib's comparison of the cycles of a complex with those of a
short complex, followed by the comparison with an explicit left homology datum, and the second is
the corresponding statement for homology. They are characterized instead, and the two
characterizations are what the naturality proofs use: the cycles identification is determined by
compatibility with the inclusion into the ambient homogeneous component, because that inclusion is
a monomorphism; and the cohomology identification is determined by compatibility with
`HomologicalComplex.homologyπ`, which is an epimorphism, by the already proved
`DifferentialGradedModule.homologyπ_gradedCohomologyIso_hom`.

*Why the proofs are written as `calc` chains with every term spelled out.* The objects
`((forgetToCochainComplex A).obj X).X n` and `ModuleCat.of R (X.grading n)` are definitionally but
not syntactically equal, and the same holds for the carrier of the explicit left homology datum
and `ModuleCat.of R (X.gradedCocycles n)`. A chain of rewrites therefore leaves the goal
type-correct only at default transparency, after which later rewrites at the reducible
transparency `rw` uses no longer fire. Writing each intermediate term out keeps every step's goal
freshly elaborated.

## References

* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW)
* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
  {X Y : DifferentialGradedModule A}

/-! ### Functoriality of the explicit cocycles and cohomology -/

/-- A homomorphism of differential graded modules commutes with the differential, degreewise. -/
theorem gradedMap_gradedDifferential (g : X ⟶ Y) (n : ℤ) (x : X.grading n) :
    Y.gradedDifferential n (g.gradedMap n x) = g.gradedMap (n + 1) (X.gradedDifferential n x) :=
  Subtype.ext (LinearMap.congr_fun g.map_d (x : X.M)).symm

/-- A homomorphism of differential graded modules takes degree-`n` cocycles to degree-`n`
cocycles. -/
def gradedCocyclesMap (g : X ⟶ Y) (n : ℤ) :
    X.gradedCocycles n →ₗ[R] Y.gradedCocycles n :=
  ((g.gradedMap n).comp (X.gradedCocycles n).subtype).codRestrict _ fun c => by
    rw [mem_gradedCocycles, LinearMap.comp_apply, Submodule.coe_subtype,
      gradedMap_gradedDifferential]
    simpa using congrArg (g.gradedMap (n + 1)) (mem_gradedCocycles.1 c.2)

/-- The map induced on cocycles is the degreewise map. -/
@[simp] theorem gradedCocyclesMap_val (g : X ⟶ Y) (n : ℤ) (c : X.gradedCocycles n) :
    (gradedCocyclesMap g n c : Y.grading n) = g.gradedMap n (c : X.grading n) := rfl

/-- The map induced on cocycles is compatible with the differential into the cocycles. -/
theorem gradedCocyclesMap_gradedToCocycles (g : X ⟶ Y) {i n : ℤ} (h : i + 1 = n) :
    (gradedCocyclesMap g n).comp (X.gradedToCocycles h) =
      (Y.gradedToCocycles h).comp (g.gradedMap i) := by
  subst h
  refine LinearMap.ext fun x => Subtype.ext (Subtype.ext ?_)
  exact LinearMap.congr_fun g.map_d (x : X.M)

/-- The map induced on cocycles takes coboundaries to coboundaries. -/
theorem gradedCoboundaries_le_comap (g : X ⟶ Y) (n : ℤ) :
    X.gradedCoboundaries n ≤ (Y.gradedCoboundaries n).comap (gradedCocyclesMap g n) := by
  rintro c ⟨x, rfl⟩
  exact ⟨g.gradedMap (n - 1) x,
    (LinearMap.congr_fun (gradedCocyclesMap_gradedToCocycles g (show n - 1 + 1 = n by omega))
      x).symm⟩

/-- The map induced on the explicit degree-`n` cohomology by a homomorphism of differential graded
modules. -/
def gradedCohomologyMap (g : X ⟶ Y) (n : ℤ) :
    (X.gradedCocycles n ⧸ X.gradedCoboundaries n) →ₗ[R]
      (Y.gradedCocycles n ⧸ Y.gradedCoboundaries n) :=
  Submodule.mapQ _ _ (gradedCocyclesMap g n) (gradedCoboundaries_le_comap g n)

/-- The induced map on cohomology takes the class of a cocycle to the class of its image. -/
@[simp] theorem gradedCohomologyMap_mk (g : X ⟶ Y) (n : ℤ) (c : X.gradedCocycles n) :
    gradedCohomologyMap g n (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (gradedCocyclesMap g n c) := rfl

/-! ### The identification of the cycles, pinned down -/

/-- The comparison of three consecutive terms of the underlying cochain complex with the explicit
short complex is the identity in the middle degree. -/
theorem gradedScIso_inv_τ₂ (X : DifferentialGradedModule A) {i n : ℤ} (h : i + 1 = n) :
    (X.gradedScIso h).inv.τ₂ = 𝟙 _ := by
  subst h; rfl

/-- The inclusion of the explicit left homology datum of the degree-`n` part of the underlying
cochain complex is the inclusion of the degree-`n` cocycles. -/
theorem gradedLeftHomologyData_i (X : DifferentialGradedModule A) (n : ℤ) :
    (X.gradedLeftHomologyData n).i = ModuleCat.ofHom (X.gradedCocycles n).subtype :=
  (congrArg
      (fun t => (X.gradedSc (show n - 1 + 1 = n by omega)).moduleCatLeftHomologyData.i ≫ t)
      (gradedScIso_inv_τ₂ X (show n - 1 + 1 = n by omega))).trans (Category.comp_id _)

/-- **The identification of the cycles is the canonical one.** The degree-`n` cycles of the
underlying cochain complex are identified with the degree-`n` cocycles compatibly with the two
inclusions into the degree-`n` homogeneous component; since those inclusions are monomorphisms,
this determines the identification. -/
theorem gradedCyclesIso_hom_subtype (X : DifferentialGradedModule A) (n : ℤ) :
    (X.gradedCyclesIso n).hom ≫ ModuleCat.ofHom (X.gradedCocycles n).subtype =
      ((forgetToCochainComplex A).obj X).iCycles n := by
  have h1 := (X.gradedLeftHomologyData n).cyclesIso_hom_comp_i
  have h2 := ((forgetToCochainComplex A).obj X).cyclesIsoSc'_hom_iCycles (n - 1) n (n + 1)
    (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)
  have key : (X.gradedCyclesIso n).hom ≫ (X.gradedLeftHomologyData n).i =
      ((forgetToCochainComplex A).obj X).iCycles n :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => _ ≫ t) h1).trans h2)
  exact (congrArg (fun t => (X.gradedCyclesIso n).hom ≫ t)
    (gradedLeftHomologyData_i X n).symm).trans key

/-! ### Naturality -/

/-- Reading a cocycle of the source as a homogeneous element and then mapping it forward is
mapping it forward and then reading it as a homogeneous element. -/
theorem ofHom_gradedCocyclesMap_comp_subtype (g : X ⟶ Y) (n : ℤ) :
    ModuleCat.ofHom (gradedCocyclesMap g n) ≫
        ModuleCat.ofHom (Y.gradedCocycles n).subtype =
      ModuleCat.ofHom (X.gradedCocycles n).subtype ≫
        ((forgetToCochainComplex A).map g).f n := rfl

/-- **The identification of the cycles with the cocycles is natural.** -/
theorem gradedCyclesIso_naturality (g : X ⟶ Y) (n : ℤ) :
    HomologicalComplex.cyclesMap ((forgetToCochainComplex A).map g) n ≫
        (Y.gradedCyclesIso n).hom =
      (X.gradedCyclesIso n).hom ≫ ModuleCat.ofHom (gradedCocyclesMap g n) := by
  have hmono : CategoryTheory.Mono (ModuleCat.ofHom (Y.gradedCocycles n).subtype) :=
    (ModuleCat.mono_iff_injective _).2 (Y.gradedCocycles n).injective_subtype
  refine (cancel_mono (ModuleCat.ofHom (Y.gradedCocycles n).subtype)).1 ?_
  rw [Category.assoc, Category.assoc, ofHom_gradedCocyclesMap_comp_subtype,
    gradedCyclesIso_hom_subtype]
  erw [← Category.assoc, gradedCyclesIso_hom_subtype]
  exact HomologicalComplex.cyclesMap_i _ _

/-- The induced map on cocycles is compatible with the two quotient maps onto the explicit
cohomology. -/
theorem ofHom_gradedCocyclesMap_comp_mkQ (g : X ⟶ Y) (n : ℤ) :
    ModuleCat.ofHom (gradedCocyclesMap g n) ≫
        ModuleCat.ofHom (Y.gradedCoboundaries n).mkQ =
      ModuleCat.ofHom (X.gradedCoboundaries n).mkQ ≫
        ModuleCat.ofHom (gradedCohomologyMap g n) := rfl

/-- **The explicit degree-`n` cohomology is natural.** The identification of the homology of the
underlying cochain complex with cocycles modulo coboundaries commutes with the maps induced by a
homomorphism of differential graded modules. -/
theorem gradedCohomologyIso_naturality (g : X ⟶ Y) (n : ℤ) :
    HomologicalComplex.homologyMap ((forgetToCochainComplex A).map g) n ≫
        (Y.gradedCohomologyIso n).hom =
      (X.gradedCohomologyIso n).hom ≫ ModuleCat.ofHom (gradedCohomologyMap g n) := by
  refine (cancel_epi (((forgetToCochainComplex A).obj X).homologyπ n)).1 ?_
  have e1 : ((forgetToCochainComplex A).obj X).homologyπ n ≫
        (HomologicalComplex.homologyMap ((forgetToCochainComplex A).map g) n ≫
          (Y.gradedCohomologyIso n).hom) =
      (HomologicalComplex.cyclesMap ((forgetToCochainComplex A).map g) n ≫
        (Y.gradedCyclesIso n).hom) ≫ ModuleCat.ofHom (Y.gradedCoboundaries n).mkQ := by
    rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc]
    exact (congrArg _ (homologyπ_gradedCohomologyIso_hom Y n)).trans (Category.assoc _ _ _).symm
  have e2 : ((forgetToCochainComplex A).obj X).homologyπ n ≫
        ((X.gradedCohomologyIso n).hom ≫ ModuleCat.ofHom (gradedCohomologyMap g n)) =
      ((X.gradedCyclesIso n).hom ≫ ModuleCat.ofHom (gradedCocyclesMap g n)) ≫
        ModuleCat.ofHom (Y.gradedCoboundaries n).mkQ := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => t ≫ ModuleCat.ofHom (gradedCohomologyMap g n))
      (homologyπ_gradedCohomologyIso_hom X n)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun t => (X.gradedCyclesIso n).hom ≫ t)
      (ofHom_gradedCocyclesMap_comp_mkQ g n).symm).trans ?_
    exact (Category.assoc _ _ _).symm
  refine e1.trans (e2.trans ?_).symm
  exact congrArg (fun t => t ≫ ModuleCat.ofHom (Y.gradedCoboundaries n).mkQ)
    (gradedCyclesIso_naturality g n).symm

/-! ### The explicit cohomology functor -/

/-- The degree-`n` cohomology of a right differential graded `A`-module, as a functor to
`R`-modules computed by the explicit quotient of cocycles by coboundaries. -/
def gradedCohomologyFunctor (A : DifferentialGradedAlgebra R) (n : ℤ) :
    DifferentialGradedModule A ⥤ ModuleCat.{u} R where
  obj X := X.gradedCohomology n
  map g := ModuleCat.ofHom (gradedCohomologyMap g n)
  map_id X := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    induction z using Submodule.Quotient.induction_on with
    | H c => exact congrArg Submodule.Quotient.mk (Subtype.ext (Subtype.ext rfl))
  map_comp g h := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    induction z using Submodule.Quotient.induction_on with
    | H c => exact congrArg Submodule.Quotient.mk (Subtype.ext (Subtype.ext rfl))

/-- **The explicit cohomology computes the cohomology of the underlying cochain complex,
naturally.** -/
def gradedCohomologyFunctorIso (A : DifferentialGradedAlgebra R) (n : ℤ) :
    forgetToCochainComplex A ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n ≅
      gradedCohomologyFunctor A n :=
  NatIso.ofComponents (fun X => X.gradedCohomologyIso n)
    fun g => gradedCohomologyIso_naturality g n

end DifferentialGradedModule

end
