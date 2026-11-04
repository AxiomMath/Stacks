module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologySingleTor
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleShiftHomologyIso

/-!
# The base-change cohomology of a module in an arbitrary degree

Let `R → A` and `R → R'` be homomorphisms of commutative rings and let `M` be an `A`-module.
`RingTheory.TorIndependence.baseChangeCohomologySingleIsoTor` identifies
`H^{-i}(M[0] ⊗ᴸ_R R')` with `Tor_i^R(R', M)`; this file moves that identification to `M` placed
in an arbitrary degree `d`,

`H^n(M[d] ⊗ᴸ_R R')  ≅  Tor_{d-n}^R(R', M)`   for `n ≤ d`,

and records that the left-hand side vanishes for `n > d`. That is what a dévissage along the
compact generator `A[0]` of `D(A)` asks for: the shifts `A[0]⟦m⟧` of the generator are the
regular module in the degrees `-m`, so a hypothesis at every shift of `A[0]` is a hypothesis
about `A` in every degree, in one fixed cohomological degree `n`.

## Main definitions

* `RingTheory.TorIndependence.baseChangeCohomologySingleDegreeIsoTor`: the displayed
  isomorphism, naturally in `M`.

## Main results

* `RingTheory.TorIndependence.baseChangeCohomologySingleDegreeIsoTor_includeLeft_smul`: the
  isomorphism carries the action of the left tensor factor `A` of `A ⊗_R R'` to functoriality of
  `Tor_i^R(R', ·)` in its second variable.
* `RingTheory.TorIndependence.isZero_baseChangeCohomologyOverBase_single_of_lt`: above the
  degree of the module the base-change cohomology vanishes.

## Implementation notes

The degree is moved by `DerivedCategory.singleCompHomologyShiftIso`: the module in degree `d` is
the module in degree zero shifted by `-d`, the shift passes through the derived base change —
which commutes with it, being a composite of two shift-commuting functors — and the shift
sequence of `H^0` turns `H^n` of a complex shifted by `-d` into `H^{n-d}`. The `A`-linearity is
then naturality of that isomorphism at `a • 𝟙 M`, exactly as at `d = 0`: the functor placing a
module in degree `d` is `A`-linear, so it carries `a • 𝟙 M` to `a • 𝟙 (M[d])`, which is what
`RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul` says the action of
`Algebra.TensorProduct.includeLeft a` is.

The vanishing is the `t`-structure estimate: `M[d]` is in `D^{≤ d}(A)`, restriction of scalars
carries it to `(M|_R)[d]`, derived extension of scalars preserves `D^{≤ d}` by
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.maps_t_le`, and a complex
in `D^{≤ d}` has no cohomology above `d`.

The model of the derived category is a binder `[HasDerivedCategory.{w} (ModuleCat.{u} ·)]` for
each of the three rings, not `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u w

namespace RingTheory.TorIndependence

/-! ### The derived base change commutes with the shift -/

section CommShift

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- **The derived base change commutes with the shift.** Restriction of scalars does, being the
derived functor of an exact functor, and derived extension of scalars does by
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.commShift`. -/
instance commShift_derivedBaseChangeFunctor :
    (derivedBaseChangeFunctor (R := R) (A := A) (R' := R')).CommShift ℤ := by
  let _ := (totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).commShift
  exact inferInstanceAs
    (((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙
      (totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).functor).CommShift ℤ)

end CommShift

/-! ### The bridge in an arbitrary degree -/

section SingleDegree

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- **The bridge at an `A`-module in degree `d`.** For `M` an `A`-module and `n + i = d`,

`H^n(M[d] ⊗ᴸ_R R') ≅ Tor_i^R(R', M)`,

naturally in `M`, both sides read over `R`. -/
def baseChangeCohomologySingleDegreeIsoTor (d n : ℤ) (i : ℕ) (h : n + (i : ℤ) = d) :
    DerivedCategory.singleFunctor (ModuleCat.{u} A) d ⋙
        derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R') n ⋙
            ModuleCat.restrictScalars.{u, u, u} (algebraMap R R') ≅
      ModuleCat.restrictScalars.{u, u, u} (algebraMap R A) ⋙
        (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R') :=
  Functor.isoWhiskerRight
      (DerivedCategory.singleCompHomologyShiftIso
        (derivedBaseChangeFunctor (R := R) (A := A) (R' := R')) d n (-(i : ℤ)) (by omega))
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')) ≪≫
    baseChangeCohomologySingleIsoTor (R := R) (A := A) (R' := R') i

/-- **The left tensor factor acts by functoriality of `Tor` in its second variable**, in every
degree. -/
theorem baseChangeCohomologySingleDegreeIsoTor_includeLeft_smul (d n : ℤ) (i : ℕ)
    (h : n + (i : ℤ) = d) (M : ModuleCat.{u} A) (a : A)
    (m : baseChangeCohomology (R := R) (R' := R')
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj M) n) :
    ((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app M).hom
        ((Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m) =
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
          ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).map (a • 𝟙 M))).hom
        (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app
          M).hom m) := by
  have hs : (DerivedCategory.singleFunctor (ModuleCat.{u} A) d).map (a • 𝟙 M) =
      a • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj M) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have hnat0 := (baseChangeCohomologySingleDegreeIsoTor
    (R := R) (A := A) (R' := R') d n i h).hom.naturality (a • 𝟙 M)
  dsimp only [Functor.comp_map] at hnat0
  rw [hs] at hnat0
  have hnat := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hnat0) m
  exact (congrArg _ (baseChangeCohomology_includeLeft_smul (R := R) (R' := R')
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj M) n a m)).trans hnat

/-- **A module in degree `d`, restricted to the base, is that module in degree `d`.** -/
theorem isLE_derivedBaseChange_single (d : ℤ) (M : ModuleCat.{u} A) :
    ((derivedBaseChangeFunctor (R := R) (A := A) (R' := R')).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj M)).IsLE d := by
  have hres : ((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj M)).IsLE d := by
    rw [DerivedCategory.isLE_iff]
    intro j hj
    refine IsZero.of_iso (DerivedCategory.isZero_of_isLE
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) d).obj
        ((ModuleCat.restrictScalars.{u} (algebraMap R A)).obj M)) d j hj) ?_
    exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).mapIso
      (((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategorySingleFunctor d).app M)
  exact (totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).maps_t_le _ d

/-- **Above the degree of the module the base-change cohomology vanishes.** -/
theorem isZero_baseChangeCohomologyOverBase_single_of_lt (d n : ℤ) (hdn : d < n)
    (M : ModuleCat.{u} A) :
    IsZero (baseChangeCohomologyOverBase (R := R) (R' := R')
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj M) n) := by
  have := isLE_derivedBaseChange_single (R := R) (A := A) (R' := R') d M
  exact DerivedCategory.isZero_of_isLE
    ((derivedBaseChangeFunctor (R := R) (A := A) (R' := R')).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj M)) d n hdn

end SingleDegree

end RingTheory.TorIndependence

end
