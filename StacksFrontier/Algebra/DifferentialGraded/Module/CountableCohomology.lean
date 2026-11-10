module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.Algebra.DifferentialGraded.Cohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.CompactFiniteCellFiltration
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomCohomologyNatural
public import StacksFrontier.Algebra.DifferentialGraded.Module.LongExactSequence

/-!
# Countable cohomology of a differential graded module

Let `(A, d)` be a differential graded algebra over a commutative ring `R` whose cohomology
`H^k(A)` is countable in every degree. This file proves that a differential graded `A`-module
carrying a *finite cell filtration* — a finite filtration by differential graded submodules whose
successive quotients are finite direct sums of shifts of `A` — has countable cohomology in every
degree.

The argument is a dévissage along the filtration. The base case is a shift `A[k]` of the algebra,
whose degree-`n` cohomology is `H^{n + k}(A)`; finite direct sums are handled by additivity of
cohomology; and the inductive step is the long exact cohomology sequence of Tag 09JK, in which the
middle term of an exact sequence of countable modules is countable.

## Main definitions

* `DifferentialGradedModule.HasCountableCohomology`: all cohomology modules of a differential
  graded module are countable.

## Main results

* `CategoryTheory.ShortComplex.countable_X₂`: the middle term of an exact sequence of modules
  whose outer terms are countable is countable.
* `DirectSum.countable`: a direct sum of countably many countable modules is countable.
* `DifferentialGradedModule.HasCountableCohomology.of_shortExact`: countability of cohomology
  passes to the middle term of a short exact sequence.
* `DifferentialGradedModule.hasCountableCohomology_shift_regularModule`: a shift of the algebra
  has countable cohomology as soon as the algebra does.
* `DifferentialGradedModule.HasCountableCohomology.of_hasFiniteCellFiltration`: a module with a
  finite cell filtration has countable cohomology.

## Implementation notes

Countability is Mathlib's `Countable` typeclass on the carrier of a module, so a statement about a
`ModuleCat` object is a statement about its underlying type; it transfers along an isomorphism of
`ModuleCat` because an isomorphism is injective on carriers.

Exactness of a three-term sequence `M₁ → M₂ → M₃` of modules bounds `M₂` by `M₃` and by the image
of `M₁`: a set-theoretic section of the second map over its range, chosen with `Classical.choice`,
turns an element of `M₂` into the pair of its image and its correction term in that image, and the
pair determines it. No linearity of the section is needed, which is why the statement is about
countability of carriers and not about the modules.

The dévissage is run on the cohomology of the *underlying cochain complex*, since that is what the
long exact sequence of Tag 09JK computes, and transported to the explicit cohomology
`DifferentialGradedModule.gradedCohomology` once, by
`DifferentialGradedModule.gradedCohomologyIso`.

## References

* [Stacks Project, Tag 09JK](https://stacks.math.columbia.edu/tag/09JK) for the long exact
  cohomology sequence, and [Tag 09R2](https://stacks.math.columbia.edu/tag/09R2) for finite cell
  filtrations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ShortComplex

/-- **The middle term of an exact sequence of countable modules is countable.** If
`M₁ → M₂ → M₃` is exact at `M₂` and `M₁` and `M₃` are countable, then so is `M₂`: an element of
`M₂` is determined by its image in `M₃` together with its difference from a chosen preimage of
that image, and that difference lies in the image of `M₁`. -/
theorem countable_X₂ {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact)
    [Countable S.X₁] [Countable S.X₃] : Countable S.X₂ := by
  classical
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range] at hS
  set g := S.g.hom
  set f := S.f.hom
  have hsec : ∀ x : S.X₂, g (Function.invFun g (g x)) = g x := fun x =>
    Function.invFun_eq ⟨x, rfl⟩
  have hmem : ∀ x : S.X₂, x - Function.invFun g (g x) ∈ Set.range f := fun x =>
    hS (by simp only [LinearMap.mem_ker, map_sub, hsec x, sub_self])
  have hrange : Countable (Set.range f) := Set.countable_range f
  refine Function.Injective.countable
    (f := fun x : S.X₂ => (g x, (⟨x - Function.invFun g (g x), hmem x⟩ : Set.range f))) ?_
  intro x y hxy
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
  obtain ⟨h₁, h₂⟩ := hxy
  rw [h₁] at h₂
  exact sub_left_inj.mp h₂

end CategoryTheory.ShortComplex

namespace DirectSum

/-- **A direct sum of countably many countable modules is countable.** An element of the direct
sum is determined by its support, a finite subset of the countable index type, together with its
values there. -/
theorem countable {ι : Type*} [Countable ι] {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
    [∀ i, Countable (β i)] : Countable (⨁ i, β i) := by
  classical
  have key : ∀ (x : ⨁ i, β i) (i : ι) (v : β i),
      (⟨i, v⟩ : Σ j, β j) ∈ (DFinsupp.support x).image (fun j => (⟨j, x j⟩ : Σ k, β k)) →
        v = x i := by
    intro x i v hv
    simp only [Finset.mem_image, Sigma.mk.injEq] at hv
    obtain ⟨j, -, rfl, hv⟩ := hv
    exact (eq_of_heq hv).symm
  refine Function.Injective.countable
    (f := fun x : ⨁ i, β i => (DFinsupp.support x).image (fun j => (⟨j, x j⟩ : Σ k, β k))) ?_
  intro x y hxy
  have h : ∀ x y : ⨁ i, β i, (DFinsupp.support x).image (fun j => (⟨j, x j⟩ : Σ k, β k)) =
      (DFinsupp.support y).image (fun j => (⟨j, y j⟩ : Σ k, β k)) → ∀ i, x i ≠ 0 → x i = y i :=
    fun x y hxy i hx => key y i (x i) (by
      rw [← hxy]
      exact Finset.mem_image_of_mem _ (DFinsupp.mem_support_iff.mpr hx))
  refine DFinsupp.ext fun i => ?_
  by_cases hx : x i = 0
  · by_cases hy : y i = 0
    · rw [hx, hy]
    · exact (h y x hxy.symm i hy).symm
  · exact h x y hxy i hx

end DirectSum

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R)

/-- Countability transfers along an isomorphism of `R`-modules: an isomorphism is injective on
carriers. -/
theorem countable_of_iso {X Y : ModuleCat.{u} R} (e : X ≅ Y) [Countable X] : Countable Y :=
  Function.Injective.countable (f := e.toLinearEquiv.symm) e.toLinearEquiv.symm.injective

/-- The cohomology of the underlying cochain complex is countable exactly when the explicit
cohomology is. -/
theorem countable_homology_iff_gradedCohomology (X : DifferentialGradedModule.{u, u, u} A)
    (n : ℤ) :
    Countable (((forgetToCochainComplex A).obj X).homology n) ↔
      Countable (X.gradedCohomology n) :=
  ⟨fun _ => countable_of_iso (X.gradedCohomologyIso n),
   fun _ => countable_of_iso (X.gradedCohomologyIso n).symm⟩

/-- Cohomology in degree `n` is an additive functor on differential graded modules: it is
isomorphic to the homology of the underlying cochain complex, and both the forgetful functor and
homology are additive. -/
instance gradedCohomologyFunctor_additive (n : ℤ) : (gradedCohomologyFunctor A n).Additive :=
  Functor.additive_of_iso (gradedCohomologyFunctorIso A n)

/-- A differential graded module **has countable cohomology** when all of its cohomology modules
are countable. -/
def HasCountableCohomology (X : DifferentialGradedModule.{u, u, u} A) : Prop :=
  ∀ n : ℤ, Countable (X.gradedCohomology n)

/-- Countability of cohomology passes to the middle term of a short exact sequence of differential
graded modules, by the long exact cohomology sequence of Tag 09JK. -/
theorem HasCountableCohomology.of_shortExact
    {S : ShortComplex (DifferentialGradedModule.{u, u, u} A)}
    (hS : S.ShortExact) (h₁ : HasCountableCohomology A S.X₁)
    (h₃ : HasCountableCohomology A S.X₃) : HasCountableCohomology A S.X₂ := by
  intro n
  have hSE := shortExact_forgetToCochainComplex A S hS
  have hLES := longExactCohomology A S hS n (n + 1) (by simp)
  have hexact : ((S.map (forgetToCochainComplex A)).map
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n)).Exact := by
    change ((HomologicalComplex.HomologySequence.composableArrows₅ hSE n (n + 1) (by simp)).sc
      hLES.toIsComplex 0 (by omega)).Exact
    exact hLES.exact 0
  exact (countable_homology_iff_gradedCohomology A S.X₂ n).1
    (@ShortComplex.countable_X₂ _ _ _ hexact
      ((countable_homology_iff_gradedCohomology A S.X₁ n).2 (h₁ n))
      ((countable_homology_iff_gradedCohomology A S.X₃ n).2 (h₃ n)))

/-! ### The base case: shifts of the algebra -/

/-- **Degree-`n` cohomology of a `k`-fold shift is degree-`(k + n)` cohomology.** The underlying
cochain complex of a shifted differential graded module is the shift of its underlying cochain
complex, and the shift sequence of homology reindexes the degree. -/
def gradedCohomologyShiftIso (M : DifferentialGradedModule.{u, u, u} A) (k n : ℤ) :
    (shift M k).gradedCohomology n ≅ M.gradedCohomology (k + n) :=
  ((shift M k).gradedCohomologyIso n).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).mapIso
      (dgShiftToCochainShiftIso A M k) ≪≫
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).shiftIso
      k n (k + n) rfl).app ((forgetToCochainComplex A).obj M) ≪≫
    M.gradedCohomologyIso (k + n)

/-- A degree-`m` cocycle of the algebra, read as a degree-`m` cocycle of the regular module: the
regular module is the algebra with its own grading and differential. -/
def regularCocycleOfCocycle (m : ℤ) (a : A.Cocycle m) :
    (regularModule A).gradedCocycles m :=
  ⟨a.1, Subtype.ext a.2⟩

/-- Every degree-`m` cocycle of the regular module comes from a degree-`m` cocycle of the
algebra. -/
theorem regularCocycleOfCocycle_surjective (m : ℤ) :
    Function.Surjective (regularCocycleOfCocycle A m) := fun x =>
  ⟨⟨x.1, congrArg Subtype.val x.2⟩, rfl⟩

/-- The degree-`m` cohomology of the algebra maps onto the degree-`m` cohomology of the regular
module; the two are in fact equal, but surjectivity is all that countability needs. -/
def regularCohomologyMap (m : ℤ) :
    A.Cohomology m → (regularModule A).gradedCohomology m :=
  Quotient.lift
    (fun a => (Submodule.Quotient.mk (regularCocycleOfCocycle A m a) :
      (regularModule A).gradedCocycles m ⧸ (regularModule A).gradedCoboundaries m))
    (by
      rintro a b ⟨c, hc⟩
      refine (Submodule.Quotient.eq _).mpr ?_
      rw [mem_gradedCoboundaries]
      exact ⟨c, hc.symm⟩)

/-- The map from the cohomology of the algebra to the cohomology of the regular module is
surjective. -/
theorem regularCohomologyMap_surjective (m : ℤ) :
    Function.Surjective (regularCohomologyMap A m) := by
  intro z
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  obtain ⟨a, rfl⟩ := regularCocycleOfCocycle_surjective A m x
  exact ⟨Quotient.mk _ a, rfl⟩

/-! ### Stability properties of countable cohomology -/

/-- Countability of cohomology is invariant under isomorphism. -/
theorem HasCountableCohomology.of_iso {X Y : DifferentialGradedModule.{u, u, u} A} (e : X ≅ Y)
    (h : HasCountableCohomology A X) : HasCountableCohomology A Y := fun n => by
  have : Countable ((gradedCohomologyFunctor A n).obj X) := h n
  exact countable_of_iso ((gradedCohomologyFunctor A n).mapIso e)

/-- A zero differential graded module has countable cohomology. -/
theorem HasCountableCohomology.of_isZero {X : DifferentialGradedModule.{u, u, u} A}
    (h : IsZero X) : HasCountableCohomology A X := by
  have hX : ∀ x : X.M, x = 0 := fun x =>
    congrArg (fun k : X ⟶ X => k.toFun x) (h.eq_of_src (𝟙 X) 0)
  intro n
  have : Subsingleton (X.gradedCocycles n) :=
    ⟨fun _ _ => Subtype.ext (Subtype.ext ((hX _).trans (hX _).symm))⟩
  have : Subsingleton (X.gradedCohomology n) := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep a
    obtain ⟨y, rfl⟩ := Quotient.exists_rep b
    rw [Subsingleton.elim x y]⟩
  infer_instance

/-- A shift of the algebra has countable cohomology as soon as the algebra does: the degree-`n`
cohomology of `A[k]` is `H^{k + n}(A)`. -/
theorem hasCountableCohomology_shift_regularModule
    (hA : ∀ m : ℤ, Countable (A.Cohomology m)) (k : ℤ) :
    HasCountableCohomology A (shift (regularModule A) k) := by
  intro n
  have := hA (k + n)
  have := (regularCohomologyMap_surjective A (k + n)).countable
  exact countable_of_iso (gradedCohomologyShiftIso A (regularModule A) k n).symm

/-! ### Finite direct sums -/

/-- Countability of cohomology is stable under finite direct sums. A finite direct sum is a
biproduct, and cohomology, being additive, carries the identity `∑ⱼ πⱼ ≫ ιⱼ = 1` of the biproduct
to the same identity; so the map from the cohomology of the direct sum to the product of the
cohomologies of the summands is a split monomorphism. -/
theorem HasCountableCohomology.of_coproduct {J : Type u} [Finite J]
    (X : J → DifferentialGradedModule.{u, u, u} A) [Limits.HasCoproduct X]
    (h : ∀ j, HasCountableCohomology A (X j)) : HasCountableCohomology A (∐ X) := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have : Limits.HasBiproduct X := Limits.HasBiproduct.of_hasCoproduct X
  suffices hb : HasCountableCohomology A (⨁ X) from hb.of_iso A (Limits.biproduct.isoCoproduct X)
  intro n
  set F := gradedCohomologyFunctor A n
  have hcount : ∀ j, Countable (F.obj (X j)) := fun j => h j n
  have hpi := countable_of_iso (ModuleCat.piIsoPi (fun j => F.obj (X j))).symm
  have hsplit : (Limits.Pi.lift fun j => F.map (Limits.biproduct.π X j)) ≫
      (∑ j : J, Limits.Pi.π (fun j => F.obj (X j)) j ≫ F.map (Limits.biproduct.ι X j)) =
      𝟙 (F.obj (⨁ X)) := by
    rw [Preadditive.comp_sum]
    have hterm : ∀ j : J, (Limits.Pi.lift fun j => F.map (Limits.biproduct.π X j)) ≫
        Limits.Pi.π (fun j => F.obj (X j)) j ≫ F.map (Limits.biproduct.ι X j) =
        F.map (Limits.biproduct.π X j ≫ Limits.biproduct.ι X j) := by
      intro j
      rw [F.map_comp, ← Category.assoc, Limits.Pi.lift_comp_π]
    rw [Finset.sum_congr rfl fun j _ => hterm j, ← F.map_sum,
      Limits.IsBilimit.total (Limits.biproduct.isBilimit X), F.map_id]
  exact ((ModuleCat.mono_iff_injective _).1 (mono_of_mono_fac hsplit)).countable

/-! ### Modules with a finite cell filtration -/

/-- **A differential graded module with a finite cell filtration has countable cohomology**, as
soon as the algebra does. The filtration begins at a zero module and its steps have cokernels
finite direct sums of shifts of the algebra, so the long exact cohomology sequence propagates
countability up the filtration, and its top step is the module itself. -/
theorem HasCountableCohomology.of_hasFiniteCellFiltration
    (hA : ∀ m : ℤ, Countable (A.Cohomology m))
    {P : DifferentialGradedModule.{u, u, u} A} (hP : HasFiniteCellFiltration P) :
    HasCountableCohomology A P := by
  obtain ⟨m, F, hzero, htop, hq⟩ := hP
  have key : ∀ i : ℕ, i ≤ m + 1 → HasCountableCohomology A (F.obj i) := by
    intro i
    induction i with
    | zero => exact fun _ => HasCountableCohomology.of_isZero A hzero
    | succ i ih =>
      intro hi
      obtain ⟨J, hJ, k, ⟨e⟩⟩ := hq ⟨i, by omega⟩
      have hcok : HasCountableCohomology A
          (Limits.cokernel (F.diagram.map (homOfLE (Nat.le_succ i)))) :=
        (HasCountableCohomology.of_coproduct A _
          fun j => hasCountableCohomology_shift_regularModule A hA (k j)).of_iso A e.symm
      exact HasCountableCohomology.of_shortExact A
        (ShortComplex.ShortExact.mk'
          (ShortComplex.cokernelSequence_exact (F.diagram.map (homOfLE (Nat.le_succ i))))
          (inferInstanceAs (Mono (F.diagram.map (homOfLE (Nat.le_succ i))))) inferInstance)
        (ih (by omega)) hcok
  exact (key (m + 1) le_rfl).of_iso A (asIso (F.ι.app (m + 1)))

end DifferentialGradedModule

end
