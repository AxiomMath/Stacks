module

public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclic
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclicGeneral
public import StacksFrontier.Algebra.DifferentialGraded.Module.OrthogonalAcyclic
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP
public import StacksFrontier.Algebra.DifferentialGraded.Telescope
public import StacksCore.Tactic.StacksAttribute

/-! # Dévissage of the derived category from the shifts of the algebra

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. A property `T` of the
objects of the derived category `D(A, d)` which

1. holds for a direct sum as soon as it holds for every summand,
2. holds for the third object of a distinguished triangle as soon as it holds for two of them,
3. holds for every shift `A[k]` of the algebra,

holds for *every* object of `D(A, d)`.

An arbitrary object of `D(A, d)` is isomorphic to the
image of a differential graded module, which receives a quasi-isomorphism from a module `P`
carrying a property-(P) filtration `F_0 ⊆ F_1 ⊆ ⋯` (Tag 09KP). The bottom stage and all the
successive quotients are direct sums of shifts of `A`, so (1) and (3) give `T` on every stage by
induction along the admissible short exact sequences `0 → F_i → F_{i+1} → F_{i+1}/F_i → 0`. The
telescope of Tag 09KL then presents `P` as the third term of an admissible short exact sequence
whose two outer terms are the direct sum `⨁_i F_i`, so (1) and (2) carry `T` to `P` and hence to
the object one started from.

## Main definitions

* `DifferentialGradedModule.directSumObjIsoSigma`: the explicit direct sum of a family of
  differential graded modules is the chosen coproduct of the family.
* `DifferentialGradedModule.uliftDirectSumIso`: a direct sum over `ℕ` is the direct sum of the
  universe-lifted family over `ULift.{u} ℕ`.
* `DifferentialGradedModule.directSumObjIsoDirectSumShifts`: the explicit direct sum of the
  shifts `A[kᵢ]` is `DifferentialGradedModule.directSumShifts`.

## Main results

* `DifferentialGradedModule.hasCoproducts_derivedCategory`: `D(A, d)` has arbitrary direct sums.
* `DifferentialGradedModule.exists_propertyP_telescope`: the telescope of Tag 09KL in the bundled
  encoding — every differential graded module receives a quasi-isomorphism from a module `P` with
  a property-(P) filtration which is the quotient term of an admissible short exact sequence
  whose outer terms are the direct sum of the stages of that filtration.
* `DifferentialGradedModule.property_of_coproducts_of_two_out_of_three_of_shifts`: the dévissage,
  for an algebra whose carrier lies in the universe of the base ring.
* `DifferentialGradedModule.General.property_of_coproducts_of_two_out_of_three_of_shifts`: the
  dévissage with the carrier of the algebra in a universe of its own, independent of the universe
  of the base ring.

## Implementation notes

The first half of the file takes the base ring, the carrier of the algebra and the carriers of
the modules in one universe `u`. The index type of a direct sum of differential graded modules
then lies in `Type u`, and the `ℕ`-indexed direct sum of the stages of a property-(P) filtration
is reindexed along `Equiv.ulift : ULift.{u} ℕ ≃ ℕ` (`DifferentialGradedModule.uliftDirectSumIso`).

The namespace `DifferentialGradedModule.General` has the base ring in `Type u` and the carrier of
the algebra, the modules and the index types in `Type v`. Its derived category is
`DifferentialGradedModule.derivedCategory`, with the pretriangulated structure on the homotopy
category whose distinguished triangles are the cone triangles.

The telescope of Tag 09KL and the property-(P) resolution of Tag 09KP are stated for the
unbundled encoding `Stacks.DifferentialGraded.DGAlgebra` / `Stacks.DifferentialGraded.DGModule`;
`DifferentialGradedModule.exists_propertyP_telescope` applies both to the same unbundled
filtration and bundles the results with the conversions of `DifferentialGradedModule.Unbundled`.

The carrier of a bundled direct sum is the bare direct sum `⨁ᵢ …` only up to unfolding at default
transparency, so the elementwise lemmas are stated with their binders at the bare direct sum.

## References

* [Stacks Project, Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE)
* [Stacks Project, Tag 09KL](https://stacks.math.columbia.edu/tag/09KL), the telescope.
* [Stacks Project, Tag 09KP](https://stacks.math.columbia.edu/tag/09KP), property-(P)
  resolutions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum ZeroObject

universe u

namespace DifferentialGradedModule

section SingleUniverse

attribute [local instance 10000] instPretriangulatedHomotopyCategory'

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-! ### Direct sums in the derived category -/

/-- The derived category of a differential graded algebra has arbitrary direct sums. -/
instance hasCoproducts_derivedCategory (A : DifferentialGradedAlgebra R) :
    HasCoproducts.{u} (derivedCategory' A) := by
  refine fun ι => ⟨fun D => ?_⟩
  let Q := (quasiIsomorphisms' A).Q
  let N : ι → DifferentialGradedModule A :=
    fun i => (Q.objPreimage (D.obj (Discrete.mk i))).as
  exact ⟨(hasColimit_of_iso (F := Discrete.functor N ⋙ (toHomotopyCategory A ⋙ Q))
    (Discrete.natIso fun i => Q.objObjPreimageIso (D.obj i)).symm).exists_colimit⟩

/-- The explicit direct sum `⨁ᵢ Nᵢ` of a family of differential graded modules agrees with the
chosen coproduct of the family in `Mod_{(A,d)}`, both being colimits of the same diagram. -/
def directSumObjIsoSigma {ι : Type u} [DecidableEq ι] (N : ι → DifferentialGradedModule A) :
    directSumObj N ≅ ∐ N :=
  (isColimit_directSumObj N).coconePointUniqueUpToIso (coproductIsCoproduct N)

/-! ### Reindexing a direct sum along the universe lift of `ℕ`

A property-(P) filtration is indexed by `ℕ`, while the index type of a direct sum of differential
graded modules must lie in `Type u`, the universe of the modules. The two are reconciled by
reindexing along `Equiv.ulift : ULift.{u} ℕ ≃ ℕ`, which on a direct sum of modules is
`DirectSum.lequivCongrLeft`; the grading, the right action and the differential of a direct sum
being componentwise, the reindexing respects all three. -/

section Ulift

variable {X : ℕ → Stacks.DifferentialGraded.DGModule (Unbundled.algebra A)}

/-- The reindexing linear equivalence `⨁_{j : ULift.{u} ℕ} X_{j.down} ≃ ⨁_{i : ℕ} X_i`. -/
def uliftDirectSumEquiv (X : ℕ → Stacks.DifferentialGraded.DGModule (Unbundled.algebra A)) :
    (⨁ j : ULift.{u} ℕ, (X j.down).carrier) ≃ₗ[R] (⨁ i : ℕ, (X i).carrier) :=
  DirectSum.lequivCongrLeft R (Equiv.ulift.{u, 0} (α := ℕ))

/-- The reindexing equivalence reads the `i`-th component off the `ULift.up i`-th one. -/
@[simp] theorem uliftDirectSumEquiv_apply
    (X : ℕ → Stacks.DifferentialGraded.DGModule (Unbundled.algebra A))
    (x : ⨁ j : ULift.{u} ℕ, (X j.down).carrier) (i : ℕ) :
    uliftDirectSumEquiv X x i = x (ULift.up i) :=
  DirectSum.lequivCongrLeft_apply R _ x i

/-- The reindexing equivalence is compatible with the right action of the algebra, which on a
direct sum is componentwise. -/
theorem uliftDirectSumEquiv_smul (X : ℕ → Stacks.DifferentialGraded.DGModule (Unbundled.algebra A))
    (a : A.Aᵐᵒᵖ) (x : ⨁ j : ULift.{u} ℕ, (X j.down).carrier) :
    uliftDirectSumEquiv X (a • x) = a • uliftDirectSumEquiv X x := by
  refine DirectSum.ext fun i => ?_
  rw [uliftDirectSumEquiv_apply, DirectSum.smul_apply, DirectSum.smul_apply,
    uliftDirectSumEquiv_apply]

/-- The reindexing equivalence commutes with the differential of a direct sum, which is
componentwise. -/
theorem uliftDirectSumEquiv_d (X : ℕ → Stacks.DifferentialGraded.DGModule (Unbundled.algebra A))
    (x : ⨁ j : ULift.{u} ℕ, (X j.down).carrier) :
    uliftDirectSumEquiv X
        (Stacks.DifferentialGraded.DGModule.directSumD (fun j : ULift.{u} ℕ => X j.down) x)
      = Stacks.DifferentialGraded.DGModule.directSumD X (uliftDirectSumEquiv X x) := by
  refine DirectSum.ext fun i => ?_
  rw [uliftDirectSumEquiv_apply, DifferentialGraded.NativeCover.Native.directSum_d_apply,
    DifferentialGraded.NativeCover.Native.directSum_d_apply, uliftDirectSumEquiv_apply]

/-- The reindexing of a direct sum of differential graded modules along `ULift.{u} ℕ ≃ ℕ`, as a
homomorphism of differential graded modules. -/
def uliftDirectSumHom (hX : ∀ i, (X i).IsLawful)
    (hS : (Stacks.DifferentialGraded.DGModule.directSum X).IsLawful) :
    directSumObj (fun j : ULift.{u} ℕ => Unbundled.bundle (hX j.down)) ⟶
      Unbundled.bundle hS where
  toFun := (uliftDirectSumEquiv X).toLinearMap
  map_smul x a := uliftDirectSumEquiv_smul X (MulOpposite.op a) x
  map_grading _ _ hx i := hx (ULift.up i)
  map_d := LinearMap.ext (uliftDirectSumEquiv_d X)

/-- A direct sum over `ℕ` is the direct sum of the universe-lifted family over
`ULift.{u} ℕ`. -/
def uliftDirectSumIso (hX : ∀ i, (X i).IsLawful)
    (hS : (Stacks.DifferentialGraded.DGModule.directSum X).IsLawful) :
    Unbundled.bundle hS ≅ directSumObj (fun j : ULift.{u} ℕ => Unbundled.bundle (hX j.down)) :=
  (Hom.isoOfBijective (uliftDirectSumHom hX hS) (uliftDirectSumEquiv X).bijective).symm

end Ulift

/-! ### Direct sums of shifts of the algebra -/

/-- The descent of the coprojections `A[kⱼ] ⟶ ⨁ᵢ A[kᵢ]` of
`DifferentialGradedModule.directSumShifts` along the explicit direct sum is the identity. -/
theorem directSumDescLinear_directSumShiftsInj_apply (A : DifferentialGradedAlgebra R)
    {ι : Type u} [DecidableEq ι] (k : ι → ℤ) (x : ⨁ _ : ι, A.A) :
    directSumDescLinear (fun i => shift (regularModule A) (k i))
      (directSumShiftsInj A k) x = x := by
  induction x using DirectSum.induction_on with
  | zero => exact map_zero _
  | of i y =>
      rw [← DirectSum.lof_eq_of (R := R)]
      exact directSumDescLinear_lof (fun i => shift (regularModule A) (k i))
        (directSumShiftsInj A k) i y
  | add y z hy hz => exact (map_add _ y z).trans (congrArg₂ (· + ·) hy hz)

/-- **The explicit direct sum of the shifts `A[kᵢ]` is
`DifferentialGradedModule.directSumShifts`.** The comparison is the descent of the coprojections
of the latter, whose underlying map is the identity of `⨁ᵢ A`. -/
def directSumObjIsoDirectSumShifts (A : DifferentialGradedAlgebra R)
    {ι : Type u} [DecidableEq ι] (k : ι → ℤ) :
    directSumObj (fun i => shift (regularModule A) (k i)) ≅ directSumShifts A k :=
  Hom.isoOfBijective (directSumDesc _ (directSumShiftsInj A k)) (by
    have hid := directSumDescLinear_directSumShiftsInj_apply A k
    exact ⟨fun a b h => by rwa [← hid a, ← hid b], fun y => ⟨y, hid y⟩⟩)

/-! ### The telescope of a property-(P) resolution -/

/-- **The telescope of a property-(P) resolution** (Tags 09KP and 09KL, in the bundled encoding).
Every differential graded `A`-module `M` receives a quasi-isomorphism `f : P ⟶ M` from a module
`P` carrying a property-(P) filtration `F`, and `P` is the quotient term of an admissible short
exact sequence `0 → S → S → P → 0` whose outer term `S` is the direct sum of the stages of `F`.
The stages are indexed by `ℕ`, so the direct sum is taken over `ULift.{u} ℕ`. -/
theorem exists_propertyP_telescope (A : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule A) :
    ∃ (P S : DifferentialGradedModule A) (f : P ⟶ M) (a : S ⟶ S) (b : S ⟶ P)
      (F : PropertyPFiltration P),
      QuasiIso ((forgetToCochainComplex A).map f) ∧ IsAdmissibleShortExact a b ∧
        Nonempty (S ≅ directSumObj (fun j : ULift.{u} ℕ => F.F j.down)) := by
  obtain ⟨P₀, hP, f₀, hf, ⟨F₀⟩⟩ := Stacks.DifferentialGraded.DGModule.exists_propertyP_resolution
    (Unbundled.algebra A) (Unbundled.algebra_isLawful A)
    (Unbundled.module M) (Unbundled.module_isLawful M)
  obtain ⟨hS, α, β, _, _, hab⟩ :=
    Stacks.DifferentialGraded.DGModule.admissible_ses_of_propertyP hP F₀
  have hX : ∀ i, ((F₀.F i).toDGModule).IsLawful :=
    fun i => Unbundled.dgSubmodule_isLawful hP (F₀.F i) (F₀.F_lawful i)
  refine ⟨Unbundled.bundle hP, Unbundled.bundle hS,
    { toFun := Unbundled.restrictR (N := Unbundled.module M) f₀.toFun
      map_smul := fun x a => f₀.toFun.map_smul (MulOpposite.op a) x
      map_grading := f₀.map_grading
      map_d := LinearMap.ext f₀.commute_d },
    Unbundled.bundleHom hS hS α, Unbundled.bundleHom hS hP β,
    bundleFiltration hP F₀, quasiIso_of_isQuasiIsomorphism _ hf, ?_, ⟨uliftDirectSumIso hX hS⟩⟩
  exact { injective := hab.injective
          surjective := hab.surjective
          exact := Submodule.ext fun x => SetLike.ext_iff.mp hab.exact x
          admissibleMono := ⟨Unbundled.bundleGradedHom hS hS hab.admissibleMono.2.choose,
            hab.admissibleMono.2.choose_spec⟩
          admissibleEpi := ⟨Unbundled.bundleGradedHom hP hS hab.admissibleEpi.2.choose,
            hab.admissibleEpi.2.choose_spec⟩ }

/-! ### The dévissage -/

/-- A property of the objects of a pretriangulated category which satisfies the two-out-of-three
property for distinguished triangles and holds for some object is invariant under isomorphism. -/
private theorem iso_invariant_of_two_out_of_three {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
    [Pretriangulated C] (T : C → Prop)
    (htriangle : ∀ Δ : Pretriangulated.Triangle C, Δ ∈ Pretriangulated.distinguishedTriangles →
      (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
      (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁))
    {X₀ : C} (h₀ : T X₀) {X Y : C} (e : X ≅ Y) (hX : T X) : T Y := by
  have hzero : T (0 : C) :=
    (htriangle _ (Pretriangulated.contractible_distinguished _)).1 h₀ h₀
  have hΔ : Pretriangulated.Triangle.mk e.hom (0 : Y ⟶ 0) (0 : (0 : C) ⟶ X⟦(1 : ℤ)⟧) ∈
      Pretriangulated.distinguishedTriangles :=
    (Pretriangulated.Triangle.distinguished_iff_of_isZero₃ _ (isZero_zero _)).2 e.isIso_hom
  exact (htriangle _ hΔ).2.1 hX hzero

/-- *"Let `R` be a ring. Let `(A, d)` be a differential graded `R`-algebra.
Using P-resolutions we can sometimes reduce statements about general objects of `D(A, d)` to
statements about `A[k]`. Namely, let `T` be a property of objects of `D(A, d)` and assume that*

1. *if `Kᵢ`, `i ∈ I` is a family of objects of `D(A, d)` and `T(Kᵢ)` holds for all `i ∈ I`, then
   `T(⨁ Kᵢ)`,*
2. *if `K → L → M → K[1]` is a distinguished triangle of `D(A, d)` and `T` holds for two, then
   `T` holds for the third object, and*
3. *`T(A[k])` holds for all `k ∈ ℤ`.*

*Then `T` holds for all objects of `D(A, d)`."*

The object denoted `A` in the source is the image of the regular module `A` in `D(A, d)`, so
hypothesis (3) is `T` on each shift of that image. Hypothesis (2) is stated as the conjunction of
its three implications, one for each position of the triangle. Isomorphism invariance of `T` is
not assumed. -/
@[stacks 0FQE]
theorem property_of_coproducts_of_two_out_of_three_of_shifts
    (A : DifferentialGradedAlgebra R) (T : derivedCategory' A → Prop)
    (hsum : ∀ {ι : Type u} (K : ι → derivedCategory' A), (∀ i, T (K i)) → T (∐ K))
    (htriangle : ∀ Δ : Pretriangulated.Triangle (derivedCategory' A),
      Δ ∈ Pretriangulated.distinguishedTriangles →
      (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
      (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁))
    (hshift : ∀ k : ℤ, T (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
      (regularModule A))⟦k⟧)) :
    ∀ K : derivedCategory' A, T K := by
  classical
  let L := (quasiIsomorphisms' A).Q
  let Q := toHomotopyCategory A ⋙ L
  have hiso : ∀ {X Y : derivedCategory' A}, (X ≅ Y) → T X → T Y :=
    iso_invariant_of_two_out_of_three T htriangle (hshift 0)
  have hcoprod : ∀ {ι : Type u} [DecidableEq ι] (N : ι → DifferentialGradedModule A),
      (∀ i, T (Q.obj (N i))) → T (Q.obj (directSumObj N)) := by
    intro ι _ N hN
    exact hiso ((Q.mapIso (directSumObjIsoSigma N)).trans
      (PreservesCoproduct.iso Q N)).symm (hsum _ hN)
  have hpieces : ∀ {ι : Type u} [DecidableEq ι] (k : ι → ℤ),
      T (Q.obj (directSumShifts A k)) := by
    intro ι _ k
    refine hiso (Q.mapIso (directSumObjIsoDirectSumShifts A k)) (hcoprod _ fun i => ?_)
    exact hiso ((Q.commShiftIso (k i)).app (regularModule A)).symm (hshift (k i))
  have hses : ∀ {K₁ K₂ K₃ : DifferentialGradedModule A} (f : K₁ ⟶ K₂) (g : K₂ ⟶ K₃),
      IsAdmissibleShortExact f g →
        (T (Q.obj K₁) → T (Q.obj K₂) → T (Q.obj K₃)) ∧
        (T (Q.obj K₁) → T (Q.obj K₃) → T (Q.obj K₂)) := by
    intro K₁ K₂ K₃ f g hfg
    exact (htriangle _ (L.map_distinguished _
      (associatedTriangle_mem_distTriang A f g hfg))).imp_right And.left
  intro K
  obtain ⟨P, S, f, a, b, F, hf, hab, ⟨e⟩⟩ :=
    exists_propertyP_telescope A (L.objPreimage K).as
  have hF : ∀ i, T (Q.obj (F.F i)) := by
    intro i
    induction i with
    | zero =>
        let _ := F.bottomDecidableEq
        exact hiso (Q.mapIso (Hom.isoOfBijective F.bottomMap F.bottom_bijective)).symm
          (hpieces F.bottomShift)
    | succ i ih =>
        let _ := F.quotientDecidableEq i
        exact (hses _ _ (F.isAdmissibleShortExact_incl_quotientMap i)).2 ih
          (hpieces (F.quotientShift i))
  have hS : T (Q.obj S) := hiso (Q.mapIso e).symm (hcoprod _ fun j => hF j.down)
  have hP : T (Q.obj P) := (hses a b hab).1 hS hS
  have : IsIso (Q.map f) :=
    Localization.inverts L (quasiIsomorphisms' A) _ ((quasiIsomorphisms_map_iff' A f).2 hf)
  exact hiso (asIso (Q.map f) ≪≫ L.objObjPreimageIso K) hP

end SingleUniverse

/-! ### The dévissage with the algebra in a universe of its own

Everything above is stated for `A : DifferentialGradedAlgebra.{u, u} R`, the carrier of the
algebra being in the universe of the base ring. The declarations of this namespace repeat the
development with the two universes kept apart: the base ring is in `Type u`, the carrier of the
algebra in `Type v`, and the modules, the index types of the direct sums and the cells of a
property-(P) filtration are all in `Type v` as well, that being the universe of the regular
module. The derived category is then the universe-polymorphic
`DifferentialGradedModule.derivedCategory` rather than `DifferentialGradedModule.derivedCategory'`,
and the pretriangulated structure on the homotopy category is the one whose distinguished
triangles are the cone triangles. -/

namespace General

universe v

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}



noncomputable section DirectSums

variable {ι : Type v} (N : ι → DifferentialGradedModule.{u, v, v} A)

/-- The degree-`n` part of the direct sum `⨁ᵢ Nᵢ`. -/
def directSumGrading (n : ℤ) : Submodule R (⨁ i, (N i).M) where
  carrier := {x | ∀ i, x i ∈ (N i).grading n}
  add_mem' {x y} hx hy i := by
    simpa only [DirectSum.add_apply] using (((N i).grading n).add_mem (hx i) (hy i))
  zero_mem' i := by
    simpa only [DirectSum.zero_apply] using ((N i).grading n).zero_mem
  smul_mem' r x hx i := by
    simpa only [DirectSum.smul_apply] using ((N i).grading n).smul_mem r (hx i)

/-- Homogeneity in the direct sum is componentwise. -/
@[simp] theorem mem_directSumGrading {n : ℤ} {x : ⨁ i, (N i).M} :
    x ∈ directSumGrading N n ↔ ∀ i, x i ∈ (N i).grading n := Iff.rfl

/-- The `j`-th coprojection carries a homogeneous element of degree `n` to one. -/
theorem lof_mem_directSumGrading [DecidableEq ι] {n : ℤ} (j : ι) {y : (N j).M}
    (hy : y ∈ (N j).grading n) :
    DirectSum.lof R ι (fun i => (N i).M) j y ∈ directSumGrading N n := by
  intro i
  by_cases h : j = i
  · subst h
    simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_same] using hy
  · simpa only [DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)] using ((N i).grading n).zero_mem

/-- The `j`-th summand inclusion carries a homogeneous element of degree `n` to one. -/
theorem of_mem_directSumGrading [DecidableEq ι] {n : ℤ} (j : ι) {y : (N j).M}
    (hy : y ∈ (N j).grading n) :
    DirectSum.of (fun i => (N i).M) j y ∈ directSumGrading N n :=
  lof_mem_directSumGrading N j hy

/-- The `j`-th component map sends the degree-`n` part of the direct sum into the degree-`n`
part of `N j`. -/
theorem map_component_directSumGrading (j : ι) (n : ℤ) :
    Submodule.map (DirectSum.component R ι (fun i => (N i).M) j) (directSumGrading N n)
      ≤ (N j).grading n := by
  rintro _ ⟨x, hx, rfl⟩
  exact hx j

/-- The degree-`n` parts of the direct sum are independent. -/
theorem directSumGrading_iSupIndep : iSupIndep (directSumGrading N) := by
  rw [iSupIndep_def]
  intro n
  rw [Submodule.disjoint_def]
  intro x hxn hxsup
  apply DirectSum.ext
  intro j
  have hgj : iSupIndep (N j).grading :=
    (DirectSum.Decomposition.isInternal (N j).grading).submodule_iSupIndep
  rw [iSupIndep_def] at hgj
  have hd := hgj n
  rw [Submodule.disjoint_def] at hd
  have hproj : x j ∈ ⨆ m, ⨆ (_ : m ≠ n), (N j).grading m := by
    have h : x j ∈ Submodule.map (DirectSum.component R ι (fun i => (N i).M) j)
        (⨆ m, ⨆ (_ : m ≠ n), directSumGrading N m) := ⟨x, hxsup, rfl⟩
    rw [Submodule.map_iSup] at h
    refine (iSup_le (fun m => ?_) : _ ≤ ⨆ m, ⨆ (_ : m ≠ n), (N j).grading m) h
    rw [Submodule.map_iSup]
    exact iSup_le (fun hm => le_trans (map_component_directSumGrading N j m)
      (le_iSup₂ (f := fun m _ => (N j).grading m) m hm))
  simpa using hd (x j) (hxn j) hproj

/-- The degree-`n` parts of the direct sum span it. -/
theorem directSumGrading_iSup_eq_top : iSup (directSumGrading N) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  rw [← DirectSum.sum_support_of x]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  suffices key : ∀ y : (N j).M, y ∈ ⨆ n, (N j).grading n →
      DirectSum.of (fun i => (N i).M) j y ∈ iSup (directSumGrading N) by
    refine key (x j) ?_
    rw [(DirectSum.Decomposition.isInternal (N j).grading).submodule_iSup_eq_top]
    exact Submodule.mem_top
  intro y hy
  induction hy using Submodule.iSup_induction' with
  | mem n z hz =>
      exact Submodule.mem_iSup_of_mem n (lof_mem_directSumGrading N j hz)
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add a b _ _ iha ihb =>
      simpa only [map_add] using Submodule.add_mem _ iha ihb

/-- The degree-`n` parts of the direct sum form a direct-sum decomposition of it. -/
@[instance_reducible]
def directSumDecomposition : DirectSum.Decomposition (directSumGrading N) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (directSumGrading_iSupIndep N) (directSumGrading_iSup_eq_top N)).chooseDecomposition _

variable [DecidableEq ι]

/-- The componentwise differential of the direct sum. -/
def directSumD : (⨁ i, (N i).M) →ₗ[R] (⨁ i, (N i).M) :=
  DirectSum.toModule R ι (⨁ i, (N i).M)
    (fun i => (DirectSum.lof R ι (fun i => (N i).M) i).comp (N i).d)

/-- The differential of the direct sum acts componentwise. -/
@[simp] theorem directSumD_apply (x : ⨁ i, (N i).M) (j : ι) :
    directSumD N x j = (N j).d (x j) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, DirectSum.zero_apply]
  | of i a =>
      rw [show DirectSum.of (fun i => (N i).M) i a
            = DirectSum.lof R ι (fun i => (N i).M) i a from rfl, directSumD,
        DirectSum.toModule_lof (R := R) (M := fun i => (N i).M) (N := (⨁ i, (N i).M)) i a]
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
      by_cases h : i = j
      · subst h; simp
      · simp only [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]

/-- The componentwise differential on the `i`-th summand. -/
theorem directSumD_of (i : ι) (y : (N i).M) :
    directSumD N (DirectSum.of (fun i => (N i).M) i y)
      = DirectSum.of (fun i => (N i).M) i ((N i).d y) := by
  apply DirectSum.ext
  intro j
  rw [directSumD_apply]
  by_cases h : j = i
  · subst h; simp
  · simp only [DirectSum.of_eq_of_ne _ _ _ h, map_zero]

/-- The direct sum `⨁ᵢ Nᵢ` of a family of differential graded modules: its carrier is the
direct sum `⨁ᵢ (Nᵢ).M` of the carriers, and its grading, right action and differential are all
componentwise. -/
@[implicit_reducible]
def directSumObj : DifferentialGradedModule.{u, v, v} A where
  M := ⨁ i, (N i).M
  grading := directSumGrading N
  decomposition := directSumDecomposition N
  smul_mem n m x a hx ha i := by
    simpa only [DirectSum.smul_apply] using (N i).smul_mem n m (x i) a (hx i) ha
  d := directSumD N
  d_comp_d := by
    refine LinearMap.ext fun x => DirectSum.ext fun j => ?_
    simp only [LinearMap.comp_apply, directSumD_apply, DirectSum.zero_apply,
      LinearMap.zero_apply]
    exact LinearMap.congr_fun (N j).d_comp_d (x j)
  d_mem n x hx i := by
    simpa only [directSumD_apply] using (N i).d_mem n (x i) (hx i)
  leibniz n m x a hx ha := by
    refine DirectSum.ext fun j => ?_
    simp only [directSumD_apply, DirectSum.add_apply, DirectSum.smul_apply,
      DirectSum.apply_eq_component]
    exact (N j).leibniz n m (x j) a (hx j) ha

/-- Homogeneity in `⨁ᵢ Nᵢ` is componentwise. -/
@[simp] theorem mem_directSumObj_grading {n : ℤ} {x : ⨁ i, (N i).M} :
    x ∈ (directSumObj N).grading n ↔ ∀ i, x i ∈ (N i).grading n := Iff.rfl

/-! ### The coprojections and the universal property

The facts about the direct sum are stated over the bare direct sum `⨁ᵢ (Nᵢ).M`, with the
differential written out as a `DirectSum.toModule`: the carrier of `directSumObj N` is that
direct sum only up to unfolding at default transparency. -/

/-- The `j`-th coprojection intertwines the differential of `N j` with the componentwise
differential of the direct sum. -/
theorem lof_comp_directSumD (j : ι) :
    (DirectSum.lof R ι (fun i => (N i).M) j).comp (N j).d
      = (DirectSum.toModule R ι (⨁ i, (N i).M)
          (fun i => (DirectSum.lof R ι (fun i => (N i).M) i).comp (N i).d)).comp
        (DirectSum.lof R ι (fun i => (N i).M) j) :=
  LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply,
      DirectSum.toModule_lof (R := R) (M := fun i => (N i).M) (N := (⨁ i, (N i).M)) j x]

/-- The `j`-th coprojection `N j ⟶ ⨁ᵢ Nᵢ`. -/
def directSumInj (j : ι) : N j ⟶ directSumObj N where
  toFun := DirectSum.lof R ι (fun i => (N i).M) j
  map_smul x a :=
    map_smul (DirectSum.lof (MulOpposite A.A) ι (fun i => (N i).M) j) (MulOpposite.op a) x
  map_grading _ _ hx := lof_mem_directSumGrading N j hx
  map_d := lof_comp_directSumD N j

/-- The `j`-th coprojection is the `j`-th coprojection of the underlying direct sum. -/
@[simp] theorem directSumInj_toFun_apply (j : ι) (x : (N j).M) :
    (directSumInj N j).toFun x = DirectSum.lof R ι (fun i => (N i).M) j x := rfl

variable {T : DifferentialGradedModule.{u, v, v} A}

/-- The descent of a family of homomorphisms out of the summands, as a linear map at the honest
type. -/
abbrev directSumDescLinear (g : ∀ i, N i ⟶ T) : (⨁ i, (N i).M) →ₗ[R] T.M :=
  DirectSum.toModule R ι T.M (fun i => (g i).toFun)

/-- The descent reads off the `i`-th map on the `i`-th coprojection. -/
theorem directSumDescLinear_lof (g : ∀ i, N i ⟶ T) (i : ι) (y : (N i).M) :
    directSumDescLinear N g (DirectSum.lof R ι (fun i => (N i).M) i y) = (g i).toFun y :=
  DirectSum.toModule_lof (R := R) (φ := fun i => (g i).toFun) i y

/-- The descent reads off the `i`-th map on the `i`-th summand. -/
theorem directSumDescLinear_of (g : ∀ i, N i ⟶ T) (i : ι) (y : (N i).M) :
    directSumDescLinear N g (DirectSum.of (fun i => (N i).M) i y) = (g i).toFun y := by
  rw [← DirectSum.lof_eq_of (R := R)]
  exact directSumDescLinear_lof N g i y

/-- The coprojections are `Aᵐᵒᵖ`-linear: a right multiple of the `i`-th coprojection of `y` is
the `i`-th coprojection of the right multiple of `y`. -/
theorem op_smul_of (i : ι) (y : (N i).M) (a : A.A) :
    MulOpposite.op a • DirectSum.of (fun i => (N i).M) i y
      = DirectSum.of (fun i => (N i).M) i (MulOpposite.op a • y) :=
  (map_smul (DirectSum.lof (MulOpposite A.A) ι (fun i => (N i).M) i) (MulOpposite.op a) y).symm

/-- The descent is compatible with the right `A`-action. -/
theorem directSumDescLinear_smul (g : ∀ i, N i ⟶ T) (x : ⨁ i, (N i).M)
    (a : A.A) :
    directSumDescLinear N g (MulOpposite.op a • x)
      = MulOpposite.op a • directSumDescLinear N g x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y =>
      rw [op_smul_of N i y a, directSumDescLinear_of, directSumDescLinear_of]
      exact (g i).map_smul y a
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The descent preserves the grading. -/
theorem directSumDescLinear_mem_grading (g : ∀ i, N i ⟶ T) (n : ℤ)
    (x : ⨁ i, (N i).M) (hx : x ∈ directSumGrading N n) :
    directSumDescLinear N g x ∈ T.grading n := by
  classical
  rw [← DirectSum.sum_support_of x, map_sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [directSumDescLinear_of]
  exact (g j).map_grading n (x j) (hx j)

/-- The descent commutes with the differentials. -/
theorem directSumDescLinear_comp_directSumD (g : ∀ i, N i ⟶ T) :
    (directSumDescLinear N g).comp
        (DirectSum.toModule R ι (⨁ i, (N i).M)
          (fun i => (DirectSum.lof R ι (fun i => (N i).M) i).comp (N i).d))
      = T.d.comp (directSumDescLinear N g) :=
  DirectSum.linearMap_ext R fun i => LinearMap.ext fun y => by
    simp only [LinearMap.comp_apply]
    rw [DirectSum.toModule_lof (R := R)
        (φ := fun i => (DirectSum.lof R ι (fun i => (N i).M) i).comp (N i).d) i y,
      LinearMap.comp_apply, directSumDescLinear_lof, directSumDescLinear_lof]
    exact LinearMap.congr_fun (g i).map_d y

/-- The descent `⨁ᵢ Nᵢ ⟶ T` of a family of homomorphisms `Nᵢ ⟶ T`. -/
def directSumDesc (g : ∀ i, N i ⟶ T) : directSumObj N ⟶ T where
  toFun := directSumDescLinear N g
  map_smul := directSumDescLinear_smul N g
  map_grading := directSumDescLinear_mem_grading N g
  map_d := directSumDescLinear_comp_directSumD N g

/-- The descent restricts on the `j`-th summand to the `j`-th given homomorphism. -/
@[simp] theorem directSumInj_comp_directSumDesc (g : ∀ i, N i ⟶ T) (j : ι) :
    directSumInj N j ≫ directSumDesc N g = g j := by
  refine Hom.ext (LinearMap.ext fun y => ?_)
  change directSumDescLinear N g (DirectSum.of (fun i => (N i).M) j y) = (g j).toFun y
  exact directSumDescLinear_of N g j y

/-- Two homomorphisms out of the direct sum agreeing on every summand are equal. -/
theorem directSum_hom_ext {f g : directSumObj N ⟶ T}
    (h : ∀ i, directSumInj N i ≫ f = directSumInj N i ≫ g) : f = g := by
  exact Hom.ext (DirectSum.linearMap_ext R fun i => congrArg Hom.toFun (h i))

/-- The direct sum `⨁ᵢ Nᵢ`, with its coprojections, is a direct sum in `Mod_{(A,d)}`. -/
def isColimit_directSumObj :
    IsColimit (Cofan.mk (directSumObj N) (directSumInj N)) :=
  Cofan.IsColimit.mk _ (fun s => directSumDesc N (fun i => s.inj i))
    (fun _ j => directSumInj_comp_directSumDesc N _ j)
    (fun _ _ hm => directSum_hom_ext N fun i =>
      (hm i).trans (directSumInj_comp_directSumDesc N _ i).symm)

/-! ### Homotopies out of a direct sum

A homotopy out of a direct sum is the same thing as a family of homotopies out of the summands:
the assembled map is produced by the universal property of the direct sum of right `A`-modules,
and the homotopy equation is checked on the coprojections, every element of a direct sum having
finite support. -/

section HomotopyAssembly

variable {T : DifferentialGradedModule.{u, v, v} A}

/-- The assembly of a family of maps out of the summands reads off the `i`-th map on the `i`-th
summand. Stated over `Aᵐᵒᵖ`, the ring over which a homotopy is linear. -/
theorem toModuleOp_of (k : ∀ i, (N i).M →ₗ[MulOpposite A.A] T.M) (i : ι) (y : (N i).M) :
    DirectSum.toModule (MulOpposite A.A) ι T.M k (DirectSum.of (fun i => (N i).M) i y)
      = k i y := by
  rw [← DirectSum.lof_eq_of (R := MulOpposite A.A)]
  exact DirectSum.toModule_lof (R := MulOpposite A.A) (φ := k) i y

/-- The assembly of a family of degree `-1` maps out of the summands again lowers the grading
by one. -/
theorem toModuleOp_mem_grading (k : ∀ i, (N i).M →ₗ[MulOpposite A.A] T.M)
    (hk : ∀ (i : ι) (n : ℤ) (y : (N i).M), y ∈ (N i).grading n → k i y ∈ T.grading (n - 1))
    (n : ℤ) (x : ⨁ i, (N i).M) (hx : x ∈ directSumGrading N n) :
    DirectSum.toModule (MulOpposite A.A) ι T.M k x ∈ T.grading (n - 1) := by
  classical
  rw [← DirectSum.sum_support_of x, map_sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [toModuleOp_of]
  exact hk j n (x j) (hx j)

/-- The homotopy equation for the assembled map, over the bare direct sum. -/
theorem toModuleOp_homotopy_eq {f g : directSumObj N ⟶ T}
    (h : ∀ i, Homotopy (directSumInj N i ≫ f) (directSumInj N i ≫ g)) (x : ⨁ i, (N i).M) :
    f.toFun x - g.toFun x
      = T.d (DirectSum.toModule (MulOpposite A.A) ι T.M (fun i => (h i).toLinearMap) x)
        + DirectSum.toModule (MulOpposite A.A) ι T.M (fun i => (h i).toLinearMap)
            (directSumD N x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y =>
      rw [directSumD_of, toModuleOp_of, toModuleOp_of]
      exact (h i).homotopy_eq y
  | add x y hx hy =>
      simp only [map_add]
      rw [show f.toFun x + f.toFun y - (g.toFun x + g.toFun y)
            = (f.toFun x - g.toFun x) + (f.toFun y - g.toFun y) from by abel, hx, hy]
      abel

/-- A family of homotopies out of the summands assembles into a homotopy out of the direct
sum. -/
def directSumHomotopy {f g : directSumObj N ⟶ T}
    (h : ∀ i, Homotopy (directSumInj N i ≫ f) (directSumInj N i ≫ g)) : Homotopy f g where
  toLinearMap := DirectSum.toModule (MulOpposite A.A) ι T.M (fun i => (h i).toLinearMap)
  map_grading := toModuleOp_mem_grading N _ (fun i n y hy => (h i).map_grading n y hy)
  homotopy_eq := toModuleOp_homotopy_eq N h

/-- The coprojections of the direct sum are jointly epimorphic in the homotopy category. -/
theorem directSum_homotopyCategory_hom_ext {Y : HomotopyCategory.{u, v, v} A}
    (f g : (toHomotopyCategory A).obj (directSumObj N) ⟶ Y)
    (hfg : ∀ i, (toHomotopyCategory A).map (directSumInj N i) ≫ f
      = (toHomotopyCategory A).map (directSumInj N i) ≫ g) : f = g := by
  have hf : (toHomotopyCategory A).map ((toHomotopyCategory A).preimage f) = f :=
    (toHomotopyCategory A).map_preimage f
  have hg : (toHomotopyCategory A).map ((toHomotopyCategory A).preimage g) = g :=
    (toHomotopyCategory A).map_preimage g
  set f' := (toHomotopyCategory A).preimage f with hf'
  set g' := (toHomotopyCategory A).preimage g with hg'
  have hcomp : ∀ i, Homotopic (directSumInj N i ≫ f') (directSumInj N i ≫ g') := by
    intro i
    refine (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) _ _).1 ?_
    rw [Functor.map_comp, Functor.map_comp, hf, hg]
    exact hfg i
  have : Homotopic f' g' := ⟨directSumHomotopy N (fun i => (hcomp i).some)⟩
  rw [← hf, ← hg]
  exact (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) f' g').2 this

end HomotopyAssembly

/-! ### Direct sums of homomorphisms, and of quasi-isomorphisms -/

section QuasiIso

variable {N' : ι → DifferentialGradedModule.{u, v, v} A} (f : ∀ i, N i ⟶ N' i)

/-- The direct sum `⨁ᵢ fᵢ : ⨁ᵢ Nᵢ ⟶ ⨁ᵢ Nᵢ'` of a family of homomorphisms. -/
def directSumMap : directSumObj N ⟶ directSumObj N' :=
  directSumDesc N (fun i => f i ≫ directSumInj N' i)

/-- The direct sum of a family of homomorphisms is componentwise on the coprojections. -/
@[simp] theorem directSumInj_comp_directSumMap (i : ι) :
    directSumInj N i ≫ directSumMap N f = f i ≫ directSumInj N' i :=
  directSumInj_comp_directSumDesc N _ i

/-- The direct sum of a family of homomorphisms, as a linear map at the honest type. -/
abbrev directSumMapLinear : (⨁ i, (N i).M) →ₗ[R] (⨁ i, (N' i).M) :=
  DirectSum.toModule R ι (⨁ i, (N' i).M) (fun i => (f i ≫ directSumInj N' i).toFun)

/-- The underlying map of `⨁ᵢ fᵢ`, read at the honest type. -/
theorem directSumMap_toFun_apply (x : ⨁ i, (N i).M) :
    (directSumMap N f).toFun x = directSumMapLinear N f x := rfl

/-- `⨁ᵢ fᵢ` carries the `i`-th summand to the `i`-th summand by `fᵢ`. -/
theorem directSumMapLinear_of (i : ι) (y : (N i).M) :
    directSumMapLinear N f (DirectSum.of (fun i => (N i).M) i y)
      = DirectSum.of (fun i => (N' i).M) i ((f i).toFun y) := by
  rw [← DirectSum.lof_eq_of (R := R)]
  exact DirectSum.toModule_lof (R := R) (φ := fun i => (f i ≫ directSumInj N' i).toFun) i y

/-- `⨁ᵢ fᵢ` acts componentwise. -/
theorem directSumMapLinear_apply (x : ⨁ i, (N i).M) (j : ι) :
    directSumMapLinear N f x j = (f j).toFun (x j) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y =>
      rw [directSumMapLinear_of]
      by_cases h : j = i
      · subst h; simp
      · simp only [DirectSum.of_eq_of_ne _ _ _ h, map_zero]
  | add a b ha hb =>
      rw [map_add]
      simp only [DirectSum.add_apply, ha, hb, map_add]

/-- Every homogeneous cocycle of `⨁ᵢ Nᵢ'` is, modulo a boundary, the image of a homogeneous
cocycle of `⨁ᵢ Nᵢ`. -/
private theorem directSumMap_cocycle_aux (hf : ∀ i, IsQuasiIsomorphism (f i)) (n : ℤ)
    (y : ⨁ i, (N' i).M) (hy : y ∈ directSumGrading N' n) (hdy : directSumD N' y = 0) :
    ∃ x : ⨁ i, (N i).M, x ∈ directSumGrading N n ∧ directSumD N x = 0 ∧
      ∃ z : ⨁ i, (N' i).M, z ∈ directSumGrading N' (n - 1) ∧
        directSumD N' z = y - directSumMapLinear N f x := by
  classical
  have hdy' : ∀ i, (N' i).d (y i) = 0 := fun i => by
    simpa only [directSumD_apply, DirectSum.zero_apply] using
      congrArg (fun t : ⨁ i, (N' i).M => t i) hdy
  rw [← DirectSum.sum_support_of y]
  refine Finset.sum_induction _ (fun w => ∃ x : ⨁ i, (N i).M, x ∈ directSumGrading N n ∧
    directSumD N x = 0 ∧ ∃ z : ⨁ i, (N' i).M, z ∈ directSumGrading N' (n - 1) ∧
      directSumD N' z = w - directSumMapLinear N f x) ?_ ?_ ?_
  · rintro a b ⟨xa, hxa, hdxa, za, hza, hzaeq⟩ ⟨xb, hxb, hdxb, zb, hzb, hzbeq⟩
    refine ⟨xa + xb, (directSumGrading N n).add_mem hxa hxb, ?_,
      za + zb, (directSumGrading N' (n - 1)).add_mem hza hzb, ?_⟩
    · rw [map_add, hdxa, hdxb, add_zero]
    · rw [map_add, hzaeq, hzbeq, map_add]
      abel
  · exact ⟨0, Submodule.zero_mem _, map_zero _, 0, Submodule.zero_mem _, by simp⟩
  · intro i _
    obtain ⟨xi, hxi, hdxi, zi, hzi, hzieq⟩ := (hf i n).1 (y i) (hy i) (hdy' i)
    refine ⟨DirectSum.of (fun i => (N i).M) i xi, of_mem_directSumGrading N i hxi, ?_,
      DirectSum.of (fun i => (N' i).M) i zi, of_mem_directSumGrading N' i hzi, ?_⟩
    · rw [directSumD_of, hdxi, map_zero]
    · rw [directSumD_of, hzieq, directSumMapLinear_of, ← map_sub]

/-- A homogeneous cocycle of `⨁ᵢ Nᵢ` whose image is a boundary is itself a boundary. -/
private theorem directSumMap_boundary_aux (hf : ∀ i, IsQuasiIsomorphism (f i)) (n : ℤ)
    (x : ⨁ i, (N i).M) (hx : x ∈ directSumGrading N n) (hdx : directSumD N x = 0)
    (hb : ∃ z : ⨁ i, (N' i).M, z ∈ directSumGrading N' (n - 1) ∧
      directSumD N' z = directSumMapLinear N f x) :
    ∃ w : ⨁ i, (N i).M, w ∈ directSumGrading N (n - 1) ∧ directSumD N w = x := by
  classical
  obtain ⟨z, hz, hzeq⟩ := hb
  have hdx' : ∀ i, (N i).d (x i) = 0 := fun i => by
    simpa only [directSumD_apply, DirectSum.zero_apply] using
      congrArg (fun t : ⨁ i, (N i).M => t i) hdx
  have hzeq' : ∀ i, (N' i).d (z i) = (f i).toFun (x i) := fun i => by
    simpa only [directSumD_apply, directSumMapLinear_apply] using
      congrArg (fun t : ⨁ i, (N' i).M => t i) hzeq
  rw [← DirectSum.sum_support_of x]
  refine Finset.sum_induction _ (fun v => ∃ w : ⨁ i, (N i).M,
    w ∈ directSumGrading N (n - 1) ∧ directSumD N w = v) ?_ ?_ ?_
  · rintro a b ⟨wa, hwa, hwaeq⟩ ⟨wb, hwb, hwbeq⟩
    exact ⟨wa + wb, (directSumGrading N (n - 1)).add_mem hwa hwb, by
      rw [map_add, hwaeq, hwbeq]⟩
  · exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  · intro i _
    obtain ⟨wi, hwi, hwieq⟩ := (hf i n).2 (x i) (hx i) (hdx' i) ⟨z i, hz i, hzeq' i⟩
    exact ⟨DirectSum.of (fun i => (N i).M) i wi, of_mem_directSumGrading N i hwi, by
      rw [directSumD_of, hwieq]⟩

/-- A direct sum of quasi-isomorphisms is a quasi-isomorphism, in the cycle-and-boundary
form. -/
theorem isQuasiIsomorphism_directSumMap (hf : ∀ i, IsQuasiIsomorphism (f i)) :
    IsQuasiIsomorphism (directSumMap N f) :=
  fun n => ⟨directSumMap_cocycle_aux N f hf n, directSumMap_boundary_aux N f hf n⟩

/-- A direct sum of quasi-isomorphisms is a quasi-isomorphism of the underlying cochain
complexes. -/
theorem quasiIso_directSumMap (hf : ∀ i, IsQuasiIsomorphism (f i)) :
    QuasiIso ((forgetToCochainComplex A).map (directSumMap N f)) :=
  quasiIso_of_isQuasiIsomorphism _ (isQuasiIsomorphism_directSumMap N f hf)

end QuasiIso

end DirectSums

section GeneralDerived

attribute [local instance 10000] instPretriangulatedHomotopyCategory
  instPreadditiveHomotopyCategory

/-! ### Direct sums of left-orthogonal modules -/

/-- A differential graded module presented as a direct sum of modules orthogonal on the left to
the acyclic modules is itself orthogonal on the left to them. -/
theorem leftOrthogonal_acyclic_of_directSum {ι : Type v} [DecidableEq ι]
    {X : ι → DifferentialGradedModule.{u, v, v} A}
    {T : DifferentialGradedModule.{u, v, v} A} (inj : ∀ j, X j ⟶ T)
    (ev : (⨁ j, (X j).M) ≃ₗ[MulOpposite A.A] T.M)
    (hev : ∀ j x, ev (DirectSum.of (fun j => (X j).M) j x) = (inj j).toFun x)
    (hgr : ∀ (n : ℤ) (z : ⨁ j, (X j).M), ev z ∈ T.grading n → ∀ j, z j ∈ (X j).grading n)
    (hX : ∀ j, (acyclic.{u, v, v} A).leftOrthogonal ((toHomotopyCategory A).obj (X j))) :
    (acyclic.{u, v, v} A).leftOrthogonal ((toHomotopyCategory A).obj T) := by
  rw [leftOrthogonal_acyclic_iff]
  intro N hN f
  rw [← isNullHomotopic_iff_homotopic_zero]
  refine isNullHomotopic_of_directSum inj ev hev hgr f (fun j => ?_)
  rw [isNullHomotopic_iff_homotopic_zero]
  exact (leftOrthogonal_acyclic_iff (X j)).1 (hX j) N hN (inj j ≫ f)

/-- A direct sum of differential graded modules orthogonal on the left to the acyclic modules is
itself orthogonal on the left to them. -/
theorem leftOrthogonal_acyclic_directSumObj {ι : Type v} [DecidableEq ι]
    (N : ι → DifferentialGradedModule.{u, v, v} A)
    (hN : ∀ i, (acyclic.{u, v, v} A).leftOrthogonal ((toHomotopyCategory A).obj (N i))) :
    (acyclic.{u, v, v} A).leftOrthogonal ((toHomotopyCategory A).obj (directSumObj N)) :=
  leftOrthogonal_acyclic_of_directSum (directSumInj N)
    (LinearEquiv.refl (MulOpposite A.A) (⨁ i, (N i).M))
    (fun _ _ => rfl) (fun _ _ hz j => hz j) hN

section Derived

variable {ι : Type v} [DecidableEq ι] (N : ι → DifferentialGradedModule.{u, v, v} A)

/-- The localization at the quasi-isomorphisms is a localization at the multiplicative system
attached to the acyclic objects: the two classes of morphisms coincide (Tag 09KW). -/
theorem q_isLocalization_acyclic_trW (A : DifferentialGradedAlgebra.{u, v} R) :
    ((quasiIsomorphisms A).Q).IsLocalization (acyclic A).trW := by
  rw [acyclic_trW_eq_quasiIsomorphisms]
  infer_instance

/-- For a module orthogonal on the left to the acyclic modules, the localization functor is
bijective on homomorphisms out of its class in the homotopy category: homomorphisms in
`D(A, d)` out of such a module are computed in `K(A, d)`. -/
theorem map_q_bijective_of_leftOrthogonal {P : DifferentialGradedModule.{u, v, v} A}
    (hP : (acyclic A).leftOrthogonal ((toHomotopyCategory A).obj P))
    (Y : HomotopyCategory.{u, v, v} A) :
    Function.Bijective (((quasiIsomorphisms A).Q).map :
      ((toHomotopyCategory A).obj P ⟶ Y) → _) :=
  have := q_isLocalization_acyclic_trW A
  ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated hP
    ((quasiIsomorphisms A).Q) Y

/-- The image of a direct sum of modules orthogonal on the left to the acyclic modules is a
direct sum in the derived category. -/
def isColimit_q_mapCocone_directSumObj
    (hN : ∀ i, (acyclic A).leftOrthogonal ((toHomotopyCategory A).obj (N i))) :
    IsColimit ((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).mapCocone
      (Cofan.mk (directSumObj N) (directSumInj N))) := by
  classical
  have hT := leftOrthogonal_acyclic_directSumObj N hN
  refine IsColimit.ofExistsUnique (fun s => ?_)
  let Y : DifferentialGradedModule.{u, v, v} A := (((quasiIsomorphisms A).Q).objPreimage s.pt).as
  let e : ((quasiIsomorphisms A).Q).obj ((toHomotopyCategory A).obj Y) ≅ s.pt :=
    ((quasiIsomorphisms A).Q).objObjPreimageIso s.pt
  choose h hh using fun i =>
    (map_q_bijective_of_leftOrthogonal (hN i) ((toHomotopyCategory A).obj Y)).surjective
      (s.ι.app ⟨i⟩ ≫ e.inv)
  let k : ∀ i, N i ⟶ Y := fun i => (toHomotopyCategory A).preimage (h i)
  have hfac : ∀ i, (toHomotopyCategory A).map (directSumInj N i)
      ≫ (toHomotopyCategory A).map (directSumDesc N k) = h i := by
    intro i
    rw [← Functor.map_comp, directSumInj_comp_directSumDesc]
    exact (toHomotopyCategory A).map_preimage (h i)
  refine ⟨((quasiIsomorphisms A).Q).map ((toHomotopyCategory A).map (directSumDesc N k))
    ≫ e.hom, ?_, ?_⟩
  · rintro ⟨i⟩
    simp only [Functor.mapCocone_ι_app, Functor.comp_map, Cofan.mk_ι_app]
    rw [← Category.assoc, ← Functor.map_comp, hfac i, hh i, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · intro m hm
    obtain ⟨m', hm'⟩ :=
      (map_q_bijective_of_leftOrthogonal hT ((toHomotopyCategory A).obj Y)).surjective
        (m ≫ e.inv)
    have hcomp : ∀ i, (toHomotopyCategory A).map (directSumInj N i) ≫ m'
        = (toHomotopyCategory A).map (directSumInj N i)
          ≫ (toHomotopyCategory A).map (directSumDesc N k) := by
      intro i
      refine (map_q_bijective_of_leftOrthogonal (hN i)
        ((toHomotopyCategory A).obj Y)).injective ?_
      have hmi := hm ⟨i⟩
      simp only [Functor.mapCocone_ι_app, Functor.comp_map, Cofan.mk_ι_app] at hmi
      rw [hfac i, hh i, Functor.map_comp, hm', ← Category.assoc, hmi]
    rw [← directSum_homotopyCategory_hom_ext N _ _ hcomp, hm', Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

/-- Every differential graded module receives a quasi-isomorphism, in the cycle-and-boundary
form, from a module orthogonal on the left to the acyclic modules (Stacks Tags 09KP and
09KM). -/
theorem exists_isQuasiIsomorphism_leftOrthogonal (A : DifferentialGradedAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v, v} A) :
    ∃ (P : DifferentialGradedModule.{u, v, v} A) (f : P ⟶ M), IsQuasiIsomorphism f ∧
      (acyclic A).leftOrthogonal ((toHomotopyCategory A).obj P) := by
  obtain ⟨P, hP, f, hf, ⟨F⟩⟩ := Stacks.DifferentialGraded.DGModule.exists_propertyP_resolution
    (Unbundled.algebra A) (Unbundled.algebra_isLawful A)
    (Unbundled.module M) (Unbundled.module_isLawful M)
  exact ⟨Unbundled.bundle hP,
    { toFun := Unbundled.restrictR (N := Unbundled.module M) f.toFun
      map_smul := fun x a => f.toFun.map_smul (MulOpposite.op a) x
      map_grading := f.map_grading
      map_d := LinearMap.ext f.commute_d }, hf,
    leftOrthogonal_acyclic_of_propertyP (bundleFiltration hP F)⟩

/-- A quasi-isomorphism becomes an isomorphism in the derived category. -/
theorem isIso_q_map_of_isQuasiIsomorphism {M M' : DifferentialGradedModule.{u, v, v} A} (g : M ⟶ M')
    (hg : IsQuasiIsomorphism g) :
    IsIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).map g) :=
  Localization.inverts ((quasiIsomorphisms A).Q) (quasiIsomorphisms A) _
    ((quasiIsomorphisms_map_iff A g).2 (quasiIso_of_isQuasiIsomorphism g hg))

/-- The direct-sum half of Stacks Tag 09QI, *"direct sums in `D(A, d)` are obtained by taking
direct sums of differential graded modules"*, in the form that the canonical functor
`Mod_{(A,d)} ⥤ D(A, d)` — the quotient by homotopy followed by the localization at the
quasi-isomorphisms — preserves direct sums. Preservation of colimits of discrete diagrams
records both that the image of a direct sum is a direct sum and that its coproduct injections
are the images of the canonical ones. -/
instance derivedCategoryQ_preservesCoproducts (A : DifferentialGradedAlgebra.{u, v} R)
    (ι : Type v) :
    PreservesColimitsOfShape (Discrete ι)
      (toHomotopyCategory.{u, v, v} A ⋙ (quasiIsomorphisms.{u, v, v} A).Q) := by
  classical
  have key : ∀ M : ι → DifferentialGradedModule.{u, v, v} A,
      PreservesColimit (Discrete.functor M)
        (toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q) := by
    intro M
    choose P f hf hP using fun i => exists_isQuasiIsomorphism_leftOrthogonal A (M i)
    have hisof : ∀ i, IsIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).map (f i)) :=
      fun i => isIso_q_map_of_isQuasiIsomorphism (f i) (hf i)
    have hisou : IsIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).map
        (directSumMap P f)) :=
      isIso_q_map_of_isQuasiIsomorphism _ (isQuasiIsomorphism_directSumMap P f hf)
    let β : Discrete.functor P ⋙ (toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q)
        ≅ Discrete.functor M ⋙ (toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q) :=
      Discrete.natIso (fun i =>
        asIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).map (f i.as)))
    refine preservesColimit_of_preserves_colimit_cocone (isColimit_directSumObj M) ?_
    refine (IsColimit.precomposeHomEquiv β _) ?_
    refine (isColimit_q_mapCocone_directSumObj P hP).ofIsoColimit
      (Cocone.ext (asIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).map
        (directSumMap P f))) ?_)
    rintro ⟨i⟩
    have hstep : (toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).map (directSumInj P i)
          ≫ (toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).map (directSumMap P f)
        = (toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).map (f i)
          ≫ (toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).map (directSumInj M i) := by
      rw [← Functor.map_comp, ← Functor.map_comp, directSumInj_comp_directSumMap]
    exact hstep
  refine ⟨fun {F} => ?_⟩
  have := key (F.obj ∘ Discrete.mk)
  exact preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := F)).symm


end Derived

namespace PropertyPFiltration

variable {P : DifferentialGradedModule.{u, v, v} A} (F : PropertyPFiltration P)

/-- The transition inclusions of a property-(P) filtration are injective. -/
theorem incl_injective (i : ℕ) : Function.Injective (F.incl i).toFun :=
  (F.admissible i).injective

/-- Each step of a property-(P) filtration is admissible short exact: the inclusion
`F i ⟶ F (i + 1)` and the projection of `F (i + 1)` onto its `i`-th graded piece form a short
exact sequence that is split as a sequence of graded modules. -/
theorem isAdmissibleShortExact_incl_quotientMap (i : ℕ) :
    IsAdmissibleShortExact (F.incl i) (F.quotientMap i) := by
  obtain ⟨r, hr⟩ := F.admissible i
  have hsurj : Function.Surjective (F.quotientMap i).toFun := F.quotient_surjective i
  have hker : LinearMap.ker (F.quotientMap i).toFun ≤
      LinearMap.ker (LinearMap.id - (F.incl i).toFun ∘ₗ r.toFun) := by
    intro x hx
    rw [F.quotient_ker i, LinearMap.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
      LinearMap.comp_apply, hr y, sub_self]
  obtain ⟨s, hs⟩ : ∃ s : (@directSumShifts R _ A (F.quotientIndex i) (F.quotientDecidableEq i)
      (F.quotientShift i)).M →ₗ[R] (F.F (i + 1)).M, ∀ x : (F.F (i + 1)).M,
        s ((F.quotientMap i).toFun x) = x - (F.incl i).toFun (r.toFun x) := by
    refine ⟨(LinearMap.ker (F.quotientMap i).toFun).liftQ
        (LinearMap.id - (F.incl i).toFun ∘ₗ r.toFun) hker ∘ₗ
      ((F.quotientMap i).toFun.quotKerEquivOfSurjective hsurj).symm.toLinearMap, fun x => ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply]
  have hzero : ∀ x : (F.F (i + 1)).M,
      (F.quotientMap i).toFun ((F.incl i).toFun (r.toFun x)) = 0 := by
    intro x
    rw [← LinearMap.mem_ker, F.quotient_ker i, LinearMap.mem_range]
    exact ⟨r.toFun x, rfl⟩
  refine { injective := F.incl_injective i
           surjective := hsurj
           exact := (F.quotient_ker i).symm
           admissibleMono := F.admissible i
           admissibleEpi := ⟨{ toFun := s, map_smul := ?_, map_grading := ?_ }, ?_⟩ }
  · intro z a
    obtain ⟨x, rfl⟩ := hsurj z
    rw [← (F.quotientMap i).map_smul, hs, hs, r.map_smul, (F.incl i).map_smul, smul_sub]
  · intro n z hz
    obtain ⟨x, hx, rfl⟩ := Hom.exists_mem_grading_of_surjective hsurj hz
    rw [hs]
    exact ((F.F (i + 1)).grading n).sub_mem hx
      ((F.incl i).map_grading n _ (r.map_grading n x hx))
  · intro z
    obtain ⟨x, rfl⟩ := hsurj z
    rw [hs, map_sub, hzero, sub_zero]

end PropertyPFiltration

/-- The derived category of a differential graded algebra has arbitrary direct sums. -/
instance hasCoproducts_derivedCategory (A : DifferentialGradedAlgebra.{u, v} R) :
    HasCoproducts.{v} (derivedCategory.{u, v, v} A) := by
  refine fun ι => ⟨fun D => ?_⟩
  let Q := (quasiIsomorphisms A).Q
  let N : ι → DifferentialGradedModule.{u, v, v} A :=
    fun i => (Q.objPreimage (D.obj (Discrete.mk i))).as
  exact ⟨(hasColimit_of_iso (F := Discrete.functor N ⋙ (toHomotopyCategory A ⋙ Q))
    (Discrete.natIso fun i => Q.objObjPreimageIso (D.obj i)).symm).exists_colimit⟩

/-- The explicit direct sum `⨁ᵢ Nᵢ` of a family of differential graded modules agrees with the
chosen coproduct of the family in `Mod_{(A,d)}`, both being colimits of the same diagram. -/
def directSumObjIsoSigma {ι : Type v} [DecidableEq ι]
    (N : ι → DifferentialGradedModule.{u, v, v} A) :
    directSumObj N ≅ ∐ N :=
  (isColimit_directSumObj N).coconePointUniqueUpToIso (coproductIsCoproduct N)

/-! ### Reindexing a direct sum along the universe lift of `ℕ`

A property-(P) filtration is indexed by `ℕ`, while the index type of a direct sum of differential
graded modules must lie in `Type v`, the universe of the modules. The two are reconciled by
reindexing along `Equiv.ulift : ULift.{v} ℕ ≃ ℕ`, which on a direct sum of modules is
`DirectSum.lequivCongrLeft`; the grading, the right action and the differential of a direct sum
being componentwise, the reindexing respects all three. -/

section Ulift

variable {X : ℕ → Stacks.DifferentialGraded.DGModule (Unbundled.algebra A)}

/-- The reindexing linear equivalence `⨁_{j : ULift.{v} ℕ} X_{j.down} ≃ ⨁_{i : ℕ} X_i`. -/
def uliftDirectSumEquiv (X : ℕ → Stacks.DifferentialGraded.DGModule (Unbundled.algebra A)) :
    (⨁ j : ULift.{v} ℕ, (X j.down).carrier) ≃ₗ[R] (⨁ i : ℕ, (X i).carrier) :=
  DirectSum.lequivCongrLeft R (Equiv.ulift.{v, 0} (α := ℕ))

/-- The reindexing equivalence reads the `i`-th component off the `ULift.up i`-th one. -/
@[simp] theorem uliftDirectSumEquiv_apply
    (X : ℕ → Stacks.DifferentialGraded.DGModule (Unbundled.algebra A))
    (x : ⨁ j : ULift.{v} ℕ, (X j.down).carrier) (i : ℕ) :
    uliftDirectSumEquiv X x i = x (ULift.up i) :=
  DirectSum.lequivCongrLeft_apply R _ x i

/-- The reindexing equivalence is compatible with the right action of the algebra, which on a
direct sum is componentwise. -/
theorem uliftDirectSumEquiv_smul (X : ℕ → Stacks.DifferentialGraded.DGModule (Unbundled.algebra A))
    (a : A.Aᵐᵒᵖ) (x : ⨁ j : ULift.{v} ℕ, (X j.down).carrier) :
    uliftDirectSumEquiv X (a • x) = a • uliftDirectSumEquiv X x := by
  refine DirectSum.ext fun i => ?_
  rw [uliftDirectSumEquiv_apply, DirectSum.smul_apply, DirectSum.smul_apply,
    uliftDirectSumEquiv_apply]

/-- The reindexing equivalence commutes with the differential of a direct sum, which is
componentwise. -/
theorem uliftDirectSumEquiv_d (X : ℕ → Stacks.DifferentialGraded.DGModule (Unbundled.algebra A))
    (x : ⨁ j : ULift.{v} ℕ, (X j.down).carrier) :
    uliftDirectSumEquiv X
        (Stacks.DifferentialGraded.DGModule.directSumD (fun j : ULift.{v} ℕ => X j.down) x)
      = Stacks.DifferentialGraded.DGModule.directSumD X (uliftDirectSumEquiv X x) := by
  refine DirectSum.ext fun i => ?_
  rw [uliftDirectSumEquiv_apply, DifferentialGraded.NativeCover.Native.directSum_d_apply,
    DifferentialGraded.NativeCover.Native.directSum_d_apply, uliftDirectSumEquiv_apply]

/-- The reindexing of a direct sum of differential graded modules along `ULift.{v} ℕ ≃ ℕ`, as a
homomorphism of differential graded modules. -/
def uliftDirectSumHom (hX : ∀ i, (X i).IsLawful)
    (hS : (Stacks.DifferentialGraded.DGModule.directSum X).IsLawful) :
    directSumObj (fun j : ULift.{v} ℕ => Unbundled.bundle (hX j.down)) ⟶
      Unbundled.bundle hS where
  toFun := (uliftDirectSumEquiv X).toLinearMap
  map_smul x a := uliftDirectSumEquiv_smul X (MulOpposite.op a) x
  map_grading _ _ hx i := hx (ULift.up i)
  map_d := LinearMap.ext (uliftDirectSumEquiv_d X)

/-- A direct sum over `ℕ` is the direct sum of the universe-lifted family over
`ULift.{v} ℕ`. -/
def uliftDirectSumIso (hX : ∀ i, (X i).IsLawful)
    (hS : (Stacks.DifferentialGraded.DGModule.directSum X).IsLawful) :
    Unbundled.bundle hS ≅ directSumObj (fun j : ULift.{v} ℕ => Unbundled.bundle (hX j.down)) :=
  (Hom.isoOfBijective (uliftDirectSumHom hX hS) (uliftDirectSumEquiv X).bijective).symm

end Ulift

/-! ### Direct sums of shifts of the algebra -/

/-- The descent of the coprojections `A[kⱼ] ⟶ ⨁ᵢ A[kᵢ]` of
`DifferentialGradedModule.directSumShifts` along the explicit direct sum is the identity. -/
theorem directSumDescLinear_directSumShiftsInj_apply (A : DifferentialGradedAlgebra.{u, v} R)
    {ι : Type v} [DecidableEq ι] (k : ι → ℤ) (x : ⨁ _ : ι, A.A) :
    directSumDescLinear (fun i => shift (regularModule A) (k i))
      (directSumShiftsInj A k) x = x := by
  induction x using DirectSum.induction_on with
  | zero => exact map_zero _
  | of i y =>
      rw [← DirectSum.lof_eq_of (R := R)]
      exact directSumDescLinear_lof (fun i => shift (regularModule A) (k i))
        (directSumShiftsInj A k) i y
  | add y z hy hz => exact (map_add _ y z).trans (congrArg₂ (· + ·) hy hz)

/-- **The explicit direct sum of the shifts `A[kᵢ]` is
`DifferentialGradedModule.directSumShifts`.** The comparison is the descent of the coprojections
of the latter, whose underlying map is the identity of `⨁ᵢ A`. -/
def directSumObjIsoDirectSumShifts (A : DifferentialGradedAlgebra.{u, v} R)
    {ι : Type v} [DecidableEq ι] (k : ι → ℤ) :
    directSumObj (fun i => shift (regularModule A) (k i)) ≅ directSumShifts A k :=
  Hom.isoOfBijective (directSumDesc _ (directSumShiftsInj A k)) (by
    have hid := directSumDescLinear_directSumShiftsInj_apply A k
    exact ⟨fun a b h => by rwa [← hid a, ← hid b], fun y => ⟨y, hid y⟩⟩)

/-! ### The telescope of a property-(P) resolution -/

/-- **The telescope of a property-(P) resolution** (Tags 09KP and 09KL, in the bundled encoding).
Every differential graded `A`-module `M` receives a quasi-isomorphism `f : P ⟶ M` from a module
`P` carrying a property-(P) filtration `F`, and `P` is the quotient term of an admissible short
exact sequence `0 → S → S → P → 0` whose outer term `S` is the direct sum of the stages of `F`.
The stages are indexed by `ℕ`, so the direct sum is taken over `ULift.{v} ℕ`. -/
theorem exists_propertyP_telescope (A : DifferentialGradedAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v, v} A) :
    ∃ (P S : DifferentialGradedModule.{u, v, v} A) (f : P ⟶ M) (a : S ⟶ S) (b : S ⟶ P)
      (F : PropertyPFiltration P),
      QuasiIso ((forgetToCochainComplex A).map f) ∧ IsAdmissibleShortExact a b ∧
        Nonempty (S ≅ directSumObj (fun j : ULift.{v} ℕ => F.F j.down)) := by
  obtain ⟨P₀, hP, f₀, hf, ⟨F₀⟩⟩ := Stacks.DifferentialGraded.DGModule.exists_propertyP_resolution
    (Unbundled.algebra A) (Unbundled.algebra_isLawful A)
    (Unbundled.module M) (Unbundled.module_isLawful M)
  obtain ⟨hS, α, β, _, _, hab⟩ :=
    Stacks.DifferentialGraded.DGModule.admissible_ses_of_propertyP hP F₀
  have hX : ∀ i, ((F₀.F i).toDGModule).IsLawful :=
    fun i => Unbundled.dgSubmodule_isLawful hP (F₀.F i) (F₀.F_lawful i)
  refine ⟨Unbundled.bundle hP, Unbundled.bundle hS,
    { toFun := Unbundled.restrictR (N := Unbundled.module M) f₀.toFun
      map_smul := fun x a => f₀.toFun.map_smul (MulOpposite.op a) x
      map_grading := f₀.map_grading
      map_d := LinearMap.ext f₀.commute_d },
    Unbundled.bundleHom hS hS α, Unbundled.bundleHom hS hP β,
    bundleFiltration hP F₀, quasiIso_of_isQuasiIsomorphism _ hf, ?_, ⟨uliftDirectSumIso hX hS⟩⟩
  exact { injective := hab.injective
          surjective := hab.surjective
          exact := Submodule.ext fun x => SetLike.ext_iff.mp hab.exact x
          admissibleMono := ⟨Unbundled.bundleGradedHom hS hS hab.admissibleMono.2.choose,
            hab.admissibleMono.2.choose_spec⟩
          admissibleEpi := ⟨Unbundled.bundleGradedHom hP hS hab.admissibleEpi.2.choose,
            hab.admissibleEpi.2.choose_spec⟩ }



/-! #### The dévissage -/

/-- The dévissage with the carrier of the algebra in a universe of its own. *"Let `R` be
a ring. Let `(A, d)` be a differential graded `R`-algebra. Using P-resolutions we can sometimes
reduce statements about general objects of `D(A, d)` to statements about `A[k]`. Namely, let `T`
be a property of objects of `D(A, d)` and assume that*

1. *if `Kᵢ`, `i ∈ I` is a family of objects of `D(A, d)` and `T(Kᵢ)` holds for all `i ∈ I`, then
   `T(⨁ Kᵢ)`,*
2. *if `K → L → M → K[1]` is a distinguished triangle of `D(A, d)` and `T` holds for two, then
   `T` holds for the third object, and*
3. *`T(A[k])` holds for all `k ∈ ℤ`.*

*Then `T` holds for all objects of `D(A, d)`."*

This is `DifferentialGradedModule.property_of_coproducts_of_two_out_of_three_of_shifts` with the
universe of the base ring `R` and the universe of the carrier of `A` independent of one another.

The object denoted `A` in the source is the image of the regular module `A` in `D(A, d)`, so
hypothesis (3) is `T` on each shift of that image. Hypothesis (2) is stated as the conjunction of
its three implications, one for each position of the triangle. Isomorphism invariance of `T` is
not assumed. -/
@[stacks 0FQE "algebra carrier universe independent of the base ring; cone-triangle structure"]
theorem property_of_coproducts_of_two_out_of_three_of_shifts
    (A : DifferentialGradedAlgebra.{u, v} R) (T : derivedCategory.{u, v, v} A → Prop)
    (hsum : ∀ {ι : Type v} (K : ι → derivedCategory.{u, v, v} A), (∀ i, T (K i)) → T (∐ K))
    (htriangle : ∀ Δ : Pretriangulated.Triangle (derivedCategory.{u, v, v} A),
      Δ ∈ Pretriangulated.distinguishedTriangles →
      (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
      (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁))
    (hshift : ∀ k : ℤ, T (((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).obj
      (regularModule A))⟦k⟧)) :
    ∀ K : derivedCategory.{u, v, v} A, T K := by
  classical
  let L := (quasiIsomorphisms.{u, v, v} A).Q
  let Q := toHomotopyCategory.{u, v, v} A ⋙ L
  have hiso : ∀ {X Y : derivedCategory.{u, v, v} A}, (X ≅ Y) → T X → T Y :=
    iso_invariant_of_two_out_of_three T htriangle (hshift 0)
  have hcoprod : ∀ {ι : Type v} [DecidableEq ι] (N : ι → DifferentialGradedModule.{u, v, v} A),
      (∀ i, T (Q.obj (N i))) → T (Q.obj (directSumObj N)) := by
    intro ι _ N hN
    exact hiso ((Q.mapIso (directSumObjIsoSigma N)).trans
      (PreservesCoproduct.iso Q N)).symm (hsum _ hN)
  have hpieces : ∀ {ι : Type v} [DecidableEq ι] (k : ι → ℤ),
      T (Q.obj (directSumShifts A k)) := by
    intro ι _ k
    refine hiso (Q.mapIso (directSumObjIsoDirectSumShifts A k)) (hcoprod _ fun i => ?_)
    exact hiso ((Q.commShiftIso (k i)).app (regularModule A)).symm (hshift (k i))
  have hses : ∀ {K₁ K₂ K₃ : DifferentialGradedModule.{u, v, v} A} (f : K₁ ⟶ K₂) (g : K₂ ⟶ K₃),
      IsAdmissibleShortExact f g →
        (T (Q.obj K₁) → T (Q.obj K₂) → T (Q.obj K₃)) ∧
        (T (Q.obj K₁) → T (Q.obj K₃) → T (Q.obj K₂)) := by
    intro K₁ K₂ K₃ f g hfg
    obtain ⟨q, _, ec, _, _, _⟩ := exists_mappingConeTriangle_iso_associatedTriangle f g hfg
    have hcone : coneTriangle f ∈ Pretriangulated.distinguishedTriangles :=
      ⟨K₁, K₂, f, ⟨Iso.refl _⟩⟩
    have h := htriangle _ (L.map_distinguished _ hcone)
    have e : Q.obj (coneObject f) ≅ Q.obj K₃ :=
      L.mapIso
        { hom := ec.hom.hom₃
          inv := ec.inv.hom₃
          hom_inv_id := congrArg Pretriangulated.TriangleMorphism.hom₃ ec.hom_inv_id
          inv_hom_id := congrArg Pretriangulated.TriangleMorphism.hom₃ ec.inv_hom_id }
    exact ⟨fun h₁ h₂ => hiso e (h.1 h₁ h₂), fun h₁ h₃ => h.2.1 h₁ (hiso e.symm h₃)⟩
  intro K
  obtain ⟨P, S, f, a, b, F, hf, hab, ⟨e⟩⟩ :=
    exists_propertyP_telescope A (L.objPreimage K).as
  have hF : ∀ i, T (Q.obj (F.F i)) := by
    intro i
    induction i with
    | zero =>
        let _ := F.bottomDecidableEq
        exact hiso (Q.mapIso (Hom.isoOfBijective F.bottomMap F.bottom_bijective)).symm
          (hpieces F.bottomShift)
    | succ i ih =>
        let _ := F.quotientDecidableEq i
        exact (hses _ _ (F.isAdmissibleShortExact_incl_quotientMap i)).2 ih
          (hpieces (F.quotientShift i))
  have hS : T (Q.obj S) := hiso (Q.mapIso e).symm (hcoprod _ fun j => hF j.down)
  have hP : T (Q.obj P) := (hses a b hab).1 hS hS
  have : IsIso (Q.map f) :=
    Localization.inverts L (quasiIsomorphisms A) _ ((quasiIsomorphisms_map_iff A f).2 hf)
  exact hiso (asIso (Q.map f) ≪≫ L.objObjPreimageIso K) hP

end GeneralDerived

end General

end DifferentialGradedModule

end
