module

public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Property-(P) resolutions at independent universes

Let `R` be a commutative ring and `(A, d)` a differential graded `R`-algebra whose carrier lies
in a universe `v` of its own. This file transports the existence of property-(P) resolutions
(Stacks Tag 09KP) from the unbundled encoding `Stacks.DifferentialGraded.DGAlgebra` /
`Stacks.DifferentialGraded.DGModule` to the bundled encoding `DifferentialGradedAlgebra` /
`DifferentialGradedModule`, with the base ring, the algebra and the module in three independent
universes.

## Main definitions

* `DifferentialGradedModule.General.directSumShifts`: the direct sum of shifts `⨁ i, A[k i]`,
  as a bundled differential graded `A`-module, for a cell index type in an arbitrary universe.
* `DifferentialGradedModule.General.PropertyPFiltration`: the data of a filtration exhibiting
  property (P), at independent universes.
* `DifferentialGradedModule.General.IsQuasiIsomorphism`: the cycle-and-boundary criterion for
  being a quasi-isomorphism.

## Main results

* `DifferentialGradedModule.General.quasiIso_of_isQuasiIsomorphism`: the cycle-and-boundary
  criterion implies that the underlying cochain map is a quasi-isomorphism in Mathlib's sense.
* `DifferentialGradedModule.General.exists_propertyP_resolution`: every differential graded
  module whose carrier universe absorbs the algebra's receives a quasi-isomorphism from a
  differential graded module carrying a property-(P) filtration.

## References

* [Stacks Project, Tag 09KP](https://stacks.math.columbia.edu/tag/09KP)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum

namespace DifferentialGradedModule.General

universe u v w

variable {R : Type u} [CommRing R]

/-! ### Transport between the unbundled and the bundled encoding -/

namespace Unbundled

/-- The unbundled differential graded algebra underlying a bundled one: the same carrier,
grading and differential, with the laws recorded separately. -/
abbrev algebra (A : DifferentialGradedAlgebra.{u, v} R) :
    Stacks.DifferentialGraded.DGAlgebra.{u, v} R where
  carrier := A.A
  grading := A.grading
  d := A.d

/-- The laws of a bundled differential graded algebra, in unbundled form. -/
theorem algebra_isLawful (A : DifferentialGradedAlgebra.{u, v} R) : (algebra A).IsLawful where
  d_mem := A.d_mem
  d_comp_d x := LinearMap.congr_fun A.d_comp_d x
  leibniz n m a b ha hb := by
    simpa only [DifferentialGradedModule.Unbundled.negOnePow_cast] using A.leibniz n m a b ha hb

variable {A : DifferentialGradedAlgebra.{u, v} R}

/-- The right `A`-action on an unbundled differential graded module, in the spelling `A.Aᵐᵒᵖ`
used by the bundled encoding rather than `(algebra A).carrierᵐᵒᵖ`. -/
instance moduleOp (M : Stacks.DifferentialGraded.DGModule (algebra A)) :
    Module A.Aᵐᵒᵖ M.carrier :=
  M.moduleA

/-- The unbundled differential graded module underlying a bundled one. -/
abbrev module (M : DifferentialGradedModule.{u, v, w} A) :
    Stacks.DifferentialGraded.DGModule (algebra A) where
  carrier := M.M
  smul_def r x := (IsScalarTower.algebraMap_smul A.Aᵐᵒᵖ r x).symm
  grading n := (M.grading n).toAddSubgroup
  d := M.d

/-- The laws of a bundled differential graded module, in unbundled form. -/
theorem module_isLawful (M : DifferentialGradedModule.{u, v, w} A) : (module M).IsLawful where
  isInternal := DirectSum.Decomposition.isInternal M.grading
  grading_smul := M.smul_mem
  d_mem := M.d_mem
  d_comp_d x := LinearMap.congr_fun M.d_comp_d x
  leibniz n m x a hx ha := by
    simpa only [DifferentialGradedModule.Unbundled.negOnePow_cast] using M.leibniz n m x a hx ha

/-- A lawful unbundled differential graded module, as a bundled one. The grading is promoted
from additive subgroups to `R`-submodules by `DifferentialGraded.NativeCover.Native.grading`,
and the internality of that grading provides the direct-sum decomposition the bundled encoding
asks for. -/
abbrev bundle {M : Stacks.DifferentialGraded.DGModule (algebra A)} (hM : M.IsLawful) :
    DifferentialGradedModule.{u, v, w} A where
  M := M.carrier
  addCommGroup := M.addCommGroup
  module := M.moduleR
  rmodule := M.moduleA
  isScalarTower := IsScalarTower.of_algebraMap_smul (fun r x => (M.smul_def r x).symm)
  grading := DifferentialGraded.NativeCover.Native.grading M hM
  decomposition := (show DirectSum.IsInternal (DifferentialGraded.NativeCover.Native.grading M hM)
    from hM.isInternal).chooseDecomposition
  smul_mem := hM.grading_smul
  d := M.d
  d_comp_d := LinearMap.ext hM.d_comp_d
  d_mem := hM.d_mem
  leibniz n m x a hx ha := by
    simpa only [DifferentialGradedModule.Unbundled.negOnePow_cast] using hM.leibniz n m x a hx ha

/-- An `Aᵐᵒᵖ`-linear map between unbundled differential graded modules, viewed as the
`R`-linear map the bundled encoding asks for. -/
def restrictR {M : Stacks.DifferentialGraded.DGModule (algebra A)}
    {N : Stacks.DifferentialGraded.DGModule (algebra A)}
    (f : M.carrier →ₗ[(algebra A).carrierᵐᵒᵖ] N.carrier) : M.carrier →ₗ[R] N.carrier where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    rw [M.smul_def, N.smul_def, map_smul]
    rfl

/-- The `R`-linear map `restrictR f` agrees with `f` on every element. -/
@[simp] theorem restrictR_apply {M : Stacks.DifferentialGraded.DGModule (algebra A)}
    {N : Stacks.DifferentialGraded.DGModule (algebra A)}
    (f : M.carrier →ₗ[(algebra A).carrierᵐᵒᵖ] N.carrier) (x : M.carrier) :
    restrictR f x = f x := rfl

/-- A graded homomorphism of unbundled differential graded modules, bundled. -/
abbrev bundleGradedHom {M : Stacks.DifferentialGraded.DGModule (algebra A)}
    {N : Stacks.DifferentialGraded.DGModule (algebra A)}
    (hM : M.IsLawful) (hN : N.IsLawful) (f : Stacks.DifferentialGraded.DGModule.GradedHom M N) :
    GradedHom (bundle hM) (bundle hN) where
  toFun := restrictR f.toFun
  map_smul x a := f.toFun.map_smul (MulOpposite.op a) x
  map_grading := f.map_grading

/-- A homomorphism of unbundled differential graded modules, bundled. -/
abbrev bundleHom {M : Stacks.DifferentialGraded.DGModule (algebra A)}
    {N : Stacks.DifferentialGraded.DGModule (algebra A)}
    (hM : M.IsLawful) (hN : N.IsLawful) (f : Stacks.DifferentialGraded.DGModule.Hom M N) :
    Hom (bundle hM) (bundle hN) where
  toFun := restrictR f.toFun
  map_smul x a := f.toFun.map_smul (MulOpposite.op a) x
  map_grading := f.map_grading
  map_d := LinearMap.ext f.commute_d

/-- An unbundled differential graded isomorphism is bijective. -/
theorem iso_bijective {M : Stacks.DifferentialGraded.DGModule (algebra A)}
    {N : Stacks.DifferentialGraded.DGModule (algebra A)}
    (e : Stacks.DifferentialGraded.DGModule.Iso M N) : Function.Bijective e.toFun :=
  ⟨Function.LeftInverse.injective e.left_inv, Function.RightInverse.surjective e.right_inv⟩

/-- A lawful differential graded submodule of a lawful differential graded module is itself a
lawful differential graded module. -/
theorem dgSubmodule_isLawful {M : Stacks.DifferentialGraded.DGModule (algebra A)}
    (hM : M.IsLawful) (K : Stacks.DifferentialGraded.DGModule.DGSubmodule M) (hK : K.IsLawful) :
    K.toDGModule.IsLawful := by
  refine ⟨hK, fun n m x a hx ha => hM.grading_smul n m (x : K.toSubmodule).val a hx ha,
    fun n x hx => hM.d_mem n (x : K.toSubmodule).val hx,
    fun x => Subtype.ext (hM.d_comp_d (x : K.toSubmodule).val),
    fun n m x a hx ha => Subtype.ext (hM.leibniz n m (x : K.toSubmodule).val a hx ha)⟩

/-- A direct sum of shifts of the algebra is lawful. -/
theorem shiftSum_isLawful (A : DifferentialGradedAlgebra.{u, v} R)
    {ι : Type w} [DecidableEq ι] (k : ι → ℤ) :
    (Stacks.DifferentialGraded.DGModule.directSum
      (fun i => Stacks.DifferentialGraded.DGModule.shiftFree (algebra A) (k i))).IsLawful := by
  have hint : DirectSum.IsInternal (Stacks.DifferentialGraded.DGModule.directSumGrading
      (fun i => Stacks.DifferentialGraded.DGModule.shiftFree (algebra A) (k i))) :=
    (DifferentialGraded.NativeCover.Native.ofModule_isLawful (A := algebra A)
      (hA := algebra_isLawful A)
      (DifferentialGraded.NativeCover.ShiftSum.shiftDG R A.A A.grading
        (DifferentialGraded.NativeCover.Native.algebra (algebra A) (algebra_isLawful A)) ι
          k)).isInternal
  exact DifferentialGradedModule.Unbundled.directSum_isLawful _
    (fun i => DifferentialGradedModule.Unbundled.shift_isLawful (algebra_isLawful A)
      (DifferentialGradedModule.Unbundled.free_isLawful (algebra_isLawful A)) (k i)) hint

end Unbundled

/-! ### Direct sums of shifts -/

/-- The direct sum of shifts `⨁ i, A[k i]` of the algebra, as a bundled differential graded
`A`-module: the underlying right module is `⨁ i, A`, an element is homogeneous of degree `n`
exactly when its `i`-th component lies in `A^{n + k i}`, and the differential acts on the `i`-th
component by `(-1)^{|k i|} d_A`.

The cell index type may be in any universe `w`; the carrier is then in `Type (max w v)`, where
`v` is the universe of the algebra's carrier. -/
@[implicit_reducible]
def directSumShifts (A : DifferentialGradedAlgebra.{u, v} R) {ι : Type w} [DecidableEq ι]
    (k : ι → ℤ) : DifferentialGradedModule.{u, v, max w v} A :=
  Unbundled.bundle (Unbundled.shiftSum_isLawful A k)

variable {A : DifferentialGradedAlgebra.{u, v} R}

/-- Membership in the degree-`n` piece of a direct sum of shifts is componentwise: `x` is
homogeneous of degree `n` exactly when `x i ∈ A^{n + k i}` for every cell `i`. -/
theorem mem_directSumShifts_grading {ι : Type w} [DecidableEq ι] (k : ι → ℤ) (n : ℤ)
    (x : ⨁ _ : ι, A.A) :
    x ∈ (directSumShifts A k).grading n ↔ ∀ i, x i ∈ A.grading (n + k i) :=
  Iff.rfl

/-- The differential of a direct sum of shifts, on the `j`-th coprojection: it is the
differential of the algebra on that summand, carrying the sign of that summand's shift. -/
theorem directSumShifts_d_lof {ι : Type w} [DecidableEq ι] (k : ι → ℤ) (j : ι) (x : A.A) :
    (directSumShifts A k).d (DirectSum.lof R ι (fun _ => A.A) j x)
      = DirectSum.lof R ι (fun _ => A.A) j (((-1 : ℤ) ^ (k j).natAbs) • A.d x) :=
  DirectSum.toModule_lof (R := R) (M := fun _ : ι => A.A) (N := (⨁ _ : ι, A.A)) j x

/-! ### Property (P) -/

/-- A *property-(P) filtration* of a differential graded `A`-module `P`: an exhaustive increasing
filtration `0 = F_{-1} ⊆ F_0 ⊆ F_1 ⊆ ⋯ ⊆ P` by differential graded submodules whose inclusions are
admissible monomorphisms and whose successive quotients are direct sums of shifts of `A`.

The stages are presented by injective homomorphisms `ι i : F i ⟶ P` rather than as submodules,
and the graded pieces by surjective homomorphisms onto direct sums of shifts with the prescribed
kernel; the implicit stage `F_{-1} = 0` is encoded by the requirement that `F 0` itself be
isomorphic to a direct sum of shifts.

The cell index types are taken in the universe of the filtered module; the direct sums of shifts
are then in `Type (max w v)`. -/
structure PropertyPFiltration (P : DifferentialGradedModule.{u, v, w} A) where
  /-- The stages `F i` of the filtration. -/
  F : ℕ → DifferentialGradedModule.{u, v, w} A
  /-- The embedding of the `i`-th stage into the filtered module. -/
  ι : ∀ i, Hom (F i) P
  /-- Each stage embeds into the filtered module. -/
  injective : ∀ i, Function.Injective (ι i).toFun
  /-- The transition inclusion `F i ⟶ F (i + 1)`. -/
  incl : ∀ i, Hom (F i) (F (i + 1))
  /-- The transition inclusions are compatible with the embeddings into `P`. -/
  incl_comp : ∀ i x, (ι (i + 1)).toFun ((incl i).toFun x) = (ι i).toFun x
  /-- Property (P)(2): every transition inclusion is an admissible monomorphism. -/
  admissible : ∀ i, IsAdmissibleMono (incl i)
  /-- Property (P)(1): the filtration is exhaustive. -/
  exhaustive : ∀ x : P.M, ∃ i y, (ι i).toFun y = x
  /-- The cells of the bottom graded piece `F 0 / F_{-1} = F 0`. -/
  bottomIndex : Type w
  /-- Decidable equality of the bottom cells, needed to form their direct sum. -/
  bottomDecidableEq : DecidableEq bottomIndex
  /-- The shift attached to each bottom cell. -/
  bottomShift : bottomIndex → ℤ
  /-- Property (P)(3) for the bottom piece, as a homomorphism onto the direct sum of shifts. -/
  bottomMap : Hom (F 0) (@directSumShifts _ _ _ _ bottomDecidableEq bottomShift)
  /-- The bottom map is an isomorphism. -/
  bottom_bijective : Function.Bijective bottomMap.toFun
  /-- The cells of the `i`-th graded piece `F (i + 1) / F i`. -/
  quotientIndex : ℕ → Type w
  /-- Decidable equality of the cells of each graded piece. -/
  quotientDecidableEq : ∀ i, DecidableEq (quotientIndex i)
  /-- The shift attached to each cell of the `i`-th graded piece. -/
  quotientShift : ∀ i, quotientIndex i → ℤ
  /-- Property (P)(3): the projection of `F (i + 1)` onto its `i`-th graded piece. -/
  quotientMap : ∀ i, Hom (F (i + 1))
    (@directSumShifts _ _ _ _ (quotientDecidableEq i) (quotientShift i))
  /-- The projection onto the `i`-th graded piece is surjective. -/
  quotient_surjective : ∀ i, Function.Surjective (quotientMap i).toFun
  /-- Its kernel is the previous stage, so the graded piece really is `F (i + 1) / F i`. -/
  quotient_ker : ∀ i, LinearMap.ker (quotientMap i).toFun = LinearMap.range (incl i).toFun

/-! ### Quasi-isomorphisms -/

/-- The cycle-and-boundary criterion for a homomorphism of differential graded modules to be a
quasi-isomorphism: in every degree, every cocycle of the target is congruent modulo a boundary
to the image of a cocycle of the source, and a cocycle of the source whose image is a boundary
is itself a boundary. -/
def IsQuasiIsomorphism {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) : Prop :=
  ∀ n : ℤ,
    (∀ y : N.M, y ∈ N.grading n → N.d y = 0 →
      ∃ x : M.M, x ∈ M.grading n ∧ M.d x = 0 ∧
        ∃ z : N.M, z ∈ N.grading (n - 1) ∧ N.d z = y - f.toFun x) ∧
    (∀ x : M.M, x ∈ M.grading n → M.d x = 0 →
      (∃ z : N.M, z ∈ N.grading (n - 1) ∧ N.d z = f.toFun x) →
        ∃ z : M.M, z ∈ M.grading (n - 1) ∧ M.d z = x)

/-- A map induced on quotients by `Submodule.mapQ` is bijective as soon as it hits every class of
the target and reflects membership in the subgroup divided out. -/
private theorem mapQ_bijective {X Y : Type w} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] {p : Submodule R X} {q : Submodule R Y} (g : X →ₗ[R] Y)
    (h : p ≤ q.comap g) (hs : ∀ y : Y, ∃ x : X, g x - y ∈ q)
    (hi : ∀ x : X, g x ∈ q → x ∈ p) :
    Function.Bijective (Submodule.mapQ p q g h) := by
  refine ⟨fun a b hab => ?_, fun c => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective p a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective p b
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hab
    exact (Submodule.Quotient.eq p).2 (hi (a - b) (by rwa [map_sub]))
  · obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective q c
    obtain ⟨x, hx⟩ := hs c
    exact ⟨Submodule.Quotient.mk x, by rwa [Submodule.mapQ_apply, Submodule.Quotient.eq]⟩

/-- The forgetful functor to cochain complexes is `toCochainComplex` on objects. -/
private theorem forget_obj (M : DifferentialGradedModule.{u, v, w} A) :
    (forgetToCochainComplex A).obj M = M.toCochainComplex := rfl

/-- The forgetful functor to cochain complexes is `Hom.toCochainMap` on morphisms. -/
private theorem forget_map {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    (forgetToCochainComplex A).map f = f.toCochainMap := rfl

/-- A morphism of short complexes of modules is a quasi-isomorphism as soon as the
cycle-and-boundary criterion holds: every cycle of the target is the image of a cycle of the
source modulo a boundary, and a cycle of the source whose image is a boundary is a boundary. -/
private theorem shortComplex_quasiIso_of_criterion
    {S T : ShortComplex (ModuleCat.{w} R)} (φ : S ⟶ T)
    (hsurj : ∀ y : T.X₂, T.g.hom y = 0 →
      ∃ x : S.X₂, S.g.hom x = 0 ∧ ∃ w : T.X₁, T.f.hom w = φ.τ₂.hom x - y)
    (hinj : ∀ x : S.X₂, S.g.hom x = 0 →
      (∃ w : T.X₁, T.f.hom w = φ.τ₂.hom x) → ∃ v : S.X₁, S.f.hom v = x) :
    ShortComplex.QuasiIso φ := by
  have hcomm : ∀ x : S.X₂, T.g.hom (φ.τ₂.hom x) = φ.τ₃.hom (S.g.hom x) := by
    intro x
    simpa using LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp φ.comm₂₃) x
  have hcommf : ∀ v : S.X₁, T.f.hom (φ.τ₁.hom v) = φ.τ₂.hom (S.f.hom v) := by
    intro v
    simpa using LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp φ.comm₁₂) v
  have hKmem : ∀ x : LinearMap.ker S.g.hom,
      φ.τ₂.hom (x : S.X₂) ∈ LinearMap.ker T.g.hom := by
    intro x
    rw [LinearMap.mem_ker, hcomm, show S.g.hom (x : S.X₂) = 0 from x.2, map_zero]
  let φKmap : ↥(LinearMap.ker S.g.hom) →ₗ[R] ↥(LinearMap.ker T.g.hom) :=
    (φ.τ₂.hom ∘ₗ (LinearMap.ker S.g.hom).subtype).codRestrict _ hKmem
  have hφKrange : LinearMap.range S.moduleCatToCycles ≤
      Submodule.comap φKmap (LinearMap.range T.moduleCatToCycles) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨φ.τ₁.hom v, Subtype.ext (hcommf v)⟩
  let γ : ShortComplex.LeftHomologyMapData φ
      S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData :=
    { φK := ModuleCat.ofHom φKmap
      φH := ModuleCat.ofHom (Submodule.mapQ _ _ φKmap hφKrange)
      commi := by ext x; rfl
      commf' := by ext v; exact Subtype.ext (hcommf v).symm
      commπ := by ext x; rfl }
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  show Function.Bijective (Submodule.mapQ _ _ φKmap hφKrange)
  refine mapQ_bijective _ _ (fun y => ?_) (fun x hx => ?_)
  · obtain ⟨x, hx, w, hw⟩ := hsurj (y : T.X₂) y.2
    exact ⟨⟨x, hx⟩, ⟨w, Subtype.ext hw⟩⟩
  · obtain ⟨w, hw⟩ := hx
    obtain ⟨v, hv⟩ := hinj (x : S.X₂) x.2 ⟨w, congrArg Subtype.val hw⟩
    exact ⟨v, Subtype.ext hv⟩

/-- The cycle-and-boundary criterion implies that the underlying cochain map of a homomorphism
of differential graded modules is a quasi-isomorphism in the sense of Mathlib. -/
theorem quasiIso_of_isQuasiIsomorphism {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N)
    (hf : IsQuasiIsomorphism f) : QuasiIso ((forgetToCochainComplex A).map f) := by
  rw [quasiIso_iff]
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  rw [quasiIsoAt_iff' _ m (m + 1) (m + 1 + 1) (by simp) (by simp)]
  refine shortComplex_quasiIso_of_criterion _ ?_ ?_ <;>
    simp only [forget_obj, forget_map, HomologicalComplex.shortComplexFunctor'_obj_g,
      HomologicalComplex.shortComplexFunctor'_obj_f, toCochainComplex_d,
      HomologicalComplex.shortComplexFunctor'_map_τ₂, Hom.toCochainMap_f]
  · intro y hy
    obtain ⟨x, hx, hdx, z, hz, hzeq⟩ :=
      (hf (m + 1)).1 y.1 y.2 (congrArg Subtype.val hy)
    refine ⟨⟨x, hx⟩, Subtype.ext hdx, ⟨-z, by simpa using neg_mem hz⟩, Subtype.ext ?_⟩
    exact (map_neg _ _).trans (by rw [hzeq, neg_sub]; rfl)
  · rintro x hx ⟨w, hw⟩
    obtain ⟨z, hz, hzeq⟩ := (hf (m + 1)).2 x.1 x.2 (congrArg Subtype.val hx)
      ⟨w.1, by simpa using w.2, congrArg Subtype.val hw⟩
    exact ⟨⟨z, by simpa using hz⟩, Subtype.ext hzeq⟩

/-! ### Existence of property-(P) resolutions -/

/-- The property-(P) filtration produced by the unbundled development, bundled. -/
def bundleFiltration {P : Stacks.DifferentialGraded.DGModule (Unbundled.algebra A)}
    (hP : P.IsLawful)
    (F : Stacks.DifferentialGraded.DGModule.PropertyPFiltration P) :
    PropertyPFiltration (Unbundled.bundle hP) := by
  let hF := fun i => Unbundled.dgSubmodule_isLawful hP (F.F i) (F.F_lawful i)
  letI := F.bottomShiftIndexDec
  let hB := Unbundled.shiftSum_isLawful A F.bottomShiftAmount
  let hQ := fun i => @Unbundled.shiftSum_isLawful R _ A (F.shiftIndex i) (F.shiftIndexDec i)
    (F.shiftAmount i)
  choose q hs hk using F.isQuotient
  refine {
    F := fun i => Unbundled.bundle (hF i)
    ι := fun i => Unbundled.bundleHom (hF i) hP (F.F i).incl
    injective := fun _ => Subtype.val_injective
    incl := fun i => Unbundled.bundleHom (hF i) (hF (i + 1)) (F.inclHom i)
    incl_comp := F.inclHom_apply
    admissible := ?_
    exhaustive := ?_
    bottomIndex := F.bottomShiftIndex
    bottomDecidableEq := F.bottomShiftIndexDec
    bottomShift := F.bottomShiftAmount
    bottomMap := Unbundled.bundleHom (hF 0) hB F.bottomIso.toHom
    bottom_bijective := Unbundled.iso_bijective F.bottomIso
    quotientIndex := F.shiftIndex
    quotientDecidableEq := F.shiftIndexDec
    quotientShift := F.shiftAmount
    quotientMap := fun i =>
      Unbundled.bundleHom (hF (i + 1)) (hQ i) ((F.quotientIso i).toHom.comp (q i))
    quotient_surjective := fun i =>
      (Unbundled.iso_bijective (F.quotientIso i)).surjective.comp (hs i)
    quotient_ker := ?_ }
  · intro i
    obtain ⟨_, r, hr⟩ := F.admissible i
    exact ⟨Unbundled.bundleGradedHom (hF (i + 1)) (hF i) r, hr⟩
  · intro x
    obtain ⟨i, hi⟩ := F.exhaustive x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · intro i
    ext x
    change (F.quotientIso i).toFun ((q i).toFun x) = 0 ↔ ∃ y, (F.inclHom i).toFun y = x
    rw [← map_zero (F.quotientIso i).toFun,
      (Unbundled.iso_bijective (F.quotientIso i)).injective.eq_iff]
    exact SetLike.ext_iff.mp (hk i) x

/-- **Property-(P) resolutions exist**, at independent universes. Every right
differential graded module `M` over a differential graded algebra `(A, d)` whose carrier
universe absorbs the algebra's receives a quasi-isomorphism from a differential graded
`A`-module `P` carrying a property-(P) filtration: an exhaustive increasing filtration by
differential graded submodules with admissible inclusions whose successive quotients are direct
sums of shifts of `A`. -/
theorem exists_propertyP_resolution (A : DifferentialGradedAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v, max v w} A) :
    ∃ (P : DifferentialGradedModule.{u, v, max v w} A) (f : P ⟶ M),
      QuasiIso ((forgetToCochainComplex A).map f) ∧ Nonempty (PropertyPFiltration P) := by
  obtain ⟨P, hP, f, hf, ⟨F⟩⟩ := Stacks.DifferentialGraded.DGModule.exists_propertyP_resolution
    (Unbundled.algebra A) (Unbundled.algebra_isLawful A)
    (Unbundled.module M) (Unbundled.module_isLawful M)
  let e : Hom (Unbundled.bundle hP) M :=
    { toFun := Unbundled.restrictR (N := Unbundled.module M) f.toFun
      map_smul := fun x a => f.toFun.map_smul (MulOpposite.op a) x
      map_grading := f.map_grading
      map_d := LinearMap.ext f.commute_d }
  exact ⟨Unbundled.bundle hP, e, quasiIso_of_isQuasiIsomorphism e hf, ⟨bundleFiltration hP F⟩⟩

end DifferentialGradedModule.General

end
