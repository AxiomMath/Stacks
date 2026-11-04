module

public import StacksFrontier.Algebra.DifferentialGraded.Module.HomCohomology
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Evaluation
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaAcyclic

/-!
# `H^n(M X)` is `Hom_{K(Mod^dg(C))}(h_X, M⟦n⟧)`

Let `C` be a differential graded category over a commutative ring `R`, let `X` be an object of
`C` and let `M` be a right differential graded `C`-module. The differential graded Yoneda lemma
(`DGCategory.yonedaEval` and `DGCategory.yonedaEval_homD`) identifies the Hom complex
`Hom^•(h_X, M)` of `Mod^dg(C)` with the complex `M X`, and Tag 09LC
(`DGCategory.homotopyClassEquiv`) identifies the morphisms of the homotopy category with the
degree-zero cohomology of a Hom complex. Composing the two gives, for every integer `n`,

`H^n(M X) ≃ Hom_{K(Mod^dg(C))}(h_X, M⟦n⟧)`.

This is the equivalence of which
`DGCategory.RightModule.subsingleton_hom_yonedaObjK_iff` records only the *vanishing*: that file
needs no more than a `Subsingleton`, which an arbitrary bijection transports, and so never
builds the bijection itself.

The cohomology appearing here is the explicit one — the degree-`n` cocycles of `M X` modulo the
degree-`n` coboundaries — because that is the shape in which the Yoneda lemma produces it and
the shape `DGCategory.homCohomology` already has on the other side.
`DGCategory.RightModule.gradedCohomologyIso` identifies it with the homology of the complex
`DGCategory.RightModule.cochainComplex` in Mathlib's sense, so the displayed statement is a
statement about `Hⁿ` and not about a stand-in for it.

## Main definitions

* `DGCategory.RightModule.gradedCocycles`, `DGCategory.RightModule.gradedBoundaries` and
  `DGCategory.RightModule.gradedCohomology`: the degree-`n` cocycles, coboundaries and
  cohomology of `M X`, explicitly.

## Main results

* `DGCategory.RightModule.yonedaHomCohomologyEquiv`: the Yoneda lemma on cohomology, in every
  degree: `H^p(Hom^•(h_X, M)) ≃ₗ[R] H^p(M X)`.
* `DGCategory.RightModule.homKEquivGradedCohomology`: `Hom_{K(Mod^dg(C))}(h_X, M) ≃ H^0(M X)`.
* `DGCategory.RightModule.homYonedaObjKEquiv`: the differential graded Yoneda functor is fully
  faithful on homotopy categories, `Hom_{K(Mod^dg(C))}(h_x, h_y) ≃ Hom_{K(C)}(x, y)`.
* `DGCategory.RightModule.gradedCohomologyShiftEquiv`: `H^i((M⟦n⟧) X) ≃ₗ[R] H^{i+n}(M X)`.
* `DGCategory.RightModule.homShiftEquivGradedCohomology`: the displayed statement.
* `DGCategory.RightModule.gradedCohomologyIso`: the explicit cohomology is the homology of
  `DGCategory.RightModule.cochainComplex`, with
  `DGCategory.RightModule.homologyπ_gradedCohomologyIso_hom` pinning the identification down.
* `DGCategory.RightModule.homShiftEquivEvaluationGradedCohomology`: the displayed statement in
  the form the chain of [Stacks, Tag 09LK] uses, with the complex written as `ev_K M`.

## Implementation notes

`DGCategory.homotopyClassEquiv` is a bare `Equiv`, stated in degree zero only, and it is used
here as it stands: no additivity of it is needed and it is not strengthened. The `R`-linear
structure enters only on the two sides it already connects — `DGCategory.homCohomology` and
`DGCategory.RightModule.gradedCohomology` are both quotients of modules, and the Yoneda
comparison between them, `DGCategory.RightModule.yonedaHomCohomologyEquiv`, is `R`-linear.
What the composite with `DGCategory.homotopyClassEquiv` loses is therefore only the additivity
that the homotopy category's own Hom groups carry; nothing downstream of this file uses it.

The shift is taken on the *target*, as `M⟦n⟧`, and raises the degree of the cohomology: the
degree-`i` part of `M⟦n⟧` at `X` is the degree-`(i + n)` part of `M`, by definition and with no
transport, so `H^i((M⟦n⟧) X)` is `H^{i+n}(M X)`. This is the same bookkeeping as
`DGCategory.RightModule.exactAt_cochainComplex_shift_iff`, and the Koszul sign `(-1)^n` on the
differential of the shift is invisible to both the kernel and the image of the differential
because it is a unit.

The degree equation of `DGCategory.RightModule.gradedCohomologyShiftEquiv` is an argument rather
than being normalised to `i + n`: at `i = 0` the degree on the right must be `n` and not
`0 + n`, which is not a definitional equality of integers, and substituting the equation is what
keeps the statement of
`DGCategory.RightModule.homShiftEquivGradedCohomology` free of transports.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public section

namespace DGCategory

universe v u r

open CategoryTheory CategoryTheory.Limits

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

namespace RightModule

/-! ### The explicit cohomology of a right differential graded module -/

/-- The degree-`n` cocycles of the complex `M X`: the elements of degree `n` killed by the
differential. -/
def gradedCocycles (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) : Submodule R (M.obj X n) :=
  LinearMap.ker (M.dLinear (x := X) (rfl : n + 1 = n + 1))

/-- An element of degree `n` is a cocycle exactly when the differential kills it. -/
theorem mem_gradedCocycles {M : RightModule.{v} C} {X : C.Obj} {n : ℤ} {a : M.obj X n} :
    a ∈ gradedCocycles M X n ↔ M.d (rfl : n + 1 = n + 1) a = 0 := Iff.rfl

/-- The differential from degree `i`, corestricted to the degree-`n` cocycles, for `i + 1 = n`. -/
def gradedToCocycles (M : RightModule.{v} C) (X : C.Obj) {i n : ℤ} (h : i + 1 = n) :
    M.obj X i →ₗ[R] gradedCocycles M X n :=
  (M.dLinear h).codRestrict _ fun a => M.d_d h rfl a

/-- The cocycle `gradedToCocycles M X h a` has underlying element the differential `M.d h a`. -/
@[simp] theorem gradedToCocycles_val (M : RightModule.{v} C) (X : C.Obj) {i n : ℤ}
    (h : i + 1 = n) (a : M.obj X i) :
    (gradedToCocycles M X h a : M.obj X n) = M.d h a := rfl

/-- The degree-`n` coboundaries of the complex `M X`, as a submodule of the degree-`n`
cocycles. -/
def gradedBoundaries (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) :
    Submodule R (gradedCocycles M X n) :=
  LinearMap.range (gradedToCocycles M X (show n - 1 + 1 = n by omega))

/-- The coboundaries in degree `n` are the image of the differential from any degree `i` with
`i + 1 = n`. -/
theorem gradedBoundaries_eq_range (M : RightModule.{v} C) (X : C.Obj) {i n : ℤ} (h : i + 1 = n) :
    gradedBoundaries M X n = LinearMap.range (gradedToCocycles M X h) := by
  obtain rfl : i = n - 1 := by omega
  rfl

/-- The degree-`n` cohomology of the complex `M X`, explicitly: the degree-`n` cocycles modulo
the degree-`n` coboundaries. -/
def gradedCohomology (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) : Type v :=
  gradedCocycles M X n ⧸ gradedBoundaries M X n

/-- The degree-`n` cohomology classes form an additive group. -/
instance (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) :
    AddCommGroup (gradedCohomology M X n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ gradedBoundaries M X n))

/-- The degree-`n` cohomology classes form a module over the base ring. -/
instance (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) :
    Module R (gradedCohomology M X n) :=
  inferInstanceAs (Module R (_ ⧸ gradedBoundaries M X n))

/-! ### The Yoneda lemma on cohomology -/

/-- Evaluation at the identity carries the cocycles of the Hom complex `Hom^•(h_X, M)` onto the
cocycles of `M X`: a homogeneous morphism is closed exactly when the element of `M X` it
evaluates to is, by `DGCategory.homD_eq_zero_iff`. -/
theorem map_cocyclesSubmodule (M : RightModule.{v} C) (X : C.Obj) (p : ℤ) :
    ((rightModuleCategory.{v} C).cocyclesSubmodule (yonedaRightModule C X) M p).map
        (yonedaEval M X p).toLinearMap = gradedCocycles M X p := by
  ext a
  rw [Submodule.mem_map_equiv, mem_gradedCocycles, DGCategory.mem_cocyclesSubmodule,
    rightModuleCategory_d, homD_eq_zero_iff M X ((yonedaEval M X p).symm a),
    LinearEquiv.apply_symm_apply]

/-- Evaluation at the identity, restricted to the cocycles of degree `p`. -/
def yonedaCocyclesEquiv (M : RightModule.{v} C) (X : C.Obj) (p : ℤ) :
    (rightModuleCategory.{v} C).cocyclesSubmodule (yonedaRightModule C X) M p ≃ₗ[R]
      gradedCocycles M X p :=
  (yonedaEval M X p).ofSubmodules _ _ (map_cocyclesSubmodule M X p)

/-- On cocycles, evaluation at the identity commutes with the differentials: this is
`DGCategory.yonedaEval_homD`. -/
theorem yonedaCocyclesEquiv_comp_toCocycles (M : RightModule.{v} C) (X : C.Obj) {i p : ℤ}
    (h : i + 1 = p) :
    (yonedaCocyclesEquiv M X p).toLinearMap.comp
        ((rightModuleCategory.{v} C).toCocycles (yonedaRightModule C X) M h) =
      (gradedToCocycles M X h).comp (yonedaEval M X i).toLinearMap := by
  subst h
  exact LinearMap.ext fun φ => Subtype.ext (yonedaEval_homD M X i φ)

/-- If `S` and `T` are the ranges of `f` and `g`, and `e ∘ f` and `g` have the same range, then `e`
carries `S` onto `T`. -/
private theorem map_eq_of_range_comp_eq {A B V W : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (e : A →ₗ[R] B) (f : V →ₗ[R] A) (g : W →ₗ[R] B) {S : Submodule R A} {T : Submodule R B}
    (hS : S = LinearMap.range f) (hT : T = LinearMap.range g)
    (h : LinearMap.range (e.comp f) = LinearMap.range g) : S.map e = T := by
  rw [hS, hT, ← LinearMap.range_comp, h]

/-- Evaluation at the identity carries the coboundaries of the Hom complex onto the coboundaries
of `M X`. -/
theorem map_boundariesSubmodule (M : RightModule.{v} C) (X : C.Obj) (p : ℤ) :
    ((rightModuleCategory.{v} C).boundariesSubmodule (yonedaRightModule C X) M p).map
        (yonedaCocyclesEquiv M X p).toLinearMap = gradedBoundaries M X p := by
  have h : p - 1 + 1 = p := by omega
  exact map_eq_of_range_comp_eq _ _ _
    ((rightModuleCategory.{v} C).boundariesSubmodule_eq_range (yonedaRightModule C X) M h)
    (gradedBoundaries_eq_range M X h)
    (by rw [yonedaCocyclesEquiv_comp_toCocycles M X h, LinearMap.range_comp, LinearEquiv.range,
      Submodule.map_top])

/-- **The differential graded Yoneda lemma on cohomology.** The degree-`p` cohomology of the Hom
complex `Hom^•(h_X, M)` of `Mod^dg(C)` is the degree-`p` cohomology of the complex `M X`,
`R`-linearly. -/
def yonedaHomCohomologyEquiv (M : RightModule.{v} C) (X : C.Obj) (p : ℤ) :
    (rightModuleCategory.{v} C).homCohomology (yonedaRightModule C X) M p ≃ₗ[R]
      gradedCohomology M X p :=
  Submodule.Quotient.equiv _ _ (yonedaCocyclesEquiv M X p) (map_boundariesSubmodule M X p)

/-! ### Morphisms of the homotopy category -/

attribute [local implicit_reducible] DGCategory.K

/-- **The differential graded Yoneda lemma in the homotopy category.** Morphisms
`h_X ⟶ M` of `K(Mod^dg(C))` are the degree-zero cohomology classes of the complex `M X`.

This is `DGCategory.homotopyClassEquiv`, which identifies the morphisms of the homotopy
category with the degree-zero cohomology of the Hom complex, followed by
`DGCategory.RightModule.yonedaHomCohomologyEquiv`. -/
noncomputable def homKEquivGradedCohomology (M : (rightModuleCategory.{v} C).K) (X : C.Obj) :
    (yonedaObjK X ⟶ M) ≃ gradedCohomology M X 0 :=
  ((rightModuleCategory.{v} C).homotopyClassEquiv (yonedaRightModule C X) M).trans
    (yonedaHomCohomologyEquiv M X 0).toEquiv

/-- **The differential graded Yoneda functor is fully faithful on homotopy categories.**
Morphisms `h_x ⟶ h_y` of `K(Mod^dg(C))` are the morphisms `x ⟶ y` of `K(C)`.

This is `DGCategory.RightModule.homKEquivGradedCohomology` at `M = h_y`, whose complex at `x` is
the Hom complex `C(x, y)`, followed by `DGCategory.homotopyClassEquiv` for `C` itself. It is the
homotopy-category counterpart of `DGCategory.yonedaPostcompEquiv`, which is the statement in
each single degree. -/
noncomputable def homYonedaObjKEquiv (x y : C.K) :
    (yonedaObjK (x : C.Obj) ⟶ (yonedaObjK (y : C.Obj) : (rightModuleCategory.{v} C).K)) ≃
      (x ⟶ y) :=
  (homKEquivGradedCohomology (yonedaObjK (y : C.Obj)) x).trans (C.homotopyClassEquiv x y).symm

/-! ### The shift -/

/-- A Koszul sign is a unit, so smultiplying by it does not change whether an element
vanishes. -/
private theorem neg_one_pow_natAbs_smul_eq_zero_iff {G : Type*} [AddCommGroup G] [Module R G]
    (k : ℤ) (z : G) : (-1 : R) ^ k.natAbs • z = 0 ↔ z = 0 := by
  refine ⟨fun hz => ?_, fun hz => by rw [hz, smul_zero]⟩
  have hz' := congrArg (fun y : G => (-1 : R) ^ k.natAbs • y) hz
  simpa [smul_smul, neg_one_pow_natAbs_mul_self (R := R) k] using hz'

/-- The image of a linear map is not changed by multiplying it by a Koszul sign. -/
private theorem range_neg_one_pow_natAbs_smul {V W : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (k : ℤ) (f : V →ₗ[R] W) :
    LinearMap.range ((-1 : R) ^ k.natAbs • f) = LinearMap.range f := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact ⟨(-1 : R) ^ k.natAbs • a, by rw [map_smul]; rfl⟩
  · rintro _ ⟨a, rfl⟩
    refine ⟨(-1 : R) ^ k.natAbs • a, ?_⟩
    rw [LinearMap.smul_apply, map_smul, smul_smul, neg_one_pow_natAbs_mul_self (R := R) k,
      one_smul]

/-- The degree-`i` cocycles of `(M⟦n⟧) X` are the degree-`(i + n)` cocycles of `M X`: the two
are submodules of the same module, and the Koszul sign on the differential of the shift is a
unit. -/
theorem gradedCocycles_shift (M : RightModule.{v} C) (n : ℤ) (X : C.Obj) (i : ℤ) :
    gradedCocycles (shift M n) X i = gradedCocycles M X (i + n) := by
  refine Submodule.ext fun a => ?_
  rw [mem_gradedCocycles, mem_gradedCocycles, shift_d M n (rfl : i + 1 = i + 1) a,
    neg_one_pow_natAbs_smul_eq_zero_iff n]
  exact d_eq_zero_congr M (show i + n + 1 = i + 1 + n by omega) rfl a

/-- The comparison of the cocycles of `(M⟦n⟧) X` with those of `M X`, as a linear
equivalence. -/
def gradedCocyclesShiftEquiv (M : RightModule.{v} C) (n : ℤ) (X : C.Obj) (i : ℤ) :
    gradedCocycles (shift M n) X i ≃ₗ[R] gradedCocycles M X (i + n) :=
  LinearEquiv.ofEq _ _ (gradedCocycles_shift M n X i)

/-- The differential of `(M⟦n⟧) X` into the cocycles is the differential of `M X` into the
cocycles, multiplied by the Koszul sign of the shift. -/
theorem gradedCocyclesShiftEquiv_comp_gradedToCocycles (M : RightModule.{v} C) (n : ℤ)
    (X : C.Obj) {m i : ℤ} (h : m + 1 = i) (h' : m + n + 1 = i + n) :
    (gradedCocyclesShiftEquiv M n X i).toLinearMap.comp (gradedToCocycles (shift M n) X h) =
      (-1 : R) ^ n.natAbs • gradedToCocycles M X h' :=
  LinearMap.ext fun a => Subtype.ext (shift_d M n h a)

/-- The degree-`i` coboundaries of `(M⟦n⟧) X` are the degree-`(i + n)` coboundaries of
`M X`. -/
theorem map_gradedBoundaries_shift (M : RightModule.{v} C) (n : ℤ) (X : C.Obj) (i : ℤ) :
    (gradedBoundaries (shift M n) X i).map (gradedCocyclesShiftEquiv M n X i).toLinearMap =
      gradedBoundaries M X (i + n) := by
  have h : i - 1 + 1 = i := by omega
  have h' : i - 1 + n + 1 = i + n := by omega
  exact map_eq_of_range_comp_eq _ _ _ (gradedBoundaries_eq_range (shift M n) X h)
    (gradedBoundaries_eq_range M X h')
    (by rw [gradedCocyclesShiftEquiv_comp_gradedToCocycles M n X h h',
      range_neg_one_pow_natAbs_smul])

/-- **The cohomology of a shift.** The degree-`i` cohomology of `(M⟦n⟧) X` is the degree-`(i+n)`
cohomology of `M X`, `R`-linearly. The target degree is an argument, so that at `i = 0` it can
be `n` rather than `0 + n`. -/
def gradedCohomologyShiftEquiv (M : RightModule.{v} C) (n : ℤ) (X : C.Obj) {i j : ℤ}
    (h : i + n = j) : gradedCohomology (shift M n) X i ≃ₗ[R] gradedCohomology M X j := by
  subst h
  exact Submodule.Quotient.equiv _ _ (gradedCocyclesShiftEquiv M n X i)
    (map_gradedBoundaries_shift M n X i)

/-- **`H^n(M X) ≃ Hom_{K(Mod^dg(C))}(h_X, M⟦n⟧)`.** The degree-`n` cohomology of the complex
`M X` is the group of morphisms `h_X ⟶ M⟦n⟧` of the homotopy category of right differential
graded `C`-modules.

This is the differential graded Yoneda lemma in degree zero,
`DGCategory.RightModule.homKEquivGradedCohomology`, applied to the shift `M⟦n⟧`, whose complex
at `X` is the complex of `M` at `X` with the degrees moved by `n`. -/
noncomputable def homShiftEquivGradedCohomology (M : (rightModuleCategory.{v} C).K) (X : C.Obj)
    (n : ℤ) : (yonedaObjK X ⟶ M⟦n⟧) ≃ gradedCohomology M X n :=
  (homKEquivGradedCohomology (shift M n) X).trans
    (gradedCohomologyShiftEquiv M n X (zero_add n)).toEquiv

/-! ### The explicit cohomology is the homology of the complex `M X` -/

/-- The differential squares to zero, in the form needed to build the short complex of three
consecutive degrees. -/
theorem dLinear_comp_dLinear (M : RightModule.{v} C) (X : C.Obj) {i n : ℤ} (h : i + 1 = n) :
    (M.dLinear (x := X) (rfl : n + 1 = n + 1)).comp (M.dLinear (x := X) h) = 0 :=
  LinearMap.ext fun a => M.d_d h rfl a

/-- The short complex of `R`-modules formed by the degrees `i`, `n` and `n + 1` of `M X`, for
`i + 1 = n`. -/
def gradedSc (M : RightModule.{v} C) (X : C.Obj) {i n : ℤ} (h : i + 1 = n) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (M.dLinear (x := X) h) (M.dLinear (x := X) (rfl : n + 1 = n + 1))
    (dLinear_comp_dLinear M X h)

/-- Mathlib's map into the cycles of that short complex is the differential corestricted to the
cocycles. -/
theorem gradedSc_moduleCatToCycles (M : RightModule.{v} C) (X : C.Obj) {i n : ℤ} (h : i + 1 = n) :
    (gradedSc M X h).moduleCatToCycles = gradedToCocycles M X h := rfl

/-- The three consecutive terms of the complex `M X` form the short complex
`DGCategory.RightModule.gradedSc`. -/
def gradedScIso (M : RightModule.{v} C) (X : C.Obj) {i n : ℤ} (h : i + 1 = n) :
    (M.cochainComplex X).sc' i n (n + 1) ≅ gradedSc M X h := by
  subst h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans
      ((cochainComplex_d M X (rfl : i + 1 = i + 1)).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans
      ((cochainComplex_d M X (rfl : i + 1 + 1 = i + 1 + 1)).symm.trans (Category.comp_id _).symm))

/-- The explicit left homology datum of the degree-`n` part of the complex `M X`: its cycles are
the degree-`n` cocycles and its homology is the degree-`n` cohomology. -/
noncomputable def gradedLeftHomologyData (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) :
    ((M.cochainComplex X).sc' (n - 1) n (n + 1)).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofIso (gradedScIso M X (show n - 1 + 1 = n by omega)).symm
    (gradedSc M X (show n - 1 + 1 = n by omega)).moduleCatLeftHomologyData

/-- The projection of that datum is the quotient map by the coboundaries. -/
theorem gradedLeftHomologyData_π (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) :
    (gradedLeftHomologyData M X n).π = ModuleCat.ofHom (gradedBoundaries M X n).mkQ := rfl

/-- **The degree-`n` cohomology of `M X`, explicitly.** The homology of the complex `M X` in
degree `n` is the degree-`n` cocycles modulo the degree-`n` coboundaries. -/
noncomputable def gradedCohomologyIso (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) :
    (M.cochainComplex X).homology n ≅ ModuleCat.of R (gradedCohomology M X n) :=
  (M.cochainComplex X).homologyIsoSc' (n - 1) n (n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n) ≪≫
    (gradedLeftHomologyData M X n).homologyIso

/-- The identification of the homology of `M X` with cocycles modulo coboundaries is the
canonical one: it takes the homology class of a cycle to the class of the corresponding
cocycle. -/
theorem homologyπ_gradedCohomologyIso_hom (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) :
    (M.cochainComplex X).homologyπ n ≫ (gradedCohomologyIso M X n).hom =
      ((M.cochainComplex X).cyclesIsoSc' (n - 1) n (n + 1)
          (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)).hom ≫
        (gradedLeftHomologyData M X n).cyclesIso.hom ≫
          ModuleCat.ofHom (gradedBoundaries M X n).mkQ :=
  (HomologicalComplex.π_homologyIsoSc'_hom_assoc _ (n - 1) n (n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n) _).trans
    (congrArg (fun z => ((M.cochainComplex X).cyclesIsoSc' (n - 1) n (n + 1)
          (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)).hom ≫ z)
      (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom _
        (gradedLeftHomologyData M X n)))

/-! ### The form the chain of Tag 09LK uses: evaluation at an object -/

/-- The complex of `ev_K M` at the single object of `E = C(K, K)` is the complex `M K`:
evaluation at `K` is restriction along the inclusion of `E`, and it changes neither the modules
nor the differential. -/
theorem cochainComplex_evaluation (M : RightModule.{v} C) (K : C.Obj)
    (e : (endDGCategory C K).Obj) :
    ((evaluationDGFunctor.{v} C K).obj M).cochainComplex e = M.cochainComplex K := rfl

/-- The explicit cohomology of `ev_K M` is the explicit cohomology of `M` at `K`. -/
theorem gradedCohomology_evaluation (M : RightModule.{v} C) (K : C.Obj)
    (e : (endDGCategory C K).Obj) (n : ℤ) :
    gradedCohomology ((evaluationDGFunctor.{v} C K).obj M) e n = gradedCohomology M K n := rfl

/-- **`H^n(ev_K M) ≃ Hom_{K(Mod^dg(C))}(h_K, M⟦n⟧)`.** The first link of the chain computing the
derived Hom of [Stacks, Tag 09LK]: the degree-`n` cohomology of the complex `ev_K M` over the
endomorphism complex `E = C(K, K)` is the group of morphisms `h_K ⟶ M⟦n⟧` of the homotopy
category.

This is `DGCategory.RightModule.homShiftEquivGradedCohomology` at the object `K`, read through
`DGCategory.RightModule.gradedCohomology_evaluation`. -/
noncomputable def homShiftEquivEvaluationGradedCohomology (M : (rightModuleCategory.{v} C).K)
    (K : C.Obj) (e : (endDGCategory C K).Obj) (n : ℤ) :
    (yonedaObjK K ⟶ M⟦n⟧) ≃
      gradedCohomology ((evaluationDGFunctor.{v} C K).obj M) e n :=
  homShiftEquivGradedCohomology M K n

end RightModule

end DGCategory

end
