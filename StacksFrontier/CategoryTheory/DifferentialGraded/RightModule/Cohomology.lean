module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Shift

/-!
# The cohomology of a right differential graded module, and acyclicity

Let `C` be a differential graded category over a commutative ring `R` and let `M` be a right
differential graded `C`-module. For every object `X` of `C` the family `M X` of `R`-modules,
with the differential of `M`, is a cochain complex of `R`-modules, and `M` is *acyclic* when
every one of those complexes is, that is when the cohomology of every complex `M X` vanishes.

## Main definitions

* `DGCategory.RightModule.cochainComplex`: the complex `M X` of `R`-modules.
* `DGCategory.RightModule.cohomology`: its cohomology `Hⁿ(M X)`.
* `DGCategory.RightModule.IsAcyclic`: `M` is acyclic when every `M X` is an acyclic complex.

## Main results

* `DGCategory.RightModule.exactAt_cochainComplex_iff` and
  `DGCategory.RightModule.isAcyclic_iff`: exactness of `M X` in a degree, and acyclicity of
  `M`, read elementwise: a closed element of `M X` in a degree is a boundary.
* `DGCategory.RightModule.isAcyclic_iff_isZero_cohomology`: acyclicity is the vanishing of
  `Hⁿ(M X)` for every `X` and every `n`.
* `DGCategory.RightModule.exactAt_cochainComplex_shift_iff` and
  `DGCategory.RightModule.isAcyclic_shift_iff`: the complex of `M⟦k⟧` at `X` is the complex of
  `M` at `X` with the degrees moved by `k`, so acyclicity is invariant under shifts.

## Implementation notes

The differential of the complex is given by a `dite` on the degree equation `i + 1 = j` rather
than through `CochainComplex.of`, so that `(M.cochainComplex X).d i j` is the differential of
`M` for *any* pair of degrees satisfying that equation, with no `eqToHom` in the way. This is
what makes `DGCategory.RightModule.exactAt_cochainComplex_iff` an outright `Iff.rfl` after the
two rewrites that name the short complex: the predecessor of `n` can be taken to be any `m`
with `m + 1 = n`, and the bookkeeping that would otherwise be needed to normalise it to `n - 1`
disappears.

The dite is wrapped in the named function `DGCategory.RightModule.cochainD` rather than written
inline in the structure instance: an anonymous function inside a definition of this shape is a
beta-redex the kernel has to unfold on every later use.

`DGCategory.homComplexModules`, the Hom complex of two objects of a differential graded
category over `R`, is the same construction applied to a different family of `R`-modules, and
the two could be factored through a common one. They are left separate because the complex
here must be the module's own, independently of any Hom: the identification of `M X` with
`Hom^•(h_X, M)` is the differential graded Yoneda lemma, and acyclicity has to be stated
before it, not through it.
-/

@[expose] public section

namespace DGCategory

universe w v u r

open CategoryTheory CategoryTheory.Limits

namespace RightModule

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-! ### The complex `M X` -/

/-- The differential of the complex `M X`, from degree `i` to degree `j`: the differential of
`M` when `i + 1 = j`, and zero otherwise. -/
def cochainD (M : RightModule.{w} C) (X : C.Obj) (i j : ℤ) :
    ModuleCat.of R (M.obj X i) ⟶ ModuleCat.of R (M.obj X j) :=
  if h : i + 1 = j then ModuleCat.ofHom (M.dLinear (x := X) h) else 0

/-- At a pair of degrees differing by one, the differential of the complex `M X` is the
differential of `M`. -/
theorem cochainD_pos (M : RightModule.{w} C) (X : C.Obj) {i j : ℤ} (h : i + 1 = j) :
    M.cochainD X i j = ModuleCat.ofHom (M.dLinear (x := X) h) := dite_eq_left h

/-- The complex `M X` of `R`-modules attached to a right differential graded `C`-module `M` and
an object `X` of `C`: its degree-`i` term is the degree-`i` part of `M` at `X`, and its
differential is the differential of `M`. -/
def cochainComplex (M : RightModule.{w} C) (X : C.Obj) : CochainComplex (ModuleCat.{w} R) ℤ where
  X i := ModuleCat.of R (M.obj X i)
  d i j := M.cochainD X i j
  shape _ _ h := dite_eq_right h
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := hij
    have hjk' : j + 1 = k := hjk
    rw [cochainD_pos M X hij', cochainD_pos M X hjk']
    ext a
    exact M.d_d hij' hjk' a

/-- The degree-`i` term of the complex `M X` is the degree-`i` part of `M` at `X`. -/
@[simp] theorem cochainComplex_X (M : RightModule.{w} C) (X : C.Obj) (i : ℤ) :
    (M.cochainComplex X).X i = ModuleCat.of R (M.obj X i) := rfl

/-- At a pair of degrees with `i + 1 = j`, the differential of the complex `M X` from degree `i`
to degree `j` is the differential of `M`. -/
@[simp] theorem cochainComplex_d (M : RightModule.{w} C) (X : C.Obj) {i j : ℤ} (h : i + 1 = j) :
    (M.cochainComplex X).d i j = ModuleCat.ofHom (M.dLinear (x := X) h) := dite_eq_left h

/-- The cohomology `Hⁿ(M X)` of a right differential graded module at an object of `C`. -/
noncomputable def cohomology (M : RightModule.{w} C) (X : C.Obj) (n : ℤ) : ModuleCat.{w} R :=
  (M.cochainComplex X).homology n

/-- Two differentials out of the same element, reaching prescribed degrees, vanish together:
the two prescribed degrees agree, and the proofs of the degree equations are irrelevant. -/
theorem d_eq_zero_congr (M : RightModule.{w} C) {x : C.Obj} {i j j' : ℤ} (h : i + 1 = j)
    (h' : i + 1 = j') (a : M.obj x i) : M.d h a = 0 ↔ M.d h' a = 0 := by
  obtain rfl : j = j' := h.symm.trans h'
  exact Iff.rfl

/-! ### Acyclicity -/

/-- A right differential graded `C`-module is *acyclic* when the complex `M X` is acyclic for
every object `X` of `C`, that is when all its cohomology vanishes. -/
def IsAcyclic (M : RightModule.{w} C) : Prop := ∀ X : C.Obj, (M.cochainComplex X).Acyclic

/-- Exactness of the complex `M X` in degree `n`, read elementwise: every element of degree `n`
killed by the differential is the differential of an element of degree `m`, for any `m` with
`m + 1 = n`. -/
theorem exactAt_cochainComplex_iff (M : RightModule.{w} C) (X : C.Obj) {m n : ℤ} (h : m + 1 = n) :
    (M.cochainComplex X).ExactAt n ↔
      ∀ a : M.obj X n, M.d (rfl : n + 1 = n + 1) a = 0 → ∃ b : M.obj X m, M.d h b = a := by
  rw [HomologicalComplex.exactAt_iff' _ m n (n + 1) (ComplexShape.prev_eq' _ h)
      (ComplexShape.next_eq' _ rfl), ShortComplex.moduleCat_exact_iff]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_X₁,
    HomologicalComplex.shortComplexFunctor'_obj_X₂,
    HomologicalComplex.shortComplexFunctor'_obj_f, HomologicalComplex.shortComplexFunctor'_obj_g,
    cochainComplex_d M X h, cochainComplex_d M X (rfl : n + 1 = n + 1)]
  exact Iff.rfl

/-- Acyclicity, read elementwise. -/
theorem isAcyclic_iff (M : RightModule.{w} C) :
    M.IsAcyclic ↔ ∀ (X : C.Obj) (n : ℤ) (a : M.obj X n), M.d (rfl : n + 1 = n + 1) a = 0 →
      ∃ b : M.obj X (n - 1), M.d (show n - 1 + 1 = n by omega) b = a := by
  refine forall_congr' fun X => ?_
  rw [HomologicalComplex.acyclic_iff]
  exact forall_congr' fun n => exactAt_cochainComplex_iff M X (show n - 1 + 1 = n by omega)

/-- Acyclicity is the vanishing of the cohomology `Hⁿ(M X)` in every degree at every object. -/
theorem isAcyclic_iff_isZero_cohomology (M : RightModule.{w} C) :
    M.IsAcyclic ↔ ∀ (X : C.Obj) (n : ℤ), IsZero (M.cohomology X n) :=
  forall_congr' fun X => (M.cochainComplex X).acyclic_iff.trans
    (forall_congr' fun n => (M.cochainComplex X).exactAt_iff_isZero_homology n)

/-! ### Shifting -/

/-- The Koszul sign of a shift is a unit, so smultiplying by it does not change whether an
element vanishes. -/
private theorem smul_eq_zero_iff_of_neg_one_pow {S G : Type*} [CommRing S] [AddCommGroup G]
    [Module S G] (k : ℤ) (z : G) : (-1 : S) ^ k.natAbs • z = 0 ↔ z = 0 := by
  refine ⟨fun hz => ?_, fun hz => by rw [hz, smul_zero]⟩
  simpa [smul_smul, neg_one_pow_natAbs_mul_self (R := S) k] using
    congrArg (fun y : G => (-1 : S) ^ k.natAbs • y) hz

/-- The complex of `M⟦k⟧` at `X` is exact in degree `i` exactly when the complex of `M` at `X`
is exact in degree `i + k`. -/
theorem exactAt_cochainComplex_shift_iff (M : RightModule.{w} C) (k : ℤ) (X : C.Obj) {i j : ℤ}
    (h : i + k = j) :
    ((shift M k).cochainComplex X).ExactAt i ↔ (M.cochainComplex X).ExactAt j := by
  subst h
  rw [exactAt_cochainComplex_iff (shift M k) X (show i - 1 + 1 = i by omega),
    exactAt_cochainComplex_iff M X (show i - 1 + k + 1 = i + k by omega)]
  refine forall_congr' fun a => ?_
  have hz : (shift M k).d (rfl : i + 1 = i + 1) a = 0 ↔
      M.d (rfl : i + k + 1 = i + k + 1) a = 0 := by
    rw [shift_d, smul_eq_zero_iff_of_neg_one_pow (S := R) k]
    exact d_eq_zero_congr M (show i + k + 1 = i + 1 + k by omega) rfl a
  rw [hz]
  refine imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨b, hb⟩
    rw [shift_d] at hb
    exact ⟨(-1 : R) ^ k.natAbs • b, by rwa [M.d_smul]⟩
  · rintro ⟨b, hb⟩
    refine ⟨(-1 : R) ^ k.natAbs • b, ?_⟩
    rwa [shift_d, M.d_smul, smul_smul, neg_one_pow_natAbs_mul_self (R := R) k, one_smul]

/-- Acyclicity is invariant under shifting. -/
theorem isAcyclic_shift_iff (M : RightModule.{w} C) (k : ℤ) :
    (shift M k).IsAcyclic ↔ M.IsAcyclic := by
  refine forall_congr' fun X => ?_
  simp only [HomologicalComplex.acyclic_iff]
  exact ⟨fun H n => (exactAt_cochainComplex_shift_iff M k X (show n - k + k = n by omega)).1 (H _),
    fun H i => (exactAt_cochainComplex_shift_iff M k X (rfl : i + k = i + k)).2 (H _)⟩

end RightModule

end DGCategory

end
