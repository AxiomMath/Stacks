module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift
public import StacksFrontier.Algebra.DGA.DirectSumGrading
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategory
public import StacksFrontier.Algebra.DGA.BimoduleDGAction

/-!
# Shifts of the Hom module of a differential graded bimodule

Let `N` be a differential graded `(A,B)`-bimodule and let `P` be a right
differential graded `B`-module. The graded right `B`-linear maps from `N` to `P`
form a right differential graded `A`-module, the `A`-action being precomposition
with the left action of `A` on `N`. Shifting this Hom module agrees canonically
with taking maps into a shift of `P`, and the comparison carries no sign.

## Main definitions

* `DifferentialGradedModule.HomDGModulePresentation` specifies the Hom module by
  its homogeneous maps, its differential, and the precomposition action of `A`.
* `DifferentialGradedModule.homComplexPresentation` constructs it, and
  `DifferentialGradedModule.homComplex` is the Hom module itself.

## Main results

* `DifferentialGradedModule.shiftHomIso` gives the canonical isomorphism from the
  shifted Hom module to the Hom module into a shift, together with the formula
  identifying the two on homogeneous elements.

## Implementation notes

The graded Hom module is both presented and constructed. A presentation is a
right differential graded `A`-module together with identifications of its
homogeneous pieces with the degree-`n` homogeneous right `B`-linear maps, under
which the differential is the signed commutator and the `A`-action is
precomposition; stating the result over a presentation rather than over one
chosen model means it applies to any construction of the Hom module. The
canonical presentation is `DifferentialGradedModule.homComplexPresentation`, so
the results stated over a presentation are results about an actual module.

The underlying module is built as the direct sum of the homogeneous pieces, graded
by `DirectSum.lofRange`, with differential and action assembled from their
degreewise formulas by `DirectSum.toModule`.

The comparison is an isomorphism of right differential graded `A`-modules, not
merely a degreewise identification. Its sign-freeness is the content: the shift
introduces `Int.negOnePow` into the differential of the shifted Hom module and
into the identification of homogeneous pieces, and the two cancel, so the
isomorphism is carried by the identity on the underlying module. Degree
bookkeeping is done with `change` and explicit degree equalities rather than by
rewriting along arithmetic identities, which would require transporting
subtype memberships.

## References

* [Stacks Project, Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u v v' w

variable {R : Type u} [CommRing R]
variable (A : DifferentialGradedAlgebra.{u, v} R)
variable (B : DifferentialGradedAlgebra.{u, v'} R)
variable (N P : DifferentialGradedModule.{u, v', max u w} B)
variable (L : DifferentialGradedModule.DGActionBimoduleStructure A B N)

/-- A presentation of the right DG `A`-module of graded right `B`-linear maps from `N` to `P`:
a right DG `A`-module whose degree-`n` part is identified with the degree-`n` homogeneous right
`B`-linear maps, so that the differential is the signed commutator and the action of `A` is
precomposition with the left action of `A` on `N`. -/
public structure HomDGModulePresentation
    (A : DifferentialGradedAlgebra.{u, v} R)
    (B : DifferentialGradedAlgebra.{u, v'} R)
    (N P : DifferentialGradedModule.{u, v', max u w} B)
    (L : DifferentialGradedModule.DGActionBimoduleStructure A B N) where
  /-- The underlying right differential graded `A`-module. -/
  module : DifferentialGradedModule.{u, v, max u w} A
  /-- The identification of the degree-`n` part of `module` with the degree-`n` homogeneous
  right `B`-linear maps from `N` to `P`. -/
  homogeneousEquiv (n : ℤ) :
    module.grading n ≃ₗ[R]
      DifferentialGradedModule.HomogeneousMap B N P n
  /-- Under `homogeneousEquiv`, the differential of `module` is
  `DifferentialGradedModule.homogeneousMapDifferential`. -/
  map_d (n : ℤ) (f : module.grading n) :
    homogeneousEquiv (n + 1) (module.gradedDifferential n f) =
      DifferentialGradedModule.homogeneousMapDifferential B
        (homogeneousEquiv n f)
  /-- Under `homogeneousEquiv`, the action of a homogeneous `a : A` is precomposition with the
  left action of `a` on `N`. -/
  map_smul (n m p : ℤ) (f : module.grading n) (a : A.grading m)
      (x : N.grading p) :
    ((homogeneousEquiv (n + m)
        ⟨MulOpposite.op (a : A.A) • (f : module.M),
          module.smul_mem n m (f : module.M) (a : A.A) f.property a.property⟩).1 x) =
      (homogeneousEquiv n f).1
        ((show N.grading (p + m) from
          (L.1.action m a).v p (p + m) (by omega) x) : N.M)

private abbrev homDegree (B : DifferentialGradedAlgebra.{u, v'} R)
    (N P : DifferentialGradedModule.{u, v', max u w} B) (n : ℤ) :=
  DifferentialGradedModule.HomogeneousMap
    B N P n

private abbrev homTotal :=
  DirectSum ℤ (fun n : ℤ => homDegree B N P n)

private abbrev homTotalGrade (n : ℤ) : Submodule R (homTotal B N P) :=
  DirectSum.lofRange (R := R)
    (fun n : ℤ => homDegree B N P n) n

@[instance_reducible] private noncomputable def homTotalDecomposition :
    DirectSum.Decomposition (homTotalGrade B N P) :=
  DirectSum.lofRangeDecomposition (R := R) _

private def homDifferentialPiece (n : ℤ) :
    homDegree B N P n →ₗ[R] homDegree B N P (n + 1) where
  toFun := DifferentialGradedModule.homogeneousMapDifferential B
  map_add' f g :=
    (DifferentialGradedModule.dgCategory B).d_add f g
  map_smul' r f :=
    (DifferentialGradedModule.dgCategory B).d_smul r f

private def homTotalDifferential : homTotal B N P →ₗ[R] homTotal B N P :=
  DirectSum.toModule R ℤ _ fun n =>
    (DirectSum.lof R ℤ (fun n : ℤ => homDegree B N P n) (n + 1)).comp
      (homDifferentialPiece B N P n)

private theorem homTotalDifferential_of (n : ℤ) (f : homDegree B N P n) :
    homTotalDifferential B N P (DirectSum.of (fun n : ℤ => homDegree B N P n) n f) =
      DirectSum.of (fun n : ℤ => homDegree B N P n) (n + 1)
        (DifferentialGradedModule.homogeneousMapDifferential B f) := by
  show (DirectSum.toModule R ℤ (homTotal B N P) (fun i =>
    (DirectSum.lof R ℤ (fun j : ℤ => homDegree B N P j) (i + 1)).comp
      (homDifferentialPiece B N P i)))
      (DirectSum.lof R ℤ (fun i : ℤ => homDegree B N P i) n f) = _
  rw [DirectSum.toModule_lof R (φ := fun i =>
    (DirectSum.lof R ℤ (fun j : ℤ => homDegree B N P j) (i + 1)).comp
      (homDifferentialPiece B N P i)) n f]
  rfl

attribute [local simp] homTotalDifferential_of

private theorem homTotalDifferential_mem (n : ℤ) (x : homTotal B N P)
    (hx : x ∈ homTotalGrade B N P n) :
    homTotalDifferential B N P x ∈ homTotalGrade B N P (n + 1) := by
  rcases hx with ⟨f, rfl⟩
  exact ⟨DifferentialGradedModule.homogeneousMapDifferential B f,
    by
      rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
      simp [homTotalDifferential_of]⟩

private theorem cochain_hom_apply_val_irrel
    {d : ℤ}
    (c : CochainComplex.HomComplex.Cochain N.toCochainComplex N.toCochainComplex d)
    (i j j' : ℤ) (h : i + d = j) (h' : i + d = j') (x : N.grading i) :
    ((c.v i j h).hom x).val = ((c.v i j' h').hom x).val := by
  have hj : j = j' := by omega
  cases hj
  rfl

private def cochainGradeIncl (q : ℤ) :
    N.toCochainComplex.X q ⟶ ModuleCat.of R N.M :=
  ModuleCat.ofHom (N.grading q).subtype

private theorem cochainCarrierEq (q : ℤ) :
    (N.toCochainComplex.X q : Type (max u w)) = N.grading q := by
  simp only [N.toCochainComplex_X]

private def cochainGradeCast (q : ℤ) (y : N.toCochainComplex.X q) :
    N.grading q :=
  (cochainCarrierEq B N q).mp y

private theorem cochainGradeIncl_eq (q : ℤ) :
    cochainGradeIncl B N q = ModuleCat.ofHom (N.grading q).subtype := by
  apply ModuleCat.hom_ext
  rfl

private theorem cochainGradeIncl_apply (q : ℤ) (y : N.toCochainComplex.X q) :
    cochainGradeIncl B N q y = (N.grading q).subtype (cochainGradeCast B N q y) := by
  rw [cochainGradeIncl_eq]
  rfl

private theorem cochainGradeIncl_hom_apply_irrel
    {d : ℤ}
    (c : CochainComplex.HomComplex.Cochain N.toCochainComplex N.toCochainComplex d)
    (i j j' : ℤ) (h : i + d = j) (h' : i + d = j') (x : N.grading i) :
    cochainGradeIncl B N j ((c.v i j h).hom x) = cochainGradeIncl B N j' ((c.v i j' h').hom x) := by
  rw [cochainGradeIncl_apply, cochainGradeIncl_apply]
  cases cochainCarrierEq B N j
  cases cochainCarrierEq B N j'
  exact cochain_hom_apply_val_irrel (B := B) (N := N) c i j j' h h' x

private theorem cochainDifferentialIncl (n : ℤ) :
    N.toCochainComplex.d n (n + 1) ≫ cochainGradeIncl B N (n + 1) =
      cochainGradeIncl B N n ≫ ModuleCat.ofHom N.d := by
  rw [N.toCochainComplex_d, cochainGradeIncl_eq, cochainGradeIncl_eq]
  apply ModuleCat.hom_ext
  ext x
  rfl

private theorem cochainDifferentialIncl_apply (n : ℤ)
    (x : N.toCochainComplex.X n) :
    cochainGradeIncl B N (n + 1)
        ((N.toCochainComplex.d n (n + 1)).hom x) =
      N.d (cochainGradeIncl B N n x) := by
  have h := congrArg (fun f => f.hom x) (cochainDifferentialIncl B N n)
  show ((cochainGradeIncl B N (n + 1)).hom
      ((N.toCochainComplex.d n (n + 1)).hom x)) =
    (ModuleCat.ofHom N.d).hom ((cochainGradeIncl B N n).hom x)
  exact h

private def bimoduleActionTotal (m : ℤ) (a : A.grading m) : N.M →ₗ[R] N.M :=
  (DirectSum.toModule R ℤ N.M (fun p =>
    (N.grading (p + m)).subtype.comp
      (((L.1.action m a).v p (p + m) (by omega)).hom))).comp
    (DirectSum.decomposeLinearEquiv N.grading).toLinearMap

private theorem bimoduleActionTotal_apply (m p : ℤ) (a : A.grading m)
    (x : N.grading p) :
    bimoduleActionTotal A B N L m a (x : N.M) =
      (N.grading (p + m)).subtype
        (((L.1.action m a).v p (p + m) (by omega)).hom x) := by
  show (DirectSum.toModule R ℤ N.M (fun q =>
    (N.grading (q + m)).subtype.comp
      (((L.1.action m a).v q (q + m) (by omega)).hom)))
      ((DirectSum.decomposeLinearEquiv N.grading) (x : N.M)) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe]
  show (DirectSum.toModule R ℤ N.M (fun q =>
    (N.grading (q + m)).subtype.comp
      (((L.1.action m a).v q (q + m) (by omega)).hom)))
      (DirectSum.lof R ℤ (fun q => N.grading q) p x) =
    (((N.grading (p + m)).subtype.comp
      (((L.1.action m a).v p (p + m) (by omega)).hom)) x)
  exact DirectSum.toModule_lof R
    (φ := fun q => (N.grading (q + m)).subtype.comp
      (((L.1.action m a).v q (q + m) (by omega)).hom)) p x

attribute [local simp] bimoduleActionTotal_apply

private theorem bimoduleActionTotal_apply_cochain (m p : ℤ) (a : A.grading m)
    (x : N.grading p) :
    bimoduleActionTotal A B N L m a (x : N.M) =
      cochainGradeIncl B N (p + m)
        (((L.1.action m a).v p (p + m) (by omega)).hom x) := by
  rw [bimoduleActionTotal_apply, cochainGradeIncl_apply]
  cases cochainCarrierEq B N (p + m)
  rfl

private theorem bimoduleActionTotal_mem (m p : ℤ) (a : A.grading m)
    (x : N.M) (hx : x ∈ N.grading p) :
    bimoduleActionTotal A B N L m a x ∈ N.grading (p + m) := by
  let x' : N.grading p := ⟨x, hx⟩
  show bimoduleActionTotal A B N L m a (x' : N.M) ∈ N.grading (p + m)
  rw [bimoduleActionTotal_apply]
  exact (N.grading (p + m)).coe_mem _

private theorem bimoduleActionTotal_eq (m : ℤ) (a : A.grading m) :
    ∃ g : homDegree B N N m,
      bimoduleActionTotal A B N L m a = g.1 := by
  obtain ⟨g, hg⟩ := L.2 m a
  refine ⟨g, ?_⟩
  apply DirectSum.decompose_lhom_ext N.grading
  intro p
  ext x
  show bimoduleActionTotal A B N L m a (x : N.M) = g.1 (x : N.M)
  rw [bimoduleActionTotal_apply]
  exact hg p x

private theorem bimoduleActionTotal_mul (m n : ℤ) (a : A.grading m)
    (b : A.grading n) :
    bimoduleActionTotal A B N L (m + n)
        ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ =
      (bimoduleActionTotal A B N L m a).comp
        (bimoduleActionTotal A B N L n b) := by
  apply DirectSum.decompose_lhom_ext N.grading
  intro p
  ext x
  let x' : N.grading p := x
  let y : N.grading (p + n) :=
    ⟨bimoduleActionTotal A B N L n b (x : N.M),
      bimoduleActionTotal_mem A B N L n p b (x : N.M) x.property⟩
  have h₁ := bimoduleActionTotal_apply A B N L (m + n) p
    ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ x'
  have h₂ := bimoduleActionTotal_apply A B N L n p b x'
  have h₃ := bimoduleActionTotal_apply A B N L m (p + n) a y
  have hcomp : ((L.1.action (m + n)
      ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩).v
      p (p + (m + n)) (by omega)).hom x =
    ((L.1.action m a).v (p + n) (p + (m + n)) (by omega)).hom
      (((L.1.action n b).v p (p + n) (by omega)).hom x) := by
    have h := congrArg
      (fun c : CochainComplex.HomComplex.Cochain N.toCochainComplex N.toCochainComplex
          (m + n) => (c.v p (p + (m + n)) (by omega)).hom x)
      (L.1.map_mul m n a b)
    rwa [CochainComplex.HomComplex.Cochain.comp_v (L.1.action n b) (L.1.action m a)
      (show n + m = m + n by omega) p (p + n) (p + (m + n)) rfl
      (by omega), ModuleCat.hom_comp] at h
  have hy : ((L.1.action n b).v p (p + n) (by omega)).hom x = y := Subtype.ext h₂.symm
  show bimoduleActionTotal A B N L (m + n)
      ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩
      (x : N.M) =
    bimoduleActionTotal A B N L m a
      (bimoduleActionTotal A B N L n b (x : N.M))
  calc
    _ = (N.grading (p + (m + n))).subtype
          (((L.1.action (m + n)
        ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩).v
          p (p + (m + n)) (by omega)).hom x) := h₁
    _ = (N.grading (p + (m + n))).subtype
          (((L.1.action m a).v (p + n) (p + (m + n)) (by omega)).hom
            (((L.1.action n b).v p (p + n) (by omega)).hom x)) :=
        congrArg (N.grading (p + (m + n))).subtype hcomp
    _ = (N.grading (p + (m + n))).subtype
          (((L.1.action m a).v (p + n) (p + (m + n)) (by omega)).hom y) := by
        rw [hy]
    _ = _ := (h₃.trans (cochain_hom_apply_val_irrel (B := B) (N := N) (L.1.action m a)
        (p + n) (p + n + m) (p + (m + n)) (by omega) (by omega) y)).symm

private def bimoduleActionTotalLinear (m : ℤ) :
    A.grading m →ₗ[R] (N.M →ₗ[R] N.M) where
  toFun := bimoduleActionTotal A B N L m
  map_add' a b := by
    apply DirectSum.decompose_lhom_ext N.grading
    intro p
    ext x
    change bimoduleActionTotal A B N L m (a + b) (x : N.M) =
      (bimoduleActionTotal A B N L m a + bimoduleActionTotal A B N L m b) (x : N.M)
    simp only [LinearMap.add_apply]
    rw [bimoduleActionTotal_apply, bimoduleActionTotal_apply, bimoduleActionTotal_apply,
      map_add]
    rfl
  map_smul' r a := by
    apply DirectSum.decompose_lhom_ext N.grading
    intro p
    ext x
    change bimoduleActionTotal A B N L m (r • a) (x : N.M) =
      (r • bimoduleActionTotal A B N L m a) (x : N.M)
    simp only [LinearMap.smul_apply]
    rw [bimoduleActionTotal_apply, bimoduleActionTotal_apply, map_smul]
    rfl

private def homPrecompPiece (n m : ℤ) (a : A.grading m) :
    homDegree B N P n →ₗ[R] homDegree B N P (n + m) where
  toFun f := ⟨f.1.comp (bimoduleActionTotal A B N L m a), by
    constructor
    · intro i x hx
      change f.1 (bimoduleActionTotal A B N L m a x) ∈ P.grading (i + (n + m))
      have hmem := bimoduleActionTotal_mem A B N L m i a x hx
      have hdeg : (i + m) + n = i + (n + m) := by omega
      simpa only [hdeg] using f.2.1 (i + m) _ hmem
    · intro b x
      obtain ⟨g, hg⟩ := bimoduleActionTotal_eq A B N L m a
      change f.1 (bimoduleActionTotal A B N L m a (MulOpposite.op b • x)) =
        MulOpposite.op b • f.1 (bimoduleActionTotal A B N L m a x)
      rw [hg, g.2.2, f.2.2]⟩
  map_add' f g := by
    apply Subtype.ext
    ext x
    simp [LinearMap.comp_apply]
  map_smul' r f := by
    apply Subtype.ext
    ext x
    simp [LinearMap.comp_apply]

private def homPrecompPieceLinear (n m : ℤ) :
    A.grading m →ₗ[R] (homDegree B N P n →ₗ[R] homDegree B N P (n + m)) where
  toFun a := homPrecompPiece A B N P L n m a
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    ext x
    change f.1 (bimoduleActionTotal A B N L m (a + b) x) =
      f.1 (bimoduleActionTotal A B N L m a x) +
        f.1 (bimoduleActionTotal A B N L m b x)
    have h := congrArg (fun T : N.M →ₗ[R] N.M => f.1 (T x))
      (LinearMap.map_add (bimoduleActionTotalLinear A B N L m) a b)
    calc
      _ = f.1 ((bimoduleActionTotal A B N L m a +
          bimoduleActionTotal A B N L m b) x) := h
      _ = _ := by simp
  map_smul' r a := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    ext x
    change f.1 (bimoduleActionTotal A B N L m (r • a) x) =
      r • f.1 (bimoduleActionTotal A B N L m a x)
    have h := congrArg (fun T : N.M →ₗ[R] N.M => f.1 (T x))
      (LinearMap.map_smul (bimoduleActionTotalLinear A B N L m) r a)
    calc
      _ = f.1 ((r • bimoduleActionTotal A B N L m a) x) := h
      _ = _ := by simp

private def homActionOnTotal (m : ℤ) (a : A.grading m) :
    homTotal B N P →ₗ[R] homTotal B N P :=
  DirectSum.toModule R ℤ (homTotal B N P) (fun n =>
    (DirectSum.lof R ℤ (fun n : ℤ => homDegree B N P n) (n + m)).comp
      (homPrecompPiece A B N P L n m a))

private theorem homActionOnTotal_of (n m : ℤ) (a : A.grading m)
    (f : homDegree B N P n) :
    homActionOnTotal A B N P L m a
      (DirectSum.of (fun n : ℤ => homDegree B N P n) n f) =
    DirectSum.of (fun n : ℤ => homDegree B N P n) (n + m)
      (homPrecompPiece A B N P L n m a f) := by
  show (DirectSum.toModule R ℤ (homTotal B N P) (fun i =>
    (DirectSum.lof R ℤ (fun j : ℤ => homDegree B N P j) (i + m)).comp
      (homPrecompPiece A B N P L i m a)))
      (DirectSum.lof R ℤ (fun i : ℤ => homDegree B N P i) n f) = _
  rw [DirectSum.toModule_lof]
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]

attribute [local simp] homActionOnTotal_of

private def homActionOnTotalLinear (m : ℤ) :
    A.grading m →ₗ[R] (homTotal B N P →ₗ[R] homTotal B N P) where
  toFun := homActionOnTotal A B N P L m
  map_add' a b := by
    apply LinearMap.ext
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp [homActionOnTotal]
    | add x y hx hy => simp [map_add, hx, hy]
    | of n f =>
      simp only [LinearMap.add_apply, homActionOnTotal_of]
      change DirectSum.of (fun j : ℤ => homDegree B N P j) (n + m)
          (homPrecompPiece A B N P L n m (a + b) f) =
        DirectSum.of (fun j : ℤ => homDegree B N P j) (n + m)
          (homPrecompPiece A B N P L n m a f) +
          DirectSum.of (fun j : ℤ => homDegree B N P j) (n + m)
            (homPrecompPiece A B N P L n m b f)
      calc
        _ = DirectSum.of _ (n + m)
            (homPrecompPiece A B N P L n m a f +
              homPrecompPiece A B N P L n m b f) := by
              congr 1
              exact LinearMap.congr_fun
                (LinearMap.map_add (homPrecompPieceLinear A B N P L n m) a b) f
        _ = _ := (DirectSum.of _ (n + m)).map_add _ _
  map_smul' r a := by
    apply LinearMap.ext
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp [homActionOnTotal]
    | add x y hx hy => simp [hx, hy]
    | of n f =>
      simp only [LinearMap.smul_apply, RingHom.id_apply, homActionOnTotal_of]
      change DirectSum.of (fun j : ℤ => homDegree B N P j) (n + m)
          (homPrecompPiece A B N P L n m (r • a) f) =
        r • DirectSum.of (fun j : ℤ => homDegree B N P j) (n + m)
          (homPrecompPiece A B N P L n m a f)
      calc
        _ = DirectSum.of _ (n + m)
            (r • homPrecompPiece A B N P L n m a f) := by
              congr 1
              exact LinearMap.congr_fun
                (LinearMap.map_smul (homPrecompPieceLinear A B N P L n m) r a) f
        _ = _ := DirectSum.of_smul _ _ _ _

private def homActionTotalAll : A.A →ₗ[R] (homTotal B N P →ₗ[R] homTotal B N P) :=
  (DirectSum.toModule R ℤ (homTotal B N P →ₗ[R] homTotal B N P)
    (fun m => homActionOnTotalLinear A B N P L m)).comp
    (DirectSum.decomposeLinearEquiv A.grading).toLinearMap

private theorem homActionTotalAll_of (m : ℤ) (a : A.grading m) :
    homActionTotalAll A B N P L (a : A.A) = homActionOnTotal A B N P L m a := by
  apply LinearMap.ext
  intro x
  simp only [homActionTotalAll, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [DirectSum.decomposeLinearEquiv_apply_coe]
  show (DirectSum.toModule R ℤ (homTotal B N P →ₗ[R] homTotal B N P)
    (fun i => homActionOnTotalLinear A B N P L i)
    (DirectSum.lof R ℤ (fun i : ℤ => A.grading i) m a)) x = _
  rw [DirectSum.toModule_lof R
    (φ := fun i => homActionOnTotalLinear A B N P L i) m a]
  rfl

private def homDegreeCast {m n : ℤ} (h : m = n) :
    homDegree B N P m ≃ₗ[R] homDegree B N P n where
  toFun f := ⟨f.1, h ▸ f.2⟩
  invFun f := ⟨f.1, h.symm ▸ f.2⟩
  left_inv f := by cases h; rfl
  right_inv f := by cases h; rfl
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' r f := by apply Subtype.ext; rfl

private theorem homDegreeCast_val {m n : ℤ} (h : m = n)
    (f : homDegree B N P m) : (homDegreeCast B N P h f : N.M →ₗ[R] P.M) = f.1 := rfl

attribute [local simp] homDegreeCast_val

private theorem homDegreeCast_heq {m n : ℤ} (h : m = n)
    (f : homDegree B N P m) : HEq f (homDegreeCast B N P h f) := by
  cases h
  rfl

private theorem bimoduleActionTotal_one :
    bimoduleActionTotal A B N L 0
      ⟨1, SetLike.one_mem_graded A.grading⟩ = LinearMap.id := by
  apply DirectSum.decompose_lhom_ext N.grading
  intro p
  ext x
  show bimoduleActionTotal A B N L 0
      ⟨1, SetLike.one_mem_graded A.grading⟩ (x : N.M) = (x : N.M)
  rw [bimoduleActionTotal_apply]
  have h := congrArg
    (fun c : CochainComplex.HomComplex.Cochain N.toCochainComplex N.toCochainComplex 0 =>
      (c.v p p (add_zero p)).hom x) L.1.map_one
  calc
    _ = (((L.1.action 0 ⟨1, SetLike.one_mem_graded A.grading⟩).v
        p (p + 0) (by omega)).hom x).val := rfl
    _ = (((L.1.action 0 ⟨1, SetLike.one_mem_graded A.grading⟩).v
        p p (add_zero p)).hom x).val :=
      cochain_hom_apply_val_irrel (B := B) (N := N)
        (L.1.action 0 ⟨1, SetLike.one_mem_graded A.grading⟩)
        p (p + 0) p (by omega) (by simp) x
    _ = (x : N.M) := congrArg (fun y : N.grading p => (y : N.M)) h

private theorem homDegree_heq_of_val_eq {m n : ℤ}
    (h : m = n) (f : homDegree B N P m) (g : homDegree B N P n)
    (hv : f.1 = g.1) : HEq f g := by
  cases h
  exact heq_of_eq (Subtype.ext hv)

private theorem homActionTotalAll_one :
    homActionTotalAll A B N P L 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp [homActionTotalAll]
  | add x y hx hy => simp [hx, hy]
  | of n f =>
      rw [homActionTotalAll_of A B N P L 0 ⟨1, SetLike.one_mem_graded A.grading⟩,
        homActionOnTotal_of]
      apply DirectSum.of_eq_of_gradedMonoid_eq
      let hidx : n + 0 = n := add_zero n
      apply Sigma.ext hidx
      let x' := homPrecompPiece A B N P L n 0
        ⟨1, SetLike.one_mem_graded A.grading⟩ f
      have hval : x'.1 = f.1 := by
        ext x
        simp [x', homPrecompPiece, bimoduleActionTotal_one]
      exact homDegree_heq_of_val_eq (B := B) (N := N) (P := P)
        hidx x' f hval

private theorem homActionTotalAll_mul_homogeneous (m n : ℤ)
    (a : A.grading m) (b : A.grading n) :
    homActionTotalAll A B N P L ((a : A.A) * (b : A.A)) =
      (homActionTotalAll A B N P L (b : A.A)).comp
        (homActionTotalAll A B N P L (a : A.A)) := by
  apply LinearMap.ext
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  | of q f =>
      rw [homActionTotalAll_of A B N P L (m + n)
        ⟨(a : A.A) * (b : A.A),
          SetLike.mul_mem_graded a.property b.property⟩,
        homActionOnTotal_of, homActionTotalAll_of A B N P L n b, LinearMap.comp_apply,
        homActionTotalAll_of A B N P L m a, homActionOnTotal_of, homActionOnTotal_of]
      apply DirectSum.of_eq_of_gradedMonoid_eq
      have hidx : q + (m + n) = (q + m) + n := by omega
      apply Sigma.ext hidx
      apply homDegree_heq_of_val_eq (B := B) (N := N) (P := P) hidx
      apply LinearMap.ext
      intro x
      show (f.1.comp (bimoduleActionTotal A B N L (m + n)
          ⟨(a : A.A) * (b : A.A),
            SetLike.mul_mem_graded a.property b.property⟩)) x =
        ((f.1.comp (bimoduleActionTotal A B N L m a)).comp
          (bimoduleActionTotal A B N L n b)) x
      rw [bimoduleActionTotal_mul]
      simp [LinearMap.comp_assoc]

private theorem homActionTotalAll_mul (a b : A.A) :
    homActionTotalAll A B N P L (a * b) =
      (homActionTotalAll A B N P L b).comp
        (homActionTotalAll A B N P L a) := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp [homActionTotalAll]
  | add a₁ a₂ ha₁ ha₂ =>
      simp only [map_add, add_mul]
      rw [ha₁, ha₂]
      simp [LinearMap.comp_add]
  | homogeneous a =>
      induction b using DirectSum.Decomposition.inductionOn A.grading with
      | zero => simp [homActionTotalAll]
      | add b₁ b₂ hb₁ hb₂ =>
          simp only [map_add, mul_add]
          rw [hb₁, hb₂]
          simp [LinearMap.add_comp]
      | homogeneous b =>
          exact homActionTotalAll_mul_homogeneous A B N P L _ _ a b

private noncomputable def homActionRingHom :
    MulOpposite A.A →+* Module.End R (homTotal B N P) where
  toFun a := homActionTotalAll A B N P L (MulOpposite.unop a)
  map_zero' := by simp [homActionTotalAll]
  map_add' a b := by
    change homActionTotalAll A B N P L (MulOpposite.unop (a + b)) = _
    rw [MulOpposite.unop_add]
    exact (homActionTotalAll A B N P L).map_add _ _
  map_one' := by
    change homActionTotalAll A B N P L (1 : A.A) = 1
    rw [homActionTotalAll_one]
    rfl
  map_mul' a b := by
    change homActionTotalAll A B N P L (MulOpposite.unop (a * b)) = _
    rw [MulOpposite.unop_mul]
    exact homActionTotalAll_mul A B N P L (MulOpposite.unop b) (MulOpposite.unop a)

private theorem homTotalDifferential_d_comp_d :
    (homTotalDifferential B N P).comp (homTotalDifferential B N P) = 0 := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro f
  show homTotalDifferential B N P
      (homTotalDifferential B N P (DirectSum.of _ n f)) = 0
  rw [homTotalDifferential_of, homTotalDifferential_of]
  have hdd :=
    (DifferentialGradedModule.dgCategory B).d_d f
  change DifferentialGradedModule.homogeneousMapDifferential B
      (DifferentialGradedModule.homogeneousMapDifferential B f) = 0 at hdd
  rw [hdd]
  simp

private theorem bimoduleActionTotal_d (m : ℤ) (a : A.grading m) :
    bimoduleActionTotal A B N L (m + 1)
        ⟨A.d a, A.d_mem m a a.property⟩ =
      N.d.comp (bimoduleActionTotal A B N L m a) -
        DifferentialGraded.gradedSign
          R m • (bimoduleActionTotal A B N L m a).comp N.d := by
  apply DirectSum.decompose_lhom_ext N.grading
  intro p
  ext x
  show bimoduleActionTotal A B N L (m + 1)
      ⟨A.d a, A.d_mem m a a.property⟩ (x : N.M) =
    N.d (bimoduleActionTotal A B N L m a (x : N.M)) -
      DifferentialGraded.gradedSign
        R m • bimoduleActionTotal A B N L m a (N.d x)
  have hMap := congrArg
    (fun c : CochainComplex.HomComplex.Cochain N.toCochainComplex N.toCochainComplex (m + 1) =>
      c.v p ((p + m) + 1) (by omega))
    (L.1.map_d m a)
  rw [CochainComplex.HomComplex.δ_v m (m + 1) (by omega) (L.1.action m a)
    p ((p + m) + 1) (by omega) (p + m) (p + 1) (by omega) rfl] at hMap
  have hsign : ((m + 1).negOnePow : R) = -
      DifferentialGraded.gradedSign
        R m := by
    rw [Int.negOnePow_succ]
    simp [DifferentialGraded.gradedSign,
      Int.coe_negOnePow]
  let dx : N.grading (p + 1) :=
    ⟨N.d x, N.d_mem p (x : N.M) x.property⟩
  have hdx : (dx : N.M) = N.d x := rfl
  have hdxsub : N.gradedDifferential p x = dx := by
    apply Subtype.ext
    rfl
  have hMapEval := congrArg (fun f => f.hom x) hMap
  simp only [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_smul] at hMapEval
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R] at hMapEval
  rw [hsign] at hMapEval
  have hMapInclEval := congrArg
    (fun y : N.toCochainComplex.X (p + m + 1) =>
      (cochainGradeIncl B N (p + m + 1)).hom y) hMapEval
  change _ = (cochainGradeIncl B N (p + m + 1)).hom
    (((ModuleCat.Hom.hom
        ((L.1.action m a).v p (p + m) (by omega) ≫
          N.toCochainComplex.d (p + m) (p + m + 1))) x) +
      (-DifferentialGraded.gradedSign
        R m) •
        ((ModuleCat.Hom.hom
          (N.toCochainComplex.d p (p + 1) ≫
            (L.1.action m a).v (p + 1) (p + m + 1) (by omega))) x)) at hMapInclEval
  rw [LinearMap.map_add, LinearMap.map_smul] at hMapInclEval
  have hpart1 :
      (cochainGradeIncl B N (p + m + 1)).hom
          ((ModuleCat.Hom.hom
            ((L.1.action m a).v p (p + m) (by omega) ≫
              N.toCochainComplex.d (p + m) (p + m + 1))) x) =
        N.d ((cochainGradeIncl B N (p + m)).hom
          (((L.1.action m a).v p (p + m) (by omega)).hom x)) := by
    rw [ModuleCat.hom_comp]
    exact cochainDifferentialIncl_apply B N (p + m)
      (((L.1.action m a).v p (p + m) (by omega)).hom x)
  have hdxX : (N.toCochainComplex.d p (p + 1)).hom x =
      (cochainCarrierEq B N (p + 1)).mpr dx := by
    rw [N.toCochainComplex_d]
    cases cochainCarrierEq B N p
    cases cochainCarrierEq B N (p + 1)
    apply Subtype.ext
    rfl
  have hpart2 :
      (cochainGradeIncl B N (p + m + 1)).hom
          ((ModuleCat.Hom.hom
            (N.toCochainComplex.d p (p + 1) ≫
              (L.1.action m a).v (p + 1) (p + m + 1) (by omega))) x) =
        (cochainGradeIncl B N (p + m + 1)).hom
          (((L.1.action m a).v (p + 1) (p + m + 1) (by omega)).hom dx) := by
    rw [ModuleCat.hom_comp]
    exact congrArg
      (fun y => (cochainGradeIncl B N (p + m + 1)).hom
        (((L.1.action m a).v (p + 1) (p + m + 1) (by omega)).hom y)) hdxX
  rw [hpart1, hpart2] at hMapInclEval
  rw [← hdx]
  rw [bimoduleActionTotal_apply_cochain (A := A) (B := B) (N := N) (L := L)
    (m + 1) p ⟨A.d a, A.d_mem m a a.property⟩ x,
    bimoduleActionTotal_apply_cochain (A := A) (B := B) (N := N) (L := L)
      m p a x,
    bimoduleActionTotal_apply_cochain (A := A) (B := B) (N := N) (L := L)
      m (p + 1) a dx]
  have hidx : (p + m) + 1 = p + (m + 1) := by omega
  have hidx' : p + m + 1 = p + 1 + m := by omega
  have hleft :
      (cochainGradeIncl B N (p + m + 1)).hom
          (((L.1.action (m + 1)
            ⟨A.d a, A.d_mem m a a.property⟩).v p (p + m + 1) (by omega)).hom x) =
        (cochainGradeIncl B N (p + (m + 1))).hom
          (((L.1.action (m + 1)
            ⟨A.d a, A.d_mem m a a.property⟩).v p (p + (m + 1)) (by omega)).hom x) := by
    exact cochainGradeIncl_hom_apply_irrel (B := B) (N := N)
      (L.1.action (m + 1) ⟨A.d a, A.d_mem m a a.property⟩)
      p (p + m + 1) (p + (m + 1)) (by omega) (by omega) x
  have hright :
      (cochainGradeIncl B N (p + m + 1)).hom
          (((L.1.action m a).v (p + 1) (p + m + 1) (by omega)).hom dx) =
        (cochainGradeIncl B N (p + 1 + m)).hom
          (((L.1.action m a).v (p + 1) (p + 1 + m) (by omega)).hom dx) := by
    exact cochainGradeIncl_hom_apply_irrel (B := B) (N := N)
      (L.1.action m a) (p + 1) (p + m + 1) (p + 1 + m)
      (by omega) (by omega) dx
  rw [hleft, hright] at hMapInclEval
  convert hMapInclEval using 1
  simp [ConcreteCategory.hom, ModuleCat.Hom.hom, sub_eq_add_neg]
  rfl

private theorem homPrecompPiece_homD (n m : ℤ) (a : A.grading m)
    (f : homDegree B N P n) :
    homDegreeCast B N P (show n + m + 1 = n + (m + 1) by omega)
        (DifferentialGradedModule.homogeneousMapDifferential B
          (homPrecompPiece A B N P L n m a f)) =
      homDegreeCast B N P (show (n + 1) + m = n + (m + 1) by omega)
          (homPrecompPiece A B N P L (n + 1) m a
            (DifferentialGradedModule.homogeneousMapDifferential B f)) +
        (DifferentialGraded.gradedSign
          R n) •
          homDegreeCast B N P (by omega)
            (homPrecompPiece A B N P L n (m + 1)
              ⟨A.d a, A.d_mem m a a.property⟩ f) := by
  apply Subtype.ext
  ext x
  show P.d (f.1 (bimoduleActionTotal A B N L m a x)) -
      DifferentialGraded.gradedSign
        R (n + m) • f.1 (bimoduleActionTotal A B N L m a (N.d x)) =
    (P.d (f.1 (bimoduleActionTotal A B N L m a x)) -
      DifferentialGraded.gradedSign
        R n • f.1 (N.d (bimoduleActionTotal A B N L m a x))) +
      DifferentialGraded.gradedSign
        R n • f.1 (bimoduleActionTotal A B N L (m + 1)
          ⟨A.d a, A.d_mem m a a.property⟩ x)
  have hAction := congrArg (fun T : N.M →ₗ[R] N.M => T x)
    (bimoduleActionTotal_d A B N L m a)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply] at hAction
  rw [hAction, map_sub, map_smul, DifferentialGraded.gradedSign_add]
  module

/-- The identification of degree-`n` homogeneous maps into `P[k]` with degree-`n + k`
homogeneous maps into `P`, given by the identity on underlying linear maps. -/
private def shiftHomEquiv (k n : ℤ) :
    DifferentialGradedModule.HomogeneousMap
        B N (DifferentialGradedModule.shift P k) n ≃ₗ[R] homDegree B N P (n + k) where
  toFun f := ⟨f.1, by
    constructor
    · intro i x hx
      have h := f.2.1 i x hx
      change f.1 x ∈ P.grading (i + n + k) at h
      simpa only [add_assoc] using h
    · intro a x
      exact f.2.2 a x⟩
  invFun f := ⟨f.1, by
    constructor
    · intro i x hx
      have h := f.2.1 i x hx
      change f.1 x ∈ (DifferentialGradedModule.shift P k).grading (i + n)
      simpa only [DifferentialGradedModule.shift_grading, add_assoc] using h
    · intro a x
      exact f.2.2 a x⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl
  map_add' f g := by
    apply Subtype.ext
    rfl
  map_smul' r f := by
    apply Subtype.ext
    rfl

private theorem shiftHomEquiv_val (k n : ℤ)
    (f : DifferentialGradedModule.HomogeneousMap
      B N (DifferentialGradedModule.shift P k) n) :
    (shiftHomEquiv B N P k n f : N.M →ₗ[R] P.M) = f.1 := rfl

attribute [local simp] shiftHomEquiv_val

private theorem shiftHomEquiv_symm_val (k n : ℤ)
    (f : homDegree B N P (n + k)) :
    ((shiftHomEquiv B N P k n).symm f).1 = f.1 := rfl

attribute [local simp] shiftHomEquiv_symm_val

/-- The reindexing equivalence intertwines the Hom differential with the
shifted differential, including the sign contributed by the shift. -/
private theorem shiftHomEquiv_homD (k n : ℤ)
    (f : DifferentialGradedModule.HomogeneousMap
      B N (DifferentialGradedModule.shift P k) n) :
    shiftHomEquiv B N P k (n + 1)
        (DifferentialGradedModule.homogeneousMapDifferential B f) =
      homDegreeCast B N P (by omega)
        ((DifferentialGraded.gradedSign
        R k) •
        DifferentialGradedModule.homogeneousMapDifferential B
          (shiftHomEquiv B N P k n f)) := by
  apply Subtype.ext
  show
    (DifferentialGradedModule.homogeneousMapDifferential B f).1 =
      DifferentialGraded.gradedSign
        R k •
        (DifferentialGradedModule.homogeneousMapDifferential B
          (shiftHomEquiv B N P k n f)).1
  ext x
  simp only [DifferentialGradedModule.homogeneousMapDifferential_val,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    DifferentialGradedModule.shift_d, shiftHomEquiv_val]
  have hk : ((k.negOnePow : ℤ) : R) =
      DifferentialGraded.gradedSign
        R k := Int.coe_negOnePow R k
  have hksq :
      DifferentialGraded.gradedSign
          R k *
        DifferentialGraded.gradedSign
          R k = 1 := by
    rw [← hk]
    simpa only [Units.val_mul, Units.val_one, Int.cast_mul, Int.cast_one] using
      congrArg (fun z : ℤˣ => (z : R)) (Int.units_mul_self k.negOnePow)
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R]
  rw [hk, smul_sub, smul_smul, DifferentialGraded.gradedSign_add]
  have hcoef :
      DifferentialGraded.gradedSign
          R k *
        (DifferentialGraded.gradedSign
            R n *
          DifferentialGraded.gradedSign
            R k) =
        DifferentialGraded.gradedSign
          R n := by
    rw [mul_left_comm, hksq, mul_one]
  rw [hcoef]

private theorem homDegree_intCast_smul {k : ℤ} (z : ℤ) (f : homDegree B N P k) :
    (z : R) • f = z • f :=
  Subtype.ext (LinearMap.ext fun x => Int.cast_smul_eq_zsmul R z (f.1 x))

private theorem homTotal_leibniz_of (n m : ℤ) (f : homDegree B N P n)
    (a : A.grading m) :
    homTotalDifferential B N P
        (homActionTotalAll A B N P L (a : A.A)
          (DirectSum.of (fun j : ℤ => homDegree B N P j) n f)) =
      homActionTotalAll A B N P L (a : A.A)
          (homTotalDifferential B N P
            (DirectSum.of (fun j : ℤ => homDegree B N P j) n f)) +
        n.negOnePow •
          homActionTotalAll A B N P L (A.d a)
            (DirectSum.of (fun j : ℤ => homDegree B N P j) n f) := by
  let da : A.grading (m + 1) := ⟨A.d a, A.d_mem m a a.property⟩
  have hda : (da : A.A) = A.d a := rfl
  rw [← hda]
  simp only [homActionTotalAll_of A B N P L m a,
    homActionTotalAll_of A B N P L (m + 1) da,
    homActionOnTotal_of, homTotalDifferential_of]
  have h := homPrecompPiece_homD A B N P L n m a f
  have hsign : (n.negOnePow : R) =
      DifferentialGraded.gradedSign
        R n := Int.coe_negOnePow R n
  rw [← hsign, homDegree_intCast_smul B N P] at h
  let K := n + (m + 1)
  have hL : n + m + 1 = K := by
    dsimp [K]
    omega
  have hF : (n + 1) + m = K := by
    dsimp [K]
    omega
  have hleft : DirectSum.of (fun j : ℤ => homDegree B N P j) K
        (homDegreeCast B N P hL
          (DifferentialGradedModule.homogeneousMapDifferential B
            (homPrecompPiece A B N P L n m a f))) =
      DirectSum.of (fun j : ℤ => homDegree B N P j) (n + m + 1)
        (DifferentialGradedModule.homogeneousMapDifferential B
          (homPrecompPiece A B N P L n m a f)) := by
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply Sigma.ext hL.symm
    exact (homDegreeCast_heq B N P hL _).symm
  have hfirst : DirectSum.of (fun j : ℤ => homDegree B N P j) K
        (homDegreeCast B N P hF
          (homPrecompPiece A B N P L (n + 1) m a
            (DifferentialGradedModule.homogeneousMapDifferential B f))) =
      DirectSum.of (fun j : ℤ => homDegree B N P j) ((n + 1) + m)
        (homPrecompPiece A B N P L (n + 1) m a
          (DifferentialGradedModule.homogeneousMapDifferential B f)) := by
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply Sigma.ext hF.symm
    exact (homDegreeCast_heq B N P hF _).symm
  have hsecond : DirectSum.of (fun j : ℤ => homDegree B N P j) K
        (homDegreeCast B N P (show K = K by rfl)
          (homPrecompPiece A B N P L n (m + 1)
            ⟨A.d a, A.d_mem m a a.property⟩ f)) =
    DirectSum.of (fun j : ℤ => homDegree B N P j) K
        (homPrecompPiece A B N P L n (m + 1) da f) := by
    congr 1
  have htotal := congrArg
    (fun z : homDegree B N P K => DirectSum.of (fun j : ℤ => homDegree B N P j) K z) h
  simp only [map_add, DirectSum.of_smul] at htotal
  calc
    _ = DirectSum.of (fun j : ℤ => homDegree B N P j) K
        (homDegreeCast B N P hL
          (DifferentialGradedModule.homogeneousMapDifferential B
            (homPrecompPiece A B N P L n m a f))) := hleft.symm
    _ = DirectSum.of (fun j : ℤ => homDegree B N P j) K
        (homDegreeCast B N P hF
          (homPrecompPiece A B N P L (n + 1) m a
            (DifferentialGradedModule.homogeneousMapDifferential B f))) +
        (n.negOnePow : ℤ) • DirectSum.of (fun j : ℤ => homDegree B N P j) K
          (homDegreeCast B N P (by omega)
            (homPrecompPiece A B N P L n (m + 1)
              ⟨A.d a, A.d_mem m a a.property⟩ f)) := htotal
    _ = _ := by
      rw [hfirst, hsecond]
      rfl

@[implicit_reducible] private noncomputable def homDGMModule :
    DifferentialGradedModule.{u, v, max u w} A := by
  let M := homTotal B N P
  letI : Module (MulOpposite A.A) M :=
    Module.compHom M (homActionRingHom A B N P L)
  letI : IsScalarTower R (MulOpposite A.A) M := by
    refine ⟨?_⟩
    intro r a x
    change homActionTotalAll A B N P L (MulOpposite.unop (r • a)) x =
      r • homActionTotalAll A B N P L (MulOpposite.unop a) x
    rw [show MulOpposite.unop (r • a) = r • MulOpposite.unop a by simp,
      (homActionTotalAll A B N P L).map_smul]
    rfl
  refine {
    M := M
    grading := homTotalGrade B N P
    decomposition := homTotalDecomposition B N P
    smul_mem := ?_
    d := homTotalDifferential B N P
    d_comp_d := homTotalDifferential_d_comp_d B N P
    d_mem := homTotalDifferential_mem B N P
    leibniz := ?_ }
  · intro n m x a hx ha
    rcases hx with ⟨f, rfl⟩
    let a' : A.grading m := ⟨a, ha⟩
    change homActionTotalAll A B N P L a (DirectSum.of _ n f) ∈
      homTotalGrade B N P (n + m)
    rw [homActionTotalAll_of A B N P L m a', homActionOnTotal_of]
    exact ⟨homPrecompPiece A B N P L n m a' f, by
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_gradedMonoid_eq]
      rfl⟩
  · intro n m x a hx ha
    rcases hx with ⟨f, rfl⟩
    let a' : A.grading m := ⟨a, ha⟩
    have hAct : ∀ (b : A.A) (z : M),
        MulOpposite.op b • z = homActionTotalAll A B N P L b z := by
      intro b z
      rfl
    simpa only [hAct, a', DirectSum.lof_eq_of, Units.smul_def] using
      homTotal_leibniz_of A B N P L n m f a'

private def homTotalGradeIncl (n : ℤ) :
    homDegree B N P n →ₗ[R] homTotalGrade B N P n where
  toFun f := ⟨DirectSum.lof R ℤ (fun j : ℤ => homDegree B N P j) n f, ⟨f, rfl⟩⟩
  map_add' f g := by
    apply Subtype.ext
    exact (DirectSum.lof R ℤ (fun j : ℤ => homDegree B N P j) n).map_add f g
  map_smul' r f := by
    apply Subtype.ext
    exact (DirectSum.lof R ℤ (fun j : ℤ => homDegree B N P j) n).map_smul r f

private theorem homTotalGradeIncl_injective (n : ℤ) :
    Function.Injective (homTotalGradeIncl B N P n) :=
  fun _ _ h => DirectSum.of_injective n (congrArg Subtype.val h)

private theorem homTotalGradeIncl_surjective (n : ℤ) :
    Function.Surjective (homTotalGradeIncl B N P n) := by
  intro x
  rcases x.property with ⟨f, hf⟩
  exact ⟨f, Subtype.ext hf⟩

private noncomputable def homTotalGradeEquiv (n : ℤ) :
    homTotalGrade B N P n ≃ₗ[R] homDegree B N P n :=
  (LinearEquiv.ofBijective (homTotalGradeIncl B N P n)
    ⟨homTotalGradeIncl_injective B N P n, homTotalGradeIncl_surjective B N P n⟩).symm

private theorem homTotalGradeEquiv_incl (n : ℤ) (f : homDegree B N P n) :
    homTotalGradeEquiv B N P n (homTotalGradeIncl B N P n f) = f := by
  exact (LinearEquiv.ofBijective (homTotalGradeIncl B N P n)
    ⟨homTotalGradeIncl_injective B N P n, homTotalGradeIncl_surjective B N P n⟩).symm_apply_apply f

attribute [local simp] homTotalGradeEquiv_incl

private theorem homTotalGradeIncl_equiv (n : ℤ)
    (f : homTotalGrade B N P n) :
    homTotalGradeIncl B N P n (homTotalGradeEquiv B N P n f) = f := by
  exact (LinearEquiv.ofBijective (homTotalGradeIncl B N P n)
    ⟨homTotalGradeIncl_injective B N P n, homTotalGradeIncl_surjective B N P n⟩).apply_symm_apply f

attribute [local simp] homTotalGradeIncl_equiv

/-- The homogeneous summand of a graded element is recovered from its image under
`homTotalGradeEquiv`. -/
private theorem lof_homTotalGradeEquiv (n : ℤ) (f : homTotalGrade B N P n) :
    DirectSum.lof R ℤ (fun j : ℤ => homDegree B N P j) n (homTotalGradeEquiv B N P n f) =
      (f : homTotal B N P) :=
  congrArg Subtype.val (homTotalGradeIncl_equiv B N P n f)

private theorem homogeneousEquiv_val_eq
    (H : HomDGModulePresentation A B N P L) {i j : ℤ} (h : i = j)
    (f : H.module.grading i) (g : H.module.grading j) (hfg : f.1 = g.1) :
    (H.homogeneousEquiv i f).1 = (H.homogeneousEquiv j g).1 := by
  subst j
  have : f = g := Subtype.ext hfg
  subst g
  rfl

private noncomputable def homDGModulePresentation :
    HomDGModulePresentation A B N P L where
  module := homDGMModule A B N P L
  homogeneousEquiv := homTotalGradeEquiv B N P
  map_d := by
    intro n f
    change homTotalGrade B N P n at f
    change homTotalGradeEquiv B N P (n + 1)
      ((homDGMModule A B N P L).gradedDifferential n f) =
      DifferentialGradedModule.homogeneousMapDifferential B
        (homTotalGradeEquiv B N P n f)
    apply homTotalGradeIncl_injective
    rw [homTotalGradeIncl_equiv]
    apply Subtype.ext
    change homTotalDifferential B N P (f : homTotal B N P) =
      DirectSum.of (fun j : ℤ => homDegree B N P j) (n + 1)
        (DifferentialGradedModule.homogeneousMapDifferential B
          (homTotalGradeEquiv B N P n f))
    conv_lhs => rw [← lof_homTotalGradeEquiv B N P n f]
    rw [DirectSum.lof_eq_of, homTotalDifferential_of]
  map_smul := by
    intro n m p f a x
    change homTotalGrade B N P n at f
    let : Module (MulOpposite A.A) (homTotal B N P) :=
      (homDGMModule A B N P L).rmodule
    have hsmul :
        homTotalGradeEquiv B N P (n + m)
          ⟨MulOpposite.op (a : A.A) • (f : homTotal B N P),
            (homDGMModule A B N P L).smul_mem n m (f : homTotal B N P)
              (a : A.A) f.property a.property⟩ =
          homPrecompPiece A B N P L n m a (homTotalGradeEquiv B N P n f) := by
      apply homTotalGradeIncl_injective
      simp only [homTotalGradeIncl_equiv]
      apply Subtype.ext
      have hAct : ∀ z : homTotal B N P,
          MulOpposite.op (a : A.A) • z =
            homActionTotalAll A B N P L (a : A.A) z := by
        intro z
        rfl
      simp only [hAct]
      conv_lhs => rw [← lof_homTotalGradeEquiv B N P n f, DirectSum.lof_eq_of]
      rw [homActionTotalAll_of A B N P L m a, homActionOnTotal_of]
      rfl
    change (homTotalGradeEquiv B N P (n + m)
        ⟨MulOpposite.op (a : A.A) • (f : homTotal B N P),
          (homDGMModule A B N P L).smul_mem n m (f : homTotal B N P)
            (a : A.A) f.property a.property⟩).1 x =
      (homTotalGradeEquiv B N P n f).1
        ((show N.grading (p + m) from
          (L.1.action m a).v p (p + m) (by omega) x) : N.M)
    rw [hsmul]
    change (homTotalGradeEquiv B N P n f).1
        (bimoduleActionTotal A B N L m a (x : N.M)) =
      (homTotalGradeEquiv B N P n f).1
        ((show N.grading (p + m) from
          (L.1.action m a).v p (p + m) (by omega) x) : N.M)
    rw [bimoduleActionTotal_apply_cochain]
    rfl

/-- The canonical, sign-free isomorphism
`Hom_B^gr(N,P)[k] ≅ Hom_B^gr(N,P[k])` of right DG `A`-modules.
The equality says that the associated homogeneous maps have the same value
on each homogeneous element of `N`. -/
@[stacks 0FQR]
public theorem shiftHomIso (k : ℤ) :
    ∃ (H : HomDGModulePresentation A B N P L)
      (Hk : HomDGModulePresentation A B N (DifferentialGradedModule.shift P k) L)
      (e : DifferentialGradedModule.shift H.module k ≅ Hk.module),
      ∀ (n p : ℤ) (f : (DifferentialGradedModule.shift H.module k).grading n)
        (x : N.grading p),
        ((Hk.homogeneousEquiv n (e.hom.gradedMap n f)).1 x : P.M) =
          (H.homogeneousEquiv (n + k)
            ⟨(f.1 : H.module.M), by
              simpa only [DifferentialGradedModule.shift_grading] using f.property⟩).1 x :=
  by
    classical
    let H : HomDGModulePresentation A B N P L := homDGModulePresentation A B N P L
    let Hk : HomDGModulePresentation A B N (DifferentialGradedModule.shift P k) L := {
      module := DifferentialGradedModule.shift H.module k
      homogeneousEquiv := fun n =>
        (H.homogeneousEquiv (n + k)).trans (shiftHomEquiv B N P k n).symm
      map_d := by
        intro n f
        change H.module.grading (n + k) at f
        apply (shiftHomEquiv B N P k (n + 1)).injective
        show H.homogeneousEquiv ((n + 1) + k)
            ((DifferentialGradedModule.shift H.module k).gradedDifferential n f) =
          shiftHomEquiv B N P k (n + 1)
            (DifferentialGradedModule.homogeneousMapDifferential B
              ((shiftHomEquiv B N P k n).symm (H.homogeneousEquiv (n + k) f)))
        rw [shiftHomEquiv_homD]
        rw [LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        show (H.homogeneousEquiv (n + 1 + k)
            ⟨k.negOnePow • H.module.d f, _⟩).1 =
          (DifferentialGraded.gradedSign
            R k •
            DifferentialGradedModule.homogeneousMapDifferential B
              (H.homogeneousEquiv (n + k) f)).1
        calc
          _ = (H.homogeneousEquiv (n + k + 1)
              ((k.negOnePow : ℤ) • H.module.gradedDifferential (n + k) f)).1 := by
            apply homogeneousEquiv_val_eq A B N P L H (by omega)
            rfl
          _ = _ := by
            rw [map_zsmul, H.map_d]
            show (k.negOnePow : ℤ) •
                (DifferentialGradedModule.homogeneousMapDifferential B
                  (H.homogeneousEquiv (n + k) f)).1 = _
            rw [← Int.cast_smul_eq_zsmul R, Int.coe_negOnePow]
            rfl
      map_smul := by
        intro n m p f a x
        change H.module.grading (n + k) at f
        show ((shiftHomEquiv B N P k (n + m)).symm
            (H.homogeneousEquiv (n + m + k)
              ⟨MulOpposite.op (a : A.A) • (f : H.module.M),
                (by
                  simpa [add_assoc, add_comm, add_left_comm] using
                    H.module.smul_mem (n + k) m (f : H.module.M) (a : A.A)
                      f.property a.property)⟩)).1 x =
          ((shiftHomEquiv B N P k n).symm (H.homogeneousEquiv (n + k) f)).1
            ((show N.grading (p + m) from
              (L.1.action m a).v p (p + m) (by omega) x) : N.M)
        simp only [shiftHomEquiv_symm_val]
        calc
          _ = (H.homogeneousEquiv (n + k + m)
              ⟨MulOpposite.op (a : A.A) • (f : H.module.M),
                H.module.smul_mem (n + k) m _ _ f.property a.property⟩).1 x := by
            congr 1
            apply homogeneousEquiv_val_eq A B N P L H (by omega)
            rfl
          _ = _ := H.map_smul (n + k) m p f a x }
    refine ⟨H, Hk, Iso.refl _, ?_⟩
    intro n p f x
    show (Hk.homogeneousEquiv n
        ((Iso.refl (DifferentialGradedModule.shift H.module k)).hom.gradedMap n f)).1 x =
      (H.homogeneousEquiv (n + k)
        ⟨(f.1 : H.module.M), by
          simpa only [DifferentialGradedModule.shift_grading] using f.property⟩).1 x
    simp only [Hk, LinearEquiv.trans_apply, shiftHomEquiv_symm_val]
    rfl

/-- The canonical presentation of the differential graded `A`-module of graded right `B`-linear
maps from `N` to `P`: its degree-`n` part is the module `DifferentialGradedModule.HomogeneousMap`
of degree-`n` homogeneous right `B`-linear maps, its differential is the signed commutator
`DifferentialGradedModule.homogeneousMapDifferential`, and the right `A`-action is
precomposition with the left action of `A` on `N`. -/
@[no_expose, sga "2 V 1.1" "more general"] public noncomputable def homComplexPresentation :
    HomDGModulePresentation A B N P L :=
  homDGModulePresentation A B N P L

/-- The differential graded `A`-module of graded right `B`-linear maps from `N` to `P`. -/
public noncomputable abbrev homComplex : DifferentialGradedModule.{u, v, max u w} A :=
  (homComplexPresentation A B N P L).module

/-- The degree-`n` part of the Hom module is the module of degree-`n` homogeneous right
`B`-linear maps from `N` to `P`. -/
public noncomputable abbrev homComplexHomogeneousEquiv (n : ℤ) :
    (homComplex A B N P L).grading n ≃ₗ[R]
      DifferentialGradedModule.HomogeneousMap B N P n :=
  (homComplexPresentation A B N P L).homogeneousEquiv n

/-- The differential of the Hom module is the signed commutator with the differentials of `N`
and `P`. -/
public theorem homComplex_gradedDifferential (n : ℤ) (f : (homComplex A B N P L).grading n) :
    homComplexHomogeneousEquiv A B N P L (n + 1)
        ((homComplex A B N P L).gradedDifferential n f) =
      DifferentialGradedModule.homogeneousMapDifferential B
        (homComplexHomogeneousEquiv A B N P L n f) :=
  (homComplexPresentation A B N P L).map_d n f

/-- The right `A`-action on the Hom module is precomposition with the left action of `A` on
`N`. -/
public theorem homComplex_smul (n m p : ℤ) (f : (homComplex A B N P L).grading n)
    (a : A.grading m) (x : N.grading p) :
    ((homComplexHomogeneousEquiv A B N P L (n + m)
        ⟨MulOpposite.op (a : A.A) • (f : (homComplex A B N P L).M),
          (homComplex A B N P L).smul_mem n m (f : (homComplex A B N P L).M)
            (a : A.A) f.property a.property⟩).1 x) =
      (homComplexHomogeneousEquiv A B N P L n f).1
        ((show N.grading (p + m) from (L.1.action m a).v p (p + m) (by omega) x) : N.M) :=
  (homComplexPresentation A B N P L).map_smul n m p f a x

end DifferentialGradedModule
