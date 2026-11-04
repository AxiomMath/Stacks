module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.RightAction
public import StacksFrontier.Homology.HomComplex.Differentials

/-!
# Evaluation into the double Hom complex of a differential graded module

Let `R` be a commutative ring, `A` a differential graded `R`-algebra and `N` a cochain complex of
`R`-modules. For a right differential graded `A`-module `M` the Hom complex `Hom^•(M, N)` is a
*left* differential graded `A`-module, its Hom complex into `N` is again a right differential
graded `A`-module, and evaluation

`ev : M ⟶ Hom(Hom(M, N), N)`

is a homomorphism of right differential graded `A`-modules. This is the right-handed orientation,
Tag 0FQ8. The source states the left-handed orientation separately as Tag 0FQ7: for a *left*
differential graded `A`-module `M`, the Hom complex `Hom^•(M, N)` is a *right* differential graded
`A`-module, its Hom complex into `N` is again a *left* differential graded `A`-module, and `ev` is
a homomorphism of *left* differential graded `A`-modules. Both orientations are formalized here,
the left-handed one by graded opposition from the right-handed one.

The two orientations are carried by two structures with the same name `HomEvaluationData`,
distinguished only by their namespace: `DifferentialGradedModule.HomEvaluationData` is the
right-handed one (Tag 0FQ8) and `DifferentialGraded.LeftModule.HomEvaluationData` the left-handed
one (Tag 0FQ7). Each sits inside the namespace of the orientation it is about, so an unqualified
`HomEvaluationData` in that namespace resolves to the right structure.

For the left-handed orientation the tagged statement is not the structure but
`DifferentialGraded.LeftModule.exists_homEvaluation`, which exhibits the two Hom modules, the
evaluation homomorphism `ev` between them, its `A`-linearity and its identification with the
evaluation map of Tag 0FNM as separate conjuncts, so that all of it is readable without unfolding
a structure; `nonempty_homEvaluationData` is the same content packaged for consumers.

## Main definitions

* `DifferentialGradedModule.HomEvaluationData`: the two Hom modules, their canonical actions and
  the evaluation homomorphism, for a *right* differential graded module (Tag 0FQ8).
* `DifferentialGraded.LeftModule.HomEvaluationData`: the same for a *left* differential graded
  module, with the orientations of every piece reversed (Tag 0FQ7).

## Main results

* `DifferentialGradedAlgebra.LeftAction.exists_leftModule`: every left differential graded action
  on a complex is realized by a left differential graded module.
* `DifferentialGradedModule.exists_homLeftModule`: for a right differential graded module `M`, the
  Hom complex `Hom^•(M, N)` is a left differential graded `A`-module, with the signed action.
* `DifferentialGraded.LeftModule.exists_homRightModule`: for a left differential graded module `L`,
  the Hom complex `Hom^•(L, N)` is a right differential graded `A`-module, acting by
  precomposition.
* `DifferentialGradedModule.nonempty_homEvaluationData` (Tag 0FQ8): for a *right* differential
  graded module, evaluation is a homomorphism of *right* differential graded modules.
* `DifferentialGraded.LeftModule.exists_homEvaluation` (Tag 0FQ7): for a *left* differential
  graded module `L`, the Hom module `Hom^•(L, N)`, the double Hom module, the evaluation
  homomorphism of *left* differential graded modules between them, its `A`-linearity and its
  identification with the evaluation map of Tag 0FNM.
* `DifferentialGraded.LeftModule.nonempty_homEvaluationData`: the same data packaged as a
  `HomEvaluationData`.

## Implementation notes

*The Hom modules are specified, not named.* Neither `Hom^•(M, N)` nor its double has a canonical
presentation as a differential graded module: only its underlying complex is canonical. The data
structures therefore record a module together with an isomorphism of its underlying complex with
the relevant Hom complex, and the formulas that isomorphism satisfies on homogeneous elements.
This is what lets the construction be performed once, through the correspondence between actions
on a complex and homomorphisms into its endomorphism algebra, without choosing a direct sum.

*Two of the formulas are heterogeneous equations.* Where a cochain of a Hom complex is applied to a
homogeneous element, the degree of the result is determined by the two degrees in two different
orders (`n + (p + q)` versus `n + p + q`), and the two terms consequently live in two
`Eq`-incompatible types; the statements are therefore `HEq`, with the degree equality implicit in
the statement rather than inserted as a cast.

*The underlying map of complexes is Tag 0FNM.* The evaluation of a complex into its double Hom
complex, with its sign `(-1)^{nq}`, is
`CochainComplex.HomComplex.evaluationToDoubleHom`; what is added here is that it is
`A`-linear, which is checked on homogeneous elements and then extended along the graded
decomposition by `DifferentialGradedModule.exists_hom_of_cochainMap`.

*The left-module statement is the right-module one over the graded opposite.* Graded opposition
(Tag 0FQ0) turns left `A`-modules into right `A^{opp}`-modules; applying the right-handed
construction over `A^{opp}` and transporting back along the canonical identification of `A` with
the graded opposite of `A^{opp}` (`DifferentialGradedAlgebra.Opposite.involution`) gives the
left-handed statement, and the Koszul signs of the two transports cancel.

## References

* [Stacks Project, Tag 0FQ7](https://stacks.math.columbia.edu/tag/0FQ7)
* [Stacks Project, Tag 0FQ8](https://stacks.math.columbia.edu/tag/0FQ8)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u v

variable {R : Type u} [CommRing R]

namespace DifferentialGradedAlgebra

/-- **Stacks 0FQ3.** Every left differential graded action of `A` on a complex `X` of `R`-modules
is the action of a left differential graded `A`-module whose underlying complex is identified with
`X`. -/
theorem LeftAction.exists_leftModule (A : DifferentialGradedAlgebra.{u, v} R)
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (s : A.LeftAction X) :
    ∃ (L : DifferentialGraded.LeftModule A)
      (i : DifferentialGraded.LeftModule.toCochainComplex A L ≅ X),
      ∀ (p q : ℤ) (a : A.grading p) (x : L.grading q),
        (s.action p a).v q (q + p) rfl (i.hom.f q x) =
          i.hom.f (q + p)
            (⟨(a : A.A) • (x : L.M), by
              simpa only [add_comm] using
                L.smul_mem p q (a : A.A) (x : L.M) a.property x.property⟩ :
              L.grading (q + p)) := by
  classical
  let O := DifferentialGradedAlgebra.opposite R A
  let c := A.leftActionEquivHom X
  let τ : O.toDifferentialGradedAlgebra.Hom (DifferentialGradedModule.oppEndAlgebra X) :=
    DifferentialGradedAlgebra.oppositeHom O (DifferentialGradedModule.oppEndOpposite X) (c.val s)
  obtain ⟨P, j, hj⟩ :=
    DifferentialGradedModule.exists_rightModule_isSignedAction
      O.toDifferentialGradedAlgebra X τ
  let F := DifferentialGraded.leftRightEquivalence R A
  let L := F.equivalence.inverse.obj P
  let k := F.equivalence.counitIso.app P
  let U := F.underlying L
  refine ⟨L, DifferentialGraded.LeftModule.oppositeCochainIso A L ≪≫
    (DifferentialGradedModule.forgetToCochainComplex O.toDifferentialGradedAlgebra).mapIso k ≪≫ j,
    ?_⟩
  intro p q a x
  let b : O.toDifferentialGradedAlgebra.grading p :=
    ⟨O.equiv.symm a, (O.mem_grading_iff p _).mpr (by simp)⟩
  let y : (F.equivalence.functor.obj L).grading q :=
    ⟨U.symm x, (F.grading L q _).mpr (by simp [U])⟩
  let z : P.grading q :=
    ⟨k.hom.toFun (y : (F.equivalence.functor.obj L).M),
      k.hom.map_grading q (y : (F.equivalence.functor.obj L).M) y.property⟩
  have he : (CochainComplex.endomorphismDGA X).cochainEquiv p
      ⟨(DifferentialGradedModule.oppEndOpposite X).equiv
          (τ.toAlgebraHom (b : O.toDifferentialGradedAlgebra.A)),
        ((DifferentialGradedModule.oppEndOpposite X).mem_grading_iff p _).mp
          (τ.map_grading p (b : O.toDifferentialGradedAlgebra.A) b.property)⟩ = s.action p a := by
    refine Eq.trans
      (congrArg ((CochainComplex.endomorphismDGA X).cochainEquiv p) (Subtype.ext ?_))
      (c.property s p a)
    show (DifferentialGradedModule.oppEndOpposite X).equiv
      ((DifferentialGradedModule.oppEndOpposite X).equiv.symm
        ((c.val s).toAlgebraHom (O.equiv (b : O.toDifferentialGradedAlgebra.A)))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact congrArg (c.val s).toAlgebraHom (O.equiv.apply_symm_apply (a : A.A))
  have hh := hj p q b z
  rw [he] at hh
  have hm : U.symm ((a : A.A) • (x : L.M)) =
      (p * q).negOnePow • (MulOpposite.op (b : O.toDifferentialGradedAlgebra.A) •
        (y : (F.equivalence.functor.obj L).M)) := by
    apply U.injective
    rw [LinearEquiv.apply_symm_apply, Units.smul_def, map_zsmul, ← Units.smul_def,
      F.action L p q b y b.property y.property]
    simp [b, y, U, O, smul_smul, Int.units_mul_self]
  have hiapp (t : ℤ) (v : L.grading t) :
      ((DifferentialGraded.LeftModule.oppositeCochainIso A L ≪≫
        (DifferentialGradedModule.forgetToCochainComplex
          O.toDifferentialGradedAlgebra).mapIso k ≪≫ j).hom.f t) v = (j.hom.f t)
        (⟨k.hom.toFun (U.symm v), k.hom.map_grading t _
          ((F.grading L t _).mpr (by simp [U]))⟩ : P.grading t) := rfl
  rw [hiapp, hiapp, hh]
  have hsub :
      (⟨k.hom.toFun (U.symm ((a : A.A) • (x : L.M))),
        k.hom.map_grading (q + p) _ ((F.grading L (q + p) _).mpr (by
          simp only [U, LinearEquiv.apply_symm_apply]
          simpa only [add_comm] using
            L.smul_mem p q (a : A.A) (x : L.M) a.property x.property))⟩ : P.grading (q + p)) =
      (p * q).negOnePow •
        (⟨MulOpposite.op (b : O.toDifferentialGradedAlgebra.A) • (z : P.M),
          P.smul_mem q p z b z.property b.property⟩ : P.grading (q + p)) := by
    apply Subtype.ext
    show k.hom.toFun (U.symm ((a : A.A) • (x : L.M))) = _
    rw [hm, show k.hom.toFun ((p * q).negOnePow •
        (MulOpposite.op (b : O.toDifferentialGradedAlgebra.A) •
          (y : (F.equivalence.functor.obj L).M))) =
      (p * q).negOnePow • k.hom.toFun (MulOpposite.op (b : O.toDifferentialGradedAlgebra.A) •
        (y : (F.equivalence.functor.obj L).M)) from map_zsmul _ _ _, k.hom.map_smul]
    rfl
  rw [hsub]
  exact (map_zsmul (j.hom.f (q + p)).hom _ _).symm

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

/-- Two homogeneous elements with the same underlying value are heterogeneously equal. -/
private theorem gradedElement_heq {X : Type*} [AddCommGroup X] [Module R X]
    (G : ℤ → Submodule R X) {p p' : ℤ} (h : p = p') (x : X) (hx : x ∈ G p) (hx' : x ∈ G p') :
    HEq (⟨x, hx⟩ : G p) (⟨x, hx'⟩ : G p') := by
  subst h; rfl

/-- Evaluating a cochain of a Hom complex at a homogeneous element respects heterogeneous
equality of the cochain and of the degrees involved. -/
private theorem homComplex_apply_heq {H K N : CochainComplex (ModuleCat.{u} R) ℤ}
    (i : H ⟶ HomComplexR R K N) {p p' q t t' : ℤ} (hp : p = p') (ht : t = t')
    (x : H.X p) (x' : H.X p') (hx : HEq x x') (y : K.X q) (h : q + p = t) (h' : q + p' = t') :
    HEq ((((i.f p).hom x).v q t h).hom y) ((((i.f p').hom x').v q t' h').hom y) := by
  subst hp; subst ht; cases hx; rfl

/-- Multiplying heterogeneously equal elements of a complex by a sign keeps them heterogeneously
equal. -/
private theorem complex_units_smul_heq (N : CochainComplex (ModuleCat.{u} R) ℤ) (s : ℤˣ)
    {t t' : ℤ} (ht : t = t') {x : N.X t} {y : N.X t'} (h : HEq x y) : HEq (s • x) (s • y) := by
  subst ht; cases h; rfl

/-- The signed value of a cochain at a homogeneous element does not depend on which expression
for the target degree is used. -/
private theorem signed_cochain_apply_heq {K N : CochainComplex (ModuleCat.{u} R) ℤ}
    {q n m m' : ℤ} (f : Cochain K N q) (hnm : n + q = m) (hnm' : n + q = m') (sign : ℤˣ)
    (x : K.X n) :
    HEq (sign • (f.v n m hnm).hom x) (sign • (f.v n m' hnm').hom x) := by
  subst hnm; subst hnm'; rfl

/-- Pulling a sign out of an `R`-linear map and merging it with another sign. -/
private theorem smul_apply_eq {X Y : ModuleCat.{u} R} (φ : X ⟶ Y) (c₁ c₂ c₃ : ℤˣ)
    (h : c₃ = c₁ * c₂) (y : X) :
    (c₁ : ℤ) • φ.hom ((c₂ : ℤ) • y) = (c₃ : ℤ) • φ.hom y := by
  rw [map_zsmul, smul_smul, h, Units.val_mul]

/-- The signed value, at a homogeneous element, of the precomposition of a cochain with a right
differential graded action. This is the computation behind the action formula on a Hom complex;
it is stated for a free cochain `g` so that the Hom complex itself does not occur. -/
private theorem signedComp_apply_heq (A : DifferentialGradedAlgebra.{u, v} R)
    (M : DifferentialGradedModule A) (N : CochainComplex (ModuleCat.{u} R) ℤ)
    (t : A.RightAction M.toCochainComplex)
    (ht : ∀ (m k : ℤ) (b : A.grading m) (y : M.grading k),
      ((t.action m b).v k (k + m) rfl).hom y =
        (m * k).negOnePow • (⟨MulOpposite.op (b : A.A) • (y : M.M),
          M.smul_mem k m (y : M.M) (b : A.A) y.property b.property⟩ : M.grading (k + m)))
    (p q n : ℤ) (a : A.grading p) (g : Cochain M.toCochainComplex N q) (x : M.grading n) :
    HEq
      ((((p * q).negOnePow • (t.action p a).comp g (show p + q = q + p by omega)).v n
        (n + (q + p)) (by omega)).hom x)
      ((p * (q + n)).negOnePow •
        ((g.v (n + p) (n + p + q) (by omega)).hom
          (⟨MulOpposite.op (a : A.A) • (x : M.M),
            M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ : M.grading (n + p)))) := by
  refine HEq.trans (heq_of_eq (a' := (p * (q + n)).negOnePow •
    ((g.v (n + p) (n + (q + p)) (by omega)).hom
      (⟨MulOpposite.op (a : A.A) • (x : M.M),
        M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ : M.grading (n + p)))) ?_)
    (signed_cochain_apply_heq (K := M.toCochainComplex) g (by omega) (by omega)
      (p * (q + n)).negOnePow _)
  show (p * q).negOnePow •
      ((g.v (n + p) (n + (q + p)) (by omega)).hom
        (((t.action p a).v n (n + p) rfl).hom x)) = _
  rw [ht p n a x]
  simp only [Units.smul_def]
  exact smul_apply_eq _ (p * q).negOnePow (p * n).negOnePow (p * (q + n)).negOnePow
    (by rw [← Int.negOnePow_add, mul_add]) _

/-- **Stacks 0FQ2.** For a right differential graded `A`-module `M` and a complex `N` of
`R`-modules, the Hom complex `Hom^•(M, N)` is a left differential graded `A`-module: a homogeneous
element of degree `p` acts on a homogeneous cochain of degree `q` by `(-1)^{p(q + n)}` times
precomposition with right multiplication, on elements of degree `n`. -/
theorem exists_homLeftModule (A : DifferentialGradedAlgebra.{u, v} R)
    (M : DifferentialGradedModule A) (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (H : DifferentialGraded.LeftModule A)
      (i : DifferentialGraded.LeftModule.toCochainComplex A H ≅
        HomComplexR R M.toCochainComplex N),
      ∀ (p q n : ℤ) (a : A.grading p) (f : H.grading q) (x : M.grading n),
        HEq
          ((((i.hom.f (p + q))
              (⟨(a : A.A) • (f : H.M),
                H.smul_mem p q (a : A.A) (f : H.M) a.property f.property⟩ :
                H.grading (p + q))).v n (n + (p + q)) (by omega)).hom x)
          ((p * (q + n)).negOnePow •
            (((i.hom.f q) f).v (n + p) (n + p + q) (by omega)).hom
              (⟨MulOpposite.op (a : A.A) • (x : M.M),
                M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ :
                M.grading (n + p))) := by
  classical
  obtain ⟨t, ht0⟩ := exists_rightAction A M M.toCochainComplex (Iso.refl _)
  have ht : ∀ (m k : ℤ) (b : A.grading m) (y : M.grading k),
      ((t.action m b).v k (k + m) rfl).hom y =
        (m * k).negOnePow • (⟨MulOpposite.op (b : A.A) • (y : M.M),
          M.smul_mem k m (y : M.M) (b : A.A) y.property b.property⟩ : M.grading (k + m)) := ht0
  obtain ⟨H, i, hi⟩ :=
    DifferentialGradedAlgebra.LeftAction.exists_leftModule A
      (HomComplexR R M.toCochainComplex N) (t.homLeftAction N)
  refine ⟨H, i, ?_⟩
  intro p q n a f x
  have key : HEq
      ((((i.hom.f (q + p))
          (⟨(a : A.A) • (f : H.M), by
            simpa only [add_comm] using
              H.smul_mem p q (a : A.A) (f : H.M) a.property f.property⟩ :
            H.grading (q + p))).v n (n + (q + p)) (by omega)).hom x)
      ((p * (q + n)).negOnePow •
        (((i.hom.f q) f).v (n + p) (n + p + q) (by omega)).hom
          (⟨MulOpposite.op (a : A.A) • (x : M.M),
            M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ :
            M.grading (n + p))) := by
    have hact : (i.hom.f (q + p))
        (⟨(a : A.A) • (f : H.M), by
          simpa only [add_comm] using
            H.smul_mem p q (a : A.A) (f : H.M) a.property f.property⟩ : H.grading (q + p)) =
        (p * q).negOnePow •
          (t.action p a).comp ((i.hom.f q) f) (show p + q = q + p by omega) := by
      rw [← hi p q a f]
      exact t.homLeftAction_homAction N p q (q + p) rfl a _
    rw [hact]
    exact signedComp_apply_heq A M N t ht p q n a ((i.hom.f q) f) x
  exact HEq.trans (homComplex_apply_heq i.hom (show p + q = q + p by omega) (by omega)
    _ _ (gradedElement_heq H.grading (by omega) _ _ _) x _ _) key

end DifferentialGradedModule

namespace DifferentialGraded.LeftModule

open DifferentialGradedAlgebra

/-- A sign may be cancelled from both sides of an equation. -/
private theorem units_smul_left_cancel {X : Type*} [AddCommGroup X] (c : ℤˣ) {x y : X}
    (h : c • x = c • y) : x = y := by
  have h2 : c • c • x = c • c • y := congrArg (fun z => c • z) h
  rwa [smul_smul, smul_smul, Int.units_mul_self, one_smul, one_smul] at h2

/-- **Stacks 0FQ2.** For a left differential graded `A`-module `L` and a complex `N` of
`R`-modules, the Hom complex `Hom^•(L, N)` is a right differential graded `A`-module, acting by
precomposition with the left action of `L`, with no intervening sign. -/
theorem exists_homRightModule (A : DifferentialGradedAlgebra.{u, v} R)
    (L : DifferentialGraded.LeftModule A) (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (P : DifferentialGradedModule A)
      (i : P.toCochainComplex ≅ HomComplexR R (toCochainComplex A L) N),
      ∀ (p q : ℤ) (a : A.grading p) (g : P.grading q),
        (i.hom.f (q + p))
            (⟨MulOpposite.op (a : A.A) • (g : P.M),
              P.smul_mem q p (g : P.M) (a : A.A) g.property a.property⟩ : P.grading (q + p)) =
          ((leftAction A L (toCochainComplex A L) (Iso.refl _)).action p a).comp
            ((i.hom.f q) g) (by omega) := by
  classical
  let O := DifferentialGradedAlgebra.opposite R A
  let act := leftAction A L (toCochainComplex A L) (Iso.refl _)
  let tB := (DifferentialGradedAlgebra.Opposite.involution A O).rightAction act
  let sB := tB.homLeftAction N
  let fB := (O.toDifferentialGradedAlgebra.leftActionEquivHom
    (HomComplexR R (toCochainComplex A L) N)).val sB
  let τ : A.Hom (DifferentialGradedModule.oppEndAlgebra
      (HomComplexR R (toCochainComplex A L) N)) :=
    DifferentialGradedAlgebra.oppositeHom
      (DifferentialGradedAlgebra.Opposite.involution A O)
      (DifferentialGradedModule.oppEndOpposite (HomComplexR R (toCochainComplex A L) N)) fB
  obtain ⟨P, i, hτ⟩ := DifferentialGradedModule.exists_rightModule_isSignedAction A
    (HomComplexR R (toCochainComplex A L) N) τ
  refine ⟨P, i, ?_⟩
  intro p q a g
  let b : O.toDifferentialGradedAlgebra.grading p := (O.gradingEquiv p).symm a
  have hcochain : (CochainComplex.endomorphismDGA
        (HomComplexR R (toCochainComplex A L) N)).cochainEquiv p
      ⟨(DifferentialGradedModule.oppEndOpposite
          (HomComplexR R (toCochainComplex A L) N)).equiv (τ.toAlgebraHom (a : A.A)),
        ((DifferentialGradedModule.oppEndOpposite
          (HomComplexR R (toCochainComplex A L) N)).mem_grading_iff p _).mp
          (τ.map_grading p (a : A.A) a.property)⟩ = sB.action p b := by
    refine Eq.trans (congrArg _ (Subtype.ext ?_))
      ((O.toDifferentialGradedAlgebra.leftActionEquivHom _).property sB p b)
    show (DifferentialGradedModule.oppEndOpposite
        (HomComplexR R (toCochainComplex A L) N)).equiv
      ((DifferentialGradedModule.oppEndOpposite
        (HomComplexR R (toCochainComplex A L) N)).equiv.symm
        (fB.toAlgebraHom (O.equiv.symm (a : A.A)))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hba : ((DifferentialGradedAlgebra.Opposite.involution A O).gradingEquiv p).symm b = a := by
    refine Subtype.ext ?_
    show O.equiv.symm.symm (O.equiv.symm (a : A.A)) = (a : A.A)
    rw [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  have htb : tB.action p b = act.action p a := by
    rw [DifferentialGradedAlgebra.Opposite.rightAction_action, hba]
  have hfull : ((sB.action p b).v q (q + p) (by omega)).hom ((i.hom.f q) g) =
      (p * q).negOnePow • (act.action p a).comp ((i.hom.f q) g) (by omega) := by
    rw [← htb]
    exact tB.homLeftAction_homAction N p q (q + p) rfl b ((i.hom.f q) g)
  have key := hτ p q a g
  rw [hcochain] at key
  have key2 : (p * q).negOnePow • (act.action p a).comp ((i.hom.f q) g) (by omega) =
      (p * q).negOnePow • (i.hom.f (q + p))
        (⟨MulOpposite.op (a : A.A) • (g : P.M),
          P.smul_mem q p (g : P.M) (a : A.A) g.property a.property⟩ : P.grading (q + p)) :=
    hfull.symm.trans key
  exact (units_smul_left_cancel (p * q).negOnePow key2).symm

end DifferentialGraded.LeftModule

namespace DifferentialGradedModule

/-- Linear maps between the homogeneous pieces of two graded modules extend to a linear map of the
total modules. -/
private theorem exists_linearMap_of_graded {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (G : ℤ → Submodule R X) [DirectSum.Decomposition G]
    (H : ℤ → Submodule R Y) (φ : ∀ n, G n →ₗ[R] H n) :
    ∃ e : X →ₗ[R] Y, ∀ (n : ℤ) (x : G n) (y : H n), φ n x = y → e x = (y : Y) := by
  refine ⟨(DirectSum.toModule R ℤ Y fun n => (H n).subtype ∘ₗ φ n) ∘ₗ
    (DirectSum.decomposeLinearEquiv G).toLinearMap, fun n x y hy => ?_⟩
  show DirectSum.toModule R ℤ Y (fun n => (H n).subtype ∘ₗ φ n) (DirectSum.decompose G (x : X)) = _
  rw [DirectSum.decompose_of_mem G x.property,
    ← DirectSum.lof_eq_of (R := R) (ι := ℤ) (M := fun n => G n) n x, DirectSum.toModule_lof]
  exact congrArg Subtype.val hy

/-- The value, at a homogeneous element, of a composite of cochains. -/
private theorem comp_v_apply {K N : CochainComplex (ModuleCat.{u} R) ℤ} {p n pn : ℤ}
    (w : Cochain K K p) (z : Cochain K N n) (hpn : p + n = pn) (q r : ℤ) (hqr : q + pn = r)
    (f : K.X q) :
    (((w.comp z hpn).v q r hqr).hom f) =
      (z.v (q + p) r (by omega)).hom ((w.v q (q + p) rfl).hom f) := by
  rw [Cochain.comp_v _ _ hpn q (q + p) r rfl (by omega), ModuleCat.hom_comp,
    LinearMap.comp_apply]

/-- The value, at a homogeneous element, of a cochain precomposed with a morphism of complexes. -/
private theorem precomp_v_apply {K K' N : CochainComplex (ModuleCat.{u} R) ℤ} (g : K' ⟶ K)
    (n q r : ℤ) (h : q + n = r) (z : Cochain K N n) (f : K'.X q) :
    ((((Stacks.HomComplex.TensorHomMap.precomp R K' K N g).f n).hom z).v q r h).hom f =
      (z.v q r h).hom ((g.f q).hom f) := by
  rw [Stacks.HomComplex.TensorHomMap.precomp_f_apply, Cochain.zero_cochain_comp_v,
    ModuleCat.hom_comp, LinearMap.comp_apply, Cochain.ofHom_v]

/-- The value, at a homogeneous element, of the evaluation into the double Hom complex, read
through a map `g` into the inner Hom complex. -/
private theorem evaluation_precomp_v_apply {K K' N : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : K' ⟶ HomComplexR R K N) (n q r : ℤ) (h : q + n = r) (x : K.X n) (f : K'.X q) :
    (((((CochainComplex.HomComplex.evaluationToDoubleHom K N ≫
        Stacks.HomComplex.TensorHomMap.precomp R K' (HomComplexR R K N) N g).f n).hom x).v
      q r h).hom f) = (n * q).negOnePow • (((g.f q).hom f).v n r (by omega)).hom x := by
  refine Eq.trans (precomp_v_apply g n q r h
    (((CochainComplex.HomComplex.evaluationToDoubleHom K N).f n) x) f) ?_
  obtain rfl : r = q + n := by omega
  exact (CochainComplex.HomComplex.evaluationToDoubleHom_apply).1 K N n q x ((g.f q).hom f)

/-- A morphism of complexes compatible with the right actions on homogeneous elements extends to a
homomorphism of right differential graded modules. -/
theorem exists_hom_of_cochainMap (A : DifferentialGradedAlgebra.{u, v} R)
    (M P : DifferentialGradedModule A) (c : M.toCochainComplex ⟶ P.toCochainComplex)
    (hc : ∀ (p n : ℤ) (a : A.grading p) (x : M.grading n) (y : P.grading n),
      (c.f n) x = y →
        (c.f (n + p))
            (⟨MulOpposite.op (a : A.A) • (x : M.M),
              M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ : M.grading (n + p)) =
          (⟨MulOpposite.op (a : A.A) • (y : P.M),
            P.smul_mem n p (y : P.M) (a : A.A) y.property a.property⟩ : P.grading (n + p))) :
    ∃ f : DifferentialGradedModule.Hom M P,
      ∀ (n : ℤ) (x : M.grading n),
        (⟨f.toFun x, f.map_grading n x x.property⟩ : P.grading n) = (c.f n) x := by
  classical
  obtain ⟨e, he⟩ := exists_linearMap_of_graded M.grading P.grading fun n => (c.f n).hom
  have hgrade (n : ℤ) (x : M.M) (hx : x ∈ M.grading n) : e x ∈ P.grading n := by
    rw [he n ⟨x, hx⟩ _ rfl]
    exact SetLike.coe_mem _
  have hsmul (x : M.M) (a : A.A) : e (MulOpposite.op a • x) = MulOpposite.op a • e x := by
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | add a b ha hb => simp [add_smul, map_add, ha, hb]
    | @homogeneous p a =>
      induction x using DirectSum.Decomposition.inductionOn M.grading with
      | zero => simp
      | add x y hx hy => simp [smul_add, map_add, hx, hy]
      | @homogeneous n x =>
        rw [he (n + p) ⟨_, M.smul_mem n p x a x.property a.property⟩ _ rfl, he n x _ rfl]
        exact congrArg Subtype.val (hc p n a x ((c.f n) x) rfl)
  have hd : e ∘ₗ M.d = P.d ∘ₗ e := by
    ext x
    show e (M.d x) = P.d (e x)
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | @homogeneous n x =>
      rw [he (n + 1) ⟨_, M.d_mem n x x.property⟩ _ rfl, he n x _ rfl]
      have hh := congrArg (fun k => (k : M.toCochainComplex.X n ⟶
          P.toCochainComplex.X (n + 1)).hom x) (c.comm n (n + 1))
      have hh' := (congrArg Subtype.val hh).symm
      simp only [toCochainComplex_d, gradedDifferential] at hh'
      exact hh'
  exact ⟨⟨e, hsmul, hgrade, hd⟩, fun n x => Subtype.ext (he n x _ rfl)⟩

/-- The two Hom modules attached to a right differential graded module `M` and a complex `N`,
their canonical actions, and the evaluation homomorphism `M ⟶ Hom(Hom(M, N), N)`.

This is the **right-handed** orientation, the one of Tag 0FQ8: the module `M` it is attached to is
a *right* differential graded `A`-module, `Hom(M, N)` is a *left* one (`leftHom`),
`Hom(Hom(M, N), N)` is a *right* one (`doubleHom`), and `evaluation` is a homomorphism of *right*
differential graded `A`-modules. For the left-handed orientation of Tag 0FQ7 — a left module in,
a right `Hom`, a left double `Hom`, and an evaluation of left modules — see the structure of the
same name in the `DifferentialGraded.LeftModule` namespace. -/
structure HomEvaluationData (A : DifferentialGradedAlgebra.{u, v} R)
    (M : DifferentialGradedModule A) (N : CochainComplex (ModuleCat.{u} R) ℤ) where
  /-- The left differential graded module `Hom(M, N)`. -/
  leftHom : DifferentialGraded.LeftModule A
  /-- Its underlying complex is the Hom complex `Hom^•(M, N)`. -/
  leftHomIso : DifferentialGraded.LeftModule.toCochainComplex A leftHom ≅
    HomComplexR R M.toCochainComplex N
  /-- The right differential graded module `Hom(Hom(M, N), N)`. -/
  doubleHom : DifferentialGradedModule A
  /-- Its underlying complex is the Hom complex `Hom^•(Hom^•(M, N), N)`. -/
  doubleHomIso : doubleHom.toCochainComplex ≅
    HomComplexR R (DifferentialGraded.LeftModule.toCochainComplex A leftHom) N
  /-- The evaluation homomorphism. -/
  evaluation : DifferentialGradedModule.Hom M doubleHom
  /-- The action on `Hom(M, N)` is signed precomposition with the right action of `M`. -/
  leftHom_action (p q n : ℤ) (a : A.grading p) (f : leftHom.grading q) (x : M.grading n) :
    HEq
      ((((leftHomIso.hom.f (p + q))
          (⟨(a : A.A) • (f : leftHom.M),
            leftHom.smul_mem p q (a : A.A) (f : leftHom.M) a.property f.property⟩ :
            leftHom.grading (p + q))).v n (n + (p + q)) (by omega)).hom x)
      ((p * (q + n)).negOnePow •
        (((leftHomIso.hom.f q) f).v (n + p) (n + p + q) (by omega)).hom
          (⟨MulOpposite.op (a : A.A) • (x : M.M),
            M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ : M.grading (n + p)))
  /-- The action on `Hom(Hom(M, N), N)` is precomposition with the left action of `Hom(M, N)`. -/
  doubleHom_action (p q : ℤ) (a : A.grading p) (g : doubleHom.grading q) :
    (doubleHomIso.hom.f (q + p))
        (⟨MulOpposite.op (a : A.A) • (g : doubleHom.M),
          doubleHom.smul_mem q p (g : doubleHom.M) (a : A.A) g.property a.property⟩ :
          doubleHom.grading (q + p)) =
      ((DifferentialGraded.LeftModule.leftAction A leftHom
        (DifferentialGraded.LeftModule.toCochainComplex A leftHom) (Iso.refl _)).action p a).comp
        ((doubleHomIso.hom.f q) g) (by omega)
  /-- Evaluation is the canonical signed evaluation of Tag 0FNM. -/
  evaluation_apply (n q : ℤ) (x : M.grading n) (f : leftHom.grading q) :
    HEq
      ((((doubleHomIso.hom.f n)
          (⟨evaluation.toFun x, evaluation.map_grading n x x.property⟩ :
            doubleHom.grading n)).v q (q + n) (by omega)).hom f)
      ((n * q).negOnePow • (((leftHomIso.hom.f q) f).v n (n + q) (by omega)).hom x)

/-- **Stacks 0FQ8.** For a right differential graded `A`-module `M` and a complex `N` of
`R`-modules, the Hom complex `Hom^•(M, N)` carries a left differential graded `A`-module structure,
its Hom complex into `N` carries a right one, and the canonical evaluation map of Tag 0FNM is a
homomorphism of right differential graded `A`-modules. -/
@[stacks 0FQ8 "the RIGHT-handed remark: `M` is a RIGHT differential graded `A`-module,
`Hom(M, N)` is a LEFT one (`leftHom`), `Hom(Hom(M, N), N)` is a RIGHT one (`doubleHom`), and
`ev` is a map of RIGHT differential graded `A`-modules — its type is
`DifferentialGradedModule.Hom M doubleHom`. The data are asserted to exist rather than named,
the Hom modules having no canonical presentation; `evaluation_apply` pins `ev` to 0FNM."]
theorem nonempty_homEvaluationData (A : DifferentialGradedAlgebra.{u, v} R)
    (M : DifferentialGradedModule A) (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    Nonempty (HomEvaluationData A M N) := by
  classical
  obtain ⟨Hm, hIso, hHact⟩ := exists_homLeftModule A M N
  obtain ⟨P, i, hi⟩ := DifferentialGraded.LeftModule.exists_homRightModule A Hm N
  let H := DifferentialGraded.LeftModule.toCochainComplex A Hm
  let act := DifferentialGraded.LeftModule.leftAction A Hm H (Iso.refl _)
  let e : M.toCochainComplex ⟶ HomComplexR R H N :=
    CochainComplex.HomComplex.evaluationToDoubleHom M.toCochainComplex N ≫
      Stacks.HomComplex.TensorHomMap.precomp R H (HomComplexR R M.toCochainComplex N) N hIso.hom
  have he : ∀ (n q r : ℤ) (h : q + n = r) (x : M.grading n) (f : Hm.grading q),
      (((e.f n) x).v q r h).hom f =
        (n * q).negOnePow • (((hIso.hom.f q) f).v n r (by omega)).hom x :=
    fun n q r h x f => evaluation_precomp_v_apply hIso.hom n q r h x f
  let c : M.toCochainComplex ⟶ P.toCochainComplex := e ≫ i.inv
  have hci : c ≫ i.hom = e := by
    show (e ≫ i.inv) ≫ i.hom = e
    rw [Category.assoc, i.inv_hom_id, Category.comp_id]
  have hec : ∀ (n : ℤ) (x : M.grading n),
      ((i.hom.f n) ((c.f n) x) : Cochain H N n) = (e.f n) x :=
    fun n x => congrArg (fun k : M.toCochainComplex ⟶ HomComplexR R H N => (k.f n) x) hci
  have hecApply : ∀ (n q r : ℤ) (h : q + n = r) (x : M.grading n) (f : Hm.grading q),
      ((((i.hom.f n) ((c.f n) x)).v q r h).hom f) =
        (n * q).negOnePow • (((hIso.hom.f q) f).v n r (by omega)).hom x := by
    intro n q r h x f
    exact (congrArg (fun z : Cochain H N n => ((z.v q r h).hom f)) (hec n x)).trans
      (he n q r h x f)
  have hc : ∀ (p n : ℤ) (a : A.grading p) (x : M.grading n) (y : P.grading n),
      (c.f n) x = y →
        (c.f (n + p))
            (⟨MulOpposite.op (a : A.A) • (x : M.M),
              M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ : M.grading (n + p)) =
          (⟨MulOpposite.op (a : A.A) • (y : P.M),
            P.smul_mem n p (y : P.M) (a : A.A) y.property a.property⟩ : P.grading (n + p)) := by
    intro p n a x y hy
    refine (ConcreteCategory.bijective_of_isIso (i.hom.f (n + p))).injective ?_
    have hmain : ((e.f (n + p))
          (⟨MulOpposite.op (a : A.A) • (x : M.M),
            M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ : M.grading (n + p)) :
          Cochain H N (n + p)) =
        (act.action p a).comp ((e.f n) x) (show p + n = n + p by omega) := by
      refine Cochain.ext _ _ fun q r hqr =>
        ModuleCat.hom_ext (LinearMap.ext fun (f : Hm.grading q) => ?_)
      have hL : (((e.f (n + p))
          (⟨MulOpposite.op (a : A.A) • (x : M.M),
            M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ :
            M.grading (n + p))).v q r hqr).hom f =
          ((n + p) * q).negOnePow •
            (((hIso.hom.f q) f).v (n + p) r (by omega)).hom
              (⟨MulOpposite.op (a : A.A) • (x : M.M),
                M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ :
                M.grading (n + p)) :=
        he (n + p) q r hqr _ f
      have hact : ((act.action p a).v q (q + p) rfl).hom f =
          (⟨(a : A.A) • (f : Hm.M), by
            simpa only [add_comm] using
              Hm.smul_mem p q (a : A.A) (f : Hm.M) a.property f.property⟩ :
            Hm.grading (q + p)) :=
        DifferentialGraded.LeftModule.leftAction_apply A Hm H (Iso.refl _) p q a f
      have hR : (((act.action p a).comp ((e.f n) x)
            (show p + n = n + p by omega)).v q r hqr).hom f =
          (n * (q + p)).negOnePow •
            (((hIso.hom.f (q + p))
              (⟨(a : A.A) • (f : Hm.M), by
                simpa only [add_comm] using
                  Hm.smul_mem p q (a : A.A) (f : Hm.M) a.property f.property⟩ :
                Hm.grading (q + p))).v n r (by omega)).hom x := by
        refine Eq.trans (comp_v_apply (act.action p a) ((e.f n) x)
          (show p + n = n + p by omega) q r hqr f) ?_
        rw [hact]
        exact he n (q + p) r (by omega) x _
      have hV : (((hIso.hom.f (q + p))
            (⟨(a : A.A) • (f : Hm.M), by
              simpa only [add_comm] using
                Hm.smul_mem p q (a : A.A) (f : Hm.M) a.property f.property⟩ :
              Hm.grading (q + p))).v n r (by omega)).hom x =
          (p * (q + n)).negOnePow •
            (((hIso.hom.f q) f).v (n + p) r (by omega)).hom
              (⟨MulOpposite.op (a : A.A) • (x : M.M),
                M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ :
                M.grading (n + p)) := by
        refine eq_of_heq ((homComplex_apply_heq hIso.hom (show q + p = p + q by omega)
          (show r = n + (p + q) by omega) _ _
          (gradedElement_heq Hm.grading (show q + p = p + q by omega) _ _ _) x _ _).trans
          ((hHact p q n a f x).trans ?_))
        exact signed_cochain_apply_heq (K := M.toCochainComplex) ((hIso.hom.f q) f)
          (by omega) (by omega) (p * (q + n)).negOnePow _
      have hsign : ((n + p) * q).negOnePow = (n * (q + p) + p * (q + n)).negOnePow := by
        rw [show n * (q + p) + p * (q + n) = (n + p) * q + 2 * (n * p) by ring,
          Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
      rw [hL, hR, hV, smul_smul, ← Int.negOnePow_add, hsign]
    refine (((hec (n + p) _).trans hmain).trans ?_)
    refine Eq.trans ?_ (hi p n a y).symm
    refine congrArg (fun z : Cochain H N n => (act.action p a).comp z
      (show p + n = n + p by omega)) ?_
    exact (hec n x).symm.trans (congrArg (fun w : P.grading n => (i.hom.f n) w) hy)
  obtain ⟨ev, hev⟩ := exists_hom_of_cochainMap A M P c hc
  refine ⟨{
    leftHom := Hm
    leftHomIso := hIso
    doubleHom := P
    doubleHomIso := i
    evaluation := ev
    leftHom_action := hHact
    doubleHom_action := hi
    evaluation_apply := ?_ }⟩
  intro n q x f
  refine HEq.trans (heq_of_eq ?_) (signed_cochain_apply_heq (K := M.toCochainComplex)
    ((hIso.hom.f q) f) (by omega) (by omega) (n * q).negOnePow x)
  refine Eq.trans (congrArg (fun y : P.grading n =>
    (((i.hom.f n) y).v q (q + n) (by omega)).hom f) (hev n x)) ?_
  exact hecApply n q (q + n) (by omega) x f

end DifferentialGradedModule

namespace DifferentialGraded.LeftModule

open DifferentialGradedAlgebra DifferentialGradedModule

/-- The value of a cochain at a homogeneous element does not depend on which expression for the
source degree is used. -/
private theorem cochain_v_source_congr {K N : CochainComplex (ModuleCat.{u} R) ℤ} {q : ℤ}
    (z : Cochain K N q) {s s' t : ℤ} (hs : s = s') (x : K.X s) (x' : K.X s') (hx : HEq x x')
    (h : s + q = t) (h' : s' + q = t) :
    (z.v s t h).hom x = (z.v s' t h').hom x' := by
  subst hs; cases hx; rfl

/-- A morphism of complexes compatible with the left actions on homogeneous elements extends to a
homomorphism of left differential graded modules. -/
theorem exists_hom_of_cochainMap (A : DifferentialGradedAlgebra.{u, v} R)
    (L D : DifferentialGraded.LeftModule A)
    (c : toCochainComplex A L ⟶ toCochainComplex A D)
    (hc : ∀ (p n : ℤ) (a : A.grading p) (x : L.grading n) (y : D.grading n),
      (c.f n) x = y →
        (c.f (p + n))
            (⟨(a : A.A) • (x : L.M),
              L.smul_mem p n (a : A.A) (x : L.M) a.property x.property⟩ : L.grading (p + n)) =
          (⟨(a : A.A) • (y : D.M),
            D.smul_mem p n (a : A.A) (y : D.M) a.property y.property⟩ : D.grading (p + n))) :
    ∃ f : DifferentialGraded.LeftModule.Hom L D,
      ∀ (n : ℤ) (x : L.grading n),
        (⟨f.toFun x, f.map_grading n x x.property⟩ : D.grading n) = (c.f n) x := by
  classical
  obtain ⟨e, he⟩ := exists_linearMap_of_graded L.grading D.grading fun n => (c.f n).hom
  have hgrade (n : ℤ) (x : L.M) (hx : x ∈ L.grading n) : e x ∈ D.grading n := by
    rw [he n ⟨x, hx⟩ _ rfl]
    exact SetLike.coe_mem _
  have hsmul (a : A.A) (x : L.M) : e (a • x) = a • e x := by
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | add a b ha hb => simp [add_smul, map_add, ha, hb]
    | @homogeneous p a =>
      induction x using DirectSum.Decomposition.inductionOn L.grading with
      | zero => simp
      | add x y hx hy => simp [smul_add, map_add, hx, hy]
      | @homogeneous n x =>
        rw [he (p + n) ⟨_, L.smul_mem p n a x a.property x.property⟩ _ rfl, he n x _ rfl]
        exact congrArg Subtype.val (hc p n a x ((c.f n) x) rfl)
  have hd : e ∘ₗ L.d = D.d ∘ₗ e := by
    ext x
    show e (L.d x) = D.d (e x)
    induction x using DirectSum.Decomposition.inductionOn L.grading with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | @homogeneous n x =>
      rw [he (n + 1) ⟨_, L.d_mem n x x.property⟩ _ rfl, he n x _ rfl]
      have hh := congrArg (fun k => (k : (toCochainComplex A L).X n ⟶
          (toCochainComplex A D).X (n + 1)).hom x) (c.comm n (n + 1))
      have hh' := (congrArg Subtype.val hh).symm
      simp only [toCochainComplex, CochainComplex.of_d, gradedDifferential] at hh'
      exact hh'
  exact ⟨⟨e, hsmul, hgrade, hd⟩, fun n x => Subtype.ext (he n x _ rfl)⟩

/-- The two Hom modules attached to a left differential graded module `L` and a complex `N`, their
canonical actions, and the evaluation homomorphism `L ⟶ Hom(Hom(L, N), N)`.

This is the **left-handed** orientation, the one of Tag 0FQ7: the module `L` it is attached to is
a *left* differential graded `A`-module, `Hom(L, N)` is a *right* one (`rightHom`),
`Hom(Hom(L, N), N)` is a *left* one (`doubleHom`), and `evaluation`, of type
`DifferentialGraded.LeftModule.Hom L doubleHom`, is a homomorphism of *left* differential graded
`A`-modules. For the right-handed orientation of Tag 0FQ8 — a right module in, a left `Hom`, a
right double `Hom`, and an evaluation of right modules — see the structure of the same name in
the `DifferentialGradedModule` namespace. -/
structure HomEvaluationData (A : DifferentialGradedAlgebra.{u, v} R)
    (L : DifferentialGraded.LeftModule A) (N : CochainComplex (ModuleCat.{u} R) ℤ) where
  /-- The right differential graded module `Hom(L, N)`. -/
  rightHom : DifferentialGradedModule A
  /-- Its underlying complex is the Hom complex `Hom^•(L, N)`. -/
  rightHomIso : rightHom.toCochainComplex ≅ HomComplexR R (toCochainComplex A L) N
  /-- The left differential graded module `Hom(Hom(L, N), N)`. -/
  doubleHom : DifferentialGraded.LeftModule A
  /-- Its underlying complex is the Hom complex `Hom^•(Hom^•(L, N), N)`. -/
  doubleHomIso : toCochainComplex A doubleHom ≅ HomComplexR R rightHom.toCochainComplex N
  /-- The evaluation homomorphism. -/
  evaluation : DifferentialGraded.LeftModule.Hom L doubleHom
  /-- The action on `Hom(L, N)` is precomposition with the left action of `L`. -/
  rightHom_action (p q : ℤ) (a : A.grading p) (f : rightHom.grading q) :
    (rightHomIso.hom.f (q + p))
        (⟨MulOpposite.op (a : A.A) • (f : rightHom.M),
          rightHom.smul_mem q p (f : rightHom.M) (a : A.A) f.property a.property⟩ :
          rightHom.grading (q + p)) =
      ((leftAction A L (toCochainComplex A L) (Iso.refl _)).action p a).comp
        ((rightHomIso.hom.f q) f) (by omega)
  /-- The action on `Hom(Hom(L, N), N)` is signed precomposition with the right action of
  `Hom(L, N)`. -/
  doubleHom_action (p q r : ℤ) (a : A.grading p) (g : doubleHom.grading r)
      (f : rightHom.grading q) :
    HEq
      ((((doubleHomIso.hom.f (p + r))
          (⟨(a : A.A) • (g : doubleHom.M),
            doubleHom.smul_mem p r (a : A.A) (g : doubleHom.M) a.property g.property⟩ :
            doubleHom.grading (p + r))).v q (q + (p + r)) (by omega)).hom f)
      ((p * (q + r)).negOnePow •
        (((doubleHomIso.hom.f r) g).v (q + p) (q + p + r) (by omega)).hom
          (⟨MulOpposite.op (a : A.A) • (f : rightHom.M),
            rightHom.smul_mem q p (f : rightHom.M) (a : A.A) f.property a.property⟩ :
            rightHom.grading (q + p)))
  /-- Evaluation is the canonical signed evaluation of Tag 0FNM. -/
  evaluation_apply (n q : ℤ) (x : L.grading n) (f : rightHom.grading q) :
    HEq
      ((((doubleHomIso.hom.f n)
          (⟨evaluation.toFun x, evaluation.map_grading n x x.property⟩ :
            doubleHom.grading n)).v q (q + n) (by omega)).hom f)
      ((n * q).negOnePow • (((rightHomIso.hom.f q) f).v n (n + q) (by omega)).hom x)

/-- **Stacks 0FQ7.** Let `A` be a differential graded `R`-algebra, `L` a left differential graded
`A`-module and `N` a complex of `R`-modules. Then there are a right differential graded
`A`-module `rightHom` with underlying complex `Hom^•(L, N)`, acting by precomposition with the
left action of `L`; a left differential graded `A`-module `doubleHom` with underlying complex
`Hom^•(Hom^•(L, N), N)`, acting by signed precomposition with the right action of `rightHom`; and
an evaluation map

`ev : L ⟶ doubleHom`

in the category of left differential graded `A`-modules, so in particular `ev (a • x) = a • ev x`
for every `a ∈ A`; on underlying complexes of `R`-modules `ev` is the evaluation map of
Tag 0FNM, read through the two identifications. -/
@[stacks 0FQ7 "the LEFT-handed remark: `M` is a LEFT differential graded `A`-module (called `L`
here), `Hom(M, N)` is a RIGHT one (`rightHom`), `Hom(Hom(M, N), N)` is a LEFT one (`doubleHom`),
and `ev` is a map of LEFT differential graded `A`-modules — its type is
`DifferentialGraded.LeftModule.Hom L doubleHom`, whose `A`-linearity the third conjunct spells
out. The modules are asserted to exist rather than named, having no canonical presentation, so
each comes with an isomorphism of its underlying complex with the relevant Hom complex and with
the formula for its action; the last conjunct identifies `ev` on underlying complexes with
`CochainComplex.HomComplex.evaluationToDoubleHom`, which is 0FNM."]
theorem exists_homEvaluation (A : DifferentialGradedAlgebra.{u, v} R)
    (L : DifferentialGraded.LeftModule A) (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (rightHom : DifferentialGradedModule A)
      (rightHomIso : rightHom.toCochainComplex ≅ HomComplexR R (toCochainComplex A L) N)
      (doubleHom : DifferentialGraded.LeftModule A)
      (doubleHomIso : toCochainComplex A doubleHom ≅ HomComplexR R rightHom.toCochainComplex N)
      (ev : DifferentialGraded.LeftModule.Hom L doubleHom),
      (∀ (p q : ℤ) (a : A.grading p) (f : rightHom.grading q),
        (rightHomIso.hom.f (q + p))
            (⟨MulOpposite.op (a : A.A) • (f : rightHom.M),
              rightHom.smul_mem q p (f : rightHom.M) (a : A.A) f.property a.property⟩ :
              rightHom.grading (q + p)) =
          ((leftAction A L (toCochainComplex A L) (Iso.refl _)).action p a).comp
            ((rightHomIso.hom.f q) f) (by omega)) ∧
      (∀ (p q r : ℤ) (a : A.grading p) (g : doubleHom.grading r) (f : rightHom.grading q),
        HEq
          ((((doubleHomIso.hom.f (p + r))
              (⟨(a : A.A) • (g : doubleHom.M),
                doubleHom.smul_mem p r (a : A.A) (g : doubleHom.M) a.property g.property⟩ :
                doubleHom.grading (p + r))).v q (q + (p + r)) (by omega)).hom f)
          ((p * (q + r)).negOnePow •
            (((doubleHomIso.hom.f r) g).v (q + p) (q + p + r) (by omega)).hom
              (⟨MulOpposite.op (a : A.A) • (f : rightHom.M),
                rightHom.smul_mem q p (f : rightHom.M) (a : A.A) f.property a.property⟩ :
                rightHom.grading (q + p)))) ∧
      (∀ (a : A.A) (x : L.M), ev.toFun (a • x) = a • ev.toFun x) ∧
      (∀ (n : ℤ) (x : L.grading n),
        (doubleHomIso.hom.f n)
            (⟨ev.toFun x, ev.map_grading n x x.property⟩ : doubleHom.grading n) =
          ((CochainComplex.HomComplex.evaluationToDoubleHom (toCochainComplex A L) N ≫
              Stacks.HomComplex.TensorHomMap.precomp R rightHom.toCochainComplex
                (HomComplexR R (toCochainComplex A L) N) N rightHomIso.hom).f n) x) := by
  classical
  obtain ⟨RH, hR, hRact⟩ := exists_homRightModule A L N
  obtain ⟨DH, hD, hDact⟩ := DifferentialGradedModule.exists_homLeftModule A RH N
  let X := toCochainComplex A L
  let act := leftAction A L X (Iso.refl _)
  let e : X ⟶ HomComplexR R RH.toCochainComplex N :=
    CochainComplex.HomComplex.evaluationToDoubleHom X N ≫
      Stacks.HomComplex.TensorHomMap.precomp R RH.toCochainComplex (HomComplexR R X N) N hR.hom
  have he : ∀ (n q r : ℤ) (h : q + n = r) (x : L.grading n) (f : RH.grading q),
      (((e.f n) x).v q r h).hom f =
        (n * q).negOnePow • (((hR.hom.f q) f).v n r (by omega)).hom x :=
    fun n q r h x f => evaluation_precomp_v_apply hR.hom n q r h x f
  let c : X ⟶ toCochainComplex A DH := e ≫ hD.inv
  have hci : c ≫ hD.hom = e := by
    show (e ≫ hD.inv) ≫ hD.hom = e
    rw [Category.assoc, hD.inv_hom_id, Category.comp_id]
  have hec : ∀ (n : ℤ) (x : L.grading n),
      ((hD.hom.f n) ((c.f n) x) : Cochain RH.toCochainComplex N n) = (e.f n) x :=
    fun n x => congrArg (fun k : X ⟶ HomComplexR R RH.toCochainComplex N => (k.f n) x) hci
  have hecApply : ∀ (n q r : ℤ) (h : q + n = r) (x : L.grading n) (f : RH.grading q),
      ((((hD.hom.f n) ((c.f n) x)).v q r h).hom f) =
        (n * q).negOnePow • (((hR.hom.f q) f).v n r (by omega)).hom x := by
    intro n q r h x f
    exact (congrArg (fun z : Cochain RH.toCochainComplex N n => ((z.v q r h).hom f))
      (hec n x)).trans (he n q r h x f)
  have hc : ∀ (p n : ℤ) (a : A.grading p) (x : L.grading n) (y : DH.grading n),
      (c.f n) x = y →
        (c.f (p + n))
            (⟨(a : A.A) • (x : L.M),
              L.smul_mem p n (a : A.A) (x : L.M) a.property x.property⟩ : L.grading (p + n)) =
          (⟨(a : A.A) • (y : DH.M),
            DH.smul_mem p n (a : A.A) (y : DH.M) a.property y.property⟩ :
            DH.grading (p + n)) := by
    intro p n a x y hy
    refine (ConcreteCategory.bijective_of_isIso (hD.hom.f (p + n))).injective ?_
    refine Cochain.ext _ _ fun q r hqr =>
      ModuleCat.hom_ext (LinearMap.ext fun (f : RH.grading q) => ?_)
    obtain rfl : r = q + (p + n) := by omega
    have hDy : ((hD.hom.f n) y : Cochain RH.toCochainComplex N n) = (e.f n) x :=
      (congrArg (fun w : DH.grading n => (hD.hom.f n) w) hy.symm).trans (hec n x)
    have hL : (((hD.hom.f (p + n)) ((c.f (p + n))
          (⟨(a : A.A) • (x : L.M),
            L.smul_mem p n (a : A.A) (x : L.M) a.property x.property⟩ :
            L.grading (p + n)))).v q (q + (p + n)) hqr).hom f =
        ((p + n) * q).negOnePow •
          (((hR.hom.f q) f).v (p + n) (q + (p + n)) (by omega)).hom
            (⟨(a : A.A) • (x : L.M),
              L.smul_mem p n (a : A.A) (x : L.M) a.property x.property⟩ :
              L.grading (p + n)) :=
      hecApply (p + n) q (q + (p + n)) hqr _ f
    have hsrc : (((hR.hom.f q) f).v (p + n) (q + (p + n)) (by omega)).hom
          (⟨(a : A.A) • (x : L.M),
            L.smul_mem p n (a : A.A) (x : L.M) a.property x.property⟩ : L.grading (p + n)) =
        (((hR.hom.f q) f).v (n + p) (q + (p + n)) (by omega)).hom
          (⟨(a : A.A) • (x : L.M), by
            simpa only [add_comm] using
              L.smul_mem p n (a : A.A) (x : L.M) a.property x.property⟩ : L.grading (n + p)) :=
      cochain_v_source_congr ((hR.hom.f q) f) (add_comm p n) _ _
        (gradedElement_heq L.grading (add_comm p n) _ _ _) _ _
    have hRA : (((hR.hom.f (q + p))
          (⟨MulOpposite.op (a : A.A) • (f : RH.M),
            RH.smul_mem q p (f : RH.M) (a : A.A) f.property a.property⟩ :
            RH.grading (q + p))).v n (q + (p + n)) (by omega)).hom x =
        (((hR.hom.f q) f).v (n + p) (q + (p + n)) (by omega)).hom
          (⟨(a : A.A) • (x : L.M), by
            simpa only [add_comm] using
              L.smul_mem p n (a : A.A) (x : L.M) a.property x.property⟩ : L.grading (n + p)) := by
      refine Eq.trans (congrArg (fun z : Cochain X N (q + p) =>
        ((z.v n (q + (p + n)) (by omega)).hom x)) (hRact p q a f)) ?_
      refine Eq.trans (comp_v_apply (act.action p a) ((hR.hom.f q) f)
        (show p + q = q + p by omega) n (q + (p + n)) (by omega) x) ?_
      exact congrArg (fun w : L.grading (n + p) =>
        (((hR.hom.f q) f).v (n + p) (q + (p + n)) (by omega)).hom w)
        (leftAction_apply A L X (Iso.refl _) p n a x)
    have hRHS : (((hD.hom.f (p + n))
          (⟨(a : A.A) • (y : DH.M),
            DH.smul_mem p n (a : A.A) (y : DH.M) a.property y.property⟩ :
            DH.grading (p + n))).v q (q + (p + n)) hqr).hom f =
        (p * (n + q)).negOnePow •
          (((hD.hom.f n) y).v (q + p) (q + (p + n)) (by omega)).hom
            (⟨MulOpposite.op (a : A.A) • (f : RH.M),
              RH.smul_mem q p (f : RH.M) (a : A.A) f.property a.property⟩ :
              RH.grading (q + p)) :=
      eq_of_heq ((hDact p n q a y f).trans
        (signed_cochain_apply_heq (K := RH.toCochainComplex) ((hD.hom.f n) y) (by omega)
          (by omega) (p * (n + q)).negOnePow _))
    have hinner : (((hD.hom.f n) y).v (q + p) (q + (p + n)) (by omega)).hom
          (⟨MulOpposite.op (a : A.A) • (f : RH.M),
            RH.smul_mem q p (f : RH.M) (a : A.A) f.property a.property⟩ :
            RH.grading (q + p)) =
        (n * (q + p)).negOnePow •
          (((hR.hom.f (q + p))
            (⟨MulOpposite.op (a : A.A) • (f : RH.M),
              RH.smul_mem q p (f : RH.M) (a : A.A) f.property a.property⟩ :
              RH.grading (q + p))).v n (q + (p + n)) (by omega)).hom x :=
      (congrArg (fun z : Cochain RH.toCochainComplex N n =>
        ((z.v (q + p) (q + (p + n)) (by omega)).hom
          (⟨MulOpposite.op (a : A.A) • (f : RH.M),
            RH.smul_mem q p (f : RH.M) (a : A.A) f.property a.property⟩ :
            RH.grading (q + p)))) hDy).trans
        (he n (q + p) (q + (p + n)) (by omega) x _)
    have hsign : ((p + n) * q).negOnePow = (p * (n + q) + n * (q + p)).negOnePow := by
      rw [show p * (n + q) + n * (q + p) = (p + n) * q + 2 * (n * p) by ring,
        Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
    rw [hL, hRHS, hinner, hRA, hsrc, smul_smul, ← Int.negOnePow_add, hsign]
  obtain ⟨ev, hev⟩ := exists_hom_of_cochainMap A L DH c hc
  refine ⟨RH, hR, DH, hD, ev, hRact, ?_, ev.map_smul, ?_⟩
  · intro p q r a g f
    rw [show p * (q + r) = p * (r + q) by ring]
    exact hDact p r q a g f
  · intro n x
    exact (congrArg (fun w : DH.grading n => (hD.hom.f n) w) (hev n x)).trans (hec n x)

/-- The data of Tag 0FQ7, packaged as a `HomEvaluationData` for consumers. It is derived from
`exists_homEvaluation`, the sign formula on homogeneous elements coming from the identification
of `ev` there with the evaluation morphism of Tag 0FNM: the explicit statement implies this one,
and the packaging adds nothing to it. -/
theorem nonempty_homEvaluationData (A : DifferentialGradedAlgebra.{u, v} R)
    (L : DifferentialGraded.LeftModule A) (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    Nonempty (HomEvaluationData A L N) := by
  obtain ⟨RH, hR, DH, hD, ev, hRact, hDact, -, hev⟩ := exists_homEvaluation A L N
  refine ⟨{
    rightHom := RH
    rightHomIso := hR
    doubleHom := DH
    doubleHomIso := hD
    evaluation := ev
    rightHom_action := hRact
    doubleHom_action := hDact
    evaluation_apply := ?_ }⟩
  intro n q x f
  refine HEq.trans (heq_of_eq ?_) (signed_cochain_apply_heq (K := toCochainComplex A L)
    ((hR.hom.f q) f) (by omega) (by omega) (n * q).negOnePow x)
  refine Eq.trans (congrArg (fun z : Cochain RH.toCochainComplex N n =>
    ((z.v q (q + n) (by omega)).hom f)) (hev n x)) ?_
  exact evaluation_precomp_v_apply hR.hom n q (q + n) (by omega) x f

end DifferentialGraded.LeftModule
