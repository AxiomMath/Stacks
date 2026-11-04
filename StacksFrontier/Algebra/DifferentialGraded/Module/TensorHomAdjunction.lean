module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.HomEvaluation
public import StacksFrontier.Algebra.DifferentialGraded.Module.BalancedTensor

/-!
# The tensor-hom adjunctions for differential graded modules

Let `R` be a commutative ring, `(A, d)` a differential graded `R`-algebra and `N` a complex of
`R`-modules. For a left differential graded `A`-module `M` the Hom complex `Hom(M, N)` is a right
differential graded `A`-module, and homomorphisms of right differential graded `A`-modules
`M' → Hom(M, N)` are the maps of complexes `M' ⊗_A M → N`. Exchanging the two variances, for a
right differential graded `A`-module `M` the Hom complex `Hom(M, N)` is a left differential graded
`A`-module, and homomorphisms of left differential graded `A`-modules `M' → Hom(M, N)` are the maps
of complexes `M ⊗_A M' → N`; here the identification carries the Koszul sign `(-1)^{pq}` coming
from the commutativity constraint.

## Main definitions

* `DifferentialGraded.rightHomBalancedEquiv`, `DifferentialGraded.leftHomBalancedEquiv`: the two
  identifications of homomorphisms into a Hom module with balanced bilinear maps.
* `DifferentialGraded.rightTensorHomEquiv`, `DifferentialGraded.leftTensorHomEquiv`: the two
  tensor-hom adjunction bijections.

## Main results

* `DifferentialGraded.rightTensorHomEquiv_apply`,
  `DifferentialGraded.leftTensorHomEquiv_apply`: the two bijections on homogeneous pure tensors,
  which determine them.
* `DifferentialGraded.exists_rightTensorHomEquiv`,
  `DifferentialGraded.exists_leftTensorHomEquiv`: the bijections exist for the Hom modules of
  Tag 0FQ2.

## Implementation notes

*The Hom modules are specified, not named.* As in Tags 0FQ7 and 0FQ8, only the complex underlying
`Hom(M, N)` is canonical, so the two bijections take the module, an identification of its
underlying complex with the Hom complex, and the formula for its action as arguments; the two
`exists_*` results feed them the modules produced by Tag 0FQ2, so nothing is hypothetical.

*Both variances factor through balanced bilinear maps.* The tensor product enters only through its
universal property `DifferentialGraded.tensorHomEquiv`, and the asymmetry between the two
statements is carried entirely by the order of its two arguments: `M' ⊗_A M` against `M ⊗_A M'`.
What is proved separately in each variance is the identification of homomorphisms into `Hom(M, N)`
with balanced bilinear maps, and that is where the Koszul sign of the left-handed statement
appears.

## References

* [Stacks Project, Tag 0FQ4](https://stacks.math.columbia.edu/tag/0FQ4)
* [Stacks Project, Tag 0FQ6](https://stacks.math.columbia.edu/tag/0FQ6)
* [Stacks Project, Tag 09LL](https://stacks.math.columbia.edu/tag/09LL)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex
open scoped TensorProduct DirectSum

universe u v

namespace DifferentialGraded

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

/-! ### Transport along equalities of degrees -/

universe u₁ u₂ u₃

/-- Transporting a component of a cochain along equalities of its source and target degrees:
`hr ▸ c.v q r h x = c.v q' r' h' (hq ▸ x)`. -/
lemma rightHomCochainVTransport
    {C D : CochainComplex (ModuleCat.{u} R) ℤ} {n q q' r r' : ℤ}
    (c : Cochain C D n) (hq : q = q') (hr : r = r')
    (h : q + n = r) (h' : q' + n = r') (x : C.X q) :
    hr ▸ ((c.v q r h).hom x) = (c.v q' r' h').hom (hq ▸ x) := by subst q'; subst r'; rfl

/-- Elements `x ∈ G i` and `y ∈ G j` of a family of submodules with the same underlying element
agree after transport along `i = j`. -/
lemma rightHomSubtypeIndexCastEq
    {M : Type u} [AddCommGroup M] [Module R M] {I : Type*}
    (G : I → Submodule R M) {i j : I} (h : i = j)
    (x : G i) (y : G j) (hxy : (x : M) = y) : h ▸ x = y := by subst j; exact Subtype.ext hxy

/-- A bilinear map transported along an equality `i = j` of the index of its codomain takes the
transported values: `((h ▸ f) x) y = h ▸ f x y`. -/
lemma rightHomCastBilinearApply
    {I : Type u₁} {V : Type u₂} {U : Type u₃} {W : I → Type u₃}
    [AddCommGroup V] [Module R V] [AddCommGroup U] [Module R U]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {i j : I} (h : i = j) (f : V →ₗ[R] U →ₗ[R] W i)
    (x : V) (y : U) : ((h ▸ f) x) y = h ▸ (f x y) := by subst j; rfl

/-- The action law, restated with the `ModuleCat.Hom.hom` form of the coercion. -/
lemma rightHomActionDotHom (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
    (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
    (hact : ∀ (p q : ℤ) (a : A.grading p) (g : P.grading q),
      (iso.hom.f (q + p))
          (⟨MulOpposite.op (a : A.A) • (g : P.M),
            P.smul_mem q p (g : P.M) (a : A.A) g.property a.property⟩ : P.grading (q + p)) =
        ((LeftModule.leftAction A M (LeftModule.toCochainComplex A M)
          (Iso.refl _)).action p a).comp ((iso.hom.f q) g) (by omega))
    (p q : ℤ) (a : A.grading p) (g : P.grading q) :
    (iso.hom.f (q + p)).hom
        (⟨MulOpposite.op (a : A.A) • (g : P.M),
          P.smul_mem q p (g : P.M) (a : A.A) g.property a.property⟩ : P.grading (q + p)) =
      ((LeftModule.leftAction A M (LeftModule.toCochainComplex A M)
        (Iso.refl _)).action p a).comp ((iso.hom.f q).hom g) (by omega) :=
  hact p q a g

/-- The differential of the complex underlying a left module sends `y ∈ M^q` to `dy ∈ M^{q+1}`. -/
private lemma leftModule_toCochainComplex_d_apply (M : LeftModule A) (q : ℤ) (y : M.grading q) :
    ((LeftModule.toCochainComplex A M).d q (q + 1)).hom y =
      (⟨M.d y, M.d_mem q y y.property⟩ : M.grading (q + 1)) := by
  simp [LeftModule.toCochainComplex, CochainComplex.of, LeftModule.gradedDifferential]
  rfl

/-! ### From a homomorphism to a balanced bilinear map -/

/-- The bilinear map `M'^p × M^q → N^{p+q}` of a homomorphism `g : M' → P`, sending `(x, y)` to
`(g x)(y)` through the identification `iso` of `P` with `Hom(M, N)`. -/
noncomputable def rightHomToBilinearMap
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
    (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
    (g : DifferentialGradedModule.Hom M' P) (p q : ℤ) :
    M'.grading p →ₗ[R] M.grading q →ₗ[R] N.X (p + q) := by
  let c : M'.grading p →ₗ[R] Cochain (LeftModule.toCochainComplex A M) N p :=
    (iso.hom.f p).hom.comp (g.gradedMap p)
  refine { toFun := fun x => ((c x).v q (p + q) (Int.add_comm q p)).hom
           map_add' := ?_, map_smul' := ?_ }
  · intro x y; ext z
    exact congrArg (fun α : Cochain (LeftModule.toCochainComplex A M) N p =>
      ((α.v q (p + q) (Int.add_comm q p)).hom z)) (c.map_add x y)
  · intro r x; ext z; rw [c.map_smul r x]; rfl

/-- The Leibniz rule for `rightHomToBilinearMap`: `d((g x)(y)) = (g (dx))(y) + (-1)^p (g x)(dy)`
for `x ∈ M'^p`. -/
theorem rightHomToBilinearMap_map_d
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
    (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
    (g : DifferentialGradedModule.Hom M' P) (p q : ℤ)
    (x : M'.grading p) (y : M.grading q) :
    (N.d (p + q) (p + q + 1)).hom
      (((rightHomToBilinearMap M' M N P iso g p q) x) y) =
      ((show (p + 1) + q = p + q + 1 by omega) ▸
          rightHomToBilinearMap M' M N P iso g (p + 1) q)
          ⟨M'.d x, M'.d_mem p x x.property⟩ y +
        (p.negOnePow : ℤ) •
          ((show p + (q + 1) = p + q + 1 by omega) ▸
            rightHomToBilinearMap M' M N P iso g p (q + 1)) x
              ⟨M.d y, M.d_mem q y y.property⟩ := by
  let K := LeftModule.toCochainComplex A M
  let dx : M'.grading (p + 1) := ⟨M'.d x, M'.d_mem p x x.property⟩
  let fdx : P.grading (p + 1) := g.gradedMap (p + 1) dx
  let c : Cochain K N p := (iso.hom.f p).hom (g.gradedMap p x)
  have hgdx : g.gradedMap (p + 1) dx =
      (P.toCochainComplex.d p (p + 1)).hom (g.gradedMap p x) := by
    rw [DifferentialGradedModule.toCochainComplex_d]
    apply Subtype.ext
    show g.toFun (M'.d (x : M'.M)) = P.d (g.toFun x)
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun g.map_d (x : M'.M)
  have hcochain :
      (iso.hom.f (p + 1)).hom (g.gradedMap (p + 1) dx) =
        ((HomComplexR R K N).d p (p + 1)).hom c := by
    calc
      _ = (iso.hom.f (p + 1)).hom
          ((P.toCochainComplex.d p (p + 1)).hom (g.gradedMap p x)) := by rw [hgdx]
      _ = _ := by
        have hc := ConcreteCategory.congr_hom (iso.hom.comm p (p + 1)) (g.gradedMap p x)
        have hcs := hc.symm
        change
          (iso.hom.f (p + 1)).hom
              ((P.toCochainComplex.d p (p + 1)).hom (g.gradedMap p x)) =
            ((HomComplexR R K N).d p (p + 1)).hom c at hcs
        exact hcs
  have hcomponent := congrArg (fun z : Cochain K N (p + 1) =>
    (z.v q (p + q + 1) (by omega)).hom y) hcochain
  rw [HomComplexR_d_apply, δ_v p (p + 1) (by omega) c q (p + q + 1) (by omega)
    (p + q) (q + 1) (by omega) rfl] at hcomponent
  change
    (((iso.hom.f (p + 1)).hom (g.gradedMap (p + 1) dx)).v
        q (p + q + 1) (by omega)).hom y =
      (N.d (p + q) (p + q + 1)).hom ((c.v q (p + q) (Int.add_comm q p)).hom y) +
        (p + 1).negOnePow •
          (c.v (q + 1) (p + q + 1) (by omega)).hom ((K.d q (q + 1)).hom y)
      at hcomponent
  rw [Int.negOnePow_succ, Units.neg_smul] at hcomponent
  let cdx : Cochain K N (p + 1) := (iso.hom.f (p + 1)).hom fdx
  let e₁ : (p + 1) + q = p + q + 1 := by omega
  let e₂ : p + (q + 1) = p + q + 1 := by omega
  let dyC : K.X (q + 1) := (K.d q (q + 1)).hom y
  have hdyval : dyC = ⟨M.d y, M.d_mem q y y.property⟩ :=
    leftModule_toCochainComplex_d_apply M q y
  have hfinal :
      (cdx.v q (p + q + 1) (by omega)).hom y =
        (N.d (p + q) (p + q + 1)).hom ((c.v q (p + q) (Int.add_comm q p)).hom y) -
          p.negOnePow • (c.v (q + 1) (p + q + 1) (by omega)).hom dyC := by
    simpa only [K, c, fdx, cdx, sub_eq_add_neg] using hcomponent
  have hfirst :
    ((e₁ ▸ rightHomToBilinearMap M' M N P iso g (p + 1) q) dx) y =
        (cdx.v q (p + q + 1) (by omega)).hom y := by
    rw [rightHomCastBilinearApply (W := fun k : ℤ => N.X k) e₁
      (rightHomToBilinearMap M' M N P iso g (p + 1) q) dx y]
    show e₁ ▸ (cdx.v q (p + 1 + q) (by omega)).hom y =
      (cdx.v q (p + q + 1) (by omega)).hom y
    simpa using rightHomCochainVTransport cdx rfl e₁
      (show q + (p + 1) = (p + 1) + q by omega)
      (show q + (p + 1) = p + q + 1 by omega) y
  have hsecond :
      (e₂ ▸ rightHomToBilinearMap M' M N P iso g p (q + 1)) x
          ⟨M.d y, M.d_mem q y y.property⟩ =
        (c.v (q + 1) (p + q + 1) (by omega)).hom dyC := by
    rw [rightHomCastBilinearApply (W := fun k : ℤ => N.X k) e₂
      (rightHomToBilinearMap M' M N P iso g p (q + 1)) x
      (⟨M.d y, M.d_mem q y y.property⟩ : M.grading (q + 1))]
    show e₂ ▸ (((iso.hom.f p).hom (g.gradedMap p x)).v
      (q + 1) (p + (q + 1)) (by omega)).hom
        (⟨M.d y, M.d_mem q y y.property⟩ : M.grading (q + 1)) = _
    rw [← hdyval]
    simpa [c] using rightHomCochainVTransport c rfl e₂
      (show (q + 1) + p = p + (q + 1) by omega)
      (show (q + 1) + p = p + q + 1 by omega) dyC
  rw [hfirst, hsecond, hfinal]
  show (N.d (p + q) (p + q + 1)).hom ((c.v q (p + q) (Int.add_comm q p)).hom y) =
    (N.d (p + q) (p + q + 1)).hom ((c.v q (p + q) (Int.add_comm q p)).hom y) -
      ((p.negOnePow : ℤ) • ((c.v (q + 1) (p + q + 1) (by omega)).hom dyC)) +
      ((p.negOnePow : ℤ) • ((c.v (q + 1) (p + q + 1) (by omega)).hom dyC))
  abel

/-- The cochain of the left action of `a ∈ A^i` on `M` sends `y ∈ M^q` to `a • y ∈ M^{i+q}`. -/
lemma rightHomLeftActionApply (M : LeftModule A)
    (i q : ℤ) (a : A.grading i) (y : M.grading q) :
    (((LeftModule.leftAction A M (LeftModule.toCochainComplex A M) (Iso.refl _)).action i a).v
      q (i + q) (Int.add_comm q i)).hom y =
      (⟨(a : A.A) • (y : M.M), M.smul_mem i q a y a.property y.property⟩ :
        M.grading (i + q)) := by
  let c := (LeftModule.leftAction A M (LeftModule.toCochainComplex A M) (Iso.refl _)).action i a
  have ha := LeftModule.leftAction_apply A M
    (LeftModule.toCochainComplex A M) (Iso.refl _) i q a y
  change (c.v q (q + i) (by omega)).hom y = _ at ha
  have ht := rightHomCochainVTransport c rfl (Int.add_comm q i)
    rfl (Int.add_comm q i) y
  rw [ha] at ht
  exact ht.symm.trans (rightHomSubtypeIndexCastEq M.grading (Int.add_comm q i) _ _ rfl)

/-- The balanced bilinear map out of `M'` and `M` of a homomorphism `g : M' → P` of right
differential graded `A`-modules, given by `(x, y) ↦ (g x)(y)`. -/
noncomputable def rightHomToBilinear
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
    (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
    (hact : ∀ (p q : ℤ) (a : A.grading p) (g : P.grading q),
      (iso.hom.f (q + p))
          (⟨MulOpposite.op (a : A.A) • (g : P.M),
            P.smul_mem q p (g : P.M) (a : A.A) g.property a.property⟩ : P.grading (q + p)) =
        ((LeftModule.leftAction A M (LeftModule.toCochainComplex A M)
          (Iso.refl _)).action p a).comp ((iso.hom.f q) g) (by omega))
    (g : DifferentialGradedModule.Hom M' P) :
    BalancedBilinear M' M N := by
  refine ⟨(fun p q n h => ?_), ?_, ?_⟩
  · subst n
    exact rightHomToBilinearMap M' M N P iso g p q
  · intro p i q n h₁ h₂ x a y
    subst n
    simp only [rightHomToBilinearMap]
    let fx : P.grading p := ⟨g.toFun x, g.map_grading p _ x.property⟩
    let c : Cochain (LeftModule.toCochainComplex A M) N p := (iso.hom.f p).hom fx
    have hsmul : g.gradedMap (p + i)
        ⟨MulOpposite.op (a : A.A) • (x : M'.M),
          M'.smul_mem p i x a x.property a.property⟩ =
        ⟨MulOpposite.op (a : A.A) • (g.toFun x),
          P.smul_mem p i (g.toFun x) (a : A.A)
            (g.map_grading p _ x.property) a.property⟩ := by
      apply Subtype.ext
      exact g.map_smul (x : M'.M) (a : A.A)
    have ha := congrArg (fun z : Cochain (LeftModule.toCochainComplex A M) N (p + i) =>
      (z.v q (p + i + q) (by omega)).hom y)
      (rightHomActionDotHom M N P iso hact i p a fx)
    have hval := congrArg (fun z : P.grading (p + i) =>
      (((iso.hom.f (p + i)).hom z).v q (p + i + q) (by omega)).hom y) hsmul
    let yC : (LeftModule.toCochainComplex A M).X q := y
    let ayC : (LeftModule.toCochainComplex A M).X (i + q) :=
      ⟨(a : A.A) • (y : M.M), M.smul_mem i q (a : A.A) y a.property y.property⟩
    calc
      _ = (((iso.hom.f (p + i)).hom
          (g.gradedMap (p + i)
            ⟨MulOpposite.op (a : A.A) • (x : M'.M),
              M'.smul_mem p i x a x.property a.property⟩)).v q
          (p + i + q) (by omega)).hom y := rfl
      _ = (((iso.hom.f (p + i)).hom
          ⟨MulOpposite.op (a : A.A) • (g.toFun x),
            P.smul_mem p i (g.toFun x) (a : A.A)
              (g.map_grading p _ x.property) a.property⟩).v q
          (p + i + q) (by omega)).hom y := hval
      _ = ((((LeftModule.leftAction A M (LeftModule.toCochainComplex A M)
            (Iso.refl _)).action i a).comp c (show i + p = p + i by omega)).v q
          (p + i + q) (by omega)).hom yC := by
            simpa [fx, c, yC, add_assoc, add_comm, add_left_comm] using ha
      _ = h₂ ▸ (c.v (i + q) (p + (i + q)) (by omega)).hom ayC := by
          rw [Cochain.comp_v _ _ (show i + p = p + i by omega)
            q (i + q) (p + i + q) (by omega) (by omega)]
          simp only [ModuleCat.comp_apply]
          rw [rightHomLeftActionApply M]
          exact (rightHomCochainVTransport c rfl h₂ (by omega) (by omega) ayC).symm
      _ = _ := by
          have hcastMap := rightHomCastBilinearApply
            (W := fun k : ℤ => N.X k) h₂
            (rightHomToBilinearMap M' M N P iso g p (i + q)) x ayC
          exact hcastMap.symm
  · intro p q n h x y
    subst n
    exact rightHomToBilinearMap_map_d M' M N P iso g p q x y

/-! ### From a balanced bilinear map to a homomorphism -/

/-- For `x ∈ M'^p`, the cochain `b(x, -)` of degree `p` from `M` to `N`. -/
noncomputable def rightHomBilinearCochain
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (b : BalancedBilinear M' M N)
    (p : ℤ) (x : M'.grading p) : Cochain (LeftModule.toCochainComplex A M) N p :=
  Cochain.mk fun q r h => ModuleCat.ofHom (b.map p q r (by omega) x)

/-- The `R`-linear map `x ↦ b(x, -)` from `M'^p` to the cochains of degree `p` from `M` to `N`. -/
noncomputable def rightHomBilinearCochainLinear
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (b : BalancedBilinear M' M N) (p : ℤ) :
    M'.grading p →ₗ[R] Cochain (LeftModule.toCochainComplex A M) N p where
  toFun := rightHomBilinearCochain M' M N b p
  map_add' x y := by
    apply Cochain.ext; intro q r h
    apply ModuleCat.hom_ext; ext z
    exact congrArg (fun f => f z) ((b.map p q r (by omega)).map_add x y)
  map_smul' a x := by
    apply Cochain.ext; intro q r h
    apply ModuleCat.hom_ext; ext z
    exact congrArg (fun f => f z) ((b.map p q r (by omega)).map_smul a x)

/-- The `R`-linear map `M'^p → P^p` sending `x` to the element of `P` corresponding under `iso` to
the cochain `b(x, -)`. -/
noncomputable def rightHomBilinearComponent
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
    (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
    (b : BalancedBilinear M' M N) (p : ℤ) : M'.grading p →ₗ[R] P.grading p :=
  (iso.inv.f p).hom.comp (rightHomBilinearCochainLinear M' M N b p)

/-- The `R`-linear map `M' → P` whose restriction to each `M'^p` is
`rightHomBilinearComponent M' M N P iso b p`. -/
noncomputable def rightHomBilinearLinearMap
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
    (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
    (b : BalancedBilinear M' M N) : M'.M →ₗ[R] P.M := by
  let components : ∀ p : ℤ, M'.grading p →ₗ[R] P.M := fun p =>
    (Submodule.subtype (P.grading p)).comp (rightHomBilinearComponent M' M N P iso b p)
  exact (DirectSum.toModule (R := R) (ι := ℤ) (M := fun p => M'.grading p)
    P.M components).comp (DirectSum.decomposeLinearEquiv M'.grading).toLinearMap

/-- On `M'^p`, `rightHomBilinearLinearMap` is `rightHomBilinearComponent` in degree `p`. -/
theorem rightHomBilinearLinearMap_on_grading
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
    (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
    (b : BalancedBilinear M' M N) (p : ℤ) (x : M'.grading p) :
    rightHomBilinearLinearMap M' M N P iso b x =
      rightHomBilinearComponent M' M N P iso b p x := by
  simp [rightHomBilinearLinearMap]

/-- `rightHomBilinearLinearMap` sends `M'^p` into `P^p`. -/
theorem rightHomBilinearLinearMap_map_grading
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
    (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
    (b : BalancedBilinear M' M N) (p : ℤ) (x : M'.M) (hx : x ∈ M'.grading p) :
    rightHomBilinearLinearMap M' M N P iso b x ∈ P.grading p := by
  let x' : M'.grading p := ⟨x, hx⟩
  show rightHomBilinearLinearMap M' M N P iso b (x' : M'.M) ∈ _
  rw [rightHomBilinearLinearMap_on_grading M' M N P iso b p x']
  exact (rightHomBilinearComponent M' M N P iso b p x').property

/-- The differential of the Hom complex sends the cochain `b(x, -)` to `b(dx, -)`. -/
theorem rightHomBilinearCochain_map_d
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (b : BalancedBilinear M' M N)
    (p : ℤ) (x : M'.grading p) :
    ((HomComplexR R (LeftModule.toCochainComplex A M) N).d p (p + 1)).hom
        (rightHomBilinearCochain M' M N b p x) =
      rightHomBilinearCochain M' M N b (p + 1) ⟨M'.d x, M'.d_mem p x x.property⟩ := by
  let c := rightHomBilinearCochain M' M N b p x
  apply Cochain.ext
  intro q r h
  have hr : r = p + q + 1 := by omega
  cases hr
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change M.grading q at y
  rw [HomComplexR_d_apply, δ_v p (p + 1) (by omega) c q (p + q + 1)
    (by omega) (p + q) (q + 1) (by omega) rfl]
  let dx : M'.grading (p + 1) := ⟨M'.d x, M'.d_mem p x x.property⟩
  let dy : M.grading (q + 1) := ⟨M.d y, M.d_mem q y y.property⟩
  have hmap := b.map_d p q (p + q) rfl x y
  have hdy : ((LeftModule.toCochainComplex A M).d q (q + 1)).hom y = dy :=
    leftModule_toCochainComplex_d_apply M q y
  show (N.d (p + q) (p + q + 1)).hom ((c.v q (p + q) (Int.add_comm q p)).hom y) +
    ((p + 1).negOnePow : ℤ) •
      (c.v (q + 1) (p + q + 1) (by omega)).hom
        (((LeftModule.toCochainComplex A M).d q (q + 1)).hom y) =
    ((rightHomBilinearCochain M' M N b (p + 1) dx).v q (p + q + 1) (by omega)).hom y
  rw [hdy]
  show (N.d (p + q) (p + q + 1)).hom ((b.map p q (p + q) rfl x) y) +
    ((p + 1).negOnePow : ℤ) • ((b.map p (q + 1) (p + q + 1) (by omega) x) dy) =
    (b.map (p + 1) q (p + q + 1) (by omega) dx y)
  rw [Int.negOnePow_succ]
  rw [hmap]
  simp [dx, dy, neg_smul, add_assoc]

/-- The maps `rightHomBilinearComponent` commute with the differentials of `M'` and `P`. -/
theorem rightHomBilinearComponent_map_d
    (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
    (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
    (b : BalancedBilinear M' M N) (p : ℤ) (x : M'.grading p) :
    rightHomBilinearComponent M' M N P iso b (p + 1)
        ⟨M'.d x, M'.d_mem p x x.property⟩ =
      ⟨P.d (rightHomBilinearComponent M' M N P iso b p x),
        P.d_mem p (rightHomBilinearComponent M' M N P iso b p x).val
          (rightHomBilinearComponent M' M N P iso b p x).property⟩ := by
  show (iso.inv.f (p + 1)).hom
      (rightHomBilinearCochain M' M N b (p + 1) ⟨M'.d x, M'.d_mem p x x.property⟩) = _
  rw [← rightHomBilinearCochain_map_d M' M N b p x]
  have hc := (ConcreteCategory.congr_hom
    (iso.inv.comm p (p + 1)) (rightHomBilinearCochain M' M N b p x)).symm
  change (iso.inv.f (p + 1)).hom
      (((HomComplexR R (LeftModule.toCochainComplex A M) N).d p (p + 1)).hom
        (rightHomBilinearCochain M' M N b p x)) =
    (P.toCochainComplex.d p (p + 1)).hom
      ((iso.inv.f p).hom (rightHomBilinearCochain M' M N b p x)) at hc
  rw [DifferentialGradedModule.toCochainComplex_d] at hc
  exact hc

section

variable (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
  (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
  (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)

/-- The degree-`p` component of `iso.hom` is injective. -/
lemma rightHomIsoComponentInjective (p : ℤ) :
    Function.Injective (iso.hom.f p).hom :=
  Function.LeftInverse.injective (fun x =>
    ConcreteCategory.congr_hom (HomologicalComplex.congr_hom iso.hom_inv_id p) x)

/-- Under `iso`, `rightHomBilinearComponent M' M N P iso b p x` is the cochain `b(x, -)`. -/
lemma rightHomIsoBilinearComponent
    (b : BalancedBilinear M' M N) (p : ℤ) (x : M'.grading p) :
    (iso.hom.f p).hom (rightHomBilinearComponent M' M N P iso b p x) =
      rightHomBilinearCochain M' M N b p x :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom iso.inv_hom_id p) _

end

section

variable (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
  (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
  (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
  (hact : ∀ (p q : ℤ) (a : A.grading p) (g : P.grading q),
    (iso.hom.f (q + p))
        (⟨MulOpposite.op (a : A.A) • (g : P.M),
          P.smul_mem q p (g : P.M) (a : A.A) g.property a.property⟩ : P.grading (q + p)) =
      ((LeftModule.leftAction A M (LeftModule.toCochainComplex A M) (Iso.refl _)).action p a).comp
        ((iso.hom.f q) g) (by omega))

include hact

/-- The maps `rightHomBilinearComponent` commute with the right actions of `A` on `M'` and `P`. -/
lemma rightHomBilinearComponent_map_smul
    (b : BalancedBilinear M' M N) (p i : ℤ) (x : M'.grading p) (a : A.grading i) :
    rightHomBilinearComponent M' M N P iso b (p + i)
        ⟨MulOpposite.op (a : A.A) • (x : M'.M), M'.smul_mem p i x a x.2 a.2⟩ =
      ⟨MulOpposite.op (a : A.A) • (rightHomBilinearComponent M' M N P iso b p x).val,
        P.smul_mem p i _ _ (rightHomBilinearComponent M' M N P iso b p x).2 a.2⟩ := by
  apply rightHomIsoComponentInjective M N P iso (p + i)
  rw [rightHomIsoBilinearComponent, rightHomActionDotHom M N P iso hact,
    rightHomIsoBilinearComponent]
  apply Cochain.ext
  intro q n h
  rw [Cochain.comp_v _ _ (show i + p = p + i by omega) q (i + q) n (by omega) (by omega)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change M.grading q at y
  show b.map (p + i) q n (by omega) _ y =
    (b.map p (i + q) n (by omega) x)
      ((((LeftModule.leftAction A M (LeftModule.toCochainComplex A M)
        (Iso.refl _)).action i a).v q (i + q) (Int.add_comm q i)).hom y)
  rw [rightHomLeftActionApply M]
  exact b.balance p i q n (by omega) (by omega) x a y

/-- The homomorphism `M' → P` of right differential graded `A`-modules of a balanced bilinear map
`b`, sending `x` to the element of `P` corresponding under `iso` to `b(x, -)`. -/
noncomputable def rightHomOfBilinear (b : BalancedBilinear M' M N) :
    DifferentialGradedModule.Hom M' P where
  toFun := rightHomBilinearLinearMap M' M N P iso b
  map_grading := rightHomBilinearLinearMap_map_grading M' M N P iso b
  map_d := by
    apply DirectSum.decompose_lhom_ext M'.grading
    intro p
    apply LinearMap.ext
    intro x
    change rightHomBilinearLinearMap M' M N P iso b (M'.d x) =
      P.d (rightHomBilinearLinearMap M' M N P iso b x)
    rw [rightHomBilinearLinearMap_on_grading M' M N P iso b p x]
    rw [rightHomBilinearLinearMap_on_grading M' M N P iso b (p + 1)
      ⟨M'.d x, M'.d_mem p x x.2⟩]
    exact congrArg Subtype.val (rightHomBilinearComponent_map_d M' M N P iso b p x)
  map_smul := by
    intro x a
    induction x using DirectSum.Decomposition.inductionOn M'.grading with
    | zero => simp
    | @homogeneous p x =>
      induction a using DirectSum.Decomposition.inductionOn A.grading with
      | zero => simp
      | @homogeneous i a =>
        rw [rightHomBilinearLinearMap_on_grading M' M N P iso b p x]
        rw [rightHomBilinearLinearMap_on_grading M' M N P iso b (p + i)
          ⟨MulOpposite.op (a : A.A) • (x : M'.M), M'.smul_mem p i x a x.2 a.2⟩]
        exact congrArg Subtype.val
          (rightHomBilinearComponent_map_smul M' M N P iso hact b p i x a)
      | add a a' ha ha' => simp only [MulOpposite.op_add, add_smul, map_add, ha, ha']
    | add x x' hx hx' => simp only [smul_add, map_add, hx, hx']

/-- In degree `p`, `rightHomOfBilinear` is `rightHomBilinearComponent`. -/
lemma rightHomOfBilinear_gradedMap (b : BalancedBilinear M' M N)
    (p : ℤ) (x : M'.grading p) :
    (rightHomOfBilinear M' M N P iso hact b).gradedMap p x =
      rightHomBilinearComponent M' M N P iso b p x :=
  Subtype.ext (rightHomBilinearLinearMap_on_grading M' M N P iso b p x)

/-- `rightHomToBilinear` sends `g` to the pairing `(x, y) ↦ (g x)(y)`. -/
lemma rightHomToBilinear_apply (g : DifferentialGradedModule.Hom M' P)
    (p q n : ℤ) (h : p + q = n) (x : M'.grading p) (y : M.grading q) :
    (rightHomToBilinear M' M N P iso hact g).map p q n h x y =
      (((iso.hom.f p).hom (g.gradedMap p x)).v q n (by omega)).hom y := by
  subst n; rfl

/-- `rightHomToBilinear` is injective. -/
lemma rightHomToBilinear_injective :
    Function.Injective (rightHomToBilinear M' M N P iso hact) := by
  intro f g h
  apply DifferentialGradedModule.Hom.ext
  apply DirectSum.decompose_lhom_ext M'.grading
  intro p
  apply LinearMap.ext
  intro x
  show (f.gradedMap p x).val = (g.gradedMap p x).val
  apply congrArg Subtype.val
  apply rightHomIsoComponentInjective M N P iso p
  apply Cochain.ext
  intro q n hqn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change M.grading q at y
  have he := congrArg (fun c : BalancedBilinear M' M N =>
    c.map p q n (by omega) x y) h
  simpa only [rightHomToBilinear_apply] using he

/-- `rightHomToBilinear` is a left inverse of `rightHomOfBilinear`. -/
lemma rightHomToBilinear_ofBilinear (b : BalancedBilinear M' M N) :
    rightHomToBilinear M' M N P iso hact (rightHomOfBilinear M' M N P iso hact b) = b := by
  apply BalancedBilinear.ext
  intro p q n h x y
  rw [rightHomToBilinear_apply, rightHomOfBilinear_gradedMap, rightHomIsoBilinearComponent]
  rfl

end

section Right

variable (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
  (N : CochainComplex (ModuleCat.{u} R) ℤ) (P : DifferentialGradedModule.{u, v, u} A)
  (iso : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N)
  (hact : ∀ (p q : ℤ) (a : A.grading p) (g : P.grading q),
    (iso.hom.f (q + p))
        (⟨MulOpposite.op (a : A.A) • (g : P.M),
          P.smul_mem q p (g : P.M) (a : A.A) g.property a.property⟩ : P.grading (q + p)) =
      ((LeftModule.leftAction A M (LeftModule.toCochainComplex A M) (Iso.refl _)).action p a).comp
        ((iso.hom.f q) g) (by omega))

/-- Homomorphisms of right differential graded `A`-modules into a presentation of `Hom(M, N)`
are the balanced bilinear maps out of `M'` and `M`. -/
noncomputable def rightHomBalancedEquiv :
    DifferentialGradedModule.Hom M' P ≃ BalancedBilinear M' M N where
  toFun := rightHomToBilinear M' M N P iso hact
  invFun := rightHomOfBilinear M' M N P iso hact
  left_inv _g := rightHomToBilinear_injective M' M N P iso hact
    (rightHomToBilinear_ofBilinear M' M N P iso hact _)
  right_inv := rightHomToBilinear_ofBilinear M' M N P iso hact

/-- The equivalence sends `g` to the pairing `(x, y) ↦ (g x)(y)`. -/
theorem rightHomBalancedEquiv_apply (g : DifferentialGradedModule.Hom M' P)
    (p q n : ℤ) (h : p + q = n) (x : M'.grading p) (y : M.grading q) :
    (rightHomBalancedEquiv M' M N P iso hact g).map p q n h x y =
      (((iso.hom.f p) ⟨g.toFun x, g.map_grading p x x.property⟩).v q n (by omega)).hom y := by
  subst n; rfl

/-! ### The right-handed adjunction -/

/-- For a right differential graded `A`-module `M'`, a left differential graded `A`-module `M` and
a complex `N` of `R`-modules, homomorphisms of right differential graded `A`-modules
`M' → Hom(M, N)` are the maps of complexes of `R`-modules `M' ⊗_A M → N`. -/
@[stacks 0FQ4 "the identification"]
noncomputable def rightTensorHomEquiv :
    DifferentialGradedModule.Hom M' P ≃ (tensorComplex M' M ⟶ N) :=
  (rightHomBalancedEquiv M' M N P iso hact).trans (tensorHomEquiv M' M N).symm

/-- `rightTensorHomEquiv` sends `g` to the map of complexes taking `x ⊗ y` to `(g x)(y)`. -/
@[stacks 0FQ4 "the identification on pure tensors"]
theorem rightTensorHomEquiv_apply (g : DifferentialGradedModule.Hom M' P)
    (p q n : ℤ) (h : p + q = n) (x : M'.grading p) (y : M.grading q) :
    ((rightTensorHomEquiv M' M N P iso hact g).f n).hom ((tensorTmul M' M).map p q n h x y) =
      (((iso.hom.f p) ⟨g.toFun x, g.map_grading p x x.property⟩).v q n (by omega)).hom y := by
  have he : rightTensorHomEquiv M' M N P iso hact g =
      tensorDesc M' M N (rightHomBalancedEquiv M' M N P iso hact g) := rfl
  rw [he, tensorDesc_apply, rightHomBalancedEquiv_apply]

end Right

section RightExistence

variable (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
  (N : CochainComplex (ModuleCat.{u} R) ℤ)

/-- There is a right differential graded `A`-module `P` with underlying complex `Hom(M, N)` such
that homomorphisms `M' → P` are in bijection with maps of complexes `M' ⊗_A M → N`. -/
@[stacks 0FQ4 "existence of the identification"]
theorem exists_rightTensorHomEquiv :
    ∃ (P : DifferentialGradedModule.{u, v, u} A)
      (_ : P.toCochainComplex ≅ HomComplexR R (LeftModule.toCochainComplex A M) N),
      Nonempty (DifferentialGradedModule.Hom M' P ≃ (tensorComplex M' M ⟶ N)) := by
  obtain ⟨P, i, hi⟩ := LeftModule.exists_homRightModule A M N
  exact ⟨P, i, ⟨rightTensorHomEquiv M' M N P i hi⟩⟩

end RightExistence

namespace LeftHomAux

/-- A presentation of the left differential graded `A`-module `Hom(M, N)`: a left module
together with an identification of its underlying complex with the Hom complex and the signed
precomposition action law. -/
structure LeftHomPresentation (M : DifferentialGradedModule.{u, v, u} A)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) where
  /-- The left differential graded `A`-module. -/
  module : LeftModule A
  /-- Its underlying complex of `R`-modules is the Hom complex. -/
  iso : LeftModule.toCochainComplex A module ≅ HomComplexR R M.toCochainComplex N
  /-- The signed action is precomposition by the right action. -/
  action : ∀ (p q n : ℤ) (a : A.grading p) (f : module.grading q) (x : M.grading n),
    HEq
      ((((iso.hom.f (p + q))
          (⟨(a : A.A) • (f : module.M),
            module.smul_mem p q (a : A.A) (f : module.M) a.property f.property⟩ :
            module.grading (p + q))).v n (n + (p + q)) (by omega)).hom x)
      ((p * (q + n)).negOnePow •
        (((iso.hom.f q) f).v (n + p) (n + p + q) (by omega)).hom
          (⟨MulOpposite.op (a : A.A) • (x : M.M),
            M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ :
            M.grading (n + p)))

/-- The action law of a presentation, written with the underlying linear maps displayed. -/
theorem LeftHomPresentation.action' {M : DifferentialGradedModule.{u, v, u} A}
    {N : CochainComplex (ModuleCat.{u} R) ℤ} (E : LeftHomPresentation M N)
    (p q n : ℤ) (a : A.grading p) (f : E.module.grading q) (x : M.grading n) :
    HEq
      ((((E.iso.hom.f (p + q)).hom
          (⟨(a : A.A) • (f : E.module.M),
            E.module.smul_mem p q (a : A.A) (f : E.module.M) a.property f.property⟩ :
            E.module.grading (p + q))).v n (n + (p + q)) (by omega)).hom x)
      ((p * (q + n)).negOnePow •
        (((E.iso.hom.f q).hom f).v (n + p) (n + p + q) (by omega)).hom
          (⟨MulOpposite.op (a : A.A) • (x : M.M),
            M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ :
            M.grading (n + p))) :=
  E.action p q n a f x

/-- The sign identity `(-1)^{p(i+q)} = (-1)^{i(q+p)} (-1)^{(p+i)q}`. -/
theorem sign_action (p i q : ℤ) :
    (p * (i + q)).negOnePow = (i * (q + p)).negOnePow * ((p + i) * q).negOnePow := by
  rw [show p * (i + q) = p * i + p * q by ring,
    show p * i = i * p by ring, Int.negOnePow_add]
  conv_rhs => rw [← Int.negOnePow_add]
  rw [show i * (q + p) + (p + i) * q = i * p + p * q + 2 * (i * q) by ring,
    Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_two_mul]
  ac_rfl

/-- Two components `z.v p q h` and `z.v p q' h'` of a cochain take heterogeneously equal values. -/
theorem cochain_v_apply_heq
    {R : Type*} [CommRing R] {F G : CochainComplex (ModuleCat R) ℤ}
    {n p q q' : ℤ} (z : Cochain F G n) (h : p + n = q) (h' : p + n = q')
    (x : F.X p) : HEq ((z.v p q h).hom x) ((z.v p q' h').hom x) := by
  have hq : q = q' := by omega
  cases hq
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  rfl

/-- Integer multiples of heterogeneously equal elements of a family of abelian groups are
heterogeneously equal. -/
theorem heq_zsmul_sameIndex {ι : Type*} (F : ι → Type*)
    [∀ i, AddCommGroup (F i)] {i j : ι} {x : F i} {y : F j} (hij : i = j)
    (n : ℤ) (h : HEq x y) : HEq (n • x) (n • y) := by
  subst j
  obtain rfl := eq_of_heq h
  rfl

variable (M : DifferentialGradedModule.{u, v, u} A) (M' : LeftModule A)
  (N : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The bilinear map `(x, y) ↦ (-1)^{pq} B(x, y)` from `M^p × M'^q` to `N^n`. -/
def valueMap (B : BalancedBilinear M M' N) (p q n : ℤ) (h : p + q = n) :
    M.grading p →ₗ[R] M'.grading q →ₗ[R] N.X n :=
  LinearMap.mk₂ R (fun x y => ((p * q).negOnePow : ℤ) • B.map p q n h x y)
    (by intro x₁ x₂ y; simp [map_add, smul_add])
    (by intro r x y; simp only [map_smul]; exact smul_comm _ _ _)
    (by intro x y₁ y₂; simp [map_add, smul_add])
    (by intro r x y; simp only [map_smul]; exact smul_comm _ _ _)

/-- For `y ∈ M'^q`, the cochain of degree `q` from `M` to `N` sending `x ∈ M^p` to
`(-1)^{pq} B(x, y)`. -/
def curryCochain (B : BalancedBilinear M M' N) (q : ℤ) (y : M'.grading q) :
    Cochain M.toCochainComplex N q :=
  Cochain.mk fun p r h => ModuleCat.ofHom {
    toFun := fun x => (valueMap M M' N B p q r (by omega) x) y
    map_add' := by intro x x'; simp
    map_smul' := by intro c x; simp }

/-- The `R`-linear map `M'^q → H^q` sending `y` to the element corresponding under `E.iso` to the
cochain `curryCochain M M' N B q y`. -/
noncomputable def curryPiece (E : LeftHomPresentation M N)
    (B : BalancedBilinear M M' N) (q : ℤ) :
    M'.grading q →ₗ[R] E.module.grading q := by
  refine {
    toFun := fun y => (E.iso.inv.f q).hom (curryCochain M M' N B q y)
    map_add' := ?_
    map_smul' := ?_ }
  · intro y z
    apply Subtype.ext
    have hc : curryCochain M M' N B q (y + z) =
        curryCochain M M' N B q y + curryCochain M M' N B q z := by
      apply Cochain.ext
      intro p r h
      apply ModuleCat.hom_ext
      ext x
      change (valueMap M M' N B p q r h x) (y + z) =
        (valueMap M M' N B p q r h x) y + (valueMap M M' N B p q r h x) z
      exact map_add (valueMap M M' N B p q r h x) y z
    have hm := (congrArg ((E.iso.inv.f q).hom) hc).trans
      ((E.iso.inv.f q).hom.map_add _ _)
    exact congrArg Subtype.val hm
  · intro c y
    apply Subtype.ext
    have hc : curryCochain M M' N B q (c • y) =
        c • curryCochain M M' N B q y := by
      apply Cochain.ext
      intro p r h
      apply ModuleCat.hom_ext
      ext x
      change (valueMap M M' N B p q r h x) (c • y) =
        c • (valueMap M M' N B p q r h x) y
      exact map_smul (valueMap M M' N B p q r h x) c y
    have hm := (congrArg ((E.iso.inv.f q).hom) hc).trans
      ((E.iso.inv.f q).hom.map_smul c _)
    exact congrArg Subtype.val hm

/-- The `R`-linear map `M' → H` whose restriction to each `M'^q` is `curryPiece M M' N E B q`. -/
noncomputable def curryToFun (E : LeftHomPresentation M N)
    (B : BalancedBilinear M M' N) : M'.M →ₗ[R] E.module.M := by
  classical
  exact LinearMap.comp
    (DirectSum.toModule R ℤ E.module.M
      (fun q => (Submodule.subtype _).comp (curryPiece M M' N E B q)))
    (DirectSum.decomposeLinearEquiv M'.grading).toLinearMap

/-- On `M'^q`, `curryToFun` is `curryPiece` in degree `q`. -/
theorem curryToFun_of_mem (E : LeftHomPresentation M N)
    (B : BalancedBilinear M M' N) (q : ℤ) (y : M'.M) (hy : y ∈ M'.grading q) :
    curryToFun M M' N E B y = (curryPiece M M' N E B q ⟨y, hy⟩ : E.module.M) := by
  classical
  unfold curryToFun
  let y' : M'.grading q := ⟨y, hy⟩
  have hd : DirectSum.decomposeLinearEquiv M'.grading y =
      DirectSum.lof R ℤ (fun i => M'.grading i) q y' := by
    simpa [y'] using DirectSum.decomposeLinearEquiv_apply_coe M'.grading q y'
  show (DirectSum.toModule R ℤ E.module.M
      (fun q => (Submodule.subtype _).comp (curryPiece M M' N E B q)))
      (DirectSum.decomposeLinearEquiv M'.grading y) = _
  rw [hd, DirectSum.toModule_lof]
  rfl

/-- `curryToFun` sends `M'^q` into `H^q`. -/
theorem curryToFun_map_grading (E : LeftHomPresentation M N)
    (B : BalancedBilinear M M' N) (q : ℤ) (y : M'.M) (hy : y ∈ M'.grading q) :
    curryToFun M M' N E B y ∈ E.module.grading q := by
  rw [curryToFun_of_mem M M' N E B q y hy]
  exact (curryPiece M M' N E B q ⟨y, hy⟩).property

/-- Under `E.iso`, `curryPiece M M' N E B q y` is the cochain `curryCochain M M' N B q y`. -/
theorem curryPiece_iso (E : LeftHomPresentation M N)
    (B : BalancedBilinear M M' N) (q : ℤ) (y : M'.grading q) :
    (E.iso.hom.f q).hom (curryPiece M M' N E B q y) =
      curryCochain M M' N B q y := by
  have h := congrArg (fun f => f.hom (curryCochain M M' N B q y))
    (congrArg (fun e => e.f q) E.iso.inv_hom_id)
  show (E.iso.inv.f q ≫ E.iso.hom.f q).hom
      (curryCochain M M' N B q y) = _
  exact h

/-- The action law of a presentation, with both sides evaluated in degree `p + (i + q)`. -/
private theorem presentation_action_eq (E : LeftHomPresentation M N) (i q p : ℤ)
    (a : A.grading i) (f : E.module.grading q) (x : M.grading p) :
    (((E.iso.hom.f (i + q)).hom
        ⟨(a : A.A) • (f : E.module.M),
          E.module.smul_mem i q (a : A.A) (f : E.module.M) a.property f.property⟩).v
        p (p + (i + q)) (by omega)).hom x =
      ((i * (q + p)).negOnePow : ℤ) •
        (((E.iso.hom.f q).hom f).v (p + i) (p + (i + q)) (by omega)).hom
          ⟨MulOpposite.op (a : A.A) • (x : M.M),
            M.smul_mem p i (x : M.M) (a : A.A) x.property a.property⟩ := by
  have ht := heq_zsmul_sameIndex (fun n : ℤ => N.X n)
    (show p + i + q = p + (i + q) by omega) ((i * (q + p)).negOnePow : ℤ)
    (cochain_v_apply_heq ((E.iso.hom.f q).hom f) (p := p + i) (q := p + i + q)
      (q' := p + (i + q)) (by omega) (by omega)
      (⟨MulOpposite.op (a : A.A) • (x : M.M),
        M.smul_mem p i (x : M.M) (a : A.A) x.property a.property⟩ : M.grading (p + i)))
  exact eq_of_heq ((E.action' i q p a f x).trans ht)

/-- The maps `curryPiece` commute with the left actions of `A` on `M'` and `H`. -/
theorem curryPiece_action (E : LeftHomPresentation M N)
    (B : BalancedBilinear M M' N) (i q : ℤ) (a : A.grading i) (y : M'.grading q) :
    (curryPiece M M' N E B (i + q) ⟨(a : A.A) • (y : M'.M),
        M'.smul_mem i q (a : A.A) (y : M'.M) a.property y.property⟩ : E.module.M) =
      (a : A.A) • (curryPiece M M' N E B q y : E.module.M) := by
  let f := curryPiece M M' N E B q y
  let ya : M'.grading (i + q) := ⟨(a : A.A) • (y : M'.M),
    M'.smul_mem i q (a : A.A) (y : M'.M) a.property y.property⟩
  let fa : E.module.grading (i + q) := ⟨(a : A.A) • (f : E.module.M),
    E.module.smul_mem i q (a : A.A) (f : E.module.M) a.property f.property⟩
  have hc : curryCochain M M' N B (i + q) ya =
      (E.iso.hom.f (i + q)).hom fa := by
    apply Cochain.ext
    intro p r hpr
    have hr : r = p + (i + q) := by omega
    subst r
    apply ModuleCat.hom_ext
    ext x
    let xx : M.grading p := x
    let xa : M.grading (p + i) := ⟨MulOpposite.op (a : A.A) • xx.val, by
      have hm := M.smul_mem p i xx.val (a : A.A) xx.property a.property
      simpa only [add_comm] using hm⟩
    have hbal := B.balance p i q (p + (i + q)) (by omega) rfl xx a y
    have hsign := sign_action p i q
    let hfcochain : Cochain M.toCochainComplex N q :=
      (E.iso.hom.f q).hom f
    have hactEq := presentation_action_eq M N E i q p a f xx
    calc
      ((curryCochain M M' N B (i + q) ya).v p (p + (i + q)) (by omega)).hom x =
          ((p * (i + q)).negOnePow : ℤ) •
            B.map p (i + q) (p + (i + q)) rfl (x : M.grading p) ya := by
        dsimp [curryCochain, valueMap]
        rfl
      _ = ((i * (q + p)).negOnePow : ℤ) •
          (hfcochain.v (p + i) (p + (i + q)) (by omega)).hom xa := by
        have heval :
            (((E.iso.hom.f q).hom f).v (p + i) (p + (i + q)) (by omega)).hom
                (xa : M.toCochainComplex.X (p + i)) =
              (((p + i) * q).negOnePow : ℤ) •
                B.map (p + i) q (p + (i + q)) (by omega) xa y := by
          rw [curryPiece_iso]
          show ((p + i) * q).negOnePow • B.map (p + i) q (p + (i + q)) _ xa y = _
          rfl
        rw [heval, ← hbal, smul_smul]
        simpa only [smul_smul, Units.val_mul] using
          congrArg (fun z : ℤˣ => (z : ℤ) •
            ((B.map (p + i) q (p + (i + q)) (by omega) xa) y)) hsign
      _ = (((E.iso.hom.f (i + q)).hom fa).v p (p + (i + q)) (by omega)).hom x :=
        hactEq.symm
  have h := congrArg (fun z => (E.iso.inv.f (i + q)).hom z) hc
  change (E.iso.inv.f (i + q)).hom (curryCochain M M' N B (i + q) ya) =
    (E.iso.inv.f (i + q)).hom ((E.iso.hom.f (i + q)).hom fa) at h
  show (((curryPiece M M' N E B (i + q) ya : E.module.grading (i + q)) : E.module.M)) = _
  have hv := congrArg Subtype.val h
  have hi : (E.iso.inv.f (i + q)).hom
      ((E.iso.hom.f (i + q)).hom fa) = fa := by
    have hh := congrArg (fun e => e.f (i + q)) E.iso.hom_inv_id
    let fa' : (LeftModule.toCochainComplex A E.module).X (i + q) := by
      show E.module.grading (i + q)
      exact fa
    have hh' := congrArg (fun z => z.hom fa') hh
    have hh'' := by
      simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.coe_comp, Function.comp_apply, HomologicalComplex.id_f,
      ModuleCat.hom_id, LinearMap.id_apply] using hh'
    change E.module.grading (i + q) at fa'
    have hfa : fa' = fa := by
      apply Subtype.ext
      rfl
    simpa only [hfa] using hh''
  rw [hi] at hv
  dsimp [curryPiece]
  exact hv

/-- `curryCochain M M' N B q y` sends `x ∈ M^p` to `(-1)^{pq} B(x, y)`. -/
theorem curryCochain_apply (B : BalancedBilinear M M' N)
    (p q n : ℤ) (h : p + q = n) (x : M.grading p) (y : M'.grading q) :
    ((curryCochain M M' N B q y).v p n h).hom x =
      (p * q).negOnePow • B.map p q n h x y := rfl

/-- The differential of the Hom complex sends `curryCochain M M' N B q y` to the cochain
`curryCochain M M' N B (q + 1) (dy)`. -/
theorem curryCochain_d (B : BalancedBilinear M M' N)
    (q : ℤ) (y : M'.grading q) :
    δ q (q + 1) (curryCochain M M' N B q y) =
      curryCochain M M' N B (q + 1) ⟨M'.d y, M'.d_mem q y y.property⟩ := by
  apply Cochain.ext
  intro p n h
  obtain rfl : n = p + q + 1 := by omega
  rw [δ_v q (q + 1) rfl _ p (p + q + 1) h (p + q) (p + 1) (by omega) rfl]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (x : M.grading p)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_smul,
    Units.smul_def, DifferentialGradedModule.toCochainComplex_d]
  show (N.d (p + q) (p + q + 1)).hom
      (((curryCochain M M' N B q y).v p (p + q) rfl).hom x) +
    (q + 1).negOnePow •
      (((curryCochain M M' N B q y).v (p + 1) (p + q + 1) (by omega)).hom
        ⟨M.d x, M.d_mem p x x.property⟩) = _
  simp only [curryCochain_apply, Units.smul_def, map_zsmul]
  rw [show (N.d (p + q) (p + q + 1)).hom (B.map p q (p + q) rfl x y) = _ from
    B.map_d p q (p + q) rfl x y]
  simp only [← Units.smul_def, smul_add, smul_smul]
  have hs : (q + 1).negOnePow * ((p + 1) * q).negOnePow = -(p * q).negOnePow := by
    rw [Int.negOnePow_succ, add_mul, one_mul, Int.negOnePow_add, neg_mul,
      mul_left_comm, Int.units_mul_self, mul_one]
  have ht : (p * q).negOnePow * p.negOnePow = (p * (q + 1)).negOnePow := by
    rw [mul_add, mul_one, Int.negOnePow_add]
  rw [hs, ht, Units.neg_smul]
  abel

/-- The maps `curryPiece` commute with the differentials of `M'` and `H`. -/
theorem curryPiece_d (E : LeftHomPresentation M N)
    (B : BalancedBilinear M M' N) (q : ℤ) (y : M'.grading q) :
    (curryPiece M M' N E B (q + 1) ⟨M'.d y, M'.d_mem q y y.property⟩ : E.module.M) =
      E.module.d (curryPiece M M' N E B q y) := by
  have hc := congrArg (fun f => f.hom (curryCochain M M' N B q y))
    (E.iso.inv.comm q (q + 1))
  have hc := congrArg (fun z : E.module.grading (q + 1) => z.val) hc
  simp only [ModuleCat.hom_comp, LeftModule.toCochainComplex, CochainComplex.of_d] at hc
  change E.module.d (curryPiece M M' N E B q y) =
    ((E.iso.inv.f (q + 1)).hom (δ q (q + 1) (curryCochain M M' N B q y)) :
      E.module.grading (q + 1)).val at hc
  rw [curryCochain_d] at hc
  exact hc.symm

/-- The homomorphism `M' → H` of left differential graded `A`-modules of a balanced bilinear map
`B`, sending `y ∈ M'^q` to the element corresponding to `x ↦ (-1)^{pq} B(x, y)`. -/
noncomputable def curryHom (E : LeftHomPresentation M N)
    (B : BalancedBilinear M M' N) : LeftModule.Hom M' E.module where
  toFun := curryToFun M M' N E B
  map_grading := curryToFun_map_grading M M' N E B
  map_smul := by
    intro a y
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | add a b ha hb => simp only [add_smul, map_add, ha, hb]
    | @homogeneous i a =>
      induction y using DirectSum.Decomposition.inductionOn M'.grading with
      | zero => simp
      | add y z hy hz => simp only [smul_add, map_add, hy, hz]
      | @homogeneous q y =>
        rw [curryToFun_of_mem M M' N E B (i + q) _
          (M'.smul_mem i q a y a.property y.property),
          curryToFun_of_mem M M' N E B q y y.property]
        exact curryPiece_action M M' N E B i q a y
  map_d := by
    ext y
    change curryToFun M M' N E B (M'.d y) = E.module.d (curryToFun M M' N E B y)
    induction y using DirectSum.Decomposition.inductionOn M'.grading with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | @homogeneous q y =>
      rw [curryToFun_of_mem M M' N E B (q + 1) _ (M'.d_mem q y y.property),
        curryToFun_of_mem M M' N E B q y y.property]
      exact curryPiece_d M M' N E B q y

/-- For a homomorphism `g : M' → H`, the `R`-linear map sending `y ∈ M'^q` to the cochain of
degree `q` from `M` to `N` corresponding to `g y` under `E.iso`. -/
noncomputable def homCochain (E : LeftHomPresentation M N)
    (g : LeftModule.Hom M' E.module) (q : ℤ) :
    M'.grading q →ₗ[R] Cochain M.toCochainComplex N q :=
  (E.iso.hom.f q).hom.comp ({
    toFun := fun y => ⟨g.toFun y, g.map_grading q y y.property⟩
    map_add' := by intro y z; apply Subtype.ext; exact g.toFun.map_add _ _
    map_smul' := by intro c y; apply Subtype.ext; exact g.toFun.map_smul c _ } :
      M'.grading q →ₗ[R] E.module.grading q)

/-- The differential of the Hom complex sends `homCochain M M' N E g q y` to the cochain
`homCochain M M' N E g (q + 1) (dy)`. -/
theorem homCochain_d (E : LeftHomPresentation M N)
    (g : LeftModule.Hom M' E.module) (q : ℤ) (y : M'.grading q) :
    δ q (q + 1) (homCochain M M' N E g q y) =
      homCochain M M' N E g (q + 1) ⟨M'.d y, M'.d_mem q y y.property⟩ := by
  have hc := congrArg (fun f => f.hom
    (⟨g.toFun y, g.map_grading q y y.property⟩ : E.module.grading q))
    (E.iso.hom.comm q (q + 1))
  simp only [ModuleCat.hom_comp, LeftModule.toCochainComplex, CochainComplex.of_d] at hc
  change δ q (q + 1) (homCochain M M' N E g q y) =
    (E.iso.hom.f (q + 1)).hom
      ⟨E.module.d (g.toFun y), E.module.d_mem q _ (g.map_grading q y y.property)⟩ at hc
  rw [hc]
  exact congrArg (E.iso.hom.f (q + 1)).hom (Subtype.ext (LinearMap.congr_fun g.map_d y).symm)

/-- The bilinear map `(x, y) ↦ (-1)^{pq} (g y)(x)` from `M^p × M'^q` to `N^n` of a homomorphism
`g : M' → H`. -/
noncomputable def uncurryMap (E : LeftHomPresentation M N)
    (g : LeftModule.Hom M' E.module)
    (p q n : ℤ) (h : p + q = n) : M.grading p →ₗ[R] M'.grading q →ₗ[R] N.X n :=
  LinearMap.mk₂ R
    (fun x y => (p * q).negOnePow • ((homCochain M M' N E g q y).v p n h).hom x)
    (by
      intro x z y
      rw [show (((homCochain M M' N E g q) y).v p n h).hom (x + z) = _ from
        (((homCochain M M' N E g q) y).v p n h).hom.map_add x z, smul_add])
    (by
      intro c x y
      rw [show (((homCochain M M' N E g q) y).v p n h).hom (c • x) = _ from
        (((homCochain M M' N E g q) y).v p n h).hom.map_smul c x]
      exact smul_comm _ _ _)
    (by
      intro x y z
      simp only [map_add, Cochain.add_v, ModuleCat.hom_add]
      change (p * q).negOnePow • ((_ : N.X n) + _) = _
      exact smul_add _ _ _)
    (by
      intro c x y
      simp only [map_smul, Cochain.smul_v, ModuleCat.hom_smul]
      exact smul_comm _ _ _)

/-- `uncurryMap` is balanced: it takes the same value on `(x a, y)` and on `(x, a y)`. -/
theorem uncurryMap_balance (E : LeftHomPresentation M N)
    (g : LeftModule.Hom M' E.module)
    (p i q n : ℤ) (h₁ : p + i + q = n) (h₂ : p + (i + q) = n)
    (x : M.grading p) (a : A.grading i) (y : M'.grading q) :
    uncurryMap M M' N E g (p + i) q n h₁
      ⟨MulOpposite.op (a : A.A) • (x : M.M), M.smul_mem p i x a x.2 a.2⟩ y =
    uncurryMap M M' N E g p (i + q) n h₂ x
      ⟨(a : A.A) • (y : M'.M), M'.smul_mem i q a y a.2 y.2⟩ := by
  subst h₂
  let f : E.module.grading q := ⟨g.toFun y, g.map_grading q y y.property⟩
  let xa : M.grading (p + i) :=
    ⟨MulOpposite.op (a : A.A) • (x : M.M), M.smul_mem p i x a x.2 a.2⟩
  have ha := presentation_action_eq M N E i q p a f x
  have hg : homCochain M M' N E g (i + q)
      ⟨(a : A.A) • (y : M'.M), M'.smul_mem i q a y a.2 y.2⟩ =
      (E.iso.hom.f (i + q)).hom
        ⟨(a : A.A) • (f : E.module.M), E.module.smul_mem i q a f a.2 f.2⟩ := by
    dsimp only [homCochain, LinearMap.comp_apply]
    exact congrArg (E.iso.hom.f (i + q)).hom (Subtype.ext (g.map_smul a y))
  show ((p + i) * q).negOnePow •
      ((homCochain M M' N E g q y).v (p + i) (p + (i + q)) _).hom xa =
    (p * (i + q)).negOnePow • _
  rw [hg, ha]
  simp only [← Units.smul_def]
  rw [smul_smul, sign_action]
  simp only [mul_right_comm _ _ (i * (q + p)).negOnePow,
    Int.units_mul_self, one_mul]
  rfl

/-- The Leibniz rule for `uncurryMap`: the differential of the value on `(x, y)` with `x ∈ M^p`
is the value on `(dx, y)` plus `(-1)^p` times the value on `(x, dy)`. -/
theorem uncurryMap_d (E : LeftHomPresentation M N)
    (g : LeftModule.Hom M' E.module)
    (p q n : ℤ) (h : p + q = n) (x : M.grading p) (y : M'.grading q) :
    N.d n (n + 1) (uncurryMap M M' N E g p q n h x y) =
      uncurryMap M M' N E g (p + 1) q (n + 1) (by omega)
        ⟨M.d x, M.d_mem p x x.2⟩ y +
      (p.negOnePow : ℤ) • uncurryMap M M' N E g p (q + 1) (n + 1) (by omega)
        x ⟨M'.d y, M'.d_mem q y y.2⟩ := by
  subst n
  have hc := congrArg (fun z : Cochain M.toCochainComplex N (q + 1) =>
    (z.v p (p + q + 1) (by omega)).hom x) (homCochain_d M M' N E g q y)
  rw [δ_v q (q + 1) rfl _ p (p + q + 1) (by omega) (p + q) (p + 1)
    (by omega) rfl] at hc
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_smul,
    Units.smul_def, DifferentialGradedModule.toCochainComplex_d] at hc
  change (N.d (p + q) (p + q + 1)).hom
      (((homCochain M M' N E g q y).v p (p + q) rfl).hom x) +
    (q + 1).negOnePow •
      (((homCochain M M' N E g q y).v (p + 1) (p + q + 1) (by omega)).hom
        ⟨M.d x, M.d_mem p x x.2⟩) = _ at hc
  show (N.d (p + q) (p + q + 1)).hom
      ((p * q).negOnePow • (((homCochain M M' N E g q y).v p (p + q) rfl).hom x)) = _
  simp only [Units.smul_def, map_zsmul]
  show (p * q).negOnePow • (_ : N.X (p + q + 1)) =
    ((p + 1) * q).negOnePow • (_ : N.X (p + q + 1)) +
      p.negOnePow • ((p * (q + 1)).negOnePow •
        (((homCochain M M' N E g (q + 1) ⟨M'.d y, M'.d_mem q y y.2⟩).v
          p (p + q + 1) (by omega)).hom x))
  rw [← hc, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  have hs : p.negOnePow * (p * (q + 1)).negOnePow = (p * q).negOnePow := by
    rw [mul_add, mul_one, Int.negOnePow_add, mul_left_comm, Int.units_mul_self, mul_one]
  have ht : (p * q).negOnePow * (q + 1).negOnePow =
      -((p + 1) * q).negOnePow := by
    rw [Int.negOnePow_succ, mul_neg, add_mul, one_mul, Int.negOnePow_add]
  rw [hs, ht, Units.neg_smul]
  abel

/-- The balanced bilinear map out of `M` and `M'` of a homomorphism `g : M' → H`, given by
`(x, y) ↦ (-1)^{pq} (g y)(x)`. -/
noncomputable def uncurryBilinear (E : LeftHomPresentation M N)
    (g : LeftModule.Hom M' E.module) : BalancedBilinear M M' N where
  map := uncurryMap M M' N E g
  balance := uncurryMap_balance M M' N E g
  map_d := uncurryMap_d M M' N E g

/-- The cochains of `curryHom M M' N E B` are the cochains `curryCochain M M' N B`. -/
theorem homCochain_curryHom (E : LeftHomPresentation M N)
    (B : BalancedBilinear M M' N) (q : ℤ) (y : M'.grading q) :
    homCochain M M' N E (curryHom M M' N E B) q y = curryCochain M M' N B q y := by
  have hy : (⟨(curryHom M M' N E B).toFun y,
      (curryHom M M' N E B).map_grading q y y.property⟩ : E.module.grading q) =
      curryPiece M M' N E B q y :=
    Subtype.ext (curryToFun_of_mem M M' N E B q y y.property)
  show (E.iso.hom.f q).hom
    (⟨(curryHom M M' N E B).toFun y,
      (curryHom M M' N E B).map_grading q y y.property⟩ : E.module.grading q) = _
  rw [hy, curryPiece_iso]

/-- `uncurryBilinear (curryHom B)` agrees with `B` on every pair of homogeneous elements. -/
theorem uncurry_curry_apply (E : LeftHomPresentation M N)
    (B : BalancedBilinear M M' N)
    (p q n : ℤ) (h : p + q = n) (x : M.grading p) (y : M'.grading q) :
    (uncurryBilinear M M' N E (curryHom M M' N E B)).map p q n h x y =
      B.map p q n h x y := by
  show (p * q).negOnePow •
    ((homCochain M M' N E (curryHom M M' N E B) q y).v p n h).hom x = _
  rw [homCochain_curryHom, curryCochain_apply, smul_smul, Int.units_mul_self, one_smul]

/-- Two homomorphisms `M' → H` with the same cochains `homCochain` are equal. -/
theorem hom_ext_cochain (E : LeftHomPresentation M N)
    (f g : LeftModule.Hom M' E.module)
    (h : ∀ q y, homCochain M M' N E f q y = homCochain M M' N E g q y) : f = g := by
  apply LeftModule.Hom.ext
  ext y
  induction y using DirectSum.Decomposition.inductionOn M'.grading with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | @homogeneous q y =>
    have hh := (ModuleCat.mono_iff_injective (E.iso.hom.f q)).mp inferInstance (h q y)
    exact congrArg Subtype.val hh

/-- `curryHom` is a left inverse of `uncurryBilinear`. -/
theorem curry_uncurry (E : LeftHomPresentation M N)
    (g : LeftModule.Hom M' E.module) :
    curryHom M M' N E (uncurryBilinear M M' N E g) = g := by
  apply hom_ext_cochain
  intro q y
  rw [homCochain_curryHom]
  apply Cochain.ext
  intro p n h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (x : M.grading p)
  rw [curryCochain_apply]
  show (p * q).negOnePow • ((p * q).negOnePow • (_ : N.X n)) = _
  rw [smul_smul, Int.units_mul_self, one_smul]

end LeftHomAux

section Left

variable (M : DifferentialGradedModule.{u, v, u} A) (M' : LeftModule A)
  (N : CochainComplex (ModuleCat.{u} R) ℤ) (H : LeftModule A)
  (iso : LeftModule.toCochainComplex A H ≅ HomComplexR R M.toCochainComplex N)
  (hact : ∀ (p q n : ℤ) (a : A.grading p) (f : H.grading q) (x : M.grading n),
    HEq
      ((((iso.hom.f (p + q))
          (⟨(a : A.A) • (f : H.M),
            H.smul_mem p q (a : A.A) (f : H.M) a.property f.property⟩ :
            H.grading (p + q))).v n (n + (p + q)) (by omega)).hom x)
      ((p * (q + n)).negOnePow •
        (((iso.hom.f q) f).v (n + p) (n + p + q) (by omega)).hom
          (⟨MulOpposite.op (a : A.A) • (x : M.M),
            M.smul_mem n p (x : M.M) (a : A.A) x.property a.property⟩ :
            M.grading (n + p))))

include iso hact

/-- Homomorphisms of left differential graded `A`-modules into a presentation of `Hom(M, N)`
are the balanced bilinear maps out of `M` and `M'`, with the Koszul sign. -/
noncomputable def leftHomBalancedEquiv :
    LeftModule.Hom M' H ≃ BalancedBilinear M M' N where
  toFun g := LeftHomAux.uncurryBilinear M M' N ⟨H, iso, hact⟩ g
  invFun B := LeftHomAux.curryHom M M' N ⟨H, iso, hact⟩ B
  left_inv g := LeftHomAux.curry_uncurry M M' N ⟨H, iso, hact⟩ g
  right_inv B := BalancedBilinear.ext fun p q n hpq x y =>
    LeftHomAux.uncurry_curry_apply M M' N ⟨H, iso, hact⟩ B p q n hpq x y

/-- The equivalence sends `g` to the pairing `(x, y) ↦ (-1)^{pq} (g y)(x)`. -/
theorem leftHomBalancedEquiv_apply (g : LeftModule.Hom M' H)
    (p q n : ℤ) (h : p + q = n) (x : M.grading p) (y : M'.grading q) :
    (leftHomBalancedEquiv M M' N H iso hact g).map p q n h x y =
      ((p * q).negOnePow : ℤ) •
        (((iso.hom.f q) ⟨g.toFun y, g.map_grading q y y.property⟩).v p n (by omega)).hom x :=
  rfl

/-! ### The left-handed adjunction -/

/-- For a right differential graded `A`-module `M`, a left differential graded `A`-module `M'` and
a complex `N` of `R`-modules, homomorphisms of left differential graded `A`-modules
`M' → Hom(M, N)` are the maps of complexes of `R`-modules `M ⊗_A M' → N`. -/
@[stacks 0FQ6 "the identification"]
noncomputable def leftTensorHomEquiv :
    LeftModule.Hom M' H ≃ (tensorComplex M M' ⟶ N) :=
  (leftHomBalancedEquiv M M' N H iso hact).trans (tensorHomEquiv M M' N).symm

/-- `leftTensorHomEquiv` sends `g` to the map of complexes taking `x ⊗ y` to
`(-1)^{pq} (g y)(x)`. -/
@[stacks 0FQ6 "the identification on pure tensors"]
theorem leftTensorHomEquiv_apply (g : LeftModule.Hom M' H)
    (p q n : ℤ) (h : p + q = n) (x : M.grading p) (y : M'.grading q) :
    ((leftTensorHomEquiv M M' N H iso hact g).f n).hom ((tensorTmul M M').map p q n h x y) =
      ((p * q).negOnePow : ℤ) •
        (((iso.hom.f q) ⟨g.toFun y, g.map_grading q y y.property⟩).v p n (by omega)).hom x := by
  have he : leftTensorHomEquiv M M' N H iso hact g =
      tensorDesc M M' N (leftHomBalancedEquiv M M' N H iso hact g) := rfl
  rw [he, tensorDesc_apply, leftHomBalancedEquiv_apply]

end Left

section LeftExistence

variable (M : DifferentialGradedModule.{u, v, u} A) (M' : LeftModule A)
  (N : CochainComplex (ModuleCat.{u} R) ℤ)

/-- There is a left differential graded `A`-module `H` with underlying complex `Hom(M, N)` such
that homomorphisms `M' → H` are in bijection with maps of complexes `M ⊗_A M' → N`. -/
@[stacks 0FQ6 "existence of the identification"]
theorem exists_leftTensorHomEquiv :
    ∃ (H : LeftModule A)
      (_ : LeftModule.toCochainComplex A H ≅ HomComplexR R M.toCochainComplex N),
      Nonempty (LeftModule.Hom M' H ≃ (tensorComplex M M' ⟶ N)) := by
  obtain ⟨H, i, hi⟩ := DifferentialGradedModule.exists_homLeftModule A M N
  exact ⟨H, i, ⟨leftTensorHomEquiv M M' N H i hi⟩⟩

end LeftExistence

end DifferentialGraded
