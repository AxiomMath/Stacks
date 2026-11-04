module

public import StacksFrontier.Algebra.DGA.QuasiIsomorphisms
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclic
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyPGeneral

/-! # Property (P) and orthogonality to the acyclic modules, at independent universes

Let `(A, d)` be a differential graded algebra over a commutative ring `R`, with the base ring,
the algebra and the modules in three independent universes. This file proves Stacks Tag 09KM at
those universes — a differential graded module with property (P) lies in the left orthogonal of
the acyclic objects of the homotopy category — and combines it with Tag 09KP to produce, for
every object of the homotopy category, a morphism to it from an object of that left orthogonal
whose cone is acyclic.

## Main definitions

* `DifferentialGradedModule.General.IsNullHomotopic`: a homomorphism of differential graded
  modules whose source and target lie in *different* universes is null-homotopic.

## Main results

* `DifferentialGradedModule.General.leftOrthogonal_acyclic_iff`: being orthogonal on the left to
  the acyclic objects of the homotopy category is the same as every homomorphism into an acyclic
  differential graded module being null-homotopic.
* `DifferentialGradedModule.General.isNullHomotopic_of_acyclic`: a homomorphism from a shift of
  the regular module into an acyclic differential graded module in any universe is
  null-homotopic.
* `DifferentialGradedModule.General.isNullHomotopic_of_directSum`: a homomorphism out of a
  differential graded module presented as a direct sum is null-homotopic as soon as each of its
  restrictions to the summands is.
* `DifferentialGradedModule.General.leftOrthogonal_acyclic_of_admissibleFiltration`: a module
  with an exhaustive filtration by admissible monomorphisms, whose bottom stage and graded pieces
  lie in the left orthogonal of the acyclic objects, lies there too.
* `DifferentialGradedModule.General.leftOrthogonal_acyclic_of_propertyP`: a module with a
  property-(P) filtration lies in the left orthogonal of the acyclic objects.
* `DifferentialGradedModule.exists_trW_leftOrthogonal_acyclic`: every object of the homotopy
  category of right differential graded `A`-modules receives a morphism, with acyclic cone, from
  an object of the left orthogonal of the acyclic objects.

## References

* [Stacks Project, Tag 09K1](https://stacks.math.columbia.edu/tag/09K1)
* [Stacks Project, Tag 09KL](https://stacks.math.columbia.edu/tag/09KL)
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM)
* [Stacks Project, Tag 09KP](https://stacks.math.columbia.edu/tag/09KP)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum

namespace DifferentialGradedModule

universe u v w w'

variable {R : Type u} [CommRing R]

namespace General

/-! ### Null-homotopies between modules in different universes -/

/-- A homomorphism of differential graded `A`-modules is *null-homotopic* when it is the
commutator `d ∘ h + h ∘ d` of the differentials with a right `A`-linear map `h` of degree `-1`.
The source and the target may lie in independent universes. -/
def IsNullHomotopic {A : DifferentialGradedAlgebra.{u, v} R}
    {M : DifferentialGradedModule.{u, v, w} A} {N : DifferentialGradedModule.{u, v, w'} A}
    (f : Hom M N) : Prop :=
  ∃ h : M.M →ₗ[MulOpposite A.A] N.M,
    (∀ (n : ℤ) (x : M.M), x ∈ M.grading n → h x ∈ N.grading (n - 1)) ∧
      ∀ x : M.M, f.toFun x = N.d (h x) + h (M.d x)

variable {A : DifferentialGradedAlgebra.{u, v} R}

/-- A homotopy from `f` to zero exhibits `f` as the commutator of the differentials with it. -/
private theorem homotopy_zero_eq {M N : DifferentialGradedModule.{u, v, w} A} {f : M ⟶ N}
    (h : Homotopy f 0) (x : M.M) :
    f.toFun x = N.d (h.toLinearMap x) + h.toLinearMap (M.d x) := by
  rw [← h.homotopy_eq x, Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero]

/-- At equal source and target universes, being null-homotopic is being homotopic to zero. -/
theorem isNullHomotopic_iff_homotopic_zero {M N : DifferentialGradedModule.{u, v, w} A}
    (f : M ⟶ N) : IsNullHomotopic f ↔ Homotopic f 0 := by
  constructor
  · rintro ⟨h, hgr, heq⟩
    refine ⟨{ toLinearMap := h, map_grading := hgr, homotopy_eq := fun x => ?_ }⟩
    rw [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero]
    exact heq x
  · rintro ⟨h⟩
    exact ⟨h.toLinearMap, h.map_grading, homotopy_zero_eq h⟩

/-- A differential graded module is orthogonal on the left to the acyclic objects of the
homotopy category exactly when every homomorphism from it into an acyclic differential graded
module is null-homotopic. -/
theorem leftOrthogonal_acyclic_iff (M : DifferentialGradedModule.{u, v, w} A) :
    (acyclic.{u, v, w} A).leftOrthogonal ((toHomotopyCategory A).obj M) ↔
      ∀ (N : DifferentialGradedModule.{u, v, w} A), N.toCochainComplex.Acyclic →
        ∀ g : M ⟶ N, Homotopic g 0 := by
  constructor
  · intro hM N hN g
    have h0 : (toHomotopyCategory A).map g = 0 := hM _ hN
    rw [← (toHomotopyCategory A).map_zero M N] at h0
    exact (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) g 0).1 h0
  · intro h Y f hY
    obtain ⟨N⟩ := Y
    induction f using Quot.inductionOn with
    | _ g =>
      show (toHomotopyCategory A).map g = 0
      rw [← (toHomotopyCategory A).map_zero M N]
      exact (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) g 0).2 (h N hY g)

/-- Orthogonality on the left to the acyclic modules transfers along an isomorphism of
differential graded modules. -/
theorem leftOrthogonal_acyclic_of_iso (A : DifferentialGradedAlgebra.{u, v} R)
    {M N : DifferentialGradedModule.{u, v, w} A} (e : M ≅ N)
    (hM : (acyclic.{u, v, w} A).leftOrthogonal ((toHomotopyCategory A).obj M)) :
    (acyclic.{u, v, w} A).leftOrthogonal ((toHomotopyCategory A).obj N) :=
  (acyclic.{u, v, w} A).leftOrthogonal.prop_of_iso ((toHomotopyCategory A).mapIso e) hM

/-! ### Maps out of a shift of the regular module -/

/-- Right multiplication by a fixed element of a right differential graded module, as a map of
right modules out of the algebra. -/
private def rightMulBy {N : DifferentialGradedModule.{u, v, w} A} (y : N.M) :
    A.A →ₗ[MulOpposite A.A] N.M where
  toFun a := MulOpposite.op a • y
  map_add' a b := by rw [MulOpposite.op_add, add_smul]
  map_smul' c a := by
    change MulOpposite.op (a * c.unop) • y = c • (MulOpposite.op a • y)
    rw [MulOpposite.op_mul, MulOpposite.op_unop, mul_smul]

@[simp] private theorem rightMulBy_apply {N : DifferentialGradedModule.{u, v, w} A} (y : N.M)
    (a : A.A) : rightMulBy y a = MulOpposite.op a • y := rfl

/-- A homomorphism from the `k`-th shift of the regular module to an acyclic differential graded
module is null-homotopic. The target may lie in any universe; the source lies in the algebra's. -/
theorem isNullHomotopic_of_acyclic {N : DifferentialGradedModule.{u, v, w} A}
    (hN : N.toCochainComplex.Acyclic) (k : ℤ)
    (g : Hom (shift (regularModule A) k) N) : IsNullHomotopic g := by
  have hdshift : ∀ b : A.A,
      (shift (regularModule A) k).d b = (k.negOnePow : ℤ) • A.d b := fun b => by
    rw [shift_d, LinearMap.smul_apply, Units.smul_def]
  have hgmul : ∀ b : A.A, g.toFun b = MulOpposite.op b • g.toFun (1 : A.A) := fun b =>
    (congrArg g.toFun (one_mul b)).symm.trans (g.map_smul (1 : A.A) b)
  have h1 : (1 : A.A) ∈ (shift (regularModule A) k).grading (-k) := by
    simp only [shift_grading, neg_add_cancel]
    exact SetLike.one_mem_graded A.grading
  have hx : g.toFun (1 : A.A) ∈ N.grading (-k) := g.map_grading (-k) (1 : A.A) h1
  have hdx : N.d (g.toFun (1 : A.A)) = 0 := by
    have hmd := LinearMap.congr_fun g.map_d (1 : A.A)
    simp only [LinearMap.comp_apply] at hmd
    rw [hdshift (1 : A.A), algebraDifferential_one, smul_zero, map_zero] at hmd
    exact hmd.symm
  obtain ⟨y, hy, hyd⟩ := exists_d_eq_of_acyclic hN (-k - 1) (g.toFun (1 : A.A))
    (by rwa [show -k - 1 + 1 = -k by ring]) hdx
  have hop : ∀ b : A.A, MulOpposite.op ((k.negOnePow : ℤ) • A.d b) • y
      = (k.negOnePow : ℤ) • (MulOpposite.op (A.d b) • y) := fun b => by
    rw [MulOpposite.op_smul, smul_assoc]
  have hsign : ((-k - 1).negOnePow : ℤ) + (k.negOnePow : ℤ) = 0 := by
    rw [show -k - 1 = -(k + 1) by ring, Int.negOnePow_neg, Int.negOnePow_add,
      Int.negOnePow_one, mul_neg_one]
    simp
  refine ⟨rightMulBy y, ?_, ?_⟩
  · intro n a ha
    have hmem := N.smul_mem (-k - 1) (n + k) y a hy ha
    rwa [show -k - 1 + (n + k) = n - 1 by ring] at hmem
  · have key : ∀ b : A.A, g.toFun b
        = N.d (rightMulBy y b) + rightMulBy y ((shift (regularModule A) k).d b) := fun b => by
      rw [hdshift b]
      simp only [rightMulBy_apply]
      rw [hop b, leibniz_apply N (-k - 1) y hy b, hyd, add_assoc, ← add_smul, hsign, zero_smul,
        add_zero]
      exact hgmul b
    exact key

/-! ### Null-homotopies out of a direct sum -/

/-- A homomorphism out of a differential graded module presented as a direct sum is
null-homotopic as soon as each of its restrictions to the summands is.

The presentation is an `A`-linear equivalence `ev` from `⨁ j, (X j).M` onto the carrier of `T`
which carries the `j`-th coprojection to `inj j` and reflects homogeneity componentwise. The
summands, the presented module and the target all lie in independent universes. -/
theorem isNullHomotopic_of_directSum {ι : Type*} [DecidableEq ι]
    {X : ι → DifferentialGradedModule.{u, v, w} A}
    {T : DifferentialGradedModule.{u, v, w'} A}
    {N : DifferentialGradedModule.{u, v, w'} A} (inj : ∀ j, Hom (X j) T)
    (ev : (⨁ j, (X j).M) ≃ₗ[MulOpposite A.A] T.M)
    (hev : ∀ j x, ev (DirectSum.of (fun j => (X j).M) j x) = (inj j).toFun x)
    (hgr : ∀ (n : ℤ) (z : ⨁ j, (X j).M), ev z ∈ T.grading n → ∀ j, z j ∈ (X j).grading n)
    (f : Hom T N) (hX : ∀ j, IsNullHomotopic (Hom.comp f (inj j))) :
    IsNullHomotopic f := by
  classical
  choose h hgrh heqh using hX
  set Hsum : (⨁ j, (X j).M) →ₗ[MulOpposite A.A] N.M :=
    DirectSum.toModule (MulOpposite A.A) ι N.M (fun j => h j) with hHsumdef
  have hHsum_of : ∀ j x, Hsum (DirectSum.of (fun j => (X j).M) j x) = h j x := by
    intro j x
    rw [hHsumdef, ← DirectSum.lof_eq_of (MulOpposite A.A), DirectSum.toModule_lof]
  set dsum : (⨁ j, (X j).M) →+ (⨁ j, (X j).M) :=
    DirectSum.toAddMonoid (fun j =>
      (DirectSum.of (fun j => (X j).M) j).comp (X j).d.toAddMonoidHom) with hdsumdef
  have hdsum_of : ∀ j x, dsum (DirectSum.of (fun j => (X j).M) j x)
      = DirectSum.of (fun j => (X j).M) j ((X j).d x) := by
    intro j x
    rw [hdsumdef, DirectSum.toAddMonoid_of]
    rfl
  have hd : ∀ z, T.d (ev z) = ev (dsum z) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of j x =>
      rw [hev, hdsum_of, hev]
      exact (LinearMap.congr_fun (inj j).map_d x).symm
    | add z w hz hw =>
      simp only [map_add]
      rw [hz, hw]
  refine ⟨Hsum ∘ₗ (ev.symm : T.M →ₗ[MulOpposite A.A] (⨁ j, (X j).M)), ?_, ?_⟩
  · intro n t ht
    show Hsum (ev.symm t) ∈ N.grading (n - 1)
    rw [← DirectSum.sum_support_of (ev.symm t), map_sum]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [hHsum_of]
    exact hgrh j n _ (hgr n (ev.symm t) (by rwa [ev.apply_symm_apply]) j)
  · have key : ∀ z, f.toFun (ev z) = N.d (Hsum z) + Hsum (dsum z) := by
      intro z
      induction z using DirectSum.induction_on with
      | zero => simp
      | of j x =>
        rw [hev, hHsum_of, hdsum_of, hHsum_of]
        exact heqh j x
      | add z w hz hw =>
        simp only [map_add]
        rw [hz, hw]
        abel
    intro t
    show f.toFun t = N.d (Hsum (ev.symm t)) + Hsum (ev.symm (T.d t))
    rw [show t = ev (ev.symm t) from (ev.apply_symm_apply t).symm, hd,
      ev.symm_apply_apply, ev.symm_apply_apply, key]

/-! ### Direct sums of shifts of the algebra -/

/-- The `j`-th coprojection intertwines the differential of a shift of the algebra with the
componentwise differential of a direct sum of shifts, written out as a `DirectSum.toModule`. -/
theorem lof_comp_shift_d (A : DifferentialGradedAlgebra.{u, v} R) {ι : Type w}
    [DecidableEq ι] (k : ι → ℤ) (j : ι) :
    (DirectSum.lof R ι (fun _ : ι => A.A) j).comp (((k j).negOnePow : ℤ) • A.d)
      = (DirectSum.toModule R ι (⨁ _ : ι, A.A) (fun i =>
            (DirectSum.lof R ι (fun _ : ι => A.A) i).comp
              (((-1 : ℤ) ^ (k i).natAbs) • A.d))).comp
          (DirectSum.lof R ι (fun _ : ι => A.A) j) :=
  LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof, LinearMap.smul_apply,
      DifferentialGradedModule.Unbundled.negOnePow_cast]

/-- The `j`-th coprojection of a direct sum of shifts of the algebra. -/
def directSumShiftsInj (A : DifferentialGradedAlgebra.{u, v} R) {ι : Type w} [DecidableEq ι]
    (k : ι → ℤ) (j : ι) : Hom (shift (regularModule A) (k j)) (directSumShifts A k) where
  toFun := DirectSum.lof R ι (fun _ => A.A) j
  map_smul x a := by
    change DirectSum.of (fun _ : ι => A.A) j (MulOpposite.op a • x)
      = MulOpposite.op a • DirectSum.of (fun _ : ι => A.A) j x
    exact (map_smul (DirectSum.lof (MulOpposite A.A) ι (fun _ : ι => A.A) j)
      (MulOpposite.op a) x)
  map_grading n x hx := by
    intro i
    by_cases h : j = i
    · subst h
      change DirectSum.of (fun _ : ι => A.A) j x j ∈ A.grading (n + k j)
      rw [DirectSum.of_eq_same]
      exact hx
    · change DirectSum.of (fun _ : ι => A.A) j x i ∈ A.grading (n + k i)
      rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      exact (A.grading (n + k i)).zero_mem
  map_d := lof_comp_shift_d A k j

/-- A direct sum of shifts of the algebra is orthogonal on the left to the acyclic differential
graded modules. -/
theorem leftOrthogonal_acyclic_directSumShifts (A : DifferentialGradedAlgebra.{u, v} R)
    {ι : Type w} [DecidableEq ι] (k : ι → ℤ) :
    (acyclic.{u, v, max w v} A).leftOrthogonal
      ((toHomotopyCategory A).obj (directSumShifts A k)) := by
  rw [leftOrthogonal_acyclic_iff]
  intro N hN f
  rw [← isNullHomotopic_iff_homotopic_zero]
  exact isNullHomotopic_of_directSum (directSumShiftsInj A k)
    (LinearEquiv.refl (MulOpposite A.A) (⨁ _ : ι, A.A))
    (fun _ _ => rfl)
    (fun _ _ hz j => hz j)
    f
    (fun j => isNullHomotopic_of_acyclic hN (k j) _)

/-! ### The telescope argument -/

/-- Let `P` carry an exhaustive filtration by the stages `F i`, embedded in `P` by `emb i`, with
transition inclusions `incl i` that are admissible monomorphisms with cokernels
`quot i : F (i + 1) ⟶ Q i`. If the bottom stage `F 0` and every graded piece `Q i` is orthogonal
on the left to the acyclic modules, so is `P`. -/
theorem leftOrthogonal_acyclic_of_admissibleFiltration
    {P : DifferentialGradedModule.{u, v, w} A}
    (F : ℕ → DifferentialGradedModule.{u, v, w} A)
    (Q : ℕ → DifferentialGradedModule.{u, v, w} A)
    (emb : ∀ i, F i ⟶ P) (incl : ∀ i, F i ⟶ F (i + 1)) (quot : ∀ i, F (i + 1) ⟶ Q i)
    (hemb : ∀ i, Function.Injective (emb i).toFun)
    (hincl : ∀ i x, (emb (i + 1)).toFun ((incl i).toFun x) = (emb i).toFun x)
    (hadm : ∀ i, IsAdmissibleMono (incl i))
    (hsurj : ∀ i, Function.Surjective (quot i).toFun)
    (hker : ∀ i, LinearMap.ker (quot i).toFun = LinearMap.range (incl i).toFun)
    (hexh : ∀ x : P.M, ∃ i y, (emb i).toFun y = x)
    (hbot : (acyclic.{u, v, w} A).leftOrthogonal ((toHomotopyCategory A).obj (F 0)))
    (hQ : ∀ i, (acyclic.{u, v, w} A).leftOrthogonal ((toHomotopyCategory A).obj (Q i))) :
    (acyclic.{u, v, w} A).leftOrthogonal ((toHomotopyCategory A).obj P) := by
  classical
  rw [leftOrthogonal_acyclic_iff]
  intro N hN g
  have hggcomp : ∀ i x, (emb i ≫ g).toFun x = (emb (i + 1) ≫ g).toFun ((incl i).toFun x) := by
    intro i x
    show g.toFun ((emb i).toFun x) = g.toFun ((emb (i + 1)).toFun ((incl i).toFun x))
    rw [hincl]
  have step : ∀ i (h : Homotopy (emb i ≫ g) 0),
      ∃ h' : Homotopy (emb (i + 1) ≫ g) 0,
        ∀ x, h'.toLinearMap ((incl i).toFun x) = h.toLinearMap x :=
    fun i h => exists_homotopy_zero_extension (incl i) (quot i) (emb (i + 1) ≫ g) (emb i ≫ g)
      (hggcomp i) (hadm i) (hsurj i) (hker i) ((leftOrthogonal_acyclic_iff _).1 (hQ i) N hN) h
  let T : ∀ i, Homotopy (emb i ≫ g) 0 := fun i =>
    Nat.rec (motive := fun i => Homotopy (emb i ≫ g) 0)
      ((leftOrthogonal_acyclic_iff _).1 hbot N hN (emb 0 ≫ g)).some
      (fun j hj => (step j hj).choose) i
  have hT : ∀ i x, (T (i + 1)).toLinearMap ((incl i).toFun x) = (T i).toLinearMap x :=
    fun i x => (step i (T i)).choose_spec x
  have chain : ∀ q p, p ≤ q → ∃ c : F p ⟶ F q,
      (∀ y, (emb q).toFun (c.toFun y) = (emb p).toFun y) ∧
        (∀ y, (T q).toLinearMap (c.toFun y) = (T p).toLinearMap y) := by
    intro q
    induction q with
    | zero =>
      intro p hp
      obtain rfl : p = 0 := Nat.le_zero.mp hp
      exact ⟨𝟙 _, fun _ => rfl, fun _ => rfl⟩
    | succ q ih =>
      intro p hp
      rcases Nat.eq_or_lt_of_le hp with rfl | h
      · exact ⟨𝟙 _, fun _ => rfl, fun _ => rfl⟩
      · obtain ⟨c, hc₁, hc₂⟩ := ih p (Nat.lt_succ_iff.mp h)
        refine ⟨c ≫ incl q, fun y => ?_, fun y => ?_⟩
        · rw [Hom.comp_toFun_apply, hincl, hc₁]
        · rw [Hom.comp_toFun_apply, hT, hc₂]
  have hwdef : ∀ p q (y : (F p).M) (z : (F q).M),
      (emb p).toFun y = (emb q).toFun z →
        (T p).toLinearMap y = (T q).toLinearMap z := by
    have key : ∀ p q (y : (F p).M) (z : (F q).M), p ≤ q →
        (emb p).toFun y = (emb q).toFun z →
          (T p).toLinearMap y = (T q).toLinearMap z := by
      intro p q y z hpq hyz
      obtain ⟨c, hc₁, hc₂⟩ := chain q p hpq
      have : c.toFun y = z := hemb q (by rw [hc₁, hyz])
      rw [← hc₂, this]
    intro p q y z hyz
    rcases le_total p q with h | h
    · exact key p q y z h hyz
    · exact (key q p z y h hyz.symm).symm
  obtain ⟨H, hH⟩ : ∃ H : P.M → N.M,
      ∀ p (y : (F p).M), H ((emb p).toFun y) = (T p).toLinearMap y :=
    ⟨fun x => (T (hexh x).choose).toLinearMap (hexh x).choose_spec.choose,
      fun p y => hwdef _ _ _ _ (hexh ((emb p).toFun y)).choose_spec.choose_spec⟩
  refine ⟨{ toLinearMap := { toFun := H, map_add' := ?_, map_smul' := ?_ }
            map_grading := ?_
            homotopy_eq := ?_ }⟩
  · intro x x'
    obtain ⟨p, y, rfl⟩ := hexh x
    obtain ⟨q, z, rfl⟩ := hexh x'
    obtain ⟨cp, hcp₁, hcp₂⟩ := chain (max p q) p (le_max_left p q)
    obtain ⟨cq, hcq₁, hcq₂⟩ := chain (max p q) q (le_max_right p q)
    rw [← hcp₁ y, ← hcq₁ z, ← map_add, hH, hH, hH, map_add, hcp₂, hcq₂]
  · intro s x
    obtain ⟨p, y, rfl⟩ := hexh x
    show H (s • (emb p).toFun y) = s • H ((emb p).toFun y)
    rw [← MulOpposite.op_unop s, ← (emb p).map_smul, hH, hH]
    exact map_smul (T p).toLinearMap _ y
  · intro n x hx
    obtain ⟨p, y, rfl⟩ := hexh x
    show H ((emb p).toFun y) ∈ N.grading (n - 1)
    rw [hH]
    exact (T p).map_grading n y (Hom.mem_grading_of_injective (hemb p) hx)
  · intro x
    obtain ⟨p, y, rfl⟩ := hexh x
    have hd : P.d ((emb p).toFun y) = (emb p).toFun ((F p).d y) :=
      (LinearMap.congr_fun (emb p).map_d y).symm
    show g.toFun ((emb p).toFun y) - (0 : P ⟶ N).toFun ((emb p).toFun y) =
      N.d (H ((emb p).toFun y)) + H (P.d ((emb p).toFun y))
    rw [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero, hd, hH, hH]
    exact homotopy_zero_eq (T p) y

/-! ### Property (P) implies left orthogonality -/

/-- A differential graded `A`-module equipped with a property-(P) filtration lies in the left
orthogonal of the acyclic objects of the homotopy category: every morphism out of it into an
acyclic object vanishes. The filtered module's carrier universe is required to absorb the
algebra's. -/
theorem leftOrthogonal_acyclic_of_propertyP
    {P : DifferentialGradedModule.{u, v, max v w} A} (F : PropertyPFiltration P) :
    (acyclic.{u, v, max v w} A).leftOrthogonal ((toHomotopyCategory A).obj P) := by
  have hQ : ∀ i, (acyclic A).leftOrthogonal ((toHomotopyCategory A).obj
      (@directSumShifts _ _ _ _ (F.quotientDecidableEq i) (F.quotientShift i))) := fun i =>
    @leftOrthogonal_acyclic_directSumShifts _ _ _ _ (F.quotientDecidableEq i) (F.quotientShift i)
  have hbot : (acyclic A).leftOrthogonal ((toHomotopyCategory A).obj (F.F 0)) :=
    leftOrthogonal_acyclic_of_iso A (F.bottomMap.isoOfBijective F.bottom_bijective).symm
      (@leftOrthogonal_acyclic_directSumShifts _ _ _ _ F.bottomDecidableEq F.bottomShift)
  exact leftOrthogonal_acyclic_of_admissibleFiltration F.F
    (fun i => @directSumShifts _ _ _ _ (F.quotientDecidableEq i) (F.quotientShift i))
    F.ι F.incl F.quotientMap F.injective F.incl_comp F.admissible F.quotient_surjective
    F.quotient_ker F.exhaustive hbot hQ

end General

/-! ### Resolutions by objects of the left orthogonal -/

/- Two pretriangulated structures on the homotopy category are in scope here: the
universe-polymorphic `DifferentialGradedModule.instPretriangulatedHomotopyCategory`, whose
distinguished triangles are the cone triangles, and the single-universe
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'`. The class `(acyclic A).trW`
below is the one of the first structure, which this priority makes instance search select. -/
attribute [local instance 10000] instPretriangulatedHomotopyCategory

/-- Every object `Y` of the homotopy category of right differential graded `A`-modules receives
a morphism `f : P ⟶ Y` whose cone is acyclic — equivalently, which is a quasi-isomorphism — from
an object `P` of the left orthogonal of the acyclic objects. The module universe is `max u v w`,
which absorbs the base ring's universe `u` and the algebra's universe `v`. -/
theorem exists_trW_leftOrthogonal_acyclic (A : DifferentialGradedAlgebra.{u, v} R)
    (Y : HomotopyCategory.{u, v, max u v w} A) :
    ∃ (P : HomotopyCategory.{u, v, max u v w} A) (f : P ⟶ Y),
      (acyclic A).trW f ∧ (acyclic A).leftOrthogonal P := by
  obtain ⟨M⟩ := Y
  obtain ⟨P, f, hf, ⟨F⟩⟩ := General.exists_propertyP_resolution.{u, v, max u w} A M
  have htrW : (acyclic.{u, v, max u v w} A).trW ((toHomotopyCategory A).map f) := by
    rwa [acyclic_trW_eq_quasiIsomorphisms, quasiIsomorphisms_map_iff]
  exact ⟨(toHomotopyCategory A).obj P, (toHomotopyCategory A).map f, htrW,
    General.leftOrthogonal_acyclic_of_propertyP.{u, v, max u w} F⟩

end DifferentialGradedModule

end
